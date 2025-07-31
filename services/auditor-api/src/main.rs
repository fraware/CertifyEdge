//! CertifyEdge Auditor API Server
//! 
//! This is the main entry point for the CertifyEdge Auditor API service.

use axum::{
    routing::{get, post},
    Router,
    http::{HeaderValue, Method},
    middleware,
};
use tower_http::cors::CorsLayer;
use std::net::SocketAddr;
use std::time::Duration;
use tokio::signal;
use tracing::{info, warn, error};

use auditor_api::{
    AuditorAPI, config::AuditorConfig, error::AuditorError,
    api, auth::AuthMiddleware,
};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Initialize logging
    init_logging()?;
    
    // Load configuration
    let config = load_config()?;
    info!("Configuration loaded successfully");
    
    // Create auditor API service
    let api_service = AuditorAPI::with_config(config.clone())
        .map_err(|e| format!("Failed to create auditor API: {}", e))?;
    
    info!("Auditor API service created successfully");
    
    // Create router with middleware
    let app = create_router(api_service, &config);
    
    // Bind to address
    let addr = format!("{}:{}", config.server.host, config.server.port)
        .parse::<SocketAddr>()
        .map_err(|e| format!("Failed to parse address: {}", e))?;
    
    info!("Starting auditor API server on {}", addr);
    
    // Start server
    let server = axum::Server::bind(&addr)
        .serve(app.into_make_service())
        .with_graceful_shutdown(shutdown_signal());
    
    // Run server
    if let Err(e) = server.await {
        error!("Server error: {}", e);
        return Err(e.into());
    }
    
    info!("Server shutdown complete");
    Ok(())
}

/// Initialize logging
fn init_logging() -> Result<(), Box<dyn std::error::Error>> {
    // Set up tracing subscriber
    tracing_subscriber::fmt()
        .with_env_filter(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| "auditor_api=info,tower_http=info".into()),
        )
        .with_target(false)
        .with_thread_ids(true)
        .with_thread_names(true)
        .with_file(true)
        .with_line_number(true)
        .init();
    
    info!("Logging initialized");
    Ok(())
}

/// Load configuration
fn load_config() -> Result<AuditorConfig, Box<dyn std::error::Error>> {
    // Try to load from environment first
    if let Ok(config_path) = std::env::var("AUDITOR_CONFIG_PATH") {
        info!("Loading configuration from {}", config_path);
        return AuditorConfig::from_file(std::path::Path::new(&config_path))
            .map_err(|e| format!("Failed to load config from file: {}", e).into());
    }
    
    // Try to load from default locations
    let config_paths = vec![
        "config/auditor.json",
        "auditor.json",
        "config/auditor.yaml",
        "auditor.yaml",
    ];
    
    for path in config_paths {
        if std::path::Path::new(path).exists() {
            info!("Loading configuration from {}", path);
            return AuditorConfig::from_file(std::path::Path::new(path))
                .map_err(|e| format!("Failed to load config from {}: {}", path, e).into());
        }
    }
    
    // Use default configuration
    info!("Using default configuration");
    let config = AuditorConfig::default();
    
    // Validate configuration
    config.validate()
        .map_err(|e| format!("Configuration validation failed: {}", e))?;
    
    Ok(config)
}

/// Create router with middleware
fn create_router(api_service: AuditorAPI, config: &AuditorConfig) -> Router {
    // Create CORS layer
    let cors = CorsLayer::new()
        .allow_origin(
            config.security.cors_allowed_origins
                .iter()
                .map(|origin| origin.parse::<HeaderValue>().unwrap())
                .collect::<Vec<_>>()
        )
        .allow_methods([
            Method::GET,
            Method::POST,
            Method::OPTIONS,
        ])
        .allow_headers(vec![
            "authorization".parse::<HeaderValue>().unwrap(),
            "content-type".parse::<HeaderValue>().unwrap(),
        ])
        .max_age(Duration::from_secs(3600));
    
    // Create rate limiting layer
    let rate_limit = if config.rate_limiting.enabled {
        tower::limit::RateLimitLayer::new(
            config.rate_limiting.requests_per_minute as u64,
            Duration::from_secs(60),
        )
    } else {
        tower::limit::RateLimitLayer::new(u64::MAX, Duration::from_secs(1))
    };
    
    // Create compression layer
    let compression = if config.performance.enable_response_compression {
        tower_http::compression::CompressionLayer::new()
    } else {
        tower_http::compression::CompressionLayer::new().no_compress()
    };
    
    // Create timeout layer
    let timeout = tower::timeout::TimeoutLayer::new(
        Duration::from_secs(config.server.request_timeout_seconds)
    );
    
    // Create tracing layer
    let tracing = tower_http::trace::TraceLayer::new_for_http()
        .make_span_with(tower_http::trace::DefaultMakeSpan::new().include_headers(true))
        .on_request(tower_http::trace::DefaultOnRequest::new().level(tracing::Level::INFO))
        .on_response(tower_http::trace::DefaultOnResponse::new().level(tracing::Level::INFO))
        .on_failure(tower_http::trace::DefaultOnFailure::new().level(tracing::Level::ERROR));
    
    // Build router
    Router::new()
        .route("/health", get(api::health_check))
        .route("/cert/:model_sha", get(api::get_certificate))
        .route("/diff/:old_sha/:new_sha", get(api::get_certificate_diff))
        .route("/query", post(api::query_certificates))
        .route("/metrics", get(api::get_metrics))
        .layer(cors)
        .layer(rate_limit)
        .layer(compression)
        .layer(timeout)
        .layer(tracing)
        .layer(middleware::from_fn_with_state(
            api_service.clone(),
            AuthMiddleware::authenticate,
        ))
        .with_state(api_service)
}

/// Graceful shutdown signal handler
async fn shutdown_signal() {
    let ctrl_c = async {
        signal::ctrl_c()
            .await
            .expect("Failed to install Ctrl+C handler");
    };
    
    #[cfg(unix)]
    let terminate = async {
        signal::unix::signal(signal::unix::SignalKind::terminate())
            .expect("Failed to install signal handler")
            .recv()
            .await;
    };
    
    #[cfg(not(unix))]
    let terminate = std::future::pending::<()>();
    
    tokio::select! {
        _ = ctrl_c => {
            info!("Received Ctrl+C, shutting down gracefully");
        }
        _ = terminate => {
            info!("Received terminate signal, shutting down gracefully");
        }
    }
    
    // Give the server a chance to finish processing requests
    tokio::time::sleep(Duration::from_secs(5)).await;
}

/// Health check handler for external monitoring
async fn health_check() -> &'static str {
    "healthy"
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_config_loading() {
        let config = load_config();
        assert!(config.is_ok());
    }
    
    #[tokio::test]
    async fn test_router_creation() {
        let config = AuditorConfig::default();
        let api_service = AuditorAPI::with_config(config.clone()).unwrap();
        let router = create_router(api_service, &config);
        assert!(router.into_make_service().into_make_service().is_ok());
    }
} 