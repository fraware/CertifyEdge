//! Authentication middleware for the CertifyEdge Auditor API

use axum::{
    extract::State,
    http::{Request, StatusCode},
    middleware::Next,
    response::Response,
};
use jsonwebtoken::{decode, DecodingKey, Validation, Algorithm};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::{SystemTime, UNIX_EPOCH};

use crate::{AuditorAPI, error::AuditorError};

/// JWT claims structure
#[derive(Debug, Serialize, Deserialize)]
pub struct Claims {
    pub sub: String,           // Subject (user ID)
    pub iss: String,           // Issuer
    pub aud: String,           // Audience
    pub exp: u64,             // Expiration time
    pub iat: u64,             // Issued at
    pub roles: Vec<String>,    // User roles
    pub permissions: Vec<String>, // User permissions
}

/// User context for request processing
#[derive(Debug, Clone)]
pub struct UserContext {
    pub user_id: String,
    pub roles: Vec<String>,
    pub permissions: Vec<String>,
    pub session_id: String,
}

/// Authentication middleware
pub struct AuthMiddleware;

impl AuthMiddleware {
    /// Authenticate and authorize requests
    pub async fn authenticate<B>(
        State(api): State<AuditorAPI>,
        mut req: Request<B>,
        next: Next<B>,
    ) -> Result<Response, (StatusCode, String)> {
        let start_time = SystemTime::now();
        
        // Extract authorization header
        let auth_header = req
            .headers()
            .get("authorization")
            .and_then(|h| h.to_str().ok())
            .ok_or((StatusCode::UNAUTHORIZED, "Missing authorization header".to_string()))?;
        
        // Validate JWT token
        let claims = Self::validate_jwt(auth_header, &api.config.auth.jwt_secret)
            .map_err(|e| (StatusCode::UNAUTHORIZED, e.to_string()))?;
        
        // Check token expiration
        let current_time = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        if claims.exp < current_time {
            return Err((StatusCode::UNAUTHORIZED, "Token expired".to_string()));
        }
        
        // Create user context
        let user_context = UserContext {
            user_id: claims.sub,
            roles: claims.roles,
            permissions: claims.permissions,
            session_id: uuid::Uuid::new_v4().to_string(),
        };
        
        // Apply OPA policies
        let opa_result = Self::apply_opa_policies(&user_context, &req, &api.config)
            .await
            .map_err(|e| (StatusCode::FORBIDDEN, e.to_string()))?;
        
        if !opa_result.allowed {
            return Err((
                StatusCode::FORBIDDEN,
                format!("Access denied: {}", opa_result.reason.unwrap_or_default()),
            ));
        }
        
        // Add user context to request extensions
        req.extensions_mut().insert(user_context);
        
        // Continue with the request
        let response = next.run(req).await;
        
        // Record authentication metrics
        let auth_time = start_time.elapsed().as_millis() as u64;
        // TODO: Update authentication metrics
        
        Ok(response)
    }
    
    /// Validate JWT token
    fn validate_jwt(token: &str, secret: &str) -> Result<Claims, AuditorError> {
        // Remove "Bearer " prefix if present
        let token = token.strip_prefix("Bearer ").unwrap_or(token);
        
        let key = DecodingKey::from_secret(secret.as_ref());
        let validation = Validation::new(Algorithm::HS256);
        
        let token_data = decode::<Claims>(token, &key, &validation)
            .map_err(|e| AuditorError::AuthenticationError(format!("JWT validation failed: {}", e)))?;
        
        Ok(token_data.claims)
    }
    
    /// Apply OPA policies for authorization
    async fn apply_opa_policies(
        user_context: &UserContext,
        req: &Request<impl axum::body::HttpBody>,
        config: &crate::config::AuditorConfig,
    ) -> Result<OpaResult, AuditorError> {
        // Build OPA input
        let opa_input = OpaInput {
            user: OpaUser {
                id: user_context.user_id.clone(),
                roles: user_context.roles.clone(),
                permissions: user_context.permissions.clone(),
            },
            request: OpaRequest {
                method: req.method().to_string(),
                path: req.uri().path().to_string(),
                headers: req
                    .headers()
                    .iter()
                    .map(|(k, v)| (k.to_string(), v.to_str().unwrap_or("").to_string()))
                    .collect(),
            },
            resource: OpaResource {
                type_: "certificate".to_string(),
                action: Self::determine_action(req.method().as_str(), req.uri().path()),
            },
        };
        
        // Call OPA service
        let opa_client = opa::OpaClient::new(&config.opa.endpoint);
        let result = opa_client.evaluate_policy("certifyedge.auditor", &opa_input).await?;
        
        Ok(result)
    }
    
    /// Determine the action being performed
    fn determine_action(method: &str, path: &str) -> String {
        match (method, path) {
            ("GET", path) if path.starts_with("/cert/") => "read".to_string(),
            ("GET", path) if path.starts_with("/diff/") => "read".to_string(),
            ("POST", "/query") => "query".to_string(),
            ("GET", "/metrics") => "read".to_string(),
            ("GET", "/health") => "read".to_string(),
            _ => "unknown".to_string(),
        }
    }
}

/// OPA input structure
#[derive(Debug, Serialize)]
pub struct OpaInput {
    pub user: OpaUser,
    pub request: OpaRequest,
    pub resource: OpaResource,
}

#[derive(Debug, Serialize)]
pub struct OpaUser {
    pub id: String,
    pub roles: Vec<String>,
    pub permissions: Vec<String>,
}

#[derive(Debug, Serialize)]
pub struct OpaRequest {
    pub method: String,
    pub path: String,
    pub headers: HashMap<String, String>,
}

#[derive(Debug, Serialize)]
pub struct OpaResource {
    #[serde(rename = "type")]
    pub type_: String,
    pub action: String,
}

/// OPA result structure
#[derive(Debug, Deserialize)]
pub struct OpaResult {
    pub allowed: bool,
    pub reason: Option<String>,
    pub obligations: Option<Vec<String>>,
}

/// Authentication configuration
#[derive(Debug, Clone)]
pub struct AuthConfig {
    pub jwt_secret: String,
    pub jwt_issuer: String,
    pub jwt_audience: String,
    pub token_expiry_seconds: u64,
    pub refresh_token_expiry_seconds: u64,
}

impl Default for AuthConfig {
    fn default() -> Self {
        Self {
            jwt_secret: "default-secret-change-in-production".to_string(),
            jwt_issuer: "certifyedge".to_string(),
            jwt_audience: "certifyedge-auditor".to_string(),
            token_expiry_seconds: 3600, // 1 hour
            refresh_token_expiry_seconds: 86400, // 24 hours
        }
    }
}

/// Role-based access control
#[derive(Debug, Clone)]
pub struct RBAC {
    pub roles: HashMap<String, Role>,
    pub permissions: HashMap<String, Permission>,
}

#[derive(Debug, Clone)]
pub struct Role {
    pub name: String,
    pub permissions: Vec<String>,
    pub description: String,
}

#[derive(Debug, Clone)]
pub struct Permission {
    pub name: String,
    pub resources: Vec<String>,
    pub actions: Vec<String>,
    pub description: String,
}

impl RBAC {
    /// Create default RBAC configuration
    pub fn new() -> Self {
        let mut roles = HashMap::new();
        let mut permissions = HashMap::new();
        
        // Define permissions
        permissions.insert(
            "certificate:read".to_string(),
            Permission {
                name: "certificate:read".to_string(),
                resources: vec!["certificate".to_string()],
                actions: vec!["read".to_string()],
                description: "Read certificate information".to_string(),
            },
        );
        
        permissions.insert(
            "certificate:query".to_string(),
            Permission {
                name: "certificate:query".to_string(),
                resources: vec!["certificate".to_string()],
                actions: vec!["query".to_string()],
                description: "Query certificates with filters".to_string(),
            },
        );
        
        permissions.insert(
            "certificate:diff".to_string(),
            Permission {
                name: "certificate:diff".to_string(),
                resources: vec!["certificate".to_string()],
                actions: vec!["diff".to_string()],
                description: "Compare certificates".to_string(),
            },
        );
        
        permissions.insert(
            "metrics:read".to_string(),
            Permission {
                name: "metrics:read".to_string(),
                resources: vec!["metrics".to_string()],
                actions: vec!["read".to_string()],
                description: "Read API metrics".to_string(),
            },
        );
        
        // Define roles
        roles.insert(
            "auditor".to_string(),
            Role {
                name: "auditor".to_string(),
                permissions: vec![
                    "certificate:read".to_string(),
                    "certificate:query".to_string(),
                    "certificate:diff".to_string(),
                    "metrics:read".to_string(),
                ],
                description: "Full auditor access".to_string(),
            },
        );
        
        roles.insert(
            "viewer".to_string(),
            Role {
                name: "viewer".to_string(),
                permissions: vec![
                    "certificate:read".to_string(),
                    "metrics:read".to_string(),
                ],
                description: "Read-only access".to_string(),
            },
        );
        
        Self { roles, permissions }
    }
    
    /// Check if user has permission
    pub fn has_permission(&self, user_roles: &[String], permission: &str) -> bool {
        for role_name in user_roles {
            if let Some(role) = self.roles.get(role_name) {
                if role.permissions.contains(&permission.to_string()) {
                    return true;
                }
            }
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rbac_creation() {
        let rbac = RBAC::new();
        assert!(!rbac.roles.is_empty());
        assert!(!rbac.permissions.is_empty());
    }

    #[test]
    fn test_rbac_permissions() {
        let rbac = RBAC::new();
        
        // Test auditor role
        let auditor_roles = vec!["auditor".to_string()];
        assert!(rbac.has_permission(&auditor_roles, "certificate:read"));
        assert!(rbac.has_permission(&auditor_roles, "certificate:query"));
        assert!(rbac.has_permission(&auditor_roles, "certificate:diff"));
        assert!(rbac.has_permission(&auditor_roles, "metrics:read"));
        
        // Test viewer role
        let viewer_roles = vec!["viewer".to_string()];
        assert!(rbac.has_permission(&viewer_roles, "certificate:read"));
        assert!(!rbac.has_permission(&viewer_roles, "certificate:query"));
        assert!(!rbac.has_permission(&viewer_roles, "certificate:diff"));
        assert!(rbac.has_permission(&viewer_roles, "metrics:read"));
    }
} 