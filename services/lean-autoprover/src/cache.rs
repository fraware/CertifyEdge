//! Proof cache for Lean 4 autoprover
//! 
//! This module provides SQLite-based caching for proof results to avoid
//! re-solving unchanged goals. The cache key is hash(AST + Lean commit).

use serde::{Deserialize, Serialize};
use sqlx::{sqlite::SqlitePool, Row};
use std::collections::HashMap;
use std::time::SystemTime;
use uuid::Uuid;

use crate::certificate::Certificate;

/// Cache entry for a proof result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheEntry {
    pub certificate: Option<Certificate>,
    pub proof_time_ms: u64,
    pub tactic_used: String,
    pub lean_commit: String,
    pub created_at: SystemTime,
}

/// Cache statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheStats {
    pub total_entries: u64,
    pub successful_entries: u64,
    pub hit_rate: f64,
    pub average_time_ms: u64,
    pub most_used_tactic: String,
}

/// SQLite-based proof cache
pub struct ProofCache {
    pool: SqlitePool,
    config: crate::config::AutoproverConfig,
}

impl ProofCache {
    /// Create a new proof cache
    pub async fn new(config: &crate::config::AutoproverConfig) -> Result<Self, crate::error::AutoproverError> {
        let pool = SqlitePool::connect(&config.cache_database_url).await
            .map_err(|e| crate::error::AutoproverError::CacheError(e.to_string()))?;
        
        // Initialize database schema
        Self::init_schema(&pool).await?;
        
        Ok(Self {
            pool,
            config: config.clone(),
        })
    }

    /// Initialize the database schema
    async fn init_schema(pool: &SqlitePool) -> Result<(), crate::error::AutoproverError> {
        sqlx::query(
            r#"
            CREATE TABLE IF NOT EXISTS proof_cache (
                id TEXT PRIMARY KEY,
                ast_hash TEXT NOT NULL,
                certificate_data TEXT,
                proof_time_ms INTEGER NOT NULL,
                tactic_used TEXT NOT NULL,
                lean_commit TEXT NOT NULL,
                created_at DATETIME NOT NULL,
                updated_at DATETIME NOT NULL
            )
            "#
        )
        .execute(pool)
        .await
        .map_err(|e| crate::error::AutoproverError::CacheError(e.to_string()))?;

        sqlx::query(
            r#"
            CREATE INDEX IF NOT EXISTS idx_proof_cache_ast_hash 
            ON proof_cache(ast_hash)
            "#
        )
        .execute(pool)
        .await
        .map_err(|e| crate::error::AutoproverError::CacheError(e.to_string()))?;

        sqlx::query(
            r#"
            CREATE INDEX IF NOT EXISTS idx_proof_cache_created_at 
            ON proof_cache(created_at)
            "#
        )
        .execute(pool)
        .await
        .map_err(|e| crate::error::AutoproverError::CacheError(e.to_string()))?;

        Ok(())
    }

    /// Get a cached proof result
    pub async fn get(&self, ast_hash: &str) -> Result<Option<CacheEntry>, crate::error::AutoproverError> {
        let row = sqlx::query(
            r#"
            SELECT certificate_data, proof_time_ms, tactic_used, lean_commit, created_at
            FROM proof_cache 
            WHERE ast_hash = ?
            "#
        )
        .bind(ast_hash)
        .fetch_optional(&self.pool)
        .await
        .map_err(|e| crate::error::AutoproverError::CacheError(e.to_string()))?;

        if let Some(row) = row {
            let certificate_data: Option<String> = row.get("certificate_data");
            let certificate = if let Some(data) = certificate_data {
                serde_json::from_str(&data).ok()
            } else {
                None
            };

            let proof_time_ms: u64 = row.get("proof_time_ms");
            let tactic_used: String = row.get("tactic_used");
            let lean_commit: String = row.get("lean_commit");
            let created_at: i64 = row.get("created_at");
            let created_at = SystemTime::UNIX_EPOCH + std::time::Duration::from_secs(created_at as u64);

            Ok(Some(CacheEntry {
                certificate,
                proof_time_ms,
                tactic_used,
                lean_commit,
                created_at,
            }))
        } else {
            Ok(None)
        }
    }

    /// Store a proof result in the cache
    pub async fn put(&self, ast_hash: &str, entry: CacheEntry) -> Result<(), crate::error::AutoproverError> {
        let id = Uuid::new_v4().to_string();
        let certificate_data = if let Some(cert) = &entry.certificate {
            serde_json::to_string(cert).ok()
        } else {
            None
        };

        let created_at = entry.created_at.duration_since(SystemTime::UNIX_EPOCH)
            .unwrap_or_default().as_secs() as i64;
        let updated_at = SystemTime::now().duration_since(SystemTime::UNIX_EPOCH)
            .unwrap_or_default().as_secs() as i64;

        sqlx::query(
            r#"
            INSERT OR REPLACE INTO proof_cache 
            (id, ast_hash, certificate_data, proof_time_ms, tactic_used, lean_commit, created_at, updated_at)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?)
            "#
        )
        .bind(&id)
        .bind(ast_hash)
        .bind(&certificate_data)
        .bind(entry.proof_time_ms as i64)
        .bind(&entry.tactic_used)
        .bind(&entry.lean_commit)
        .bind(created_at)
        .bind(updated_at)
        .execute(&self.pool)
        .await
        .map_err(|e| crate::error::AutoproverError::CacheError(e.to_string()))?;

        Ok(())
    }

    /// Get cache statistics
    pub async fn get_stats(&self) -> Result<CacheStats, crate::error::AutoproverError> {
        // Get total entries
        let total_entries: i64 = sqlx::query("SELECT COUNT(*) FROM proof_cache")
            .fetch_one(&self.pool)
            .await
            .map_err(|e| crate::error::AutoproverError::CacheError(e.to_string()))?
            .get(0);

        // Get successful entries
        let successful_entries: i64 = sqlx::query(
            "SELECT COUNT(*) FROM proof_cache WHERE certificate_data IS NOT NULL"
        )
        .fetch_one(&self.pool)
        .await
        .map_err(|e| crate::error::AutoproverError::CacheError(e.to_string()))?
        .get(0);

        // Get average time
        let avg_time: Option<i64> = sqlx::query("SELECT AVG(proof_time_ms) FROM proof_cache")
            .fetch_one(&self.pool)
            .await
            .map_err(|e| crate::error::AutoproverError::CacheError(e.to_string()))?
            .get(0);

        // Get most used tactic
        let most_used_tactic: Option<String> = sqlx::query(
            r#"
            SELECT tactic_used, COUNT(*) as count 
            FROM proof_cache 
            GROUP BY tactic_used 
            ORDER BY count DESC 
            LIMIT 1
            "#
        )
        .fetch_optional(&self.pool)
        .await
        .map_err(|e| crate::error::AutoproverError::CacheError(e.to_string()))?
        .map(|row| row.get("tactic_used"));

        // Calculate hit rate (simplified - in practice this would track actual hits)
        let hit_rate = if total_entries > 0 {
            successful_entries as f64 / total_entries as f64
        } else {
            0.0
        };

        Ok(CacheStats {
            total_entries: total_entries as u64,
            successful_entries: successful_entries as u64,
            hit_rate,
            average_time_ms: avg_time.unwrap_or(0) as u64,
            most_used_tactic: most_used_tactic.unwrap_or_else(|| "simp".to_string()),
        })
    }

    /// Clear expired cache entries
    pub async fn cleanup(&self) -> Result<u64, crate::error::AutoproverError> {
        let cutoff = SystemTime::now() - std::time::Duration::from_secs(self.config.cache_ttl_seconds);
        let cutoff_secs = cutoff.duration_since(SystemTime::UNIX_EPOCH)
            .unwrap_or_default().as_secs() as i64;

        let result = sqlx::query(
            "DELETE FROM proof_cache WHERE created_at < ?"
        )
        .bind(cutoff_secs)
        .execute(&self.pool)
        .await
        .map_err(|e| crate::error::AutoproverError::CacheError(e.to_string()))?;

        Ok(result.rows_affected())
    }

    /// Get cache size in bytes
    pub async fn size_bytes(&self) -> Result<u64, crate::error::AutoproverError> {
        let row = sqlx::query(
            "SELECT SUM(LENGTH(certificate_data) + LENGTH(ast_hash) + LENGTH(tactic_used) + LENGTH(lean_commit)) as size FROM proof_cache"
        )
        .fetch_one(&self.pool)
        .await
        .map_err(|e| crate::error::AutoproverError::CacheError(e.to_string()))?;

        let size: Option<i64> = row.get("size");
        Ok(size.unwrap_or(0) as u64)
    }

    /// Export cache statistics to JSON
    pub async fn export_stats(&self) -> Result<String, crate::error::AutoproverError> {
        let stats = self.get_stats().await?;
        serde_json::to_string_pretty(&stats)
            .map_err(|e| crate::error::AutoproverError::CacheError(e.to_string()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::AutoproverConfig;

    #[tokio::test]
    async fn test_cache_operations() {
        let config = AutoproverConfig::default();
        let cache = ProofCache::new(&config).await.unwrap();

        // Test put and get
        let entry = CacheEntry {
            certificate: None,
            proof_time_ms: 100,
            tactic_used: "simp".to_string(),
            lean_commit: "test-commit".to_string(),
            created_at: SystemTime::now(),
        };

        cache.put("test-hash", entry.clone()).await.unwrap();
        let retrieved = cache.get("test-hash").await.unwrap();
        assert!(retrieved.is_some());

        // Test stats
        let stats = cache.get_stats().await.unwrap();
        assert!(stats.total_entries > 0);
    }
} 