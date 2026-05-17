use crate::source_commit::{resolve_source_commit, SourceCommitResolution, ZERO_SOURCE_COMMIT};

#[derive(Debug, Clone)]
pub struct CertifyEdgeMetadata {
    pub checker_version: String,
    pub producer_version: String,
    pub source_commit: String,
    pub source_commit_resolution: SourceCommitResolution,
    pub release_mode: bool,
}

impl CertifyEdgeMetadata {
    /// Resolve producer metadata. In release mode, `source_commit` must be a real git SHA
    /// (from `CERTIFYEDGE_SOURCE_COMMIT` or `git rev-parse HEAD` in the CertifyEdge repo).
    pub fn resolve(release_mode: bool) -> Result<Self, String> {
        let resolved = resolve_source_commit(release_mode)?;
        Ok(Self {
            checker_version: env!("CARGO_PKG_VERSION").to_string(),
            producer_version: env!("CARGO_PKG_VERSION").to_string(),
            source_commit: resolved.commit,
            source_commit_resolution: resolved.resolution,
            release_mode,
        })
    }

    pub fn dev_default() -> Self {
        Self::resolve(false).unwrap_or_else(|_| Self {
            checker_version: env!("CARGO_PKG_VERSION").to_string(),
            producer_version: env!("CARGO_PKG_VERSION").to_string(),
            source_commit: ZERO_SOURCE_COMMIT.to_string(),
            source_commit_resolution: SourceCommitResolution::LocalDev,
            release_mode: false,
        })
    }
}
