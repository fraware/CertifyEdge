//! Configuration for the STL compiler

use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use crate::error::{ConfigError, ConfigResult};

/// Main configuration for the STL compiler
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompilerConfig {
    /// Lean 4 configuration
    pub lean4: Lean4Config,
    /// SMT solver configuration
    pub smt: SMTConfig,
    /// Compilation settings
    pub compilation: CompilationConfig,
    /// Performance settings
    pub performance: PerformanceConfig,
    /// Output settings
    pub output: OutputConfig,
}

/// Lean 4 specific configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Lean4Config {
    /// Path to Lean 4 executable
    pub lean4_path: Option<PathBuf>,
    /// Lean 4 version
    pub version: String,
    /// Timeout for Lean 4 operations (milliseconds)
    pub timeout_ms: u64,
    /// Memory limit for Lean 4 (MB)
    pub memory_limit_mb: u64,
    /// Enable native compilation
    pub enable_native: bool,
    /// Additional Lean 4 flags
    pub additional_flags: Vec<String>,
    /// Lean 4 library paths
    pub library_paths: Vec<PathBuf>,
}

/// SMT solver configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SMTConfig {
    /// Z3 configuration
    pub z3: Z3Config,
    /// CVC5 configuration
    pub cvc5: CVC5Config,
    /// Default solver to use
    pub default_solver: String,
    /// Enable differential testing
    pub enable_differential_testing: bool,
    /// Timeout for SMT operations (milliseconds)
    pub timeout_ms: u64,
}

/// Z3 solver configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Z3Config {
    /// Path to Z3 executable
    pub z3_path: Option<PathBuf>,
    /// Z3 version
    pub version: String,
    /// Z3 specific flags
    pub flags: Vec<String>,
    /// Enable Z3
    pub enabled: bool,
}

/// CVC5 solver configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CVC5Config {
    /// Path to CVC5 executable
    pub cvc5_path: Option<PathBuf>,
    /// CVC5 version
    pub version: String,
    /// CVC5 specific flags
    pub flags: Vec<String>,
    /// Enable CVC5
    pub enabled: bool,
}

/// Compilation configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompilationConfig {
    /// Enable optimization
    pub optimize: bool,
    /// Enable debug information
    pub debug: bool,
    /// Enable warnings
    pub warnings: bool,
    /// Enable strict mode
    pub strict: bool,
    /// Enable validation
    pub validate: bool,
    /// Output format
    pub output_format: OutputFormat,
}

/// Performance configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceConfig {
    /// Maximum compilation time (milliseconds)
    pub max_compilation_time_ms: u64,
    /// Maximum memory usage (MB)
    pub max_memory_mb: u64,
    /// Enable parallel compilation
    pub parallel: bool,
    /// Number of parallel threads
    pub num_threads: usize,
    /// Enable caching
    pub enable_cache: bool,
    /// Cache directory
    pub cache_dir: Option<PathBuf>,
}

/// Output configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OutputConfig {
    /// Output directory
    pub output_dir: PathBuf,
    /// Generate Lean 4 files
    pub generate_lean4: bool,
    /// Generate SMT-LIB files
    pub generate_smt: bool,
    /// Generate documentation
    pub generate_docs: bool,
    /// Generate test files
    pub generate_tests: bool,
    /// Pretty print output
    pub pretty_print: bool,
}

/// Output format options
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum OutputFormat {
    /// Lean 4 format
    Lean4,
    /// SMT-LIB format
    SMTLib,
    /// Both formats
    Both,
}

impl Default for CompilerConfig {
    fn default() -> Self {
        Self {
            lean4: Lean4Config::default(),
            smt: SMTConfig::default(),
            compilation: CompilationConfig::default(),
            performance: PerformanceConfig::default(),
            output: OutputConfig::default(),
        }
    }
}

impl Default for Lean4Config {
    fn default() -> Self {
        Self {
            lean4_path: None,
            version: "4.0.0".to_string(),
            timeout_ms: 30000, // 30 seconds
            memory_limit_mb: 1024, // 1GB
            enable_native: true,
            additional_flags: vec![],
            library_paths: vec![],
        }
    }
}

impl Default for SMTConfig {
    fn default() -> Self {
        Self {
            z3: Z3Config::default(),
            cvc5: CVC5Config::default(),
            default_solver: "z3".to_string(),
            enable_differential_testing: true,
            timeout_ms: 10000, // 10 seconds
        }
    }
}

impl Default for Z3Config {
    fn default() -> Self {
        Self {
            z3_path: None,
            version: "4.13.0".to_string(),
            flags: vec!["-smt2".to_string(), "-in".to_string()],
            enabled: true,
        }
    }
}

impl Default for CVC5Config {
    fn default() -> Self {
        Self {
            cvc5_path: None,
            version: "1.2.0".to_string(),
            flags: vec!["--lang=smt2".to_string(), "--incremental".to_string()],
            enabled: true,
        }
    }
}

impl Default for CompilationConfig {
    fn default() -> Self {
        Self {
            optimize: true,
            debug: false,
            warnings: true,
            strict: true,
            validate: true,
            output_format: OutputFormat::Both,
        }
    }
}

impl Default for PerformanceConfig {
    fn default() -> Self {
        Self {
            max_compilation_time_ms: 60000, // 1 minute
            max_memory_mb: 2048, // 2GB
            parallel: true,
            num_threads: num_cpus::get(),
            enable_cache: true,
            cache_dir: None,
        }
    }
}

impl Default for OutputConfig {
    fn default() -> Self {
        Self {
            output_dir: PathBuf::from("output"),
            generate_lean4: true,
            generate_smt: true,
            generate_docs: true,
            generate_tests: true,
            pretty_print: true,
        }
    }
}

impl CompilerConfig {
    /// Load configuration from file
    pub fn from_file(path: &PathBuf) -> ConfigResult<Self> {
        let content = std::fs::read_to_string(path)
            .map_err(|e| ConfigError::FileNotFound { path: path.to_string_lossy().to_string() })?;
        
        let config: CompilerConfig = serde_json::from_str(&content)
            .map_err(|e| ConfigError::InvalidFormat { message: e.to_string() })?;
        
        config.validate()?;
        Ok(config)
    }

    /// Save configuration to file
    pub fn save_to_file(&self, path: &PathBuf) -> ConfigResult<()> {
        let content = serde_json::to_string_pretty(self)
            .map_err(|e| ConfigError::InvalidFormat { message: e.to_string() })?;
        
        std::fs::write(path, content)
            .map_err(|e| ConfigError::InvalidFormat { message: e.to_string() })?;
        
        Ok(())
    }

    /// Validate configuration
    pub fn validate(&self) -> ConfigResult<()> {
        // Validate Lean 4 configuration
        if let Some(lean4_path) = &self.lean4.lean4_path {
            if !lean4_path.exists() {
                return Err(ConfigError::InvalidValue {
                    key: "lean4.lean4_path".to_string(),
                    value: lean4_path.to_string_lossy().to_string(),
                });
            }
        }

        // Validate SMT solver configuration
        if let Some(z3_path) = &self.smt.z3.z3_path {
            if !z3_path.exists() {
                return Err(ConfigError::InvalidValue {
                    key: "smt.z3.z3_path".to_string(),
                    value: z3_path.to_string_lossy().to_string(),
                });
            }
        }

        if let Some(cvc5_path) = &self.smt.cvc5.cvc5_path {
            if !cvc5_path.exists() {
                return Err(ConfigError::InvalidValue {
                    key: "smt.cvc5.cvc5_path".to_string(),
                    value: cvc5_path.to_string_lossy().to_string(),
                });
            }
        }

        // Validate performance configuration
        if self.performance.num_threads == 0 {
            return Err(ConfigError::InvalidValue {
                key: "performance.num_threads".to_string(),
                value: "0".to_string(),
            });
        }

        // Validate output configuration
        if !self.output.output_dir.exists() {
            std::fs::create_dir_all(&self.output.output_dir)
                .map_err(|e| ConfigError::InvalidValue {
                    key: "output.output_dir".to_string(),
                    value: self.output.output_dir.to_string_lossy().to_string(),
                })?;
        }

        Ok(())
    }

    /// Get Lean 4 path, trying to find it automatically if not specified
    pub fn get_lean4_path(&self) -> ConfigResult<PathBuf> {
        if let Some(path) = &self.lean4.lean4_path {
            Ok(path.clone())
        } else {
            // Try to find Lean 4 in PATH
            which::which("lean")
                .map_err(|_| ConfigError::MissingKey { key: "lean4.lean4_path".to_string() })
        }
    }

    /// Get Z3 path, trying to find it automatically if not specified
    pub fn get_z3_path(&self) -> ConfigResult<PathBuf> {
        if let Some(path) = &self.smt.z3.z3_path {
            Ok(path.clone())
        } else {
            // Try to find Z3 in PATH
            which::which("z3")
                .map_err(|_| ConfigError::MissingKey { key: "smt.z3.z3_path".to_string() })
        }
    }

    /// Get CVC5 path, trying to find it automatically if not specified
    pub fn get_cvc5_path(&self) -> ConfigResult<PathBuf> {
        if let Some(path) = &self.smt.cvc5.cvc5_path {
            Ok(path.clone())
        } else {
            // Try to find CVC5 in PATH
            which::which("cvc5")
                .map_err(|_| ConfigError::MissingKey { key: "smt.cvc5.cvc5_path".to_string() })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn test_default_config() {
        let config = CompilerConfig::default();
        assert_eq!(config.lean4.version, "4.0.0");
        assert_eq!(config.smt.default_solver, "z3");
        assert!(config.compilation.optimize);
        assert!(config.performance.parallel);
    }

    #[test]
    fn test_config_validation() {
        let config = CompilerConfig::default();
        assert!(config.validate().is_ok());
    }

    #[test]
    fn test_config_serialization() {
        let config = CompilerConfig::default();
        let json = serde_json::to_string(&config).unwrap();
        let deserialized: CompilerConfig = serde_json::from_str(&json).unwrap();
        assert_eq!(config.lean4.version, deserialized.lean4.version);
    }

    #[test]
    fn test_config_file_operations() {
        let temp_dir = tempdir().unwrap();
        let config_path = temp_dir.path().join("config.json");
        
        let config = CompilerConfig::default();
        config.save_to_file(&config_path).unwrap();
        
        let loaded_config = CompilerConfig::from_file(&config_path).unwrap();
        assert_eq!(config.lean4.version, loaded_config.lean4.version);
    }
} 