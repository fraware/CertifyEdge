//! Lean 4 translation for STL specifications

use crate::ast::{STLFormula, STLSpecification, AtomicPredicate, ComparisonOperator, TimeInterval, TimeUnit};
use crate::config::CompilerConfig;
use crate::error::{Lean4Error, Lean4Result};
use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use std::process::Command;
use tempfile::NamedTempFile;
use std::io::Write;

/// Lean 4 output containing the generated code and metadata
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Lean4Output {
    /// Generated Lean 4 code
    pub lean4_code: String,
    /// Proof skeleton with placeholders
    pub proof_skeleton: String,
    /// Import statements
    pub imports: Vec<String>,
    /// Generated theorems
    pub theorems: Vec<Theorem>,
    /// Compilation metadata
    pub metadata: Lean4Metadata,
}

/// Lean 4 theorem definition
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Theorem {
    /// Theorem name
    pub name: String,
    /// Theorem statement
    pub statement: String,
    /// Proof skeleton
    pub proof: String,
    /// Dependencies
    pub dependencies: Vec<String>,
}

/// Lean 4 compilation metadata
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Lean4Metadata {
    /// Compilation time (milliseconds)
    pub compilation_time_ms: u64,
    /// Lean 4 version used
    pub lean4_version: String,
    /// Number of theorems generated
    pub theorem_count: usize,
    /// Compilation success
    pub success: bool,
    /// Error messages if compilation failed
    pub errors: Vec<String>,
}

/// Lean 4 translator that converts STL AST to Lean 4 code
pub struct Lean4Translator {
    config: CompilerConfig,
}

impl Lean4Translator {
    /// Create a new Lean 4 translator
    pub fn new(config: &CompilerConfig) -> Self {
        Self {
            config: config.clone(),
        }
    }

    /// Translate STL specification to Lean 4
    pub async fn translate(&mut self, spec: &STLSpecification) -> Lean4Result<Lean4Output> {
        let start_time = std::time::Instant::now();
        
        // Generate Lean 4 code
        let lean4_code = self.generate_lean4_code(spec)?;
        
        // Generate proof skeleton
        let proof_skeleton = self.generate_proof_skeleton(spec)?;
        
        // Compile and validate
        let metadata = self.compile_and_validate(&lean4_code).await?;
        
        let compilation_time = start_time.elapsed().as_millis() as u64;
        
        Ok(Lean4Output {
            lean4_code,
            proof_skeleton,
            imports: self.generate_imports(),
            theorems: self.generate_theorems(spec),
            metadata: Lean4Metadata {
                compilation_time_ms: compilation_time,
                lean4_version: self.get_lean4_version()?,
                theorem_count: self.count_theorems(spec),
                success: metadata.success,
                errors: metadata.errors,
            },
        })
    }

    /// Generate Lean 4 code from STL specification
    fn generate_lean4_code(&self, spec: &STLSpecification) -> Lean4Result<String> {
        let mut code = String::new();
        
        // Add imports
        code.push_str(&self.generate_imports_code());
        code.push('\n');
        
        // Add namespace
        code.push_str(&format!("namespace {}\n\n", self.sanitize_name(&spec.name)));
        
        // Add variable definitions
        code.push_str(&self.generate_variable_definitions(spec));
        code.push('\n');
        
        // Add STL formula definitions
        code.push_str(&self.generate_formula_definitions(spec));
        code.push('\n');
        
        // Add theorems
        code.push_str(&self.generate_theorems_code(spec));
        code.push('\n');
        
        // Close namespace
        code.push_str("end ");
        code.push_str(&self.sanitize_name(&spec.name));
        
        Ok(code)
    }

    /// Generate proof skeleton
    fn generate_proof_skeleton(&self, spec: &STLSpecification) -> Lean4Result<String> {
        let mut skeleton = String::new();
        
        skeleton.push_str("-- Proof skeleton for STL specification\n");
        skeleton.push_str(&format!("-- Specification: {}\n", spec.name));
        skeleton.push('\n');
        
        // Generate proof placeholders for each theorem
        for theorem in &self.generate_theorems(spec) {
            skeleton.push_str(&format!("theorem {}\n", theorem.name));
            skeleton.push_str(&format!("  : {}\n", theorem.statement));
            skeleton.push_str("  := by\n");
            skeleton.push_str("    -- TODO: Implement proof\n");
            skeleton.push_str("    sorry\n\n");
        }
        
        Ok(skeleton)
    }

    /// Generate imports code
    fn generate_imports_code(&self) -> String {
        let mut imports = vec![
            "import Mathlib.Data.Real.Basic".to_string(),
            "import Mathlib.Data.Real.Sqrt".to_string(),
            "import Mathlib.Algebra.Order.Ring".to_string(),
            "import Mathlib.Topology.Instances.Real".to_string(),
            "import Mathlib.Analysis.NormedSpace.Basic".to_string(),
        ];
        
        imports.join("\n")
    }

    /// Generate variable definitions
    fn generate_variable_definitions(&self, spec: &STLSpecification) -> String {
        let mut code = String::new();
        let variables = spec.formula.variables();
        
        code.push_str("-- Variable definitions\n");
        for var in variables {
            code.push_str(&format!("variable ({} : ℝ)\n", self.sanitize_name(&var)));
        }
        code.push('\n');
        
        code
    }

    /// Generate formula definitions
    fn generate_formula_definitions(&self, spec: &STLSpecification) -> String {
        let mut code = String::new();
        
        code.push_str("-- STL formula definitions\n");
        code.push_str(&self.translate_formula(&spec.formula, "φ"));
        code.push('\n');
        
        code
    }

    /// Translate STL formula to Lean 4
    fn translate_formula(&self, formula: &STLFormula, name: &str) -> String {
        match formula {
            STLFormula::Atomic(pred) => self.translate_atomic_predicate(pred, name),
            STLFormula::And(left, right) => self.translate_binary_op("∧", left, right, name),
            STLFormula::Or(left, right) => self.translate_binary_op("∨", left, right, name),
            STLFormula::Not(formula) => self.translate_unary_op("¬", formula, name),
            STLFormula::Always(interval, formula) => self.translate_temporal_op("□", interval, formula, name),
            STLFormula::Eventually(interval, formula) => self.translate_temporal_op("◇", interval, formula, name),
            STLFormula::Until(interval, left, right) => self.translate_until(interval, left, right, name),
            STLFormula::Next(formula) => self.translate_unary_op("○", formula, name),
            STLFormula::Implies(left, right) => self.translate_binary_op("→", left, right, name),
            STLFormula::Equiv(left, right) => self.translate_binary_op("↔", left, right, name),
            _ => format!("-- Unsupported formula: {:?}", formula),
        }
    }

    /// Translate atomic predicate
    fn translate_atomic_predicate(&self, pred: &AtomicPredicate, name: &str) -> String {
        let var = self.sanitize_name(&pred.variable);
        let op = self.translate_comparison_operator(&pred.operator);
        let threshold = pred.threshold;
        
        format!("def {} : Prop := {} {} {}", name, var, op, threshold)
    }

    /// Translate comparison operator
    fn translate_comparison_operator(&self, op: &ComparisonOperator) -> &'static str {
        match op {
            ComparisonOperator::Equal => "=",
            ComparisonOperator::NotEqual => "≠",
            ComparisonOperator::GreaterThan => ">",
            ComparisonOperator::GreaterEqual => "≥",
            ComparisonOperator::LessThan => "<",
            ComparisonOperator::LessEqual => "≤",
        }
    }

    /// Translate binary operator
    fn translate_binary_op(&self, op: &str, left: &STLFormula, right: &STLFormula, name: &str) -> String {
        let left_name = format!("{}_left", name);
        let right_name = format!("{}_right", name);
        
        let left_def = self.translate_formula(left, &left_name);
        let right_def = self.translate_formula(right, &right_name);
        
        format!("{}\n{}\ndef {} : Prop := {} {} {}", 
                left_def, right_def, name, left_name, op, right_name)
    }

    /// Translate unary operator
    fn translate_unary_op(&self, op: &str, formula: &STLFormula, name: &str) -> String {
        let inner_name = format!("{}_inner", name);
        let inner_def = self.translate_formula(formula, &inner_name);
        
        format!("{}\ndef {} : Prop := {} {}", inner_def, name, op, inner_name)
    }

    /// Translate temporal operator
    fn translate_temporal_op(&self, op: &str, interval: &TimeInterval, formula: &STLFormula, name: &str) -> String {
        let inner_name = format!("{}_inner", name);
        let inner_def = self.translate_formula(formula, &inner_name);
        let interval_def = self.translate_time_interval(interval);
        
        format!("{}\ndef {} : Prop := {} {} {}", 
                inner_def, name, op, interval_def, inner_name)
    }

    /// Translate until operator
    fn translate_until(&self, interval: &TimeInterval, left: &STLFormula, right: &STLFormula, name: &str) -> String {
        let left_name = format!("{}_left", name);
        let right_name = format!("{}_right", name);
        let left_def = self.translate_formula(left, &left_name);
        let right_def = self.translate_formula(right, &right_name);
        let interval_def = self.translate_time_interval(interval);
        
        format!("{}\n{}\ndef {} : Prop := {} U {} {}", 
                left_def, right_def, name, left_name, interval_def, right_name)
    }

    /// Translate time interval
    fn translate_time_interval(&self, interval: &TimeInterval) -> String {
        let (start, end) = interval.to_seconds();
        let start_str = start.map(|s| s.to_string()).unwrap_or_else(|| "0".to_string());
        let end_str = end.map(|e| e.to_string()).unwrap_or_else(|| "∞".to_string());
        
        format!("[{}, {}]", start_str, end_str)
    }

    /// Generate theorems
    fn generate_theorems(&self, spec: &STLSpecification) -> Vec<Theorem> {
        let mut theorems = Vec::new();
        
        // Main specification theorem
        theorems.push(Theorem {
            name: format!("{}_spec", self.sanitize_name(&spec.name)),
            statement: format!("φ : Prop"),
            proof: "sorry".to_string(),
            dependencies: vec![],
        });
        
        // Safety property theorem
        theorems.push(Theorem {
            name: format!("{}_safety", self.sanitize_name(&spec.name)),
            statement: "∀ t : ℝ, φ t → φ (t + 1)".to_string(),
            proof: "sorry".to_string(),
            dependencies: vec![format!("{}_spec", self.sanitize_name(&spec.name))],
        });
        
        theorems
    }

    /// Generate theorems code
    fn generate_theorems_code(&self, spec: &STLSpecification) -> String {
        let mut code = String::new();
        
        code.push_str("-- Theorems\n");
        for theorem in &self.generate_theorems(spec) {
            code.push_str(&format!("theorem {}\n", theorem.name));
            code.push_str(&format!("  : {}\n", theorem.statement));
            code.push_str("  := sorry\n\n");
        }
        
        code
    }

    /// Generate imports list
    fn generate_imports(&self) -> Vec<String> {
        vec![
            "Mathlib.Data.Real.Basic".to_string(),
            "Mathlib.Data.Real.Sqrt".to_string(),
            "Mathlib.Algebra.Order.Ring".to_string(),
            "Mathlib.Topology.Instances.Real".to_string(),
            "Mathlib.Analysis.NormedSpace.Basic".to_string(),
        ]
    }

    /// Count theorems in specification
    fn count_theorems(&self, _spec: &STLSpecification) -> usize {
        2 // spec and safety theorems
    }

    /// Sanitize name for Lean 4
    fn sanitize_name(&self, name: &str) -> String {
        name.replace('-', "_")
            .replace('.', "_")
            .replace(' ', "_")
            .chars()
            .filter(|c| c.is_alphanumeric() || *c == '_')
            .collect()
    }

    /// Compile and validate Lean 4 code
    async fn compile_and_validate(&self, code: &str) -> Lean4Result<Lean4Metadata> {
        let lean4_path = self.config.get_lean4_path()?;
        
        // Create temporary file
        let mut temp_file = NamedTempFile::new()
            .map_err(|e| Lean4Error::CompilationFailed { output: e.to_string() })?;
        
        temp_file.write_all(code.as_bytes())
            .map_err(|e| Lean4Error::CompilationFailed { output: e.to_string() })?;
        
        // Run Lean 4 check
        let output = Command::new(lean4_path)
            .arg("--check")
            .arg(temp_file.path())
            .output()
            .map_err(|e| Lean4Error::CompilationFailed { output: e.to_string() })?;
        
        let success = output.status.success();
        let errors = if success {
            vec![]
        } else {
            String::from_utf8_lossy(&output.stderr)
                .lines()
                .map(|s| s.to_string())
                .collect()
        };
        
        Ok(Lean4Metadata {
            compilation_time_ms: 0, // Will be set by caller
            lean4_version: self.get_lean4_version()?,
            theorem_count: 0, // Will be set by caller
            success,
            errors,
        })
    }

    /// Get Lean 4 version
    fn get_lean4_version(&self) -> Lean4Result<String> {
        let lean4_path = self.config.get_lean4_path()?;
        
        let output = Command::new(lean4_path)
            .arg("--version")
            .output()
            .map_err(|e| Lean4Error::Lean4NotFound { path: lean4_path.to_string_lossy().to_string() })?;
        
        let version = String::from_utf8_lossy(&output.stdout)
            .lines()
            .next()
            .unwrap_or("unknown")
            .to_string();
        
        Ok(version)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{STLSpecification, STLFormula, AtomicPredicate, ComparisonOperator};

    #[test]
    fn test_sanitize_name() {
        let translator = Lean4Translator::new(&CompilerConfig::default());
        assert_eq!(translator.sanitize_name("test-name"), "test_name");
        assert_eq!(translator.sanitize_name("test.name"), "test_name");
        assert_eq!(translator.sanitize_name("test name"), "test_name");
    }

    #[test]
    fn test_translate_comparison_operator() {
        let translator = Lean4Translator::new(&CompilerConfig::default());
        assert_eq!(translator.translate_comparison_operator(&ComparisonOperator::GreaterThan), ">");
        assert_eq!(translator.translate_comparison_operator(&ComparisonOperator::LessThan), "<");
    }

    #[test]
    fn test_generate_theorems() {
        let spec = STLSpecification {
            name: "test-spec".to_string(),
            description: None,
            formula: STLFormula::Atomic(AtomicPredicate {
                variable: "voltage".to_string(),
                operator: ComparisonOperator::GreaterThan,
                threshold: 220.0,
                tolerance: None,
            }),
            parameters: vec![],
            constraints: vec![],
            metadata: std::collections::HashMap::new(),
        };
        
        let translator = Lean4Translator::new(&CompilerConfig::default());
        let theorems = translator.generate_theorems(&spec);
        
        assert_eq!(theorems.len(), 2);
        assert!(theorems[0].name.contains("test_spec"));
        assert!(theorems[1].name.contains("test_spec"));
    }
} 