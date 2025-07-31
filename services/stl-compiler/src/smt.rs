//! SMT-LIB translation for STL specifications

use crate::ast::{STLFormula, STLSpecification, AtomicPredicate, ComparisonOperator, TimeInterval, TimeUnit};
use crate::config::CompilerConfig;
use crate::error::{SMTError, SMTResult};
use serde::{Deserialize, Serialize};
use std::process::Command;
use tempfile::NamedTempFile;
use std::io::Write;

/// SMT-LIB output containing the generated expressions and metadata
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SMTOutput {
    /// Generated SMT-LIB code
    pub smt_lib_code: String,
    /// Z3-specific output
    pub z3_output: SolverOutput,
    /// CVC5-specific output
    pub cvc5_output: SolverOutput,
    /// Metadata
    pub metadata: SMTMetadata,
}

/// Solver-specific output
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SolverOutput {
    /// Solver name
    pub solver_name: String,
    /// SMT-LIB script
    pub script: String,
    /// Result (sat/unsat/unknown)
    pub result: SMTResult,
    /// Model (if sat)
    pub model: Option<String>,
    /// Unsat core (if unsat)
    pub unsat_core: Option<Vec<String>>,
    /// Execution time (milliseconds)
    pub execution_time_ms: u64,
    /// Error messages
    pub errors: Vec<String>,
}

/// SMT result type
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SMTResult {
    Sat,
    Unsat,
    Unknown,
    Error,
}

/// SMT metadata
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SMTMetadata {
    /// Total execution time (milliseconds)
    pub total_time_ms: u64,
    /// Z3 version
    pub z3_version: String,
    /// CVC5 version
    pub cvc5_version: String,
    /// Number of assertions
    pub assertion_count: usize,
    /// Success
    pub success: bool,
}

/// SMT translator that converts STL AST to SMT-LIB
pub struct SMTTranslator {
    config: CompilerConfig,
}

impl SMTTranslator {
    /// Create a new SMT translator
    pub fn new(config: &CompilerConfig) -> Self {
        Self {
            config: config.clone(),
        }
    }

    /// Translate STL specification to SMT-LIB
    pub async fn translate(&mut self, spec: &STLSpecification) -> SMTResult<SMTOutput> {
        let start_time = std::time::Instant::now();
        
        // Generate SMT-LIB code
        let smt_lib_code = self.generate_smt_lib_code(spec)?;
        
        // Execute with Z3
        let z3_output = self.execute_with_z3(&smt_lib_code).await?;
        
        // Execute with CVC5
        let cvc5_output = self.execute_with_cvc5(&smt_lib_code).await?;
        
        let total_time = start_time.elapsed().as_millis() as u64;
        
        Ok(SMTOutput {
            smt_lib_code,
            z3_output,
            cvc5_output,
            metadata: SMTMetadata {
                total_time_ms: total_time,
                z3_version: self.get_z3_version()?,
                cvc5_version: self.get_cvc5_version()?,
                assertion_count: self.count_assertions(spec),
                success: z3_output.result != SMTResult::Error && cvc5_output.result != SMTResult::Error,
            },
        })
    }

    /// Generate SMT-LIB code from STL specification
    fn generate_smt_lib_code(&self, spec: &STLSpecification) -> SMTResult<String> {
        let mut script = String::new();
        
        // Set logic
        script.push_str("(set-logic QF_LRA)\n");
        script.push_str("(set-option :produce-models true)\n");
        script.push_str("(set-option :produce-unsat-cores true)\n\n");
        
        // Declare variables
        script.push_str(&self.generate_variable_declarations(spec));
        script.push('\n');
        
        // Generate assertions
        script.push_str(&self.generate_assertions(spec));
        script.push('\n');
        
        // Check satisfiability
        script.push_str("(check-sat)\n");
        script.push_str("(get-model)\n");
        script.push_str("(get-unsat-core)\n");
        
        Ok(script)
    }

    /// Generate variable declarations
    fn generate_variable_declarations(&self, spec: &STLSpecification) -> String {
        let mut declarations = String::new();
        let variables = spec.formula.variables();
        
        declarations.push_str("; Variable declarations\n");
        for var in variables {
            declarations.push_str(&format!("(declare-fun {} () Real)\n", self.sanitize_name(&var)));
        }
        
        declarations
    }

    /// Generate assertions from STL formula
    fn generate_assertions(&self, spec: &STLSpecification) -> String {
        let mut assertions = String::new();
        
        assertions.push_str("; STL formula assertions\n");
        let formula_assertion = self.translate_formula_to_smt(&spec.formula);
        assertions.push_str(&format!("(assert {})\n", formula_assertion));
        
        // Add constraints
        for constraint in &spec.constraints {
            assertions.push_str(&format!("; Constraint: {}\n", constraint.name));
            assertions.push_str(&format!("(assert {})\n", self.translate_constraint(constraint)));
        }
        
        assertions
    }

    /// Translate STL formula to SMT-LIB
    fn translate_formula_to_smt(&self, formula: &STLFormula) -> String {
        match formula {
            STLFormula::Atomic(pred) => self.translate_atomic_predicate(pred),
            STLFormula::And(left, right) => self.translate_binary_op("and", left, right),
            STLFormula::Or(left, right) => self.translate_binary_op("or", left, right),
            STLFormula::Not(formula) => self.translate_unary_op("not", formula),
            STLFormula::Always(interval, formula) => self.translate_temporal_op("always", interval, formula),
            STLFormula::Eventually(interval, formula) => self.translate_temporal_op("eventually", interval, formula),
            STLFormula::Until(interval, left, right) => self.translate_until(interval, left, right),
            STLFormula::Next(formula) => self.translate_unary_op("next", formula),
            STLFormula::Implies(left, right) => self.translate_binary_op("=>", left, right),
            STLFormula::Equiv(left, right) => self.translate_binary_op("=", left, right),
            _ => format!("; Unsupported formula: {:?}", formula),
        }
    }

    /// Translate atomic predicate
    fn translate_atomic_predicate(&self, pred: &AtomicPredicate) -> String {
        let var = self.sanitize_name(&pred.variable);
        let op = self.translate_comparison_operator(&pred.operator);
        let threshold = pred.threshold;
        
        format!("({} {} {})", op, var, threshold)
    }

    /// Translate comparison operator
    fn translate_comparison_operator(&self, op: &ComparisonOperator) -> &'static str {
        match op {
            ComparisonOperator::Equal => "=",
            ComparisonOperator::NotEqual => "distinct",
            ComparisonOperator::GreaterThan => ">",
            ComparisonOperator::GreaterEqual => ">=",
            ComparisonOperator::LessThan => "<",
            ComparisonOperator::LessEqual => "<=",
        }
    }

    /// Translate binary operator
    fn translate_binary_op(&self, op: &str, left: &STLFormula, right: &STLFormula) -> String {
        let left_expr = self.translate_formula_to_smt(left);
        let right_expr = self.translate_formula_to_smt(right);
        
        format!("({} {} {})", op, left_expr, right_expr)
    }

    /// Translate unary operator
    fn translate_unary_op(&self, op: &str, formula: &STLFormula) -> String {
        let expr = self.translate_formula_to_smt(formula);
        
        format!("({} {})", op, expr)
    }

    /// Translate temporal operator
    fn translate_temporal_op(&self, op: &str, interval: &TimeInterval, formula: &STLFormula) -> String {
        let expr = self.translate_formula_to_smt(formula);
        let interval_expr = self.translate_time_interval(interval);
        
        // For now, we'll use a simplified temporal encoding
        // In practice, this would need a more sophisticated temporal logic encoding
        match op {
            "always" => format!("(forall ((t Real)) (=> (and (>= t {}) (<= t {})) {}))", 
                               interval_expr.0, interval_expr.1, expr),
            "eventually" => format!("(exists ((t Real)) (and (>= t {}) (<= t {}) {}))", 
                                   interval_expr.0, interval_expr.1, expr),
            _ => expr,
        }
    }

    /// Translate until operator
    fn translate_until(&self, interval: &TimeInterval, left: &STLFormula, right: &STLFormula) -> String {
        let left_expr = self.translate_formula_to_smt(left);
        let right_expr = self.translate_formula_to_smt(right);
        let interval_expr = self.translate_time_interval(interval);
        
        // Simplified until encoding
        format!("(exists ((t Real)) (and (>= t {}) (<= t {}) (and {} {})))", 
                interval_expr.0, interval_expr.1, left_expr, right_expr)
    }

    /// Translate time interval
    fn translate_time_interval(&self, interval: &TimeInterval) -> (f64, f64) {
        let (start, end) = interval.to_seconds();
        let start_val = start.unwrap_or(0.0);
        let end_val = end.unwrap_or(f64::INFINITY);
        (start_val, end_val)
    }

    /// Translate constraint
    fn translate_constraint(&self, constraint: &crate::ast::Constraint) -> String {
        // For now, return the constraint expression as-is
        // In practice, this would need proper parsing and translation
        format!("(= {} 0)", constraint.expression)
    }

    /// Execute SMT-LIB script with Z3
    async fn execute_with_z3(&self, script: &str) -> SMTResult<SolverOutput> {
        let start_time = std::time::Instant::now();
        
        let z3_path = self.config.get_z3_path()?;
        
        // Create temporary file
        let mut temp_file = NamedTempFile::new()
            .map_err(|e| SMTError::SolverExecutionFailed { output: e.to_string() })?;
        
        temp_file.write_all(script.as_bytes())
            .map_err(|e| SMTError::SolverExecutionFailed { output: e.to_string() })?;
        
        // Execute Z3
        let output = Command::new(z3_path)
            .args(&["-smt2", "-in"])
            .stdin(temp_file.reopen().unwrap())
            .output()
            .map_err(|e| SMTError::SolverExecutionFailed { output: e.to_string() })?;
        
        let execution_time = start_time.elapsed().as_millis() as u64;
        let output_str = String::from_utf8_lossy(&output.stdout);
        let error_str = String::from_utf8_lossy(&output.stderr);
        
        let result = self.parse_smt_result(&output_str);
        let model = if result == SMTResult::Sat {
            Some(output_str.lines().filter(|l| l.starts_with("(model")).collect::<Vec<_>>().join("\n"))
        } else {
            None
        };
        
        let unsat_core = if result == SMTResult::Unsat {
            Some(output_str.lines().filter(|l| l.starts_with("(")).map(|s| s.to_string()).collect())
        } else {
            None
        };
        
        let errors = if !error_str.is_empty() {
            error_str.lines().map(|s| s.to_string()).collect()
        } else {
            vec![]
        };
        
        Ok(SolverOutput {
            solver_name: "z3".to_string(),
            script: script.to_string(),
            result,
            model,
            unsat_core,
            execution_time_ms: execution_time,
            errors,
        })
    }

    /// Execute SMT-LIB script with CVC5
    async fn execute_with_cvc5(&self, script: &str) -> SMTResult<SolverOutput> {
        let start_time = std::time::Instant::now();
        
        let cvc5_path = self.config.get_cvc5_path()?;
        
        // Create temporary file
        let mut temp_file = NamedTempFile::new()
            .map_err(|e| SMTError::SolverExecutionFailed { output: e.to_string() })?;
        
        temp_file.write_all(script.as_bytes())
            .map_err(|e| SMTError::SolverExecutionFailed { output: e.to_string() })?;
        
        // Execute CVC5
        let output = Command::new(cvc5_path)
            .args(&["--lang=smt2", "--incremental"])
            .stdin(temp_file.reopen().unwrap())
            .output()
            .map_err(|e| SMTError::SolverExecutionFailed { output: e.to_string() })?;
        
        let execution_time = start_time.elapsed().as_millis() as u64;
        let output_str = String::from_utf8_lossy(&output.stdout);
        let error_str = String::from_utf8_lossy(&output.stderr);
        
        let result = self.parse_smt_result(&output_str);
        let model = if result == SMTResult::Sat {
            Some(output_str.lines().filter(|l| l.starts_with("(model")).collect::<Vec<_>>().join("\n"))
        } else {
            None
        };
        
        let unsat_core = if result == SMTResult::Unsat {
            Some(output_str.lines().filter(|l| l.starts_with("(")).map(|s| s.to_string()).collect())
        } else {
            None
        };
        
        let errors = if !error_str.is_empty() {
            error_str.lines().map(|s| s.to_string()).collect()
        } else {
            vec![]
        };
        
        Ok(SolverOutput {
            solver_name: "cvc5".to_string(),
            script: script.to_string(),
            result,
            model,
            unsat_core,
            execution_time_ms: execution_time,
            errors,
        })
    }

    /// Parse SMT solver result
    fn parse_smt_result(&self, output: &str) -> SMTResult {
        let output_lower = output.to_lowercase();
        if output_lower.contains("sat") {
            SMTResult::Sat
        } else if output_lower.contains("unsat") {
            SMTResult::Unsat
        } else if output_lower.contains("unknown") {
            SMTResult::Unknown
        } else {
            SMTResult::Error
        }
    }

    /// Count assertions in specification
    fn count_assertions(&self, spec: &STLSpecification) -> usize {
        1 + spec.constraints.len() // 1 for main formula + constraints
    }

    /// Sanitize name for SMT-LIB
    fn sanitize_name(&self, name: &str) -> String {
        name.replace('-', "_")
            .replace('.', "_")
            .replace(' ', "_")
            .chars()
            .filter(|c| c.is_alphanumeric() || *c == '_')
            .collect()
    }

    /// Get Z3 version
    fn get_z3_version(&self) -> SMTResult<String> {
        let z3_path = self.config.get_z3_path()?;
        
        let output = Command::new(z3_path)
            .arg("--version")
            .output()
            .map_err(|e| SMTError::SolverNotFound { solver: "z3".to_string() })?;
        
        let version = String::from_utf8_lossy(&output.stdout)
            .lines()
            .next()
            .unwrap_or("unknown")
            .to_string();
        
        Ok(version)
    }

    /// Get CVC5 version
    fn get_cvc5_version(&self) -> SMTResult<String> {
        let cvc5_path = self.config.get_cvc5_path()?;
        
        let output = Command::new(cvc5_path)
            .arg("--version")
            .output()
            .map_err(|e| SMTError::SolverNotFound { solver: "cvc5".to_string() })?;
        
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
        let translator = SMTTranslator::new(&CompilerConfig::default());
        assert_eq!(translator.sanitize_name("test-name"), "test_name");
        assert_eq!(translator.sanitize_name("test.name"), "test_name");
        assert_eq!(translator.sanitize_name("test name"), "test_name");
    }

    #[test]
    fn test_translate_comparison_operator() {
        let translator = SMTTranslator::new(&CompilerConfig::default());
        assert_eq!(translator.translate_comparison_operator(&ComparisonOperator::GreaterThan), ">");
        assert_eq!(translator.translate_comparison_operator(&ComparisonOperator::LessThan), "<");
    }

    #[test]
    fn test_translate_atomic_predicate() {
        let translator = SMTTranslator::new(&CompilerConfig::default());
        let pred = AtomicPredicate {
            variable: "voltage".to_string(),
            operator: ComparisonOperator::GreaterThan,
            threshold: 220.0,
            tolerance: None,
        };
        
        let result = translator.translate_atomic_predicate(&pred);
        assert!(result.contains("voltage"));
        assert!(result.contains(">"));
        assert!(result.contains("220"));
    }

    #[test]
    fn test_parse_smt_result() {
        let translator = SMTTranslator::new(&CompilerConfig::default());
        
        assert!(matches!(translator.parse_smt_result("sat"), SMTResult::Sat));
        assert!(matches!(translator.parse_smt_result("unsat"), SMTResult::Unsat));
        assert!(matches!(translator.parse_smt_result("unknown"), SMTResult::Unknown));
        assert!(matches!(translator.parse_smt_result("error"), SMTResult::Error));
    }
} 