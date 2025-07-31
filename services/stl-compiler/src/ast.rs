//! Abstract Syntax Tree (AST) for Signal Temporal Logic (STL) specifications

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// STL Specification - the root AST node
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct STLSpecification {
    pub name: String,
    pub description: Option<String>,
    pub formula: STLFormula,
    pub parameters: Vec<Parameter>,
    pub constraints: Vec<Constraint>,
    pub metadata: HashMap<String, String>,
}

/// STL Formula - represents a temporal logic expression
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum STLFormula {
    /// Atomic predicate: variable comparison with threshold
    Atomic(AtomicPredicate),
    /// Logical AND: φ ∧ ψ
    And(Box<STLFormula>, Box<STLFormula>),
    /// Logical OR: φ ∨ ψ
    Or(Box<STLFormula>, Box<STLFormula>),
    /// Logical NOT: ¬φ
    Not(Box<STLFormula>),
    /// Temporal AND: φ ∧ ψ
    TemporalAnd(Box<STLFormula>, Box<STLFormula>),
    /// Temporal OR: φ ∨ ψ
    TemporalOr(Box<STLFormula>, Box<STLFormula>),
    /// Always: □φ (globally)
    Always(TimeInterval, Box<STLFormula>),
    /// Eventually: ◇φ (finally)
    Eventually(TimeInterval, Box<STLFormula>),
    /// Until: φ U ψ
    Until(TimeInterval, Box<STLFormula>, Box<STLFormula>),
    /// Release: φ R ψ
    Release(TimeInterval, Box<STLFormula>, Box<STLFormula>),
    /// Next: ○φ
    Next(Box<STLFormula>),
    /// Implication: φ → ψ
    Implies(Box<STLFormula>, Box<STLFormula>),
    /// Equivalence: φ ↔ ψ
    Equiv(Box<STLFormula>, Box<STLFormula>),
}

/// Atomic predicate for signal comparison
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AtomicPredicate {
    pub variable: String,
    pub operator: ComparisonOperator,
    pub threshold: f64,
    pub tolerance: Option<f64>,
}

/// Comparison operators for atomic predicates
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ComparisonOperator {
    Equal,
    NotEqual,
    GreaterThan,
    GreaterEqual,
    LessThan,
    LessEqual,
}

/// Time interval for temporal operators
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TimeInterval {
    pub start: Option<f64>,
    pub end: Option<f64>,
    pub unit: TimeUnit,
}

/// Time units for intervals
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum TimeUnit {
    Seconds,
    Milliseconds,
    Minutes,
    Hours,
}

/// Parameter definition for STL specifications
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Parameter {
    pub name: String,
    pub parameter_type: ParameterType,
    pub default_value: Option<ParameterValue>,
    pub description: Option<String>,
}

/// Parameter types
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ParameterType {
    Real,
    Integer,
    Boolean,
    String,
    Time,
}

/// Parameter values
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ParameterValue {
    Real(f64),
    Integer(i64),
    Boolean(bool),
    String(String),
    Time(f64),
}

impl PartialEq for ParameterValue {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (ParameterValue::Real(a), ParameterValue::Real(b)) => (a - b).abs() < f64::EPSILON,
            (ParameterValue::Integer(a), ParameterValue::Integer(b)) => a == b,
            (ParameterValue::Boolean(a), ParameterValue::Boolean(b)) => a == b,
            (ParameterValue::String(a), ParameterValue::String(b)) => a == b,
            (ParameterValue::Time(a), ParameterValue::Time(b)) => (a - b).abs() < f64::EPSILON,
            _ => false,
        }
    }
}

impl Eq for ParameterValue {}

/// Constraint definition for STL specifications
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Constraint {
    pub name: String,
    pub constraint_type: ConstraintType,
    pub expression: String,
    pub description: Option<String>,
}

/// Constraint types
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ConstraintType {
    Bounds,
    Linear,
    Nonlinear,
    Temporal,
}

impl STLFormula {
    /// Get all variables used in this formula
    pub fn variables(&self) -> std::collections::HashSet<String> {
        let mut vars = std::collections::HashSet::new();
        self.collect_variables(&mut vars);
        vars
    }

    /// Collect variables recursively
    fn collect_variables(&self, vars: &mut std::collections::HashSet<String>) {
        match self {
            STLFormula::Atomic(pred) => {
                vars.insert(pred.variable.clone());
            }
            STLFormula::And(left, right) | STLFormula::Or(left, right) | STLFormula::TemporalAnd(left, right) | STLFormula::TemporalOr(left, right) | STLFormula::Until(_, left, right) | STLFormula::Release(_, left, right) | STLFormula::Implies(left, right) | STLFormula::Equiv(left, right) => {
                left.collect_variables(vars);
                right.collect_variables(vars);
            }
            STLFormula::Not(formula) | STLFormula::Next(formula) => {
                formula.collect_variables(vars);
            }
            STLFormula::Always(_, formula) | STLFormula::Eventually(_, formula) => {
                formula.collect_variables(vars);
            }
        }
    }

    /// Get the maximum nesting depth of temporal operators
    pub fn temporal_depth(&self) -> usize {
        match self {
            STLFormula::Atomic(_) => 0,
            STLFormula::And(left, right) | STLFormula::Or(left, right) | STLFormula::TemporalAnd(left, right) | STLFormula::TemporalOr(left, right) | STLFormula::Implies(left, right) | STLFormula::Equiv(left, right) => {
                std::cmp::max(left.temporal_depth(), right.temporal_depth())
            }
            STLFormula::Not(formula) | STLFormula::Next(formula) => {
                formula.temporal_depth()
            }
            STLFormula::Always(_, formula) | STLFormula::Eventually(_, formula) => {
                1 + formula.temporal_depth()
            }
            STLFormula::Until(_, left, right) | STLFormula::Release(_, left, right) => {
                1 + std::cmp::max(left.temporal_depth(), right.temporal_depth())
            }
        }
    }

    /// Check if the formula is in negation normal form (NNF)
    pub fn is_negation_normal_form(&self) -> bool {
        match self {
            STLFormula::Atomic(_) => true,
            STLFormula::And(left, right) | STLFormula::Or(left, right) | STLFormula::TemporalAnd(left, right) | STLFormula::TemporalOr(left, right) | STLFormula::Until(_, left, right) | STLFormula::Release(_, left, right) | STLFormula::Implies(left, right) | STLFormula::Equiv(left, right) => {
                left.is_negation_normal_form() && right.is_negation_normal_form()
            }
            STLFormula::Not(formula) => {
                matches!(**formula, STLFormula::Atomic(_))
            }
            STLFormula::Next(formula) => {
                formula.is_negation_normal_form()
            }
            STLFormula::Always(_, formula) | STLFormula::Eventually(_, formula) => {
                formula.is_negation_normal_form()
            }
        }
    }
}

impl TimeInterval {
    /// Convert to seconds
    pub fn to_seconds(&self) -> (Option<f64>, Option<f64>) {
        let convert = |t: Option<f64>| {
            t.map(|t| match self.unit {
                TimeUnit::Seconds => t,
                TimeUnit::Milliseconds => t / 1000.0,
                TimeUnit::Minutes => t * 60.0,
                TimeUnit::Hours => t * 3600.0,
            })
        };
        (convert(self.start), convert(self.end))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_variables_collection() {
        let formula = STLFormula::And(
            Box::new(STLFormula::Atomic(AtomicPredicate {
                variable: "voltage".to_string(),
                operator: ComparisonOperator::GreaterThan,
                threshold: 220.0,
                tolerance: None,
            })),
            Box::new(STLFormula::Atomic(AtomicPredicate {
                variable: "current".to_string(),
                operator: ComparisonOperator::LessThan,
                threshold: 100.0,
                tolerance: None,
            })),
        );

        let vars = formula.variables();
        assert!(vars.contains("voltage"));
        assert!(vars.contains("current"));
        assert_eq!(vars.len(), 2);
    }

    #[test]
    fn test_temporal_depth() {
        let formula = STLFormula::Always(
            TimeInterval {
                start: Some(0.0),
                end: Some(10.0),
                unit: TimeUnit::Seconds,
            },
            Box::new(STLFormula::Atomic(AtomicPredicate {
                variable: "voltage".to_string(),
                operator: ComparisonOperator::GreaterThan,
                threshold: 220.0,
                tolerance: None,
            })),
        );

        assert_eq!(formula.temporal_depth(), 1);
    }

    #[test]
    fn test_negation_normal_form() {
        let atomic = STLFormula::Atomic(AtomicPredicate {
            variable: "voltage".to_string(),
            operator: ComparisonOperator::GreaterThan,
            threshold: 220.0,
            tolerance: None,
        });

        let not_atomic = STLFormula::Not(Box::new(atomic.clone()));
        let not_not_atomic = STLFormula::Not(Box::new(not_atomic.clone()));

        assert!(atomic.is_negation_normal_form());
        assert!(not_atomic.is_negation_normal_form());
        assert!(!not_not_atomic.is_negation_normal_form());
    }
} 