//! STL parser using ANTLR-generated grammar

use crate::ast::{STLSpecification, STLFormula, AtomicPredicate, ComparisonOperator, TimeInterval, TimeUnit, Parameter, Constraint, ParameterType, ConstraintType};
use crate::error::{ParseError, ParseResult};
use std::collections::HashMap;

/// STL parser that converts text to AST
pub struct STLParser {
    /// Parser state
    state: ParserState,
}

/// Parser state
#[derive(Debug, Clone)]
struct ParserState {
    /// Current position in input
    position: usize,
    /// Current line number
    line: usize,
    /// Current column number
    column: usize,
    /// Error messages
    errors: Vec<String>,
}

impl STLParser {
    /// Create a new STL parser
    pub fn new() -> Self {
        Self {
            state: ParserState {
                position: 0,
                line: 1,
                column: 1,
                errors: Vec::new(),
            },
        }
    }

    /// Parse STL specification from string
    pub fn parse(&mut self, input: &str) -> ParseResult<STLSpecification> {
        self.state = ParserState {
            position: 0,
            line: 1,
            column: 1,
            errors: Vec::new(),
        };

        // For now, we'll use a simplified parser
        // In practice, this would use ANTLR-generated code
        self.parse_specification(input)
    }

    /// Parse specification
    fn parse_specification(&mut self, input: &str) -> ParseResult<STLSpecification> {
        let lines: Vec<&str> = input.lines().collect();
        
        if lines.is_empty() {
            return Err(ParseError::SyntaxError {
                position: 0,
                message: "Empty specification".to_string(),
            });
        }

        // Parse name (first line)
        let name = self.parse_name(lines[0])?;
        
        // Parse description (optional, second line)
        let description = if lines.len() > 1 && lines[1].starts_with("//") {
            Some(lines[1][2..].trim().to_string())
        } else {
            None
        };

        // Parse formula (third line or after description)
        let formula_start = if description.is_some() { 2 } else { 1 };
        let formula_line = if lines.len() > formula_start {
            lines[formula_start]
        } else {
            return Err(ParseError::SyntaxError {
                position: 0,
                message: "Missing formula".to_string(),
            });
        };

        let formula = self.parse_formula(formula_line)?;

        // Parse parameters and constraints (remaining lines)
        let mut parameters = Vec::new();
        let mut constraints = Vec::new();
        let mut metadata = HashMap::new();

        for line in lines.iter().skip(formula_start + 1) {
            if line.starts_with("param:") {
                let param = self.parse_parameter(line)?;
                parameters.push(param);
            } else if line.starts_with("constraint:") {
                let constraint = self.parse_constraint(line)?;
                constraints.push(constraint);
            } else if line.starts_with("meta:") {
                let (key, value) = self.parse_metadata(line)?;
                metadata.insert(key, value);
            }
        }

        Ok(STLSpecification {
            name,
            description,
            formula,
            parameters,
            constraints,
            metadata,
        })
    }

    /// Parse specification name
    fn parse_name(&mut self, line: &str) -> ParseResult<String> {
        let name = line.trim();
        if name.is_empty() {
            return Err(ParseError::SyntaxError {
                position: 0,
                message: "Empty specification name".to_string(),
            });
        }
        Ok(name.to_string())
    }

    /// Parse STL formula
    fn parse_formula(&mut self, input: &str) -> ParseResult<STLFormula> {
        let input = input.trim();
        
        // Simple recursive descent parser for basic STL formulas
        if input.contains("&&") {
            self.parse_binary_formula(input, "&&", |left, right| {
                STLFormula::And(Box::new(left), Box::new(right))
            })
        } else if input.contains("||") {
            self.parse_binary_formula(input, "||", |left, right| {
                STLFormula::Or(Box::new(left), Box::new(right))
            })
        } else if input.starts_with("!") {
            let inner = self.parse_formula(&input[1..])?;
            Ok(STLFormula::Not(Box::new(inner)))
        } else if input.starts_with("G[") {
            self.parse_temporal_formula(input, "G", |interval, formula| {
                STLFormula::Always(interval, Box::new(formula))
            })
        } else if input.starts_with("F[") {
            self.parse_temporal_formula(input, "F", |interval, formula| {
                STLFormula::Eventually(interval, Box::new(formula))
            })
        } else if input.starts_with("X") {
            let inner = self.parse_formula(&input[1..])?;
            Ok(STLFormula::Next(Box::new(inner)))
        } else if input.contains("->") {
            self.parse_binary_formula(input, "->", |left, right| {
                STLFormula::Implies(Box::new(left), Box::new(right))
            })
        } else if input.contains("<->") {
            self.parse_binary_formula(input, "<->", |left, right| {
                STLFormula::Equiv(Box::new(left), Box::new(right))
            })
        } else {
            // Try to parse as atomic predicate
            self.parse_atomic_predicate(input)
        }
    }

    /// Parse binary formula
    fn parse_binary_formula<F>(&mut self, input: &str, op: &str, constructor: F) -> ParseResult<STLFormula>
    where
        F: FnOnce(STLFormula, STLFormula) -> STLFormula,
    {
        let parts: Vec<&str> = input.split(op).collect();
        if parts.len() != 2 {
            return Err(ParseError::SyntaxError {
                position: 0,
                message: format!("Invalid binary formula: {}", input),
            });
        }

        let left = self.parse_formula(parts[0])?;
        let right = self.parse_formula(parts[1])?;

        Ok(constructor(left, right))
    }

    /// Parse temporal formula
    fn parse_temporal_formula<F>(&mut self, input: &str, op: &str, constructor: F) -> ParseResult<STLFormula>
    where
        F: FnOnce(TimeInterval, STLFormula) -> STLFormula,
    {
        // Extract interval from G[0,10] or F[0,10]
        let start = input.find('[').ok_or_else(|| ParseError::SyntaxError {
            position: 0,
            message: format!("Invalid temporal formula: {}", input),
        })?;
        let end = input.find(']').ok_or_else(|| ParseError::SyntaxError {
            position: 0,
            message: format!("Invalid temporal formula: {}", input),
        })?;

        let interval_str = &input[start + 1..end];
        let interval = self.parse_time_interval(interval_str)?;

        let formula_str = &input[end + 1..];
        let formula = self.parse_formula(formula_str)?;

        Ok(constructor(interval, formula))
    }

    /// Parse atomic predicate
    fn parse_atomic_predicate(&mut self, input: &str) -> ParseResult<STLFormula> {
        // Parse patterns like: variable > threshold, variable < threshold, etc.
        let input = input.trim();
        
        // Find comparison operator
        let operators = [">", ">=", "<", "<=", "==", "!="];
        let mut op_found = None;
        let mut op_pos = 0;

        for op in &operators {
            if let Some(pos) = input.find(op) {
                op_found = Some(*op);
                op_pos = pos;
                break;
            }
        }

        let op = op_found.ok_or_else(|| ParseError::SyntaxError {
            position: 0,
            message: format!("No comparison operator found in: {}", input),
        })?;

        let variable = input[..op_pos].trim().to_string();
        let threshold_str = input[op_pos + op.len()..].trim();

        let threshold = threshold_str.parse::<f64>().map_err(|_| ParseError::InvalidNumber {
            position: op_pos,
            message: format!("Invalid number: {}", threshold_str),
        })?;

        let operator = match op {
            ">" => ComparisonOperator::GreaterThan,
            ">=" => ComparisonOperator::GreaterEqual,
            "<" => ComparisonOperator::LessThan,
            "<=" => ComparisonOperator::LessEqual,
            "==" => ComparisonOperator::Equal,
            "!=" => ComparisonOperator::NotEqual,
            _ => return Err(ParseError::SyntaxError {
                position: op_pos,
                message: format!("Unknown operator: {}", op),
            }),
        };

        Ok(STLFormula::Atomic(AtomicPredicate {
            variable,
            operator,
            threshold,
            tolerance: None,
        }))
    }

    /// Parse time interval
    fn parse_time_interval(&mut self, input: &str) -> ParseResult<TimeInterval> {
        let parts: Vec<&str> = input.split(',').collect();
        if parts.len() != 2 {
            return Err(ParseError::SyntaxError {
                position: 0,
                message: format!("Invalid time interval: {}", input),
            });
        }

        let start_str = parts[0].trim();
        let end_str = parts[1].trim();

        let start = if start_str == "0" || start_str.is_empty() {
            None
        } else {
            Some(start_str.parse::<f64>().map_err(|_| ParseError::InvalidNumber {
                position: 0,
                message: format!("Invalid start time: {}", start_str),
            })?)
        };

        let end = if end_str == "inf" || end_str.is_empty() {
            None
        } else {
            Some(end_str.parse::<f64>().map_err(|_| ParseError::InvalidNumber {
                position: 0,
                message: format!("Invalid end time: {}", end_str),
            })?)
        };

        Ok(TimeInterval {
            start,
            end,
            unit: TimeUnit::Seconds,
        })
    }

    /// Parse parameter
    fn parse_parameter(&mut self, line: &str) -> ParseResult<Parameter> {
        // Parse format: param: name type [default_value] [description]
        let content = line.strip_prefix("param:").unwrap_or(line).trim();
        let parts: Vec<&str> = content.split_whitespace().collect();

        if parts.is_empty() {
            return Err(ParseError::SyntaxError {
                position: 0,
                message: "Empty parameter".to_string(),
            });
        }

        let name = parts[0].to_string();
        let param_type = if parts.len() > 1 {
            match parts[1] {
                "real" => ParameterType::Real,
                "int" => ParameterType::Integer,
                "bool" => ParameterType::Boolean,
                "string" => ParameterType::String,
                "time" => ParameterType::Time,
                _ => return Err(ParseError::InvalidParameterType {
                    expected: "real|int|bool|string|time".to_string(),
                    actual: parts[1].to_string(),
                }),
            }
        } else {
            ParameterType::Real
        };

        let default_value = if parts.len() > 2 {
            Some(self.parse_parameter_value(parts[2], &param_type)?)
        } else {
            None
        };

        let description = if parts.len() > 3 {
            Some(parts[3..].join(" "))
        } else {
            None
        };

        Ok(Parameter {
            name,
            parameter_type: param_type,
            default_value,
            description,
        })
    }

    /// Parse parameter value
    fn parse_parameter_value(&mut self, value: &str, param_type: &ParameterType) -> ParseResult<crate::ast::ParameterValue> {
        match param_type {
            ParameterType::Real => {
                let val = value.parse::<f64>().map_err(|_| ParseError::InvalidParameterType {
                    expected: "real number".to_string(),
                    actual: value.to_string(),
                })?;
                Ok(crate::ast::ParameterValue::Real(val))
            }
            ParameterType::Integer => {
                let val = value.parse::<i64>().map_err(|_| ParseError::InvalidParameterType {
                    expected: "integer".to_string(),
                    actual: value.to_string(),
                })?;
                Ok(crate::ast::ParameterValue::Integer(val))
            }
            ParameterType::Boolean => {
                let val = value.parse::<bool>().map_err(|_| ParseError::InvalidParameterType {
                    expected: "boolean".to_string(),
                    actual: value.to_string(),
                })?;
                Ok(crate::ast::ParameterValue::Boolean(val))
            }
            ParameterType::String => {
                Ok(crate::ast::ParameterValue::String(value.to_string()))
            }
            ParameterType::Time => {
                let val = value.parse::<f64>().map_err(|_| ParseError::InvalidParameterType {
                    expected: "time value".to_string(),
                    actual: value.to_string(),
                })?;
                Ok(crate::ast::ParameterValue::Time(val))
            }
        }
    }

    /// Parse constraint
    fn parse_constraint(&mut self, line: &str) -> ParseResult<Constraint> {
        // Parse format: constraint: name type expression [description]
        let content = line.strip_prefix("constraint:").unwrap_or(line).trim();
        let parts: Vec<&str> = content.split_whitespace().collect();

        if parts.len() < 3 {
            return Err(ParseError::SyntaxError {
                position: 0,
                message: "Invalid constraint format".to_string(),
            });
        }

        let name = parts[0].to_string();
        let constraint_type = match parts[1] {
            "bounds" => ConstraintType::Bounds,
            "linear" => ConstraintType::Linear,
            "nonlinear" => ConstraintType::Nonlinear,
            "temporal" => ConstraintType::Temporal,
            _ => return Err(ParseError::InvalidParameterType {
                expected: "bounds|linear|nonlinear|temporal".to_string(),
                actual: parts[1].to_string(),
            }),
        };

        let expression = parts[2].to_string();
        let description = if parts.len() > 3 {
            Some(parts[3..].join(" "))
        } else {
            None
        };

        Ok(Constraint {
            name,
            constraint_type,
            expression,
            description,
        })
    }

    /// Parse metadata
    fn parse_metadata(&mut self, line: &str) -> ParseResult<(String, String)> {
        // Parse format: meta: key value
        let content = line.strip_prefix("meta:").unwrap_or(line).trim();
        let parts: Vec<&str> = content.split_whitespace().collect();

        if parts.len() < 2 {
            return Err(ParseError::SyntaxError {
                position: 0,
                message: "Invalid metadata format".to_string(),
            });
        }

        let key = parts[0].to_string();
        let value = parts[1..].join(" ");

        Ok((key, value))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{STLFormula, AtomicPredicate, ComparisonOperator};

    #[test]
    fn test_parse_atomic_predicate() {
        let mut parser = STLParser::new();
        let result = parser.parse_atomic_predicate("voltage > 220");
        assert!(result.is_ok());
        
        if let Ok(STLFormula::Atomic(pred)) = result {
            assert_eq!(pred.variable, "voltage");
            assert!(matches!(pred.operator, ComparisonOperator::GreaterThan));
            assert_eq!(pred.threshold, 220.0);
        } else {
            panic!("Expected atomic predicate");
        }
    }

    #[test]
    fn test_parse_binary_formula() {
        let mut parser = STLParser::new();
        let result = parser.parse_formula("voltage > 220 && current < 100");
        assert!(result.is_ok());
        
        if let Ok(STLFormula::And(left, right)) = result {
            assert!(matches!(*left, STLFormula::Atomic(_)));
            assert!(matches!(*right, STLFormula::Atomic(_)));
        } else {
            panic!("Expected binary formula");
        }
    }

    #[test]
    fn test_parse_temporal_formula() {
        let mut parser = STLParser::new();
        let result = parser.parse_formula("G[0,10] voltage > 220");
        assert!(result.is_ok());
        
        if let Ok(STLFormula::Always(interval, formula)) = result {
            assert_eq!(interval.start, Some(0.0));
            assert_eq!(interval.end, Some(10.0));
            assert!(matches!(*formula, STLFormula::Atomic(_)));
        } else {
            panic!("Expected temporal formula");
        }
    }

    #[test]
    fn test_parse_specification() {
        let input = "voltage_safety
// Voltage safety specification
voltage > 220 && current < 100
param: max_voltage real 240.0 Maximum voltage threshold
constraint: voltage_bounds bounds voltage <= 250.0
meta: author CertifyEdge Team";
        
        let mut parser = STLParser::new();
        let result = parser.parse(input);
        assert!(result.is_ok());
        
        if let Ok(spec) = result {
            assert_eq!(spec.name, "voltage_safety");
            assert!(spec.description.is_some());
            assert!(matches!(spec.formula, STLFormula::And(_, _)));
            assert_eq!(spec.parameters.len(), 1);
            assert_eq!(spec.constraints.len(), 1);
            assert_eq!(spec.metadata.len(), 1);
        } else {
            panic!("Expected valid specification");
        }
    }
} 