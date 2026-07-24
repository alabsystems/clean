// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! JSON Schema Parser for TLAPS Benchmark Obligations
//!
//! Copyright 2026 Andrew Yates
//! Licensed under Apache-2.0
//!
//! Parses the benchmark JSON format and converts to TlaObligation.

use crate::encoding::{TlaArithOp, TlaCmpOp, TlaExpr, TlaFormula};
use crate::obligation::TlaDeclare;
use crate::TlaObligation;
use serde::{Deserialize, Serialize};
use serde_json::Value;

/// Benchmark obligation as stored in JSON files
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct BenchmarkObligation {
    /// Unique identifier (e.g., "nat_induction/sum_formula")
    pub id: String,

    /// Module name
    pub module: String,

    /// Line number in source (optional)
    pub line: Option<u32>,

    /// Declarations in scope
    #[serde(default)]
    pub declares: Vec<DeclareJson>,

    /// Hypotheses
    #[serde(default)]
    pub hypotheses: Vec<HypothesisJson>,

    /// Goal formula to prove
    pub goal: Value,

    /// Suggested tactic
    pub tactic_hint: Option<String>,

    /// Expected result (true = should prove, false = should fail)
    #[serde(default = "default_expected_true")]
    pub expected_result: bool,

    /// Difficulty level
    #[serde(default)]
    pub difficulty: String,

    /// Source of the obligation
    #[serde(default)]
    pub source: String,

    /// Tags for categorization
    #[serde(default)]
    pub tags: Vec<String>,
}

fn default_expected_true() -> bool {
    true
}

/// Declaration in JSON format
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct DeclareJson {
    #[serde(rename = "type")]
    pub decl_type: String,
    pub name: String,
    #[serde(default)]
    pub arity: u32,
}

/// Hypothesis in JSON format
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct HypothesisJson {
    pub name: String,
    pub formula: Value,
}

impl BenchmarkObligation {
    /// Load a benchmark obligation from a JSON file
    pub fn load(path: &std::path::Path) -> Result<Self, String> {
        let content = std::fs::read_to_string(path)
            .map_err(|e| format!("Failed to read {}: {}", path.display(), e))?;
        serde_json::from_str(&content)
            .map_err(|e| format!("Failed to parse {}: {}", path.display(), e))
    }

    /// Convert to TlaObligation
    pub fn to_tla_obligation(&self) -> Result<TlaObligation, String> {
        let mut obligation = TlaObligation::new(parse_formula(&self.goal)?).in_module(&self.module);

        if let Some(line) = self.line {
            obligation = obligation.at_line(line);
        }

        if let Some(ref hint) = self.tactic_hint {
            obligation = obligation.with_tactic(hint);
        }

        // Convert declarations
        for decl in &self.declares {
            let tla_decl = match decl.decl_type.as_str() {
                "constant" => TlaDeclare::Constant {
                    name: decl.name.clone(),
                    arity: decl.arity,
                },
                "variable" => TlaDeclare::Variable {
                    name: decl.name.clone(),
                },
                "prop" => TlaDeclare::Prop {
                    name: decl.name.clone(),
                },
                _ => return Err(format!("Unknown declare type: {}", decl.decl_type)),
            };
            obligation = obligation.with_declare(tla_decl);
        }

        // Convert hypotheses
        for hyp in &self.hypotheses {
            let formula = parse_formula(&hyp.formula)?;
            obligation = obligation.with_hypothesis(&hyp.name, formula);
        }

        Ok(obligation)
    }
}

/// Parse a JSON value into a TlaFormula
pub fn parse_formula(value: &Value) -> Result<TlaFormula, String> {
    match value {
        Value::Bool(true) => Ok(TlaFormula::True),
        Value::Bool(false) => Ok(TlaFormula::False),
        Value::String(s) => {
            // String represents a variable reference
            Ok(TlaFormula::Expr(TlaExpr::Var(s.clone())))
        }
        Value::Object(obj) => parse_formula_object(obj),
        _ => Err(format!("Cannot parse formula from: {:?}", value)),
    }
}

fn parse_formula_object(obj: &serde_json::Map<String, Value>) -> Result<TlaFormula, String> {
    // Check for each formula constructor

    if let Some(inner) = obj.get("always") {
        return Ok(TlaFormula::Always(Box::new(parse_formula(inner)?)));
    }

    if let Some(inner) = obj.get("eventually") {
        return Ok(TlaFormula::Eventually(Box::new(parse_formula(inner)?)));
    }

    if let Some(arr) = obj.get("leads_to") {
        let arr = arr.as_array().ok_or("leads_to expects array")?;
        if arr.len() != 2 {
            return Err("leads_to expects [P, Q]".to_string());
        }
        return Ok(TlaFormula::LeadsTo(
            Box::new(parse_formula(&arr[0])?),
            Box::new(parse_formula(&arr[1])?),
        ));
    }

    if let Some(arr) = obj.get("forall_in") {
        let arr = arr.as_array().ok_or("forall_in expects array")?;
        if arr.len() != 3 {
            return Err("forall_in expects [var, set, body]".to_string());
        }
        let var = arr[0].as_str().ok_or("forall_in var must be string")?;
        let set = parse_expr(&arr[1])?;
        let body = parse_formula(&arr[2])?;
        return Ok(TlaFormula::ForallIn(
            var.to_string(),
            Box::new(set),
            Box::new(body),
        ));
    }

    if let Some(arr) = obj.get("exists_in") {
        let arr = arr.as_array().ok_or("exists_in expects array")?;
        if arr.len() != 3 {
            return Err("exists_in expects [var, set, body]".to_string());
        }
        let var = arr[0].as_str().ok_or("exists_in var must be string")?;
        let set = parse_expr(&arr[1])?;
        let body = parse_formula(&arr[2])?;
        return Ok(TlaFormula::ExistsIn(
            var.to_string(),
            Box::new(set),
            Box::new(body),
        ));
    }

    if let Some(arr) = obj.get("eq") {
        let arr = arr.as_array().ok_or("eq expects array")?;
        if arr.len() != 2 {
            return Err("eq expects [a, b]".to_string());
        }
        return Ok(TlaFormula::Eq(
            Box::new(parse_expr(&arr[0])?),
            Box::new(parse_expr(&arr[1])?),
        ));
    }

    if let Some(arr) = obj.get("mem") {
        let arr = arr.as_array().ok_or("mem expects array")?;
        if arr.len() != 2 {
            return Err("mem expects [elem, set]".to_string());
        }
        return Ok(TlaFormula::Mem(
            Box::new(parse_expr(&arr[0])?),
            Box::new(parse_expr(&arr[1])?),
        ));
    }

    if let Some(arr) = obj.get("implies") {
        let arr = arr.as_array().ok_or("implies expects array")?;
        if arr.len() != 2 {
            return Err("implies expects [P, Q]".to_string());
        }
        return Ok(TlaFormula::Implies(
            Box::new(parse_formula(&arr[0])?),
            Box::new(parse_formula(&arr[1])?),
        ));
    }

    if let Some(arr) = obj.get("and") {
        let arr = arr.as_array().ok_or("and expects array")?;
        if arr.len() != 2 {
            return Err("and expects [P, Q]".to_string());
        }
        return Ok(TlaFormula::And(
            Box::new(parse_formula(&arr[0])?),
            Box::new(parse_formula(&arr[1])?),
        ));
    }

    if let Some(arr) = obj.get("or") {
        let arr = arr.as_array().ok_or("or expects array")?;
        if arr.len() != 2 {
            return Err("or expects [P, Q]".to_string());
        }
        return Ok(TlaFormula::Or(
            Box::new(parse_formula(&arr[0])?),
            Box::new(parse_formula(&arr[1])?),
        ));
    }

    if let Some(arr) = obj.get("iff") {
        let arr = arr.as_array().ok_or("iff expects array")?;
        if arr.len() != 2 {
            return Err("iff expects [P, Q]".to_string());
        }
        return Ok(TlaFormula::Iff(
            Box::new(parse_formula(&arr[0])?),
            Box::new(parse_formula(&arr[1])?),
        ));
    }

    if let Some(inner) = obj.get("not") {
        return Ok(TlaFormula::Not(Box::new(parse_formula(inner)?)));
    }

    // Check for expression wrappers
    if let Some(expr_val) = obj.get("expr") {
        return Ok(TlaFormula::Expr(parse_expr(expr_val)?));
    }

    // Comparison operators as formulas
    if let Some(arr) = obj.get("lt") {
        let arr = arr.as_array().ok_or("lt expects array")?;
        if arr.len() != 2 {
            return Err("lt expects [a, b]".to_string());
        }
        return Ok(TlaFormula::Expr(TlaExpr::Cmp(
            TlaCmpOp::Lt,
            Box::new(parse_expr(&arr[0])?),
            Box::new(parse_expr(&arr[1])?),
        )));
    }

    if let Some(arr) = obj.get("le") {
        let arr = arr.as_array().ok_or("le expects array")?;
        if arr.len() != 2 {
            return Err("le expects [a, b]".to_string());
        }
        return Ok(TlaFormula::Expr(TlaExpr::Cmp(
            TlaCmpOp::Le,
            Box::new(parse_expr(&arr[0])?),
            Box::new(parse_expr(&arr[1])?),
        )));
    }

    if let Some(arr) = obj.get("gt") {
        let arr = arr.as_array().ok_or("gt expects array")?;
        if arr.len() != 2 {
            return Err("gt expects [a, b]".to_string());
        }
        return Ok(TlaFormula::Expr(TlaExpr::Cmp(
            TlaCmpOp::Gt,
            Box::new(parse_expr(&arr[0])?),
            Box::new(parse_expr(&arr[1])?),
        )));
    }

    if let Some(arr) = obj.get("ge") {
        let arr = arr.as_array().ok_or("ge expects array")?;
        if arr.len() != 2 {
            return Err("ge expects [a, b]".to_string());
        }
        return Ok(TlaFormula::Expr(TlaExpr::Cmp(
            TlaCmpOp::Ge,
            Box::new(parse_expr(&arr[0])?),
            Box::new(parse_expr(&arr[1])?),
        )));
    }

    Err(format!("Unknown formula object: {:?}", obj))
}

/// Parse a JSON value into a TlaExpr
pub fn parse_expr(value: &Value) -> Result<TlaExpr, String> {
    match value {
        Value::Number(n) => {
            if let Some(i) = n.as_i64() {
                Ok(TlaExpr::Int(i))
            } else {
                Err(format!("Cannot parse number: {:?}", n))
            }
        }
        Value::String(s) => {
            // Special set names
            match s.as_str() {
                "Nat" => Ok(TlaExpr::Nat),
                "Int" => Ok(TlaExpr::Integer),
                "Real" => Ok(TlaExpr::Real),
                "Boolean" | "BOOLEAN" => Ok(TlaExpr::Boolean),
                "STRING" => Ok(TlaExpr::String_),
                _ => Ok(TlaExpr::Var(s.clone())),
            }
        }
        Value::Bool(true) => Ok(TlaExpr::True),
        Value::Bool(false) => Ok(TlaExpr::False),
        Value::Object(obj) => parse_expr_object(obj),
        Value::Array(arr) => {
            // Array of expressions becomes a tuple
            let exprs: Result<Vec<_>, _> = arr.iter().map(parse_expr).collect();
            Ok(TlaExpr::Tuple(exprs?))
        }
        Value::Null => Err("Cannot parse null as expression".to_string()),
    }
}

fn parse_expr_object(obj: &serde_json::Map<String, Value>) -> Result<TlaExpr, String> {
    // Constant reference
    if let Some(name) = obj.get("const") {
        let name = name.as_str().ok_or("const must be string")?;
        return Ok(TlaExpr::Const(name.to_string()));
    }

    // Variable reference
    if let Some(name) = obj.get("var") {
        let name = name.as_str().ok_or("var must be string")?;
        return Ok(TlaExpr::Var(name.to_string()));
    }

    // Integer literal
    if let Some(n) = obj.get("int") {
        let n = n.as_i64().ok_or("int must be integer")?;
        return Ok(TlaExpr::Int(n));
    }

    // Arithmetic operations
    if let Some(arr) = obj.get("add") {
        let arr = arr.as_array().ok_or("add expects array")?;
        if arr.len() != 2 {
            return Err("add expects [a, b]".to_string());
        }
        return Ok(TlaExpr::Arith(
            TlaArithOp::Add,
            Box::new(parse_expr(&arr[0])?),
            Box::new(parse_expr(&arr[1])?),
        ));
    }

    if let Some(arr) = obj.get("sub") {
        let arr = arr.as_array().ok_or("sub expects array")?;
        if arr.len() != 2 {
            return Err("sub expects [a, b]".to_string());
        }
        return Ok(TlaExpr::Arith(
            TlaArithOp::Sub,
            Box::new(parse_expr(&arr[0])?),
            Box::new(parse_expr(&arr[1])?),
        ));
    }

    if let Some(arr) = obj.get("mul") {
        let arr = arr.as_array().ok_or("mul expects array")?;
        if arr.len() != 2 {
            return Err("mul expects [a, b]".to_string());
        }
        return Ok(TlaExpr::Arith(
            TlaArithOp::Mul,
            Box::new(parse_expr(&arr[0])?),
            Box::new(parse_expr(&arr[1])?),
        ));
    }

    if let Some(arr) = obj.get("div") {
        let arr = arr.as_array().ok_or("div expects array")?;
        if arr.len() != 2 {
            return Err("div expects [a, b]".to_string());
        }
        return Ok(TlaExpr::Arith(
            TlaArithOp::Div,
            Box::new(parse_expr(&arr[0])?),
            Box::new(parse_expr(&arr[1])?),
        ));
    }

    if let Some(arr) = obj.get("mod") {
        let arr = arr.as_array().ok_or("mod expects array")?;
        if arr.len() != 2 {
            return Err("mod expects [a, b]".to_string());
        }
        return Ok(TlaExpr::Arith(
            TlaArithOp::Mod,
            Box::new(parse_expr(&arr[0])?),
            Box::new(parse_expr(&arr[1])?),
        ));
    }

    // Comparison operators
    if let Some(arr) = obj.get("lt") {
        let arr = arr.as_array().ok_or("lt expects array")?;
        if arr.len() != 2 {
            return Err("lt expects [a, b]".to_string());
        }
        return Ok(TlaExpr::Cmp(
            TlaCmpOp::Lt,
            Box::new(parse_expr(&arr[0])?),
            Box::new(parse_expr(&arr[1])?),
        ));
    }

    if let Some(arr) = obj.get("le") {
        let arr = arr.as_array().ok_or("le expects array")?;
        if arr.len() != 2 {
            return Err("le expects [a, b]".to_string());
        }
        return Ok(TlaExpr::Cmp(
            TlaCmpOp::Le,
            Box::new(parse_expr(&arr[0])?),
            Box::new(parse_expr(&arr[1])?),
        ));
    }

    if let Some(arr) = obj.get("gt") {
        let arr = arr.as_array().ok_or("gt expects array")?;
        if arr.len() != 2 {
            return Err("gt expects [a, b]".to_string());
        }
        return Ok(TlaExpr::Cmp(
            TlaCmpOp::Gt,
            Box::new(parse_expr(&arr[0])?),
            Box::new(parse_expr(&arr[1])?),
        ));
    }

    if let Some(arr) = obj.get("ge") {
        let arr = arr.as_array().ok_or("ge expects array")?;
        if arr.len() != 2 {
            return Err("ge expects [a, b]".to_string());
        }
        return Ok(TlaExpr::Cmp(
            TlaCmpOp::Ge,
            Box::new(parse_expr(&arr[0])?),
            Box::new(parse_expr(&arr[1])?),
        ));
    }

    // Operator application: {"op": ["name", arg1, arg2, ...]}
    if let Some(arr) = obj.get("op") {
        let arr = arr.as_array().ok_or("op expects array")?;
        if arr.is_empty() {
            return Err("op requires at least operator name".to_string());
        }
        let name = arr[0].as_str().ok_or("op name must be string")?;
        let args: Result<Vec<_>, _> = arr[1..].iter().map(parse_expr).collect();
        return Ok(TlaExpr::OpApply(name.to_string(), args?));
    }

    // Set enumeration: {"set": [a, b, c]}
    if let Some(arr) = obj.get("set") {
        let arr = arr.as_array().ok_or("set expects array")?;
        let elems: Result<Vec<_>, _> = arr.iter().map(parse_expr).collect();
        return Ok(TlaExpr::SetEnum(elems?));
    }

    // Range: {"range": [a, b]}
    if let Some(arr) = obj.get("range") {
        let arr = arr.as_array().ok_or("range expects array")?;
        if arr.len() != 2 {
            return Err("range expects [a, b]".to_string());
        }
        return Ok(TlaExpr::Range(
            Box::new(parse_expr(&arr[0])?),
            Box::new(parse_expr(&arr[1])?),
        ));
    }

    // Domain: {"domain": f}
    if let Some(f) = obj.get("domain") {
        return Ok(TlaExpr::Domain(Box::new(parse_expr(f)?)));
    }

    // Apply: {"apply": [f, x]}
    if let Some(arr) = obj.get("apply") {
        let arr = arr.as_array().ok_or("apply expects array")?;
        if arr.len() != 2 {
            return Err("apply expects [f, x]".to_string());
        }
        return Ok(TlaExpr::Apply(
            Box::new(parse_expr(&arr[0])?),
            Box::new(parse_expr(&arr[1])?),
        ));
    }

    Err(format!("Unknown expr object: {:?}", obj))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_formula() {
        let json: Value = serde_json::json!({"always": true});
        let formula = parse_formula(&json).expect("parse simple always formula");
        assert!(matches!(formula, TlaFormula::Always(_)));
    }

    #[test]
    fn test_parse_forall_in() {
        let json: Value = serde_json::json!({
            "forall_in": ["n", "Nat", true]
        });
        let formula = parse_formula(&json).expect("parse forall_in formula");
        if let TlaFormula::ForallIn(var, set, _body) = formula {
            assert_eq!(var, "n");
            assert!(matches!(*set, TlaExpr::Nat));
        } else {
            panic!("Expected ForallIn");
        }
    }

    #[test]
    fn test_parse_arithmetic() {
        let json: Value = serde_json::json!({
            "add": [{"var": "x"}, 1]
        });
        let expr = parse_expr(&json).expect("parse add arithmetic expression");
        if let TlaExpr::Arith(TlaArithOp::Add, _, _) = expr {
            // ok
        } else {
            panic!("Expected Arith Add");
        }
    }

    #[test]
    fn test_parse_leads_to() {
        let json: Value = serde_json::json!({
            "leads_to": [
                {"expr": {"lt": ["x", {"const": "MAX"}]}},
                {"eq": ["x", {"const": "MAX"}]}
            ]
        });
        let formula = parse_formula(&json).expect("parse leads_to formula");
        assert!(matches!(formula, TlaFormula::LeadsTo(_, _)));
    }
}
