// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! AC-reflexivity tactic and normalization engine.
//!
//! Proves equality by checking if both sides are equal up to associativity
//! and commutativity of operations. Split from norm.rs for file size (#307).

use clean_kernel::{Expr, ExprKind};

use super::arith_field_simp::get_app_fn;
use super::core::{ProofState, TacticError, TacticResult};
use super::equality::match_equality;
use super::proof_term::rfl;
use crate::stack_safe;

/// AC-reflexivity tactic.
///
/// Proves equality by checking if both sides are equal up to associativity
/// and commutativity of operations. Useful for equations that are trivially
/// equal modulo AC.
///
/// # Supported Operations
/// - Addition (commutative, associative)
/// - Multiplication (commutative, associative)
/// - Boolean operations (and, or)
/// - Set operations (union, intersection)
///
/// # Example
/// ```text
/// -- Goal: a + b + c = c + a + b
/// ac_rfl
/// -- Goal closed
/// ```
///
/// # Errors
/// - `NoGoals` if there are no goals
/// - `GoalMismatch` if goal is not an equality
/// - `Other` if sides are not AC-equal
pub fn ac_rfl(state: &mut ProofState) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Check that goal is an equality
    let (_ty, lhs, rhs, _levels) = match_equality(&goal.target)
        .map_err(|_| TacticError::GoalMismatch("ac_rfl: goal is not an equality".to_string()))?;

    // Normalize both sides using AC normalization
    let lhs_norm = ac_normalize(&lhs);
    let rhs_norm = ac_normalize(&rhs);

    // Check if normalized forms are equal
    if ac_exprs_equal(&lhs_norm, &rhs_norm) {
        rfl(state)
    } else {
        Err(TacticError::ArithmeticFailed {
            tactic: "ac_rfl".to_string(),
            reason: format!("sides not AC-equal:\n  LHS: {lhs_norm:?}\n  RHS: {rhs_norm:?}"),
        })
    }
}

/// AC-normalized expression representation
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum ACExpr {
    /// A constant or variable (atomic)
    Atom(String),
    /// Commutative-associative operation with sorted operands
    CAOp { op: String, operands: Vec<ACExpr> },
    /// Non-AC application
    App(Box<ACExpr>, Box<ACExpr>),
    /// Lambda
    Lambda(Box<ACExpr>, Box<ACExpr>),
    /// Bound variable
    BVar(usize),
}

/// Normalize expression for AC equality.
///
/// # Contract
///
/// REQUIRES: `expr` is a well-formed expression
/// ENSURES: Result is a canonical form under associativity/commutativity
/// ENSURES: If `a` and `b` are AC-equal, `ac_normalize(a) == ac_normalize(b)`
/// ENSURES: CAOp operands are sorted for canonical ordering
/// ENSURES: Recursion terminates via `stack_safe` guard
pub(crate) fn ac_normalize(expr: &Expr) -> ACExpr {
    stack_safe(|| match expr.kind() {
        ExprKind::BVar(idx) => ACExpr::BVar(*idx as usize),
        ExprKind::FVar(id) => ACExpr::Atom(format!("fvar_{}", id.as_u64())),
        ExprKind::Const(name, _) => ACExpr::Atom(name.to_string()),
        ExprKind::Lit(lit) => ACExpr::Atom(format!("{lit:?}")),
        ExprKind::Sort(level) => ACExpr::Atom(format!("Sort_{level:?}")),

        ExprKind::App(f, arg) => {
            // Check for AC operations
            if let Some((op_name, operands)) = extract_ac_operation(expr) {
                // Recursively normalize operands and sort them
                let mut normalized: Vec<ACExpr> =
                    operands.iter().map(|e| ac_normalize(e)).collect();
                normalized.sort();

                return ACExpr::CAOp {
                    op: op_name,
                    operands: normalized,
                };
            }

            // Regular application
            ACExpr::App(Box::new(ac_normalize(f)), Box::new(ac_normalize(arg)))
        }

        ExprKind::Lam(_, ty, body) => {
            ACExpr::Lambda(Box::new(ac_normalize(ty)), Box::new(ac_normalize(body)))
        }

        ExprKind::Pi(_, ty, body) => {
            // Treat Pi as a special app for AC purposes
            ACExpr::App(
                Box::new(ACExpr::Atom("Pi".to_string())),
                Box::new(ACExpr::App(
                    Box::new(ac_normalize(ty)),
                    Box::new(ac_normalize(body)),
                )),
            )
        }

        ExprKind::Let(_, ty, val, body, _) => ACExpr::App(
            Box::new(ACExpr::Atom("Let".to_string())),
            Box::new(ACExpr::App(
                Box::new(ac_normalize(ty)),
                Box::new(ACExpr::App(
                    Box::new(ac_normalize(val)),
                    Box::new(ac_normalize(body)),
                )),
            )),
        ),

        ExprKind::Proj(name, idx, e) => ACExpr::App(
            Box::new(ACExpr::Atom(format!("Proj_{name}_{idx}"))),
            Box::new(ac_normalize(e)),
        ),

        ExprKind::MData(_, inner) => ac_normalize(inner),

        // Mode-specific expressions - treat as atoms
        ExprKind::CubicalInterval => ACExpr::Atom("CubicalI".to_string()),
        ExprKind::CubicalI0 => ACExpr::Atom("I0".to_string()),
        ExprKind::CubicalI1 => ACExpr::Atom("I1".to_string()),
        ExprKind::CubicalPath { .. } => ACExpr::Atom("Path".to_string()),
        ExprKind::CubicalPathLam { .. } => ACExpr::Atom("PathLam".to_string()),
        ExprKind::CubicalPathApp { .. } => ACExpr::Atom("PathApp".to_string()),
        ExprKind::CubicalHComp { .. } => ACExpr::Atom("HComp".to_string()),
        ExprKind::CubicalTransp { .. } => ACExpr::Atom("Transp".to_string()),
        ExprKind::CubicalCoe { .. } => ACExpr::Atom("Coe".to_string()),
        ExprKind::ZFCSet(_) => ACExpr::Atom("ZFCSet".to_string()),
        ExprKind::ZFCMem { .. } => ACExpr::Atom("ZFCMem".to_string()),
        ExprKind::ZFCComprehension { .. } => ACExpr::Atom("ZFCComp".to_string()),
        ExprKind::SProp => ACExpr::Atom("SProp".to_string()),
        ExprKind::Squash(inner) => ACExpr::App(
            Box::new(ACExpr::Atom("Squash".to_string())),
            Box::new(ac_normalize(inner)),
        ),
    })
}

/// Extract AC operation and its operands from an expression
fn extract_ac_operation(expr: &Expr) -> Option<(String, Vec<&Expr>)> {
    // Check if this is a binary application of an AC operator
    if let ExprKind::App(f, _arg2) = expr.kind() {
        if let ExprKind::App(f2, _arg1) = f.as_ref().kind() {
            // Try to get the operator name
            let op_name = get_ac_op_name(f2)?;

            // Flatten nested applications of the same operator
            let mut operands = Vec::new();
            flatten_ac_operands(expr, &op_name, &mut operands);

            if operands.len() >= 2 {
                return Some((op_name, operands));
            }
        }
    }
    None
}

/// Get AC operator name if this is an AC operator
pub(crate) fn get_ac_op_name(expr: &Expr) -> Option<String> {
    match get_app_fn(expr).kind() {
        ExprKind::Const(name, _) => {
            let name_str = name.to_string();

            // Known commutative-associative operations
            if name_str.contains("Add")
                || name_str.contains("add")
                || name_str.contains("HAdd.hAdd")
            {
                return Some("add".to_string());
            }
            if name_str.contains("Mul")
                || name_str.contains("mul")
                || name_str.contains("HMul.hMul")
            {
                return Some("mul".to_string());
            }
            if name_str.contains("And") || name_str.contains("and") {
                return Some("and".to_string());
            }
            if name_str.contains("Or") || name_str.contains("or") {
                return Some("or".to_string());
            }
            if name_str.contains("Union") || name_str.contains("union") {
                return Some("union".to_string());
            }
            if name_str.contains("Inter") || name_str.contains("inter") {
                return Some("inter".to_string());
            }
            if name_str.contains("Max") || name_str.contains("max") {
                return Some("max".to_string());
            }
            if name_str.contains("Min") || name_str.contains("min") {
                return Some("min".to_string());
            }

            None
        }
        _ => None,
    }
}

/// Flatten nested applications of an AC operator
fn flatten_ac_operands<'a>(expr: &'a Expr, target_op: &str, operands: &mut Vec<&'a Expr>) {
    stack_safe(|| {
        if let ExprKind::App(f, arg2) = expr.kind() {
            if let ExprKind::App(f2, arg1) = f.as_ref().kind() {
                if let Some(op) = get_ac_op_name(f2) {
                    if op == target_op {
                        // Recursively flatten
                        flatten_ac_operands(arg1, target_op, operands);
                        flatten_ac_operands(arg2, target_op, operands);
                        return;
                    }
                }
            }
        }
        // Not a matching application - this is a leaf
        operands.push(expr);
    })
}

/// Check if two AC expressions are equal
pub(crate) fn ac_exprs_equal(e1: &ACExpr, e2: &ACExpr) -> bool {
    stack_safe(|| match (e1, e2) {
        (ACExpr::Atom(s1), ACExpr::Atom(s2)) => s1 == s2,
        (ACExpr::BVar(i1), ACExpr::BVar(i2)) => i1 == i2,
        (
            ACExpr::CAOp {
                op: op1,
                operands: ops1,
            },
            ACExpr::CAOp {
                op: op2,
                operands: ops2,
            },
        ) => {
            if op1 != op2 || ops1.len() != ops2.len() {
                return false;
            }
            // Operands are already sorted, so just compare pairwise
            ops1.iter()
                .zip(ops2.iter())
                .all(|(a, b)| ac_exprs_equal(a, b))
        }
        (ACExpr::App(f1, a1), ACExpr::App(f2, a2)) => {
            ac_exprs_equal(f1, f2) && ac_exprs_equal(a1, a2)
        }
        (ACExpr::Lambda(t1, b1), ACExpr::Lambda(t2, b2)) => {
            ac_exprs_equal(t1, t2) && ac_exprs_equal(b1, b2)
        }
        _ => false,
    })
}
