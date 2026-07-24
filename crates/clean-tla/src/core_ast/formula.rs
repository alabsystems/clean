// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::expr::expr_from_core;
use super::shared::bound_name;
use crate::encoding::TlaFormula;
use crate::tla_core::ast as core_ast;
use crate::tla_core::Spanned;
use crate::TlaError;

pub(super) fn formula_from_core(expr: &Spanned<core_ast::Expr>) -> Result<TlaFormula, TlaError> {
    if let Some(converted) = convert_boolean_formula(expr)? {
        return Ok(converted);
    }
    if let Some(converted) = convert_quantifier_formula(expr)? {
        return Ok(converted);
    }
    if let Some(converted) = convert_relation_formula(expr)? {
        return Ok(converted);
    }
    if let Some(converted) = convert_temporal_formula(expr)? {
        return Ok(converted);
    }
    Ok(TlaFormula::Expr(expr_from_core(expr)?))
}

fn convert_boolean_formula(expr: &Spanned<core_ast::Expr>) -> Result<Option<TlaFormula>, TlaError> {
    match &expr.node {
        core_ast::Expr::Bool(value) => Ok(Some(if *value {
            TlaFormula::True
        } else {
            TlaFormula::False
        })),
        core_ast::Expr::And(lhs, rhs) => Ok(Some(TlaFormula::And(
            Box::new(formula_from_core(lhs)?),
            Box::new(formula_from_core(rhs)?),
        ))),
        core_ast::Expr::Or(lhs, rhs) => Ok(Some(TlaFormula::Or(
            Box::new(formula_from_core(lhs)?),
            Box::new(formula_from_core(rhs)?),
        ))),
        core_ast::Expr::Not(inner) => {
            Ok(Some(TlaFormula::Not(Box::new(formula_from_core(inner)?))))
        }
        core_ast::Expr::Implies(lhs, rhs) => Ok(Some(TlaFormula::Implies(
            Box::new(formula_from_core(lhs)?),
            Box::new(formula_from_core(rhs)?),
        ))),
        core_ast::Expr::Equiv(lhs, rhs) => Ok(Some(TlaFormula::Iff(
            Box::new(formula_from_core(lhs)?),
            Box::new(formula_from_core(rhs)?),
        ))),
        _ => Ok(None),
    }
}

fn convert_quantifier_formula(
    expr: &Spanned<core_ast::Expr>,
) -> Result<Option<TlaFormula>, TlaError> {
    match &expr.node {
        core_ast::Expr::Forall(bounds, body) => {
            convert_quantifier(bounds, body, Quantifier::Forall).map(Some)
        }
        core_ast::Expr::Exists(bounds, body) => {
            convert_quantifier(bounds, body, Quantifier::Exists).map(Some)
        }
        _ => Ok(None),
    }
}

/// Convert a (possibly tuple-pattern-bearing) quantifier.
///
/// Any tuple-pattern binder (`\E <<x, y>> \in S : P`) is first desugared into a
/// fresh single-name binder with the body rewritten to project the components
/// (`\E t \in S : P[x := t[1], y := t[2]]`); see
/// [`super::tuple_pattern::desugar_quantifier_bounds`]. The rewritten,
/// tuple-free bounds and body are then folded by [`fold_quantifiers`]. When no
/// binder uses a tuple pattern the original nodes are folded directly (no
/// allocation).
fn convert_quantifier(
    bounds: &[core_ast::BoundVar],
    body: &Spanned<core_ast::Expr>,
    quantifier: Quantifier,
) -> Result<TlaFormula, TlaError> {
    let context = match quantifier {
        Quantifier::Forall => "\\A quantifier",
        Quantifier::Exists => "\\E quantifier",
    };
    match super::tuple_pattern::desugar_quantifier_bounds(bounds, body, context)? {
        Some((desugared_bounds, desugared_body)) => {
            fold_quantifiers(&desugared_bounds, &desugared_body, quantifier)
        }
        None => fold_quantifiers(bounds, body, quantifier),
    }
}

fn convert_relation_formula(
    expr: &Spanned<core_ast::Expr>,
) -> Result<Option<TlaFormula>, TlaError> {
    match &expr.node {
        core_ast::Expr::Eq(lhs, rhs) => Ok(Some(TlaFormula::Eq(
            Box::new(expr_from_core(lhs)?),
            Box::new(expr_from_core(rhs)?),
        ))),
        core_ast::Expr::Neq(lhs, rhs) => Ok(Some(TlaFormula::Not(Box::new(TlaFormula::Eq(
            Box::new(expr_from_core(lhs)?),
            Box::new(expr_from_core(rhs)?),
        ))))),
        core_ast::Expr::In(lhs, rhs) => Ok(Some(TlaFormula::Mem(
            Box::new(expr_from_core(lhs)?),
            Box::new(expr_from_core(rhs)?),
        ))),
        core_ast::Expr::NotIn(lhs, rhs) => Ok(Some(TlaFormula::Not(Box::new(TlaFormula::Mem(
            Box::new(expr_from_core(lhs)?),
            Box::new(expr_from_core(rhs)?),
        ))))),
        core_ast::Expr::Subseteq(lhs, rhs) => Ok(Some(TlaFormula::Subset(
            Box::new(expr_from_core(lhs)?),
            Box::new(expr_from_core(rhs)?),
        ))),
        _ => Ok(None),
    }
}

fn convert_temporal_formula(
    expr: &Spanned<core_ast::Expr>,
) -> Result<Option<TlaFormula>, TlaError> {
    match &expr.node {
        core_ast::Expr::Always(inner) => Ok(Some(TlaFormula::Always(Box::new(formula_from_core(
            inner,
        )?)))),
        core_ast::Expr::Eventually(inner) => Ok(Some(TlaFormula::Eventually(Box::new(
            formula_from_core(inner)?,
        )))),
        core_ast::Expr::LeadsTo(lhs, rhs) => Ok(Some(TlaFormula::LeadsTo(
            Box::new(formula_from_core(lhs)?),
            Box::new(formula_from_core(rhs)?),
        ))),
        core_ast::Expr::WeakFair(vars, action) => Ok(Some(TlaFormula::WeakFairness(
            Box::new(expr_from_core(vars)?),
            Box::new(formula_from_core(action)?),
        ))),
        core_ast::Expr::StrongFair(vars, action) => Ok(Some(TlaFormula::StrongFairness(
            Box::new(expr_from_core(vars)?),
            Box::new(formula_from_core(action)?),
        ))),
        // UNCHANGED e ≡ e' = e. `e` is a value expression (a variable or tuple
        // of variables); the equality is expanded during translation.
        core_ast::Expr::Unchanged(vars) => {
            Ok(Some(TlaFormula::Unchanged(Box::new(expr_from_core(vars)?))))
        }
        // ENABLED A — A is an action (formula). Encoded as a primitive modality.
        core_ast::Expr::Enabled(action) => Ok(Some(TlaFormula::Enabled(Box::new(
            formula_from_core(action)?,
        )))),
        _ => Ok(None),
    }
}

enum Quantifier {
    Forall,
    Exists,
}

fn fold_quantifiers(
    bounds: &[core_ast::BoundVar],
    body: &Spanned<core_ast::Expr>,
    quantifier: Quantifier,
) -> Result<TlaFormula, TlaError> {
    let mut result = formula_from_core(body)?;
    for bound in bounds.iter().rev() {
        let name = bound_name(bound, "quantifier")?;
        result = match (&quantifier, &bound.domain) {
            (Quantifier::Forall, Some(domain)) => {
                TlaFormula::ForallIn(name, Box::new(expr_from_core(domain)?), Box::new(result))
            }
            (Quantifier::Forall, None) => TlaFormula::Forall(name, Box::new(result)),
            (Quantifier::Exists, Some(domain)) => {
                TlaFormula::ExistsIn(name, Box::new(expr_from_core(domain)?), Box::new(result))
            }
            (Quantifier::Exists, None) => TlaFormula::Exists(name, Box::new(result)),
        };
    }
    Ok(result)
}
