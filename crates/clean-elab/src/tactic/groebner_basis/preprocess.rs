// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::collections::{BTreeMap, HashMap};

use clean_kernel::{Expr, ExprKind, FVarId};

use super::super::polynomial::{expr_to_polynomial, Polynomial, VarMap};
use super::super::{match_equality, Goal, LinearConstraint, LinearExpr, ProofState};
use super::basis::GBasis;
use super::types::{
    GroebnerConfig, GroebnerResult, IntPolynomial, Monomial, PolynomialRelation, RelationKind,
};

/// Parse polynomial equalities/inequalities from the current proof state,
/// compute a Groebner basis for equality hypotheses, and feed any affine
/// consequences back into nlinarith as linear constraints.
pub(crate) fn groebner_preprocess(
    state: &ProofState,
    goal: &Goal,
    linear_var_map: &mut HashMap<FVarId, usize>,
    config: &GroebnerConfig,
) -> GroebnerResult {
    let mut poly_var_map = VarMap::new();
    let mut generators = Vec::new();
    let mut candidate_relations = Vec::new();

    for decl in &goal.local_ctx {
        let ty = state.metas.instantiate(&decl.ty);
        if let Some(relation) =
            parse_polynomial_relation_with_whnf(state, goal, &ty, &mut poly_var_map)
        {
            match relation.kind {
                RelationKind::Eq => generators.push(relation.polynomial.clone()),
                RelationKind::Le | RelationKind::Lt => candidate_relations.push(relation),
            }
        }
    }

    let target = state.metas.instantiate(&goal.target);
    if let Some(relation) =
        parse_polynomial_relation_with_whnf(state, goal, &target, &mut poly_var_map)
    {
        if let Some(negated_goal) = relation.negated_goal_relation() {
            candidate_relations.push(negated_goal);
        }
    }

    if generators.is_empty() {
        return GroebnerResult {
            linear_constraints: Vec::new(),
            nonnegativity_witnesses: Vec::new(),
        };
    }

    let basis = GBasis::compute(&generators, config);
    let mut linear_constraints = Vec::new();

    for basis_poly in basis.polynomials() {
        if let Some(linear_expr) =
            int_polynomial_to_linear_expr(basis_poly, &poly_var_map, linear_var_map)
        {
            let constraint = LinearConstraint::Eq(linear_expr);
            if !linear_constraints.contains(&constraint) {
                linear_constraints.push(constraint);
            }
        }
    }

    for relation in candidate_relations {
        let reduced = basis.reduce(&relation.polynomial);
        let Some(linear_expr) =
            int_polynomial_to_linear_expr(&reduced, &poly_var_map, linear_var_map)
        else {
            continue;
        };

        let constraint = match relation.kind {
            RelationKind::Eq => LinearConstraint::Eq(linear_expr),
            RelationKind::Le => LinearConstraint::Le(linear_expr),
            RelationKind::Lt => LinearConstraint::Lt(linear_expr),
        };
        if !linear_constraints.contains(&constraint) {
            linear_constraints.push(constraint);
        }
    }

    GroebnerResult {
        linear_constraints,
        nonnegativity_witnesses: Vec::new(),
    }
}

pub(super) fn parse_polynomial_relation_with_whnf(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
    poly_var_map: &mut VarMap,
) -> Option<PolynomialRelation> {
    parse_polynomial_relation(expr, poly_var_map).or_else(|| {
        let normalized = state.whnf(goal, expr);
        (normalized != *expr).then(|| parse_polynomial_relation(&normalized, poly_var_map))?
    })
}

fn parse_polynomial_relation(expr: &Expr, poly_var_map: &mut VarMap) -> Option<PolynomialRelation> {
    if let Ok((_ty, lhs, rhs, _levels)) = match_equality(expr) {
        let lhs_poly = expr_to_int_polynomial(&lhs, poly_var_map)?;
        let rhs_poly = expr_to_int_polynomial(&rhs, poly_var_map)?;
        return Some(PolynomialRelation {
            kind: RelationKind::Eq,
            polynomial: lhs_poly.sub(&rhs_poly),
        });
    }

    if let ExprKind::App(f1, rhs) = expr.kind() {
        if let ExprKind::App(f2, lhs) = f1.kind() {
            if let ExprKind::App(f3, _inst) = f2.kind() {
                if let ExprKind::App(f4, _ty) = f3.kind() {
                    if let ExprKind::Const(name, _) = f4.kind() {
                        let lhs_poly = expr_to_int_polynomial(lhs, poly_var_map)?;
                        let rhs_poly = expr_to_int_polynomial(rhs, poly_var_map)?;
                        let name = name.to_string();

                        if name.contains("LE.le") || name.contains("Nat.le") {
                            return Some(PolynomialRelation {
                                kind: RelationKind::Le,
                                polynomial: lhs_poly.sub(&rhs_poly),
                            });
                        }
                        if name.contains("LT.lt") || name.contains("Nat.lt") {
                            return Some(PolynomialRelation {
                                kind: RelationKind::Lt,
                                polynomial: lhs_poly.sub(&rhs_poly),
                            });
                        }
                        if name.contains("GE.ge") {
                            return Some(PolynomialRelation {
                                kind: RelationKind::Le,
                                polynomial: rhs_poly.sub(&lhs_poly),
                            });
                        }
                        if name.contains("GT.gt") {
                            return Some(PolynomialRelation {
                                kind: RelationKind::Lt,
                                polynomial: rhs_poly.sub(&lhs_poly),
                            });
                        }
                    }
                }
            }
        }
    }

    None
}

pub(super) fn expr_to_int_polynomial(
    expr: &Expr,
    poly_var_map: &mut VarMap,
) -> Option<IntPolynomial> {
    let poly = expr_to_polynomial(expr, poly_var_map)?;
    int_polynomial_from_polynomial(&poly)
}

fn int_polynomial_from_polynomial(poly: &Polynomial) -> Option<IntPolynomial> {
    let mut terms = BTreeMap::new();
    for (mono, (num, den)) in &poly.terms {
        if *den != 1 {
            return None;
        }

        let mono: Monomial = mono
            .iter()
            .map(|(var, exp)| Some((*var, u32::try_from(*exp).ok()?)))
            .collect::<Option<_>>()?;
        let entry = terms.entry(mono.clone()).or_insert(0i128);
        *entry = entry.saturating_add(i128::from(*num));
        if *entry == 0 {
            terms.remove(&mono);
        }
    }
    Some(IntPolynomial { terms })
}

fn int_polynomial_to_linear_expr(
    poly: &IntPolynomial,
    poly_var_map: &VarMap,
    linear_var_map: &mut HashMap<FVarId, usize>,
) -> Option<LinearExpr> {
    let mut expr = LinearExpr::constant(0);

    for (mono, coeff) in &poly.terms {
        let coeff = i64::try_from(*coeff).ok()?;
        match mono.as_slice() {
            [] => {
                expr.constant = expr.constant.checked_add(coeff)?;
            }
            [(poly_var_idx, 1)] => {
                let name = poly_var_map.name(*poly_var_idx)?;
                let fvar_id = parse_fvar_name(name)?;
                let linear_idx = match linear_var_map.get(&fvar_id) {
                    Some(idx) => *idx,
                    None => {
                        let idx = linear_var_map.len();
                        linear_var_map.insert(fvar_id, idx);
                        idx
                    }
                };

                expr.try_add_to_coeff(linear_idx, coeff)?;
            }
            _ => return None,
        }
    }

    Some(expr)
}

pub(super) fn parse_fvar_name(name: &str) -> Option<FVarId> {
    let id = name.strip_prefix("fvar_")?.parse::<u64>().ok()?;
    Some(FVarId::new(id))
}
