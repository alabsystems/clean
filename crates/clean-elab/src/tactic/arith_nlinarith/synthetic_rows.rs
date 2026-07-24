// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof-carrying synthetic row builders for `nlinarith`.

use clean_kernel::name::Name;
use clean_kernel::Level;
use clean_kernel::{Expr, FVarId};

use super::super::arith_linarith::{extract_certified_linear_constraints, CertifiedConstraint};
use super::super::arith_linarith_proof::build_scaled_proof;
use super::super::{match_le, Goal, LocalDecl, ProofState};
use super::NlinarithConfig;
use crate::tactic::tc_app::{mk_tc_rel, rel_inst_for_type};
use crate::tactic::{LinearConstraint, LinearExpr};

#[derive(Debug, Clone)]
pub(crate) struct SyntheticRowDecl {
    pub(crate) decl: LocalDecl,
    pub(crate) proof_value: Expr,
}

#[derive(Debug, Clone)]
struct LeHypRow {
    expr: LinearExpr,
    hyp_index: usize,
}

fn is_one_hot_hyp(certificate: &[i128], hyp_index: usize) -> bool {
    certificate
        .iter()
        .enumerate()
        .all(|(idx, &coeff)| (idx == hyp_index && coeff == 1) || (idx != hyp_index && coeff == 0))
}

fn source_le_row(
    goal: &Goal,
    certified_constraints: &[CertifiedConstraint],
    hyp_fvar: FVarId,
    hyp_index: usize,
) -> Option<LeHypRow> {
    let decl = goal.local_ctx.iter().find(|decl| decl.fvar == hyp_fvar)?;
    let _ = match_le(&decl.ty)?;

    let expr = certified_constraints.iter().find_map(|constraint| {
        if !is_one_hot_hyp(&constraint.certificate.coefficients, hyp_index) {
            return None;
        }

        match &constraint.constraint {
            LinearConstraint::Le(expr) => Some(expr.clone()),
            _ => None,
        }
    })?;

    Some(LeHypRow { expr, hyp_index })
}

fn scaled_source_hyp(left: &LeHypRow, right: &LeHypRow) -> Option<(usize, i128)> {
    if left.expr.is_constant() {
        return scaled_source_hyp_from_constant(left, right);
    }

    if right.expr.is_constant() {
        return scaled_source_hyp_from_constant(right, left);
    }

    None
}

fn scaled_source_hyp_from_constant(
    constant_row: &LeHypRow,
    source_row: &LeHypRow,
) -> Option<(usize, i128)> {
    if source_row.expr.is_constant() {
        return None;
    }

    let factor = i128::from(constant_row.expr.constant.checked_neg()?);
    (factor > 1).then_some((source_row.hyp_index, factor))
}

fn build_synthetic_row_decl(
    state: &mut ProofState,
    goal: &Goal,
    hypothesis_fvars: &[FVarId],
    source_hyp_index: usize,
    scale_factor: i128,
) -> Option<SyntheticRowDecl> {
    let source_fvar = *hypothesis_fvars.get(source_hyp_index)?;
    let source_decl = goal
        .local_ctx
        .iter()
        .find(|decl| decl.fvar == source_fvar)?;
    let instantiated_source_ty = state.metas.instantiate(&source_decl.ty);
    let (alpha, lhs, rhs) = match_le(&instantiated_source_ty)?;

    let proof_value =
        build_scaled_proof(&[(source_hyp_index, scale_factor)], hypothesis_fvars, goal)?;
    let inferred_ty = state.infer_type(goal, &proof_value).ok()?;
    let proof_ty = build_scaled_le_type(&alpha, &lhs, &rhs, scale_factor)?;
    if !state.is_def_eq(goal, &inferred_ty, &proof_ty) {
        return None;
    }

    let fvar = state.fresh_fvar();
    let decl = LocalDecl {
        fvar,
        name: format!("nlinarith_synth_{}", fvar.as_u64()),
        ty: proof_ty,
        value: Some(proof_value.clone()),
    };

    Some(SyntheticRowDecl { decl, proof_value })
}

fn build_scaled_le_type(alpha: &Expr, lhs: &Expr, rhs: &Expr, scale_factor: i128) -> Option<Expr> {
    let coeff = coeff_expr(alpha, scale_factor)?;
    let scaled_lhs = mul_app(alpha, &coeff, lhs)?;
    let scaled_rhs = mul_app(alpha, &coeff, rhs)?;
    Some(mk_tc_rel(
        Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
        alpha.clone(),
        rel_inst_for_type(alpha, "LE.le"),
        scaled_lhs,
        scaled_rhs,
    ))
}

fn coeff_expr(alpha: &Expr, scale_factor: i128) -> Option<Expr> {
    if scale_factor <= 0 {
        return None;
    }

    let scale_nat = u64::try_from(scale_factor).ok()?;

    match alpha.kind() {
        clean_kernel::expr::ExprKind::Const(name, _) if name == &Name::from_string("Nat") => {
            Some(Expr::nat_lit(scale_nat))
        }
        clean_kernel::expr::ExprKind::Const(name, _) if name == &Name::from_string("Int") => {
            Some(Expr::app(
                Expr::const_(Name::from_string("Int.ofNat"), vec![]),
                Expr::nat_lit(scale_nat),
            ))
        }
        clean_kernel::expr::ExprKind::Const(name, _) if name == &Name::from_string("Rat") => {
            Some(Expr::app(
                Expr::const_(Name::from_string("Rat.ofInt"), vec![]),
                Expr::app(
                    Expr::const_(Name::from_string("Int.ofNat"), vec![]),
                    Expr::nat_lit(scale_nat),
                ),
            ))
        }
        clean_kernel::expr::ExprKind::Const(name, _) if name == &Name::from_string("Real") => {
            Some(Expr::app(
                Expr::const_(Name::from_string("Real.ofInt"), vec![]),
                Expr::app(
                    Expr::const_(Name::from_string("Int.ofNat"), vec![]),
                    Expr::nat_lit(scale_nat),
                ),
            ))
        }
        _ => None,
    }
}

fn mul_app(alpha: &Expr, lhs: &Expr, rhs: &Expr) -> Option<Expr> {
    if matches!(
        alpha.kind(),
        clean_kernel::expr::ExprKind::Const(name, _) if name == &Name::from_string("Nat")
    ) {
        let zero = Expr::nat_lit(0);
        if lhs == &zero || rhs == &zero {
            return Some(zero);
        }
    }

    let mul_name = match alpha.kind() {
        clean_kernel::expr::ExprKind::Const(name, _) if name == &Name::from_string("Nat") => {
            "Nat.mul"
        }
        clean_kernel::expr::ExprKind::Const(name, _) if name == &Name::from_string("Int") => {
            "Int.mul"
        }
        clean_kernel::expr::ExprKind::Const(name, _) if name == &Name::from_string("Rat") => {
            "Rat.mul"
        }
        clean_kernel::expr::ExprKind::Const(name, _) if name == &Name::from_string("Real") => {
            "Real.mul"
        }
        _ => return None,
    };

    Some(Expr::app(
        Expr::app(
            Expr::const_(Name::from_string(mul_name), vec![]),
            lhs.clone(),
        ),
        rhs.clone(),
    ))
}

pub(crate) fn build_synthetic_row_decls(
    state: &mut ProofState,
    goal: &Goal,
    config: &NlinarithConfig,
) -> Vec<SyntheticRowDecl> {
    let Some((certified_constraints, _var_map, hypothesis_fvars)) =
        extract_certified_linear_constraints(state, goal)
    else {
        return Vec::new();
    };

    let le_rows: Vec<LeHypRow> = hypothesis_fvars
        .iter()
        .enumerate()
        .filter_map(|(hyp_index, &hyp_fvar)| {
            source_le_row(goal, &certified_constraints, hyp_fvar, hyp_index)
        })
        .collect();

    let mut synthetic_rows = Vec::new();
    for i in 0..le_rows.len() {
        if synthetic_rows.len() >= config.max_products {
            break;
        }

        for j in i..le_rows.len() {
            if synthetic_rows.len() >= config.max_products {
                break;
            }

            let Some((source_hyp_index, scale_factor)) =
                scaled_source_hyp(&le_rows[i], &le_rows[j])
            else {
                continue;
            };

            if let Some(synthetic_row) = build_synthetic_row_decl(
                state,
                goal,
                &hypothesis_fvars,
                source_hyp_index,
                scale_factor,
            ) {
                synthetic_rows.push(synthetic_row);
            }
        }
    }

    synthetic_rows
}
