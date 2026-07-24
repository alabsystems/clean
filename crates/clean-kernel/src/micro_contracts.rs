// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Verification-oriented contract checkpoints for the micro-checker.
//!
//! This module does not re-run the checker. It snapshots observable state around
//! a micro-check operation so tests and future Kani harnesses can assert the
//! most important behavioral contracts.

use crate::micro::{MicroCert, MicroError, MicroExpr, MicroLevel, MicroLiteral};
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) enum MicroOperation {
    #[default]
    Verify,
    Reduce,
    Substitute,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum MicroContractSpec {
    TermWellFormed,
    ReductionPreserves,
    TypeCheckSound,
    SubstitutionCorrect,
}
pub(crate) const MICRO_CONTRACTS: [MicroContractSpec; 4] = [
    MicroContractSpec::TermWellFormed,
    MicroContractSpec::ReductionPreserves,
    MicroContractSpec::TypeCheckSound,
    MicroContractSpec::SubstitutionCorrect,
];
#[derive(Clone, Debug, Default, PartialEq)]
pub(crate) struct MicroCheckpoint {
    pub operation: MicroOperation,
    pub context_depth_before: usize,
    pub context_depth_after: usize,
    pub expr_before: Option<MicroExpr>,
    pub expr_after: Option<MicroExpr>,
    pub cert: Option<MicroCert>,
    pub substitution_value: Option<MicroExpr>,
    pub before_type: Option<MicroExpr>,
    pub after_type: Option<MicroExpr>,
    pub observed_result: Option<Result<MicroExpr, MicroError>>,
    pub expected_error: Option<MicroError>,
}
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct MicroContractVerdict {
    pub applicable: bool,
    pub holds: bool,
}
#[rustfmt::skip]
const fn ok(holds: bool) -> MicroContractVerdict { MicroContractVerdict { applicable: true, holds } }
#[rustfmt::skip]
const fn skip() -> MicroContractVerdict { MicroContractVerdict { applicable: false, holds: false } }

pub(crate) fn verify_micro_contract(
    spec: MicroContractSpec,
    checkpoint: &MicroCheckpoint,
) -> MicroContractVerdict {
    match spec {
        MicroContractSpec::TermWellFormed => {
            if !has_term_payload(checkpoint) {
                return skip();
            }
            ok(checkpoint_terms_well_formed(checkpoint))
        }
        MicroContractSpec::ReductionPreserves => match (
            checkpoint.operation,
            checkpoint.expr_before.as_ref(),
            checkpoint.expr_after.as_ref(),
            checkpoint.before_type.as_ref(),
            checkpoint.after_type.as_ref(),
        ) {
            (
                MicroOperation::Reduce,
                Some(before),
                Some(after),
                Some(before_ty),
                Some(after_ty),
            ) => ok(
                checkpoint.context_depth_before == checkpoint.context_depth_after
                    && checkpoint_terms_well_formed(checkpoint)
                    && expr_def_eq(&whnf(before), after)
                    && expr_def_eq(before_ty, after_ty),
            ),
            _ => skip(),
        },
        MicroContractSpec::TypeCheckSound => match (
            checkpoint.operation,
            checkpoint.expr_before.as_ref(),
            checkpoint.cert.as_ref(),
            checkpoint.observed_result.as_ref(),
        ) {
            (MicroOperation::Verify, Some(expr), Some(cert), Some(result)) => match result {
                Ok(ty) => ok(checkpoint_terms_well_formed(checkpoint)
                    && cert_matches_expr(cert, expr)
                    && checkpoint.context_depth_before == checkpoint.context_depth_after
                    && checkpoint
                        .after_type
                        .as_ref()
                        .is_some_and(|expected| expr_def_eq(expected, ty))),
                Err(err) => ok(checkpoint_terms_well_formed(checkpoint)
                    && checkpoint.expected_error.as_ref() == Some(err)),
            },
            _ => skip(),
        },
        MicroContractSpec::SubstitutionCorrect => match (
            checkpoint.operation,
            checkpoint.expr_before.as_ref(),
            checkpoint.expr_after.as_ref(),
            checkpoint.substitution_value.as_ref(),
        ) {
            (MicroOperation::Substitute, Some(before), Some(after), Some(value)) => ok(checkpoint
                .context_depth_before
                == checkpoint.context_depth_after.saturating_add(1)
                && checkpoint_terms_well_formed(checkpoint)
                && *after == before.instantiate(value)),
            _ => skip(),
        },
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct MicroContractReport {
    pub checked: usize,
    pub held: Vec<MicroContractSpec>,
    pub failed: Vec<MicroContractSpec>,
}

impl MicroContractReport {
    pub(crate) fn from_checkpoint(checkpoint: &MicroCheckpoint) -> Self {
        let mut report = Self::default();
        for spec in MICRO_CONTRACTS {
            let verdict = verify_micro_contract(spec, checkpoint);
            if verdict.applicable {
                report.checked += 1;
                if verdict.holds {
                    report.held.push(spec);
                } else {
                    report.failed.push(spec);
                }
            }
        }
        report
    }
    pub(crate) fn all_hold(&self) -> bool {
        self.failed.is_empty()
    }
}

fn has_term_payload(checkpoint: &MicroCheckpoint) -> bool {
    checkpoint.expr_before.is_some()
        || checkpoint.expr_after.is_some()
        || checkpoint.cert.is_some()
        || checkpoint.substitution_value.is_some()
        || checkpoint.before_type.is_some()
        || checkpoint.after_type.is_some()
        || checkpoint.observed_result.is_some()
}

fn checkpoint_terms_well_formed(checkpoint: &MicroCheckpoint) -> bool {
    let before = match u32::try_from(checkpoint.context_depth_before) {
        Ok(depth) => depth,
        Err(_) => return false,
    };
    let after = match u32::try_from(checkpoint.context_depth_after) {
        Ok(depth) => depth,
        Err(_) => return false,
    };

    checkpoint
        .expr_before
        .as_ref()
        .is_none_or(|expr| expr_well_formed(expr, before))
        && checkpoint
            .expr_after
            .as_ref()
            .is_none_or(|expr| expr_well_formed(expr, after))
        && checkpoint
            .cert
            .as_ref()
            .is_none_or(|cert| cert_well_formed(cert, before))
        && checkpoint
            .substitution_value
            .as_ref()
            .is_none_or(|expr| expr_well_formed(expr, after))
        && checkpoint
            .before_type
            .as_ref()
            .is_none_or(|expr| expr_well_formed(expr, before))
        && checkpoint
            .after_type
            .as_ref()
            .is_none_or(|expr| expr_well_formed(expr, after))
        && checkpoint
            .observed_result
            .as_ref()
            .is_none_or(|result| match result {
                Ok(expr) => expr_well_formed(expr, after),
                Err(_) => true,
            })
}

fn expr_well_formed(expr: &MicroExpr, depth: u32) -> bool {
    match expr {
        MicroExpr::BVar(idx) => *idx < depth,
        MicroExpr::Sort(level) => level_well_formed(level),
        MicroExpr::App(fun, arg) => expr_well_formed(fun, depth) && expr_well_formed(arg, depth),
        MicroExpr::Lam(ty, body) | MicroExpr::Pi(ty, body) => {
            expr_well_formed(ty, depth) && expr_well_formed(body, depth.saturating_add(1))
        }
        MicroExpr::Let(ty, val, body) => {
            expr_well_formed(ty, depth)
                && expr_well_formed(val, depth)
                && expr_well_formed(body, depth.saturating_add(1))
        }
        MicroExpr::Opaque(ty) => expr_well_formed(ty, depth),
        MicroExpr::Lit(MicroLiteral::Nat(_)) | MicroExpr::Lit(MicroLiteral::String(_)) => true,
        MicroExpr::Proj(_, expr) => expr_well_formed(expr, depth),
        // Constants are closed (no free BVars), hence always well-formed at
        // any depth. Their resolution against the read-only MicroEnv happens
        // during checking, not here.
        MicroExpr::Const(_) => true,
    }
}

fn cert_well_formed(cert: &MicroCert, depth: u32) -> bool {
    match cert {
        MicroCert::Sort { level } => level_well_formed(level),
        MicroCert::BVar { idx, ty } => *idx < depth && expr_well_formed(ty, depth),
        MicroCert::Opaque { ty } => expr_well_formed(ty, depth),
        // A Const cert is well-formed iff its carried (instantiated) type is.
        // The name is resolved against the read-only MicroEnv at check time.
        MicroCert::Const { ty, .. } => expr_well_formed(ty, depth),
        MicroCert::App {
            fn_cert,
            arg_cert,
            result_ty,
        } => {
            cert_well_formed(fn_cert, depth)
                && cert_well_formed(arg_cert, depth)
                && expr_well_formed(result_ty, depth)
        }
        MicroCert::Lam {
            arg_ty_cert,
            body_cert,
            result_ty,
        } => {
            cert_well_formed(arg_ty_cert, depth)
                && cert_well_formed(body_cert, depth.saturating_add(1))
                && expr_well_formed(result_ty, depth)
        }
        MicroCert::Pi {
            arg_ty_cert,
            arg_level,
            body_ty_cert,
            body_level,
        } => {
            cert_well_formed(arg_ty_cert, depth)
                && level_well_formed(arg_level)
                && cert_well_formed(body_ty_cert, depth.saturating_add(1))
                && level_well_formed(body_level)
        }
        MicroCert::Let {
            ty_cert,
            val_cert,
            body_cert,
            result_ty,
        } => {
            cert_well_formed(ty_cert, depth)
                && cert_well_formed(val_cert, depth)
                && cert_well_formed(body_cert, depth.saturating_add(1))
                && expr_well_formed(result_ty, depth)
        }
        MicroCert::Lit { ty, .. } => expr_well_formed(ty, depth),
        MicroCert::Proj {
            expr_cert,
            field_ty,
            ..
        } => cert_well_formed(expr_cert, depth) && expr_well_formed(field_ty, depth),
    }
}

fn level_well_formed(level: &MicroLevel) -> bool {
    match level {
        MicroLevel::Zero => true,
        MicroLevel::Succ(inner) => level_well_formed(inner),
        MicroLevel::Max(lhs, rhs) | MicroLevel::IMax(lhs, rhs) => {
            level_well_formed(lhs) && level_well_formed(rhs)
        }
    }
}

fn cert_matches_expr(cert: &MicroCert, expr: &MicroExpr) -> bool {
    match (cert, expr) {
        (MicroCert::Sort { level }, MicroExpr::Sort(actual)) => level.level_eq(actual),
        (MicroCert::BVar { idx, .. }, MicroExpr::BVar(actual)) => idx == actual,
        (MicroCert::Opaque { .. }, MicroExpr::Opaque(_)) => true,
        (
            MicroCert::App {
                fn_cert, arg_cert, ..
            },
            MicroExpr::App(fun, arg),
        ) => cert_matches_expr(fn_cert, fun) && cert_matches_expr(arg_cert, arg),
        (
            MicroCert::Lam {
                arg_ty_cert,
                body_cert,
                ..
            },
            MicroExpr::Lam(arg_ty, body),
        ) => cert_matches_expr(arg_ty_cert, arg_ty) && cert_matches_expr(body_cert, body),
        (
            MicroCert::Pi {
                arg_ty_cert,
                body_ty_cert,
                ..
            },
            MicroExpr::Pi(arg_ty, body_ty),
        ) => cert_matches_expr(arg_ty_cert, arg_ty) && cert_matches_expr(body_ty_cert, body_ty),
        (
            MicroCert::Let {
                ty_cert,
                val_cert,
                body_cert,
                ..
            },
            MicroExpr::Let(ty, val, body),
        ) => {
            cert_matches_expr(ty_cert, ty)
                && cert_matches_expr(val_cert, val)
                && cert_matches_expr(body_cert, body)
        }
        (MicroCert::Lit { lit, .. }, MicroExpr::Lit(actual)) => lit == actual,
        (MicroCert::Proj { idx, expr_cert, .. }, MicroExpr::Proj(actual_idx, expr)) => {
            idx == actual_idx && cert_matches_expr(expr_cert, expr)
        }
        _ => false,
    }
}

fn whnf(expr: &MicroExpr) -> MicroExpr {
    match expr {
        MicroExpr::App(fun, arg) => {
            let fun_whnf = whnf(fun);
            match &fun_whnf {
                MicroExpr::Lam(_, body) => whnf(&body.instantiate(arg)),
                _ => MicroExpr::App(fun_whnf.into(), arg.clone()),
            }
        }
        MicroExpr::Let(_, val, body) => whnf(&body.instantiate(val)),
        _ => expr.clone(),
    }
}
fn expr_def_eq(lhs: &MicroExpr, rhs: &MicroExpr) -> bool {
    structural_eq(&whnf(lhs), &whnf(rhs))
}

fn structural_eq(lhs: &MicroExpr, rhs: &MicroExpr) -> bool {
    match (lhs, rhs) {
        (MicroExpr::BVar(i), MicroExpr::BVar(j)) => i == j,
        (MicroExpr::Sort(l1), MicroExpr::Sort(l2)) => l1.level_eq(l2),
        (MicroExpr::App(f1, a1), MicroExpr::App(f2, a2)) => {
            structural_eq(f1, f2) && structural_eq(a1, a2)
        }
        (MicroExpr::Lam(t1, b1), MicroExpr::Lam(t2, b2))
        | (MicroExpr::Pi(t1, b1), MicroExpr::Pi(t2, b2)) => {
            structural_eq(t1, t2) && structural_eq(b1, b2)
        }
        (MicroExpr::Let(t1, v1, b1), MicroExpr::Let(t2, v2, b2)) => {
            structural_eq(t1, t2) && structural_eq(v1, v2) && structural_eq(b1, b2)
        }
        (MicroExpr::Opaque(t1), MicroExpr::Opaque(t2)) => structural_eq(t1, t2),
        (MicroExpr::Lit(l1), MicroExpr::Lit(l2)) => l1 == l2,
        (MicroExpr::Proj(i1, e1), MicroExpr::Proj(i2, e2)) => i1 == i2 && structural_eq(e1, e2),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    #[rustfmt::skip]
    use super::{
        verify_micro_contract, MicroCheckpoint, MicroContractReport, MicroContractSpec,
        MicroOperation,
    };
    use crate::micro::{MicroCert, MicroChecker, MicroError, MicroExpr, MicroLevel};
    use std::sync::Arc;
    #[rustfmt::skip] fn l0() -> MicroLevel { MicroLevel::Zero }
    #[rustfmt::skip] fn l1() -> MicroLevel { MicroLevel::succ(l0()) }
    #[rustfmt::skip] fn sort(level: MicroLevel) -> MicroExpr { MicroExpr::Sort(level) }
    #[rustfmt::skip] fn bvar(idx: u32) -> MicroExpr { MicroExpr::BVar(idx) }
    #[rustfmt::skip] fn app(fun: MicroExpr, arg: MicroExpr) -> MicroExpr { MicroExpr::App(Arc::new(fun), Arc::new(arg)) }
    #[rustfmt::skip] fn lam(ty: MicroExpr, body: MicroExpr) -> MicroExpr { MicroExpr::Lam(Arc::new(ty), Arc::new(body)) }
    #[rustfmt::skip] fn pi(ty: MicroExpr, body: MicroExpr) -> MicroExpr { MicroExpr::Pi(Arc::new(ty), Arc::new(body)) }

    #[test]
    fn verify_checkpoints_cover_success_and_expected_rejection() {
        let mut checker = MicroChecker::new();
        let prop = sort(l0());
        let expr = lam(prop.clone(), bvar(0));
        let type1 = sort(l1());
        let expected_ty = pi(prop.clone(), prop.clone());
        let cert = MicroCert::Lam {
            arg_ty_cert: Box::new(MicroCert::Sort { level: l0() }),
            body_cert: Box::new(MicroCert::BVar {
                idx: 0,
                ty: Box::new(prop.clone()),
            }),
            result_ty: Box::new(expected_ty.clone()),
        };
        let before = checker.context_depth();
        let observed_result = checker.verify(&cert, &expr);
        let after = checker.context_depth();

        let checkpoint = MicroCheckpoint {
            operation: MicroOperation::Verify,
            context_depth_before: before,
            observed_result: Some(observed_result),
            context_depth_after: after,
            expr_before: Some(expr.clone()),
            cert: Some(cert),
            after_type: Some(expected_ty),
            ..MicroCheckpoint::default()
        };

        let report = MicroContractReport::from_checkpoint(&checkpoint);
        assert_eq!(report.checked, 2);
        assert!(report.all_hold());
        assert!(report.held.contains(&MicroContractSpec::TermWellFormed));
        assert!(report.held.contains(&MicroContractSpec::TypeCheckSound));
        let cert = MicroCert::Lam {
            arg_ty_cert: Box::new(MicroCert::Sort { level: l0() }),
            body_cert: Box::new(MicroCert::BVar {
                idx: 0,
                ty: Box::new(type1.clone()),
            }),
            result_ty: Box::new(pi(prop.clone(), prop.clone())),
        };
        let before = checker.context_depth();
        let observed_result = checker.verify(&cert, &expr);
        let after = checker.context_depth();

        let checkpoint = MicroCheckpoint {
            operation: MicroOperation::Verify,
            context_depth_before: before,
            observed_result: Some(observed_result),
            context_depth_after: after,
            expr_before: Some(expr),
            cert: Some(cert),
            expected_error: Some(MicroError::TypeMismatch {
                expected: prop,
                actual: type1,
            }),
            ..MicroCheckpoint::default()
        };

        assert!(verify_micro_contract(MicroContractSpec::TypeCheckSound, &checkpoint).holds);
    }

    #[test]
    fn reduction_contract_requires_type_preservation() {
        let arg = sort(l0());
        let expr = app(lam(sort(l1()), bvar(0)), arg.clone());
        let checkpoint = MicroCheckpoint {
            operation: MicroOperation::Reduce,
            context_depth_before: 0,
            context_depth_after: 0,
            expr_before: Some(expr),
            expr_after: Some(arg),
            before_type: Some(sort(l1())),
            after_type: Some(sort(l1())),
            ..MicroCheckpoint::default()
        };

        assert!(verify_micro_contract(MicroContractSpec::ReductionPreserves, &checkpoint).holds);
    }

    #[test]
    fn broken_substitution_is_reported() {
        let checkpoint = MicroCheckpoint {
            operation: MicroOperation::Substitute,
            context_depth_before: 1,
            context_depth_after: 0,
            expr_before: Some(bvar(0)),
            expr_after: Some(sort(l1())),
            substitution_value: Some(sort(l0())),
            ..MicroCheckpoint::default()
        };

        let report = MicroContractReport::from_checkpoint(&checkpoint);
        assert_eq!(report.checked, 2);
        assert!(report
            .failed
            .contains(&MicroContractSpec::SubstitutionCorrect));
        assert!(!report.all_hold());
    }
}
