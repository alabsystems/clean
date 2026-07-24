// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Helper functions for HOL proof-rule translation.

use super::super::{
    HolLightImportError, HolTerm, HolTermSubstitution, HolTypeSubstitution, HolVar,
};
use super::context::{scope_args_in_context, Scope, ScopeBinderKind};
use super::term::{dest_eq, TermTranslator};
use crate::{BinderInfo, Expr, Level};

#[derive(Clone, Debug)]
pub(super) struct CheckedTheorem {
    pub(super) assumptions: Vec<HolTerm>,
    pub(super) conclusion: HolTerm,
    pub(super) proof: Expr,
}

pub(super) fn theorem_from_body(
    scope: &Scope,
    assumptions: Vec<HolTerm>,
    conclusion: HolTerm,
    body: Expr,
    translator: &mut TermTranslator<'_>,
) -> Result<CheckedTheorem, HolLightImportError> {
    Ok(CheckedTheorem {
        proof: close_lam(scope, &assumptions, body, translator)?,
        assumptions,
        conclusion,
    })
}

pub(super) fn close_lam(
    scope: &Scope,
    assumptions: &[HolTerm],
    mut body: Expr,
    translator: &mut TermTranslator<'_>,
) -> Result<Expr, HolLightImportError> {
    for assumption in assumptions.iter().rev() {
        body = Expr::lam(
            BinderInfo::Default,
            translator.translate_term(scope, assumption)?,
            body,
        );
    }
    for binder in scope.binders().iter().rev() {
        body = Expr::lam(binder_info(binder.kind), binder.lean_ty.clone(), body);
    }
    Ok(body)
}

pub(super) fn close_pi(
    scope: &Scope,
    assumptions: &[HolTerm],
    body: Expr,
    translator: &mut TermTranslator<'_>,
) -> Result<Expr, HolLightImportError> {
    // The conclusion was translated relative to `scope`'s binders; wrapping the
    // `k` assumption hypotheses introduces `k` binders ABOVE it, so its de Bruijn
    // indices must be lifted by `k`. Likewise the `i`-th hypothesis domain
    // (0-indexed from the outermost) sits under `i` earlier hypothesis binders
    // and must be lifted by `i`. (refl/trans/beta have zero assumptions, so this
    // path was previously never exercised — hence the latent off-by-`k` bug.)
    let k = assumptions.len() as u32;
    let mut body = body.lift(k);
    for (i, assumption) in assumptions.iter().enumerate().rev() {
        let dom = translator.translate_term(scope, assumption)?.lift(i as u32);
        body = Expr::pi(BinderInfo::Default, dom, body);
    }
    for binder in scope.binders().iter().rev() {
        body = Expr::pi(binder_info(binder.kind), binder.lean_ty.clone(), body);
    }
    Ok(body)
}

pub(super) fn binder_info(kind: ScopeBinderKind) -> BinderInfo {
    match kind {
        ScopeBinderKind::TypeVar => BinderInfo::Implicit,
        ScopeBinderKind::TermVar => BinderInfo::Default,
    }
}

pub(super) fn eq_refl(ty: Expr, value: Expr) -> Expr {
    // HOL types embed at clean `Type` (Sort 1), so `Eq` over them is at
    // universe 1 (HOL is universe-monomorphic). Using level 0 here produces a
    // proof term that fails the kernel's universe check (Sort 0 vs Sort 1).
    Expr::apps(
        Expr::const_str_levels("Eq.refl", vec![Level::succ(Level::zero())]),
        [ty, value],
    )
}

pub(super) fn expect_eq<'a>(
    rule: &'static str,
    term: &'a HolTerm,
) -> Result<(&'a HolTerm, &'a HolTerm), HolLightImportError> {
    dest_eq(term).ok_or(HolLightImportError::ExpectedEquality { rule })
}

pub(super) fn ensure_prop(
    rule: &'static str,
    term: &HolTerm,
    translator: &TermTranslator<'_>,
) -> Result<(), HolLightImportError> {
    let ty = translator.infer_type(term)?;
    if ty.is_bool() {
        Ok(())
    } else {
        Err(HolLightImportError::ExpectedProposition { rule, ty })
    }
}

pub(super) fn merge_assumptions(left: &[HolTerm], right: &[HolTerm]) -> Vec<HolTerm> {
    let mut merged = left.to_vec();
    for assumption in right {
        if !merged.contains(assumption) {
            merged.push(assumption.clone());
        }
    }
    merged
}

pub(super) fn remove_assumption(
    assumptions: &[HolTerm],
    target: &HolTerm,
    rule: &'static str,
) -> Result<Vec<HolTerm>, HolLightImportError> {
    let mut removed = false;
    let retained = assumptions
        .iter()
        .filter_map(|assumption| {
            if !removed && assumption == target {
                removed = true;
                None
            } else {
                Some(assumption.clone())
            }
        })
        .collect::<Vec<_>>();
    if removed {
        Ok(retained)
    } else {
        Err(HolLightImportError::MissingAssumption {
            rule,
            term: target.clone(),
        })
    }
}

pub(super) fn available_assumptions(
    assumptions: &[HolTerm],
    args: &[Expr],
) -> Vec<(HolTerm, Expr)> {
    assumptions
        .iter()
        .cloned()
        .zip(args.iter().cloned())
        .collect()
}

pub(super) fn apply_theorem(
    theorem: &CheckedTheorem,
    binder_args: &[Expr],
    available_assumptions: &[(HolTerm, Expr)],
) -> Result<Expr, HolLightImportError> {
    let assumption_args = match_assumption_args(&theorem.assumptions, available_assumptions)?;
    Ok(apply_proof(&theorem.proof, binder_args, &assumption_args))
}

pub(super) fn apply_proof(proof: &Expr, binder_args: &[Expr], assumption_args: &[Expr]) -> Expr {
    binder_args
        .iter()
        .chain(assumption_args.iter())
        .fold(proof.clone(), |acc, arg| Expr::app(acc, arg.clone()))
}

pub(super) fn match_assumption_args(
    expected: &[HolTerm],
    available: &[(HolTerm, Expr)],
) -> Result<Vec<Expr>, HolLightImportError> {
    expected
        .iter()
        .map(|term| {
            available
                .iter()
                .find(|(candidate, _)| candidate == term)
                .map(|(_, expr)| expr.clone())
                .ok_or_else(|| HolLightImportError::MissingAssumption {
                    rule: "proof application",
                    term: term.clone(),
                })
        })
        .collect()
}

pub(super) fn term_has_free_var(term: &HolTerm, binder: &HolVar, bound: &mut Vec<HolVar>) -> bool {
    match term {
        HolTerm::Var { name, ty } => {
            let candidate = HolVar::new(name.clone(), ty.clone());
            candidate == *binder && !bound.contains(&candidate)
        }
        HolTerm::Const { .. } => false,
        HolTerm::App { func, arg } => {
            term_has_free_var(func, binder, bound) || term_has_free_var(arg, binder, bound)
        }
        HolTerm::Abs {
            binder: inner,
            body,
        } => {
            bound.push(inner.clone());
            let result = term_has_free_var(body, binder, bound);
            bound.pop();
            result
        }
    }
}

pub(super) fn validate_term_substitutions(
    scope: &Scope,
    substitutions: &[HolTermSubstitution],
    translator: &TermTranslator<'_>,
) -> Result<(), HolLightImportError> {
    for substitution in substitutions {
        if scope.lookup_term(&substitution.variable).is_none() {
            return Err(HolLightImportError::InvalidSubstitutionTarget {
                name: substitution.variable.name.clone(),
            });
        }
        let replacement_ty = translator.infer_type(&substitution.replacement)?;
        if replacement_ty != substitution.variable.ty {
            return Err(HolLightImportError::TypeMismatch {
                expected: substitution.variable.ty.clone(),
                actual: replacement_ty,
            });
        }
    }
    Ok(())
}

pub(super) fn instantiated_term_scope_args(
    scope: &Scope,
    substitutions: &[HolTermSubstitution],
    lift: u32,
    translator: &mut TermTranslator<'_>,
) -> Result<Vec<Expr>, HolLightImportError> {
    let current = scope_args_in_context(scope, lift as usize, 0);
    scope
        .binders()
        .iter()
        .zip(current)
        .map(|(binder, default_arg)| match binder.kind {
            ScopeBinderKind::TypeVar => Ok(default_arg),
            ScopeBinderKind::TermVar => {
                // Scope construction always records a HOL type for term
                // binders; without one no substitution can match, so the
                // default argument is the correct result.
                let Some(hol_ty) = binder.hol_ty.clone() else {
                    return Ok(default_arg);
                };
                let variable = HolVar::new(binder.name.clone(), hol_ty);
                substitutions
                    .iter()
                    .find(|substitution| substitution.variable == variable)
                    .map(|substitution| {
                        translator
                            .translate_term(scope, &substitution.replacement)
                            .map(|expr| expr.lift(lift))
                    })
                    .unwrap_or(Ok(default_arg))
            }
        })
        .collect()
}

pub(super) fn instantiated_type_scope_args(
    scope: &Scope,
    substitutions: &[HolTypeSubstitution],
    lift: u32,
    translator: &mut TermTranslator<'_>,
) -> Result<Vec<Expr>, HolLightImportError> {
    let current = scope_args_in_context(scope, lift as usize, 0);
    scope
        .binders()
        .iter()
        .zip(current)
        .map(|(binder, default_arg)| match binder.kind {
            ScopeBinderKind::TermVar => Ok(default_arg),
            ScopeBinderKind::TypeVar => substitutions
                .iter()
                .find(|substitution| substitution.variable == binder.name)
                .map(|substitution| {
                    translator
                        .translate_type(scope, &substitution.replacement)
                        .map(|expr| expr.lift(lift))
                })
                .unwrap_or(Ok(default_arg)),
        })
        .collect()
}
