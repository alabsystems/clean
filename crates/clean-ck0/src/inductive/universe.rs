// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The universe constraint: every constructor field's sort is at most the
//! inductive's.

use super::{pi_domains, split_ctor_telescope, AdmitError, InductiveDecl};
use crate::budget::Budget;
use crate::infer::InferError;
use crate::level::Level;
use crate::term::Term;
use crate::validate::Env;

/// Every constructor field's sort must be `<=` the inductive's sort
/// (`ind_sort >= field_sort`), with the standard Prop exception: a `Prop`
/// inductive (`ind_sort = 0`) admits fields of any sort (Lean impredicativity).
/// Fail-closed: budget exhaustion or a non-sort field type is a reject.
/// Block-aware universe constraint: each type's constructor fields are checked
/// against *that type's* sort. (The field-sort inference resolves block types
/// through the staging env, so cross-type field references type cleanly.) For a
/// single-element block this is exactly [`check_universe_constraint`].
pub(crate) fn check_universe_constraint_block(
    env: &dyn Env,
    decl: &InductiveDecl,
    ind_sort: &Level,
) -> Result<(), AdmitError> {
    check_universe_constraint(env, decl, ind_sort)
}

pub(super) fn check_universe_constraint(
    env: &dyn Env,
    decl: &InductiveDecl,
    ind_sort: &Level,
) -> Result<(), AdmitError> {
    // Prop is impredicative: a Prop-valued inductive may quantify over fields in
    // any universe (Lean kernel: the level-le check is skipped when the inductive
    // is in Prop).
    if ind_sort.is_zero() {
        return Ok(());
    }
    let mut budget = Budget::default_budget();
    for ctor in &decl.constructors {
        let (field_tys, _ret) = split_ctor_telescope(&ctor.type_, decl.num_params);
        // Field domains are typed under a context of [params..., earlier fields].
        // We type each field's sort in the running context.
        let mut ctx: Vec<Term> = Vec::new();
        // Push parameter binder types (the leading Pi domains of the ctor type).
        let param_binders = pi_domains(&ctor.type_, decl.num_params);
        for d in &param_binders {
            ctx.push(d.clone());
        }
        for field_ty in &field_tys {
            let sort =
                infer_sort_in_ctx(env, &ctx, field_ty, &mut budget).map_err(|e| match e {
                    InferError::OutOfBudget => AdmitError::OutOfBudget {
                        ind: decl.name.clone(),
                    },
                    _ => AdmitError::UniverseTooLarge {
                        ind: decl.name.clone(),
                        ctor: ctor.name.clone(),
                    },
                })?;
            // A comparison past its work bound is a refusal, never `false`
            // read as an answer (R172).
            match Level::try_is_geq(ind_sort, &sort) {
                Ok(true) => {}
                Ok(false) => {
                    return Err(AdmitError::UniverseTooLarge {
                        ind: decl.name.clone(),
                        ctor: ctor.name.clone(),
                    });
                }
                Err(_) => {
                    return Err(AdmitError::OutOfBudget {
                        ind: decl.name.clone(),
                    });
                }
            }
            ctx.push(field_ty.clone());
        }
    }
    Ok(())
}

/// Infer the sort of `ty` under a local context — thin wrapper over `infer`'s
/// context-aware path (added in M2).
fn infer_sort_in_ctx(
    env: &dyn Env,
    ctx: &[Term],
    ty: &Term,
    budget: &mut Budget,
) -> Result<Level, InferError> {
    crate::infer::infer_sort_in_context(env, ctx, ty, budget)
}
