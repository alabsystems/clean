// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `inhabit α` — Mathlib's `Mathlib/Tactic/Inhabit.lean` (`evalInhabit`):
//! from a `Nonempty α` instance, assert `inhabited_h : Inhabited α` so later
//! terms can use `default`. Clean cannot run the compiled `elab_rules`, so the
//! tactic was "unknown" (`nonempty_unique`, `lt_of_strongLT`, measured
//! 2026-09-12). The asserted value is `⟨Classical.choice h⟩`, which Mathlib's
//! `nonempty_to_inhabited` unfolds to; the new local is a class-typed local and
//! therefore a local instance for later tactics (the by-block bridge).
//!
//! # Where the `Nonempty α` proof comes from
//!
//! `evalInhabit` calls `synthInstance (Nonempty α)`: the real resolver, so a
//! GLOBAL instance (`instance : Nonempty Foo`), a parametric one and a local
//! `[Nonempty α]` binder all answer. The elaborator's dispatch runs that
//! search (`ElabCtx::synthesize_inhabit_witness`, the resolver path
//! `infer_instance` takes) and hands the proof over as `args[1]`. This handler
//! alone has no resolver, so without `args[1]` it falls back to a local of
//! type `Nonempty α` — what it did before, and all a bare `ProofState` caller
//! can do — and with neither it fails closed rather than guessing.

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

use super::core::{ProofState, TacticError, TacticResult};

/// Run `inhabit α` on the current goal.
///
/// REQUIRES: `args[0]` is the elaborated type `α`; `args[1]`, when present, is
///   a synthesized proof of `Nonempty α`.
/// ENSURES: on success the goal gains `inhabited_h : Inhabited α` (kernel
///   checked by `have_`); on failure the state is unchanged. A supplied
///   `args[1]` whose type is not `Nonempty α` is refused, never trusted.
pub(crate) fn inhabit(ps: &mut ProofState, args: &[Expr]) -> TacticResult {
    let alpha = args
        .first()
        .cloned()
        .ok_or_else(|| TacticError::InvalidTarget {
            tactic: "inhabit".into(),
            detail: "expected a type argument".into(),
        })?;
    let goal = ps.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let sort = ps.whnf(&goal, &ps.infer_type(&goal, &alpha)?);
    let ExprKind::Sort(level) = sort.kind() else {
        return Err(TacticError::InvalidTarget {
            tactic: "inhabit".into(),
            detail: format!("`{alpha}` is not a type"),
        });
    };
    let level = level.clone();
    let nonempty = Expr::app(
        Expr::const_(Name::from_string("Nonempty"), vec![level.clone()]),
        alpha.clone(),
    );
    let witness = match args.get(1) {
        Some(synthesized) => {
            let witness_ty = ps.infer_type(&goal, synthesized)?;
            if !ps.is_def_eq(&goal, &ps.metas.instantiate(&witness_ty), &nonempty) {
                return Err(TacticError::InvalidTarget {
                    tactic: "inhabit".into(),
                    detail: format!(
                        "the synthesized instance is not a proof of `Nonempty {alpha}`"
                    ),
                });
            }
            synthesized.clone()
        }
        None => goal
            .local_ctx
            .iter()
            .rev()
            .find(|d| ps.is_def_eq(&goal, &ps.metas.instantiate(&d.ty), &nonempty))
            .map(|d| Expr::fvar(d.fvar))
            .ok_or_else(|| TacticError::InvalidTarget {
                tactic: "inhabit".into(),
                detail: format!("failed to synthesize `Nonempty {alpha}`: no instance in scope"),
            })?,
    };
    let choice = Expr::apps(
        Expr::const_(Name::from_string("Classical.choice"), vec![level.clone()]),
        [alpha.clone(), witness],
    );
    let value = Expr::apps(
        Expr::const_(Name::from_string("Inhabited.mk"), vec![level.clone()]),
        [alpha.clone(), choice],
    );
    let ty = Expr::app(
        Expr::const_(Name::from_string("Inhabited"), vec![level]),
        alpha,
    );
    super::have_(
        ps,
        &clean_parser::SurfaceName::generated_path("inhabited_h"),
        ty,
        Some(value),
    )
}
