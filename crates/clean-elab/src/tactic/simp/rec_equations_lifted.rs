// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `simp [f]` equations for a member of a lifted `mutual` block (gap G23,
//! brick B3; design `designs/2026-10-08-mutual-nested-recursion.md` §5.5).
//!
//! A lifted member's value applies its block's SHARED nested recursor
//! (`T.rec_k`, possibly projected out of a `PProd` tuple), which the plain
//! structural synthesis in [`super::rec_equations`] declines (several motives,
//! a nested family). The lift records, per member, one closed statement per
//! constructor of its major premise's type (`infer/mutual_lift/eqns.rs`):
//!
//! ```text
//!   ∀ xs, f … (c fields…) … = rhs        -- rhs in surface form
//! ```
//!
//! This module turns those statements into [`SimpLemma`]s with the same
//! `Eq.refl`-over-LHS proof template and the same all-or-nothing rule as the
//! structural synthesis, so the contract at `rec_equations.rs` (re-checked by
//! `proof_matches_rewrite` and `close_goal`) holds unchanged: a wrong statement
//! refuses a rewrite, it cannot mint one.

use clean_kernel::env::ConstantKind;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, ExprKind};

use super::types::{SimpIndexMode, SimpLemma};

/// Same tier as the structural synthesis (`rec_equations::EQUATION_PRIORITY`).
const EQUATION_PRIORITY: u32 = 50;

/// `None` when `name` is not a lifted member (the caller falls through to the
/// structural synthesis); otherwise its equations, or the reason there are
/// none.
pub(super) fn lifted_member_equations(
    env: &Environment,
    name: &Name,
) -> Option<Result<Vec<SimpLemma>, &'static str>> {
    let state = env.get_ext_state::<crate::MutualLiftState>(crate::mutual_lift_idx())?;
    let entry = state.get(name)?;
    Some(equations_of(env, name, &entry.equations))
}

fn equations_of(
    env: &Environment,
    name: &Name,
    statements: &[Expr],
) -> Result<Vec<SimpLemma>, &'static str> {
    let decl = env.get_const(name).ok_or("no such constant")?;
    if !matches!(decl.kind, ConstantKind::Definition) {
        return Err("not a definition");
    }
    // As in the structural synthesis: the `Eq.refl` template is built here,
    // where nothing can solve a level parameter.
    if !decl.level_params.is_empty() {
        return Err("level-polymorphic");
    }
    if statements.is_empty() {
        return Err("the lift recorded no equations");
    }
    statements
        .iter()
        .map(|statement| lemma_of(name, statement))
        .collect()
}

/// `∀ xs, @Eq.{u} T lhs rhs` ↦ the lemma over the telescope's loose BVars
/// (the `extract_equality_full` convention: innermost binder = 0).
fn lemma_of(name: &Name, statement: &Expr) -> Result<SimpLemma, &'static str> {
    if statement.has_fvar_quick() || statement.has_expr_mvar_quick() {
        return Err("an equation is not closed");
    }
    let mut body = statement;
    while let ExprKind::Pi(_, _, inner) = body.kind() {
        body = inner;
    }
    let ExprKind::Const(eq, levels) = body.get_app_fn().kind() else {
        return Err("an equation is not an equality");
    };
    let args = body.get_app_args();
    if eq.to_string() != "Eq" || levels.len() != 1 || args.len() != 3 {
        return Err("an equation is not an equality");
    }
    let (eq_ty, lhs, rhs) = (args[0].clone(), args[1].clone(), args[2].clone());
    let proof = Expr::apps(
        Expr::const_str_levels("Eq.refl", levels.to_vec()),
        [eq_ty.clone(), lhs.clone()],
    );
    Ok(SimpLemma {
        name: name.clone(),
        lhs,
        rhs,
        eq_type: Some(eq_ty),
        proof_expr: Some(proof),
        // The LHS head is the member itself, delta-unfoldable: keep it
        // always offered, as the structural synthesis does.
        index_mode: SimpIndexMode::Unindexed,
        priority: EQUATION_PRIORITY,
    })
}
