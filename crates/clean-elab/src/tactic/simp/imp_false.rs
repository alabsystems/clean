// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean 4.8's `@[simp] imp_false : (a → False) ↔ ¬a`, applied as its own step
//! (G39, ledger (109)).
//!
//! Read as an ordinary rewrite rule, its left-hand side `?a → False` is a
//! `∀`-pattern, and Clean's prelude declares `Not` REDUCIBLE where Lean's is a
//! plain `def`. The matcher then unified `?a` against the UNFOLDED domain:
//! `¬p → False` became `¬(p → False)` instead of `¬¬p`, and
//! `Decidable.not_not` could no longer see a double negation (measured on
//! `G39-simp-ite-eq-iff.lean` with `CLEAN_SIMP_REWRITE_TRACE`). This step reads
//! the domain as written: a non-dependent `dom → False` with `dom : Prop`
//! becomes `¬dom`, proved by `propext (@imp_false dom)`.

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

use super::types::{SimpConfig, SimpResult};
use crate::tactic::core::{Goal, ProofState};

/// `dom → False` ↦ `¬dom`, or `None` when `expr` is not that shape, `dom` is
/// not a proposition, the call is `simp only`, `imp_false` is erased, or the
/// environment has no `imp_false`.
///
/// SOUNDNESS: the proof is `@propext (dom → False) (Not dom) (@imp_false
/// dom)`, re-checked with the rest of simp's proof at `close_goal`.
pub(super) fn simp_imp_false(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
    config: &SimpConfig,
) -> Option<SimpResult> {
    if config.only {
        return None;
    }
    let ExprKind::Pi(_, dom, body) = expr.kind() else {
        return None;
    };
    let is_false =
        |e: &Expr| matches!(e.kind(), ExprKind::Const(n, _) if *n == Name::from_string("False"));
    if crate::tactic::bvar_ops::has_loose_bvar(body, 0) || !is_false(body) {
        return None;
    }
    let imp_false = Name::from_string("imp_false");
    if config
        .exclude
        .contains(&clean_parser::SurfaceName::from_name(imp_false.clone()))
    {
        return None;
    }
    state.env.get_const(&imp_false)?;
    if !state.infer_type(goal, dom).ok()?.is_prop() {
        return None;
    }
    let dom = dom.as_ref().clone();
    let not_dom = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), dom.clone());
    let iff = Expr::app(Expr::const_(imp_false, vec![]), dom);
    let proof = Expr::apps(
        Expr::const_(Name::from_string("propext"), vec![]),
        [expr.clone(), not_dom.clone(), iff],
    );
    Some(SimpResult {
        expr: not_dom,
        proof: Some(proof),
    })
}
