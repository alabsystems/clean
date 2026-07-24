// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `get_elem_tactic` analog — discharging the `xs[i]` bounds-proof hole
//! (Brick 4).
//!
//! Lean's `$x[$i]` macro expands to `getElem $x $i (by get_elem_tactic)`
//! (`Init/GetElem.lean:82`), where `get_elem_tactic` is
//! `first | done | assumption | get_elem_tactic_extensible | fail …` and the
//! extensible defaults try (in effective order) `omega`, `simp +arith; done`,
//! `trivial` (`Init/Tactics.lean:2505-2547`). Clean's parser emits the same
//! shape with a bare `Hole` in the proof slot (`getElem xs i _`); this module
//! is the tactic block that hole stands for.
//!
//! Scoping: the chain fires exactly for the `valid xs i` slot of a
//! `GetElem.getElem` application whose proof argument is a syntactic hole —
//! never for holes anywhere else (no global auto-discharge), and never in
//! `@`-explicit mode (Lean's `@getElem …` has no `by` block either). One
//! deviation from Lean: a hand-written `getElem xs i _` is indistinguishable
//! from the `xs[i]` desugar in Clean's surface tree, so it receives the same
//! tactic chain (Lean would leave that `_` to unification and fail); this is
//! strictly narrower than accepting more programs unsoundly — the produced
//! proof is a real term, kernel-re-checked with the declaration.
//!
//! Soundness (audit §5.1: the highest-stakes latent silent-wrong): the hole is
//! NEVER filled with `sorry` and never left as an unassigned metavariable that
//! could default — each candidate tactic must CLOSE the goal and its proof is
//! re-verified by `elab_by_tactic`'s `verify_tactic_proof` before being
//! accepted; if no candidate closes the goal, elaboration fails LOUD with
//! [`ElabError::GetElemValidUnproved`].

use clean_kernel::{Expr, ExprKind, Name};
use clean_parser::{Span, SurfaceTactic, SurfaceTacticLocation};

use super::ElabCtx;
use crate::error::ElabError;

/// The candidate chain, in Lean's effective order (`assumption` first, then
/// the `get_elem_tactic_extensible` defaults `omega`, `simp; done`,
/// `trivial`). `decide` is appended as Clean's closer for ground goals
/// (e.g. `0 < List.length [1, 2, 3]`) that Lean's `simp +arith` normalizes
/// away but Clean's plain `simp` may not; it produces a kernel-checked
/// `Decidable.decide` witness, so it can only close genuinely true decidable
/// bounds.
const GETELEM_TACTIC_CHAIN: &str = "assumption/omega/simp/trivial/decide";

impl ElabCtx<'_> {
    /// If `func_expr` is (an application spine headed by) the
    /// `GetElem.getElem` projection, return the 0-based index of its `valid
    /// xs i` proof slot among the EXPLICIT arguments (`xs`, `i`, `h` → 2).
    pub(in crate::infer) fn getelem_valid_proof_slot(func_expr: &Expr) -> Option<usize> {
        match func_expr.get_app_fn().kind() {
            ExprKind::Const(name, _) if *name == Name::from_string("GetElem.getElem") => Some(2),
            _ => None,
        }
    }

    /// Discharge a pinned `valid xs i` GetElem bounds obligation with the
    /// `get_elem_tactic` analog: try `assumption`, `omega`, `simp`,
    /// `trivial`, `decide` in order, each as an isolated single-tactic block
    /// over the current local context. The first proof that closes AND
    /// re-verifies against the goal wins; if none does, fail LOUD — the hole
    /// is never left unassigned and never `sorry`-filled.
    pub(in crate::infer) fn discharge_getelem_valid_hole(
        &mut self,
        goal: &Expr,
    ) -> Result<Expr, ElabError> {
        let span = Span::dummy();
        let named = |name: &str| SurfaceTactic::Named {
            span,
            name: name.to_string(),
            args: vec![],
        };
        let candidates: Vec<SurfaceTactic> = vec![
            named("assumption"),
            named("omega"),
            // Lean's `simp +arith; done`: `elab_by_tactic` already errors
            // unless every goal is closed — exactly the trailing `done`.
            SurfaceTactic::Simp {
                span,
                only: false,
                lemmas: vec![],
                location: SurfaceTacticLocation::Goal,
            },
            named("trivial"),
            named("decide"),
        ];

        for tactic in candidates {
            // Isolate each attempt: a failing tactic must not leak
            // metavariable assignments into the surrounding elaboration.
            self.metas.push_scope();
            let saved_expected = self.current_expected_type.replace(goal.clone());
            let attempt = self.elab_by_tactic(std::slice::from_ref(&tactic));
            self.current_expected_type = saved_expected;
            match attempt {
                Ok(proof) => {
                    self.metas.commit();
                    return Ok(proof);
                }
                Err(_) => {
                    self.metas.pop_scope();
                }
            }
        }

        // Beta-reduce the reported goal: the raw obligation is the redex
        // `(fun as i => i < as.length) xs i`; the reduced form is what the
        // user has to prove.
        let shown = crate::tactic::simp::beta_reduce(goal);
        Err(ElabError::GetElemValidUnproved {
            goal: format!("{shown:?}"),
            tried: GETELEM_TACTIC_CHAIN.to_string(),
        })
    }
}
