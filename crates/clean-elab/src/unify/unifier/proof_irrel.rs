// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof irrelevance BEFORE reduction for an argument pair.
//!
//! Lean's `isExprDefEqAuxImpl` (`Lean/Meta/ExprDefEq.lean`) asks
//! `isDefEqProofIrrel t s` right after `isDefEqQuick` and BEFORE `whnfCore`
//! touches either side: when `t` is a proof, `t =?= s` is decided by comparing
//! the two PROPOSITIONS, and neither proof is ever reduced. The gate is
//! `isProofQuick` (`Lean/Meta/InferType.lean`): a syntactic walk to the head of
//! the term, the head constant's (or local's) declared type, and
//! `isArrowProposition` -- strip one `∀` per argument and ask `isPropQuick`
//! whether what remains is a proposition. No reduction, no full inference.
//!
//! Clean's App/App arm reduced BOTH arguments to WHNF before comparing them
//! (`unify_app_args`), proofs included. A proof's δι-unfolding is the proof's
//! own recursion, so that reduction can cost anything at all. Measured
//! 2026-10-07 (`tests/bitvec_multilimb_pipeline_e2e.rs`,
//! `composite_multilimb_operand_wraps_and_registers_by_rfl`): once the kernel
//! refused `BitVec.ofNat`'s payload reducer in the `clean-prelude` world
//! (2291e9cd7, a sound kernel decision), `BitVec.ofNat 64 x =?= BitVec.ofNat 64 y`
//! reached `BitVec.ofFin 64 (Fin.mk (2^64) (x % 2^64) (Nat.mod_lt x (2^64) _))`
//! on both sides, the value arguments agreed, and the unifier then WHNF'd the
//! `Nat.mod_lt` proof argument for a 128-bit `x`: 53 CPU-minutes without
//! finishing. The kernel's `is_def_eq` closes the same pair in 1.5 ms because it
//! never reduces a proof either (`tc/def_eq/proof_irrel.rs`).
//!
//! It follows the kernel's own rule for WHERE proofs are irrelevant: never in
//! the cubical or directed layers, where identifying two paths in `Prop` would
//! be axiom K (`tc/def_eq/proof_irrel.rs`). There it declines, as the kernel
//! does.
//!
//! This is an ADDITIONAL success path and nothing else. It answers only when
//! a side is quickly known to be a proof, both types can be inferred, and the
//! two propositions unify; it then commits. In every other case -- not a quick
//! proof, an inference failure (a term carrying metavariables), propositions
//! that fail to unify or stay stuck -- the attempt is rolled back exactly and
//! the historical reduced comparison runs as before, so nothing that unified
//! before stops unifying. Acceptance stays the kernel's: every elaborated
//! declaration is re-checked by the unmodified kernel, whose def-eq already
//! identifies two proofs of one proposition.
//!
//! WS6.11 (F-106, merged at the 2026-10-14 rebase) found the same runaway
//! independently, on `rfl` over wrapped `UInt64` arithmetic, and adds three
//! things, each pinned in `proof_irrel_f106_tests.rs`. The rule is also asked
//! at the `unify` ENTRY, before its leading WHNF (Lean asks
//! `isDefEqProofIrrel` at every `isDefEq`, not only for arguments): `unify` on
//! the two `Nat.mod_lt` proofs of the F-106 pair otherwise spent its whole
//! 20,000-tick test budget in that WHNF and failed. And two cheap DECLINES
//! run before any work: a pair with a loose bound variable, and a ground pair
//! of propositions the cached checker refutes
//! (`checker_refutes_ground_propositions`). Neither decline can add an
//! acceptance: the first skips an inference that can only fail, the second an
//! attempt whose propositions the checker has already refuted.

use clean_kernel::mode::CleanMode;
use clean_kernel::{Expr, ExprKind};

use super::{Unifier, UnifyResult};
use crate::unify::MetaState;

impl Unifier<'_> {
    /// `Some(Success)` when `a1` and `a2` are proofs of unifiable
    /// propositions; `None` (state untouched) otherwise.
    pub(super) fn try_unify_proof_args(&mut self, a1: &Expr, a2: &Expr) -> Option<UnifyResult> {
        if !self.has_whnf()
            || !self.proofs_are_irrelevant_here()
            || self.as_meta(a1).is_some()
            || self.as_meta(a2).is_some()
            // A LOOSE bound variable has no type in any context, so the
            // inference below could only fail on it. Some arms still compare
            // unopened bodies (the cubical path-lambda arm); decline before
            // the checker is asked anything (WS6.11 review: 36 ticks -> 0).
            || a1.has_loose_bvars_quick()
            || a2.has_loose_bvars_quick()
        {
            return None;
        }
        if !(self.is_proof_quick(a1) || self.is_proof_quick(a2)) {
            return None;
        }
        // A proof that still mentions an UNASSIGNED metavariable is left to
        // the structural comparison, which can solve it. Lean reaches such a
        // pair only after `lazyDeltaReduction` has compared the same-head
        // applications above it argument by argument (assigning the
        // metavariable there); Clean's eager WHNF can unfold past that head,
        // and answering by proof irrelevance then succeeds with the
        // metavariable never assigned. Measured 2026-10-16: Mathlib's
        // `Classical.choose_eq` (`@choose_spec _ (· = a) _` against
        // `Exists.choose ⟨a, rfl⟩`) reduced both sides to `Classical.choice`
        // of a `Nonempty` proof built from `?h` on one side and `⟨a, rfl⟩` on
        // the other, and `?h` reached the kernel as a free variable.
        if self.has_unassigned_meta(a1) || self.has_unassigned_meta(a2) {
            return None;
        }
        let (ty1, ty2) = {
            let tc_cache = self.tc_cache.borrow();
            let tc = tc_cache.as_ref()?;
            (tc.infer_type(a1).ok()?, tc.infer_type(a2).ok()?)
        };
        if self.checker_refutes_ground_propositions(&ty1, &ty2) {
            return None;
        }
        self.metas.push_scope();
        if matches!(self.unify_core(&ty1, &ty2), UnifyResult::Success) {
            self.metas.commit();
            return Some(UnifyResult::Success);
        }
        self.metas.pop_scope();
        None
    }

    /// Whether the cached checker refutes `ty1 ≡ ty2` for two propositions that
    /// mention no metavariable and no universe parameter.
    ///
    /// A cost filter on the DECLINE only. Measured 2026-10-14 (WS6.11's
    /// adversarial probes, `proof_irrel_f106_tests.rs`): `unify_core` spent
    /// 13,499 ticks refusing `∀ {y}, 0 < y → 7 % y < y` against the same
    /// statement at 9 (a symbolic modulus), where this checker refuses the pair
    /// in 58 — and a declining attempt is pure overhead, since the historical
    /// comparison runs after it anyway. Over such terms `unify_core` has no
    /// metavariable to assign, and the checker (the same cached one, with the
    /// same reducibility setting) decides definitional equality itself. Its
    /// `true` is never taken here: an accept still comes only from
    /// `unify_core` above, so this cannot add an acceptance. A spent heartbeat
    /// makes its `false` meaningless, so that case is left to `unify_core`.
    fn checker_refutes_ground_propositions(&self, ty1: &Expr, ty2: &Expr) -> bool {
        let mut remaining = 256;
        if !Self::rigid_expr(ty1, &mut remaining) || !Self::rigid_expr(ty2, &mut remaining) {
            return false;
        }
        let tc_cache = self.tc_cache.borrow();
        let Some(tc) = tc_cache.as_ref() else {
            return false;
        };
        if tc.heartbeat_spent() {
            return false;
        }
        !tc.is_def_eq(ty1, ty2) && !tc.heartbeat_spent()
    }

    /// Whether `e`, with every assigned metavariable instantiated, still
    /// mentions an elaborator metavariable.
    fn has_unassigned_meta(&self, e: &Expr) -> bool {
        MetaState::expr_has_meta(e) && MetaState::expr_has_meta(&self.metas.instantiate(e))
    }

    /// Whether the checker's mode has definitional proof irrelevance at all:
    /// the kernel turns it off in the cubical and directed layers.
    fn proofs_are_irrelevant_here(&self) -> bool {
        self.tc_cache
            .borrow()
            .as_ref()
            .is_some_and(|tc| !matches!(tc.mode(), CleanMode::Cubical | CleanMode::Directed))
    }

    /// Lean's `isProofQuick`: `true` only when `e` is syntactically a proof.
    fn is_proof_quick(&self, e: &Expr) -> bool {
        match e.kind() {
            ExprKind::Lam(_, _, body) | ExprKind::Let(_, _, _, body, _) => {
                self.is_proof_quick(body)
            }
            ExprKind::MData(_, inner) => self.is_proof_quick(inner),
            ExprKind::Const(..) | ExprKind::FVar(_) => self
                .head_type(e)
                .is_some_and(|ty| self.is_arrow_proposition(&ty, 0)),
            ExprKind::App(..) => {
                let head = e.get_app_fn();
                matches!(head.kind(), ExprKind::Const(..) | ExprKind::FVar(_))
                    && self
                        .head_type(head)
                        .is_some_and(|ty| self.is_arrow_proposition(&ty, e.get_app_num_args()))
            }
            _ => false,
        }
    }

    /// Lean's `isArrowProposition`: strip `n` binders (no reduction) and ask
    /// whether what remains is a proposition.
    fn is_arrow_proposition(&self, ty: &Expr, n: usize) -> bool {
        match ty.kind() {
            ExprKind::Pi(_, _, body) if n > 0 => self.is_arrow_proposition(body, n - 1),
            ExprKind::Let(_, _, _, body, _) => self.is_arrow_proposition(body, n),
            ExprKind::MData(_, inner) => self.is_arrow_proposition(inner, n),
            _ => n == 0 && self.is_prop_quick(ty),
        }
    }

    /// Lean's `isPropQuick`: `true` only when `ty` is syntactically a
    /// proposition (a `∀` into one, or an application of a constant or local
    /// whose declared type ends in `Prop` after one `∀` per argument).
    fn is_prop_quick(&self, ty: &Expr) -> bool {
        match ty.kind() {
            ExprKind::Pi(_, _, body) | ExprKind::Let(_, _, _, body, _) => self.is_prop_quick(body),
            ExprKind::MData(_, inner) => self.is_prop_quick(inner),
            ExprKind::Const(..) | ExprKind::FVar(_) => {
                self.head_type(ty).is_some_and(|t| is_arrow_prop(&t, 0))
            }
            ExprKind::App(..) => {
                let head = ty.get_app_fn();
                matches!(head.kind(), ExprKind::Const(..) | ExprKind::FVar(_))
                    && self
                        .head_type(head)
                        .is_some_and(|t| is_arrow_prop(&t, ty.get_app_num_args()))
            }
            _ => false,
        }
    }

    /// The declared type of a constant or a local of the checker's context.
    /// A metavariable head is not consulted (`None`): its type is the
    /// elaborator's guess, which is exactly what this quick test must not lean
    /// on.
    fn head_type(&self, head: &Expr) -> Option<Expr> {
        if self.as_meta(head).is_some() {
            return None;
        }
        let tc_cache = self.tc_cache.borrow();
        tc_cache.as_ref()?.infer_type(head).ok()
    }
}

/// Lean's `isArrowProp`: strip `n` binders (no reduction) and require `Prop`
/// itself, `Sort 0`.
fn is_arrow_prop(ty: &Expr, n: usize) -> bool {
    match ty.kind() {
        ExprKind::Pi(_, _, body) if n > 0 => is_arrow_prop(body, n - 1),
        ExprKind::Let(_, _, _, body, _) => is_arrow_prop(body, n),
        ExprKind::MData(_, inner) => is_arrow_prop(inner, n),
        ExprKind::Sort(level) => n == 0 && level.is_zero(),
        _ => false,
    }
}

#[cfg(test)]
#[path = "proof_irrel_tests.rs"]
mod tests;

/// WS6.11's F-106 probes (the wrapped-`UInt64` `rfl` runaway), run against this
/// rule since the 2026-10-14 rebase.
#[cfg(test)]
#[path = "proof_irrel_f106_tests.rs"]
mod f106_tests;
