// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Compare the parts of an application AS WRITTEN before reducing them.
//!
//! Lean's `isDefEq` does not δ-reduce the parts of an application before
//! comparing them. Two applications with the same constant head are compared
//! argument by argument first (`isDefEqApp`, `Lean/Meta/ExprDefEq.lean:2120-2131`;
//! inside lazy delta reduction the same step is `tryHeuristic`, `:1423-1480`,
//! tried before either side is unfolded), and a flex application `?m a =?= v`
//! is solved from `v` as it stands (`processAssignment`, `:1268-1311`, which
//! falls back to the first-order `?m =?= f`, `a =?= b` split of
//! `processAssignmentFOApprox` without reducing `v`). Clean's App/App arm
//! reduced both function parts to WHNF whenever they differed, and reduced
//! both arguments before comparing them. Reducing can erase exactly the part a
//! metavariable needed:
//!
//! * `LT.lt ?α X ?a ?b =?= LT.lt α inst a b` — `LT.lt` is a projection
//!   function, the WHNF of `LT.lt ?α X ?a` is `X.1 ?a`, and `?α` is gone: it
//!   was never assigned and `simp` refused the match as `lhs-meta-leak`
//!   (`Mathlib/Order/Basic.lean`'s `not_lt_iff_le_imp_ge`, `min_rec`);
//! * `?g (f x) =?= surjInv h (f x)` — reducing the defined side first turned
//!   the first-order split into `?g := chooseAx (fun a => f a = f x)` against
//!   the unfolded body, capturing the bound `x`, where Lean assigns
//!   `?g := surjInv h` (`Function.bijective_iff_has_inverse` once its
//!   statement elaborates).
//!
//! The historical reduced comparison stays as the fallback: failed probes
//! restore term/universe assignment state before it runs. Speculative work
//! still spends cumulative checker budgets; this is not a universal
//! resource-bounded acceptance or solution-choice guarantee. These probes
//! precede WHNF: differing function parts of an App/App pair,
//! and argument pairs that are either flex-against-anything or applications of
//! the same constant. A bare metavariable against a reducible argument keeps
//! its historical reduced solution (no measured row needs that changed, and
//! the adversarial review measured `simp` matches that depend on it — `¬¬?a`
//! against `¬(Q → False)` through `Not`, whose heads differ and so never take
//! this route).

use clean_kernel::{ConstantKind, Expr, ExprKind, Reducibility};

use super::{Unifier, UnifyResult};

/// Failed unreduced attempts one unifier may make before it stops trying
/// them. Each failure is followed by the historical comparison of the same
/// pair, so nested failures multiply work; the bound caps that at a fixed
/// multiple of the historical cost. Exhausting it only returns to the
/// historical behaviour, never rejects anything.
const MAX_UNREDUCED_FAILURES: u32 = 64;

impl Unifier<'_> {
    /// The argument half of the App/App arm, once the function parts agree.
    ///
    /// Split out of `unify_core_inner` so the unreduced-first attempt of
    /// `app_heads.rs` compares the arguments exactly as this arm does.
    pub(super) fn unify_app_args(&mut self, a1: &Expr, a2: &Expr) -> UnifyResult {
        if a1 == a2 {
            return UnifyResult::Success;
        }
        // Two proofs are compared by their propositions, before either is
        // reduced or compared structurally (Lean's `isDefEqProofIrrel`, which
        // runs right after `isDefEqQuick`; see `proof_irrel.rs`). Reducing a
        // proof argument below can cost anything at all.
        if let Some(result) = self.try_unify_proof_args(a1, a2) {
            return result;
        }
        // Targeted exception: do NOT Î´-unfold an argument whose head is
        // an `Irreducible` constant (the Track II `Nat.land`/`lor`/`xor`)
        // WHEN the OPPOSITE argument is a bare metavariable, so the
        // metavar is assigned the SURFACE head a later `rw`/`unfold`
        // relies on. Gating on "opposite is a bare meta" confines it to
        // metavar assignment; general structural unification keeps #379
        // WHNF. Soundness unchanged (kernel re-checks the proof term).
        // Second targeted exception: a beta-redex argument (Lam-headed
        // application) paired against a FLEX application (spine head is
        // an unsolved metavariable) has TWO legitimate higher-order
        // solutions, and eager reduction commits to the wrong one when
        // it is type-incorrect. For the postponed-lambda `congrArg`
        // shape the pair is
        //   `(fun o => Ev s n (Value.nat o)) x  =?=  ?f x`
        // Beta-first yields the PROJECTION `?f := Ev s n` — here
        // type-incorrect (`Nat → Prop` slot, `Value → Prop` head), and
        // the failed attempt used to leave `?f` poisoned for every
        // later consumer (the trust-spec-temporal FiniteModel
        // regression). Keeping the redex pairs the spines and yields
        // the IMITATION `?f := (fun o => …)` — but arg-driven flows
        // (the LRAT `List.rec`/`congrArg` corpus shape) genuinely rely
        // on the projection. So: try the historical reduced path in a
        // SPECULATIVE scope first — committing when it succeeds keeps
        // every previously-working solution byte-identical — and only
        // on failure roll back (un-poisoning the flex head) and pair
        // the spines unreduced. Soundness unchanged either way: the
        // assignment is kernel-re-checked, and beta ⊆ def-eq means the
        // kept redex can only refine WHICH solution is found, never
        // equate unequal terms.
        let flex_head = |u: &Self, e: &Expr| {
            matches!(e.kind(), ExprKind::App(_, _)) && u.as_meta(e.get_app_fn()).is_some()
        };
        let lam_headed_app = |e: &Expr| {
            matches!(e.kind(), ExprKind::App(_, _))
                && matches!(e.get_app_fn().kind(), ExprKind::Lam(_, _, _))
        };
        if (lam_headed_app(a1) && flex_head(self, a2))
            || (lam_headed_app(a2) && flex_head(self, a1))
        {
            self.metas.push_scope();
            let reduced = {
                let a1_whnf = self.try_whnf(a1);
                let a2_whnf = self.try_whnf(a2);
                self.unify_core(&a1_whnf, &a2_whnf)
            };
            if matches!(reduced, UnifyResult::Success) {
                self.metas.commit();
                return UnifyResult::Success;
            }
            self.metas.pop_scope();
            return self.unify_core(a1, a2);
        }
        let a1_keep = self.head_is_protected_def(a1) && self.as_meta(a2).is_some();
        let a2_keep = self.head_is_protected_def(a2) && self.as_meta(a1).is_some();
        // Do not normalize a large computation merely to decide whether this
        // same-head/flex structural attempt should run. A failed probe rolls
        // back its assignments before the unchanged WHNF fallback below.
        if self.unify_argument_unreduced(a1, a2) {
            return UnifyResult::Success;
        }
        let a1_whnf = if a1_keep {
            a1.clone()
        } else {
            self.try_whnf(a1)
        };
        let a2_whnf = if a2_keep {
            a2.clone()
        } else {
            self.try_whnf(a2)
        };
        // A flex application, or two applications of one constant, against a
        // reducible side: Lean compares them AS WRITTEN (`processAssignment`,
        // `isDefEqApp`); reducing first split `?g (f x) =?= surjInv h (f x)`
        // against an unfolded body (`?g := chooseAx (…)`, capturing `x`) and
        // turned `LT.lt ?α X ?a ?b` into `X.1 ?a ?b`, losing `?α`. Tried in a
        // rollback scope with the reduced comparison below as the fallback;
        // see `app_heads.rs`.
        self.unify_core(&a1_whnf, &a2_whnf)
    }

    /// Whether an unreduced attempt is worth making for `left =?= right`: a
    /// ground pair has no metavariable to solve, but applications of the same
    /// rigid constant and arity can compare their syntactic arguments without
    /// evaluating the enclosing computation. Other ground shapes retain the
    /// historical path. Exhausting the failure budget also retains that path.
    fn unreduced_attempt_allowed(&self, left: &Expr, right: &Expr) -> bool {
        let ground = |e: &Expr| !e.has_fvar_quick() && !e.has_level_param_quick();
        (!(ground(left) && ground(right)) || self.same_regular_definition_head(left, right))
            && self.unreduced_failures.get() < MAX_UNREDUCED_FAILURES
    }

    /// The ground half of Lean's `tryHeuristic` guard (`lazyDeltaReduction`,
    /// `Lean/Meta/ExprDefEq.lean`): with no metavariable on either side, two
    /// applications of one constant are compared argument by argument before
    /// unfolding only when the constant is a REGULAR definition. An
    /// abbreviation, projection or instance (`HMod.hMod`, `Reducibility::
    /// Reducible`) is unfolded instead, and a ground `x % 2^64 =?= y % 2^64`
    /// then evaluates; probed, it descended into `Nat.mod`'s unfolded body for
    /// a 128-bit `x` (`proof_irrel_tests`' multilimb row) and never returned.
    fn same_regular_definition_head(&self, left: &Expr, right: &Expr) -> bool {
        let ExprKind::Const(name, _) = left.get_app_fn().kind() else {
            return false;
        };
        same_constant_head(left, right)
            && self
                .env
                .and_then(|env| env.get_const(name))
                .is_some_and(|info| {
                    info.kind == ConstantKind::Definition
                        && !info.is_reducible
                        && matches!(info.reducibility, Reducibility::Regular(_))
                })
    }

    /// Run `attempt` in a rollback scope: committed and `true` when it
    /// succeeds, rolled back (and counted against the budget) otherwise.
    fn attempt_unreduced(&mut self, attempt: impl FnOnce(&mut Self) -> bool) -> bool {
        self.metas.push_scope();
        if attempt(self) {
            self.metas.commit();
            return true;
        }
        self.metas.pop_scope();
        self.unreduced_failures
            .set(self.unreduced_failures.get().saturating_add(1));
        false
    }

    /// `f1 a1 =?= f2 a2` with `f1 =?= f2` compared unreduced, then the
    /// arguments as the App/App arm compares them, BEFORE either function part
    /// is reduced. A failed probe restores the assignments for WHNF fallback.
    pub(super) fn unify_app_unreduced_function_parts(
        &mut self,
        (left, right): (&Expr, &Expr),
        (f1, a1): (&Expr, &Expr),
        (f2, a2): (&Expr, &Expr),
    ) -> bool {
        self.unreduced_attempt_allowed(left, right)
            && self.attempt_unreduced(|u| {
                matches!(u.unify_core(f1, f2), UnifyResult::Success)
                    && matches!(u.unify_app_args(a1, a2), UnifyResult::Success)
            })
    }

    /// An argument pair Lean compares before reducing either side: one side a
    /// flex application (solved against the other side as written), both
    /// applications of the same constant with the same arity (compared
    /// argument by argument), or a BARE assignable metavariable facing a
    /// constant-headed application. Probe BEFORE WHNF; equivalent argument
    /// spellings must not force evaluation of their enclosing computation.
    ///
    /// The second shape is where `simp` met row 28: the lemma's `¬ ?a < ?b`
    /// puts `LT.lt ?α X ?a ?b` in an ARGUMENT position of `Not`, and it was
    /// reduced here, before the App/App arm could compare it head-first.
    pub(super) fn unify_argument_unreduced(&mut self, a1: &Expr, a2: &Expr) -> bool {
        (self.is_flex_app(a1)
            || self.is_flex_app(a2)
            || same_constant_head(a1, a2)
            || self.bare_meta_against_const_app(a1, a2))
            && self.unreduced_attempt_allowed(a1, a2)
            && self.attempt_unreduced(|u| matches!(u.unify_core(a1, a2), UnifyResult::Success))
    }

    /// One side is a BARE assignable metavariable and the other a
    /// CONSTANT-headed application — Lean's `isDefEqQuickOther`
    /// (`Lean/Meta/ExprDefEq.lean:1797`) hands the term to
    /// `processAssignment'` AS WRITTEN, with no `whnf` anywhere on that path.
    ///
    /// Clean reduced it, so `congrFun h a'` against
    /// `@Eq (∀ x, β x) (Function.update f a' v) (Function.update f a' v')
    ///  =?= @Eq ?T ?f ?g` assigned `?f` the δ-unfolded `fun x => dite …`, and
    /// `rwa [update_self] at this` could no longer find `Function.update` in
    /// the hypothesis it had just built (`Function.update_injective`,
    /// Mathlib/Logic/Function/Basic). `is_flex_app` deliberately excludes a
    /// bare metavariable (`pattern.rs`: it opens with `if !expr.is_app()`),
    /// which is why the pre-existing unreduced attempt declined here.
    ///
    /// Confined to a CONSTANT head on the opposite side, which is the shape
    /// the measured divergence has and the only one whose folded spelling a
    /// later `rw`/`simp`/`unfold` can key on. A beta redex (`Lam`-headed
    /// application) is deliberately NOT included: it has its own arm above
    /// (`unify_expr.rs`, the `congrArg`/FiniteModel projection-vs-imitation
    /// split), where the reduced solution is tried FIRST and is the one the
    /// LRAT `List.rec`/`congrArg` corpus relies on.
    fn bare_meta_against_const_app(&self, a1: &Expr, a2: &Expr) -> bool {
        let const_app =
            |e: &Expr| e.is_app() && matches!(e.get_app_fn().kind(), ExprKind::Const(_, _));
        (self.as_meta(a1).is_some() && const_app(a2))
            || (self.as_meta(a2).is_some() && const_app(a1))
    }
}

/// Whether `a1` and `a2` are applications of the same constant to the same
/// number of arguments (Lean's `isDefEqApp` / `sameHeadSymbol` shape).
fn same_constant_head(a1: &Expr, a2: &Expr) -> bool {
    let (ExprKind::Const(n1, _), ExprKind::Const(n2, _)) =
        (a1.get_app_fn().kind(), a2.get_app_fn().kind())
    else {
        return false;
    };
    n1 == n2 && a1.is_app() && a1.get_app_num_args() == a2.get_app_num_args()
}

#[cfg(test)]
#[path = "app_heads_structural_first_tests.rs"]
mod structural_first_tests;
