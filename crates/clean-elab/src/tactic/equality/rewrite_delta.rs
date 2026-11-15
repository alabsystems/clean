// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `rw [<definition>]` — rewriting by a DEFINITION name, as a bounded δβ unfold.
//!
//! # What this is for
//!
//! Mathlib writes `rw [Xor', or_and_right, …]` (`Mathlib/Logic/Basic.lean:365`),
//! where `Xor'` is a `def`, not an equation lemma. Clean's rewrite admission
//! rejected such a rule with
//! *"rewrite rule 'Xor'' is not an equation: its type is not of the form
//! (∀ …, a = b) or (∀ …, p ↔ q)"*. Lean 4 instead rewrites by the definition's
//! equation lemma, i.e. it δ-unfolds the constant and β-applies its arguments.
//!
//! # Why it is a SEPARATE module and not a new arm of the shared resolver
//!
//! A previous attempt (reverted 2026-08-23) synthesized the definitional
//! equation *inside* [`super::rewrite::peel_and_resolve_rewrite_equation`] and
//! let it flow through the ordinary rewrite pipeline. Unit tests were green and
//! it then wedged the corpus: `Mathlib/Logic/Basic.lean` ran 17 h 49 m wall /
//! 1069 CPU-minutes at 7 GB RSS with no output (normally ~60 min), and the
//! `Mathlib/Data/Subtype.lean` canary (~4 min) did not finish inside 10 min.
//!
//! Reading every caller of the two shared resolvers shows the *hypothesised*
//! cause — "simp/conv iterate the shared resolver to a fixpoint" — is FALSE:
//! no caller iterates, and simp never reaches this code at all (it has its own
//! delta-unfold seeding, `simp::lemmas::seed_unfold_defs_from_simp_defs`). The
//! cost is not a tactic-level loop; it is what the shared pipeline *does* once
//! a `Definition`-headed pattern is admitted into it:
//!
//! 1. `unify_pattern_with_subterm` walks every subterm of the haystack and, at
//!    each node that is not a rigid-const head mismatch, runs the full unifier
//!    (`Unifier::with_env`, `crates/clean-elab/src/unify/unifier/mod.rs`), whose
//!    `TypeChecker` runs at **Default transparency with `honor_reducibility`
//!    and no heartbeat budget** — the one unbudgeted TC in the elaborator
//!    (`reports/kernel-panic-rca-*`, the 2026-08-13 OOM-wall analysis). Handing
//!    it a pattern whose head is a δ-reducible `Definition` with metavariable
//!    arguments is precisely the "full-delta whnf bomb" class already
//!    documented there (multi-GB working terms, one core pegged).
//! 2. If the metas are then solved against a node that is *not* the surface
//!    occurrence, `finish_rewrite`'s `contains_expr` misses and
//!    `find_defeq_subterm` runs a kernel def-eq scan with a `Definition`-headed
//!    needle.
//! 3. The synthesized `Eq.refl`/`Eq.subst` term embeds the (possibly enormous)
//!    definition body and is re-inferred by `close_goal`'s strict path.
//!
//! This module reaches none of that. It performs the same job the shipped
//! [`crate::tactic::unfold`] tactic already performs — substitute the body,
//! prove nothing, let `replace_target_def_eq` / `replace_local_decl_def_eq`
//! carry the definitional justification — with two guards `unfold` does not
//! have (recursion, node budget). Concretely:
//!
//! * **no unification** — occurrence selection is syntactic (`Const` head of an
//!   application spine), so the unbudgeted unifier is never invoked;
//! * **no synthesized proof term** — nothing new reaches the kernel beyond the
//!   def-eq check `replace_target_def_eq` already performs, so the trust
//!   surface is strictly smaller than the reverted patch's `Eq.refl` cast;
//! * **no fixpoint** — one pass over the goal, one substitution per occurrence;
//! * **bounded** — a self-referential body is refused (a δ step could otherwise
//!   re-introduce its own head), and a body whose traversal exceeds
//!   [`MAX_DELTA_BODY_VISITS`] is refused outright.
//!
//! Every refusal is *fail closed*: the caller falls through to the pre-existing
//! `resolve_env_rewrite_equation` path and the user sees the identical
//! admission error as before this module existed.

use std::cell::Cell;

use clean_kernel::env::{ConstantKind, Reducibility};
use clean_kernel::{Expr, ExprFolder, ExprFolderOpt, ExprKind, FVarId, LevelVec, Name};

use super::super::{Goal, ProofState, TacticError, TacticResult};
use super::expr_utils::{match_equality, match_iff, rewrite_candidate_summaries};

/// Traversal budget for the pre-admission body scan (see [`body_is_unfoldable`]).
///
/// This bounds *visits*, not distinct nodes: `Expr` is `Arc`-shared, so a
/// heavily-shared (DAG) body can be visited far more often than it has nodes,
/// and it is exactly such a body — an olean-imported `WellFounded.fix` /
/// `Nat.rec` compilation — that must never be spliced into a goal. A
/// hand-written `def` of the target class is tiny (Mathlib's `Xor'` body is
/// ~15 nodes), so the budget is ~3 orders of magnitude of headroom for the
/// cases this brick exists to serve, while hard-capping the pathological ones.
///
/// Exceeding it is a REFUSAL, never a truncation: a partially scanned body has
/// not been proved free of self-reference, so admitting it would defeat the
/// recursion guard.
const MAX_DELTA_BODY_VISITS: usize = 20_000;

/// An environment `Definition` admitted as a `rw` δ-unfold rule.
///
/// Constructed only by [`delta_rule`], which enforces every admission gate.
/// Holding the value here (rather than re-reading the environment) keeps the
/// `&ProofState` borrow off the subsequent `&mut ProofState` operations.
pub(super) struct DeltaRule {
    /// The constant being unfolded.
    name: Name,
    /// Its declared universe parameters, in declaration order.
    level_params: Vec<Name>,
    /// Its stored body, over `level_params`. Instantiated per *occurrence*
    /// (each occurrence carries its own level arguments — RC-E.2; see
    /// `tactic::unfold::substitute_const_levels`).
    value: Expr,
}

/// Decide whether `name` is a `rw` rule that must be handled as a δ-unfold
/// rather than as an equation, and capture what the unfold needs.
///
/// The caller owns the local-hypothesis shadowing check (`rw [h]` where `h` is
/// a local hypothesis resolves to the hypothesis, Lean 4 resolution order) and
/// the direction check; this function only inspects the environment.
///
/// Admission gates, all fail-closed — `None` means "not a delta rule", and the
/// caller then takes the pre-existing equation path, which produces the
/// unchanged admission error for a non-equation source:
///
/// 1. `name` resolves to an environment constant.
/// 2. Its kind is `Definition`. Theorems (proof terms are not unfold targets),
///    axioms and opaques (no usable body) are excluded — the same
///    `Definition`-only gate as `simp`'s unfold sources
///    (`simp::lemmas::resolve_unfold_defs`).
/// 3. Its reducibility is not `Irreducible`/`Opaque`. Lean's `rw [f]` cannot
///    unfold an `@[irreducible]` `f` either; admitting one here would only
///    trade the admission error for a later def-eq failure.
/// 4. Its type — under its leading binders — is **neither** an `Eq` **nor** an
///    `Iff`. Equation-typed definitions therefore keep the existing rewrite
///    path *bit for bit*: this module can only fire where the pre-patch code
///    raised the admission error, so no currently-working rewrite changes.
/// 5. It has a stored value.
/// 6. That value passes [`body_is_unfoldable`] (not self-referential, within
///    the traversal budget).
///
/// REQUIRES: `name` is not shadowed by a local hypothesis of the current goal.
/// ENSURES: `Some(rule)` implies unfolding `rule` is a δβ step whose result is
///   definitionally equal to the input, with a body of bounded size.
pub(super) fn delta_rule(
    state: &ProofState,
    name: &clean_parser::SurfaceName,
) -> Option<DeltaRule> {
    let const_name = name.name().clone();
    let info = state.env.get_const(&const_name)?;

    if !matches!(info.kind, ConstantKind::Definition) {
        return None;
    }
    if matches!(
        info.reducibility,
        Reducibility::Irreducible | Reducibility::Opaque
    ) {
        return None;
    }
    if type_is_rewrite_equation(&info.type_) {
        return None;
    }
    let value = info.value.as_ref()?;
    if !body_is_unfoldable(value, &const_name) {
        return None;
    }

    Some(DeltaRule {
        name: const_name,
        level_params: info.level_params.clone(),
        value: value.clone(),
    })
}

/// `rw [<def>]` at the goal: δβ-unfold every occurrence of the rule's constant
/// in the current target.
///
/// The new target is definitionally equal to the old one by construction (δ
/// substitutes a `Definition`'s own body; β contracts the redexes that
/// substitution creates), and `replace_target_def_eq` re-checks exactly that
/// before closing the old goal — so an incorrect unfold fails closed in the
/// kernel rather than being taken on trust here.
///
/// REQUIRES: `state` has a current goal; `rule` came from [`delta_rule`].
/// ENSURES: On `Ok`, the current goal's target has every `rule` occurrence
///   replaced by the β-applied body, and the old goal is closed through
///   `replace_target_def_eq`'s def-eq check.
/// ENSURES: On `Err(RewriteNoMatch)`, the constant did not occur in the target
///   and the proof state is unchanged — `rw` reports a no-match exactly as it
///   does for an equation rule whose LHS is absent, never a silent success.
pub(super) fn unfold_in_goal(state: &mut ProofState, rule: &DeltaRule) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);
    let unfolded = delta_beta_unfold(&target, rule);
    if unfolded == target {
        return Err(no_match_error(rule, &target, Vec::new()));
    }
    state.replace_target_def_eq(unfolded)
}

/// `rw [<def>] at h`: the at-hypothesis analogue of [`unfold_in_goal`].
///
/// Uses `replace_local_decl_def_eq`, the same helper the shipped `unfold_at`
/// tactic uses, which re-checks def-eq before installing the new type.
///
/// REQUIRES: `hyp_fvar` is the fvar of hypothesis `hyp_name` in the current
///   goal; `old_ty` is its type; `rule` came from [`delta_rule`].
/// ENSURES: On `Ok`, `hyp_name`'s type has every `rule` occurrence replaced by
///   the β-applied body.
pub(super) fn unfold_at_hyp(
    state: &mut ProofState,
    rule: &DeltaRule,
    hyp_fvar: FVarId,
    hyp_name: &clean_parser::SurfaceName,
    old_ty: &Expr,
) -> Result<FVarId, TacticError> {
    let old_ty = state.metas.instantiate(old_ty);
    let unfolded = delta_beta_unfold(&old_ty, rule);
    if unfolded == old_ty {
        return Err(no_match_error(
            rule,
            &old_ty,
            vec![format!("hyp:{hyp_name}")],
        ));
    }
    state.replace_local_decl_def_eq_fvar(hyp_fvar, unfolded)
}

/// The `RewriteNoMatch` a `rw [<def>]` reports when the definition does not
/// occur in the rewritten location. Shaped exactly like the equation path's
/// no-match (same `tactic`/`direction` strings and candidate summaries) so
/// diagnostics and any error-shape assertions stay uniform.
fn no_match_error(rule: &DeltaRule, haystack: &Expr, focus_path: Vec<String>) -> TacticError {
    let needle = Expr::const_(rule.name.clone(), LevelVec::new());
    TacticError::RewriteNoMatch {
        tactic: "rewrite".to_owned(),
        rule: rule.name.to_string(),
        direction: "forward".to_owned(),
        searched_for: needle.to_string(),
        focus: haystack.to_string(),
        focus_path,
        candidates: rewrite_candidate_summaries(haystack, &needle, 5),
    }
}

/// Whether `ty`, under its leading `∀`/Pi binders, is an `Eq` or an `Iff`.
///
/// This is the discriminator that keeps this module strictly additive: a
/// `true` here means the existing rewrite pipeline can already admit the rule,
/// so the delta path must stand aside. The peel is purely structural (no
/// `whnf`, no metavariables), mirroring `search::simple::classify_rewrite_head`
/// — a cheap pre-filter, never the thing that builds a proof.
fn type_is_rewrite_equation(ty: &Expr) -> bool {
    let mut codomain = ty;
    while let ExprKind::Pi(_, _, body) = codomain.kind() {
        codomain = body;
    }
    match_equality(codomain).is_ok() || match_iff(codomain).is_some()
}

/// Whether `value` may be spliced into a goal as `name`'s δ-unfold.
///
/// Two refusals, both fail-closed:
///
/// * **self-reference** — a body that mentions its own constant would
///   re-introduce the head it just replaced. `simp` refuses these for the same
///   reason (`seed_unfold_defs_from_simp_defs`, "a naive delta-unfold would
///   re-introduce the constant and loop"); the reverted patch explicitly did
///   NOT, on the reasoning that `rw` performs a single step. That reasoning is
///   right about *this* tactic and wrong about the pipeline it fed, so the
///   guard is reinstated here as the structural loop barrier.
/// * **budget exhaustion** — traversal is capped at [`MAX_DELTA_BODY_VISITS`]
///   visits via `ExprFolderOpt::should_descend`, which stops descent without
///   allocating (every hook returns `None`, so nothing is rebuilt). An
///   exhausted scan has NOT established freedom from self-reference, so it must
///   refuse; it also refuses precisely the enormous compiled bodies whose
///   substitution produced the 7 GB working set in the reverted attempt.
///
/// ENSURES: Returns in `O(MAX_DELTA_BODY_VISITS)` regardless of `value`'s size.
/// ENSURES: `true` implies `value` contains no `Const(name, _)` node.
fn body_is_unfoldable(value: &Expr, name: &Name) -> bool {
    body_is_unfoldable_within(value, name, MAX_DELTA_BODY_VISITS)
}

/// [`body_is_unfoldable`] with an explicit visit budget, so the guard's two
/// refusal modes can be unit-tested without building a 20 000-node term.
fn body_is_unfoldable_within(value: &Expr, name: &Name, budget: usize) -> bool {
    struct BodyGuard<'a> {
        target: &'a Name,
        /// Remaining traversal budget. `Cell` because `should_descend` takes
        /// `&self` (it is documented as an O(1) metadata guard).
        budget: Cell<usize>,
        /// Set when the budget ran out, i.e. the scan is INCOMPLETE.
        exhausted: Cell<bool>,
        /// Set when `target` occurs in the body.
        self_referential: bool,
    }

    impl ExprFolderOpt for BodyGuard<'_> {
        fn should_descend(&self, _expr: &Expr) -> bool {
            match self.budget.get().checked_sub(1) {
                Some(remaining) => {
                    self.budget.set(remaining);
                    true
                }
                None => {
                    self.exhausted.set(true);
                    false
                }
            }
        }

        fn fold_const_opt(&mut self, name: &Name, _levels: &LevelVec) -> Option<Expr> {
            if name == self.target {
                self.self_referential = true;
            }
            // `None` = "unchanged": the scan never rebuilds the term.
            None
        }
    }

    let mut guard = BodyGuard {
        target: name,
        budget: Cell::new(budget),
        exhausted: Cell::new(false),
        self_referential: false,
    };
    // Every hook returns `None`, so the folder is sharing-preserving and
    // rebuilds nothing; the `_`-prefixed binding keeps the `debug_assert!` able
    // to state that invariant without warning in release builds.
    let _scan = ExprFolderOpt::fold_expr_opt(&mut guard, value);
    debug_assert!(
        _scan.is_none(),
        "the body guard must be a pure scan, never a rewrite"
    );
    !guard.self_referential && !guard.exhausted.get()
}

/// δ-unfold `rule` in `expr` and β-apply the arguments it was applied to.
///
/// At an application spine whose head is `Const(rule.name, levels)` the whole
/// spine is replaced by `body[levels]` β-applied to the (recursively unfolded)
/// arguments, so the result is the instantiated body rather than a
/// `(fun … ) arg…` redex chain — which matters beyond cosmetics: the remaining
/// rules of a `rw [Xor', or_and_right, …]` chain select their occurrence
/// *syntactically*, and would not see their pattern under an un-contracted
/// redex.
///
/// A bare (unapplied) occurrence is replaced by the level-instantiated body,
/// exactly as `tactic::unfold::substitute_const_levels` does.
///
/// KNOWN NARROWNESS (fail-soft, not unsound): a spine head hidden under
/// `MData` is not recognised as the spine head, so that occurrence takes the
/// bare-constant path and leaves a β-redex behind. The result is still
/// definitionally equal — only a later syntactic match may miss. This matches
/// the shipped `unfold` tactic's behaviour and is deliberately not "fixed" by
/// whnf-ing anything here.
fn delta_beta_unfold(expr: &Expr, rule: &DeltaRule) -> Expr {
    struct UnfoldFolder<'a> {
        rule: &'a DeltaRule,
    }

    impl UnfoldFolder<'_> {
        /// `rule.value` with the declaration's level params instantiated by the
        /// level arguments THIS occurrence carries (RC-E.2: substituting a
        /// polymorphic body verbatim leaves dangling `Sort (Param u)`s).
        fn body_at(&self, levels: &LevelVec) -> Expr {
            self.rule
                .value
                .instantiate_level_params_direct(&self.rule.level_params, levels)
        }
    }

    impl ExprFolder for UnfoldFolder<'_> {
        fn fold_app(&mut self, f: &Expr, a: &Expr) -> Expr {
            // `fold_expr` dispatches top-down, so the OUTERMOST `App` of a
            // spine is seen first; handling the full spine here means the inner
            // `App` nodes of the same spine are never folded separately (and
            // hence the head `Const` never reaches `fold_const`).
            if let ExprKind::Const(name, levels) = f.get_app_fn().kind() {
                if name == &self.rule.name {
                    let mut args: Vec<Expr> = f
                        .get_app_args()
                        .into_iter()
                        .map(|arg| self.fold_expr(arg))
                        .collect();
                    args.push(self.fold_expr(a));
                    return beta_apply(self.body_at(levels), &args);
                }
            }
            Expr::app(self.fold_expr(f), self.fold_expr(a))
        }

        fn fold_const(&mut self, name: &Name, levels: &LevelVec) -> Expr {
            if name == &self.rule.name {
                self.body_at(levels)
            } else {
                Expr::const_(name.clone(), levels.clone())
            }
        }
    }

    let mut folder = UnfoldFolder { rule };
    folder.fold_expr(expr)
}

/// β-apply `value` (a definition's stored body) to `args`.
///
/// Leading lambdas are consumed by substitution so the result is the
/// instantiated body. If the value runs out of leading lambdas before the
/// argument list is exhausted — an eta-contracted body such as
/// `def f : Nat → Nat := Nat.succ`, or a `match`-compiled spine under `MData` —
/// the remaining arguments are re-applied as ordinary `App`s. That is still
/// definitionally equal at the applied type, which is all the caller's
/// `replace_target_def_eq` def-eq check needs.
///
/// ENSURES: Runs in `O(args.len())` substitutions; it never iterates to a
///   fixpoint and never re-examines its own output for further redexes.
fn beta_apply(value: Expr, args: &[Expr]) -> Expr {
    let mut current = value;
    for arg in args {
        // `current.clone()` in the fallback arm keeps the scrutinee borrow of
        // `current.kind()` and the consumption of `current` apart (`Expr` is
        // `Arc`-backed; the clone is a refcount bump, not a deep copy).
        let next = match current.kind() {
            ExprKind::Lam(_, _, body) => body.instantiate(arg),
            _ => Expr::app(current.clone(), arg.clone()),
        };
        current = next;
    }
    current
}

/// Whether `goal` has a local hypothesis named `name`.
///
/// `rw` resolution order is Lean 4's: a local hypothesis shadows an
/// environment constant of the same name, so the delta path must not even look
/// at the environment when one exists.
pub(super) fn shadowed_by_local(goal: &Goal, name: &clean_parser::SurfaceName) -> bool {
    goal.local_ctx
        .iter()
        .any(|d| crate::tactic::pattern::names::hypothesis_named(&d.name, name))
}

#[cfg(test)]
mod tests {
    //! Unit coverage for the two admission guards that the reverted
    //! 2026-08-23 attempt did not have. These are NOT the acceptance evidence
    //! for this brick — see `patches/rw-def-unfold-v2/NOTES.md`: a change on a
    //! rewrite path is only shippable behind a timed real-corpus canary. They
    //! exist so a future edit cannot silently delete a guard.

    use super::*;
    use clean_kernel::Level;

    fn const_(name: &str) -> Expr {
        Expr::const_(Name::from_string(name), LevelVec::new())
    }

    #[test]
    fn test_body_guard_accepts_an_ordinary_body() {
        // `Or (And p q) (And q p)` — the `Xor'`-shaped body, ~10 nodes.
        let body = Expr::app(
            Expr::app(const_("Or"), Expr::app(const_("p"), const_("q"))),
            Expr::app(const_("q"), const_("p")),
        );
        assert!(
            body_is_unfoldable(&body, &Name::from_string("PXor")),
            "a small body that does not mention its own constant is unfoldable"
        );
    }

    #[test]
    fn test_body_guard_refuses_a_self_referential_body() {
        // The loop barrier: a body mentioning its own constant would
        // re-introduce the head the delta step just replaced.
        let body = Expr::app(const_("PXor"), const_("p"));
        assert!(
            !body_is_unfoldable(&body, &Name::from_string("PXor")),
            "a body referencing its own constant must be refused"
        );
    }

    #[test]
    fn test_body_guard_refuses_when_the_visit_budget_is_exhausted() {
        // An oversized body is refused, not truncated: a partial scan has not
        // established freedom from self-reference.
        let mut body = const_("base");
        for _ in 0..32 {
            body = Expr::app(body, const_("arg"));
        }
        assert!(
            !body_is_unfoldable_within(&body, &Name::from_string("PXor"), 8),
            "a body whose traversal exceeds the budget must be refused"
        );
        assert!(
            body_is_unfoldable_within(&body, &Name::from_string("PXor"), 10_000),
            "the same body is accepted when the budget covers it"
        );
    }

    #[test]
    fn test_equation_typed_declarations_are_not_delta_rules() {
        // Gate 4: an `Eq`/`Iff`-typed declaration keeps the existing equation
        // path, so this module can only ever fire where `rw` used to raise its
        // admission error.
        let eq_ty = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                    const_("N"),
                ),
                const_("x"),
            ),
            const_("y"),
        );
        assert!(type_is_rewrite_equation(&eq_ty));

        let iff_ty = Expr::app(Expr::app(const_("Iff"), const_("p")), const_("q"));
        assert!(type_is_rewrite_equation(&iff_ty));

        // `(a b : Prop) → Prop` — the `Xor'` shape, the one this module serves.
        let def_ty = Expr::pi(
            clean_kernel::BinderInfo::Default,
            Expr::prop(),
            Expr::pi(
                clean_kernel::BinderInfo::Default,
                Expr::prop(),
                Expr::prop(),
            ),
        );
        assert!(!type_is_rewrite_equation(&def_ty));
    }
}
