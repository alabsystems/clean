// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Calc block elaboration: desugars `calc step1 step2 ...` to transitivity chains.
//!
//! A calc block is a sequence of steps, each asserting a relation (`a = b`, `a ≤ c`, etc.)
//! with a proof. The steps are chained via relation-specific transitivity lemmas:
//!
//! ```text
//! calc
//!   a ≤ b := proof1
//!   _ < c := proof2
//! ```
//!
//! desugars to `lt_of_le_of_lt proof1 proof2 : a < c`.
//!
//! Supports all combinations in the transitivity rule table (20 rules):
//! - Pure equality: `Eq.trans`
//! - Pure ordering: `le_trans`, `lt_trans`, `ge_trans`, `gt_trans`
//! - Mixed LE/LT: `lt_of_le_of_lt`, `lt_of_lt_of_le`
//! - Mixed GE/GT: `gt_of_ge_of_gt`, `gt_of_gt_of_ge`
//! - Eq mixed with any ordering: `le_of_eq_of_le`, `lt_of_eq_of_lt`, etc.
//! - Iff: `Iff.trans`
//! - Ne with Eq: `ne_of_eq_of_ne`, `ne_of_ne_of_eq`
//!
//! Falls back to `Trans.trans` for unrecognized relation types.
//!
//! Reference: ~/lean4-ref/src/Lean/Elab/Calc.lean

use super::*;
use crate::tactic::calc::CalcRel;
use crate::tactic::calc_trans::lookup_trans_rule;
use crate::tactic::calc_trans_match::{calc_endpoints, calc_relation_head, match_goal_rel};
use clean_parser::{SurfaceCalcJustification, SurfaceCalcStep};

impl<'a> ElabCtx<'a> {
    /// Elaborate a calc proof block.
    ///
    /// Each step produces a proof of a relation. Steps are chained:
    /// - Step 1: proof₁ : a R₁ b
    /// - Step 2: proof₂ : b R₂ c
    /// - Result: Trans.trans proof₁ proof₂ : a R c
    ///
    /// If only one step, return its proof directly.
    pub(crate) fn elab_calc(&mut self, steps: &[SurfaceCalcStep]) -> Result<Expr, ElabError> {
        if steps.is_empty() {
            return Err(ElabError::NotImplemented("empty calc block".into()));
        }

        // Elaborate the first step to get (proof, type) pair. The first step has
        // no predecessor, so its `_` (if any) cannot be threaded.
        let first = &steps[0];
        let (mut result_proof, mut result_type, mut prev_rhs) = self.elab_calc_step(first, None)?;

        // Chain remaining steps. Each subsequent step's leading `_` placeholder is
        // threaded with the previous step's right-hand side (Lean's
        // `annotateFirstHoleWithType` / `isDefEqGuarded lhs prevRhs`), then its
        // proof is composed with the running result via transitivity.
        for step in &steps[1..] {
            let (step_proof, step_type, step_rhs) = self.elab_calc_step(step, Some(&prev_rhs))?;
            let (chained_proof, chained_type) =
                self.mk_calc_trans(result_proof, result_type, step_proof, step_type)?;
            result_proof = chained_proof;
            result_type = chained_type;
            prev_rhs = step_rhs;
        }

        Ok(result_proof)
    }

    /// Elaborate a single calc step: relation + justification.
    ///
    /// `prev_rhs` is the right-hand side of the previous step (if any). When
    /// present, the step's left-hand side is unified with it. This both
    /// (a) pins the `_` placeholder that opens a step like `_ ≤ c` to the
    /// previous step's RHS — Lean's `annotateFirstHoleWithType` — and
    /// (b) rejects a broken chain whose middle term does not connect
    /// (Lean's `isDefEqGuarded lhs prevRhs`).
    ///
    /// Returns `(proof, relation_type, rhs)` where `relation_type` is the
    /// elaborated relation expression (e.g. the type `a ≤ b`) and `rhs` is its
    /// right-hand side, threaded into the next step.
    fn elab_calc_step(
        &mut self,
        step: &SurfaceCalcStep,
        prev_rhs: Option<&Expr>,
    ) -> Result<(Expr, Expr, Expr), ElabError> {
        // Elaborate the relation expression as a type. A leading `_` becomes a
        // fresh metavariable that is pinned below by unifying the step's LHS with
        // the previous step's RHS.
        let rel_type = self.elaborate(&step.rel)?;
        let rel_type = self.metas.instantiate(&rel_type);

        // Decompose the relation into (lhs, rhs) and, when chaining, connect the
        // chain by unifying this step's LHS with the previous step's RHS.
        //
        // `calc_endpoints` is Lean's `getCalcRelation?`: the dedicated
        // seven-relation matcher first, then the generic "last two arguments"
        // rule. Gating on the dedicated matcher alone rejected every relation
        // outside {Eq, Ne, LE.le, LT.lt, GE.ge, GT.gt, Iff} — `List.Sublist`,
        // `List.Perm`, a user's own inductive relation — with "relation
        // expected", before any transitivity lemma was ever consulted.
        let (lhs, fallback_rhs) = calc_endpoints(&rel_type).ok_or_else(|| {
            ElabError::NotImplemented(format!("calc step: relation expected, got {rel_type:?}"))
        })?;

        if let Some(prev) = prev_rhs {
            let prev = self.metas.instantiate(prev);
            let lhs_inst = self.metas.instantiate(&lhs);
            // Unify LHS with the previous RHS. For `_ ≤ c` this assigns the
            // placeholder metavariable; for an explicit middle term it checks the
            // chain actually connects and ERRORS otherwise (no over-accept).
            let unified = {
                let ctx = self.build_local_ctx();
                let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
                matches!(unifier.unify(&lhs_inst, &prev), UnifyResult::Success)
            };
            if !unified {
                return Err(ElabError::TypeMismatch {
                    expected: format!("calc step LHS = previous RHS {prev:?}"),
                    actual: format!("{lhs_inst:?}"),
                });
            }
        }

        // Re-instantiate the relation type now that the placeholder is pinned, so
        // the proof is checked against the connected relation (e.g. `b ≤ c`).
        let rel_type = self.metas.instantiate(&rel_type);

        // Elaborate the justification as a proof of rel_type, ensuring the proof
        // actually has that type (Lean's `elabTermEnsuringType`). This pins any
        // remaining metavariables in the relation from the proof's type.
        let proof = match &step.proof {
            SurfaceCalcJustification::Term(term_expr) => {
                // `:= proof_term` — elaborate the term against the relation type.
                let proof = self.elaborate_with_expected_type(term_expr, Some(rel_type.clone()))?;
                self.coerce_to_expected_type(&proof, &rel_type)?
            }
            SurfaceCalcJustification::Tactic(tactics) => {
                // `:= by tac_seq` — run tactic elaboration, then ensure the type.
                //
                // The step's `by`-block goal is THIS step's relation (`b = c`),
                // not the enclosing calc block's goal (`a = c`). `elab_by_tactic`
                // reads `current_expected_type` as its tactic goal, so it must be
                // pointed at `rel_type` for the duration of the block — exactly as
                // the term-mode arm passes `rel_type` to
                // `elaborate_with_expected_type`. Without this, every step's
                // `by`-block inherits the STALE outer calc target (the theorem's
                // `by calc …` goal), so `exact h1`/`exact h2` unifies its proof
                // against the wrong relation and reports a spurious `fvar
                // mismatch` (e.g. `b` vs `c`). Save/restore around the call so the
                // outer expected type is unchanged for subsequent steps and for
                // `mk_calc_trans`. Soundness: this only sets the EXPECTED type for
                // the block; the produced proof is coerced to `rel_type` below,
                // the chain is assembled by `mk_calc_trans`, and the whole calc
                // term is kernel-rechecked by `verify_tactic_proof`/`add_decl`.
                let saved_expected = self.current_expected_type.take();
                self.current_expected_type = Some(rel_type.clone());
                let proof = self.elab_by_tactic(tactics);
                self.current_expected_type = saved_expected;
                let proof = proof?;
                self.coerce_to_expected_type(&proof, &rel_type)?
            }
        };

        // Recompute the relation type and RHS after the proof has been checked,
        // so the threaded RHS reflects any metavariable assignments.
        let rel_type = self.metas.instantiate(&rel_type);
        let rhs = match calc_endpoints(&rel_type) {
            Some((_, rhs)) => self.metas.instantiate(&rhs),
            None => self.metas.instantiate(&fallback_rhs),
        };

        Ok((proof, rel_type, rhs))
    }

    /// Chain two calc steps via the appropriate transitivity lemma.
    ///
    /// Given:
    ///   result: proof₁ : a R₁ b
    ///   step:   proof₂ : b R₂ c
    /// Produces:
    ///   @lemma ty a b c proof₁ proof₂ : a R c
    ///
    /// where `lemma` is looked up from the transitivity rule table based on
    /// the detected relations R₁ and R₂. Supports mixed chains like
    /// LE + LT = LT, EQ + LE = LE, etc.
    ///
    /// Falls back to `Trans.trans proof₁ proof₂` when the relation types
    /// cannot be detected (e.g., user-defined relations).
    #[cfg_attr(test, allow(dead_code))]
    pub(crate) fn mk_calc_trans(
        &mut self,
        result: Expr,
        result_type: Expr,
        step: Expr,
        step_type: Expr,
    ) -> Result<(Expr, Expr), ElabError> {
        let result_type = self.metas.instantiate(&result_type);
        let step_type = self.metas.instantiate(&step_type);

        // Try to detect the relations from the elaborated types and pick the
        // dedicated transitivity lemma (`le_trans`, `lt_of_le_of_lt`, …).
        let result_match = match_goal_rel(&result_type);
        let step_match = match_goal_rel(&step_type);

        // Eq-mixed steps: exactly one side is `=`. There are no carrier
        // `le_of_le_of_eq`-style transitivity lemmas registered, so compose via
        // subst (`▸`) instead — for `x R b` with `b = c` transport the relation
        // proof along the equality (and symmetrically for `a = b` with `b R c`).
        // Both-`=` is left to the `Eq.trans` rule below. The transport result is
        // kernel-re-checked by `close_goal`.
        //
        // Only ONE side has to be a recognized `Eq`: the other may be any
        // relation at all (`List.Sublist`, a user relation, …), because
        // transporting a proof along an equality is relation-agnostic. Gating
        // both sides on the dedicated matcher kept `a = b` followed by
        // `MyR b c` out of this path even though `Eq.rec` handles it.
        {
            let a_is_eq = matches!(result_match, Some((CalcRel::Eq, ..)));
            let b_is_eq = matches!(step_match, Some((CalcRel::Eq, ..)));
            if a_is_eq != b_is_eq {
                // step is `=` → cast the result proof along the step equality;
                // result is `=` → cast the step proof along the result equality.
                let (heq, h) = if b_is_eq {
                    (step.clone(), result.clone())
                } else {
                    (result.clone(), step.clone())
                };
                if let Ok(Some((cast, cast_ty))) = self.subst_transport_elaborated(heq, h) {
                    // `subst_transport_elaborated` returns the SURFACE result
                    // type (`x R c`, …), so it is directly recognizable by
                    // `match_goal_rel` and can thread into a following calc step
                    // (multi-step `a = b ≤ c < d` chains). `close_goal` re-checks
                    // the `@Eq.rec` term against the goal (fail-closed).
                    let cast_ty = self.metas.instantiate(&cast_ty);
                    if calc_endpoints(&cast_ty).is_some() {
                        return Ok((cast, cast_ty));
                    }
                }
            }
        }

        if let (Some((rel_a, ty, a_ep, b_ep, _)), Some((rel_b, _, _, c_ep, _))) =
            (&result_match, &step_match)
        {
            if let Some(rule) = lookup_trans_rule(*rel_a, *rel_b) {
                // Try each candidate transitivity lemma in priority order:
                // the carrier-qualified lemma first (e.g. `Nat.le_trans`, which
                // this environment registers as a real theorem), then the bare
                // lemma (`le_trans`). The bare name can be a degenerate stub
                // (`le_trans : Sort u`) that `apply_lemma_to_proofs` rejects;
                // looking up a *registered* per-type lemma is read-only and does
                // not touch instance registration.
                let mut cand_names = self.trans_lemma_candidates(ty, rule.lemma_name);
                // `lt` + `le` also composes via `le_trans` when `lt x y` is
                // definitionally `le (x + 1) y` (Nat, Int, …): `le_trans
                // (h1 : le (a+1) b) (h2 : le b c) : le (a+1) c ≡ a < c`. This
                // closes `a < b ≤ c` even when the carrier's dedicated
                // `lt_of_lt_of_le` lemma is not registered (e.g. Nat, where only
                // `Nat.le_trans` exists). Tried only after the dedicated lemma so
                // carriers that DO register it (Int) are unaffected.
                if matches!(rule.rel_a, CalcRel::Lt) && matches!(rule.rel_b, CalcRel::Le) {
                    cand_names.extend(self.trans_lemma_candidates(ty, "le_trans"));
                }
                for cand in cand_names {
                    let cname = Name::from_string(&cand);
                    if self.env.get_const(&cname).is_none() {
                        continue;
                    }
                    // Apply the lemma to just the two proofs, letting implicit
                    // argument insertion fill the type, instance, and endpoint
                    // arguments from the proof types (rather than guessing
                    // universe levels). This mirrors `Nat.le_trans h1 h2` — it
                    // works when the endpoints `{a b c}` are IMPLICIT binders.
                    let lemma = self.mk_const_str(&cand);
                    if let Ok((proof, lty)) =
                        self.apply_lemma_to_proofs(lemma.clone(), &result, &step)
                    {
                        if match_goal_rel(&lty).is_some() {
                            return Ok((proof, lty));
                        }
                    }
                    // Fallback for lemmas whose endpoint binders are EXPLICIT,
                    // e.g. the mixed-relation `Nat.lt_of_le_of_lt (a b c : Nat)
                    // (h1 : a ≤ b) (h2 : b < c)`. `apply_lemma_to_proofs` cannot
                    // handle these — it only auto-inserts implicit/instance
                    // leading binders, so it would try to unify `h1` against the
                    // endpoint domain (`Nat`) and fail. Supply the three
                    // endpoints `a`, `b`, `c` (from the calc step relation types)
                    // directly, then the two proofs, and keep the result only if
                    // it type-checks to a relation (`close_goal` re-checks it).
                    if let Some((proof, lty)) =
                        self.try_apply_explicit_endpoints(&lemma, a_ep, b_ep, c_ep, &result, &step)
                    {
                        return Ok((proof, lty));
                    }
                }
            }
        }

        // Relation-native transitivity: when both steps carry the SAME relation
        // head `R`, use that relation's own transitivity lemma `R.trans`
        // (`List.Sublist.trans`, `List.Perm.trans`, a user's `MyR.trans`, …).
        //
        // This is not a heuristic detour around the `Trans` class — it is the
        // very term Lean's `Trans` instances are built from
        // (`instance : Trans (@Sublist α) Sublist Sublist := ⟨Sublist.trans⟩`),
        // so it composes the identical proof. It is tried before the class
        // route because Clean's built-in three-universe `Trans` stub
        // (`clean-kernel/src/env/order_structures.rs`) shadows Lean's real
        // six-universe `Trans` on import, so no imported `Trans` instance is
        // currently synthesizable at all — see `data/prelude_collision_census.json`.
        // When that collision is retired this route simply becomes a fast path.
        //
        // Read-only: it looks a constant up and applies it. The applied term is
        // type-checked by `apply_lemma_to_proofs` (`infer_type`) and re-checked
        // by the kernel through `add_decl`/`close_goal`, so a relation whose
        // `.trans` has an unrelated shape fails loudly rather than over-accepts.
        let same_head = match (
            calc_relation_head(&result_type),
            calc_relation_head(&step_type),
        ) {
            (Some(head_a), Some(head_b)) if head_a == head_b => Some(head_a),
            _ => None,
        };
        if let Some(head) = same_head {
            let cand = format!("{head}.trans");
            if self.env.get_const(&Name::from_string(&cand)).is_some() {
                let lemma = self.mk_const_str(&cand);
                if let Ok((proof, lty)) = self.apply_lemma_to_proofs(lemma, &result, &step) {
                    if calc_endpoints(&lty).is_some() {
                        return Ok((proof, lty));
                    }
                }
            }
        }

        // Fallback: compose via the `Trans` typeclass, mirroring Lean's
        // `mkCalcTrans`. Insert the implicit `{α β γ r s t}` + instance
        // `[Trans r s t]` arguments BEFORE applying the two proofs so that no
        // free metavariable leaks into the result term.
        let trans = self.mk_const_str("Trans.trans");
        let (proof, ty) = self.apply_lemma_to_proofs(trans, &result, &step)?;

        // The composed result must itself be a relation, otherwise the chain is
        // ill-formed (Lean errors with "step result is not a relation"). Uses
        // the same generic decomposition Lean applies here (`getCalcRelation?`),
        // so a `Trans` instance producing a non-enum output relation is accepted.
        if calc_endpoints(&ty).is_none() {
            return Err(ElabError::NotImplemented(format!(
                "calc: composed step result is not a relation: {ty:?}"
            )));
        }

        Ok((proof, ty))
    }

    /// Apply a carrier-qualified transitivity lemma whose endpoint binders are
    /// EXPLICIT — e.g. `Nat.lt_of_le_of_lt (a b c : Nat) (h1 : a ≤ b)
    /// (h2 : b < c) : a < c`. Builds `@lemma a b c left_proof right_proof` with
    /// the three endpoints supplied directly (from the calc step relation
    /// types), unifying each proof against the expected domain (def-eq). Returns
    /// `Some((term, ty))` only when the lemma is fully applied to a relation;
    /// otherwise `None` (the lemma's shape did not match, so the caller falls
    /// through to the next candidate).
    ///
    /// This is the explicit-endpoint counterpart of `apply_lemma_to_proofs`
    /// (which handles only implicit/instance leading binders). Soundness is
    /// guaranteed by `infer_type` here plus the caller's `close_goal` re-check.
    fn try_apply_explicit_endpoints(
        &mut self,
        lemma: &Expr,
        a: &Expr,
        b: &Expr,
        c: &Expr,
        left_proof: &Expr,
        right_proof: &Expr,
    ) -> Option<(Expr, Expr)> {
        let mut term = lemma.clone();
        let mut ty = self.infer_type(lemma).ok()?;
        // Apply the three explicit endpoint arguments `a`, `b`, `c` directly.
        for endpoint in [a, b, c] {
            ty = self.whnf(&self.metas.instantiate(&ty));
            let body = match ty.kind() {
                ExprKind::Pi(_, _dom, body) => body.as_ref().clone(),
                _ => return None,
            };
            term = Expr::app(term, endpoint.clone());
            ty = self.metas.instantiate(&body.instantiate(endpoint));
        }
        // Apply the two relation proofs, unifying each against the expected
        // binder domain. Unification (unlike a strict `infer_type` arg-check)
        // reconciles the surface `LE.le α inst a b` / `LT.lt α inst a b` with the
        // carrier lemma's direct `α.le a b` / `α.lt a b` via def-eq unfolding.
        for proof in [left_proof, right_proof] {
            ty = self.whnf(&self.metas.instantiate(&ty));
            let (dom, body) = match ty.kind() {
                ExprKind::Pi(_, dom, body) => (dom.as_ref().clone(), body.as_ref().clone()),
                _ => return None,
            };
            let expected = self.metas.instantiate(&dom);
            let proof_ty = self.metas.instantiate(&self.infer_type(proof).ok()?);
            let unified = {
                let ctx = self.build_local_ctx();
                let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
                matches!(unifier.unify(&proof_ty, &expected), UnifyResult::Success)
            };
            if !unified {
                return None;
            }
            term = Expr::app(term, proof.clone());
            ty = self.metas.instantiate(&body.instantiate(proof));
        }
        // Require the lemma to be FULLY applied — its conclusion must be the
        // result relation, not a leftover `Pi` (which would mean the lemma had a
        // different arity than the expected 3 endpoints + 2 proofs). Accept both
        // the surface (`LT.lt α inst a c`) and direct (`α.lt a c`) relation
        // forms; `close_goal` re-checks the whole term against the goal.
        let ty = self.metas.instantiate(&self.infer_type(&term).ok()?);
        let ty_whnf = self.whnf(&ty);
        if matches!(ty_whnf.kind(), ExprKind::Pi(..)) {
            return None;
        }
        Some((term, ty))
    }

    /// Build the ordered list of candidate transitivity lemma names for a calc
    /// step, from most specific to most general.
    ///
    /// For a carrier type whose head is a constant `C` (e.g. `Nat`), the
    /// carrier-qualified name `C.<lemma>` (e.g. `Nat.le_trans`) is tried first,
    /// then the bare `<lemma>` (e.g. `le_trans`). This is a read-only lookup of
    /// already-registered constants — it does not register anything.
    fn trans_lemma_candidates(&self, carrier_ty: &Expr, lemma: &str) -> Vec<String> {
        let mut candidates = Vec::new();
        let carrier = self.whnf(&self.metas.instantiate(carrier_ty));
        if let ExprKind::Const(name, _) = carrier.get_app_fn().kind() {
            let head = name.to_string();
            if !head.is_empty() {
                candidates.push(format!("{head}.{lemma}"));
            }
        }
        candidates.push(lemma.to_string());
        candidates
    }

    /// Apply a transitivity lemma to exactly two proof arguments, inserting any
    /// leading/intermediate implicit and instance arguments and unifying each
    /// explicit argument's type with the proof's type.
    ///
    /// Returns `(applied_proof, result_type)` where `result_type` is the inferred
    /// type of the fully applied term with metavariables instantiated. The two
    /// proofs are applied as the lemma's two explicit (relation-proof) arguments;
    /// implicit `{…}` and instance `[…]` binders encountered before/between them
    /// are filled via `insert_implicit_args` (metavariables + instance
    /// resolution), exactly as ordinary application elaboration would.
    fn apply_lemma_to_proofs(
        &mut self,
        lemma: Expr,
        left_proof: &Expr,
        right_proof: &Expr,
    ) -> Result<(Expr, Expr), ElabError> {
        let lemma_type = self.infer_type(&lemma)?;
        // Defer instance resolution (e.g. `[Trans r s t]`): when the leading
        // implicit binders are inserted, the relation carriers `r`/`s`/`t` are
        // still metavariables, so an eager `resolve_instance` cannot pick the
        // right `Trans` instance. We pin those carriers from the proof types
        // first, then resolve the recorded instance metavariables — Lean's
        // postponement of typeclass resolution (`mkCalcTrans`).
        let (mut term, mut ty, mut pending) =
            self.insert_implicit_args_deferring_instances(lemma, &lemma_type);

        for proof in [left_proof, right_proof] {
            ty = self.whnf(&self.metas.instantiate(&ty));
            let (binder_dom, body) = match ty.kind() {
                ExprKind::Pi(_, dom, body) => (dom.as_ref().clone(), body.as_ref().clone()),
                _ => {
                    return Err(ElabError::NotImplemented(format!(
                        "calc: transitivity lemma is not a function expecting proofs: {ty:?}"
                    )));
                }
            };

            let expected = self.metas.instantiate(&binder_dom);
            let proof_ty = self.metas.instantiate(&self.infer_type(proof)?);
            // Unify the proof's type with the expected argument type. This pins
            // the lemma's implicit endpoints (e.g. the middle term `b`) and the
            // carrier metavariables from the actual proof types.
            let unified = {
                let ctx = self.build_local_ctx();
                let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
                matches!(unifier.unify(&proof_ty, &expected), UnifyResult::Success)
            };
            if !unified {
                return Err(ElabError::TypeMismatch {
                    expected: format!("{expected:?}"),
                    actual: format!("{proof_ty:?}"),
                });
            }

            term = Expr::app(term, proof.clone());
            ty = self.metas.instantiate(&body.instantiate(proof));
            // Insert any implicit/instance binders that follow this explicit arg,
            // again deferring instance resolution until carriers are pinned.
            let (next_term, next_ty, mut next_pending) =
                self.insert_implicit_args_deferring_instances(term, &ty);
            term = next_term;
            ty = next_ty;
            pending.append(&mut next_pending);
        }

        // Now that the proofs have pinned the relation carriers, resolve the
        // deferred instance arguments (e.g. synthesize `[Trans (·≤·) (·≤·) ?t]`,
        // which also determines the output relation `t`).
        if !pending.is_empty() && !self.resolve_deferred_instances(&pending) {
            return Err(ElabError::NotImplemented(
                "calc: failed to synthesize transitivity instance".into(),
            ));
        }

        let term = self.metas.instantiate(&term);
        let term = self.metas.instantiate_levels(&term);
        let ty = self.metas.instantiate(&self.infer_type(&term)?);
        Ok((term, ty))
    }
}
