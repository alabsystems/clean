// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Faithful `Block.compose` carrier for the C006 MASQUERADE cluster (#3491).
//!
//! Companion to `nn_verify_blockwise_crown_ext_carriers.rs`. Split out
//! so each sibling module stays under the 500-line file-size limit.
//!
//! ## Purpose
//!
//! Phase 2 of `designs/2026-04-19-demasquerade-cxxx-pattern.md` demands
//! faithful replacements for the two `C006` carriers (`Block.compose`
//! and `Block.monolithic_crown`) that currently both reduce to
//! `zero_ib (block_dim k)` and therefore collapse every C006 theorem
//! into a vacuous identity via Rule M1 (alias-collapse) + Rule M2
//! (argument-discarding) + Rule M3 (IH-ignoring step).
//!
//! This module registers:
//!
//! - `NNVerify.Block.compose_faithful :
//!     (d : Nat) -> (k : Nat) ->
//!     (cb : Nat -> IntervalBounds d -> IntervalBounds d) ->
//!     IntervalBounds d -> IntervalBounds d`
//!   with body
//!   `fun d k cb B =>
//!      @Nat.rec.{1} (fun _ => IB d) B (fun m ih => cb m ih) k`.
//!   Structurally distinct from `Block.monolithic_crown_faithful`
//!   (in `nn_verify_blockwise_crown_ext_carriers.rs`): the step case
//!   applies `cb m ih` instead of returning `zero_ib d`, so the step's
//!   induction hypothesis is actually consumed (Rule M3 inverted).
//!
//! - `NNVerify.Block.compose_faithful_zero_eq_input` — the
//!   specialisation at `k = Nat.zero`, proving
//!   `compose_faithful d 0 cb B = B` via `Eq.refl` on the bound
//!   variable `B` (not a collapsed constant; Rule M4 inverted).
//!
//! ## What this does NOT do
//!
//! - It does NOT re-promote `NNVerify.C006.blockwise_step` from axiom
//!   to theorem. That is Phase 3 of #3491 and requires the new
//!   carriers to be wired into the `C006.blockwise_*` theorem types.
//! - It does NOT yet touch `NNVerify.Block.compose` itself — that
//!   carrier lives in `nn_verify_blockwise_crown_values.rs` and still
//!   has the masquerading `zero_ib` body. The faithful sibling
//!   registered here is a non-aliased companion that Phase 3 can
//!   migrate the C006 theorems to consume.
//!
//! Part of #3491 Phase 2 (faithful carriers).

use super::nn_verify_blockwise_crown::BlockwiseCrownConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `NNVerify.Block.compose_faithful`.
    ///
    /// **Faithful-carrier replacement** for `Block.compose` (see #3491
    /// MASQUERADE Phase 2, Branch B). The old carrier's body was
    /// `fun k bd cb lg lb eps B => zero_ib (bd k)` — it discarded every
    /// argument including `cb` and `B`, so the successor branch of any
    /// inductive proof reduced to the same constant as the base case and
    /// closed by `Eq.refl`, never referencing the induction hypothesis.
    /// That is the canonical Rule M3 masquerade ("IH-ignoring inductive
    /// step"; see `designs/2026-04-19-demasquerade-cxxx-pattern.md`).
    ///
    /// This replacement's body genuinely uses the induction hypothesis
    /// in its step case — applying `cb m ih` rather than ignoring `ih`:
    ///
    /// ```text
    /// compose_faithful d k cb B
    ///   := @Nat.rec.{1} (fun _ : Nat => IntervalBounds d)
    ///                   B                           -- base case: B
    ///                   (fun m ih => cb m ih)       -- step: APPLY cb to IH
    ///                   k
    /// ```
    ///
    /// Semantics:
    ///
    /// 1. At `k = Nat.zero`: iota-reduces to `B` (the input bound).
    /// 2. At `k = Nat.succ m`: iota-reduces to
    ///    `cb m (compose_faithful d m cb B)`. This is a real unfolding
    ///    — `cb` is applied to the IH (`compose_faithful d m cb B`), so
    ///    different `cb` inputs yield different outputs.
    ///    Cross-check against `monolithic_crown_faithful`: at
    ///    `k = succ 0`, `compose_faithful d 1 cb B = cb 0 B`, while
    ///    `monolithic_crown_faithful d 1 B = zero_ib d`. Two syntactically
    ///    distinct normal forms — the two carriers are not alias-equivalent.
    ///
    /// Discriminator properties (per design, Template → Discriminator):
    ///
    /// * **Depends on `cb`.** Two distinct block-step functions
    ///   `cb1 ≠ cb2` produce distinct outputs at `k = succ 0`.
    /// * **Depends on `B`.** At `k = 0` returns `B`; two distinct inputs
    ///   yield distinct outputs.
    /// * **Depends on `k`.** At `k = 0` returns `B`; at `k = succ _`
    ///   returns `cb _ _` — structurally distinct.
    /// * **Uses its IH.** The step case's body references the IH
    ///   variable, so the proof term at the step does not
    ///   lambda-bind-and-ignore (Rule M3 inverted).
    /// * **Structurally distinct from `monolithic_crown_faithful`.**
    ///   Their step cases have different bodies (`cb m ih` vs
    ///   `zero_ib d`), so
    ///   `whnf(compose_faithful d 1 cb B)` ≠
    ///   `whnf(monolithic_crown_faithful d 1 B)` whenever `cb` is not
    ///   itself `fun _ _ => zero_ib d`.
    ///
    /// Registered as `Declaration::Definition { is_reducible: true }`
    /// so the kernel can iota-reduce applications during proof checking.
    ///
    /// # Contract
    ///
    /// REQUIRES: `Nat.rec` registered (foundational); `IntervalBounds`
    /// registered (call `init_nn_verify_types()` first; guaranteed by
    /// `init_nn_verify_blockwise_crown_ext`).
    /// ENSURES: Idempotent (returns `Ok(())` if already registered).
    /// ENSURES: `self.get_const(&Name::from_string(
    /// "NNVerify.Block.compose_faithful")).is_some()`.
    ///
    /// Part of #3491 Phase 2 — faithful `Block.compose` carrier,
    /// structurally distinct from `monolithic_crown_faithful` via its
    /// step case actually consuming the induction hypothesis.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_compose_faithful(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Block.compose_faithful");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = BlockwiseCrownConsts::new();
        // Type: (d : Nat) -> (k : Nat) ->
        //         (cb : Nat -> IntervalBounds d -> IntervalBounds d) ->
        //         IntervalBounds d -> IntervalBounds d
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let (k_id, _k) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(d.clone());
            // cb : Nat -> IntervalBounds d -> IntervalBounds d
            let cb_ty = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (m_id, _m) = ch.fresh_local(c.nat.clone());
                let (ib_id, _ib_v) = ch.fresh_local(ib_d.clone());
                let r = ch.mk_pi(ib_id, BinderInfo::Default, ib_d.clone(), ib_d.clone());
                let r = ch.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), r);
                ch.finish_child(r)
            };
            let (cb_id, _cb) = b.fresh_local(cb_ty.clone());
            let (b_id, _bnd) = b.fresh_local(ib_d.clone());
            let r = b.mk_pi(b_id, BinderInfo::Default, ib_d.clone(), ib_d);
            let r = b.mk_pi(cb_id, BinderInfo::Default, cb_ty, r);
            let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        // Value:
        //   fun (d k : Nat) (cb : Nat -> IB d -> IB d) (B : IB d) =>
        //     @Nat.rec.{1}
        //       (fun _ : Nat => IB d)                   -- motive
        //       B                                       -- base
        //       (fun (m : Nat) (ih : IB d) => cb m ih)  -- step USES ih
        //       k
        let nat_rec_ib = Expr::const_(
            Name::from_string("Nat.rec"),
            vec![Level::succ(Level::zero())],
        );
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(d.clone());
            let cb_ty = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (m_id, _m) = ch.fresh_local(c.nat.clone());
                let (ib_id, _ib_v) = ch.fresh_local(ib_d.clone());
                let r = ch.mk_pi(ib_id, BinderInfo::Default, ib_d.clone(), ib_d.clone());
                let r = ch.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), r);
                ch.finish_child(r)
            };
            let (cb_id, cb) = b.fresh_local(cb_ty.clone());
            let (b_id, b_var) = b.fresh_local(ib_d.clone());

            // Motive: fun (_ : Nat) => IB d
            let motive = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (m_id, _m) = ch.fresh_local(c.nat.clone());
                let r = ch.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), ib_d.clone());
                ch.finish_child(r)
            };

            // Step: fun (m : Nat) (ih : IB d) => cb m ih
            //       — the body REFERENCES ih, satisfying Rule M3 inversion.
            let succ_case = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (m_id, m) = ch.fresh_local(c.nat.clone());
                let (ih_id, ih) = ch.fresh_local(ib_d.clone());
                let apply = Expr::app(Expr::app(cb.clone(), m), ih);
                let r = ch.mk_lam(ih_id, BinderInfo::Default, ib_d.clone(), apply);
                let r = ch.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), r);
                ch.finish_child(r)
            };

            // @Nat.rec.{1} motive B succ_case k
            let rec_app = Expr::apps(nat_rec_ib, [motive, b_var, succ_case, k]);

            let r = b.mk_lam(b_id, BinderInfo::Default, ib_d.clone(), rec_app);
            let r = b.mk_lam(cb_id, BinderInfo::Default, cb_ty, r);
            let r = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// Register `NNVerify.Block.compose_faithful_zero_eq_input` — a
    /// constructive theorem over the faithful `Block.compose_faithful`
    /// carrier, pinned at `k = 0`.
    ///
    /// ```text
    /// forall (d : Nat) (cb : Nat -> IntervalBounds d -> IntervalBounds d)
    ///        (B : IntervalBounds d),
    ///   compose_faithful d Nat.zero cb B = B
    /// ```
    ///
    /// Pairs with `register_compose_faithful` the same way
    /// `blockwise_crown_equiv_faithful` pairs with
    /// `register_monolithic_crown_faithful`: a companion theorem that
    /// locks in the discriminator at the `Nat.zero` branch. At `k = 0`
    /// the body iota-reduces to `B`, so `@Eq.refl (IB d) B` closes the
    /// goal — the `Eq.refl` is on the **bound variable `B`**, NOT a
    /// collapsed constant. Replacing `compose_faithful` with the old
    /// `fun d k cb B => zero_ib d` carrier would break this proof
    /// because the LHS would reduce to `zero_ib d` and `Eq.refl B` would
    /// not type-check at `IB d = IB d` unless `B = zero_ib d`.
    ///
    /// Part of #3491 — pair a faithful-carrier theorem with
    /// `compose_faithful` so the demasquerade Phase 2 is demonstrably
    /// invertible. A step-case theorem that uses `cb m ih` becomes
    /// available once `crown_block` acquires semantic content (Phase 3).
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_compose_faithful_zero_eq_input(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Block.compose_faithful_zero_eq_input");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = BlockwiseCrownConsts::new();
        let cf = Expr::const_(Name::from_string("NNVerify.Block.compose_faithful"), vec![]);
        let nat_zero = c.nat_zero.clone();
        let eq_refl = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        );

        // Type: forall (d : Nat) (cb : Nat -> IB d -> IB d) (B : IB d),
        //   @Eq (IB d) (compose_faithful d Nat.zero cb B) B
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(d.clone());
            let cb_ty = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (m_id, _m) = ch.fresh_local(c.nat.clone());
                let (ib_id, _ib_v) = ch.fresh_local(ib_d.clone());
                let r = ch.mk_pi(ib_id, BinderInfo::Default, ib_d.clone(), ib_d.clone());
                let r = ch.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), r);
                ch.finish_child(r)
            };
            let (cb_id, cb) = b.fresh_local(cb_ty.clone());
            let (b_id, b_var) = b.fresh_local(ib_d.clone());
            let lhs = Expr::apps(cf.clone(), [d.clone(), nat_zero.clone(), cb, b_var.clone()]);
            let concl = c.ib_eq(&d, lhs, b_var);
            let r = b.mk_pi(b_id, BinderInfo::Default, ib_d, concl);
            let r = b.mk_pi(cb_id, BinderInfo::Default, cb_ty, r);
            let r = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        // Proof: fun (d : Nat) (cb : ...) (B : IB d) => @Eq.refl.{1} (IB d) B
        // Kernel reduces LHS to `B` via one iota step on Nat.rec @ Nat.zero.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(d.clone());
            let cb_ty = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (m_id, _m) = ch.fresh_local(c.nat.clone());
                let (ib_id, _ib_v) = ch.fresh_local(ib_d.clone());
                let r = ch.mk_pi(ib_id, BinderInfo::Default, ib_d.clone(), ib_d.clone());
                let r = ch.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), r);
                ch.finish_child(r)
            };
            let (cb_id, _cb) = b.fresh_local(cb_ty.clone());
            let (b_id, b_var) = b.fresh_local(ib_d.clone());
            let body = Expr::app(Expr::app(eq_refl, ib_d.clone()), b_var);
            let r = b.mk_lam(b_id, BinderInfo::Default, ib_d, body);
            let r = b.mk_lam(cb_id, BinderInfo::Default, cb_ty, r);
            let r = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        // Base-case iota-unfold on faithful carrier. See triage report
        // reports/triage/2026-04-20-3646-masquerade-grandfathered-triage.md
        // Site 2. Tracking: #3646, #3597, #3491.
        // MASQUERADE-ALLOW: faithful carrier, BVar refl (#3646 Site 2).
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Register `NNVerify.Block.compose_faithful_succ_unfold` — the
    /// generic successor-unfold lemma for `compose_faithful`.
    ///
    /// ```text
    /// forall (d m : Nat)
    ///        (cb : Nat -> IntervalBounds d -> IntervalBounds d)
    ///        (B : IntervalBounds d),
    ///   compose_faithful d (Nat.succ m) cb B
    ///     = cb m (compose_faithful d m cb B)
    /// ```
    ///
    /// ## Why this holds by one iota step
    ///
    /// `compose_faithful` is registered as a reducible
    /// `Declaration::Definition` whose body is
    /// `@Nat.rec.{1} (fun _ => IB d) B (fun m ih => cb m ih) k`. At
    /// `k = Nat.succ m` the kernel's iota rule for `Nat.rec` reduces the
    /// expression to the step-case body applied to `m` and the
    /// recursive call `@Nat.rec.{1} ... m` — i.e. to
    /// `cb m (compose_faithful d m cb B)`. The step case's body
    /// structurally USES its `ih` argument (Rule M3 inverted); the
    /// reduction is therefore not a trivial alias-collapse, but a real
    /// one-step unfold of the recursion equation. `@Eq.refl (IB d)
    /// (cb m (compose_faithful d m cb B))` type-checks against both
    /// sides because WHNF normalises them to the same term.
    ///
    /// ## Discriminator properties (Phase-3 upgrade, #3533)
    ///
    /// Strictly stronger than `compose_faithful_zero_eq_input`: together,
    /// the zero-case and successor-unfold lemmas specify `compose_faithful`
    /// by its `Nat.rec` equations. The `Eq.refl` witness is the
    /// **constructed term** `cb m (compose_faithful d m cb B)`, NOT a
    /// bound variable — so the proof is not the k=0 BVar-refl pattern
    /// and genuinely depends on the step-case body.
    ///
    /// ## Axiom profile
    ///
    /// Proof term references only `Eq.refl` (foundational), `Nat.succ`,
    /// `Nat` (inductive types, not axioms), and `compose_faithful`
    /// (reducible definition). The transitive axiom closure is a subset
    /// of `FOUNDATIONAL_AXIOMS` — see
    /// `tests_nn_verify_blockwise_crown_faithful.rs` for the assertion.
    ///
    /// # Contract
    ///
    /// REQUIRES: `compose_faithful` registered (call
    /// `register_compose_faithful` first; guaranteed by the parent
    /// `init_nn_verify_blockwise_crown_ext`).
    /// ENSURES: Idempotent (returns `Ok(())` if already registered).
    /// ENSURES: Registered as `Declaration::Theorem` — NOT an axiom
    /// wrapper.
    ///
    /// Part of #3533 — Phase 3 promotion of the `_faithful` scaffolding
    /// from the degenerate `k = 0` base case to a generic successor
    /// unfold. Does NOT close #3491/#3492/#3493/#3494 (those require real
    /// per-block CROWN content in `monolithic_crown_faithful`'s step
    /// case) or #3488 (real LayerNorm arithmetic).
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_compose_faithful_succ_unfold(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Block.compose_faithful_succ_unfold");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = BlockwiseCrownConsts::new();
        let cf = Expr::const_(Name::from_string("NNVerify.Block.compose_faithful"), vec![]);
        let nat_succ = c.nat_succ.clone();
        let eq_refl = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        );

        // Type: forall (d m : Nat) (cb : Nat -> IB d -> IB d) (B : IB d),
        //   @Eq (IB d)
        //       (compose_faithful d (Nat.succ m) cb B)
        //       (cb m (compose_faithful d m cb B))
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(d.clone());
            let cb_ty = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (m2_id, _m2) = ch.fresh_local(c.nat.clone());
                let (ib_id, _ib_v) = ch.fresh_local(ib_d.clone());
                let r = ch.mk_pi(ib_id, BinderInfo::Default, ib_d.clone(), ib_d.clone());
                let r = ch.mk_pi(m2_id, BinderInfo::Default, c.nat.clone(), r);
                ch.finish_child(r)
            };
            let (cb_id, cb) = b.fresh_local(cb_ty.clone());
            let (b_id, b_var) = b.fresh_local(ib_d.clone());

            // succ m
            let succ_m = Expr::app(nat_succ.clone(), m.clone());
            // LHS: compose_faithful d (succ m) cb B
            let lhs = Expr::apps(cf.clone(), [d.clone(), succ_m, cb.clone(), b_var.clone()]);
            // recursive call: compose_faithful d m cb B
            let rec_call = Expr::apps(
                cf.clone(),
                [d.clone(), m.clone(), cb.clone(), b_var.clone()],
            );
            // RHS: cb m (compose_faithful d m cb B)
            let rhs = Expr::app(Expr::app(cb, m), rec_call);
            let concl = c.ib_eq(&d, lhs, rhs);

            let r = b.mk_pi(b_id, BinderInfo::Default, ib_d, concl);
            let r = b.mk_pi(cb_id, BinderInfo::Default, cb_ty, r);
            let r = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        // Proof: fun (d m : Nat) (cb : ...) (B : IB d) =>
        //   @Eq.refl.{1} (IB d) (cb m (compose_faithful d m cb B))
        //
        // Kernel reduces LHS `compose_faithful d (Nat.succ m) cb B` to
        // `cb m (compose_faithful d m cb B)` via one iota step on Nat.rec
        // at the succ branch, making the refl typecheck.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(d.clone());
            let cb_ty = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (m2_id, _m2) = ch.fresh_local(c.nat.clone());
                let (ib_id, _ib_v) = ch.fresh_local(ib_d.clone());
                let r = ch.mk_pi(ib_id, BinderInfo::Default, ib_d.clone(), ib_d.clone());
                let r = ch.mk_pi(m2_id, BinderInfo::Default, c.nat.clone(), r);
                ch.finish_child(r)
            };
            let (cb_id, cb) = b.fresh_local(cb_ty.clone());
            let (b_id, b_var) = b.fresh_local(ib_d.clone());

            // compose_faithful d m cb B
            let rec_call = Expr::apps(
                cf.clone(),
                [d.clone(), m.clone(), cb.clone(), b_var.clone()],
            );
            // cb m (compose_faithful d m cb B) — the witness term
            let witness = Expr::app(Expr::app(cb, m), rec_call);
            // @Eq.refl.{1} (IB d) witness
            let body = Expr::app(Expr::app(eq_refl, ib_d.clone()), witness);

            let r = b.mk_lam(b_id, BinderInfo::Default, ib_d, body);
            let r = b.mk_lam(cb_id, BinderInfo::Default, cb_ty, r);
            let r = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        // Succ-case iota-unfold on faithful carrier: `Eq.refl` witness
        // is the constructed term `cb m (compose_faithful d m cb B)` —
        // structurally depends on the step-case body (Rule M3 inverted).
        // See reports/triage/2026-04-20-3646-masquerade-grandfathered-triage.md
        // Site 3. Tracking: #3646, #3597, #3533.
        // MASQUERADE-ALLOW: faithful carrier, constructed witness (#3646 Site 3).
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}
