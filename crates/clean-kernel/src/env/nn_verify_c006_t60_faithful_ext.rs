// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! # C006 T60 faithful extension — M1 + M2 of #3494 design
//!
//! Sibling module to `nn_verify_blockwise_crown_ext.rs` (kept under the
//! 500-line file-size limit by splitting per-milestone content into
//! separate files). Implements milestones M1 and M2 from
//! `designs/2026-04-19-blockwise-crown-ih-step-design.md`.
//!
//! ## Why a NEW carrier, not a mutation of `monolithic_crown_faithful`
//!
//! The Phase-2 carrier `Block.monolithic_crown_faithful`
//! (`nn_verify_blockwise_crown_ext_carriers.rs:186`) was deliberately
//! registered with an **IH-ignoring** step case
//! (`fun _m _ih => zero_ib d`) to serve as the discriminator counter-
//! example for Rule M3 in
//! `designs/2026-04-19-demasquerade-cxxx-pattern.md`. The existing test
//! `test_compose_faithful_structurally_distinct_from_monolithic` at
//! `tests_nn_verify_blockwise_crown_faithful.rs:550` locks that shape in:
//! it requires `monolithic_crown_faithful d 1 sym_B  →*  zero_ib 1`
//! (distinct WHNF from `compose_faithful d 1 (identity cb) sym_B → sym_B`).
//! Rewriting `monolithic_crown_faithful`'s step body would regress that
//! discriminator.
//!
//! So we register a NEW sibling carrier
//! `NNVerify.Block.monolithic_crown_ihstep` whose step case actually
//! consumes its induction hypothesis via `monolithic_step d m ih`. The
//! Phase-2 carrier remains as a structural discriminator; the Phase-3
//! (#3494) promotion operates on the new carrier.
//!
//! ## What lives here
//!
//! - **M1: `NNVerify.Block.monolithic_step`** — faithful monolithic step
//!   body `(d : Nat) -> Nat -> IB d -> IB d` with body
//!   `fun d _m ih => ih`. Reducible Definition. Placeholder identity per
//!   the design (real CROWN semantics belong to M5 per the remediation
//!   plan). The key property is that the body structurally references
//!   its `ih` argument, so any `Nat.rec` step `fun m ih => monolithic_step
//!   d m ih` is genuinely IH-using (Rule M3 inverted).
//!
//! - **M1: `NNVerify.Block.monolithic_crown_ihstep`** — the IH-consuming
//!   companion to `monolithic_crown_faithful`. Body:
//!   ```text
//!   fun d k B =>
//!     @Nat.rec.{1} (fun _ => IB d) B
//!                  (fun m ih => monolithic_step d m ih)
//!                  k
//!   ```
//!   Reducible Definition. At `k = Nat.zero` iota-reduces to `B`. At
//!   `k = Nat.succ m` iota-reduces to
//!   `monolithic_step d m (monolithic_crown_ihstep d m B)`.
//!
//! - **M2: `NNVerify.Block.monolithic_crown_ihstep_succ_unfold`** —
//!   theorem
//!   ```text
//!   forall (d m : Nat) (B : IntervalBounds d),
//!     monolithic_crown_ihstep d (Nat.succ m) B
//!       = monolithic_step d m (monolithic_crown_ihstep d m B)
//!   ```
//!   Proof term is
//!   `@Eq.refl.{1} (IB d)
//!       (monolithic_step d m (monolithic_crown_ihstep d m B))`.
//!   Kernel closes by one iota step on `Nat.rec` at the `Nat.succ`
//!   branch. Mirrors the `compose_faithful_succ_unfold` proof shape at
//!   `nn_verify_blockwise_crown_ext_compose.rs:381`.
//!
//! ## What this does NOT do (M3 scope — follow-up)
//!
//! - The hypothesised T60 equivalence theorem
//!   `T60_faithful_ext :
//!      forall d k cb B (H : forall m B', cb m B' = monolithic_step d m B'),
//!        compose_faithful d k cb B = monolithic_crown_ihstep d k B`
//!   is M3 and lands in a follow-up session. The proof reuses the
//!   `compose_faithful_ext` shape (`Nat.rec` + `Eq.trans` + `congrArg ih`
//!   + `H m _`). Before M3 lands, `T60_faithful_ext` would literally
//!   state a false equation between the two carriers — hence the
//!   hypothesis `H` constraining `cb` to match `monolithic_step` is
//!   mandatory.
//!
//! Part of #3494 — M1 + M2 transcription of the design doc skeleton
//! with different carrier constants than `compose_faithful_ext`.

use super::nn_verify_blockwise_crown::BlockwiseCrownConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register M1 + M2 declarations for the T60 faithful IH-using step.
    ///
    /// Wired in from `init_nn_verify_blockwise_crown_ext` after the
    /// Phase-2 faithful carriers land, so `Block.monolithic_step` and
    /// `Block.monolithic_crown_ihstep` coexist with the IH-ignoring
    /// `Block.monolithic_crown_faithful` discriminator.
    ///
    /// Idempotent — every `register_*` call short-circuits on the
    /// already-registered constant name.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn init_nn_verify_c006_t60_faithful_ext(&mut self) -> Result<(), EnvError> {
        self.register_block_monolithic_step()?;
        self.register_block_monolithic_crown_ihstep()?;
        self.register_block_monolithic_crown_ihstep_succ_unfold()?;
        Ok(())
    }

    /// Register `NNVerify.Block.monolithic_step : (d : Nat) -> Nat -> IB d -> IB d`
    /// with body `fun (d : Nat) (_m : Nat) (ih : IB d) => ih`.
    ///
    /// **M1 step-body placeholder.** Per the design doc
    /// (`designs/2026-04-19-blockwise-crown-ih-step-design.md` §3, M1),
    /// the minimum viable body is one that structurally references `ih`
    /// — the identity `fun d _m ih => ih` suffices. Real CROWN semantics
    /// (interval arithmetic, Jacobian density) belong to M5 and are
    /// blocked on the Batch-2 interval-arithmetic foundation.
    ///
    /// Discriminator property — the body references `ih` as a free
    /// variable, so any step `fun m ih => monolithic_step d m ih` in a
    /// `Nat.rec` call genuinely consumes its IH (Rule M3 inverted).
    ///
    /// Registered as `Declaration::Definition { is_reducible: true }` so
    /// the kernel's iota rule for `Nat.rec` can reduce applications
    /// through this carrier during proof checking.
    ///
    /// # Contract
    ///
    /// REQUIRES: `Nat` and `IntervalBounds` registered
    /// (`init_nn_verify_types` guarantees this; the caller is
    /// `init_nn_verify_blockwise_crown_ext`).
    /// ENSURES: Idempotent (returns `Ok(())` if already registered).
    /// ENSURES: `self.get_const(&Name::from_string(
    /// "NNVerify.Block.monolithic_step")).is_some()`.
    ///
    /// Part of #3494 M1 — faithful monolithic step body.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_block_monolithic_step(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Block.monolithic_step");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = BlockwiseCrownConsts::new();
        // Type: (d : Nat) -> Nat -> IB d -> IB d
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let (m_id, _m) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(d.clone());
            let (ih_id, _ih) = b.fresh_local(ib_d.clone());
            let r = b.mk_pi(ih_id, BinderInfo::Default, ib_d.clone(), ib_d);
            let r = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        // Value: fun (d : Nat) (_m : Nat) (ih : IB d) => ih
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let (m_id, _m) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(d.clone());
            let (ih_id, ih) = b.fresh_local(ib_d.clone());
            let r = b.mk_lam(ih_id, BinderInfo::Default, ib_d, ih);
            let r = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), r);
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

    /// Register `NNVerify.Block.monolithic_crown_ihstep :
    /// (d : Nat) -> Nat -> IB d -> IB d` with body
    ///
    /// ```text
    /// fun d k B =>
    ///   @Nat.rec.{1} (fun _ => IB d)
    ///                B
    ///                (fun (m : Nat) (ih : IB d) => monolithic_step d m ih)
    ///                k
    /// ```
    ///
    /// **M1 IH-using monolithic carrier.** Structurally matches
    /// `compose_faithful`'s shape at
    /// `nn_verify_blockwise_crown_ext_compose.rs:127` but with
    /// `monolithic_step d m ih` as the step-case body (rather than
    /// `cb m ih`). Reducible Definition so the kernel can iota-reduce
    /// during type-checking.
    ///
    /// Semantics:
    ///
    /// 1. At `k = Nat.zero`: iota-reduces to `B` (base case of Nat.rec).
    /// 2. At `k = Nat.succ m`: iota-reduces to the step case applied to
    ///    `m` and the recursive call, i.e.
    ///    `monolithic_step d m (monolithic_crown_ihstep d m B)`. Because
    ///    `monolithic_step` is the identity, this further reduces to
    ///    `monolithic_crown_ihstep d m B` — the carrier is a constant
    ///    function of `k` (modulo the identity step). Still, the
    ///    STRUCTURAL body references `ih`, so the step case is not a
    ///    Rule-M3 masquerade.
    ///
    /// Discriminator properties:
    ///
    /// * **Uses IH.** Step body is `fun m ih => monolithic_step d m ih`
    ///   — the step `ih` argument is passed into `monolithic_step`,
    ///   which in turn references it in its body (identity). Rule M3
    ///   inverted.
    /// * **Structurally distinct from `monolithic_crown_faithful`.** The
    ///   Phase-2 carrier's step returns `zero_ib d` regardless of `ih`;
    ///   this carrier's step returns `ih` itself. At `k = 1` with a
    ///   symbolic `B`, `monolithic_crown_ihstep d 1 B` WHNF-reduces to
    ///   `B`, while `monolithic_crown_faithful d 1 B` reduces to
    ///   `zero_ib d`. The two carriers are NOT alias-equivalent — they
    ///   cannot be substituted for each other.
    ///
    /// # Contract
    ///
    /// REQUIRES: `monolithic_step` registered (call
    /// `register_block_monolithic_step` first).
    /// ENSURES: Idempotent (returns `Ok(())` if already registered).
    /// ENSURES: `self.get_const(&Name::from_string(
    /// "NNVerify.Block.monolithic_crown_ihstep")).is_some()`.
    ///
    /// Part of #3494 M1 — IH-using monolithic carrier, sibling to
    /// `compose_faithful` with different step-case body.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_block_monolithic_crown_ihstep(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Block.monolithic_crown_ihstep");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = BlockwiseCrownConsts::new();
        let mono_step = Expr::const_(Name::from_string("NNVerify.Block.monolithic_step"), vec![]);
        // Type: (d : Nat) -> Nat -> IB d -> IB d
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let (k_id, _k) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(d.clone());
            let (b_id, _bnd) = b.fresh_local(ib_d.clone());
            let r = b.mk_pi(b_id, BinderInfo::Default, ib_d.clone(), ib_d);
            let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        // Value:
        //   fun (d : Nat) (k : Nat) (B : IB d) =>
        //     @Nat.rec.{1}
        //       (fun _ : Nat => IB d)                          -- motive
        //       B                                              -- base
        //       (fun (m : Nat) (ih : IB d) =>
        //          monolithic_step d m ih)                     -- step USES ih
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
            let (b_id, b_var) = b.fresh_local(ib_d.clone());

            // Motive: fun (_ : Nat) => IB d
            let motive = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (m_id, _m) = ch.fresh_local(c.nat.clone());
                let r = ch.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), ib_d.clone());
                ch.finish_child(r)
            };

            // Step case: fun (m : Nat) (ih : IB d) => monolithic_step d m ih
            // — Rule M3 inverted: ih appears free in the body.
            let succ_case = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (m_id, m) = ch.fresh_local(c.nat.clone());
                let (ih_id, ih) = ch.fresh_local(ib_d.clone());
                let apply = Expr::apps(mono_step.clone(), [d.clone(), m, ih]);
                let r = ch.mk_lam(ih_id, BinderInfo::Default, ib_d.clone(), apply);
                let r = ch.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), r);
                ch.finish_child(r)
            };

            // @Nat.rec.{1} motive B succ_case k
            let rec_app = Expr::apps(nat_rec_ib, [motive, b_var, succ_case, k]);

            let r = b.mk_lam(b_id, BinderInfo::Default, ib_d, rec_app);
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

    /// Register `NNVerify.Block.monolithic_crown_ihstep_succ_unfold` —
    /// the M2 successor-unfold lemma for `monolithic_crown_ihstep`.
    ///
    /// ```text
    /// forall (d m : Nat) (B : IntervalBounds d),
    ///   monolithic_crown_ihstep d (Nat.succ m) B
    ///     = monolithic_step d m (monolithic_crown_ihstep d m B)
    /// ```
    ///
    /// Mirrors the `compose_faithful_succ_unfold` proof shape at
    /// `nn_verify_blockwise_crown_ext_compose.rs:381` — the Eq.refl
    /// witness is the CONSTRUCTED RHS term, not a bound variable. The
    /// kernel reduces the LHS via one iota step on `Nat.rec` at the
    /// `Nat.succ` branch: the recursor expands the step case
    /// `fun m' ih' => monolithic_step d m' ih'` at `m' := m` and
    /// `ih' := @Nat.rec.{1} ... m`, producing the term
    /// `monolithic_step d m (monolithic_crown_ihstep d m B)` after
    /// delta-unfolding the inner `Nat.rec` back through the reducible
    /// definition. Both sides normalise to the same kernel term, so
    /// `Eq.refl` on the RHS type-checks.
    ///
    /// ## Axiom profile
    ///
    /// Proof term references only `Eq.refl` (foundational), `Nat.succ`,
    /// `Nat` (inductive types), `monolithic_step`, and
    /// `monolithic_crown_ihstep` (reducible definitions). The transitive
    /// axiom closure is a subset of `FOUNDATIONAL_AXIOMS` — no domain
    /// axioms introduced.
    ///
    /// # Contract
    ///
    /// REQUIRES: `monolithic_step` and `monolithic_crown_ihstep`
    /// registered.
    /// ENSURES: Idempotent (returns `Ok(())` if already registered).
    /// ENSURES: Registered as `Declaration::Theorem` — NOT an axiom
    /// wrapper.
    ///
    /// Part of #3494 M2 — monolithic-side successor-unfold lemma,
    /// companion to `compose_faithful_succ_unfold` and a prerequisite
    /// for M3 (`T60_faithful_ext`, follow-up session).
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_block_monolithic_crown_ihstep_succ_unfold(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Block.monolithic_crown_ihstep_succ_unfold");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = BlockwiseCrownConsts::new();
        let mcih = Expr::const_(
            Name::from_string("NNVerify.Block.monolithic_crown_ihstep"),
            vec![],
        );
        let mono_step = Expr::const_(Name::from_string("NNVerify.Block.monolithic_step"), vec![]);
        let nat_succ = c.nat_succ.clone();
        let eq_refl = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        );

        // Type: forall (d m : Nat) (B : IB d),
        //   @Eq (IB d)
        //       (monolithic_crown_ihstep d (Nat.succ m) B)
        //       (monolithic_step d m (monolithic_crown_ihstep d m B))
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(d.clone());
            let (b_id, b_var) = b.fresh_local(ib_d.clone());

            // succ m
            let succ_m = Expr::app(nat_succ.clone(), m.clone());
            // LHS: monolithic_crown_ihstep d (succ m) B
            let lhs = Expr::apps(mcih.clone(), [d.clone(), succ_m, b_var.clone()]);
            // recursive call: monolithic_crown_ihstep d m B
            let rec_call = Expr::apps(mcih.clone(), [d.clone(), m.clone(), b_var.clone()]);
            // RHS: monolithic_step d m (monolithic_crown_ihstep d m B)
            let rhs = Expr::apps(mono_step.clone(), [d.clone(), m.clone(), rec_call]);
            let concl = c.ib_eq(&d, lhs, rhs);

            let r = b.mk_pi(b_id, BinderInfo::Default, ib_d, concl);
            let r = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        // Proof: fun (d m : Nat) (B : IB d) =>
        //   @Eq.refl.{1} (IB d)
        //     (monolithic_step d m (monolithic_crown_ihstep d m B))
        //
        // Kernel reduces LHS `monolithic_crown_ihstep d (Nat.succ m) B` to
        // the RHS via one iota step on Nat.rec at the succ branch.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(d.clone());
            let (b_id, b_var) = b.fresh_local(ib_d.clone());

            // monolithic_crown_ihstep d m B
            let rec_call = Expr::apps(mcih.clone(), [d.clone(), m.clone(), b_var.clone()]);
            // monolithic_step d m (monolithic_crown_ihstep d m B) — the witness
            let witness = Expr::apps(mono_step.clone(), [d.clone(), m.clone(), rec_call]);
            // @Eq.refl.{1} (IB d) witness
            let body = Expr::app(Expr::app(eq_refl, ib_d.clone()), witness);

            let r = b.mk_lam(b_id, BinderInfo::Default, ib_d, body);
            let r = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        // MASQUERADE-ALLOW: genuine Nat.rec succ-unfold on the new
        // `monolithic_crown_ihstep` carrier; the gate is matching the
        // `monolithic_crown` substring, not an alias-collapse over the
        // deprecated `NNVerify.Block.monolithic_crown` surface.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}
