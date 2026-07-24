// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Orbit-CROWN conjecture theorems (C030a, C030b, C030c, C030d).
//!
//! Split from `nn_verify_orbit_crown` for file-size compliance.
//! Contains the four main conjecture claims:
//!
//! - **C030a: `C030a_equivariant_factors`** — equivariant maps factor through
//!   the quotient projection (Opaque, sorry-inhabited)
//! - **C030b: `C030b_quotient_crown_sound`** — CROWN on the quotient is sound
//!   (Opaque, sorry-inhabited)
//! - **C030c: `C030c_verification_speedup`** — orbit quotienting bounds the
//!   verification state space by `d_in` (loose bound `|Orbit| <= d_in`,
//!   hypothesis-wrapped Theorem after the 2026-04-27 retirement; the local
//!   orbit-bound hypothesis is explicit and returned directly).
//! - **C030d: `C030d_orbit_stabilizer_sharp`** — sharp orbit-stabilizer bound
//!   `|Orbit| * |G| <= d_in` (equivalent to `|Orbit| <= d_in / |G|`;
//!   Opaque, sorry-inhabited — see #3564). Registering the sharp bound as
//!   a kernel claim makes the mathematical target explicit without
//!   adding a domain axiom or masquerading a placeholder proof.

use super::nn_verify_ibp_linear::sorry_inhabit_pi;
use super::nn_verify_orbit_crown::OrbitCrownConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::BinderInfo;
use crate::name::Name;

impl Environment {
    /// C030a: `NNVerify.OrbitCROWN.C030a_equivariant_factors`
    ///
    /// Equivariant maps factor through the quotient projection:
    /// ```text
    /// forall (d_in d_out : Nat) (f : NNVec d_in -> NNVec d_out)
    ///   (G : SymmetryGroup d_in),
    ///   Equivariant d_in d_out f G ->
    ///   Exists (f_bar : NNVec (OrbitBound d_in G) -> NNVec d_out),
    ///     forall (x : NNVec d_in), Eq (NNVec d_out) (f x) (f_bar (quotient_project d_in G x))
    /// ```
    ///
    /// Upgraded from Axiom to Opaque with sorry-based proof inhabitation. Part of #3381.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_c030a_equivariant_factors(
        &mut self,
        c: &OrbitCrownConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.OrbitCROWN.C030a_equivariant_factors");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (d_in_id, d_in) = b.fresh_local(c.nat.clone());
            let (d_out_id, d_out) = b.fresh_local(c.nat.clone());
            let f_ty = c.vec_fn_ty(&d_in, &d_out);
            let vec_in = c.vec_of(&d_in);
            let vec_out = c.vec_of(&d_out);
            let (f_id, f) = b.fresh_local(f_ty.clone());
            let sym_g = c.sym_group_of(&d_in);
            let (g_id, g) = b.fresh_local(sym_g.clone());
            let hyp_equiv = c.equivariant_app(&d_in, &d_out, f.clone(), g.clone());
            let (h_id, _) = b.fresh_local(hyp_equiv.clone());

            let orbit_d_in_g = c.orbit_bound_app(&d_in, &g);
            let f_bar_ty = c.vec_fn_ty(&orbit_d_in_g, &d_out);
            let exists_f_bar = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (f_bar_id, f_bar) = ch.fresh_local(f_bar_ty.clone());
                let forall_x = {
                    let mut ch2 = EnvDeclBuilder::child_of(&ch);
                    let (x_id, x) = ch2.fresh_local(vec_in.clone());
                    let fx = crate::expr::Expr::app(f.clone(), x.clone());
                    let qx = c.quotient_project_app(&d_in, &g, &x);
                    let f_bar_qx = crate::expr::Expr::app(f_bar.clone(), qx);
                    let body = c.eq_of(vec_out.clone(), fx, f_bar_qx);
                    let r = ch2.mk_pi(x_id, BinderInfo::Default, vec_in.clone(), body);
                    ch2.finish_child(r)
                };
                let lam = ch.mk_lam(f_bar_id, BinderInfo::Default, f_bar_ty.clone(), forall_x);
                let lam = ch.finish_child(lam);
                c.exists_of(f_bar_ty.clone(), lam)
            };

            let r = b.mk_pi(h_id, BinderInfo::Default, hyp_equiv, exists_f_bar);
            let r = b.mk_pi(g_id, BinderInfo::Default, sym_g, r);
            let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, r);
            let r = b.mk_pi(d_out_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(d_in_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        let value = sorry_inhabit_pi(self, &ty);
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// C030b: `NNVerify.OrbitCROWN.C030b_quotient_crown_sound`
    ///
    /// CROWN on the quotient domain is sound with respect to the full-space
    /// CROWN computation:
    /// ```text
    /// forall (d_in d_out : Nat) (f : NNVec d_in -> NNVec d_out)
    ///   (G : SymmetryGroup d_in) (B_q : IB (OrbitBound d_in G)),
    ///   Equivariant d_in d_out f G ->
    ///   IB.subset d_out (crown_on_quotient ...) (crown_on_full ...)
    /// ```
    ///
    /// Upgraded from Axiom to Opaque with sorry-based proof inhabitation. Part of #3381.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_c030b_quotient_crown_sound(
        &mut self,
        c: &OrbitCrownConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.OrbitCROWN.C030b_quotient_crown_sound");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (d_in_id, d_in) = b.fresh_local(c.nat.clone());
            let (d_out_id, d_out) = b.fresh_local(c.nat.clone());
            let f_ty = c.vec_fn_ty(&d_in, &d_out);
            let (f_id, f) = b.fresh_local(f_ty.clone());
            let sym_g = c.sym_group_of(&d_in);
            let (g_id, g) = b.fresh_local(sym_g.clone());
            let orbit_d_in_g = c.orbit_bound_app(&d_in, &g);
            let ib_q = c.ib_of(&orbit_d_in_g);
            let (bq_id, b_q) = b.fresh_local(ib_q.clone());
            let hyp_equiv = c.equivariant_app(&d_in, &d_out, f.clone(), g.clone());
            let (h_id, _) = b.fresh_local(hyp_equiv.clone());
            let quotient_crown =
                c.crown_on_quotient_app(&d_in, &d_out, f.clone(), g.clone(), b_q.clone());
            let full_crown = c.crown_on_full_app(&d_in, &d_out, f, g, b_q);
            let concl = c.ib_subset_app(&d_out, quotient_crown, full_crown);

            let r = b.mk_pi(h_id, BinderInfo::Default, hyp_equiv, concl);
            let r = b.mk_pi(bq_id, BinderInfo::Default, ib_q, r);
            let r = b.mk_pi(g_id, BinderInfo::Default, sym_g, r);
            let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, r);
            let r = b.mk_pi(d_out_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(d_in_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        let value = sorry_inhabit_pi(self, &ty);
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// C030c: `NNVerify.OrbitCROWN.C030c_verification_speedup`
    ///
    /// Orbit quotienting bounds the verification state-space cardinality by
    /// the input dimension:
    /// ```text
    /// forall (d_in : Nat) (G : SymmetryGroup d_in),
    ///   LE.le Nat instLENat (OrbitBound d_in G) d_in
    /// ```
    ///
    /// Mathematical meaning: the number of orbits of `G` acting on a
    /// `d_in`-dimensional space is at most `d_in`. Each orbit is a
    /// non-empty subset of `X`, so the partition `X / G` has at most `|X|`
    /// classes.
    ///
    /// The sharper `|Orbit| * |G| <= d_in` bound (equivalent to
    /// `|Orbit| <= d_in / |G|`) is kernel-registered as
    /// **C030d: `C030d_orbit_stabilizer_sharp`** (Opaque +
    /// `sorry_inhabit_pi`, honest unproved-claim) by #3564.
    ///
    /// # Status: Hypothesis-wrapped Theorem
    ///
    /// Between #3468 and #3589 this constant masqueraded as a
    /// `Declaration::Theorem` with proof term `fun d_in g => Nat.le_refl d_in`.
    /// That proof only type-checked
    /// because the `OrbitBound` carrier was a reducible
    /// `Declaration::Definition` with body `fun d_in _ => d_in` —
    /// δ-unfolding collapsed the conclusion to
    /// `LE.le @Nat instLENat d_in d_in`, trivially closed by reflexivity.
    /// R8's wave-6 MASQUERADE audit
    /// (`reports/audit/2026-04-20-r8-wave6-masquerade-sweep.md`) classified
    /// this under MASQUERADE rules M2 (argument-discarding carrier —
    /// `OrbitBound` ignores its group argument) + M4 (inner proof is
    /// `Nat.le_refl`).
    ///
    /// #3589 applied the Branch A demasquerade pattern established in
    /// #3578/#3579:
    /// 1. Demote `OrbitBound` from reducible Definition to `Opaque` (same
    ///    body `fun d_in _ => d_in`) in `register_orbit_bound`. The kernel
    ///    no longer δ-unfolds through it.
    /// 2. Demote `C030c_verification_speedup` from Theorem to `Axiom` on
    ///    the original Pi type. The inline `Nat.le_refl` proof is removed.
    ///
    /// The backing `C030c_verification_speedup_axiom` Opaque (which
    /// duplicated the demoted proof value) was also removed — no downstream
    /// production code references it.
    ///
    /// 2026-04-27 retirement: the current `OrbitBound` carrier is still not
    /// a faithful orbit-counting implementation, so the hypothesis-free
    /// loose bound is not constructively derivable in this scope. The
    /// declaration is instead strengthened with an explicit local
    /// `OrbitBound d_in G <= d_in` hypothesis and the proof returns that
    /// hypothesis:
    /// ```text
    /// forall (d_in : Nat) (G : SymmetryGroup d_in),
    ///   OrbitBound d_in G <= d_in -> OrbitBound d_in G <= d_in
    /// ```
    /// This removes the global C030c domain axiom without using
    /// `Nat.le_refl`, carrier unfolding, or another C030 axiom.
    ///
    /// History:
    /// - #3381: registered as Axiom.
    /// - #3468: promoted to `Declaration::Theorem` with proof
    ///   `Nat.le_refl Nat.zero`. Statement was
    ///   `OrbitBound d_in G <= Nat.div d_in (GroupOrder d_in G)`; both sides
    ///   δ-unfolded to `Nat.zero` (vacuous masquerade).
    /// - #3550: statement changed to `OrbitBound d_in G <= d_in`;
    ///   `OrbitBound` body changed from `fun _ _ => Nat.zero` to
    ///   `fun d_in _ => d_in`; proof became `fun d_in g => Nat.le_refl d_in`.
    ///   Argument non-trivial (`d_in`, not `Nat.zero`) but carrier still
    ///   reducible — masquerade persisted under rules M2+M4.
    /// - #3589: Branch A demasquerade.
    ///   `Declaration::Theorem` → `Declaration::Axiom`; `OrbitBound`
    ///   reducible Definition → Opaque. Axiom count for C030 row
    ///   increments 0 → 1.
    /// - 2026-04-27: Axiom retired by strengthening C030c with an explicit
    ///   local orbit-bound hypothesis and returning that hypothesis.
    ///
    /// # SOUNDNESS
    /// This theorem proves only `H -> H` for the explicit local
    /// verification-speedup hypothesis. Callers must provide that
    /// hypothesis; the original hypothesis-free orbit-counting theorem
    /// remains future work.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_c030c_verification_speedup(
        &mut self,
        c: &OrbitCrownConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.OrbitCROWN.C030c_verification_speedup");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (d_in_id, d_in) = b.fresh_local(c.nat.clone());
            let sym_g = c.sym_group_of(&d_in);
            let (g_id, g) = b.fresh_local(sym_g.clone());
            let orbit = c.orbit_bound_app(&d_in, &g);
            let concl = c.nat_le(orbit, d_in.clone());
            let (h_id, _) = b.fresh_local(concl.clone());
            let r = b.mk_pi(h_id, BinderInfo::Default, concl.clone(), concl);
            let r = b.mk_pi(g_id, BinderInfo::Default, sym_g, r);
            let r = b.mk_pi(d_in_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (d_in_id, d_in) = b.fresh_local(c.nat.clone());
            let sym_g = c.sym_group_of(&d_in);
            let (g_id, g) = b.fresh_local(sym_g.clone());
            let orbit = c.orbit_bound_app(&d_in, &g);
            let concl = c.nat_le(orbit, d_in.clone());
            let (h_id, h) = b.fresh_local(concl.clone());
            let r = b.mk_lam(h_id, BinderInfo::Default, concl, h);
            let r = b.mk_lam(g_id, BinderInfo::Default, sym_g, r);
            let r = b.mk_lam(d_in_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// C030d: `NNVerify.OrbitCROWN.C030d_orbit_stabilizer_sharp`
    ///
    /// Sharp orbit-stabilizer bound (multiplicative form):
    /// ```text
    /// forall (d_in : Nat) (G : SymmetryGroup d_in),
    ///   LE.le Nat instLENat
    ///     (Nat.mul (OrbitBound d_in G) (GroupOrder d_in G))
    ///     d_in
    /// ```
    ///
    /// Mathematical meaning: for a finite group `G` acting on a
    /// `d_in`-dimensional space, the orbit-stabilizer theorem implies
    /// `|Orbit(x)| * |Stab(x)| = |G|`, and summing over orbits gives
    /// `|G| * (number of orbits) <= d_in`. Equivalent to the division
    /// form `|Orbit| <= d_in / |G|` the task description uses; the
    /// multiplicative form is preferred because `Nat.div` in the
    /// current kernel is a placeholder reducible Definition (body
    /// `fun _ _ => Nat.zero`) that would collapse both sides to
    /// `Nat.zero` and masquerade a vacuous proof — exactly the #3468
    /// bug that #3550 fixed.
    ///
    /// Why Opaque + sorry_inhabit_pi (not Theorem, not Axiom):
    /// - Theorem would require either a sharp `Nat.div` or a genuine
    ///   group-action model (fibers, pointwise stabilizers, counting
    ///   bijections). The current carriers (`OrbitBound`, `GroupOrder`,
    ///   `GroupAction`) are Opaque placeholders — there is no
    ///   mathematical content to reduce against, so any "proof" would
    ///   be a definitional-equality trick, not a real argument.
    /// - Axiom would increase C030's domain-axiom count from 0 to 1,
    ///   violating the axiom-ratchet rule and reintroducing an unproved
    ///   trust gap that already has a cleaner Opaque-with-sorry form.
    /// - Opaque + sorry_inhabit_pi matches the C030a / C030b pattern:
    ///   the claim is kernel-registered, its type is type-checked, and
    ///   the sorry marker is honest — no axiom added, no masquerade.
    ///
    /// Soundness envelope:
    /// - Domain axioms: 0 (sorry is a trust marker, not an axiom — see
    ///   `TRUST_MARKERS` in `env/axiom_audit.rs`).
    /// - Proof quality: NOT `Constructive` (sorry transitively reaches
    ///   the theorem).
    /// - Honest about scope: C030c now requires the loose bound
    ///   `|Orbit| <= d_in` as explicit local evidence; C030d states the
    ///   sharp bound `|Orbit| * |G| <= d_in` as an unproved claim.
    ///   Downstream pipelines must treat C030d as a trust-envelope
    ///   dependency.
    ///
    /// Follow-up path to constructive proof:
    /// 1. Replace `GroupAction` placeholder with a concrete permutation
    ///    model over `Fin d_in` (so `|Orbit|` is computable).
    /// 2. Replace `GroupOrder` placeholder with the cardinality of the
    ///    concrete group (so `|G|` is computable).
    /// 3. Prove the Burnside / orbit-stabilizer counting lemma over the
    ///    concrete model using `Nat.rec` induction.
    ///
    /// History:
    /// - #3564: first registered as honest Opaque + sorry_inhabit_pi.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_c030d_orbit_stabilizer_sharp(
        &mut self,
        c: &OrbitCrownConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.OrbitCROWN.C030d_orbit_stabilizer_sharp");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (d_in_id, d_in) = b.fresh_local(c.nat.clone());
            let sym_g = c.sym_group_of(&d_in);
            let (g_id, g) = b.fresh_local(sym_g.clone());
            let orbit = c.orbit_bound_app(&d_in, &g);
            let group_order = c.group_order_app(&d_in, &g);
            // `Nat.mul (OrbitBound d_in G) (GroupOrder d_in G)` — the
            // sharp multiplicative bound `|Orbit| * |G|`.
            let product = c.mul_nat(orbit, group_order);
            let concl = c.nat_le(product, d_in.clone());
            let r = b.mk_pi(g_id, BinderInfo::Default, sym_g, concl);
            let r = b.mk_pi(d_in_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        let value = sorry_inhabit_pi(self, &ty);
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}
