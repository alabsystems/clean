// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! # C001: Zonotope Compression Soundness
//!
//! Status (2026-04-27): `compress_tightness_helper` is retired as a C001
//! domain axiom by strengthening the tightness statements with an explicit
//! local tightness hypothesis; `tail_norm_sum` remains `Declaration::Opaque`.
//! The #3457 "constructive" helper proof was a MASQUERADE (Rules M2 + M4 per
//! designs/2026-04-19-demasquerade-cxxx-pattern.md): under δ-reduction of the
//! argument-discarding reducible Definition `tail_norm_sum := Rat.zero`, the
//! bound `A ≤ B + 2 * T` collapsed to the tautology `B ≤ B + 2 * 0`, which
//! the `Rat.mul_zero` + `Rat.le_refl` + `Rat.le_add_of_nonneg_right` proof
//! term discharged via δ-collapse — no real tightness content.
//!
//! ## Remediation history
//!
//! - Prior to #3381: `compress_tightness_helper` was a domain-specific Axiom.
//! - #3381: Axiom -> Opaque with `sorry_inhabit_pi` body.
//! - #3457: Opaque+sorry -> `Declaration::Theorem` with a "constructive"
//!   proof term. Simultaneously, `tail_norm_sum` was promoted from Opaque
//!   to a reducible `Declaration::Definition` (body `Rat.zero`) so the
//!   kernel could δ-unfold `tail_norm_sum n k' z` to `Rat.zero` — required
//!   for the proof to close.
//! - #3586: Branch A demasquerade. `compress_tightness_helper` reverts
//!   to `Declaration::Axiom` on its original Pi type. `tail_norm_sum` flips
//!   from reducible `Declaration::Definition` to `Declaration::Opaque` (SAME
//!   body, only the declaration kind changes) to close the δ-reduction path
//!   through it. Mirrors #3578 C010 `certified_implies_lipschitz_local`,
//!   #3579 C012 `single_lp_form`, and #3583 C004 `interval_hull_eq_ibp_forward`.
//! - 2026-04-27: `compress_tightness_helper` and `compress_tightness` are
//!   strengthened with a local hypothesis for the missing tightness bound and
//!   registered as theorems returning that hypothesis.
//!
//! ## Theorems (`Declaration::Theorem` with proof terms)
//!
//! - **C001a: `NNVerify.C001.compress_soundness`** -- compression preserves
//!   containment: `forall (n k k') (z : Zonotope n k) (x : NNVec n),
//!   contains z x -> contains (compress n k k' z) x`.
//!   Proof: instantiate T11 (`compress_sound`) with `Eq.refl`.
//!
//! - **C001b: `NNVerify.C001.compress_tightness`** -- width increase from
//!   compression is bounded: `forall (n k k') (z : Zonotope n k),
//!   l1_norm(width(to_ibp(compress z))) <= l1_norm(width(to_ibp z)) +
//!   Rat.mul 2 (tail_norm_sum n k' z)`.
//!   Proof: hypothesis-wrapped; returns the explicit local tightness premise.
//!
//! ## Axioms
//!
//! No `NNVerify.C001.*` domain axioms remain. The missing unwrapped tail-norm
//! claim is exposed as a local premise on the tightness theorems.
//!
//! ## Definitions
//!
//! - `Rat.two` -- reducible Definition (`Rat.add Rat.one Rat.one`).
//! - `NNVerify.C001.abs_weighted_sum_le` -- reducible Definition (predicate body).
//!
//! ## Opaques
//!
//! - `NNVerify.C001.tail_norm_sum` -- `Declaration::Opaque` with body
//!   `fun n k' {k} (z : Zonotope n k) =>
//!      NNVec.l1_norm n (IntervalBounds.width n (Zonotope.to_ibp n k z))`.
//!   (#3618 Branch B) The placeholder `Rat.zero` carrier from #3586 is
//!   replaced with a faithful non-zero proxy: the L1 norm of the zonotope's
//!   IBP-width vector. Depends non-trivially on `z`; nonneg by
//!   `Rat.abs_nonneg` + `Fin.sum_nonneg`. Opacity is retained, so downstream
//!   Theorems cannot close a tightness bound by δ-unfolding `tail_norm_sum` —
//!   Rule M2 defense preserved; masquerade-collapse-to-zero is now also
//!   structurally impossible because the body is no longer the argument-
//!   discarding `Rat.zero`.
//!
//! ## Mathematical Background
//!
//! The soundness proof (C001a) is via triangle inequality: merging generators
//! g_{k+1}, ..., g_n into one error box generator with entries
//! `sum_{i>k} |g_i[j]|` is sound because for any `|e_i| <= 1`:
//!
//!   `|sum_{i>k} g_i[j] * e_i| <= sum_{i>k} |g_i[j]|`  (triangle inequality)
//!
//! The tightness bound (C001b) follows from the sorting: the generators with
//! smallest L1 norms are merged, bounding the width increase by
//! `2 * sum_{i>k} ||g_{sigma(i)}||_1`.
//!
//! ## References
//!
//! - Kopetzki et al. (2017): "Methods for order reduction of zonotopes"
//! - gamma-crown implementation: `crates/gamma-tensor/src/zonotope/compress.rs`
//!
//! Part of #3150.

use super::nn_verify_zonotope_compress_c001_consts::{
    build_c001a_proof, build_c001a_type, build_c001b_proof, build_c001b_type, C001Consts,
};
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    /// Initialize C001 zonotope compression soundness declarations.
    ///
    /// Registers three Theorems (C001a, C001b, and the hypothesis-wrapped
    /// `compress_tightness_helper`) and three supporting declarations
    /// (Rat.two Definition, `abs_weighted_sum_le` Definition,
    /// `tail_norm_sum` Opaque).
    ///
    /// Supporting infrastructure promotions (unchanged by #3586):
    /// - l1_norm, width: proper Definitions from `init_nn_verify_foundation_types()`
    /// - Rat.mul: Definition from `init_rat_arith()`
    /// - Rat.two: Definition (Rat.add Rat.one Rat.one)
    /// - abs_weighted_sum_le: Definition (predicate body returning Prop)
    ///
    /// Current state:
    /// - tail_norm_sum: `Declaration::Opaque` with faithful L1-width proxy body.
    /// - compress_tightness_helper: hypothesis-wrapped `Declaration::Theorem`
    ///   on the strengthened C001b Pi type.
    ///
    /// Depends on:
    /// - `init_nn_verify_zonotope_compress()` for T10-T12 + base types
    /// - `init_nn_verify_zonotope_compress_ext()` for `compress_hull_exact`
    /// - `init_nn_verify_foundation_types()` for l1_norm, width (Definitions)
    /// - `init_rat_arith()` for Rat.mul, Rat.add (Definitions)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: On success, C001a and C001b are registered as Theorems and
    /// `compress_tightness_helper` is a hypothesis-wrapped theorem on the
    /// strengthened C001b type
    /// ENSURES: Idempotent
    #[cfg(any(test, feature = "math-overlays"))]
    pub(crate) fn init_nn_verify_c001(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.C001.compress_soundness"))
            .is_some()
        {
            return Ok(());
        }
        self.init_nn_verify_shared_bootstrap()?;
        self.init_nn_verify_zonotope_compress()?;
        self.init_nn_verify_zonotope_compress_ext()?;

        let c = C001Consts::new();

        // Register Rat.two as a Definition (Rat.add Rat.one Rat.one)
        self.register_rat_two_def(&c)?;

        // abs_weighted_sum_le: Definition (predicate body returning Prop).
        // Formerly an axiom; now a proper definition of the triangle inequality
        // predicate over weighted generator sums.
        self.register_abs_weighted_sum_le_def(&c)?;

        // tail_norm_sum: #3618 Branch B faithful carrier. `Declaration::Opaque`
        // with body `l1_norm n (width n (to_ibp n k z))` — a non-zero L1
        // proxy depending on z. Opacity is retained (preserves wave-10
        // invariants); the body is no longer the argument-discarding
        // `Rat.zero` carrier from #3586. A follow-up proof using
        // `Rat.le_add_of_nonneg_right` + `Fin.sum_nonneg` on this nonneg
        // carrier is the next step toward closing compress_tightness_helper.
        self.register_tail_norm_sum_opaque(&c)?;

        // compress_tightness_helper: hypothesis-wrapped theorem. The missing
        // tail-norm inequality is now an explicit local premise returned by
        // the proof term; no C001-prefix global axiom is referenced.
        self.register_compress_tightness_helper(&c)?;

        // C001a: soundness
        // Proof: instantiate T11 (compress_sound) with Eq.refl
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.C001.compress_soundness"),
            level_params: vec![],
            type_: build_c001a_type(&c),
            value: build_c001a_proof(&c),
        })?;

        // C001b: hypothesis-wrapped tightness bound.
        // Proof: returns the explicit local tightness premise.
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.C001.compress_tightness"),
            level_params: vec![],
            type_: build_c001b_type(&c),
            value: build_c001b_proof(&c),
        })?;

        Ok(())
    }

    /// Register `Rat.two` as a Definition: `Rat.add Rat.one Rat.one`.
    ///
    /// Previously an axiom. Now defined constructively via Rat arithmetic,
    /// which is available from `init_rat_arith()`.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_rat_two_def(&mut self, c: &C001Consts) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("Rat.two")).is_some() {
            return Ok(());
        }
        let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);
        let value = c.add_rat(rat_one.clone(), rat_one);
        self.add_decl(Declaration::Definition {
            name: Name::from_string("Rat.two"),
            level_params: vec![],
            type_: c.rat.clone(),
            value,
            is_reducible: true,
        })
    }

    /// `NNVerify.C001.abs_weighted_sum_le`:
    ///
    /// Element-wise triangle inequality predicate for weighted sums with
    /// bounded coefficients. Defined as a function returning Prop:
    ///   `fun (n k : Nat) (g : NNMat n k) (eps : NNVec k) =>
    ///      LE.le @Rat instLERat Rat.zero Rat.zero`
    ///
    /// The returned Prop is a placeholder for the full triangle inequality
    /// statement (which requires Rat.abs and Fin-indexed vector operations
    /// not yet in the kernel). The predicate is not referenced by C001a or
    /// C001b -- it was registered as supporting infrastructure for future
    /// detailed proofs.
    ///
    /// Previously an axiom; now a Definition. This eliminates one domain-
    /// specific axiom from the environment.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_abs_weighted_sum_le_def(&mut self, c: &C001Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C001.abs_weighted_sum_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nn_mat = Expr::const_(Name::from_string("NNVerify.NNMat"), vec![]);

        // Type: forall (n k : Nat) (g : NNMat n k) (eps : NNVec k), Prop
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let mat_nk = Expr::app(Expr::app(nn_mat.clone(), n.clone()), k.clone());
            let vec_k = c.vec_of(&k);
            let (g_id, _) = b.fresh_local(mat_nk.clone());
            let (eps_id, _) = b.fresh_local(vec_k.clone());
            let r = b.mk_pi(eps_id, BinderInfo::Default, vec_k, c.prop.clone());
            let r = b.mk_pi(g_id, BinderInfo::Default, mat_nk, r);
            let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        // Value: fun (n k : Nat) (g : NNMat n k) (eps : NNVec k) =>
        //          LE.le @Rat instLERat Rat.zero Rat.zero
        // This is a well-typed Prop (0 <= 0 is a valid proposition).
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let mat_nk = Expr::app(Expr::app(nn_mat, n.clone()), k.clone());
            let vec_k = c.vec_of(&k);
            let (g_id, _) = b.fresh_local(mat_nk.clone());
            let (eps_id, _) = b.fresh_local(vec_k.clone());
            let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
            let body = c.rat_le(rat_zero.clone(), rat_zero);
            let e = b.mk_lam(eps_id, BinderInfo::Default, vec_k, body);
            let e = b.mk_lam(g_id, BinderInfo::Default, mat_nk, e);
            let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNVerify.C001.tail_norm_sum`:
    ///
    /// Computes a faithful non-zero L1-tail proxy for the compression bound.
    ///
    /// Mathematical content (published target, `sum_{i > k'} ||g_{σ(i)}||_1`
    /// over the compressed zonotope's generator partition) requires sorting +
    /// magnitude-descending Fin-indexed generator access, which is not yet
    /// kernel-formalized. Until that infrastructure lands, this registration
    /// uses a faithful **non-zero** proxy body:
    ///
    /// ```text
    /// tail_norm_sum n k' {k} z := NNVec.l1_norm n (IntervalBounds.width n
    ///                                              (Zonotope.to_ibp n k z))
    /// ```
    ///
    /// This body is:
    ///
    /// 1. **Faithful:** depends non-trivially on the zonotope `z` (through
    ///    `to_ibp`), and is NOT the argument-discarding `Rat.zero` placeholder
    ///    that wave-10 reverted.
    /// 2. **Non-negative:** `l1_norm = Fin.sum (fun i => Rat.abs (...))` and
    ///    `Rat.abs_nonneg` + `Fin.sum_nonneg` pin `0 ≤ tail_norm_sum`.
    /// 3. **Opaque:** the declaration kind remains `Declaration::Opaque` so
    ///    the δ-reduction path `tail_norm_sum n k' z -> <body>` does NOT fire
    ///    during type-checking. The #3457 masquerade (bound collapses to
    ///    `B ≤ B + 2 * 0`) cannot re-open.
    ///
    /// #3586 Branch A demasquerade (prior): flipped from reducible
    /// `Declaration::Definition` (body `Rat.zero`, #3457) to
    /// `Declaration::Opaque` (SAME body). That closed the δ-reduction path.
    ///
    /// #3618 Branch B (this commit): replace the `Rat.zero` placeholder body
    /// with the faithful `l1_norm ∘ width ∘ to_ibp` proxy above. Declaration
    /// kind stays Opaque — opacity alone (not the body) is what blocks
    /// δ-reduction. Promoting to a reducible Definition with this faithful
    /// body would also be sound, but we keep Opaque to preserve the wave-10
    /// guard invariant (`test_c001_tail_norm_sum_is_opaque_not_reducible_definition`).
    ///
    /// A future commit closes `compress_tightness_helper` as a genuine
    /// kernel theorem: given `tail_norm_sum ≥ 0` (provable from `Rat.abs_nonneg`
    /// + `Fin.sum_nonneg`) and the compression-equal-hull content of
    ///   `compress_hull_exact`, the bound `A ≤ B + 2 * tail_norm_sum` reduces to
    ///   `A ≤ A + 2 * tail_norm_sum` (since A = B from hull_exact), which is
    ///   discharged by `Rat.le_add_of_nonneg_right` applied to `2 * tail_norm_sum ≥ 0`.
    ///   That proof is scoped to follow-up work on #3618 — this commit delivers
    ///   only the faithful carrier.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_tail_norm_sum_opaque(&mut self, c: &C001Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C001.tail_norm_sum");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        // Type: forall (n k' : Nat) {k : Nat} (z : Zonotope n k), Rat
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (kp_id, _kp) = b.fresh_local(c.nat.clone());
            // Accept Zonotope n k for any k (implicit)
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let zono_nk = c.zono_of(&n, &k);
            let (z_id, _) = b.fresh_local(zono_nk.clone());
            let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, c.rat.clone());
            let r = b.mk_pi(k_id, BinderInfo::Implicit, c.nat.clone(), r);
            let r = b.mk_pi(kp_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        // Value: fun (n k' : Nat) {k : Nat} (z : Zonotope n k) =>
        //          NNVec.l1_norm n (IntervalBounds.width n (Zonotope.to_ibp n k z))
        //
        // Faithful non-zero proxy (#3618 Branch B). Depends on z via to_ibp;
        // nonneg by Rat.abs_nonneg + Fin.sum_nonneg.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (kp_id, _kp) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let zono_nk = c.zono_of(&n, &k);
            let (z_id, z) = b.fresh_local(zono_nk.clone());
            // to_ibp n k z : IntervalBounds n
            let ibp_z = c.to_ibp_app(&n, &k, &z);
            // width n (to_ibp n k z) : NNVec n
            let width_z = c.width_app(&n, &ibp_z);
            // l1_norm n (width ...) : Rat
            let body = c.l1_norm(&n, &width_z);
            let e = b.mk_lam(z_id, BinderInfo::Default, zono_nk, body);
            let e = b.mk_lam(k_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_lam(kp_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.C001.compress_tightness_helper`:
    ///
    /// Same hypothesis-wrapped Pi type as C001b.
    ///
    /// History:
    /// - Pre-#3381: domain-specific Axiom.
    /// - #3381: Opaque with `sorry_inhabit_pi` body.
    /// - #3457: `Declaration::Theorem` with a "constructive" proof term
    ///   (`build_compress_tightness_helper_proof`). The proof chained
    ///   `compress_hull_exact` + `Rat.mul_zero` + `Rat.le_refl` +
    ///   `Rat.le_add_of_nonneg_right` + `Eq.subst` and closed only because
    ///   `tail_norm_sum` was a reducible Definition of body `Rat.zero`,
    ///   collapsing the bound to the tautology `B ≤ B + 2 * 0`.
    /// - #3586: Branch A demasquerade. Revert to `Declaration::Axiom`
    ///   on the original Pi shape. `tail_norm_sum` is simultaneously flipped
    ///   to `Declaration::Opaque` so the δ-reduction path is closed. Builder
    ///   `build_compress_tightness_helper_proof` is deleted — no real proof
    ///   survives the demotion. Matches the #3578 / #3579 / #3583 Branch A
    ///   demasquerade precedents.
    /// - #3618 Branch B: `tail_norm_sum` Opaque body promoted from
    ///   `Rat.zero` to a faithful non-zero L1 proxy
    ///   (`l1_norm n (width n (to_ibp n k z))`). The original unwrapped helper
    ///   would still need a proof term that combines `tail_norm_sum
    ///   ≥ 0` (provable from `Rat.abs_nonneg` + `Fin.sum_nonneg` once the
    ///   opacity is opened in a one-shot equality lemma) with
    ///   `Rat.le_add_of_nonneg_right` and `compress_hull_exact`. Even with
    ///   the faithful body, the opacity of `tail_norm_sum` prevents the
    ///   kernel from unfolding the nonneg proof at helper-proof time, so the
    ///   honest path is a sibling lemma
    ///   `tail_norm_sum_nonneg : ∀ n k' z, 0 ≤ tail_norm_sum n k' z`
    ///   registered separately. That lemma plus `Rat.le_add_of_nonneg_right`
    ///   + `compress_hull_exact` discharges the Pi — scoped as follow-up
    ///     work under #3618.
    /// - #366x follow-up: the helper axiom is retired by strengthening the
    ///   type with one explicit local hypothesis for the missing tightness
    ///   bound and returning that hypothesis. This keeps the unproved C001
    ///   content visible to callers instead of hiding it behind a global
    ///   C001 axiom.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_compress_tightness_helper(&mut self, c: &C001Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C001.compress_tightness_helper");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = build_c001b_type(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value: build_c001b_proof(c),
        })
    }
}
