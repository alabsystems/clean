// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! # C029: PAC-to-Proof — BRANCH A DEMASQUERADE (#3588)
//!
//! Status: After the 2026-04-27 hypothesis-wrapping pass, the three headline
//! C029 claims are `Declaration::Theorem` entries whose strengthened
//! statements require local evidence for the missing PAC/volume/certificate
//! obligations. The three leaf
//! carriers (`coverage_volume`, `miss_probability`, `proof_certificate`)
//! have been co-demoted from reducible `Declaration::Definition` to
//! `Declaration::Opaque` (same bodies; only the declaration kind
//! flipped), closing the δ-reduction loophole that let the prior
//! `Rat.le_refl` proofs type-check via alias-collapse.
//!
//! The three axioms are:
//!
//! - `proof_lifting` (C029c): `... -> proof_certificate d f x0 eps delta`.
//! - `volume_ratio_bound` (C029b): `... -> coverage_volume eps L H <= RHS`.
//! - `pac_certification_bound` (C029a): `... -> miss_probability k ... <= RHS`.
//!
//! Prior state (pre-#3588): three `Declaration::Theorem` entries whose
//! proof terms were all `Rat.le_refl` over reducible identity carriers.
//! Per `designs/2026-04-19-demasquerade-cxxx-pattern.md` Rules M1
//! (alias-collapse via reducible Definition) + M4 (Rat.le_refl root),
//! this is a textbook MASQUERADE — the leaves ARE the claim by
//! construction, so the inequality is trivially x ≤ x and closes by
//! reflexivity without any mathematical content.
//!
//! Inventory after the hypothesis-wrapping pass: 5 base-support Opaques (pgd_search,
//! lipschitz_bound, hessian_bound, nat_to_rat, pac_confidence) +
//! 3 carrier Opaques (coverage_volume, miss_probability,
//! proof_certificate) + 3 local-evidence Theorems (pac_certification_bound,
//! volume_ratio_bound, proof_lifting) = 11 decls, 0 domain axioms.
//!
//! History: Phase 1 (8 support -> Opaque), Phase 2 (#3378: sorry
//! Opaques), Phase 3 (#3467: proof_lifting -> Theorem via True),
//! Phase 4 (#3549: demasquerade True -> Rat.le delta delta),
//! Phase 5 (#3563: demasquerade C029a/b leaves to real arithmetic
//! formulas + promote to Theorem via Rat.le_refl),
//! Phase 6 (#3588: Branch A honest demotion — three Theorems ->
//! Axioms, three reducible Definition carriers -> Opaques).
//!
//! Branch B (faithful probability-measure carriers with real
//! Hoeffding/Chernoff derivations and a real geometric coverage
//! argument for the coverage_volume bound) remains future work; it
//! requires Mathlib probability theory and substantive measure-theoretic
//! infrastructure that is out of scope for this kernel.
//!
//! See: designs/2026-04-17-publication-quality-gamma-crown-proofs.md,
//! designs/2026-04-18-per-conjecture-remediation-path.md,
//! designs/2026-04-19-demasquerade-cxxx-pattern.md.
//!
//! Part of #3588 (extends #3378, #3467, #3549, #3563).

use super::nn_verify_pac_proof_defs;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for PAC-to-Proof formalization.
pub(super) struct PacProofConsts {
    pub(super) nat: Expr,
    pub(super) rat: Expr,
    pub(super) prop: Expr,
    pub(super) nn_vec: Expr,
    pub(super) rat_add: Expr,
    pub(super) rat_mul: Expr,
    pub(super) rat_div: Expr,
    pub(super) rat_one: Expr,
    pub(super) rat_zero: Expr,
    pub(super) le_le: Expr,
    pub(super) lt_lt: Expr,
    pub(super) inst_le_rat: Expr,
    pub(super) inst_lt_rat: Expr,
    pub(super) and: Expr,
    pub(super) real_exp: Expr,
    pub(super) neg: Expr,
    pub(super) nat_to_rat: Expr,
    pub(super) pgd_search: Expr,
    pub(super) lipschitz_bound: Expr,
    pub(super) hessian_bound: Expr,
    pub(super) coverage_volume: Expr,
    pub(super) miss_probability: Expr,
    pub(super) proof_certificate: Expr,
    pub(super) pac_confidence: Expr,
}

impl PacProofConsts {
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_div: Expr::const_(Name::from_string("Rat.div"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            lt_lt: Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            inst_lt_rat: Expr::const_(Name::from_string("instLTRat"), vec![]),
            and: Expr::const_(Name::from_string("And"), vec![]),
            real_exp: Expr::const_(Name::from_string("NNVerify.Lipschitz.real_exp"), vec![]),
            neg: Expr::const_(Name::from_string("Rat.neg"), vec![]),
            nat_to_rat: Expr::const_(Name::from_string("NNVerify.PacProof.nat_to_rat"), vec![]),
            pgd_search: Expr::const_(Name::from_string("NNVerify.PacProof.pgd_search"), vec![]),
            lipschitz_bound: Expr::const_(
                Name::from_string("NNVerify.PacProof.lipschitz_bound"),
                vec![],
            ),
            hessian_bound: Expr::const_(
                Name::from_string("NNVerify.PacProof.hessian_bound"),
                vec![],
            ),
            coverage_volume: Expr::const_(
                Name::from_string("NNVerify.PacProof.coverage_volume"),
                vec![],
            ),
            miss_probability: Expr::const_(
                Name::from_string("NNVerify.PacProof.miss_probability"),
                vec![],
            ),
            proof_certificate: Expr::const_(
                Name::from_string("NNVerify.PacProof.proof_certificate"),
                vec![],
            ),
            pac_confidence: Expr::const_(
                Name::from_string("NNVerify.PacProof.pac_confidence"),
                vec![],
            ),
        }
    }

    /// Build `LE.le @Rat instLERat lhs rhs`.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn rat_le(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(self.le_le.clone(), self.rat.clone()),
                    self.inst_le_rat.clone(),
                ),
                lhs,
            ),
            rhs,
        )
    }

    /// Build `LT.lt @Rat instLTRat lhs rhs`.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn rat_lt(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(self.lt_lt.clone(), self.rat.clone()),
                    self.inst_lt_rat.clone(),
                ),
                lhs,
            ),
            rhs,
        )
    }

    /// Build `Rat.add a b`.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_add.clone(), a), b)
    }

    /// Build `Rat.mul a b`.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_mul.clone(), a), b)
    }

    /// Build `Rat.div a b`.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn div(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_div.clone(), a), b)
    }

    /// Build `NNVerify.NNVec n`.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn vec_of(&self, n: Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n)
    }

    /// Function type `NNVerify.NNVec n -> NNVerify.NNVec n`.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn endo_ty(&self, n: &Expr) -> Expr {
        Expr::pi(
            BinderInfo::Default,
            self.vec_of(n.clone()),
            self.vec_of(n.clone()),
        )
    }
}

impl Environment {
    /// Initialize C029 (PAC-to-Proof) declarations.
    ///
    /// Depends on:
    /// - `init_nn_verify_types()` for NNVec
    /// - `init_rat()` / `init_rat_arith()` / `init_rat_ord()` for Rat structure
    /// - `init_rat_linear_order()` for `Rat.le_refl` (#3549 constructive proof)
    /// - `init_eq()` for equality, `init_and()` for conjunction
    /// - `init_nn_verify_lipschitz()` for `NNVerify.Lipschitz.real_exp`
    /// - `init_sorry()` for sorry-based Opaque proof inhabitation (#3378)
    #[cfg(any(test, feature = "math-overlays"))]
    pub(crate) fn init_nn_verify_pac_proof(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.PacProof.pgd_search"))
            .is_some()
        {
            return Ok(());
        }

        self.init_nn_verify_types()?;
        self.init_rat()?;
        self.init_rat_arith()?;
        self.init_rat_ord()?;
        self.init_rat_linear_order()?; // Provides Rat.le_refl for #3549 proof_lifting
        self.init_eq()?;
        self.init_and()?;
        self.init_true_false()?;
        self.init_nn_verify_lipschitz()?;
        self.init_sorry()?; // Required for sorry-based Opaque proof inhabitation

        let c = PacProofConsts::new();

        // Opaques (data/functions — 8)
        self.register_pp_pgd_search(&c)?;
        self.register_pp_lipschitz_bound(&c)?;
        self.register_pp_hessian_bound(&c)?;
        self.register_pp_nat_to_rat(&c)?;
        self.register_pp_coverage_volume(&c)?;
        self.register_pp_miss_probability(&c)?;
        self.register_pp_proof_certificate(&c)?;
        self.register_pp_pac_confidence(&c)?;

        // Opaques (promoted claims, sorry-inhabited — 3)
        self.register_pp_pac_certification_bound(&c)?;
        self.register_pp_volume_ratio_bound(&c)?;
        self.register_pp_proof_lifting(&c)?;

        Ok(())
    }

    // -- Opaque Definitions (formerly Axioms) -----------------------------------

    /// `pgd_search : Nat -> (NNVec n -> NNVec n) -> NNVec n -> Rat -> Nat -> Prop`
    /// Opaque: `fun n _ _ _ _ => True`
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_pp_pgd_search(&mut self, c: &PacProofConsts) -> Result<(), EnvError> {
        let true_const = Expr::const_(Name::from_string("True"), vec![]);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let endo = c.endo_ty(&n);
            let (f_id, _) = b.fresh_local(endo.clone());
            let (x0_id, _) = b.fresh_local(c.vec_of(n.clone()));
            let (eps_id, _) = b.fresh_local(c.rat.clone());
            let (k_id, _) = b.fresh_local(c.nat.clone());
            let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), true_const);
            let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(x0_id, BinderInfo::Default, c.vec_of(n), e);
            let e = b.mk_lam(f_id, BinderInfo::Default, endo, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.PacProof.pgd_search"),
            level_params: vec![],
            type_: nn_verify_pac_proof_defs::build_pgd_search_type(c),
            value,
        })
    }

    /// `lipschitz_bound : Nat -> (NNVec n -> NNVec n) -> Rat -> Prop`
    /// Opaque: `fun n _ _ => True`
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_pp_lipschitz_bound(&mut self, c: &PacProofConsts) -> Result<(), EnvError> {
        let true_const = Expr::const_(Name::from_string("True"), vec![]);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let endo = c.endo_ty(&n);
            let (f_id, _) = b.fresh_local(endo.clone());
            let (l_id, _) = b.fresh_local(c.rat.clone());
            let e = b.mk_lam(l_id, BinderInfo::Default, c.rat.clone(), true_const);
            let e = b.mk_lam(f_id, BinderInfo::Default, endo, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.PacProof.lipschitz_bound"),
            level_params: vec![],
            type_: nn_verify_pac_proof_defs::build_lipschitz_bound_type(c),
            value,
        })
    }

    /// `hessian_bound : Nat -> (NNVec n -> NNVec n) -> Rat -> Prop`
    /// Opaque: `fun n _ _ => True`
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_pp_hessian_bound(&mut self, c: &PacProofConsts) -> Result<(), EnvError> {
        let true_const = Expr::const_(Name::from_string("True"), vec![]);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let endo = c.endo_ty(&n);
            let (f_id, _) = b.fresh_local(endo.clone());
            let (h_id, _) = b.fresh_local(c.rat.clone());
            let e = b.mk_lam(h_id, BinderInfo::Default, c.rat.clone(), true_const);
            let e = b.mk_lam(f_id, BinderInfo::Default, endo, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.PacProof.hessian_bound"),
            level_params: vec![],
            type_: nn_verify_pac_proof_defs::build_hessian_bound_type(c),
            value,
        })
    }

    /// `nat_to_rat : Nat -> Rat`
    /// Opaque: `fun _ => Rat.zero`
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_pp_nat_to_rat(&mut self, c: &PacProofConsts) -> Result<(), EnvError> {
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, _) = b.fresh_local(c.nat.clone());
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), c.rat_zero.clone());
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.PacProof.nat_to_rat"),
            level_params: vec![],
            type_: nn_verify_pac_proof_defs::build_nat_to_rat_type(c),
            value,
        })
    }

    /// `coverage_volume : Rat -> Rat -> Rat -> Rat`
    ///
    /// #3588 Branch A demasquerade: **Declaration::Opaque** (same body
    /// as the pre-#3588 reducible Definition, only the declaration kind
    /// flipped). Body is `fun eps L H => (L * (eps * eps)) / (1 + H * (eps * eps))`.
    ///
    /// The flip to Opaque closes the δ-reduction path that let the
    /// pre-#3588 `volume_ratio_bound` Theorem discharge its `Rat.le`
    /// goal via `Rat.le_refl RHS` (alias-collapse MASQUERADE per
    /// `designs/2026-04-19-demasquerade-cxxx-pattern.md` Rules M1 + M4).
    /// With `coverage_volume` now Opaque, `coverage_volume eps L H`
    /// does not unfold during `def_eq`, so that trivial proof path is
    /// gone.
    ///
    /// Part of #3588 (Branch A — mirrors #3579 C012 single_lp_form and
    /// #3578 C010 lipschitz_local co-demotion pattern).
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_pp_coverage_volume(&mut self, c: &PacProofConsts) -> Result<(), EnvError> {
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (eps_id, eps) = b.fresh_local(c.rat.clone());
            let (l_id, l) = b.fresh_local(c.rat.clone());
            let (h_id, h) = b.fresh_local(c.rat.clone());
            // Body: (L * (eps * eps)) / (1 + H * (eps * eps))
            let eps_sq = c.mul(eps.clone(), eps);
            let body = c.div(
                c.mul(l, eps_sq.clone()),
                c.add(c.rat_one.clone(), c.mul(h, eps_sq)),
            );
            let e = b.mk_lam(h_id, BinderInfo::Default, c.rat.clone(), body);
            let e = b.mk_lam(l_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.PacProof.coverage_volume"),
            level_params: vec![],
            type_: nn_verify_pac_proof_defs::build_coverage_volume_type(c),
            value,
        })
    }

    /// `miss_probability : Nat -> Rat -> Rat`
    ///
    /// #3588 Branch A demasquerade: **Declaration::Opaque** (same body
    /// as the pre-#3588 reducible Definition, only the declaration kind
    /// flipped). Body is `fun k v => real_exp (neg (mul (nat_to_rat k) v))`
    /// — the PAC-Chernoff definitional form in terms of sample count
    /// `k` and coverage volume `v`.
    ///
    /// The flip to Opaque closes the δ-reduction path that let the
    /// pre-#3588 `pac_certification_bound` Theorem discharge its
    /// `Rat.le` goal via `Rat.le_refl RHS` (alias-collapse MASQUERADE
    /// per `designs/2026-04-19-demasquerade-cxxx-pattern.md` Rules
    /// M1 + M4). With `miss_probability` now Opaque, the kernel cannot
    /// unfold `miss_probability k v` during def_eq, so the trivial
    /// reflexivity path is gone.
    ///
    /// **Honesty caveat:** the *claim* encoded by this symbol — that
    /// `miss_probability <= exp(-k * coverage_volume)` — is a
    /// probability-theoretic bound (Hoeffding/Chernoff). A substantive
    /// derivation from a real probability measure requires Mathlib's
    /// probability theory, which remains out of scope.
    ///
    /// Part of #3588 (Branch A — follow-up to #3563, #3549, #3467).
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_pp_miss_probability(&mut self, c: &PacProofConsts) -> Result<(), EnvError> {
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (v_id, v) = b.fresh_local(c.rat.clone());
            // Body: real_exp (neg (mul (nat_to_rat k) v))
            let body = Expr::app(
                c.real_exp.clone(),
                Expr::app(c.neg.clone(), c.mul(Expr::app(c.nat_to_rat.clone(), k), v)),
            );
            let e = b.mk_lam(v_id, BinderInfo::Default, c.rat.clone(), body);
            let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.PacProof.miss_probability"),
            level_params: vec![],
            type_: nn_verify_pac_proof_defs::build_miss_probability_type(c),
            value,
        })
    }

    /// `proof_certificate : Nat -> (NNVec n -> NNVec n) -> NNVec n -> Rat -> Rat -> Prop`
    ///
    /// #3588 Branch A demasquerade: **Declaration::Opaque** (same body
    /// as the pre-#3588 reducible Definition, only the declaration kind
    /// flipped). Body is `fun _ _ _ _ delta => Rat.le delta delta`.
    ///
    /// The flip to Opaque closes the δ-reduction path that let the
    /// pre-#3588 `proof_lifting` Theorem discharge its
    /// `proof_certificate d f x0 eps delta` conclusion via
    /// `Rat.le_refl delta` (alias-collapse MASQUERADE per
    /// `designs/2026-04-19-demasquerade-cxxx-pattern.md` Rules
    /// M1 + M4). With `proof_certificate` now Opaque, the conclusion
    /// no longer reduces to `Rat.le delta delta` during def_eq, so the
    /// trivial reflexivity path is gone.
    ///
    /// Part of #3588 (Branch A — follow-up to #3549, #3467).
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_pp_proof_certificate(&mut self, c: &PacProofConsts) -> Result<(), EnvError> {
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let endo = c.endo_ty(&n);
            let (f_id, _) = b.fresh_local(endo.clone());
            let (x0_id, _) = b.fresh_local(c.vec_of(n.clone()));
            let (eps_id, _) = b.fresh_local(c.rat.clone());
            let (delta_id, delta) = b.fresh_local(c.rat.clone());
            // Body: `Rat.le delta delta` — real Rat inequality (not True).
            let body = c.rat_le(delta.clone(), delta);
            let e = b.mk_lam(delta_id, BinderInfo::Default, c.rat.clone(), body);
            let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(x0_id, BinderInfo::Default, c.vec_of(n), e);
            let e = b.mk_lam(f_id, BinderInfo::Default, endo, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.PacProof.proof_certificate"),
            level_params: vec![],
            type_: nn_verify_pac_proof_defs::build_proof_certificate_type(c),
            value,
        })
    }

    /// `pac_confidence : Rat -> Rat`
    /// Opaque: `fun _ => Rat.zero`
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_pp_pac_confidence(&mut self, c: &PacProofConsts) -> Result<(), EnvError> {
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (r_id, _) = b.fresh_local(c.rat.clone());
            let e = b.mk_lam(r_id, BinderInfo::Default, c.rat.clone(), c.rat_zero.clone());
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.PacProof.pac_confidence"),
            level_params: vec![],
            type_: nn_verify_pac_proof_defs::build_pac_confidence_type(c),
            value,
        })
    }

    // -- Axioms (post-#3588 Branch A demasquerade demotion) -------------------

    /// `pac_certification_bound` (C029a): PAC-Chernoff miss-probability bound.
    ///
    /// 2026-04-27: hypothesis-wrapped `Declaration::Theorem`. The statement
    /// exposes the missing PAC/Chernoff inequality as a local premise and the
    /// proof returns that premise directly. This does not unfold the opaque
    /// `miss_probability` carrier and does not depend on a global C029 axiom.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_pp_pac_certification_bound(&mut self, c: &PacProofConsts) -> Result<(), EnvError> {
        let type_ = nn_verify_pac_proof_defs::build_pac_certification_bound_type(c);
        let value = nn_verify_pac_proof_defs::build_pac_certification_bound_proof(c);
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.PacProof.pac_certification_bound"),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `volume_ratio_bound` (C029b): coverage-volume upper bound.
    ///
    /// 2026-04-27: hypothesis-wrapped `Declaration::Theorem`. The statement
    /// exposes the missing volume-ratio inequality as a local premise and the
    /// proof returns that premise directly.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_pp_volume_ratio_bound(&mut self, c: &PacProofConsts) -> Result<(), EnvError> {
        let type_ = nn_verify_pac_proof_defs::build_volume_ratio_bound_type(c);
        let value = nn_verify_pac_proof_defs::build_volume_ratio_bound_proof(c);
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.PacProof.volume_ratio_bound"),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `proof_lifting` (C029c): PAC search lifts to proof certificate.
    ///
    /// 2026-04-27: hypothesis-wrapped `Declaration::Theorem`. The statement
    /// exposes the missing certificate witness as a local premise and the
    /// proof returns that premise directly.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_pp_proof_lifting(&mut self, c: &PacProofConsts) -> Result<(), EnvError> {
        let type_ = nn_verify_pac_proof_defs::build_proof_lifting_type(c);
        let value = nn_verify_pac_proof_defs::build_proof_lifting_proof(c);
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.PacProof.proof_lifting"),
            level_params: vec![],
            type_,
            value,
        })
    }
}
