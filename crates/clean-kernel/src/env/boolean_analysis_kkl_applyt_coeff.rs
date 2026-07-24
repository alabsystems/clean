// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual `(4/3→2)` bound — Stage C-3, the **applyT-coefficient orthogonality
//! identity** (design `2026-06-18-kkl-real-sqrt-layer-plan.md` §10.9, the pinned
//! residual). This is the genuine remaining §9.6 content of the dual bound: the
//! operator-spectrum (Fourier-coefficient) law of the materialized noise
//! operator `BoolAnalysis.applyT`.
//!
//! # The theorem
//!
//! ```text
//! BoolAnalysis.applyT_coeff_eq :
//!   ∀ (ρ : Rat) (n : Nat) (g : HCPoint n → Rat) (jS : Fin (2^n)),
//!     subsetSum n (fun x => applyT ρ n g x · χ_{hcDecode n jS}(x))   -- A_{applyT(ρ)g}(S)
//!       = ((2^n) · powNat ρ (setSizeNat n (hcDecode n jS)))          -- 2^n·ρ^{|S|}·…
//!           · subsetSum n (fun x => g x · χ_{hcDecode n jS}(x))      -- …·A_g(S)
//! ```
//!
//! i.e. with `A a S := subsetSum n (fun x => a x · χ_S x)`, the Fourier
//! coefficient of `applyT(ρ)g` at `S` is `2^n·ρ^{|S|}` times that of `g`. The
//! subset `S` is materialized as the DECODED index `hcDecode n jS` (`jS : Fin
//! (2^n)`) — exactly the convention of the landed `subsetSum_inversion_core`,
//! so the diagonal collapse over the SPECTRAL index `T` lands at the `Fin (2^n)`
//! index `jS` (`Fin.sum_diag_collapse`) with the off-diagonal terms killed by
//! `chi_offdiag_subsetSum_zero`. (Quantifying `jS` rather than a free `HCPoint n`
//! avoids the absent `hcEncode` round-trip; the STEP-2 consumer
//! `subsetSum_parseval_core` at `a := applyT ρ n g` δ-unfolds its `S`-sum to
//! `Fin.sum (2^n) (… ∘ hcDecode)`, so the per-`jS` form lifts under
//! `Fin.sum_congr` without ever naming a free subset.)
//!
//! # The eigen-action core
//!
//! The identity factors through the **diagonal action of the noise kernel on a
//! single character** (`noiseDensity_apply_chi_eigen`):
//!
//! ```text
//! ∀ ρ n jS y, subsetSum n (fun x => noiseDensityW ρ n x y · χ_{hcDecode jS}(x))
//!   = ((2^n)·powNat ρ (setSizeNat n (hcDecode jS))) · χ_{hcDecode jS}(y).
//! ```
//!
//! `noiseDensityW ρ n x y` δ-unfolds (reducible) to `Σ_T ρ^{|T|}·(χ_T x·χ_T y)`,
//! so the `x`-sum is `Σ_x (Σ_T ρ^{|T|}(χ_T x·χ_T y))·χ_S x`. Swapping `x↔T`
//! (`subsetSum_swap`) and pulling the `T`-constants out (`subsetSum_smul`,
//! `Rat.mul_*`) gives `Σ_T (ρ^{|T|}·χ_T y)·(Σ_x χ_T x·χ_S x)`. The inner `x`-sum
//! is `2^n·δ_{T,S}` (the landed bricks `chi_offdiag_subsetSum_zero` /
//! `chi_diag_subsetSum_cube`), so `Fin.sum_diag_collapse` at `jS` lands the sole
//! surviving `T = S` term `(ρ^{|S|}·χ_S y)·2^n`, regrouped to the target.
//!
//! # The assembly
//!
//! `A_{applyT(ρ)g}(S) = Σ_x (Σ_y g y·W(ρ,x,y))·χ_S x`. Per-`x` `mul_comm` +
//! `subsetSum_smul` pulls `χ_S x` into the `y`-sum, `subsetSum_swap` brings the
//! `y`-sum outside, `subsetSum_smul` pulls each `g y` out, and the eigen-action
//! collapses the inner `x`-sum: `Σ_y g y·(2^n·ρ^{|S|}·χ_S y) = 2^n·ρ^{|S|}·A_g(S)`.
//!
//! Every leaf (`subsetSum_swap`/`_smul`/`_congr`, `chi_*_subsetSum_*`,
//! `Fin.sum_diag_collapse`, `Rat.mul_*`, `Eq.*`, `congrArg`) is `Constructive`
//! with empty admitted-axiom closure, so both lemmas are too. No axiom is added
//! or removed.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached atoms for the applyT-coefficient orthogonality identity.
struct CoeffConsts {
    nat: Expr,
    rat: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    nat_pow: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_mul: Expr,
    rat_zero: Expr,
    rat_mul_zero: Expr,
    rat_mul_comm: Expr,
    rat_mul_assoc: Expr,
    pow_nat: Expr,
    set_size_nat: Expr,
    hcpoint: Expr,
    hc_decode: Expr,
    chi: Expr,
    applyt: Expr,
    noise_density: Expr,
    subset_sum: Expr,
    subset_sum_congr: Expr,
    subset_sum_swap: Expr,
    subset_sum_smul: Expr,
    chi_offdiag: Expr,
    chi_diag: Expr,
    fin: Expr,
    fin_sum: Expr,
    fin_sum_diag_collapse: Expr,
    eq1: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
    false_c: Expr,
}

impl CoeffConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            nat_succ: k("Nat.succ"),
            nat_zero: k("Nat.zero"),
            nat_pow: k("Nat.pow"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            rat_mul: k("Rat.mul"),
            rat_zero: k("Rat.zero"),
            rat_mul_zero: k("Rat.mul_zero"),
            rat_mul_comm: k("Rat.mul_comm"),
            rat_mul_assoc: k("Rat.mul_assoc"),
            pow_nat: k("Rat.powNat"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            hc_decode: k("BoolAnalysis.hcDecode"),
            chi: k("BoolAnalysis.chi"),
            applyt: k("BoolAnalysis.applyT"),
            noise_density: k("BoolAnalysis.noiseDensityW"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            subset_sum_congr: k("BoolAnalysis.subsetSum_congr"),
            subset_sum_swap: k("BoolAnalysis.subsetSum_swap"),
            subset_sum_smul: k("BoolAnalysis.subsetSum_smul"),
            chi_offdiag: k("BoolAnalysis.chi_offdiag_subsetSum_zero"),
            chi_diag: k("BoolAnalysis.chi_diag_subsetSum_cube"),
            fin: k("Fin"),
            fin_sum: k("Fin.sum"),
            fin_sum_diag_collapse: k("Fin.sum_diag_collapse"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
            false_c: k("False"),
        }
    }

    fn one(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.nat_zero.clone())
    }
    fn two(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.one())
    }
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two(), n.clone()])
    }
    /// `2^n` as a `Rat` — `Rat.mk (Int.ofNat (Nat.pow 2 n)) 1`, byte-for-byte the
    /// `cube` numeral the chi bricks / parseval-core produce.
    fn cube(&self, n: &Expr) -> Expr {
        let ofnat = Expr::app(self.int_of_nat.clone(), self.pow2(n));
        Expr::apps(self.rat_mk.clone(), [ofnat, self.one()])
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn fsum(&self, n: Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n, g])
    }
    fn chi_(&self, n: &Expr, s: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.chi.clone(), [n.clone(), s.clone(), x.clone()])
    }
    fn pow(&self, rho: &Expr, kk: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [rho.clone(), kk.clone()])
    }
    fn set_size(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    fn hc_decode(&self, n: &Expr, j: &Expr) -> Expr {
        Expr::apps(self.hc_decode.clone(), [n.clone(), j.clone()])
    }
    fn density(&self, rho: &Expr, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        Expr::apps(
            self.noise_density.clone(),
            [rho.clone(), n.clone(), x.clone(), y.clone()],
        )
    }
    fn applyt(&self, rho: &Expr, n: &Expr, g: &Expr, x: &Expr) -> Expr {
        Expr::apps(
            self.applyt.clone(),
            [rho.clone(), n.clone(), g.clone(), x.clone()],
        )
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    fn eq_fin_pow(&self, n: &Expr, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            self.eq1.clone(),
            [self.fin_of(&self.pow2(n)), a.clone(), b.clone()],
        )
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }
    fn congr(&self, a: Expr, b: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, g, h],
        )
    }
    fn mul_comm(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_mul_comm.clone(), [a.clone(), b.clone()])
    }
    fn mul_assoc(&self, a: &Expr, b: &Expr, cc: &Expr) -> Expr {
        Expr::apps(
            self.rat_mul_assoc.clone(),
            [a.clone(), b.clone(), cc.clone()],
        )
    }
    /// `congrArg (fun z => left·z) h : left·a = left·bb`.
    fn mul_left_congr(
        &self,
        parent: &EnvDeclBuilder,
        left: &Expr,
        a: Expr,
        bb: Expr,
        h: Expr,
    ) -> Expr {
        let g = {
            let mut b = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = b.fresh_local(self.rat.clone());
            let body = self.mul(left.clone(), z);
            b.finish_child(b.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.congr(a, bb, g, h)
    }
    /// `congrArg (fun z => z·right) h : a·right = bb·right`.
    fn mul_right_congr(
        &self,
        parent: &EnvDeclBuilder,
        right: &Expr,
        a: Expr,
        bb: Expr,
        h: Expr,
    ) -> Expr {
        let g = {
            let mut b = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = b.fresh_local(self.rat.clone());
            let body = self.mul(z, right.clone());
            b.finish_child(b.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.congr(a, bb, g, h)
    }
    /// `subsetSum_smul n cc f : subsetSum n (fun z => cc·f z) = cc · subsetSum n f`.
    fn ssum_smul(&self, n: &Expr, cc: &Expr, f: &Expr) -> Expr {
        Expr::apps(
            self.subset_sum_smul.clone(),
            [n.clone(), cc.clone(), f.clone()],
        )
    }
    /// `subsetSum_congr n G H hyp : subsetSum n G = subsetSum n H`.
    fn ssum_congr(&self, n: &Expr, g: &Expr, h: &Expr, hyp: Expr) -> Expr {
        Expr::apps(
            self.subset_sum_congr.clone(),
            [n.clone(), g.clone(), h.clone(), hyp],
        )
    }
}

include!("boolean_analysis_kkl_applyt_coeff_eigen.rs");
include!("boolean_analysis_kkl_applyt_coeff_assemble.rs");

impl Environment {
    /// Register the deps shared by the eigen-action and the coefficient identity.
    fn register_applyt_coeff_deps(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_boolean_analysis()?;
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_subset_sum_swap_theorem()?;
        self.register_subset_sum_smul_theorem()?;
        self.register_rat_pow_nat()?;
        self.register_set_size_nat()?;
        self.register_noise_density_w()?;
        self.register_applyt()?;
        self.register_chi_offdiag_subset_sum_zero()?;
        self.register_chi_diag_subset_sum_cube()?;
        self.register_fin_sum_diag_collapse_theorem()?;
        // Rat.mul_assoc / Rat.mul_comm / Rat.mul_zero (quotient structural lemmas).
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?;
        }
        Ok(())
    }

    /// Register `BoolAnalysis.noiseDensity_apply_chi_eigen` — the diagonal action
    /// of the noise kernel on a single (decoded) character:
    /// `Σ_x W(ρ,x,y)·χ_S(x) = (2^n·ρ^{|S|})·χ_S(y)` at `S = hcDecode n jS`.
    /// Kernel-checked, `ProofQuality::Constructive`, empty admitted-axiom
    /// closure. Idempotent.
    pub fn register_noise_density_apply_chi_eigen(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.noiseDensity_apply_chi_eigen");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_applyt_coeff_deps()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = CoeffConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: eigen_type(&c),
            value: eigen_value(&c),
        })
    }

    /// Register `BoolAnalysis.applyT_coeff_eq` — the applyT-coefficient
    /// orthogonality identity `A_{applyT(ρ)g}(S) = 2^n·ρ^{|S|}·A_g(S)` at
    /// `S = hcDecode n jS`. Kernel-checked, `ProofQuality::Constructive`, empty
    /// admitted-axiom closure. Idempotent.
    pub fn register_applyt_coeff_eq(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.applyT_coeff_eq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_noise_density_apply_chi_eigen()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = CoeffConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: coeff_type(&c),
            value: coeff_value(&c),
        })
    }

    /// Init hook for the applyT-coefficient orthogonality overlay module.
    pub fn init_boolean_analysis_kkl_applyt_coeff(&mut self) -> Result<(), EnvError> {
        self.register_applyt_coeff_eq()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::carrier_refutation::refute_conjecture;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_applyt_coeff()
            .expect("init_boolean_analysis_kkl_applyt_coeff");
        env.init_boolean_analysis_kkl_applyt_coeff()
            .expect("idempotent");
        env
    }

    fn assert_constructive_axiom_free(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
        let value = info.value.clone().expect("theorem value present");
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("{name} proof must check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "{name} must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "{name} closure must be foundational-only, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_noise_density_apply_chi_eigen_constructive() {
        let env = env();
        assert_constructive_axiom_free(&env, "BoolAnalysis.noiseDensity_apply_chi_eigen");
    }

    #[test]
    fn test_applyt_coeff_eq_constructive() {
        let env = env();
        assert_constructive_axiom_free(&env, "BoolAnalysis.applyT_coeff_eq");
    }

    #[test]
    fn test_applyt_coeff_eq_not_refuted() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let info = env
            .get_const(&Name::from_string("BoolAnalysis.applyT_coeff_eq"))
            .expect("registered");
        assert_eq!(
            refute_conjecture(&tc, &info.type_),
            None,
            "applyT_coeff_eq is a TRUE orthogonality identity; must NOT refute"
        );
    }

    #[test]
    fn test_eigen_not_refuted() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let info = env
            .get_const(&Name::from_string(
                "BoolAnalysis.noiseDensity_apply_chi_eigen",
            ))
            .expect("registered");
        assert_eq!(
            refute_conjecture(&tc, &info.type_),
            None,
            "eigen-action is a TRUE identity; must NOT refute"
        );
    }
}
