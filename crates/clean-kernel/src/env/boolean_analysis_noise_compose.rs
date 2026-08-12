// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Noise-operator semigroup campaign — the **cube-level Fubini assembly**
//! `noiseDensityW_compose` (BUILD #1 of the noiseOp Parseval diagonalization).
//!
//! ```text
//! BoolAnalysis.noiseDensityW_compose :
//!   ∀ (ρ : Rat) (n : Nat) (x z : HCPoint n),
//!     subsetSum n (fun y => noiseDensityW ρ n x y · noiseDensityW ρ n y z)
//!       = cube n · noiseDensityW (ρ·ρ) n x z
//! ```
//!
//! with `cube n := Rat.mk (Int.ofNat (Nat.pow 2 n)) 1` (the keystone's `2^n`).
//! This is the un-normalized noise SEMIGROUP: composing the noise density over
//! the lone intermediate cube point `y` multiplies the correlation parameter
//! (`ρ → ρ·ρ`) and pays one `2^n` un-normalization factor.
//!
//! ## Proof route (multi-leg `Eq.trans`, mirrors `noise_spectral_core`)
//!
//! `noiseDensityW ρ n x y` δ-unfolds (reducible) to
//! `Σ_S ρ^{|S|}·(χ_S x · χ_S y)`. Write `wS := ρ^{|S|}`, `gS(y) := χ_S y`. Then
//! the per-`y` product is `(Σ_S wS·χ_S x·gS(y))·(Σ_T wT·gT(y)·χ_T z)`, and the
//! chain is (all sums are `subsetSum n`):
//!
//! ```text
//! E0  Σ_y  dens(x,y)·dens(y,z)
//!   =[legA, per-y product→double sum]   Σ_y Σ_S Σ_T K_{S,T}(x,z) · (χ_S y · χ_T y)
//!   =[legB, swap y↔S]                   Σ_S Σ_y Σ_T K_{S,T} · (χ_S y · χ_T y)
//!   =[legC, congr·swap y↔T per S]       Σ_S Σ_T Σ_y K_{S,T} · (χ_S y · χ_T y)
//!   =[legD, congr²·pull K out of Σ_y]   Σ_S Σ_T K_{S,T} · (Σ_y χ_S y · χ_T y)
//!   =[legE, congr²·KEYSTONE]            Σ_S Σ_T K_{S,T} · (cube · [S = T])
//!   =[legF, per-S scaled δ-extract T]   Σ_S cube · K_{S,S}(x,z)
//!   =[legG, congr·powNat_mul_base]      Σ_S cube · ((ρ·ρ)^{|S|}·(χ_S x · χ_S z))
//!   =[legH, pull cube out (smul)]       cube · Σ_S (ρ·ρ)^{|S|}·(χ_S x · χ_S z)
//!   ≡[δ noiseDensityW]                  cube · noiseDensityW (ρ·ρ) n x z   = E_rhs
//! ```
//!
//! where `K_{S,T}(x,z) := (wS·χ_S x)·(wT·χ_T z)`. At the diagonal `T = S`:
//! `K_{S,S} = (wS·χ_S x)·(wS·χ_S z)` and `legG` regroups
//! `(ρ^{|S|}·χ_S x)·(ρ^{|S|}·χ_S z) →[mmmc] (ρ^{|S|}·ρ^{|S|})·(χ_S x·χ_S z)
//! →[powNat_mul_base] (ρ·ρ)^{|S|}·(χ_S x·χ_S z)`.
//!
//! Every cited brick (`subsetSum_swap/_smul/_congr`, `subsetSum_chi_pair_diag`,
//! `subsetSum_subset_diag_extract_scaled`, `Rat.powNat_mul_base`,
//! `Rat.mul_*`, Eq built-ins) is a kernel-checked Theorem with an empty
//! admitted-axiom closure, so `noiseDensityW_compose` is
//! `ProofQuality::Constructive`, EMPTY closure. No axiom is added or removed.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the cube-level noise semigroup. All `noiseDensityW` /
/// `subsetSum` / `chi` / popcount spellings are byte-for-byte the
/// `boolean_analysis_noise_delta_proof.rs` / keystone shapes so the reducible
/// `noiseDensityW` head stays def-eq to its `subsetSum` integrand throughout.
struct ComposeConsts {
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    nat_beq: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_mul: Expr,
    bool_xor: Expr,
    hcpoint: Expr,
    fin: Expr,
    chi: Expr,
    ind: Expr,
    set_size_nat: Expr,
    pow_nat: Expr,
    noise_density: Expr,
    subset_sum: Expr,
    subset_sum_congr: Expr,
    subset_sum_swap: Expr,
    subset_sum_smul: Expr,
    diag_scaled: Expr,
    chi_pair_diag: Expr,
    pownat_mul_base: Expr,
    rat_mmmc: Expr,
    rat_mul_comm: Expr,
    rat_mul_assoc: Expr,
    eq1: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
}

impl ComposeConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            bool_: k("Bool"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_pow: k("Nat.pow"),
            nat_beq: k("Nat.beq"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            rat_mul: k("Rat.mul"),
            bool_xor: k("Bool.xor"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            fin: k("Fin"),
            chi: k("BoolAnalysis.chi"),
            ind: k("BoolAnalysis.ind"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            pow_nat: k("Rat.powNat"),
            noise_density: k("BoolAnalysis.noiseDensityW"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            subset_sum_congr: k("BoolAnalysis.subsetSum_congr"),
            subset_sum_swap: k("BoolAnalysis.subsetSum_swap"),
            subset_sum_smul: k("BoolAnalysis.subsetSum_smul"),
            diag_scaled: k("BoolAnalysis.subsetSum_subset_diag_extract_scaled"),
            chi_pair_diag: k("BoolAnalysis.subsetSum_chi_pair_diag"),
            pownat_mul_base: k("Rat.powNat_mul_base"),
            rat_mmmc: k("Rat.mul_mul_mul_comm"),
            rat_mul_comm: k("Rat.mul_comm"),
            rat_mul_assoc: k("Rat.mul_assoc"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
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
    fn chi_(&self, n: &Expr, s: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.chi.clone(), [n.clone(), s.clone(), x.clone()])
    }
    fn pow(&self, rho: &Expr, k: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [rho.clone(), k.clone()])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }
    /// `congrArg.{1,1} Rat Rat from to motive h : motive from = motive to`.
    fn congr(&self, from: Expr, to: Expr, motive: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), from, to, motive, h],
        )
    }

    fn one_nat(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.nat_zero.clone())
    }
    fn two_nat(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.one_nat())
    }
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two_nat(), n.clone()])
    }
    /// `cube n := Rat.mk (Int.ofNat (2^n)) 1` — the keystone's `2^n`.
    fn cube(&self, n: &Expr) -> Expr {
        let ofnat = Expr::app(self.int_of_nat.clone(), self.pow2(n));
        Expr::apps(self.rat_mk.clone(), [ofnat, self.one_nat()])
    }

    /// `indNat (S i) = @Bool.rec.{1} (fun _ => Nat) 0 1 (S i)` — byte-for-byte the
    /// `NoiseConsts::ind_nat` / `setSizeNat` build.
    fn ind_nat(&self, s_i: Expr) -> Expr {
        let nat_one = self.one_nat();
        let nat_motive = Expr::lam(BinderInfo::Default, self.bool_.clone(), self.nat.clone());
        let bool_rec_nat = Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        );
        Expr::apps(
            bool_rec_nat,
            [nat_motive, self.nat_zero.clone(), nat_one, s_i],
        )
    }
    /// `pc n S = Fin.sumNat n (fun i => indNat (S i))` — byte-for-byte the
    /// `noiseDensityW` weight exponent (so `ρ^{pc n S}` δ-matches the density).
    fn popcount(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let body = self.ind_nat(Expr::app(s.clone(), i.clone()));
        let pc_fn = b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body));
        Expr::apps(
            Expr::const_(Name::from_string("Fin.sumNat"), vec![]),
            [n.clone(), pc_fn],
        )
    }
    /// `w S := ρ^{pc n S}` — the per-subset ρ-weight (matches the density).
    fn weight(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, s: &Expr) -> Expr {
        self.pow(rho, &self.popcount(parent, n, s))
    }
    fn noise_density(&self, rho: &Expr, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        Expr::apps(
            self.noise_density.clone(),
            [rho.clone(), n.clone(), x.clone(), y.clone()],
        )
    }
    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }

    // ── named-lemma applications ─────────────────────────────────────────────
    /// `subsetSum_congr n G H h : subsetSum n G = subsetSum n H`.
    fn ss_congr(&self, n: &Expr, g: &Expr, h: &Expr, hyp: Expr) -> Expr {
        Expr::apps(
            self.subset_sum_congr.clone(),
            [n.clone(), g.clone(), h.clone(), hyp],
        )
    }
    /// `subsetSum_swap n f : Σ_a Σ_b f a b = Σ_b Σ_a f a b`.
    fn ss_swap(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.subset_sum_swap.clone(), [n.clone(), f.clone()])
    }
    /// `subsetSum_smul n c f : Σ_S c·(f S) = c·Σ_S f S`.
    fn ss_smul(&self, n: &Expr, cc: &Expr, f: &Expr) -> Expr {
        Expr::apps(
            self.subset_sum_smul.clone(),
            [n.clone(), cc.clone(), f.clone()],
        )
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    fn mul_comm(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_mul_comm.clone(), [a.clone(), b.clone()])
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    fn mul_assoc(&self, a: &Expr, b: &Expr, cc: &Expr) -> Expr {
        Expr::apps(
            self.rat_mul_assoc.clone(),
            [a.clone(), b.clone(), cc.clone()],
        )
    }
    /// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn mmmc(&self, a: &Expr, b: &Expr, cc: &Expr, d: &Expr) -> Expr {
        Expr::apps(
            self.rat_mmmc.clone(),
            [a.clone(), b.clone(), cc.clone(), d.clone()],
        )
    }
    /// `Rat.powNat_mul_base a b k : (a·b)^k = a^k·b^k`.
    fn pownat_mul_base(&self, a: &Expr, b: &Expr, kk: &Expr) -> Expr {
        Expr::apps(
            self.pownat_mul_base.clone(),
            [a.clone(), b.clone(), kk.clone()],
        )
    }
    /// `subsetSum_chi_pair_diag n S T : Σ_x χ_S x·χ_T x = cube n · ind[SΔT=∅]`.
    fn chi_pair_diag(&self, n: &Expr, s: &Expr, t: &Expr) -> Expr {
        Expr::apps(
            self.chi_pair_diag.clone(),
            [n.clone(), s.clone(), t.clone()],
        )
    }
    /// `fun (z : Rat) => left·z` — congruence on the RIGHT mul factor.
    fn mul_right_motive(&self, parent: &EnvDeclBuilder, left: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(self.rat.clone());
        let body = self.mul(left.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
    }
    /// `fun (z : Rat) => z·right` — congruence on the LEFT mul factor.
    fn mul_left_motive(&self, parent: &EnvDeclBuilder, right: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(self.rat.clone());
        let body = self.mul(z, right.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
    }
}

include!("boolean_analysis_noise_compose_endpoints.rs");
include!("boolean_analysis_noise_compose_legs.rs");

impl Environment {
    /// Register `BoolAnalysis.noiseDensityW_compose` — the un-normalized noise
    /// semigroup `Σ_y dens(ρ,x,y)·dens(ρ,y,z) = cube n · dens(ρ², x, z)`.
    /// Kernel-checked, `Constructive`, EMPTY admitted-axiom closure. Idempotent.
    pub(crate) fn register_noise_density_w_compose(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.noiseDensityW_compose");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_subset_sum_swap_theorem()?;
        self.register_subset_sum_smul_theorem()?;
        self.register_rat_pow_nat()?;
        self.register_noise_density_w()?;
        self.register_subset_sum_chi_pair_diag()?;
        self.register_subset_sum_subset_diag_extract_scaled()?;
        self.register_rat_pow_nat_mul_base_theorem()?;
        self.register_rat_mul_mul_mul_comm_theorem()?;
        self.register_fin_sum_mul_sum_theorem()?; // legA: (Σ F)·(Σ G) = Σ Σ F·G
        {
            // `Fin.sum_congr` (legF, decoded δ-extraction over the outer S-sum).
            use super::nn_verify_fin_sum::FinSumConsts;
            let fc = FinSumConsts::new();
            self.register_fin_sum_congr(&fc)?;
        }
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?; // Rat.mul_comm, Rat.mul_assoc
        }
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = ComposeConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: compose_type(&c),
            value: compose_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_noise_density_w_compose_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_noise_density_w_compose()
            .expect("register_noise_density_w_compose");
        env.register_noise_density_w_compose().expect("idempotent");
        let name = Name::from_string("BoolAnalysis.noiseDensityW_compose");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("noiseDensityW_compose proof must check against its type");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "transitive axiom closure must be empty, got {:?}",
            env.axiom_deps(&name)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }
}
