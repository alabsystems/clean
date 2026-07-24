// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dual-HC `‖T_ρ g‖₂²` Parseval diagonalization (BUILD #2 of the noiseOp
//! semigroup campaign).
//!
//! ```text
//! BoolAnalysis.dualhc_W_eq_spectral :
//!   ∀ (n : Nat) (g : HCPoint n → Rat),
//!     subsetSum n (fun y => noiseOp third n g y · noiseOp third n g y)
//!       = cube n · subsetSum n (fun S => levelWt third n S · (A g S · A g S))
//! ```
//!
//! with `third := Rat.mk (Int.ofNat 1) 3` (the `hc24_at_third` ρ build),
//! `cube n := Rat.mk (Int.ofNat (Nat.pow 2 n)) 1`, and
//! `A g S := subsetSum n (fun x => g x · χ_S x)` the un-normalized Fourier
//! coefficient. `levelWt third n S = (third·third)^{|S|} = (1/9)^{|S|}` by
//! `levelWt_eq_powNat`, so the spectral weight is the textbook `ρ^{2|S|}` mass.
//!
//! ## Proof route (three landed/sibling bricks, chained by `Eq.trans`)
//!
//! ```text
//! E_lhs  Σ_y (T g y)²
//!   =[noise_self_adjoint_sq]   Σ_x g x · (T² g)(x)                     (R1 self-adjoint)
//!   =[W_self_adjoint_glue]     cube · Σ_x Σ_v (g x·g v)·dens(ρ²,x,v)   (semigroup glue)
//!   =[noise_spectral_level]    cube · Σ_S levelWt third n S · (A·A)    (Parseval)
//! ```
//!
//! The middle `W_self_adjoint_glue` lemma is the genuine new content: it folds
//! the doubly-applied operator `T²` into a single `ρ²` density via the cube-level
//! noise SEMIGROUP `noiseDensityW_compose` (BUILD #1), paying the matching `cube`
//! un-normalization. `noise_self_adjoint_sq` and `noise_spectral_level` are
//! landed Constructive Theorems with empty closure; `noiseDensityW_compose` is
//! BUILD #1 (same). So `dualhc_W_eq_spectral` is `ProofQuality::Constructive`,
//! EMPTY admitted-axiom closure. No axiom is added or removed.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the dual-HC W spectral chain. All `noiseOp` / `noiseDensityW`
/// / `subsetSum` / `levelWt` / `A` spellings are byte-for-byte the landed
/// `boolean_analysis_kkl_dualhc_glue.rs` / `boolean_analysis_kkl_levelsplit.rs` /
/// `boolean_analysis_noise_self_adjoint.rs` conventions, so the brick instances
/// stay def-eq to the chain endpoints.
struct WSpectralConsts {
    nat: Expr,
    rat: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    nat_pow: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_mul: Expr,
    hcpoint: Expr,
    noise_op: Expr,
    noise_density: Expr,
    level_wt: Expr,
    subset_sum: Expr,
    subset_sum_congr: Expr,
    subset_sum_smul: Expr,
    subset_sum_swap: Expr,
    noise_compose: Expr,
    noise_density_symm: Expr,
    chi: Expr,
    rat_mul_comm: Expr,
    rat_mul_assoc: Expr,
    eq1: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
}

impl WSpectralConsts {
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
            hcpoint: k("BoolAnalysis.HCPoint"),
            noise_op: k("BoolAnalysis.noiseOp"),
            noise_density: k("BoolAnalysis.noiseDensityW"),
            level_wt: k("BoolAnalysis.levelWt"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            subset_sum_congr: k("BoolAnalysis.subsetSum_congr"),
            subset_sum_smul: k("BoolAnalysis.subsetSum_smul"),
            subset_sum_swap: k("BoolAnalysis.subsetSum_swap"),
            noise_compose: k("BoolAnalysis.noiseDensityW_compose"),
            noise_density_symm: k("BoolAnalysis.noiseDensityW_symm"),
            chi: k("BoolAnalysis.chi"),
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
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
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
    fn three_nat(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.two_nat())
    }
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two_nat(), n.clone()])
    }
    /// `cube n := Rat.mk (Int.ofNat (2^n)) 1`.
    fn cube(&self, n: &Expr) -> Expr {
        let ofnat = Expr::app(self.int_of_nat.clone(), self.pow2(n));
        Expr::apps(self.rat_mk.clone(), [ofnat, self.one_nat()])
    }
    /// `third := Rat.mk (Int.ofNat 1) 3` — byte-for-byte `rho_third`/`hc24_at_third`.
    fn third(&self) -> Expr {
        let ofnat = Expr::app(self.int_of_nat.clone(), self.one_nat());
        Expr::apps(self.rat_mk.clone(), [ofnat, self.three_nat()])
    }

    /// `noiseOp ρ n g`.
    fn op(&self, rho: &Expr, n: &Expr, g: &Expr) -> Expr {
        Expr::apps(self.noise_op.clone(), [rho.clone(), n.clone(), g.clone()])
    }
    /// `noiseDensityW ρ n x y`.
    fn dens(&self, rho: &Expr, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        Expr::apps(
            self.noise_density.clone(),
            [rho.clone(), n.clone(), x.clone(), y.clone()],
        )
    }
    /// `levelWt ρ n S`.
    fn level_wt(&self, rho: &Expr, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.level_wt.clone(), [rho.clone(), n.clone(), s.clone()])
    }
    /// `χ n S x`.
    fn chi_(&self, n: &Expr, s: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.chi.clone(), [n.clone(), s.clone(), x.clone()])
    }
    /// `A a S := subsetSum n (fun x => a x · χ_S x)` — byte-for-byte `a_coeff`.
    fn a_coeff(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr, s: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = self.mul(Expr::app(a.clone(), x.clone()), self.chi_(n, s, &x));
        let f = b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body));
        self.ssum(n, f)
    }

    // ── named bricks ─────────────────────────────────────────────────────────
    /// `subsetSum_congr n G H hyp : subsetSum n G = subsetSum n H`.
    fn ss_congr(&self, n: &Expr, g: &Expr, h: &Expr, hyp: Expr) -> Expr {
        Expr::apps(
            self.subset_sum_congr.clone(),
            [n.clone(), g.clone(), h.clone(), hyp],
        )
    }
    /// `subsetSum_smul n c f : Σ_S c·(f S) = c·Σ_S f S`.
    fn ss_smul(&self, n: &Expr, cc: &Expr, f: &Expr) -> Expr {
        Expr::apps(
            self.subset_sum_smul.clone(),
            [n.clone(), cc.clone(), f.clone()],
        )
    }
    /// `subsetSum_swap n f : Σ_a Σ_b f a b = Σ_b Σ_a f a b`.
    fn ss_swap(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.subset_sum_swap.clone(), [n.clone(), f.clone()])
    }
    /// `noiseDensityW_compose ρ n x z : Σ_w dens(ρ,x,w)·dens(ρ,w,z) = cube·dens(ρ²,x,z)`.
    fn compose(&self, rho: &Expr, n: &Expr, x: &Expr, z: &Expr) -> Expr {
        Expr::apps(
            self.noise_compose.clone(),
            [rho.clone(), n.clone(), x.clone(), z.clone()],
        )
    }
    /// `noiseDensityW_symm ρ n x y : dens(ρ,x,y) = dens(ρ,y,x)`.
    fn dens_symm(&self, rho: &Expr, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        Expr::apps(
            self.noise_density_symm.clone(),
            [rho.clone(), n.clone(), x.clone(), y.clone()],
        )
    }
    /// `Rat.mul_comm a b`.
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

include!("boolean_analysis_dualhc_w_spectral_glue.rs");

impl Environment {
    /// Register `BoolAnalysis.dualhc_W_eq_spectral` — the dual-HC `‖T_{1/3} g‖₂²`
    /// Parseval diagonalization (BUILD #2). Kernel-checked, `Constructive`, EMPTY
    /// admitted-axiom closure. Idempotent.
    pub(crate) fn register_dualhc_w_eq_spectral(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.dualhc_W_eq_spectral");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_subset_sum_smul_theorem()?;
        self.register_subset_sum_swap_theorem()?;
        self.register_noise_op()?;
        self.register_noise_self_adjoint_sq()?;
        self.register_noise_spectral_level()?;
        self.register_noise_density_w_compose()?;
        self.register_noise_density_w_symm()?;
        self.register_level_wt()?;
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?; // Rat.mul_comm, Rat.mul_assoc
        }
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = WSpectralConsts::new();
        // First register the semigroup glue lemma it consumes.
        self.register_w_self_adjoint_glue()?;
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: w_spectral_type(&c),
            value: w_spectral_value(&c),
        })
    }

    /// Register `BoolAnalysis.W_self_adjoint_glue` — the semigroup glue
    /// `Σ_x g x·(T² g)(x) = cube · Σ_x Σ_v (g x·g v)·dens(ρ²,x,v)`. See module docs.
    /// Kernel-checked, `Constructive`, EMPTY closure. Idempotent.
    pub(crate) fn register_w_self_adjoint_glue(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.W_self_adjoint_glue");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_subset_sum_smul_theorem()?;
        self.register_subset_sum_swap_theorem()?;
        self.register_noise_op()?;
        self.register_noise_density_w()?;
        self.register_noise_density_w_compose()?;
        self.register_noise_density_w_symm()?;
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?;
        }
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = WSpectralConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: glue_type(&c),
            value: glue_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn assert_constructive(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "{name} must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "{name} closure must be empty, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_dualhc_w_eq_spectral_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_dualhc_w_eq_spectral()
            .expect("register_dualhc_w_eq_spectral");
        env.register_dualhc_w_eq_spectral().expect("idempotent");
        assert_constructive(&env, "BoolAnalysis.W_self_adjoint_glue");
        assert_constructive(&env, "BoolAnalysis.dualhc_W_eq_spectral");
    }
}
