// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Noise campaign RUNG 5 — the un-normalized ρ-weighted spectral identity.
//!
//! `BoolAnalysis.noise_spectral_core : ∀ (ρ : Rat) (n : Nat) (a : HCPoint n → Rat),
//!     subsetSum n (fun x => subsetSum n (fun y =>
//!         Rat.mul (Rat.mul (a x) (a y)) (noiseDensityW ρ n x y)))
//!       = subsetSum n (fun S =>
//!           Rat.mul (Rat.powNat ρ (pc n S))
//!                   (Rat.mul (subsetSum n (fun x => Rat.mul (a x) (chi n S x)))
//!                            (subsetSum n (fun x => Rat.mul (a x) (chi n S x)))))`
//!
//! With `A(S) := Σ_x a(x)·χ_S(x)` this is `Σ_x Σ_y a(x)·a(y)·noiseDensityW ρ n x y
//! = Σ_S ρ^{|S|}·A(S)²`. Substituting `a := fun x => pm (f x)` gives the
//! textbook noise-stability Fourier expansion `Σ_S ρ^{|S|}·f̂(S)²` (up to the
//! `2^n`-per-coordinate normalization deferred to a later run); `A(S) = 2^n·f̂(S)`.
//!
//! This is PURE FUBINI — the same shape as `subsetSum_parseval_core`
//! (`boolean_analysis_parseval_rung3b.rs`) but STRICTLY EASIER: there is no
//! Kronecker dichotomy and no diagonal collapse. The `ρ^{|S|}` weight rides the
//! `S`-sum throughout (it is constant w.r.t. the inner `x,y` cube sums, so
//! `subsetSum_smul` pulls it in/out of those inner sums under `subsetSum_congr`):
//!
//!   e_rhs Σ_S w_S·((Σ_x g_Sx)·(Σ_x g_Sx))   [g_Sx := a x·χ_S x, w_S := ρ^{|S|}]
//!     →[congr·sq_to_double]  Σ_S w_S·(Σ_x Σ_y g_Sx·g_Sy)
//!     →[congr·smul²]         Σ_S (Σ_x Σ_y w_S·(g_Sx·g_Sy))
//!     →[swap S↔x]            Σ_x Σ_S Σ_y w_S·(g_Sx·g_Sy)
//!     →[congr·swap S↔y]      Σ_x Σ_y Σ_S w_S·(g_Sx·g_Sy)
//!     →[congr²·mmmc+smul]    Σ_x Σ_y (a x·a y)·Σ_S w_S·(χ_Sx·χ_Sy)
//!     ≡[noiseDensityW δ]     Σ_x Σ_y (a x·a y)·noiseDensityW ρ n x y    = e_lhs
//!
//! The final `≡` is definitional: `noiseDensityW ρ n x y` (reducible) δ-unfolds to
//! `subsetSum n (fun S => ρ^{|S|}·(χ_S x·χ_S y))`, byte-for-byte the inner
//! `S`-sum of the previous line. Every cited lemma is constructive with an empty
//! admitted-axiom closure, so `noise_spectral_core` is `ProofQuality::Constructive`.
//! No axiom is added or removed.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct SpectralConsts {
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    rat_mul: Expr,
    hcpoint: Expr,
    chi: Expr,
    pow_nat: Expr,
    subset_sum: Expr,
    subset_sum_congr: Expr,
    subset_sum_swap: Expr,
    subset_sum_smul: Expr,
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    subset_sum_sq_to_double: Expr,
    noise_density: Expr,
    fin: Expr,
    rat_mmmc: Expr,
    eq1: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
}

impl SpectralConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            chi: Expr::const_(Name::from_string("BoolAnalysis.chi"), vec![]),
            pow_nat: Expr::const_(Name::from_string("Rat.powNat"), vec![]),
            subset_sum: Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            subset_sum_congr: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_congr"),
                vec![],
            ),
            subset_sum_swap: Expr::const_(Name::from_string("BoolAnalysis.subsetSum_swap"), vec![]),
            subset_sum_smul: Expr::const_(Name::from_string("BoolAnalysis.subsetSum_smul"), vec![]),
            #[cfg(test)]
            subset_sum_sq_to_double: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_sq_to_double"),
                vec![],
            ),
            noise_density: Expr::const_(Name::from_string("BoolAnalysis.noiseDensityW"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            rat_mmmc: Expr::const_(Name::from_string("Rat.mul_mul_mul_comm"), vec![]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
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
    fn congr(&self, a: Expr, b: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, g, h],
        )
    }
    fn mmmc(&self, a: Expr, bb: Expr, cc: Expr, d: Expr) -> Expr {
        Expr::apps(self.rat_mmmc.clone(), [a, bb, cc, d])
    }

    /// `indNat (S i) = @Bool.rec.{1} (fun _ => Nat) 0 1 (S i)` — per-bit popcount
    /// summand, byte-for-byte the `NoiseConsts::ind_nat` build.
    fn ind_nat(&self, s_i: Expr) -> Expr {
        let nat_one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
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
    /// `pc n S = Fin.sumNat n (fun i => indNat (S i))` — the popcount `|S|`,
    /// byte-for-byte the `NoiseConsts::popcount` build (so `w S` is def-eq to
    /// the `noiseDensityW` weight).
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
    /// `w S = ρ^{pc n S}` — the per-subset ρ-weight.
    fn weight(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, s: &Expr) -> Expr {
        self.pow(rho, &self.popcount(parent, n, s))
    }
    /// `g S x = a x · χ_S x` — the Fourier integrand.
    fn g(&self, n: &Expr, a: &Expr, s: &Expr, x: &Expr) -> Expr {
        self.mul(Expr::app(a.clone(), x.clone()), self.chi_(n, s, x))
    }
    fn noise_density(&self, rho: &Expr, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        Expr::apps(
            self.noise_density.clone(),
            [rho.clone(), n.clone(), x.clone(), y.clone()],
        )
    }
}

include!("boolean_analysis_noise_spectral_legs.rs");

impl Environment {
    /// Register `BoolAnalysis.noise_spectral_core` — the un-normalized ρ-weighted
    /// spectral (Fubini) identity `Σ_x Σ_y a(x)a(y)·noiseDensityW ρ n x y
    /// = Σ_S ρ^{|S|}·A(S)²` (noise campaign rung 5). Kernel-checked, constructive
    /// (empty admitted-axiom closure). Idempotent.
    pub(crate) fn register_noise_spectral_core_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.noise_spectral_core");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_subset_sum_swap_theorem()?;
        self.register_subset_sum_smul_theorem()?;
        self.register_subset_sum_sq_to_double_theorem()?;
        self.register_rat_pow_nat()?;
        self.register_noise_density_w()?;
        self.register_rat_mul_mul_mul_comm_theorem()?;
        // `Rat.mul_assoc` / `Rat.mul_comm` are referenced directly in the
        // per-S regroup legs (idempotent quotient structural lemmas).
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?;
        }

        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = SpectralConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: spectral_type(&c),
            value: spectral_value(&c),
        })
    }

    /// Build the `noise_spectral_core` conclusion `Eq` at fixed `ρ, n, a` (the
    /// coefficient `a : HCPoint n → Rat`):
    /// `Σ_x Σ_y (a x·a y)·noiseDensityW ρ n x y = Σ_S ρ^{|S|}·A(S)²`.
    ///
    /// Reuses the exact `spectral_type` builders, so for `a := fun x => pm (f x)`
    /// the result is byte-for-byte the conclusion of
    /// `noise_spectral_core ρ n (fun x => pm (f x))`. Exposed so the
    /// `noise_stability_fourier` retirement can carry this genuine spectral
    /// statement as a reducible `Eq` helper Definition (over the `noiseDensityW`
    /// carrier — see `noiseDensityW_eq_prod` for the textbook-density anchor).
    pub(crate) fn noise_spectral_body_eq(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        a: &Expr,
    ) -> Expr {
        let c = SpectralConsts::new();
        let lhs = c.ssum(n, c.lhs_x_fn(parent, rho, n, a));
        let rhs = c.ssum(n, c.rhs_s_fn(parent, rho, n, a));
        c.eq_rat(lhs, rhs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_noise_spectral_core_is_constructive_theorem() {
        let mut env = Environment::new();
        env.register_noise_spectral_core_theorem()
            .expect("register_noise_spectral_core_theorem");
        let n = Name::from_string("BoolAnalysis.noise_spectral_core");
        let info = env.get_const(&n).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("noise_spectral_core proof must check against its type");
        assert_eq!(
            env.proof_quality(&n),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&n).expect("deps").is_empty(),
            "transitive axiom closure must be empty"
        );
    }
}
