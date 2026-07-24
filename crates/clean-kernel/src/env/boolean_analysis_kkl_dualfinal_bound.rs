// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual `(4/3→2)` bound — Stage C-3, the **applyT spectral-square identity**
//! (design `2026-06-18-kkl-real-sqrt-layer-plan.md` §10.9, STEP 2 — the HONEST,
//! `2^n`-faithful normalized-contraction precursor).
//!
//! # The theorem
//!
//! ```text
//! BoolAnalysis.applyT_two_norm_sq_spectral :
//!   ∀ (ρ : Rat) (n : Nat) (g : HCPoint n → Rat),
//!     (2^n) · subsetSum n (fun x => applyT ρ n g x · applyT ρ n g x)   -- 2^n·Σ_x sq(applyT(ρ)g)
//!       = subsetSum n (fun S =>                                        -- = Σ_S (2^n·ρ^{|S|}·A_g(S))²
//!           ((2^n · powNat ρ |S|) · A_g(S)) · ((2^n · powNat ρ |S|) · A_g(S)))
//! ```
//!
//! with `A_g(S) := subsetSum n (fun x => g x · χ_S x)`. Combining the landed
//! Parseval core (`subsetSum_parseval_core`: `Σ_S A_a(S)² = 2^n·Σ_x sq(a x)`) at
//! `a := applyT ρ n g` with the STEP-1 coefficient law (`applyT_coeff_eq`:
//! `A_{applyT(ρ)g}(S) = 2^n·ρ^{|S|}·A_g(S)`), this is the EXACT spectral content of
//! the operator 2-norm — with EVERY `2^n` tracked.
//!
//! # The `2^n` normalization (design §10.9 — read carefully)
//!
//! `applyT` is the UN-normalized operator (`applyT(ρ)g = 2^n·(T_ρ g)`), so its
//! spatial 2-norm is amplified by `2^{2n}`:
//! ```text
//!   2^n·Σ_x sq(applyT(ρ)g x)  =  Σ_S A_{applyT(ρ)g}(S)²   [Parseval at applyT(ρ)g]
//!                             =  Σ_S (2^n·ρ^{|S|}·A_g(S))²  [STEP 1, per-S]
//!                             =  2^{2n}·Σ_S ρ^{2|S|}·A_g(S)².
//! ```
//! This identity is TRUE and `2^n`-faithful; the FALSE shortcut
//! `Σ_x sq(applyT(ρ)g x) ≤ Σ_x sq(g x)` (the un-normalized spatial contraction,
//! §10.9) is NOT registered. The genuine contraction lives at the SPECTRAL /
//! `Expect`-normalized level (`spectral_level_two_norm_contraction`): termwise
//! `ρ^{2|S|}·A_g(S)² ≤ A_g(S)²` for `ρ² ≤ 1`. Multiplying THIS identity's RHS by
//! that contraction (and the Parseval identity at `a := g`,
//! `Σ_S A_g(S)² = 2^n·Σ_x sq(g x)`) gives the `2^{2n}`-faithful spatial relation
//! `2^n·Σ_x sq(applyT(ρ)g x) ≤ 2^{2n}·Σ_x sq(g x)` — NOT the false un-normalized
//! `≤ Σ_x sq(g x)`. Closing the dual bound on the NORMALIZED operator
//! (`z := T_ρ g = applyT(ρ)g / 2^n`, `count := Inf = (Σ X)/2^n`) requires the
//! `Expect`-level `Rat`-division-by-`2^n` normalization to thread through the
//! pairing (`applyT_pairing_eq_two_norm`) and `dual_m2_for_seq` — design §10.9
//! residual (b), NOT yet expressible axiom-free; see the module-level report.
//!
//! # Proof (constructive, empty admitted-axiom closure)
//!
//! `Eq.trans` of two legs:
//! 1. `Eq.symm (subsetSum_parseval_core n (applyT ρ n g))` :
//!    `2^n·Σ_x sq(applyT(ρ)g x) = Σ_S A_{applyT(ρ)g}(S)²`.
//! 2. `Fin.sum_congr (2^n) Fmid Frhs h` (lifting the per-decoded-`jS` squared
//!    STEP-1 law `congrArg (·²) (applyT_coeff_eq ρ n g jS)`), since
//!    `subsetSum n F ≡ Fin.sum (2^n) (F ∘ hcDecode)` (reducible δ) makes the
//!    `S`-sums def-eq to the decoded `Fin.sum`s — avoiding the absent `hcEncode`.
//!
//! Every leaf (`subsetSum_parseval_core`, `applyT_coeff_eq`, `Fin.sum_congr`,
//! `congrArg`, `Eq.symm`, `Eq.trans`) is `Constructive` with empty admitted-axiom
//! closure, so this identity is too. No axiom is added or removed.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached atoms for the applyT spectral-square identity.
struct BoundConsts {
    nat: Expr,
    rat: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    nat_pow: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_mul: Expr,
    pow_nat: Expr,
    set_size_nat: Expr,
    hcpoint: Expr,
    hc_decode: Expr,
    chi: Expr,
    applyt: Expr,
    subset_sum: Expr,
    parseval_core: Expr,
    applyt_coeff_eq: Expr,
    fin: Expr,
    fin_sum_congr: Expr,
    eq1: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
}

impl BoundConsts {
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
            pow_nat: k("Rat.powNat"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            hc_decode: k("BoolAnalysis.hcDecode"),
            chi: k("BoolAnalysis.chi"),
            applyt: k("BoolAnalysis.applyT"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            parseval_core: k("BoolAnalysis.subsetSum_parseval_core"),
            applyt_coeff_eq: k("BoolAnalysis.applyT_coeff_eq"),
            fin: k("Fin"),
            fin_sum_congr: k("Fin.sum_congr"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
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
    fn applyt(&self, rho: &Expr, n: &Expr, g: &Expr, x: &Expr) -> Expr {
        Expr::apps(
            self.applyt.clone(),
            [rho.clone(), n.clone(), g.clone(), x.clone()],
        )
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

    /// `A_g(S) := subsetSum n (fun x => g x · χ_S x)` — byte-for-byte the
    /// Parseval / STEP-1 coefficient shape.
    fn a_coeff(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr, s: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = self.mul(Expr::app(g.clone(), x.clone()), self.chi_(n, s, &x));
        let f = b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body));
        self.ssum(n, f)
    }
    /// `(2^n · ρ^{|S|}) · A_g(S)` — STEP 1's RHS coefficient.
    fn coeff(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, g: &Expr, s: &Expr) -> Expr {
        let scale = self.mul(self.cube(n), self.pow(rho, &self.set_size(n, s)));
        self.mul(scale, self.a_coeff(parent, n, g, s))
    }
    /// `fun x => applyT ρ n g x · applyT ρ n g x` — the spatial 2-norm integrand.
    fn applyt_sq_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, g: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let at = self.applyt(rho, n, g, &x);
        let body = self.mul(at.clone(), at);
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `fun S => coeff(S)·coeff(S)` (RHS `S`-integrand, free `S`).
    fn rhs_s_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, g: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let cf = self.coeff(&b, rho, n, g, &s);
        let body = self.mul(cf.clone(), cf);
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `fun S => A_{applyT(ρ)g}(S)·A_{applyT(ρ)g}(S)` — Parseval's LHS `S`-integrand
    /// (`a := applyT ρ n g`), free `S`. Byte-for-byte `subsetSum_parseval_core`'s
    /// `lhs_s_fn` at `a := applyT ρ n g`.
    fn mid_s_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, g: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let inner = {
            let mut xb = EnvDeclBuilder::child_of(&b);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let at = self.applyt(rho, n, g, &x);
            let body = self.mul(at, self.chi_(n, &s, &x));
            let f = xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body));
            self.ssum(n, f)
        };
        let body = self.mul(inner.clone(), inner);
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
}

include!("boolean_analysis_kkl_dualfinal_bound_proof.rs");

impl Environment {
    /// Register `BoolAnalysis.applyT_two_norm_sq_spectral` — the `2^n`-faithful
    /// operator 2-norm spectral identity `2^n·Σ_x sq(applyT(ρ)g) = Σ_S (2^n·ρ^{|S|}
    /// ·A_g(S))²` (STEP 2). Kernel-checked, `ProofQuality::Constructive`, empty
    /// admitted-axiom closure. Idempotent.
    pub fn register_applyt_two_norm_sq_spectral(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.applyT_two_norm_sq_spectral");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_applyt_coeff_eq()?; // STEP 1 (+ applyT, subsetSum, …)
        self.register_subset_sum_parseval_core_theorem()?;
        self.init_fin_sum()?; // Fin.sum_congr
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = BoundConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: bound_type(&c),
            value: bound_value(&c),
        })
    }

    /// Init hook for the applyT spectral-square (STEP 2) overlay module.
    pub fn init_boolean_analysis_kkl_dualfinal_bound(&mut self) -> Result<(), EnvError> {
        self.register_applyt_two_norm_sq_spectral()
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
        env.init_boolean_analysis_kkl_dualfinal_bound()
            .expect("init_boolean_analysis_kkl_dualfinal_bound");
        env.init_boolean_analysis_kkl_dualfinal_bound()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_applyt_two_norm_sq_spectral_constructive() {
        let env = env();
        let nm = Name::from_string("BoolAnalysis.applyT_two_norm_sq_spectral");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let value = info.value.clone().expect("theorem value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("applyT_two_norm_sq_spectral proof must check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be foundational-only, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_applyt_two_norm_sq_spectral_not_refuted() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let info = env
            .get_const(&Name::from_string(
                "BoolAnalysis.applyT_two_norm_sq_spectral",
            ))
            .expect("registered");
        assert_eq!(
            refute_conjecture(&tc, &info.type_),
            None,
            "applyT_two_norm_sq_spectral is a TRUE 2^n-faithful identity; must NOT refute"
        );
    }
}
