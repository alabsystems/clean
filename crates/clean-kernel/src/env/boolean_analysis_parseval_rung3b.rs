// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parseval RUNG 3 (stage 3z) — the assembly: the unnormalized Parseval core.
//!
//! `BoolAnalysis.subsetSum_parseval_core : ∀ (n : Nat) (a : HCPoint n → Rat),
//!     subsetSum n (fun S =>
//!         Rat.mul (subsetSum n (fun x => Rat.mul (a x) (chi n S x)))
//!                 (subsetSum n (fun x => Rat.mul (a x) (chi n S x))))
//!       = Rat.mul (Rat.mk (Int.ofNat (Nat.pow 2 n)) 1)
//!                 (subsetSum n (fun x => Rat.mul (a x) (a x)))`
//!
//! Chains the landed RUNG-3 primitives (`subsetSum_sq_to_double`,
//! `subsetSum_swap`, `subsetSum_smul`, `subsetSum_congr`), the delta
//! (`subsetSum_chi_bilinear`), the Kronecker dichotomy (`prod_offdiag_eq_zero` /
//! `prod_diag_eq_cube`), and RUNG-2's `Fin.sum_diag_collapse`:
//!
//!   e0  LHS = Σ_S (Σ_x aχ_Sx)²
//!     →[sq_to_double]  Σ_S Σ_x Σ_y (aχ_Sx)(aχ_Sy)
//!     →[swap S↔x]      Σ_x Σ_S Σ_y (aχ_Sx)(aχ_Sy)
//!     →[swap S↔y]      Σ_x Σ_y Σ_S (aχ_Sx)(aχ_Sy)
//!     →[mmmc+smul+δ]   Σ_x Σ_y (a x·a y)·Π_i(1+pm(x i)pm(y i))
//!     →[diag-collapse] Σ_x (a x·a x)·2^n
//!     →[smul+comm]     2^n · Σ_x (a x·a x)
//!
//! Every cited lemma is constructive with an empty admitted-axiom closure, so
//! `subsetSum_parseval_core` is `ProofQuality::Constructive`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct CoreConsts {
    nat: Expr,
    rat: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    nat_pow: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_mul: Expr,
    rat_add: Expr,
    rat_one: Expr,
    hcpoint: Expr,
    hc_decode: Expr,
    chi: Expr,
    pm: Expr,
    subset_sum: Expr,
    subset_sum_congr: Expr,
    subset_sum_swap: Expr,
    subset_sum_smul: Expr,
    subset_sum_sq_to_double: Expr,
    subset_chi_bilinear: Expr,
    prod_offdiag: Expr,
    prod_diag_cube: Expr,
    fin: Expr,
    fin_prod: Expr,
    fin_sum: Expr,
    fin_sum_diag_collapse: Expr,
    rat_mmmc: Expr,
    rat_mul_comm: Expr,
    eq1: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
    false_c: Expr,
}

impl CoreConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            rat_mk: Expr::const_(Name::from_string("Rat.mk"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            hc_decode: Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]),
            chi: Expr::const_(Name::from_string("BoolAnalysis.chi"), vec![]),
            pm: Expr::const_(Name::from_string("BoolAnalysis.pm"), vec![]),
            subset_sum: Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            subset_sum_congr: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_congr"),
                vec![],
            ),
            subset_sum_swap: Expr::const_(Name::from_string("BoolAnalysis.subsetSum_swap"), vec![]),
            subset_sum_smul: Expr::const_(Name::from_string("BoolAnalysis.subsetSum_smul"), vec![]),
            subset_sum_sq_to_double: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_sq_to_double"),
                vec![],
            ),
            subset_chi_bilinear: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_chi_bilinear"),
                vec![],
            ),
            prod_offdiag: Expr::const_(
                Name::from_string("BoolAnalysis.prod_offdiag_eq_zero"),
                vec![],
            ),
            prod_diag_cube: Expr::const_(
                Name::from_string("BoolAnalysis.prod_diag_eq_cube"),
                vec![],
            ),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            fin_prod: Expr::const_(Name::from_string("Fin.prod"), vec![]),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            fin_sum_diag_collapse: Expr::const_(Name::from_string("Fin.sum_diag_collapse"), vec![]),
            rat_mmmc: Expr::const_(Name::from_string("Rat.mul_mul_mul_comm"), vec![]),
            rat_mul_comm: Expr::const_(Name::from_string("Rat.mul_comm"), vec![]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
            false_c: Expr::const_(Name::from_string("False"), vec![]),
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
    fn fsum(&self, n: Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n, g])
    }
    fn fprod(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_prod.clone(), [n.clone(), g])
    }
    fn chi_(&self, n: &Expr, s: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.chi.clone(), [n.clone(), s.clone(), x.clone()])
    }
    fn pm_(&self, b: Expr) -> Expr {
        Expr::app(self.pm.clone(), b)
    }
    fn hc_decode(&self, n: &Expr, j: &Expr) -> Expr {
        Expr::apps(self.hc_decode.clone(), [n.clone(), j.clone()])
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
    fn mmmc(&self, a: Expr, bb: Expr, cc: Expr, d: Expr) -> Expr {
        Expr::apps(self.rat_mmmc.clone(), [a, bb, cc, d])
    }
    fn mul_comm(&self, a: Expr, bb: Expr) -> Expr {
        Expr::apps(self.rat_mul_comm.clone(), [a, bb])
    }

    /// `g S x = a x · chi n S x`.
    fn g(&self, n: &Expr, a: &Expr, s: &Expr, x: &Expr) -> Expr {
        self.mul(Expr::app(a.clone(), x.clone()), self.chi_(n, s, x))
    }
    /// `fun (k : Fin n) => 1 + pm(x k)·pm(y k)` — Parseval product integrand.
    fn prod_int(&self, parent: &EnvDeclBuilder, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (k_id, k) = b.fresh_local(fin_n.clone());
        let pmx = self.pm_(Expr::app(x.clone(), k.clone()));
        let pmy = self.pm_(Expr::app(y.clone(), k.clone()));
        let body = Expr::apps(
            self.rat_add.clone(),
            [self.rat_one.clone(), self.mul(pmx, pmy)],
        );
        b.finish_child(b.mk_lam(k_id, BinderInfo::Default, fin_n, body))
    }
}

include!("boolean_analysis_parseval_rung3b_legs.rs");

impl Environment {
    /// Register `BoolAnalysis.subsetSum_parseval_core` — the unnormalized
    /// Parseval identity (RUNG-3 assembly). Kernel-checked, constructive.
    /// Idempotent.
    pub(crate) fn register_subset_sum_parseval_core_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_parseval_core");
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
        self.register_subset_sum_chi_bilinear_theorem()?;
        self.register_prod_offdiag_eq_zero()?;
        self.register_prod_diag_eq_cube()?;
        self.register_fin_sum_diag_collapse_theorem()?;
        self.register_rat_mul_mul_mul_comm_theorem()?;

        // Re-check idempotency: `init_boolean_analysis()` above runs the Parseval
        // retirement, which re-enters this very registration (the flag-guarded
        // path short-circuits the recursion). If so, the core is already present
        // and we must NOT add it twice.
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = CoreConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: core_type(&c),
            value: core_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::tc::TypeChecker;

    #[test]
    fn test_subset_sum_parseval_core_is_constructive_theorem() {
        let mut env = Environment::new();
        env.register_subset_sum_parseval_core_theorem()
            .expect("register_subset_sum_parseval_core_theorem");
        let n = Name::from_string("BoolAnalysis.subsetSum_parseval_core");
        let info = env.get_const(&n).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ty = tc
            .infer_type(&Expr::const_(n, vec![]))
            .expect("subsetSum_parseval_core should type-check");
    }
}
