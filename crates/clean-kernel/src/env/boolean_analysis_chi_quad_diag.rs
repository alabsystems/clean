// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Diagonal extraction for the 4-fold character orthogonality — sharp-KKL
//! roadmap RUNG 1 (`subsetSum_chi_quad_diag`, the diagonal-VALUE form).
//!
//! The on-branch `subsetSum_chi_quad_orthogonality`
//! (`boolean_analysis_chi_quad_orthogonality.rs`) FOLDS the 4-fold product to a
//! single character: `Σ_x (χ_{S1}·χ_{S2})·(χ_{S3}·χ_{S4}) = Σ_x χ_U` where
//! `U := (S1 Δ S2) Δ (S3 Δ S4)`. This module supplies the missing DIAGONAL
//! EXTRACTION — the evaluation of the single-character sum to its `2^n`-or-`0`
//! value — completing the roadmap's exact rung-1 statement
//!
//!   `subsetSum n (fun x => (χ_{S1}·χ_{S2})·(χ_{S3}·χ_{S4}))
//!      = 2^n · ind(U = ∅)`,
//!
//! with `ind(U = ∅)` rendered in the codebase-native indicator idiom
//! `ind (Nat.beq (setSizeNat n U) 0)` (the same encoding used by
//! `emptyset_mass_isolation` / `variance_eq_nonempty_mass`).
//!
//! ## New bricks (all kernel-checked, `Constructive`, empty admitted-axiom closure)
//!
//! 1. `chi_single_subsetSum_eq_prod` — the single-character sum collapses to the
//!    Kronecker product form:
//!      `subsetSum n (fun x => χ_U x) = Fin.prod n (fun i => 1 + pm(U i))`.
//!    Route: `χ_U x = χ_U x · χ_∅ x` (`chi_empty` ∘ `Rat.mul_one`-symm under
//!    `subsetSum_congr`), then the SIGN-side bilinear `subsetSum_chi_sign_bilinear`
//!    at `(U, ∅)` collapses `Σ_x χ_U·χ_∅` to `Π_i (1 + pm(U i)·pm(∅ i))`, whose
//!    integrand is def-eq to `1 + pm(U i)` (`pm(∅ i) = pm(false) ≡ 1`).
//!
//! This is the genuine new content of the diagonal extraction: it bridges the
//! folded single-character sum to the product form that the on-branch Kronecker
//! collapse (`prod_diag_eq_cube` on the diagonal, `prod_offdiag_eq_zero` off it)
//! evaluates to `2^n` or `0`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for the diagonal-extraction lemmas.
struct DiagConsts {
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    bool_false: Expr,
    #[cfg(test)]
    bool_xor: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    nat_beq: Expr,
    int_of_nat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_add: Expr,
    rat_mk: Expr,
    rat_mul_one: Expr,
    rat_mul_zero: Expr,
    pm: Expr,
    ind: Expr,
    bool_rec_nat: Expr,
    hcpoint: Expr,
    chi: Expr,
    fin: Expr,
    fin_prod: Expr,
    fin_prod_congr: Expr,
    set_size_nat: Expr,
    subset_sum: Expr,
    subset_sum_congr: Expr,
    sign_bilinear: Expr,
    chi_empty: Expr,
    prod_dichotomy: Expr,
    prod_diag_eq_two: Expr,
    prod_const_two_eq_pow: Expr,
    fin_sum_nat_const_zero_of: Expr,
    fin_sum_nat_eq_zero: Expr,
    indnat_eq_zero: Expr,
    nat_eq_of_beq: Expr,
    natcast_ne_zero: Expr,
    one_le_two_pow: Expr,
    #[cfg(test)]
    quad_ortho: Expr,
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    false_c: Expr,
    false_elim: Expr,
    or_c: Expr,
    or_rec: Expr,
    bool_cases_on: Expr,
    eq1: Expr,
    eq0: Expr,
    eq_refl: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
    congr_arg_nr: Expr,
    congr_arg_br: Expr,
}

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
impl DiagConsts {
    fn new() -> Self {
        let l0 = Level::zero();
        let l1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            bool_false: Expr::const_(Name::from_string("Bool.false"), vec![]),
            #[cfg(test)]
            bool_xor: Expr::const_(Name::from_string("Bool.xor"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            nat_beq: Expr::const_(Name::from_string("Nat.beq"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            rat_mk: Expr::const_(Name::from_string("Rat.mk"), vec![]),
            rat_mul_one: Expr::const_(Name::from_string("Rat.mul_one"), vec![]),
            rat_mul_zero: Expr::const_(Name::from_string("Rat.mul_zero"), vec![]),
            pm: Expr::const_(Name::from_string("BoolAnalysis.pm"), vec![]),
            ind: Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]),
            bool_rec_nat: Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            chi: Expr::const_(Name::from_string("BoolAnalysis.chi"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            fin_prod: Expr::const_(Name::from_string("Fin.prod"), vec![]),
            fin_prod_congr: Expr::const_(Name::from_string("Fin.prod_congr"), vec![]),
            set_size_nat: Expr::const_(Name::from_string("BoolAnalysis.setSizeNat"), vec![]),
            subset_sum: Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            subset_sum_congr: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_congr"),
                vec![],
            ),
            sign_bilinear: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_chi_sign_bilinear"),
                vec![],
            ),
            chi_empty: Expr::const_(Name::from_string("BoolAnalysis.chi_empty"), vec![]),
            prod_dichotomy: Expr::const_(
                Name::from_string("BoolAnalysis.prod_factor_zero_or_pointwise_eq"),
                vec![],
            ),
            prod_diag_eq_two: Expr::const_(
                Name::from_string("BoolAnalysis.prod_diag_eq_two"),
                vec![],
            ),
            prod_const_two_eq_pow: Expr::const_(
                Name::from_string("BoolAnalysis.prod_const_two_eq_pow"),
                vec![],
            ),
            fin_sum_nat_const_zero_of: Expr::const_(
                Name::from_string("Fin.sumNat_const_zero_of"),
                vec![],
            ),
            fin_sum_nat_eq_zero: Expr::const_(Name::from_string("Fin.sumNat_eq_zero"), vec![]),
            indnat_eq_zero: Expr::const_(Name::from_string("BoolAnalysis.indNat_eq_zero"), vec![]),
            nat_eq_of_beq: Expr::const_(Name::from_string("Nat.eq_of_beq_eq_true"), vec![]),
            natcast_ne_zero: Expr::const_(Name::from_string("Rat.natCast_ne_zero_of_pos"), vec![]),
            one_le_two_pow: Expr::const_(Name::from_string("Nat.one_le_two_pow"), vec![]),
            #[cfg(test)]
            quad_ortho: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_chi_quad_orthogonality"),
                vec![],
            ),
            #[cfg(test)]
            false_c: Expr::const_(Name::from_string("False"), vec![]),
            false_elim: Expr::const_(Name::from_string("False.elim"), vec![l0.clone()]),
            or_c: Expr::const_(Name::from_string("Or"), vec![]),
            or_rec: Expr::const_(Name::from_string("Or.rec"), vec![]),
            // Bool.casesOn eliminating into a Prop motive (Sort 0).
            bool_cases_on: Expr::const_(Name::from_string("Bool.casesOn"), vec![l0.clone()]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq0: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            // congrArg with domain Nat (level 1), codomain Rat (level 1).
            congr_arg_nr: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            // congrArg with domain Bool (level 1), codomain Rat (level 1).
            congr_arg_br: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
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
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn pm_(&self, b: Expr) -> Expr {
        Expr::app(self.pm.clone(), b)
    }
    fn chi_(&self, n: &Expr, s: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.chi.clone(), [n.clone(), s.clone(), x.clone()])
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn fprod(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_prod.clone(), [n.clone(), g])
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
    /// `@congrArg.{1,1} Rat Rat a b g h : g a = g b`.
    fn congr(&self, a: Expr, b: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, g, h],
        )
    }

    /// `∅ : HCPoint n := fun (_ : Fin n) => Bool.false` — the all-false subset.
    fn empty_fn(&self, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, _i) = b.fresh_local(fin_n.clone());
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, self.bool_false.clone()))
    }

    /// `fun (x : HCPoint n) => χ_U(x)` — the single-character integrand.
    fn chi_single_fn(&self, parent: &EnvDeclBuilder, n: &Expr, u: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = self.chi_(n, u, &x);
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }

    /// `fun (x : HCPoint n) => χ_U(x)·χ_∅(x)` — the character-vs-empty pair
    /// integrand, the `subsetSum_chi_sign_bilinear` LHS at `(U, ∅)`.
    fn chi_pair_empty_fn(&self, parent: &EnvDeclBuilder, n: &Expr, u: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let empty = self.empty_fn(&b, n);
        let body = self.mul(self.chi_(n, u, &x), self.chi_(n, &empty, &x));
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }

    /// `fun (i : Fin n) => 1 + pm(U i)·pm(∅ i)` — `subsetSum_chi_sign_bilinear`'s
    /// RHS integrand at `(U, ∅)`. Def-eq to `1 + pm(U i)` (`pm(∅ i) = pm(false)
    /// ≡ Rat.one`), but kept in the bilinear's exact spelling so the bilinear
    /// applies syntactically.
    fn prod_pair_empty_fn(&self, parent: &EnvDeclBuilder, n: &Expr, u: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let empty = self.empty_fn(&b, n);
        let pm_u = self.pm_(Expr::app(u.clone(), i.clone()));
        let pm_e = self.pm_(Expr::app(empty, i.clone()));
        let body = self.add(self.rat_one.clone(), self.mul(pm_u, pm_e));
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }

    // ── diagonal-value (2^n · ind) atoms ──

    fn one_nat(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.nat_zero.clone())
    }
    fn two_nat(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.one_nat())
    }
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two_nat(), n.clone()])
    }
    /// `Rat.mk (Int.ofNat (2^n)) 1` — the rational `2^n` (= `natCast (2^n)`).
    fn cube(&self, n: &Expr) -> Expr {
        let ofnat = Expr::app(self.int_of_nat.clone(), self.pow2(n));
        Expr::apps(self.rat_mk.clone(), [ofnat, self.one_nat()])
    }
    fn ind_of(&self, b: Expr) -> Expr {
        Expr::app(self.ind.clone(), b)
    }
    /// `Nat.beq m Nat.zero`.
    fn beq0(&self, m: Expr) -> Expr {
        Expr::apps(self.nat_beq.clone(), [m, self.nat_zero.clone()])
    }
    /// `setSizeNat n U`.
    fn ss_nat(&self, n: &Expr, u: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), u.clone()])
    }
    /// `ind (Nat.beq (setSizeNat n U) 0)` — the empty-set indicator `ind(U=∅)`.
    fn empty_ind(&self, n: &Expr, u: &Expr) -> Expr {
        self.ind_of(self.beq0(self.ss_nat(n, u)))
    }
    #[cfg(test)]
    fn xor(&self, a: Expr, bb: Expr) -> Expr {
        Expr::apps(self.bool_xor.clone(), [a, bb])
    }
    #[cfg(test)]
    fn eq_nat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.nat.clone(), l, r])
    }
    fn eq_bool(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq0.clone(), [self.bool_.clone(), l, r])
    }
    #[cfg(test)]
    fn trans_nat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.nat.clone(), a, b, cc, h1, h2])
    }
    /// `@congrArg Nat Rat a b g h : g a = g b`.
    fn congr_nr(&self, a: Expr, b: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg_nr.clone(),
            [self.nat.clone(), self.rat.clone(), a, b, g, h],
        )
    }
    /// `@congrArg Bool Rat a b g h : g a = g b`.
    fn congr_br(&self, a: Expr, b: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg_br.clone(),
            [self.bool_.clone(), self.rat.clone(), a, b, g, h],
        )
    }

    /// `indNat b = @Bool.rec (fun _ => Nat) Nat.zero (Nat.succ Nat.zero) b` — the
    /// `setSizeNat` summand (the `Nat` indicator).
    fn ind_nat_of(&self, b: Expr) -> Expr {
        let nat_motive = Expr::lam(BinderInfo::Default, self.bool_.clone(), self.nat.clone());
        Expr::apps(
            self.bool_rec_nat.clone(),
            [nat_motive, self.nat_zero.clone(), self.one_nat(), b],
        )
    }
    /// `fun (i : Fin n) => indNat (U i)` — the `setSizeNat` summand function.
    fn ind_nat_fn(&self, parent: &EnvDeclBuilder, n: &Expr, u: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let body = self.ind_nat_of(Expr::app(u.clone(), i.clone()));
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }

    /// `fun (i : Fin n) => Rat.one + Rat.one` — the constant-2 factor function.
    fn const_two_fn(&self, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, _i) = b.fresh_local(fin_n.clone());
        let body = self.add(self.rat_one.clone(), self.rat_one.clone());
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }

    /// `fun (i : Fin n) => 1 + pm(∅ i)·pm(∅ i)` — `prod_diag_eq_two`'s LHS
    /// integrand at `x := ∅` (the all-false diagonal).
    fn prod_empty_diag_fn(&self, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let empty = self.empty_fn(&b, n);
        let pm_e = self.pm_(Expr::app(empty, i.clone()));
        let body = self.add(self.rat_one.clone(), self.mul(pm_e.clone(), pm_e));
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }

    /// `Fin.prod_congr n f g pw : Fin.prod n f = Fin.prod n g`.
    fn prod_congr(&self, n: &Expr, f: Expr, g: Expr, pw: Expr) -> Expr {
        Expr::apps(self.fin_prod_congr.clone(), [n.clone(), f, g, pw])
    }
}

// ===========================================================================
// chi_single_subsetSum_eq_prod — single-character sum to product form.
// ===========================================================================

/// `∀ (n : Nat) (U : HCPoint n),
///   subsetSum n (fun x => χ_U(x))
///     = Fin.prod n (fun i => 1 + pm(U i)·pm(∅ i))`.
///
/// The RHS is kept in the SIGN-bilinear's exact `(U, ∅)` pair spelling — that is
/// precisely the Kronecker product form `1 + pm(x i)·pm(y i)` the on-branch
/// `prod_diag_eq_cube` / `prod_offdiag_eq_zero` collapse to `2^n` / `0`.
fn reduce_type(c: &DiagConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (u_id, u) = b.fresh_local(hcp.clone());
    let lhs = c.ssum(&n, c.chi_single_fn(&b, &n, &u));
    let rhs = c.fprod(&n, c.prod_pair_empty_fn(&b, &n, &u));
    let concl = c.eq_rat(lhs, rhs);
    let r = b.mk_pi(u_id, BinderInfo::Default, hcp, concl);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

fn reduce_value(c: &DiagConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (u_id, u) = b.fresh_local(hcp.clone());

    let chi_single = c.chi_single_fn(&b, &n, &u);
    let chi_pair = c.chi_pair_empty_fn(&b, &n, &u);
    let prod_pair = c.prod_pair_empty_fn(&b, &n, &u);

    let ss_single = c.ssum(&n, chi_single.clone());
    let ss_pair = c.ssum(&n, chi_pair.clone());
    let fp_pair = c.fprod(&n, prod_pair.clone());

    // leg1 : subsetSum n (χ_U) = subsetSum n (χ_U·χ_∅)
    //   subsetSum_congr n (χ_U) (χ_U·χ_∅) (fun x => symm (mul_one (χ_U x)) ∘ congr).
    //   Per-point: χ_U x = χ_U x · χ_∅ x. Since χ_∅ x ≡ ... (NOT def-eq for
    //   symbolic n), we go χ_U x = χ_U x · 1 (symm Rat.mul_one) then rewrite the
    //   `1` to `χ_∅ x` via chi_empty (symm).
    let leg1 = {
        let pointwise = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (x_id, x) = d.fresh_local(hcp.clone());
            let empty = c.empty_fn(&d, &n);
            let chi_u_x = c.chi_(&n, &u, &x);
            let chi_e_x = c.chi_(&n, &empty, &x);
            // mo : χ_U x · 1 = χ_U x   (Rat.mul_one (χ_U x))
            let mul_one = Expr::app(c.rat_mul_one.clone(), chi_u_x.clone());
            // m1 : χ_U x = χ_U x · 1   (symm)
            let chi_u_times_one = c.mul(chi_u_x.clone(), c.rat_one.clone());
            let m1 = c.symm(chi_u_times_one.clone(), chi_u_x.clone(), mul_one);
            // he : χ_∅ x = 1   (chi_empty n ∅ x (fun i => Eq.refl false))
            let hyp_proof = {
                let mut e = EnvDeclBuilder::child_of(&d);
                let fin_n = c.fin_of(&n);
                let (i_id, _i) = e.fresh_local(fin_n.clone());
                let refl_false = Expr::apps(
                    Expr::const_(
                        Name::from_string("Eq.refl"),
                        vec![Level::succ(Level::zero())],
                    ),
                    [c.bool_.clone(), c.bool_false.clone()],
                );
                e.finish_child(e.mk_lam(i_id, BinderInfo::Default, fin_n, refl_false))
            };
            let he = Expr::apps(
                c.chi_empty.clone(),
                [n.clone(), empty.clone(), x.clone(), hyp_proof],
            );
            // h_e_symm : 1 = χ_∅ x   (symm he)
            let h_e_symm = c.symm(chi_e_x.clone(), c.rat_one.clone(), he);
            // m2 : χ_U x · 1 = χ_U x · χ_∅ x   (congrArg (χ_U x ·) h_e_symm)
            let g_left = {
                let mut e = EnvDeclBuilder::child_of(&d);
                let (z_id, z) = e.fresh_local(c.rat.clone());
                let body = c.mul(chi_u_x.clone(), z);
                e.finish_child(e.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let m2 = c.congr(c.rat_one.clone(), chi_e_x.clone(), g_left, h_e_symm);
            // proof_x : χ_U x = χ_U x · χ_∅ x   (trans m1 m2)
            let chi_u_times_e = c.mul(chi_u_x.clone(), chi_e_x);
            let proof_x = c.trans(chi_u_x.clone(), chi_u_times_one, chi_u_times_e, m1, m2);
            d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp.clone(), proof_x))
        };
        Expr::apps(
            c.subset_sum_congr.clone(),
            [n.clone(), chi_single.clone(), chi_pair.clone(), pointwise],
        )
    };

    // leg2 : subsetSum n (χ_U·χ_∅) = Fin.prod n (1 + pm(U i)·pm(∅ i))
    //   subsetSum_chi_sign_bilinear n U ∅.
    let empty_top = c.empty_fn(&b, &n);
    let leg2 = Expr::apps(c.sign_bilinear.clone(), [n.clone(), u.clone(), empty_top]);
    // leg2's stated RHS `Fin.prod n (1 + pm(U i)·pm(∅ i))` is `fp_pair`.

    // proof : subsetSum n (χ_U) = Fin.prod n (1 + pm(U i)·pm(∅ i))
    //   trans leg1 leg2.
    let proof = c.trans(ss_single, ss_pair, fp_pair, leg1, leg2);

    let val = b.mk_lam(u_id, BinderInfo::Default, hcp, proof);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.chi_single_subsetSum_eq_prod`: the single-character
    /// cube sum collapses to the Kronecker product form,
    /// `∀ n U, subsetSum n (fun x => χ_U x)
    ///    = Fin.prod n (fun i => 1 + pm(U i)·pm(∅ i))`.
    ///
    /// Route: pad the single character with `χ_∅` (`χ_U = χ_U · χ_∅` per-point,
    /// `chi_empty` ∘ `Rat.mul_one`, under `subsetSum_congr`), then collapse the
    /// resulting pair sum with the SIGN-side bilinear `subsetSum_chi_sign_bilinear`
    /// at `(U, ∅)`. The bilinear's RHS `Fin.prod n (1 + pm(U i)·pm(∅ i))` is
    /// def-eq to the stated `Fin.prod n (1 + pm(U i))` (`pm(∅ i) = pm(false) ≡ 1`).
    /// This bridges the folded single-character sum (RUNG 1's
    /// `subsetSum_chi_quad_orthogonality` RHS) to the product form that the
    /// on-branch Kronecker collapse evaluates to `2^n` or `0`. Constructive, empty
    /// admitted-axiom closure. Idempotent.
    pub(crate) fn register_chi_single_subset_sum_eq_prod(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.chi_single_subsetSum_eq_prod");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?; // Rat.mul_one
        self.init_boolean_analysis()?; // chi, pm, Bool.false
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_subset_sum_chi_sign_bilinear_theorem()?;
        self.register_chi_empty()?;

        let c = DiagConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: reduce_type(&c),
            value: reduce_value(&c),
        })
    }
}

// ===========================================================================
// prod_pair_empty_eq_pow_ind — the (U, ∅) Kronecker product → 2^n·ind(U=∅).
// ===========================================================================

impl DiagConsts {
    /// Given `hagree : ∀ i, U i = ∅ i`, build a proof of
    /// `Fin.prod n (fun i => 1 + pm(U i)·pm(∅ i)) = cube n`:
    ///   congr (U → ∅ in the first slot) ∘ `prod_diag_eq_two n ∅` ∘
    ///   `prod_const_two_eq_pow n`.
    fn prod_eq_cube_of_agree(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        u: &Expr,
        hagree: &Expr,
    ) -> Expr {
        let prod_pair = self.prod_pair_empty_fn(parent, n, u);
        let prod_empty_diag = self.prod_empty_diag_fn(parent, n);
        let const_two = self.const_two_fn(parent, n);

        let fp_pair = self.fprod(n, prod_pair.clone());
        let fp_empty_diag = self.fprod(n, prod_empty_diag.clone());
        let fp_const_two = self.fprod(n, const_two.clone());
        let cube = self.cube(n);

        // pw : ∀ i, (1 + pm(U i)·pm(∅ i)) = (1 + pm(∅ i)·pm(∅ i))
        //   = fun i => congrArg (fun b => 1 + pm(b)·pm(∅ i)) (hagree i)
        let pw = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let fin_n = self.fin_of(n);
            let (i_id, i) = d.fresh_local(fin_n.clone());
            let empty = self.empty_fn(&d, n);
            let pm_e = self.pm_(Expr::app(empty.clone(), i.clone()));
            let u_i = Expr::app(u.clone(), i.clone());
            let e_i = Expr::app(empty, i.clone());
            // g : Bool → Rat := fun b => 1 + pm(b)·pm(∅ i)
            let g = {
                let mut e = EnvDeclBuilder::child_of(&d);
                let (b_id, bb) = e.fresh_local(self.bool_.clone());
                let body = self.add(self.rat_one.clone(), self.mul(self.pm_(bb), pm_e.clone()));
                e.finish_child(e.mk_lam(b_id, BinderInfo::Default, self.bool_.clone(), body))
            };
            let h_i = Expr::app(hagree.clone(), i.clone());
            let body = self.congr_br(u_i, e_i, g, h_i);
            d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, body))
        };
        // step1 : Fin.prod n (pair) = Fin.prod n (empty diag)
        let step1 = self.prod_congr(n, prod_pair, prod_empty_diag, pw);
        // step2 : Fin.prod n (empty diag) = Fin.prod n (1+1)   prod_diag_eq_two n ∅
        let empty_top = self.empty_fn(parent, n);
        let step2 = Expr::apps(self.prod_diag_eq_two.clone(), [n.clone(), empty_top]);
        // step3 : Fin.prod n (1+1) = cube n   prod_const_two_eq_pow n
        let step3 = Expr::app(self.prod_const_two_eq_pow.clone(), n.clone());
        // chain: fp_pair = fp_empty_diag = fp_const_two = cube
        let t1 = self.trans(
            fp_pair.clone(),
            fp_empty_diag.clone(),
            fp_const_two.clone(),
            step1,
            step2,
        );
        self.trans(fp_pair, fp_const_two, cube, t1, step3)
    }

    /// Given `hagree : ∀ i, U i = ∅ i`, build `setSizeNat n U = 0`:
    ///   `Fin.sumNat_const_zero_of n (indNatFn U) (fun i => congrArg indNat (hagree i))`.
    /// (`setSizeNat n U ≡ Fin.sumNat n (indNatFn U)`, and `indNat (∅ i) ≡ indNat
    /// false ≡ 0`, so each summand is `0` by `congrArg`.)
    fn ss_nat_eq_zero_of_agree(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        u: &Expr,
        hagree: &Expr,
    ) -> Expr {
        let ind_nat_fn = self.ind_nat_fn(parent, n, u);
        // pw : ∀ i, indNat (U i) = 0
        //   = fun i => congrArg indNat (hagree i)   (indNat (∅ i) ≡ indNat false ≡ 0)
        let pw = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let fin_n = self.fin_of(n);
            let (i_id, i) = d.fresh_local(fin_n.clone());
            let empty = self.empty_fn(&d, n);
            let u_i = Expr::app(u.clone(), i.clone());
            let e_i = Expr::app(empty, i.clone());
            // g_nat : Bool → Nat := indNat
            let g_nat = {
                let mut e = EnvDeclBuilder::child_of(&d);
                let (b_id, bb) = e.fresh_local(self.bool_.clone());
                let body = self.ind_nat_of(bb);
                e.finish_child(e.mk_lam(b_id, BinderInfo::Default, self.bool_.clone(), body))
            };
            let h_i = Expr::app(hagree.clone(), i.clone());
            // congrArg Bool Nat (U i) (∅ i) indNat (h_i) : indNat (U i) = indNat (∅ i) ≡ 0
            let body = Expr::apps(
                self.congr_arg.clone(),
                [self.bool_.clone(), self.nat.clone(), u_i, e_i, g_nat, h_i],
            );
            d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, body))
        };
        // Fin.sumNat_const_zero_of n (indNatFn U) pw : Fin.sumNat n (indNatFn U) = 0
        //   ≡ setSizeNat n U = 0 (def-eq).
        Expr::apps(
            self.fin_sum_nat_const_zero_of.clone(),
            [n.clone(), ind_nat_fn, pw],
        )
    }
}

/// `∀ (n : Nat) (U : HCPoint n),
///   Fin.prod n (fun i => 1 + pm(U i)·pm(∅ i)) = cube n · ind(Nat.beq (setSizeNat n U) 0)`.
fn collapse_type(c: &DiagConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (u_id, u) = b.fresh_local(hcp.clone());
    let lhs = c.fprod(&n, c.prod_pair_empty_fn(&b, &n, &u));
    let rhs = c.mul(c.cube(&n), c.empty_ind(&n, &u));
    let concl = c.eq_rat(lhs, rhs);
    let r = b.mk_pi(u_id, BinderInfo::Default, hcp, concl);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

fn collapse_value(c: &DiagConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (u_id, u) = b.fresh_local(hcp.clone());

    let prod_pair = c.prod_pair_empty_fn(&b, &n, &u);
    let fp_pair = c.fprod(&n, prod_pair.clone());
    let cube = c.cube(&n);
    let empty_ind = c.empty_ind(&n, &u);
    let goal = c.eq_rat(fp_pair.clone(), c.mul(cube.clone(), empty_ind.clone()));

    // The dichotomy `prod_factor_zero_or_pointwise_eq n U ∅`:
    //   Or (Fin.prod n (1+pm(U i)·pm(∅ i)) = 0) (∀ i, U i = ∅ i).
    let empty = c.empty_fn(&b, &n);
    let left_prop = c.eq_rat(fp_pair.clone(), c.rat_zero.clone());
    let right_prop = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let empty_i = c.empty_fn(&d, &n);
        let body = c.eq_bool(
            Expr::app(u.clone(), i.clone()),
            Expr::app(empty_i, i.clone()),
        );
        d.finish_child(d.mk_pi(i_id, BinderInfo::Default, fin_n, body))
    };
    let dichotomy = Expr::apps(
        c.prod_dichotomy.clone(),
        [n.clone(), u.clone(), empty.clone()],
    );

    // or_motive : fun (_ : Or left right) => goal
    let or_motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let or_ty = Expr::apps(c.or_c.clone(), [left_prop.clone(), right_prop.clone()]);
        let (h_id, _h) = d.fresh_local(or_ty.clone());
        d.finish_child(d.mk_lam(h_id, BinderInfo::Default, or_ty, goal.clone()))
    };

    // ── RIGHT branch: hagree : ∀ i, U i = ∅ i ──
    //   product = cube n, and setSizeNat n U = 0 ⟹ ind(beq 0 0) ≡ ind true ≡ 1,
    //   so RHS = cube·1 = cube. Close: goal = (fp_pair = cube·ind).
    let case_right = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (hr_id, hr) = d.fresh_local(right_prop.clone());
        // p_cube : fp_pair = cube
        let p_cube = c.prod_eq_cube_of_agree(&d, &n, &u, &hr);
        // ss0 : setSizeNat n U = 0
        let ss0 = c.ss_nat_eq_zero_of_agree(&d, &n, &u, &hr);
        // rewrite RHS `cube · ind(beq (setSizeNat n U) 0)` ← `cube · ind(beq 0 0)`
        //   via congrArg (fun m => cube · ind(beq m 0)) ss0 : cube·ind(beq ss 0) = cube·ind(beq 0 0)
        //   and cube·ind(beq 0 0) ≡ cube·ind(true) ≡ cube·1 (def-eq).
        let g_rhs = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (m_id, m) = e.fresh_local(c.nat.clone());
            let body = c.mul(cube.clone(), c.ind_of(c.beq0(m)));
            e.finish_child(e.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), body))
        };
        let ss_expr = c.ss_nat(&n, &u);
        let rhs_at_ss = c.mul(cube.clone(), c.ind_of(c.beq0(ss_expr.clone())));
        let rhs_at_0 = c.mul(cube.clone(), c.ind_of(c.beq0(c.nat_zero.clone())));
        // h_rhs : cube·ind(beq ss 0) = cube·ind(beq 0 0)
        let h_rhs = c.congr_nr(ss_expr, c.nat_zero.clone(), g_rhs, ss0);
        // cube = cube·1   (symm (Rat.mul_one cube)); cube·1 ≡ cube·ind(beq 0 0) def-eq
        let mul_one_cube = Expr::app(c.rat_mul_one.clone(), cube.clone());
        let cube_times_one = c.mul(cube.clone(), c.rat_one.clone());
        let h_cube_one = c.symm(cube_times_one.clone(), cube.clone(), mul_one_cube);
        // chain: fp_pair = cube = cube·1 ≡ cube·ind(beq 0 0)  then  symm h_rhs gives = cube·ind(beq ss 0)
        // Build: fp_pair = cube·ind(beq ss 0).
        //   t1 : fp_pair = cube·1   (trans p_cube h_cube_one)
        let t1 = c.trans(
            fp_pair.clone(),
            cube.clone(),
            cube_times_one.clone(),
            p_cube,
            h_cube_one,
        );
        //   h_rhs_symm : cube·ind(beq 0 0) = cube·ind(beq ss 0)   (symm h_rhs)
        let h_rhs_symm = c.symm(rhs_at_ss.clone(), rhs_at_0.clone(), h_rhs);
        //   cube·1 ≡ cube·ind(beq 0 0) (def-eq), so t1 : fp_pair = cube·ind(beq 0 0) by retype;
        //   final : fp_pair = cube·ind(beq ss 0)   (trans t1 h_rhs_symm)
        let body = c.trans(fp_pair.clone(), rhs_at_0, rhs_at_ss, t1, h_rhs_symm);
        d.finish_child(d.mk_lam(hr_id, BinderInfo::Default, right_prop.clone(), body))
    };

    // ── LEFT branch: hz : fp_pair = 0 ──
    //   sub-case on the bit `Nat.beq (setSizeNat n U) 0`:
    //     false: RHS = cube·ind(false) = cube·0 = 0 = fp_pair (hz).
    //     true:  setSizeNat=0 ⟹ ∀i U i=false ⟹ product=cube, but hz: product=0,
    //            so cube=0, refuted by natCast_ne_zero_of_pos.
    let case_left = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (hz_id, hz) = d.fresh_local(left_prop.clone());
        let ss_expr = c.ss_nat(&n, &u);
        let beq_expr = c.beq0(ss_expr.clone());

        // bcases_motive : fun (bb : Bool) => Eq Bool beq_expr bb → goal
        let bcases_motive = {
            let mut m = EnvDeclBuilder::child_of(&d);
            let (bb_id, bb) = m.fresh_local(c.bool_.clone());
            let prem = c.eq_bool(beq_expr.clone(), bb);
            let body = Expr::pi(BinderInfo::Default, prem, goal.clone());
            m.finish_child(m.mk_lam(bb_id, BinderInfo::Default, c.bool_.clone(), body))
        };

        // false_branch : Eq Bool beq_expr false → goal
        let false_branch = {
            let mut m = EnvDeclBuilder::child_of(&d);
            let prem = c.eq_bool(beq_expr.clone(), c.bool_false.clone());
            let (hf_id, hf) = m.fresh_local(prem.clone());
            // g_rhs2 : Bool → Rat := fun bb => cube · ind bb
            let g_rhs2 = {
                let mut e = EnvDeclBuilder::child_of(&m);
                let (bb_id, bb) = e.fresh_local(c.bool_.clone());
                let body = c.mul(cube.clone(), c.ind_of(bb));
                e.finish_child(e.mk_lam(bb_id, BinderInfo::Default, c.bool_.clone(), body))
            };
            let rhs_at_beq = c.mul(cube.clone(), c.ind_of(beq_expr.clone()));
            let rhs_at_false = c.mul(cube.clone(), c.ind_of(c.bool_false.clone()));
            // h1 : cube·ind(beq) = cube·ind(false)   (congrArg g_rhs2 hf)
            let h1 = c.congr_br(beq_expr.clone(), c.bool_false.clone(), g_rhs2, hf);
            // cube·ind(false) ≡ cube·0; Rat.mul_zero cube : cube·0 = 0
            let mul_zero_cube = Expr::app(c.rat_mul_zero.clone(), cube.clone());
            let cube_times_zero = c.mul(cube.clone(), c.rat_zero.clone());
            // h2 : cube·ind(false) = 0   (cube·ind(false) ≡ cube·0 def-eq, then mul_zero)
            //   We need: cube·0 = 0; rhs_at_false ≡ cube·0 so mul_zero_cube retypes.
            let h2 = mul_zero_cube;
            // h12 : cube·ind(beq) = 0   (trans h1 h2 ; rhs_at_false ≡ cube·0)
            let h12 = c.trans(
                rhs_at_beq.clone(),
                rhs_at_false.clone(),
                c.rat_zero.clone(),
                h1,
                h2,
            );
            let _ = cube_times_zero;
            // goal : fp_pair = cube·ind(beq).  hz: fp_pair = 0; symm h12: 0 = cube·ind(beq).
            let h12_symm = c.symm(rhs_at_beq.clone(), c.rat_zero.clone(), h12);
            let body = c.trans(
                fp_pair.clone(),
                c.rat_zero.clone(),
                rhs_at_beq,
                hz.clone(),
                h12_symm,
            );
            m.finish_child(m.mk_lam(hf_id, BinderInfo::Default, prem, body))
        };

        // true_branch : Eq Bool beq_expr true → goal  (refute via cube = 0)
        let true_branch = {
            let mut m = EnvDeclBuilder::child_of(&d);
            let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);
            let prem = c.eq_bool(beq_expr.clone(), bool_true.clone());
            let (ht_id, ht) = m.fresh_local(prem.clone());
            // ss0 : setSizeNat n U = 0   (Nat.eq_of_beq_eq_true (setSizeNat n U) 0 ht')
            //   where ht' : Nat.beq (setSizeNat n U) 0 = true  (= ht).
            let ss0 = Expr::apps(
                c.nat_eq_of_beq.clone(),
                [ss_expr.clone(), c.nat_zero.clone(), ht.clone()],
            );
            // hsum : ∀ i, indNat (U i) = 0   (Fin.sumNat_eq_zero n (indNatFn U) ss0)
            //   (setSizeNat n U ≡ Fin.sumNat n (indNatFn U), so ss0 retypes.)
            let ind_nat_fn = c.ind_nat_fn(&m, &n, &u);
            let hsum = Expr::apps(c.fin_sum_nat_eq_zero.clone(), [n.clone(), ind_nat_fn, ss0]);
            // hagree : ∀ i, U i = ∅ i
            //   = fun i => indNat_eq_zero (U i) (hsum i)   (gives U i = false ≡ ∅ i)
            let hagree = {
                let mut e = EnvDeclBuilder::child_of(&m);
                let fin_n = c.fin_of(&n);
                let (i_id, i) = e.fresh_local(fin_n.clone());
                let u_i = Expr::app(u.clone(), i.clone());
                let hsum_i = Expr::app(hsum.clone(), i.clone());
                let body = Expr::apps(c.indnat_eq_zero.clone(), [u_i, hsum_i]);
                e.finish_child(e.mk_lam(i_id, BinderInfo::Default, fin_n, body))
            };
            // p_cube : fp_pair = cube
            let p_cube = c.prod_eq_cube_of_agree(&m, &n, &u, &hagree);
            // cube = 0 : Eq.trans (symm p_cube) hz : cube = 0
            let cube_eq_zero = c.trans(
                cube.clone(),
                fp_pair.clone(),
                c.rat_zero.clone(),
                c.symm(fp_pair.clone(), cube.clone(), p_cube),
                hz.clone(),
            );
            // contra : False = natCast_ne_zero_of_pos (2^n) (one_le_two_pow n) cube_eq_zero
            let contra = Expr::apps(
                c.natcast_ne_zero.clone(),
                [
                    c.pow2(&n),
                    Expr::app(c.one_le_two_pow.clone(), n.clone()),
                    cube_eq_zero,
                ],
            );
            // False.elim goal contra
            let body = Expr::apps(c.false_elim.clone(), [goal.clone(), contra]);
            m.finish_child(m.mk_lam(ht_id, BinderInfo::Default, prem, body))
        };

        // @Bool.casesOn motive beq_expr false_branch true_branch (Eq.refl beq_expr)
        let refl_beq = Expr::apps(c.eq_refl.clone(), [c.bool_.clone(), beq_expr.clone()]);
        let cases = Expr::apps(
            c.bool_cases_on.clone(),
            [
                bcases_motive,
                beq_expr.clone(),
                false_branch,
                true_branch,
                refl_beq,
            ],
        );
        d.finish_child(d.mk_lam(hz_id, BinderInfo::Default, left_prop.clone(), cases))
    };

    // Or.rec left right or_motive case_left case_right dichotomy
    let proof = Expr::apps(
        c.or_rec.clone(),
        [
            left_prop, right_prop, or_motive, case_left, case_right, dichotomy,
        ],
    );

    let val = b.mk_lam(u_id, BinderInfo::Default, hcp, proof);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.prod_pair_empty_eq_pow_ind`: the `(U, ∅)` Kronecker
    /// product collapses to `2^n · ind(U = ∅)`,
    /// `∀ n U, Fin.prod n (fun i => 1 + pm(U i)·pm(∅ i))
    ///    = cube n · ind (Nat.beq (setSizeNat n U) 0)`.
    ///
    /// Case on the constructive dichotomy `prod_factor_zero_or_pointwise_eq n U ∅`
    /// (`Or (product = 0) (∀ i, U i = ∅ i)`):
    /// - RIGHT (`∀ i, U i = ∅ i`): the product is `cube n` (rewrite `U → ∅` in the
    ///   first factor slot then `prod_diag_eq_two ∅` ∘ `prod_const_two_eq_pow`), and
    ///   `setSizeNat n U = 0` (`Fin.sumNat_const_zero_of`), so the indicator
    ///   `ind(beq 0 0) ≡ ind true ≡ 1`; both sides equal `cube n`.
    /// - LEFT (`product = 0`): sub-case the indicator bit (`Bool.casesOn`): the
    ///   `false` leaf gives `cube · ind false ≡ cube · 0 = 0` (`Rat.mul_zero`),
    ///   matching `product = 0`; the `true` leaf forces `setSizeNat n U = 0`
    ///   (`Nat.eq_of_beq_eq_true`) ⟹ `∀ i, U i = false` (`Fin.sumNat_eq_zero` ∘
    ///   `indNat_eq_zero`) ⟹ `product = cube n`, contradicting `product = 0` via
    ///   `cube n ≠ 0` (`Rat.natCast_ne_zero_of_pos` ∘ `Nat.one_le_two_pow`).
    ///
    /// Constructive, empty admitted-axiom closure. Idempotent.
    pub(crate) fn register_prod_pair_empty_eq_pow_ind(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.prod_pair_empty_eq_pow_ind");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?;
        self.init_rat_field_inst()?; // Rat.mul_one, Rat.mul_zero
        self.init_boolean_analysis()?; // chi, pm, ind, Bool.false/xor
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_set_size_nat()?;
        self.register_prod_factor_zero_or_pointwise_eq()?;
        self.register_fin_prod_diag_eq_two()?;
        self.register_prod_const_two_eq_pow()?;
        self.register_fin_prod_one_theorems()?; // Fin.prod_congr
        self.register_fin_sum_nat_const_zero_of()?;
        self.register_fin_sum_nat_eq_zero()?;
        self.register_indnat_eq_zero()?;
        self.register_nat_eq_of_beq_eq_true()?;
        self.register_expect_one_theorems()?; // Nat.one_le_two_pow, Rat.natCast_ne_zero_of_pos

        let c = DiagConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: collapse_type(&c),
            value: collapse_value(&c),
        })
    }
}

// ===========================================================================
// chi_single_subsetSum_diag — single character sum = 2^n · ind(U = ∅).
// ===========================================================================

/// `∀ (n : Nat) (U : HCPoint n),
///   subsetSum n (fun x => χ_U(x)) = cube n · ind (Nat.beq (setSizeNat n U) 0)`.
fn single_diag_type(c: &DiagConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (u_id, u) = b.fresh_local(hcp.clone());
    let lhs = c.ssum(&n, c.chi_single_fn(&b, &n, &u));
    let rhs = c.mul(c.cube(&n), c.empty_ind(&n, &u));
    let concl = c.eq_rat(lhs, rhs);
    let r = b.mk_pi(u_id, BinderInfo::Default, hcp, concl);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

fn single_diag_value(c: &DiagConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (u_id, u) = b.fresh_local(hcp.clone());

    let ss_single = c.ssum(&n, c.chi_single_fn(&b, &n, &u));
    let fp_pair = c.fprod(&n, c.prod_pair_empty_fn(&b, &n, &u));
    let rhs = c.mul(c.cube(&n), c.empty_ind(&n, &u));

    // leg1 : subsetSum n (χ_U) = Fin.prod n (1+pm(U i)·pm(∅ i))   (chi_single_subsetSum_eq_prod)
    let leg1 = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.chi_single_subsetSum_eq_prod"),
            vec![],
        ),
        [n.clone(), u.clone()],
    );
    // leg2 : Fin.prod n (...) = cube·ind(beq..)   (prod_pair_empty_eq_pow_ind)
    let leg2 = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.prod_pair_empty_eq_pow_ind"),
            vec![],
        ),
        [n.clone(), u.clone()],
    );
    let proof = c.trans(ss_single, fp_pair, rhs, leg1, leg2);

    let val = b.mk_lam(u_id, BinderInfo::Default, hcp, proof);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.chi_single_subsetSum_diag`: the single-character cube
    /// sum equals its `2^n`-or-`0` diagonal value,
    /// `∀ n U, subsetSum n (fun x => χ_U x) = cube n · ind (Nat.beq (setSizeNat n U) 0)`.
    ///
    /// `Eq.trans` of `chi_single_subsetSum_eq_prod` (sum → Kronecker product form)
    /// and `prod_pair_empty_eq_pow_ind` (product → `2^n · ind(U = ∅)`). Constructive,
    /// empty admitted-axiom closure. Idempotent.
    pub(crate) fn register_chi_single_subset_sum_diag(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.chi_single_subsetSum_diag");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_chi_single_subset_sum_eq_prod()?;
        self.register_prod_pair_empty_eq_pow_ind()?;

        let c = DiagConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: single_diag_type(&c),
            value: single_diag_value(&c),
        })
    }
}

// ===========================================================================
// subsetSum_chi_quad_diag — the roadmap's exact RUNG-1 diagonal statement.
// ===========================================================================

impl DiagConsts {
    /// `fun (i : Fin n) => Bool.xor (S i) (T i)` — `S Δ T` (matches the
    /// `subsetSum_chi_quad_orthogonality` symm_diff spelling exactly).
    #[cfg(test)]
    fn symm_diff_fn(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr, t: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let body = self.xor(
            Expr::app(s.clone(), i.clone()),
            Expr::app(t.clone(), i.clone()),
        );
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }

    /// `(S1 Δ S2) Δ (S3 Δ S4)` as an `HCPoint n` — the 4-fold symmetric
    /// difference `symmDiff4`, byte-identical to the fold's RHS subset.
    #[cfg(test)]
    fn symm_diff4(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        s1: &Expr,
        s2: &Expr,
        s3: &Expr,
        s4: &Expr,
    ) -> Expr {
        let sd12 = self.symm_diff_fn(parent, n, s1, s2);
        let sd34 = self.symm_diff_fn(parent, n, s3, s4);
        self.symm_diff_fn(parent, n, &sd12, &sd34)
    }

    /// `fun (x : HCPoint n) => (χ_{S1}·χ_{S2})·(χ_{S3}·χ_{S4})` — the 4-fold
    /// product integrand (matches `subsetSum_chi_quad_orthogonality`'s LHS).
    #[cfg(test)]
    fn quad_product_fn(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        s1: &Expr,
        s2: &Expr,
        s3: &Expr,
        s4: &Expr,
    ) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = self.mul(
            self.mul(self.chi_(n, s1, &x), self.chi_(n, s2, &x)),
            self.mul(self.chi_(n, s3, &x), self.chi_(n, s4, &x)),
        );
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
}

/// `∀ (n : Nat) (S1 S2 S3 S4 : HCPoint n),
///   subsetSum n (fun x => (χ_{S1}·χ_{S2})·(χ_{S3}·χ_{S4}))
///     = cube n · ind (Nat.beq (setSizeNat n ((S1 Δ S2) Δ (S3 Δ S4))) 0)`.
#[cfg(test)]
fn quad_diag_type(c: &DiagConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (s1_id, s1) = b.fresh_local(hcp.clone());
    let (s2_id, s2) = b.fresh_local(hcp.clone());
    let (s3_id, s3) = b.fresh_local(hcp.clone());
    let (s4_id, s4) = b.fresh_local(hcp.clone());

    let lhs = c.ssum(&n, c.quad_product_fn(&b, &n, &s1, &s2, &s3, &s4));
    let sd = c.symm_diff4(&b, &n, &s1, &s2, &s3, &s4);
    let rhs = c.mul(c.cube(&n), c.empty_ind(&n, &sd));
    let concl = c.eq_rat(lhs, rhs);

    let r = b.mk_pi(s4_id, BinderInfo::Default, hcp.clone(), concl);
    let r = b.mk_pi(s3_id, BinderInfo::Default, hcp.clone(), r);
    let r = b.mk_pi(s2_id, BinderInfo::Default, hcp.clone(), r);
    let r = b.mk_pi(s1_id, BinderInfo::Default, hcp, r);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

#[cfg(test)]
fn quad_diag_value(c: &DiagConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (s1_id, s1) = b.fresh_local(hcp.clone());
    let (s2_id, s2) = b.fresh_local(hcp.clone());
    let (s3_id, s3) = b.fresh_local(hcp.clone());
    let (s4_id, s4) = b.fresh_local(hcp.clone());

    let lhs = c.ssum(&n, c.quad_product_fn(&b, &n, &s1, &s2, &s3, &s4));
    let sd = c.symm_diff4(&b, &n, &s1, &s2, &s3, &s4);
    let mid = c.ssum(&n, c.chi_single_fn(&b, &n, &sd));
    let rhs = c.mul(c.cube(&n), c.empty_ind(&n, &sd));

    // leg1 : Σ 4-prod = subsetSum n (χ_{symmDiff4})   (subsetSum_chi_quad_orthogonality)
    let leg1 = Expr::apps(
        c.quad_ortho.clone(),
        [n.clone(), s1.clone(), s2.clone(), s3.clone(), s4.clone()],
    );
    // leg2 : subsetSum n (χ_{symmDiff4}) = cube·ind(beq..)   (chi_single_subsetSum_diag n symmDiff4)
    let leg2 = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.chi_single_subsetSum_diag"),
            vec![],
        ),
        [n.clone(), sd.clone()],
    );
    let proof = c.trans(lhs, mid, rhs, leg1, leg2);

    let val = b.mk_lam(s4_id, BinderInfo::Default, hcp.clone(), proof);
    let val = b.mk_lam(s3_id, BinderInfo::Default, hcp.clone(), val);
    let val = b.mk_lam(s2_id, BinderInfo::Default, hcp.clone(), val);
    let val = b.mk_lam(s1_id, BinderInfo::Default, hcp, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.subsetSum_chi_quad_diag` — the sharp-KKL roadmap's
    /// EXACT rung-1 diagonal statement,
    /// `∀ n S1 S2 S3 S4,
    ///    subsetSum n (fun x => (χ_{S1}·χ_{S2})·(χ_{S3}·χ_{S4}))
    ///      = 2^n · ind((S1 Δ S2) Δ (S3 Δ S4) = ∅)`,
    /// with `ind(U = ∅)` rendered as the codebase-native `ind (Nat.beq (setSizeNat
    /// n U) 0)`.
    ///
    /// `Eq.trans` of the on-branch 4-fold fold `subsetSum_chi_quad_orthogonality`
    /// (collapsing the 4-fold character product sum to the single-character sum at
    /// `U := (S1 Δ S2) Δ (S3 Δ S4)`) and the diagonal extraction
    /// `chi_single_subsetSum_diag` (`Σ_x χ_U = 2^n · ind(U = ∅)`). This is the
    /// 4-fold symmetric-difference fold + diagonal-value evaluation that rung 1 of
    /// the roadmap names "THE HARD CRUX". Constructive, empty admitted-axiom
    /// closure. Idempotent.
    #[cfg(test)]
    pub(crate) fn register_subset_sum_chi_quad_diag(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_chi_quad_diag");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_subset_sum_chi_quad_orthogonality()?;
        self.register_chi_single_subset_sum_diag()?;

        let c = DiagConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: quad_diag_type(&c),
            value: quad_diag_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn assert_constructive_theorem(env: &Environment, name_str: &str) {
        let name = Name::from_string(name_str);
        let info = env.get_const(&name).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{name_str} must be a Theorem"
        );
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(&info.value.clone().expect("proof"), &info.type_)
            .unwrap_or_else(|e| panic!("{name_str} must type-check: {e:?}"));
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "{name_str} must be axiom-free, got {:?}",
            env.axiom_deps(&name)
        );
        assert_eq!(
            env.proof_quality(&name).expect("quality"),
            ProofQuality::Constructive,
            "{name_str} must be Constructive",
        );
    }

    #[test]
    fn test_chi_quad_diag_prod_pair_empty_collapse() {
        let mut env = Environment::new();
        env.register_prod_pair_empty_eq_pow_ind()
            .expect("register_prod_pair_empty_eq_pow_ind");
        env.register_prod_pair_empty_eq_pow_ind()
            .expect("idempotent");
        assert_constructive_theorem(&env, "BoolAnalysis.prod_pair_empty_eq_pow_ind");
    }

    #[test]
    fn test_chi_quad_diag_single_diag() {
        let mut env = Environment::new();
        env.register_chi_single_subset_sum_diag()
            .expect("register_chi_single_subset_sum_diag");
        assert_constructive_theorem(&env, "BoolAnalysis.chi_single_subsetSum_diag");
    }

    #[test]
    fn test_chi_quad_diag_full() {
        let mut env = Environment::new();
        env.register_subset_sum_chi_quad_diag()
            .expect("register_subset_sum_chi_quad_diag");
        env.register_subset_sum_chi_quad_diag().expect("idempotent");
        assert_constructive_theorem(&env, "BoolAnalysis.subsetSum_chi_quad_diag");
    }

    #[test]
    fn test_chi_single_subset_sum_eq_prod_is_constructive_theorem() {
        let mut env = Environment::new();
        env.register_chi_single_subset_sum_eq_prod()
            .expect("register_chi_single_subset_sum_eq_prod");
        env.register_chi_single_subset_sum_eq_prod()
            .expect("idempotent");
        let name = Name::from_string("BoolAnalysis.chi_single_subsetSum_eq_prod");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&info.value.clone().expect("proof"), &info.type_)
            .expect("chi_single_subsetSum_eq_prod must type-check");
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "chi_single_subsetSum_eq_prod must be axiom-free, got {:?}",
            env.axiom_deps(&name)
        );
        assert_eq!(
            env.proof_quality(&name).expect("quality"),
            ProofQuality::Constructive,
        );
    }
}
