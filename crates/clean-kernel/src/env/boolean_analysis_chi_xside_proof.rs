// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! x-side character orthonormality in UN-NORMALIZED (subsetSum) form — the
//! numerator pieces of `Σ_x χ_S(x)·χ_T(x)` over the cube.
//!
//! These are the dual of the inner-δ collapse used in `subsetSum_parseval_core`
//! (which collapses `Σ_S χ_S(x)·χ_S(y)`): here the OUTER sum is over `x` and the
//! collapsing index is the SUBSET pair `(S, T)`. The two facts needed to assemble
//! the x-side Parseval core are
//!
//!   • DIAGONAL (`S = T`):  `Σ_x χ_S(x)·χ_S(x) = 2^n`  — this module's
//!     `chi_self_subsetSum_eq_cube`. Constructive: `subsetSum_congr` over the
//!     proven per-point `chi_mul_self` (`χ_S(x)·χ_S(x) = 1`) lands the constant-1
//!     sum, whose value is `2^n` by `Fin.sum_const_one` (the subsetSum unfolds,
//!     reducibly, to exactly that `Fin.sum`).
//!
//!   • OFF-DIAGONAL (`S ≠ T`):  `Σ_x χ_S(x)·χ_T(x) = 0`  — still requires the
//!     coordinate-agnostic off-diagonal average in numerator form (the proven
//!     `chi_inner_offdiag_zero` is E-form and phrased for the (n+1)-cube with a
//!     top-coordinate hypothesis); not yet assembled here.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for the x-side numerator lemmas.
struct XSideConsts {
    nat: Expr,
    rat: Expr,
    #[cfg(test)]
    nat_succ: Expr,
    #[cfg(test)]
    nat_zero: Expr,
    #[cfg(test)]
    nat_pow: Expr,
    #[cfg(test)]
    int_of_nat: Expr,
    #[cfg(test)]
    rat_mk: Expr,
    rat_mul: Expr,
    #[cfg(test)]
    rat_one: Expr,
    hcpoint: Expr,
    chi: Expr,
    subset_sum: Expr,
    subset_sum_congr: Expr,
    #[cfg(test)]
    chi_mul_self: Expr,
    chi_mul_chi_symm_diff: Expr,
    bool_xor: Expr,
    #[cfg(test)]
    bool_c: Expr,
    #[cfg(test)]
    btrue: Expr,
    fin: Expr,
    #[cfg(test)]
    fin_last: Expr,
    #[cfg(test)]
    rat_zero: Expr,
    #[cfg(test)]
    chi_offdiag_numerator_zero: Expr,
    #[cfg(test)]
    fin_sum_const_one: Expr,
    eq1: Expr,
    #[cfg(test)]
    eq_trans: Expr,
}

impl XSideConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            #[cfg(test)]
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            #[cfg(test)]
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            #[cfg(test)]
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            #[cfg(test)]
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            #[cfg(test)]
            rat_mk: Expr::const_(Name::from_string("Rat.mk"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            #[cfg(test)]
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            chi: Expr::const_(Name::from_string("BoolAnalysis.chi"), vec![]),
            subset_sum: Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            subset_sum_congr: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_congr"),
                vec![],
            ),
            #[cfg(test)]
            chi_mul_self: Expr::const_(Name::from_string("BoolAnalysis.chi_mul_self"), vec![]),
            chi_mul_chi_symm_diff: Expr::const_(
                Name::from_string("BoolAnalysis.chi_mul_chi_symmDiff"),
                vec![],
            ),
            bool_xor: Expr::const_(Name::from_string("Bool.xor"), vec![]),
            #[cfg(test)]
            bool_c: Expr::const_(Name::from_string("Bool"), vec![]),
            #[cfg(test)]
            btrue: Expr::const_(Name::from_string("Bool.true"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            #[cfg(test)]
            fin_last: Expr::const_(Name::from_string("Fin.last"), vec![]),
            #[cfg(test)]
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            #[cfg(test)]
            chi_offdiag_numerator_zero: Expr::const_(
                Name::from_string("BoolAnalysis.chi_offdiag_numerator_zero"),
                vec![],
            ),
            #[cfg(test)]
            fin_sum_const_one: Expr::const_(Name::from_string("Fin.sum_const_one"), vec![]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            #[cfg(test)]
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1]),
        }
    }

    #[cfg(test)]
    fn one(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.nat_zero.clone())
    }
    #[cfg(test)]
    fn two(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.one())
    }
    #[cfg(test)]
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two(), n.clone()])
    }
    /// `Rat.mk (Int.ofNat (2^n)) 1` — the rational `2^n`.
    #[cfg(test)]
    fn cube(&self, n: &Expr) -> Expr {
        let ofnat = Expr::app(self.int_of_nat.clone(), self.pow2(n));
        Expr::apps(self.rat_mk.clone(), [ofnat, self.one()])
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
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
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    #[cfg(test)]
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }

    /// `fun (x : HCPoint n) => χ_S(x)·χ_S(x)` — the diagonal integrand.
    #[cfg(test)]
    fn chi_sq_fn(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let chi_sx = self.chi_(n, s, &x);
        let body = self.mul(chi_sx.clone(), chi_sx);
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `fun (_ : HCPoint n) => Rat.one` — the constant-1 integrand.
    #[cfg(test)]
    fn const_one_fn(&self, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, _x) = b.fresh_local(hcp.clone());
        let lam = b.mk_lam(x_id, BinderInfo::Default, hcp, self.rat_one.clone());
        b.finish_child(lam)
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    /// `fun (i : Fin n) => Bool.xor (S i) (T i)` — the symmetric difference
    /// `S Δ T` as an `HCPoint n` (matches `chi_mul_chi_symmDiff`'s RHS subset).
    fn symm_diff_fn(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr, t: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let body = Expr::apps(
            self.bool_xor.clone(),
            [Expr::app(s.clone(), i.clone()), Expr::app(t.clone(), i)],
        );
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
    /// `fun (x : HCPoint n) => χ_S(x)·χ_T(x)` — the off-diagonal integrand.
    fn chi_pair_fn(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr, t: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = self.mul(self.chi_(n, s, &x), self.chi_(n, t, &x));
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `fun (x : HCPoint n) => χ_U(x)` — the single-character integrand at `U`.
    fn chi_single_fn(&self, parent: &EnvDeclBuilder, n: &Expr, u: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = self.chi_(n, u, &x);
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    #[cfg(test)]
    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }
    #[cfg(test)]
    fn last(&self, n: &Expr) -> Expr {
        Expr::app(self.fin_last.clone(), n.clone())
    }
    /// `@Eq Bool a b`.
    #[cfg(test)]
    fn eq_bool(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.bool_c.clone(), a, b])
    }
}

/// `∀ (n : Nat) (S : HCPoint n), subsetSum n (fun x => χ_S(x)·χ_S(x)) = 2^n`.
#[cfg(test)]
fn diag_type(c: &XSideConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let lhs = c.ssum(&n, c.chi_sq_fn(&b, &n, &s));
    let concl = c.eq_rat(lhs, c.cube(&n));
    let r = b.mk_pi(s_id, BinderInfo::Default, hcp, concl);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

#[cfg(test)]
fn diag_value(c: &XSideConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());

    let chi_sq = c.chi_sq_fn(&b, &n, &s);
    let const_one = c.const_one_fn(&b, &n);
    let ss_chi_sq = c.ssum(&n, chi_sq.clone());
    let ss_one = c.ssum(&n, const_one.clone());
    let cube = c.cube(&n);

    // leg1 : subsetSum n (χ_S·χ_S) = subsetSum n (const 1)
    //   subsetSum_congr n (χ_S·χ_S) (const 1) (fun x => chi_mul_self n S x)
    let pointwise = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let body = Expr::apps(c.chi_mul_self.clone(), [n.clone(), s.clone(), x]);
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
    };
    let leg1 = Expr::apps(
        c.subset_sum_congr.clone(),
        [n.clone(), chi_sq, const_one, pointwise],
    );

    // leg2 : subsetSum n (const 1) = 2^n.
    //   subsetSum n (fun _ => Rat.one) δ-unfolds (subsetSum reducible) to
    //   Fin.sum (2^n) (fun k => (fun _ => Rat.one) (hcDecode n k)) which β-reduces
    //   to Fin.sum (2^n) (fun _ => Rat.one) — exactly Fin.sum_const_one (2^n)'s LHS;
    //   its RHS is Rat.mk (Int.ofNat (2^n)) 1 = cube.
    let leg2 = Expr::app(c.fin_sum_const_one.clone(), c.pow2(&n));

    let proof = c.trans(ss_chi_sq, ss_one, cube, leg1, leg2);
    let val = b.mk_lam(s_id, BinderInfo::Default, hcp, proof);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.chi_self_subsetSum_eq_cube`: the DIAGONAL x-side
    /// character orthonormality in un-normalized form,
    /// `∀ n S, subsetSum n (fun x => χ_S(x)·χ_S(x)) = 2^n`.
    ///
    /// `Eq.trans` of two legs: (1) `subsetSum_congr` over the proven per-point
    /// `chi_mul_self` (`χ_S(x)·χ_S(x) = 1`), collapsing the diagonal integrand to
    /// the constant `1`; and (2) `Fin.sum_const_one (2^n)` (`Σ_{k<2^n} 1 = 2^n`),
    /// to which the constant-1 `subsetSum` is def-equal (reducible unfold + β).
    /// Both legs are constructive with empty admitted-axiom closure, so the
    /// result is `ProofQuality::Constructive`. Idempotent.
    #[cfg(test)]
    pub(crate) fn register_chi_self_subset_sum_eq_cube(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.chi_self_subsetSum_eq_cube");
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
        self.register_chi_mul_self_theorem()?;
        self.register_fin_sum_const_one_theorems()?; // Fin.sum_const_one

        let c = XSideConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: diag_type(&c),
            value: diag_value(&c),
        })
    }
}

/// `∀ (n : Nat) (S T : HCPoint n),
///   subsetSum n (fun x => χ_S(x)·χ_T(x))
///     = subsetSum n (fun x => χ_{S Δ T}(x))`.
fn symmdiff_type(c: &XSideConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let (t_id, t) = b.fresh_local(hcp.clone());
    let lhs = c.ssum(&n, c.chi_pair_fn(&b, &n, &s, &t));
    let sd = c.symm_diff_fn(&b, &n, &s, &t);
    let rhs = c.ssum(&n, c.chi_single_fn(&b, &n, &sd));
    let concl = c.eq_rat(lhs, rhs);
    let r = b.mk_pi(t_id, BinderInfo::Default, hcp.clone(), concl);
    let r = b.mk_pi(s_id, BinderInfo::Default, hcp, r);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

fn symmdiff_value(c: &XSideConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let (t_id, t) = b.fresh_local(hcp.clone());

    let chi_pair = c.chi_pair_fn(&b, &n, &s, &t);
    let sd = c.symm_diff_fn(&b, &n, &s, &t);
    let chi_single = c.chi_single_fn(&b, &n, &sd);

    // subsetSum_congr n (χ_S·χ_T) (χ_{SΔT}) (fun x => chi_mul_chi_symmDiff n S T x)
    //   per-point: χ_S(x)·χ_T(x) = χ_{SΔT}(x). The two integrands β-match the
    //   subsetSum arguments exactly (symm_diff_fn = chi_mul_chi_symmDiff's RHS
    //   subset), so the congruence proof retypes by defeq.
    let pointwise = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let body = Expr::apps(
            c.chi_mul_chi_symm_diff.clone(),
            [n.clone(), s.clone(), t.clone(), x],
        );
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
    };
    let proof = Expr::apps(
        c.subset_sum_congr.clone(),
        [n.clone(), chi_pair, chi_single, pointwise],
    );

    let val = b.mk_lam(t_id, BinderInfo::Default, hcp.clone(), proof);
    let val = b.mk_lam(s_id, BinderInfo::Default, hcp, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.chi_pair_subsetSum_eq_symmDiff`: the x-side
    /// character-product reduction in un-normalized (subsetSum) form,
    /// `∀ n S T, subsetSum n (fun x => χ_S(x)·χ_T(x))
    ///            = subsetSum n (fun x => χ_{S Δ T}(x))`.
    ///
    /// `subsetSum_congr` over the proven per-point character group law
    /// `chi_mul_chi_symmDiff` (`χ_S(x)·χ_T(x) = χ_{S Δ T}(x)`). The un-normalized
    /// analog of `chi_inner_eq_expect_symmDiff` (the E-form reduction): it
    /// collapses the off-diagonal character inner product to a SINGLE-character
    /// sum at `S Δ T`, reducing x-side orthonormality to the vanishing of
    /// `Σ_x χ_U(x)` for nonempty `U`. Constructive, empty admitted-axiom closure.
    /// Idempotent.
    pub(crate) fn register_chi_pair_subset_sum_eq_symm_diff(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.chi_pair_subsetSum_eq_symmDiff");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // chi_mul_chi_symmDiff, chi, Bool.xor
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_chi_symm_diff_theorem()?;

        let c = XSideConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: symmdiff_type(&c),
            value: symmdiff_value(&c),
        })
    }
}

/// `∀ (n : Nat) (U : HCPoint (n+1)),
///   U (Fin.last n) = true → subsetSum (n+1) (fun x => χ_U(x)) = 0`.
#[cfg(test)]
fn single_top_type(c: &XSideConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let sn = c.succ(&n);
    let hcp = c.hcpoint_of(&sn);
    let (u_id, u) = b.fresh_local(hcp.clone());
    let u_last = Expr::app(u.clone(), c.last(&n));
    let h_ty = c.eq_bool(u_last, c.btrue.clone());
    let (h_id, _h) = b.fresh_local(h_ty.clone());

    let lhs = c.ssum(&sn, c.chi_single_fn(&b, &sn, &u));
    let concl = c.eq_rat(lhs, c.rat_zero.clone());
    let r = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
    let r = b.mk_pi(u_id, BinderInfo::Default, hcp, r);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

#[cfg(test)]
fn single_top_value(c: &XSideConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let sn = c.succ(&n);
    let hcp = c.hcpoint_of(&sn);
    let (u_id, u) = b.fresh_local(hcp.clone());
    let u_last = Expr::app(u.clone(), c.last(&n));
    let h_ty = c.eq_bool(u_last, c.btrue.clone());
    let (h_id, h) = b.fresh_local(h_ty.clone());

    // chi_offdiag_numerator_zero n U h :
    //   Fin.sum (2^(n+1)) (fun k => chi (n+1) U (hcDecode (n+1) k)) = 0.
    // The goal LHS `subsetSum (n+1) (fun x => χ_U(x))` δ-unfolds (subsetSum
    // reducible) to `Fin.sum (2^(n+1)) (fun j => (fun x => χ_U(x)) (hcDecode (n+1) j))`,
    // which β-reduces to exactly the numerator sum — so the proof retypes by defeq.
    let proof = Expr::apps(
        c.chi_offdiag_numerator_zero.clone(),
        [n.clone(), u.clone(), h.clone()],
    );

    let val = b.mk_lam(h_id, BinderInfo::Default, h_ty, proof);
    let val = b.mk_lam(u_id, BinderInfo::Default, hcp, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.chi_single_subsetSum_top_zero`: the un-normalized
    /// single-character sum vanishes when the TOP coordinate is present,
    /// `∀ n (U : HCPoint (n+1)), U (Fin.last n) = true
    ///    → subsetSum (n+1) (fun x => χ_U(x)) = 0`.
    ///
    /// A thin def-eq bridge from the proven `chi_offdiag_numerator_zero` (whose
    /// LHS is the `Fin.sum (2^(n+1))` numerator that `subsetSum (n+1)` reducibly
    /// unfolds to). Combined with `chi_pair_subsetSum_eq_symmDiff`, this gives the
    /// off-diagonal x-side orthonormality whenever `S Δ T` carries the top
    /// coordinate. Constructive, empty admitted-axiom closure. Idempotent.
    ///
    /// RESIDUAL: the GENERAL off-diagonal (arbitrary present coordinate, hence
    /// arbitrary distinct decoded subsets) needs a coordinate-agnostic vanishing
    /// lemma — a general-coordinate cube split or a χ coordinate-permutation
    /// symmetry — which is genuinely new machinery not yet assembled.
    #[cfg(test)]
    pub(crate) fn register_chi_single_subset_sum_top_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.chi_single_subsetSum_top_zero");
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
        self.register_chi_offdiag_numerator_zero_theorem()?;

        let c = XSideConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: single_top_type(&c),
            value: single_top_value(&c),
        })
    }
}

// ===========================================================================
// GENERAL x-side character orthonormality in numerator (subsetSum) form, read
// off the sign-side bilinear `subsetSum_chi_sign_bilinear` plus the EXISTING
// Kronecker product collapse `prod_offdiag_eq_zero` / `prod_diag_eq_cube`.
// These supersede the top-coordinate-only `chi_single_subsetSum_top_zero`: the
// off-diagonal holds for ANY distinct decoded gates (arbitrary present coord).
// ===========================================================================

/// Extra constants for the general orthonormality numerators.
struct GenConsts {
    nat: Expr,
    rat: Expr,
    #[cfg(test)]
    bool_: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_add: Expr,
    rat_zero: Expr,
    pm: Expr,
    fin: Expr,
    nat_pow: Expr,
    two: Expr,
    hc_decode: Expr,
    chi: Expr,
    subset_sum: Expr,
    fin_prod: Expr,
    sign_bilinear: Expr,
    prod_offdiag: Expr,
    prod_diag_cube: Expr,
    false_c: Expr,
    eq1: Expr,
    eq_trans1: Expr,
}

impl GenConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let z = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let s = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let two = Expr::app(s.clone(), Expr::app(s, z));
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            #[cfg(test)]
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            pm: Expr::const_(Name::from_string("BoolAnalysis.pm"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            two,
            hc_decode: Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]),
            chi: Expr::const_(Name::from_string("BoolAnalysis.chi"), vec![]),
            subset_sum: Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            fin_prod: Expr::const_(Name::from_string("Fin.prod"), vec![]),
            sign_bilinear: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_chi_sign_bilinear"),
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
            false_c: Expr::const_(Name::from_string("False"), vec![]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![l1]),
        }
    }
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two.clone(), n.clone()])
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn cube(&self, n: &Expr) -> Expr {
        let one = Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
        );
        let ofnat = Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            self.pow2(n),
        );
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mk"), vec![]),
            [ofnat, one],
        )
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            n.clone(),
        )
    }
    fn hc_decode(&self, n: &Expr, j: &Expr) -> Expr {
        Expr::apps(self.hc_decode.clone(), [n.clone(), j.clone()])
    }
    fn chi(&self, n: &Expr, s: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.chi.clone(), [n.clone(), s.clone(), x.clone()])
    }
    fn pm(&self, b: Expr) -> Expr {
        Expr::app(self.pm.clone(), b)
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans1.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    /// `fun (x : HCPoint n) => χ_S(x)·χ_T(x)` — the off-diagonal integrand.
    fn pair_fn(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr, t: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = self.mul(self.chi(n, s, &x), self.chi(n, t, &x));
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `Fin.prod n (fun i => 1 + pm(S i)·pm(T i))` — the bilinear product form.
    fn prod_form(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr, t: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let body = self.add(
            self.rat_one.clone(),
            self.mul(
                self.pm(Expr::app(s.clone(), i.clone())),
                self.pm(Expr::app(t.clone(), i)),
            ),
        );
        let f = b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body));
        Expr::apps(self.fin_prod.clone(), [n.clone(), f])
    }
}

/// `∀ n (jS jT : Fin (2^n)), (jS = jT → False) →
///   subsetSum n (fun x => χ_{hcDecode jS}(x)·χ_{hcDecode jT}(x)) = 0`.
fn gen_offdiag_type(c: &GenConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let fin_p = c.fin_of(&c.pow2(&n));
    let (js_id, js) = b.fresh_local(fin_p.clone());
    let (jt_id, jt) = b.fresh_local(fin_p.clone());
    let eq_jk = Expr::apps(c.eq1.clone(), [fin_p.clone(), js.clone(), jt.clone()]);
    let ne_ty = Expr::pi(BinderInfo::Default, eq_jk, c.false_c.clone());
    let (ne_id, _ne) = b.fresh_local(ne_ty.clone());
    let s = c.hc_decode(&n, &js);
    let t = c.hc_decode(&n, &jt);
    let lhs = c.ssum(&n, c.pair_fn(&b, &n, &s, &t));
    let concl = c.eq_rat(lhs, c.rat_zero.clone());
    let r = b.mk_pi(ne_id, BinderInfo::Default, ne_ty, concl);
    let r = b.mk_pi(jt_id, BinderInfo::Default, fin_p.clone(), r);
    let r = b.mk_pi(js_id, BinderInfo::Default, fin_p, r);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

fn gen_offdiag_value(c: &GenConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let fin_p = c.fin_of(&c.pow2(&n));
    let (js_id, js) = b.fresh_local(fin_p.clone());
    let (jt_id, jt) = b.fresh_local(fin_p.clone());
    let eq_jk = Expr::apps(c.eq1.clone(), [fin_p.clone(), js.clone(), jt.clone()]);
    let ne_ty = Expr::pi(BinderInfo::Default, eq_jk, c.false_c.clone());
    let (ne_id, ne) = b.fresh_local(ne_ty.clone());

    let s = c.hc_decode(&n, &js);
    let t = c.hc_decode(&n, &jt);
    let lhs = c.ssum(&n, c.pair_fn(&b, &n, &s, &t));
    let prod = c.prod_form(&b, &n, &s, &t);

    // leg1 : subsetSum n (χ_S·χ_T) = Fin.prod n (1+pm(S i)pm(T i))
    //   subsetSum_chi_sign_bilinear n (hcDecode jS)(hcDecode jT).
    let leg1 = Expr::apps(c.sign_bilinear.clone(), [n.clone(), s.clone(), t.clone()]);
    // leg2 : Fin.prod n (...) = 0   prod_offdiag_eq_zero n jS jT ne.
    let leg2 = Expr::apps(
        c.prod_offdiag.clone(),
        [n.clone(), js.clone(), jt.clone(), ne.clone()],
    );
    let proof = c.trans(lhs, prod, c.rat_zero.clone(), leg1, leg2);

    let val = b.mk_lam(ne_id, BinderInfo::Default, ne_ty, proof);
    let val = b.mk_lam(jt_id, BinderInfo::Default, fin_p.clone(), val);
    let val = b.mk_lam(js_id, BinderInfo::Default, fin_p, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

/// `∀ n (S : HCPoint n), subsetSum n (fun x => χ_S(x)·χ_S(x)) = 2^n`.
/// (Self-orthonormality via the sign-side bilinear; an alternative route to
/// `chi_self_subsetSum_eq_cube` exposing the SAME product form as the off-diag.)
fn gen_diag_type(c: &GenConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let lhs = c.ssum(&n, c.pair_fn(&b, &n, &s, &s));
    let concl = c.eq_rat(lhs, c.cube(&n));
    let r = b.mk_pi(s_id, BinderInfo::Default, hcp, concl);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

fn gen_diag_value(c: &GenConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let lhs = c.ssum(&n, c.pair_fn(&b, &n, &s, &s));
    let prod = c.prod_form(&b, &n, &s, &s);
    // leg1 : subsetSum n (χ_S·χ_S) = Fin.prod n (1+pm(S i)pm(S i))  (bilinear S S)
    let leg1 = Expr::apps(c.sign_bilinear.clone(), [n.clone(), s.clone(), s.clone()]);
    // leg2 : Fin.prod n (...) = 2^n   (prod_diag_eq_cube n S)
    let leg2 = Expr::apps(c.prod_diag_cube.clone(), [n.clone(), s.clone()]);
    let proof = c.trans(lhs, prod, c.cube(&n), leg1, leg2);
    let val = b.mk_lam(s_id, BinderInfo::Default, hcp, proof);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.chi_offdiag_subsetSum_zero`: the GENERAL x-side
    /// off-diagonal orthonormality in numerator form,
    /// `∀ n (jS jT : Fin (2^n)), jS ≠ jT →
    ///    subsetSum n (fun x => χ_{hcDecode jS}(x)·χ_{hcDecode jT}(x)) = 0`.
    ///
    /// `Eq.trans` of the sign-side bilinear `subsetSum_chi_sign_bilinear`
    /// (collapsing the off-diagonal character sum to the product
    /// `Π_i (1 + pm(S i)·pm(T i))`) and the EXISTING Kronecker product collapse
    /// `prod_offdiag_eq_zero` (zero on distinct decoded gates). Unlike the
    /// top-coordinate-only `chi_single_subsetSum_top_zero`, this holds for ANY
    /// distinct gates (arbitrary present coordinate). Constructive, empty
    /// admitted-axiom closure. Idempotent.
    pub(crate) fn register_chi_offdiag_subset_sum_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.chi_offdiag_subsetSum_zero");
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
        self.register_subset_sum_chi_sign_bilinear_theorem()?;
        self.register_prod_offdiag_eq_zero()?;

        let c = GenConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: gen_offdiag_type(&c),
            value: gen_offdiag_value(&c),
        })
    }

    /// Register `BoolAnalysis.chi_diag_subsetSum_cube`: the x-side DIAGONAL
    /// orthonormality `∀ n S, subsetSum n (fun x => χ_S(x)·χ_S(x)) = 2^n`, via
    /// the sign-side bilinear at `S = T` and `prod_diag_eq_cube`. Companion of
    /// `chi_offdiag_subsetSum_zero` exposing the SAME product form. Constructive,
    /// empty admitted-axiom closure. Idempotent.
    pub(crate) fn register_chi_diag_subset_sum_cube(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.chi_diag_subsetSum_cube");
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
        self.register_subset_sum_chi_sign_bilinear_theorem()?;
        self.register_prod_diag_eq_cube()?;

        let c = GenConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: gen_diag_type(&c),
            value: gen_diag_value(&c),
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
    fn test_chi_self_subset_sum_eq_cube_is_constructive_theorem() {
        let mut env = Environment::new();
        env.register_chi_self_subset_sum_eq_cube()
            .expect("register_chi_self_subset_sum_eq_cube");
        env.register_chi_self_subset_sum_eq_cube()
            .expect("idempotent");
        let name = Name::from_string("BoolAnalysis.chi_self_subsetSum_eq_cube");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&info.value.clone().expect("proof"), &info.type_)
            .expect("chi_self_subsetSum_eq_cube must type-check");
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "chi_self_subsetSum_eq_cube must be axiom-free, got {:?}",
            env.axiom_deps(&name)
        );
        assert_eq!(
            env.proof_quality(&name).expect("quality"),
            ProofQuality::Constructive,
        );
    }

    #[test]
    fn test_chi_single_subset_sum_top_zero_is_constructive_theorem() {
        let mut env = Environment::new();
        env.register_chi_single_subset_sum_top_zero()
            .expect("register_chi_single_subset_sum_top_zero");
        env.register_chi_single_subset_sum_top_zero()
            .expect("idempotent");
        let name = Name::from_string("BoolAnalysis.chi_single_subsetSum_top_zero");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&info.value.clone().expect("proof"), &info.type_)
            .expect("chi_single_subsetSum_top_zero must type-check");
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "chi_single_subsetSum_top_zero must be axiom-free, got {:?}",
            env.axiom_deps(&name)
        );
        assert_eq!(
            env.proof_quality(&name).expect("quality"),
            ProofQuality::Constructive,
        );
    }

    #[test]
    fn test_chi_offdiag_subset_sum_zero_is_constructive_theorem() {
        let mut env = Environment::new();
        env.register_chi_offdiag_subset_sum_zero()
            .expect("register_chi_offdiag_subset_sum_zero");
        env.register_chi_offdiag_subset_sum_zero()
            .expect("idempotent");
        let name = Name::from_string("BoolAnalysis.chi_offdiag_subsetSum_zero");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&info.value.clone().expect("proof"), &info.type_)
            .expect("chi_offdiag_subsetSum_zero must type-check");
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "chi_offdiag_subsetSum_zero must be axiom-free, got {:?}",
            env.axiom_deps(&name)
        );
        assert_eq!(
            env.proof_quality(&name).expect("quality"),
            ProofQuality::Constructive,
        );
    }

    #[test]
    fn test_chi_diag_subset_sum_cube_is_constructive_theorem() {
        let mut env = Environment::new();
        env.register_chi_diag_subset_sum_cube()
            .expect("register_chi_diag_subset_sum_cube");
        env.register_chi_diag_subset_sum_cube().expect("idempotent");
        let name = Name::from_string("BoolAnalysis.chi_diag_subsetSum_cube");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&info.value.clone().expect("proof"), &info.type_)
            .expect("chi_diag_subsetSum_cube must type-check");
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "chi_diag_subsetSum_cube must be axiom-free, got {:?}",
            env.axiom_deps(&name)
        );
        assert_eq!(
            env.proof_quality(&name).expect("quality"),
            ProofQuality::Constructive,
        );
    }

    #[test]
    fn test_chi_pair_subset_sum_eq_symm_diff_is_constructive_theorem() {
        let mut env = Environment::new();
        env.register_chi_pair_subset_sum_eq_symm_diff()
            .expect("register_chi_pair_subset_sum_eq_symm_diff");
        env.register_chi_pair_subset_sum_eq_symm_diff()
            .expect("idempotent");
        let name = Name::from_string("BoolAnalysis.chi_pair_subsetSum_eq_symmDiff");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&info.value.clone().expect("proof"), &info.type_)
            .expect("chi_pair_subsetSum_eq_symmDiff must type-check");
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "chi_pair_subsetSum_eq_symmDiff must be axiom-free, got {:?}",
            env.axiom_deps(&name)
        );
        assert_eq!(
            env.proof_quality(&name).expect("quality"),
            ProofQuality::Constructive,
        );
    }
}
