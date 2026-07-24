// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! RUNG 3 of the sharp-KKL roadmap: the discrete-derivative 4-norm / 2-norm
//! collapse and its identification with influence.
//!
//! At a fixed `(n, f, i)`, write the (un-halved) discrete derivative on the
//! `{+1,−1}` side as
//!
//! ```text
//! D_i f x := pm (f x) − pm (f (hcFlip n x i))      ∈ {0, ±2}.
//! ```
//!
//! Its square `D·D ∈ {0,4}` and its fourth power `(D·D)·(D·D) ∈ {0,16}` carry
//! the genuine `‖·‖₄⁴ = 4·‖·‖₂²` collapse (O'Donnell §2.2, the `{0,±1}`
//! derivative being supported on the disagreement set). Two landed bricks:
//!
//!   * `deriv_pow4_sum_eq_four_sq` — the **keystone**:
//!     `subsetSum n (fun x => pow4(D_i f x)) = 4 · subsetSum n (fun x => sq(D_i f x))`
//!     (the summed 4-norm = 4·2-norm collapse). Built from the pointwise
//!     `disagree_sq_self_eq_four_mul` (`pow4(D) = 4·sq(D)`) lifted through
//!     `subsetSum_congr` and pulled out by `subsetSum_smul`.
//!   * `deriv_sq_sum_eq_four_disagree` — the 2-norm → disagreement-count bridge:
//!     `subsetSum n (fun x => sq(D_i f x)) = 4 · subsetSum n (fun x => ind(disagree x))`
//!     (pointwise `disagree_sq_bridge`: `sq(D) = 4·ind(disagree)`). Since
//!     `Influence n f i = Expect n (ind∘disagree) = subsetSum n (ind∘disagree) /
//!     2^n`, this is the un-normalized form of the derivative 2-norm = 4·influence
//!     identity (`‖D_i f‖₂² = 4·Inf_i[f]` once divided through by `2^n`).
//!
//! Both are kernel-checked `Declaration::Theorem`s with empty admitted axiom
//! closure (`ProofQuality::Constructive`). Term constructions are byte-identical
//! to the on-branch influence-bridge infrastructure (`subsetSum`, `disagree`,
//! `disagree_sq_bridge`, `disagree_sq_self_eq_four_mul`, `subsetSum_congr`,
//! `subsetSum_smul`) — no new carriers are introduced.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached atoms / term builders for the RUNG-3 derivative-4norm bricks. Every
/// construction mirrors the on-branch `InflConsts` / `HcDualConsts` spellings so
/// the resulting terms are byte-identical to the infrastructure they reuse.
struct DerivConsts {
    nat: Expr,
    rat: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_mul: Expr,
    rat_sub: Expr,
    hcpoint: Expr,
    bool_fn: Expr,
    fin: Expr,
    hc_flip: Expr,
    pm: Expr,
    ind: Expr,
    bool_beq: Expr,
    bool_not: Expr,
    subset_sum: Expr,
    subset_sum_congr: Expr,
    subset_sum_smul: Expr,
    disagree_sq_self: Expr,
    disagree_sq_bridge: Expr,
    expect: Expr,
    influence: Expr,
    rat_inv: Expr,
    rat_mul_assoc: Expr,
    congr_arg: Expr,
    eq1: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
}

impl DerivConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            nat_succ: k("Nat.succ"),
            nat_zero: k("Nat.zero"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            rat_mul: k("Rat.mul"),
            rat_sub: k("Rat.sub"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            fin: k("Fin"),
            hc_flip: k("BoolAnalysis.hcFlip"),
            pm: k("BoolAnalysis.pm"),
            ind: k("BoolAnalysis.ind"),
            bool_beq: k("Bool.beq"),
            bool_not: k("Bool.not"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            subset_sum_congr: k("BoolAnalysis.subsetSum_congr"),
            subset_sum_smul: k("BoolAnalysis.subsetSum_smul"),
            disagree_sq_self: k("BoolAnalysis.disagree_sq_self_eq_four_mul"),
            disagree_sq_bridge: k("BoolAnalysis.disagree_sq_bridge"),
            expect: k("BoolAnalysis.Expect"),
            influence: k("BoolAnalysis.Influence"),
            rat_inv: k("Rat.inv"),
            rat_mul_assoc: k("Rat.mul_assoc"),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1]),
        }
    }

    // ── type helpers ───────────────────────────────────────────────────────
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }

    // ── term builders ──────────────────────────────────────────────────────
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_sub.clone(), [a, b])
    }
    fn pm_(&self, b: Expr) -> Expr {
        Expr::app(self.pm.clone(), b)
    }
    fn ind_(&self, b: Expr) -> Expr {
        Expr::app(self.ind.clone(), b)
    }
    fn sq(&self, d: Expr) -> Expr {
        self.mul(d.clone(), d)
    }
    fn pow4(&self, d: Expr) -> Expr {
        let s = self.sq(d);
        self.mul(s.clone(), s)
    }
    fn hc_flip_(&self, n: &Expr, x: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.hc_flip.clone(), [n.clone(), x.clone(), i.clone()])
    }
    /// `D_i f x := pm (f x) − pm (f (hcFlip n x i))`.
    fn deriv(&self, n: &Expr, f: &Expr, x: &Expr, i: &Expr) -> Expr {
        let fx = Expr::app(f.clone(), x.clone());
        let fflip = Expr::app(f.clone(), self.hc_flip_(n, x, i));
        self.sub(self.pm_(fx), self.pm_(fflip))
    }
    /// `disagree x := Bool.not (Bool.beq (f x) (f (hcFlip n x i)))`.
    fn disagree(&self, n: &Expr, f: &Expr, x: &Expr, i: &Expr) -> Expr {
        let fx = Expr::app(f.clone(), x.clone());
        let fflip = Expr::app(f.clone(), self.hc_flip_(n, x, i));
        Expr::app(
            self.bool_not.clone(),
            Expr::apps(self.bool_beq.clone(), [fx, fflip]),
        )
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    /// `4 : Rat = Rat.mk (Int.ofNat (succ⁴ 0)) 1` — byte-matches
    /// `HcDualConsts::four()` and `InflConsts::rat_four()`.
    fn four(&self) -> Expr {
        let mut k = self.nat_zero.clone();
        for _ in 0..4 {
            k = Expr::app(self.nat_succ.clone(), k);
        }
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), k), one],
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
    fn ssum_congr(&self, n: &Expr, g: Expr, h: Expr, hyp: Expr) -> Expr {
        Expr::apps(self.subset_sum_congr.clone(), [n.clone(), g, h, hyp])
    }
    fn ssum_smul(&self, n: &Expr, cc: Expr, f: Expr) -> Expr {
        Expr::apps(self.subset_sum_smul.clone(), [n.clone(), cc, f])
    }
    /// `disagree_sq_self_eq_four_mul a b : pow4(pm a − pm b) = 4·sq(pm a − pm b)`.
    fn disagree_self(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.disagree_sq_self.clone(), [a, b])
    }
    /// `disagree_sq_bridge a b : 4·ind(not(beq a b)) = (pm a − pm b)·(pm a − pm b)`.
    fn disagree_bridge(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.disagree_sq_bridge.clone(), [a, b])
    }
    /// `Expect n g`.
    fn expect_of(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.expect.clone(), [n.clone(), g])
    }
    /// `Influence n f i`.
    fn influence_of(&self, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.influence.clone(), [n.clone(), f.clone(), i.clone()])
    }
    /// `Rat.inv (Rat.mk (Int.ofNat (Nat.pow 2 n)) 1)` — the inverse of the cube
    /// cardinality `2^n`, spelled byte-identically to `Expect`'s denominator.
    fn cube_inv(&self, n: &Expr) -> Expr {
        let two = Expr::app(
            self.nat_succ.clone(),
            Expr::app(self.nat_succ.clone(), self.nat_zero.clone()),
        );
        let pow2 = Expr::apps(
            Expr::const_(Name::from_string("Nat.pow"), vec![]),
            [two, n.clone()],
        );
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        let denom = Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), pow2), one],
        );
        Expr::app(self.rat_inv.clone(), denom)
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    fn assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_mul_assoc.clone(), [a, b, cc])
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
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, bb, g, h],
        )
    }

    // ── summand-lambda builders (over the cube point `x : HCPoint n`) ───────
    /// `fun x => pow4(D_i f x)`.
    fn pow4_deriv_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let body = self.pow4(self.deriv(n, f, &x, i));
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `fun x => sq(D_i f x)`.
    fn sq_deriv_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let body = self.sq(self.deriv(n, f, &x, i));
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `fun x => 4·sq(D_i f x)`.
    fn scaled_sq_deriv_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let body = self.mul(self.four(), self.sq(self.deriv(n, f, &x, i)));
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `fun x => ind(disagree x)`.
    fn ind_disagree_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let body = self.ind_(self.disagree(n, f, &x, i));
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `fun x => 4·ind(disagree x)`.
    fn scaled_ind_disagree_fn(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        f: &Expr,
        i: &Expr,
    ) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let body = self.mul(self.four(), self.ind_(self.disagree(n, f, &x, i)));
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
}

// ───────────────────── Theorem 1: deriv_pow4_sum_eq_four_sq ─────────────────
//
//   subsetSum n (fun x => pow4(D_i f x)) = 4 · subsetSum n (fun x => sq(D_i f x))

fn pow4_sum_type(c: &DerivConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let f_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    let lhs = c.ssum(&n, c.pow4_deriv_fn(&b, &n, &f, &i));
    let rhs = c.mul(c.four(), c.ssum(&n, c.sq_deriv_fn(&b, &n, &f, &i)));
    let concl = c.eq_rat(lhs, rhs);
    let e = b.mk_pi(i_id, BinderInfo::Default, c.fin_of(&n), concl);
    let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

fn pow4_sum_value(c: &DerivConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let f_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    // leg1 : Σ_x pow4(D x) = Σ_x 4·sq(D x)   (subsetSum_congr + per-x).
    let per_x = {
        let mut xb = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(&n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let fx = Expr::app(f.clone(), x.clone());
        let fflip = Expr::app(f.clone(), c.hc_flip_(&n, &x, &i));
        let pf = c.disagree_self(fx, fflip); // pow4(D) = 4·sq(D)
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, pf))
    };
    let g_pow4 = c.pow4_deriv_fn(&b, &n, &f, &i);
    let g_scaled_sq = c.scaled_sq_deriv_fn(&b, &n, &f, &i);
    let leg1 = c.ssum_congr(&n, g_pow4.clone(), g_scaled_sq.clone(), per_x);

    // leg2 : Σ_x 4·sq(D x) = 4·Σ_x sq(D x)   (subsetSum_smul).
    let g_sq = c.sq_deriv_fn(&b, &n, &f, &i);
    let leg2 = c.ssum_smul(&n, c.four(), g_sq.clone());

    let e0 = c.ssum(&n, g_pow4);
    let e1 = c.ssum(&n, g_scaled_sq);
    let rhs = c.mul(c.four(), c.ssum(&n, g_sq));
    let proof = c.trans(e0, e1, rhs, leg1, leg2);

    let e = b.mk_lam(i_id, BinderInfo::Default, c.fin_of(&n), proof);
    let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

// ──────────────── Theorem 2: deriv_sq_sum_eq_four_disagree ──────────────────
//
//   subsetSum n (fun x => sq(D_i f x)) = 4 · subsetSum n (fun x => ind(disagree x))

fn sq_sum_type(c: &DerivConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let f_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    let lhs = c.ssum(&n, c.sq_deriv_fn(&b, &n, &f, &i));
    let rhs = c.mul(c.four(), c.ssum(&n, c.ind_disagree_fn(&b, &n, &f, &i)));
    let concl = c.eq_rat(lhs, rhs);
    let e = b.mk_pi(i_id, BinderInfo::Default, c.fin_of(&n), concl);
    let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

fn sq_sum_value(c: &DerivConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let f_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    // leg1 : Σ_x sq(D x) = Σ_x 4·ind(disagree x)   (subsetSum_congr + per-x).
    let per_x = {
        let mut xb = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(&n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let fx = Expr::app(f.clone(), x.clone());
        let fflip = Expr::app(f.clone(), c.hc_flip_(&n, &x, &i));
        let sq_d = c.sq(c.deriv(&n, &f, &x, &i));
        let four_ind = c.mul(c.four(), c.ind_(c.disagree(&n, &f, &x, &i)));
        // bridge : 4·ind = sq(D) ;  symm : sq(D) = 4·ind.
        let bridge = c.disagree_bridge(fx, fflip);
        let pf = c.symm(four_ind, sq_d, bridge);
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, pf))
    };
    let g_sq = c.sq_deriv_fn(&b, &n, &f, &i);
    let g_scaled_ind = c.scaled_ind_disagree_fn(&b, &n, &f, &i);
    let leg1 = c.ssum_congr(&n, g_sq.clone(), g_scaled_ind.clone(), per_x);

    // leg2 : Σ_x 4·ind(disagree x) = 4·Σ_x ind(disagree x)   (subsetSum_smul).
    let g_ind = c.ind_disagree_fn(&b, &n, &f, &i);
    let leg2 = c.ssum_smul(&n, c.four(), g_ind.clone());

    let e0 = c.ssum(&n, g_sq);
    let e1 = c.ssum(&n, g_scaled_ind);
    let rhs = c.mul(c.four(), c.ssum(&n, g_ind));
    let proof = c.trans(e0, e1, rhs, leg1, leg2);

    let e = b.mk_lam(i_id, BinderInfo::Default, c.fin_of(&n), proof);
    let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

// ───────────── Theorem 3: derivative_4norm_eq_4_influence ───────────────────
//
//   Expect n (fun x => sq(D_i f x)) = 4 · Influence n f i
//
// The normalized derivative 2-norm equals 4·influence. `Influence` δ-unfolds to
// `Expect n (ind∘disagree)`, and both `Expect`s δ-unfold through `Rat.div ·` to
// `Rat.mul (subsetSum n ·) (Rat.inv (2^n))`. So, writing `Q = subsetSum n
// (sq∘D)`, `S = subsetSum n (ind∘disagree)`, `Dinv = Rat.inv 2^n`:
//
//   LHS ≡ Q·Dinv,    RHS ≡ 4·(S·Dinv).
//
// From Theorem 2, `Q = 4·S`; `congrArg (·Dinv)` gives `Q·Dinv = (4·S)·Dinv`,
// then `Rat.mul_assoc 4 S Dinv` gives `(4·S)·Dinv = 4·(S·Dinv)`. The kernel
// def-eq-reduces the stated `Expect`/`Influence` endpoints to these `Rat.mul`/
// `Rat.inv` forms.

fn influence_eq_type(c: &DerivConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let f_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    let lhs = c.expect_of(&n, c.sq_deriv_fn(&b, &n, &f, &i));
    let rhs = c.mul(c.four(), c.influence_of(&n, &f, &i));
    let concl = c.eq_rat(lhs, rhs);
    let e = b.mk_pi(i_id, BinderInfo::Default, c.fin_of(&n), concl);
    let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

fn influence_eq_value(c: &DerivConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let f_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    let dinv = c.cube_inv(&n);
    let four = c.four();
    let q = c.ssum(&n, c.sq_deriv_fn(&b, &n, &f, &i)); // subsetSum(sq∘D)
    let s = c.ssum(&n, c.ind_disagree_fn(&b, &n, &f, &i)); // subsetSum(ind∘disagree)

    // h_t2 : Q = 4·S   (deriv_sq_sum_eq_four_disagree n f i).
    let h_t2 = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.deriv_sq_sum_eq_four_disagree"),
            vec![],
        ),
        [n.clone(), f.clone(), i.clone()],
    );
    let four_s = c.mul(four.clone(), s.clone());

    // step1 : Q·Dinv = (4·S)·Dinv   congrArg (·Dinv) h_t2.
    let step1 = c.mul_right_congr(&b, &dinv, q.clone(), four_s.clone(), h_t2);
    // step2 : (4·S)·Dinv = 4·(S·Dinv)   mul_assoc 4 S Dinv.
    let step2 = c.assoc(four.clone(), s.clone(), dinv.clone());

    let q_dinv = c.mul(q, dinv.clone());
    let four_s_dinv = c.mul(four_s, dinv.clone());
    let s_dinv = c.mul(s, dinv);
    let four_sdinv = c.mul(four, s_dinv);
    let proof = c.trans(q_dinv, four_s_dinv, four_sdinv, step1, step2);

    let e = b.mk_lam(i_id, BinderInfo::Default, c.fin_of(&n), proof);
    let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

impl Environment {
    /// Register `BoolAnalysis.deriv_pow4_sum_eq_four_sq` — the RUNG-3 keystone:
    /// the summed 4-norm / 2-norm collapse of the discrete derivative,
    /// `subsetSum n (fun x => pow4(D_i f x)) = 4 · subsetSum n (fun x => sq(D_i f x))`.
    /// Kernel-checked, constructive, empty admitted closure. Idempotent.
    pub fn register_deriv_pow4_sum_eq_four_sq(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.deriv_pow4_sum_eq_four_sq");
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
        self.register_subset_sum_smul_theorem()?;
        self.register_disagree_sq_self_eq_four_mul()?;

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = DerivConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: pow4_sum_type(&c),
            value: pow4_sum_value(&c),
        })
    }

    /// Register `BoolAnalysis.deriv_sq_sum_eq_four_disagree` — the 2-norm →
    /// disagreement-count bridge,
    /// `subsetSum n (fun x => sq(D_i f x)) = 4 · subsetSum n (fun x => ind(disagree x))`.
    /// Since `Influence n f i = subsetSum n (ind∘disagree) / 2^n`, this is the
    /// un-normalized derivative-2norm = 4·influence identity. Kernel-checked,
    /// constructive, empty admitted closure. Idempotent.
    pub fn register_deriv_sq_sum_eq_four_disagree(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.deriv_sq_sum_eq_four_disagree");
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
        self.register_subset_sum_smul_theorem()?;
        self.register_disagree_sq_bridge()?;

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = DerivConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: sq_sum_type(&c),
            value: sq_sum_value(&c),
        })
    }

    /// Register `BoolAnalysis.derivative_4norm_eq_4_influence` — the RUNG-3
    /// target: the normalized discrete-derivative 2-norm equals four times the
    /// influence, `Expect n (fun x => sq(D_i f x)) = 4 · Influence n f i`. Built
    /// from `deriv_sq_sum_eq_four_disagree` by pushing the common `Rat.inv 2^n`
    /// factor of `Expect`/`Influence` through `Rat.mul_assoc`. Kernel-checked,
    /// constructive, empty admitted closure. Idempotent.
    pub fn register_derivative_4norm_eq_4_influence(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.derivative_4norm_eq_4_influence");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // Expect, Influence (reducible defs)
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_deriv_sq_sum_eq_four_disagree()?;
        self.init_rat()?; // Rat.inv
        self.init_rat_field_inst()?; // Rat.mul_assoc

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = DerivConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: influence_eq_type(&c),
            value: influence_eq_value(&c),
        })
    }

    /// Register all RUNG-3 derivative-4norm bricks. Idempotent.
    pub fn init_boolean_analysis_deriv_4norm(&mut self) -> Result<(), EnvError> {
        self.register_deriv_pow4_sum_eq_four_sq()?;
        self.register_deriv_sq_sum_eq_four_disagree()?;
        self.register_derivative_4norm_eq_4_influence()?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_deriv_4norm()
            .expect("init_boolean_analysis_deriv_4norm");
        env.init_boolean_analysis_deriv_4norm().expect("idempotent");
        env
    }

    fn assert_constructive_theorem(env: &Environment, name: &str) {
        let n = Name::from_string(name);
        let info = env.get_const(&n).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
        let tc = TypeChecker::with_mode(env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(n.clone(), vec![]))
            .unwrap_or_else(|e| panic!("{name} should type-check: {e:?}"));
        let deps = env.axiom_deps(&n).expect("deps");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(
            names.is_empty(),
            "{name} closure must be ⊆ FOUNDATIONAL_AXIOMS, got {names:?}"
        );
        assert!(
            matches!(env.proof_quality(&n), Some(ProofQuality::Constructive)),
            "{name} must be Constructive"
        );
    }

    #[test]
    fn test_deriv_pow4_sum_eq_four_sq_constructive() {
        assert_constructive_theorem(&env(), "BoolAnalysis.deriv_pow4_sum_eq_four_sq");
    }

    #[test]
    fn test_deriv_sq_sum_eq_four_disagree_constructive() {
        assert_constructive_theorem(&env(), "BoolAnalysis.deriv_sq_sum_eq_four_disagree");
    }

    #[test]
    fn test_derivative_4norm_eq_4_influence_constructive() {
        assert_constructive_theorem(&env(), "BoolAnalysis.derivative_4norm_eq_4_influence");
    }
}
