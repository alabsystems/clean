// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner campaign — ring-identity proof-term builders.
//!
//! The pure equational `Rat` ring identities that the (2,4)-hypercontractivity
//! "even-pair" / B5 step consumes: square expansion `(x+y)² = x² + 2xy + y²`,
//! the `(x−y)²` mirror, and the fourth-power even-pair identity
//! `(A+B)⁴ + (A−B)⁴ = 2·A⁴ + 12·A²·B² + 2·B⁴`.
//!
//! Every term here is built from the genuinely-`Constructive` `Rat` ring
//! surface (`Rat.left_distrib`, `Rat.right_distrib`, `Rat.mul_comm`,
//! `Rat.mul_assoc`, `Rat.add_assoc`, `Rat.add_comm`, `Rat.one_mul`,
//! `Rat.mul_neg`, `Rat.neg_neg`, …) — all `ProofQuality::Constructive` over the
//! quotient carrier — so every identity registered through these builders is
//! itself `Constructive` (empty domain-axiom closure).
//!
//! Split from `boolean_analysis_ring_identities.rs` to keep each file under the
//! 500-line limit (mirrors the order-toolkit split). The registration entry
//! points live in the parent module; this file holds the pure proof-term
//! construction and the `RingConsts` plumbing the registrars consume.

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

// ---------------------------------------------------------------------------
// Ring-identity constants + congruence smart-constructors
// ---------------------------------------------------------------------------

/// Cached kernel constants + congruence smart-constructors for the ring
/// identities. Wraps an `OrderConsts` (for `Rat`, `add`, `mul`, `neg`, `sub`,
/// `eq`, `symm`, `trans`, `subst`, `rat_eq`) and adds the ring lemmas and the
/// `congrArg`-based congruences over `Rat.add` / `Rat.mul`.
pub(super) struct RingConsts {
    pub(super) o: OrderConsts,
    pub(super) congr_arg: Expr,
    pub(super) left_distrib: Expr,
    pub(super) right_distrib: Expr,
    pub(super) mul_comm: Expr,
    pub(super) mul_assoc: Expr,
    pub(super) add_assoc: Expr,
    pub(super) add_comm: Expr,
    pub(super) one_mul: Expr,
    pub(super) mul_neg: Expr,
    pub(super) neg_neg: Expr,
}

impl RingConsts {
    pub(super) fn new() -> Self {
        let u1 = Level::succ(Level::zero());
        Self {
            o: OrderConsts::new(),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![u1.clone(), u1]),
            left_distrib: Expr::const_(Name::from_string("Rat.left_distrib"), vec![]),
            right_distrib: Expr::const_(Name::from_string("Rat.right_distrib"), vec![]),
            mul_comm: Expr::const_(Name::from_string("Rat.mul_comm"), vec![]),
            mul_assoc: Expr::const_(Name::from_string("Rat.mul_assoc"), vec![]),
            add_assoc: Expr::const_(Name::from_string("Rat.add_assoc"), vec![]),
            add_comm: Expr::const_(Name::from_string("Rat.add_comm"), vec![]),
            one_mul: Expr::const_(Name::from_string("Rat.one_mul"), vec![]),
            mul_neg: Expr::const_(Name::from_string("Rat.mul_neg"), vec![]),
            neg_neg: Expr::const_(Name::from_string("Rat.neg_neg"), vec![]),
        }
    }

    // ── re-exported OrderConsts atoms ───────────────────────────────────────
    pub(super) fn rat(&self) -> Expr {
        self.o.rat.clone()
    }
    pub(super) fn one(&self) -> Expr {
        self.o.rat_one.clone()
    }
    pub(super) fn add(&self, a: Expr, b: Expr) -> Expr {
        self.o.add(a, b)
    }
    pub(super) fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.o.mul(a, b)
    }
    pub(super) fn neg(&self, a: Expr) -> Expr {
        self.o.neg(a)
    }
    pub(super) fn sub(&self, a: Expr, b: Expr) -> Expr {
        self.o.sub(a, b)
    }
    pub(super) fn eq(&self, a: Expr, b: Expr) -> Expr {
        self.o.rat_eq(a, b)
    }
    pub(super) fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        self.o.symm(a, b, h)
    }
    pub(super) fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        self.o.trans(a, b, cc, h1, h2)
    }

    /// `Rat.two := Rat.add Rat.one Rat.one`.
    pub(super) fn two(&self) -> Expr {
        self.add(self.one(), self.one())
    }

    /// `n·t` where `n` is a built-up numeral expression.
    pub(super) fn nmul(&self, n: Expr, t: Expr) -> Expr {
        self.mul(n, t)
    }

    // ── ring lemma instances ────────────────────────────────────────────────
    /// `Rat.left_distrib a b c : a·(b+c) = a·b + a·c`.
    pub(super) fn ldist(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.left_distrib.clone(), [a, b, cc])
    }
    /// `Rat.right_distrib a b c : (a+b)·c = a·c + b·c`.
    pub(super) fn rdist(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.right_distrib.clone(), [a, b, cc])
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    pub(super) fn mcomm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a, b])
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    pub(super) fn massoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.mul_assoc.clone(), [a, b, cc])
    }
    /// `Rat.add_assoc a b c : (a+b)+c = a+(b+c)`.
    pub(super) fn aassoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.add_assoc.clone(), [a, b, cc])
    }
    /// `Rat.add_comm a b : a+b = b+a`.
    pub(super) fn acomm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.add_comm.clone(), [a, b])
    }
    /// `Rat.one_mul a : 1·a = a`.
    pub(super) fn one_mul(&self, a: Expr) -> Expr {
        Expr::app(self.one_mul.clone(), a)
    }
    /// `Rat.mul_neg a b : a·(-b) = -(a·b)`.
    pub(super) fn mneg(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_neg.clone(), [a, b])
    }
    /// `Rat.neg_neg a : -(-a) = a`.
    pub(super) fn dneg(&self, a: Expr) -> Expr {
        Expr::app(self.neg_neg.clone(), a)
    }

    // ── congruence over Rat.add / Rat.mul (single-side rewrites) ────────────
    /// `(x `op` fixed) = (y `op` fixed)` from `h : x = y` over `Rat`.
    pub(super) fn cong_left(
        &self,
        parent: &EnvDeclBuilder,
        op: &Expr,
        x: Expr,
        y: Expr,
        fixed: Expr,
        h: Expr,
    ) -> Expr {
        let f = {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = ch.fresh_local(self.rat());
            let body = Expr::apps(op.clone(), [w, fixed]);
            let lam = ch.mk_lam(w_id, BinderInfo::Default, self.rat(), body);
            ch.finish_child(lam)
        };
        Expr::apps(self.congr_arg.clone(), [self.rat(), self.rat(), x, y, f, h])
    }

    /// `(fixed `op` x) = (fixed `op` y)` from `h : x = y` over `Rat`.
    pub(super) fn cong_right(
        &self,
        parent: &EnvDeclBuilder,
        op: &Expr,
        x: Expr,
        y: Expr,
        fixed: Expr,
        h: Expr,
    ) -> Expr {
        let f = {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = ch.fresh_local(self.rat());
            let body = Expr::apps(op.clone(), [fixed, w]);
            let lam = ch.mk_lam(w_id, BinderInfo::Default, self.rat(), body);
            ch.finish_child(lam)
        };
        Expr::apps(self.congr_arg.clone(), [self.rat(), self.rat(), x, y, f, h])
    }

    pub(super) fn add_const(&self) -> Expr {
        self.o.rat_add.clone()
    }
    pub(super) fn mul_const(&self) -> Expr {
        self.o.rat_mul.clone()
    }

    /// `h_two_mul t : (1+1)·t = t + t`.
    ///
    /// `Rat.right_distrib 1 1 t : (1+1)·t = 1·t + 1·t`, then `Rat.one_mul t`
    /// rewrites each `1·t` to `t`.
    pub(super) fn two_mul(&self, parent: &EnvDeclBuilder, t: Expr) -> Expr {
        let one = self.one();
        let two = self.two();
        let two_t = self.mul(two, t.clone());
        let one_t = self.mul(one.clone(), t.clone());
        // d : (1+1)·t = 1·t + 1·t
        let d = self.rdist(one.clone(), one, t.clone());
        let lhs_sum = self.add(one_t.clone(), one_t.clone()); // 1·t + 1·t
                                                              // rewrite left 1·t → t : (1·t + 1·t) = (t + 1·t)
        let h_om = self.one_mul(t.clone()); // 1·t = t
        let add_c = self.add_const();
        let c1 = self.cong_left(
            parent,
            &add_c,
            one_t.clone(),
            t.clone(),
            one_t.clone(),
            h_om.clone(),
        );
        let t_plus_one_t = self.add(t.clone(), one_t.clone()); // t + 1·t
                                                               // rewrite right 1·t → t : (t + 1·t) = (t + t)
        let c2 = self.cong_right(parent, &add_c, one_t.clone(), t.clone(), t.clone(), h_om);
        let t_plus_t = self.add(t.clone(), t.clone());
        // chain: two_t = lhs_sum = t_plus_one_t = t_plus_t
        let s1 = self.trans(two_t.clone(), lhs_sum.clone(), t_plus_one_t.clone(), d, c1);
        self.trans(two_t, t_plus_one_t, t_plus_t, s1, c2)
    }
}

// ---------------------------------------------------------------------------
// add_sq : (x+y)·(x+y) = (x·x + 2·(x·y)) + y·y       [2 := 1+1]
// ---------------------------------------------------------------------------

/// Type of `Rat.add_sq`:
/// `∀ x y : Rat, (x+y)·(x+y) = (x·x + (1+1)·(x·y)) + y·y`.
pub(super) fn add_sq_type(c: &RingConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.rat());
    let (y_id, y) = b.fresh_local(c.rat());
    let lhs = {
        let s = c.add(x.clone(), y.clone());
        c.mul(s.clone(), s)
    };
    let rhs = add_sq_rhs(c, &x, &y);
    let body = c.eq(lhs, rhs);
    let e = b.mk_pi(y_id, BinderInfo::Default, c.rat(), body);
    let e = b.mk_pi(x_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

/// The canonical RHS normal form `(x·x + 2·(x·y)) + y·y`.
pub(super) fn add_sq_rhs(c: &RingConsts, x: &Expr, y: &Expr) -> Expr {
    let xx = c.mul(x.clone(), x.clone());
    let xy = c.mul(x.clone(), y.clone());
    let yy = c.mul(y.clone(), y.clone());
    let two_xy = c.nmul(c.two(), xy);
    c.add(c.add(xx, two_xy), yy)
}

/// The canonical `sub_sq` RHS normal form `(x·x + 2·(x·(−y))) + y·y`.
///
/// Mirrors `add_sq_rhs` with `y ↦ −y` in the cross term, but with the trailing
/// `(−y)·(−y)` already collapsed to `y·y` via `Rat.neg_mul_neg`. The cross term
/// is deliberately left as `x·(−y)` (not `−(x·y)`) so that, when paired with
/// `add_sq_rhs`, the two cross terms are syntactic negatives whose sum cancels
/// through `Rat.mul_neg` in the fourth-power even-pair assembly.
pub(super) fn sub_sq_rhs(c: &RingConsts, x: &Expr, y: &Expr) -> Expr {
    let neg_y = c.neg(y.clone());
    let xx = c.mul(x.clone(), x.clone());
    let x_negy = c.mul(x.clone(), neg_y);
    let yy = c.mul(y.clone(), y.clone());
    let two_x_negy = c.nmul(c.two(), x_negy);
    c.add(c.add(xx, two_x_negy), yy)
}

/// Type of `Rat.sub_sq`:
/// `∀ x y : Rat, (x−y)·(x−y) = (x·x + (1+1)·(x·(−y))) + y·y`.
pub(super) fn sub_sq_type(c: &RingConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.rat());
    let (y_id, y) = b.fresh_local(c.rat());
    let lhs = {
        let d = c.sub(x.clone(), y.clone());
        c.mul(d.clone(), d)
    };
    let rhs = sub_sq_rhs(c, &x, &y);
    let body = c.eq(lhs, rhs);
    let e = b.mk_pi(y_id, BinderInfo::Default, c.rat(), body);
    let e = b.mk_pi(x_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

/// Build the proof term for `Rat.sub_sq`.
///
/// Instantiate `add_sq_core` at `(x, −y)`:
///   `(x+(−y))·(x+(−y)) = (x·x + 2·(x·(−y))) + (−y)·(−y)`.
/// The LHS is definitionally `(x−y)·(x−y)` (reducible `Rat.sub`). Then
/// `Rat.neg_mul_neg y y : (−y)·(−y) = y·y` rewrites the trailing square
/// (lifted over the fixed left addend by `cong_right` on `Rat.add`), giving the
/// canonical `sub_sq` RHS.
pub(super) fn build_sub_sq_proof(c: &RingConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.rat());
    let (y_id, y) = b.fresh_local(c.rat());
    let neg_y = c.neg(y.clone());

    // core : (x+(−y))·(x+(−y)) = (x·x + 2·(x·(−y))) + (−y)·(−y)
    let core = add_sq_core(c, &b, &x, &neg_y);

    // The `add_sq_core` RHS, and the target RHS after the (−y)·(−y) → y·y fold.
    let xx = c.mul(x.clone(), x.clone());
    let x_negy = c.mul(x.clone(), neg_y.clone());
    let two_x_negy = c.nmul(c.two(), x_negy);
    let xx_two = c.add(xx.clone(), two_x_negy.clone()); // x·x + 2·(x·(−y))  (fixed left addend)
    let negy_negy = c.mul(neg_y.clone(), neg_y.clone()); // (−y)·(−y)
    let yy = c.mul(y.clone(), y.clone());
    let core_rhs = c.add(xx_two.clone(), negy_negy.clone());
    let target_rhs = c.add(xx_two.clone(), yy.clone());

    // h_nmn : (−y)·(−y) = y·y   [Rat.neg_mul_neg y y]
    let neg_mul_neg = Expr::const_(Name::from_string("Rat.neg_mul_neg"), vec![]);
    let h_nmn = Expr::apps(neg_mul_neg, [y.clone(), y.clone()]);
    // lift over fixed left addend: core_rhs = target_rhs
    let add_c = c.add_const();
    let cong = c.cong_right(&b, &add_c, negy_negy, yy, xx_two, h_nmn);

    // LHS of the stated identity (used as the trans anchor).
    let xpny = c.add(x.clone(), neg_y); // x + (−y)
    let lhs = c.mul(xpny.clone(), xpny);

    // body : lhs = target_rhs   [trans core cong]
    let body = c.trans(lhs, core_rhs, target_rhs, core, cong);

    let e = b.mk_lam(y_id, BinderInfo::Default, c.rat(), body);
    let e = b.mk_lam(x_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

/// Build the proof term for `Rat.add_sq`.
pub(super) fn build_add_sq_proof(c: &RingConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.rat());
    let (y_id, y) = b.fresh_local(c.rat());
    let body = add_sq_core(c, &b, &x, &y);
    let e = b.mk_lam(y_id, BinderInfo::Default, c.rat(), body);
    let e = b.mk_lam(x_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

/// The `add_sq` proof body for FREE `x`, `y` (parent builder `b`), proving
/// `(x+y)·(x+y) = (x·x + 2·(x·y)) + y·y`. Factored so the `(x−y)²` mirror and
/// the fourth-power identity can reuse it on derived sub-terms.
pub(super) fn add_sq_core(c: &RingConsts, b: &EnvDeclBuilder, x: &Expr, y: &Expr) -> Expr {
    let add_c = c.add_const();
    let xpy = c.add(x.clone(), y.clone());
    let e0 = c.mul(xpy.clone(), xpy.clone()); // (x+y)·(x+y)

    let xpy_x = c.mul(xpy.clone(), x.clone()); // (x+y)·x
    let xpy_y = c.mul(xpy.clone(), y.clone()); // (x+y)·y
    let e1 = c.add(xpy_x.clone(), xpy_y.clone());
    // t1 : e0 = e1
    let t1 = c.ldist(xpy.clone(), x.clone(), y.clone());

    let xx = c.mul(x.clone(), x.clone());
    let yx = c.mul(y.clone(), x.clone());
    let xy = c.mul(x.clone(), y.clone());
    let yy = c.mul(y.clone(), y.clone());
    let xx_yx = c.add(xx.clone(), yx.clone()); // x·x + y·x
    let xy_yy = c.add(xy.clone(), yy.clone()); // x·y + y·y

    // t2a : (x+y)·x = x·x + y·x
    let t2a = c.rdist(x.clone(), y.clone(), x.clone());
    // t2b : (x+y)·y = x·y + y·y
    let t2b = c.rdist(x.clone(), y.clone(), y.clone());

    // c1 : e1 = (x·x+y·x) + (x+y)·y
    let mid1 = c.add(xx_yx.clone(), xpy_y.clone());
    let c1 = c.cong_left(b, &add_c, xpy_x.clone(), xx_yx.clone(), xpy_y.clone(), t2a);
    // c2 : (x·x+y·x) + (x+y)·y = (x·x+y·x) + (x·y+y·y)
    let e2 = c.add(xx_yx.clone(), xy_yy.clone());
    let c2 = c.cong_right(b, &add_c, xpy_y.clone(), xy_yy.clone(), xx_yx.clone(), t2b);

    // c3 : (x·x+y·x) = (x·x+x·y)   [rewrite y·x → x·y]
    let xx_xy = c.add(xx.clone(), xy.clone());
    let h_yx = c.mcomm(y.clone(), x.clone()); // y·x = x·y
    let c3 = c.cong_right(b, &add_c, yx.clone(), xy.clone(), xx.clone(), h_yx);
    // c3' : e2 = (x·x+x·y) + (x·y+y·y)
    let e3 = c.add(xx_xy.clone(), xy_yy.clone());
    let c3p = c.cong_left(b, &add_c, xx_yx.clone(), xx_xy.clone(), xy_yy.clone(), c3);

    // aassoc (x·x) (x·y) (x·y+y·y) : (x·x+x·y)+(x·y+y·y) = x·x + (x·y + (x·y+y·y))
    let inner_r = c.add(xy.clone(), xy_yy.clone()); // x·y + (x·y+y·y)
    let e4 = c.add(xx.clone(), inner_r.clone());
    let a1 = c.aassoc(xx.clone(), xy.clone(), xy_yy.clone());

    // inner regroup: symm (aassoc (x·y)(x·y)(y·y)) :
    //   x·y + (x·y+y·y) = (x·y+x·y)+y·y
    let xy_xy = c.add(xy.clone(), xy.clone());
    let xy_xy_yy = c.add(xy_xy.clone(), yy.clone());
    let a_inner = c.aassoc(xy.clone(), xy.clone(), yy.clone()); // (x·y+x·y)+y·y = x·y+(x·y+y·y)
    let a_inner_sym = c.symm(xy_xy_yy.clone(), inner_r.clone(), a_inner);
    // lift over fixed x·x (cong_right add): e4 = x·x + ((x·y+x·y)+y·y)
    let e5 = c.add(xx.clone(), xy_xy_yy.clone());
    let c5 = c.cong_right(
        b,
        &add_c,
        inner_r.clone(),
        xy_xy_yy.clone(),
        xx.clone(),
        a_inner_sym,
    );

    // symm (aassoc (x·x) (x·y+x·y) (y·y)) :
    //   x·x + ((x·y+x·y)+y·y) = (x·x+(x·y+x·y)) + y·y
    let xx_xy_xy = c.add(xx.clone(), xy_xy.clone());
    let e6 = c.add(xx_xy_xy.clone(), yy.clone());
    let a_outer = c.aassoc(xx.clone(), xy_xy.clone(), yy.clone()); // (x·x+(x·y+x·y))+y·y = x·x+((x·y+x·y)+y·y)
    let a_outer_sym = c.symm(e6.clone(), e5.clone(), a_outer);

    // replace (x·y+x·y) → 2·(x·y)
    let two_xy = c.nmul(c.two(), xy.clone());
    let h_two = c.two_mul(b, xy.clone()); // 2·(x·y) = (x·y)+(x·y)
    let h_two_sym = c.symm(two_xy.clone(), xy_xy.clone(), h_two); // (x·y+x·y) = 2·(x·y)
                                                                  // c7 : (x·x+(x·y+x·y)) = (x·x + 2·(x·y))
    let xx_two_xy = c.add(xx.clone(), two_xy.clone());
    let c7 = c.cong_right(
        b,
        &add_c,
        xy_xy.clone(),
        two_xy.clone(),
        xx.clone(),
        h_two_sym,
    );
    // c7' : e6 = (x·x+2·(x·y)) + y·y
    let rhs = c.add(xx_two_xy.clone(), yy.clone());
    let c7p = c.cong_left(
        b,
        &add_c,
        xx_xy_xy.clone(),
        xx_two_xy.clone(),
        yy.clone(),
        c7,
    );

    // Now trans-chain: e0 → e1 → mid1 → e2 → e3 → e4 → e5 → e6 → rhs
    let s = c.trans(e0.clone(), e1.clone(), mid1.clone(), t1, c1);
    let s = c.trans(e0.clone(), mid1.clone(), e2.clone(), s, c2);
    let s = c.trans(e0.clone(), e2.clone(), e3.clone(), s, c3p);
    let s = c.trans(e0.clone(), e3.clone(), e4.clone(), s, a1);
    let s = c.trans(e0.clone(), e4.clone(), e5.clone(), s, c5);
    let s = c.trans(e0.clone(), e5.clone(), e6.clone(), s, a_outer_sym);
    c.trans(e0, e6, rhs, s, c7p)
}
