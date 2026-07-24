// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — `Rat.mul_lt_mul_add_of_bounds`, the generic
//! single-direction product-perturbation bound `NNReal.IsCauchy_mul` calls
//! twice (once per direction of the two-sided Cauchy conjunction).
//!
//! # Statement
//!
//! ```text
//! Rat.mul_lt_mul_add_of_bounds :
//!   ∀ (am an bm bn B d : Rat),
//!     Rat.le Rat.zero an → Rat.le Rat.zero bm →
//!     Rat.lt an B → Rat.lt bm B → Rat.lt Rat.zero d →
//!     Rat.le am (Rat.add an d) → Rat.le bm (Rat.add bn d) →
//!     Rat.lt (Rat.mul am bm)
//!            (Rat.add (Rat.mul an bn)
//!                     (Rat.add (Rat.mul d B) (Rat.mul d B)))
//! ```
//!
//! # Proof (midpoint `an·bm`)
//!
//! ```text
//!   am·bm ≤ (an+d)·bm = an·bm + d·bm           (mul_le_mul_of_nonneg_right, right_distrib)  (A)
//!   an·bm ≤ an·(bn+d) = an·bn + an·d           (mul_le_mul_of_nonneg_left,  left_distrib)   (B)
//!   ⟹ an·bm + d·bm ≤ (an·bn + an·d) + d·bm     (add_le_add_right on B)                       (C)
//!   ⟹ am·bm ≤ (an·bn + an·d) + d·bm            (le_trans A C)                                (D)
//!            = an·bn + (an·d + d·bm)            (add_assoc)                                   (E)
//!   an·d = d·an < d·B                          (mul_comm, mul_lt_mul_of_pos_left)            (F)
//!   d·bm < d·B                                 (mul_lt_mul_of_pos_left)                       (G)
//!   ⟹ an·d + d·bm < d·B + d·B                  (Rat.add_lt_add F G)                          (H)
//!   ⟹ an·bn + (an·d + d·bm) < an·bn + (d·B+d·B) (Rat.add_lt_add_left H)                       (I)
//!   ⟹ am·bm < an·bn + (d·B + d·B)              (Rat.lt_of_le_of_lt E I).
//! ```
//!
//! Every cited lemma is a kernel-checked `Declaration::Theorem`/`Definition`
//! with foundational-only admitted-axiom closure, so the result is
//! `Constructive` with empty closure. NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, FVarId};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for `Rat.mul_lt_mul_add_of_bounds`.
pub(crate) struct MulCloseConstsRecovered {
    rat: Expr,
    rat_zero: Expr,
    rat_add: Expr,
    rat_mul: Expr,
    rat_lt: Expr,
    le_le: Expr,
    inst_le_rat: Expr,
    mul_le_left: Expr,
    mul_le_right: Expr,
    mul_lt_left: Expr,
    left_distrib: Expr,
    right_distrib: Expr,
    add_assoc: Expr,
    mul_comm: Expr,
    add_lt_add: Expr,
    add_lt_add_left: Expr,
    add_le_add_right: Expr,
    lt_of_le_of_lt: Expr,
    le_trans: Expr,
    eq_symm: Expr,
    eq_subst: Expr,
}

impl MulCloseConstsRecovered {
    pub(crate) fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_add: k("Rat.add"),
            rat_mul: k("Rat.mul"),
            rat_lt: k("Rat.lt"),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: k("instLERat"),
            mul_le_left: k("Rat.mul_le_mul_of_nonneg_left"),
            mul_le_right: k("Rat.mul_le_mul_of_nonneg_right"),
            mul_lt_left: k("Rat.mul_lt_mul_of_pos_left"),
            left_distrib: k("Rat.left_distrib"),
            right_distrib: k("Rat.right_distrib"),
            add_assoc: k("Rat.add_assoc"),
            mul_comm: k("Rat.mul_comm"),
            add_lt_add: k("Rat.add_lt_add"),
            add_lt_add_left: k("Rat.add_lt_add_left"),
            add_le_add_right: k("Rat.add_le_add_right"),
            lt_of_le_of_lt: k("Rat.lt_of_le_of_lt"),
            le_trans: k("Rat.le_trans"),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![lvl1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1]),
        }
    }

    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    /// Bare `Rat.lt a b` (the form the strict order lemmas — `add_lt_add`,
    /// `mul_lt_mul_of_pos_left`, `lt_of_le_of_lt` — produce/consume).
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    /// Typeclass `LE.le Rat instLERat a b` (the `≤` form the order-toolkit
    /// monotonicity lemmas — `mul_le_mul_of_nonneg_*`, `add_le_add_right`,
    /// `le_trans` — produce/consume; definitionally `Rat.le a b`).
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            self.le_le.clone(),
            [self.rat.clone(), self.inst_le_rat.clone(), a, b],
        )
    }
    /// `mul_le_mul_of_nonneg_left a b c (h_bc : b≤c)(h_a : 0≤a) : a·b ≤ a·c`.
    fn mul_le_left(&self, a: Expr, b: Expr, cc: Expr, h_bc: Expr, h_a: Expr) -> Expr {
        Expr::apps(self.mul_le_left.clone(), [a, b, cc, h_bc, h_a])
    }
    /// `mul_le_mul_of_nonneg_right a b c (h_bc : b≤c)(h_a : 0≤a) : b·a ≤ c·a`.
    fn mul_le_right(&self, a: Expr, b: Expr, cc: Expr, h_bc: Expr, h_a: Expr) -> Expr {
        Expr::apps(self.mul_le_right.clone(), [a, b, cc, h_bc, h_a])
    }
    /// `mul_lt_mul_of_pos_left a b c (h_bc : b<c)(h_a : 0<a) : a·b < a·c`.
    fn mul_lt_left(&self, a: Expr, b: Expr, cc: Expr, h_bc: Expr, h_a: Expr) -> Expr {
        Expr::apps(self.mul_lt_left.clone(), [a, b, cc, h_bc, h_a])
    }
    /// `left_distrib a b c : a·(b+c) = a·b + a·c`.
    fn left_distrib(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.left_distrib.clone(), [a, b, cc])
    }
    /// `right_distrib a b c : (a+b)·c = a·c + b·c`.
    fn right_distrib(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.right_distrib.clone(), [a, b, cc])
    }
    /// `add_assoc a b c : (a+b)+c = a+(b+c)`.
    fn add_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.add_assoc.clone(), [a, b, cc])
    }
    /// `mul_comm a b : a·b = b·a`.
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a, b])
    }
    /// `add_lt_add a b c d (a<b)(c<d) : (a+c) < (b+d)`.
    fn add_lt_add(&self, a: Expr, b: Expr, cc: Expr, d: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.add_lt_add.clone(), [a, b, cc, d, h1, h2])
    }
    /// `add_lt_add_left a b c (h : a<b) : (c+a) < (c+b)` (binders a,b,c THEN h).
    fn add_lt_add_left(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(self.add_lt_add_left.clone(), [a, b, cc, h])
    }
    /// `add_le_add_right a b c (h : a≤b) : (a+c) ≤ (b+c)`.
    fn add_le_add_right(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(self.add_le_add_right.clone(), [a, b, cc, h])
    }
    /// `lt_of_le_of_lt a b c (a≤b)(b<c) : a<c`.
    fn lt_of_le_of_lt(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.lt_of_le_of_lt.clone(), [a, b, cc, h1, h2])
    }
    /// `le_trans a b c (a≤b)(b≤c) : a≤c`.
    fn le_trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.le_trans.clone(), [a, b, cc, h1, h2])
    }
    /// `@Eq.symm Rat a b h : Eq Rat b a`.
    fn eq_symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }
    /// `@Eq.subst Rat motive a b h_eq h : motive b`.
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
}

impl Environment {
    /// Register `Rat.mul_lt_mul_add_of_bounds`. Idempotent.
    pub fn init_algebra_rat_mul_close_recovered(&mut self) -> Result<(), EnvError> {
        // left/right distrib, mul_comm, add_assoc.
        self.init_rat_field_inst()?;
        // mul_le_mul_of_nonneg_left/_right, le_trans.
        self.init_boolean_analysis_order_toolkit()?;
        // mul_lt_mul_of_pos_left.
        self.init_boolean_analysis_order_toolkit_b1b()?;
        // add_lt_add, add_lt_add_left, add_le_add_right, lt_of_le_of_lt.
        self.init_boolean_analysis_kkl_strictadd2()?;
        self.init_eq()?;

        let c = MulCloseConstsRecovered::new();
        self.register_rat_mul_lt_mul_add_of_bounds(&c)
    }

    fn register_rat_mul_lt_mul_add_of_bounds(
        &mut self,
        c: &MulCloseConstsRecovered,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.mul_lt_mul_add_of_bounds");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = mul_close_type(c);
        let value = build_mul_close_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// The six leading universally-quantified Rat binders, shared by the type and
/// the proof. Returns `(builder, [am, an, bm, bn, B, d], [ids])`.
fn six_binders(b: &mut EnvDeclBuilder, c: &MulCloseConstsRecovered) -> ([Expr; 6], [FVarId; 6]) {
    let (am_id, am) = b.fresh_local(c.rat.clone());
    let (an_id, an) = b.fresh_local(c.rat.clone());
    let (bm_id, bm) = b.fresh_local(c.rat.clone());
    let (bn_id, bn) = b.fresh_local(c.rat.clone());
    let (bb_id, bb) = b.fresh_local(c.rat.clone());
    let (d_id, d) = b.fresh_local(c.rat.clone());
    (
        [am, an, bm, bn, bb, d],
        [am_id, an_id, bm_id, bn_id, bb_id, d_id],
    )
}

/// The full type of `Rat.mul_lt_mul_add_of_bounds`.
fn mul_close_type(c: &MulCloseConstsRecovered) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let ([am, an, bm, bn, bb, d], [am_id, an_id, bm_id, bn_id, bb_id, d_id]) =
        six_binders(&mut b, c);

    let h0an = c.le(c.rat_zero.clone(), an.clone());
    let h0bm = c.le(c.rat_zero.clone(), bm.clone());
    let han_b = c.lt(an.clone(), bb.clone());
    let hbm_b = c.lt(bm.clone(), bb.clone());
    let h0d = c.lt(c.rat_zero.clone(), d.clone());
    let ham = c.le(am.clone(), c.add(an.clone(), d.clone()));
    let hbm = c.le(bm.clone(), c.add(bn.clone(), d.clone()));

    let (h0an_id, _) = b.fresh_local(h0an.clone());
    let (h0bm_id, _) = b.fresh_local(h0bm.clone());
    let (han_b_id, _) = b.fresh_local(han_b.clone());
    let (hbm_b_id, _) = b.fresh_local(hbm_b.clone());
    let (h0d_id, _) = b.fresh_local(h0d.clone());
    let (ham_id, _) = b.fresh_local(ham.clone());
    let (hbm_id, _) = b.fresh_local(hbm.clone());

    let db = c.mul(d.clone(), bb.clone());
    let concl = c.lt(
        c.mul(am.clone(), bm.clone()),
        c.add(c.mul(an.clone(), bn.clone()), c.add(db.clone(), db)),
    );

    let e = b.mk_pi(hbm_id, BinderInfo::Default, hbm, concl);
    let e = b.mk_pi(ham_id, BinderInfo::Default, ham, e);
    let e = b.mk_pi(h0d_id, BinderInfo::Default, h0d, e);
    let e = b.mk_pi(hbm_b_id, BinderInfo::Default, hbm_b, e);
    let e = b.mk_pi(han_b_id, BinderInfo::Default, han_b, e);
    let e = b.mk_pi(h0bm_id, BinderInfo::Default, h0bm, e);
    let e = b.mk_pi(h0an_id, BinderInfo::Default, h0an, e);
    let e = b.mk_pi(d_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(bb_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(bn_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(bm_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(an_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(am_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

#[allow(clippy::too_many_lines)]
fn build_mul_close_proof(c: &MulCloseConstsRecovered) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let ([am, an, bm, bn, bb, d], [am_id, an_id, bm_id, bn_id, bb_id, d_id]) =
        six_binders(&mut b, c);

    let h0an_ty = c.le(c.rat_zero.clone(), an.clone());
    let (h0an_id, h0an) = b.fresh_local(h0an_ty.clone());
    let h0bm_ty = c.le(c.rat_zero.clone(), bm.clone());
    let (h0bm_id, h0bm) = b.fresh_local(h0bm_ty.clone());
    let han_b_ty = c.lt(an.clone(), bb.clone());
    let (han_b_id, han_b) = b.fresh_local(han_b_ty.clone());
    let hbm_b_ty = c.lt(bm.clone(), bb.clone());
    let (hbm_b_id, hbm_b) = b.fresh_local(hbm_b_ty.clone());
    let h0d_ty = c.lt(c.rat_zero.clone(), d.clone());
    let (h0d_id, h0d) = b.fresh_local(h0d_ty.clone());
    let ham_ty = c.le(am.clone(), c.add(an.clone(), d.clone()));
    let (ham_id, ham) = b.fresh_local(ham_ty.clone());
    let hbm_ty = c.le(bm.clone(), c.add(bn.clone(), d.clone()));
    let (hbm_id, hbm) = b.fresh_local(hbm_ty.clone());

    let an_d = c.add(an.clone(), d.clone()); // an+d
    let bn_d = c.add(bn.clone(), d.clone()); // bn+d
    let am_bm = c.mul(am.clone(), bm.clone());
    let an_bm = c.mul(an.clone(), bm.clone());
    let an_bn = c.mul(an.clone(), bn.clone());
    let d_bm = c.mul(d.clone(), bm.clone());
    let an_d_mul = c.mul(an.clone(), d.clone()); // an·d
    let d_an = c.mul(d.clone(), an.clone()); // d·an
    let d_b = c.mul(d.clone(), bb.clone()); // d·B
    let cross = c.add(an_d_mul.clone(), d_bm.clone()); // an·d + d·bm
    let dbb = c.add(d_b.clone(), d_b.clone()); // d·B + d·B

    // (A) am·bm ≤ an·bm + d·bm.
    //   step1 : am·bm ≤ (an+d)·bm.
    //   `mul_le_right a b c (h_bc:b≤c)(h_a:0≤a) : b·a ≤ c·a` — the FIRST arg is the
    //   FIXED right factor. So a:=bm, b:=am, c:=an+d, h_bc:=ham, h_a:=h0bm.
    let step1 = c.mul_le_right(
        bm.clone(),
        am.clone(),
        an_d.clone(),
        ham.clone(),
        h0bm.clone(),
    );
    //   rd : (an+d)·bm = an·bm + d·bm  [right_distrib an d bm].
    let rd = c.right_distrib(an.clone(), d.clone(), bm.clone());
    //   subst RHS of step1 from (an+d)·bm to an·bm+d·bm: motive t := am·bm ≤ t.
    let motive_a = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.le(am_bm.clone(), t);
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let andbm = c.add(an_bm.clone(), d_bm.clone());
    let step_a = c.subst(
        motive_a,
        c.mul(an_d.clone(), bm.clone()),
        andbm.clone(),
        rd,
        step1,
    ); // am·bm ≤ an·bm + d·bm

    // (B) an·bm ≤ an·bn + an·d.
    //   step2 : an·bm ≤ an·(bn+d)  [mul_le_left an bm (bn+d) hbm h0an].
    let step2 = c.mul_le_left(
        an.clone(),
        bm.clone(),
        bn_d.clone(),
        hbm.clone(),
        h0an.clone(),
    );
    //   ld : an·(bn+d) = an·bn + an·d  [left_distrib an bn d].
    let ld = c.left_distrib(an.clone(), bn.clone(), d.clone());
    let motive_b = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.le(an_bm.clone(), t);
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let anbn_and = c.add(an_bn.clone(), an_d_mul.clone());
    let step_b = c.subst(
        motive_b,
        c.mul(an.clone(), bn_d.clone()),
        anbn_and.clone(),
        ld,
        step2,
    ); // an·bm ≤ an·bn + an·d

    // (C) an·bm + d·bm ≤ (an·bn + an·d) + d·bm  [add_le_add_right step_b].
    let step_c = c.add_le_add_right(an_bm.clone(), anbn_and.clone(), d_bm.clone(), step_b);

    // (D) am·bm ≤ (an·bn + an·d) + d·bm  [le_trans step_a step_c].
    let anbn_and_dbm = c.add(anbn_and.clone(), d_bm.clone());
    let step_d = c.le_trans(
        am_bm.clone(),
        andbm.clone(),
        anbn_and_dbm.clone(),
        step_a,
        step_c,
    );

    // (E) am·bm ≤ an·bn + (an·d + d·bm)  [subst via add_assoc].
    //   aa : (an·bn + an·d) + d·bm = an·bn + (an·d + d·bm).
    let aa = c.add_assoc(an_bn.clone(), an_d_mul.clone(), d_bm.clone());
    let motive_e = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.le(am_bm.clone(), t);
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let anbn_cross = c.add(an_bn.clone(), cross.clone());
    let step_e = c.subst(
        motive_e,
        anbn_and_dbm.clone(),
        anbn_cross.clone(),
        aa,
        step_d,
    ); // am·bm ≤ an·bn + (an·d + d·bm)

    // (F) an·d < d·B.
    //   t1 : d·an < d·B  [mul_lt_left d an B han_b h0d].
    let t1 = c.mul_lt_left(
        d.clone(),
        an.clone(),
        bb.clone(),
        han_b.clone(),
        h0d.clone(),
    );
    //   mc : an·d = d·an  [mul_comm an d]. subst LHS of t1 from d·an to an·d:
    //     motive t := t < d·B.
    let mc = c.mul_comm(an.clone(), d.clone()); // an·d = d·an
    let motive_f = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.lt(t, d_b.clone());
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    // want: an·d < d·B from d·an < d·B and (an·d = d·an).  subst with h_eq : d·an = an·d
    //   i.e. Eq.symm mc, a := d·an, b := an·d.
    let step_f = c.subst(
        motive_f,
        d_an.clone(),
        an_d_mul.clone(),
        c.eq_symm(an_d_mul.clone(), d_an.clone(), mc),
        t1,
    ); // an·d < d·B

    // (G) d·bm < d·B  [mul_lt_left d bm B hbm_b h0d].
    let step_g = c.mul_lt_left(
        d.clone(),
        bm.clone(),
        bb.clone(),
        hbm_b.clone(),
        h0d.clone(),
    );

    // (H) (an·d + d·bm) < (d·B + d·B)  [add_lt_add (an·d)(d·B)(d·bm)(d·B) F G].
    let step_h = c.add_lt_add(
        an_d_mul.clone(),
        d_b.clone(),
        d_bm.clone(),
        d_b.clone(),
        step_f,
        step_g,
    );

    // (I) an·bn + (an·d + d·bm) < an·bn + (d·B + d·B)  [add_lt_add_left cross dbb (an·bn) H].
    let step_i = c.add_lt_add_left(cross.clone(), dbb.clone(), an_bn.clone(), step_h);

    // final : am·bm < an·bn + (d·B + d·B)  [lt_of_le_of_lt E I].
    let anbn_dbb = c.add(an_bn.clone(), dbb.clone());
    let body = c.lt_of_le_of_lt(am_bm, anbn_cross, anbn_dbb, step_e, step_i);

    // Wrap all binders.
    let e = b.mk_lam(hbm_id, BinderInfo::Default, hbm_ty, body);
    let e = b.mk_lam(ham_id, BinderInfo::Default, ham_ty, e);
    let e = b.mk_lam(h0d_id, BinderInfo::Default, h0d_ty, e);
    let e = b.mk_lam(hbm_b_id, BinderInfo::Default, hbm_b_ty, e);
    let e = b.mk_lam(han_b_id, BinderInfo::Default, han_b_ty, e);
    let e = b.mk_lam(h0bm_id, BinderInfo::Default, h0bm_ty, e);
    let e = b.mk_lam(h0an_id, BinderInfo::Default, h0an_ty, e);
    let e = b.mk_lam(d_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(bb_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(bn_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(bm_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(an_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(am_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_mul_close_kernel_check_and_closure() {
        let mut env = Environment::with_prelude();
        env.init_algebra_rat_mul_close_recovered()
            .expect("init_algebra_rat_mul_close_recovered");
        env.init_algebra_rat_mul_close_recovered()
            .expect("idempotent");

        let nm = Name::from_string("Rat.mul_lt_mul_add_of_bounds");
        let info = env.get_const(&nm).expect("registered");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .expect("Rat.mul_lt_mul_add_of_bounds must kernel-check");

        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be foundational-only: {:?}",
            env.axiom_deps(&nm)
        );
    }
}
