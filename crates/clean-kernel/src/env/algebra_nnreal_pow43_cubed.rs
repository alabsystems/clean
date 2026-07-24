// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — THE pow43 CUBE KEYSTONE: `pow43³ = x⁴` (axiom-free).
//!
//! `NNReal.pow43_cubed : ∀ x (h0:0≤x)(h1:x<1),`
//! `   NNReal.mul (NNReal.mul (pow43 x h0)(pow43 x h0))(pow43 x h0)`
//! `     = NNReal.ofRat (((x·x)·x)·x) h4`   (canonical x⁴ = `ofRat ((x·x·x)·x)`).
//!
//! `pow43 x h0 := NNReal.mul (ofRat x h0)(cbrt x)`, so writing `A := ofRat x h0`
//! and `C := cbrt x`, the LHS is `(A·C)·(A·C)·(A·C)`. The regrouping to the
//! SEPARATED cube `(A·A·A)·(C·C·C)` uses **origin/main's** carrier mul algebra
//! (`init_algebra_nnreal_reverse_square_algebra` seeds `NNReal.ofRat_mul`,
//! `NNReal.mul_comm`, `NNReal.mul_assoc`) plus one LOCAL interchange helper:
//!
//! - `NNReal.ofRat_mul : mul (ofRat a)(ofRat b) = ofRat (a·b)`  — REUSED from
//!   origin (do NOT redefine).
//! - `NNReal.mul_mul_mul_comm : (a·b)·(c·d) = (a·c)·(b·d)`  — the interchange
//!   law, built HERE from origin's `NNReal.mul_assoc`/`mul_comm` only (it is
//!   NOT on origin).
//!
//! Origin's `NNReal.mul_assoc` is `a·(b·c) = (a·b)·c` (RHS-associated), so the
//! interchange chain is adapted to that direction.
//!
//! With those, `(A·C)·(A·C) = (A·A)·(C·C)` (interchange) and then
//! `((A·A)·(C·C))·(A·C) = ((A·A)·A)·((C·C)·C)` (interchange again). The
//! `C`-cube `(C·C)·C = ofRat x h0` is `NNReal.cbrt_cubed`; the `A`-cube
//! `(A·A)·A = ofRat ((x·x)·x)` is two `ofRat_mul`s; a final `ofRat_mul` folds
//! `ofRat ((x·x)·x) · ofRat x = ofRat (((x·x)·x)·x)`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, foundational-only
//! (empty) closure. NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the pow43 cube assembly.
/// Self-contained (no dependency on the prior agent's deleted `NNMulLawConsts`).
struct Pow43CubedConsts {
    nnreal: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    rat_mul_nonneg: Expr,
    nnreal_mul: Expr,
    nnreal_of_rat: Expr,
    nnreal_cbrt: Expr,
    nnreal_pow43: Expr,
    nnreal_mul_comm: Expr,
    nnreal_mul_assoc: Expr,
    nnreal_ofrat_mul: Expr,
    nnreal_mmm_comm: Expr,
    nnreal_cbrt_cubed: Expr,
    eq1: Expr,
    eq_refl1: Expr,
    eq_symm1: Expr,
    eq_trans1: Expr,
    eq_subst1: Expr,
}

impl Pow43CubedConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let kl = |s: &str| Expr::const_(Name::from_string(s), vec![l1.clone()]);
        Self {
            nnreal: k("NNReal"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_mul: k("Rat.mul"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            rat_mul_nonneg: k("Rat.mul_nonneg"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_of_rat: k("NNReal.ofRat"),
            nnreal_cbrt: k("NNReal.cbrt"),
            nnreal_pow43: k("NNReal.pow43"),
            nnreal_mul_comm: k("NNReal.mul_comm"),
            nnreal_mul_assoc: k("NNReal.mul_assoc"),
            nnreal_ofrat_mul: k("NNReal.ofRat_mul"),
            nnreal_mmm_comm: k("NNReal.mul_mul_mul_comm"),
            nnreal_cbrt_cubed: k("NNReal.cbrt_cubed"),
            eq1: kl("Eq"),
            eq_refl1: kl("Eq.refl"),
            eq_symm1: kl("Eq.symm"),
            eq_trans1: kl("Eq.trans"),
            eq_subst1: kl("Eq.subst"),
        }
    }

    fn rmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn rle(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn rlt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    /// `NNReal.mul a b`.
    fn nnmul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
    /// `Eq NNReal a b`.
    fn eq_nn(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            self.eq1.clone(),
            [self.nnreal.clone(), a.clone(), b.clone()],
        )
    }
    /// `@Eq.refl.{1} NNReal a`.
    fn refl_nn(&self, a: &Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.nnreal.clone(), a.clone()])
    }
    /// `@Eq.trans.{1} NNReal a b c hab hbc`.
    fn trans_nn(&self, a: &Expr, b: &Expr, cc: &Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            self.eq_trans1.clone(),
            [
                self.nnreal.clone(),
                a.clone(),
                b.clone(),
                cc.clone(),
                hab,
                hbc,
            ],
        )
    }
    /// `@Eq.symm.{1} NNReal a b h`.
    fn symm_nn(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_symm1.clone(),
            [self.nnreal.clone(), a.clone(), b.clone(), h],
        )
    }
    /// `@Eq.subst.{1} NNReal motive a b h_eq h : motive b`.
    fn subst_nn(&self, motive: Expr, a: &Expr, b: &Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.nnreal.clone(), motive, a.clone(), b.clone(), h_eq, h],
        )
    }
    /// `NNReal.ofRat x h`.
    fn ofrat(&self, x: &Expr, h: &Expr) -> Expr {
        Expr::apps(self.nnreal_of_rat.clone(), [x.clone(), h.clone()])
    }
    /// `NNReal.mul_comm a b : a·b = b·a`.
    fn nn_mul_comm(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul_comm.clone(), [a.clone(), b.clone()])
    }
    /// `NNReal.mul_assoc a b c : a·(b·c) = (a·b)·c`  (origin's direction).
    fn nn_mul_assoc(&self, a: &Expr, b: &Expr, cc: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_mul_assoc.clone(),
            [a.clone(), b.clone(), cc.clone()],
        )
    }
    /// `NNReal.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn nn_mmm(&self, a: &Expr, b: &Expr, cc: &Expr, d: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_mmm_comm.clone(),
            [a.clone(), b.clone(), cc.clone(), d.clone()],
        )
    }
    /// `NNReal.ofRat_mul a b ha hb hab : mul (ofRat a ha)(ofRat b hb) = ofRat (a·b) hab`.
    fn nn_ofrat_mul(&self, a: &Expr, b: &Expr, ha: &Expr, hb: &Expr, hab: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_ofrat_mul.clone(),
            [a.clone(), b.clone(), ha.clone(), hb.clone(), hab.clone()],
        )
    }
    /// `Rat.mul_nonneg a b ha hb : 0 ≤ a·b`.
    fn rat_mul_nonneg(&self, a: &Expr, b: &Expr, ha: &Expr, hb: &Expr) -> Expr {
        Expr::apps(
            self.rat_mul_nonneg.clone(),
            [a.clone(), b.clone(), ha.clone(), hb.clone()],
        )
    }
}

impl Environment {
    /// Register `NNReal.mul_mul_mul_comm` and `NNReal.pow43_cubed`. Reuses
    /// origin's `NNReal.ofRat_mul`/`mul_comm`/`mul_assoc`. Idempotent;
    /// foundational-only closure.
    pub fn init_algebra_nnreal_pow43_cubed(&mut self) -> Result<(), EnvError> {
        // Origin's carrier mul algebra: NNReal.ofRat_mul/mul_comm/mul_assoc.
        self.init_algebra_nnreal_reverse_square_algebra()?;
        self.init_algebra_nnreal_cbrt_identity()?; // NNReal.cbrt_cubed
        self.init_algebra_nnreal_pow43()?; // NNReal.pow43
        self.init_algebra_nnreal_sqrt_squeeze()?; // Rat.mul_nonneg via register_rat_order_proofs

        let c = Pow43CubedConsts::new();
        self.register_nnreal_mul_mul_mul_comm(&c)?;
        self.register_nnreal_pow43_cubed(&c)?;
        Ok(())
    }

    /// `NNReal.mul_mul_mul_comm : ∀ a b c d,`
    /// `   mul (mul a b)(mul c d) = mul (mul a c)(mul b d)`.
    /// From origin's assoc (`a·(b·c)=(a·b)·c`) / comm (`a·b=b·a`) only:
    /// `(a·b)·(c·d) =[symm assoc] a·(b·(c·d)) =[assoc b c d] a·((b·c)·d)`
    /// `=[comm b c]  a·((c·b)·d) =[symm assoc c b d] a·(c·(b·d))`
    /// `=[assoc a c (b·d)] (a·c)·(b·d)`.
    fn register_nnreal_mul_mul_mul_comm(&mut self, c: &Pow43CubedConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.mul_mul_mul_comm");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nn = &c.nnreal;
        let ty = {
            let mut bd = EnvDeclBuilder::new();
            let (a_id, a) = bd.fresh_local(nn.clone());
            let (b_id, bv) = bd.fresh_local(nn.clone());
            let (cc_id, cc) = bd.fresh_local(nn.clone());
            let (d_id, d) = bd.fresh_local(nn.clone());
            let lhs = c.nnmul(&c.nnmul(&a, &bv), &c.nnmul(&cc, &d));
            let rhs = c.nnmul(&c.nnmul(&a, &cc), &c.nnmul(&bv, &d));
            let concl = c.eq_nn(&lhs, &rhs);
            let e = bd.mk_pi(d_id, BinderInfo::Default, nn.clone(), concl);
            let e = bd.mk_pi(cc_id, BinderInfo::Default, nn.clone(), e);
            let e = bd.mk_pi(b_id, BinderInfo::Default, nn.clone(), e);
            bd.finish(bd.mk_pi(a_id, BinderInfo::Default, nn.clone(), e))
        };
        let value = {
            let mut bd = EnvDeclBuilder::new();
            let (a_id, a) = bd.fresh_local(nn.clone());
            let (b_id, bv) = bd.fresh_local(nn.clone());
            let (cc_id, cc) = bd.fresh_local(nn.clone());
            let (d_id, d) = bd.fresh_local(nn.clone());
            let body = build_mmm_comm(c, &bd, &a, &bv, &cc, &d);
            let e = bd.mk_lam(d_id, BinderInfo::Default, nn.clone(), body);
            let e = bd.mk_lam(cc_id, BinderInfo::Default, nn.clone(), e);
            let e = bd.mk_lam(b_id, BinderInfo::Default, nn.clone(), e);
            bd.finish(bd.mk_lam(a_id, BinderInfo::Default, nn.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.pow43_cubed`.
    fn register_nnreal_pow43_cubed(&mut self, c: &Pow43CubedConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.pow43_cubed");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut bd = EnvDeclBuilder::new();
            let (x_id, x) = bd.fresh_local(c.rat.clone());
            let h0_ty = c.rle(c.rat_zero.clone(), x.clone());
            let (h0_id, h0) = bd.fresh_local(h0_ty.clone());
            let h1_ty = c.rlt(x.clone(), c.rat_one.clone());
            let (h1_id, _h1) = bd.fresh_local(h1_ty.clone());
            let pw = Expr::apps(c.nnreal_pow43.clone(), [x.clone(), h0.clone()]);
            let lhs = c.nnmul(&c.nnmul(&pw, &pw), &pw);
            let (x4, h4) = x4_and_proof(c, &x, &h0);
            let rhs = c.ofrat(&x4, &h4);
            let concl = c.eq_nn(&lhs, &rhs);
            let e = bd.mk_pi(h1_id, BinderInfo::Default, h1_ty, concl);
            let e = bd.mk_pi(h0_id, BinderInfo::Default, h0_ty, e);
            bd.finish(bd.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e))
        };
        let value = build_pow43_cubed_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `x⁴ := ((x·x)·x)·x` (left-nested) and `h4 : 0 ≤ x⁴` from `h0 : 0≤x`.
fn x4_and_proof(c: &Pow43CubedConsts, x: &Expr, h0: &Expr) -> (Expr, Expr) {
    let xx = c.rmul(x.clone(), x.clone());
    let xxx = c.rmul(xx.clone(), x.clone());
    let xxxx = c.rmul(xxx.clone(), x.clone());
    let h_xx = c.rat_mul_nonneg(x, x, h0, h0);
    let h_xxx = c.rat_mul_nonneg(&xx, x, &h_xx, h0);
    let h_xxxx = c.rat_mul_nonneg(&xxx, x, &h_xxx, h0);
    (xxxx, h_xxxx)
}

/// Build the `mul_mul_mul_comm` proof body (NNReal interchange, origin assoc dir).
fn build_mmm_comm(
    c: &Pow43CubedConsts,
    parent: &EnvDeclBuilder,
    a: &Expr,
    bv: &Expr,
    cc: &Expr,
    d: &Expr,
) -> Expr {
    // Targets.
    let ab = c.nnmul(a, bv);
    let cd = c.nnmul(cc, d);
    let lhs = c.nnmul(&ab, &cd); // (a·b)·(c·d)
    let ac = c.nnmul(a, cc);
    let bd = c.nnmul(bv, d);
    let rhs = c.nnmul(&ac, &bd); // (a·c)·(b·d)

    // s1 : (a·b)·(c·d) = a·(b·(c·d))   symm (assoc a b (c·d)).
    let t1 = c.nnmul(a, &c.nnmul(bv, &cd)); // a·(b·(c·d))
    let assoc_abcd = c.nn_mul_assoc(a, bv, &cd); // a·(b·(c·d)) = (a·b)·(c·d)
    let s1 = c.symm_nn(&t1, &lhs, assoc_abcd);

    // s2 : a·(b·(c·d)) = a·((b·c)·d)   congr right of assoc b c d.
    let bc = c.nnmul(bv, cc);
    let b_cd = c.nnmul(bv, &cd); // b·(c·d)
    let bc_d = c.nnmul(&bc, d); // (b·c)·d
    let assoc_bcd = c.nn_mul_assoc(bv, cc, d); // b·(c·d) = (b·c)·d
    let s2 = congr_mul_right(c, parent, a, &b_cd, &bc_d, assoc_bcd);
    let t2 = c.nnmul(a, &bc_d); // a·((b·c)·d)

    // s3 : a·((b·c)·d) = a·((c·b)·d)   comm b c under motive a·(□·d).
    let cb = c.nnmul(cc, bv);
    let comm_bc = c.nn_mul_comm(bv, cc); // b·c = c·b
    let inner3 = congr_mul_left(c, parent, &bc, &cb, d, comm_bc); // (b·c)·d = (c·b)·d
    let cb_d = c.nnmul(&cb, d); // (c·b)·d
    let s3 = congr_mul_right(c, parent, a, &bc_d, &cb_d, inner3);
    let t3 = c.nnmul(a, &cb_d); // a·((c·b)·d)

    // s4 : a·((c·b)·d) = a·(c·(b·d))   symm (assoc c b d) under motive a·□.
    let c_bd = c.nnmul(cc, &bd); // c·(b·d)
    let assoc_cbd = c.nn_mul_assoc(cc, bv, d); // c·(b·d) = (c·b)·d
    let inner4 = c.symm_nn(&c_bd, &cb_d, assoc_cbd); // (c·b)·d = c·(b·d)
    let s4 = congr_mul_right(c, parent, a, &cb_d, &c_bd, inner4);
    let t4 = c.nnmul(a, &c_bd); // a·(c·(b·d))

    // s5 : a·(c·(b·d)) = (a·c)·(b·d)   assoc a c (b·d).
    let s5 = c.nn_mul_assoc(a, cc, &bd);

    // Chain: lhs =s1 t1 =s2 t2 =s3 t3 =s4 t4 =s5 rhs.
    let c12 = c.trans_nn(&lhs, &t1, &t2, s1, s2);
    let c13 = c.trans_nn(&lhs, &t2, &t3, c12, s3);
    let c14 = c.trans_nn(&lhs, &t3, &t4, c13, s4);
    c.trans_nn(&lhs, &t4, &rhs, c14, s5)
}

/// `a·p = a·q` from `h : p = q` (congruence in the right factor).
/// `Eq.subst (motive t := a·p = a·t) p q h (Eq.refl (a·p))`.
fn congr_mul_right(
    c: &Pow43CubedConsts,
    parent: &EnvDeclBuilder,
    a: &Expr,
    p: &Expr,
    q: &Expr,
    h_pq: Expr,
) -> Expr {
    let ap = c.nnmul(a, p);
    let motive = {
        let mut mm = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mm.fresh_local(c.nnreal.clone());
        let body = c.eq_nn(&ap, &c.nnmul(a, &t));
        mm.finish_child(mm.mk_lam(t_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    c.subst_nn(motive, p, q, h_pq, c.refl_nn(&ap))
}

/// `p·a = q·a` from `h : p = q` (congruence in the left factor).
fn congr_mul_left(
    c: &Pow43CubedConsts,
    parent: &EnvDeclBuilder,
    p: &Expr,
    q: &Expr,
    a: &Expr,
    h_pq: Expr,
) -> Expr {
    let pa = c.nnmul(p, a);
    let motive = {
        let mut mm = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mm.fresh_local(c.nnreal.clone());
        let body = c.eq_nn(&pa, &c.nnmul(&t, a));
        mm.finish_child(mm.mk_lam(t_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    c.subst_nn(motive, p, q, h_pq, c.refl_nn(&pa))
}

/// The full `pow43_cubed` proof term.
fn build_pow43_cubed_value(c: &Pow43CubedConsts) -> Expr {
    let mut bd = EnvDeclBuilder::new();
    let (x_id, x) = bd.fresh_local(c.rat.clone());
    let h0_ty = c.rle(c.rat_zero.clone(), x.clone());
    let (h0_id, h0) = bd.fresh_local(h0_ty.clone());
    let h1_ty = c.rlt(x.clone(), c.rat_one.clone());
    let (h1_id, h1) = bd.fresh_local(h1_ty.clone());

    // A := ofRat x h0 ; C := cbrt x ; pw := pow43 x h0 = mul A C.
    let a = c.ofrat(&x, &h0);
    let cbrt = Expr::app(c.nnreal_cbrt.clone(), x.clone());
    let pw = Expr::apps(c.nnreal_pow43.clone(), [x.clone(), h0.clone()]);

    // LHS := mul (mul pw pw) pw. `pw` is reducible-defeq `mul A C`.
    let ac = c.nnmul(&a, &cbrt); // A·C  (defeq pw)
    let lhs = c.nnmul(&c.nnmul(&pw, &pw), &pw);

    // ── Regroup (A·C)·(A·C)·(A·C) → ((A·A)·A)·((C·C)·C) ──
    // i1 : (A·C)·(A·C) = (A·A)·(C·C)   mmm A C A C.
    let aa = c.nnmul(&a, &a);
    let cc_ = c.nnmul(&cbrt, &cbrt);
    let acac = c.nnmul(&ac, &ac); // (A·C)·(A·C)
    let aacc = c.nnmul(&aa, &cc_); // (A·A)·(C·C)
    let i1 = c.nn_mmm(&a, &cbrt, &a, &cbrt);
    // i2 : ((A·A)·(C·C))·(A·C) = ((A·A)·A)·((C·C)·C)   mmm (A·A)(C·C) A C.
    let aaa = c.nnmul(&aa, &a); // (A·A)·A
    let ccc = c.nnmul(&cc_, &cbrt); // (C·C)·C
    let i2 = c.nn_mmm(&aa, &cc_, &a, &cbrt);
    let aacc_ac = c.nnmul(&aacc, &ac); // ((A·A)·(C·C))·(A·C)
    let aaa_ccc = c.nnmul(&aaa, &ccc); // ((A·A)·A)·((C·C)·C)

    // step_regroup : (A·C·A·C)·(A·C) = ((A·A)·A)·((C·C)·C).
    //   first rewrite the OUTER-LEFT (A·C)·(A·C) → (A·A)·(C·C) via i1
    //   (congr_mul_left under ·(A·C)), then apply i2.
    let left_rw = congr_mul_left(c, &bd, &acac, &aacc, &ac, i1); // (acac)·ac = (aacc)·ac
    let acac_ac = c.nnmul(&acac, &ac); // (A·C·A·C)·(A·C) = lhs once pw≡A·C.
    let step_regroup = c.trans_nn(&acac_ac, &aacc_ac, &aaa_ccc, left_rw, i2);

    // ── C-cube : (C·C)·C = ofRat x h0 = A   (NNReal.cbrt_cubed). ──
    let ccc_eq_a = Expr::apps(
        c.nnreal_cbrt_cubed.clone(),
        [x.clone(), h0.clone(), h1.clone()],
    ); // (cbrt·cbrt)·cbrt = ofRat x h0

    // ── A-cube : (A·A)·A = ofRat ((x·x)·x) hxxx. ──
    let xx = c.rmul(x.clone(), x.clone());
    let xxx = c.rmul(xx.clone(), x.clone());
    let h_xx = c.rat_mul_nonneg(&x, &x, &h0, &h0);
    let h_xxx = c.rat_mul_nonneg(&xx, &x, &h_xx, &h0);
    // aa = mul A A ; ofRat_mul x x : mul (ofRat x)(ofRat x) = ofRat (x·x).
    let of_xx = c.ofrat(&xx, &h_xx);
    let of_xxx = c.ofrat(&xxx, &h_xxx);
    let aa_eq_ofxx = c.nn_ofrat_mul(&x, &x, &h0, &h0, &h_xx); // A·A = ofRat(x·x)
                                                              // (A·A)·A = ofRat(x·x)·A   congr_mul_left.
    let aaa_to_ofxx_a = congr_mul_left(c, &bd, &aa, &of_xx, &a, aa_eq_ofxx);
    let ofxx_a = c.nnmul(&of_xx, &a); // ofRat(x·x)·ofRat x
                                      // ofRat(x·x)·ofRat x = ofRat((x·x)·x)   ofRat_mul (x·x) x.
    let ofxx_a_eq = c.nn_ofrat_mul(&xx, &x, &h_xx, &h0, &h_xxx);
    // aaa_eq_ofxxx : (A·A)·A = ofRat((x·x)·x).
    let aaa_eq_ofxxx = c.trans_nn(&aaa, &ofxx_a, &of_xxx, aaa_to_ofxx_a, ofxx_a_eq);

    // ── Combine: ((A·A)·A)·((C·C)·C) = ofRat((x·x)·x)·(ofRat x) = ofRat(((x·x)·x)·x). ──
    // first rewrite (C·C)·C → A (= ofRat x h0) via ccc_eq_a, congr_mul_right.
    let aaa_a = c.nnmul(&aaa, &a); // ((A·A)·A)·A
    let ccc_to_a = congr_mul_right(c, &bd, &aaa, &ccc, &a, ccc_eq_a); // aaa·ccc = aaa·A
                                                                      // then rewrite (A·A)·A → ofRat((x·x)·x) via aaa_eq_ofxxx, congr_mul_left (·A).
    let ofxxx_a = c.nnmul(&of_xxx, &a); // ofRat((x·x)·x)·ofRat x
    let aaa_a_to_ofxxx_a = congr_mul_left(c, &bd, &aaa, &of_xxx, &a, aaa_eq_ofxxx); // aaa·A = ofRat(xxx)·A
                                                                                    // ofRat((x·x)·x)·ofRat x = ofRat(((x·x)·x)·x)   ofRat_mul (xxx) x.
    let xxxx = c.rmul(xxx.clone(), x.clone());
    let h_xxxx = c.rat_mul_nonneg(&xxx, &x, &h_xxx, &h0);
    let of_xxxx = c.ofrat(&xxxx, &h_xxxx);
    let ofxxx_a_eq = c.nn_ofrat_mul(&xxx, &x, &h_xxx, &h0, &h_xxxx);

    // chain the combine: aaa_ccc = aaa·A = ofRat(xxx)·A = ofRat(xxxx).
    let comb1 = c.trans_nn(&aaa_ccc, &aaa_a, &ofxxx_a, ccc_to_a, aaa_a_to_ofxxx_a);
    let comb = c.trans_nn(&aaa_ccc, &ofxxx_a, &of_xxxx, comb1, ofxxx_a_eq);

    // FULL: lhs = aaa_ccc (step_regroup) = ofRat(xxxx) (comb).
    let full = c.trans_nn(&lhs, &aaa_ccc, &of_xxxx, step_regroup, comb);

    let e = bd.mk_lam(h1_id, BinderInfo::Default, h1_ty, full);
    let e = bd.mk_lam(h0_id, BinderInfo::Default, h0_ty, e);
    bd.finish(bd.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THMS: &[&str] = &["NNReal.mul_mul_mul_comm", "NNReal.pow43_cubed"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_pow43_cubed()
            .expect("init_algebra_nnreal_pow43_cubed");
        env.init_algebra_nnreal_pow43_cubed().expect("idempotent");
        env
    }

    #[test]
    fn test_pow43_cubed_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THMS {
            let nm = Name::from_string(name);
            let info = env.get_const(&nm).expect("registered");
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_pow43_cubed_constructive_empty_closure() {
        let env = env();
        for name in THMS {
            let nm = Name::from_string(name);
            let info = env.get_const(&nm).expect("registered");
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            assert_eq!(
                env.proof_quality(&nm),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} closure must be foundational-only: {:?}",
                env.axiom_deps(&nm)
            );
        }
    }
}
