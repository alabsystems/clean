// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — the ½-HÖLDER MODULUS for the scaled square root,
//! `√(b+d) ≤ √b + √d` (sqrt SUBADDITIVITY), axiom-free.
//!
//! # Why this module exists (the `NNReal.sqrt` well-definedness modulus)
//!
//! Lifting a per-term square root through `Quot.lift` over the `NNReal` Cauchy
//! carrier needs a UNIFORM continuity modulus: `b_n ~ b'_n` (their values close
//! up) must force `√b_n ~ √b'_n`. The exact analytic content is the ½-Hölder
//! bound `|√a − √b| ≤ √|a − b|`. Over the subtraction-free `NNReal` carrier the
//! clean equivalent is sqrt SUBADDITIVITY:
//!
//! ```text
//!   √(b + d) ≤ √b + √d           (set a = b + d; then √a − √b ≤ √d = √(a−b))
//! ```
//!
//! This is exactly the per-term modulus the `Quot.lift` respect proof for
//! `NNReal.sqrt` consumes (designs note: the ½-Hölder rung of the
//! `2026-06-18-kkl-real-sqrt-layer-plan`). It is also a genuine, standalone,
//! reusable `NNReal` square-root theorem.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `NNReal.sqrtGen_add_le :`
//!     `∀ (b d sbd rbd sb rb sd rd : Rat)`
//!     `  (hb:0≤b)(hd:0≤d)`
//!     `  (hsbd:0≤sbd)(hrbd:0≤rbd)(hrbd1:rbd<1)(heqbd:(b+d)=(sbd·sbd)·rbd)`
//!     `  (hsb:0≤sb)(hrb:0≤rb)(hrb1:rb<1)(heqb:b=(sb·sb)·rb)`
//!     `  (hsd:0≤sd)(hrd:0≤rd)(hrd1:rd<1)(heqd:d=(sd·sd)·rd),`
//!     `  NNReal.le (NNReal.sqrtGen sbd rbd hsbd)`
//!     `           (NNReal.add (NNReal.sqrtGen sb rb hsb)(NNReal.sqrtGen sd rd hsd))`.
//!
//! # Proof (no dyadic-floor work; pure `NNReal` algebra + `le_of_sq_le_sq`)
//!
//! Write `A := √(b+d)`, `B := √b`, `D := √d`. By `le_of_sq_le_sq` it suffices to
//! show `A·A ≤ (B+D)·(B+D)`. First, `A·A = ofRat (b+d)` (`sqrtGen_sq_at` at
//! `b+d`), `ofRat (b+d) = ofRat b + ofRat d` (`ofRat_add`), and
//! `ofRat b = B·B`, `ofRat d = D·D` (`sqrtGen_sq_at` at `b`, `d`, symm), so
//! `A·A = B·B + D·D`. And `(B+D)·(B+D)` expands (`add_mul` + `mul_add` +
//! `add_assoc`/`add_comm`) to `(B·B + D·D) + (B·D + D·B)`, hence
//! `B·B + D·D ≤ (B+D)·(B+D)` is `NNReal.le_self_add (B·B+D·D)(B·D+D·B)`
//! transported along that square expansion. Chaining gives `A·A ≤ (B+D)²`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural` / `Real` / `Rat.dist`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles for the sqrt-subadditivity modulus.
struct SubAddConsts {
    nnreal: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_add: Expr,
    rat_mul: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    nnreal_add: Expr,
    nnreal_mul: Expr,
    nnreal_le: Expr,
    nnreal_of_rat: Expr,
    nnreal_sqrt_gen: Expr,
    nnreal_sqrt_gen_sq_at: Expr,
    nnreal_ofrat_add: Expr,
    nnreal_add_mul: Expr,
    nnreal_mul_add: Expr,
    nnreal_add_assoc: Expr,
    nnreal_add_comm: Expr,
    nnreal_le_self_add: Expr,
    nnreal_le_of_sq_le_sq: Expr,
    rat_le_trans: Expr,
    rat_le_add_of_nonneg_right: Expr,
    eq1: Expr,
    eq_refl1: Expr,
    eq_symm1: Expr,
    eq_trans1: Expr,
    eq_subst1: Expr,
}

impl SubAddConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let kl = |s: &str| Expr::const_(Name::from_string(s), vec![l1.clone()]);
        Self {
            nnreal: k("NNReal"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_add: k("Rat.add"),
            rat_mul: k("Rat.mul"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            nnreal_add: k("NNReal.add"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_le: k("NNReal.le"),
            nnreal_of_rat: k("NNReal.ofRat"),
            nnreal_sqrt_gen: k("NNReal.sqrtGen"),
            nnreal_sqrt_gen_sq_at: k("NNReal.sqrtGen_sq_at"),
            nnreal_ofrat_add: k("NNReal.ofRat_add"),
            nnreal_add_mul: k("NNReal.add_mul"),
            nnreal_mul_add: k("NNReal.mul_add"),
            nnreal_add_assoc: k("NNReal.add_assoc"),
            nnreal_add_comm: k("NNReal.add_comm"),
            nnreal_le_self_add: k("NNReal.le_self_add"),
            nnreal_le_of_sq_le_sq: k("NNReal.le_of_sq_le_sq"),
            rat_le_trans: k("Rat.le_trans"),
            rat_le_add_of_nonneg_right: k("Rat.le_add_of_nonneg_right"),
            eq1: kl("Eq"),
            eq_refl1: kl("Eq.refl"),
            eq_symm1: kl("Eq.symm"),
            eq_trans1: kl("Eq.trans"),
            eq_subst1: kl("Eq.subst"),
        }
    }

    // ── Rat ──
    fn radd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
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
    fn nonneg(&self, a: Expr) -> Expr {
        self.rle(self.rat_zero.clone(), a)
    }
    /// `(s·s)·r`.
    fn ss_r(&self, s: &Expr, r: &Expr) -> Expr {
        let ss = self.rmul(s.clone(), s.clone());
        self.rmul(ss, r.clone())
    }
    /// `0 ≤ b+d` from `hb : 0≤b`, `hd : 0≤d`:
    ///   `le_trans 0 b (b+d) hb (le_add_of_nonneg_right b d hd)`.
    fn add_nonneg(&self, b: &Expr, d: &Expr, hb: &Expr, hd: &Expr) -> Expr {
        let bd = self.radd(b.clone(), d.clone());
        // b ≤ b+d.
        let b_le_bd = Expr::apps(
            self.rat_le_add_of_nonneg_right.clone(),
            [b.clone(), d.clone(), hd.clone()],
        );
        Expr::apps(
            self.rat_le_trans.clone(),
            [self.rat_zero.clone(), b.clone(), bd, hb.clone(), b_le_bd],
        )
    }

    // ── NNReal ──
    fn nnadd(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_add.clone(), [a.clone(), b.clone()])
    }
    fn nnmul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
    fn nnsq(&self, a: &Expr) -> Expr {
        self.nnmul(a, a)
    }
    fn nnle(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_le.clone(), [a.clone(), b.clone()])
    }
    fn ofrat(&self, x: &Expr, h: &Expr) -> Expr {
        Expr::apps(self.nnreal_of_rat.clone(), [x.clone(), h.clone()])
    }
    fn sqrt_gen(&self, s: &Expr, r: &Expr, hs: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_sqrt_gen.clone(),
            [s.clone(), r.clone(), hs.clone()],
        )
    }
    /// `sqrtGen_sq_at x s r hx hs hr hr1 heq : mul a a = ofRat x hx`.
    #[allow(clippy::too_many_arguments)]
    fn sqrt_gen_sq_at(
        &self,
        x: &Expr,
        s: &Expr,
        r: &Expr,
        hx: &Expr,
        hs: &Expr,
        hr: &Expr,
        hr1: &Expr,
        heq: &Expr,
    ) -> Expr {
        Expr::apps(
            self.nnreal_sqrt_gen_sq_at.clone(),
            [
                x.clone(),
                s.clone(),
                r.clone(),
                hx.clone(),
                hs.clone(),
                hr.clone(),
                hr1.clone(),
                heq.clone(),
            ],
        )
    }
    /// `ofRat_add a b ha hb hab : add (ofRat a)(ofRat b) = ofRat (a+b)`.
    fn ofrat_add(&self, a: &Expr, b: &Expr, ha: &Expr, hb: &Expr, hab: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_ofrat_add.clone(),
            [a.clone(), b.clone(), ha.clone(), hb.clone(), hab.clone()],
        )
    }
    /// `add_mul a b c : (a+b)·c = a·c + b·c`.
    fn add_mul(&self, a: &Expr, b: &Expr, cc: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_add_mul.clone(),
            [a.clone(), b.clone(), cc.clone()],
        )
    }
    /// `mul_add c a b : c·(a+b) = c·a + c·b`.
    fn mul_add(&self, cc: &Expr, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_mul_add.clone(),
            [cc.clone(), a.clone(), b.clone()],
        )
    }
    /// `add_assoc a b c : (a+b)+c = a+(b+c)`.
    fn add_assoc(&self, a: &Expr, b: &Expr, cc: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_add_assoc.clone(),
            [a.clone(), b.clone(), cc.clone()],
        )
    }
    /// `add_comm a b : a+b = b+a`.
    fn add_comm(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_add_comm.clone(), [a.clone(), b.clone()])
    }
    /// `le_self_add a b : NNReal.le a (add a b)`.
    fn le_self_add(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_le_self_add.clone(), [a.clone(), b.clone()])
    }
    /// `le_of_sq_le_sq a b (mul a a ≤ mul b b) : NNReal.le a b`.
    fn le_of_sq_le_sq(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.nnreal_le_of_sq_le_sq.clone(),
            [a.clone(), b.clone(), h],
        )
    }

    // ── Eq.{1} over NNReal ──
    fn eq_nn(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            self.eq1.clone(),
            [self.nnreal.clone(), a.clone(), b.clone()],
        )
    }
    fn refl_nn(&self, a: &Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.nnreal.clone(), a.clone()])
    }
    fn symm_nn(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_symm1.clone(),
            [self.nnreal.clone(), a.clone(), b.clone(), h],
        )
    }
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
    /// `@Eq.subst.{1} NNReal motive a b h_eq h : motive b`.
    fn subst_nn(&self, motive: Expr, a: &Expr, b: &Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.nnreal.clone(), motive, a.clone(), b.clone(), h_eq, h],
        )
    }
}

/// `a·p = a·q` from `h : p = q` (congruence in the right factor).
#[cfg(test)]
fn congr_mul_right(
    c: &SubAddConsts,
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

/// `a+p = a+q` from `h : p = q` (congruence in the right summand).
fn congr_add_right(
    c: &SubAddConsts,
    parent: &EnvDeclBuilder,
    a: &Expr,
    p: &Expr,
    q: &Expr,
    h_pq: Expr,
) -> Expr {
    let ap = c.nnadd(a, p);
    let motive = {
        let mut mm = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mm.fresh_local(c.nnreal.clone());
        let body = c.eq_nn(&ap, &c.nnadd(a, &t));
        mm.finish_child(mm.mk_lam(t_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    c.subst_nn(motive, p, q, h_pq, c.refl_nn(&ap))
}

/// `p+a = q+a` from `h : p = q` (congruence in the left summand).
fn congr_add_left(
    c: &SubAddConsts,
    parent: &EnvDeclBuilder,
    p: &Expr,
    q: &Expr,
    a: &Expr,
    h_pq: Expr,
) -> Expr {
    let pa = c.nnadd(p, a);
    let motive = {
        let mut mm = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mm.fresh_local(c.nnreal.clone());
        let body = c.eq_nn(&pa, &c.nnadd(&t, a));
        mm.finish_child(mm.mk_lam(t_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    c.subst_nn(motive, p, q, h_pq, c.refl_nn(&pa))
}

impl Environment {
    /// Register `NNReal.sqrtGen_add_le` (sqrt subadditivity / ½-Hölder modulus).
    /// Idempotent; foundational-only closure.
    pub fn init_algebra_nnreal_sqrt_gen_subadd(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_sqrt_gen()?; // sqrtGen, sqrtGen_sq_at
        self.init_algebra_nnreal_le()?; // NNReal.le, ofRat_le_ofRat
        self.init_algebra_nnreal_reverse_square_sq()?; // NNReal.le_of_sq_le_sq
        self.init_algebra_nnreal_finsum_ofrat()?; // NNReal.ofRat_add
        self.init_algebra_nnreal_add_mul()?; // NNReal.add_mul
        self.init_algebra_nnreal_mul_distrib()?; // NNReal.mul_add
        self.init_algebra_nnreal_add_comm_assoc()?; // NNReal.add_comm, add_assoc
        self.init_algebra_nnreal_le_self_add()?; // NNReal.le_self_add
        self.init_rat_quotient_poc()?; // Rat.le_trans, Rat.le_add_of_nonneg_right
        self.init_eq()?;

        let c = SubAddConsts::new();
        self.register_sqrt_gen_add_le(&c)?;
        Ok(())
    }

    fn register_sqrt_gen_add_le(&mut self, c: &SubAddConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.sqrtGen_add_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = build_subadd_ty(c);
        let value = build_subadd_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// The 16-binder telescope of `NNReal.sqrtGen_add_le`.
fn build_subadd_ty(c: &SubAddConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (dv_id, dv) = b.fresh_local(c.rat.clone());
    let (sbd_id, sbd) = b.fresh_local(c.rat.clone());
    let (rbd_id, rbd) = b.fresh_local(c.rat.clone());
    let (sb_id, sb) = b.fresh_local(c.rat.clone());
    let (rb_id, rb) = b.fresh_local(c.rat.clone());
    let (sd_id, sd) = b.fresh_local(c.rat.clone());
    let (rd_id, rd) = b.fresh_local(c.rat.clone());
    let hb_ty = c.nonneg(bv.clone());
    let (hb_id, _) = b.fresh_local(hb_ty.clone());
    let hd_ty = c.nonneg(dv.clone());
    let (hd_id, _) = b.fresh_local(hd_ty.clone());
    let hsbd_ty = c.nonneg(sbd.clone());
    let (hsbd_id, hsbd) = b.fresh_local(hsbd_ty.clone());
    let hrbd_ty = c.nonneg(rbd.clone());
    let (hrbd_id, _) = b.fresh_local(hrbd_ty.clone());
    let hrbd1_ty = c.rlt(rbd.clone(), c.rat_one.clone());
    let (hrbd1_id, _) = b.fresh_local(hrbd1_ty.clone());
    let bd = c.radd(bv.clone(), dv.clone());
    let heqbd_ty = Expr::apps(
        c.eq1.clone(),
        [c.rat.clone(), bd.clone(), c.ss_r(&sbd, &rbd)],
    );
    let (heqbd_id, _) = b.fresh_local(heqbd_ty.clone());
    let hsb_ty = c.nonneg(sb.clone());
    let (hsb_id, hsb) = b.fresh_local(hsb_ty.clone());
    let hrb_ty = c.nonneg(rb.clone());
    let (hrb_id, _) = b.fresh_local(hrb_ty.clone());
    let hrb1_ty = c.rlt(rb.clone(), c.rat_one.clone());
    let (hrb1_id, _) = b.fresh_local(hrb1_ty.clone());
    let heqb_ty = Expr::apps(c.eq1.clone(), [c.rat.clone(), bv.clone(), c.ss_r(&sb, &rb)]);
    let (heqb_id, _) = b.fresh_local(heqb_ty.clone());
    let hsd_ty = c.nonneg(sd.clone());
    let (hsd_id, hsd) = b.fresh_local(hsd_ty.clone());
    let hrd_ty = c.nonneg(rd.clone());
    let (hrd_id, _) = b.fresh_local(hrd_ty.clone());
    let hrd1_ty = c.rlt(rd.clone(), c.rat_one.clone());
    let (hrd1_id, _) = b.fresh_local(hrd1_ty.clone());
    let heqd_ty = Expr::apps(c.eq1.clone(), [c.rat.clone(), dv.clone(), c.ss_r(&sd, &rd)]);
    let (heqd_id, _) = b.fresh_local(heqd_ty.clone());

    let a = c.sqrt_gen(&sbd, &rbd, &hsbd);
    let big_b = c.sqrt_gen(&sb, &rb, &hsb);
    let big_d = c.sqrt_gen(&sd, &rd, &hsd);
    let rhs = c.nnadd(&big_b, &big_d);
    let concl = c.nnle(&a, &rhs);

    let mk_pi = |b: &mut EnvDeclBuilder, id, ty: Expr, body: Expr| {
        b.mk_pi(id, BinderInfo::Default, ty, body)
    };
    let e = mk_pi(&mut b, heqd_id, heqd_ty, concl);
    let e = mk_pi(&mut b, hrd1_id, hrd1_ty, e);
    let e = mk_pi(&mut b, hrd_id, hrd_ty, e);
    let e = mk_pi(&mut b, hsd_id, hsd_ty, e);
    let e = mk_pi(&mut b, heqb_id, heqb_ty, e);
    let e = mk_pi(&mut b, hrb1_id, hrb1_ty, e);
    let e = mk_pi(&mut b, hrb_id, hrb_ty, e);
    let e = mk_pi(&mut b, hsb_id, hsb_ty, e);
    let e = mk_pi(&mut b, heqbd_id, heqbd_ty, e);
    let e = mk_pi(&mut b, hrbd1_id, hrbd1_ty, e);
    let e = mk_pi(&mut b, hrbd_id, hrbd_ty, e);
    let e = mk_pi(&mut b, hsbd_id, hsbd_ty, e);
    let e = mk_pi(&mut b, hd_id, hd_ty, e);
    let e = mk_pi(&mut b, hb_id, hb_ty, e);
    let e = mk_pi(&mut b, rd_id, c.rat.clone(), e);
    let e = mk_pi(&mut b, sd_id, c.rat.clone(), e);
    let e = mk_pi(&mut b, rb_id, c.rat.clone(), e);
    let e = mk_pi(&mut b, sb_id, c.rat.clone(), e);
    let e = mk_pi(&mut b, rbd_id, c.rat.clone(), e);
    let e = mk_pi(&mut b, sbd_id, c.rat.clone(), e);
    let e = mk_pi(&mut b, dv_id, c.rat.clone(), e);
    let e = mk_pi(&mut b, bv_id, c.rat.clone(), e);
    b.finish(e)
}

/// The proof term of `NNReal.sqrtGen_add_le`.
///
/// `A := √(b+d)`, `B := √b`, `D := √d`. We produce `le_of_sq_le_sq A (B+D) hsq`
/// where `hsq : A·A ≤ (B+D)·(B+D)` is built by transporting
/// `le_self_add (B·B+D·D)(B·D+D·B)` along the two equations
///   `A·A = B·B + D·D`                 (`h_aa`, via sqrtGen_sq_at + ofRat_add),
///   `(B·B+D·D)+(B·D+D·B) = (B+D)·(B+D)`  (`h_sq`, the square expansion).
fn build_subadd_value(c: &SubAddConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (dv_id, dv) = b.fresh_local(c.rat.clone());
    let (sbd_id, sbd) = b.fresh_local(c.rat.clone());
    let (rbd_id, rbd) = b.fresh_local(c.rat.clone());
    let (sb_id, sb) = b.fresh_local(c.rat.clone());
    let (rb_id, rb) = b.fresh_local(c.rat.clone());
    let (sd_id, sd) = b.fresh_local(c.rat.clone());
    let (rd_id, rd) = b.fresh_local(c.rat.clone());
    let hb_ty = c.nonneg(bv.clone());
    let (hb_id, hb) = b.fresh_local(hb_ty.clone());
    let hd_ty = c.nonneg(dv.clone());
    let (hd_id, hd) = b.fresh_local(hd_ty.clone());
    let hsbd_ty = c.nonneg(sbd.clone());
    let (hsbd_id, hsbd) = b.fresh_local(hsbd_ty.clone());
    let hrbd_ty = c.nonneg(rbd.clone());
    let (hrbd_id, hrbd) = b.fresh_local(hrbd_ty.clone());
    let hrbd1_ty = c.rlt(rbd.clone(), c.rat_one.clone());
    let (hrbd1_id, hrbd1) = b.fresh_local(hrbd1_ty.clone());
    let bd = c.radd(bv.clone(), dv.clone());
    let heqbd_ty = Expr::apps(
        c.eq1.clone(),
        [c.rat.clone(), bd.clone(), c.ss_r(&sbd, &rbd)],
    );
    let (heqbd_id, heqbd) = b.fresh_local(heqbd_ty.clone());
    let hsb_ty = c.nonneg(sb.clone());
    let (hsb_id, hsb) = b.fresh_local(hsb_ty.clone());
    let hrb_ty = c.nonneg(rb.clone());
    let (hrb_id, hrb) = b.fresh_local(hrb_ty.clone());
    let hrb1_ty = c.rlt(rb.clone(), c.rat_one.clone());
    let (hrb1_id, hrb1) = b.fresh_local(hrb1_ty.clone());
    let heqb_ty = Expr::apps(c.eq1.clone(), [c.rat.clone(), bv.clone(), c.ss_r(&sb, &rb)]);
    let (heqb_id, heqb) = b.fresh_local(heqb_ty.clone());
    let hsd_ty = c.nonneg(sd.clone());
    let (hsd_id, hsd) = b.fresh_local(hsd_ty.clone());
    let hrd_ty = c.nonneg(rd.clone());
    let (hrd_id, hrd) = b.fresh_local(hrd_ty.clone());
    let hrd1_ty = c.rlt(rd.clone(), c.rat_one.clone());
    let (hrd1_id, hrd1) = b.fresh_local(hrd1_ty.clone());
    let heqd_ty = Expr::apps(c.eq1.clone(), [c.rat.clone(), dv.clone(), c.ss_r(&sd, &rd)]);
    let (heqd_id, heqd) = b.fresh_local(heqd_ty.clone());

    let a = c.sqrt_gen(&sbd, &rbd, &hsbd);
    let big_b = c.sqrt_gen(&sb, &rb, &hsb);
    let big_d = c.sqrt_gen(&sd, &rd, &hsd);

    // h_bd : 0 ≤ b+d, from hb, hd.
    let h_bd = c.add_nonneg(&bv, &dv, &hb, &hd);

    let aa = c.nnsq(&a);
    let bb = c.nnsq(&big_b);
    let dd = c.nnsq(&big_d);
    let bd_cross = c.nnmul(&big_b, &big_d); // B·D
    let db_cross = c.nnmul(&big_d, &big_b); // D·B
    let bb_dd = c.nnadd(&bb, &dd); // B·B + D·D
    let cross = c.nnadd(&bd_cross, &db_cross); // B·D + D·B
    let sum_full = c.nnadd(&bb_dd, &cross); // (B·B+D·D)+(B·D+D·B)
    let big_b_d = c.nnadd(&big_b, &big_d); // B+D
    let sq_rhs = c.nnsq(&big_b_d); // (B+D)·(B+D)

    let of_b = c.ofrat(&bv, &hb);
    let of_d = c.ofrat(&dv, &hd);
    let of_bd = c.ofrat(&bd, &h_bd);

    // ── h_aa : A·A = B·B + D·D ──────────────────────────────────────────────
    // A·A = ofRat(b+d)               (sqrtGen_sq_at at b+d)
    //     = ofRat b + ofRat d        (symm ofRat_add)
    //     = B·B + ofRat d            (congr left, symm sqB)
    //     = B·B + D·D                (congr right, symm sqD)
    let sq_a = c.sqrt_gen_sq_at(&bd, &sbd, &rbd, &h_bd, &hsbd, &hrbd, &hrbd1, &heqbd); // A·A = ofRat(b+d)
    let sq_b = c.sqrt_gen_sq_at(&bv, &sb, &rb, &hb, &hsb, &hrb, &hrb1, &heqb); // B·B = ofRat b
    let sq_d = c.sqrt_gen_sq_at(&dv, &sd, &rd, &hd, &hsd, &hrd, &hrd1, &heqd); // D·D = ofRat d

    // ofRat b + ofRat d = ofRat(b+d) ; we want symm: ofRat(b+d) = ofRat b + ofRat d.
    let ofr_add = c.ofrat_add(&bv, &dv, &hb, &hd, &h_bd); // (ofRat b + ofRat d) = ofRat(b+d)
    let of_b_of_d = c.nnadd(&of_b, &of_d);
    let ofbd_to_obod = c.symm_nn(&of_b_of_d, &of_bd, ofr_add); // ofRat(b+d) = ofRat b + ofRat d

    // congr left: ofRat b → B·B  (needs ofRat b = B·B = symm sq_b).
    let sqb_symm = c.symm_nn(&bb, &of_b, sq_b.clone()); // ofRat b = B·B
    let bb_of_d = c.nnadd(&bb, &of_d);
    let obod_to_bbod = congr_add_left(c, &b, &of_b, &bb, &of_d, sqb_symm); // (ofRat b+ofRat d)=(B·B+ofRat d)
                                                                           // congr right: ofRat d → D·D (ofRat d = D·D = symm sq_d).
    let sqd_symm = c.symm_nn(&dd, &of_d, sq_d.clone()); // ofRat d = D·D
    let bbod_to_bbdd = congr_add_right(c, &b, &bb, &of_d, &dd, sqd_symm); // (B·B+ofRat d)=(B·B+D·D)

    // chain: A·A = ofRat(b+d) = (ofRat b+ofRat d) = (B·B+ofRat d) = (B·B+D·D).
    let t1 = c.trans_nn(&aa, &of_bd, &of_b_of_d, sq_a, ofbd_to_obod);
    let t2 = c.trans_nn(&aa, &of_b_of_d, &bb_of_d, t1, obod_to_bbod);
    let h_aa = c.trans_nn(&aa, &bb_of_d, &bb_dd, t2, bbod_to_bbdd); // A·A = B·B+D·D

    // ── h_sq : (B·B+D·D)+(B·D+D·B) = (B+D)·(B+D) ────────────────────────────
    // (B+D)·(B+D) = B·(B+D) + D·(B+D)              (add_mul B D (B+D))
    //   B·(B+D) = B·B + B·D                        (mul_add B B D)
    //   D·(B+D) = D·B + D·D                        (mul_add D B D)
    // so (B+D)² = (B·B + B·D) + (D·B + D·D).
    // We prove the SYMM direction sum_full = sq_rhs and then symm at use site.
    // Build sq_rhs = (B·B+B·D)+(D·B+D·D) =: rearr0, then re-bracket to sum_full.
    let b_bd = c.nnmul(&big_b, &big_b_d); // B·(B+D)
    let d_bd = c.nnmul(&big_d, &big_b_d); // D·(B+D)
    let bb_bd = c.nnadd(&bb, &bd_cross); // B·B + B·D
    let db_dd = c.nnadd(&db_cross, &dd); // D·B + D·D
    let rearr0 = c.nnadd(&bb_bd, &db_dd); // (B·B+B·D)+(D·B+D·D)

    // step A: (B+D)·(B+D) = B·(B+D) + D·(B+D).
    let exp1 = c.add_mul(&big_b, &big_d, &big_b_d); // sq_rhs = B·(B+D)+D·(B+D)
    let b_bd_d_bd = c.nnadd(&b_bd, &d_bd);
    // step B: B·(B+D) = B·B+B·D ; congr left into (… + D·(B+D)).
    let exp_b = c.mul_add(&big_b, &big_b, &big_d); // B·(B+D)=B·B+B·D
    let bbd_to_bbbd = congr_add_left(c, &b, &b_bd, &bb_bd, &d_bd, exp_b); // (B·(B+D)+D·(B+D))=(B·B+B·D)+D·(B+D)
    let bbbd_d_bd = c.nnadd(&bb_bd, &d_bd);
    // step C: D·(B+D) = D·B+D·D ; congr right.
    let exp_d = c.mul_add(&big_d, &big_b, &big_d); // D·(B+D)=D·B+D·D
    let dbd_to_dbdd = congr_add_right(c, &b, &bb_bd, &d_bd, &db_dd, exp_d); // (B·B+B·D)+D·(B+D)=(B·B+B·D)+(D·B+D·D)

    // sq_rhs = b_bd_d_bd = bbbd_d_bd = rearr0.
    let e1 = c.trans_nn(&sq_rhs, &b_bd_d_bd, &bbbd_d_bd, exp1, bbd_to_bbbd);
    let sq_to_rearr0 = c.trans_nn(&sq_rhs, &bbbd_d_bd, &rearr0, e1, dbd_to_dbdd); // (B+D)² = (B·B+B·D)+(D·B+D·D)

    // Now re-bracket rearr0 = (B·B+B·D)+(D·B+D·D) into sum_full = (B·B+D·D)+(B·D+D·B).
    // Both equal B·B+B·D+D·B+D·D up to assoc/comm. Build the equation
    //   sum_full = rearr0  via the fully-right-associated normal form
    //   N := B·B + (B·D + (D·B + D·D)).
    // sum_full = (B·B+D·D)+(B·D+D·B):
    //   = B·B + (D·D + (B·D + D·B))               [add_assoc]
    //   then reorder D·D+(B·D+D·B) → B·D+(D·B+D·D) … this is getting long.
    // Cleaner: prove rearr0 = sum_full directly via the normal form N.
    let n_inner2 = c.nnadd(&db_cross, &dd); // D·B + D·D
    let n_inner1 = c.nnadd(&bd_cross, &n_inner2); // B·D + (D·B + D·D)
    let nf = c.nnadd(&bb, &n_inner1); // B·B + (B·D + (D·B + D·D))

    // rearr0 = (B·B+B·D)+(D·B+D·D) = B·B + (B·D + (D·B + D·D)) = nf  [add_assoc B·B B·D (D·B+D·D)]
    let rearr0_to_nf = c.add_assoc(&bb, &bd_cross, &db_dd); // (B·B+B·D)+(D·B+D·D) = B·B+(B·D+(D·B+D·D))

    // sum_full = (B·B+D·D)+(B·D+D·B) = B·B + (D·D + (B·D+D·B))  [add_assoc B·B D·D (B·D+D·B)]
    let dd_cross = c.nnadd(&dd, &cross); // D·D + (B·D+D·B)
    let bb_dd_cross = c.nnadd(&bb, &dd_cross); // B·B + (D·D+(B·D+D·B))
    let sumfull_to_split = c.add_assoc(&bb, &dd, &cross); // sum_full = B·B + (D·D+(B·D+D·B))

    // Need: B·B + (D·D+(B·D+D·B)) = nf = B·B + (B·D+(D·B+D·D)).
    // i.e. congr right with  (D·D+(B·D+D·B)) = (B·D+(D·B+D·D)).
    // Prove that inner equation, call it h_inner.
    // LHS = D·D + (B·D + D·B). RHS = B·D + (D·B + D·D).
    // chain: D·D+(B·D+D·B)
    //   = (D·D+B·D)+D·B           [symm add_assoc D·D B·D D·B]
    //   = (B·D+D·D)+D·B           [congr left: D·D+B·D = B·D+D·D, add_comm]
    //   = B·D+(D·D+D·B)           [add_assoc B·D D·D D·B]
    //   = B·D+(D·B+D·D)           [congr right: D·D+D·B = D·B+D·D, add_comm]
    let ddbd = c.nnadd(&dd, &bd_cross); // D·D+B·D
    let ddbd_db = c.nnadd(&ddbd, &db_cross); // (D·D+B·D)+D·B
    let dd_bd_db = c.nnadd(&dd, &cross); // D·D+(B·D+D·B)  (= LHS, since cross=B·D+D·B)
                                         // step i: D·D+(B·D+D·B) = (D·D+B·D)+D·B  (symm add_assoc).
    let aassoc_ddbddb = c.add_assoc(&dd, &bd_cross, &db_cross); // (D·D+B·D)+D·B = D·D+(B·D+D·B)
    let step_i = c.symm_nn(&ddbd_db, &dd_bd_db, aassoc_ddbddb); // D·D+(B·D+D·B) = (D·D+B·D)+D·B
                                                                // step ii: (D·D+B·D)+D·B = (B·D+D·D)+D·B  (congr left add_comm D·D B·D).
    let comm_ddbd = c.add_comm(&dd, &bd_cross); // D·D+B·D = B·D+D·D
    let bddd = c.nnadd(&bd_cross, &dd); // B·D+D·D
    let bddd_db = c.nnadd(&bddd, &db_cross); // (B·D+D·D)+D·B
    let step_ii = congr_add_left(c, &b, &ddbd, &bddd, &db_cross, comm_ddbd); // (D·D+B·D)+D·B = (B·D+D·D)+D·B
                                                                             // step iii: (B·D+D·D)+D·B = B·D+(D·D+D·B)  (add_assoc B·D D·D D·B).
    let ddb = c.nnadd(&dd, &db_cross); // D·D+D·B
    let bd_ddb = c.nnadd(&bd_cross, &ddb); // B·D+(D·D+D·B)
    let step_iii = c.add_assoc(&bd_cross, &dd, &db_cross); // (B·D+D·D)+D·B = B·D+(D·D+D·B)
                                                           // step iv: B·D+(D·D+D·B) = B·D+(D·B+D·D)  (congr right add_comm D·D D·B).
    let comm_ddb = c.add_comm(&dd, &db_cross); // D·D+D·B = D·B+D·D
    let step_iv = congr_add_right(c, &b, &bd_cross, &ddb, &n_inner2, comm_ddb); // B·D+(D·D+D·B)=B·D+(D·B+D·D)

    // assemble h_inner : D·D+(B·D+D·B) = B·D+(D·B+D·D) = n_inner1.
    let hi1 = c.trans_nn(&dd_bd_db, &ddbd_db, &bddd_db, step_i, step_ii);
    let hi2 = c.trans_nn(&dd_bd_db, &bddd_db, &bd_ddb, hi1, step_iii);
    let h_inner = c.trans_nn(&dd_bd_db, &bd_ddb, &n_inner1, hi2, step_iv); // D·D+(B·D+D·B) = n_inner1

    // congr right: B·B + (D·D+(B·D+D·B)) = B·B + n_inner1 = nf.
    let split_to_nf = congr_add_right(c, &b, &bb, &dd_cross, &n_inner1, h_inner); // bb_dd_cross = nf

    // sum_full = bb_dd_cross = nf, and rearr0 = nf, so sum_full = rearr0.
    let sumfull_to_nf = c.trans_nn(&sum_full, &bb_dd_cross, &nf, sumfull_to_split, split_to_nf);
    let nf_to_rearr0 = c.symm_nn(&rearr0, &nf, rearr0_to_nf); // nf = rearr0
    let sumfull_to_rearr0 = c.trans_nn(&sum_full, &nf, &rearr0, sumfull_to_nf, nf_to_rearr0);

    // h_sq : sum_full = (B+D)·(B+D)   (sum_full = rearr0 = sq_rhs).
    let rearr0_to_sq = c.symm_nn(&sq_rhs, &rearr0, sq_to_rearr0); // rearr0 = (B+D)²
    let h_sq = c.trans_nn(&sum_full, &rearr0, &sq_rhs, sumfull_to_rearr0, rearr0_to_sq); // sum_full=(B+D)²

    // ── assemble the square-level inequality ────────────────────────────────
    // base : NNReal.le (B·B+D·D) sum_full   (= le_self_add (B·B+D·D)(B·D+D·B)).
    let base = c.le_self_add(&bb_dd, &cross); // le bb_dd sum_full
                                              // rewrite RHS sum_full → (B+D)²: subst over `fun t => le (B·B+D·D) t`.
    let motive_r = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = m.fresh_local(c.nnreal.clone());
        let body = c.nnle(&bb_dd, &t);
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let le_bbdd_sq = c.subst_nn(motive_r, &sum_full, &sq_rhs, h_sq, base); // le (B·B+D·D) (B+D)²
                                                                           // rewrite LHS B·B+D·D → A·A: subst over `fun t => le t (B+D)²` using symm h_aa.
    let aa_to_bbdd = h_aa; // A·A = B·B+D·D
    let bbdd_to_aa = c.symm_nn(&aa, &bb_dd, aa_to_bbdd); // B·B+D·D = A·A
    let motive_l = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = m.fresh_local(c.nnreal.clone());
        let body = c.nnle(&t, &sq_rhs);
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let hsq_le = c.subst_nn(motive_l, &bb_dd, &aa, bbdd_to_aa, le_bbdd_sq); // le (A·A) (B+D)²

    // le_of_sq_le_sq A (B+D) hsq_le : NNReal.le A (B+D).
    let proof = c.le_of_sq_le_sq(&a, &big_b_d, hsq_le);

    let mk_lam = |b: &mut EnvDeclBuilder, id, ty: Expr, body: Expr| {
        b.mk_lam(id, BinderInfo::Default, ty, body)
    };
    let e = mk_lam(&mut b, heqd_id, heqd_ty, proof);
    let e = mk_lam(&mut b, hrd1_id, hrd1_ty, e);
    let e = mk_lam(&mut b, hrd_id, hrd_ty, e);
    let e = mk_lam(&mut b, hsd_id, hsd_ty, e);
    let e = mk_lam(&mut b, heqb_id, heqb_ty, e);
    let e = mk_lam(&mut b, hrb1_id, hrb1_ty, e);
    let e = mk_lam(&mut b, hrb_id, hrb_ty, e);
    let e = mk_lam(&mut b, hsb_id, hsb_ty, e);
    let e = mk_lam(&mut b, heqbd_id, heqbd_ty, e);
    let e = mk_lam(&mut b, hrbd1_id, hrbd1_ty, e);
    let e = mk_lam(&mut b, hrbd_id, hrbd_ty, e);
    let e = mk_lam(&mut b, hsbd_id, hsbd_ty, e);
    let e = mk_lam(&mut b, hd_id, hd_ty, e);
    let e = mk_lam(&mut b, hb_id, hb_ty, e);
    let e = mk_lam(&mut b, rd_id, c.rat.clone(), e);
    let e = mk_lam(&mut b, sd_id, c.rat.clone(), e);
    let e = mk_lam(&mut b, rb_id, c.rat.clone(), e);
    let e = mk_lam(&mut b, sb_id, c.rat.clone(), e);
    let e = mk_lam(&mut b, rbd_id, c.rat.clone(), e);
    let e = mk_lam(&mut b, sbd_id, c.rat.clone(), e);
    let e = mk_lam(&mut b, dv_id, c.rat.clone(), e);
    let e = mk_lam(&mut b, bv_id, c.rat.clone(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &["NNReal.sqrtGen_add_le"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_sqrt_gen_subadd()
            .expect("init_algebra_nnreal_sqrt_gen_subadd");
        env.init_algebra_nnreal_sqrt_gen_subadd()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_sqrt_gen_add_le_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_sqrt_gen_add_le_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
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
