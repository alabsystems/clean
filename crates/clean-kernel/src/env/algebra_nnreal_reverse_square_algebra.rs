// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — the routine de-square carrier algebra:
//! `NNReal.ofRat_mul`, `NNReal.mul_comm`, `NNReal.mul_assoc`.
//!
//! # Why this module exists
//!
//! The de-square (`W² ≤ 16·Inf³` over Rat ⟹ `W ≤ 4·Inf^{3/2}` over NNReal)
//! supplies the `IsRpow32`-style witnesses by writing the RHS square
//! `(4·Inf^{3/2})²` as `ofRat(16·Inf³)` via `sqrtRat_mul_self` + `ofRat_mul`, then
//! invoking `le_of_sq_le_sq`. That rewrite needs the multiplicative carrier
//! algebra lifted to `NNReal`.
//!
//! Each lemma is `Quot.sound` (for `ofRat_mul`) or nested `Quot.ind` +
//! `Quot.sound` (for `mul_comm`/`mul_assoc`) on a per-index `Equiv` whose leaf
//! `h_eq` is a single `Rat`-level equality (`Eq.refl`, `Rat.mul_comm`, or
//! `Rat.mul_assoc`) — the `NNRat.val_mul`/`NNRat.ofRat` projections fire
//! DEFINITIONALLY, so the leaf reduces to the corresponding `Rat` identity, and
//! the two strict bounds are the constant-`Equiv` `v < v + ε` pattern
//! (mirroring `NNReal.ofRat_add`).
//!
//! - `NNReal.ofRat_mul : ∀ a b ha hb hab,
//!     mul (ofRat a ha)(ofRat b hb) = ofRat (Rat.mul a b) hab`.
//! - `NNReal.mul_comm : ∀ a b, mul a b = mul b a`.
//! - `NNReal.mul_assoc : ∀ a b c, mul a (mul b c) = mul (mul a b) c`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the carrier mul algebra.
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
pub(crate) struct MulAlgConsts {
    nat: Expr,
    nat_zero: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_add: Expr,
    rat_mul: Expr,
    rat_lt: Expr,
    rat_le: Expr,
    rat_mul_comm: Expr,
    rat_mul_assoc: Expr,
    rat_add_zero: Expr,
    rat_add_lt_add_left: Expr,
    nat_le: Expr,
    #[cfg(test)]
    nnrat: Expr,
    nnrat_val: Expr,
    nnrat_of_rat: Expr,
    causeq: Expr,
    causeq_seq: Expr,
    causeq_equiv: Expr,
    causeq_mul: Expr,
    causeq_const: Expr,
    // logic / Eq.{1}.
    and_c: Expr,
    and_intro: Expr,
    #[cfg(test)]
    exists_c: Expr,
    exists_intro: Expr,
    eq1: Expr,
    eq_refl1: Expr,
    eq_symm1: Expr,
    eq_subst1: Expr,
    quot: Expr,
    quot_mk: Expr,
    quot_sound: Expr,
    quot_ind: Expr,
}

impl MulAlgConsts {
    pub(crate) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_add: k("Rat.add"),
            rat_mul: k("Rat.mul"),
            rat_lt: k("Rat.lt"),
            rat_le: k("Rat.le"),
            rat_mul_comm: k("Rat.mul_comm"),
            rat_mul_assoc: k("Rat.mul_assoc"),
            rat_add_zero: k("Rat.add_zero"),
            rat_add_lt_add_left: k("Rat.add_lt_add_left"),
            nat_le: k("Nat.le"),
            #[cfg(test)]
            nnrat: k("NNRat"),
            nnrat_val: k("NNRat.val"),
            nnrat_of_rat: k("NNRat.ofRat"),
            causeq: k("NNReal.CauSeq"),
            causeq_seq: k("NNReal.CauSeq.seq"),
            causeq_equiv: k("NNReal.CauSeq.Equiv"),
            causeq_mul: k("NNReal.CauSeq.mul"),
            causeq_const: k("NNReal.CauSeq.const"),
            and_c: k("And"),
            and_intro: k("And.intro"),
            #[cfg(test)]
            exists_c: Expr::const_(Name::from_string("Exists"), vec![l1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![l1.clone()]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_subst1: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            quot: Expr::const_(Name::from_string("Quot"), vec![l1.clone()]),
            quot_mk: Expr::const_(Name::from_string("Quot.mk"), vec![l1.clone()]),
            quot_sound: Expr::const_(Name::from_string("Quot.sound"), vec![l1.clone()]),
            quot_ind: Expr::const_(Name::from_string("Quot.ind"), vec![l1]),
        }
    }

    fn radd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn rmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn rlt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn rle(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    /// `NNRat.val (CauSeq.seq x m)`.
    fn vseq(&self, x: &Expr, m: &Expr) -> Expr {
        let seq = Expr::app(Expr::app(self.causeq_seq.clone(), x.clone()), m.clone());
        Expr::app(self.nnrat_val.clone(), seq)
    }
    fn nnreal(&self) -> Expr {
        Expr::apps(
            self.quot.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone()],
        )
    }
    fn quot_mk(&self, l: Expr) -> Expr {
        Expr::apps(
            self.quot_mk.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone(), l],
        )
    }
    fn cau_mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_mul.clone(), [a, b])
    }
    fn nn_mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("NNReal.mul"), vec![]),
            [a, b],
        )
    }
    fn eq_nnreal(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.nnreal(), a, b])
    }
    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    fn eq_rat_ty(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), a, b])
    }
    fn refl_rat(&self, a: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.rat.clone(), a])
    }
    fn eq_symm_rat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.rat.clone(), a, b, h])
    }
    fn subst_rat(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    fn add_zero(&self, a: Expr) -> Expr {
        Expr::app(self.rat_add_zero.clone(), a)
    }
    fn add_lt_add_left(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_add_lt_add_left.clone(), [a, b, cc, h])
    }
    fn quot_sound(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.quot_sound.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone(), a, b, h],
        )
    }
}

impl Environment {
    /// Register `NNReal.ofRat_mul`, `NNReal.mul_comm`, `NNReal.mul_assoc`.
    /// Idempotent.
    pub fn init_algebra_nnreal_reverse_square_algebra(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_mul_lift()?; // NNReal.mul, CauSeq.mul, NNRat.val_mul
        self.init_rat_field_inst()?; // Rat.add_zero
        self.register_rat_mul_comm_proof()?; // Rat.mul_comm
        self.register_rat_mul_assoc_proof()?; // Rat.mul_assoc
        self.register_rat_add_lt_add_left()?; // Rat.add_lt_add_left
        self.init_eq()?;
        self.init_and()?;
        self.init_exists()?;

        let c = MulAlgConsts::new();
        self.register_nnreal_ofrat_mul(&c)?;
        self.register_nnreal_mul_comm(&c)?;
        self.register_nnreal_mul_assoc(&c)?;
        Ok(())
    }

    /// `NNReal.ofRat_mul : ∀ (a b : Rat)(ha : 0≤a)(hb : 0≤b)(hab : 0≤a·b),
    ///     NNReal.mul (NNReal.ofRat a ha)(NNReal.ofRat b hb)
    ///       = NNReal.ofRat (Rat.mul a b) hab`.
    fn register_nnreal_ofrat_mul(&mut self, c: &MulAlgConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.ofRat_mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let of_rat = Expr::const_(Name::from_string("NNReal.ofRat"), vec![]);
        let nn_of = |x: Expr, h: Expr| Expr::apps(of_rat.clone(), [x, h]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bb_id, bb) = b.fresh_local(c.rat.clone());
            let ha_ty = c.rle(c.rat_zero.clone(), a.clone());
            let (ha_id, ha) = b.fresh_local(ha_ty.clone());
            let hb_ty = c.rle(c.rat_zero.clone(), bb.clone());
            let (hb_id, hb) = b.fresh_local(hb_ty.clone());
            let hab_ty = c.rle(c.rat_zero.clone(), c.rmul(a.clone(), bb.clone()));
            let (hab_id, hab) = b.fresh_local(hab_ty.clone());
            let lhs = c.nn_mul(nn_of(a.clone(), ha), nn_of(bb.clone(), hb));
            let rhs = nn_of(c.rmul(a.clone(), bb.clone()), hab);
            let concl = c.eq_nnreal(lhs, rhs);
            let e = b.mk_pi(hab_id, BinderInfo::Default, hab_ty, concl);
            let e = b.mk_pi(hb_id, BinderInfo::Default, hb_ty, e);
            let e = b.mk_pi(ha_id, BinderInfo::Default, ha_ty, e);
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bb_id, bb) = b.fresh_local(c.rat.clone());
            let ha_ty = c.rle(c.rat_zero.clone(), a.clone());
            let (ha_id, ha) = b.fresh_local(ha_ty.clone());
            let hb_ty = c.rle(c.rat_zero.clone(), bb.clone());
            let (hb_id, hb) = b.fresh_local(hb_ty.clone());
            let hab_ty = c.rle(c.rat_zero.clone(), c.rmul(a.clone(), bb.clone()));
            let (hab_id, hab) = b.fresh_local(hab_ty.clone());

            // The two raw CauSeqs the goal sides ι-reduce to:
            //   cl = CauSeq.mul (const (NNRat.ofRat a ha))(const (NNRat.ofRat b hb))
            //   cr = const (NNRat.ofRat (a·b) hab)
            let nn_a = Expr::apps(c.nnrat_of_rat.clone(), [a.clone(), ha]);
            let nn_b = Expr::apps(c.nnrat_of_rat.clone(), [bb.clone(), hb]);
            let ab = c.rmul(a.clone(), bb.clone());
            let nn_ab = Expr::apps(c.nnrat_of_rat.clone(), [ab, hab]);
            let const_a = Expr::app(c.causeq_const.clone(), nn_a);
            let const_b = Expr::app(c.causeq_const.clone(), nn_b);
            let cl = c.cau_mul(const_a, const_b);
            let cr = Expr::app(c.causeq_const.clone(), nn_ab);

            // h_eq builder: at index m, both vals ι-reduce to `a·b`, so refl.
            let h_eq = |bw: &EnvDeclBuilder, cl: &Expr, _cr: &Expr, m: &Expr| {
                let _ = bw;
                c.refl_rat(c.vseq(cl, m))
            };
            let equiv = build_const_equiv(c, &b, &cl, &cr, &h_eq);
            let sound = c.quot_sound(cl, cr, equiv);

            let e = b.mk_lam(hab_id, BinderInfo::Default, hab_ty, sound);
            let e = b.mk_lam(hb_id, BinderInfo::Default, hb_ty, e);
            let e = b.mk_lam(ha_id, BinderInfo::Default, ha_ty, e);
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.mul_comm : ∀ a b : NNReal, NNReal.mul a b = NNReal.mul b a`.
    fn register_nnreal_mul_comm(&mut self, c: &MulAlgConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.mul_comm");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nnreal = c.nnreal();
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nnreal.clone());
            let (bv_id, bv) = b.fresh_local(nnreal.clone());
            let concl = c.eq_nnreal(
                c.nn_mul(a.clone(), bv.clone()),
                c.nn_mul(bv.clone(), a.clone()),
            );
            let e = b.mk_pi(bv_id, BinderInfo::Default, nnreal.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_mul_comm_value(c, &nnreal);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.mul_assoc : ∀ a b c : NNReal,
    ///     NNReal.mul a (NNReal.mul b c) = NNReal.mul (NNReal.mul a b) c`.
    fn register_nnreal_mul_assoc(&mut self, c: &MulAlgConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.mul_assoc");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nnreal = c.nnreal();
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nnreal.clone());
            let (bv_id, bv) = b.fresh_local(nnreal.clone());
            let (cv_id, cv) = b.fresh_local(nnreal.clone());
            let lhs = c.nn_mul(a.clone(), c.nn_mul(bv.clone(), cv.clone()));
            let rhs = c.nn_mul(c.nn_mul(a.clone(), bv.clone()), cv.clone());
            let concl = c.eq_nnreal(lhs, rhs);
            let e = b.mk_pi(cv_id, BinderInfo::Default, nnreal.clone(), concl);
            let e = b.mk_pi(bv_id, BinderInfo::Default, nnreal.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_mul_assoc_value(c, &nnreal);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Build a constant-style `Equiv cl cr` whose per-index leaf `h_eq m : vL = vR`
/// is supplied by `h_eq` (an `Eq Rat`). Mirrors `NNReal.ofRat_add`'s
/// `build_ofrat_add_equiv` (same `self_lt_add` + `subst` structure).
fn build_const_equiv(
    c: &MulAlgConsts,
    parent: &EnvDeclBuilder,
    cl: &Expr,
    cr: &Expr,
    h_eq: &dyn Fn(&EnvDeclBuilder, &Expr, &Expr, &Expr) -> Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.rlt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

    let pred = {
        let mut bn = EnvDeclBuilder::child_of(&b);
        let (cap_id, cap) = bn.fresh_local(c.nat.clone());
        let inner = {
            let mut bi = EnvDeclBuilder::child_of(&bn);
            let (m_id, m) = bi.fresh_local(c.nat.clone());
            let hle = c.nat_le(cap.clone(), m.clone());
            let (hle_id, _h) = bi.fresh_local(hle.clone());
            let vl = c.vseq(cl, &m);
            let vr = c.vseq(cr, &m);
            let left = c.rlt(vl.clone(), c.radd(vr.clone(), eps.clone()));
            let right = c.rlt(vr.clone(), c.radd(vl.clone(), eps.clone()));
            let concl = Expr::apps(c.and_c.clone(), [left, right]);
            let e = bi.mk_pi(hle_id, BinderInfo::Default, hle, concl);
            let e = bi.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
            bi.finish_child(e)
        };
        bn.finish_child(bn.mk_lam(cap_id, BinderInfo::Default, c.nat.clone(), inner))
    };

    let witness = {
        let mut bw = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = bw.fresh_local(c.nat.clone());
        let hle_ty = c.nat_le(c.nat_zero.clone(), m.clone());
        let (hle_id, _hle) = bw.fresh_local(hle_ty.clone());

        let vl = c.vseq(cl, &m);
        let vr = c.vseq(cr, &m);
        // h_eq : vL = vR.
        let heq = h_eq(&bw, cl, cr, &m);

        let vr_eps = c.radd(vr.clone(), eps.clone());
        let vl_eps = c.radd(vl.clone(), eps.clone());
        let vr_lt = self_lt_add(c, &bw, &vr, &eps, &hpos);
        let vl_lt = self_lt_add(c, &bw, &vl, &eps, &hpos);

        // left : vL < vR + ε  — from vR < vR+ε, subst vR → vL via symm h_eq.
        let motive_l = {
            let mut mb = EnvDeclBuilder::child_of(&bw);
            let (t_id, t) = mb.fresh_local(c.rat.clone());
            let body = c.rlt(t, vr_eps.clone());
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let heq_symm = c.eq_symm_rat(vl.clone(), vr.clone(), heq.clone());
        let left = c.subst_rat(motive_l, vr.clone(), vl.clone(), heq_symm, vr_lt);

        // right : vR < vL + ε — from vL < vL+ε, subst vL → vR via h_eq.
        let motive_r = {
            let mut mb = EnvDeclBuilder::child_of(&bw);
            let (t_id, t) = mb.fresh_local(c.rat.clone());
            let body = c.rlt(t, vl_eps.clone());
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let right = c.subst_rat(motive_r, vl.clone(), vr.clone(), heq, vl_lt);

        let l_ty = c.rlt(vl.clone(), vr_eps);
        let r_ty = c.rlt(vr.clone(), vl_eps);
        let proof = Expr::apps(c.and_intro.clone(), [l_ty, r_ty, left, right]);

        let e = bw.mk_lam(hle_id, BinderInfo::Default, hle_ty, proof);
        let e = bw.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
        bw.finish_child(e)
    };

    let intro = Expr::apps(
        c.exists_intro.clone(),
        [c.nat.clone(), pred, c.nat_zero.clone(), witness],
    );
    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, intro);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish_child(e)
}

/// `v < v + ε` from `0 < ε` (`add_lt_add_left 0 ε v` + `add_zero` transport).
fn self_lt_add(
    c: &MulAlgConsts,
    parent: &EnvDeclBuilder,
    v: &Expr,
    eps: &Expr,
    hpos: &Expr,
) -> Expr {
    let h = c.add_lt_add_left(c.rat_zero.clone(), eps.clone(), v.clone(), hpos.clone());
    let v_zero = c.radd(v.clone(), c.rat_zero.clone());
    let v_eps = c.radd(v.clone(), eps.clone());
    let e_az = c.add_zero(v.clone());
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.rlt(t, v_eps.clone());
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    c.subst_rat(motive, v_zero, v.clone(), e_az, h)
}

/// `NNReal.mul_comm` via `Quot.ind`² + `Quot.sound` on `Rat.mul_comm` leaf.
fn build_mul_comm_value(c: &MulAlgConsts, nnreal: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(nnreal.clone());
    let (bv_id, bv) = b.fresh_local(nnreal.clone());

    // descend on `a` with motive P a := mul a bv = mul bv a.
    let motive_a = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(nnreal.clone());
        let body = c.eq_nnreal(
            c.nn_mul(x.clone(), bv.clone()),
            c.nn_mul(bv.clone(), x.clone()),
        );
        mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, nnreal.clone(), body))
    };
    let minor_a = {
        let mut mf = EnvDeclBuilder::child_of(&b);
        let (f_id, f) = mf.fresh_local(c.causeq.clone());
        let mkf = c.quot_mk(f.clone());
        // descend on `bv` with motive Q y := mul (mk f) y = mul y (mk f).
        let motive_b = {
            let mut mb = EnvDeclBuilder::child_of(&mf);
            let (y_id, y) = mb.fresh_local(nnreal.clone());
            let body = c.eq_nnreal(
                c.nn_mul(mkf.clone(), y.clone()),
                c.nn_mul(y.clone(), mkf.clone()),
            );
            mb.finish_child(mb.mk_lam(y_id, BinderInfo::Default, nnreal.clone(), body))
        };
        let minor_b = {
            let mut mg = EnvDeclBuilder::child_of(&mf);
            let (g_id, g) = mg.fresh_local(c.causeq.clone());
            // goal at leaf: mul (mk f)(mk g) = mul (mk g)(mk f)
            //   ι-reduces to Quot.mk (CauSeq.mul f g) = Quot.mk (CauSeq.mul g f).
            let cl = c.cau_mul(f.clone(), g.clone());
            let cr = c.cau_mul(g.clone(), f.clone());
            let h_eq = move |_bw: &EnvDeclBuilder, cl: &Expr, _cr: &Expr, m: &Expr| -> Expr {
                // vL = vf·vg, vR = vg·vf ; h_eq := Rat.mul_comm (vf m)(vg m).
                let vf = c.vseq(&f, m);
                let vg = c.vseq(&g, m);
                let _ = cl;
                Expr::apps(c.rat_mul_comm.clone(), [vf, vg])
            };
            let equiv = build_const_equiv(c, &mg, &cl, &cr, &h_eq);
            let sound = c.quot_sound(cl, cr, equiv);
            mg.finish_child(mg.mk_lam(g_id, BinderInfo::Default, c.causeq.clone(), sound))
        };
        let ind_b = Expr::apps(
            c.quot_ind.clone(),
            [
                c.causeq.clone(),
                c.causeq_equiv.clone(),
                motive_b,
                minor_b,
                bv.clone(),
            ],
        );
        mf.finish_child(mf.mk_lam(f_id, BinderInfo::Default, c.causeq.clone(), ind_b))
    };
    let ind_a = Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive_a,
            minor_a,
            a.clone(),
        ],
    );
    let e = b.mk_lam(bv_id, BinderInfo::Default, nnreal.clone(), ind_a);
    let e = b.mk_lam(a_id, BinderInfo::Default, nnreal.clone(), e);
    b.finish(e)
}

/// `NNReal.mul_assoc` via `Quot.ind`³ + `Quot.sound` on `Rat.mul_assoc` leaf.
fn build_mul_assoc_value(c: &MulAlgConsts, nnreal: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(nnreal.clone());
    let (bv_id, bv) = b.fresh_local(nnreal.clone());
    let (cv_id, cv) = b.fresh_local(nnreal.clone());

    let assoc_eq = |x: &Expr, y: &Expr, z: &Expr| -> Expr {
        c.eq_nnreal(
            c.nn_mul(x.clone(), c.nn_mul(y.clone(), z.clone())),
            c.nn_mul(c.nn_mul(x.clone(), y.clone()), z.clone()),
        )
    };

    // descend on a.
    let motive_a = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(nnreal.clone());
        let body = assoc_eq(&x, &bv, &cv);
        mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, nnreal.clone(), body))
    };
    let minor_a = {
        let mut mf = EnvDeclBuilder::child_of(&b);
        let (f_id, f) = mf.fresh_local(c.causeq.clone());
        let mkf = c.quot_mk(f.clone());
        // descend on b.
        let motive_b = {
            let mut mb = EnvDeclBuilder::child_of(&mf);
            let (y_id, y) = mb.fresh_local(nnreal.clone());
            let body = assoc_eq(&mkf, &y, &cv);
            mb.finish_child(mb.mk_lam(y_id, BinderInfo::Default, nnreal.clone(), body))
        };
        let minor_b = {
            let mut mg = EnvDeclBuilder::child_of(&mf);
            let (g_id, g) = mg.fresh_local(c.causeq.clone());
            let mkg = c.quot_mk(g.clone());
            // descend on c.
            let motive_c = {
                let mut mb = EnvDeclBuilder::child_of(&mg);
                let (z_id, z) = mb.fresh_local(nnreal.clone());
                let body = assoc_eq(&mkf, &mkg, &z);
                mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, nnreal.clone(), body))
            };
            let minor_c = {
                let mut mh = EnvDeclBuilder::child_of(&mg);
                let (h_id, h) = mh.fresh_local(c.causeq.clone());
                // leaf goal: mul (mk f)(mul (mk g)(mk h)) = mul (mul (mk f)(mk g))(mk h)
                //   ι-reduces to mk (mul f (mul g h)) = mk (mul (mul f g) h).
                let cl = c.cau_mul(f.clone(), c.cau_mul(g.clone(), h.clone()));
                let cr = c.cau_mul(c.cau_mul(f.clone(), g.clone()), h.clone());
                let h_eq = move |_bw: &EnvDeclBuilder, _cl: &Expr, _cr: &Expr, m: &Expr| -> Expr {
                    // vL = vf·(vg·vh), vR = (vf·vg)·vh.
                    // Rat.mul_assoc vf vg vh : (vf·vg)·vh = vf·(vg·vh), so the
                    // leaf needs its symm: vf·(vg·vh) = (vf·vg)·vh.
                    let vf = c.vseq(&f, m);
                    let vg = c.vseq(&g, m);
                    let vh = c.vseq(&h, m);
                    let vfg = c.rmul(vf.clone(), vg.clone());
                    let vgh = c.rmul(vg.clone(), vh.clone());
                    let lhs = c.rmul(c.rmul(vf.clone(), vg.clone()), vh.clone()); // (vf·vg)·vh
                    let rhs = c.rmul(vf.clone(), c.rmul(vg.clone(), vh.clone())); // vf·(vg·vh)
                    let assoc = Expr::apps(c.rat_mul_assoc.clone(), [vf, vg, vh]);
                    let _ = (vfg, vgh);
                    c.eq_symm_rat(lhs, rhs, assoc)
                };
                let equiv = build_const_equiv(c, &mh, &cl, &cr, &h_eq);
                let sound = c.quot_sound(cl, cr, equiv);
                mh.finish_child(mh.mk_lam(h_id, BinderInfo::Default, c.causeq.clone(), sound))
            };
            let ind_c = Expr::apps(
                c.quot_ind.clone(),
                [
                    c.causeq.clone(),
                    c.causeq_equiv.clone(),
                    motive_c,
                    minor_c,
                    cv.clone(),
                ],
            );
            mg.finish_child(mg.mk_lam(g_id, BinderInfo::Default, c.causeq.clone(), ind_c))
        };
        let ind_b = Expr::apps(
            c.quot_ind.clone(),
            [
                c.causeq.clone(),
                c.causeq_equiv.clone(),
                motive_b,
                minor_b,
                bv.clone(),
            ],
        );
        mf.finish_child(mf.mk_lam(f_id, BinderInfo::Default, c.causeq.clone(), ind_b))
    };
    let ind_a = Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive_a,
            minor_a,
            a.clone(),
        ],
    );
    let e = b.mk_lam(cv_id, BinderInfo::Default, nnreal.clone(), ind_a);
    let e = b.mk_lam(bv_id, BinderInfo::Default, nnreal.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, nnreal.clone(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &["NNReal.ofRat_mul", "NNReal.mul_comm", "NNReal.mul_assoc"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_reverse_square_algebra()
            .expect("init_algebra_nnreal_reverse_square_algebra");
        env.init_algebra_nnreal_reverse_square_algebra()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_reverse_square_algebra_kernel_check() {
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
    fn test_reverse_square_algebra_constructive_empty_closure() {
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
