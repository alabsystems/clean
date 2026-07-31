// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — Component A, Step (4): `NNReal.mul` (binary `Quot.lift`).
//!
//! # Why this module exists
//!
//! With `NNReal.IsCauchy_mul` (`algebra_nnreal_mul_op.rs`) and the symmetric
//! product-respect core `Rat.mul_respect_close` (`algebra_rat_mul_respect.rs`)
//! landed, the carrier product can be lifted. `NNReal.CauSeq.mul` builds the
//! pointwise-product Cauchy subtype element; `NNReal.mul` is the nested binary
//! `Quot.lift` (mirroring `NNReal.add`), discharging both per-argument respect
//! obligations.
//!
//! - `NNReal.CauSeq.mul : CauSeq → CauSeq → CauSeq`
//!     `:= fun f g => CauSeq.mk (fun n => NNRat.mul (seq f n)(seq g n)) hcau`
//!     `hcau := IsCauchy_mul (seq f)(seq g)(property f)(property g)`.
//! - `NNReal.mul : NNReal → NNReal → NNReal`   (nested binary `Quot.lift`).
//!
//! # The respect obligation (the genuinely-new part vs. `add`)
//!
//! Unlike addition (shared summand cancels), the multiplicative respect
//! `Equiv (mul s x)(mul s x2)` from `Equiv x x2` SCALES the error by the shared
//! factor, so it needs all three reps BOUNDED. `NNReal.IsCauchy_bounded`
//! supplies `Bs`,`Bx`,`Bx2`; the δ-choice (`Rat.deltaMul`) gives a band `δ`
//! with `δ·(Bs+Bx2) ≤ ε/2` AND `δ·(Bs+Bx) ≤ ε/2` (both `≤ δ·D` for
//! `D := Bs+Bx+Bx2+1`); and `Rat.mul_respect_close` discharges BOTH conjuncts
//! at once. The val transport is via `NNRat.val_mul` (plus a `Rat.mul_comm`
//! reconciliation in the `!p_first` orientation, where `val(seq L) = vx·vs`).
//!
//! NO `sorry` / `add_decl_unchecked` / `add_decl_structural`. `NNReal.mul` is a
//! `Definition`; its well-definedness rides on the kernel-checked `Quot.lift`
//! respect arguments (each an `Equiv` proof, foundational closure).

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for `NNReal.mul`.
pub(crate) struct NNMulConsts {
    nat: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    nnrat: Expr,
    nnrat_mul: Expr,
    nnrat_val: Expr,
    nnrat_val_mul: Expr,
    nnrat_property: Expr,
    causeq: Expr,
    causeq_mk: Expr,
    causeq_seq: Expr,
    causeq_property: Expr,
    causeq_equiv: Expr,
    is_cauchy_mul: Expr,
    is_cauchy_bounded: Expr,
    rat_add: Expr,
    rat_mul: Expr,
    rat_mul_comm: Expr,
    rat_lt: Expr,
    rat_le: Expr,
    nat_le: Expr,
    rat_zero_lt_one: Expr,
    rat_zero_add: Expr,
    rat_add_zero: Expr,
    rat_add_le_add: Expr,
    rat_add_lt_add_left: Expr,
    rat_le_refl: Expr,
    rat_lt_of_le_of_lt: Expr,
    rat_mul_le_left: Expr,
    rat_lt_iff_le_not_le: Expr,
    rat_deltamul: Expr,
    rat_deltamul_pos: Expr,
    rat_deltamul_mul_eq: Expr,
    rat_mul_respect: Expr,
    quot: Expr,
    quot_mk: Expr,
    quot_lift: Expr,
    quot_sound: Expr,
    and_c: Expr,
    and_intro: Expr,
    and_left: Expr,
    and_right: Expr,
    not_c: Expr,
    iff_mp: Expr,
    exists_c: Expr,
    exists_intro: Expr,
    exists_elim: Expr,
    eq_rat: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    eq_subst: Expr,
}

impl NNMulConsts {
    pub(crate) fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            nnrat: k("NNRat"),
            nnrat_mul: k("NNRat.mul"),
            nnrat_val: k("NNRat.val"),
            nnrat_val_mul: k("NNRat.val_mul"),
            nnrat_property: k("NNRat.property"),
            causeq: k("NNReal.CauSeq"),
            causeq_mk: k("NNReal.CauSeq.mk"),
            causeq_seq: k("NNReal.CauSeq.seq"),
            causeq_property: k("NNReal.CauSeq.property"),
            causeq_equiv: k("NNReal.CauSeq.Equiv"),
            is_cauchy_mul: k("NNReal.IsCauchy_mul"),
            is_cauchy_bounded: k("NNReal.IsCauchy_bounded"),
            rat_add: k("Rat.add"),
            rat_mul: k("Rat.mul"),
            rat_mul_comm: k("Rat.mul_comm"),
            rat_lt: k("Rat.lt"),
            rat_le: k("Rat.le"),
            nat_le: k("Nat.le"),
            rat_zero_lt_one: k("Rat.zero_lt_one"),
            rat_zero_add: k("Rat.zero_add"),
            rat_add_zero: k("Rat.add_zero"),
            rat_add_le_add: k("Rat.add_le_add"),
            rat_add_lt_add_left: k("Rat.add_lt_add_left"),
            rat_le_refl: k("Rat.le_refl"),
            rat_lt_of_le_of_lt: k("Rat.lt_of_le_of_lt"),
            rat_mul_le_left: k("Rat.mul_le_mul_of_nonneg_left"),
            rat_lt_iff_le_not_le: k("Rat.lt_iff_le_not_le"),
            rat_deltamul: k("Rat.deltaMul"),
            rat_deltamul_pos: k("Rat.deltaMul_pos"),
            rat_deltamul_mul_eq: k("Rat.deltaMul_mul_eq"),
            rat_mul_respect: k("Rat.mul_respect_close"),
            quot: Expr::const_(Name::from_string("Quot"), vec![lvl1.clone()]),
            quot_mk: Expr::const_(Name::from_string("Quot.mk"), vec![lvl1.clone()]),
            quot_lift: Expr::const_(
                Name::from_string("Quot.lift"),
                vec![lvl1.clone(), lvl1.clone()],
            ),
            quot_sound: Expr::const_(Name::from_string("Quot.sound"), vec![lvl1.clone()]),
            and_c: k("And"),
            and_intro: k("And.intro"),
            and_left: k("And.left"),
            and_right: k("And.right"),
            not_c: k("Not"),
            iff_mp: k("Iff.mp"),
            exists_c: Expr::const_(Name::from_string("Exists"), vec![lvl1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![lvl1.clone()]),
            exists_elim: Expr::const_(Name::from_string("Exists.elim"), vec![lvl1.clone()]),
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![lvl1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![lvl1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1]),
        }
    }

    fn nnreal(&self) -> Expr {
        Expr::apps(
            self.quot.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone()],
        )
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
    #[cfg(test)]
    fn nonneg(&self, a: Expr) -> Expr {
        self.rle(self.rat_zero.clone(), a)
    }
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    fn and_ty(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.and_c.clone(), [p, q])
    }
    fn val(&self, q: Expr) -> Expr {
        Expr::app(self.nnrat_val.clone(), q)
    }
    fn seq_at(&self, f: &Expr, n: &Expr) -> Expr {
        Expr::app(Expr::app(self.causeq_seq.clone(), f.clone()), n.clone())
    }
    fn vseq(&self, f: &Expr, n: &Expr) -> Expr {
        self.val(self.seq_at(f, n))
    }
    fn seq_of(&self, f: &Expr) -> Expr {
        Expr::app(self.causeq_seq.clone(), f.clone())
    }
    fn property(&self, f: &Expr) -> Expr {
        Expr::app(self.causeq_property.clone(), f.clone())
    }
    fn nnmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnrat_mul.clone(), [a, b])
    }
    fn nnrat_property(&self, q: Expr) -> Expr {
        Expr::app(self.nnrat_property.clone(), q)
    }
    fn equiv(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_equiv.clone(), [a, b])
    }
    fn bound_pair(&self, x: Expr, y: Expr, eps: Expr) -> Expr {
        let left = self.rlt(x.clone(), self.radd(y.clone(), eps.clone()));
        let right = self.rlt(y, self.radd(x, eps));
        self.and_ty(left, right)
    }
    fn quot_mk(&self, l: Expr) -> Expr {
        Expr::apps(
            self.quot_mk.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone(), l],
        )
    }
    fn quot_sound(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.quot_sound.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone(), a, b, h],
        )
    }
    fn val_mul(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.nnrat_val_mul.clone(), [p, q])
    }
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul_comm.clone(), [a, b])
    }
    fn eq_ty(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq_rat.clone(), [self.rat.clone(), a, b])
    }
    fn eq_symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }
    fn eq_trans(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.rat.clone(), a, b, cc, hab, hbc],
        )
    }
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    fn add_le_add(&self, a: Expr, b: Expr, cc: Expr, d: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_add_le_add.clone(), [a, b, cc, d, h1, h2])
    }
    fn add_lt_add_left(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_add_lt_add_left.clone(), [a, b, cc, h])
    }
    fn le_refl(&self, a: Expr) -> Expr {
        Expr::app(self.rat_le_refl.clone(), a)
    }
    fn lt_of_le_of_lt(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_lt_of_le_of_lt.clone(), [a, b, cc, h1, h2])
    }
    fn mul_le_left(&self, a: Expr, b: Expr, cc: Expr, hbc: Expr, ha: Expr) -> Expr {
        Expr::apps(self.rat_mul_le_left.clone(), [a, b, cc, hbc, ha])
    }
    fn add_zero(&self, a: Expr) -> Expr {
        Expr::app(self.rat_add_zero.clone(), a)
    }
    fn zero_add(&self, a: Expr) -> Expr {
        Expr::app(self.rat_zero_add.clone(), a)
    }
    fn delta(&self, eps: &Expr, d: &Expr) -> Expr {
        Expr::apps(self.rat_deltamul.clone(), [eps.clone(), d.clone()])
    }
    fn half(&self, eps: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.div"), vec![]),
            [
                eps.clone(),
                Expr::const_(Name::from_string("Rat.two"), vec![]),
            ],
        )
    }
    fn le_of_lt(&self, a: Expr, b: Expr, hlt: Expr) -> Expr {
        let le_ab = self.rle(a.clone(), b.clone());
        let not_le_ba = Expr::app(self.not_c.clone(), self.rle(b.clone(), a.clone()));
        let and_ty = self.and_ty(le_ab.clone(), not_le_ba.clone());
        let lt_ab = self.rlt(a.clone(), b.clone());
        let iff = Expr::apps(self.rat_lt_iff_le_not_le.clone(), [a, b]);
        let mp = Expr::apps(self.iff_mp.clone(), [lt_ab, and_ty, iff, hlt]);
        Expr::apps(self.and_left.clone(), [le_ab, not_le_ba, mp])
    }
    fn bounded_of(&self, f: &Expr) -> Expr {
        Expr::apps(
            self.is_cauchy_bounded.clone(),
            [self.seq_of(f), self.property(f)],
        )
    }
    fn bounded_pred(&self, parent: &EnvDeclBuilder, f: &Expr) -> Expr {
        let mut pb = EnvDeclBuilder::child_of(parent);
        let (bb_id, bb) = pb.fresh_local(self.nnrat.clone());
        let inner = {
            let mut ib = EnvDeclBuilder::child_of(&pb);
            let (n_id, n) = ib.fresh_local(self.nat.clone());
            let nle = Expr::apps(
                Expr::const_(Name::from_string("NNRat.le"), vec![]),
                [self.seq_at(f, &n), bb.clone()],
            );
            ib.finish_child(ib.mk_pi(n_id, BinderInfo::Default, self.nat.clone(), nle))
        };
        pb.finish_child(pb.mk_lam(bb_id, BinderInfo::Default, self.nnrat.clone(), inner))
    }
    #[cfg(test)]
    fn bounded_exists(&self, parent: &EnvDeclBuilder, f: &Expr) -> Expr {
        Expr::apps(
            self.exists_c.clone(),
            [self.nnrat.clone(), self.bounded_pred(parent, f)],
        )
    }
    fn bound_hyp_at(&self, parent: &EnvDeclBuilder, f: &Expr, big_b: &Expr) -> Expr {
        let mut ib = EnvDeclBuilder::child_of(parent);
        let (n_id, n) = ib.fresh_local(self.nat.clone());
        let nle = Expr::apps(
            Expr::const_(Name::from_string("NNRat.le"), vec![]),
            [self.seq_at(f, &n), big_b.clone()],
        );
        ib.finish_child(ib.mk_pi(n_id, BinderInfo::Default, self.nat.clone(), nle))
    }
    fn caumul(&self, parent: &EnvDeclBuilder, f: &Expr, g: &Expr) -> Expr {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (n_id, n) = bn.fresh_local(self.nat.clone());
        let body = self.nnmul(self.seq_at(f, &n), self.seq_at(g, &n));
        let seq = bn.mk_lam(n_id, BinderInfo::Default, self.nat.clone(), body);
        let seq = bn.finish_child(seq);
        let hcau = Expr::apps(
            self.is_cauchy_mul.clone(),
            [
                self.seq_of(f),
                self.seq_of(g),
                self.property(f),
                self.property(g),
            ],
        );
        Expr::apps(self.causeq_mk.clone(), [seq, hcau])
    }
    fn pred_n_combined(&self, parent: &EnvDeclBuilder, cl: &Expr, cr: &Expr, eps: &Expr) -> Expr {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (n_id, n) = bn.fresh_local(self.nat.clone());
        let inner = {
            let mut bi = EnvDeclBuilder::child_of(&bn);
            let (m_id, m) = bi.fresh_local(self.nat.clone());
            let hle = self.nat_le(n.clone(), m.clone());
            let (hle_id, _h) = bi.fresh_local(hle.clone());
            let concl = self.bound_pair(self.vseq(cl, &m), self.vseq(cr, &m), eps.clone());
            let e = bi.mk_pi(hle_id, BinderInfo::Default, hle, concl);
            let e = bi.mk_pi(m_id, BinderInfo::Default, self.nat.clone(), e);
            bi.finish_child(e)
        };
        bn.finish_child(bn.mk_lam(n_id, BinderInfo::Default, self.nat.clone(), inner))
    }
    fn exists_pred_combined(
        &self,
        parent: &EnvDeclBuilder,
        cl: &Expr,
        cr: &Expr,
        eps: &Expr,
    ) -> Expr {
        Expr::apps(
            self.exists_c.clone(),
            [self.nat.clone(), self.pred_n_combined(parent, cl, cr, eps)],
        )
    }
    fn pred_n_pair_at(
        &self,
        parent: &EnvDeclBuilder,
        a: &Expr,
        b: &Expr,
        eps: &Expr,
        cap: &Expr,
    ) -> Expr {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (m_id, m) = bn.fresh_local(self.nat.clone());
        let hle = self.nat_le(cap.clone(), m.clone());
        let (hle_id, _h) = bn.fresh_local(hle.clone());
        let concl = self.bound_pair(self.vseq(a, &m), self.vseq(b, &m), eps.clone());
        let e = bn.mk_pi(hle_id, BinderInfo::Default, hle, concl);
        let e = bn.mk_pi(m_id, BinderInfo::Default, self.nat.clone(), e);
        bn.finish_child(e)
    }
    fn pred_n_pair(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr, eps: &Expr) -> Expr {
        self.pred_n_combined(parent, a, b, eps)
    }
}

impl Environment {
    /// Register `NNReal.CauSeq.mul` and `NNReal.mul`. Idempotent.
    pub fn init_algebra_nnreal_mul_lift(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_cauchy()?; // CauSeq, Equiv, mk, seq, property; NNRat.*
        self.init_algebra_nnreal_mul_op()?; // IsCauchy_mul + Rat surface
        self.init_algebra_nnreal_bounded()?; // IsCauchy_bounded
        self.init_algebra_rat_delta_choice()?; // deltaMul + lemmas
        self.init_algebra_rat_mul_respect()?; // mul_respect_close (+ mul_close)
        self.register_rat_order_proofs()?; // zero_lt_one, le_refl
        self.register_rat_mul_comm_proof()?; // mul_comm (for !p_first reconciliation)
        self.init_exists()?;
        self.init_algebra_nnreal_nnrat()?; // NNRat.val_mul, NNRat.property

        let c = NNMulConsts::new();
        self.register_nnreal_causeq_mul(&c)?;
        self.register_nnreal_mul(&c)?;
        Ok(())
    }

    fn register_nnreal_causeq_mul(&mut self, c: &NNMulConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNReal.CauSeq.mul"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(
            BinderInfo::Default,
            c.causeq.clone(),
            Expr::pi(BinderInfo::Default, c.causeq.clone(), c.causeq.clone()),
        );
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.causeq.clone());
            let (g_id, g) = b.fresh_local(c.causeq.clone());
            let body = c.caumul(&b, &f, &g);
            let e = b.mk_lam(g_id, BinderInfo::Default, c.causeq.clone(), body);
            let e = b.mk_lam(f_id, BinderInfo::Default, c.causeq.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNReal.CauSeq.mul"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    fn register_nnreal_mul(&mut self, c: &NNMulConsts) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("NNReal.mul")).is_some() {
            return Ok(());
        }
        let nnreal = c.nnreal();
        let ty = Expr::pi(
            BinderInfo::Default,
            nnreal.clone(),
            Expr::pi(BinderInfo::Default, nnreal.clone(), nnreal.clone()),
        );
        let value = build_nnreal_mul_value(c, &nnreal);
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNReal.mul"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }
}

/// `NNReal.mul := fun a b => Quot.lift (outer_f)(outer_h) a` (mirror `NNReal.add`).
fn build_nnreal_mul_value(c: &NNMulConsts, nnreal: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(nnreal.clone());
    let (bv_id, bv) = b.fresh_local(nnreal.clone());

    let inner_lift = |p: &Expr, parent: &EnvDeclBuilder, second: &Expr| -> Expr {
        let inner_f = {
            let mut bi = EnvDeclBuilder::child_of(parent);
            let (q_id, q) = bi.fresh_local(c.causeq.clone());
            let body = c.quot_mk(c.caumul(&bi, p, &q));
            let lam = bi.mk_lam(q_id, BinderInfo::Default, c.causeq.clone(), body);
            bi.finish_child(lam)
        };
        let inner_h = {
            let mut bi = EnvDeclBuilder::child_of(parent);
            let (q_id, q) = bi.fresh_local(c.causeq.clone());
            let (q2_id, q2) = bi.fresh_local(c.causeq.clone());
            let hyp = c.equiv(q.clone(), q2.clone());
            let (hq_id, hq) = bi.fresh_local(hyp.clone());
            let eqv = build_mul_respect(c, &bi, p, &q, &q2, &hq, /*p_first=*/ true);
            let mul_pq = c.caumul(&bi, p, &q);
            let mul_pq2 = c.caumul(&bi, p, &q2);
            let sound = c.quot_sound(mul_pq, mul_pq2, eqv);
            let lam = bi.mk_lam(hq_id, BinderInfo::Default, hyp, sound);
            let lam = bi.mk_lam(q2_id, BinderInfo::Default, c.causeq.clone(), lam);
            let lam = bi.mk_lam(q_id, BinderInfo::Default, c.causeq.clone(), lam);
            bi.finish_child(lam)
        };
        Expr::apps(
            c.quot_lift.clone(),
            [
                c.causeq.clone(),
                c.causeq_equiv.clone(),
                nnreal.clone(),
                inner_f,
                inner_h,
                second.clone(),
            ],
        )
    };

    let outer_f = {
        let mut bo = EnvDeclBuilder::child_of(&b);
        let (p_id, p) = bo.fresh_local(c.causeq.clone());
        let body = inner_lift(&p, &bo, &bv);
        let lam = bo.mk_lam(p_id, BinderInfo::Default, c.causeq.clone(), body);
        bo.finish_child(lam)
    };

    let outer_h = {
        let mut bh = EnvDeclBuilder::child_of(&b);
        let (p_id, p) = bh.fresh_local(c.causeq.clone());
        let (p2_id, p2) = bh.fresh_local(c.causeq.clone());
        let hyp = c.equiv(p.clone(), p2.clone());
        let (hp_id, hp) = bh.fresh_local(hyp.clone());

        let quot_ind = Expr::const_(
            Name::from_string("Quot.ind"),
            vec![Level::succ(Level::zero())],
        );
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&bh);
            let (x_id, x) = mb.fresh_local(nnreal.clone());
            let lhs = inner_lift(&p, &mb, &x);
            let rhs = inner_lift(&p2, &mb, &x);
            let eq_nn = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [nnreal.clone(), lhs, rhs],
            );
            mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, nnreal.clone(), eq_nn))
        };
        let minor = {
            let mut mb = EnvDeclBuilder::child_of(&bh);
            let (q_id, q) = mb.fresh_local(c.causeq.clone());
            let eqv = build_mul_respect(c, &mb, &q, &p, &p2, &hp, /*p_first=*/ false);
            let mul_pq = c.caumul(&mb, &p, &q);
            let mul_p2q = c.caumul(&mb, &p2, &q);
            let sound = c.quot_sound(mul_pq, mul_p2q, eqv);
            mb.finish_child(mb.mk_lam(q_id, BinderInfo::Default, c.causeq.clone(), sound))
        };
        let ind = Expr::apps(
            quot_ind,
            [
                c.causeq.clone(),
                c.causeq_equiv.clone(),
                motive,
                minor,
                bv.clone(),
            ],
        );
        let lam = bh.mk_lam(hp_id, BinderInfo::Default, hyp, ind);
        let lam = bh.mk_lam(p2_id, BinderInfo::Default, c.causeq.clone(), lam);
        let lam = bh.mk_lam(p_id, BinderInfo::Default, c.causeq.clone(), lam);
        bh.finish_child(lam)
    };

    let outer = Expr::apps(
        c.quot_lift.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            nnreal.clone(),
            outer_f,
            outer_h,
            a.clone(),
        ],
    );
    let e = b.mk_lam(bv_id, BinderInfo::Default, nnreal.clone(), outer);
    let e = b.mk_lam(a_id, BinderInfo::Default, nnreal.clone(), e);
    b.finish(e)
}

/// The multiplicative respect proof.
///
/// `shared` is the fixed factor; `x`,`x2` are the varying factor with
/// `hx : Equiv x x2`. Produces `Equiv (mul A B)(mul A2 B2)` per `p_first`:
///   `p_first = true`  : `mul shared x` vs `mul shared x2`.
///   `p_first = false` : `mul x shared` vs `mul x2 shared`.
#[allow(clippy::too_many_arguments)]
fn build_mul_respect(
    c: &NNMulConsts,
    parent: &EnvDeclBuilder,
    shared: &Expr,
    x: &Expr,
    x2: &Expr,
    hx: &Expr,
    p_first: bool,
) -> Expr {
    let mut bb = EnvDeclBuilder::child_of(parent);
    let (eps_id, eps) = bb.fresh_local(c.rat.clone());
    let hpos_ty = c.rlt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = bb.fresh_local(hpos_ty.clone());

    let (cl, cr) = if p_first {
        (c.caumul(&bb, shared, x), c.caumul(&bb, shared, x2))
    } else {
        (c.caumul(&bb, x, shared), c.caumul(&bb, x2, shared))
    };
    let goal_exists = c.exists_pred_combined(&bb, &cl, &cr, &eps);

    // Bound all three reps.
    let exists_bs = c.bounded_of(shared);
    let exists_bx = c.bounded_of(x);
    let exists_bx2 = c.bounded_of(x2);
    let pred_bs = c.bounded_pred(&bb, shared);
    let pred_bx = c.bounded_pred(&bb, x);
    let pred_bx2 = c.bounded_pred(&bb, x2);

    let elim_bs = {
        let mut bs = EnvDeclBuilder::child_of(&bb);
        let (big_bs_id, big_bs) = bs.fresh_local(c.nnrat.clone());
        let hbs_ty = c.bound_hyp_at(&bs, shared, &big_bs);
        let (hbs_id, hbs) = bs.fresh_local(hbs_ty.clone());

        let elim_bx = {
            let mut bxb = EnvDeclBuilder::child_of(&bs);
            let (big_bx_id, big_bx) = bxb.fresh_local(c.nnrat.clone());
            let hbx_ty = c.bound_hyp_at(&bxb, x, &big_bx);
            let (hbx_id, hbx) = bxb.fresh_local(hbx_ty.clone());

            let elim_bx2 = {
                let mut bx2b = EnvDeclBuilder::child_of(&bxb);
                let (big_bx2_id, big_bx2) = bx2b.fresh_local(c.nnrat.clone());
                let hbx2_ty = c.bound_hyp_at(&bx2b, x2, &big_bx2);
                let (hbx2_id, hbx2) = bx2b.fresh_local(hbx2_ty.clone());

                let body = build_respect_body(
                    c,
                    &bx2b,
                    shared,
                    x,
                    x2,
                    &cl,
                    &cr,
                    &eps,
                    &hpos,
                    hx,
                    &big_bs,
                    &big_bx,
                    &big_bx2,
                    &hbs,
                    &hbx,
                    &hbx2,
                    &goal_exists,
                    p_first,
                );

                let e = bx2b.mk_lam(hbx2_id, BinderInfo::Default, hbx2_ty, body);
                let e = bx2b.mk_lam(big_bx2_id, BinderInfo::Default, c.nnrat.clone(), e);
                bx2b.finish_child(e)
            };
            let elim = Expr::apps(
                c.exists_elim.clone(),
                [
                    c.nnrat.clone(),
                    pred_bx2.clone(),
                    goal_exists.clone(),
                    exists_bx2,
                    elim_bx2,
                ],
            );
            let e = bxb.mk_lam(hbx_id, BinderInfo::Default, hbx_ty, elim);
            let e = bxb.mk_lam(big_bx_id, BinderInfo::Default, c.nnrat.clone(), e);
            bxb.finish_child(e)
        };
        let elim = Expr::apps(
            c.exists_elim.clone(),
            [
                c.nnrat.clone(),
                pred_bx.clone(),
                goal_exists.clone(),
                exists_bx,
                elim_bx,
            ],
        );
        let e = bs.mk_lam(hbs_id, BinderInfo::Default, hbs_ty, elim);
        let e = bs.mk_lam(big_bs_id, BinderInfo::Default, c.nnrat.clone(), e);
        bs.finish_child(e)
    };

    let elim_outer = Expr::apps(
        c.exists_elim.clone(),
        [
            c.nnrat.clone(),
            pred_bs.clone(),
            goal_exists,
            exists_bs,
            elim_bs,
        ],
    );
    let e = bb.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, elim_outer);
    let e = bb.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    bb.finish_child(e)
}

/// The body once all three bounds (`Bs`,`Bx`,`Bx2`) are in scope: build `D`, the
/// δ-choice, the two budgets, instantiate `hx` at δ, and the inner witness.
#[allow(clippy::too_many_arguments)]
fn build_respect_body(
    c: &NNMulConsts,
    parent: &EnvDeclBuilder,
    shared: &Expr,
    x: &Expr,
    x2: &Expr,
    cl: &Expr,
    cr: &Expr,
    eps: &Expr,
    hpos: &Expr,
    hx: &Expr,
    big_bs: &Expr,
    big_bx: &Expr,
    big_bx2: &Expr,
    hbs: &Expr,
    hbx: &Expr,
    hbx2: &Expr,
    goal_exists: &Expr,
    p_first: bool,
) -> Expr {
    let bsr = c.val(big_bs.clone());
    let bxr = c.val(big_bx.clone());
    let bx2r = c.val(big_bx2.clone());
    // D := ((Bsr+Bxr)+Bx2r)+1.
    let bs_bx = c.radd(bsr.clone(), bxr.clone()); // Bsr+Bxr
    let bs_bx_bx2 = c.radd(bs_bx.clone(), bx2r.clone()); // (Bsr+Bxr)+Bx2r
    let big_d = c.radd(bs_bx_bx2.clone(), c.rat_one.clone());
    let delta = c.delta(eps, &big_d);
    let half_eps = c.half(eps);

    let h0bsr = c.nnrat_property(big_bs.clone());
    let h0bxr = c.nnrat_property(big_bx.clone());
    let h0bx2r = c.nnrat_property(big_bx2.clone());

    // 0 ≤ Bsr+Bxr+Bx2r.
    let h0sum = nonneg_sum3(c, parent, &bsr, &bxr, &bx2r, &h0bsr, &h0bxr, &h0bx2r);
    // Bsr+Bxr+Bx2r < D.
    let sum_lt_d = sum_lt_succ(c, parent, &bs_bx_bx2, &big_d);
    // 0 < D.
    let h0d = c.lt_of_le_of_lt(
        c.rat_zero.clone(),
        bs_bx_bx2.clone(),
        big_d.clone(),
        h0sum,
        sum_lt_d,
    );
    let hdne = build_d_ne_zero(c, parent, &big_d, &h0d);
    let hdelta_pos = Expr::apps(
        c.rat_deltamul_pos.clone(),
        [eps.clone(), big_d.clone(), hpos.clone(), h0d],
    );
    let h0delta = c.le_of_lt(c.rat_zero.clone(), delta.clone(), hdelta_pos.clone());
    let hdelta_d = Expr::apps(
        c.rat_deltamul_mul_eq.clone(),
        [eps.clone(), big_d.clone(), hdne],
    );

    // `0 ≤ 1` for the +1 padding step.
    let h01 = Expr::const_(Name::from_string("Rat.zero_le_one"), vec![]);

    // Two budgets: δ·(Bsr+Bx2r) ≤ ε/2 and δ·(Bsr+Bxr) ≤ ε/2.
    //   Each from mul_le_left δ (Bsr+B?) D (Bsr+B? ≤ D) h0δ, transport δ·D → ε/2.
    let bs_bx2 = c.radd(bsr.clone(), bx2r.clone()); // Bsr+Bx2r
                                                    // Bsr+Bx2r ≤ D : (Bsr+Bx2r) ≤ (Bsr+Bxr)+Bx2r ≤ D.
    let bs_bx2_le_d = {
        // Bsr ≤ Bsr+Bxr  (Bsr+0 ≤ Bsr+Bxr via 0≤Bxr, transport add_zero).
        let bsr_le_bsbx = le_add_nonneg_right(c, parent, &bsr, &bxr, &h0bxr);
        // (Bsr+Bx2r) ≤ (Bsr+Bxr)+Bx2r  := add_le_add Bsr (Bsr+Bxr) Bx2r Bx2r (·)(refl).
        let step1 = c.add_le_add(
            bsr.clone(),
            bs_bx.clone(),
            bx2r.clone(),
            bx2r.clone(),
            bsr_le_bsbx,
            c.le_refl(bx2r.clone()),
        );
        // (Bsr+Bxr)+Bx2r ≤ D  (sum ≤ sum+1 via 0≤1).
        let step2 = le_add_nonneg_right(c, parent, &bs_bx_bx2, &c.rat_one.clone(), &h01);
        let le_trans = Expr::const_(Name::from_string("Rat.le_trans"), vec![]);
        Expr::apps(
            le_trans,
            [
                bs_bx2.clone(),
                bs_bx_bx2.clone(),
                big_d.clone(),
                step1,
                step2,
            ],
        )
    };
    let budget_fwd = build_budget(
        c,
        parent,
        &delta,
        &bs_bx2,
        &big_d,
        &half_eps,
        &hdelta_d,
        &h0delta,
        bs_bx2_le_d,
    );
    // Bsr+Bxr ≤ D : (Bsr+Bxr) ≤ (Bsr+Bxr)+Bx2r ≤ D.
    let bs_bx_le_d = {
        let step1 = le_add_nonneg_right(c, parent, &bs_bx, &bx2r, &h0bx2r);
        let step2 = le_add_nonneg_right(c, parent, &bs_bx_bx2, &c.rat_one.clone(), &h01);
        let le_trans = Expr::const_(Name::from_string("Rat.le_trans"), vec![]);
        Expr::apps(
            le_trans,
            [
                bs_bx.clone(),
                bs_bx_bx2.clone(),
                big_d.clone(),
                step1,
                step2,
            ],
        )
    };
    let budget_rev = build_budget(
        c, parent, &delta, &bs_bx, &big_d, &half_eps, &hdelta_d, &h0delta, bs_bx_le_d,
    );

    // hx δ hδpos : ∃ N, ∀ n, N≤n → bound_pair (vx)(vx2) δ.
    let exists_n = Expr::apps(hx.clone(), [delta.clone(), hdelta_pos]);
    let pred_x = c.pred_n_pair(parent, x, x2, &delta);

    let elim_n = {
        let mut be = EnvDeclBuilder::child_of(parent);
        let (cap_id, cap) = be.fresh_local(c.nat.clone());
        let hn_ty = c.pred_n_pair_at(&be, x, x2, &delta, &cap);
        let (hn_id, hn) = be.fresh_local(hn_ty.clone());

        let witness = build_mul_witness(
            c,
            &be,
            shared,
            x,
            x2,
            cl,
            cr,
            eps,
            &delta,
            &bsr,
            &bxr,
            &bx2r,
            &budget_fwd,
            &budget_rev,
            &h0delta,
            hpos,
            hbs,
            hbx,
            hbx2,
            &cap,
            &hn,
            p_first,
        );

        let intro = Expr::apps(
            c.exists_intro.clone(),
            [
                c.nat.clone(),
                c.pred_n_combined(&be, cl, cr, eps),
                cap.clone(),
                witness,
            ],
        );
        let e = be.mk_lam(hn_id, BinderInfo::Default, hn_ty, intro);
        let e = be.mk_lam(cap_id, BinderInfo::Default, c.nat.clone(), e);
        be.finish_child(e)
    };

    Expr::apps(
        c.exists_elim.clone(),
        [c.nat.clone(), pred_x, goal_exists.clone(), exists_n, elim_n],
    )
}

/// `t ≤ t+u` from `h0u : 0 ≤ u`: `t+0 ≤ t+u` (add_le_add refl h0u), transport
/// the LHS `t+0 → t` via `add_zero t`.
fn le_add_nonneg_right(
    c: &NNMulConsts,
    parent: &EnvDeclBuilder,
    t: &Expr,
    u: &Expr,
    h0u: &Expr,
) -> Expr {
    let raw = c.add_le_add(
        t.clone(),
        t.clone(),
        c.rat_zero.clone(),
        u.clone(),
        c.le_refl(t.clone()),
        h0u.clone(),
    ); // t+0 ≤ t+u
    let t_plus_zero = c.radd(t.clone(), c.rat_zero.clone());
    let t_plus_u = c.radd(t.clone(), u.clone());
    let motive = {
        let mut m = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = m.fresh_local(c.rat.clone());
        let body = c.rle(z, t_plus_u.clone());
        m.finish_child(m.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    c.subst(motive, t_plus_zero, t.clone(), c.add_zero(t.clone()), raw)
}

#[allow(clippy::too_many_arguments)]
fn build_budget(
    c: &NNMulConsts,
    parent: &EnvDeclBuilder,
    delta: &Expr,
    bsum: &Expr,
    big_d: &Expr,
    half_eps: &Expr,
    hdelta_d: &Expr,
    h0delta: &Expr,
    bsum_le_d: Expr,
) -> Expr {
    let prod_le = c.mul_le_left(
        delta.clone(),
        bsum.clone(),
        big_d.clone(),
        bsum_le_d,
        h0delta.clone(),
    );
    let delta_d = c.rmul(delta.clone(), big_d.clone());
    let delta_bsum = c.rmul(delta.clone(), bsum.clone());
    let motive = {
        let mut m = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = m.fresh_local(c.rat.clone());
        let body = c.rle(delta_bsum.clone(), t);
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    c.subst(motive, delta_d, half_eps.clone(), hdelta_d.clone(), prod_le)
}

#[allow(clippy::too_many_arguments)]
fn nonneg_sum3(
    c: &NNMulConsts,
    parent: &EnvDeclBuilder,
    bsr: &Expr,
    bxr: &Expr,
    bx2r: &Expr,
    h0bsr: &Expr,
    h0bxr: &Expr,
    h0bx2r: &Expr,
) -> Expr {
    // 0 ≤ Bsr+Bxr : (0+0) ≤ Bsr+Bxr, transport zero_add.
    let bs_bx = c.radd(bsr.clone(), bxr.clone());
    let h0_bs_bx = {
        let step = c.add_le_add(
            c.rat_zero.clone(),
            bsr.clone(),
            c.rat_zero.clone(),
            bxr.clone(),
            h0bsr.clone(),
            h0bxr.clone(),
        );
        let zz = c.radd(c.rat_zero.clone(), c.rat_zero.clone());
        let motive = {
            let mut m = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = m.fresh_local(c.rat.clone());
            let body = c.rle(t, bs_bx.clone());
            m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        c.subst(
            motive,
            zz,
            c.rat_zero.clone(),
            c.zero_add(c.rat_zero.clone()),
            step,
        )
    };
    // 0 ≤ (Bsr+Bxr)+Bx2r : (0+0) ≤ (Bsr+Bxr)+Bx2r, transport zero_add.
    let bs_bx_bx2 = c.radd(bs_bx.clone(), bx2r.clone());
    let step = c.add_le_add(
        c.rat_zero.clone(),
        bs_bx.clone(),
        c.rat_zero.clone(),
        bx2r.clone(),
        h0_bs_bx,
        h0bx2r.clone(),
    );
    let zz = c.radd(c.rat_zero.clone(), c.rat_zero.clone());
    let motive = {
        let mut m = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = m.fresh_local(c.rat.clone());
        let body = c.rle(t, bs_bx_bx2.clone());
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    c.subst(
        motive,
        zz,
        c.rat_zero.clone(),
        c.zero_add(c.rat_zero.clone()),
        step,
    )
}

/// `t < t+1` : `t+0 < t+1` (add_lt_add_left 0 1 t zero_lt_one), transport add_zero.
fn sum_lt_succ(c: &NNMulConsts, parent: &EnvDeclBuilder, t: &Expr, t_plus_one: &Expr) -> Expr {
    let raw = c.add_lt_add_left(
        c.rat_zero.clone(),
        c.rat_one.clone(),
        t.clone(),
        c.rat_zero_lt_one.clone(),
    );
    let t_plus_zero = c.radd(t.clone(), c.rat_zero.clone());
    let motive = {
        let mut m = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = m.fresh_local(c.rat.clone());
        let body = c.rlt(z, t_plus_one.clone());
        m.finish_child(m.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    c.subst(motive, t_plus_zero, t.clone(), c.add_zero(t.clone()), raw)
}

fn build_d_ne_zero(c: &NNMulConsts, parent: &EnvDeclBuilder, big_d: &Expr, h0d: &Expr) -> Expr {
    let mut nb = EnvDeclBuilder::child_of(parent);
    let hd0_ty = c.eq_ty(big_d.clone(), c.rat_zero.clone());
    let (hd0_id, hd0) = nb.fresh_local(hd0_ty.clone());
    let motive = {
        let mut m = EnvDeclBuilder::child_of(&nb);
        let (t_id, t) = m.fresh_local(c.rat.clone());
        let body = c.rlt(c.rat_zero.clone(), t);
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let lt00 = c.subst(motive, big_d.clone(), c.rat_zero.clone(), hd0, h0d.clone());
    let le00 = c.rle(c.rat_zero.clone(), c.rat_zero.clone());
    let not_le00 = Expr::app(c.not_c.clone(), le00.clone());
    let and00 = c.and_ty(le00.clone(), not_le00.clone());
    let lt00ty = c.rlt(c.rat_zero.clone(), c.rat_zero.clone());
    let iff00 = Expr::apps(
        c.rat_lt_iff_le_not_le.clone(),
        [c.rat_zero.clone(), c.rat_zero.clone()],
    );
    let mp00 = Expr::apps(c.iff_mp.clone(), [lt00ty, and00, iff00, lt00]);
    let not_le00_pf = Expr::apps(c.and_right.clone(), [le00.clone(), not_le00, mp00]);
    let refl00 = c.le_refl(c.rat_zero.clone());
    let false_pf = Expr::app(not_le00_pf, refl00);
    nb.finish_child(nb.mk_lam(hd0_id, BinderInfo::Default, hd0_ty, false_pf))
}

/// The inner witness for the multiplicative respect.
#[allow(clippy::too_many_arguments)]
fn build_mul_witness(
    c: &NNMulConsts,
    parent: &EnvDeclBuilder,
    shared: &Expr,
    x: &Expr,
    x2: &Expr,
    cl: &Expr,
    cr: &Expr,
    eps: &Expr,
    delta: &Expr,
    bsr: &Expr,
    bxr: &Expr,
    bx2r: &Expr,
    budget_fwd: &Expr,
    budget_rev: &Expr,
    h0delta: &Expr,
    hpos: &Expr,
    hbs: &Expr,
    hbx: &Expr,
    hbx2: &Expr,
    cap: &Expr,
    hn: &Expr,
    p_first: bool,
) -> Expr {
    let mut bw = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = bw.fresh_local(c.nat.clone());
    let hle_ty = c.nat_le(cap.clone(), m.clone());
    let (hle_id, hle) = bw.fresh_local(hle_ty.clone());

    let base = Expr::apps(hn.clone(), [m.clone(), hle]);
    let vs = c.vseq(shared, &m);
    let vx = c.vseq(x, &m);
    let vx2 = c.vseq(x2, &m);
    let l_x = c.rlt(vx.clone(), c.radd(vx2.clone(), delta.clone()));
    let r_x = c.rlt(vx2.clone(), c.radd(vx.clone(), delta.clone()));
    let lt_x_x2 = Expr::apps(c.and_left.clone(), [l_x.clone(), r_x.clone(), base.clone()]);
    let lt_x2_x = Expr::apps(c.and_right.clone(), [l_x, r_x, base]);
    let cle_x_x2 = c.le_of_lt(vx.clone(), c.radd(vx2.clone(), delta.clone()), lt_x_x2);
    let cle_x2_x = c.le_of_lt(vx2.clone(), c.radd(vx.clone(), delta.clone()), lt_x2_x);

    let h0vs = c.nnrat_property(c.seq_at(shared, &m));
    let h0vx = c.nnrat_property(c.seq_at(x, &m));
    let h0vx2 = c.nnrat_property(c.seq_at(x2, &m));

    let bnd_vs = Expr::app(hbs.clone(), m.clone()); // vs ≤ Bsr
    let bnd_vx = Expr::app(hbx.clone(), m.clone()); // vx ≤ Bxr
    let bnd_vx2 = Expr::app(hbx2.clone(), m.clone()); // vx2 ≤ Bx2r

    // mul_respect_close s x x2 Bs Bx Bx2 ε δ … : And (s·x<s·x2+ε)(s·x2<s·x+ε).
    let respect = Expr::apps(
        c.rat_mul_respect.clone(),
        [
            vs.clone(),
            vx.clone(),
            vx2.clone(),
            bsr.clone(),
            bxr.clone(),
            bx2r.clone(),
            eps.clone(),
            delta.clone(),
            h0vs,
            h0vx,
            h0vx2,
            h0delta.clone(),
            bnd_vs,
            bnd_vx,
            bnd_vx2,
            cle_x_x2,
            cle_x2_x,
            budget_fwd.clone(),
            budget_rev.clone(),
            hpos.clone(),
        ],
    );

    // Conjuncts: fwd : vs·vx < vs·vx2 + ε ; rev : vs·vx2 < vs·vx + ε.
    let sx = c.rmul(vs.clone(), vx.clone());
    let sx2 = c.rmul(vs.clone(), vx2.clone());
    let fwd_ty = c.rlt(sx.clone(), c.radd(sx2.clone(), eps.clone()));
    let rev_ty = c.rlt(sx2.clone(), c.radd(sx.clone(), eps.clone()));
    let fwd = Expr::apps(
        c.and_left.clone(),
        [fwd_ty.clone(), rev_ty.clone(), respect.clone()],
    );
    let rev = Expr::apps(c.and_right.clone(), [fwd_ty, rev_ty, respect]);

    // Transport vs·vx → val(seq L m), vs·vx2 → val(seq R m).
    let proof = build_mul_endpoints(
        c, &bw, shared, x, x2, &m, eps, &vs, &vx, &vx2, cl, cr, &fwd, &rev, p_first,
    );

    let e = bw.mk_lam(hle_id, BinderInfo::Default, hle_ty, proof);
    let e = bw.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
    bw.finish_child(e)
}

/// Transport the `vs·vx`/`vs·vx2` bounds to the combined-seq `val(seq L/R m)`
/// form, producing `bound_pair (vL)(vR) ε`.
#[allow(clippy::too_many_arguments)]
fn build_mul_endpoints(
    c: &NNMulConsts,
    parent: &EnvDeclBuilder,
    shared: &Expr,
    x: &Expr,
    x2: &Expr,
    m: &Expr,
    eps: &Expr,
    vs: &Expr,
    vx: &Expr,
    vx2: &Expr,
    _cl: &Expr,
    _cr: &Expr,
    fwd: &Expr,
    rev: &Expr,
    p_first: bool,
) -> Expr {
    let seq_shared = c.seq_at(shared, m);
    let seq_x = c.seq_at(x, m);
    let seq_x2 = c.seq_at(x2, m);
    let sx = c.rmul(vs.clone(), vx.clone()); // vs·vx (the mul_respect form)
    let sx2 = c.rmul(vs.clone(), vx2.clone());

    // vl_form := val(seq L m), vr_form := val(seq R m).
    // Equality eqL : vs·vx = vl_form, eqR : vs·vx2 = vr_form.
    let (vl_form, vr_form, eq_l, eq_r) = if p_first {
        // L = mul shared x ⟹ val_mul (seq shared)(seq x) : vl_form = vs·vx.
        let vl = c.val(c.nnmul(seq_shared.clone(), seq_x.clone()));
        let vr = c.val(c.nnmul(seq_shared.clone(), seq_x2.clone()));
        // eqL : vs·vx = vl_form  := Eq.symm (val_mul ..).
        let eq_l = c.eq_symm(
            vl.clone(),
            sx.clone(),
            c.val_mul(seq_shared.clone(), seq_x.clone()),
        );
        let eq_r = c.eq_symm(
            vr.clone(),
            sx2.clone(),
            c.val_mul(seq_shared.clone(), seq_x2.clone()),
        );
        (vl, vr, eq_l, eq_r)
    } else {
        // L = mul x shared ⟹ val_mul (seq x)(seq shared) : vl_form = vx·vs.
        let vl = c.val(c.nnmul(seq_x.clone(), seq_shared.clone()));
        let vr = c.val(c.nnmul(seq_x2.clone(), seq_shared.clone()));
        let xs = c.rmul(vx.clone(), vs.clone()); // vx·vs
        let x2s = c.rmul(vx2.clone(), vs.clone());
        // eqL : vs·vx = vl_form. Chain: vs·vx = vx·vs (mul_comm) = vl_form (symm val_mul).
        let comm_l = c.mul_comm(vs.clone(), vx.clone()); // vs·vx = vx·vs
        let symm_vm_l = c.eq_symm(
            vl.clone(),
            xs.clone(),
            c.val_mul(seq_x.clone(), seq_shared.clone()),
        ); // vx·vs = vl_form
        let eq_l = c.eq_trans(sx.clone(), xs, vl.clone(), comm_l, symm_vm_l);
        let comm_r = c.mul_comm(vs.clone(), vx2.clone());
        let symm_vm_r = c.eq_symm(
            vr.clone(),
            x2s.clone(),
            c.val_mul(seq_x2.clone(), seq_shared.clone()),
        );
        let eq_r = c.eq_trans(sx2.clone(), x2s, vr.clone(), comm_r, symm_vm_r);
        (vl, vr, eq_l, eq_r)
    };

    // fwd : vs·vx < vs·vx2 + ε.
    //   step1 rewrite RHS summand vs·vx2 → vr_form via eq_r.
    let motive_rhs_fwd = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.rlt(sx.clone(), c.radd(t, eps.clone()));
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let fwd1 = c.subst(
        motive_rhs_fwd,
        sx2.clone(),
        vr_form.clone(),
        eq_r.clone(),
        fwd.clone(),
    );
    let motive_lhs_fwd = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.rlt(t, c.radd(vr_form.clone(), eps.clone()));
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let fwd_final = c.subst(
        motive_lhs_fwd,
        sx.clone(),
        vl_form.clone(),
        eq_l.clone(),
        fwd1,
    );

    // rev : vs·vx2 < vs·vx + ε.
    let motive_rhs_rev = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.rlt(sx2.clone(), c.radd(t, eps.clone()));
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let rev1 = c.subst(
        motive_rhs_rev,
        sx.clone(),
        vl_form.clone(),
        eq_l,
        rev.clone(),
    );
    let motive_lhs_rev = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.rlt(t, c.radd(vl_form.clone(), eps.clone()));
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let rev_final = c.subst(motive_lhs_rev, sx2.clone(), vr_form.clone(), eq_r, rev1);

    let l_final = c.rlt(vl_form.clone(), c.radd(vr_form.clone(), eps.clone()));
    let r_final = c.rlt(vr_form.clone(), c.radd(vl_form.clone(), eps.clone()));
    Expr::apps(
        c.and_intro.clone(),
        [l_final, r_final, fwd_final, rev_final],
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::tc::TypeChecker;

    #[test]
    fn test_nnreal_mul_kernel_check_and_closure() {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_mul_lift()
            .expect("init_algebra_nnreal_mul_lift");
        env.init_algebra_nnreal_mul_lift().expect("idempotent");

        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in ["NNReal.CauSeq.mul", "NNReal.mul"] {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
            assert_eq!(
                info.kind,
                ConstantKind::Definition,
                "{name} is a Definition"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} closure must be foundational-only: {:?}",
                env.axiom_deps(&nm)
            );
        }
    }
}
