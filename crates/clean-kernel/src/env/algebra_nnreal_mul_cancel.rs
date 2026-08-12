// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — positive-left MULTIPLICATION CANCELLATION against a
//! concrete rational lower bound: `NNReal.le_of_mul_le_mul_of_ofRat_lower`.
//!
//! # Why this module exists
//!
//! The σ-route certificate for M2 lemma (A) reduces, after the deg-9 polynomial
//! identity, to `27·σ³·LHS' ≥ 27·σ³·22`, and the final step cancels the positive
//! factor `27·σ³`. NNReal has no `lt`/strict-positivity primitive and no
//! eventual-lower-bound dual of `IsCauchy_bounded`, so the *abstract*
//! cancellation is blocked. But `27·σ³` has a CONCRETE lower bound
//! `27·σ³ ≥ 27·(5/4)³ = 3375/64 = ofRat d` with `d > 0` a fixed rational (from
//! the landed `σ ≥ 5/4`). With a concrete `ofRat d ≤ c (d>0)` lower bound the
//! cancellation is elementary — we divide by `d/2 > 0` per index, never needing
//! eventual-lower-bound machinery.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `Rat.lt_add_of_mul_lt_mul_lower : ∀ (vc va vb dlo eps : Rat),
//!     0 ≤ vc → dlo ≤ vc → 0 ≤ eps →
//!     Rat.lt (vc·va) ((vc·vb) + dlo·eps) → Rat.lt va (vb + eps)` — the per-index
//!   Rat cancellation: if `va ≥ vb+eps` then multiplying by `vc ≥ dlo ≥ 0` gives
//!   `vc·vb + dlo·eps ≤ vc·va < vc·vb + dlo·eps`, absurd; the strict goal is
//!   assembled through `Rat.lt_iff_le_not_le` + `Rat.le_total`.
//!
//! - `NNReal.CauSeq.le_cancel_of_const_lower : ∀ (d : Rat)(hd : 0≤d)
//!     (hpos : 0<d)(cf af bf : CauSeq),
//!     CauSeq.le (CauSeq.const (NNRat.ofRat d hd)) cf →
//!     CauSeq.le (CauSeq.mul cf af)(CauSeq.mul cf bf) → CauSeq.le af bf` — the
//!   CauSeq-level core. For tolerance ε it picks `dlo := d/2 > 0`, extracts an
//!   eventual `d/2 ≤ vc n` from the lower-bound hyp at `ε':=d/2` (via
//!   `add_halves` + `lt_of_add_lt_add_right`), extracts
//!   `vc·va < vc·vb + (d/2)·ε` from the product hyp at `ε'':=(d/2)·ε`
//!   (`mul_pos`), transports the product endpoints through `NNRat.val_mul`, and
//!   applies the Rat cancellation at index `max(N1,N2)`.
//!
//! - `NNReal.le_of_mul_le_mul_of_ofRat_lower : ∀ (c a b : NNReal)(d : Rat)
//!     (hd : 0≤d)(hpos : 0<d),
//!     NNReal.le (NNReal.ofRat d hd) c →
//!     NNReal.le (NNReal.mul c a)(NNReal.mul c b) → NNReal.le a b` — the quotient
//!   lift: triple `Quot.ind` on `c,a,b` reduces each leaf to the CauSeq core
//!   (`NNReal.ofRat d hd ≡ mk (const (ofRat d hd))`, so the lower-bound hyp
//!   reduces to the `CauSeq.const` form).
//!
//! Each theorem is `Declaration::Theorem`, `ProofQuality::Constructive`, with an
//! empty admitted-axiom closure (foundational only). NO `sorry` /
//! `add_decl_unchecked` / `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the cancellation.
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
pub(crate) struct MulCancelConsts {
    nat: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_two: Expr,
    #[cfg(test)]
    nnrat: Expr,
    nnrat_val: Expr,
    nnrat_val_mul: Expr,
    nnrat_mul: Expr,
    nnrat_of_rat: Expr,
    nnrat_property: Expr,
    causeq: Expr,
    causeq_equiv: Expr,
    causeq_seq: Expr,
    causeq_le: Expr,
    causeq_mul: Expr,
    causeq_const: Expr,
    rat_add: Expr,
    rat_mul: Expr,
    rat_div: Expr,
    rat_lt: Expr,
    rat_le: Expr,
    nat_le: Expr,
    // Rat lemmas.
    rat_le_refl: Expr,
    rat_le_total: Expr,
    rat_lt_iff_le_not_le: Expr,
    rat_le_trans: Expr,
    rat_lt_of_le_of_lt: Expr,
    rat_mul_le_left: Expr,
    rat_mul_le_right: Expr,
    rat_left_distrib: Expr,
    rat_add_le_add: Expr,
    rat_add_halves: Expr,
    rat_half_pos: Expr,
    rat_mul_pos: Expr,
    rat_lt_of_add_lt_add_right: Expr,
    // Nat lemmas.
    nat_max: Expr,
    nat_le_max_left: Expr,
    nat_le_max_right: Expr,
    nat_le_trans: Expr,
    // Logic.
    and_c: Expr,
    and_intro: Expr,
    and_left: Expr,
    and_right: Expr,
    not_c: Expr,
    iff_mp: Expr,
    iff_mpr: Expr,
    false_elim: Expr,
    or_c: Expr,
    or_rec: Expr,
    exists_c: Expr,
    exists_intro: Expr,
    exists_elim: Expr,
    #[cfg(test)]
    eq_rat: Expr,
    eq_symm: Expr,
    eq_subst: Expr,
    quot_mk: Expr,
    quot_ind: Expr,
}

impl MulCancelConsts {
    pub(crate) fn new() -> Self {
        let lvl0 = Level::zero();
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_two: k("Rat.two"),
            #[cfg(test)]
            nnrat: k("NNRat"),
            nnrat_val: k("NNRat.val"),
            nnrat_val_mul: k("NNRat.val_mul"),
            nnrat_mul: k("NNRat.mul"),
            nnrat_of_rat: k("NNRat.ofRat"),
            nnrat_property: k("NNRat.property"),
            causeq: k("NNReal.CauSeq"),
            causeq_equiv: k("NNReal.CauSeq.Equiv"),
            causeq_seq: k("NNReal.CauSeq.seq"),
            causeq_le: k("NNReal.CauSeq.le"),
            causeq_mul: k("NNReal.CauSeq.mul"),
            causeq_const: k("NNReal.CauSeq.const"),
            rat_add: k("Rat.add"),
            rat_mul: k("Rat.mul"),
            rat_div: k("Rat.div"),
            rat_lt: k("Rat.lt"),
            rat_le: k("Rat.le"),
            nat_le: k("Nat.le"),
            rat_le_refl: k("Rat.le_refl"),
            rat_le_total: k("Rat.le_total"),
            rat_lt_iff_le_not_le: k("Rat.lt_iff_le_not_le"),
            rat_le_trans: k("Rat.le_trans"),
            rat_lt_of_le_of_lt: k("Rat.lt_of_le_of_lt"),
            rat_mul_le_left: k("Rat.mul_le_mul_of_nonneg_left"),
            rat_mul_le_right: k("Rat.mul_le_mul_of_nonneg_right"),
            rat_left_distrib: k("Rat.left_distrib"),
            rat_add_le_add: k("Rat.add_le_add"),
            rat_add_halves: k("Rat.add_halves"),
            rat_half_pos: k("Rat.half_pos"),
            rat_mul_pos: k("Rat.mul_pos"),
            rat_lt_of_add_lt_add_right: k("Rat.lt_of_add_lt_add_right"),
            nat_max: k("Nat.max"),
            nat_le_max_left: k("Nat.le_max_left"),
            nat_le_max_right: k("Nat.le_max_right"),
            nat_le_trans: k("Nat.le_trans"),
            and_c: k("And"),
            and_intro: k("And.intro"),
            and_left: k("And.left"),
            and_right: k("And.right"),
            not_c: k("Not"),
            iff_mp: k("Iff.mp"),
            iff_mpr: k("Iff.mpr"),
            false_elim: Expr::const_(Name::from_string("False.elim"), vec![lvl0]),
            or_c: k("Or"),
            or_rec: k("Or.rec"),
            exists_c: Expr::const_(Name::from_string("Exists"), vec![lvl1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![lvl1.clone()]),
            exists_elim: Expr::const_(Name::from_string("Exists.elim"), vec![lvl1.clone()]),
            #[cfg(test)]
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![lvl1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1.clone()]),
            quot_mk: Expr::const_(Name::from_string("Quot.mk"), vec![lvl1.clone()]),
            quot_ind: Expr::const_(Name::from_string("Quot.ind"), vec![lvl1]),
        }
    }

    // ── Rat term constructors ────────────────────────────────────────────────
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
    fn half(&self, eps: &Expr) -> Expr {
        Expr::apps(self.rat_div.clone(), [eps.clone(), self.rat_two.clone()])
    }
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    fn val(&self, q: Expr) -> Expr {
        Expr::app(self.nnrat_val.clone(), q)
    }
    fn seq_at(&self, x: &Expr, n: &Expr) -> Expr {
        Expr::app(Expr::app(self.causeq_seq.clone(), x.clone()), n.clone())
    }
    fn vseq(&self, x: &Expr, n: &Expr) -> Expr {
        self.val(self.seq_at(x, n))
    }
    fn nnmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnrat_mul.clone(), [a, b])
    }
    fn cau_mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_mul.clone(), [a, b])
    }
    fn cau_const(&self, q: Expr) -> Expr {
        Expr::app(self.causeq_const.clone(), q)
    }
    fn causeq_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_le.clone(), [a, b])
    }
    fn property_seq(&self, x: &Expr, n: &Expr) -> Expr {
        Expr::app(self.nnrat_property.clone(), self.seq_at(x, n))
    }

    // ── Rat proof constructors ───────────────────────────────────────────────
    fn le_refl(&self, a: Expr) -> Expr {
        Expr::app(self.rat_le_refl.clone(), a)
    }
    fn le_trans(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(self.rat_le_trans.clone(), [a, b, cc, hab, hbc])
    }
    fn lt_of_le_of_lt(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(self.rat_lt_of_le_of_lt.clone(), [a, b, cc, hab, hbc])
    }
    /// `Rat.mul_le_mul_of_nonneg_left a b c (b≤c)(0≤a) : a·b ≤ a·c`.
    fn mul_le_left(&self, a: Expr, b: Expr, cc: Expr, hbc: Expr, ha: Expr) -> Expr {
        Expr::apps(self.rat_mul_le_left.clone(), [a, b, cc, hbc, ha])
    }
    /// `Rat.mul_le_mul_of_nonneg_right a b c (b≤c)(0≤a) : b·a ≤ c·a`.
    fn mul_le_right(&self, a: Expr, b: Expr, cc: Expr, hbc: Expr, ha: Expr) -> Expr {
        Expr::apps(self.rat_mul_le_right.clone(), [a, b, cc, hbc, ha])
    }
    /// `Rat.add_le_add a b c d (a≤b)(c≤d) : a+c ≤ b+d`.
    fn add_le_add(&self, a: Expr, b: Expr, cc: Expr, d: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_add_le_add.clone(), [a, b, cc, d, h1, h2])
    }
    /// `Rat.left_distrib a b c : a·(b+c) = a·b + a·c`.
    fn left_distrib(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_left_distrib.clone(), [a, b, cc])
    }
    /// `Rat.add_halves e : (e/2)+(e/2) = e`.
    fn add_halves(&self, e: &Expr) -> Expr {
        Expr::app(self.rat_add_halves.clone(), e.clone())
    }
    /// `Rat.half_pos e (0<e) : 0 < e/2`.
    fn half_pos(&self, e: &Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_half_pos.clone(), [e.clone(), h])
    }
    /// `Rat.mul_pos a b (0<a)(0<b) : 0 < a·b`.
    fn mul_pos(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.rat_mul_pos.clone(), [a, b, ha, hb])
    }
    /// `Rat.lt_of_add_lt_add_right a b c ((a+c)<(b+c)) : a < b`.
    fn lt_of_add_lt_add_right(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_lt_of_add_lt_add_right.clone(), [a, b, cc, h])
    }
    /// `Rat.le_total a b : Or (a≤b)(b≤a)`.
    fn le_total(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le_total.clone(), [a, b])
    }
    fn nat_le_trans(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(self.nat_le_trans.clone(), [a, b, cc, hab, hbc])
    }
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
    /// `NNRat.val_mul p q : val (NNRat.mul p q) = (val p)·(val q)`.
    fn val_mul(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.nnrat_val_mul.clone(), [p, q])
    }
    /// `Rat.le a b` from `hlt : Rat.lt a b` via
    /// `And.left (Iff.mp (lt_iff_le_not_le a b) hlt)`.
    fn le_of_lt(&self, a: Expr, b: Expr, hlt: Expr) -> Expr {
        let le_ab = self.rle(a.clone(), b.clone());
        let not_le_ba = Expr::app(self.not_c.clone(), self.rle(b.clone(), a.clone()));
        let and_ty = Expr::apps(self.and_c.clone(), [le_ab.clone(), not_le_ba.clone()]);
        let lt_ab = self.rlt(a.clone(), b.clone());
        let iff = Expr::apps(self.rat_lt_iff_le_not_le.clone(), [a, b]);
        let mp = Expr::apps(self.iff_mp.clone(), [lt_ab, and_ty, iff, hlt]);
        Expr::apps(self.and_left.clone(), [le_ab, not_le_ba, mp])
    }

    fn nnreal(&self) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Quot"), vec![Level::succ(Level::zero())]),
            [self.causeq.clone(), self.causeq_equiv.clone()],
        )
    }
    fn quot_mk(&self, l: Expr) -> Expr {
        Expr::apps(
            self.quot_mk.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone(), l],
        )
    }

    /// `fun N => ∀ n, N≤n → vseq a n < vseq b n + eps`.
    fn pred_n(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr, eps: &Expr) -> Expr {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (n_id, cap) = bn.fresh_local(self.nat.clone());
        let inner = self.pred_n_at(&bn, a, b, eps, &cap);
        bn.finish_child(bn.mk_lam(n_id, BinderInfo::Default, self.nat.clone(), inner))
    }
    fn pred_n_at(
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
        let concl = self.rlt(self.vseq(a, &m), self.radd(self.vseq(b, &m), eps.clone()));
        let e = bn.mk_pi(hle_id, BinderInfo::Default, hle, concl);
        let e = bn.mk_pi(m_id, BinderInfo::Default, self.nat.clone(), e);
        bn.finish_child(e)
    }
    fn exists_pred(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr, eps: &Expr) -> Expr {
        Expr::apps(
            self.exists_c.clone(),
            [self.nat.clone(), self.pred_n(parent, a, b, eps)],
        )
    }
}

impl Environment {
    /// Register `Rat.lt_add_of_mul_lt_mul_lower`,
    /// `NNReal.CauSeq.le_cancel_of_const_lower`, and
    /// `NNReal.le_of_mul_le_mul_of_ofRat_lower`. Idempotent.
    pub fn init_algebra_nnreal_mul_cancel(&mut self) -> Result<(), EnvError> {
        // The whole NNReal mul/le/CauSeq/bounded surface plus the Rat order /
        // field / half lemmas (mul_le_mul_of_nonneg_*, lt_of_le_of_lt, le_trans,
        // le_refl, left_distrib, add_le_add, add_halves, half_pos, le_total,
        // lt_iff_le_not_le, mul_pos) come transitively from this single init.
        self.init_algebra_nnreal_reverse_square_mono()?;
        // `Rat.lt_of_add_lt_add_right`.
        self.init_algebra_nnreal_cancel()?;
        self.init_or()?;
        self.init_and()?;
        self.init_iff()?;
        self.init_true_false()?;
        self.init_eq()?;
        self.init_exists()?;

        let c = MulCancelConsts::new();
        self.register_rat_lt_add_of_mul_lt_mul_lower(&c)?;
        self.register_causeq_le_cancel_of_const_lower(&c)?;
        self.register_nnreal_le_of_mul_le_mul_of_ofrat_lower(&c)?;
        Ok(())
    }

    /// `Rat.lt_add_of_mul_lt_mul_lower : ∀ (vc va vb dlo eps : Rat),
    ///   0 ≤ vc → dlo ≤ vc → 0 ≤ eps →
    ///   Rat.lt (vc·va) ((vc·vb) + dlo·eps) → Rat.lt va (vb + eps)`.
    fn register_rat_lt_add_of_mul_lt_mul_lower(
        &mut self,
        c: &MulCancelConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.lt_add_of_mul_lt_mul_lower");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (vc_id, vc) = b.fresh_local(c.rat.clone());
            let (va_id, va) = b.fresh_local(c.rat.clone());
            let (vb_id, vb) = b.fresh_local(c.rat.clone());
            let (dlo_id, dlo) = b.fresh_local(c.rat.clone());
            let (eps_id, eps) = b.fresh_local(c.rat.clone());
            let h0vc = c.rle(c.rat_zero.clone(), vc.clone());
            let (h0vc_id, _) = b.fresh_local(h0vc.clone());
            let hdvc = c.rle(dlo.clone(), vc.clone());
            let (hdvc_id, _) = b.fresh_local(hdvc.clone());
            let h0eps = c.rle(c.rat_zero.clone(), eps.clone());
            let (h0eps_id, _) = b.fresh_local(h0eps.clone());
            let hmul = c.rlt(
                c.rmul(vc.clone(), va.clone()),
                c.radd(
                    c.rmul(vc.clone(), vb.clone()),
                    c.rmul(dlo.clone(), eps.clone()),
                ),
            );
            let (hmul_id, _) = b.fresh_local(hmul.clone());
            let concl = c.rlt(va.clone(), c.radd(vb.clone(), eps.clone()));
            let e = b.mk_pi(hmul_id, BinderInfo::Default, hmul, concl);
            let e = b.mk_pi(h0eps_id, BinderInfo::Default, h0eps, e);
            let e = b.mk_pi(hdvc_id, BinderInfo::Default, hdvc, e);
            let e = b.mk_pi(h0vc_id, BinderInfo::Default, h0vc, e);
            let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(dlo_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(vb_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(va_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(vc_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = build_rat_lt_add_of_mul_lt_mul_lower(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.CauSeq.le_cancel_of_const_lower`.
    fn register_causeq_le_cancel_of_const_lower(
        &mut self,
        c: &MulCancelConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.CauSeq.le_cancel_of_const_lower");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.rat.clone());
            let hd_ty = c.rle(c.rat_zero.clone(), d.clone());
            let (hd_id, hd) = b.fresh_local(hd_ty.clone());
            let hpos_ty = c.rlt(c.rat_zero.clone(), d.clone());
            let (hpos_id, _) = b.fresh_local(hpos_ty.clone());
            let (cf_id, cf) = b.fresh_local(c.causeq.clone());
            let (af_id, af) = b.fresh_local(c.causeq.clone());
            let (bf_id, bf) = b.fresh_local(c.causeq.clone());
            let const_d = c.cau_const(Expr::apps(c.nnrat_of_rat.clone(), [d.clone(), hd.clone()]));
            let hlow_ty = c.causeq_le(const_d, cf.clone());
            let (hlow_id, _) = b.fresh_local(hlow_ty.clone());
            let hmul_ty = c.causeq_le(
                c.cau_mul(cf.clone(), af.clone()),
                c.cau_mul(cf.clone(), bf.clone()),
            );
            let (hmul_id, _) = b.fresh_local(hmul_ty.clone());
            let concl = c.causeq_le(af.clone(), bf.clone());
            let e = b.mk_pi(hmul_id, BinderInfo::Default, hmul_ty, concl);
            let e = b.mk_pi(hlow_id, BinderInfo::Default, hlow_ty, e);
            let e = b.mk_pi(bf_id, BinderInfo::Default, c.causeq.clone(), e);
            let e = b.mk_pi(af_id, BinderInfo::Default, c.causeq.clone(), e);
            let e = b.mk_pi(cf_id, BinderInfo::Default, c.causeq.clone(), e);
            let e = b.mk_pi(hpos_id, BinderInfo::Default, hpos_ty, e);
            let e = b.mk_pi(hd_id, BinderInfo::Default, hd_ty, e);
            let e = b.mk_pi(d_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = build_causeq_le_cancel(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.le_of_mul_le_mul_of_ofRat_lower`.
    fn register_nnreal_le_of_mul_le_mul_of_ofrat_lower(
        &mut self,
        c: &MulCancelConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.le_of_mul_le_mul_of_ofRat_lower");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nnreal = c.nnreal();
        let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
        let nnmul = Expr::const_(Name::from_string("NNReal.mul"), vec![]);
        let of_rat = Expr::const_(Name::from_string("NNReal.ofRat"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (cv_id, cv) = b.fresh_local(nnreal.clone());
            let (av_id, av) = b.fresh_local(nnreal.clone());
            let (bv_id, bv) = b.fresh_local(nnreal.clone());
            let (d_id, d) = b.fresh_local(c.rat.clone());
            let hd_ty = c.rle(c.rat_zero.clone(), d.clone());
            let (hd_id, hd) = b.fresh_local(hd_ty.clone());
            let hpos_ty = c.rlt(c.rat_zero.clone(), d.clone());
            let (hpos_id, _) = b.fresh_local(hpos_ty.clone());
            let ofd = Expr::apps(of_rat.clone(), [d.clone(), hd.clone()]);
            let hlow_ty = Expr::apps(nnle.clone(), [ofd, cv.clone()]);
            let (hlow_id, _) = b.fresh_local(hlow_ty.clone());
            let mul_ca = Expr::apps(nnmul.clone(), [cv.clone(), av.clone()]);
            let mul_cb = Expr::apps(nnmul.clone(), [cv.clone(), bv.clone()]);
            let hmul_ty = Expr::apps(nnle.clone(), [mul_ca, mul_cb]);
            let (hmul_id, _) = b.fresh_local(hmul_ty.clone());
            let concl = Expr::apps(nnle.clone(), [av.clone(), bv.clone()]);
            let e = b.mk_pi(hmul_id, BinderInfo::Default, hmul_ty, concl);
            let e = b.mk_pi(hlow_id, BinderInfo::Default, hlow_ty, e);
            let e = b.mk_pi(hpos_id, BinderInfo::Default, hpos_ty, e);
            let e = b.mk_pi(hd_id, BinderInfo::Default, hd_ty, e);
            let e = b.mk_pi(d_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, nnreal.clone(), e);
            let e = b.mk_pi(av_id, BinderInfo::Default, nnreal.clone(), e);
            let e = b.mk_pi(cv_id, BinderInfo::Default, nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_nnreal_le_of_mul_cancel(c, &nnreal);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Build the per-index Rat cancellation proof value.
fn build_rat_lt_add_of_mul_lt_mul_lower(c: &MulCancelConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (vc_id, vc) = b.fresh_local(c.rat.clone());
    let (va_id, va) = b.fresh_local(c.rat.clone());
    let (vb_id, vb) = b.fresh_local(c.rat.clone());
    let (dlo_id, dlo) = b.fresh_local(c.rat.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let h0vc_ty = c.rle(c.rat_zero.clone(), vc.clone());
    let (h0vc_id, h0vc) = b.fresh_local(h0vc_ty.clone());
    let hdvc_ty = c.rle(dlo.clone(), vc.clone());
    let (hdvc_id, hdvc) = b.fresh_local(hdvc_ty.clone());
    let h0eps_ty = c.rle(c.rat_zero.clone(), eps.clone());
    let (h0eps_id, h0eps) = b.fresh_local(h0eps_ty.clone());
    let vc_vb = c.rmul(vc.clone(), vb.clone());
    let dlo_eps = c.rmul(dlo.clone(), eps.clone());
    let rhs = c.radd(vc_vb.clone(), dlo_eps.clone()); // vc·vb + dlo·eps
    let hmul_ty = c.rlt(c.rmul(vc.clone(), va.clone()), rhs.clone());
    let (hmul_id, hmul) = b.fresh_local(hmul_ty.clone());

    let vb_eps = c.radd(vb.clone(), eps.clone()); // vb + eps

    // not_le : (vb+eps ≤ va) → False.
    let not_le = {
        let mut nb = EnvDeclBuilder::child_of(&b);
        let hge_ty = c.rle(vb_eps.clone(), va.clone());
        let (hge_id, hge) = nb.fresh_local(hge_ty.clone());

        // s1 : vc·(vb+eps) ≤ vc·va.
        let s1 = c.mul_le_left(vc.clone(), vb_eps.clone(), va.clone(), hge, h0vc.clone());
        // distrib : vc·(vb+eps) = vc·vb + vc·eps.
        let vc_eps = c.rmul(vc.clone(), eps.clone());
        let distrib = c.left_distrib(vc.clone(), vb.clone(), eps.clone());
        let vc_vbeps = c.rmul(vc.clone(), vb_eps.clone());
        let vcvb_vceps = c.radd(vc_vb.clone(), vc_eps.clone());
        // s1' : (vc·vb + vc·eps) ≤ vc·va  [subst s1 along distrib on the LHS].
        let m_s1 = {
            let mut mb = EnvDeclBuilder::child_of(&nb);
            let (t_id, t) = mb.fresh_local(c.rat.clone());
            let body = c.rle(t, c.rmul(vc.clone(), va.clone()));
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let s1p = c.subst(m_s1, vc_vbeps.clone(), vcvb_vceps.clone(), distrib, s1);

        // s2 : dlo·eps ≤ vc·eps.
        let s2 = c.mul_le_right(
            eps.clone(),
            dlo.clone(),
            vc.clone(),
            hdvc.clone(),
            h0eps.clone(),
        );
        // s3 : (vc·vb + dlo·eps) ≤ (vc·vb + vc·eps).
        let s3 = c.add_le_add(
            vc_vb.clone(),
            vc_vb.clone(),
            dlo_eps.clone(),
            vc_eps.clone(),
            c.le_refl(vc_vb.clone()),
            s2,
        );
        // s4 : (vc·vb + dlo·eps) ≤ vc·va.
        let s4 = c.le_trans(
            rhs.clone(),
            vcvb_vceps.clone(),
            c.rmul(vc.clone(), va.clone()),
            s3,
            s1p,
        );
        // s5 : (vc·vb + dlo·eps) < (vc·vb + dlo·eps).
        let s5 = c.lt_of_le_of_lt(
            rhs.clone(),
            c.rmul(vc.clone(), va.clone()),
            rhs.clone(),
            s4,
            hmul.clone(),
        );
        // False from s5 : X < X.
        let le_xx = c.rle(rhs.clone(), rhs.clone());
        let not_le_xx = Expr::app(c.not_c.clone(), le_xx.clone());
        let and_xx = Expr::apps(c.and_c.clone(), [le_xx.clone(), not_le_xx.clone()]);
        let lt_xx = c.rlt(rhs.clone(), rhs.clone());
        let iff_xx = Expr::apps(c.rat_lt_iff_le_not_le.clone(), [rhs.clone(), rhs.clone()]);
        let mp_xx = Expr::apps(c.iff_mp.clone(), [lt_xx, and_xx, iff_xx, s5]);
        let not_le_pf = Expr::apps(c.and_right.clone(), [le_xx.clone(), not_le_xx, mp_xx]);
        let false_pf = Expr::app(not_le_pf, c.le_refl(rhs.clone()));
        nb.finish_child(nb.mk_lam(hge_id, BinderInfo::Default, hge_ty, false_pf))
    };

    // le_va : va ≤ vb+eps  from le_total va (vb+eps).
    let le_va = {
        let le_l = c.rle(va.clone(), vb_eps.clone());
        let le_r = c.rle(vb_eps.clone(), va.clone());
        let disj = c.le_total(va.clone(), vb_eps.clone());
        let or_motive = {
            let mut ob = EnvDeclBuilder::child_of(&b);
            let or_ty = Expr::apps(c.or_c.clone(), [le_l.clone(), le_r.clone()]);
            let (dd_id, _dd) = ob.fresh_local(or_ty.clone());
            ob.finish_child(ob.mk_lam(dd_id, BinderInfo::Default, or_ty, le_l.clone()))
        };
        let left = {
            let mut lb = EnvDeclBuilder::child_of(&b);
            let (h_id, h) = lb.fresh_local(le_l.clone());
            lb.finish_child(lb.mk_lam(h_id, BinderInfo::Default, le_l.clone(), h))
        };
        let right = {
            let mut rb = EnvDeclBuilder::child_of(&b);
            let (h_id, h) = rb.fresh_local(le_r.clone());
            let false_pf = Expr::app(not_le.clone(), h);
            let fe = Expr::apps(c.false_elim.clone(), [le_l.clone(), false_pf]);
            rb.finish_child(rb.mk_lam(h_id, BinderInfo::Default, le_r.clone(), fe))
        };
        Expr::apps(c.or_rec.clone(), [le_l, le_r, or_motive, left, right, disj])
    };

    // Iff.mpr (lt_iff_le_not_le va (vb+eps)) (And.intro le_va not_le).
    let lt_goal = c.rlt(va.clone(), vb_eps.clone());
    let le_part = c.rle(va.clone(), vb_eps.clone());
    let not_le_ba = Expr::app(c.not_c.clone(), c.rle(vb_eps.clone(), va.clone()));
    let and_ty = Expr::apps(c.and_c.clone(), [le_part.clone(), not_le_ba.clone()]);
    let and_intro = Expr::apps(
        c.and_intro.clone(),
        [le_part.clone(), not_le_ba.clone(), le_va, not_le],
    );
    let iff_goal = Expr::apps(c.rat_lt_iff_le_not_le.clone(), [va.clone(), vb_eps.clone()]);
    let proof = Expr::apps(c.iff_mpr.clone(), [lt_goal, and_ty, iff_goal, and_intro]);

    let e = b.mk_lam(hmul_id, BinderInfo::Default, hmul_ty, proof);
    let e = b.mk_lam(h0eps_id, BinderInfo::Default, h0eps_ty, e);
    let e = b.mk_lam(hdvc_id, BinderInfo::Default, hdvc_ty, e);
    let e = b.mk_lam(h0vc_id, BinderInfo::Default, h0vc_ty, e);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(dlo_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(vb_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(va_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(vc_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Build the CauSeq-level core proof value.
fn build_causeq_le_cancel(c: &MulCancelConsts) -> Expr {
    let rat_helper = Expr::const_(Name::from_string("Rat.lt_add_of_mul_lt_mul_lower"), vec![]);
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.rat.clone());
    let hd_ty = c.rle(c.rat_zero.clone(), d.clone());
    let (hd_id, hd) = b.fresh_local(hd_ty.clone());
    let hpos_ty = c.rlt(c.rat_zero.clone(), d.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());
    let (cf_id, cf) = b.fresh_local(c.causeq.clone());
    let (af_id, af) = b.fresh_local(c.causeq.clone());
    let (bf_id, bf) = b.fresh_local(c.causeq.clone());
    let const_d = c.cau_const(Expr::apps(c.nnrat_of_rat.clone(), [d.clone(), hd.clone()]));
    let hlow_ty = c.causeq_le(const_d.clone(), cf.clone());
    let (hlow_id, hlow) = b.fresh_local(hlow_ty.clone());
    let hmul_ty = c.causeq_le(
        c.cau_mul(cf.clone(), af.clone()),
        c.cau_mul(cf.clone(), bf.clone()),
    );
    let (hmul_id, hmul) = b.fresh_local(hmul_ty.clone());

    // Goal: CauSeq.le af bf.
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let heps_ty = c.rlt(c.rat_zero.clone(), eps.clone());
    let (heps_id, heps) = b.fresh_local(heps_ty.clone());

    let dlo = c.half(&d); // d/2
    let hdlo_pos = c.half_pos(&d, hpos.clone()); // 0 < d/2
                                                 // 0 ≤ eps from heps.
    let h0eps = c.le_of_lt(c.rat_zero.clone(), eps.clone(), heps.clone());

    // Lower-bound stream.
    let exists_n1 = Expr::apps(hlow.clone(), [dlo.clone(), hdlo_pos.clone()]);
    let pred_low = c.pred_n(&b, &const_d, &cf, &dlo);

    // Product stream at (d/2)·ε.
    let dlo_eps = c.rmul(dlo.clone(), eps.clone());
    let hdloeps_pos = c.mul_pos(dlo.clone(), eps.clone(), hdlo_pos.clone(), heps.clone());
    let cl = c.cau_mul(cf.clone(), af.clone());
    let cr = c.cau_mul(cf.clone(), bf.clone());
    let exists_n2 = Expr::apps(hmul.clone(), [dlo_eps.clone(), hdloeps_pos]);
    let pred_mul = c.pred_n(&b, &cl, &cr, &dlo_eps);

    let goal_exists = c.exists_pred(&b, &af, &bf, &eps);

    let elim_n1 = {
        let mut b1 = EnvDeclBuilder::child_of(&b);
        let (n1_id, n1) = b1.fresh_local(c.nat.clone());
        let hn1_ty = c.pred_n_at(&b1, &const_d, &cf, &dlo, &n1);
        let (hn1_id, hn1) = b1.fresh_local(hn1_ty.clone());

        let elim_n2 = {
            let mut b2 = EnvDeclBuilder::child_of(&b1);
            let (n2_id, n2) = b2.fresh_local(c.nat.clone());
            let hn2_ty = c.pred_n_at(&b2, &cl, &cr, &dlo_eps, &n2);
            let (hn2_id, hn2) = b2.fresh_local(hn2_ty.clone());

            let nmax = Expr::apps(c.nat_max.clone(), [n1.clone(), n2.clone()]);

            let witness = build_cancel_witness(
                c,
                &b2,
                &d,
                &cf,
                &af,
                &bf,
                &eps,
                &dlo,
                &dlo_eps,
                &h0eps,
                &n1,
                &n2,
                &hn1,
                &hn2,
                &rat_helper,
            );

            let intro = Expr::apps(
                c.exists_intro.clone(),
                [c.nat.clone(), c.pred_n(&b2, &af, &bf, &eps), nmax, witness],
            );
            let e = b2.mk_lam(hn2_id, BinderInfo::Default, hn2_ty, intro);
            let e = b2.mk_lam(n2_id, BinderInfo::Default, c.nat.clone(), e);
            b2.finish_child(e)
        };

        let elim = Expr::apps(
            c.exists_elim.clone(),
            [
                c.nat.clone(),
                pred_mul.clone(),
                goal_exists.clone(),
                exists_n2,
                elim_n2,
            ],
        );
        let e = b1.mk_lam(hn1_id, BinderInfo::Default, hn1_ty, elim);
        let e = b1.mk_lam(n1_id, BinderInfo::Default, c.nat.clone(), e);
        b1.finish_child(e)
    };

    let elim_outer = Expr::apps(
        c.exists_elim.clone(),
        [c.nat.clone(), pred_low, goal_exists, exists_n1, elim_n1],
    );

    let e = b.mk_lam(heps_id, BinderInfo::Default, heps_ty, elim_outer);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(hmul_id, BinderInfo::Default, hmul_ty, e);
    let e = b.mk_lam(hlow_id, BinderInfo::Default, hlow_ty, e);
    let e = b.mk_lam(bf_id, BinderInfo::Default, c.causeq.clone(), e);
    let e = b.mk_lam(af_id, BinderInfo::Default, c.causeq.clone(), e);
    let e = b.mk_lam(cf_id, BinderInfo::Default, c.causeq.clone(), e);
    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, e);
    let e = b.mk_lam(hd_id, BinderInfo::Default, hd_ty, e);
    let e = b.mk_lam(d_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// The witness `∀ m, max(N1,N2)≤m → vseq af m < vseq bf m + ε`.
#[allow(clippy::too_many_arguments)]
fn build_cancel_witness(
    c: &MulCancelConsts,
    parent: &EnvDeclBuilder,
    d: &Expr,
    cf: &Expr,
    af: &Expr,
    bf: &Expr,
    eps: &Expr,
    dlo: &Expr,
    dlo_eps: &Expr,
    h0eps: &Expr,
    n1: &Expr,
    n2: &Expr,
    hn1: &Expr,
    hn2: &Expr,
    rat_helper: &Expr,
) -> Expr {
    let mut bw = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = bw.fresh_local(c.nat.clone());
    let nmax = Expr::apps(c.nat_max.clone(), [n1.clone(), n2.clone()]);
    let hle_ty = c.nat_le(nmax.clone(), m.clone());
    let (hle_id, hle) = bw.fresh_local(hle_ty.clone());

    let le_max_l = Expr::apps(c.nat_le_max_left.clone(), [n1.clone(), n2.clone()]);
    let le_max_r = Expr::apps(c.nat_le_max_right.clone(), [n1.clone(), n2.clone()]);
    let n1_le_m = c.nat_le_trans(n1.clone(), nmax.clone(), m.clone(), le_max_l, hle.clone());
    let n2_le_m = c.nat_le_trans(n2.clone(), nmax.clone(), m.clone(), le_max_r, hle);

    let vc = c.vseq(cf, &m);
    let va = c.vseq(af, &m);
    let vb = c.vseq(bf, &m);

    // base_low : d < vc m + d/2  (vseq const(ofRat d hd) m ≡ d).
    let base_low = Expr::apps(hn1.clone(), [m.clone(), n1_le_m]);
    let dlo_dlo = c.radd(dlo.clone(), dlo.clone()); // d/2 + d/2
    let vc_dlo = c.radd(vc.clone(), dlo.clone()); // vc + d/2
                                                  // rewrite LHS d → d/2+d/2 via symm(add_halves d).
    let m_low = {
        let mut mb = EnvDeclBuilder::child_of(&bw);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.rlt(t, vc_dlo.clone());
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let half_eq = c.add_halves(d); // (d/2 + d/2) = d
    let symm_half = c.eq_symm(dlo_dlo.clone(), d.clone(), half_eq); // d = (d/2+d/2)
    let base_low_p = c.subst(m_low, d.clone(), dlo_dlo.clone(), symm_half, base_low);
    // dlo_lt_vc : d/2 < vc.
    let dlo_lt_vc = c.lt_of_add_lt_add_right(dlo.clone(), vc.clone(), dlo.clone(), base_low_p);
    // hdvc : d/2 ≤ vc.
    let hdvc = c.le_of_lt(dlo.clone(), vc.clone(), dlo_lt_vc);

    // h0vc : 0 ≤ vc  [NNRat.property (seq cf m)].
    let h0vc = c.property_seq(cf, &m);

    // base_mul : vseq(mul cf af) m < vseq(mul cf bf) m + (d/2)·ε.
    let base_mul = Expr::apps(hn2.clone(), [m.clone(), n2_le_m]);
    let seq_c = c.seq_at(cf, &m);
    let seq_a = c.seq_at(af, &m);
    let seq_b = c.seq_at(bf, &m);
    let vmul_a = c.val(c.nnmul(seq_c.clone(), seq_a.clone()));
    let vmul_b = c.val(c.nnmul(seq_c.clone(), seq_b.clone()));
    let vc_va = c.rmul(vc.clone(), va.clone());
    let vc_vb = c.rmul(vc.clone(), vb.clone());
    let valmul_a = c.val_mul(seq_c.clone(), seq_a);
    let valmul_b = c.val_mul(seq_c, seq_b);
    // step1: rewrite RHS summand vmul_b → vc·vb.
    let m_rhs = {
        let mut mb = EnvDeclBuilder::child_of(&bw);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.rlt(vmul_a.clone(), c.radd(t, dlo_eps.clone()));
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let step1 = c.subst(m_rhs, vmul_b.clone(), vc_vb.clone(), valmul_b, base_mul);
    // step2: rewrite LHS vmul_a → vc·va.
    let m_lhs = {
        let mut mb = EnvDeclBuilder::child_of(&bw);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.rlt(t, c.radd(vc_vb.clone(), dlo_eps.clone()));
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let hmul_idx = c.subst(m_lhs, vmul_a.clone(), vc_va.clone(), valmul_a, step1);

    // Rat helper: lt_add_of_mul_lt_mul_lower vc va vb (d/2) eps h0vc hdvc h0eps hmul_idx.
    let proof = Expr::apps(
        rat_helper.clone(),
        [
            vc.clone(),
            va.clone(),
            vb.clone(),
            dlo.clone(),
            eps.clone(),
            h0vc,
            hdvc,
            h0eps.clone(),
            hmul_idx,
        ],
    );

    let e = bw.mk_lam(hle_id, BinderInfo::Default, hle_ty, proof);
    let e = bw.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
    bw.finish_child(e)
}

/// `NNReal.le_of_mul_le_mul_of_ofRat_lower` via triple `Quot.ind` on `c,a,b`.
/// The core `NNReal.CauSeq.le_cancel_of_const_lower` closes each leaf
/// (`ofRat d hd ≡ mk (const (ofRat d hd))`, `mul (mk cf)(mk af) ≡ mk (mul cf af)`).
fn build_nnreal_le_of_mul_cancel(c: &MulCancelConsts, nnreal: &Expr) -> Expr {
    let core = Expr::const_(
        Name::from_string("NNReal.CauSeq.le_cancel_of_const_lower"),
        vec![],
    );
    let mut b = EnvDeclBuilder::new();
    let (cv_id, cv) = b.fresh_local(nnreal.clone());
    let (av_id, av) = b.fresh_local(nnreal.clone());
    let (bv_id, bv) = b.fresh_local(nnreal.clone());
    let (d_id, d) = b.fresh_local(c.rat.clone());
    let hd_ty = c.rle(c.rat_zero.clone(), d.clone());
    let (hd_id, hd) = b.fresh_local(hd_ty.clone());
    let hpos_ty = c.rlt(c.rat_zero.clone(), d.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

    let body = descend_c(c, &b, nnreal, &cv, &av, &bv, &d, &hd, &hpos, &core);

    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, body);
    let e = b.mk_lam(hd_id, BinderInfo::Default, hd_ty, e);
    let e = b.mk_lam(d_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, nnreal.clone(), e);
    let e = b.mk_lam(av_id, BinderInfo::Default, nnreal.clone(), e);
    let e = b.mk_lam(cv_id, BinderInfo::Default, nnreal.clone(), e);
    b.finish(e)
}

/// The hypotheses-and-conclusion telescope `(hlow → hmul → concl)` for given
/// multiplier `cc`, factors `aa,bb`, fixed `d,hd`. `nnle/nnmul/ofRat` closed.
fn cancel_imp_chain(
    _c: &MulCancelConsts,
    cc: &Expr,
    aa: &Expr,
    bb: &Expr,
    d: &Expr,
    hd: &Expr,
) -> (Expr, Expr, Expr) {
    let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
    let nnmul = Expr::const_(Name::from_string("NNReal.mul"), vec![]);
    let of_rat = Expr::const_(Name::from_string("NNReal.ofRat"), vec![]);
    let ofd = Expr::apps(of_rat, [d.clone(), hd.clone()]);
    let hlow = Expr::apps(nnle.clone(), [ofd, cc.clone()]);
    let mul_ca = Expr::apps(nnmul.clone(), [cc.clone(), aa.clone()]);
    let mul_cb = Expr::apps(nnmul.clone(), [cc.clone(), bb.clone()]);
    let hmul = Expr::apps(nnle.clone(), [mul_ca, mul_cb]);
    let concl = Expr::apps(nnle, [aa.clone(), bb.clone()]);
    (hlow, hmul, concl)
}

/// Descend on `c` (the multiplier).
#[allow(clippy::too_many_arguments)]
fn descend_c(
    c: &MulCancelConsts,
    parent: &EnvDeclBuilder,
    nnreal: &Expr,
    cv: &Expr,
    av: &Expr,
    bv: &Expr,
    d: &Expr,
    hd: &Expr,
    hpos: &Expr,
    core: &Expr,
) -> Expr {
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = mb.fresh_local(nnreal.clone());
        let (hlow, hmul, concl) = cancel_imp_chain(c, &x, av, bv, d, hd);
        let imp = Expr::pi(
            BinderInfo::Default,
            hlow,
            Expr::pi(BinderInfo::Default, hmul, concl),
        );
        mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, nnreal.clone(), imp))
    };
    let minor = {
        let mut mf = EnvDeclBuilder::child_of(parent);
        let (cf_id, cf) = mf.fresh_local(c.causeq.clone());
        let mkc = c.quot_mk(cf.clone());
        let body = descend_a(c, &mf, nnreal, &mkc, &cf, av, bv, d, hd, hpos, core);
        mf.finish_child(mf.mk_lam(cf_id, BinderInfo::Default, c.causeq.clone(), body))
    };
    Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive,
            minor,
            cv.clone(),
        ],
    )
}

/// Descend on `a`.
#[allow(clippy::too_many_arguments)]
fn descend_a(
    c: &MulCancelConsts,
    parent: &EnvDeclBuilder,
    nnreal: &Expr,
    mkc: &Expr,
    cf: &Expr,
    av: &Expr,
    bv: &Expr,
    d: &Expr,
    hd: &Expr,
    hpos: &Expr,
    core: &Expr,
) -> Expr {
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = mb.fresh_local(nnreal.clone());
        let (hlow, hmul, concl) = cancel_imp_chain(c, mkc, &x, bv, d, hd);
        let imp = Expr::pi(
            BinderInfo::Default,
            hlow,
            Expr::pi(BinderInfo::Default, hmul, concl),
        );
        mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, nnreal.clone(), imp))
    };
    let minor = {
        let mut mf = EnvDeclBuilder::child_of(parent);
        let (af_id, af) = mf.fresh_local(c.causeq.clone());
        let mka = c.quot_mk(af.clone());
        let body = descend_b(c, &mf, nnreal, mkc, cf, &mka, &af, bv, d, hd, hpos, core);
        mf.finish_child(mf.mk_lam(af_id, BinderInfo::Default, c.causeq.clone(), body))
    };
    Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive,
            minor,
            av.clone(),
        ],
    )
}

/// Descend on `b`. The leaf supplies rep `bf`; the hyps reduce to the CauSeq
/// forms and the core closes the goal.
#[allow(clippy::too_many_arguments)]
fn descend_b(
    c: &MulCancelConsts,
    parent: &EnvDeclBuilder,
    nnreal: &Expr,
    mkc: &Expr,
    cf: &Expr,
    mka: &Expr,
    af: &Expr,
    bv: &Expr,
    d: &Expr,
    hd: &Expr,
    hpos: &Expr,
    core: &Expr,
) -> Expr {
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = mb.fresh_local(nnreal.clone());
        let (hlow, hmul, concl) = cancel_imp_chain(c, mkc, mka, &x, d, hd);
        let imp = Expr::pi(
            BinderInfo::Default,
            hlow,
            Expr::pi(BinderInfo::Default, hmul, concl),
        );
        mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, nnreal.clone(), imp))
    };
    let minor = {
        let mut mf = EnvDeclBuilder::child_of(parent);
        let (bf_id, bf) = mf.fresh_local(c.causeq.clone());
        // hlow reduces: NNReal.le (ofRat d hd)(mk cf) ≡ CauSeq.le (const (ofRat d hd)) cf.
        let const_d = c.cau_const(Expr::apps(c.nnrat_of_rat.clone(), [d.clone(), hd.clone()]));
        let hlow_ty = c.causeq_le(const_d, cf.clone());
        let (hlow_id, hlow) = mf.fresh_local(hlow_ty.clone());
        // hmul reduces: NNReal.le (mul (mk cf)(mk af))(mul (mk cf)(mk bf))
        //   ≡ CauSeq.le (mul cf af)(mul cf bf).
        let hmul_ty = c.causeq_le(
            c.cau_mul(cf.clone(), af.clone()),
            c.cau_mul(cf.clone(), bf.clone()),
        );
        let (hmul_id, hmul) = mf.fresh_local(hmul_ty.clone());
        // core d hd hpos cf af bf hlow hmul : CauSeq.le af bf ≡ NNReal.le (mk af)(mk bf).
        let body = Expr::apps(
            core.clone(),
            [
                d.clone(),
                hd.clone(),
                hpos.clone(),
                cf.clone(),
                af.clone(),
                bf.clone(),
                hlow,
                hmul,
            ],
        );
        let e = mf.mk_lam(hmul_id, BinderInfo::Default, hmul_ty, body);
        let e = mf.mk_lam(hlow_id, BinderInfo::Default, hlow_ty, e);
        mf.finish_child(mf.mk_lam(bf_id, BinderInfo::Default, c.causeq.clone(), e))
    };
    Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive,
            minor,
            bv.clone(),
        ],
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &[
        "Rat.lt_add_of_mul_lt_mul_lower",
        "NNReal.CauSeq.le_cancel_of_const_lower",
        "NNReal.le_of_mul_le_mul_of_ofRat_lower",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_mul_cancel()
            .expect("init_algebra_nnreal_mul_cancel");
        env.init_algebra_nnreal_mul_cancel().expect("idempotent");
        env
    }

    #[test]
    fn test_mul_cancel_kernel_check() {
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
    fn test_mul_cancel_constructive_empty_closure() {
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
