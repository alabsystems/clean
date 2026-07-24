// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real layer — additive CANCELLATION on the `NNReal` Cauchy carrier, the
//! final-step bricks for the M2 lemma (A) deg-9 σ-route (design
//! `2026-06-20-degnine-poly-identity-helper.md`, §"Final steps after the
//! identity"): from `M·LHS' = M·22 + nonneg` conclude `LHS' ≥ 22`. The
//! `add`-cancellation `a+c = b+c → a = b` (with no positivity, since the carrier
//! is genuinely cancellative) plus its `le` shadow `a+c ≤ b+c → a ≤ b` are the
//! subtraction-free moves that strip the carried `M·32` and `M·22` terms.
//!
//! # Why this module exists
//!
//! NNReal has no subtraction. On the surface `s³+r³=2` the certificate identity
//! lands as `M·LHS' + M·32 = M·22 + M·32 + nonneg`; stripping the common `M·32`
//! summand is exactly `add_right_cancel`. The genuine content is a single
//! `CauSeq`-level domination-cancellation lemma; everything else lifts via
//! `Quot.ind` and closes through the landed `NNReal.le_antisymm`.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `Rat.lt_of_add_lt_add_right : ∀ a b c, (a+c) < (b+c) → a < b` — the Rat
//!   strict right-cancellation helper (mirrors `Rat.add_lt_add_right`'s neg-cancel
//!   bookkeeping), needed to cancel the shared per-index `vc` in the CauSeq leaf.
//! - `NNReal.CauSeq.le_of_add_le_add_right : ∀ fa fb fc,
//!       CauSeq.le (CauSeq.add fa fc)(CauSeq.add fb fc) → CauSeq.le fa fb` — the
//!   eventual-domination cancellation core: from `(va+vc) < (vb+vc)+ε` at every
//!   `n ≥ N`, reassociate the RHS to `(vb+ε)+vc` and cancel `vc` via the Rat
//!   helper to land `va < vb+ε`.
//! - `NNReal.le_of_add_le_add_right : ∀ a b c : NNReal,
//!       NNReal.le (NNReal.add a c)(NNReal.add b c) → NNReal.le a b` — the triple
//!   `Quot.ind` lift (the hypothesis ι-reduces through the `NNReal.add` /
//!   `NNReal.le` `Quot.lift`s to the `CauSeq` core).
//! - `NNReal.add_right_cancel : ∀ a b c : NNReal,
//!       NNReal.add a c = NNReal.add b c → a = b` — from the `Eq NNReal` derive
//!       both `le (a+c)(b+c)` and `le (b+c)(a+c)` (`Eq.subst` + `le.refl`), apply
//!       the `le`-cancellation twice, and close with `NNReal.le_antisymm`.
//!
//! Each declaration is `Declaration::Theorem`, `ProofQuality::Constructive`, with
//! empty admitted-axiom closure (foundational only). NO `sorry` /
//! `add_decl_unchecked` / `add_decl_structural` / `Real` / `Rat.dist`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the cancellation bricks.
pub(crate) struct CancelConsts {
    nat: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_neg: Expr,
    rat_add: Expr,
    rat_lt: Expr,
    nnrat_val: Expr,
    nnrat_add: Expr,
    nnrat_val_add: Expr,
    causeq: Expr,
    causeq_seq: Expr,
    causeq_equiv: Expr,
    causeq_le: Expr,
    causeq_add: Expr,
    nat_le: Expr,
    // Rat lemmas.
    rat_add_assoc: Expr,
    rat_add_comm: Expr,
    rat_add_zero: Expr,
    rat_add_neg_self: Expr,
    rat_add_lt_add_right: Expr,
    rat_lt_of_add_lt_add_right: Expr,
    // Logic / Eq.{1}.
    exists_c: Expr,
    exists_intro: Expr,
    exists_elim: Expr,
    eq_rat: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    eq_subst: Expr,
    congr_arg: Expr,
    // Quot machinery at level 1.
    quot: Expr,
    quot_mk: Expr,
    quot_ind: Expr,
}

impl CancelConsts {
    pub(crate) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_neg: k("Rat.neg"),
            rat_add: k("Rat.add"),
            rat_lt: k("Rat.lt"),
            nnrat_val: k("NNRat.val"),
            nnrat_add: k("NNRat.add"),
            nnrat_val_add: k("NNRat.val_add"),
            causeq: k("NNReal.CauSeq"),
            causeq_seq: k("NNReal.CauSeq.seq"),
            causeq_equiv: k("NNReal.CauSeq.Equiv"),
            causeq_le: k("NNReal.CauSeq.le"),
            causeq_add: k("NNReal.CauSeq.add"),
            nat_le: k("Nat.le"),
            rat_add_assoc: k("Rat.add_assoc"),
            rat_add_comm: k("Rat.add_comm"),
            rat_add_zero: k("Rat.add_zero"),
            rat_add_neg_self: k("Rat.add_neg_self"),
            rat_add_lt_add_right: k("Rat.add_lt_add_right"),
            rat_lt_of_add_lt_add_right: k("Rat.lt_of_add_lt_add_right"),
            exists_c: Expr::const_(Name::from_string("Exists"), vec![l1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![l1.clone()]),
            exists_elim: Expr::const_(Name::from_string("Exists.elim"), vec![l1.clone()]),
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            quot: Expr::const_(Name::from_string("Quot"), vec![l1.clone()]),
            quot_mk: Expr::const_(Name::from_string("Quot.mk"), vec![l1.clone()]),
            quot_ind: Expr::const_(Name::from_string("Quot.ind"), vec![l1]),
        }
    }

    // ── Rat term constructors ────────────────────────────────────────────────
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn neg(&self, a: Expr) -> Expr {
        Expr::app(self.rat_neg.clone(), a)
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    /// `NNRat.val (CauSeq.seq x n) : Rat`.
    fn vseq(&self, x: &Expr, n: &Expr) -> Expr {
        let seq = Expr::app(self.causeq_seq.clone(), x.clone());
        let at = Expr::app(seq, n.clone());
        Expr::app(self.nnrat_val.clone(), at)
    }
    /// `CauSeq.seq x n : NNRat`.
    fn seq_at(&self, x: &Expr, n: &Expr) -> Expr {
        Expr::app(Expr::app(self.causeq_seq.clone(), x.clone()), n.clone())
    }
    /// `CauSeq.add a b : CauSeq`.
    fn causeq_add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_add.clone(), [a, b])
    }
    /// `CauSeq.le a b : Prop`.
    fn causeq_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_le.clone(), [a, b])
    }

    // ── Rat proof constructors ───────────────────────────────────────────────
    /// `Rat.add_assoc a b c : Eq Rat ((a+b)+c)(a+(b+c))`.
    fn add_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_add_assoc.clone(), [a, b, cc])
    }
    /// `Rat.add_comm a b : Eq Rat (a+b)(b+a)`.
    fn add_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add_comm.clone(), [a, b])
    }
    /// `Rat.add_zero a : Eq Rat (a+0) a`.
    fn add_zero(&self, a: Expr) -> Expr {
        Expr::app(self.rat_add_zero.clone(), a)
    }
    /// `Rat.add_neg_self a : Eq Rat (a + (-a)) 0`.
    fn add_neg_self(&self, a: Expr) -> Expr {
        Expr::app(self.rat_add_neg_self.clone(), a)
    }
    /// `Rat.add_lt_add_right a b c h : (a+c) < (b+c)` from `h : a<b`.
    fn add_lt_add_right(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_add_lt_add_right.clone(), [a, b, cc, h])
    }
    /// `Rat.lt_of_add_lt_add_right a b c h : a<b` from `h : (a+c)<(b+c)`.
    fn lt_of_add_lt_add_right(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_lt_of_add_lt_add_right.clone(), [a, b, cc, h])
    }
    /// `@Eq.trans Rat a b c hab hbc`.
    fn eq_trans(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.rat.clone(), a, b, cc, hab, hbc],
        )
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
    /// `@congrArg Rat Rat a a' f h : Eq Rat (f a)(f a')`.
    fn congr_arg(&self, a: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, a2, f, h],
        )
    }
    /// `NNRat.val_add p q : Eq Rat (val (NNRat.add p q)) ((val p)+(val q))`.
    fn val_add(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.nnrat_val_add.clone(), [p, q])
    }

    // ── CauSeq.le predicate plumbing ─────────────────────────────────────────
    /// `vseq a m < vseq b m + ε`.
    fn dom(&self, a: &Expr, b: &Expr, m: &Expr, eps: &Expr) -> Expr {
        self.lt(self.vseq(a, m), self.add(self.vseq(b, m), eps.clone()))
    }
    /// `∀ n, N≤n → vseq a n < vseq b n + ε` (predicate fully applied at `cap`).
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
        let (hle_id, _hle) = bn.fresh_local(hle.clone());
        let concl = self.dom(a, b, &m, eps);
        let e = bn.mk_pi(hle_id, BinderInfo::Default, hle, concl);
        let e = bn.mk_pi(m_id, BinderInfo::Default, self.nat.clone(), e);
        bn.finish_child(e)
    }
    /// `fun N => ∀ n, N≤n → vseq a n < vseq b n + ε`.
    fn pred_n(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr, eps: &Expr) -> Expr {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (n_id, n_cap) = bn.fresh_local(self.nat.clone());
        let inner = self.pred_n_at(&bn, a, b, eps, &n_cap);
        bn.finish_child(bn.mk_lam(n_id, BinderInfo::Default, self.nat.clone(), inner))
    }
    /// `∃ N, pred_n a b eps N : Prop`.
    fn exists_pred(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr, eps: &Expr) -> Expr {
        Expr::apps(
            self.exists_c.clone(),
            [self.nat.clone(), self.pred_n(parent, a, b, eps)],
        )
    }
    /// `@Quot.mk.{1} CauSeq Equiv l : NNReal`.
    fn quot_mk(&self, l: &Expr) -> Expr {
        Expr::apps(
            self.quot_mk.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone(), l.clone()],
        )
    }
    fn nnreal(&self) -> Expr {
        Expr::apps(
            self.quot.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone()],
        )
    }
}

impl Environment {
    /// Register the additive-cancellation bricks. Idempotent.
    pub fn init_algebra_nnreal_cancel(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_add()?; // CauSeq.add, NNReal.add, NNRat.val_add
        self.init_algebra_nnreal_le()?; // CauSeq.le, NNReal.le
        self.init_algebra_nnreal_le_antisymm()?; // NNReal.le_antisymm
        self.init_rat_field_inst()?; // add_assoc, add_comm, add_zero, add_neg_self
        self.register_rat_add_lt_add_right()?; // Rat.add_lt_add_right
        self.init_exists()?;

        let c = CancelConsts::new();
        self.register_rat_lt_of_add_lt_add_right(&c)?;
        self.register_causeq_le_of_add_le_add_right(&c)?;
        self.register_nnreal_le_of_add_le_add_right(&c)?;
        self.register_nnreal_add_right_cancel(&c)?;
        Ok(())
    }

    /// `Rat.lt_of_add_lt_add_right : ∀ a b c, (a+c) < (b+c) → a < b`.
    fn register_rat_lt_of_add_lt_add_right(&mut self, c: &CancelConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.lt_of_add_lt_add_right");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let (cv_id, cv) = b.fresh_local(c.rat.clone());
            let h_ty = c.lt(c.add(a.clone(), cv.clone()), c.add(bv.clone(), cv.clone()));
            let (h_id, _h) = b.fresh_local(h_ty.clone());
            let concl = c.lt(a.clone(), bv.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
            let e = b.mk_pi(cv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = build_rat_lt_of_add_lt_add_right(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.CauSeq.le_of_add_le_add_right :
    ///    ∀ fa fb fc, CauSeq.le (add fa fc)(add fb fc) → CauSeq.le fa fb`.
    fn register_causeq_le_of_add_le_add_right(&mut self, c: &CancelConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.CauSeq.le_of_add_le_add_right");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (fa_id, fa) = b.fresh_local(c.causeq.clone());
            let (fb_id, fb) = b.fresh_local(c.causeq.clone());
            let (fc_id, fc) = b.fresh_local(c.causeq.clone());
            let hyp = c.causeq_le(
                c.causeq_add(fa.clone(), fc.clone()),
                c.causeq_add(fb.clone(), fc.clone()),
            );
            let (h_id, _h) = b.fresh_local(hyp.clone());
            let concl = c.causeq_le(fa.clone(), fb.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let e = b.mk_pi(fc_id, BinderInfo::Default, c.causeq.clone(), e);
            let e = b.mk_pi(fb_id, BinderInfo::Default, c.causeq.clone(), e);
            let e = b.mk_pi(fa_id, BinderInfo::Default, c.causeq.clone(), e);
            b.finish(e)
        };
        let value = build_causeq_le_of_add_le_add_right(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.le_of_add_le_add_right :
    ///    ∀ a b c : NNReal, NNReal.le (add a c)(add b c) → NNReal.le a b`.
    fn register_nnreal_le_of_add_le_add_right(&mut self, c: &CancelConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.le_of_add_le_add_right");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nnreal = c.nnreal();
        let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
        let nnadd = Expr::const_(Name::from_string("NNReal.add"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nnreal.clone());
            let (bv_id, bv) = b.fresh_local(nnreal.clone());
            let (cv_id, cv) = b.fresh_local(nnreal.clone());
            let hyp = Expr::apps(
                nnle.clone(),
                [
                    Expr::apps(nnadd.clone(), [a.clone(), cv.clone()]),
                    Expr::apps(nnadd.clone(), [bv.clone(), cv.clone()]),
                ],
            );
            let (h_id, _h) = b.fresh_local(hyp.clone());
            let concl = Expr::apps(nnle.clone(), [a.clone(), bv.clone()]);
            let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let e = b.mk_pi(cv_id, BinderInfo::Default, nnreal.clone(), e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, nnreal.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_nnreal_le_of_add_le_add_right(c, &nnreal);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.add_right_cancel :
    ///    ∀ a b c : NNReal, NNReal.add a c = NNReal.add b c → a = b`.
    fn register_nnreal_add_right_cancel(&mut self, c: &CancelConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.add_right_cancel");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nnreal = c.nnreal();
        let nnadd = Expr::const_(Name::from_string("NNReal.add"), vec![]);
        let eq_nn = |x: &Expr, y: &Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [nnreal.clone(), x.clone(), y.clone()],
            )
        };
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nnreal.clone());
            let (bv_id, bv) = b.fresh_local(nnreal.clone());
            let (cv_id, cv) = b.fresh_local(nnreal.clone());
            let ac = Expr::apps(nnadd.clone(), [a.clone(), cv.clone()]);
            let bc = Expr::apps(nnadd.clone(), [bv.clone(), cv.clone()]);
            let hyp = eq_nn(&ac, &bc);
            let (h_id, _h) = b.fresh_local(hyp.clone());
            let concl = eq_nn(&a, &bv);
            let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let e = b.mk_pi(cv_id, BinderInfo::Default, nnreal.clone(), e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, nnreal.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_nnreal_add_right_cancel(c, &nnreal);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Build `Rat.lt_of_add_lt_add_right`.
///
/// From `h : (a+c) < (b+c)`:
///   `add_lt_add_right (a+c)(b+c)(-c) h : ((a+c)+(-c)) < ((b+c)+(-c))`,
/// then `cancel_right x : (x+c)+(-c) = x` (assoc + add_neg_self + add_zero)
/// rewrites both endpoints to `a < b`.
fn build_rat_lt_of_add_lt_add_right(c: &CancelConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());
    let h_ty = c.lt(c.add(a.clone(), cv.clone()), c.add(bv.clone(), cv.clone()));
    let (h_id, h) = b.fresh_local(h_ty.clone());

    let neg_c = c.neg(cv.clone());
    let ac = c.add(a.clone(), cv.clone()); // a+c
    let bc = c.add(bv.clone(), cv.clone()); // b+c

    // pushed : ((a+c)+(-c)) < ((b+c)+(-c)).
    let pushed = c.add_lt_add_right(ac.clone(), bc.clone(), neg_c.clone(), h);
    let ac_negc = c.add(ac.clone(), neg_c.clone()); // (a+c)+(-c)
    let bc_negc = c.add(bc.clone(), neg_c.clone()); // (b+c)+(-c)

    // cancel_right a : (a+c)+(-c) = a ; cancel_right b : (b+c)+(-c) = b.
    let cancel_a = build_cancel_right(c, &b, &a, &cv);
    let cancel_b = build_cancel_right(c, &b, &bv, &cv);

    // rewrite LHS endpoint via cancel_a: motive t := t < ((b+c)+(-c)).
    let motive_l = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = m.fresh_local(c.rat.clone());
        let body = c.lt(t, bc_negc.clone());
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let step_l = c.subst(motive_l, ac_negc.clone(), a.clone(), cancel_a, pushed);
    // rewrite RHS endpoint via cancel_b: motive t := a < t.
    let motive_r = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = m.fresh_local(c.rat.clone());
        let body = c.lt(a.clone(), t);
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let proof = c.subst(motive_r, bc_negc.clone(), bv.clone(), cancel_b, step_l);

    let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, proof);
    let e = b.mk_lam(cv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// `(x+c)+(-c) = x`, via:
///   `(x+c)+(-c) = x+(c+(-c))`   [add_assoc x c (-c)]
///             `= x+0`           [congrArg (x+·) (add_neg_self c)]
///             `= x`             [add_zero x]
fn build_cancel_right(c: &CancelConsts, parent: &EnvDeclBuilder, x: &Expr, cv: &Expr) -> Expr {
    let neg_c = c.neg(cv.clone());
    let xc = c.add(x.clone(), cv.clone()); // x+c
    let xc_negc = c.add(xc.clone(), neg_c.clone()); // (x+c)+(-c)
    let c_negc = c.add(cv.clone(), neg_c.clone()); // c+(-c)
    let x_cnegc = c.add(x.clone(), c_negc.clone()); // x+(c+(-c))
    let x_zero = c.add(x.clone(), c.rat_zero.clone()); // x+0

    // s0 : (x+c)+(-c) = x+(c+(-c)).
    let s0 = c.add_assoc(x.clone(), cv.clone(), neg_c.clone());
    // s1 : x+(c+(-c)) = x+0  via congrArg (x+·) (add_neg_self c).
    let add_x_fn = {
        let mut fb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = fb.fresh_local(c.rat.clone());
        let body = c.add(x.clone(), t);
        fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let s1 = c.congr_arg(
        c_negc.clone(),
        c.rat_zero.clone(),
        add_x_fn,
        c.add_neg_self(cv.clone()),
    );
    // s2 : x+0 = x  [add_zero x].
    let s2 = c.add_zero(x.clone());
    // chain s0 → s1 → s2.
    let chain1 = c.eq_trans(xc_negc.clone(), x_cnegc, x_zero.clone(), s0, s1);
    c.eq_trans(xc_negc, x_zero, x.clone(), chain1, s2)
}

/// Build `NNReal.CauSeq.le_of_add_le_add_right`.
fn build_causeq_le_of_add_le_add_right(c: &CancelConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (fa_id, fa) = b.fresh_local(c.causeq.clone());
    let (fb_id, fb) = b.fresh_local(c.causeq.clone());
    let (fc_id, fc) = b.fresh_local(c.causeq.clone());
    let cl = c.causeq_add(fa.clone(), fc.clone());
    let cr = c.causeq_add(fb.clone(), fc.clone());
    let hyp_ty = c.causeq_le(cl.clone(), cr.clone());
    let (h_id, h) = b.fresh_local(hyp_ty.clone());

    // Goal: CauSeq.le fa fb = ∀ ε, 0<ε → ∃ N, ∀ n, N≤n → vfa n < vfb n + ε.
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.lt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

    // h ε hpos : ∃ N, ∀ n, N≤n → v(add fa fc) n < v(add fb fc) n + ε.
    let exists_src = Expr::apps(h.clone(), [eps.clone(), hpos.clone()]);
    let pred_src = c.pred_n(&b, &cl, &cr, &eps);
    let goal_exists = c.exists_pred(&b, &fa, &fb, &eps);

    let elim_fn = {
        let mut be = EnvDeclBuilder::child_of(&b);
        let (cap_id, cap) = be.fresh_local(c.nat.clone());
        let hn_ty = c.pred_n_at(&be, &cl, &cr, &eps, &cap);
        let (hn_id, hn) = be.fresh_local(hn_ty.clone());

        // witness over fa,fb with the SAME N=cap.
        let witness = {
            let mut bw = EnvDeclBuilder::child_of(&be);
            let (m_id, m) = bw.fresh_local(c.nat.clone());
            let hle_ty = c.nat_le(cap.clone(), m.clone());
            let (hle_id, hle) = bw.fresh_local(hle_ty.clone());

            // base : v(add fa fc) m < v(add fb fc) m + ε   (hn m hle).
            let base = Expr::apps(hn.clone(), [m.clone(), hle]);
            let proof = build_cancel_leaf(c, &bw, &fa, &fb, &fc, &m, &eps, &base);

            let e = bw.mk_lam(hle_id, BinderInfo::Default, hle_ty, proof);
            let e = bw.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
            bw.finish_child(e)
        };

        let intro = Expr::apps(
            c.exists_intro.clone(),
            [
                c.nat.clone(),
                c.pred_n(&be, &fa, &fb, &eps),
                cap.clone(),
                witness,
            ],
        );
        let e = be.mk_lam(hn_id, BinderInfo::Default, hn_ty, intro);
        let e = be.mk_lam(cap_id, BinderInfo::Default, c.nat.clone(), e);
        be.finish_child(e)
    };

    let elim = Expr::apps(
        c.exists_elim.clone(),
        [c.nat.clone(), pred_src, goal_exists, exists_src, elim_fn],
    );

    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, elim);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(h_id, BinderInfo::Default, hyp_ty, e);
    let e = b.mk_lam(fc_id, BinderInfo::Default, c.causeq.clone(), e);
    let e = b.mk_lam(fb_id, BinderInfo::Default, c.causeq.clone(), e);
    let e = b.mk_lam(fa_id, BinderInfo::Default, c.causeq.clone(), e);
    b.finish(e)
}

/// At index `m`, transform `base : v(add fa fc) m < v(add fb fc) m + ε` into the
/// goal `vfa m < vfb m + ε`, cancelling the shared `vfc m`.
///
/// Let `va := vfa m`, `vb := vfb m`, `vc := vfc m`.
/// `base` is (after `val_add`): `(va+vc) < (vb+vc)+ε`.
/// Reassociate RHS `(vb+vc)+ε = (vb+ε)+vc` (add_right_comm), then
/// `lt_of_add_lt_add_right va (vb+ε) vc : va < vb+ε`.
fn build_cancel_leaf(
    c: &CancelConsts,
    parent: &EnvDeclBuilder,
    fa: &Expr,
    fb: &Expr,
    fc: &Expr,
    m: &Expr,
    eps: &Expr,
    base: &Expr,
) -> Expr {
    let va = c.vseq(fa, m);
    let vb = c.vseq(fb, m);
    let vc = c.vseq(fc, m);
    let seq_fa = c.seq_at(fa, m);
    let seq_fb = c.seq_at(fb, m);
    let seq_fc = c.seq_at(fc, m);

    let va_vc = c.add(va.clone(), vc.clone()); // va+vc
    let vb_vc = c.add(vb.clone(), vc.clone()); // vb+vc
    let vb_eps = c.add(vb.clone(), eps.clone()); // vb+ε

    // ── Step A: rewrite base's endpoints v(add f. fc) m → (v.+vc) ──
    // val_add (seq fa m)(seq fc m) : v(NNRat.add ..) = va+vc, and
    // v(add fa fc) m ≡ v(NNRat.add (seq fa m)(seq fc m)) (defeq).
    let val_add_l = c.val_add(seq_fa.clone(), seq_fc.clone()); // vL_form = va+vc
    let val_add_r = c.val_add(seq_fb.clone(), seq_fc.clone()); // vR_form = vb+vc
    let vl_form = Expr::app(
        c.nnrat_val.clone(),
        Expr::apps(c.nnrat_add.clone(), [seq_fa.clone(), seq_fc.clone()]),
    );
    let vr_form = Expr::app(
        c.nnrat_val.clone(),
        Expr::apps(c.nnrat_add.clone(), [seq_fb.clone(), seq_fc.clone()]),
    );

    // base : vl_form < vr_form + ε. Rewrite RHS summand vr_form → vb+vc.
    let motive_rhs = {
        let mut m2 = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = m2.fresh_local(c.rat.clone());
        let body = c.lt(vl_form.clone(), c.add(t, eps.clone()));
        m2.finish_child(m2.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let s1 = c.subst(
        motive_rhs,
        vr_form.clone(),
        vb_vc.clone(),
        val_add_r,
        base.clone(),
    );
    // Rewrite LHS vl_form → va+vc.
    let motive_lhs = {
        let mut m2 = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = m2.fresh_local(c.rat.clone());
        let body = c.lt(t, c.add(vb_vc.clone(), eps.clone()));
        m2.finish_child(m2.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    // s2 : (va+vc) < (vb+vc)+ε.
    let s2 = c.subst(motive_lhs, vl_form.clone(), va_vc.clone(), val_add_l, s1);

    // ── Step B: reassociate RHS (vb+vc)+ε = (vb+ε)+vc ──
    // reshuffle : (vb+vc)+ε = (vb+ε)+vc  (add_right_comm vb vc ε).
    let reshuffle = build_add_right_comm(c, parent, &vb, &vc, eps);
    let vb_vc_eps = c.add(vb_vc.clone(), eps.clone()); // (vb+vc)+ε
    let vb_eps_vc = c.add(vb_eps.clone(), vc.clone()); // (vb+ε)+vc
    let motive_re = {
        let mut m2 = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = m2.fresh_local(c.rat.clone());
        let body = c.lt(va_vc.clone(), t);
        m2.finish_child(m2.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    // s3 : (va+vc) < (vb+ε)+vc.
    let s3 = c.subst(motive_re, vb_vc_eps, vb_eps_vc, reshuffle, s2);

    // ── Step C: cancel vc on the right ──
    // lt_of_add_lt_add_right va (vb+ε) vc s3 : va < vb+ε.
    c.lt_of_add_lt_add_right(va.clone(), vb_eps.clone(), vc.clone(), s3)
}

/// `(b+c)+ε = (b+ε)+c`  (add_right_comm). Built from add_assoc + add_comm:
///   `(b+c)+ε = b+(c+ε)`   [add_assoc b c ε]
///          `= b+(ε+c)`    [congrArg (b+·) (add_comm c ε)]
///          `= (b+ε)+c`    [symm (add_assoc b ε c)]
fn build_add_right_comm(
    c: &CancelConsts,
    parent: &EnvDeclBuilder,
    bb: &Expr,
    cc: &Expr,
    eps: &Expr,
) -> Expr {
    // a1 : (b+c)+ε = b+(c+ε).
    let a1 = c.add_assoc(bb.clone(), cc.clone(), eps.clone());
    // a2 : b+(c+ε) = b+(ε+c)  via congrArg (b+·) (add_comm c ε).
    let comm = c.add_comm(cc.clone(), eps.clone());
    let add_b_fn = {
        let mut fb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = fb.fresh_local(c.rat.clone());
        let body = c.add(bb.clone(), t);
        fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let a2 = c.congr_arg(
        c.add(cc.clone(), eps.clone()),
        c.add(eps.clone(), cc.clone()),
        add_b_fn,
        comm,
    );
    // a3 : b+(ε+c) = (b+ε)+c  [symm (add_assoc b ε c)].
    let assoc2 = c.add_assoc(bb.clone(), eps.clone(), cc.clone());
    let a3 = c.eq_symm(
        c.add(c.add(bb.clone(), eps.clone()), cc.clone()),
        c.add(bb.clone(), c.add(eps.clone(), cc.clone())),
        assoc2,
    );
    // chain a1 → a2 → a3.
    let t_bc_eps = c.add(c.add(bb.clone(), cc.clone()), eps.clone()); // (b+c)+ε
    let t_b_c_eps = c.add(bb.clone(), c.add(cc.clone(), eps.clone())); // b+(c+ε)
    let t_b_eps_c = c.add(bb.clone(), c.add(eps.clone(), cc.clone())); // b+(ε+c)
    let t_be_c = c.add(c.add(bb.clone(), eps.clone()), cc.clone()); // (b+ε)+c
    let chain1 = c.eq_trans(t_bc_eps.clone(), t_b_c_eps, t_b_eps_c.clone(), a1, a2);
    c.eq_trans(t_bc_eps, t_b_eps_c, t_be_c, chain1, a3)
}

/// `NNReal.le_of_add_le_add_right` via triple `Quot.ind` reducing to the core.
fn build_nnreal_le_of_add_le_add_right(c: &CancelConsts, nnreal: &Expr) -> Expr {
    let core = Expr::const_(
        Name::from_string("NNReal.CauSeq.le_of_add_le_add_right"),
        vec![],
    );
    let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
    let nnadd = Expr::const_(Name::from_string("NNReal.add"), vec![]);
    let add = |x: Expr, y: Expr| Expr::apps(nnadd.clone(), [x, y]);
    let le = |x: Expr, y: Expr| Expr::apps(nnle.clone(), [x, y]);

    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(nnreal.clone());
    let (bv_id, bv) = b.fresh_local(nnreal.clone());
    let (cv_id, cv) = b.fresh_local(nnreal.clone());

    // Descend on a: motive Pa x := le (add x c)(add b c) → le x b.
    let motive_a = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(nnreal.clone());
        let hyp = le(add(x.clone(), cv.clone()), add(bv.clone(), cv.clone()));
        let (hyp_id, _h) = mb.fresh_local(hyp.clone());
        let concl = le(x.clone(), bv.clone());
        let e = mb.mk_pi(hyp_id, BinderInfo::Default, hyp, concl);
        mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, nnreal.clone(), e))
    };
    let minor_a = {
        let mut mf = EnvDeclBuilder::child_of(&b);
        let (fa_id, fa) = mf.fresh_local(c.causeq.clone());
        let mka = c.quot_mk(&fa);
        // Descend on b: motive Pb y := le (add (mk fa) c)(add y c) → le (mk fa) y.
        let body = descend_b_le(c, &mf, nnreal, &mka, &fa, &bv, &cv, &core);
        mf.finish_child(mf.mk_lam(fa_id, BinderInfo::Default, c.causeq.clone(), body))
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

/// Descend on `b` (rep `mka = mk fa` fixed). Then descend on `c`.
#[allow(clippy::too_many_arguments)]
fn descend_b_le(
    c: &CancelConsts,
    parent: &EnvDeclBuilder,
    nnreal: &Expr,
    mka: &Expr,
    fa: &Expr,
    bv: &Expr,
    cv: &Expr,
    core: &Expr,
) -> Expr {
    let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
    let nnadd = Expr::const_(Name::from_string("NNReal.add"), vec![]);
    let add = |x: Expr, y: Expr| Expr::apps(nnadd.clone(), [x, y]);
    let le = |x: Expr, y: Expr| Expr::apps(nnle.clone(), [x, y]);

    let motive_b = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (y_id, y) = mb.fresh_local(nnreal.clone());
        let hyp = le(add(mka.clone(), cv.clone()), add(y.clone(), cv.clone()));
        let (hyp_id, _h) = mb.fresh_local(hyp.clone());
        let concl = le(mka.clone(), y.clone());
        let e = mb.mk_pi(hyp_id, BinderInfo::Default, hyp, concl);
        mb.finish_child(mb.mk_lam(y_id, BinderInfo::Default, nnreal.clone(), e))
    };
    let minor_b = {
        let mut mg = EnvDeclBuilder::child_of(parent);
        let (fb_id, fb) = mg.fresh_local(c.causeq.clone());
        let mkb = c.quot_mk(&fb);
        let body = descend_c_le(c, &mg, nnreal, mka, fa, &mkb, &fb, cv, core);
        mg.finish_child(mg.mk_lam(fb_id, BinderInfo::Default, c.causeq.clone(), body))
    };
    Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive_b,
            minor_b,
            bv.clone(),
        ],
    )
}

/// Descend on `c` (reps `mka = mk fa`, `mkb = mk fb` fixed). Leaf supplies rep
/// `fc`; the hypothesis ι-reduces to the CauSeq core's hypothesis.
#[allow(clippy::too_many_arguments)]
fn descend_c_le(
    c: &CancelConsts,
    parent: &EnvDeclBuilder,
    nnreal: &Expr,
    mka: &Expr,
    fa: &Expr,
    mkb: &Expr,
    fb: &Expr,
    cv: &Expr,
    core: &Expr,
) -> Expr {
    let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
    let nnadd = Expr::const_(Name::from_string("NNReal.add"), vec![]);
    let add = |x: Expr, y: Expr| Expr::apps(nnadd.clone(), [x, y]);
    let le = |x: Expr, y: Expr| Expr::apps(nnle.clone(), [x, y]);

    let motive_c = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = mb.fresh_local(nnreal.clone());
        let hyp = le(add(mka.clone(), z.clone()), add(mkb.clone(), z.clone()));
        let (hyp_id, _h) = mb.fresh_local(hyp.clone());
        let concl = le(mka.clone(), mkb.clone());
        let e = mb.mk_pi(hyp_id, BinderInfo::Default, hyp, concl);
        mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, nnreal.clone(), e))
    };
    let minor_c = {
        let mut mh = EnvDeclBuilder::child_of(parent);
        let (fc_id, fc) = mh.fresh_local(c.causeq.clone());
        // hyp : le (add (mk fa)(mk fc))(add (mk fb)(mk fc))
        //   ≡ le (mk(CauSeq.add fa fc))(mk(CauSeq.add fb fc))     [NNReal.add ι]
        //   ≡ CauSeq.le (CauSeq.add fa fc)(CauSeq.add fb fc)      [NNReal.le ι].
        let mkc = c.quot_mk(&fc);
        let hyp = le(add(mka.clone(), mkc.clone()), add(mkb.clone(), mkc.clone()));
        let (hyp_id, hh) = mh.fresh_local(hyp.clone());
        // core fa fb fc hh : CauSeq.le fa fb ≡ NNReal.le (mk fa)(mk fb).
        let proof = Expr::apps(core.clone(), [fa.clone(), fb.clone(), fc.clone(), hh]);
        let e = mh.mk_lam(hyp_id, BinderInfo::Default, hyp, proof);
        mh.finish_child(mh.mk_lam(fc_id, BinderInfo::Default, c.causeq.clone(), e))
    };
    Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive_c,
            minor_c,
            cv.clone(),
        ],
    )
}

/// `NNReal.add_right_cancel` from the `le`-cancellation + `le_antisymm`.
///
/// From `h : add a c = add b c`:
///   `le_ac_bc : le (add a c)(add b c)` := subst (motive t := le (add a c) t) h (le.refl (add a c)).
///   `le_bc_ac : le (add b c)(add a c)` := subst (motive t := le t (add a c)) h (le.refl (add a c)).
///   `le_a_b := le_of_add_le_add_right a b c le_ac_bc`
///   `le_b_a := le_of_add_le_add_right b a c le_bc_ac`
///   `le_antisymm a b le_a_b le_b_a : a = b`.
fn build_nnreal_add_right_cancel(c: &CancelConsts, nnreal: &Expr) -> Expr {
    let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
    let nnadd = Expr::const_(Name::from_string("NNReal.add"), vec![]);
    let le_refl = Expr::const_(Name::from_string("NNReal.le.refl"), vec![]);
    let le_antisymm = Expr::const_(Name::from_string("NNReal.le_antisymm"), vec![]);
    let le_cancel = Expr::const_(Name::from_string("NNReal.le_of_add_le_add_right"), vec![]);
    let eq_subst1 = Expr::const_(
        Name::from_string("Eq.subst"),
        vec![Level::succ(Level::zero())],
    );

    let add = |x: Expr, y: Expr| Expr::apps(nnadd.clone(), [x, y]);
    let le = |x: Expr, y: Expr| Expr::apps(nnle.clone(), [x, y]);

    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(nnreal.clone());
    let (bv_id, bv) = b.fresh_local(nnreal.clone());
    let (cv_id, cv) = b.fresh_local(nnreal.clone());
    let ac = add(a.clone(), cv.clone());
    let bc = add(bv.clone(), cv.clone());
    let h_ty = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nnreal.clone(), ac.clone(), bc.clone()],
    );
    let (h_id, h) = b.fresh_local(h_ty.clone());

    // refl_ac : le (add a c)(add a c).
    let refl_ac = Expr::app(le_refl.clone(), ac.clone());

    // le_ac_bc : le (add a c)(add b c) := subst (λ t, le (add a c) t) (add a c)(add b c) h refl_ac.
    let motive_r = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = m.fresh_local(nnreal.clone());
        let body = le(ac.clone(), t);
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, nnreal.clone(), body))
    };
    let le_ac_bc = Expr::apps(
        eq_subst1.clone(),
        [
            nnreal.clone(),
            motive_r,
            ac.clone(),
            bc.clone(),
            h.clone(),
            refl_ac.clone(),
        ],
    );

    // le_bc_ac : le (add b c)(add a c) := subst (λ t, le t (add a c)) (add a c)(add b c) h refl_ac.
    let motive_l = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = m.fresh_local(nnreal.clone());
        let body = le(t, ac.clone());
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, nnreal.clone(), body))
    };
    let le_bc_ac = Expr::apps(
        eq_subst1,
        [
            nnreal.clone(),
            motive_l,
            ac.clone(),
            bc.clone(),
            h.clone(),
            refl_ac,
        ],
    );

    // le_a_b := le_of_add_le_add_right a b c le_ac_bc.
    let le_a_b = Expr::apps(
        le_cancel.clone(),
        [a.clone(), bv.clone(), cv.clone(), le_ac_bc],
    );
    // le_b_a := le_of_add_le_add_right b a c le_bc_ac.
    let le_b_a = Expr::apps(le_cancel, [bv.clone(), a.clone(), cv.clone(), le_bc_ac]);

    // le_antisymm a b le_a_b le_b_a : a = b.
    let proof = Expr::apps(le_antisymm, [a.clone(), bv.clone(), le_a_b, le_b_a]);

    let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, proof);
    let e = b.mk_lam(cv_id, BinderInfo::Default, nnreal.clone(), e);
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

    const THEOREMS: &[&str] = &[
        "Rat.lt_of_add_lt_add_right",
        "NNReal.CauSeq.le_of_add_le_add_right",
        "NNReal.le_of_add_le_add_right",
        "NNReal.add_right_cancel",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_cancel()
            .expect("init_algebra_nnreal_cancel");
        env.init_algebra_nnreal_cancel().expect("idempotent");
        env
    }

    #[test]
    fn test_nnreal_cancel_kernel_check() {
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
    fn test_nnreal_cancel_constructive_empty_closure() {
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
