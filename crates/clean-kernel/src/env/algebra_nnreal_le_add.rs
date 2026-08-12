// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — Component B, target 2: `NNReal.add_le_add`
//! (monotonicity of `NNReal.add`).
//!
//! # Why this module exists
//!
//! The `NNReal`-valued `Fin.sum` monotonicity (`NNReal.finSum_le`) closes its
//! `Nat.rec` step case by combining the prefix inequality with the last-index
//! inequality via additive monotonicity:
//!
//! - `NNReal.add_le_add : ∀ a b c d, NNReal.le a b → NNReal.le c d →
//!       NNReal.le (NNReal.add a c) (NNReal.add b d)`.
//!
//! # Proof shape (axiom-free)
//!
//! The genuine content is a standalone `CauSeq`-level lemma:
//!
//! ```text
//! CauSeq.add_le_add fa fb fc fd (hac : CauSeq.le fa fb)(hbd : CauSeq.le fc fd)
//!   : CauSeq.le (CauSeq.add fa fc)(CauSeq.add fb fd)
//! ```
//!
//! Its body, for `ε>0`, instantiates BOTH hypotheses at `ε/2`, takes the common
//! anchor `N := Nat.max N1 N2`, and at index `m` derives the combined bound from
//! `vfa < vfb + ε/2` and `vfc < vfd + ε/2`:
//!   `(vfa+vfc) < ((vfb+vfd) + ε/2) + ε/2 = (vfb+vfd) + ε`
//! (via `Rat.add_lt_add` + the `((·+ε/2)+ε/2)=(·+ε)` recombination), then
//! transports both endpoints `(vfa+vfc)`/`(vfb+vfd)` to the COMBINED-sequence
//! `val(seq(add ·) m)` form via `Eq.symm (NNRat.val_add …)`.
//!
//! `NNReal.add_le_add` is the four-fold nested `Quot.ind` lifting (mirroring
//! `NNReal.le.trans`): the leaf reduces `NNReal.le (mk fa)(mk fb)` etc. to
//! `CauSeq.le fa fb` (Quot.lift computation) and `NNReal.add (mk fa)(mk fc)` to
//! `mk (CauSeq.add fa fc)`, closing by `CauSeq.add_le_add`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for `NNReal.add_le_add`.
pub(crate) struct LeAddConsts {
    nat: Expr,
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    nat_zero: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_two: Expr,
    nnrat_val: Expr,
    nnrat_add: Expr,
    nnrat_val_add: Expr,
    causeq: Expr,
    causeq_seq: Expr,
    causeq_equiv: Expr,
    causeq_le: Expr,
    causeq_add: Expr,
    rat_add: Expr,
    rat_div: Expr,
    rat_lt: Expr,
    nat_le: Expr,
    // Rat lemmas.
    rat_half_pos: Expr,
    rat_add_lt_add: Expr,
    rat_add_assoc: Expr,
    rat_add_halves: Expr,
    rat_add_comm: Expr,
    // Nat order.
    nat_max: Expr,
    nat_le_max_left: Expr,
    nat_le_max_right: Expr,
    nat_le_trans: Expr,
    // Logic.
    exists_c: Expr,
    exists_intro: Expr,
    exists_elim: Expr,
    // Eq.{1} over Rat.
    eq_trans: Expr,
    eq_symm: Expr,
    eq_subst: Expr,
    congr_arg: Expr,
    // Quot machinery.
    quot_mk: Expr,
    quot_ind: Expr,
}

impl LeAddConsts {
    pub(crate) fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            #[cfg(test)]
            nat_zero: k("Nat.zero"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_two: k("Rat.two"),
            nnrat_val: k("NNRat.val"),
            nnrat_add: k("NNRat.add"),
            nnrat_val_add: k("NNRat.val_add"),
            causeq: k("NNReal.CauSeq"),
            causeq_seq: k("NNReal.CauSeq.seq"),
            causeq_equiv: k("NNReal.CauSeq.Equiv"),
            causeq_le: k("NNReal.CauSeq.le"),
            causeq_add: k("NNReal.CauSeq.add"),
            rat_add: k("Rat.add"),
            rat_div: k("Rat.div"),
            rat_lt: k("Rat.lt"),
            nat_le: k("Nat.le"),
            rat_half_pos: k("Rat.half_pos"),
            rat_add_lt_add: k("Rat.add_lt_add"),
            rat_add_assoc: k("Rat.add_assoc"),
            rat_add_halves: k("Rat.add_halves"),
            rat_add_comm: k("Rat.add_comm"),
            nat_max: k("Nat.max"),
            nat_le_max_left: k("Nat.le_max_left"),
            nat_le_max_right: k("Nat.le_max_right"),
            nat_le_trans: k("Nat.le_trans"),
            exists_c: Expr::const_(Name::from_string("Exists"), vec![lvl1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![lvl1.clone()]),
            exists_elim: Expr::const_(Name::from_string("Exists.elim"), vec![lvl1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![lvl1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![lvl1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1.clone()]),
            congr_arg: Expr::const_(
                Name::from_string("congrArg"),
                vec![lvl1.clone(), lvl1.clone()],
            ),
            quot_mk: Expr::const_(Name::from_string("Quot.mk"), vec![lvl1.clone()]),
            quot_ind: Expr::const_(Name::from_string("Quot.ind"), vec![lvl1]),
        }
    }

    // ── term constructors ───────────────────────────────────────────────────

    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn half(&self, eps: Expr) -> Expr {
        Expr::apps(self.rat_div.clone(), [eps, self.rat_two.clone()])
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
    /// The one-sided domination conclusion at index `m`: `vseq a m < vseq b m + ε`.
    fn dom(&self, a: &Expr, b: &Expr, m: &Expr, eps: &Expr) -> Expr {
        self.lt(self.vseq(a, m), self.add(self.vseq(b, m), eps.clone()))
    }

    /// `fun N => ∀ n, N≤n → vseq a n < vseq b n + ε`.
    fn pred_n(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr, eps: &Expr) -> Expr {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (n_id, n_cap) = bn.fresh_local(self.nat.clone());
        let inner = self.pred_n_at(&bn, a, b, eps, &n_cap);
        bn.finish_child(bn.mk_lam(n_id, BinderInfo::Default, self.nat.clone(), inner))
    }

    /// `∀ n, N≤n → vseq a n < vseq b n + ε` (the predicate fully applied at `cap`).
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

    /// `∃ N, pred_n a b eps N : Prop`.
    fn exists_pred(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr, eps: &Expr) -> Expr {
        Expr::apps(
            self.exists_c.clone(),
            [self.nat.clone(), self.pred_n(parent, a, b, eps)],
        )
    }

    /// The `CauSeq.le` body for a fixed `(f,g)`:
    ///   `∀ ε, 0<ε → ∃ N, ∀ n, N≤n → vseq f n < vseq g n + ε`.
    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    fn le_body(&self, parent: &EnvDeclBuilder, f: &Expr, g: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (eps_id, eps) = b.fresh_local(self.rat.clone());
        let hpos = self.lt(self.rat_zero.clone(), eps.clone());
        let (hpos_id, _hpos) = b.fresh_local(hpos.clone());
        let body = self.exists_pred(&b, f, g, &eps);
        let e = b.mk_pi(hpos_id, BinderInfo::Default, hpos, body);
        let e = b.mk_pi(eps_id, BinderInfo::Default, self.rat.clone(), e);
        b.finish_child(e)
    }

    // ── proof helpers ─────────────────────────────────────────────────────────

    /// `Rat.add_lt_add a b c d (h1 : a<b)(h2 : c<d) : (a+c) < (b+d)`.
    fn add_lt_add(&self, a: Expr, b: Expr, cc: Expr, d: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_add_lt_add.clone(), [a, b, cc, d, h1, h2])
    }
    /// `Rat.add_assoc a b c : Eq Rat ((a+b)+c)(a+(b+c))`.
    fn add_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_add_assoc.clone(), [a, b, cc])
    }
    /// `Rat.add_halves eps : Eq Rat ((eps/2)+(eps/2)) eps`.
    fn add_halves(&self, eps: Expr) -> Expr {
        Expr::app(self.rat_add_halves.clone(), eps)
    }
    /// `Rat.add_comm a b : Eq Rat (a+b)(b+a)`.
    fn add_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add_comm.clone(), [a, b])
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
    /// `Nat.le_trans a b c hab hbc : Nat.le a c`.
    fn nat_le_trans(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(self.nat_le_trans.clone(), [a, b, cc, hab, hbc])
    }
    /// `NNRat.val_add p q : Eq Rat (val (NNRat.add p q)) ((val p)+(val q))`.
    fn val_add(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.nnrat_val_add.clone(), [p, q])
    }
    /// `@Quot.mk.{1} CauSeq Equiv l : NNReal`.
    fn quot_mk(&self, l: Expr) -> Expr {
        Expr::apps(
            self.quot_mk.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone(), l],
        )
    }
    fn nnreal(&self) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Quot"), vec![Level::succ(Level::zero())]),
            [self.causeq.clone(), self.causeq_equiv.clone()],
        )
    }
}

impl Environment {
    /// Register `NNReal.add_le_add` (+ the `CauSeq.add_le_add` core). Idempotent.
    pub fn init_algebra_nnreal_le_add(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_add()?; // CauSeq.add, NNReal.add, NNRat.val_add
        self.init_algebra_nnreal_le()?; // CauSeq.le, NNReal.le
        self.init_algebra_rat_half_pos()?; // Rat.half_pos (+ add_halves, two)
        self.register_rat_add_lt_add()?; // Rat.add_lt_add
        self.init_rat_field_inst()?; // Rat.add_assoc, Rat.add_comm
        self.register_nat_minmax_proofs()?; // Nat.max, Nat.le_max_left/right
        self.register_nat_le_trans_proof()?; // Nat.le_trans
        self.init_exists()?;

        let c = LeAddConsts::new();
        self.register_causeq_add_le_add(&c)?;
        self.register_nnreal_add_le_add(&c)?;
        Ok(())
    }

    /// `NNReal.CauSeq.add_le_add : ∀ fa fb fc fd, CauSeq.le fa fb →
    ///     CauSeq.le fc fd → CauSeq.le (CauSeq.add fa fc)(CauSeq.add fb fd)`.
    fn register_causeq_add_le_add(&mut self, c: &LeAddConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.CauSeq.add_le_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (fa_id, fa) = b.fresh_local(c.causeq.clone());
            let (fb_id, fb) = b.fresh_local(c.causeq.clone());
            let (fc_id, fc) = b.fresh_local(c.causeq.clone());
            let (fd_id, fd) = b.fresh_local(c.causeq.clone());
            let hac = c.causeq_le(fa.clone(), fb.clone());
            let (hac_id, _h) = b.fresh_local(hac.clone());
            let hbd = c.causeq_le(fc.clone(), fd.clone());
            let (hbd_id, _h) = b.fresh_local(hbd.clone());
            let concl = c.causeq_le(
                c.causeq_add(fa.clone(), fc.clone()),
                c.causeq_add(fb.clone(), fd.clone()),
            );
            let e = b.mk_pi(hbd_id, BinderInfo::Default, hbd, concl);
            let e = b.mk_pi(hac_id, BinderInfo::Default, hac, e);
            let e = b.mk_pi(fd_id, BinderInfo::Default, c.causeq.clone(), e);
            let e = b.mk_pi(fc_id, BinderInfo::Default, c.causeq.clone(), e);
            let e = b.mk_pi(fb_id, BinderInfo::Default, c.causeq.clone(), e);
            let e = b.mk_pi(fa_id, BinderInfo::Default, c.causeq.clone(), e);
            b.finish(e)
        };
        let value = build_causeq_add_le_add_fn(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.add_le_add : ∀ a b c d, NNReal.le a b → NNReal.le c d →
    ///     NNReal.le (NNReal.add a c)(NNReal.add b d)`. Four-fold nested
    /// `Quot.ind` reducing each leaf to `CauSeq.add_le_add`.
    fn register_nnreal_add_le_add(&mut self, c: &LeAddConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.add_le_add");
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
            let (dv_id, dv) = b.fresh_local(nnreal.clone());
            let hab = Expr::apps(nnle.clone(), [a.clone(), bv.clone()]);
            let (hab_id, _h) = b.fresh_local(hab.clone());
            let hcd = Expr::apps(nnle.clone(), [cv.clone(), dv.clone()]);
            let (hcd_id, _h) = b.fresh_local(hcd.clone());
            let add_ac = Expr::apps(nnadd.clone(), [a.clone(), cv.clone()]);
            let add_bd = Expr::apps(nnadd.clone(), [bv.clone(), dv.clone()]);
            let concl = Expr::apps(nnle.clone(), [add_ac, add_bd]);
            let e = b.mk_pi(hcd_id, BinderInfo::Default, hcd, concl);
            let e = b.mk_pi(hab_id, BinderInfo::Default, hab, e);
            let e = b.mk_pi(dv_id, BinderInfo::Default, nnreal.clone(), e);
            let e = b.mk_pi(cv_id, BinderInfo::Default, nnreal.clone(), e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, nnreal.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_nnreal_add_le_add(c, &nnreal);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// The standalone `CauSeq.add_le_add` proof value.
fn build_causeq_add_le_add_fn(c: &LeAddConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (fa_id, fa) = b.fresh_local(c.causeq.clone());
    let (fb_id, fb) = b.fresh_local(c.causeq.clone());
    let (fc_id, fc) = b.fresh_local(c.causeq.clone());
    let (fd_id, fd) = b.fresh_local(c.causeq.clone());
    let hac_ty = c.causeq_le(fa.clone(), fb.clone());
    let (hac_id, hac) = b.fresh_local(hac_ty.clone());
    let hbd_ty = c.causeq_le(fc.clone(), fd.clone());
    let (hbd_id, hbd) = b.fresh_local(hbd_ty.clone());

    // goal: CauSeq.le (add fa fc)(add fb fd)
    //   = ∀ ε, 0<ε → ∃ N, ∀ n, N≤n → vseq(add fa fc) n < vseq(add fb fd) n + ε.
    let cl = c.causeq_add(fa.clone(), fc.clone());
    let cr = c.causeq_add(fb.clone(), fd.clone());

    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.lt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

    let half = c.half(eps.clone());
    let heps2 = Expr::apps(c.rat_half_pos.clone(), [eps.clone(), hpos.clone()]);
    let exists_ac = Expr::apps(hac.clone(), [half.clone(), heps2.clone()]);
    let exists_bd = Expr::apps(hbd.clone(), [half.clone(), heps2]);

    let goal_exists = c.exists_pred(&b, &cl, &cr, &eps);
    let pred_ac = c.pred_n(&b, &fa, &fb, &half);
    let pred_bd = c.pred_n(&b, &fc, &fd, &half);

    let elim_outer = {
        let mut bo = EnvDeclBuilder::child_of(&b);
        let (n1_id, n1) = bo.fresh_local(c.nat.clone());
        let hn1_ty = c.pred_n_at(&bo, &fa, &fb, &half, &n1);
        let (hn1_id, hn1) = bo.fresh_local(hn1_ty.clone());

        let elim_inner = {
            let mut bi = EnvDeclBuilder::child_of(&bo);
            let (n2_id, n2) = bi.fresh_local(c.nat.clone());
            let hn2_ty = c.pred_n_at(&bi, &fc, &fd, &half, &n2);
            let (hn2_id, hn2) = bi.fresh_local(hn2_ty.clone());

            let nmax = Expr::apps(c.nat_max.clone(), [n1.clone(), n2.clone()]);

            let witness = {
                let mut bw = EnvDeclBuilder::child_of(&bi);
                let (m_id, m) = bw.fresh_local(c.nat.clone());
                let hle_ty = c.nat_le(nmax.clone(), m.clone());
                let (hle_id, hle) = bw.fresh_local(hle_ty.clone());

                let le_max_l = Expr::apps(c.nat_le_max_left.clone(), [n1.clone(), n2.clone()]);
                let le_max_r = Expr::apps(c.nat_le_max_right.clone(), [n1.clone(), n2.clone()]);
                let n1_le_m =
                    c.nat_le_trans(n1.clone(), nmax.clone(), m.clone(), le_max_l, hle.clone());
                let n2_le_m = c.nat_le_trans(n2.clone(), nmax.clone(), m.clone(), le_max_r, hle);

                // base_ac : vfa < vfb + ε/2 ; base_bd : vfc < vfd + ε/2.
                let base_ac = Expr::apps(hn1.clone(), [m.clone(), n1_le_m]);
                let base_bd = Expr::apps(hn2.clone(), [m.clone(), n2_le_m]);

                let proof = build_combined(
                    c, &bw, &fa, &fb, &fc, &fd, &m, &eps, &half, &base_ac, &base_bd,
                );

                let e = bw.mk_lam(hle_id, BinderInfo::Default, hle_ty, proof);
                let e = bw.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
                bw.finish_child(e)
            };

            let intro = Expr::apps(
                c.exists_intro.clone(),
                [c.nat.clone(), c.pred_n(&bi, &cl, &cr, &eps), nmax, witness],
            );
            let e = bi.mk_lam(hn2_id, BinderInfo::Default, hn2_ty, intro);
            let e = bi.mk_lam(n2_id, BinderInfo::Default, c.nat.clone(), e);
            bi.finish_child(e)
        };

        let elim_bd = Expr::apps(
            c.exists_elim.clone(),
            [
                c.nat.clone(),
                pred_bd.clone(),
                goal_exists.clone(),
                exists_bd.clone(),
                elim_inner,
            ],
        );
        let e = bo.mk_lam(hn1_id, BinderInfo::Default, hn1_ty, elim_bd);
        let e = bo.mk_lam(n1_id, BinderInfo::Default, c.nat.clone(), e);
        bo.finish_child(e)
    };

    let elim_ac = Expr::apps(
        c.exists_elim.clone(),
        [c.nat.clone(), pred_ac, goal_exists, exists_ac, elim_outer],
    );

    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, elim_ac);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(hbd_id, BinderInfo::Default, hbd_ty, e);
    let e = b.mk_lam(hac_id, BinderInfo::Default, hac_ty, e);
    let e = b.mk_lam(fd_id, BinderInfo::Default, c.causeq.clone(), e);
    let e = b.mk_lam(fc_id, BinderInfo::Default, c.causeq.clone(), e);
    let e = b.mk_lam(fb_id, BinderInfo::Default, c.causeq.clone(), e);
    let e = b.mk_lam(fa_id, BinderInfo::Default, c.causeq.clone(), e);
    b.finish(e)
}

/// At a fixed index `m`, combine `base_ac : vfa < vfb + ε/2` and
/// `base_bd : vfc < vfd + ε/2` into the combined-sequence bound
/// `vseq(add fa fc) m < vseq(add fb fd) m + ε`.
#[allow(clippy::too_many_arguments)]
fn build_combined(
    c: &LeAddConsts,
    parent: &EnvDeclBuilder,
    fa: &Expr,
    fb: &Expr,
    fc: &Expr,
    fd: &Expr,
    m: &Expr,
    eps: &Expr,
    half: &Expr,
    base_ac: &Expr,
    base_bd: &Expr,
) -> Expr {
    let vfa = c.vseq(fa, m);
    let vfb = c.vseq(fb, m);
    let vfc = c.vseq(fc, m);
    let vfd = c.vseq(fd, m);

    let vfb_half = c.add(vfb.clone(), half.clone());
    let vfd_half = c.add(vfd.clone(), half.clone());

    // step1 : (vfa+vfc) < ((vfb+ε/2)+(vfd+ε/2))  via add_lt_add.
    let step1 = c.add_lt_add(
        vfa.clone(),
        vfb_half.clone(),
        vfc.clone(),
        vfd_half.clone(),
        base_ac.clone(),
        base_bd.clone(),
    );

    // reshuffle : (vfb+ε/2)+(vfd+ε/2) = (vfb+vfd)+ε.
    let reshuffle = build_reshuffle(c, parent, &vfb, &vfd, half, eps);
    let lhs_sum = c.add(vfa.clone(), vfc.clone());
    let mid = c.add(vfb_half.clone(), vfd_half.clone());
    let vfbd = c.add(vfb.clone(), vfd.clone());
    let vfbd_eps = c.add(vfbd.clone(), eps.clone());
    // step2 : (vfa+vfc) < (vfb+vfd)+ε.
    let motive_resh = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.lt(lhs_sum.clone(), t);
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let step2 = c.subst(motive_resh, mid, vfbd_eps.clone(), reshuffle, step1);

    // Transport endpoints (vfa+vfc) → val(seq(add fa fc) m) and
    // (vfb+vfd) → val(seq(add fb fd) m) via Eq.symm (NNRat.val_add …).
    // val(seq(add fa fc) m) ≡ val(NNRat.add (seq fa m)(seq fc m)) (defeq), and
    // val_add (seq fa m)(seq fc m) : that = vfa+vfc.
    let seq_fa = c.seq_at(fa, m);
    let seq_fb = c.seq_at(fb, m);
    let seq_fc = c.seq_at(fc, m);
    let seq_fd = c.seq_at(fd, m);
    let val_add_l = c.val_add(seq_fa.clone(), seq_fc.clone()); // val(add..) = vfa+vfc
    let val_add_r = c.val_add(seq_fb.clone(), seq_fd.clone()); // val(add..) = vfb+vfd
    let vl_form = Expr::app(
        c.nnrat_val.clone(),
        Expr::apps(c.nnrat_add.clone(), [seq_fa, seq_fc]),
    );
    let vr_form = Expr::app(
        c.nnrat_val.clone(),
        Expr::apps(c.nnrat_add.clone(), [seq_fb, seq_fd]),
    );

    // step3 : (vfa+vfc) < vr_form + ε  (rewrite RHS summand vfbd → vr_form).
    let motive_rhs = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.lt(lhs_sum.clone(), c.add(t, eps.clone()));
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let step3 = c.subst(
        motive_rhs,
        vfbd.clone(),
        vr_form.clone(),
        c.eq_symm(vr_form.clone(), vfbd.clone(), val_add_r),
        step2,
    );

    // step4 : vl_form < vr_form + ε (rewrite LHS vfa+vfc → vl_form).
    let motive_lhs = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.lt(t, c.add(vr_form.clone(), eps.clone()));
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    c.subst(
        motive_lhs,
        lhs_sum.clone(),
        vl_form.clone(),
        c.eq_symm(vl_form, lhs_sum, val_add_l),
        step3,
    )
}

/// `(a+h)+(b+h) = (a+b)+(h+h) = (a+b)+ε`, where `h = ε/2`.
///
/// Chain:
///   `(a+h)+(b+h) = a+(h+(b+h))`            add_assoc a h (b+h)
///              `= a+((h+b)+h)`             congrArg (a+·) (symm (add_assoc h b h))
///              `= a+((b+h)+h)`             congrArg (a+·) (congrArg (·+h)(add_comm h b))
///              `= a+(b+(h+h))`             congrArg (a+·) (add_assoc b h h)
///              `= a+(b+ε)`                 congrArg (a+·) (congrArg (b+·) add_halves)
///              `= (a+b)+ε`                 symm (add_assoc a b ε)
fn build_reshuffle(
    c: &LeAddConsts,
    parent: &EnvDeclBuilder,
    a: &Expr,
    b: &Expr,
    h: &Expr,
    eps: &Expr,
) -> Expr {
    let rat = c.rat.clone();
    // helper: fun t => a + t
    let add_a_fn = {
        let mut fb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = fb.fresh_local(rat.clone());
        let body = c.add(a.clone(), t);
        fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, rat.clone(), body))
    };
    // helper: fun t => b + t
    let add_b_fn = {
        let mut fb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = fb.fresh_local(rat.clone());
        let body = c.add(b.clone(), t);
        fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, rat.clone(), body))
    };
    // helper: fun t => t + h
    let add_h_right_fn = {
        let mut fb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = fb.fresh_local(rat.clone());
        let body = c.add(t, h.clone());
        fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, rat.clone(), body))
    };

    let a_h = c.add(a.clone(), h.clone());
    let b_h = c.add(b.clone(), h.clone());
    let h_b = c.add(h.clone(), b.clone());
    let h_h = c.add(h.clone(), h.clone());
    let a_b = c.add(a.clone(), b.clone());

    // l0 := (a+h)+(b+h).
    let l0 = c.add(a_h.clone(), b_h.clone());
    // s1 : l0 = a+(h+(b+h))  via add_assoc a h (b+h).
    let t1 = c.add(a.clone(), c.add(h.clone(), b_h.clone()));
    let s1 = c.add_assoc(a.clone(), h.clone(), b_h.clone());

    // inner1 : h+(b+h) = (h+b)+h  via symm (add_assoc h b h).
    let hb_h = c.add(h_b.clone(), h.clone());
    let inner1 = c.eq_symm(
        c.add(c.add(h.clone(), b.clone()), h.clone()),
        c.add(h.clone(), c.add(b.clone(), h.clone())),
        c.add_assoc(h.clone(), b.clone(), h.clone()),
    );
    // s2 : a+(h+(b+h)) = a+((h+b)+h)  via congrArg (a+·) inner1.
    let t2 = c.add(a.clone(), hb_h.clone());
    let s2 = c.congr_arg(
        c.add(h.clone(), b_h.clone()),
        hb_h.clone(),
        add_a_fn.clone(),
        inner1,
    );

    // inner2a : h+b = b+h  via add_comm h b.
    let comm_hb = c.add_comm(h.clone(), b.clone());
    // inner2 : (h+b)+h = (b+h)+h  via congrArg (·+h) (add_comm h b).
    let bh_h = c.add(b_h.clone(), h.clone());
    let inner2 = c.congr_arg(h_b.clone(), b_h.clone(), add_h_right_fn, comm_hb);
    // s3 : a+((h+b)+h) = a+((b+h)+h)  via congrArg (a+·) inner2.
    let t3 = c.add(a.clone(), bh_h.clone());
    let s3 = c.congr_arg(hb_h.clone(), bh_h.clone(), add_a_fn.clone(), inner2);

    // inner3 : (b+h)+h = b+(h+h)  via add_assoc b h h.
    let b_hh = c.add(b.clone(), h_h.clone());
    let inner3 = c.add_assoc(b.clone(), h.clone(), h.clone());
    // s4 : a+((b+h)+h) = a+(b+(h+h))  via congrArg (a+·) inner3.
    let t4 = c.add(a.clone(), b_hh.clone());
    let s4 = c.congr_arg(bh_h.clone(), b_hh.clone(), add_a_fn.clone(), inner3);

    // inner4 : b+(h+h) = b+ε  via congrArg (b+·) add_halves.
    let b_eps = c.add(b.clone(), eps.clone());
    let inner4 = c.congr_arg(
        h_h.clone(),
        eps.clone(),
        add_b_fn,
        c.add_halves(eps.clone()),
    );
    // s5 : a+(b+(h+h)) = a+(b+ε)  via congrArg (a+·) inner4.
    let t5 = c.add(a.clone(), b_eps.clone());
    let s5 = c.congr_arg(b_hh.clone(), b_eps.clone(), add_a_fn, inner4);

    // s6 : a+(b+ε) = (a+b)+ε  via symm (add_assoc a b ε).
    let t6 = c.add(a_b.clone(), eps.clone());
    let s6 = c.eq_symm(
        c.add(c.add(a.clone(), b.clone()), eps.clone()),
        c.add(a.clone(), c.add(b.clone(), eps.clone())),
        c.add_assoc(a.clone(), b.clone(), eps.clone()),
    );

    // chain s1..s6.
    let ch1 = c.eq_trans(l0.clone(), t1.clone(), t2.clone(), s1, s2);
    let ch2 = c.eq_trans(l0.clone(), t2.clone(), t3.clone(), ch1, s3);
    let ch3 = c.eq_trans(l0.clone(), t3.clone(), t4.clone(), ch2, s4);
    let ch4 = c.eq_trans(l0.clone(), t4.clone(), t5.clone(), ch3, s5);
    c.eq_trans(l0, t5, t6, ch4, s6)
}

/// `NNReal.add_le_add` via four nested `Quot.ind`s, each motive an
/// implication chain (mirroring `NNReal.le.trans`'s nested-ind structure).
fn build_nnreal_add_le_add(c: &LeAddConsts, nnreal: &Expr) -> Expr {
    let causeq_add_le_add = Expr::const_(Name::from_string("NNReal.CauSeq.add_le_add"), vec![]);
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(nnreal.clone());
    let (bv_id, bv) = b.fresh_local(nnreal.clone());
    let (cv_id, cv) = b.fresh_local(nnreal.clone());
    let (dv_id, dv) = b.fresh_local(nnreal.clone());
    let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
    let hab_ty = Expr::apps(nnle.clone(), [a.clone(), bv.clone()]);
    let (hab_id, hab) = b.fresh_local(hab_ty.clone());
    let hcd_ty = Expr::apps(nnle.clone(), [cv.clone(), dv.clone()]);
    let (hcd_id, hcd) = b.fresh_local(hcd_ty.clone());

    let body = descend_a(
        c,
        &b,
        nnreal,
        &a,
        &bv,
        &cv,
        &dv,
        &hab,
        &hcd,
        &causeq_add_le_add,
    );

    let e = b.mk_lam(hcd_id, BinderInfo::Default, hcd_ty, body);
    let e = b.mk_lam(hab_id, BinderInfo::Default, hab_ty, e);
    let e = b.mk_lam(dv_id, BinderInfo::Default, nnreal.clone(), e);
    let e = b.mk_lam(cv_id, BinderInfo::Default, nnreal.clone(), e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, nnreal.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, nnreal.clone(), e);
    b.finish(e)
}

/// `nnle (add x cv)(add bv dv)` over `x` with motive
///   `P x := nnle x bv → nnle cv dv → nnle (add x cv)(add bv dv)`.
#[allow(clippy::too_many_arguments)]
fn descend_a(
    c: &LeAddConsts,
    parent: &EnvDeclBuilder,
    nnreal: &Expr,
    a: &Expr,
    bv: &Expr,
    cv: &Expr,
    dv: &Expr,
    hab: &Expr,
    hcd: &Expr,
    core: &Expr,
) -> Expr {
    let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
    let nnadd = Expr::const_(Name::from_string("NNReal.add"), vec![]);
    let add = |x: Expr, y: Expr| Expr::apps(nnadd.clone(), [x, y]);

    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = mb.fresh_local(nnreal.clone());
        let h1 = Expr::apps(nnle.clone(), [x.clone(), bv.clone()]);
        let h2 = Expr::apps(nnle.clone(), [cv.clone(), dv.clone()]);
        let concl = Expr::apps(
            nnle.clone(),
            [add(x.clone(), cv.clone()), add(bv.clone(), dv.clone())],
        );
        let imp2 = Expr::pi(BinderInfo::Default, h2, concl);
        let imp1 = Expr::pi(BinderInfo::Default, h1, imp2);
        mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, nnreal.clone(), imp1))
    };
    let minor = {
        let mut mf = EnvDeclBuilder::child_of(parent);
        let (fa_id, fa) = mf.fresh_local(c.causeq.clone());
        let mka = c.quot_mk(fa.clone());
        let body = descend_b(c, &mf, nnreal, &mka, &fa, bv, cv, dv, core);
        mf.finish_child(mf.mk_lam(fa_id, BinderInfo::Default, c.causeq.clone(), body))
    };
    let ind = Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive,
            minor,
            a.clone(),
        ],
    );
    Expr::apps(ind, [hab.clone(), hcd.clone()])
}

/// Descend on `bv`: motive `Q y := nnle (mk fa) y → nnle cv dv →
///   nnle (add (mk fa) cv)(add y dv)`. Leaf supplies rep `fb`.
#[allow(clippy::too_many_arguments)]
fn descend_b(
    c: &LeAddConsts,
    parent: &EnvDeclBuilder,
    nnreal: &Expr,
    mka: &Expr,
    fa: &Expr,
    bv: &Expr,
    cv: &Expr,
    dv: &Expr,
    core: &Expr,
) -> Expr {
    let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
    let nnadd = Expr::const_(Name::from_string("NNReal.add"), vec![]);
    let add = |x: Expr, y: Expr| Expr::apps(nnadd.clone(), [x, y]);

    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (y_id, y) = mb.fresh_local(nnreal.clone());
        let h1 = Expr::apps(nnle.clone(), [mka.clone(), y.clone()]);
        let h2 = Expr::apps(nnle.clone(), [cv.clone(), dv.clone()]);
        let concl = Expr::apps(
            nnle.clone(),
            [add(mka.clone(), cv.clone()), add(y.clone(), dv.clone())],
        );
        let imp2 = Expr::pi(BinderInfo::Default, h2, concl);
        let imp1 = Expr::pi(BinderInfo::Default, h1, imp2);
        mb.finish_child(mb.mk_lam(y_id, BinderInfo::Default, nnreal.clone(), imp1))
    };
    let minor = {
        let mut mf = EnvDeclBuilder::child_of(parent);
        let (fb_id, fb) = mf.fresh_local(c.causeq.clone());
        let mkb = c.quot_mk(fb.clone());
        let body = descend_c(c, &mf, nnreal, mka, fa, &mkb, &fb, cv, dv, core);
        mf.finish_child(mf.mk_lam(fb_id, BinderInfo::Default, c.causeq.clone(), body))
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

/// Descend on `cv`: motive `R z := nnle (mk fa)(mk fb) → nnle z dv →
///   nnle (add (mk fa) z)(add (mk fb) dv)`. Leaf supplies rep `fc`.
#[allow(clippy::too_many_arguments)]
fn descend_c(
    c: &LeAddConsts,
    parent: &EnvDeclBuilder,
    nnreal: &Expr,
    mka: &Expr,
    fa: &Expr,
    mkb: &Expr,
    fb: &Expr,
    cv: &Expr,
    dv: &Expr,
    core: &Expr,
) -> Expr {
    let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
    let nnadd = Expr::const_(Name::from_string("NNReal.add"), vec![]);
    let add = |x: Expr, y: Expr| Expr::apps(nnadd.clone(), [x, y]);

    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = mb.fresh_local(nnreal.clone());
        let h1 = Expr::apps(nnle.clone(), [mka.clone(), mkb.clone()]);
        let h2 = Expr::apps(nnle.clone(), [z.clone(), dv.clone()]);
        let concl = Expr::apps(
            nnle.clone(),
            [add(mka.clone(), z.clone()), add(mkb.clone(), dv.clone())],
        );
        let imp2 = Expr::pi(BinderInfo::Default, h2, concl);
        let imp1 = Expr::pi(BinderInfo::Default, h1, imp2);
        mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, nnreal.clone(), imp1))
    };
    let minor = {
        let mut mf = EnvDeclBuilder::child_of(parent);
        let (fc_id, fc) = mf.fresh_local(c.causeq.clone());
        let mkc = c.quot_mk(fc.clone());
        let body = descend_d(c, &mf, nnreal, mka, fa, mkb, fb, &mkc, &fc, dv, core);
        mf.finish_child(mf.mk_lam(fc_id, BinderInfo::Default, c.causeq.clone(), body))
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

/// Descend on `dv`: motive `S w := nnle (mk fa)(mk fb) → nnle (mk fc) w →
///   nnle (add (mk fa)(mk fc))(add (mk fb) w)`. Leaf supplies rep `fd`; the two
/// hyps reduce to `CauSeq.le fa fb`,`CauSeq.le fc fd` and the goal (via
/// `NNReal.add (mk ·)(mk ·) ≡ mk (CauSeq.add · ·)` defeq) to
/// `CauSeq.le (add fa fc)(add fb fd)`, closed by `core fa fb fc fd`.
#[allow(clippy::too_many_arguments)]
fn descend_d(
    c: &LeAddConsts,
    parent: &EnvDeclBuilder,
    nnreal: &Expr,
    mka: &Expr,
    fa: &Expr,
    mkb: &Expr,
    fb: &Expr,
    mkc: &Expr,
    fc: &Expr,
    dv: &Expr,
    core: &Expr,
) -> Expr {
    let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
    let nnadd = Expr::const_(Name::from_string("NNReal.add"), vec![]);
    let add = |x: Expr, y: Expr| Expr::apps(nnadd.clone(), [x, y]);

    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = mb.fresh_local(nnreal.clone());
        let h1 = Expr::apps(nnle.clone(), [mka.clone(), mkb.clone()]);
        let h2 = Expr::apps(nnle.clone(), [mkc.clone(), w.clone()]);
        let concl = Expr::apps(
            nnle.clone(),
            [add(mka.clone(), mkc.clone()), add(mkb.clone(), w.clone())],
        );
        let imp2 = Expr::pi(BinderInfo::Default, h2, concl);
        let imp1 = Expr::pi(BinderInfo::Default, h1, imp2);
        mb.finish_child(mb.mk_lam(w_id, BinderInfo::Default, nnreal.clone(), imp1))
    };
    let minor = {
        let mut mf = EnvDeclBuilder::child_of(parent);
        let (fd_id, fd) = mf.fresh_local(c.causeq.clone());
        // hyps reduce: nnle (mk fa)(mk fb) ≡ CauSeq.le fa fb, etc.
        let h1_ty = c.causeq_le(fa.clone(), fb.clone());
        let (h1_id, h1) = mf.fresh_local(h1_ty.clone());
        let h2_ty = c.causeq_le(fc.clone(), fd.clone());
        let (h2_id, h2) = mf.fresh_local(h2_ty.clone());
        // core fa fb fc fd h1 h2 : CauSeq.le (add fa fc)(add fb fd)
        //   ≡ nnle (add (mk fa)(mk fc))(add (mk fb)(mk fd)).
        let body = Expr::apps(
            core.clone(),
            [fa.clone(), fb.clone(), fc.clone(), fd.clone(), h1, h2],
        );
        let e = mf.mk_lam(h2_id, BinderInfo::Default, h2_ty, body);
        let e = mf.mk_lam(h1_id, BinderInfo::Default, h1_ty, e);
        let e = mf.mk_lam(fd_id, BinderInfo::Default, c.causeq.clone(), e);
        mf.finish_child(e)
    };
    Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive,
            minor,
            dv.clone(),
        ],
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &["NNReal.CauSeq.add_le_add", "NNReal.add_le_add"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_le_add()
            .expect("init_algebra_nnreal_le_add");
        env.init_algebra_nnreal_le_add().expect("idempotent");
        env
    }

    #[test]
    fn test_nnreal_add_le_add_kernel_check() {
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
    fn test_nnreal_add_le_add_constructive_empty_closure() {
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
