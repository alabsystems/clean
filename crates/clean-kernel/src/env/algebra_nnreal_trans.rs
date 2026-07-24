// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — `NNReal.CauSeq.Equiv.trans` (the setoid gate).
//!
//! # Why this module exists
//!
//! `NNReal.CauSeq.Equiv` (`algebra_nnreal_cauchy.rs`) already has `refl` and
//! `symm`; `trans` is the last property that makes it a genuine setoid, and
//! everything below it (`NNReal.add`/`le`/`sqrt`) depends on `Equiv` being an
//! equivalence (plan `designs/2026-06-18-kkl-real-sqrt-layer-plan.md`, Stage B).
//!
//! `trans` is the ε/2-split: combining `vf < vg + ε` and `vg < vh + ε` with a
//! shared `ε` only lands at `vf < vh + 2ε`; you instantiate BOTH Cauchy
//! hypotheses at `ε/2` (positivity from `Rat.half_pos`), take `N := Nat.max N1
//! N2`, and recombine `(vh + ε/2) + ε/2 = vh + (ε/2 + ε/2) = vh + ε` via
//! `Rat.add_assoc` + `Rat.add_halves`.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `NNReal.CauSeq.Equiv.trans :
//!       ∀ f g h, Equiv f g → Equiv g h → Equiv f h`
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for `Equiv.trans`. The `Equiv`
/// body uses `NNRat.val (NNReal.CauSeq.seq · n)` distances bounded by `Rat.lt`.
pub(crate) struct TransConsts {
    nat: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_two: Expr,
    causeq: Expr,
    causeq_seq: Expr,
    causeq_equiv: Expr,
    nnrat_val: Expr,
    rat_add: Expr,
    rat_div: Expr,
    rat_lt: Expr,
    nat_le: Expr,
    // Lemmas.
    rat_half_pos: Expr,
    rat_add_lt_add_right: Expr,
    rat_lt_trans: Expr,
    rat_add_assoc: Expr,
    rat_add_halves: Expr,
    nat_max: Expr,
    nat_le_max_left: Expr,
    nat_le_max_right: Expr,
    nat_le_trans: Expr,
    // Logic.
    and_c: Expr,
    and_intro: Expr,
    and_left: Expr,
    and_right: Expr,
    exists_c: Expr,
    exists_intro: Expr,
    exists_elim: Expr,
    // Eq.{1} over Rat.
    eq_rat: Expr,
    eq_trans: Expr,
    eq_subst: Expr,
    congr_arg: Expr,
}

impl TransConsts {
    pub(crate) fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_two: k("Rat.two"),
            causeq: k("NNReal.CauSeq"),
            causeq_seq: k("NNReal.CauSeq.seq"),
            causeq_equiv: k("NNReal.CauSeq.Equiv"),
            nnrat_val: k("NNRat.val"),
            rat_add: k("Rat.add"),
            rat_div: k("Rat.div"),
            rat_lt: k("Rat.lt"),
            nat_le: k("Nat.le"),
            rat_half_pos: k("Rat.half_pos"),
            rat_add_lt_add_right: k("Rat.add_lt_add_right"),
            rat_lt_trans: k("Rat.lt_trans"),
            rat_add_assoc: k("Rat.add_assoc"),
            rat_add_halves: k("Rat.add_halves"),
            nat_max: k("Nat.max"),
            nat_le_max_left: k("Nat.le_max_left"),
            nat_le_max_right: k("Nat.le_max_right"),
            nat_le_trans: k("Nat.le_trans"),
            and_c: k("And"),
            and_intro: k("And.intro"),
            and_left: k("And.left"),
            and_right: k("And.right"),
            exists_c: Expr::const_(Name::from_string("Exists"), vec![lvl1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![lvl1.clone()]),
            exists_elim: Expr::const_(Name::from_string("Exists.elim"), vec![lvl1.clone()]),
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![lvl1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![lvl1.clone(), lvl1]),
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
    fn and_ty(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.and_c.clone(), [p, q])
    }
    /// `NNRat.val (NNReal.CauSeq.seq x n) : Rat`.
    fn vseq(&self, x: &Expr, n: &Expr) -> Expr {
        let seq = Expr::app(self.causeq_seq.clone(), x.clone());
        let at = Expr::app(seq, n.clone());
        Expr::app(self.nnrat_val.clone(), at)
    }
    /// `NNReal.CauSeq.Equiv a b : Prop`.
    fn equiv(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_equiv.clone(), [a, b])
    }
    /// The two-sided bound `And (Rat.lt x (y+ε)) (Rat.lt y (x+ε))`.
    fn bound_pair(&self, x: Expr, y: Expr, eps: Expr) -> Expr {
        let left = self.lt(x.clone(), self.add(y.clone(), eps.clone()));
        let right = self.lt(y, self.add(x, eps));
        self.and_ty(left, right)
    }

    /// The `∀ N`-predicate body for a fixed pair `(a,b)` at tolerance `eps`:
    ///   `fun N => ∀ n, Nat.le N n → bound_pair (vseq a n)(vseq b n) eps`.
    fn pred_n(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr, eps: &Expr) -> Expr {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (n_id, n_cap) = bn.fresh_local(self.nat.clone());
        let inner = {
            let mut bi = EnvDeclBuilder::child_of(&bn);
            let (m_id, m) = bi.fresh_local(self.nat.clone());
            let hle = self.nat_le(n_cap.clone(), m.clone());
            let (hle_id, _hle) = bi.fresh_local(hle.clone());
            let concl = self.bound_pair(self.vseq(a, &m), self.vseq(b, &m), eps.clone());
            let e = bi.mk_pi(hle_id, BinderInfo::Default, hle, concl);
            let e = bi.mk_pi(m_id, BinderInfo::Default, self.nat.clone(), e);
            bi.finish_child(e)
        };
        let lam = bn.mk_lam(n_id, BinderInfo::Default, self.nat.clone(), inner);
        bn.finish_child(lam)
    }

    /// `∃ N, pred_n a b eps N : Prop`.
    fn exists_pred(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr, eps: &Expr) -> Expr {
        Expr::apps(
            self.exists_c.clone(),
            [self.nat.clone(), self.pred_n(parent, a, b, eps)],
        )
    }

    // ── proof constructors ──────────────────────────────────────────────────

    fn and_left(&self, p: Expr, q: Expr, h: Expr) -> Expr {
        Expr::apps(self.and_left.clone(), [p, q, h])
    }
    fn and_right(&self, p: Expr, q: Expr, h: Expr) -> Expr {
        Expr::apps(self.and_right.clone(), [p, q, h])
    }
    fn and_intro(&self, p: Expr, q: Expr, hp: Expr, hq: Expr) -> Expr {
        Expr::apps(self.and_intro.clone(), [p, q, hp, hq])
    }
    /// `Rat.add_lt_add_right a b c h : (a+c) < (b+c)`.
    fn add_lt_add_right(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_add_lt_add_right.clone(), [a, b, cc, h])
    }
    /// `Rat.lt_trans a b c hab hbc : a < c`.
    fn lt_trans(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(self.rat_lt_trans.clone(), [a, b, cc, hab, hbc])
    }
    /// `Rat.add_assoc a b c : Eq Rat ((a+b)+c) (a+(b+c))`.
    fn add_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_add_assoc.clone(), [a, b, cc])
    }
    /// `Rat.add_halves eps : Eq Rat ((eps/2)+(eps/2)) eps`.
    fn add_halves(&self, eps: Expr) -> Expr {
        Expr::app(self.rat_add_halves.clone(), eps)
    }
    /// `@Eq.trans Rat a b c hab hbc`.
    fn eq_trans(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.rat.clone(), a, b, cc, hab, hbc],
        )
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

    /// `eq_recombine vx eps : Eq Rat ((vx + eps/2) + eps/2) (vx + eps)`.
    /// `(vx+ε/2)+ε/2 = vx+(ε/2+ε/2)` (add_assoc) `= vx+ε` (congrArg add_halves).
    fn eq_recombine(&self, parent: &EnvDeclBuilder, vx: &Expr, eps: &Expr) -> Expr {
        let half = self.half(eps.clone());
        let assoc = self.add_assoc(vx.clone(), half.clone(), half.clone());
        let half_pair = self.add(half.clone(), half.clone());
        // congrArg (fun t => vx + t) (add_halves eps) : (vx+(ε/2+ε/2)) = (vx+ε).
        let add_vx_fn = {
            let mut fb = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = fb.fresh_local(self.rat.clone());
            let body = self.add(vx.clone(), t);
            fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
        };
        let congr = self.congr_arg(
            half_pair.clone(),
            eps.clone(),
            add_vx_fn,
            self.add_halves(eps.clone()),
        );
        // chain: ((vx+ε/2)+ε/2) → (vx+(ε/2+ε/2)) → (vx+ε).
        let lhs = self.add(self.add(vx.clone(), half.clone()), half);
        let mid = self.add(vx.clone(), half_pair);
        let rhs = self.add(vx.clone(), eps.clone());
        self.eq_trans(lhs, mid, rhs, assoc, congr)
    }
}

impl Environment {
    /// Register `NNReal.CauSeq.Equiv.trans`. Idempotent. Pulls in the Cauchy
    /// carrier (`refl`/`symm`/`Equiv`), `Rat.half_pos`, and the Rat/Nat order
    /// lemmas the ε/2-recombination needs.
    pub fn init_algebra_nnreal_trans(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_cauchy()?; // CauSeq, Equiv, refl, symm
        self.init_algebra_rat_half_pos()?; // Rat.half_pos (+ Rat.add_halves, Rat.two)
        self.register_rat_add_lt_add_right()?; // Rat.add_lt_add_right
        self.register_rat_lt_trans()?; // Rat.lt_trans
        self.register_nat_minmax_proofs()?; // Nat.max, Nat.le_max_left/right
        self.register_nat_le_trans_proof()?; // Nat.le_trans
                                             // Rat.add_assoc is registered by init_rat_field_inst (via half_pos chain);
                                             // ensure idempotently.
        self.init_rat_field_inst()?;

        let c = TransConsts::new();
        self.register_nnreal_equiv_trans(&c)
    }

    fn register_nnreal_equiv_trans(&mut self, c: &TransConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.CauSeq.Equiv.trans");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.causeq.clone());
            let (g_id, g) = b.fresh_local(c.causeq.clone());
            let (h_id, h) = b.fresh_local(c.causeq.clone());
            let efg = c.equiv(f.clone(), g.clone());
            let (hfg_id, _hfg) = b.fresh_local(efg.clone());
            let egh = c.equiv(g.clone(), h.clone());
            let (hgh_id, _hgh) = b.fresh_local(egh.clone());
            let concl = c.equiv(f.clone(), h.clone());
            let e = b.mk_pi(hgh_id, BinderInfo::Default, egh, concl);
            let e = b.mk_pi(hfg_id, BinderInfo::Default, efg, e);
            let e = b.mk_pi(h_id, BinderInfo::Default, c.causeq.clone(), e);
            let e = b.mk_pi(g_id, BinderInfo::Default, c.causeq.clone(), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.causeq.clone(), e);
            b.finish(e)
        };

        let value = build_trans_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Build the proof term for `NNReal.CauSeq.Equiv.trans`. Kept as a free function
/// to keep the registration method short.
fn build_trans_proof(c: &TransConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (f_id, f) = b.fresh_local(c.causeq.clone());
    let (g_id, g) = b.fresh_local(c.causeq.clone());
    let (h_id, h) = b.fresh_local(c.causeq.clone());
    let efg_ty = c.equiv(f.clone(), g.clone());
    let (hfg_id, hfg) = b.fresh_local(efg_ty.clone());
    let egh_ty = c.equiv(g.clone(), h.clone());
    let (hgh_id, hgh) = b.fresh_local(egh_ty.clone());

    // Goal: Equiv f h = ∀ ε, 0<ε → ∃ N, ∀ n, N≤n → bound_pair (vf)(vh) ε.
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.lt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

    let half = c.half(eps.clone());
    // heps2 : 0 < ε/2.
    let heps2 = Expr::apps(c.rat_half_pos.clone(), [eps.clone(), hpos.clone()]);

    // hfg (ε/2) heps2 : ∃ N1, ∀ n, N1≤n → bound_pair (vf)(vg) (ε/2).
    let exists_fg = Expr::apps(hfg.clone(), [half.clone(), heps2.clone()]);
    // hgh (ε/2) heps2 : ∃ N2, ∀ n, N2≤n → bound_pair (vg)(vh) (ε/2).
    let exists_gh = Expr::apps(hgh.clone(), [half.clone(), heps2]);

    // Target of the double Exists.elim:  ∃ N, ∀ n, N≤n → bound_pair (vf)(vh) ε.
    let goal_exists = c.exists_pred(&b, &f, &h, &eps);

    let pred_fg = c.pred_n(&b, &f, &g, &half);
    let pred_gh = c.pred_n(&b, &g, &h, &half);

    // Inner elim function: given N1, hN1, produce ∃ N, … from exists_gh.
    let elim_outer = {
        let mut bo = EnvDeclBuilder::child_of(&b);
        let (n1_id, n1) = bo.fresh_local(c.nat.clone());
        // hN1 : ∀ n, N1≤n → bound_pair (vf)(vg) (ε/2)  (= pred_fg N1).
        let hn1_ty = pred_fg_at(c, &bo, &f, &g, &half, &n1);
        let (hn1_id, hn1) = bo.fresh_local(hn1_ty.clone());

        // Inner Exists.elim over exists_gh.
        let elim_inner = {
            let mut bi = EnvDeclBuilder::child_of(&bo);
            let (n2_id, n2) = bi.fresh_local(c.nat.clone());
            let hn2_ty = pred_fg_at(c, &bi, &g, &h, &half, &n2);
            let (hn2_id, hn2) = bi.fresh_local(hn2_ty.clone());

            // N := Nat.max N1 N2.
            let nmax = Expr::apps(c.nat_max.clone(), [n1.clone(), n2.clone()]);

            // witness : pred_n f h ε N  = ∀ n, N≤n → bound_pair (vf)(vh) ε.
            let witness = {
                let mut bw = EnvDeclBuilder::child_of(&bi);
                let (m_id, m) = bw.fresh_local(c.nat.clone());
                let hle_ty = c.nat_le(nmax.clone(), m.clone());
                let (hle_id, hle) = bw.fresh_local(hle_ty.clone());

                // N1≤n := le_trans N1 (max) n (le_max_left N1 N2) hle.
                let le_max_l = Expr::apps(c.nat_le_max_left.clone(), [n1.clone(), n2.clone()]);
                let le_max_r = Expr::apps(c.nat_le_max_right.clone(), [n1.clone(), n2.clone()]);
                let n1_le_m =
                    c.nat_le_trans(n1.clone(), nmax.clone(), m.clone(), le_max_l, hle.clone());
                let n2_le_m = c.nat_le_trans(n2.clone(), nmax.clone(), m.clone(), le_max_r, hle);

                // hN1 m n1_le_m : bound_pair (vf m)(vg m) (ε/2).
                let base_fg = Expr::apps(hn1.clone(), [m.clone(), n1_le_m]);
                // hN2 m n2_le_m : bound_pair (vg m)(vh m) (ε/2).
                let base_gh = Expr::apps(hn2.clone(), [m.clone(), n2_le_m]);

                let vf = c.vseq(&f, &m);
                let vg = c.vseq(&g, &m);
                let vh = c.vseq(&h, &m);

                // conjunct types of base_fg:  l_fg := vf < vg+ε/2 ; r_fg := vg < vf+ε/2.
                let l_fg = c.lt(vf.clone(), c.add(vg.clone(), half.clone()));
                let r_fg = c.lt(vg.clone(), c.add(vf.clone(), half.clone()));
                // conjunct types of base_gh:  l_gh := vg < vh+ε/2 ; r_gh := vh < vg+ε/2.
                let l_gh = c.lt(vg.clone(), c.add(vh.clone(), half.clone()));
                let r_gh = c.lt(vh.clone(), c.add(vg.clone(), half.clone()));

                let a_fg = c.and_left(l_fg.clone(), r_fg.clone(), base_fg.clone()); // vf<vg+ε/2
                let b_fg = c.and_right(l_fg, r_fg, base_fg); // vg<vf+ε/2
                let a_gh = c.and_left(l_gh.clone(), r_gh.clone(), base_gh.clone()); // vg<vh+ε/2
                let b_gh = c.and_right(l_gh, r_gh, base_gh); // vh<vg+ε/2

                // ── forward: vf < vh + ε ───────────────────────────────────
                // step1 : (vg+ε/2) < ((vh+ε/2)+ε/2)  := add_lt_add_right vg (vh+ε/2) (ε/2) a_gh.
                let vh_half = c.add(vh.clone(), half.clone());
                let step1 = c.add_lt_add_right(vg.clone(), vh_half.clone(), half.clone(), a_gh);
                // step2 : vf < ((vh+ε/2)+ε/2)  := lt_trans vf (vg+ε/2) ((vh+ε/2)+ε/2) a_fg step1.
                let vg_half = c.add(vg.clone(), half.clone());
                let vh_hh = c.add(vh_half.clone(), half.clone());
                let step2 = c.lt_trans(vf.clone(), vg_half, vh_hh.clone(), a_fg, step1);
                // recombine : ((vh+ε/2)+ε/2) = (vh+ε) ; transport step2: motive t := vf < t.
                let rec_h = c.eq_recombine(&bw, &vh, &eps);
                let vh_eps = c.add(vh.clone(), eps.clone());
                let motive_fwd = {
                    let mut mb = EnvDeclBuilder::child_of(&bw);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.lt(vf.clone(), t);
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let fwd = c.subst(motive_fwd, vh_hh, vh_eps.clone(), rec_h, step2);

                // ── reverse: vh < vf + ε ───────────────────────────────────
                // step1' : (vg+ε/2) < ((vf+ε/2)+ε/2) := add_lt_add_right vg (vf+ε/2)(ε/2) b_fg.
                let vf_half = c.add(vf.clone(), half.clone());
                let step1r = c.add_lt_add_right(vg.clone(), vf_half.clone(), half.clone(), b_fg);
                // step2' : vh < ((vf+ε/2)+ε/2) := lt_trans vh (vg+ε/2) ((vf+ε/2)+ε/2) b_gh step1'.
                let vg_half2 = c.add(vg.clone(), half.clone());
                let vf_hh = c.add(vf_half.clone(), half.clone());
                let step2r = c.lt_trans(vh.clone(), vg_half2, vf_hh.clone(), b_gh, step1r);
                let rec_f = c.eq_recombine(&bw, &vf, &eps);
                let vf_eps = c.add(vf.clone(), eps.clone());
                let motive_rev = {
                    let mut mb = EnvDeclBuilder::child_of(&bw);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.lt(vh.clone(), t);
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let rev = c.subst(motive_rev, vf_hh, vf_eps.clone(), rec_f, step2r);

                // And.intro (vf<vh+ε)(vh<vf+ε) fwd rev : bound_pair (vf)(vh) ε.
                let l_final = c.lt(vf.clone(), vh_eps);
                let r_final = c.lt(vh.clone(), vf_eps);
                let proof = c.and_intro(l_final, r_final, fwd, rev);

                let e = bw.mk_lam(hle_id, BinderInfo::Default, hle_ty, proof);
                let e = bw.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
                bw.finish_child(e)
            };

            // Exists.intro Nat (pred_n f h ε) nmax witness : ∃ N, …
            let intro = Expr::apps(
                c.exists_intro.clone(),
                [c.nat.clone(), c.pred_n(&bi, &f, &h, &eps), nmax, witness],
            );
            let e = bi.mk_lam(hn2_id, BinderInfo::Default, hn2_ty, intro);
            let e = bi.mk_lam(n2_id, BinderInfo::Default, c.nat.clone(), e);
            bi.finish_child(e)
        };

        // @Exists.elim Nat pred_gh goal_exists exists_gh elim_inner : goal_exists.
        let elim_gh = Expr::apps(
            c.exists_elim.clone(),
            [
                c.nat.clone(),
                pred_gh.clone(),
                goal_exists.clone(),
                exists_gh.clone(),
                elim_inner,
            ],
        );
        let e = bo.mk_lam(hn1_id, BinderInfo::Default, hn1_ty, elim_gh);
        let e = bo.mk_lam(n1_id, BinderInfo::Default, c.nat.clone(), e);
        bo.finish_child(e)
    };

    // @Exists.elim Nat pred_fg goal_exists exists_fg elim_outer : goal_exists.
    let elim_fg = Expr::apps(
        c.exists_elim.clone(),
        [
            c.nat.clone(),
            pred_fg.clone(),
            goal_exists,
            exists_fg,
            elim_outer,
        ],
    );

    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, elim_fg);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(hgh_id, BinderInfo::Default, egh_ty, e);
    let e = b.mk_lam(hfg_id, BinderInfo::Default, efg_ty, e);
    let e = b.mk_lam(h_id, BinderInfo::Default, c.causeq.clone(), e);
    let e = b.mk_lam(g_id, BinderInfo::Default, c.causeq.clone(), e);
    let e = b.mk_lam(f_id, BinderInfo::Default, c.causeq.clone(), e);
    b.finish(e)
}

/// `pred_n a b eps N` fully applied — `∀ n, Nat.le N n → bound_pair (va)(vb) eps`
/// — re-derived with the binder `N := cap`, for the `Exists.elim` hyp types.
fn pred_fg_at(
    c: &TransConsts,
    parent: &EnvDeclBuilder,
    a: &Expr,
    bb: &Expr,
    eps: &Expr,
    cap: &Expr,
) -> Expr {
    let mut bn = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = bn.fresh_local(c.nat.clone());
    let hle = c.nat_le(cap.clone(), m.clone());
    let (hle_id, _hle) = bn.fresh_local(hle.clone());
    let concl = c.bound_pair(c.vseq(a, &m), c.vseq(bb, &m), eps.clone());
    let e = bn.mk_pi(hle_id, BinderInfo::Default, hle, concl);
    let e = bn.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
    bn.finish_child(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_nnreal_equiv_trans_kernel_check_and_closure() {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_trans()
            .expect("init_algebra_nnreal_trans");
        env.init_algebra_nnreal_trans().expect("idempotent");

        let nm = Name::from_string("NNReal.CauSeq.Equiv.trans");
        let info = env.get_const(&nm).expect("Equiv.trans registered");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .expect("Equiv.trans must kernel-check");

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
