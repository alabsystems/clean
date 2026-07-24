// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — closure of `NNReal.IsCauchy` under pointwise
//! multiplication (`NNReal.IsCauchy_mul`).
//!
//! # Statement
//!
//! ```text
//! NNReal.IsCauchy_mul : ∀ (f g : Nat → NNRat),
//!   IsCauchy f → IsCauchy g → IsCauchy (fun n => NNRat.mul (f n) (g n))
//! ```
//!
//! # Proof shape
//!
//! Mirrors `IsCauchy_add`'s nested `Exists.elim`, but the perturbation algebra
//! is the genuine product estimate. Given `ε > 0`:
//!
//! 1. `NNReal.IsCauchy_bounded` on `f`/`g` extracts `B_f, B_g : NNRat` with
//!    `∀ n, NNRat.le (f n) B_f` (defeq `val (f n) ≤ val B_f`), likewise `B_g`.
//! 2. `B' := val B_f + (val B_g + 1)` is a common STRICT bound: every value is
//!    `≤ val B_f` (or `val B_g`), and `val B_f, val B_g < B'`
//!    (`Rat.lt_add_of_pos_right`, `0 < 1`), so every value is `< B'`
//!    (`Rat.lt_of_le_of_lt`). And `0 < B'` (`0 ≤ val B_f`, `val B_f < B'`).
//! 3. `δ := (ε/2)/B'`. `0 < δ` (`Rat.div_pos` + `Rat.half_pos`), and the budget
//!    collapse `δ·B' = ε/2` is `Rat.div_mul_cancel_pos (ε/2) B' (0<B')`, so
//!    `(δ·B') + (δ·B') = (ε/2)+(ε/2) = ε` (`Rat.add_halves`).
//! 4. Run the `f`/`g` Cauchy tails at `δ`; `N := Nat.max N_f N_g`. For
//!    `m, n ≥ N`, `Rat.mul_lt_mul_add_of_bounds` applied at `(val(fm),val(fn),
//!    val(gm),val(gn),B',δ)` yields `val(fm)·val(gm) < val(fn)·val(gn) +
//!    (δ·B'+δ·B')`; rewriting `δ·B'+δ·B' → ε` and transporting endpoints through
//!    `NNRat.val_mul` lands the forward conjunct. The reverse swaps `m ↔ n`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for `IsCauchy_mul`.
pub(crate) struct IsCauchyMulConsts {
    nat: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_two: Expr,
    nnrat: Expr,
    nnrat_mul: Expr,
    nnrat_val: Expr,
    nnrat_val_mul: Expr,
    nnrat_property: Expr,
    is_cauchy: Expr,
    is_cauchy_bounded: Expr,
    rat_add: Expr,
    rat_mul: Expr,
    rat_div: Expr,
    rat_lt: Expr,
    le_le: Expr,
    inst_le_rat: Expr,
    nat_le: Expr,
    // Lemmas.
    rat_half_pos: Expr,
    rat_add_halves: Expr,
    rat_zero_lt_one: Expr,
    rat_div_pos: Expr,
    rat_le_of_lt: Expr,
    rat_lt_of_le_of_lt: Expr,
    rat_lt_of_lt_of_le: Expr,
    rat_lt_add_of_pos_right: Expr,
    rat_le_add_of_nonneg_left: Expr,
    rat_div_mul_cancel_pos: Expr,
    rat_mul_close: Expr,
    nat_max: Expr,
    nat_le_max_left: Expr,
    nat_le_max_right: Expr,
    nat_le_trans: Expr,
    // Logic.
    and_c: Expr,
    and_intro: Expr,
    and_left: Expr,
    and_right: Expr,
    exists_intro: Expr,
    exists_elim: Expr,
    exists_c: Expr,
    // Eq.{1} over Rat / NNRat.
    eq_rat: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    eq_subst: Expr,
    congr_arg: Expr,
}

impl IsCauchyMulConsts {
    pub(crate) fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_two: k("Rat.two"),
            nnrat: k("NNRat"),
            nnrat_mul: k("NNRat.mul"),
            nnrat_val: k("NNRat.val"),
            nnrat_val_mul: k("NNRat.val_mul"),
            nnrat_property: k("NNRat.property"),
            is_cauchy: k("NNReal.IsCauchy"),
            is_cauchy_bounded: k("NNReal.IsCauchy_bounded"),
            rat_add: k("Rat.add"),
            rat_mul: k("Rat.mul"),
            rat_div: k("Rat.div"),
            rat_lt: k("Rat.lt"),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: k("instLERat"),
            nat_le: k("Nat.le"),
            rat_half_pos: k("Rat.half_pos"),
            rat_add_halves: k("Rat.add_halves"),
            rat_zero_lt_one: k("Rat.zero_lt_one"),
            rat_div_pos: k("Rat.div_pos"),
            rat_le_of_lt: k("Rat.le_of_lt"),
            rat_lt_of_le_of_lt: k("Rat.lt_of_le_of_lt"),
            rat_lt_of_lt_of_le: k("Rat.lt_of_lt_of_le"),
            rat_lt_add_of_pos_right: k("Rat.lt_add_of_pos_right"),
            rat_le_add_of_nonneg_left: k("Rat.le_add_of_nonneg_left"),
            rat_div_mul_cancel_pos: k("Rat.div_mul_cancel_pos"),
            rat_mul_close: k("Rat.mul_lt_mul_add_of_bounds"),
            nat_max: k("Nat.max"),
            nat_le_max_left: k("Nat.le_max_left"),
            nat_le_max_right: k("Nat.le_max_right"),
            nat_le_trans: k("Nat.le_trans"),
            and_c: k("And"),
            and_intro: k("And.intro"),
            and_left: k("And.left"),
            and_right: k("And.right"),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![lvl1.clone()]),
            exists_elim: Expr::const_(Name::from_string("Exists.elim"), vec![lvl1.clone()]),
            exists_c: Expr::const_(Name::from_string("Exists"), vec![lvl1.clone()]),
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![lvl1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![lvl1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![lvl1.clone(), lvl1]),
        }
    }

    pub(crate) fn seq_ty(&self) -> Expr {
        Expr::pi(BinderInfo::Default, self.nat.clone(), self.nnrat.clone())
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn div(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_div.clone(), [a, b])
    }
    fn half(&self, eps: &Expr) -> Expr {
        self.div(eps.clone(), self.rat_two.clone())
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    /// Typeclass `LE.le Rat instLERat a b` (matches the order-toolkit `≤` form).
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            self.le_le.clone(),
            [self.rat.clone(), self.inst_le_rat.clone(), a, b],
        )
    }
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    fn and_ty(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.and_c.clone(), [p, q])
    }
    /// `NNRat.val q : Rat`.
    fn val(&self, q: Expr) -> Expr {
        Expr::app(self.nnrat_val.clone(), q)
    }
    /// `NNRat.mul a b : NNRat`.
    fn nnmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnrat_mul.clone(), [a, b])
    }
    /// `f n : NNRat`.
    fn at(&self, f: &Expr, n: &Expr) -> Expr {
        Expr::app(f.clone(), n.clone())
    }
    /// `val (f n) : Rat`.
    fn vat(&self, f: &Expr, n: &Expr) -> Expr {
        self.val(self.at(f, n))
    }
    /// `NNRat.property q : Rat.le Rat.zero (NNRat.val q)` — but in the order-
    /// toolkit `LE.le` form (the carrier uses bare `Rat.le`; both are defeq so
    /// the kernel accepts `property` where an `LE.le` term is wanted).
    fn property(&self, q: Expr) -> Expr {
        Expr::app(self.nnrat_property.clone(), q)
    }
    fn is_cauchy(&self, f: Expr) -> Expr {
        Expr::app(self.is_cauchy.clone(), f)
    }
    /// The two-sided strict-bound conjunction `And (x<y+ε)(y<x+ε)`.
    fn bound_pair(&self, x: Expr, y: Expr, eps: Expr) -> Expr {
        let left = self.lt(x.clone(), self.add(y.clone(), eps.clone()));
        let right = self.lt(y, self.add(x, eps));
        self.and_ty(left, right)
    }
    fn and_left(&self, p: Expr, q: Expr, h: Expr) -> Expr {
        Expr::apps(self.and_left.clone(), [p, q, h])
    }
    fn and_right(&self, p: Expr, q: Expr, h: Expr) -> Expr {
        Expr::apps(self.and_right.clone(), [p, q, h])
    }
    fn and_intro(&self, p: Expr, q: Expr, hp: Expr, hq: Expr) -> Expr {
        Expr::apps(self.and_intro.clone(), [p, q, hp, hq])
    }
    /// `@Eq Rat a b`.
    fn eq_rat_ty(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq_rat.clone(), [self.rat.clone(), a, b])
    }
    /// `@Eq.symm Rat a b h : Eq Rat b a`.
    fn eq_symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }
    /// `@Eq.trans Rat a b c h1 h2 : Eq Rat a c`.
    fn eq_trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    /// `@congrArg Rat Rat a a' f h : Eq Rat (f a)(f a')`.
    fn congr_arg(&self, a: Expr, a2: Expr, ff: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, a2, ff, h],
        )
    }
    /// `Rat.add_halves eps : Eq Rat ((eps/2)+(eps/2)) eps`.
    fn add_halves(&self, eps: &Expr) -> Expr {
        Expr::app(self.rat_add_halves.clone(), eps.clone())
    }
    /// `Rat.div_mul_cancel_pos a b (0<b) : Eq Rat ((a/b)·b) a`.
    fn div_mul_cancel(&self, a: Expr, bb: Expr, hpos: Expr) -> Expr {
        Expr::apps(self.rat_div_mul_cancel_pos.clone(), [a, bb, hpos])
    }
    /// `@Eq.subst Rat motive a b h_eq h : motive b`.
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `NNRat.val_mul p q : Eq Rat (val (NNRat.mul p q)) (Rat.mul (val p)(val q))`.
    fn val_mul(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.nnrat_val_mul.clone(), [p, q])
    }
    /// `Rat.le_of_lt a b h : Rat.le a b` (the order-toolkit `LE.le` form is what
    /// `le_of_lt` returns? it returns bare `Rat.le`; used only where bare le is
    /// fed to the close lemma's `LE.le` slot — defeq, accepted).
    fn le_of_lt(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_le_of_lt.clone(), [a, b, h])
    }
    /// `Rat.lt_of_le_of_lt a b c (a≤b)(b<c) : a<c`.
    fn lt_of_le_of_lt(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_lt_of_le_of_lt.clone(), [a, b, cc, h1, h2])
    }
    /// `Rat.lt_of_lt_of_le a b c (a<b)(b≤c) : a<c`.
    fn lt_of_lt_of_le(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_lt_of_lt_of_le.clone(), [a, b, cc, h1, h2])
    }
    /// `Rat.lt_add_of_pos_right a p (0<p) : a < a+p`.
    fn lt_add_of_pos_right(&self, a: Expr, p: Expr, hp: Expr) -> Expr {
        Expr::apps(self.rat_lt_add_of_pos_right.clone(), [a, p, hp])
    }
    /// `Rat.le_add_of_nonneg_left a p (0≤p) : a ≤ p+a` (bare `Rat.le`).
    fn le_add_of_nonneg_left(&self, a: Expr, p: Expr, hp: Expr) -> Expr {
        Expr::apps(self.rat_le_add_of_nonneg_left.clone(), [a, p, hp])
    }
    /// `Nat.max a b`.
    fn nat_max(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_max.clone(), [a, b])
    }
    fn nat_le_trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.nat_le_trans.clone(), [a, b, cc, h1, h2])
    }

    /// `IsCauchy_bounded f hf : ∃ B, ∀ n, NNRat.le (f n) B`.
    fn bounded(&self, f: &Expr, hf: &Expr) -> Expr {
        Expr::apps(self.is_cauchy_bounded.clone(), [f.clone(), hf.clone()])
    }

    /// The pointwise-product raw sequence `fun n => NNRat.mul (f n)(g n)`.
    pub(crate) fn prod_seq(&self, parent: &EnvDeclBuilder, f: &Expr, g: &Expr) -> Expr {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (n_id, n) = bn.fresh_local(self.nat.clone());
        let body = self.nnmul(self.at(f, &n), self.at(g, &n));
        bn.finish_child(bn.mk_lam(n_id, BinderInfo::Default, self.nat.clone(), body))
    }

    /// The `IsCauchy_bounded` existential predicate `fun B => ∀ n, NNRat.le (f n) B`.
    fn bound_pred(&self, parent: &EnvDeclBuilder, f: &Expr) -> Expr {
        let mut pb = EnvDeclBuilder::child_of(parent);
        let (bb_id, bb) = pb.fresh_local(self.nnrat.clone());
        let inner = {
            let mut ib = EnvDeclBuilder::child_of(&pb);
            let (n_id, n) = ib.fresh_local(self.nat.clone());
            // NNRat.le (f n) B — but stated via the `Rat.le`-equivalent LE.le form
            // is unnecessary; we use the genuine NNRat.le const so it matches the
            // IsCauchy_bounded conclusion exactly.
            let nnle = Expr::const_(Name::from_string("NNRat.le"), vec![]);
            let concl = Expr::apps(nnle, [self.at(f, &n), bb.clone()]);
            ib.finish_child(ib.mk_pi(n_id, BinderInfo::Default, self.nat.clone(), concl))
        };
        pb.finish_child(pb.mk_lam(bb_id, BinderInfo::Default, self.nnrat.clone(), inner))
    }

    /// The IsCauchy tail predicate at `f`,`eps`: `fun N => ∀ m n, N≤m → N≤n →
    /// bound_pair (val(f m))(val(f n)) eps`.
    fn tail_pred(&self, parent: &EnvDeclBuilder, f: &Expr, eps: &Expr) -> Expr {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (cap_id, cap) = bn.fresh_local(self.nat.clone());
        let body = self.tail_pred_at(&bn, f, eps, &cap);
        bn.finish_child(bn.mk_lam(cap_id, BinderInfo::Default, self.nat.clone(), body))
    }

    /// `∀ m n, cap≤m → cap≤n → bound_pair (val(f m))(val(f n)) eps`.
    fn tail_pred_at(&self, parent: &EnvDeclBuilder, f: &Expr, eps: &Expr, cap: &Expr) -> Expr {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (m_id, m) = bn.fresh_local(self.nat.clone());
        let (n_id, n) = bn.fresh_local(self.nat.clone());
        let hle_m = self.nat_le(cap.clone(), m.clone());
        let (hlem_id, _h) = bn.fresh_local(hle_m.clone());
        let hle_n = self.nat_le(cap.clone(), n.clone());
        let (hlen_id, _h2) = bn.fresh_local(hle_n.clone());
        let concl = self.bound_pair(self.vat(f, &m), self.vat(f, &n), eps.clone());
        let e = bn.mk_pi(hlen_id, BinderInfo::Default, hle_n, concl);
        let e = bn.mk_pi(hlem_id, BinderInfo::Default, hle_m, e);
        let e = bn.mk_pi(n_id, BinderInfo::Default, self.nat.clone(), e);
        let e = bn.mk_pi(m_id, BinderInfo::Default, self.nat.clone(), e);
        bn.finish_child(e)
    }

    /// The goal existential `∃ N, prod_tail_pred N` (the product sequence at ε).
    fn goal_exists(&self, parent: &EnvDeclBuilder, prod: &Expr, eps: &Expr) -> Expr {
        let pred = self.tail_pred(parent, prod, eps);
        Expr::apps(self.exists_c.clone(), [self.nat.clone(), pred])
    }

    /// `Rat.mul_lt_mul_add_of_bounds am an bm bn B d h0an h0bm hanB hbmB h0d ham hbm`.
    #[allow(clippy::too_many_arguments)]
    fn mul_close(
        &self,
        am: Expr,
        an: Expr,
        bm: Expr,
        bn: Expr,
        bb: Expr,
        d: Expr,
        h0an: Expr,
        h0bm: Expr,
        han_b: Expr,
        hbm_b: Expr,
        h0d: Expr,
        ham: Expr,
        hbm: Expr,
    ) -> Expr {
        Expr::apps(
            self.rat_mul_close.clone(),
            [
                am, an, bm, bn, bb, d, h0an, h0bm, han_b, hbm_b, h0d, ham, hbm,
            ],
        )
    }
}

impl Environment {
    /// Register `NNReal.IsCauchy_mul`. Idempotent.
    pub fn init_algebra_nnreal_iscauchy_mul(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_cauchy()?; // IsCauchy, NNRat.*, val, property
        self.init_algebra_nnreal_bounded()?; // NNReal.IsCauchy_bounded
        self.init_algebra_rat_half_pos()?; // Rat.half_pos, add_halves, two
        self.init_algebra_rat_inv_pos()?; // Rat.div_pos, le_of_lt
        self.init_algebra_rat_div_mul_cancel()?; // Rat.div_mul_cancel_pos
        self.init_algebra_rat_mul_close()?; // Rat.zero_lt_one + lt_of_le_of_lt/lt_of_lt_of_le chain
        self.init_algebra_rat_mul_close_recovered()?; // Rat.mul_lt_mul_add_of_bounds (the close lemma the proof actually cites)
        self.init_algebra_rat_add_lt_add_mixed()?; // lt_add_of_pos_right, le_add_of_nonneg_left
        self.register_nat_minmax_proofs()?; // Nat.max, le_max_left/right
        self.register_nat_le_trans_proof()?; // Nat.le_trans

        let c = IsCauchyMulConsts::new();
        self.register_nnreal_is_cauchy_mul_recovered(&c)
    }

    fn register_nnreal_is_cauchy_mul_recovered(
        &mut self,
        c: &IsCauchyMulConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.IsCauchy_mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.seq_ty());
            let (g_id, g) = b.fresh_local(c.seq_ty());
            let hf = c.is_cauchy(f.clone());
            let (hf_id, _h) = b.fresh_local(hf.clone());
            let hg = c.is_cauchy(g.clone());
            let (hg_id, _h2) = b.fresh_local(hg.clone());
            let prod = c.prod_seq(&b, &f, &g);
            let concl = c.is_cauchy(prod);
            let e = b.mk_pi(hg_id, BinderInfo::Default, hg, concl);
            let e = b.mk_pi(hf_id, BinderInfo::Default, hf, e);
            let e = b.mk_pi(g_id, BinderInfo::Default, c.seq_ty(), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.seq_ty(), e);
            b.finish(e)
        };
        let value = build_is_cauchy_mul_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Build the full proof term for `NNReal.IsCauchy_mul`.
#[allow(clippy::too_many_lines)]
fn build_is_cauchy_mul_proof(c: &IsCauchyMulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (f_id, f) = b.fresh_local(c.seq_ty());
    let (g_id, g) = b.fresh_local(c.seq_ty());
    let hf_ty = c.is_cauchy(f.clone());
    let (hf_id, hf) = b.fresh_local(hf_ty.clone());
    let hg_ty = c.is_cauchy(g.clone());
    let (hg_id, hg) = b.fresh_local(hg_ty.clone());

    let prod = c.prod_seq(&b, &f, &g);

    // Goal: IsCauchy prod = ∀ ε, 0<ε → goal_exists.
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.lt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

    let goal_exists = c.goal_exists(&b, &prod, &eps);

    // existsBf := IsCauchy_bounded f hf ; existsBg likewise.
    let exists_bf = c.bounded(&f, &hf);
    let exists_bg = c.bounded(&g, &hg);
    let pred_bf = c.bound_pred(&b, &f);
    let pred_bg = c.bound_pred(&b, &g);

    // Outer elim over B_f.
    let elim_bf_fn = {
        let mut bo = EnvDeclBuilder::child_of(&b);
        let (bf_id, bf) = bo.fresh_local(c.nnrat.clone());
        // hBf : ∀ n, NNRat.le (f n) B_f.
        let hbf_ty = {
            let mut hb = EnvDeclBuilder::child_of(&bo);
            let (n_id, n) = hb.fresh_local(c.nat.clone());
            let nnle = Expr::const_(Name::from_string("NNRat.le"), vec![]);
            let concl = Expr::apps(nnle, [c.at(&f, &n), bf.clone()]);
            hb.finish_child(hb.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl))
        };
        let (hbf_id, hbf) = bo.fresh_local(hbf_ty.clone());

        let elim_bg_fn = {
            let mut bi = EnvDeclBuilder::child_of(&bo);
            let (bg_id, bg) = bi.fresh_local(c.nnrat.clone());
            let hbg_ty = {
                let mut hb = EnvDeclBuilder::child_of(&bi);
                let (n_id, n) = hb.fresh_local(c.nat.clone());
                let nnle = Expr::const_(Name::from_string("NNRat.le"), vec![]);
                let concl = Expr::apps(nnle, [c.at(&g, &n), bg.clone()]);
                hb.finish_child(hb.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl))
            };
            let (hbg_id, hbg) = bi.fresh_local(hbg_ty.clone());

            let inner = build_with_bounds(
                c,
                &bi,
                &f,
                &g,
                &prod,
                &eps,
                &hpos,
                &hf,
                &hg,
                &bf,
                &bg,
                &hbf,
                &hbg,
                &goal_exists,
            );

            let e = bi.mk_lam(hbg_id, BinderInfo::Default, hbg_ty, inner);
            let e = bi.mk_lam(bg_id, BinderInfo::Default, c.nnrat.clone(), e);
            bi.finish_child(e)
        };

        let elim_bg = Expr::apps(
            c.exists_elim.clone(),
            [
                c.nnrat.clone(),
                pred_bg.clone(),
                goal_exists.clone(),
                exists_bg.clone(),
                elim_bg_fn,
            ],
        );
        let e = bo.mk_lam(hbf_id, BinderInfo::Default, hbf_ty, elim_bg);
        let e = bo.mk_lam(bf_id, BinderInfo::Default, c.nnrat.clone(), e);
        bo.finish_child(e)
    };

    let elim_bf = Expr::apps(
        c.exists_elim.clone(),
        [c.nnrat.clone(), pred_bf, goal_exists, exists_bf, elim_bf_fn],
    );

    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, elim_bf);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(hg_id, BinderInfo::Default, hg_ty, e);
    let e = b.mk_lam(hf_id, BinderInfo::Default, hf_ty, e);
    let e = b.mk_lam(g_id, BinderInfo::Default, c.seq_ty(), e);
    let e = b.mk_lam(f_id, BinderInfo::Default, c.seq_ty(), e);
    b.finish(e)
}

/// With both bounds `B_f, B_g` in scope, build `B'`, `δ`, the Cauchy-tail
/// `Exists.elim`s, and the witness. Returns a term of type `goal_exists`.
#[allow(clippy::too_many_arguments)]
fn build_with_bounds(
    c: &IsCauchyMulConsts,
    parent: &EnvDeclBuilder,
    f: &Expr,
    g: &Expr,
    prod: &Expr,
    eps: &Expr,
    hpos: &Expr,
    hf: &Expr,
    hg: &Expr,
    bf: &Expr,
    bg: &Expr,
    hbf: &Expr,
    hbg: &Expr,
    goal_exists: &Expr,
) -> Expr {
    let vbf = c.val(bf.clone()); // val B_f
    let vbg = c.val(bg.clone()); // val B_g
    let one = c.rat_one.clone();

    // B' := vbf + (vbg + 1).
    let vbg1 = c.add(vbg.clone(), one.clone()); // vbg + 1
    let bprime = c.add(vbf.clone(), vbg1.clone()); // vbf + (vbg+1)

    // half := ε/2 ; δ := half / B'.
    let half = c.half(eps); // ε/2
    let delta = c.div(half.clone(), bprime.clone()); // (ε/2)/B'

    // ── positivity facts ──
    // h0half : 0 < ε/2 := Rat.half_pos ε hpos.
    let h0half = Expr::apps(c.rat_half_pos.clone(), [eps.clone(), hpos.clone()]);
    // h0bf : 0 ≤ vbf := NNRat.property B_f.
    let h0bf = c.property(bf.clone());
    // hbf_lt : vbf < B' := lt_add_of_pos_right vbf (vbg+1) h0vbg1.
    //   h0vbg1 : 0 < (vbg+1) := lt_of_le_of_lt 0 vbg (vbg+1) (property B_g) (lt_add_of_pos_right vbg 1 0<1).
    let h0vbg = c.property(bg.clone()); // 0 ≤ vbg
    let vbg_lt = c.lt_add_of_pos_right(vbg.clone(), one.clone(), c.rat_zero_lt_one.clone()); // vbg < vbg+1
    let h0vbg1 = c.lt_of_le_of_lt(c.rat_zero.clone(), vbg.clone(), vbg1.clone(), h0vbg, vbg_lt); // 0 < vbg+1
    let hbf_lt = c.lt_add_of_pos_right(vbf.clone(), vbg1.clone(), h0vbg1.clone()); // vbf < B'
                                                                                   // h0bprime : 0 < B' := lt_of_le_of_lt 0 vbf B' h0bf hbf_lt.
    let h0bprime = c.lt_of_le_of_lt(
        c.rat_zero.clone(),
        vbf.clone(),
        bprime.clone(),
        h0bf,
        hbf_lt.clone(),
    );
    // h0delta : 0 < δ := Rat.div_pos (ε/2) B' h0half h0bprime.
    let h0delta = Expr::apps(
        c.rat_div_pos.clone(),
        [half.clone(), bprime.clone(), h0half, h0bprime.clone()],
    );

    // budget : (δ·B') + (δ·B') = ε.
    //   db_eq : δ·B' = ε/2  := Rat.div_mul_cancel_pos (ε/2) B' h0bprime.
    //   add_halves ε : (ε/2 + ε/2) = ε.
    //   Compose: subst both summands of (ε/2+ε/2) to δ·B'... we build the Eq
    //   `(δ·B')+(δ·B') = ε` directly in `build_witness` where it's consumed.

    // Cauchy tails at δ.
    let exists_f = Expr::apps(hf.clone(), [delta.clone(), h0delta.clone()]);
    let exists_g = Expr::apps(hg.clone(), [delta.clone(), h0delta.clone()]);
    let pred_f = c.tail_pred(parent, f, &delta);
    let pred_g = c.tail_pred(parent, g, &delta);

    let elim_nf_fn = {
        let mut bo = EnvDeclBuilder::child_of(parent);
        let (nf_id, nf) = bo.fresh_local(c.nat.clone());
        let hnf_ty = c.tail_pred_at(&bo, f, &delta, &nf);
        let (hnf_id, hnf) = bo.fresh_local(hnf_ty.clone());

        let elim_ng_fn = {
            let mut bi = EnvDeclBuilder::child_of(&bo);
            let (ng_id, ng) = bi.fresh_local(c.nat.clone());
            let hng_ty = c.tail_pred_at(&bi, g, &delta, &ng);
            let (hng_id, hng) = bi.fresh_local(hng_ty.clone());

            let nmax = c.nat_max(nf.clone(), ng.clone());

            let witness = build_witness(
                c, &bi, f, g, prod, eps, &delta, &h0delta, &bprime, &h0bprime, bf, bg, hbf, hbg,
                &hbf_lt, &nf, &ng, &hnf, &hng, &nmax,
            );

            let pred_prod = c.tail_pred(&bi, prod, eps);
            let intro = Expr::apps(
                c.exists_intro.clone(),
                [c.nat.clone(), pred_prod, nmax, witness],
            );
            let e = bi.mk_lam(hng_id, BinderInfo::Default, hng_ty, intro);
            let e = bi.mk_lam(ng_id, BinderInfo::Default, c.nat.clone(), e);
            bi.finish_child(e)
        };

        let elim_ng = Expr::apps(
            c.exists_elim.clone(),
            [
                c.nat.clone(),
                pred_g.clone(),
                goal_exists.clone(),
                exists_g.clone(),
                elim_ng_fn,
            ],
        );
        let e = bo.mk_lam(hnf_id, BinderInfo::Default, hnf_ty, elim_ng);
        let e = bo.mk_lam(nf_id, BinderInfo::Default, c.nat.clone(), e);
        bo.finish_child(e)
    };

    Expr::apps(
        c.exists_elim.clone(),
        [
            c.nat.clone(),
            pred_f,
            goal_exists.clone(),
            exists_f,
            elim_nf_fn,
        ],
    )
}

/// The per-index witness `∀ m n, N≤m → N≤n → bound_pair (val(prod m))(val(prod n)) ε`.
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn build_witness(
    c: &IsCauchyMulConsts,
    parent: &EnvDeclBuilder,
    f: &Expr,
    g: &Expr,
    _prod: &Expr,
    eps: &Expr,
    delta: &Expr,
    h0delta: &Expr,
    bprime: &Expr,
    h0bprime: &Expr,
    bf: &Expr,
    bg: &Expr,
    hbf: &Expr,
    hbg: &Expr,
    hbf_lt: &Expr,
    nf: &Expr,
    ng: &Expr,
    hnf: &Expr,
    hng: &Expr,
    nmax: &Expr,
) -> Expr {
    let mut bw = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = bw.fresh_local(c.nat.clone());
    let (n_id, n) = bw.fresh_local(c.nat.clone());
    let hle_m_ty = c.nat_le(nmax.clone(), m.clone());
    let (hlem_id, hle_m) = bw.fresh_local(hle_m_ty.clone());
    let hle_n_ty = c.nat_le(nmax.clone(), n.clone());
    let (hlen_id, hle_n) = bw.fresh_local(hle_n_ty.clone());

    // Nf≤m, Nf≤n, Ng≤m, Ng≤n via le_trans through max.
    let le_max_l = Expr::apps(c.nat_le_max_left.clone(), [nf.clone(), ng.clone()]);
    let le_max_r = Expr::apps(c.nat_le_max_right.clone(), [nf.clone(), ng.clone()]);
    let nf_le_m = c.nat_le_trans(
        nf.clone(),
        nmax.clone(),
        m.clone(),
        le_max_l.clone(),
        hle_m.clone(),
    );
    let nf_le_n = c.nat_le_trans(nf.clone(), nmax.clone(), n.clone(), le_max_l, hle_n.clone());
    let ng_le_m = c.nat_le_trans(ng.clone(), nmax.clone(), m.clone(), le_max_r.clone(), hle_m);
    let ng_le_n = c.nat_le_trans(ng.clone(), nmax.clone(), n.clone(), le_max_r, hle_n);

    // f-tail / g-tail conjunctions at (m,n).
    let base_f = Expr::apps(hnf.clone(), [m.clone(), n.clone(), nf_le_m, nf_le_n]);
    let base_g = Expr::apps(hng.clone(), [m.clone(), n.clone(), ng_le_m, ng_le_n]);

    let am = c.vat(f, &m);
    let an = c.vat(f, &n);
    let bm = c.vat(g, &m);
    let bn = c.vat(g, &n);

    // f conjuncts: af_l : am < an+δ ; af_r : an < am+δ.
    let lf = c.lt(am.clone(), c.add(an.clone(), delta.clone()));
    let rf = c.lt(an.clone(), c.add(am.clone(), delta.clone()));
    let af_l = c.and_left(lf.clone(), rf.clone(), base_f.clone());
    let af_r = c.and_right(lf, rf, base_f);
    // g conjuncts: bg_l : bm < bn+δ ; bg_r : bn < bm+δ.
    let lg = c.lt(bm.clone(), c.add(bn.clone(), delta.clone()));
    let rg = c.lt(bn.clone(), c.add(bm.clone(), delta.clone()));
    let bg_l = c.and_left(lg.clone(), rg.clone(), base_g.clone());
    let bg_r = c.and_right(lg, rg, base_g);

    // weak (≤) forms for the close lemma.
    let af_l_le = c.le_of_lt(am.clone(), c.add(an.clone(), delta.clone()), af_l); // am ≤ an+δ
    let af_r_le = c.le_of_lt(an.clone(), c.add(am.clone(), delta.clone()), af_r); // an ≤ am+δ
    let bg_l_le = c.le_of_lt(bm.clone(), c.add(bn.clone(), delta.clone()), bg_l); // bm ≤ bn+δ
    let bg_r_le = c.le_of_lt(bn.clone(), c.add(bm.clone(), delta.clone()), bg_r); // bn ≤ bm+δ

    // nonneg facts.
    let h0am = c.property(c.at(f, &m)); // 0 ≤ am
    let h0an = c.property(c.at(f, &n)); // 0 ≤ an
    let h0bm = c.property(c.at(g, &m)); // 0 ≤ bm
    let h0bn = c.property(c.at(g, &n)); // 0 ≤ bn

    // ── strict bounds x < B' for x ∈ {am, an, bm, bn} ──
    // B' = vbf + (vbg+1). hbf_lt : vbf < B' (passed in).
    // hbg_lt : vbg < B' := lt_of_lt_of_le vbg (vbg+1) B' (vbg<vbg+1) ((vbg+1) ≤ B').
    let vbf = c.val(bf.clone());
    let vbg = c.val(bg.clone());
    let one = c.rat_one.clone();
    let vbg1 = c.add(vbg.clone(), one.clone());
    // vbg < vbg+1.
    let vbg_lt_vbg1 = c.lt_add_of_pos_right(vbg.clone(), one.clone(), c.rat_zero_lt_one.clone());
    // (vbg+1) ≤ vbf+(vbg+1)  := le_add_of_nonneg_left (vbg+1) vbf (0≤vbf).
    let vbg1_le_bprime = c.le_add_of_nonneg_left(vbg1.clone(), vbf.clone(), c.property(bf.clone()));
    let hbg_lt = c.lt_of_lt_of_le(
        vbg.clone(),
        vbg1.clone(),
        bprime.clone(),
        vbg_lt_vbg1,
        vbg1_le_bprime,
    ); // vbg < B'

    // Bound-at-index facts (defeq Rat.le forms): am≤vbf, an≤vbf, bm≤vbg, bn≤vbg.
    let am_le_vbf = Expr::apps(hbf.clone(), [m.clone()]);
    let an_le_vbf = Expr::apps(hbf.clone(), [n.clone()]);
    let bm_le_vbg = Expr::apps(hbg.clone(), [m.clone()]);
    let bn_le_vbg = Expr::apps(hbg.clone(), [n.clone()]);

    // am < B' := lt_of_le_of_lt am vbf B' (am≤vbf) hbf_lt ; etc.
    let am_lt = c.lt_of_le_of_lt(
        am.clone(),
        vbf.clone(),
        bprime.clone(),
        am_le_vbf,
        hbf_lt.clone(),
    );
    let an_lt = c.lt_of_le_of_lt(
        an.clone(),
        vbf.clone(),
        bprime.clone(),
        an_le_vbf,
        hbf_lt.clone(),
    );
    let bm_lt = c.lt_of_le_of_lt(
        bm.clone(),
        vbg.clone(),
        bprime.clone(),
        bm_le_vbg,
        hbg_lt.clone(),
    );
    let bn_lt = c.lt_of_le_of_lt(bn.clone(), vbg.clone(), bprime.clone(), bn_le_vbg, hbg_lt);

    // ── budget : (δ·B' + δ·B') = ε ──
    let db = c.mul(delta.clone(), bprime.clone()); // δ·B'
    let dbdb = c.add(db.clone(), db.clone()); // δ·B' + δ·B'
    let db_eq = c.div_mul_cancel(c.half(eps), bprime.clone(), h0bprime.clone()); // δ·B' = ε/2
    let half = c.half(eps);
    // e1 : (δB'+δB') = (ε/2 + δB')  := congrArg (·+δB') db_eq.
    let add_r_fn = {
        let mut fb = EnvDeclBuilder::child_of(&bw);
        let (t_id, t) = fb.fresh_local(c.rat.clone());
        let body = c.add(t, db.clone());
        fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let e1 = c.congr_arg(db.clone(), half.clone(), add_r_fn, db_eq.clone());
    // e2 : (ε/2 + δB') = (ε/2 + ε/2)  := congrArg (ε/2 + ·) db_eq.
    let add_l_fn = {
        let mut fb = EnvDeclBuilder::child_of(&bw);
        let (t_id, t) = fb.fresh_local(c.rat.clone());
        let body = c.add(half.clone(), t);
        fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let e2 = c.congr_arg(db.clone(), half.clone(), add_l_fn, db_eq);
    // e3 : (ε/2 + ε/2) = ε  := add_halves ε.
    let e3 = c.add_halves(eps);
    let half_db = c.add(half.clone(), db.clone()); // ε/2 + δB'
    let half_half = c.add(half.clone(), half.clone()); // ε/2 + ε/2
    let c12 = c.eq_trans(dbdb.clone(), half_db, half_half.clone(), e1, e2); // (δB'+δB') = (ε/2+ε/2)
    let budget = c.eq_trans(dbdb.clone(), half_half, eps.clone(), c12, e3); // (δB'+δB') = ε

    // ── products & endpoint transports ──
    let am_bm = c.mul(am.clone(), bm.clone());
    let an_bn = c.mul(an.clone(), bn.clone());
    // val_mul (f m)(g m) : v(mul(fm)(gm)) = am·bm  (and at n).
    let vprod_m = c.val(c.nnmul(c.at(f, &m), c.at(g, &m))); // ≡ v(prod m) defeq
    let vprod_n = c.val(c.nnmul(c.at(f, &n), c.at(g, &n)));
    let valmul_m = c.val_mul(c.at(f, &m), c.at(g, &m)); // v(mul..) = am·bm
    let valmul_n = c.val_mul(c.at(f, &n), c.at(g, &n));

    // ── FORWARD : v(prod m) < v(prod n) + ε ──
    let fwd_raw = c.mul_close(
        am.clone(),
        an.clone(),
        bm.clone(),
        bn.clone(),
        bprime.clone(),
        delta.clone(),
        h0an,
        h0bm,
        an_lt.clone(),
        bm_lt.clone(),
        h0delta.clone(),
        af_l_le,
        bg_l_le,
    );
    // fwd_raw : am·bm < an·bn + (δB'+δB').
    // step 1: rewrite inner (δB'+δB') → ε. motive t := am·bm < an·bn + t.
    let mfwd_budget = {
        let mut mb = EnvDeclBuilder::child_of(&bw);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.lt(am_bm.clone(), c.add(an_bn.clone(), t));
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let fwd1 = c.subst(
        mfwd_budget,
        dbdb.clone(),
        eps.clone(),
        budget.clone(),
        fwd_raw,
    );
    // step 2: rewrite RHS summand an·bn → v(prod n). motive t := am·bm < t + ε.
    let mfwd_rhs = {
        let mut mb = EnvDeclBuilder::child_of(&bw);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.lt(am_bm.clone(), c.add(t, eps.clone()));
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let fwd2 = c.subst(
        mfwd_rhs,
        an_bn.clone(),
        vprod_n.clone(),
        c.eq_symm(vprod_n.clone(), an_bn.clone(), valmul_n.clone()),
        fwd1,
    );
    // step 3: rewrite LHS am·bm → v(prod m). motive t := t < v(prod n) + ε.
    let mfwd_lhs = {
        let mut mb = EnvDeclBuilder::child_of(&bw);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.lt(t, c.add(vprod_n.clone(), eps.clone()));
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let fwd = c.subst(
        mfwd_lhs,
        am_bm.clone(),
        vprod_m.clone(),
        c.eq_symm(vprod_m.clone(), am_bm.clone(), valmul_m.clone()),
        fwd2,
    );

    // ── REVERSE : v(prod n) < v(prod m) + ε ──
    // mul_close with m↔n swapped: (an,am,bn,bm,B',δ) and hyps 0≤am,0≤bn,an<B',bn<B',
    //   an≤am+δ, bn≤bm+δ. Conclusion: an·bn < am·bm + (δB'+δB').
    let rev_raw = c.mul_close(
        an.clone(),
        am.clone(),
        bn.clone(),
        bm.clone(),
        bprime.clone(),
        delta.clone(),
        h0am,
        h0bn,
        am_lt,
        bn_lt,
        h0delta.clone(),
        af_r_le,
        bg_r_le,
    );
    let mrev_budget = {
        let mut mb = EnvDeclBuilder::child_of(&bw);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.lt(an_bn.clone(), c.add(am_bm.clone(), t));
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let rev1 = c.subst(mrev_budget, dbdb.clone(), eps.clone(), budget, rev_raw);
    let mrev_rhs = {
        let mut mb = EnvDeclBuilder::child_of(&bw);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.lt(an_bn.clone(), c.add(t, eps.clone()));
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let rev2 = c.subst(
        mrev_rhs,
        am_bm.clone(),
        vprod_m.clone(),
        c.eq_symm(vprod_m.clone(), am_bm.clone(), valmul_m),
        rev1,
    );
    let mrev_lhs = {
        let mut mb = EnvDeclBuilder::child_of(&bw);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.lt(t, c.add(vprod_m.clone(), eps.clone()));
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let rev = c.subst(
        mrev_lhs,
        an_bn.clone(),
        vprod_n.clone(),
        c.eq_symm(vprod_n.clone(), an_bn.clone(), valmul_n),
        rev2,
    );

    // And.intro of the two-sided strict bound on v(prod m)/v(prod n).
    let l_final = c.lt(vprod_m.clone(), c.add(vprod_n.clone(), eps.clone()));
    let r_final = c.lt(vprod_n.clone(), c.add(vprod_m.clone(), eps.clone()));
    let proof = c.and_intro(l_final, r_final, fwd, rev);

    let e = bw.mk_lam(hlen_id, BinderInfo::Default, hle_n_ty, proof);
    let e = bw.mk_lam(hlem_id, BinderInfo::Default, hle_m_ty, e);
    let e = bw.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = bw.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
    bw.finish_child(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_is_cauchy_mul_kernel_check_and_closure() {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_iscauchy_mul()
            .expect("init_algebra_nnreal_iscauchy_mul");
        env.init_algebra_nnreal_iscauchy_mul().expect("idempotent");

        let nm = Name::from_string("NNReal.IsCauchy_mul");
        let info = env.get_const(&nm).expect("IsCauchy_mul registered");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .expect("IsCauchy_mul must kernel-check");

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
