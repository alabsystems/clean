// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — Component A, Step (3b)/(4): closure of `NNReal.IsCauchy`
//! under pointwise MULTIPLICATION, and the `NNReal.mul` binary `Quot.lift`.
//!
//! # Why this module exists
//!
//! `NNReal.CauSeq.mul` builds the pointwise-product sequence
//! `fun n => NNRat.mul (seq f n)(seq g n)`, so `NNReal.CauSeq.mk` needs:
//!
//! - `NNReal.IsCauchy_mul : ∀ (f g : Nat → NNRat), IsCauchy f → IsCauchy g →
//!       IsCauchy (fun n => NNRat.mul (f n)(g n))`
//!
//! Unlike addition (a clean ε/2 split), the product needs the factors BOUNDED.
//! `NNReal.IsCauchy_bounded` (axiom-free, on main) supplies bounds `Bf`,`Bg`;
//! the δ-choice (`Rat.deltaMul`, axiom-free) supplies a band `δ` with
//! `δ·(Bfr+Bgr) ≤ ε/2`; and `Rat.mul_close_of_close` (axiom-free) discharges
//! both conjuncts of the product `bound_pair` from the cross-term estimate.
//!
//! `NNReal.mul` is then the binary `Quot.lift` (mirroring `NNReal.add`), built
//! in a companion run once `IsCauchy_mul` lands — see `algebra_nnreal_add.rs`.
//!
//! # Proof shape (`IsCauchy_mul`)
//!
//! ```text
//! λ f g hf hg ε hpos =>
//!   Exists.elim (IsCauchy_bounded f hf) (Bf, hBf) =>
//!   Exists.elim (IsCauchy_bounded g hg) (Bg, hBg) =>
//!     Bfr := val Bf ; Bgr := val Bg ; D := (Bfr+Bgr)+1
//!     h0D : 0<D ; hDne : D=0→False ; δ := deltaMul ε D
//!     hδpos : 0<δ ; h0δ : 0≤δ ; hδD : δ·D = ε/2
//!     hbudget : δ·(Bfr+Bgr) ≤ ε/2     (mul_le_left δ (Bfr+Bgr) D + hδD)
//!   Exists.elim (hf δ hδpos) (Nf, hNf) =>
//!   Exists.elim (hg δ hδpos) (Ng, hNg) =>
//!     N := Nat.max Nf Ng
//!     Exists.intro (prod-pred ε) N (λ m n hNm hNn =>
//!       base_f := hNf m n (Nf≤m)(Nf≤n)   -- via max+le_trans
//!       base_g := hNg m n (Ng≤m)(Ng≤n)
//!       fwd : vfm·vgm < vfn·vgn + ε
//!         := mul_close_of_close vfm vfn vgm vgn Bfr Bgr ε δ … hpos
//!       rev : vfn·vgn < vfm·vgm + ε   (mul_close with m↔n swapped)
//!       transport vfx·vgx → val(prod x) via symm (NNRat.val_mul (f x)(g x))
//!       And.intro fwd' rev')
//! ```
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
    rat_add: Expr,
    rat_mul: Expr,
    rat_div: Expr,
    rat_lt: Expr,
    rat_le: Expr,
    nat_le: Expr,
    // Rat lemmas.
    rat_zero_lt_one: Expr,
    rat_zero_le_one: Expr,
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
    rat_mul_close: Expr,
    // Nat lemmas.
    nat_max: Expr,
    nat_le_max_left: Expr,
    nat_le_max_right: Expr,
    nat_le_trans: Expr,
    // IsCauchy_bounded.
    is_cauchy_bounded: Expr,
    // Logic.
    and_c: Expr,
    and_intro: Expr,
    and_left: Expr,
    and_right: Expr,
    not_c: Expr,
    iff_mp: Expr,
    exists_c: Expr,
    exists_intro: Expr,
    exists_elim: Expr,
    // Eq.{1} over Rat.
    eq_rat: Expr,
    eq_symm: Expr,
    eq_subst: Expr,
}

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
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
            rat_add: k("Rat.add"),
            rat_mul: k("Rat.mul"),
            rat_div: k("Rat.div"),
            rat_lt: k("Rat.lt"),
            rat_le: k("Rat.le"),
            nat_le: k("Nat.le"),
            rat_zero_lt_one: k("Rat.zero_lt_one"),
            rat_zero_le_one: k("Rat.zero_le_one"),
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
            rat_mul_close: k("Rat.mul_close_of_close"),
            nat_max: k("Nat.max"),
            nat_le_max_left: k("Nat.le_max_left"),
            nat_le_max_right: k("Nat.le_max_right"),
            nat_le_trans: k("Nat.le_trans"),
            is_cauchy_bounded: k("NNReal.IsCauchy_bounded"),
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
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1]),
        }
    }

    fn seq_ty(&self) -> Expr {
        Expr::pi(BinderInfo::Default, self.nat.clone(), self.nnrat.clone())
    }
    fn at(&self, f: &Expr, n: &Expr) -> Expr {
        Expr::app(f.clone(), n.clone())
    }
    fn val(&self, q: Expr) -> Expr {
        Expr::app(self.nnrat_val.clone(), q)
    }
    fn vat(&self, f: &Expr, n: &Expr) -> Expr {
        self.val(self.at(f, n))
    }
    fn nnmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnrat_mul.clone(), [a, b])
    }
    fn radd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn rmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn rdiv(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_div.clone(), [a, b])
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
    fn half(&self, eps: Expr) -> Expr {
        self.rdiv(eps, self.rat_two.clone())
    }
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    fn is_cauchy(&self, f: Expr) -> Expr {
        Expr::app(self.is_cauchy.clone(), f)
    }
    fn property(&self, q: Expr) -> Expr {
        Expr::app(self.nnrat_property.clone(), q)
    }
    /// `NNRat.val_mul p q : Eq Rat (val (NNRat.mul p q)) ((val p)·(val q))`.
    fn val_mul(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.nnrat_val_mul.clone(), [p, q])
    }
    fn bound_pair(&self, x: Expr, y: Expr, eps: Expr) -> Expr {
        let left = self.rlt(x.clone(), self.radd(y.clone(), eps.clone()));
        let right = self.rlt(y, self.radd(x, eps));
        Expr::apps(self.and_c.clone(), [left, right])
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
    fn nat_le_trans(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(self.nat_le_trans.clone(), [a, b, cc, hab, hbc])
    }
    fn mul_le_left(&self, a: Expr, b: Expr, cc: Expr, hbc: Expr, ha: Expr) -> Expr {
        Expr::apps(self.rat_mul_le_left.clone(), [a, b, cc, hbc, ha])
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
    fn add_zero(&self, a: Expr) -> Expr {
        Expr::app(self.rat_add_zero.clone(), a)
    }
    fn zero_add(&self, a: Expr) -> Expr {
        Expr::app(self.rat_zero_add.clone(), a)
    }
    fn eq_ty(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq_rat.clone(), [self.rat.clone(), a, b])
    }
    fn eq_symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `Rat.lt_iff` bridge: from `hlt : Rat.lt a b`, extract `Rat.le a b`.
    fn le_of_lt(&self, a: Expr, b: Expr, hlt: Expr) -> Expr {
        let le_ab = self.rle(a.clone(), b.clone());
        let not_le_ba = Expr::app(self.not_c.clone(), self.rle(b.clone(), a.clone()));
        let and_ty = Expr::apps(self.and_c.clone(), [le_ab.clone(), not_le_ba.clone()]);
        let lt_ab = self.rlt(a.clone(), b.clone());
        let iff = Expr::apps(self.rat_lt_iff_le_not_le.clone(), [a, b]);
        let mp = Expr::apps(self.iff_mp.clone(), [lt_ab, and_ty, iff, hlt]);
        Expr::apps(self.and_left.clone(), [le_ab, not_le_ba, mp])
    }
    /// `Rat.deltaMul ε D`.
    fn delta(&self, eps: &Expr, d: &Expr) -> Expr {
        Expr::apps(self.rat_deltamul.clone(), [eps.clone(), d.clone()])
    }
    /// The pointwise-product raw sequence `fun n => NNRat.mul (f n)(g n)`.
    fn prod_seq(&self, parent: &EnvDeclBuilder, f: &Expr, g: &Expr) -> Expr {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (n_id, n) = bn.fresh_local(self.nat.clone());
        let body = self.nnmul(self.at(f, &n), self.at(g, &n));
        bn.finish_child(bn.mk_lam(n_id, BinderInfo::Default, self.nat.clone(), body))
    }
    /// `∃ B, ∀ n, NNRat.le (f n) B` predicate body (for Exists.elim type).
    fn bounded_pred(&self, parent: &EnvDeclBuilder, f: &Expr) -> Expr {
        let mut pb = EnvDeclBuilder::child_of(parent);
        let (bb_id, bb) = pb.fresh_local(self.nnrat.clone());
        let inner = {
            let mut ib = EnvDeclBuilder::child_of(&pb);
            let (n_id, n) = ib.fresh_local(self.nat.clone());
            let nle = Expr::apps(
                Expr::const_(Name::from_string("NNRat.le"), vec![]),
                [self.at(f, &n), bb.clone()],
            );
            ib.finish_child(ib.mk_pi(n_id, BinderInfo::Default, self.nat.clone(), nle))
        };
        pb.finish_child(pb.mk_lam(bb_id, BinderInfo::Default, self.nnrat.clone(), inner))
    }
    /// `∃ B, ∀ n, NNRat.le (f n) B` (the IsCauchy_bounded result type).
    #[cfg(test)]
    fn bounded_exists(&self, parent: &EnvDeclBuilder, f: &Expr) -> Expr {
        Expr::apps(
            self.exists_c.clone(),
            [self.nnrat.clone(), self.bounded_pred(parent, f)],
        )
    }
    /// `∀ n, NNRat.le (f n) B` — the bound hypothesis hB's type, at witness B.
    fn bound_hyp_at(&self, parent: &EnvDeclBuilder, f: &Expr, big_b: &Expr) -> Expr {
        let mut ib = EnvDeclBuilder::child_of(parent);
        let (n_id, n) = ib.fresh_local(self.nat.clone());
        let nle = Expr::apps(
            Expr::const_(Name::from_string("NNRat.le"), vec![]),
            [self.at(f, &n), big_b.clone()],
        );
        ib.finish_child(ib.mk_pi(n_id, BinderInfo::Default, self.nat.clone(), nle))
    }
    /// `pred_at f δ cap` = `∀ m n, cap≤m → cap≤n → bound_pair (vf m)(vf n) δ`.
    fn pred_at(&self, parent: &EnvDeclBuilder, f: &Expr, eps: &Expr, cap: &Expr) -> Expr {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (m_id, m) = bn.fresh_local(self.nat.clone());
        let (n_id, n) = bn.fresh_local(self.nat.clone());
        let hle_m = self.nat_le(cap.clone(), m.clone());
        let (hlem_id, _) = bn.fresh_local(hle_m.clone());
        let hle_n = self.nat_le(cap.clone(), n.clone());
        let (hlen_id, _) = bn.fresh_local(hle_n.clone());
        let concl = self.bound_pair(self.vat(f, &m), self.vat(f, &n), eps.clone());
        let e = bn.mk_pi(hlen_id, BinderInfo::Default, hle_n, concl);
        let e = bn.mk_pi(hlem_id, BinderInfo::Default, hle_m, e);
        let e = bn.mk_pi(n_id, BinderInfo::Default, self.nat.clone(), e);
        let e = bn.mk_pi(m_id, BinderInfo::Default, self.nat.clone(), e);
        bn.finish_child(e)
    }
    /// `∃ N, pred_at f δ N` (the IsCauchy result type at tolerance δ).
    fn exists_pred(&self, parent: &EnvDeclBuilder, f: &Expr, eps: &Expr) -> Expr {
        let pred = {
            let mut bn = EnvDeclBuilder::child_of(parent);
            let (cap_id, cap) = bn.fresh_local(self.nat.clone());
            let body = self.pred_at(&bn, f, eps, &cap);
            bn.finish_child(bn.mk_lam(cap_id, BinderInfo::Default, self.nat.clone(), body))
        };
        Expr::apps(self.exists_c.clone(), [self.nat.clone(), pred])
    }
    fn pred_lambda(&self, parent: &EnvDeclBuilder, f: &Expr, eps: &Expr) -> Expr {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (cap_id, cap) = bn.fresh_local(self.nat.clone());
        let body = self.pred_at(&bn, f, eps, &cap);
        bn.finish_child(bn.mk_lam(cap_id, BinderInfo::Default, self.nat.clone(), body))
    }
}

impl Environment {
    /// Register `NNReal.IsCauchy_mul`. Idempotent.
    pub fn init_algebra_nnreal_mul_op(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_cauchy()?; // IsCauchy, CauSeq, NNRat.*
        self.init_algebra_nnreal_bounded()?; // IsCauchy_bounded
        self.init_algebra_rat_delta_choice()?; // deltaMul, deltaMul_pos, deltaMul_mul_eq
        self.init_algebra_rat_mul_close()?; // mul_close_of_close + the order/field surface
        self.register_nat_minmax_proofs()?; // Nat.max, Nat.le_max_left/right
        self.register_nat_le_trans_proof()?; // Nat.le_trans
                                             // val_mul lives in NNRat (already via cauchy), order/iff via mul_close.
        self.register_rat_order_proofs()?; // Rat.zero_lt_one, le_refl
        self.init_exists()?;

        let c = IsCauchyMulConsts::new();
        self.register_nnreal_is_cauchy_mul(&c)
    }

    fn register_nnreal_is_cauchy_mul(&mut self, c: &IsCauchyMulConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.IsCauchy_mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.seq_ty());
            let (g_id, g) = b.fresh_local(c.seq_ty());
            let hf = c.is_cauchy(f.clone());
            let (hf_id, _) = b.fresh_local(hf.clone());
            let hg = c.is_cauchy(g.clone());
            let (hg_id, _) = b.fresh_local(hg.clone());
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

/// Build the proof term for `NNReal.IsCauchy_mul`.
fn build_is_cauchy_mul_proof(c: &IsCauchyMulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (f_id, f) = b.fresh_local(c.seq_ty());
    let (g_id, g) = b.fresh_local(c.seq_ty());
    let hf_ty = c.is_cauchy(f.clone());
    let (hf_id, hf) = b.fresh_local(hf_ty.clone());
    let hg_ty = c.is_cauchy(g.clone());
    let (hg_id, hg) = b.fresh_local(hg_ty.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.rlt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

    let prod = c.prod_seq(&b, &f, &g);
    // Goal: IsCauchy prod, but we are already under (ε, hpos), so the goal of
    // the bound elims is `∃ N, pred_at prod ε N`.
    let goal_exists = c.exists_pred(&b, &prod, &eps);

    // IsCauchy_bounded f hf : ∃ Bf, ∀ n, NNRat.le (f n) Bf.
    let exists_bf = Expr::apps(c.is_cauchy_bounded.clone(), [f.clone(), hf.clone()]);
    let exists_bg = Expr::apps(c.is_cauchy_bounded.clone(), [g.clone(), hg.clone()]);
    let pred_bf = c.bounded_pred(&b, &f);
    let pred_bg = c.bounded_pred(&b, &g);

    // elim over Bf.
    let elim_bf = {
        let mut bf = EnvDeclBuilder::child_of(&b);
        let (big_bf_id, big_bf) = bf.fresh_local(c.nnrat.clone());
        let hbf_ty = c.bound_hyp_at(&bf, &f, &big_bf);
        let (hbf_id, hbf) = bf.fresh_local(hbf_ty.clone());

        // elim over Bg.
        let elim_bg = {
            let mut bg = EnvDeclBuilder::child_of(&bf);
            let (big_bg_id, big_bg) = bg.fresh_local(c.nnrat.clone());
            let hbg_ty = c.bound_hyp_at(&bg, &g, &big_bg);
            let (hbg_id, hbg) = bg.fresh_local(hbg_ty.clone());

            let bfr = c.val(big_bf.clone()); // Bfr = val Bf
            let bgr = c.val(big_bg.clone()); // Bgr = val Bg
            let bf_bg = c.radd(bfr.clone(), bgr.clone()); // Bfr+Bgr
            let big_d = c.radd(bf_bg.clone(), c.rat_one.clone()); // D = (Bfr+Bgr)+1
            let delta = c.delta(&eps, &big_d);
            let half_eps = c.half(eps.clone());

            // 0≤Bfr, 0≤Bgr via NNRat.property.
            let h0bfr = c.property(big_bf.clone());
            let h0bgr = c.property(big_bg.clone());

            // h0_bfbg : 0 ≤ Bfr+Bgr.  add_le_add 0 Bfr 0 Bgr h0bfr h0bgr : 0+0 ≤ Bfr+Bgr;
            //   transport 0+0 → 0 via zero_add 0.
            let h0bfbg = {
                let step = c.add_le_add(
                    c.rat_zero.clone(),
                    bfr.clone(),
                    c.rat_zero.clone(),
                    bgr.clone(),
                    h0bfr.clone(),
                    h0bgr.clone(),
                );
                let zz = c.radd(c.rat_zero.clone(), c.rat_zero.clone());
                let motive = {
                    let mut m = EnvDeclBuilder::child_of(&bg);
                    let (t_id, t) = m.fresh_local(c.rat.clone());
                    let body = c.rle(t, bf_bg.clone());
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

            // bfbg_lt_D : Bfr+Bgr < D.  add_lt_add_left 0 1 (Bfr+Bgr) zero_lt_one :
            //   (Bfr+Bgr)+0 < (Bfr+Bgr)+1 ; transport LHS (Bfr+Bgr)+0 → Bfr+Bgr.
            let bfbg_lt_d = {
                let raw = c.add_lt_add_left(
                    c.rat_zero.clone(),
                    c.rat_one.clone(),
                    bf_bg.clone(),
                    c.rat_zero_lt_one.clone(),
                );
                let bfbg_plus_zero = c.radd(bf_bg.clone(), c.rat_zero.clone());
                let motive = {
                    let mut m = EnvDeclBuilder::child_of(&bg);
                    let (t_id, t) = m.fresh_local(c.rat.clone());
                    let body = c.rlt(t, big_d.clone());
                    m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                c.subst(
                    motive,
                    bfbg_plus_zero,
                    bf_bg.clone(),
                    c.add_zero(bf_bg.clone()),
                    raw,
                )
            };

            // h0D : 0 < D := lt_of_le_of_lt 0 (Bfr+Bgr) D h0bfbg bfbg_lt_D.
            let h0d = c.lt_of_le_of_lt(
                c.rat_zero.clone(),
                bf_bg.clone(),
                big_d.clone(),
                h0bfbg,
                bfbg_lt_d,
            );

            // hDne : D = 0 → False  (from h0d : 0<D).
            let hdne = {
                let mut nb = EnvDeclBuilder::child_of(&bg);
                let hd0_ty = c.eq_ty(big_d.clone(), c.rat_zero.clone());
                let (hd0_id, hd0) = nb.fresh_local(hd0_ty.clone());
                // 0<0 := subst (motive t := 0<t) D 0 hd0 h0d.
                let motive = {
                    let mut m = EnvDeclBuilder::child_of(&nb);
                    let (t_id, t) = m.fresh_local(c.rat.clone());
                    let body = c.rlt(c.rat_zero.clone(), t);
                    m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let lt00 = c.subst(motive, big_d.clone(), c.rat_zero.clone(), hd0, h0d.clone());
                // ¬(0≤0) := And.right (Iff.mp (lt_iff 0 0) lt00).
                let le00 = c.rle(c.rat_zero.clone(), c.rat_zero.clone());
                let not_le00 = Expr::app(c.not_c.clone(), le00.clone());
                let and00 = Expr::apps(c.and_c.clone(), [le00.clone(), not_le00.clone()]);
                let lt00ty = c.rlt(c.rat_zero.clone(), c.rat_zero.clone());
                let iff00 = Expr::apps(
                    c.rat_lt_iff_le_not_le.clone(),
                    [c.rat_zero.clone(), c.rat_zero.clone()],
                );
                let mp00 = Expr::apps(c.iff_mp.clone(), [lt00ty, and00, iff00, lt00]);
                let not_le00_pf = c.and_right(le00.clone(), not_le00, mp00);
                // le_refl 0 : 0≤0.
                let refl00 = c.le_refl(c.rat_zero.clone());
                let false_pf = Expr::app(not_le00_pf, refl00);
                nb.finish_child(nb.mk_lam(hd0_id, BinderInfo::Default, hd0_ty, false_pf))
            };

            // hδpos : 0<δ := deltaMul_pos ε D hpos h0d.
            let hdelta_pos = Expr::apps(
                c.rat_deltamul_pos.clone(),
                [eps.clone(), big_d.clone(), hpos.clone(), h0d],
            );
            // h0δ : 0≤δ.
            let h0delta = c.le_of_lt(c.rat_zero.clone(), delta.clone(), hdelta_pos.clone());

            // hδD : δ·D = ε/2 := deltaMul_mul_eq ε D hDne.
            let hdelta_d = Expr::apps(
                c.rat_deltamul_mul_eq.clone(),
                [eps.clone(), big_d.clone(), hdne],
            );

            // hbudget : δ·(Bfr+Bgr) ≤ ε/2.
            //   mul_le_left δ (Bfr+Bgr) D (Bfr+Bgr ≤ D) h0δ : δ·(Bfr+Bgr) ≤ δ·D.
            //   transport RHS δ·D → ε/2 via hδD.
            let hbudget = {
                // Bfr+Bgr ≤ D := le_of_lt of bfbg_lt_D? we consumed it; rebuild.
                // Use bfbg_le_D : (Bfr+Bgr)+0 ≤ (Bfr+Bgr)+1 via add_le_add refl + zero_le_one,
                //   transport LHS via add_zero.
                let bfbg_le_d = {
                    let raw = c.add_le_add(
                        bf_bg.clone(),
                        bf_bg.clone(),
                        c.rat_zero.clone(),
                        c.rat_one.clone(),
                        c.le_refl(bf_bg.clone()),
                        c.rat_zero_le_one.clone(),
                    );
                    let bfbg_plus_zero = c.radd(bf_bg.clone(), c.rat_zero.clone());
                    let motive = {
                        let mut m = EnvDeclBuilder::child_of(&bg);
                        let (t_id, t) = m.fresh_local(c.rat.clone());
                        let body = c.rle(t, big_d.clone());
                        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                    };
                    c.subst(
                        motive,
                        bfbg_plus_zero,
                        bf_bg.clone(),
                        c.add_zero(bf_bg.clone()),
                        raw,
                    )
                };
                let prod_le = c.mul_le_left(
                    delta.clone(),
                    bf_bg.clone(),
                    big_d.clone(),
                    bfbg_le_d,
                    h0delta.clone(),
                ); // δ·(Bfr+Bgr) ≤ δ·D
                let delta_d = c.rmul(delta.clone(), big_d.clone());
                let delta_bfbg = c.rmul(delta.clone(), bf_bg.clone());
                let motive = {
                    let mut m = EnvDeclBuilder::child_of(&bg);
                    let (t_id, t) = m.fresh_local(c.rat.clone());
                    let body = c.rle(delta_bfbg.clone(), t);
                    m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                c.subst(motive, delta_d, half_eps.clone(), hdelta_d, prod_le)
            };

            // hf δ hδpos : ∃ Nf, pred_at f δ Nf ; hg δ hδpos : ∃ Ng, pred_at g δ Ng.
            let exists_nf = Expr::apps(hf.clone(), [delta.clone(), hdelta_pos.clone()]);
            let exists_ng = Expr::apps(hg.clone(), [delta.clone(), hdelta_pos]);
            let pred_f = c.pred_lambda(&bg, &f, &delta);
            let pred_g = c.pred_lambda(&bg, &g, &delta);

            // elim over Nf.
            let elim_nf = {
                let mut bo = EnvDeclBuilder::child_of(&bg);
                let (nf_id, nf) = bo.fresh_local(c.nat.clone());
                let hnf_ty = c.pred_at(&bo, &f, &delta, &nf);
                let (hnf_id, hnf) = bo.fresh_local(hnf_ty.clone());

                // elim over Ng.
                let elim_ng = {
                    let mut bi = EnvDeclBuilder::child_of(&bo);
                    let (ng_id, ng) = bi.fresh_local(c.nat.clone());
                    let hng_ty = c.pred_at(&bi, &g, &delta, &ng);
                    let (hng_id, hng) = bi.fresh_local(hng_ty.clone());

                    let nmax = Expr::apps(c.nat_max.clone(), [nf.clone(), ng.clone()]);

                    let witness = build_witness(
                        c, &bi, &f, &g, &prod, &eps, &delta, &bfr, &bgr, &hbudget, &h0delta, &hpos,
                        &hbf, &hbg, &nf, &ng, &nmax, &hnf, &hng,
                    );

                    let pred_prod = c.pred_lambda(&bi, &prod, &eps);
                    let intro = Expr::apps(
                        c.exists_intro.clone(),
                        [c.nat.clone(), pred_prod, nmax, witness],
                    );
                    let e = bi.mk_lam(hng_id, BinderInfo::Default, hng_ty, intro);
                    let e = bi.mk_lam(ng_id, BinderInfo::Default, c.nat.clone(), e);
                    bi.finish_child(e)
                };

                let elim_g = Expr::apps(
                    c.exists_elim.clone(),
                    [
                        c.nat.clone(),
                        pred_g.clone(),
                        goal_exists.clone(),
                        exists_ng,
                        elim_ng,
                    ],
                );
                let e = bo.mk_lam(hnf_id, BinderInfo::Default, hnf_ty, elim_g);
                let e = bo.mk_lam(nf_id, BinderInfo::Default, c.nat.clone(), e);
                bo.finish_child(e)
            };

            let elim_f = Expr::apps(
                c.exists_elim.clone(),
                [
                    c.nat.clone(),
                    pred_f.clone(),
                    goal_exists.clone(),
                    exists_nf,
                    elim_nf,
                ],
            );
            let e = bg.mk_lam(hbg_id, BinderInfo::Default, hbg_ty, elim_f);
            let e = bg.mk_lam(big_bg_id, BinderInfo::Default, c.nnrat.clone(), e);
            bg.finish_child(e)
        };

        // Exists.elim Bg.
        let elim = Expr::apps(
            c.exists_elim.clone(),
            [
                c.nnrat.clone(),
                pred_bg.clone(),
                goal_exists.clone(),
                exists_bg,
                elim_bg,
            ],
        );
        let e = bf.mk_lam(hbf_id, BinderInfo::Default, hbf_ty, elim);
        let e = bf.mk_lam(big_bf_id, BinderInfo::Default, c.nnrat.clone(), e);
        bf.finish_child(e)
    };

    // Exists.elim Bf.
    let elim_outer = Expr::apps(
        c.exists_elim.clone(),
        [
            c.nnrat.clone(),
            pred_bf.clone(),
            goal_exists,
            exists_bf,
            elim_bf,
        ],
    );

    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, elim_outer);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(hg_id, BinderInfo::Default, hg_ty, e);
    let e = b.mk_lam(hf_id, BinderInfo::Default, hf_ty, e);
    let e = b.mk_lam(g_id, BinderInfo::Default, c.seq_ty(), e);
    let e = b.mk_lam(f_id, BinderInfo::Default, c.seq_ty(), e);
    b.finish(e)
}

/// Build the inner witness `∀ m n, N≤m → N≤n →
///   bound_pair (val(prod m))(val(prod n)) ε`.
#[allow(clippy::too_many_arguments)]
fn build_witness(
    c: &IsCauchyMulConsts,
    parent: &EnvDeclBuilder,
    f: &Expr,
    g: &Expr,
    _prod: &Expr,
    eps: &Expr,
    delta: &Expr,
    bfr: &Expr,
    bgr: &Expr,
    hbudget: &Expr,
    h0delta: &Expr,
    hpos: &Expr,
    hbf: &Expr,
    hbg: &Expr,
    nf: &Expr,
    ng: &Expr,
    nmax: &Expr,
    hnf: &Expr,
    hng: &Expr,
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

    // base_f : bound_pair (vf m)(vf n) δ := hnf m n nf_le_m nf_le_n.
    let base_f = Expr::apps(hnf.clone(), [m.clone(), n.clone(), nf_le_m, nf_le_n]);
    let base_g = Expr::apps(hng.clone(), [m.clone(), n.clone(), ng_le_m, ng_le_n]);

    let vfm = c.vat(f, &m);
    let vfn = c.vat(f, &n);
    let vgm = c.vat(g, &m);
    let vgn = c.vat(g, &n);

    // Conjuncts of base_f / base_g.
    let lf = c.rlt(vfm.clone(), c.radd(vfn.clone(), delta.clone()));
    let rf = c.rlt(vfn.clone(), c.radd(vfm.clone(), delta.clone()));
    let lg = c.rlt(vgm.clone(), c.radd(vgn.clone(), delta.clone()));
    let rg = c.rlt(vgn.clone(), c.radd(vgm.clone(), delta.clone()));
    // vfm < vfn+δ, vfn < vfm+δ, vgm < vgn+δ, vgn < vgm+δ.
    let lt_fm_fn = c.and_left(lf.clone(), rf.clone(), base_f.clone());
    let lt_fn_fm = c.and_right(lf, rf, base_f);
    let lt_gm_gn = c.and_left(lg.clone(), rg.clone(), base_g.clone());
    let lt_gn_gm = c.and_right(lg, rg, base_g);
    // Closeness le forms.
    let cle_fm_fn = c.le_of_lt(vfm.clone(), c.radd(vfn.clone(), delta.clone()), lt_fm_fn); // vfm ≤ vfn+δ
    let cle_fn_fm = c.le_of_lt(vfn.clone(), c.radd(vfm.clone(), delta.clone()), lt_fn_fm); // vfn ≤ vfm+δ
    let cle_gm_gn = c.le_of_lt(vgm.clone(), c.radd(vgn.clone(), delta.clone()), lt_gm_gn); // vgm ≤ vgn+δ
    let cle_gn_gm = c.le_of_lt(vgn.clone(), c.radd(vgm.clone(), delta.clone()), lt_gn_gm); // vgn ≤ vgm+δ

    // Nonneg of all vals (NNRat.property of (f m), etc).
    let h0fm = c.property(c.at(f, &m));
    let h0fn = c.property(c.at(f, &n));
    let h0gm = c.property(c.at(g, &m));
    let h0gn = c.property(c.at(g, &n));

    // Bounds: vfm ≤ Bfr := hbf m ; vfn ≤ Bfr := hbf n ; vgm ≤ Bgr := hbg m ; vgn ≤ Bgr := hbg n.
    //   hbf m : NNRat.le (f m) Bf  ≡  Rat.le (vf m) Bfr.
    let bnd_fm = Expr::app(hbf.clone(), m.clone());
    let bnd_fn = Expr::app(hbf.clone(), n.clone());
    let bnd_gm = Expr::app(hbg.clone(), m.clone());
    let bnd_gn = Expr::app(hbg.clone(), n.clone());

    // FORWARD: vfm·vgm < vfn·vgn + ε.
    //   mul_close_of_close vfm vfn vgm vgn Bfr Bgr ε δ
    //     h0fm h0gm h0gn h0δ  (a=vfm, b=vgm, b'=vgn)  -- wait map below
    //     (vfm≤Bfr)(vgn≤Bgr)(vfm≤vfn+δ)(vgm≤vgn+δ) hbudget hpos.
    // Mapping: a=vfm, a'=vfn, b=vgm, b'=vgn, Ba=Bfr, Bb=Bgr.
    //   0≤a=0≤vfm=h0fm ; 0≤b=0≤vgm=h0gm ; 0≤b'=0≤vgn=h0gn ; 0≤δ=h0δ
    //   a≤Ba = vfm≤Bfr = bnd_fm ; b'≤Bb = vgn≤Bgr = bnd_gn
    //   a≤a'+δ = vfm≤vfn+δ = cle_fm_fn ; b≤b'+δ = vgm≤vgn+δ = cle_gm_gn.
    let fwd = Expr::apps(
        c.rat_mul_close.clone(),
        [
            vfm.clone(),
            vfn.clone(),
            vgm.clone(),
            vgn.clone(),
            bfr.clone(),
            bgr.clone(),
            eps.clone(),
            delta.clone(),
            h0fm.clone(),
            h0gm.clone(),
            h0gn.clone(),
            h0delta.clone(),
            bnd_fm.clone(),
            bnd_gn.clone(),
            cle_fm_fn,
            cle_gm_gn,
            hbudget.clone(),
            hpos.clone(),
        ],
    );

    // REVERSE: vfn·vgn < vfm·vgm + ε.
    //   mapping: a=vfn, a'=vfm, b=vgn, b'=vgm, Ba=Bfr, Bb=Bgr.
    //   0≤a=h0fn ; 0≤b=h0gn ; 0≤b'=h0gm ; 0≤δ
    //   a≤Ba = vfn≤Bfr = bnd_fn ; b'≤Bb = vgm≤Bgr = bnd_gm
    //   a≤a'+δ = vfn≤vfm+δ = cle_fn_fm ; b≤b'+δ = vgn≤vgm+δ = cle_gn_gm.
    let rev = Expr::apps(
        c.rat_mul_close.clone(),
        [
            vfn.clone(),
            vfm.clone(),
            vgn.clone(),
            vgm.clone(),
            bfr.clone(),
            bgr.clone(),
            eps.clone(),
            delta.clone(),
            h0fn,
            h0gn,
            h0gm,
            h0delta.clone(),
            bnd_fn,
            bnd_gm,
            cle_fn_fm,
            cle_gn_gm,
            hbudget.clone(),
            hpos.clone(),
        ],
    );

    // Transport endpoints vfx·vgx → val(prod x) via symm (val_mul (f x)(g x)).
    //   val(prod m) ≡ val(NNRat.mul (f m)(g m)) (prod m reduces);
    //   val_mul (f m)(g m) : val(mul..) = vfm·vgm.  symm → vfm·vgm = val(prod m).
    let vfm_vgm = c.rmul(vfm.clone(), vgm.clone());
    let vfn_vgn = c.rmul(vfn.clone(), vgn.clone());
    let vprod_m = c.val(c.nnmul(c.at(f, &m), c.at(g, &m)));
    let vprod_n = c.val(c.nnmul(c.at(f, &n), c.at(g, &n)));
    let valmul_m = c.val_mul(c.at(f, &m), c.at(g, &m)); // val(prod m) = vfm·vgm
    let valmul_n = c.val_mul(c.at(f, &n), c.at(g, &n)); // val(prod n) = vfn·vgn

    // forward final: vprod_m < vprod_n + ε.
    //   step1 rewrite RHS summand vfn·vgn → vprod_n via symm valmul_n.
    let mfwd_rhs = {
        let mut m = EnvDeclBuilder::child_of(&bw);
        let (t_id, t) = m.fresh_local(c.rat.clone());
        let body = c.rlt(vfm_vgm.clone(), c.radd(t, eps.clone()));
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let fwd1 = c.subst(
        mfwd_rhs,
        vfn_vgn.clone(),
        vprod_n.clone(),
        c.eq_symm(vprod_n.clone(), vfn_vgn.clone(), valmul_n.clone()),
        fwd,
    );
    let mfwd_lhs = {
        let mut m = EnvDeclBuilder::child_of(&bw);
        let (t_id, t) = m.fresh_local(c.rat.clone());
        let body = c.rlt(t, c.radd(vprod_n.clone(), eps.clone()));
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let fwd_final = c.subst(
        mfwd_lhs,
        vfm_vgm.clone(),
        vprod_m.clone(),
        c.eq_symm(vprod_m.clone(), vfm_vgm.clone(), valmul_m.clone()),
        fwd1,
    );

    // reverse final: vprod_n < vprod_m + ε.
    let mrev_rhs = {
        let mut m = EnvDeclBuilder::child_of(&bw);
        let (t_id, t) = m.fresh_local(c.rat.clone());
        let body = c.rlt(vfn_vgn.clone(), c.radd(t, eps.clone()));
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let rev1 = c.subst(
        mrev_rhs,
        vfm_vgm.clone(),
        vprod_m.clone(),
        c.eq_symm(vprod_m.clone(), vfm_vgm.clone(), valmul_m),
        rev,
    );
    let mrev_lhs = {
        let mut m = EnvDeclBuilder::child_of(&bw);
        let (t_id, t) = m.fresh_local(c.rat.clone());
        let body = c.rlt(t, c.radd(vprod_m.clone(), eps.clone()));
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let rev_final = c.subst(
        mrev_lhs,
        vfn_vgn.clone(),
        vprod_n.clone(),
        c.eq_symm(vprod_n.clone(), vfn_vgn.clone(), valmul_n),
        rev1,
    );

    let l_final = c.rlt(vprod_m.clone(), c.radd(vprod_n.clone(), eps.clone()));
    let r_final = c.rlt(vprod_n.clone(), c.radd(vprod_m.clone(), eps.clone()));
    let proof = c.and_intro(l_final, r_final, fwd_final, rev_final);

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
        env.init_algebra_nnreal_mul_op()
            .expect("init_algebra_nnreal_mul_op");
        env.init_algebra_nnreal_mul_op().expect("idempotent");

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
