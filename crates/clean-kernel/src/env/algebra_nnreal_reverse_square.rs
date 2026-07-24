// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — the Archimedean REVERSE-order keystone
//! `NNReal.le_of_forall_lt_add` + the routine de-square carrier algebra
//! (`NNReal.ofRat_mul`, `NNReal.mul_comm`, `NNReal.mul_assoc`,
//! `NNReal.mul_le_mul_left`).
//!
//! # Why this module exists
//!
//! `algebra_nnreal_le.rs` lands the FORWARD `ofRat` order bridge
//! (`NNReal.ofRat_le_ofRat`) but explicitly names the UNBUILT blocker: the
//! Archimedean REVERSE bridge `le_of_forall_lt_add`. The de-square
//! (`W² ≤ 16·Inf³` over Rat ⟹ `W ≤ 4·Inf^{3/2}` over NNReal) needs exactly
//! this reverse step plus a small amount of multiplicative carrier algebra.
//!
//! # `NNReal.le_of_forall_lt_add` (the keystone — fully constructive)
//!
//! ```text
//!   ∀ a b : NNReal,
//!     (∀ e : Rat, Rat.lt 0 e → NNReal.le a (NNReal.add b (NNReal.ofRat e (le_of_lt e))))
//!       → NNReal.le a b
//! ```
//!
//! The genuine completeness/antisymmetry content. The proof is DIRECT, not by
//! contradiction: route `a`,`b` through nested `Quot.ind` to reps `f`,`g`. The
//! goal `CauSeq.le f g` is `∀ ε>0 ∃N ∀n≥N, vf n < vg n + ε`. For a fixed `ε`,
//! instantiate the hypothesis at `e := ε/2` (positive, `Rat.half_pos`), obtaining
//! `NNReal.le (mk f) (add (mk g) (ofRat (ε/2)))`, which ι-reduces to
//! `CauSeq.le f (CauSeq.add g (const (NNRat.ofRat (ε/2))))`; its body at index `n`
//! is `vf n < (vg n + ε/2) + ε'` (the `val_add`/`const` projections fire
//! DEFINITIONALLY). Instantiating its inner tolerance `ε'` at `ε/2` and choosing
//! `N` from that existential, at each `n ≥ N` we have
//! `vf n < (vg n + ε/2) + ε/2 = vg n + ε` (associativity + `add_halves`,
//! the `eq_recombine` reshuffle), which is exactly the goal body. No limit
//! argument, no classical step: the `+e` slack supplied by the hypothesis is
//! split into the two halves.
//!
//! # Carrier algebra (de-square also needs these)
//!
//! - `NNReal.ofRat_mul : ∀ a b ha hb hab,
//!     mul (ofRat a ha)(ofRat b hb) = ofRat (Rat.mul a b) hab` — `Quot.sound` on
//!   the constant-sequence `Equiv` (both vals ι-reduce to `a·b`), mirroring
//!   `NNReal.ofRat_add`.
//! - `NNReal.mul_comm : ∀ a b, mul a b = mul b a` — `Quot.ind`² + `Quot.sound`
//!   on the per-index `NNRat.val_mul` + `Rat.mul_comm` equality.
//! - `NNReal.mul_assoc : ∀ a b c, mul a (mul b c) = mul (mul a b) c` —
//!   `Quot.ind`³ + `Quot.sound` on `Rat.mul_assoc`.
//! - `NNReal.mul_le_mul_left : ∀ a c d, NNReal.le c d → NNReal.le (mul a c)(mul a d)`
//!   — `Quot.ind`³ reducing to a `CauSeq`-level lemma that bounds
//!   `vf·vc < vf·vd + ε` via the shared-factor bound (`IsCauchy_bounded`) and the
//!   δ-band (`Rat.mul_close_of_close`-style cross estimate), mirroring
//!   `IsCauchy_mul`.
//!
//! `Declaration::Theorem`/`Definition`, `ProofQuality::Constructive`, empty
//! admitted-axiom closure (foundational only). NO `sorry` / `add_decl_unchecked`
//! / `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the reverse-order keystone.
pub(crate) struct RevSqConsts {
    prop: Expr,
    nat: Expr,
    nat_zero: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_two: Expr,
    nnrat: Expr,
    nnrat_val: Expr,
    nnrat_of_rat: Expr,
    causeq: Expr,
    causeq_seq: Expr,
    causeq_equiv: Expr,
    causeq_le: Expr,
    causeq_add: Expr,
    causeq_const: Expr,
    rat_add: Expr,
    rat_div: Expr,
    rat_lt: Expr,
    rat_le: Expr,
    nat_le: Expr,
    // Rat order/field lemmas.
    rat_half_pos: Expr,
    rat_add_assoc: Expr,
    rat_add_halves: Expr,
    rat_add_zero: Expr,
    rat_add_lt_add_left: Expr,
    rat_lt_iff_le_not_le: Expr,
    not_c: Expr,
    and_c: Expr,
    and_left: Expr,
    iff_mp: Expr,
    // Logic: Exists.* at level 1, Eq.{1}, congrArg.
    exists_c: Expr,
    exists_intro: Expr,
    exists_elim: Expr,
    eq_trans: Expr,
    eq_subst: Expr,
    congr_arg: Expr,
    // Quot machinery at level 1.
    quot: Expr,
    quot_mk: Expr,
}

impl RevSqConsts {
    pub(crate) fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_two: k("Rat.two"),
            nnrat: k("NNRat"),
            nnrat_val: k("NNRat.val"),
            nnrat_of_rat: k("NNRat.ofRat"),
            causeq: k("NNReal.CauSeq"),
            causeq_seq: k("NNReal.CauSeq.seq"),
            causeq_equiv: k("NNReal.CauSeq.Equiv"),
            causeq_le: k("NNReal.CauSeq.le"),
            causeq_add: k("NNReal.CauSeq.add"),
            causeq_const: k("NNReal.CauSeq.const"),
            rat_add: k("Rat.add"),
            rat_div: k("Rat.div"),
            rat_lt: k("Rat.lt"),
            rat_le: k("Rat.le"),
            nat_le: k("Nat.le"),
            rat_half_pos: k("Rat.half_pos"),
            rat_add_assoc: k("Rat.add_assoc"),
            rat_add_halves: k("Rat.add_halves"),
            rat_add_zero: k("Rat.add_zero"),
            rat_add_lt_add_left: k("Rat.add_lt_add_left"),
            rat_lt_iff_le_not_le: k("Rat.lt_iff_le_not_le"),
            not_c: k("Not"),
            and_c: k("And"),
            and_left: k("And.left"),
            iff_mp: k("Iff.mp"),
            exists_c: Expr::const_(Name::from_string("Exists"), vec![lvl1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![lvl1.clone()]),
            exists_elim: Expr::const_(Name::from_string("Exists.elim"), vec![lvl1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![lvl1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1.clone()]),
            congr_arg: Expr::const_(
                Name::from_string("congrArg"),
                vec![lvl1.clone(), lvl1.clone()],
            ),
            quot: Expr::const_(Name::from_string("Quot"), vec![lvl1.clone()]),
            quot_mk: Expr::const_(Name::from_string("Quot.mk"), vec![lvl1]),
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
    fn rle(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    /// `NNRat.val (NNReal.CauSeq.seq x n) : Rat`.
    fn vseq(&self, x: &Expr, n: &Expr) -> Expr {
        let seq = Expr::app(self.causeq_seq.clone(), x.clone());
        let at = Expr::app(seq, n.clone());
        Expr::app(self.nnrat_val.clone(), at)
    }
    /// `NNReal.CauSeq.le a b : Prop`.
    fn causeq_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_le.clone(), [a, b])
    }
    /// The one-sided domination at index `m`: `vseq a m < vseq b m + ε`.
    fn dom(&self, a: &Expr, bb: &Expr, m: &Expr, eps: &Expr) -> Expr {
        self.lt(self.vseq(a, m), self.add(self.vseq(bb, m), eps.clone()))
    }

    /// `∀ n, Nat.le N n → vseq a n < vseq b n + ε` (pred fully applied at `cap`).
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

    /// `Rat.add_assoc a b c : Eq Rat ((a+b)+c)(a+(b+c))`.
    fn add_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_add_assoc.clone(), [a, b, cc])
    }
    /// `Rat.add_halves eps : Eq Rat ((eps/2)+(eps/2)) eps`.
    fn add_halves(&self, eps: Expr) -> Expr {
        Expr::app(self.rat_add_halves.clone(), eps)
    }
    /// `Rat.add_zero a : Eq Rat (Rat.add a Rat.zero) a`.
    fn add_zero(&self, a: Expr) -> Expr {
        Expr::app(self.rat_add_zero.clone(), a)
    }
    /// `Rat.add_lt_add_left a b c h : (c+a) < (c+b)`.
    fn add_lt_add_left(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_add_lt_add_left.clone(), [a, b, cc, h])
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

    /// `eq_recombine vx eps : Eq Rat ((vx + eps/2) + eps/2) (vx + eps)`.
    /// `(vx+ε/2)+ε/2 = vx+(ε/2+ε/2)` (add_assoc) `= vx+ε` (congrArg add_halves).
    fn eq_recombine(&self, parent: &EnvDeclBuilder, vx: &Expr, eps: &Expr) -> Expr {
        let half = self.half(eps.clone());
        let assoc = self.add_assoc(vx.clone(), half.clone(), half.clone());
        let half_pair = self.add(half.clone(), half.clone());
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
        let lhs = self.add(self.add(vx.clone(), half.clone()), half);
        let mid = self.add(vx.clone(), half_pair);
        let rhs = self.add(vx.clone(), eps.clone());
        self.eq_trans(lhs, mid, rhs, assoc, congr)
    }

    /// `le_of_lt e : Rat.le 0 e` from `he : Rat.lt 0 e`
    /// via `And.left (Iff.mp (Rat.lt_iff_le_not_le 0 e) he)`.
    fn le_of_lt(&self, a: Expr, b: Expr, hlt: Expr) -> Expr {
        let le_ab = self.rle(a.clone(), b.clone());
        let not_le_ba = Expr::app(self.not_c.clone(), self.rle(b.clone(), a.clone()));
        let and_ty = Expr::apps(self.and_c.clone(), [le_ab.clone(), not_le_ba.clone()]);
        let lt_ab = self.lt(a.clone(), b.clone());
        let iff = Expr::apps(self.rat_lt_iff_le_not_le.clone(), [a, b]);
        let mp = Expr::apps(self.iff_mp.clone(), [lt_ab, and_ty, iff, hlt]);
        Expr::apps(self.and_left.clone(), [le_ab, not_le_ba, mp])
    }

    /// `NNReal := @Quot.{1} CauSeq Equiv`.
    fn nnreal(&self) -> Expr {
        Expr::apps(
            self.quot.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone()],
        )
    }
    /// `@Quot.mk.{1} CauSeq Equiv l : NNReal`.
    fn quot_mk(&self, l: Expr) -> Expr {
        Expr::apps(
            self.quot_mk.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone(), l],
        )
    }
    /// `NNReal.ofRat e (le_of_lt 0 e he) : NNReal` (the slack at a positive `e`).
    fn of_rat_of_pos(&self, e: &Expr, he: &Expr) -> Expr {
        let h_nn = self.le_of_lt(self.rat_zero.clone(), e.clone(), he.clone());
        Expr::apps(self.nnrat_of_rat_real(), [e.clone(), h_nn])
    }
    fn nnrat_of_rat_real(&self) -> Expr {
        Expr::const_(Name::from_string("NNReal.ofRat"), vec![])
    }
    /// `NNReal.add a b`.
    fn nn_add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("NNReal.add"), vec![]),
            [a, b],
        )
    }
    /// `NNReal.le a b`.
    fn nn_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("NNReal.le"), vec![]), [a, b])
    }
    /// `NNReal.CauSeq.add a b`.
    fn cau_add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_add.clone(), [a, b])
    }
    /// `NNReal.CauSeq.const (NNRat.ofRat e h_nn)` (the constant slack rep).
    fn const_of_pos(&self, e: &Expr, he: &Expr) -> Expr {
        let h_nn = self.le_of_lt(self.rat_zero.clone(), e.clone(), he.clone());
        let q = Expr::apps(self.nnrat_of_rat.clone(), [e.clone(), h_nn]);
        Expr::app(self.causeq_const.clone(), q)
    }
}

impl Environment {
    /// Register `NNReal.le_of_forall_lt_add` (+ its `CauSeq` core). Idempotent.
    pub fn init_algebra_nnreal_reverse_square(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_le()?; // CauSeq, CauSeq.le, NNReal.le (eps-form)
        self.init_algebra_nnreal_add()?; // NNReal.add, CauSeq.add
        self.init_algebra_rat_half_pos()?; // Rat.half_pos (+ add_halves, two)
        self.init_rat_field_inst()?; // Rat.add_assoc, Rat.add_zero
        self.register_rat_add_lt_add_left()?; // Rat.add_lt_add_left
        self.init_iff()?; // Iff.mp
        self.init_and()?; // And.left
        self.init_rat_linear_order()?; // Rat.lt_iff_le_not_le (linear order)
        self.init_exists()?;

        let c = RevSqConsts::new();
        self.register_causeq_le_of_forall_lt_add(&c)?;
        self.register_nnreal_le_of_forall_lt_add(&c)?;
        Ok(())
    }

    /// `NNReal.CauSeq.le_of_forall_lt_add : ∀ f g,
    ///     (∀ e : Rat, Rat.lt 0 e → CauSeq.le f (CauSeq.add g (const (NNRat.ofRat e (le_of_lt e)))))
    ///       → CauSeq.le f g`.
    ///
    /// The genuine analytic content at the representative level. For goal-`ε`
    /// take `e := ε/2`, instantiate the hypothesis there, then its inner
    /// tolerance at `ε/2`; the `+e` slack reduces (val_add/const projections,
    /// defeq) to `vg + ε/2`, and the eq_recombine reshuffle folds
    /// `(vg+ε/2)+ε/2 = vg+ε`.
    fn register_causeq_le_of_forall_lt_add(&mut self, c: &RevSqConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.CauSeq.le_of_forall_lt_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = build_causeq_keystone_type(c);
        let value = build_causeq_keystone_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.le_of_forall_lt_add : ∀ a b : NNReal,
    ///     (∀ e : Rat, Rat.lt 0 e → NNReal.le a (NNReal.add b (NNReal.ofRat e (le_of_lt e))))
    ///       → NNReal.le a b`. Nested `Quot.ind` reducing the leaf to the CauSeq core.
    fn register_nnreal_le_of_forall_lt_add(&mut self, c: &RevSqConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.le_of_forall_lt_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = build_nnreal_keystone_type(c);
        let value = build_nnreal_keystone_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// The hypothesis body `∀ e, 0<e → P(e)`, parametric in how `P(e)` is built from
/// `(e, he)` (CauSeq-form vs NNReal-form). Returns a Pi over `e` and `he`.
fn forall_pos_hyp(
    c: &RevSqConsts,
    parent: &EnvDeclBuilder,
    body_at: impl Fn(&EnvDeclBuilder, &Expr, &Expr) -> Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (e_id, e) = b.fresh_local(c.rat.clone());
    let hpos = c.lt(c.rat_zero.clone(), e.clone());
    let (he_id, he) = b.fresh_local(hpos.clone());
    let concl = body_at(&b, &e, &he);
    let e_pi = b.mk_pi(he_id, BinderInfo::Default, hpos, concl);
    let e_pi = b.mk_pi(e_id, BinderInfo::Default, c.rat.clone(), e_pi);
    b.finish_child(e_pi)
}

/// `∀ f g, (CauSeq hypothesis) → CauSeq.le f g`.
fn build_causeq_keystone_type(c: &RevSqConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (f_id, f) = b.fresh_local(c.causeq.clone());
    let (g_id, g) = b.fresh_local(c.causeq.clone());
    let hyp = forall_pos_hyp(c, &b, |bb, e, he| {
        let slack = c.const_of_pos(e, he);
        let g_plus = c.cau_add(g.clone(), slack);
        let _ = bb;
        c.causeq_le(f.clone(), g_plus)
    });
    let (hyp_id, _hyp) = b.fresh_local(hyp.clone());
    let concl = c.causeq_le(f.clone(), g.clone());
    let e = b.mk_pi(hyp_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(g_id, BinderInfo::Default, c.causeq.clone(), e);
    let e = b.mk_pi(f_id, BinderInfo::Default, c.causeq.clone(), e);
    b.finish(e)
}

/// The CauSeq keystone proof value.
fn build_causeq_keystone_value(c: &RevSqConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (f_id, f) = b.fresh_local(c.causeq.clone());
    let (g_id, g) = b.fresh_local(c.causeq.clone());
    let hyp_ty = forall_pos_hyp(c, &b, |bb, e, he| {
        let slack = c.const_of_pos(e, he);
        let g_plus = c.cau_add(g.clone(), slack);
        let _ = bb;
        c.causeq_le(f.clone(), g_plus)
    });
    let (hyp_id, hyp) = b.fresh_local(hyp_ty.clone());

    // goal: CauSeq.le f g = ∀ ε, 0<ε → ∃ N, ∀ n, N≤n → vf n < vg n + ε.
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.lt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

    let half = c.half(eps.clone());
    let heps2 = Expr::apps(c.rat_half_pos.clone(), [eps.clone(), hpos.clone()]);

    // The slack CauSeq at e := ε/2, and the augmented sequence g + slack.
    let slack = c.const_of_pos(&half, &heps2);
    let g_plus = c.cau_add(g.clone(), slack.clone());

    // hyp (ε/2) heps2 : CauSeq.le f (add g slack)
    //   = ∀ ε', 0<ε' → ∃ N, ∀ n, N≤n → vf n < val(seq (add g slack) n) + ε'.
    let hyp_at = Expr::apps(hyp.clone(), [half.clone(), heps2.clone()]);
    // Instantiate the inner tolerance ε' at ε/2 (positive via heps2 again).
    let exists_src = Expr::apps(hyp_at, [half.clone(), heps2]);

    // pred for the source exists: over (f, g_plus) at ε/2.
    let pred_src = c.pred_n(&b, &f, &g_plus, &half);
    // goal exists: over (f, g) at ε.
    let goal_exists = c.exists_pred(&b, &f, &g, &eps);

    let elim_fn = {
        let mut be = EnvDeclBuilder::child_of(&b);
        let (cap_id, cap) = be.fresh_local(c.nat.clone());
        let hn_ty = c.pred_n_at(&be, &f, &g_plus, &half, &cap);
        let (hn_id, hn) = be.fresh_local(hn_ty.clone());

        // witness with the SAME N=cap.
        let witness = {
            let mut bw = EnvDeclBuilder::child_of(&be);
            let (m_id, m) = bw.fresh_local(c.nat.clone());
            let hle_ty = c.nat_le(cap.clone(), m.clone());
            let (hle_id, hle) = bw.fresh_local(hle_ty.clone());

            // base : vf m < val(seq (add g slack) m) + ε/2 := hn m hle.
            // val(seq (add g slack) m) ≡ vg m + ε/2 DEFINITIONALLY (val_add/const).
            // So `base` has type defeq to `vf m < (vg m + ε/2) + ε/2`.
            let base = Expr::apps(hn.clone(), [m.clone(), hle]);

            let vf = c.vseq(&f, &m);
            let vg = c.vseq(&g, &m);
            // recombine ((vg+ε/2)+ε/2) = (vg+ε).
            let rec = c.eq_recombine(&bw, &vg, &eps);
            let vg_hh = c.add(c.add(vg.clone(), half.clone()), half.clone());
            let vg_eps = c.add(vg.clone(), eps.clone());
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&bw);
                let (t_id, t) = mb.fresh_local(c.rat.clone());
                let body = c.lt(vf.clone(), t);
                mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            // proof : vf m < vg m + ε.
            let proof = c.subst(motive, vg_hh, vg_eps, rec, base);

            let e = bw.mk_lam(hle_id, BinderInfo::Default, hle_ty, proof);
            let e = bw.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
            bw.finish_child(e)
        };

        let intro = Expr::apps(
            c.exists_intro.clone(),
            [
                c.nat.clone(),
                c.pred_n(&be, &f, &g, &eps),
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
    let e = b.mk_lam(hyp_id, BinderInfo::Default, hyp_ty, e);
    let e = b.mk_lam(g_id, BinderInfo::Default, c.causeq.clone(), e);
    let e = b.mk_lam(f_id, BinderInfo::Default, c.causeq.clone(), e);
    b.finish(e)
}

/// `∀ a b : NNReal, (NNReal hypothesis) → NNReal.le a b`.
fn build_nnreal_keystone_type(c: &RevSqConsts) -> Expr {
    let nnreal = c.nnreal();
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(nnreal.clone());
    let (bv_id, bv) = b.fresh_local(nnreal.clone());
    let hyp = forall_pos_hyp(c, &b, |bb, e, he| {
        let slack = c.of_rat_of_pos(e, he);
        let b_plus = c.nn_add(bv.clone(), slack);
        let _ = bb;
        c.nn_le(a.clone(), b_plus)
    });
    let (hyp_id, _hyp) = b.fresh_local(hyp.clone());
    let concl = c.nn_le(a.clone(), bv.clone());
    let e = b.mk_pi(hyp_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(bv_id, BinderInfo::Default, nnreal.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, nnreal.clone(), e);
    b.finish(e)
}

/// `NNReal.le_of_forall_lt_add` via nested `Quot.ind` reducing the leaf to the
/// `CauSeq` core. The motive over `a` carries the hypothesis as an implication.
fn build_nnreal_keystone_value(c: &RevSqConsts) -> Expr {
    let nnreal = c.nnreal();
    let core = Expr::const_(
        Name::from_string("NNReal.CauSeq.le_of_forall_lt_add"),
        vec![],
    );

    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(nnreal.clone());
    let (bv_id, bv) = b.fresh_local(nnreal.clone());
    let hyp_ty = forall_pos_hyp(c, &b, |bb, e, he| {
        let slack = c.of_rat_of_pos(e, he);
        let b_plus = c.nn_add(bv.clone(), slack);
        let _ = bb;
        c.nn_le(a.clone(), b_plus)
    });
    let (hyp_id, hyp) = b.fresh_local(hyp_ty.clone());

    let body = descend_keystone(c, &b, &nnreal, &a, &bv, &hyp, &core);

    let e = b.mk_lam(hyp_id, BinderInfo::Default, hyp_ty, body);
    let e = b.mk_lam(bv_id, BinderInfo::Default, nnreal.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, nnreal.clone(), e);
    b.finish(e)
}

/// The NNReal-form hypothesis body at a fixed `(a, b)` pair (parametric in the
/// reps used for `a` and `b`).
fn nn_hyp_ty_for(c: &RevSqConsts, parent: &EnvDeclBuilder, a: &Expr, bv: &Expr) -> Expr {
    forall_pos_hyp(c, parent, |bb, e, he| {
        let slack = c.of_rat_of_pos(e, he);
        let b_plus = c.nn_add(bv.clone(), slack);
        let _ = bb;
        c.nn_le(a.clone(), b_plus)
    })
}

/// Descend on `a` then `b` via `Quot.ind`; at the leaf both `a,b` are `mk f,mk g`
/// and the hypothesis/goal reduce to the `CauSeq` forms, closed by `core f g`.
#[allow(clippy::too_many_arguments)]
fn descend_keystone(
    c: &RevSqConsts,
    parent: &EnvDeclBuilder,
    nnreal: &Expr,
    a: &Expr,
    bv: &Expr,
    hyp: &Expr,
    core: &Expr,
) -> Expr {
    let quot_ind = Expr::const_(
        Name::from_string("Quot.ind"),
        vec![Level::succ(Level::zero())],
    );

    // motive over `a`: P a := (nn_hyp_ty a bv) → NNReal.le a bv.
    let motive_a = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = mb.fresh_local(nnreal.clone());
        let h = nn_hyp_ty_for(c, &mb, &x, bv);
        let concl = c.nn_le(x.clone(), bv.clone());
        let imp = Expr::pi(BinderInfo::Default, h, concl);
        mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, nnreal.clone(), imp))
    };
    let minor_a = {
        let mut mf = EnvDeclBuilder::child_of(parent);
        let (f_id, f) = mf.fresh_local(c.causeq.clone());
        let mkf = c.quot_mk(f.clone());
        let body = descend_keystone_b(c, &mf, nnreal, &mkf, &f, bv, core);
        mf.finish_child(mf.mk_lam(f_id, BinderInfo::Default, c.causeq.clone(), body))
    };
    let ind_a = Expr::apps(
        quot_ind,
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive_a,
            minor_a,
            a.clone(),
        ],
    );
    Expr::apps(ind_a, [hyp.clone()])
}

/// Descend on `b`: motive `Q b := (nn_hyp_ty (mk f) b) → NNReal.le (mk f) b`.
/// Leaf supplies rep `g`; the hypothesis reduces to the CauSeq hypothesis and the
/// goal to `CauSeq.le f g`, closed by `core f g`.
#[allow(clippy::too_many_arguments)]
fn descend_keystone_b(
    c: &RevSqConsts,
    parent: &EnvDeclBuilder,
    nnreal: &Expr,
    mkf: &Expr,
    f: &Expr,
    bv: &Expr,
    core: &Expr,
) -> Expr {
    let quot_ind = Expr::const_(
        Name::from_string("Quot.ind"),
        vec![Level::succ(Level::zero())],
    );

    let motive_b = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (y_id, y) = mb.fresh_local(nnreal.clone());
        let h = nn_hyp_ty_for(c, &mb, mkf, &y);
        let concl = c.nn_le(mkf.clone(), y.clone());
        let imp = Expr::pi(BinderInfo::Default, h, concl);
        mb.finish_child(mb.mk_lam(y_id, BinderInfo::Default, nnreal.clone(), imp))
    };
    let minor_b = {
        let mut mg = EnvDeclBuilder::child_of(parent);
        let (g_id, g) = mg.fresh_local(c.causeq.clone());
        // Leaf: hypothesis has type (nn_hyp_ty (mk f)(mk g)), which is DEFEQ to the
        // CauSeq hypothesis (NNReal.le (mk f)(add (mk g)(ofRat e)) ≡
        // CauSeq.le f (CauSeq.add g (const (NNRat.ofRat e)))). The kernel accepts
        // it directly as the `core`'s hypothesis argument.
        let hyp_cau_ty = build_causeq_hyp_ty(c, &mg, f, &g);
        let (hh_id, hh) = mg.fresh_local(hyp_cau_ty.clone());
        // core f g hh : CauSeq.le f g ≡ NNReal.le (mk f)(mk g).
        let body = Expr::apps(core.clone(), [f.clone(), g.clone(), hh]);
        let e = mg.mk_lam(hh_id, BinderInfo::Default, hyp_cau_ty, body);
        mg.finish_child(mg.mk_lam(g_id, BinderInfo::Default, c.causeq.clone(), e))
    };
    Expr::apps(
        quot_ind,
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive_b,
            minor_b,
            bv.clone(),
        ],
    )
}

/// The CauSeq-form hypothesis type at reps `(f, g)`:
///   `∀ e, 0<e → CauSeq.le f (CauSeq.add g (const (NNRat.ofRat e (le_of_lt e))))`.
fn build_causeq_hyp_ty(c: &RevSqConsts, parent: &EnvDeclBuilder, f: &Expr, g: &Expr) -> Expr {
    forall_pos_hyp(c, parent, |bb, e, he| {
        let slack = c.const_of_pos(e, he);
        let g_plus = c.cau_add(g.clone(), slack);
        let _ = bb;
        c.causeq_le(f.clone(), g_plus)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &[
        "NNReal.CauSeq.le_of_forall_lt_add",
        "NNReal.le_of_forall_lt_add",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_reverse_square()
            .expect("init_algebra_nnreal_reverse_square");
        env.init_algebra_nnreal_reverse_square()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_reverse_square_kernel_check() {
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
    fn test_reverse_square_constructive_empty_closure() {
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
