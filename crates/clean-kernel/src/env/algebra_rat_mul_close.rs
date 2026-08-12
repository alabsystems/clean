// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — Component A, Step (3a): the pure-`Rat` product
//! closeness core for `NNReal.IsCauchy_mul`.
//!
//! # Why this module exists
//!
//! `NNReal.IsCauchy_mul`'s forward (and, by m↔n symmetry, reverse) conjunct is
//! the nonneg, subtraction-free product estimate
//!
//! ```text
//! a·b < a'·b' + ε
//! ```
//!
//! from closeness `a ≤ a'+δ`, `b ≤ b'+δ`, the factor bounds `a ≤ Ba`,
//! `b' ≤ Bb`, the δ-budget `δ·(Ba+Bb) ≤ ε/2`, and `0 < ε`. The CROSS-TERM split
//! (bound the first factor by `Ba`, not by `a'+δ`) keeps the estimate `δ²`-free,
//! which is exactly why the δ-budget (`algebra_rat_delta_choice.rs`) avoids the
//! sqrt-level division layer §7.5 flagged.
//!
//! - `Rat.mul_close_of_close : ∀ (a a' b b' Ba Bb ε δ : Rat),
//!       Rat.le 0 a → Rat.le 0 b → Rat.le 0 b' → Rat.le 0 δ →
//!       Rat.le a Ba → Rat.le b' Bb →
//!       Rat.le a (a'+δ) → Rat.le b (b'+δ) →
//!       Rat.le (Rat.mul δ (Ba+Bb)) (Rat.div ε Rat.two) →
//!       Rat.lt 0 ε →
//!       Rat.lt (Rat.mul a b) (Rat.add (Rat.mul a' b') ε)`
//!
//! # Proof chain (all non-strict until the final `ε/2 < ε`)
//!
//! ```text
//! a·b ≤ a·(b'+δ)            [mul_le_left a b (b'+δ) (b≤b'+δ)(0≤a)]
//!     = a·b' + a·δ          [left_distrib a b' δ]
//! a·b' ≤ (a'+δ)·b'          [mul_le_right b' a (a'+δ) (a≤a'+δ)(0≤b')]
//!      = a'·b' + δ·b'       [right_distrib a' δ b']
//! δ·b' ≤ δ·Bb               [mul_le_left δ b' Bb (b'≤Bb)(0≤δ)]
//! a·δ  = δ·a ≤ δ·Ba         [mul_comm a δ ; mul_le_left δ a Ba (a≤Ba)(0≤δ)]
//! ⟹ a·b ≤ (a'·b' + δ·Bb) + δ·Ba
//!       = a'·b' + (δ·Bb + δ·Ba)        [add_assoc]
//!       δ·Bb + δ·Ba = δ·(Bb+Ba)        [left_distrib δ Bb Ba, reversed]
//!       δ·(Bb+Ba) ≤ δ·(Ba+Bb)          [add_comm Bb Ba ; mul_le_left refl]
//!                 ≤ ε/2                 [the δ-budget hypothesis]
//! ⟹ a·b ≤ a'·b' + ε/2
//! a'·b' + ε/2 < a'·b' + ε              [add_lt_add_left ; ε/2 < ε]
//! ε/2 < ε : ε/2 = ε/2+0 < ε/2+ε/2 = ε  [add_lt_add_left (0<ε/2) ; add_zero ; add_halves]
//! ⟹ a·b < a'·b' + ε                     [lt_of_le_of_lt]
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

/// Pre-resolved handles + smart-constructors for `Rat.mul_close_of_close`.
pub(crate) struct MulCloseConsts {
    rat: Expr,
    rat_zero: Expr,
    rat_two: Expr,
    rat_add: Expr,
    rat_mul: Expr,
    rat_div: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    // Order/arith lemmas.
    mul_le_left: Expr,
    mul_le_right: Expr,
    add_le_add: Expr,
    le_refl: Expr,
    le_trans: Expr,
    lt_of_le_of_lt: Expr,
    add_lt_add_left: Expr,
    half_pos: Expr,
    add_halves: Expr,
    // Field identities.
    left_distrib: Expr,
    right_distrib: Expr,
    add_assoc: Expr,
    add_comm: Expr,
    add_zero: Expr,
    mul_comm: Expr,
    // Eq.{1} over Rat.
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    eq_rat: Expr,
    eq_symm: Expr,
    eq_subst: Expr,
    congr_arg: Expr,
}

impl MulCloseConsts {
    pub(crate) fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_two: k("Rat.two"),
            rat_add: k("Rat.add"),
            rat_mul: k("Rat.mul"),
            rat_div: k("Rat.div"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            mul_le_left: k("Rat.mul_le_mul_of_nonneg_left"),
            mul_le_right: k("Rat.mul_le_mul_of_nonneg_right"),
            add_le_add: k("Rat.add_le_add"),
            le_refl: k("Rat.le_refl"),
            le_trans: k("Rat.le_trans"),
            lt_of_le_of_lt: k("Rat.lt_of_le_of_lt"),
            add_lt_add_left: k("Rat.add_lt_add_left"),
            half_pos: k("Rat.half_pos"),
            add_halves: k("Rat.add_halves"),
            left_distrib: k("Rat.left_distrib"),
            right_distrib: k("Rat.right_distrib"),
            add_assoc: k("Rat.add_assoc"),
            add_comm: k("Rat.add_comm"),
            add_zero: k("Rat.add_zero"),
            mul_comm: k("Rat.mul_comm"),
            #[cfg(test)]
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![lvl1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![lvl1.clone(), lvl1]),
        }
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
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn nonneg(&self, a: Expr) -> Expr {
        self.le(self.rat_zero.clone(), a)
    }
    fn half(&self, eps: Expr) -> Expr {
        self.div(eps, self.rat_two.clone())
    }
    /// `Rat.mul_le_mul_of_nonneg_left a b c (b≤c)(0≤a) : a·b ≤ a·c`.
    fn mul_le_left(&self, a: Expr, b: Expr, cc: Expr, hbc: Expr, ha: Expr) -> Expr {
        Expr::apps(self.mul_le_left.clone(), [a, b, cc, hbc, ha])
    }
    /// `Rat.mul_le_mul_of_nonneg_right a b c (b≤c)(0≤a) : b·a ≤ c·a`.
    fn mul_le_right(&self, a: Expr, b: Expr, cc: Expr, hbc: Expr, ha: Expr) -> Expr {
        Expr::apps(self.mul_le_right.clone(), [a, b, cc, hbc, ha])
    }
    /// `Rat.add_le_add a b c d (a≤b)(c≤d) : (a+c) ≤ (b+d)`.
    fn add_le_add(&self, a: Expr, b: Expr, cc: Expr, d: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.add_le_add.clone(), [a, b, cc, d, h1, h2])
    }
    /// `Rat.le_refl a : a ≤ a`.
    fn le_refl(&self, a: Expr) -> Expr {
        Expr::app(self.le_refl.clone(), a)
    }
    /// `Rat.le_trans a b c (a≤b)(b≤c) : a ≤ c`.
    fn le_trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.le_trans.clone(), [a, b, cc, h1, h2])
    }
    /// `Rat.lt_of_le_of_lt a b c (a≤b)(b<c) : a < c`.
    fn lt_of_le_of_lt(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.lt_of_le_of_lt.clone(), [a, b, cc, h1, h2])
    }
    /// `Rat.add_lt_add_left a b c (a<b) : (c+a) < (c+b)`.
    fn add_lt_add_left(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(self.add_lt_add_left.clone(), [a, b, cc, h])
    }
    /// `Rat.half_pos eps (0<eps) : 0 < eps/2`.
    fn half_pos(&self, eps: Expr, h: Expr) -> Expr {
        Expr::apps(self.half_pos.clone(), [eps, h])
    }
    /// `Rat.add_halves eps : (eps/2)+(eps/2) = eps`.
    fn add_halves(&self, eps: Expr) -> Expr {
        Expr::app(self.add_halves.clone(), eps)
    }
    /// `Rat.left_distrib a b c : a·(b+c) = a·b + a·c`.
    fn left_distrib(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.left_distrib.clone(), [a, b, cc])
    }
    /// `Rat.right_distrib a b c : (a+b)·c = a·c + b·c`.
    fn right_distrib(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.right_distrib.clone(), [a, b, cc])
    }
    /// `Rat.add_assoc a b c : (a+b)+c = a+(b+c)`.
    fn add_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.add_assoc.clone(), [a, b, cc])
    }
    /// `Rat.add_comm a b : a+b = b+a`.
    fn add_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.add_comm.clone(), [a, b])
    }
    /// `Rat.add_zero a : a+0 = a`.
    fn add_zero(&self, a: Expr) -> Expr {
        Expr::app(self.add_zero.clone(), a)
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a, b])
    }
    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    fn eq_ty(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq_rat.clone(), [self.rat.clone(), a, b])
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
    /// `Eq.subst`-transport an `le X ?` along a RHS rewrite: from
    /// `h : Rat.le x p` and `heq : p = q`, get `Rat.le x q`.
    fn le_rewrite_rhs(
        &self,
        parent: &EnvDeclBuilder,
        x: Expr,
        p: Expr,
        q: Expr,
        heq: Expr,
        h: Expr,
    ) -> Expr {
        let motive = {
            let mut m = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = m.fresh_local(self.rat.clone());
            let body = self.le(x.clone(), t);
            m.finish_child(m.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.subst(motive, p, q, heq, h)
    }
    /// transport `le ? Y` along a LHS rewrite: from `h : Rat.le p y` and
    /// `heq : p = q`, get `Rat.le q y`.
    fn le_rewrite_lhs(
        &self,
        parent: &EnvDeclBuilder,
        y: Expr,
        p: Expr,
        q: Expr,
        heq: Expr,
        h: Expr,
    ) -> Expr {
        let motive = {
            let mut m = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = m.fresh_local(self.rat.clone());
            let body = self.le(t, y.clone());
            m.finish_child(m.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.subst(motive, p, q, heq, h)
    }
}

impl Environment {
    /// Register `Rat.mul_close_of_close`. Idempotent.
    pub fn init_algebra_rat_mul_close(&mut self) -> Result<(), EnvError> {
        self.init_boolean_analysis_order_toolkit()?; // mul_le_mul_of_nonneg_left/right
        self.init_boolean_analysis_order_toolkit_b1c()?; // lt_of_le_of_lt
        self.register_rat_add_lt_add_left()?; // add_lt_add_left
        self.register_rat_add_le_add()?; // add_le_add
        self.register_rat_le_trans_proof()?; // le_trans
        self.register_rat_order_proofs()?; // le_refl
        self.register_rat_mul_comm_proof()?; // mul_comm
        self.init_rat_field_inst()?; // left/right_distrib, add_assoc, add_zero, mul/add bits
        self.init_algebra_rat_half_pos()?; // half_pos, add_halves, two

        let c = MulCloseConsts::new();
        self.register_rat_mul_close_of_close(&c)
    }

    fn register_rat_mul_close_of_close(&mut self, c: &MulCloseConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.mul_close_of_close");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = build_mul_close_type(c);
        let value = build_mul_close_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Build the type of `Rat.mul_close_of_close`.
fn build_mul_close_type(c: &MulCloseConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (ap_id, ap) = b.fresh_local(c.rat.clone());
    let (bb_id, bbv) = b.fresh_local(c.rat.clone());
    let (bp_id, bp) = b.fresh_local(c.rat.clone());
    let (ba_id, ba) = b.fresh_local(c.rat.clone());
    let (bbnd_id, bbnd) = b.fresh_local(c.rat.clone());
    let (e_id, eps) = b.fresh_local(c.rat.clone());
    let (d_id, delta) = b.fresh_local(c.rat.clone());

    let h0a = c.nonneg(a.clone());
    let (h0a_id, _) = b.fresh_local(h0a.clone());
    let h0b = c.nonneg(bbv.clone());
    let (h0b_id, _) = b.fresh_local(h0b.clone());
    let h0bp = c.nonneg(bp.clone());
    let (h0bp_id, _) = b.fresh_local(h0bp.clone());
    let h0d = c.nonneg(delta.clone());
    let (h0d_id, _) = b.fresh_local(h0d.clone());
    let haba = c.le(a.clone(), ba.clone());
    let (haba_id, _) = b.fresh_local(haba.clone());
    let hbpbb = c.le(bp.clone(), bbnd.clone());
    let (hbpbb_id, _) = b.fresh_local(hbpbb.clone());
    let hcla = c.le(a.clone(), c.add(ap.clone(), delta.clone()));
    let (hcla_id, _) = b.fresh_local(hcla.clone());
    let hclb = c.le(bbv.clone(), c.add(bp.clone(), delta.clone()));
    let (hclb_id, _) = b.fresh_local(hclb.clone());
    let hbudget = c.le(
        c.mul(delta.clone(), c.add(ba.clone(), bbnd.clone())),
        c.half(eps.clone()),
    );
    let (hbud_id, _) = b.fresh_local(hbudget.clone());
    let h0e = c.lt(c.rat_zero.clone(), eps.clone());
    let (h0e_id, _) = b.fresh_local(h0e.clone());

    let concl = c.lt(
        c.mul(a.clone(), bbv.clone()),
        c.add(c.mul(ap.clone(), bp.clone()), eps.clone()),
    );

    let e = b.mk_pi(h0e_id, BinderInfo::Default, h0e, concl);
    let e = b.mk_pi(hbud_id, BinderInfo::Default, hbudget, e);
    let e = b.mk_pi(hclb_id, BinderInfo::Default, hclb, e);
    let e = b.mk_pi(hcla_id, BinderInfo::Default, hcla, e);
    let e = b.mk_pi(hbpbb_id, BinderInfo::Default, hbpbb, e);
    let e = b.mk_pi(haba_id, BinderInfo::Default, haba, e);
    let e = b.mk_pi(h0d_id, BinderInfo::Default, h0d, e);
    let e = b.mk_pi(h0bp_id, BinderInfo::Default, h0bp, e);
    let e = b.mk_pi(h0b_id, BinderInfo::Default, h0b, e);
    let e = b.mk_pi(h0a_id, BinderInfo::Default, h0a, e);
    let e = b.mk_pi(d_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(e_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(bbnd_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(ba_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(bp_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(bb_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(ap_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Build the proof term of `Rat.mul_close_of_close`.
fn build_mul_close_proof(c: &MulCloseConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (ap_id, ap) = b.fresh_local(c.rat.clone());
    let (bb_id, bbv) = b.fresh_local(c.rat.clone());
    let (bp_id, bp) = b.fresh_local(c.rat.clone());
    let (ba_id, ba) = b.fresh_local(c.rat.clone());
    let (bbnd_id, bbnd) = b.fresh_local(c.rat.clone());
    let (e_id, eps) = b.fresh_local(c.rat.clone());
    let (d_id, delta) = b.fresh_local(c.rat.clone());

    let h0a_ty = c.nonneg(a.clone());
    let (h0a_id, h0a) = b.fresh_local(h0a_ty.clone());
    let h0b_ty = c.nonneg(bbv.clone());
    let (h0b_id, _h0b) = b.fresh_local(h0b_ty.clone());
    let h0bp_ty = c.nonneg(bp.clone());
    let (h0bp_id, h0bp) = b.fresh_local(h0bp_ty.clone());
    let h0d_ty = c.nonneg(delta.clone());
    let (h0d_id, h0d) = b.fresh_local(h0d_ty.clone());
    let haba_ty = c.le(a.clone(), ba.clone());
    let (haba_id, haba) = b.fresh_local(haba_ty.clone());
    let hbpbb_ty = c.le(bp.clone(), bbnd.clone());
    let (hbpbb_id, hbpbb) = b.fresh_local(hbpbb_ty.clone());
    let hcla_ty = c.le(a.clone(), c.add(ap.clone(), delta.clone()));
    let (hcla_id, hcla) = b.fresh_local(hcla_ty.clone());
    let hclb_ty = c.le(bbv.clone(), c.add(bp.clone(), delta.clone()));
    let (hclb_id, hclb) = b.fresh_local(hclb_ty.clone());
    let hbudget_ty = c.le(
        c.mul(delta.clone(), c.add(ba.clone(), bbnd.clone())),
        c.half(eps.clone()),
    );
    let (hbud_id, hbudget) = b.fresh_local(hbudget_ty.clone());
    let h0e_ty = c.lt(c.rat_zero.clone(), eps.clone());
    let (h0e_id, h0e) = b.fresh_local(h0e_ty.clone());

    // Shorthand terms.
    let ab = c.mul(a.clone(), bbv.clone()); // a·b
    let apbp = c.mul(ap.clone(), bp.clone()); // a'·b'
    let bp_d = c.add(bp.clone(), delta.clone()); // b'+δ
    let ap_d = c.add(ap.clone(), delta.clone()); // a'+δ
    let a_bp = c.mul(a.clone(), bp.clone()); // a·b'
    let a_d = c.mul(a.clone(), delta.clone()); // a·δ
    let d_a = c.mul(delta.clone(), a.clone()); // δ·a
    let d_ba = c.mul(delta.clone(), ba.clone()); // δ·Ba
    let d_bp = c.mul(delta.clone(), bp.clone()); // δ·b'
    let d_bb = c.mul(delta.clone(), bbnd.clone()); // δ·Bb

    // (1) a·b ≤ a·(b'+δ)  [mul_le_left a b (b'+δ) hclb h0a].
    let s1 = c.mul_le_left(a.clone(), bbv.clone(), bp_d.clone(), hclb, h0a.clone());
    // a·(b'+δ) = a·b' + a·δ  [left_distrib a b' δ].
    let ld1 = c.left_distrib(a.clone(), bp.clone(), delta.clone());
    let a_bpd = c.mul(a.clone(), bp_d.clone());
    let a_bp_plus_a_d = c.add(a_bp.clone(), a_d.clone());
    // s1b : a·b ≤ a·b' + a·δ  (transport RHS of s1 along ld1).
    let s1b = c.le_rewrite_rhs(&b, ab.clone(), a_bpd, a_bp_plus_a_d.clone(), ld1, s1);

    // (2) a·b' ≤ (a'+δ)·b'  [mul_le_right b' a (a'+δ) hcla h0bp].
    let s2 = c.mul_le_right(bp.clone(), a.clone(), ap_d.clone(), hcla, h0bp);
    // (a'+δ)·b' = a'·b' + δ·b'  [right_distrib a' δ b'].
    let rd1 = c.right_distrib(ap.clone(), delta.clone(), bp.clone());
    let apd_bp = c.mul(ap_d.clone(), bp.clone());
    let apbp_plus_dbp = c.add(apbp.clone(), d_bp.clone());
    // s2b : a·b' ≤ a'·b' + δ·b'.
    let s2b = c.le_rewrite_rhs(&b, a_bp.clone(), apd_bp, apbp_plus_dbp.clone(), rd1, s2);

    // (3) δ·b' ≤ δ·Bb  [mul_le_left δ b' Bb hbpbb h0d].
    let s3 = c.mul_le_left(delta.clone(), bp.clone(), bbnd.clone(), hbpbb, h0d.clone());
    // a·b' ≤ a'·b' + δ·Bb : chain s2b with add_le_add (refl a'·b')(s3).
    //   add_le_add a'·b' a'·b' (δ·b')(δ·Bb) (refl)(s3) : a'·b'+δ·b' ≤ a'·b'+δ·Bb
    let apbp_plus_dbb = c.add(apbp.clone(), d_bb.clone());
    let add1 = c.add_le_add(
        apbp.clone(),
        apbp.clone(),
        d_bp.clone(),
        d_bb.clone(),
        c.le_refl(apbp.clone()),
        s3,
    );
    // s2c : a·b' ≤ a'·b' + δ·Bb.
    let s2c = c.le_trans(
        a_bp.clone(),
        apbp_plus_dbp.clone(),
        apbp_plus_dbb.clone(),
        s2b,
        add1,
    );

    // (4) a·δ ≤ δ·Ba : a·δ = δ·a [mul_comm a δ], δ·a ≤ δ·Ba [mul_le_left δ a Ba haba h0d].
    let s4_da = c.mul_le_left(delta.clone(), a.clone(), ba.clone(), haba, h0d);
    // transport LHS δ·a → a·δ via (mul_comm δ a : δ·a = a·δ).
    let s4 = c.le_rewrite_lhs(
        &b,
        d_ba.clone(),
        d_a.clone(),
        a_d.clone(),
        c.mul_comm(delta.clone(), a.clone()),
        s4_da,
    );
    // s4 : a·δ ≤ δ·Ba.

    // Combine (a·b' + a·δ) ≤ (a'·b' + δ·Bb) + δ·Ba :
    //   add_le_add (a·b')(a'·b'+δ·Bb)(a·δ)(δ·Ba) s2c s4.
    let lhs_sum = c.add(a_bp.clone(), a_d.clone()); // a·b' + a·δ
    let mid_sum = c.add(apbp_plus_dbb.clone(), d_ba.clone()); // (a'·b'+δ·Bb)+δ·Ba
    let add2 = c.add_le_add(
        a_bp.clone(),
        apbp_plus_dbb.clone(),
        a_d.clone(),
        d_ba.clone(),
        s2c,
        s4,
    );
    // s5 : a·b ≤ (a'·b'+δ·Bb)+δ·Ba  [le_trans s1b add2].
    let s5 = c.le_trans(ab.clone(), lhs_sum.clone(), mid_sum.clone(), s1b, add2);

    // (a'·b'+δ·Bb)+δ·Ba = a'·b'+(δ·Bb+δ·Ba)  [add_assoc a'·b' δ·Bb δ·Ba].
    let dbb_plus_dba = c.add(d_bb.clone(), d_ba.clone()); // δ·Bb+δ·Ba
    let apbp_plus_dd = c.add(apbp.clone(), dbb_plus_dba.clone());
    let assoc1 = c.add_assoc(apbp.clone(), d_bb.clone(), d_ba.clone());
    // s6 : a·b ≤ a'·b'+(δ·Bb+δ·Ba).
    let s6 = c.le_rewrite_rhs(&b, ab.clone(), mid_sum, apbp_plus_dd.clone(), assoc1, s5);

    // Budget: δ·Bb+δ·Ba = δ·(Bb+Ba)  [left_distrib δ Bb Ba, used as symm].
    //   left_distrib δ Bb Ba : δ·(Bb+Ba) = δ·Bb + δ·Ba.  Eq.symm ⟹ the rewrite.
    let bb_plus_ba = c.add(bbnd.clone(), ba.clone()); // Bb+Ba
    let d_bbba = c.mul(delta.clone(), bb_plus_ba.clone()); // δ·(Bb+Ba)
    let ld_budget = c.left_distrib(delta.clone(), bbnd.clone(), ba.clone()); // δ·(Bb+Ba)=δ·Bb+δ·Ba
                                                                             // δ·(Bb+Ba) ≤ δ·(Ba+Bb):  Bb+Ba = Ba+Bb [add_comm], then refl-ish via subst.
                                                                             //   add_comm Bb Ba : Bb+Ba = Ba+Bb. congrArg (δ·) gives δ·(Bb+Ba)=δ·(Ba+Bb).
    let ba_plus_bb = c.add(ba.clone(), bbnd.clone()); // Ba+Bb
    let d_baba = c.mul(delta.clone(), ba_plus_bb.clone()); // δ·(Ba+Bb)
    let mul_d_fn = {
        let mut fb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = fb.fresh_local(c.rat.clone());
        let body = c.mul(delta.clone(), t);
        fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let eq_dbbba_dbaba = c.congr_arg(
        bb_plus_ba.clone(),
        ba_plus_bb.clone(),
        mul_d_fn,
        c.add_comm(bbnd.clone(), ba.clone()),
    );
    // hbudget : δ·(Ba+Bb) ≤ ε/2. Transport its LHS δ·(Ba+Bb) ← δ·(Bb+Ba)
    //   to get δ·(Bb+Ba) ≤ ε/2.
    let half_eps = c.half(eps.clone());
    let budget_bbba = c.le_rewrite_lhs(
        &b,
        half_eps.clone(),
        d_baba.clone(),
        d_bbba.clone(),
        c.eq_symm(d_bbba.clone(), d_baba.clone(), eq_dbbba_dbaba),
        hbudget,
    );
    // δ·Bb+δ·Ba ≤ ε/2 : transport budget_bbba LHS δ·(Bb+Ba) → δ·Bb+δ·Ba via ld_budget.
    let cross_le_half = c.le_rewrite_lhs(
        &b,
        half_eps.clone(),
        d_bbba.clone(),
        dbb_plus_dba.clone(),
        ld_budget,
        budget_bbba,
    );
    // a'·b' + (δ·Bb+δ·Ba) ≤ a'·b' + ε/2  [add_le_add (refl a'·b')(cross_le_half)].
    let apbp_plus_half = c.add(apbp.clone(), half_eps.clone());
    let add3 = c.add_le_add(
        apbp.clone(),
        apbp.clone(),
        dbb_plus_dba.clone(),
        half_eps.clone(),
        c.le_refl(apbp.clone()),
        cross_le_half,
    );
    // s7 : a·b ≤ a'·b' + ε/2  [le_trans s6 add3].
    let s7 = c.le_trans(ab.clone(), apbp_plus_dd, apbp_plus_half.clone(), s6, add3);

    // ε/2 < ε : ε/2 = ε/2+0 < ε/2+ε/2 = ε.
    //   half_pos eps h0e : 0 < ε/2.
    //   add_lt_add_left 0 (ε/2) (ε/2) (0<ε/2) : (ε/2+0) < (ε/2+ε/2).
    let half_pos = c.half_pos(eps.clone(), h0e);
    let lt_raw = c.add_lt_add_left(
        c.rat_zero.clone(),
        half_eps.clone(),
        half_eps.clone(),
        half_pos,
    );
    // transport LHS (ε/2+0) → ε/2 via add_zero (ε/2).
    let half_plus_zero = c.add(half_eps.clone(), c.rat_zero.clone());
    let half_plus_half = c.add(half_eps.clone(), half_eps.clone());
    let lt_lhs_motive = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = m.fresh_local(c.rat.clone());
        let body = c.lt(t, half_plus_half.clone());
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let lt1 = c.subst(
        lt_lhs_motive,
        half_plus_zero,
        half_eps.clone(),
        c.add_zero(half_eps.clone()),
        lt_raw,
    );
    // transport RHS (ε/2+ε/2) → ε via add_halves eps.
    let lt_rhs_motive = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = m.fresh_local(c.rat.clone());
        let body = c.lt(half_eps.clone(), t);
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let half_lt_eps = c.subst(
        lt_rhs_motive,
        half_plus_half,
        eps.clone(),
        c.add_halves(eps.clone()),
        lt1,
    );
    // a'·b' + ε/2 < a'·b' + ε  [add_lt_add_left (ε/2) ε (a'·b') half_lt_eps].
    let apbp_plus_eps = c.add(apbp.clone(), eps.clone());
    let final_lt = c.add_lt_add_left(half_eps.clone(), eps.clone(), apbp.clone(), half_lt_eps);

    // a·b < a'·b' + ε  [lt_of_le_of_lt (a·b)(a'·b'+ε/2)(a'·b'+ε) s7 final_lt].
    let proof = c.lt_of_le_of_lt(ab, apbp_plus_half, apbp_plus_eps, s7, final_lt);

    let e = b.mk_lam(h0e_id, BinderInfo::Default, h0e_ty, proof);
    let e = b.mk_lam(hbud_id, BinderInfo::Default, hbudget_ty, e);
    let e = b.mk_lam(hclb_id, BinderInfo::Default, hclb_ty, e);
    let e = b.mk_lam(hcla_id, BinderInfo::Default, hcla_ty, e);
    let e = b.mk_lam(hbpbb_id, BinderInfo::Default, hbpbb_ty, e);
    let e = b.mk_lam(haba_id, BinderInfo::Default, haba_ty, e);
    let e = b.mk_lam(h0d_id, BinderInfo::Default, h0d_ty, e);
    let e = b.mk_lam(h0bp_id, BinderInfo::Default, h0bp_ty, e);
    let e = b.mk_lam(h0b_id, BinderInfo::Default, h0b_ty, e);
    let e = b.mk_lam(h0a_id, BinderInfo::Default, h0a_ty, e);
    let e = b.mk_lam(d_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(e_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(bbnd_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(ba_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(bp_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(bb_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(ap_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_rat_mul_close()
            .expect("init_algebra_rat_mul_close");
        env.init_algebra_rat_mul_close().expect("idempotent");
        env
    }

    #[test]
    fn test_mul_close_present_and_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nm = Name::from_string("Rat.mul_close_of_close");
        let info = env
            .get_const(&nm)
            .expect("Rat.mul_close_of_close registered");
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .expect("Rat.mul_close_of_close must kernel-check");
    }

    #[test]
    fn test_mul_close_constructive_empty_closure() {
        let env = env();
        let nm = Name::from_string("Rat.mul_close_of_close");
        let info = env.get_const(&nm).expect("registered");
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
