// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! TCB-shrink Tier 3: genuine, kernel-checked elimination of the last
//! `Rat.abs_*` Soundness-Certificate TCB axiom,
//!
//! ```text
//! Rat.abs_mul : ∀ a b : Rat,
//!     Eq Rat (Rat.abs (Rat.mul a b)) (Rat.mul (Rat.abs a) (Rat.abs b)).
//! ```
//!
//! # Why this was deferred, and how it is now closed
//!
//! Over the SOUND quotient carrier `Rat := @Quot Rat.Raw Rat.Raw.Equiv`,
//! `Rat.abs` is the FAITHFUL reducible Definition `Rat.abs q := Rat.max q
//! (Rat.neg q)` (`algebra_rat_abs_proof.rs`). The easy/hard `Rat.abs_*`
//! batches there proved `abs_of_nonneg/abs_of_neg/abs_zero/abs_nonneg/abs_neg`
//! and the triangle inequalities, but left `Rat.abs_mul` as an honest admitted
//! `Declaration::Axiom`: a faithful proof needs the FOUR-way sign-case
//! multiplicative analysis (`|a·b| = |a|·|b|` is `±(a·b)` matched against
//! `(±a)·(±b)`), which depends on multiplicative sign/monotonicity lemmas over
//! the quotient that only recently landed.
//!
//! Those lemmas now exist as kernel-checked constructive `Declaration::Theorem`s
//! over the quotient:
//!
//! * `Rat.mul_nonneg : ∀ a b, 0 ≤ a → 0 ≤ b → 0 ≤ a·b`
//!   (`algebra_rat_order_proofs.rs`, via `Int.mul_nonneg`),
//! * `Rat.mul_neg    : ∀ a b, a·(-b) = -(a·b)`
//!   (`nn_verify_rat_ordering.rs` → quotient `register_rat_q_mul_neg`),
//! * `Rat.mul_comm   : ∀ a b, a·b = b·a` (`algebra_rat_mul_comm_proof.rs`),
//! * `Rat.le_total`, `Rat.le_trans`, `Rat.neg_le_neg`, `Rat.max_def`,
//!   `Rat.max_def'`, plus the additive-group lemmas (`Rat.add_left_neg`,
//!   `Rat.add_neg_self`, `Rat.add_right_cancel`, `Rat.zero_add`).
//!
//! From these this module DERIVES (inline, kernel-checked) the missing
//! algebraic facts and assembles the four-case proof:
//!
//! * `Rat.neg_mul a b   : (-a)·b = -(a·b)`           [`mul_comm` ∘ `mul_neg`]
//! * `Rat.neg_mul_neg a b : (-a)·(-b) = a·b`          [`neg_mul` ∘ `mul_neg` ∘
//!                                                      `neg_neg`]
//! * `Rat.neg_neg a : -(-a) = a`                      [`add_right_cancel`]
//! * `abs_of_nonpos a : a ≤ 0 → |a| = -a`             [`max_def`]
//!   (the `≤ 0` companion of the landed `abs_of_nonneg : 0 ≤ a → |a| = a`),
//! * sign bridges `0 ≤ -x ↔ x ≤ 0` via `neg_le_neg` + `neg_zero`/`neg_neg`.
//!
//! # The four sign cases (`@Or.rec` on `le_total 0 a`, nested on `le_total 0 b`)
//!
//! Writing `P := a·b`:
//! 1. `0 ≤ a, 0 ≤ b`: `0 ≤ P` (`mul_nonneg`), `|P| = P`, `|a|·|b| = a·b = P`.
//! 2. `0 ≤ a, b ≤ 0`: `0 ≤ a·(-b) = -P` (`mul_neg`) ⟹ `P ≤ 0`, `|P| = -P`,
//!    `|a|·|b| = a·(-b) = -P` (`mul_neg`).
//! 3. `a ≤ 0, 0 ≤ b`: `0 ≤ (-a)·b = -P` (`neg_mul`) ⟹ `P ≤ 0`, `|P| = -P`,
//!    `|a|·|b| = (-a)·b = -P` (`neg_mul`).
//! 4. `a ≤ 0, b ≤ 0`: `0 ≤ (-a)·(-b) = P` (`neg_mul_neg`) ⟹ `0 ≤ P`,
//!    `|P| = P`, `|a|·|b| = (-a)·(-b) = P` (`neg_mul_neg`).
//!
//! In every case the proof closes `|P| = |a|·|b|` by
//! `Eq.trans (e_absP : |P| = S) (Eq.symm (e_prod : |a|·|b| = S))`, where `S`
//! is the matched signed product and `e_prod` is the congruence
//! `|a|·|b| = T_a·T_b` (from `e_a : |a| = T_a`, `e_b : |b| = T_b`) chained with
//! the product identity `T_a·T_b = S`.
//!
//! # Axiom closure
//!
//! Every delegate is a constructive `Declaration::Theorem` or a foundational
//! primitive (`Eq`/`Eq.refl`/`Eq.symm`/`Eq.trans`/`Eq.subst`/`congrArg`,
//! `Or`/`Or.rec`). No `Declaration::Axiom` is reached, so `Rat.abs_mul`'s
//! transitive domain-axiom closure is empty (`ProofQuality::Constructive`).
//! It therefore leaves the Soundness-Certificate TCB.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached constants + smart-constructors for the `Rat.abs_mul` proof term.
struct RatAbsMulConsts {
    rat: Expr,
    rat_zero: Expr,
    rat_add: Expr,
    rat_neg: Expr,
    rat_mul: Expr,
    rat_max: Expr,
    rat_le: Expr,
    // Eq machinery (Rat : Sort 1).
    eq_c: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    eq_subst: Expr,
    congr_arg: Expr,
    // Order / lattice lemmas.
    le_trans: Expr,
    le_total: Expr,
    max_def: Expr,
    max_def_prime: Expr,
    neg_le_neg: Expr,
    // Ring / sign lemmas.
    mul_comm: Expr,
    mul_neg: Expr,
    mul_nonneg: Expr,
    // Additive group lemmas (for the inline `neg_neg` / `neg_zero`).
    add_left_neg: Expr,
    add_neg_self: Expr,
    add_right_cancel: Expr,
    zero_add: Expr,
    // Logic.
    or_c: Expr,
    or_rec: Expr,
}

impl RatAbsMulConsts {
    fn new() -> Self {
        let t1 = Level::succ(Level::zero());
        let c = |n: &str| Expr::const_(Name::from_string(n), vec![]);
        Self {
            rat: c("Rat"),
            rat_zero: c("Rat.zero"),
            rat_add: c("Rat.add"),
            rat_neg: c("Rat.neg"),
            rat_mul: c("Rat.mul"),
            rat_max: c("Rat.max"),
            rat_le: c("Rat.le"),
            eq_c: Expr::const_(Name::from_string("Eq"), vec![t1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![t1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![t1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![t1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![t1.clone(), t1]),
            le_trans: c("Rat.le_trans"),
            le_total: c("Rat.le_total"),
            max_def: c("Rat.max_def"),
            max_def_prime: c("Rat.max_def'"),
            neg_le_neg: c("Rat.neg_le_neg"),
            mul_comm: c("Rat.mul_comm"),
            mul_neg: c("Rat.mul_neg"),
            mul_nonneg: c("Rat.mul_nonneg"),
            add_left_neg: c("Rat.add_left_neg"),
            add_neg_self: c("Rat.add_neg_self"),
            add_right_cancel: c("Rat.add_right_cancel"),
            zero_add: c("Rat.zero_add"),
            or_c: c("Or"),
            or_rec: c("Or.rec"),
        }
    }

    // ── term builders ───────────────────────────────────────────────────────
    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [x, y])
    }
    fn neg(&self, x: Expr) -> Expr {
        Expr::app(self.rat_neg.clone(), x)
    }
    fn mul(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [x, y])
    }
    /// `Rat.abs x`, written as its reducible carrier `Rat.max x (Rat.neg x)`.
    fn abs(&self, x: Expr) -> Expr {
        Expr::apps(self.rat_max.clone(), [x.clone(), self.neg(x)])
    }
    fn le(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [x, y])
    }
    fn eq(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.eq_c.clone(), [self.rat.clone(), x, y])
    }
    fn symm(&self, x: Expr, y: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), x, y, h])
    }
    fn trans(&self, x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), x, y, z, h1, h2])
    }
    /// `@congrArg.{1,1} Rat Rat a b f h : f a = f b`.
    fn congr_arg(&self, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }
    /// `@Eq.subst.{1} Rat motive a b h_eq h_motive_a : motive b`.
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_a: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h_a],
        )
    }
    fn le_trans(&self, x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.le_trans.clone(), [x, y, z, h1, h2])
    }
    fn neg_le_neg(&self, x: Expr, y: Expr, h: Expr) -> Expr {
        Expr::apps(self.neg_le_neg.clone(), [x, y, h])
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a, b])
    }
    /// `Rat.mul_neg a b : a·(-b) = -(a·b)`.
    fn mul_neg(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_neg.clone(), [a, b])
    }
    /// `Rat.mul_nonneg a b ha hb : 0 ≤ a·b`.
    fn mul_nonneg(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.mul_nonneg.clone(), [a, b, ha, hb])
    }

    // ── inline derived equalities ────────────────────────────────────────────

    /// `e : Rat.neg Rat.zero = Rat.zero` (`-0 + 0 = 0 = 0 + 0`, cancel `0`).
    fn neg_zero_eq(&self) -> Expr {
        let z = self.rat_zero.clone();
        let neg_z = self.neg(z.clone());
        let h_l = Expr::app(self.add_left_neg.clone(), z.clone()); // -0 + 0 = 0
        let h_r = Expr::app(self.zero_add.clone(), z.clone()); // 0 + 0 = 0
        let zero_plus_zero = self.add(z.clone(), z.clone());
        let h_r_sym = self.symm(zero_plus_zero.clone(), z.clone(), h_r);
        let neg_z_plus_zero = self.add(neg_z.clone(), z.clone());
        let h_comb = self.trans(neg_z_plus_zero, z.clone(), zero_plus_zero, h_l, h_r_sym);
        Expr::apps(self.add_right_cancel.clone(), [neg_z, z.clone(), z, h_comb])
    }

    /// `e : Rat.neg (Rat.neg x) = x` (`-(-x) + (-x) = 0 = x + (-x)`, cancel
    /// `-x`).
    fn neg_neg_eq(&self, x: Expr) -> Expr {
        let neg_x = self.neg(x.clone());
        let neg_neg_x = self.neg(neg_x.clone());
        let h_l = Expr::app(self.add_left_neg.clone(), neg_x.clone()); // -(-x)+(-x)=0
        let h_r = Expr::app(self.add_neg_self.clone(), x.clone()); // x+(-x)=0
        let x_plus_neg_x = self.add(x.clone(), neg_x.clone());
        let h_r_sym = self.symm(x_plus_neg_x.clone(), self.rat_zero.clone(), h_r);
        let neg_neg_x_plus_neg_x = self.add(neg_neg_x.clone(), neg_x.clone());
        let h_comb = self.trans(
            neg_neg_x_plus_neg_x,
            self.rat_zero.clone(),
            x_plus_neg_x,
            h_l,
            h_r_sym,
        );
        Expr::apps(self.add_right_cancel.clone(), [neg_neg_x, neg_x, x, h_comb])
    }

    /// `Rat.neg_mul a b : (-a)·b = -(a·b)`.
    ///
    /// Chain: `(-a)·b = b·(-a)` [`mul_comm`] `= -(b·a)` [`mul_neg`]
    ///        `= -(a·b)` [`congrArg neg (mul_comm b a)`].
    fn neg_mul_eq(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr) -> Expr {
        let neg_a = self.neg(a.clone());
        let b_neg_a = self.mul(b.clone(), neg_a.clone()); // b·(-a)
        let neg_ba = self.neg(self.mul(b.clone(), a.clone())); // -(b·a)
        let neg_ab = self.neg(self.mul(a.clone(), b.clone())); // -(a·b)
        let lhs = self.mul(neg_a.clone(), b.clone()); // (-a)·b
                                                      // e1 : (-a)·b = b·(-a)   via mul_comm (-a) b
        let e1 = self.mul_comm(neg_a.clone(), b.clone());
        // e2 : b·(-a) = -(b·a)   via mul_neg b a
        let e2 = self.mul_neg(b.clone(), a.clone());
        // e3 : -(b·a) = -(a·b)   via congrArg neg (mul_comm b a)
        let e3 = self.congr_arg(
            self.mul(b.clone(), a.clone()),
            self.mul(a.clone(), b.clone()),
            self.rat_neg.clone(),
            self.mul_comm(b.clone(), a.clone()),
        );
        let _ = parent;
        // trans e1 (trans e2 e3)
        let t23 = self.trans(b_neg_a.clone(), neg_ba, neg_ab.clone(), e2, e3);
        self.trans(lhs, b_neg_a, neg_ab, e1, t23)
    }

    /// `Rat.neg_mul_neg a b : (-a)·(-b) = a·b`.
    ///
    /// Chain: `(-a)·(-b) = -(a·(-b))` [`neg_mul`] `= -(-(a·b))`
    ///        [`congrArg neg (mul_neg a b)`] `= a·b` [`neg_neg`].
    fn neg_mul_neg_eq(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr) -> Expr {
        let neg_a = self.neg(a.clone());
        let neg_b = self.neg(b.clone());
        let ab = self.mul(a.clone(), b.clone());
        let a_neg_b = self.mul(a.clone(), neg_b.clone()); // a·(-b)
        let neg_a_neg_b = self.mul(neg_a.clone(), neg_b.clone()); // (-a)·(-b)
        let neg_a_neg_b_eq = self.neg(a_neg_b.clone()); // -(a·(-b))
        let neg_neg_ab = self.neg(self.neg(ab.clone())); // -(-(a·b))
                                                         // e1 : (-a)·(-b) = -(a·(-b))   via neg_mul a (-b)
        let e1 = self.neg_mul_eq(parent, a, &neg_b);
        // e2 : -(a·(-b)) = -(-(a·b))   via congrArg neg (mul_neg a b)
        let e2 = self.congr_arg(
            a_neg_b.clone(),
            self.neg(ab.clone()),
            self.rat_neg.clone(),
            self.mul_neg(a.clone(), b.clone()),
        );
        // e3 : -(-(a·b)) = a·b   via neg_neg (a·b)
        let e3 = self.neg_neg_eq(ab.clone());
        // trans e1 (trans e2 e3)
        let t23 = self.trans(neg_a_neg_b_eq.clone(), neg_neg_ab, ab.clone(), e2, e3);
        self.trans(neg_a_neg_b, neg_a_neg_b_eq, ab, e1, t23)
    }

    // ── sign bridges (≤) ─────────────────────────────────────────────────────

    /// `0 ≤ Rat.neg x` from `h : x ≤ 0`. `neg_le_neg x 0 h : -0 ≤ -x`,
    /// transported along `-0 = 0` with motive `λ y, y ≤ -x`.
    fn zero_le_neg_of_le_zero(&self, parent: &EnvDeclBuilder, x: &Expr, h_x_le_0: Expr) -> Expr {
        let neg_x = self.neg(x.clone());
        let neg_zero = self.neg(self.rat_zero.clone());
        let h = self.neg_le_neg(x.clone(), self.rat_zero.clone(), h_x_le_0); // -0 ≤ -x
        let motive = {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (y_id, y) = ch.fresh_local(self.rat.clone());
            let body = self.le(y, neg_x.clone());
            let lam = ch.mk_lam(y_id, BinderInfo::Default, self.rat.clone(), body);
            ch.finish_child(lam)
        };
        self.subst(
            motive,
            neg_zero,
            self.rat_zero.clone(),
            self.neg_zero_eq(),
            h,
        )
    }

    /// `x ≤ 0` from `h : 0 ≤ Rat.neg x`. `neg_le_neg 0 (-x) h : -(-x) ≤ -0`,
    /// transported along `-(-x) = x` (motive `λ y, y ≤ -0`) and `-0 = 0`
    /// (motive `λ y, x ≤ y`).
    fn le_zero_of_zero_le_neg(
        &self,
        parent: &EnvDeclBuilder,
        x: &Expr,
        h_0_le_neg_x: Expr,
    ) -> Expr {
        let neg_x = self.neg(x.clone());
        let neg_neg_x = self.neg(neg_x.clone());
        let neg_zero = self.neg(self.rat_zero.clone());
        // neg_le_neg 0 (-x) h : -(-x) ≤ -0
        let h = self.neg_le_neg(self.rat_zero.clone(), neg_x.clone(), h_0_le_neg_x);
        // rewrite -(-x) → x : x ≤ -0
        let motive1 = {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (y_id, y) = ch.fresh_local(self.rat.clone());
            let body = self.le(y, neg_zero.clone());
            let lam = ch.mk_lam(y_id, BinderInfo::Default, self.rat.clone(), body);
            ch.finish_child(lam)
        };
        let h1 = self.subst(
            motive1,
            neg_neg_x.clone(),
            x.clone(),
            self.neg_neg_eq(x.clone()),
            h,
        );
        // rewrite -0 → 0 : x ≤ 0
        let motive2 = {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (y_id, y) = ch.fresh_local(self.rat.clone());
            let body = self.le(x.clone(), y);
            let lam = ch.mk_lam(y_id, BinderInfo::Default, self.rat.clone(), body);
            ch.finish_child(lam)
        };
        self.subst(
            motive2,
            neg_zero,
            self.rat_zero.clone(),
            self.neg_zero_eq(),
            h1,
        )
    }

    // ── abs characterizations ────────────────────────────────────────────────

    /// `|a| = a` from `h : 0 ≤ a`. `-a ≤ 0 ≤ a` ⟹ `-a ≤ a`, then
    /// `max_def' a (-a) (-a ≤ a) : max a (-a) = a`.
    fn abs_of_nonneg(&self, parent: &EnvDeclBuilder, a: &Expr, h_0_le_a: Expr) -> Expr {
        let neg_a = self.neg(a.clone());
        // -a ≤ 0  from  0 ≤ a  (le_zero_of_zero_le_neg with x := a needs 0 ≤ -a;
        //   easier: derive -a ≤ 0 directly via neg_le_neg 0 a h then -0=0).
        // neg_le_neg 0 a h : -a ≤ -0 ; rewrite -0 → 0.
        let neg_a_le_neg0 = self.neg_le_neg(self.rat_zero.clone(), a.clone(), h_0_le_a.clone());
        let motive = {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (y_id, y) = ch.fresh_local(self.rat.clone());
            let body = self.le(neg_a.clone(), y);
            let lam = ch.mk_lam(y_id, BinderInfo::Default, self.rat.clone(), body);
            ch.finish_child(lam)
        };
        let neg_a_le_0 = self.subst(
            motive,
            self.neg(self.rat_zero.clone()),
            self.rat_zero.clone(),
            self.neg_zero_eq(),
            neg_a_le_neg0,
        );
        // -a ≤ a  via le_trans (-a) 0 a
        let neg_a_le_a = self.le_trans(
            neg_a.clone(),
            self.rat_zero.clone(),
            a.clone(),
            neg_a_le_0,
            h_0_le_a,
        );
        Expr::apps(self.max_def_prime.clone(), [a.clone(), neg_a, neg_a_le_a])
    }

    /// `|a| = -a` from `h : a ≤ 0`. `a ≤ 0 ≤ -a` ⟹ `a ≤ -a`, then
    /// `max_def a (-a) (a ≤ -a) : max a (-a) = -a`.
    fn abs_of_nonpos(&self, parent: &EnvDeclBuilder, a: &Expr, h_a_le_0: Expr) -> Expr {
        let neg_a = self.neg(a.clone());
        // 0 ≤ -a  from  a ≤ 0
        let zero_le_neg_a = self.zero_le_neg_of_le_zero(parent, a, h_a_le_0.clone());
        // a ≤ -a  via le_trans a 0 (-a)
        let a_le_neg_a = self.le_trans(
            a.clone(),
            self.rat_zero.clone(),
            neg_a.clone(),
            h_a_le_0,
            zero_le_neg_a,
        );
        Expr::apps(self.max_def.clone(), [a.clone(), neg_a, a_le_neg_a])
    }

    // ── product congruence ───────────────────────────────────────────────────

    /// `|a|·|b| = T_a·T_b` from `e_a : |a| = T_a` and `e_b : |b| = T_b`.
    /// Two `congrArg` steps over `λx, mul x |b|` and `λx, mul T_a x`.
    fn mul_abs_congr(
        &self,
        parent: &EnvDeclBuilder,
        a: &Expr,
        b: &Expr,
        ta: &Expr,
        tb: &Expr,
        e_a: Expr,
        e_b: Expr,
    ) -> Expr {
        let abs_a = self.abs(a.clone());
        let abs_b = self.abs(b.clone());
        // s1 : |a|·|b| = T_a·|b|   via congrArg (λx, mul x |b|) e_a
        let f1 = {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = ch.fresh_local(self.rat.clone());
            let body = self.mul(x, abs_b.clone());
            let lam = ch.mk_lam(x_id, BinderInfo::Default, self.rat.clone(), body);
            ch.finish_child(lam)
        };
        let s1 = self.congr_arg(abs_a.clone(), ta.clone(), f1, e_a);
        // s2 : T_a·|b| = T_a·T_b   via congrArg (λx, mul T_a x) e_b
        let f2 = {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = ch.fresh_local(self.rat.clone());
            let body = self.mul(ta.clone(), x);
            let lam = ch.mk_lam(x_id, BinderInfo::Default, self.rat.clone(), body);
            ch.finish_child(lam)
        };
        let s2 = self.congr_arg(abs_b.clone(), tb.clone(), f2, e_b);
        let mul_absa_absb = self.mul(abs_a, abs_b.clone());
        let mul_ta_absb = self.mul(ta.clone(), abs_b);
        let mul_ta_tb = self.mul(ta.clone(), tb.clone());
        self.trans(mul_absa_absb, mul_ta_absb, mul_ta_tb, s1, s2)
    }
}

impl Environment {
    /// Initialize the dependencies needed by the `Rat.abs_mul` proof term.
    ///
    /// Pulls in the FAITHFUL `Rat.abs` carrier + `abs_of_nonneg` (easy batch),
    /// the lattice/order lemmas, and the multiplicative sign lemmas
    /// (`Rat.mul_nonneg`, `Rat.mul_neg`, `Rat.mul_comm`). Every registrar is
    /// idempotent.
    fn init_rat_abs_mul_proof_deps(&mut self) -> Result<(), EnvError> {
        // Faithful carrier + easy abs lemmas + lattice/order/add lemmas
        // (`Rat.max`, `Rat.max_def{,'}`, `Rat.le_trans`, `Rat.le_total`,
        // `Rat.neg_le_neg`, `Rat.add_left_neg`/`add_neg_self`/`add_right_cancel`/
        // `zero_add`). `register_rat_abs_proofs_easy` runs all of these via
        // `init_rat_abs_proof_deps`.
        self.register_rat_abs_proofs_easy()?;
        // `Rat.mul_neg` (+ `Rat.add_neg_self`, sub lemmas).
        self.init_nn_verify_rat_ordering()?;
        // `Rat.mul_nonneg` / `Rat.le_total` / `Rat.mul_pos` (quotient order).
        self.register_rat_order_proofs()?;
        // `Rat.mul_comm`.
        self.register_rat_mul_comm_proof()?;
        Ok(())
    }

    /// Register `Rat.abs_mul` as a kernel-checked constructive
    /// `Declaration::Theorem`, replacing the prior honest admitted
    /// `Declaration::Axiom` in `algebra_abs.rs::init_rat_abs`.
    ///
    /// `∀ a b : Rat, Eq Rat (Rat.abs (Rat.mul a b)) (Rat.mul (Rat.abs a) (Rat.abs b))`.
    ///
    /// # Contract
    ///
    /// ENSURES: On success, `Rat.abs_mul` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Rat.abs_mul` is already a `Theorem`, returns
    ///          `Ok(())` unchanged.
    pub(crate) fn register_rat_abs_mul_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.abs_mul");
        if self.get_const(&name).map(|i| i.kind) == Some(crate::env::types::ConstantKind::Theorem) {
            return Ok(());
        }
        self.init_rat_abs_mul_proof_deps()?;
        let c = RatAbsMulConsts::new();

        let type_ = build_abs_mul_type(&c);
        let value = build_abs_mul_value(&c);

        // SOUNDNESS: Real kernel-checked proof term over the FAITHFUL
        // `Rat.abs q := Rat.max q (Rat.neg q)` carrier. Four-way sign-case
        // (`@Or.rec` on `Rat.le_total Rat.zero a`, nested on `… b`); each leaf
        // derives the sign of `a·b` from `Rat.mul_nonneg` + the inline
        // `Rat.neg_mul`/`Rat.neg_mul_neg` (built from `Rat.mul_comm`,
        // `Rat.mul_neg`, the `add_right_cancel` `neg_neg`), characterizes
        // `Rat.abs` via `Rat.max_def{,'}`, and closes `|a·b| = |a|·|b|` by
        // `Eq.trans`/`Eq.symm`/`congrArg`. No `sorry`, no self-reference, no
        // `Declaration::Axiom` in the closure (`ProofQuality::Constructive`).
        // Eliminates the last `Rat.abs_*` Soundness-Certificate TCB axiom.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

/// `∀ a b : Rat, Eq Rat (Rat.abs (Rat.mul a b)) (Rat.mul (Rat.abs a) (Rat.abs b))`.
///
/// Stated with the genuine `Rat.abs` constant so the registered Theorem type is
/// byte-identical to the eliminated axiom's type (`Rat.abs` is a reducible
/// Definition def-eq to `Rat.max _ (Rat.neg _)`, so the `max`-form proof value
/// still checks against it).
fn build_abs_mul_type(c: &RatAbsMulConsts) -> Expr {
    let rat_abs = Expr::const_(Name::from_string("Rat.abs"), vec![]);
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let lhs = Expr::app(rat_abs.clone(), c.mul(a.clone(), bv.clone()));
    let rhs = c.mul(
        Expr::app(rat_abs.clone(), a.clone()),
        Expr::app(rat_abs.clone(), bv.clone()),
    );
    let concl = c.eq(lhs, rhs);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), concl);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// `λ a b => @Or.rec _ _ (motive) left right (le_total 0 a)` where each branch
/// nests another `@Or.rec` on `le_total 0 b`.
fn build_abs_mul_value(c: &RatAbsMulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());

    // Goal at (a, b): |a·b| = |a|·|b|.
    let goal = {
        let p = c.mul(a.clone(), bv.clone());
        c.eq(c.abs(p), c.mul(c.abs(a.clone()), c.abs(bv.clone())))
    };

    // le_total 0 a : Or (0 ≤ a) (a ≤ 0).
    let le_0_a = c.le(c.rat_zero.clone(), a.clone());
    let le_a_0 = c.le(a.clone(), c.rat_zero.clone());
    let total_a = Expr::apps(c.le_total.clone(), [c.rat_zero.clone(), a.clone()]);

    // Outer Or motive: λ (_ : Or (0≤a)(a≤0)) => goal.
    let outer_motive = {
        let mut om = EnvDeclBuilder::child_of(&b);
        let or_ty = Expr::apps(c.or_c.clone(), [le_0_a.clone(), le_a_0.clone()]);
        let (h_id, _h) = om.fresh_local(or_ty.clone());
        let lam = om.mk_lam(h_id, BinderInfo::Default, or_ty, goal.clone());
        om.finish_child(lam)
    };

    // Helper to build the inner Or.rec on b, given the outer sign fact for a.
    // `a_nonneg` selects which abs characterization / product identity to use.
    let inner_rec = |parent: &EnvDeclBuilder, a_nonneg: bool, h_a: &Expr| -> Expr {
        let le_0_b = c.le(c.rat_zero.clone(), bv.clone());
        let le_b_0 = c.le(bv.clone(), c.rat_zero.clone());
        let total_b = Expr::apps(c.le_total.clone(), [c.rat_zero.clone(), bv.clone()]);

        // Inner Or motive: λ (_ : Or (0≤b)(b≤0)) => goal.
        let inner_motive = {
            let mut im = EnvDeclBuilder::child_of(parent);
            let or_ty = Expr::apps(c.or_c.clone(), [le_0_b.clone(), le_b_0.clone()]);
            let (h_id, _h) = im.fresh_local(or_ty.clone());
            let lam = im.mk_lam(h_id, BinderInfo::Default, or_ty, goal.clone());
            im.finish_child(lam)
        };

        // Build one leaf for a fixed pair of signs.
        let leaf = |hyp_b_ty: Expr, b_nonneg: bool| -> Expr {
            let mut lb = EnvDeclBuilder::child_of(parent);
            let (hb_id, h_b) = lb.fresh_local(hyp_b_ty.clone());

            let p = c.mul(a.clone(), bv.clone()); // a·b
            let neg_p = c.neg(p.clone());
            let neg_a = c.neg(a.clone());
            let neg_b = c.neg(bv.clone());

            // e_a : |a| = T_a ; T_a is `a` (nonneg) or `-a` (nonpos).
            let (ta, e_a) = if a_nonneg {
                (a.clone(), c.abs_of_nonneg(&lb, &a, h_a.clone()))
            } else {
                (neg_a.clone(), c.abs_of_nonpos(&lb, &a, h_a.clone()))
            };
            // e_b : |b| = T_b.
            let (tb, e_b) = if b_nonneg {
                (bv.clone(), c.abs_of_nonneg(&lb, &bv, h_b.clone()))
            } else {
                (neg_b.clone(), c.abs_of_nonpos(&lb, &bv, h_b.clone()))
            };

            // Product identity `prod_id : T_a·T_b = S` and `0 ≤ S` / `S ≤ 0`
            // bridge to determine `|P|`.
            //
            // S is the signed product:
            //   (+,+) -> P=a·b,  prod: a·b = a·b (refl)
            //   (+,-) -> -P,     prod: a·(-b) = -(a·b) (mul_neg)
            //   (-,+) -> -P,     prod: (-a)·b = -(a·b) (neg_mul)
            //   (-,-) -> P,      prod: (-a)·(-b) = a·b (neg_mul_neg)
            let mul_ta_tb = c.mul(ta.clone(), tb.clone());

            // (s_val, prod_id : T_a·T_b = S, e_absP : |P| = S)
            let (s_val, prod_id, e_abs_p) = if a_nonneg && b_nonneg {
                // S = P. prod_id: a·b = a·b (refl). |P|=P via abs_of_nonneg P (0≤P).
                let refl = {
                    let eq_refl = Expr::const_(
                        Name::from_string("Eq.refl"),
                        vec![Level::succ(Level::zero())],
                    );
                    Expr::apps(eq_refl, [c.rat.clone(), p.clone()])
                };
                let h_0_le_p = c.mul_nonneg(a.clone(), bv.clone(), h_a.clone(), h_b.clone());
                let e_abs = c.abs_of_nonneg(&lb, &p, h_0_le_p);
                (p.clone(), refl, e_abs)
            } else if a_nonneg && !b_nonneg {
                // S = -P. prod_id: a·(-b) = -(a·b) (mul_neg a b).
                let prod = c.mul_neg(a.clone(), bv.clone());
                // 0 ≤ a·(-b) = -P : mul_nonneg a (-b) (0≤a) (0≤-b).
                let h_0_le_neg_b = c.zero_le_neg_of_le_zero(&lb, &bv, h_b.clone());
                let h_0_le_a_negb =
                    c.mul_nonneg(a.clone(), neg_b.clone(), h_a.clone(), h_0_le_neg_b);
                // rewrite a·(-b) → -P along prod : 0 ≤ -P
                let motive = {
                    let mut ch = EnvDeclBuilder::child_of(&lb);
                    let (y_id, y) = ch.fresh_local(c.rat.clone());
                    let body = c.le(c.rat_zero.clone(), y);
                    let lam = ch.mk_lam(y_id, BinderInfo::Default, c.rat.clone(), body);
                    ch.finish_child(lam)
                };
                let a_neg_b = c.mul(a.clone(), neg_b.clone());
                let h_0_le_neg_p =
                    c.subst(motive, a_neg_b, neg_p.clone(), prod.clone(), h_0_le_a_negb);
                let h_p_le_0 = c.le_zero_of_zero_le_neg(&lb, &p, h_0_le_neg_p);
                let e_abs = c.abs_of_nonpos(&lb, &p, h_p_le_0);
                (neg_p.clone(), prod, e_abs)
            } else if !a_nonneg && b_nonneg {
                // S = -P. prod_id: (-a)·b = -(a·b) (neg_mul a b).
                let prod = c.neg_mul_eq(&lb, &a, &bv);
                let h_0_le_neg_a = c.zero_le_neg_of_le_zero(&lb, &a, h_a.clone());
                let h_0_le_nega_b =
                    c.mul_nonneg(neg_a.clone(), bv.clone(), h_0_le_neg_a, h_b.clone());
                let motive = {
                    let mut ch = EnvDeclBuilder::child_of(&lb);
                    let (y_id, y) = ch.fresh_local(c.rat.clone());
                    let body = c.le(c.rat_zero.clone(), y);
                    let lam = ch.mk_lam(y_id, BinderInfo::Default, c.rat.clone(), body);
                    ch.finish_child(lam)
                };
                let nega_b = c.mul(neg_a.clone(), bv.clone());
                let h_0_le_neg_p =
                    c.subst(motive, nega_b, neg_p.clone(), prod.clone(), h_0_le_nega_b);
                let h_p_le_0 = c.le_zero_of_zero_le_neg(&lb, &p, h_0_le_neg_p);
                let e_abs = c.abs_of_nonpos(&lb, &p, h_p_le_0);
                (neg_p.clone(), prod, e_abs)
            } else {
                // (-,-) S = P. prod_id: (-a)·(-b) = a·b (neg_mul_neg a b).
                let prod = c.neg_mul_neg_eq(&lb, &a, &bv);
                let h_0_le_neg_a = c.zero_le_neg_of_le_zero(&lb, &a, h_a.clone());
                let h_0_le_neg_b = c.zero_le_neg_of_le_zero(&lb, &bv, h_b.clone());
                let h_0_le_nega_negb =
                    c.mul_nonneg(neg_a.clone(), neg_b.clone(), h_0_le_neg_a, h_0_le_neg_b);
                let motive = {
                    let mut ch = EnvDeclBuilder::child_of(&lb);
                    let (y_id, y) = ch.fresh_local(c.rat.clone());
                    let body = c.le(c.rat_zero.clone(), y);
                    let lam = ch.mk_lam(y_id, BinderInfo::Default, c.rat.clone(), body);
                    ch.finish_child(lam)
                };
                let nega_negb = c.mul(neg_a.clone(), neg_b.clone());
                let h_0_le_p =
                    c.subst(motive, nega_negb, p.clone(), prod.clone(), h_0_le_nega_negb);
                let e_abs = c.abs_of_nonneg(&lb, &p, h_0_le_p);
                (p.clone(), prod, e_abs)
            };

            // e_prod : |a|·|b| = S = trans (|a|·|b| = T_a·T_b) (T_a·T_b = S).
            let congr = c.mul_abs_congr(&lb, &a, &bv, &ta, &tb, e_a, e_b);
            let mul_absa_absb = c.mul(c.abs(a.clone()), c.abs(bv.clone()));
            let e_prod = c.trans(
                mul_absa_absb.clone(),
                mul_ta_tb.clone(),
                s_val.clone(),
                congr,
                prod_id,
            );
            // goal : |P| = |a|·|b| = trans e_absP (symm e_prod).
            let abs_p = c.abs(p.clone());
            let e_prod_sym = c.symm(mul_absa_absb.clone(), s_val.clone(), e_prod);
            let body = c.trans(abs_p, s_val, mul_absa_absb, e_abs_p, e_prod_sym);

            lb.mk_lam(hb_id, BinderInfo::Default, hyp_b_ty, body)
        };

        let left_b = leaf(le_0_b.clone(), true);
        let right_b = leaf(le_b_0.clone(), false);

        Expr::apps(
            c.or_rec.clone(),
            [le_0_b, le_b_0, inner_motive, left_b, right_b, total_b],
        )
    };

    // Outer left branch: 0 ≤ a.
    let left_a = {
        let mut la = EnvDeclBuilder::child_of(&b);
        let (ha_id, h_a) = la.fresh_local(le_0_a.clone());
        let inner = inner_rec(&la, true, &h_a);
        let lam = la.mk_lam(ha_id, BinderInfo::Default, le_0_a.clone(), inner);
        la.finish_child(lam)
    };
    // Outer right branch: a ≤ 0.
    let right_a = {
        let mut ra = EnvDeclBuilder::child_of(&b);
        let (ha_id, h_a) = ra.fresh_local(le_a_0.clone());
        let inner = inner_rec(&ra, false, &h_a);
        let lam = ra.mk_lam(ha_id, BinderInfo::Default, le_a_0.clone(), inner);
        ra.finish_child(lam)
    };

    let outer_rec = Expr::apps(
        c.or_rec.clone(),
        [le_0_a, le_a_0, outer_motive, left_a, right_a, total_a],
    );

    let lam = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), outer_rec);
    let lam = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), lam);
    b.finish(lam)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};
    use crate::tc::TypeChecker;

    fn registered_env() -> Environment {
        let mut env = Environment::new();
        env.register_rat_abs_mul_proof()
            .expect("register_rat_abs_mul_proof should succeed");
        env
    }

    #[test]
    fn test_rat_abs_mul_is_constructive_theorem() {
        let env = registered_env();
        let info = env
            .get_const(&Name::from_string("Rat.abs_mul"))
            .expect("Rat.abs_mul should be registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "Rat.abs_mul must be a kernel-checked Theorem, got {:?}",
            info.kind
        );
        assert!(
            info.value.is_some(),
            "Rat.abs_mul Theorem must retain its proof value"
        );
        let q = env
            .proof_quality(&Name::from_string("Rat.abs_mul"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(q, ProofQuality::Constructive),
            "Rat.abs_mul must be Constructive (no domain axiom in closure), got {q:?}"
        );
    }

    #[test]
    fn test_rat_abs_mul_kernel_type_checks() {
        let env = registered_env();
        let info = env
            .get_const(&Name::from_string("Rat.abs_mul"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let tc = TypeChecker::new(&env);
        let inferred = tc
            .infer_type(value)
            .expect("proof term must type-check in the kernel");
        assert!(
            tc.is_def_eq(&inferred, &info.type_),
            "inferred type must match the declared Rat.abs_mul type"
        );
    }

    #[test]
    fn test_rat_abs_mul_axiom_deps_empty() {
        let env = registered_env();
        let deps = env
            .axiom_deps(&Name::from_string("Rat.abs_mul"))
            .expect("Rat.abs_mul is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Rat.abs_mul must have empty domain-axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }

    #[test]
    fn test_rat_abs_mul_idempotent() {
        let mut env = Environment::new();
        env.register_rat_abs_mul_proof()
            .expect("first registration");
        env.register_rat_abs_mul_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Rat.abs_mul"))
            .expect("Rat.abs_mul should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
    }

    #[test]
    fn test_rat_abs_mul_wins_over_axiom_in_init_rat_abs() {
        // `init_rat_abs` must register the THEOREM (not the legacy axiom).
        let mut env = Environment::new();
        env.init_rat_abs().expect("init_rat_abs should succeed");
        let info = env
            .get_const(&Name::from_string("Rat.abs_mul"))
            .expect("Rat.abs_mul should be registered by init_rat_abs");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "init_rat_abs must register Rat.abs_mul as a Theorem, got {:?}",
            info.kind
        );
    }
}
