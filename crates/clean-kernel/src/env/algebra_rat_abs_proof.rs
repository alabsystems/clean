// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TCB-shrink Tier 1: genuine, kernel-checked elimination of the opaque
//! `Rat.abs` identity carrier and the `Rat.abs_*` lemma axioms over the SOUND
//! quotient `Rat := @Quot.{1} Rat.Raw Rat.Raw.Equiv`.
//!
//! # The latent soundness bug this fixes
//!
//! Before this module, `Rat.abs` was a `Declaration::Opaque` with the IDENTITY
//! body `fun a : Rat => a` (#3435 / #3565). Semantically that body means
//! `|q| = q`, so the lemma `Rat.abs_nonneg : ∀ q, 0 ≤ |q|` reads `∀ q, 0 ≤ q`
//! — which is FALSE for any negative `q` (e.g. `q = -1`). The axiom was not
//! *syntactically* refutable only because the carrier was `Opaque` (its body
//! does not δ-reduce during `def_eq`, so the carrier-refutation engine got
//! stuck and reported "non-refutable"). That is a latent unsoundness masked by
//! opacity: the admitted axiom is false in the intended model.
//!
//! # The fix
//!
//! Replace the carrier with the FAITHFUL reducible Definition
//! `Rat.abs q := Rat.max q (Rat.neg q)` (`= q` when `0 ≤ q`, `= -q` when
//! `q ≤ 0`; the standard `|q| = max q (-q)` identity). Over this real body the
//! `Rat.abs_*` propositions are genuine arithmetic facts, PROVED here as
//! kernel-checked constructive `Declaration::Theorem`s reusing the landed sound
//! quotient lattice/order lemmas (`Rat.max_def{,'}`, `Rat.le_max_left/right`,
//! `Rat.max_le`, `Rat.le_total/le_trans/le_refl`, `Rat.neg_le_neg`,
//! `Rat.add_le_add`). No `Rat.abs_*` axiom remains for the proven lemmas, so
//! they leave the Soundness-Certificate TCB.
//!
//! Easy batch (`register_rat_abs_proofs_easy`): `abs_of_nonneg`, `abs_of_neg`,
//! `abs_zero`, `abs_nonneg`, `abs_neg`. Hard batch
//! (`register_rat_abs_proofs_hard`): the triangle inequalities `abs_add_le`
//! (via `max_le` + `add_le_add` + an inline `neg_add : -(a+b) = -a + -b`) and
//! `abs_sub_le` (corollary: `a - b ≡ a + (-b)`, `abs_add_le a (-b)` + `abs_neg
//! b`). DEFERRED: `Rat.abs_mul` stays an honest admitted `Declaration::Axiom`
//! over the REAL carrier — non-refutable and true in the model, but a faithful
//! proof needs four-way sign-case multiplicative monotonicity not yet available
//! over the quotient.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached constants + smart-constructors for the `Rat.abs` proof terms.
pub(super) struct RatAbsConsts {
    rat: Expr,
    rat_zero: Expr,
    // Arithmetic (reducible Definitions).
    rat_add: Expr,
    rat_neg: Expr,
    rat_max: Expr,
    // Order (Prop-valued).
    rat_le: Expr,
    // Eq machinery (Rat lives in Sort 1).
    eq_c: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    eq_subst: Expr,
    congr_arg: Expr,
    // Landed sound quotient lemmas.
    le_refl: Expr,
    le_trans: Expr,
    le_total: Expr,
    le_max_left: Expr,
    le_max_right: Expr,
    max_le: Expr,
    max_def: Expr,
    max_def_prime: Expr,
    neg_le_neg: Expr,
    add_le_add: Expr,
    add_left_neg: Expr,
    add_neg_self: Expr,
    add_right_cancel: Expr,
    add_assoc: Expr,
    add_comm: Expr,
    add_zero: Expr,
    zero_add: Expr,
    // Logic.
    or_c: Expr,
    or_rec: Expr,
}

impl RatAbsConsts {
    pub(super) fn new() -> Self {
        let t1 = Level::succ(Level::zero());
        let c = |n: &str| Expr::const_(Name::from_string(n), vec![]);
        Self {
            rat: c("Rat"),
            rat_zero: c("Rat.zero"),
            rat_add: c("Rat.add"),
            rat_neg: c("Rat.neg"),
            rat_max: c("Rat.max"),
            rat_le: c("Rat.le"),
            eq_c: Expr::const_(Name::from_string("Eq"), vec![t1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![t1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![t1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![t1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![t1.clone(), t1]),
            le_refl: c("Rat.le_refl"),
            le_trans: c("Rat.le_trans"),
            le_total: c("Rat.le_total"),
            le_max_left: c("Rat.le_max_left"),
            le_max_right: c("Rat.le_max_right"),
            max_le: c("Rat.max_le"),
            max_def: c("Rat.max_def"),
            max_def_prime: c("Rat.max_def'"),
            neg_le_neg: c("Rat.neg_le_neg"),
            add_le_add: c("Rat.add_le_add"),
            add_left_neg: c("Rat.add_left_neg"),
            add_neg_self: c("Rat.add_neg_self"),
            add_right_cancel: c("Rat.add_right_cancel"),
            add_assoc: c("Rat.add_assoc"),
            add_comm: c("Rat.add_comm"),
            add_zero: c("Rat.add_zero"),
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
    fn max(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.rat_max.clone(), [x, y])
    }
    /// `Rat.abs x` written directly as its carrier `Rat.max x (Rat.neg x)` so
    /// proof terms can talk about the unfolded form (the registered `Rat.abs`
    /// is a reducible Definition equal to this, so the two are def-eq).
    fn abs(&self, x: Expr) -> Expr {
        self.max(x.clone(), self.neg(x))
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
    fn le_refl(&self, x: Expr) -> Expr {
        Expr::app(self.le_refl.clone(), x)
    }
    fn le_trans(&self, x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.le_trans.clone(), [x, y, z, h1, h2])
    }
    fn neg_le_neg(&self, x: Expr, y: Expr, h: Expr) -> Expr {
        Expr::apps(self.neg_le_neg.clone(), [x, y, h])
    }

    /// Inline `e : Rat.neg Rat.zero = Rat.zero` via the `add_right_cancel`
    /// trick: `-0 + 0 = 0 = 0 + 0`, cancel `0`.
    fn neg_zero_eq(&self) -> Expr {
        let z = self.rat_zero.clone();
        let neg_z = self.neg(z.clone());
        // h_l : -0 + 0 = 0   via add_left_neg 0
        let h_l = Expr::app(self.add_left_neg.clone(), z.clone());
        // h_r : 0 + 0 = 0    via zero_add 0
        let h_r = Expr::app(self.zero_add.clone(), z.clone());
        // h_r_sym : 0 = 0 + 0
        let zero_plus_zero = self.add(z.clone(), z.clone());
        let h_r_sym = self.symm(zero_plus_zero.clone(), z.clone(), h_r);
        // h_comb : -0 + 0 = 0 + 0
        let neg_z_plus_zero = self.add(neg_z.clone(), z.clone());
        let h_comb = self.trans(neg_z_plus_zero, z.clone(), zero_plus_zero, h_l, h_r_sym);
        // add_right_cancel (-0) 0 0 h_comb : -0 = 0
        Expr::apps(self.add_right_cancel.clone(), [neg_z, z.clone(), z, h_comb])
    }

    /// Inline `e : Rat.neg (Rat.neg x) = x` via the `add_right_cancel` trick:
    /// `-(-x) + (-x) = 0 = x + (-x)`, cancel `-x`.
    fn neg_neg_eq(&self, x: Expr) -> Expr {
        let neg_x = self.neg(x.clone());
        let neg_neg_x = self.neg(neg_x.clone());
        // h_l : -(-x) + (-x) = 0   via add_left_neg (-x)
        let h_l = Expr::app(self.add_left_neg.clone(), neg_x.clone());
        // h_r : x + (-x) = 0       via add_neg_self x
        let h_r = Expr::app(self.add_neg_self.clone(), x.clone());
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

    /// `0 ≤ Rat.neg x` from `h : x ≤ 0`. Uses `neg_le_neg x 0 h : -0 ≤ -x`,
    /// transported along `neg_zero : -0 = 0` with motive `λ y, y ≤ -x`.
    fn zero_le_neg_of_le_zero(&self, parent: &EnvDeclBuilder, x: &Expr, h_x_le_0: Expr) -> Expr {
        let neg_x = self.neg(x.clone());
        let neg_zero = self.neg(self.rat_zero.clone());
        // neg_le_neg x 0 h : -0 ≤ -x
        let h_negzero_le_negx = self.neg_le_neg(x.clone(), self.rat_zero.clone(), h_x_le_0);
        // motive : λ y, y ≤ -x
        let motive = {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (y_id, y) = ch.fresh_local(self.rat.clone());
            let body = self.le(y, neg_x.clone());
            let lam = ch.mk_lam(y_id, BinderInfo::Default, self.rat.clone(), body);
            ch.finish_child(lam)
        };
        // subst rewriting `-0 → 0` : 0 ≤ -x
        self.subst(
            motive,
            neg_zero,
            self.rat_zero.clone(),
            self.neg_zero_eq(),
            h_negzero_le_negx,
        )
    }

    /// `Rat.neg x ≤ 0` from `h : 0 ≤ x`. Uses `neg_le_neg 0 x h : -x ≤ -0`,
    /// transported along `neg_zero : -0 = 0` with motive `λ y, -x ≤ y`.
    fn neg_le_zero_of_zero_le(&self, parent: &EnvDeclBuilder, x: &Expr, h_0_le_x: Expr) -> Expr {
        let neg_x = self.neg(x.clone());
        let neg_zero = self.neg(self.rat_zero.clone());
        // neg_le_neg 0 x h : -x ≤ -0
        let h_negx_le_negzero = self.neg_le_neg(self.rat_zero.clone(), x.clone(), h_0_le_x);
        let motive = {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (y_id, y) = ch.fresh_local(self.rat.clone());
            let body = self.le(neg_x.clone(), y);
            let lam = ch.mk_lam(y_id, BinderInfo::Default, self.rat.clone(), body);
            ch.finish_child(lam)
        };
        self.subst(
            motive,
            neg_zero,
            self.rat_zero.clone(),
            self.neg_zero_eq(),
            h_negx_le_negzero,
        )
    }

    // ── hard-batch builders ─────────────────────────────────────────────────

    fn le_max_left(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.le_max_left.clone(), [x, y])
    }
    fn le_max_right(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.le_max_right.clone(), [x, y])
    }
    /// `Rat.max_le a b c h1 h2 : Rat.le (Rat.max a b) c`.
    fn max_le(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.max_le.clone(), [a, b, c, h1, h2])
    }
    /// `Rat.add_le_add a b c d h1 h2 : Rat.le (Rat.add a c) (Rat.add b d)`.
    fn add_le_add(&self, a: Expr, b: Expr, c: Expr, d: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.add_le_add.clone(), [a, b, c, d, h1, h2])
    }
    /// `Rat.add_assoc a b c : (a+b)+c = a+(b+c)`.
    fn add_assoc(&self, a: Expr, b: Expr, c: Expr) -> Expr {
        Expr::apps(self.add_assoc.clone(), [a, b, c])
    }
    /// `Rat.add_comm a b : a+b = b+a`.
    fn add_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.add_comm.clone(), [a, b])
    }

    /// Inline `K : (Rat.neg a + Rat.neg b) + (a + b) = Rat.zero`.
    ///
    /// Chain: `(-a + -b) + (a+b) = -a + (-b + (a+b))` [assoc]
    ///        `-b + (a+b) = a`                          [`neg_b_plus_sum_eq`]
    ///        `-a + (-b + (a+b)) = -a + a`              [congrArg]
    ///        `-a + a = 0`                              [add_left_neg]
    fn neg_sum_plus_sum_zero(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr) -> Expr {
        let neg_a = self.neg(a.clone());
        let neg_b = self.neg(b.clone());
        let sum = self.add(a.clone(), b.clone());
        let neg_sum_neg = self.add(neg_a.clone(), neg_b.clone());
        let inner = self.add(neg_b.clone(), sum.clone()); // -b + (a+b)
                                                          // e1 : (-a + -b) + (a+b) = -a + (-b + (a+b))   via add_assoc
        let e1 = self.add_assoc(neg_a.clone(), neg_b.clone(), sum.clone());
        // e2 : -b + (a+b) = a
        let e2 = self.neg_b_plus_sum_eq(parent, a, b);
        // e3 : -a + (-b + (a+b)) = -a + a   via congrArg (λ x, -a + x) e2
        let f3 = {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = ch.fresh_local(self.rat.clone());
            let body = self.add(neg_a.clone(), x);
            let lam = ch.mk_lam(x_id, BinderInfo::Default, self.rat.clone(), body);
            ch.finish_child(lam)
        };
        let neg_a_plus_inner = self.add(neg_a.clone(), inner.clone());
        let neg_a_plus_a = self.add(neg_a.clone(), a.clone());
        let e3 = self.congr_arg(inner.clone(), a.clone(), f3, e2);
        // e4 : -a + a = 0   via add_left_neg a
        let e4 = Expr::app(self.add_left_neg.clone(), a.clone());
        // K = trans e1 (trans e3 e4)
        let inner_trans = self.trans(
            neg_a_plus_inner.clone(),
            neg_a_plus_a,
            self.rat_zero.clone(),
            e3,
            e4,
        );
        // Whole-chain LHS is `(-a + -b) + (a+b)` (the LHS of e1), NOT `-a + -b`.
        let neg_sum_neg_plus_sum = self.add(neg_sum_neg, sum);
        self.trans(
            neg_sum_neg_plus_sum,
            neg_a_plus_inner,
            self.rat_zero.clone(),
            e1,
            inner_trans,
        )
    }

    /// Inline `e2 : Rat.neg b + (a + b) = a`.
    ///
    /// Chain: `-b + (a+b) = -b + (b+a)`     [congrArg via add_comm a b]
    ///        `-b + (b+a) = (-b + b) + a`    [symm add_assoc]
    ///        `(-b + b) + a = 0 + a`         [congrArg via add_left_neg b]
    ///        `0 + a = a`                    [zero_add]
    fn neg_b_plus_sum_eq(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr) -> Expr {
        let neg_b = self.neg(b.clone());
        let a_plus_b = self.add(a.clone(), b.clone());
        let b_plus_a = self.add(b.clone(), a.clone());
        // s1 : -b + (a+b) = -b + (b+a)   via congrArg (λ x, -b + x) (add_comm a b)
        let f1 = {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = ch.fresh_local(self.rat.clone());
            let body = self.add(neg_b.clone(), x);
            let lam = ch.mk_lam(x_id, BinderInfo::Default, self.rat.clone(), body);
            ch.finish_child(lam)
        };
        let s1 = self.congr_arg(
            a_plus_b.clone(),
            b_plus_a.clone(),
            f1,
            self.add_comm(a.clone(), b.clone()),
        );
        // s2 : -b + (b+a) = (-b + b) + a   via symm (add_assoc (-b) b a)
        let assoc = self.add_assoc(neg_b.clone(), b.clone(), a.clone()); // (-b+b)+a = -b+(b+a)
        let neg_b_b = self.add(neg_b.clone(), b.clone());
        let lhs_assoc = self.add(neg_b_b.clone(), a.clone()); // (-b+b)+a
        let rhs_assoc = self.add(neg_b.clone(), b_plus_a.clone()); // -b+(b+a)
        let s2 = self.symm(lhs_assoc.clone(), rhs_assoc.clone(), assoc);
        // s3 : (-b + b) + a = 0 + a   via congrArg (λ x, x + a) (add_left_neg b)
        let f3 = {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = ch.fresh_local(self.rat.clone());
            let body = self.add(x, a.clone());
            let lam = ch.mk_lam(x_id, BinderInfo::Default, self.rat.clone(), body);
            ch.finish_child(lam)
        };
        let add_left_neg_b = Expr::app(self.add_left_neg.clone(), b.clone()); // -b+b = 0
        let zero_plus_a = self.add(self.rat_zero.clone(), a.clone());
        let s3 = self.congr_arg(neg_b_b.clone(), self.rat_zero.clone(), f3, add_left_neg_b);
        // s4 : 0 + a = a   via zero_add a
        let s4 = Expr::app(self.zero_add.clone(), a.clone());
        // e2 = trans s1 (trans s2 (trans s3 s4))
        let inner_b = self.add(neg_b.clone(), a_plus_b.clone()); // -b+(a+b)
        let t34 = self.trans(lhs_assoc.clone(), zero_plus_a, a.clone(), s3, s4);
        let t234 = self.trans(rhs_assoc.clone(), lhs_assoc, a.clone(), s2, t34);
        self.trans(inner_b, rhs_assoc, a.clone(), s1, t234)
    }

    /// Inline `e : Rat.neg (Rat.add a b) = Rat.add (Rat.neg a) (Rat.neg b)`
    /// via `add_right_cancel (-(a+b)) (a+b) (-a + -b) H`, where
    /// `H : -(a+b) + (a+b) = (-a + -b) + (a+b)` is built from
    /// `add_left_neg (a+b)` and (symm of) `neg_sum_plus_sum_zero`.
    fn neg_add_eq(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr) -> Expr {
        let sum = self.add(a.clone(), b.clone());
        let neg_sum = self.neg(sum.clone());
        let neg_a = self.neg(a.clone());
        let neg_b = self.neg(b.clone());
        let neg_sum_neg = self.add(neg_a.clone(), neg_b.clone());
        // h_l : -(a+b) + (a+b) = 0
        let h_l = Expr::app(self.add_left_neg.clone(), sum.clone());
        // k : (-a + -b) + (a+b) = 0  ⇒  k_sym : 0 = (-a + -b) + (a+b)
        let k = self.neg_sum_plus_sum_zero(parent, a, b);
        let rhs_sum = self.add(neg_sum_neg.clone(), sum.clone());
        let k_sym = self.symm(rhs_sum.clone(), self.rat_zero.clone(), k);
        // H : -(a+b) + (a+b) = (-a + -b) + (a+b)
        let lhs_sum = self.add(neg_sum.clone(), sum.clone());
        let h = self.trans(lhs_sum, self.rat_zero.clone(), rhs_sum, h_l, k_sym);
        // add_right_cancel (-(a+b)) (a+b) (-a+-b) H : -(a+b) = -a + -b
        Expr::apps(
            self.add_right_cancel.clone(),
            [neg_sum, sum, neg_sum_neg, h],
        )
    }
}

impl Environment {
    /// Initialize dependencies needed by the `Rat.abs` proof terms: the sound
    /// quotient `Rat.max`/lattice lemmas, the order lemmas, and the
    /// `Rat.neg_le_neg`/`Rat.add_le_add` family.
    ///
    /// IMPORTANT (cycle break): we do NOT call
    /// `init_nn_verify_interval_arith_proofs` here even though it would supply
    /// `Rat.neg_le_neg` / `Rat.add_le_add` — that path transitively reaches
    /// `init_nn_verify_foundation_types → init_rat_abs`, and since this function
    /// runs from inside `init_rat_abs` (before its `rat_abs_init` flag is set),
    /// it would recurse. Instead we pull the two registrars directly after
    /// their lighter, abs-independent quotient-ordering prerequisites
    /// (`init_nn_verify_rat_ordering` supplies `Rat.sub_nonneg_of_le` /
    /// `Rat.le_of_sub_nonneg` / `Rat.add_comm` / `Rat.add_assoc` etc.).
    fn init_rat_abs_proof_deps(&mut self) -> Result<(), EnvError> {
        self.init_rat_ord()?; // Rat, Rat.le, Rat.lt, Rat.zero
        self.init_rat_arith()?; // Rat.add, Rat.neg, Rat.sub, Rat.mul
        self.init_eq()?; // Eq, Eq.refl/symm/trans/subst, congrArg
        self.init_or()?; // Or, Or.rec
        self.init_rat_linear_order()?; // instLERat (LE typeclass instance)
        self.register_rat_minmax_proofs()?; // Rat.max + lattice + le_total/le_trans/...
        self.init_nn_verify_rat_ordering()?; // Rat.sub_nonneg_of_le, le_of_sub_nonneg, add_comm/assoc
        self.register_rat_neg_le_neg()?; // Rat.neg_le_neg
        self.register_rat_add_le_add()?; // Rat.add_le_add
        Ok(())
    }

    /// EASY batch: flip `Rat.abs` to the faithful reducible Definition
    /// `Rat.max q (Rat.neg q)` and register the five tractable lemmas as
    /// kernel-checked constructive `Declaration::Theorem`s:
    /// `abs_of_nonneg`, `abs_of_neg`, `abs_zero`, `abs_nonneg`, `abs_neg`.
    ///
    /// Idempotent: each target is registered only if not already a Definition /
    /// Theorem, so the `init_rat_abs` axiom fallbacks become no-ops.
    pub(crate) fn register_rat_abs_proofs_easy(&mut self) -> Result<(), EnvError> {
        self.init_rat_abs_proof_deps()?;
        let c = RatAbsConsts::new();

        self.register_rat_abs_carrier(&c)?;
        self.register_rat_abs_of_nonneg(&c)?;
        self.register_rat_abs_of_neg(&c)?;
        self.register_rat_abs_zero(&c)?;
        self.register_rat_abs_nonneg(&c)?;
        self.register_rat_abs_neg(&c)?;
        Ok(())
    }

    /// `Rat.abs : Rat → Rat := fun a => Rat.max a (Rat.neg a)` — reducible
    /// Definition replacing the `Opaque` identity carrier.
    fn register_rat_abs_carrier(&mut self, c: &RatAbsConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.abs");
        if self.get_const(&name).map(|i| i.kind)
            == Some(crate::env::types::ConstantKind::Definition)
        {
            return Ok(());
        }
        // Replace any prior registration (the Opaque identity carrier) with the
        // faithful Definition. `add_decl` overwrites by name in this kernel.
        let ty = Expr::pi(BinderInfo::Default, c.rat.clone(), c.rat.clone());
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let body = c.max(a.clone(), c.neg(a.clone()));
            let lam = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), body);
            b.finish(lam)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `Rat.abs_of_nonneg : ∀ a, Rat.le Rat.zero a → Eq (Rat.abs a) a`.
    ///
    /// `abs a ≡ max a (-a)`. From `0 ≤ a` get `-a ≤ 0 ≤ a` (so `-a ≤ a`), then
    /// `max_def' a (-a) (-a ≤ a) : max a (-a) = a`.
    fn register_rat_abs_of_nonneg(&mut self, c: &RatAbsConsts) -> Result<(), EnvError> {
        let nm = Name::from_string("Rat.abs_of_nonneg");
        if self.is_already_theorem(&nm) {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let hyp = c.le(c.rat_zero.clone(), a.clone());
            let (h_id, _) = b.fresh_local(hyp.clone());
            let concl = c.eq(c.abs(a.clone()), a.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let hyp = c.le(c.rat_zero.clone(), a.clone());
            let (h_id, h) = b.fresh_local(hyp.clone());
            // neg_a_le_0 : -a ≤ 0
            let neg_a_le_0 = c.neg_le_zero_of_zero_le(&b, &a, h.clone());
            // neg_a_le_a : -a ≤ a   via le_trans (-a) 0 a (neg_a_le_0) h
            let neg_a = c.neg(a.clone());
            let neg_a_le_a =
                c.le_trans(neg_a.clone(), c.rat_zero.clone(), a.clone(), neg_a_le_0, h);
            // max_def' a (-a) (neg_a_le_a) : max a (-a) = a
            let body = Expr::apps(c.max_def_prime.clone(), [a.clone(), neg_a, neg_a_le_a]);
            let e = b.mk_lam(h_id, BinderInfo::Default, hyp, body);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: nm,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.abs_of_neg : ∀ a, Rat.lt a Rat.zero → Eq (Rat.abs a) (Rat.neg a)`.
    ///
    /// `abs a ≡ max a (-a)`. From `a < 0` extract `a ≤ 0` (via the `And.left`
    /// of `Rat.lt_iff_le_not_le`), get `0 ≤ -a` (so `a ≤ -a`), then
    /// `max_def a (-a) (a ≤ -a) : max a (-a) = -a`.
    fn register_rat_abs_of_neg(&mut self, c: &RatAbsConsts) -> Result<(), EnvError> {
        let nm = Name::from_string("Rat.abs_of_neg");
        if self.is_already_theorem(&nm) {
            return Ok(());
        }
        let rat_lt = Expr::const_(Name::from_string("Rat.lt"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let hyp = Expr::apps(rat_lt.clone(), [a.clone(), c.rat_zero.clone()]);
            let (h_id, _) = b.fresh_local(hyp.clone());
            let concl = c.eq(c.abs(a.clone()), c.neg(a.clone()));
            let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let hyp = Expr::apps(rat_lt.clone(), [a.clone(), c.rat_zero.clone()]);
            let (h_id, h) = b.fresh_local(hyp.clone());

            // a ≤ 0 := And.left _ _ (Iff.mp (lt_iff_le_not_le a 0) h)
            let le_a_0 = c.le(a.clone(), c.rat_zero.clone());
            let not_le_0_a = {
                let not_c = Expr::const_(Name::from_string("Not"), vec![]);
                Expr::app(not_c, c.le(c.rat_zero.clone(), a.clone()))
            };
            let lt_ab = Expr::apps(rat_lt.clone(), [a.clone(), c.rat_zero.clone()]);
            let and_le_notle = Expr::apps(
                Expr::const_(Name::from_string("And"), vec![]),
                [le_a_0.clone(), not_le_0_a.clone()],
            );
            let iff_mp = Expr::apps(
                Expr::const_(Name::from_string("Iff.mp"), vec![]),
                [
                    lt_ab.clone(),
                    and_le_notle.clone(),
                    Expr::apps(
                        Expr::const_(Name::from_string("Rat.lt_iff_le_not_le"), vec![]),
                        [a.clone(), c.rat_zero.clone()],
                    ),
                    h.clone(),
                ],
            );
            let h_a_le_0 = Expr::apps(
                Expr::const_(Name::from_string("And.left"), vec![]),
                [le_a_0.clone(), not_le_0_a, iff_mp],
            );
            // 0 ≤ -a
            let h_0_le_neg_a = c.zero_le_neg_of_le_zero(&b, &a, h_a_le_0.clone());
            // a ≤ -a := le_trans a 0 (-a) (a≤0) (0≤-a)
            let neg_a = c.neg(a.clone());
            let a_le_neg_a = c.le_trans(
                a.clone(),
                c.rat_zero.clone(),
                neg_a.clone(),
                h_a_le_0,
                h_0_le_neg_a,
            );
            // max_def a (-a) (a≤-a) : max a (-a) = -a
            let body = Expr::apps(c.max_def.clone(), [a.clone(), neg_a, a_le_neg_a]);
            let e = b.mk_lam(h_id, BinderInfo::Default, hyp, body);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: nm,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.abs_zero : Eq (Rat.abs Rat.zero) Rat.zero`.
    ///
    /// `abs 0 ≡ max 0 (-0)`. `-0 ≤ 0` (from `neg_zero` transported into
    /// `le_refl 0`), then `max_def' 0 (-0) (-0 ≤ 0) : max 0 (-0) = 0`.
    fn register_rat_abs_zero(&mut self, c: &RatAbsConsts) -> Result<(), EnvError> {
        let nm = Name::from_string("Rat.abs_zero");
        if self.is_already_theorem(&nm) {
            return Ok(());
        }
        let ty = c.eq(c.abs(c.rat_zero.clone()), c.rat_zero.clone());
        let value = {
            let mut b = EnvDeclBuilder::new();
            let zero = c.rat_zero.clone();
            let neg_zero = c.neg(zero.clone());
            // neg_zero_le_zero : -0 ≤ 0
            //   subst (λ y, y ≤ 0) (neg_zero : -0 = 0)⁻¹? — simpler: rewrite
            //   le_refl 0 : 0 ≤ 0 along (0 = -0) to get -0 ≤ 0.
            // Build (0 = -0) := symm neg_zero.
            let eq_neg0_0 = c.neg_zero_eq(); // -0 = 0
            let eq_0_neg0 = c.symm(neg_zero.clone(), zero.clone(), eq_neg0_0);
            let motive = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (y_id, y) = ch.fresh_local(c.rat.clone());
                let body = c.le(y, zero.clone());
                let lam = ch.mk_lam(y_id, BinderInfo::Default, c.rat.clone(), body);
                ch.finish_child(lam)
            };
            // subst motive 0 (-0) (0 = -0) (le_refl 0) : -0 ≤ 0
            let neg_zero_le_zero = c.subst(
                motive,
                zero.clone(),
                neg_zero.clone(),
                eq_0_neg0,
                c.le_refl(zero.clone()),
            );
            // max_def' 0 (-0) (-0 ≤ 0) : max 0 (-0) = 0
            let body = Expr::apps(
                c.max_def_prime.clone(),
                [zero.clone(), neg_zero, neg_zero_le_zero],
            );
            let _ = &mut b;
            body
        };
        self.add_decl(Declaration::Theorem {
            name: nm,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.abs_nonneg : ∀ a, Rat.le Rat.zero (Rat.abs a)`.
    ///
    /// `abs a ≡ max a (-a)`. Case-split `le_total 0 a`:
    /// * `0 ≤ a`: `a ≤ max a (-a)` (le_max_left) ⇒ `0 ≤ max` by transitivity.
    /// * `a ≤ 0`: `0 ≤ -a` and `-a ≤ max a (-a)` (le_max_right) ⇒ `0 ≤ max`.
    fn register_rat_abs_nonneg(&mut self, c: &RatAbsConsts) -> Result<(), EnvError> {
        let nm = Name::from_string("Rat.abs_nonneg");
        if self.is_already_theorem(&nm) {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let body = c.le(c.rat_zero.clone(), c.abs(a.clone()));
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), body);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let neg_a = c.neg(a.clone());
            let abs_a = c.abs(a.clone());
            let goal = c.le(c.rat_zero.clone(), abs_a.clone());

            // le_total 0 a : Or (0 ≤ a) (a ≤ 0)
            let le_0_a = c.le(c.rat_zero.clone(), a.clone());
            let le_a_0 = c.le(a.clone(), c.rat_zero.clone());
            let total = Expr::apps(c.le_total.clone(), [c.rat_zero.clone(), a.clone()]);

            // motive : λ (_ : Or ..) => 0 ≤ abs a
            let or_motive = {
                let mut om = EnvDeclBuilder::child_of(&b);
                let or_ty = Expr::apps(c.or_c.clone(), [le_0_a.clone(), le_a_0.clone()]);
                let (hh_id, _hh) = om.fresh_local(or_ty.clone());
                let lam = om.mk_lam(hh_id, BinderInfo::Default, or_ty, goal.clone());
                om.finish_child(lam)
            };
            // left: 0 ≤ a ⇒ le_trans 0 a (max..) h (le_max_left a (-a))
            let left_fn = {
                let mut lb = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = lb.fresh_local(le_0_a.clone());
                let le_a_max = Expr::apps(c.le_max_left.clone(), [a.clone(), neg_a.clone()]);
                let body = c.le_trans(c.rat_zero.clone(), a.clone(), abs_a.clone(), h, le_a_max);
                let lam = lb.mk_lam(h_id, BinderInfo::Default, le_0_a.clone(), body);
                lb.finish_child(lam)
            };
            // right: a ≤ 0 ⇒ (0 ≤ -a) then le_trans 0 (-a) (max..) (0≤-a) (le_max_right)
            let right_fn = {
                let mut rb = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = rb.fresh_local(le_a_0.clone());
                let h_0_le_neg_a = c.zero_le_neg_of_le_zero(&rb, &a, h);
                let le_neg_a_max = Expr::apps(c.le_max_right.clone(), [a.clone(), neg_a.clone()]);
                let body = c.le_trans(
                    c.rat_zero.clone(),
                    neg_a.clone(),
                    abs_a.clone(),
                    h_0_le_neg_a,
                    le_neg_a_max,
                );
                let lam = rb.mk_lam(h_id, BinderInfo::Default, le_a_0.clone(), body);
                rb.finish_child(lam)
            };
            let rec = Expr::apps(
                c.or_rec.clone(),
                [le_0_a, le_a_0, or_motive, left_fn, right_fn, total],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), rec);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: nm,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.abs_neg : ∀ a, Eq (Rat.abs (Rat.neg a)) (Rat.abs a)`.
    ///
    /// `abs (-a) ≡ max (-a) (-(-a))`, `abs a ≡ max a (-a)`. Prove equal by
    /// antisymmetry (`le_antisymm`) is avoidable: instead use `neg_neg` to
    /// rewrite `-(-a) → a` and then `max` commutativity.
    ///
    /// Concretely we show `max (-a) (-(-a)) = max a (-a)` by `Rat.le_antisymm`:
    /// each direction is a `max_le` whose two premises are `le_max_left` /
    /// `le_max_right` after transporting `-(-a) = a`.
    fn register_rat_abs_neg(&mut self, c: &RatAbsConsts) -> Result<(), EnvError> {
        let nm = Name::from_string("Rat.abs_neg");
        if self.is_already_theorem(&nm) {
            return Ok(());
        }
        let le_antisymm = Expr::const_(Name::from_string("Rat.le_antisymm"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let body = c.eq(c.abs(c.neg(a.clone())), c.abs(a.clone()));
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), body);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let neg_a = c.neg(a.clone());
            let neg_neg_a = c.neg(neg_a.clone());
            let lhs = c.max(neg_a.clone(), neg_neg_a.clone()); // abs (-a)
            let rhs = c.max(a.clone(), neg_a.clone()); // abs a

            // e_nna : -(-a) = a
            let e_nna = c.neg_neg_eq(a.clone());

            // Direction 1: lhs ≤ rhs  via max_le (-a) (-(-a)) rhs h1a h1b.
            //   h1a : -a ≤ rhs = max a (-a)  := le_max_right a (-a)
            //   h1b : -(-a) ≤ rhs            := transport (le_max_left a (-a) : a ≤ rhs)
            //                                   backwards along -(-a)=a with motive λy, y ≤ rhs
            let h1a = Expr::apps(c.le_max_right.clone(), [a.clone(), neg_a.clone()]);
            let a_le_rhs = Expr::apps(c.le_max_left.clone(), [a.clone(), neg_a.clone()]); // a ≤ rhs
            let motive_d1 = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (y_id, y) = ch.fresh_local(c.rat.clone());
                let body = c.le(y, rhs.clone());
                let lam = ch.mk_lam(y_id, BinderInfo::Default, c.rat.clone(), body);
                ch.finish_child(lam)
            };
            // subst (λy, y ≤ rhs) a (-(-a)) (a = -(-a)) (a_le_rhs) : -(-a) ≤ rhs
            let e_a_nna = c.symm(neg_neg_a.clone(), a.clone(), e_nna.clone()); // a = -(-a)
            let h1b = c.subst(motive_d1, a.clone(), neg_neg_a.clone(), e_a_nna, a_le_rhs);
            let dir1 = Expr::apps(
                c.max_le.clone(),
                [neg_a.clone(), neg_neg_a.clone(), rhs.clone(), h1a, h1b],
            );

            // Direction 2: rhs ≤ lhs  via max_le a (-a) lhs h2a h2b.
            //   h2a : a ≤ lhs = max (-a) (-(-a))  := transport (le_max_right (-a) (-(-a)) : -(-a) ≤ lhs)
            //                                        along -(-a)=a with motive λy, y ≤ lhs
            //   h2b : -a ≤ lhs                    := le_max_left (-a) (-(-a))
            let nna_le_lhs = Expr::apps(c.le_max_right.clone(), [neg_a.clone(), neg_neg_a.clone()]); // -(-a) ≤ lhs
            let motive_d2 = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (y_id, y) = ch.fresh_local(c.rat.clone());
                let body = c.le(y, lhs.clone());
                let lam = ch.mk_lam(y_id, BinderInfo::Default, c.rat.clone(), body);
                ch.finish_child(lam)
            };
            // subst (λy, y ≤ lhs) (-(-a)) a (-(-a) = a) (nna_le_lhs) : a ≤ lhs
            let h2a = c.subst(motive_d2, neg_neg_a.clone(), a.clone(), e_nna, nna_le_lhs);
            let h2b = Expr::apps(c.le_max_left.clone(), [neg_a.clone(), neg_neg_a.clone()]);
            let dir2 = Expr::apps(
                c.max_le.clone(),
                [a.clone(), neg_a.clone(), lhs.clone(), h2a, h2b],
            );

            // le_antisymm lhs rhs dir1 dir2 : lhs = rhs
            let body = Expr::apps(le_antisymm, [lhs, rhs, dir1, dir2]);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: nm,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// HARD batch: register the triangle inequalities `Rat.abs_add_le` and
    /// `Rat.abs_sub_le` as kernel-checked constructive `Declaration::Theorem`s.
    ///
    /// `Rat.abs_mul` is DEFERRED (left as an honest admitted `Declaration::Axiom`
    /// over the REAL `max a (-a)` carrier — non-refutable and true in the model):
    /// a faithful proof needs full four-way sign-case analysis with
    /// multiplicative monotonicity lemmas that are not yet available over the
    /// quotient. See the module-level report.
    pub(crate) fn register_rat_abs_proofs_hard(&mut self) -> Result<(), EnvError> {
        self.init_rat_abs_proof_deps()?;
        // The faithful carrier must already be installed (it is, via the easy
        // batch which `init_rat_abs` runs first); register it defensively so the
        // hard batch is self-contained if ever called standalone.
        let c = RatAbsConsts::new();
        self.register_rat_abs_carrier(&c)?;
        self.register_rat_abs_add_le(&c)?;
        self.register_rat_abs_sub_le(&c)?;
        Ok(())
    }

    /// `Rat.abs_add_le : ∀ a b, Rat.le (Rat.abs (Rat.add a b))
    ///                                  (Rat.add (Rat.abs a) (Rat.abs b))`.
    ///
    /// `abs x ≡ max x (-x)`. Goal `max (a+b) (-(a+b)) ≤ |a| + |b|` by
    /// `max_le (a+b) (-(a+b)) (|a|+|b|) h1 h2`:
    /// * `h1 : a+b ≤ |a|+|b|`  from `add_le_add` on `a ≤ |a|` (le_max_left) and
    ///   `b ≤ |b|` (le_max_left).
    /// * `h2 : -(a+b) ≤ |a|+|b|`  from `add_le_add` on `-a ≤ |a|` (le_max_right)
    ///   and `-b ≤ |b|` (le_max_right), giving `-a + -b ≤ |a|+|b|`, transported
    ///   backwards along `neg_add : -(a+b) = -a + -b`.
    fn register_rat_abs_add_le(&mut self, c: &RatAbsConsts) -> Result<(), EnvError> {
        let nm = Name::from_string("Rat.abs_add_le");
        if self.is_already_theorem(&nm) {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let lhs = c.abs(c.add(a.clone(), bv.clone()));
            let rhs = c.add(c.abs(a.clone()), c.abs(bv.clone()));
            let body = c.le(lhs, rhs);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let abs_a = c.abs(a.clone());
            let abs_b = c.abs(bv.clone());
            let rhs = c.add(abs_a.clone(), abs_b.clone()); // |a| + |b|
            let sum = c.add(a.clone(), bv.clone());
            let neg_sum = c.neg(sum.clone());
            let neg_a = c.neg(a.clone());
            let neg_b = c.neg(bv.clone());

            // h1 : a + b ≤ |a| + |b|
            let a_le_absa = c.le_max_left(a.clone(), neg_a.clone()); // a ≤ |a|
            let b_le_absb = c.le_max_left(bv.clone(), neg_b.clone()); // b ≤ |b|
            let h1 = c.add_le_add(
                a.clone(),
                abs_a.clone(),
                bv.clone(),
                abs_b.clone(),
                a_le_absa,
                b_le_absb,
            );

            // h2 : -(a+b) ≤ |a| + |b|
            // First: -a + -b ≤ |a| + |b| via add_le_add on le_max_right.
            let nega_le_absa = c.le_max_right(a.clone(), neg_a.clone()); // -a ≤ |a|
            let negb_le_absb = c.le_max_right(bv.clone(), neg_b.clone()); // -b ≤ |b|
            let neg_sum_le = c.add_le_add(
                neg_a.clone(),
                abs_a.clone(),
                neg_b.clone(),
                abs_b.clone(),
                nega_le_absa,
                negb_le_absb,
            ); // -a + -b ≤ |a|+|b|
               // From `neg_sum_le : (-a+-b) ≤ rhs` derive `-(a+b) ≤ rhs` by
               // rewriting `(-a+-b) → -(a+b)` along `e_sym : (-a+-b) = -(a+b)`
               // (the symm of `neg_add : -(a+b) = -a+-b`), motive `λ y, y ≤ rhs`.
            let e_neg_add = c.neg_add_eq(&b, &a, &bv); // -(a+b) = -a + -b
            let neg_sum_neg = c.add(neg_a.clone(), neg_b.clone());
            let e_sym = c.symm(neg_sum.clone(), neg_sum_neg.clone(), e_neg_add); // (-a+-b) = -(a+b)
            let motive_h2 = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (y_id, y) = ch.fresh_local(c.rat.clone());
                let body = c.le(y, rhs.clone());
                let lam = ch.mk_lam(y_id, BinderInfo::Default, c.rat.clone(), body);
                ch.finish_child(lam)
            };
            let h2 = c.subst(motive_h2, neg_sum_neg, neg_sum.clone(), e_sym, neg_sum_le);

            let body = c.max_le(sum, neg_sum, rhs, h1, h2);
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: nm,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.abs_sub_le : ∀ a b, Rat.le (Rat.abs (Rat.sub a b))
    ///                                  (Rat.add (Rat.abs a) (Rat.abs b))`.
    ///
    /// `Rat.sub a b ≡ Rat.add a (Rat.neg b)` (reducible), so the LHS is def-eq
    /// to `Rat.abs (a + (-b))`. By `abs_add_le a (-b)` we get
    /// `|a + (-b)| ≤ |a| + |(-b)|`, and `abs_neg b : |(-b)| = |b|` rewrites the
    /// RHS `|a| + |(-b)| → |a| + |b|` (congrArg + subst).
    fn register_rat_abs_sub_le(&mut self, c: &RatAbsConsts) -> Result<(), EnvError> {
        let nm = Name::from_string("Rat.abs_sub_le");
        if self.is_already_theorem(&nm) {
            return Ok(());
        }
        let rat_sub = Expr::const_(Name::from_string("Rat.sub"), vec![]);
        let abs_add_le = Expr::const_(Name::from_string("Rat.abs_add_le"), vec![]);
        let abs_neg = Expr::const_(Name::from_string("Rat.abs_neg"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let lhs = c.abs(Expr::apps(rat_sub.clone(), [a.clone(), bv.clone()]));
            let rhs = c.add(c.abs(a.clone()), c.abs(bv.clone()));
            let body = c.le(lhs, rhs);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let neg_b = c.neg(bv.clone());
            let abs_a = c.abs(a.clone());
            let abs_neg_b = c.abs(neg_b.clone()); // |(-b)|
            let abs_b = c.abs(bv.clone()); // |b|

            // base : |a + (-b)| ≤ |a| + |(-b)|   via abs_add_le a (-b)
            let base = Expr::apps(abs_add_le, [a.clone(), neg_b.clone()]);
            // e_absneg : |(-b)| = |b|   via abs_neg b
            let e_absneg = Expr::app(abs_neg, bv.clone());
            // congr : |a| + |(-b)| = |a| + |b|   via congrArg (λ x, |a| + x) e_absneg
            let f = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = ch.fresh_local(c.rat.clone());
                let body = c.add(abs_a.clone(), x);
                let lam = ch.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
                ch.finish_child(lam)
            };
            let e_rhs = c.congr_arg(abs_neg_b.clone(), abs_b.clone(), f, e_absneg);
            // subst with motive (λ y, |a + (-b)| ≤ y), rewriting RHS
            // |a|+|(-b)| → |a|+|b|. The LHS `|a + (-b)|` is def-eq to the goal's
            // `|Rat.sub a b|` (Rat.sub reducible), so this yields the stated type.
            let abs_sum = c.abs(c.add(a.clone(), neg_b.clone()));
            let rhs_old = c.add(abs_a.clone(), abs_neg_b);
            let rhs_new = c.add(abs_a.clone(), abs_b);
            let motive = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (y_id, y) = ch.fresh_local(c.rat.clone());
                let body = c.le(abs_sum.clone(), y);
                let lam = ch.mk_lam(y_id, BinderInfo::Default, c.rat.clone(), body);
                ch.finish_child(lam)
            };
            let body = c.subst(motive, rhs_old, rhs_new, e_rhs, base);
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: nm,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Helper: is `nm` already a kernel-checked `Declaration::Theorem`?
    fn is_already_theorem(&self, nm: &Name) -> bool {
        self.get_const(nm).map(|i| i.kind) == Some(crate::env::types::ConstantKind::Theorem)
    }
}
