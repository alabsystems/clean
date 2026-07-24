// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.lt_trichotomy : ∀ a b : Int,
//!    Or (Int.lt a b) (Or (Eq a b) (Int.lt b a))`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `order_int.rs::init_int_ord_lemmas` with a kernel-checked
//! `Declaration::Theorem` whose transitive axiom closure is empty.
//!
//! # Definitions in play
//!
//! ```text
//! Int.le a b := Int.NonNeg (Int.sub b a)                 -- reducible Definition
//! Int.lt a b := Int.le (Int.add a 1) b
//!             ≡ Int.NonNeg (Int.sub b (Int.add a 1))      -- (1 := ofNat (succ 0))
//! Int.sub x y := Int.add x (Int.neg y)                   -- reducible Definition
//! Int.zero := Int.ofNat Nat.zero                         -- reducible Definition
//! inductive Int.NonNeg : Int → Prop where
//!   | mk (n : Nat) : Int.NonNeg (Int.ofNat n)
//! ```
//!
//! Kernel reductions exploited (all on closed numerals):
//! `Int.neg (Int.negSucc n) ≡ Int.ofNat (Nat.succ n)`,
//! `Int.sub (Int.ofNat (Nat.succ m)) 1 ≡ Int.ofNat m`,
//! `Int.sub (Int.ofNat (Nat.succ n)) 1 ≡ Int.ofNat n`.
//!
//! # Proof strategy
//!
//! A single `@Int.rec.{0}` case-analysis on the difference `d := Int.sub b a`,
//! with an equation-carrying motive
//!
//! ```text
//! M := λ (i : Int) => Eq Int (Int.sub b a) i → Goal
//! Goal := Or (Int.lt a b) (Or (Eq a b) (Int.lt b a))
//! ```
//!
//! applied to `i := Int.sub b a` and the reflexivity witness
//! `@Eq.refl.{1} Int (Int.sub b a)`. The recursor's two minors receive the
//! exact relationship `heq : Eq (Int.sub b a) <pattern>`:
//!
//! - `ofNat n` minor → inner `@Nat.rec.{0}` on `n`:
//!   - `n = 0`: `heq : Eq (b - a) (ofNat 0) ≡ Eq (b - a) Int.zero`, so
//!     `eq_of_sub_eq_zero` yields `Eq a b` (the middle disjunct).
//!   - `n = succ m`: transport `@Int.NonNeg.mk m : NonNeg (ofNat m)` along
//!     `b - (a+1) = (b-a) - 1 = (ofNat (succ m)) - 1 = ofNat m` (B1 with
//!     `heq` and kernel reduction) to `NonNeg (Int.sub b (a+1))` ≡
//!     `Int.lt a b` (the left disjunct).
//! - `negSucc n` minor: transport `@Int.NonNeg.mk n : NonNeg (ofNat n)` along
//!   `a - (b+1) = (neg (b-a)) - 1 = (neg (negSucc n)) - 1 = ofNat n` (B2 with
//!   `heq` and kernel reduction) to `NonNeg (Int.sub a (b+1))` ≡
//!   `Int.lt b a` (the right disjunct).
//!
//! The transports use `@Eq.subst.{1} Int (λ x => Int.NonNeg x)`. All equality
//! witnesses are built from already-constructive Int lemmas (`Int.add_assoc`,
//! `Int.add_comm`, `Int.add_zero`, `Int.zero_add`, `Int.neg_add`,
//! `Int.neg_neg`, `Int.neg_add_self`) via `Eq.trans` / `Eq.symm` /
//! `congrArg`. No domain-specific axiom is touched.
//!
//! # Axiom closure
//!
//! The proof term mentions only `Int`, `Int.le`, `Int.lt`, `Int.sub`,
//! `Int.add`, `Int.neg`, `Int.ofNat`, `Int.negSucc`, `Int.NonNeg`,
//! `Int.NonNeg.mk`, `Int.rec`, `Nat`, `Nat.rec`, `Nat.zero`, `Nat.succ`,
//! `Or`, `Or.inl`, `Or.inr`, `Eq`, `Eq.refl`, `Eq.symm`, `Eq.trans`,
//! `Eq.subst`, `congrArg`, and the constructive Int arithmetic theorems
//! listed above — none of which is a `Declaration::Axiom`. Therefore
//! `env.axiom_deps("Int.lt_trichotomy")` is empty and
//! `env.proof_quality("Int.lt_trichotomy") == ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntLtTrichotomyConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    int_lt: Expr,
    int_sub: Expr,
    int_add: Expr,
    int_neg: Expr,
    int_of_nat: Expr,
    int_neg_succ: Expr,
    int_zero: Expr,
    nonneg: Expr,
    nonneg_mk: Expr,
    int_rec: Expr,
    nat_rec: Expr,
    or_const: Expr,
    or_inl: Expr,
    or_inr: Expr,
    eq_const: Expr,
    eq_refl: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    eq_subst: Expr,
    congr_arg: Expr,
    add_assoc: Expr,
    add_comm: Expr,
    add_zero: Expr,
    zero_add: Expr,
    neg_add: Expr,
    neg_neg: Expr,
    neg_add_self: Expr,
}

impl IntLtTrichotomyConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            int_lt: Expr::const_(Name::from_string("Int.lt"), vec![]),
            int_sub: Expr::const_(Name::from_string("Int.sub"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_neg: Expr::const_(Name::from_string("Int.neg"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            int_zero: Expr::const_(Name::from_string("Int.zero"), vec![]),
            nonneg: Expr::const_(Name::from_string("Int.NonNeg"), vec![]),
            nonneg_mk: Expr::const_(Name::from_string("Int.NonNeg.mk"), vec![]),
            // Int.rec into a `Prop`-valued motive (`λ i => Eq d i → Goal`,
            // which lands in `Sort 0`).
            int_rec: Expr::const_(Name::from_string("Int.rec"), vec![Level::zero()]),
            // Nat.rec producing a `Prop : Sort 0` value (motive is `Nat → Prop`).
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            or_const: Expr::const_(Name::from_string("Or"), vec![]),
            or_inl: Expr::const_(Name::from_string("Or.inl"), vec![]),
            or_inr: Expr::const_(Name::from_string("Or.inr"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![type1.clone()]),
            // congrArg.{1,1} : {α β : Type} → {a₁ a₂ : α} → (f : α → β) →
            //   Eq a₁ a₂ → Eq (f a₁) (f a₂)
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            add_assoc: Expr::const_(Name::from_string("Int.add_assoc"), vec![]),
            add_comm: Expr::const_(Name::from_string("Int.add_comm"), vec![]),
            add_zero: Expr::const_(Name::from_string("Int.add_zero"), vec![]),
            zero_add: Expr::const_(Name::from_string("Int.zero_add"), vec![]),
            neg_add: Expr::const_(Name::from_string("Int.neg_add"), vec![]),
            neg_neg: Expr::const_(Name::from_string("Int.neg_neg"), vec![]),
            neg_add_self: Expr::const_(Name::from_string("Int.neg_add_self"), vec![]),
        }
    }

    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), x), y)
    }

    fn sub(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_sub.clone(), x), y)
    }

    fn neg(&self, x: Expr) -> Expr {
        Expr::app(self.int_neg.clone(), x)
    }

    fn lt(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_lt.clone(), x), y)
    }

    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }

    fn neg_succ(&self, n: Expr) -> Expr {
        Expr::app(self.int_neg_succ.clone(), n)
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }

    fn nonneg_of(&self, x: Expr) -> Expr {
        Expr::app(self.nonneg.clone(), x)
    }

    /// `1 := Int.ofNat (Nat.succ Nat.zero)` — the canonical `Int.lt` unit.
    fn one(&self) -> Expr {
        self.of_nat(self.succ(self.nat_zero.clone()))
    }

    /// `@Eq.{1} Int lhs rhs`.
    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }

    /// `@Eq.refl.{1} Int t : Eq Int t t`.
    fn refl_int(&self, t: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.int_type.clone(), t])
    }

    /// `@Eq.symm.{1} Int lhs rhs h : Eq Int rhs lhs` (from `h : Eq Int lhs rhs`).
    fn symm_int(&self, lhs: Expr, rhs: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.int_type.clone(), lhs, rhs, h])
    }

    /// `@Eq.trans.{1} Int x y z h1 h2 : Eq Int x z`.
    fn trans_int(&self, x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.int_type.clone(), x, y, z, h1, h2],
        )
    }

    /// `@congrArg.{1,1} Int Int a1 a2 f h : Eq Int (f a1) (f a2)`.
    fn congr_arg_int(&self, a1: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.int_type.clone(), self.int_type.clone(), a1, a2, f, h],
        )
    }

    /// `@Eq.subst.{1} Int (λ x => NonNeg x) lhs rhs e w : NonNeg rhs`
    /// (from `e : Eq Int lhs rhs`, `w : NonNeg lhs`).
    fn subst_nonneg(
        &self,
        parent: &EnvDeclBuilder,
        lhs: Expr,
        rhs: Expr,
        e: Expr,
        w: Expr,
    ) -> Expr {
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = mb.fresh_local(self.int_type.clone());
            let body = self.nonneg_of(x);
            let lam = mb.mk_lam(x_id, BinderInfo::Default, self.int_type.clone(), body);
            mb.finish_child(lam)
        };
        Expr::apps(
            self.eq_subst.clone(),
            [self.int_type.clone(), motive, lhs, rhs, e, w],
        )
    }

    /// `@Or.inl la lb h`.
    fn or_inl(&self, la: Expr, lb: Expr, h: Expr) -> Expr {
        Expr::apps(self.or_inl.clone(), [la, lb, h])
    }

    /// `@Or.inr la lb h`.
    fn or_inr(&self, la: Expr, lb: Expr, h: Expr) -> Expr {
        Expr::apps(self.or_inr.clone(), [la, lb, h])
    }

    fn or_of(&self, la: Expr, lb: Expr) -> Expr {
        Expr::apps(self.or_const.clone(), [la, lb])
    }

    /// Build a closed `λ (x : Int) => Int.add lhs_or_rhs x`-style adder. The
    /// `which` selects whether `arg` sits on the left (`arg + x`) or right
    /// (`x + arg`) of the application.
    fn add_fn_left(&self, parent: &EnvDeclBuilder, arg: Expr) -> Expr {
        let mut fb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = fb.fresh_local(self.int_type.clone());
        let body = self.add(arg.clone(), x);
        let lam = fb.mk_lam(x_id, BinderInfo::Default, self.int_type.clone(), body);
        fb.finish_child(lam)
    }

    fn add_fn_right(&self, parent: &EnvDeclBuilder, arg: Expr) -> Expr {
        let mut fb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = fb.fresh_local(self.int_type.clone());
        let body = self.add(x, arg.clone());
        let lam = fb.mk_lam(x_id, BinderInfo::Default, self.int_type.clone(), body);
        fb.finish_child(lam)
    }
}

/// `Or (Int.lt a b) (Or (Eq a b) (Int.lt b a))`.
fn trichotomy_goal(c: &IntLtTrichotomyConsts, a: &Expr, bb: &Expr) -> Expr {
    let lt_ab = c.lt(a.clone(), bb.clone());
    let eq_ab = c.eq_int(a.clone(), bb.clone());
    let lt_ba = c.lt(bb.clone(), a.clone());
    let inner = c.or_of(eq_ab, lt_ba);
    c.or_of(lt_ab, inner)
}

/// Build `∀ a b : Int, Or (Int.lt a b) (Or (Eq a b) (Int.lt b a))`.
fn build_type(c: &IntLtTrichotomyConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bb_id, bb) = b.fresh_local(c.int_type.clone());
    let goal = trichotomy_goal(c, &a, &bb);
    let r = b.mk_pi(bb_id, BinderInfo::Default, c.int_type.clone(), goal);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// `Eq a b` from `heq0 : Eq (Int.sub b a) Int.zero`.
///
/// Adds `a` to both sides of `b + (-a) = 0`, collapsing
/// `(b + (-a)) + a = b + ((-a) + a) = b + 0 = b` and `0 + a = a`, then
/// reverses to `Eq a b`.
fn eq_of_sub_eq_zero(
    c: &IntLtTrichotomyConsts,
    parent: &EnvDeclBuilder,
    a: &Expr,
    bb: &Expr,
    heq0: Expr,
) -> Expr {
    let neg_a = c.neg(a.clone());
    let sub_ba = c.add(bb.clone(), neg_a.clone()); // b + (-a) ≡ b - a
    let zero = c.int_zero.clone();

    // s1 : Eq ((b + (-a)) + a) (0 + a)  := congrArg (· + a) heq0
    let lhs1 = c.add(sub_ba.clone(), a.clone());
    let rhs1 = c.add(zero.clone(), a.clone());
    let add_a_fn = c.add_fn_right(parent, a.clone());
    let s1 = c.congr_arg_int(sub_ba.clone(), zero.clone(), add_a_fn, heq0);

    // s2 : Eq ((b + (-a)) + a) (b + ((-a) + a))  := Int.add_assoc b (-a) a
    let grouped = c.add(bb.clone(), c.add(neg_a.clone(), a.clone()));
    let s2 = Expr::apps(c.add_assoc.clone(), [bb.clone(), neg_a.clone(), a.clone()]);

    // s3 : Eq ((-a) + a) 0  := Int.neg_add_self a
    let neg_a_plus_a = c.add(neg_a.clone(), a.clone());
    let s3 = Expr::app(c.neg_add_self.clone(), a.clone());

    // s4 : Eq (b + ((-a) + a)) (b + 0)  := congrArg (b + ·) s3
    let b_plus_zero = c.add(bb.clone(), zero.clone());
    let add_b_fn = c.add_fn_left(parent, bb.clone());
    let s4 = c.congr_arg_int(neg_a_plus_a.clone(), zero.clone(), add_b_fn, s3);

    // s5 : Eq (b + 0) b  := Int.add_zero b
    let s5 = Expr::app(c.add_zero.clone(), bb.clone());

    // s6 : Eq (0 + a) a  := Int.zero_add a
    let s6 = Expr::app(c.zero_add.clone(), a.clone());

    // `Eq lhs1 b` := trans s2 (trans s4 s5)
    let t_s4_s5 = c.trans_int(grouped.clone(), b_plus_zero.clone(), bb.clone(), s4, s5);
    let lhs1_eq_b = c.trans_int(lhs1.clone(), grouped, bb.clone(), s2, t_s4_s5);

    // `Eq lhs1 a` := trans s1 s6
    let lhs1_eq_a = c.trans_int(lhs1.clone(), rhs1, a.clone(), s1, s6);

    // `Eq b a` := trans (symm lhs1_eq_b) lhs1_eq_a
    let b_eq_lhs1 = c.symm_int(lhs1.clone(), bb.clone(), lhs1_eq_b);
    let b_eq_a = c.trans_int(bb.clone(), lhs1, a.clone(), b_eq_lhs1, lhs1_eq_a);

    // `Eq a b` := symm
    c.symm_int(bb.clone(), a.clone(), b_eq_a)
}

/// B1: `Eq (Int.sub b (a+1)) (Int.sub (Int.sub b a) 1)`.
///
/// `b - (a+1) = b + (-(a+1)) = b + ((-a) + (-1))` (neg_add)
/// `= (b + (-a)) + (-1)` (symm add_assoc) `= (b - a) - 1`.
fn bridge_b1(c: &IntLtTrichotomyConsts, parent: &EnvDeclBuilder, a: &Expr, bb: &Expr) -> Expr {
    let one = c.one();
    let neg_a = c.neg(a.clone());
    let neg_one = c.neg(one.clone());
    let a_plus_one = c.add(a.clone(), one.clone());

    // lhs := b - (a+1) ≡ b + (-(a+1))
    let lhs = c.sub(bb.clone(), a_plus_one.clone());
    let neg_a_plus_one = c.neg(a_plus_one.clone()); // -(a+1)

    // s_neg : Eq (-(a+1)) ((-a) + (-1))  := Int.neg_add a 1
    let neg_a_plus_neg_one = c.add(neg_a.clone(), neg_one.clone());
    let s_neg = Expr::apps(c.neg_add.clone(), [a.clone(), one.clone()]);

    // s1 : Eq (b + (-(a+1))) (b + ((-a)+(-1)))  := congrArg (b + ·) s_neg
    let mid = c.add(bb.clone(), neg_a_plus_neg_one.clone());
    let add_b_fn = c.add_fn_left(parent, bb.clone());
    let s1 = c.congr_arg_int(neg_a_plus_one, neg_a_plus_neg_one.clone(), add_b_fn, s_neg);

    // s2 : Eq ((b+(-a)) + (-1)) (b + ((-a)+(-1)))  := Int.add_assoc b (-a) (-1)
    let assoc_lhs = c.add(c.add(bb.clone(), neg_a.clone()), neg_one.clone());
    let s2 = Expr::apps(
        c.add_assoc.clone(),
        [bb.clone(), neg_a.clone(), neg_one.clone()],
    );
    // symm s2 : Eq (b + ((-a)+(-1))) ((b+(-a)) + (-1))
    let s2_sym = c.symm_int(assoc_lhs.clone(), mid.clone(), s2);

    // result : Eq lhs ((b-a)-1) := trans s1 s2_sym   (rhs ≡ (b+(-a))+(-1) ≡ assoc_lhs)
    c.trans_int(lhs, mid, assoc_lhs, s1, s2_sym)
}

/// B2: `Eq (Int.sub a (b+1)) (Int.sub (Int.neg (Int.sub b a)) 1)`.
///
/// `a - (b+1) = a + ((-b) + (-1)) = (a + (-b)) + (-1) = ((-b) + a) + (-1)`
/// and `-(b - a) - 1 = (-b + a) + (-1)`.
fn bridge_b2(c: &IntLtTrichotomyConsts, parent: &EnvDeclBuilder, a: &Expr, bb: &Expr) -> Expr {
    let one = c.one();
    let neg_a = c.neg(a.clone());
    let neg_b = c.neg(bb.clone());
    let neg_one = c.neg(one.clone());
    let b_plus_one = c.add(bb.clone(), one.clone());

    // lhs := a - (b+1) ≡ a + (-(b+1))
    let lhs = c.sub(a.clone(), b_plus_one.clone());
    let neg_b_plus_one = c.neg(b_plus_one.clone());

    // p1 : Eq (-(b+1)) ((-b)+(-1))  := Int.neg_add b 1
    let neg_b_plus_neg_one = c.add(neg_b.clone(), neg_one.clone());
    let p1 = Expr::apps(c.neg_add.clone(), [bb.clone(), one.clone()]);

    // s1 : Eq (a + (-(b+1))) (a + ((-b)+(-1)))  := congrArg (a + ·) p1
    let mid1 = c.add(a.clone(), neg_b_plus_neg_one.clone());
    let add_a_fn = c.add_fn_left(parent, a.clone());
    let s1 = c.congr_arg_int(neg_b_plus_one, neg_b_plus_neg_one.clone(), add_a_fn, p1);

    // s2 : Eq ((a+(-b)) + (-1)) (a + ((-b)+(-1)))  := Int.add_assoc a (-b) (-1)
    let assoc1_lhs = c.add(c.add(a.clone(), neg_b.clone()), neg_one.clone());
    let s2 = Expr::apps(
        c.add_assoc.clone(),
        [a.clone(), neg_b.clone(), neg_one.clone()],
    );
    let s2_sym = c.symm_int(assoc1_lhs.clone(), mid1.clone(), s2);
    // lhs_eq : Eq lhs ((a+(-b)) + (-1))  := trans s1 s2_sym
    let lhs_eq = c.trans_int(lhs.clone(), mid1, assoc1_lhs.clone(), s1, s2_sym);

    // RHS side: rhs := (-(b - a)) - 1 ≡ (Int.neg (b + (-a))) + (-1).
    let sub_ba = c.add(bb.clone(), neg_a.clone()); // b + (-a) ≡ b - a
    let neg_sub_ba = c.neg(sub_ba.clone());
    let rhs = c.add(neg_sub_ba.clone(), neg_one.clone());

    // q1 : Eq (-(b + (-a))) ((-b) + (-(-a)))  := Int.neg_add b (-a)
    let neg_neg_a = c.neg(neg_a.clone());
    let nb_plus_nna = c.add(neg_b.clone(), neg_neg_a.clone());
    let q1 = Expr::apps(c.neg_add.clone(), [bb.clone(), neg_a.clone()]);

    // q2 : Eq (-(-a)) a  := Int.neg_neg a
    let q2 = Expr::app(c.neg_neg.clone(), a.clone());
    // q3 : Eq ((-b) + (-(-a))) ((-b) + a)  := congrArg ((-b) + ·) q2
    let nb_plus_a = c.add(neg_b.clone(), a.clone());
    let add_nb_fn = c.add_fn_left(parent, neg_b.clone());
    let q3 = c.congr_arg_int(neg_neg_a.clone(), a.clone(), add_nb_fn, q2);
    // neg_sub_eq : Eq (-(b+(-a))) ((-b) + a)  := trans q1 q3
    let neg_sub_eq = c.trans_int(neg_sub_ba.clone(), nb_plus_nna, nb_plus_a.clone(), q1, q3);

    // r1 : Eq ((-(b+(-a))) + (-1)) (((-b)+a) + (-1))  := congrArg (· + (-1)) neg_sub_eq
    let nb_plus_a_plus_neg_one = c.add(nb_plus_a.clone(), neg_one.clone());
    let add_neg_one_fn = c.add_fn_right(parent, neg_one.clone());
    let r1 = c.congr_arg_int(
        neg_sub_ba.clone(),
        nb_plus_a.clone(),
        add_neg_one_fn,
        neg_sub_eq,
    );
    // r1 : Eq rhs nb_plus_a_plus_neg_one.

    // c1 : Eq (a + (-b)) ((-b) + a)  := Int.add_comm a (-b)
    let a_plus_nb = c.add(a.clone(), neg_b.clone());
    let c1 = Expr::apps(c.add_comm.clone(), [a.clone(), neg_b.clone()]);
    // d1 : Eq assoc1_lhs nb_plus_a_plus_neg_one  := congrArg (· + (-1)) c1
    let add_neg_one_fn2 = c.add_fn_right(parent, neg_one.clone());
    let d1 = c.congr_arg_int(a_plus_nb, nb_plus_a, add_neg_one_fn2, c1);

    // Assemble: lhs --lhs_eq--> assoc1_lhs --d1--> nb_plus_a_plus_neg_one
    //   then `Eq lhs rhs` := trans (trans lhs_eq d1) (symm r1).
    let lhs_to_nbapno = c.trans_int(
        lhs.clone(),
        assoc1_lhs.clone(),
        nb_plus_a_plus_neg_one.clone(),
        lhs_eq,
        d1,
    );
    let nbapno_to_rhs = c.symm_int(rhs.clone(), nb_plus_a_plus_neg_one.clone(), r1);
    c.trans_int(
        lhs,
        nb_plus_a_plus_neg_one,
        rhs,
        lhs_to_nbapno,
        nbapno_to_rhs,
    )
}

/// Build the closed proof value.
fn build_value(c: &IntLtTrichotomyConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bb_id, bb) = b.fresh_local(c.int_type.clone());

    let goal = trichotomy_goal(c, &a, &bb);
    let lt_ab = c.lt(a.clone(), bb.clone());
    let eq_ab = c.eq_int(a.clone(), bb.clone());
    let lt_ba = c.lt(bb.clone(), a.clone());
    let inner_or = c.or_of(eq_ab.clone(), lt_ba.clone()); // Or (Eq a b) (lt b a)

    let d = c.sub(bb.clone(), a.clone()); // d := b - a

    // ---- outer Int.rec motive: λ (i : Int) => Eq Int d i → Goal ----
    let outer_motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = mb.fresh_local(c.int_type.clone());
        let eq_di = c.eq_int(d.clone(), i.clone());
        let (h_id, _h) = mb.fresh_local(eq_di.clone());
        let body = mb.mk_pi(h_id, BinderInfo::Default, eq_di, goal.clone());
        let lam = mb.mk_lam(i_id, BinderInfo::Default, c.int_type.clone(), body);
        mb.finish_child(lam)
    };

    // ---- ofNat minor: λ (n : Nat) => @Nat.rec.{0} N zeroCase succCase n ----
    let of_nat_minor = {
        let mut ob = EnvDeclBuilder::child_of(&b);
        let (n_id, n) = ob.fresh_local(c.nat_type.clone());

        // inner Nat.rec motive: λ (k : Nat) => Eq Int d (ofNat k) → Goal
        let inner_motive = {
            let mut mb = EnvDeclBuilder::child_of(&ob);
            let (k_id, k) = mb.fresh_local(c.nat_type.clone());
            let eq_dk = c.eq_int(d.clone(), c.of_nat(k.clone()));
            let (h_id, _h) = mb.fresh_local(eq_dk.clone());
            let body = mb.mk_pi(h_id, BinderInfo::Default, eq_dk, goal.clone());
            let lam = mb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), body);
            mb.finish_child(lam)
        };

        // zero case: λ (heq : Eq d (ofNat 0)) =>
        //   Or.inr lt_ab inner_or (Or.inl eq_ab lt_ba (eq_of_sub_eq_zero heq))
        let zero_case = {
            let mut zb = EnvDeclBuilder::child_of(&ob);
            let eq_d0 = c.eq_int(d.clone(), c.of_nat(c.nat_zero.clone()));
            let (heq_id, heq) = zb.fresh_local(eq_d0.clone());
            // heq : Eq (b-a) (ofNat 0) ≡ Eq (b-a) Int.zero (defeq).
            let eq_proof = eq_of_sub_eq_zero(c, &zb, &a, &bb, heq);
            let inl = c.or_inl(eq_ab.clone(), lt_ba.clone(), eq_proof);
            let body = c.or_inr(lt_ab.clone(), inner_or.clone(), inl);
            let lam = zb.mk_lam(heq_id, BinderInfo::Default, eq_d0, body);
            zb.finish_child(lam)
        };

        // succ case: λ (m : Nat) (_ih) (heq : Eq d (ofNat (succ m))) =>
        //   Or.inl lt_ab inner_or <NonNeg (b-(a+1)) witness>
        let succ_case = {
            let mut sb = EnvDeclBuilder::child_of(&ob);
            let (m_id, m) = sb.fresh_local(c.nat_type.clone());
            // ih type: Eq d (ofNat m) → Goal
            let ih_inner = {
                let eq_dm = c.eq_int(d.clone(), c.of_nat(m.clone()));
                let mut ib = EnvDeclBuilder::child_of(&sb);
                let (h_id, _h) = ib.fresh_local(eq_dm.clone());
                let body = ib.mk_pi(h_id, BinderInfo::Default, eq_dm, goal.clone());
                ib.finish_child(body)
            };
            let (ih_id, _ih) = sb.fresh_local(ih_inner.clone());
            let succ_m = c.succ(m.clone());
            let eq_dsm = c.eq_int(d.clone(), c.of_nat(succ_m.clone()));
            let (heq_id, heq) = sb.fresh_local(eq_dsm.clone());

            // target := Int.sub b (a+1)  (≡ Int.lt a b after delta).
            let one = c.one();
            let a_plus_one = c.add(a.clone(), one.clone());
            let target = c.sub(bb.clone(), a_plus_one.clone());

            // e1 : Eq target ((b-a) - 1)   := B1
            let sub_d_one = c.sub(d.clone(), one.clone());
            let e1 = bridge_b1(c, &sb, &a, &bb);

            // e2 : Eq ((b-a) - 1) ((ofNat (succ m)) - 1)  := congrArg (· - 1) heq
            let sub_one_fn = {
                let mut fb = EnvDeclBuilder::child_of(&sb);
                let (x_id, x) = fb.fresh_local(c.int_type.clone());
                let body = c.sub(x, one.clone());
                let lam = fb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
                fb.finish_child(lam)
            };
            let ofnat_sm_sub_one = c.sub(c.of_nat(succ_m.clone()), one.clone());
            let e2 = c.congr_arg_int(d.clone(), c.of_nat(succ_m.clone()), sub_one_fn, heq.clone());

            // e3 : Eq ((ofNat (succ m)) - 1) (ofNat m)  := Eq.refl (defeq reduction)
            let ofnat_m = c.of_nat(m.clone());
            let e3 = c.refl_int(ofnat_sm_sub_one.clone());

            // e_fwd : Eq target (ofNat m) := trans (trans e1 e2) e3
            let e12 = c.trans_int(
                target.clone(),
                sub_d_one.clone(),
                ofnat_sm_sub_one.clone(),
                e1,
                e2,
            );
            let e_fwd = c.trans_int(target.clone(), ofnat_sm_sub_one, ofnat_m.clone(), e12, e3);
            // e : Eq (ofNat m) target := symm e_fwd
            let e = c.symm_int(target.clone(), ofnat_m.clone(), e_fwd);

            // witness : NonNeg (ofNat m) := @Int.NonNeg.mk m
            let w = Expr::app(c.nonneg_mk.clone(), m.clone());
            let nn_target = c.subst_nonneg(&sb, ofnat_m, target, e, w);
            // Or.inl lt_ab inner_or nn_target : Goal (nn_target : Int.lt a b by defeq)
            let body = c.or_inl(lt_ab.clone(), inner_or.clone(), nn_target);

            let lam = sb.mk_lam(heq_id, BinderInfo::Default, eq_dsm, body);
            let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_inner, lam);
            let lam = sb.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), lam);
            sb.finish_child(lam)
        };

        // @Nat.rec.{0} inner_motive zero_case succ_case n : (Eq d (ofNat n) → Goal)
        let nat_rec_app = Expr::apps(
            c.nat_rec.clone(),
            [inner_motive, zero_case, succ_case, n.clone()],
        );
        let lam = ob.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), nat_rec_app);
        ob.finish_child(lam)
    };

    // ---- negSucc minor: λ (n : Nat) (heq : Eq d (negSucc n)) => ... ----
    let neg_succ_minor = {
        let mut nb = EnvDeclBuilder::child_of(&b);
        let (n_id, n) = nb.fresh_local(c.nat_type.clone());
        let neg_succ_n = c.neg_succ(n.clone());
        let eq_dns = c.eq_int(d.clone(), neg_succ_n.clone());
        let (heq_id, heq) = nb.fresh_local(eq_dns.clone());

        // target2 := Int.sub a (b+1)  (≡ Int.lt b a after delta).
        let one = c.one();
        let b_plus_one = c.add(bb.clone(), one.clone());
        let target2 = c.sub(a.clone(), b_plus_one.clone());

        // e1 : Eq target2 ((neg (b-a)) - 1)  := B2
        let neg_d = c.neg(d.clone());
        let neg_d_sub_one = c.sub(neg_d.clone(), one.clone());
        let e1 = bridge_b2(c, &nb, &a, &bb);

        // e2 : Eq ((neg (b-a)) - 1) ((neg (negSucc n)) - 1)
        //    := congrArg (λ x => (neg x) - 1) heq
        let neg_sub_one_fn = {
            let mut fb = EnvDeclBuilder::child_of(&nb);
            let (x_id, x) = fb.fresh_local(c.int_type.clone());
            let body = c.sub(c.neg(x), one.clone());
            let lam = fb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
            fb.finish_child(lam)
        };
        let neg_ns_sub_one = c.sub(c.neg(neg_succ_n.clone()), one.clone());
        let e2 = c.congr_arg_int(d.clone(), neg_succ_n.clone(), neg_sub_one_fn, heq.clone());

        // e3 : Eq ((neg (negSucc n)) - 1) (ofNat n)  := Eq.refl (defeq reduction)
        //   neg (negSucc n) ≡ ofNat (succ n); (ofNat (succ n)) - 1 ≡ ofNat n.
        let ofnat_n = c.of_nat(n.clone());
        let e3 = c.refl_int(neg_ns_sub_one.clone());

        // e_fwd : Eq target2 (ofNat n) := trans (trans e1 e2) e3
        let e12 = c.trans_int(
            target2.clone(),
            neg_d_sub_one.clone(),
            neg_ns_sub_one.clone(),
            e1,
            e2,
        );
        let e_fwd = c.trans_int(target2.clone(), neg_ns_sub_one, ofnat_n.clone(), e12, e3);
        // e : Eq (ofNat n) target2 := symm e_fwd
        let e = c.symm_int(target2.clone(), ofnat_n.clone(), e_fwd);

        // witness : NonNeg (ofNat n) := @Int.NonNeg.mk n
        let w = Expr::app(c.nonneg_mk.clone(), n.clone());
        let nn_target2 = c.subst_nonneg(&nb, ofnat_n, target2, e, w);
        // Or.inr lt_ab inner_or (Or.inr eq_ab lt_ba nn_target2)
        let inr_inner = c.or_inr(eq_ab.clone(), lt_ba.clone(), nn_target2);
        let body = c.or_inr(lt_ab.clone(), inner_or.clone(), inr_inner);

        let lam = nb.mk_lam(heq_id, BinderInfo::Default, eq_dns, body);
        let lam = nb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), lam);
        nb.finish_child(lam)
    };

    // @Int.rec.{0} outer_motive of_nat_minor neg_succ_minor d : (Eq d d → Goal)
    let int_rec_app = Expr::apps(
        c.int_rec.clone(),
        [outer_motive, of_nat_minor, neg_succ_minor, d.clone()],
    );
    // apply to refl: (Eq d d → Goal) (Eq.refl d) : Goal
    let refl_d = c.refl_int(d.clone());
    let applied = Expr::app(int_rec_app, refl_d);

    let lam = b.mk_lam(bb_id, BinderInfo::Default, c.int_type.clone(), applied);
    let lam = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), lam);
    b.finish(lam)
}

impl Environment {
    /// Register `Int.lt_trichotomy` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_ord()` has registered `Int.lt`, `Int.le`,
    ///           `Int.NonNeg`, `Int.NonNeg.mk`, `Int.sub`, `Int.add`,
    ///           `Int.neg`, `Int.rec`, `Int.ofNat`, `Int.negSucc`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`, `Eq.symm`,
    ///           `Eq.trans`, `Eq.subst`, `congrArg`.
    /// REQUIRES: `self.init_classical()` has registered `Or`, `Or.inl`,
    ///           `Or.inr`.
    /// ENSURES: On success, `Int.lt_trichotomy` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.lt_trichotomy` is already registered with
    ///          any declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_int_lt_trichotomy_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.lt_trichotomy");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_ord()?;
        self.init_eq()?;
        self.init_classical()?; // Or, Or.inl, Or.inr

        // Constructive arithmetic dependencies (all empty-closure Theorems).
        self.register_int_add_assoc_proof()?;
        self.register_int_add_comm_proof()?;
        self.register_int_add_zero_proof()?;
        self.register_int_zero_add_proof()?;
        self.register_int_neg_add_proof()?;
        self.register_int_neg_neg_proof()?;
        self.register_int_neg_add_self_proof()?;

        let c = IntLtTrichotomyConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. A single `@Int.rec.{0}`
        // case-analysis on `d := Int.sub b a` (with an equation-carrying motive
        // `λ i => Eq (Int.sub b a) i → Goal`, applied to `Eq.refl (Int.sub b a)`)
        // splits into the `ofNat`/`negSucc` signs; the `ofNat` branch refines via
        // `@Nat.rec.{0}` into the `0` (→ `Eq a b` via `eq_of_sub_eq_zero`) and
        // `succ m` (→ `Int.lt a b`) cases, and the `negSucc n` branch yields
        // `Int.lt b a`. The two strict cases transport `@Int.NonNeg.mk · :
        // NonNeg (ofNat ·)` along constructive arithmetic equalities (B1/B2,
        // built from `Int.add_assoc`/`add_comm`/`add_zero`/`zero_add`/`neg_add`/
        // `neg_neg`/`neg_add_self` via `Eq.trans`/`Eq.symm`/`congrArg`) plus
        // kernel reductions, using `@Eq.subst.{1}`. No `sorry`, no
        // self-reference, no domain-axiom dependency. Replaces the prior
        // `Declaration::Axiom` in `order_int.rs::init_int_ord_lemmas`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::axiom_audit::ProofQuality;
    use crate::env::ConstantKind;

    #[test]
    fn test_int_lt_trichotomy_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_lt_trichotomy_proof()
            .expect("first registration");
        env.register_int_lt_trichotomy_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.lt_trichotomy"))
            .expect("Int.lt_trichotomy should be registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "Int.lt_trichotomy must be a Theorem (constructive proof), got {:?}",
            info.kind
        );
    }

    #[test]
    fn test_int_lt_trichotomy_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_lt_trichotomy_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.lt_trichotomy"))
            .expect("Int.lt_trichotomy is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.lt_trichotomy must have empty domain-axiom closure, got {domain_deps:?}"
        );
    }

    #[test]
    fn test_int_lt_trichotomy_proof_quality_constructive() {
        let mut env = Environment::new();
        env.register_int_lt_trichotomy_proof().unwrap();
        match env.proof_quality(&Name::from_string("Int.lt_trichotomy")) {
            Some(ProofQuality::Constructive) => {}
            other => panic!("Int.lt_trichotomy must be ProofQuality::Constructive, got {other:?}"),
        }
    }

    #[test]
    fn test_int_lt_trichotomy_type_checks() {
        use crate::tc::TypeChecker;

        let mut env = Environment::new();
        env.register_int_lt_trichotomy_proof().unwrap();

        let tc = TypeChecker::new(&env);
        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let lt_const = Expr::const_(Name::from_string("Int.lt"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let or_const = Expr::const_(Name::from_string("Or"), vec![]);

        let inferred = tc
            .infer_type(&Expr::const_(
                Name::from_string("Int.lt_trichotomy"),
                vec![],
            ))
            .expect("Int.lt_trichotomy should infer a type");

        // Expected: ∀ a b : Int, Or (Int.lt a b) (Or (Eq a b) (Int.lt b a))
        let expected = {
            let mut bld = EnvDeclBuilder::new();
            let (a_id, a) = bld.fresh_local(int_const.clone());
            let (b_id, bv) = bld.fresh_local(int_const.clone());
            let lt_ab = Expr::app(Expr::app(lt_const.clone(), a.clone()), bv.clone());
            let lt_ba = Expr::app(Expr::app(lt_const.clone(), bv.clone()), a.clone());
            let eq_ab = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), int_const.clone()), a),
                bv,
            );
            let inner = Expr::app(Expr::app(or_const.clone(), eq_ab), lt_ba);
            let r = Expr::app(Expr::app(or_const.clone(), lt_ab), inner);
            let r = bld.mk_pi(b_id, BinderInfo::Default, int_const.clone(), r);
            let r = bld.mk_pi(a_id, BinderInfo::Default, int_const.clone(), r);
            bld.finish(r)
        };

        assert!(
            tc.is_def_eq(&inferred, &expected),
            "Int.lt_trichotomy type mismatch: got {inferred:?}"
        );
    }

    #[test]
    fn test_int_lt_trichotomy_proof_uses_int_rec() {
        // The proof must perform a genuine `Int.rec` case-analysis (not be an
        // axiom restatement). After peeling the two outer λ binders (over `a`,
        // `b`), the proof root's application head must be `@Int.rec`.
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_lt_trichotomy_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.lt_trichotomy"))
            .expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.as_ref().expect("Theorem carries a value");
        // Peel λ a => λ b => <body>.
        let mut body = value.clone();
        for _ in 0..2 {
            body = match body.kind() {
                ExprKind::Lam(_, _, inner) => (**inner).clone(),
                k => panic!("expected outer λ, got {k:?}"),
            };
        }
        // Walk the application spine to its head.
        let mut head = body;
        while let ExprKind::App(f, _) = head.kind() {
            head = (**f).clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Int.rec",
                "Int.lt_trichotomy proof root must be Int.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Int.rec, ..) at proof root, got {k:?}"),
        }
    }
}
