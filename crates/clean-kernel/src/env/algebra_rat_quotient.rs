// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// WS-A live carrier swap (in progress): the quotient definitions, lifted ops,
// and payoff theorems below are wired into `init_rat` / `init_rat_arith` /
// `init_rat_ord` incrementally. Until every builder is wired, some helpers are
// staged but not yet called; the allow keeps the staged-but-green steps clean.
//! A NORMALIZED rational type built as a `Quot` makes the
//! structural-equality axioms that are FALSE over the free `Rat.mk : Int → Nat`
//! carrier into GENUINE kernel-checked theorems.
//!
//! # The soundness bug this validates a fix for
//!
//! The live `Rat` is the free inductive `Rat.mk : Int → Nat → Rat` with NO
//! `denom > 0` / reduced-form invariant, so structural `@Eq Rat` facts are
//! FALSE:
//!
//! - `Rat.zero_mul : ∀ a, Rat.mul Rat.zero a = Rat.zero` is false because
//!   `mul (mk 0 1) (mk 3 5) = mk 0 5`, structurally distinct from `mk 0 1`.
//! - `Rat.le_antisymm : ∀ a b, le a b → le b a → Eq a b` is false because
//!   `mk 1 1` and `mk 2 2` are `≤` both ways yet structurally distinct.
//!
//! # The fix this module validates
//!
//! A QUOTIENT carrier `Qat := Quot Qat.Raw.Equiv`, where two raw fractions are
//! `Equiv` iff their cross-products are equal, identifies all representatives
//! of the same rational. Under that quotient BOTH axioms above become
//! `Quot.sound`-closed theorems — built ENTIRELY through the checked
//! `self.add_decl` path (no `sorry`, no `add_decl_unchecked`,
//! no `add_decl_structural`). `Quot.sound` and `propext` are FOUNDATIONAL, so
//! the payoff theorems classify as `ProofQuality::Constructive`.
//!
//! Fresh names live under the `Qat` namespace; the live `Rat` is untouched, so
//! this compiles alongside it. Everything is registered by
//! [`Environment::init_rat_quotient_poc`].

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved constant handles + small smart-constructors for the quotient
/// `Rat` carrier swap. Mirrors the `LeTransConsts` idiom in
/// `algebra_rat_le_trans_proof.rs`.
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
pub(crate) struct RatRawConsts {
    // Sorts.
    prop: Expr,
    // Int / Nat.
    int: Expr,
    nat: Expr,
    int_mul: Expr,
    int_le: Expr,
    int_of_nat: Expr,
    int_zero: Expr,
    nat_mul: Expr,
    nat_succ: Expr,
    nat_pred: Expr,
    nat_zero: Expr,
    // Raw carrier.
    raw: Expr,
    raw_mk: Expr,
    raw_num: Expr,
    raw_denom: Expr,
    raw_eff_denom: Expr,
    raw_equiv: Expr,
    // Quotient (Qat.Raw : Type 0 = Sort 1, so Quot lives at level 1).
    ratq: Expr,
    ratq_mk: Expr,
    quot: Expr,
    quot_mk: Expr,
    quot_lift: Expr,
    quot_sound: Expr,
    quot_ind: Expr,
    // Eq machinery (all at `Eq.{1}` — Int and Qat both live in `Type 0`).
    eq_int: Expr,
    eq_ratq: Expr,
    eq_refl_int: Expr,
    eq_symm_int: Expr,
    eq_trans_int: Expr,
    congr_arg: Expr,
    // Int lemmas (constructive Theorems registered elsewhere).
    int_mul_comm: Expr,
    int_mul_assoc: Expr,
    int_mul_left_cancel: Expr,
    int_le_antisymm: Expr,
    int_zero_mul: Expr,
    int_le_refl: Expr,
    int_le_cross_trans: Expr,
    eq_subst_int: Expr,
    propext: Expr,
    // `Quot.lift.{1,1}` into `Prop` (codomain `Prop = Sort 1`).
    quot_lift_prop: Expr,
    // Int lemmas for the additive / distributive / order theorems.
    int_add: Expr,
    int_neg: Expr,
    #[cfg(test)]
    int_zero_2: Expr,
    int_add_comm: Expr,
    int_add_assoc: Expr,
    int_left_distrib: Expr,
    int_right_distrib: Expr,
    int_mul_zero: Expr,
    int_neg_mul_left: Expr,
    int_neg_mul_right: Expr,
    #[cfg(test)]
    int_add_le_add_left: Expr,
    #[cfg(test)]
    int_mul_le_mul_of_nonneg_right: Expr,
    int_neg_add_self: Expr,
    int_add_neg_self: Expr,
    int_mul_one: Expr,
    // Strict order (`Rat.lt`) toolkit.
    int_lt: Expr,
    int_lt_cross_trans: Expr,
    // Order-monotonicity (`Rat.add_le_add_left` / `Rat.le_add_of_nonneg_right`).
    int_mul_le_mul_right: Expr,
    int_add_le_add_left_const: Expr,
    int_mul_nonneg: Expr,
    int_ofnat_zero_le: Expr,
    int_add_zero: Expr,
    // Field (`Rat.inv` / `Rat.div`) toolkit.
    int_rec: Expr,
    nat_rec: Expr,
    int_neg_neg: Expr,
    int_neg_succ: Expr,
    /// `Int.rec.{0}` — Prop motive (the `inv` respect goal is an `Eq`, in Prop).
    int_rec_prop: Expr,
    /// `Nat.rec.{0}` — Prop motive, for the inner ofNat-zero/succ split.
    nat_rec_prop: Expr,
    /// `Int.noConfusion.{0}` — discharges impossible mixed-sign `hp` leaves.
    int_no_confusion: Expr,
    /// `Nat.noConfusion.{0}` — discharges the `0 = succ _` magnitude leaves.
    nat_no_confusion: Expr,
    /// `False` / `@False.elim.{0}` — for the `mul_inv_cancel` zero leaf, where
    /// `np = 0` contradicts `a ≠ 0`.
    false_elim: Expr,
    // Order-lemma toolkit (`Rat.le_refl` / `le_total` / `lt_iff_le_not_le` /
    // `mul_pos` / `mul_nonneg` over the quotient).
    int_le_total: Expr,
    int_lt_iff_le_not_le: Expr,
    int_mul_pos: Expr,
    int_zero_mul_2: Expr,
}

impl RatRawConsts {
    pub(crate) fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        Self {
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            int: Expr::const_(Name::from_string("Int"), vec![]),
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            int_mul: Expr::const_(Name::from_string("Int.mul"), vec![]),
            int_le: Expr::const_(Name::from_string("Int.le"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_zero: Expr::const_(Name::from_string("Int.zero"), vec![]),
            nat_mul: Expr::const_(Name::from_string("Nat.mul"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_pred: Expr::const_(Name::from_string("Nat.pred"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            raw: Expr::const_(Name::from_string("Rat.Raw"), vec![]),
            raw_mk: Expr::const_(Name::from_string("Rat.Raw.mk"), vec![]),
            raw_num: Expr::const_(Name::from_string("Rat.Raw.num"), vec![]),
            raw_denom: Expr::const_(Name::from_string("Rat.Raw.denom"), vec![]),
            raw_eff_denom: Expr::const_(Name::from_string("Rat.Raw.effDenom"), vec![]),
            raw_equiv: Expr::const_(Name::from_string("Rat.Raw.Equiv"), vec![]),
            ratq: Expr::const_(Name::from_string("Rat"), vec![]),
            ratq_mk: Expr::const_(Name::from_string("Rat.mk"), vec![]),
            quot: Expr::const_(Name::from_string("Quot"), vec![lvl1.clone()]),
            quot_mk: Expr::const_(Name::from_string("Quot.mk"), vec![lvl1.clone()]),
            quot_lift: Expr::const_(
                Name::from_string("Quot.lift"),
                vec![lvl1.clone(), lvl1.clone()],
            ),
            quot_sound: Expr::const_(Name::from_string("Quot.sound"), vec![lvl1.clone()]),
            quot_ind: Expr::const_(Name::from_string("Quot.ind"), vec![lvl1.clone()]),
            eq_int: Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
            eq_ratq: Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
            eq_refl_int: Expr::const_(Name::from_string("Eq.refl"), vec![lvl1.clone()]),
            eq_symm_int: Expr::const_(Name::from_string("Eq.symm"), vec![lvl1.clone()]),
            eq_trans_int: Expr::const_(Name::from_string("Eq.trans"), vec![lvl1.clone()]),
            congr_arg: Expr::const_(
                Name::from_string("congrArg"),
                vec![lvl1.clone(), lvl1.clone()],
            ),
            int_mul_comm: Expr::const_(Name::from_string("Int.mul_comm"), vec![]),
            int_mul_assoc: Expr::const_(Name::from_string("Int.mul_assoc"), vec![]),
            int_mul_left_cancel: Expr::const_(
                Name::from_string("Int.mul_left_cancel_ofNat_succ"),
                vec![],
            ),
            int_le_antisymm: Expr::const_(Name::from_string("Int.le_antisymm"), vec![]),
            int_zero_mul: Expr::const_(Name::from_string("Int.zero_mul"), vec![]),
            int_le_refl: Expr::const_(Name::from_string("Int.le_refl"), vec![]),
            int_le_cross_trans: Expr::const_(Name::from_string("Int.le_cross_trans"), vec![]),
            eq_subst_int: Expr::const_(
                Name::from_string("Eq.subst"),
                vec![Level::succ(Level::zero())],
            ),
            propext: Expr::const_(Name::from_string("propext"), vec![]),
            quot_lift_prop: Expr::const_(
                Name::from_string("Quot.lift"),
                vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
            ),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_neg: Expr::const_(Name::from_string("Int.neg"), vec![]),
            #[cfg(test)]
            int_zero_2: Expr::const_(Name::from_string("Int.zero"), vec![]),
            int_add_comm: Expr::const_(Name::from_string("Int.add_comm"), vec![]),
            int_add_assoc: Expr::const_(Name::from_string("Int.add_assoc"), vec![]),
            int_left_distrib: Expr::const_(Name::from_string("Int.left_distrib"), vec![]),
            int_right_distrib: Expr::const_(Name::from_string("Int.right_distrib"), vec![]),
            int_mul_zero: Expr::const_(Name::from_string("Int.mul_zero"), vec![]),
            int_neg_mul_left: Expr::const_(Name::from_string("Int.neg_mul_left"), vec![]),
            int_neg_mul_right: Expr::const_(Name::from_string("Int.neg_mul_right"), vec![]),
            #[cfg(test)]
            int_add_le_add_left: Expr::const_(Name::from_string("Int.add_le_add_left"), vec![]),
            #[cfg(test)]
            int_mul_le_mul_of_nonneg_right: Expr::const_(
                Name::from_string("Int.mul_le_mul_of_nonneg_right"),
                vec![],
            ),
            int_neg_add_self: Expr::const_(Name::from_string("Int.neg_add_self"), vec![]),
            int_add_neg_self: Expr::const_(Name::from_string("Int.add_neg_self"), vec![]),
            int_mul_one: Expr::const_(Name::from_string("Int.mul_one"), vec![]),
            int_lt: Expr::const_(Name::from_string("Int.lt"), vec![]),
            int_lt_cross_trans: Expr::const_(Name::from_string("Int.lt_cross_trans"), vec![]),
            int_mul_le_mul_right: Expr::const_(
                Name::from_string("Int.mul_le_mul_of_nonneg_right"),
                vec![],
            ),
            int_add_le_add_left_const: Expr::const_(
                Name::from_string("Int.add_le_add_left"),
                vec![],
            ),
            int_mul_nonneg: Expr::const_(Name::from_string("Int.mul_nonneg"), vec![]),
            int_ofnat_zero_le: Expr::const_(Name::from_string("Int.ofNat_zero_le"), vec![]),
            int_add_zero: Expr::const_(Name::from_string("Int.add_zero"), vec![]),
            int_rec: Expr::const_(Name::from_string("Int.rec"), vec![lvl1.clone()]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![lvl1]),
            int_neg_neg: Expr::const_(Name::from_string("Int.neg_neg"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            int_rec_prop: Expr::const_(Name::from_string("Int.rec"), vec![Level::zero()]),
            nat_rec_prop: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            int_no_confusion: Expr::const_(
                Name::from_string("Int.noConfusion"),
                vec![Level::zero()],
            ),
            nat_no_confusion: Expr::const_(
                Name::from_string("Nat.noConfusion"),
                vec![Level::zero()],
            ),
            false_elim: Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            int_le_total: Expr::const_(Name::from_string("Int.le_total"), vec![]),
            int_lt_iff_le_not_le: Expr::const_(Name::from_string("Int.lt_iff_le_not_le"), vec![]),
            int_mul_pos: Expr::const_(Name::from_string("Int.mul_pos"), vec![]),
            int_zero_mul_2: Expr::const_(Name::from_string("Int.zero_mul"), vec![]),
        }
    }

    // ── Int / Nat smart-constructors ────────────────────────────────────────

    /// `Int.mul x y`.
    fn mul(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_mul.clone(), [x, y])
    }

    /// `Int.ofNat n`.
    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }

    /// `Nat.mul x y`.
    fn nmul(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.nat_mul.clone(), [x, y])
    }

    // ── Raw carrier smart-constructors ──────────────────────────────────────

    /// `Qat.Raw.mk n d`.
    fn raw_mk(&self, n: Expr, d: Expr) -> Expr {
        Expr::apps(self.raw_mk.clone(), [n, d])
    }

    /// `Qat.Raw.num p`.
    fn num(&self, p: Expr) -> Expr {
        Expr::app(self.raw_num.clone(), p)
    }

    /// `Int.ofNat (Qat.Raw.effDenom p)` — the positive effective denominator,
    /// which is DEFINITIONALLY `Int.ofNat (Nat.succ (Nat.pred (denom p)))`.
    fn eff(&self, p: Expr) -> Expr {
        self.of_nat(Expr::app(self.raw_eff_denom.clone(), p))
    }

    /// `Qat.Raw.Equiv p q`.
    fn equiv(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.raw_equiv.clone(), [p, q])
    }

    // ── Eq smart-constructors (`Eq.{1}` over `Int`) ─────────────────────────

    /// `@Eq.{1} Int x y` (a Prop).
    fn eq_int_ty(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.eq_int.clone(), [self.int.clone(), x, y])
    }

    /// `@Eq.refl.{1} Int x : Eq Int x x`.
    fn refl_int(&self, x: Expr) -> Expr {
        Expr::apps(self.eq_refl_int.clone(), [self.int.clone(), x])
    }

    /// `@Eq.symm.{1} Int x y h : Eq Int y x`.
    fn symm_int(&self, x: Expr, y: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm_int.clone(), [self.int.clone(), x, y, h])
    }

    /// `@Eq.trans.{1} Int x y z h1 h2 : Eq Int x z`.
    fn trans_int(&self, x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans_int.clone(),
            [self.int.clone(), x, y, z, h1, h2],
        )
    }

    /// `@congrArg.{1,1} Int Int x y f h : Eq (f x) (f y)`.
    fn congr_arg(&self, x: Expr, y: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.int.clone(), self.int.clone(), x, y, f, h],
        )
    }

    // ── Rat-level (`Eq.{1}` over `Rat`) smart-constructors ──────────────────

    /// `@Eq.symm.{1} Rat x y h : Eq Rat y x`.
    fn rsymm(&self, x: Expr, y: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm_int.clone(), [self.ratq.clone(), x, y, h])
    }

    /// `@Eq.trans.{1} Rat x y z h1 h2 : Eq Rat x z`.
    fn rtrans(&self, x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans_int.clone(),
            [self.ratq.clone(), x, y, z, h1, h2],
        )
    }

    /// `@congrArg.{1,1} Rat Rat x y f h : Eq Rat (f x)(f y)`.
    fn rcongr(&self, x: Expr, y: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.ratq.clone(), self.ratq.clone(), x, y, f, h],
        )
    }

    /// `f := fun w => Rat.add w y` (Rat-level congrArg on the left summand).
    fn radd_left_fn(&self, parent: &EnvDeclBuilder, y: Expr) -> Expr {
        let ratq_add = Expr::const_(Name::from_string("Rat.add"), vec![]);
        let mut ch = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = ch.fresh_local(self.ratq.clone());
        let body = Expr::apps(ratq_add, [w, y]);
        let lam = ch.mk_lam(w_id, BinderInfo::Default, self.ratq.clone(), body);
        ch.finish_child(lam)
    }

    /// `Int.mul_comm x y : Eq (x*y) (y*x)`.
    fn mul_comm(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_mul_comm.clone(), [x, y])
    }

    /// `Int.mul_assoc x y z : Eq ((x*y)*z) (x*(y*z))`.
    fn mul_assoc(&self, x: Expr, y: Expr, z: Expr) -> Expr {
        Expr::apps(self.int_mul_assoc.clone(), [x, y, z])
    }

    /// `Int.zero_mul a : Eq (Int.mul Int.zero a) Int.zero`.
    fn zero_mul(&self, a: Expr) -> Expr {
        Expr::app(self.int_zero_mul.clone(), a)
    }

    /// `Int.add x y`.
    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_add.clone(), [x, y])
    }

    /// `Int.neg x`.
    fn neg(&self, x: Expr) -> Expr {
        Expr::app(self.int_neg.clone(), x)
    }

    /// `Int.add_comm x y : Eq (x+y) (y+x)`.
    fn add_comm(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_add_comm.clone(), [x, y])
    }

    /// `Int.add_assoc x y z : Eq ((x+y)+z) (x+(y+z))`.
    fn add_assoc(&self, x: Expr, y: Expr, z: Expr) -> Expr {
        Expr::apps(self.int_add_assoc.clone(), [x, y, z])
    }

    /// `Int.left_distrib a b c : Eq (a*(b+c)) (a*b + a*c)`.
    fn left_distrib(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.int_left_distrib.clone(), [a, b, cc])
    }

    /// `Int.right_distrib a b c : Eq ((a+b)*c) (a*c + b*c)`.
    fn right_distrib(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.int_right_distrib.clone(), [a, b, cc])
    }

    /// `Int.mul_zero a : Eq (a * Int.zero) Int.zero`.
    fn mul_zero(&self, a: Expr) -> Expr {
        Expr::app(self.int_mul_zero.clone(), a)
    }

    /// `Int.neg_mul_left a b : Eq (Int.neg (a*b)) ((Int.neg a)*b)`.
    fn neg_mul_left(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.int_neg_mul_left.clone(), [a, b])
    }

    /// `Int.neg_mul_right a b : Eq (Int.neg (a*b)) (a*(Int.neg b))`.
    fn neg_mul_right(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.int_neg_mul_right.clone(), [a, b])
    }

    /// `Int.neg_add_self a : Eq ((Int.neg a) + a) Int.zero`.
    fn neg_add_self(&self, a: Expr) -> Expr {
        Expr::app(self.int_neg_add_self.clone(), a)
    }

    /// `Int.add_neg_self a : Eq (a + (Int.neg a)) Int.zero`.
    fn add_neg_self(&self, a: Expr) -> Expr {
        Expr::app(self.int_add_neg_self.clone(), a)
    }

    /// `Int.mul_one a : Eq (Int.mul a (Int.ofNat 1)) a`.
    fn mul_one(&self, a: Expr) -> Expr {
        Expr::app(self.int_mul_one.clone(), a)
    }

    /// `f := fun w => x * w`  (congrArg on the right factor).
    fn mul_left_fn(&self, parent: &EnvDeclBuilder, x: Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = ch.fresh_local(self.int.clone());
        let body = self.mul(x, w);
        let lam = ch.mk_lam(w_id, BinderInfo::Default, self.int.clone(), body);
        ch.finish_child(lam)
    }

    /// `f := fun w => w * x`  (congrArg on the left factor).
    fn mul_right_fn(&self, parent: &EnvDeclBuilder, x: Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = ch.fresh_local(self.int.clone());
        let body = self.mul(w, x);
        let lam = ch.mk_lam(w_id, BinderInfo::Default, self.int.clone(), body);
        ch.finish_child(lam)
    }

    // ── Quot smart-constructors over the `Qat.Raw` / `Qat.Raw.Equiv` carrier ─

    /// `@Quot.mk.{1} Qat.Raw Qat.Raw.Equiv l : Qat` (relation EXPLICIT). The
    /// result is definitionally `Qat`, since `Qat := @Quot.{1} Qat.Raw Equiv`.
    fn quot_mk(&self, l: Expr) -> Expr {
        Expr::apps(
            self.quot_mk.clone(),
            [self.raw.clone(), self.raw_equiv.clone(), l],
        )
    }

    /// `@Quot.sound.{1} Qat.Raw Qat.Raw.Equiv a b h
    ///    : @Eq Qat (Quot.mk _ a) (Quot.mk _ b)` (relation/a/b IMPLICIT but
    /// passed positionally, as in `data_types_multiset.rs`).
    fn quot_sound(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.quot_sound.clone(),
            [self.raw.clone(), self.raw_equiv.clone(), a, b, h],
        )
    }

    /// `@Quot.mk.{1} Qat.Raw Qat.Raw.Equiv`, the raw `Qat.mk`-class function
    /// partially applied (used as `Quot.ind`'s `mk` argument unfolds it).
    fn mul_mul_mul_comm(&self, a: Expr, bb: Expr, cc: Expr, d: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.Int.mulMulMulComm"), vec![]),
            [a, bb, cc, d],
        )
    }

    /// `mulMulMulComm2 a b c d : (a·b)·(c·d) = (a·d)·(c·b)` — the "swap the inner
    /// pair" rearrangement. Built inline from `mulMulMulComm` + `mul_comm`:
    ///   `(a·b)·(c·d)` =[mmmc a b c d] `(a·c)·(b·d)`
    ///                 =[congrArg ((a·c)·) (mul_comm b d)] `(a·c)·(d·b)`
    ///                 =[symm (mmmc a d c b)] `(a·d)·(c·b)`.
    fn mul_mul_mul_comm2(
        &self,
        parent: &EnvDeclBuilder,
        a: &Expr,
        bb: &Expr,
        cc: &Expr,
        d: &Expr,
    ) -> Expr {
        let ab = self.mul(a.clone(), bb.clone());
        let cd = self.mul(cc.clone(), d.clone());
        let lhs = self.mul(ab, cd);
        let ac = self.mul(a.clone(), cc.clone());
        let bd = self.mul(bb.clone(), d.clone());
        let mid1 = self.mul(ac.clone(), bd.clone());
        let db = self.mul(d.clone(), bb.clone());
        let mid2 = self.mul(ac.clone(), db.clone());
        let ad = self.mul(a.clone(), d.clone());
        let cb = self.mul(cc.clone(), bb.clone());
        let rhs = self.mul(ad, cb);
        // s1 : lhs = mid1
        let s1 = self.mul_mul_mul_comm(a.clone(), bb.clone(), cc.clone(), d.clone());
        // s2 : mid1 = mid2   [congrArg ((a·c)·) (mul_comm b d)]
        let s2 = self.congr_arg(
            bd.clone(),
            db.clone(),
            self.mul_left_fn(parent, ac.clone()),
            self.mul_comm(bb.clone(), d.clone()),
        );
        // s3 : mid2 = rhs   [symm (mmmc a d c b)]
        let s3 = self.symm_int(
            rhs.clone(),
            mid2.clone(),
            self.mul_mul_mul_comm(a.clone(), d.clone(), cc.clone(), bb.clone()),
        );
        let t1 = self.trans_int(lhs.clone(), mid1.clone(), mid2.clone(), s1, s2);
        self.trans_int(lhs, mid2, rhs, t1, s3)
    }

    /// Cross-multiplication proof for the SECOND-argument respect of `Qat.mul`.
    ///
    /// Given numerators/effDenoms `np, nq, ep, eq` of `p, q` and `nq2, eq2` of
    /// `q'` together with `hq : Eq (nq·eq2) (nq2·eq)` (i.e. `Equiv q q'`),
    /// build a proof of
    ///   `Eq ((np·nq)·(ep·eq2)) ((np·nq2)·(ep·eq))`,
    /// which is DEFINITIONALLY `Equiv (Raw.mul p q) (Raw.mul p q')` (the result
    /// effDenoms reduce to the Int products `ep·eq`, `ep·eq2`).
    #[allow(clippy::too_many_arguments)]
    fn mul_cross_right(
        &self,
        parent: &EnvDeclBuilder,
        np: &Expr,
        nq: &Expr,
        ep: &Expr,
        eq: &Expr,
        nq2: &Expr,
        eq2: &Expr,
        hq: &Expr,
    ) -> Expr {
        // f := fun w => (np·ep) * w  (congrArg on the right factor).
        let np_ep = self.mul(np.clone(), ep.clone());
        let mul_left_np_ep = {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = ch.fresh_local(self.int.clone());
            let body = self.mul(np_ep.clone(), w);
            let lam = ch.mk_lam(w_id, BinderInfo::Default, self.int.clone(), body);
            ch.finish_child(lam)
        };
        // LHS := (np·nq)·(ep·eq2) ; goal RHS := (np·nq2)·(ep·eq).
        let np_nq = self.mul(np.clone(), nq.clone());
        let ep_eq2 = self.mul(ep.clone(), eq2.clone());
        let lhs = self.mul(np_nq.clone(), ep_eq2.clone());
        let np_nq2 = self.mul(np.clone(), nq2.clone());
        let ep_eq = self.mul(ep.clone(), eq.clone());
        let rhs = self.mul(np_nq2.clone(), ep_eq.clone());

        // step1 : (np·nq)·(ep·eq2) = (np·ep)·(nq·eq2)   [mulMulMulComm np nq ep eq2]
        let nq_eq2 = self.mul(nq.clone(), eq2.clone());
        let mid1 = self.mul(np_ep.clone(), nq_eq2.clone());
        let step1 = self.mul_mul_mul_comm(np.clone(), nq.clone(), ep.clone(), eq2.clone());
        // step2 : (np·ep)·(nq·eq2) = (np·ep)·(nq2·eq)   [congrArg ((np·ep)*·) hq]
        let nq2_eq = self.mul(nq2.clone(), eq.clone());
        let mid2 = self.mul(np_ep.clone(), nq2_eq.clone());
        let step2 = self.congr_arg(nq_eq2.clone(), nq2_eq.clone(), mul_left_np_ep, hq.clone());
        // step3 : (np·ep)·(nq2·eq) = (np·nq2)·(ep·eq)   [mulMulMulComm np ep nq2 eq]
        let step3 = self.mul_mul_mul_comm(np.clone(), ep.clone(), nq2.clone(), eq.clone());

        // chain step1 ; step2 ; step3.
        let t1 = self.trans_int(lhs.clone(), mid1.clone(), mid2.clone(), step1, step2);
        self.trans_int(lhs, mid2, rhs, t1, step3)
    }

    /// Cross-multiplication proof for the FIRST-argument respect of `Qat.mul`.
    ///
    /// Given `np, ep, nq, eq` of `p, q` and `np2, ep2` of `p'` together with
    /// `hp : Eq (np·ep2) (np2·ep)` (i.e. `Equiv p p'`), build a proof of
    ///   `Eq ((np·nq)·(ep2·eq)) ((np2·nq)·(ep·eq))`,
    /// definitionally `Equiv (Raw.mul p q) (Raw.mul p' q)`.
    #[allow(clippy::too_many_arguments)]
    fn mul_cross_left(
        &self,
        parent: &EnvDeclBuilder,
        np: &Expr,
        ep: &Expr,
        nq: &Expr,
        eq: &Expr,
        np2: &Expr,
        ep2: &Expr,
        hp: &Expr,
    ) -> Expr {
        // f := fun w => w * (nq·eq)  (congrArg on the left factor).
        let nq_eq = self.mul(nq.clone(), eq.clone());
        let mul_right_nq_eq = {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = ch.fresh_local(self.int.clone());
            let body = self.mul(w, nq_eq.clone());
            let lam = ch.mk_lam(w_id, BinderInfo::Default, self.int.clone(), body);
            ch.finish_child(lam)
        };
        // LHS := (np·nq)·(ep2·eq) ; RHS := (np2·nq)·(ep·eq).
        let np_nq = self.mul(np.clone(), nq.clone());
        let ep2_eq = self.mul(ep2.clone(), eq.clone());
        let lhs = self.mul(np_nq.clone(), ep2_eq.clone());
        let np2_nq = self.mul(np2.clone(), nq.clone());
        let ep_eq = self.mul(ep.clone(), eq.clone());
        let rhs = self.mul(np2_nq.clone(), ep_eq.clone());

        // step1 : (np·nq)·(ep2·eq) = (np·ep2)·(nq·eq)   [mulMulMulComm np nq ep2 eq]
        let np_ep2 = self.mul(np.clone(), ep2.clone());
        let mid1 = self.mul(np_ep2.clone(), nq_eq.clone());
        let step1 = self.mul_mul_mul_comm(np.clone(), nq.clone(), ep2.clone(), eq.clone());
        // step2 : (np·ep2)·(nq·eq) = (np2·ep)·(nq·eq)   [congrArg (·*(nq·eq)) hp]
        let np2_ep = self.mul(np2.clone(), ep.clone());
        let mid2 = self.mul(np2_ep.clone(), nq_eq.clone());
        let step2 = self.congr_arg(np_ep2.clone(), np2_ep.clone(), mul_right_nq_eq, hp.clone());
        // step3 : (np2·ep)·(nq·eq) = (np2·nq)·(ep·eq)   [mulMulMulComm np2 ep nq eq]
        let step3 = self.mul_mul_mul_comm(np2.clone(), ep.clone(), nq.clone(), eq.clone());

        let t1 = self.trans_int(lhs.clone(), mid1.clone(), mid2.clone(), step1, step2);
        self.trans_int(lhs, mid2, rhs, t1, step3)
    }

    /// `Term1 : (np·eq)·(ep·eq2) = (np·eq2)·(ep·eq)` — the cross-respect of the
    /// FIRST addend `np·E?` of `Raw.add p ?` under the SECOND-argument move.
    /// Both sides normalize to `(np·ep)·(eq·eq2)` / `(np·ep)·(eq2·eq)` via
    /// `mulMulMulComm`, then `mul_comm eq eq2`.
    fn add_term1_right(
        &self,
        parent: &EnvDeclBuilder,
        np: &Expr,
        ep: &Expr,
        eq: &Expr,
        eq2: &Expr,
    ) -> Expr {
        let np_eq = self.mul(np.clone(), eq.clone());
        let ep_eq2 = self.mul(ep.clone(), eq2.clone());
        let lhs = self.mul(np_eq, ep_eq2);
        let np_ep = self.mul(np.clone(), ep.clone());
        let eq_eq2 = self.mul(eq.clone(), eq2.clone());
        let mid1 = self.mul(np_ep.clone(), eq_eq2.clone());
        let eq2_eq = self.mul(eq2.clone(), eq.clone());
        let mid2 = self.mul(np_ep.clone(), eq2_eq.clone());
        let np_eq2 = self.mul(np.clone(), eq2.clone());
        let ep_eq = self.mul(ep.clone(), eq.clone());
        let rhs = self.mul(np_eq2, ep_eq);
        // s1 : lhs = (np·ep)·(eq·eq2)
        let s1 = self.mul_mul_mul_comm(np.clone(), eq.clone(), ep.clone(), eq2.clone());
        // s2 : (np·ep)·(eq·eq2) = (np·ep)·(eq2·eq)  [congrArg ((np·ep)·)(mul_comm eq eq2)]
        let s2 = self.congr_arg(
            eq_eq2.clone(),
            eq2_eq.clone(),
            self.mul_left_fn(parent, np_ep.clone()),
            self.mul_comm(eq.clone(), eq2.clone()),
        );
        // s3 : (np·ep)·(eq2·eq) = (np·eq2)·(ep·eq)  [symm (mmmc np eq2 ep eq)]
        let s3 = self.symm_int(
            rhs.clone(),
            mid2.clone(),
            self.mul_mul_mul_comm(np.clone(), eq2.clone(), ep.clone(), eq.clone()),
        );
        let t1 = self.trans_int(lhs.clone(), mid1.clone(), mid2.clone(), s1, s2);
        self.trans_int(lhs, mid2, rhs, t1, s3)
    }

    /// `Term2 : (nq·ep)·(ep·eq2) = (nq2·ep)·(ep·eq)` — the cross-respect of the
    /// SECOND addend `n?·ep` of `Raw.add p ?` under the SECOND-argument move,
    /// from `hq : nq·eq2 = nq2·eq`. Both sides normalize to `(nq·eq2)·(ep·ep)` /
    /// `(nq2·eq)·(ep·ep)` via `mulMulMulComm2`, then `hq`.
    #[allow(clippy::too_many_arguments)]
    fn add_term2_right(
        &self,
        parent: &EnvDeclBuilder,
        nq: &Expr,
        ep: &Expr,
        eq: &Expr,
        nq2: &Expr,
        eq2: &Expr,
        hq: &Expr,
    ) -> Expr {
        let nq_ep = self.mul(nq.clone(), ep.clone());
        let ep_eq2 = self.mul(ep.clone(), eq2.clone());
        let lhs = self.mul(nq_ep, ep_eq2);
        let nq_eq2 = self.mul(nq.clone(), eq2.clone());
        let ep_ep = self.mul(ep.clone(), ep.clone());
        let mid1 = self.mul(nq_eq2.clone(), ep_ep.clone());
        let nq2_eq = self.mul(nq2.clone(), eq.clone());
        let mid2 = self.mul(nq2_eq.clone(), ep_ep.clone());
        let nq2_ep = self.mul(nq2.clone(), ep.clone());
        let ep_eq = self.mul(ep.clone(), eq.clone());
        let rhs = self.mul(nq2_ep, ep_eq);
        // s1 : lhs = (nq·eq2)·(ep·ep)   [mmmc2 nq ep ep eq2]
        let s1 = self.mul_mul_mul_comm2(parent, nq, ep, ep, eq2);
        // s2 : (nq·eq2)·(ep·ep) = (nq2·eq)·(ep·ep)  [congrArg (·*(ep·ep)) hq]
        let s2 = self.congr_arg(
            nq_eq2.clone(),
            nq2_eq.clone(),
            self.mul_right_fn(parent, ep_ep.clone()),
            hq.clone(),
        );
        // s3 : (nq2·eq)·(ep·ep) = (nq2·ep)·(ep·eq)  [symm (mmmc2 nq2 ep ep eq)]
        let s3 = self.symm_int(
            rhs.clone(),
            mid2.clone(),
            self.mul_mul_mul_comm2(parent, nq2, ep, ep, eq),
        );
        let t1 = self.trans_int(lhs.clone(), mid1.clone(), mid2.clone(), s1, s2);
        self.trans_int(lhs, mid2, rhs, t1, s3)
    }

    /// SECOND-argument cross-respect for `Qat.add`: from `hq : nq·eq2 = nq2·eq`
    /// (i.e. `Equiv q q'`) build a proof of
    ///   `Eq ((np·eq + nq·ep)·(ep·eq2)) ((np·eq2 + nq2·ep)·(ep·eq))`,
    /// DEFINITIONALLY `Equiv (Raw.add p q)(Raw.add p q')` (result effDenoms
    /// reduce to the Int products `ep·eq`, `ep·eq2`). Built from `right_distrib`
    /// on both sides plus `add_term1_right` / `add_term2_right`.
    #[allow(clippy::too_many_arguments)]
    fn add_cross_right(
        &self,
        parent: &EnvDeclBuilder,
        np: &Expr,
        nq: &Expr,
        ep: &Expr,
        eq: &Expr,
        nq2: &Expr,
        eq2: &Expr,
        hq: &Expr,
    ) -> Expr {
        let np_eq = self.mul(np.clone(), eq.clone());
        let nq_ep = self.mul(nq.clone(), ep.clone());
        let l_num = self.add(np_eq.clone(), nq_ep.clone());
        let np_eq2 = self.mul(np.clone(), eq2.clone());
        let nq2_ep = self.mul(nq2.clone(), ep.clone());
        let r_num = self.add(np_eq2.clone(), nq2_ep.clone());
        let ep_eq2 = self.mul(ep.clone(), eq2.clone());
        let ep_eq = self.mul(ep.clone(), eq.clone());
        let lhs = self.mul(l_num.clone(), ep_eq2.clone());
        let rhs = self.mul(r_num.clone(), ep_eq.clone());

        // d1 : lhs = (np·eq)·(ep·eq2) + (nq·ep)·(ep·eq2)   [right_distrib]
        let t1l = self.mul(np_eq.clone(), ep_eq2.clone());
        let t2l = self.mul(nq_ep.clone(), ep_eq2.clone());
        let sum_l = self.add(t1l.clone(), t2l.clone());
        let d1 = self.right_distrib(np_eq.clone(), nq_ep.clone(), ep_eq2.clone());
        // d2 : rhs = (np·eq2)·(ep·eq) + (nq2·ep)·(ep·eq)   [right_distrib]
        let t1r = self.mul(np_eq2.clone(), ep_eq.clone());
        let t2r = self.mul(nq2_ep.clone(), ep_eq.clone());
        let sum_r = self.add(t1r.clone(), t2r.clone());
        let d2 = self.right_distrib(np_eq2.clone(), nq2_ep.clone(), ep_eq.clone());
        // mid : sum_l = sum_r   [add_cong term1 term2]
        let term1 = self.add_term1_right(parent, np, ep, eq, eq2);
        let term2 = self.add_term2_right(parent, nq, ep, eq, nq2, eq2, hq);
        let mid = self.add_cong(parent, &t1l, &t1r, &t2l, &t2r, &term1, &term2);
        // lhs = sum_l = sum_r = rhs.
        let t = self.trans_int(lhs.clone(), sum_l.clone(), sum_r.clone(), d1, mid);
        let d2_sym = self.symm_int(rhs.clone(), sum_r.clone(), d2);
        self.trans_int(lhs, sum_r, rhs, t, d2_sym)
    }

    /// FIRST-argument cross-respect for `Qat.add`: from `hp : np·ep2 = np2·ep`
    /// (i.e. `Equiv p p'`) build a proof of
    ///   `Eq ((np·eq + nq·ep)·(ep2·eq)) ((np2·eq + nq·ep2)·(ep·eq))`,
    /// DEFINITIONALLY `Equiv (Raw.add p q)(Raw.add p' q)`. Built symmetrically
    /// to `add_cross_right` (the FIRST addend carries `hp`, the second is the
    /// pure-commute term).
    #[allow(clippy::too_many_arguments)]
    fn add_cross_left(
        &self,
        parent: &EnvDeclBuilder,
        np: &Expr,
        ep: &Expr,
        nq: &Expr,
        eq: &Expr,
        np2: &Expr,
        ep2: &Expr,
        hp: &Expr,
    ) -> Expr {
        let np_eq = self.mul(np.clone(), eq.clone());
        let nq_ep = self.mul(nq.clone(), ep.clone());
        let l_num = self.add(np_eq.clone(), nq_ep.clone());
        let np2_eq = self.mul(np2.clone(), eq.clone());
        let nq_ep2 = self.mul(nq.clone(), ep2.clone());
        let r_num = self.add(np2_eq.clone(), nq_ep2.clone());
        let ep2_eq = self.mul(ep2.clone(), eq.clone());
        let ep_eq = self.mul(ep.clone(), eq.clone());
        let lhs = self.mul(l_num.clone(), ep2_eq.clone());
        let rhs = self.mul(r_num.clone(), ep_eq.clone());

        // d1 : lhs = (np·eq)·(ep2·eq) + (nq·ep)·(ep2·eq)   [right_distrib]
        let t1l = self.mul(np_eq.clone(), ep2_eq.clone());
        let t2l = self.mul(nq_ep.clone(), ep2_eq.clone());
        let sum_l = self.add(t1l.clone(), t2l.clone());
        let d1 = self.right_distrib(np_eq.clone(), nq_ep.clone(), ep2_eq.clone());
        // d2 : rhs = (np2·eq)·(ep·eq) + (nq·ep2)·(ep·eq)   [right_distrib]
        let t1r = self.mul(np2_eq.clone(), ep_eq.clone());
        let t2r = self.mul(nq_ep2.clone(), ep_eq.clone());
        let sum_r = self.add(t1r.clone(), t2r.clone());
        let d2 = self.right_distrib(np2_eq.clone(), nq_ep2.clone(), ep_eq.clone());
        // term1 : (np·eq)·(ep2·eq) = (np2·eq)·(ep·eq)  — carries hp.
        //   Reuse add_term2_right's shape: it proves
        //   (n·d)·(e·f) = (n'·d)·(e·f') style. Build directly here.
        //   (np·eq)·(ep2·eq) =[mmmc2 np eq ep2 eq] (np·eq)·(ep2·eq)? use a direct route:
        //   normalize both to (np·ep2)·(eq·eq) / (np2·ep)·(eq·eq) via mmmc, then hp.
        let term1 = {
            // lhs1 = (np·eq)·(ep2·eq) ; rhs1 = (np2·eq)·(ep·eq).
            let lhs1 = self.mul(np_eq.clone(), ep2_eq.clone());
            let np_ep2 = self.mul(np.clone(), ep2.clone());
            let eq_eq = self.mul(eq.clone(), eq.clone());
            let m1 = self.mul(np_ep2.clone(), eq_eq.clone());
            let np2_ep = self.mul(np2.clone(), ep.clone());
            let m2 = self.mul(np2_ep.clone(), eq_eq.clone());
            let rhs1 = self.mul(np2_eq.clone(), ep_eq.clone());
            // s1 : (np·eq)·(ep2·eq) = (np·ep2)·(eq·eq)   [mmmc np eq ep2 eq]
            let s1 = self.mul_mul_mul_comm(np.clone(), eq.clone(), ep2.clone(), eq.clone());
            // s2 : (np·ep2)·(eq·eq) = (np2·ep)·(eq·eq)   [congrArg (·*(eq·eq)) hp]
            let s2 = self.congr_arg(
                np_ep2.clone(),
                np2_ep.clone(),
                self.mul_right_fn(parent, eq_eq.clone()),
                hp.clone(),
            );
            // s3 : (np2·ep)·(eq·eq) = (np2·eq)·(ep·eq)   [symm (mmmc np2 eq ep eq)]
            let s3 = self.symm_int(
                rhs1.clone(),
                m2.clone(),
                self.mul_mul_mul_comm(np2.clone(), eq.clone(), ep.clone(), eq.clone()),
            );
            let tt = self.trans_int(lhs1.clone(), m1.clone(), m2.clone(), s1, s2);
            self.trans_int(lhs1, m2, rhs1, tt, s3)
        };
        // term2 : (nq·ep)·(ep2·eq) = (nq·ep2)·(ep·eq)  — pure commute, no hyp.
        let term2 = {
            let lhs2 = self.mul(nq_ep.clone(), ep2_eq.clone());
            let nq_ep2b = self.mul(nq.clone(), ep2.clone());
            let ep_eqb = self.mul(ep.clone(), eq.clone());
            let m1 = self.mul(nq_ep2b.clone(), ep_eqb.clone());
            let rhs2 = self.mul(nq_ep2.clone(), ep_eq.clone());
            // (nq·ep)·(ep2·eq) =[mmmc2 nq ep ep2 eq] (nq·eq)·(ep2·ep)? Need (nq·ep2)·(ep·eq).
            //   mmmc nq ep ep2 eq : (nq·ep)·(ep2·eq) = (nq·ep2)·(ep·eq). Exactly term2!
            let direct = self.mul_mul_mul_comm(nq.clone(), ep.clone(), ep2.clone(), eq.clone());
            // direct : (nq·ep)·(ep2·eq) = (nq·ep2)·(ep·eq) = rhs2.  m1 unused guard.
            let _ = (m1, rhs2, lhs2);
            direct
        };
        let mid = self.add_cong(parent, &t1l, &t1r, &t2l, &t2r, &term1, &term2);
        let t = self.trans_int(lhs.clone(), sum_l.clone(), sum_r.clone(), d1, mid);
        let d2_sym = self.symm_int(rhs.clone(), sum_r.clone(), d2);
        self.trans_int(lhs, sum_r, rhs, t, d2_sym)
    }

    /// `f := fun w => Int.add w y`  (congrArg on the left summand).
    fn add_left_fn(&self, parent: &EnvDeclBuilder, y: Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = ch.fresh_local(self.int.clone());
        let body = self.add(w, y);
        let lam = ch.mk_lam(w_id, BinderInfo::Default, self.int.clone(), body);
        ch.finish_child(lam)
    }

    /// `f := fun w => Int.add x w`  (congrArg on the right summand).
    fn add_right_fn(&self, parent: &EnvDeclBuilder, x: Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = ch.fresh_local(self.int.clone());
        let body = self.add(x, w);
        let lam = ch.mk_lam(w_id, BinderInfo::Default, self.int.clone(), body);
        ch.finish_child(lam)
    }

    /// Congruence on a binary `Int.add`: from `hx : Eq x1 x2`, `hy : Eq y1 y2`
    /// build `Eq (x1+y1) (x2+y2)` via two `congrArg` + `Eq.trans` steps.
    #[allow(clippy::too_many_arguments)]
    fn add_cong(
        &self,
        parent: &EnvDeclBuilder,
        x1: &Expr,
        x2: &Expr,
        y1: &Expr,
        y2: &Expr,
        hx: &Expr,
        hy: &Expr,
    ) -> Expr {
        let lhs = self.add(x1.clone(), y1.clone());
        let mid = self.add(x2.clone(), y1.clone());
        let rhs = self.add(x2.clone(), y2.clone());
        // step1 : x1+y1 = x2+y1   [congrArg (·+y1) hx]
        let step1 = self.congr_arg(
            x1.clone(),
            x2.clone(),
            self.add_left_fn(parent, y1.clone()),
            hx.clone(),
        );
        // step2 : x2+y1 = x2+y2   [congrArg (x2+·) hy]
        let step2 = self.congr_arg(
            y1.clone(),
            y2.clone(),
            self.add_right_fn(parent, x2.clone()),
            hy.clone(),
        );
        self.trans_int(lhs, mid, rhs, step1, step2)
    }

    // ── Order / Prop smart-constructors (for `Qat.le`) ──────────────────────

    /// `Int.le x y` (a Prop).
    fn int_le(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_le.clone(), [x, y])
    }

    /// `Int.lt x y` (a Prop).
    fn int_lt(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_lt.clone(), [x, y])
    }

    /// `Qat.Raw.lt p q := Int.lt (num p · eff q) (num q · eff p)` — the raw
    /// (pre-quotient) strict order, INLINED (we never register `Qat.Raw.lt`).
    fn raw_lt(&self, p: &Expr, q: &Expr) -> Expr {
        let lhs = self.mul(self.num(p.clone()), self.eff(q.clone()));
        let rhs = self.mul(self.num(q.clone()), self.eff(p.clone()));
        self.int_lt(lhs, rhs)
    }

    /// `Int.lt_cross_trans na nb nc da db dc h1 h2`
    ///   : `Int.lt (na·E dc) (nc·E da)` from
    ///     `h1 : Int.lt (na·E db) (nb·E da)`, `h2 : Int.le (nb·E dc) (nc·E db)`,
    /// where `E k := Int.ofNat (Nat.succ k)`. (h2 is `≤`, supplied via
    /// `le_of_eq` from the `Equiv` cross-equality.)
    #[allow(clippy::too_many_arguments)]
    fn lt_cross_trans(
        &self,
        na: Expr,
        nb: Expr,
        nc: Expr,
        da: Expr,
        db: Expr,
        dc: Expr,
        h1: Expr,
        h2: Expr,
    ) -> Expr {
        Expr::apps(
            self.int_lt_cross_trans.clone(),
            [na, nb, nc, da, db, dc, h1, h2],
        )
    }

    /// `Qat.Raw.le p q := Int.le (num p · eff q) (num q · eff p)` — the raw
    /// (pre-quotient) order, INLINED (we never register `Qat.Raw.le`; it is the
    /// body of the lift).
    fn raw_le(&self, p: &Expr, q: &Expr) -> Expr {
        let lhs = self.mul(self.num(p.clone()), self.eff(q.clone()));
        let rhs = self.mul(self.num(q.clone()), self.eff(p.clone()));
        self.int_le(lhs, rhs)
    }

    /// `@propext P1 P2 (Iff.intro P1 P2 fwd bwd) : @Eq Prop P1 P2`.
    ///
    /// The faithful Lean `propext : {a b} → (a ↔ b) → a = b` takes a single
    /// `Iff`; we package the two implications `fwd : P1 → P2` / `bwd : P2 → P1`
    /// via `Iff.intro` (same proof content) to build the `P1 ↔ P2` argument.
    fn propext(&self, p1: Expr, p2: Expr, fwd: Expr, bwd: Expr) -> Expr {
        let iff = Expr::apps(
            Expr::const_(Name::from_string("Iff.intro"), vec![]),
            [p1.clone(), p2.clone(), fwd, bwd],
        );
        Expr::apps(self.propext.clone(), [p1, p2, iff])
    }

    /// `Int.le_cross_trans na nb nc da db dc h1 h2`
    ///   : `Int.le (na·E dc) (nc·E da)` from
    ///     `h1 : Int.le (na·E db) (nb·E da)`, `h2 : Int.le (nb·E dc) (nc·E db)`,
    /// where `E k := Int.ofNat (Nat.succ k)`.
    #[allow(clippy::too_many_arguments)]
    fn le_cross_trans(
        &self,
        na: Expr,
        nb: Expr,
        nc: Expr,
        da: Expr,
        db: Expr,
        dc: Expr,
        h1: Expr,
        h2: Expr,
    ) -> Expr {
        Expr::apps(
            self.int_le_cross_trans.clone(),
            [na, nb, nc, da, db, dc, h1, h2],
        )
    }

    /// `@Eq.subst.{1} Int (fun z => Int.le lo z) x y h_eq (Int.le_refl lo)`
    ///   : `Int.le lo y` from `h_eq : Eq x y` and the fact `lo ≤ x ≡ x` here
    /// `lo := x` so the seed is `Int.le_refl x`. Concretely turns
    /// `h_eq : Eq a b` into `Int.le a b` (a ≤ b because a = b).
    fn le_of_eq(&self, parent: &EnvDeclBuilder, a: &Expr, bb: &Expr, h_eq: &Expr) -> Expr {
        // motive := fun z => Int.le a z
        let motive = {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = ch.fresh_local(self.int.clone());
            let body = self.int_le(a.clone(), z);
            let lam = ch.mk_lam(z_id, BinderInfo::Default, self.int.clone(), body);
            ch.finish_child(lam)
        };
        // seed := Int.le_refl a : Int.le a a
        let seed = Expr::app(self.int_le_refl.clone(), a.clone());
        // @Eq.subst Int motive a b h_eq seed : Int.le a b
        Expr::apps(
            self.eq_subst_int.clone(),
            [
                self.int.clone(),
                motive,
                a.clone(),
                bb.clone(),
                h_eq.clone(),
                seed,
            ],
        )
    }

    /// `kd x := Nat.pred (Qat.Raw.denom x)` — the `n` such that
    /// `eff x ≡ Int.ofNat (Nat.succ n)`, the shape `Int.le_cross_trans` wants.
    fn kd(&self, x: &Expr) -> Expr {
        Expr::app(
            self.nat_pred.clone(),
            Expr::app(self.raw_denom.clone(), x.clone()),
        )
    }

    /// One implication of the SECOND-argument order respect:
    /// `Raw.le p q → Raw.le p q'`, from `hq : Equiv q q'`
    /// (`nq·eff q' = nq2·eff q`). Built from `Int.le_cross_trans`.
    fn le_impl_right(
        &self,
        parent: &EnvDeclBuilder,
        p: &Expr,
        q: &Expr,
        q2: &Expr,
        hq: &Expr,
    ) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let pre = self.raw_le(p, q);
        let (hle_id, hle) = ch.fresh_local(pre.clone());
        // h2 : Int.le (nq·E(kd q2)) (nq2·E(kd q))  from hq via le_of_eq.
        let nq_effq2 = self.mul(self.num(q.clone()), self.eff(q2.clone()));
        let nq2_effq = self.mul(self.num(q2.clone()), self.eff(q.clone()));
        let h2 = self.le_of_eq(&ch, &nq_effq2, &nq2_effq, hq);
        // cross_trans np nq nq2 (kd p)(kd q)(kd q2) hle h2 : Raw.le p q'.
        let body = self.le_cross_trans(
            self.num(p.clone()),
            self.num(q.clone()),
            self.num(q2.clone()),
            self.kd(p),
            self.kd(q),
            self.kd(q2),
            hle,
            h2,
        );
        let lam = ch.mk_lam(hle_id, BinderInfo::Default, pre, body);
        ch.finish_child(lam)
    }

    /// SECOND-argument order respect as a `Prop` equality:
    /// `@Eq Prop (Raw.le p q) (Raw.le p q')` via `propext` of both implications
    /// (the backward one swaps `q, q'` and uses `Eq.symm hq`).
    fn le_respects_right(
        &self,
        parent: &EnvDeclBuilder,
        p: &Expr,
        q: &Expr,
        q2: &Expr,
        hq: &Expr,
    ) -> Expr {
        let fwd = self.le_impl_right(parent, p, q, q2, hq);
        // hq_symm : Equiv q' q  ≡  nq2·eff q = nq·eff q'.
        let nq_effq2 = self.mul(self.num(q.clone()), self.eff(q2.clone()));
        let nq2_effq = self.mul(self.num(q2.clone()), self.eff(q.clone()));
        let hq_symm = self.symm_int(nq_effq2, nq2_effq, hq.clone());
        let bwd = self.le_impl_right(parent, p, q2, q, &hq_symm);
        self.propext(self.raw_le(p, q), self.raw_le(p, q2), fwd, bwd)
    }

    /// One implication of the FIRST-argument order respect:
    /// `Raw.le p q → Raw.le p' q`, from `hp : Equiv p p'`
    /// (`np·eff p' = np2·eff p`). Built from `Int.le_cross_trans`.
    fn le_impl_left(
        &self,
        parent: &EnvDeclBuilder,
        p: &Expr,
        p2: &Expr,
        q: &Expr,
        hp: &Expr,
    ) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let pre = self.raw_le(p, q);
        let (hle_id, hle) = ch.fresh_local(pre.clone());
        // Goal: Raw.le p' q ≡ Int.le (np2·E q) (nq·E p2).
        // Use cross_trans with na=nq, nb=np, nc=np2 and da=kd q, db=kd p, dc=kd p2:
        //   h1 : nq·E(kd p) ≤ np·E(kd q)   — that is `Raw.le q p`, the SYMMetric
        //        statement of `Raw.le p q` (le on Int is the same prop after the
        //        commutation np·E q ≤ nq·E p ⇒ flip), so we instead pick the
        //        orientation that matches `hle` directly:
        //   na=np, nb=nq is wrong for a LEFT move; we move the FIRST factor.
        //
        // Cleaner: cross_trans na=np, nb=np2? No — cross_trans changes the
        // `nc/dc` (third) slot. We need to change the FIRST operand p→p'. Use
        // cross_trans on the SWAPPED order `Raw.le q p` then swap back. Simplest
        // is the direct route below.
        //
        // Direct: from hle : np·E q ≤ nq·E p and hp : np·E p2 = np2·E p, derive
        // np2·E q ≤ nq·E p2. Set in cross_trans:
        //   na = np2, nb = np, nc = nq, da = kd p2, db = kd p, dc = kd q
        //   h1 : np2·E(kd p) ≤ np·E(kd p2)   [from hp, an equality, via le_of_eq]
        //   h2 : np·E(kd q)  ≤ nq·E(kd p)    [= hle]
        //   ⇒  np2·E(kd q) ≤ nq·E(kd p2)     [= Raw.le p' q]  ✓
        let np2_effp = self.mul(self.num(p2.clone()), self.eff(p.clone()));
        let np_effp2 = self.mul(self.num(p.clone()), self.eff(p2.clone()));
        // hp : np·eff p2 = np2·eff p ; we need np2·E(kd p) ≤ np·E(kd p2),
        // i.e. le_of_eq from (np2·eff p = np·eff p2) = Eq.symm hp.
        let hp_symm = self.symm_int(np_effp2.clone(), np2_effp.clone(), hp.clone());
        let h1 = self.le_of_eq(&ch, &np2_effp, &np_effp2, &hp_symm);
        let body = self.le_cross_trans(
            self.num(p2.clone()),
            self.num(p.clone()),
            self.num(q.clone()),
            self.kd(p2),
            self.kd(p),
            self.kd(q),
            h1,
            hle,
        );
        let lam = ch.mk_lam(hle_id, BinderInfo::Default, pre, body);
        ch.finish_child(lam)
    }

    /// FIRST-argument order respect as a `Prop` equality:
    /// `@Eq Prop (Raw.le p q) (Raw.le p' q)` via `propext`.
    fn le_respects_left(
        &self,
        parent: &EnvDeclBuilder,
        p: &Expr,
        p2: &Expr,
        q: &Expr,
        hp: &Expr,
    ) -> Expr {
        let fwd = self.le_impl_left(parent, p, p2, q, hp);
        let np_effp2 = self.mul(self.num(p.clone()), self.eff(p2.clone()));
        let np2_effp = self.mul(self.num(p2.clone()), self.eff(p.clone()));
        let hp_symm = self.symm_int(np_effp2, np2_effp, hp.clone());
        let bwd = self.le_impl_left(parent, p2, p, q, &hp_symm);
        self.propext(self.raw_le(p, q), self.raw_le(p2, q), fwd, bwd)
    }

    // ── Strict order respect (for `Qat.lt`) ─────────────────────────────────

    /// One implication of the SECOND-argument STRICT order respect:
    /// `Raw.lt p q → Raw.lt p q'`, from `hq : Equiv q q'`
    /// (`nq·eff q' = nq2·eff q`). Built from `Int.lt_cross_trans`, with the
    /// strict hyp `Raw.lt p q` in `h1` and the equality `hq` (as a `≤` via
    /// `le_of_eq`) in `h2`.
    fn lt_impl_right(
        &self,
        parent: &EnvDeclBuilder,
        p: &Expr,
        q: &Expr,
        q2: &Expr,
        hq: &Expr,
    ) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let pre = self.raw_lt(p, q);
        let (hlt_id, hlt) = ch.fresh_local(pre.clone());
        // h2 : Int.le (nq·E(kd q2)) (nq2·E(kd q))  from hq via le_of_eq.
        let nq_effq2 = self.mul(self.num(q.clone()), self.eff(q2.clone()));
        let nq2_effq = self.mul(self.num(q2.clone()), self.eff(q.clone()));
        let h2 = self.le_of_eq(&ch, &nq_effq2, &nq2_effq, hq);
        // lt_cross_trans np nq nq2 (kd p)(kd q)(kd q2) hlt h2 : Raw.lt p q'.
        let body = self.lt_cross_trans(
            self.num(p.clone()),
            self.num(q.clone()),
            self.num(q2.clone()),
            self.kd(p),
            self.kd(q),
            self.kd(q2),
            hlt,
            h2,
        );
        let lam = ch.mk_lam(hlt_id, BinderInfo::Default, pre, body);
        ch.finish_child(lam)
    }

    /// SECOND-argument strict order respect as a `Prop` equality:
    /// `@Eq Prop (Raw.lt p q) (Raw.lt p q')` via `propext`.
    fn lt_respects_right(
        &self,
        parent: &EnvDeclBuilder,
        p: &Expr,
        q: &Expr,
        q2: &Expr,
        hq: &Expr,
    ) -> Expr {
        let fwd = self.lt_impl_right(parent, p, q, q2, hq);
        let nq_effq2 = self.mul(self.num(q.clone()), self.eff(q2.clone()));
        let nq2_effq = self.mul(self.num(q2.clone()), self.eff(q.clone()));
        let hq_symm = self.symm_int(nq_effq2, nq2_effq, hq.clone());
        let bwd = self.lt_impl_right(parent, p, q2, q, &hq_symm);
        self.propext(self.raw_lt(p, q), self.raw_lt(p, q2), fwd, bwd)
    }

    /// One implication of the FIRST-argument STRICT order respect:
    /// `Raw.lt p q → Raw.lt p' q`, from `hp : Equiv p p'`
    /// (`np·eff p' = np2·eff p`). The goal `Raw.lt p' q ≡
    /// Int.lt (np2·E q) (nq·E p2)` is produced by `Int.lt_cross_trans'`
    /// (`le → lt → lt`): the equality `hp` (as a `≤`) occupies the `h1` slot,
    /// the strict hyp `Raw.lt p q` occupies the `h2` slot. Index map (mirrors
    /// `le_impl_left`): na=np2, nb=np, nc=nq, da=kd p2, db=kd p, dc=kd q.
    ///   h1 : np2·E(kd p) ≤ np·E(kd p2)   [from hp via le_of_eq]
    ///   h2 : np·E(kd q)  < nq·E(kd p)    [= Raw.lt p q, strict]
    ///   ⇒  np2·E(kd q)  < nq·E(kd p2)    [= Raw.lt p' q]
    fn lt_impl_left(
        &self,
        parent: &EnvDeclBuilder,
        p: &Expr,
        p2: &Expr,
        q: &Expr,
        hp: &Expr,
    ) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let pre = self.raw_lt(p, q);
        let (hlt_id, hlt) = ch.fresh_local(pre.clone());
        // h1 : np2·E(kd p) ≤ np·E(kd p2)  from hp : np·eff p2 = np2·eff p.
        let np_effp2 = self.mul(self.num(p.clone()), self.eff(p2.clone()));
        let np2_effp = self.mul(self.num(p2.clone()), self.eff(p.clone()));
        // le_of_eq needs an equality `a = b` to prove `a ≤ b`; we want
        // np2·E p ≤ np·E p2, i.e. from (np2·eff p = np·eff p2) = symm hp.
        let hp_symm = self.symm_int(np_effp2.clone(), np2_effp.clone(), hp.clone());
        let h1 = self.le_of_eq(&ch, &np2_effp, &np_effp2, &hp_symm);
        // h2 : np·E(kd q) < nq·E(kd p)  = hlt (Raw.lt p q).
        let body = self.lt_cross_trans_le_lt(
            self.num(p2.clone()),
            self.num(p.clone()),
            self.num(q.clone()),
            self.kd(p2),
            self.kd(p),
            self.kd(q),
            h1,
            hlt,
        );
        let lam = ch.mk_lam(hlt_id, BinderInfo::Default, pre, body);
        ch.finish_child(lam)
    }

    /// FIRST-argument strict order respect as a `Prop` equality:
    /// `@Eq Prop (Raw.lt p q) (Raw.lt p' q)` via `propext`.
    fn lt_respects_left(
        &self,
        parent: &EnvDeclBuilder,
        p: &Expr,
        p2: &Expr,
        q: &Expr,
        hp: &Expr,
    ) -> Expr {
        let fwd = self.lt_impl_left(parent, p, p2, q, hp);
        let np_effp2 = self.mul(self.num(p.clone()), self.eff(p2.clone()));
        let np2_effp = self.mul(self.num(p2.clone()), self.eff(p.clone()));
        let hp_symm = self.symm_int(np_effp2, np2_effp, hp.clone());
        let bwd = self.lt_impl_left(parent, p2, p, q, &hp_symm);
        self.propext(self.raw_lt(p, q), self.raw_lt(p2, q), fwd, bwd)
    }

    /// `Int.lt_cross_trans' na nb nc da db dc h1 h2`
    ///   : `Int.lt (na·E dc) (nc·E da)` from
    ///     `h1 : Int.le (na·E db) (nb·E da)`, `h2 : Int.lt (nb·E dc) (nc·E db)`,
    /// where `E k := Int.ofNat (Nat.succ k)`. The `le → lt → lt` companion of
    /// `Int.lt_cross_trans`, used by the FIRST-argument strict respect (the
    /// `Equiv`-equality lands in `h1`, the strict order datum in `h2`).
    #[allow(clippy::too_many_arguments)]
    fn lt_cross_trans_le_lt(
        &self,
        na: Expr,
        nb: Expr,
        nc: Expr,
        da: Expr,
        db: Expr,
        dc: Expr,
        h1: Expr,
        h2: Expr,
    ) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Int.lt_cross_trans'"), vec![]),
            [na, nb, nc, da, db, dc, h1, h2],
        )
    }

    // ── Order-monotonicity smart-constructors (for the payoff order axioms) ──

    /// `Int.mul_le_mul_of_nonneg_right a b cc h hc : Int.le (a·cc) (b·cc)`.
    fn mul_le_mul_right(&self, a: Expr, b: Expr, cc: Expr, h: Expr, hc: Expr) -> Expr {
        Expr::apps(self.int_mul_le_mul_right.clone(), [a, b, cc, h, hc])
    }

    /// `Int.add_le_add_left a b h cc : Int.le (cc+a) (cc+b)`.
    fn add_le_add_left_int(&self, a: Expr, b: Expr, h: Expr, cc: Expr) -> Expr {
        Expr::apps(self.int_add_le_add_left_const.clone(), [a, b, h, cc])
    }

    /// `Int.mul_nonneg a b ha hb : Int.le 0 (a·b)`.
    fn mul_nonneg(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.int_mul_nonneg.clone(), [a, b, ha, hb])
    }

    /// `Int.le 0 (Int.ofNat (Nat.succ n))` via `Int.ofNat_zero_le (Nat.succ n)`.
    /// `effDenom x ≡ Nat.succ (Nat.pred (denom x))`, so `Int.ofNat (effDenom x)`
    /// is `Int.ofNat (Nat.succ _)`, the shape `Int.ofNat_zero_le` consumes.
    fn nonneg_eff(&self, x: &Expr) -> Expr {
        Expr::app(
            self.int_ofnat_zero_le.clone(),
            Expr::app(self.raw_eff_denom.clone(), x.clone()),
        )
    }

    /// `Int.add_zero a : Eq (Int.add a Int.zero) a`.
    fn add_zero(&self, a: Expr) -> Expr {
        Expr::app(self.int_add_zero.clone(), a)
    }

    /// Transport `h : Int.le lo x` along `h_eq : Eq x y` to `Int.le lo y`
    /// using `@Eq.subst.{0}` with motive `fun w => Int.le lo w` (Prop-valued).
    fn le_subst_right(
        &self,
        parent: &EnvDeclBuilder,
        lo: &Expr,
        x: &Expr,
        y: &Expr,
        h_eq: &Expr,
        h: &Expr,
    ) -> Expr {
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = mb.fresh_local(self.int.clone());
            let body = self.int_le(lo.clone(), w);
            let lam = mb.mk_lam(w_id, BinderInfo::Default, self.int.clone(), body);
            mb.finish_child(lam)
        };
        Expr::apps(
            self.eq_subst_int.clone(),
            [
                self.int.clone(),
                motive,
                x.clone(),
                y.clone(),
                h_eq.clone(),
                h.clone(),
            ],
        )
    }

    /// Transport `h : Int.le x hi` along `h_eq : Eq x y` to `Int.le y hi`
    /// using `@Eq.subst.{0}` with motive `fun w => Int.le w hi` (Prop-valued).
    fn le_subst_left(
        &self,
        parent: &EnvDeclBuilder,
        hi: &Expr,
        x: &Expr,
        y: &Expr,
        h_eq: &Expr,
        h: &Expr,
    ) -> Expr {
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = mb.fresh_local(self.int.clone());
            let body = self.int_le(w, hi.clone());
            let lam = mb.mk_lam(w_id, BinderInfo::Default, self.int.clone(), body);
            mb.finish_child(lam)
        };
        Expr::apps(
            self.eq_subst_int.clone(),
            [
                self.int.clone(),
                motive,
                x.clone(),
                y.clone(),
                h_eq.clone(),
                h.clone(),
            ],
        )
    }

    // ── Field (`Rat.inv`) sign-split smart-constructors ─────────────────────

    /// `Int.negSucc k`.
    fn neg_succ(&self, k: Expr) -> Expr {
        Expr::app(self.int_neg_succ.clone(), k)
    }

    /// `Nat.succ k`.
    fn nsucc(&self, k: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), k)
    }

    /// `Int.neg_neg a : Eq (Int.neg (Int.neg a)) a`.
    fn neg_neg(&self, a: Expr) -> Expr {
        Expr::app(self.int_neg_neg.clone(), a)
    }

    /// `f := fun w => Int.neg w` (congrArg on a negation).
    fn neg_fn(&self, parent: &EnvDeclBuilder) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = ch.fresh_local(self.int.clone());
        let body = self.neg(w);
        let lam = ch.mk_lam(w_id, BinderInfo::Default, self.int.clone(), body);
        ch.finish_child(lam)
    }

    /// `@Int.noConfusion.{0} P lhs rhs h` — discharge an impossible
    /// cross-constructor `h : Eq Int lhs rhs` directly, yielding the goal `P`.
    fn int_no_conf_refute(&self, p: Expr, lhs: Expr, rhs: Expr, h: Expr) -> Expr {
        Expr::apps(self.int_no_confusion.clone(), [p, lhs, rhs, h])
    }

    /// Refute a same-`ofNat`-constructor `h : Eq Int (ofNat a)(ofNat b)` whose
    /// fields `a, b` are DIFFERENT `Nat` constructors (`0` vs `succ _`):
    /// `Int.noConfusion` extracts `Eq Nat a b`, then `Nat.noConfusion` discharges
    /// it directly into the goal `P`. `mul_lhs`/`mul_rhs` are the reduced product
    /// forms (`ofNat a` / `ofNat b`) the `h` actually has.
    fn nat_field_refute(
        &self,
        parent: &EnvDeclBuilder,
        p: &Expr,
        mul_lhs: &Expr,
        mul_rhs: &Expr,
        nat_a: &Expr,
        nat_b: &Expr,
        h: &Expr,
    ) -> Expr {
        let eq_nat = |x: Expr, y: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [self.nat.clone(), x, y],
            )
        };
        let field_eq_ty = eq_nat(nat_a.clone(), nat_b.clone());
        // cont : Eq Nat a b → P  :=  λ e => Nat.noConfusion P a b e.
        let cont = {
            let mut cb = EnvDeclBuilder::child_of(parent);
            let (e_id, e) = cb.fresh_local(field_eq_ty.clone());
            let refute = Expr::apps(
                self.nat_no_confusion.clone(),
                [p.clone(), nat_a.clone(), nat_b.clone(), e],
            );
            let lam = cb.mk_lam(e_id, BinderInfo::Default, field_eq_ty.clone(), refute);
            cb.finish_child(lam)
        };
        Expr::apps(
            self.int_no_confusion.clone(),
            [p.clone(), mul_lhs.clone(), mul_rhs.clone(), h.clone(), cont],
        )
    }

    /// `raw_inv_from(parent, num_e, eff_nat_e)` — the sign-split inverse body as
    /// a function of an EXPLICIT numerator `num_e : Int` and effective
    /// denominator `eff_nat_e : Nat` (a `Nat.succ _`):
    ///   `Int.rec (λ _ => Raw) ofNatCase negSuccCase num_e` where
    ///     ofNatCase nat_n := Nat.rec (λ _ => Raw) (raw_mk 0 1)
    ///                          (λ m _ => raw_mk (ofNat eff_nat_e) (succ m)) nat_n
    ///     negSuccCase k   := raw_mk (neg (ofNat eff_nat_e)) (succ k).
    /// Keeping `num_e` as the recursor scrutinee lets the `inv` respect proof
    /// case on it via `Int.rec` (generalizing the goal over the numerator).
    fn raw_inv_from(&self, parent: &EnvDeclBuilder, num_e: &Expr, eff_nat_e: &Expr) -> Expr {
        let nat_one = self.nsucc(self.nat_zero.clone());
        let int_d = self.of_nat(eff_nat_e.clone());
        // motive : λ _ : Int => Raw.
        let inv_motive = Expr::lam(BinderInfo::Default, self.int.clone(), self.raw.clone());
        // ofNat case: λ nat_n : Nat => Nat.rec natMotive zeroCase succCase nat_n.
        let of_nat_case = {
            let mut b = EnvDeclBuilder::child_of(parent);
            let (nat_n_id, nat_n) = b.fresh_local(self.nat.clone());
            let nat_motive = Expr::lam(BinderInfo::Default, self.nat.clone(), self.raw.clone());
            let zero_case = self.raw_mk(self.int_zero.clone(), nat_one.clone());
            let succ_case = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (m_id, m) = s.fresh_local(self.nat.clone());
                let (ih_id, _ih) = s.fresh_local(self.raw.clone());
                let body = self.raw_mk(int_d.clone(), self.nsucc(m));
                let e = s.mk_lam(ih_id, BinderInfo::Default, self.raw.clone(), body);
                let e = s.mk_lam(m_id, BinderInfo::Default, self.nat.clone(), e);
                s.finish_child(e)
            };
            let body = Expr::apps(
                self.nat_rec.clone(),
                [nat_motive, zero_case, succ_case, nat_n],
            );
            let lam = b.mk_lam(nat_n_id, BinderInfo::Default, self.nat.clone(), body);
            b.finish_child(lam)
        };
        // negSucc case: λ k : Nat => raw_mk (neg (ofNat eff_nat_e)) (succ k).
        let neg_succ_case = {
            let mut b = EnvDeclBuilder::child_of(parent);
            let (k_id, k) = b.fresh_local(self.nat.clone());
            let neg_int_d = self.neg(int_d.clone());
            let body = self.raw_mk(neg_int_d, self.nsucc(k));
            let lam = b.mk_lam(k_id, BinderInfo::Default, self.nat.clone(), body);
            b.finish_child(lam)
        };
        Expr::apps(
            self.int_rec.clone(),
            [inv_motive, of_nat_case, neg_succ_case, num_e.clone()],
        )
    }

    /// `Raw.inv p := raw_inv_from(num p, effDenom p)`.
    fn raw_inv(&self, parent: &EnvDeclBuilder, p: &Expr) -> Expr {
        let eff_nat = Expr::app(self.raw_eff_denom.clone(), p.clone());
        self.raw_inv_from(parent, &self.num(p.clone()), &eff_nat)
    }

    /// The full `inv` respect proof body (see `register_rat_q_inv`).
    /// `p`, `p2` are the two raw reps; the enclosing builder binds `hp`.
    fn inv_respect(&self, parent: &EnvDeclBuilder, p: &Expr, p2: &Expr, hp: &Expr) -> Expr {
        // Fixed data: effDenom NATs and their ofNat lifts.
        let dp = Expr::app(self.raw_eff_denom.clone(), p.clone());
        let dp2 = Expr::app(self.raw_eff_denom.clone(), p2.clone());
        let ep = self.of_nat(dp.clone());
        let ep2 = self.of_nat(dp2.clone());
        let np2 = self.num(p2.clone());

        // invMk(z, dnat) := Quot.mk (raw_inv_from z dnat).
        let inv_mk = |parent: &EnvDeclBuilder, z: &Expr, dnat: &Expr| -> Expr {
            self.quot_mk(self.raw_inv_from(parent, z, dnat))
        };
        // hypTy(z, w) := Eq Int (z·Ep')(w·Ep).
        let hyp_ty = |z: &Expr, w: &Expr| -> Expr {
            self.eq_int_ty(
                self.mul(z.clone(), ep2.clone()),
                self.mul(w.clone(), ep.clone()),
            )
        };
        // goalEq(zRep, wRep) := Eq Rat zRep wRep.
        let goal_eq = |zrep: &Expr, wrep: &Expr| -> Expr {
            Expr::apps(
                self.eq_ratq.clone(),
                [self.ratq.clone(), zrep.clone(), wrep.clone()],
            )
        };

        // ── Inner Int.rec on np' (for a fixed outer z0 and its inv rep zr0) ──
        // Builds a term of type hypTy(z0, np') → Eq Rat zr0 (Quot.mk (Raw.inv p2)).
        // `okind`: 0 = outer zero, 1 = outer positive (z0=ofNat(succ m)),
        //          2 = outer negative (z0=negSucc k, magnitude mk0=ofNat(succ k)).
        let build_inner = |parent: &EnvDeclBuilder,
                           okind: u8,
                           z0: &Expr,
                           zr0: &Expr,
                           mk0: Option<&Expr>|
         -> Expr {
            // Inner motive N(w) := hypTy(z0,w) → Eq Rat zr0 (invMk(w, dp')).
            let n_motive = {
                let mut mb = EnvDeclBuilder::child_of(parent);
                let (w_id, w) = mb.fresh_local(self.int.clone());
                let wrep = inv_mk(&mb, &w, &dp2);
                let concl = goal_eq(zr0, &wrep);
                let hty = hyp_ty(z0, &w);
                let (h_id, _h) = mb.fresh_local(hty.clone());
                let pi = mb.mk_pi(h_id, BinderInfo::Default, hty, concl);
                let lam = mb.mk_lam(w_id, BinderInfo::Default, self.int.clone(), pi);
                mb.finish_child(lam)
            };

            // Inner ofNat case: Nat.rec on w's magnitude → {zero, pos} inner leaves.
            let inner_ofnat = {
                let mut ob = EnvDeclBuilder::child_of(parent);
                let (wn_id, wn) = ob.fresh_local(self.nat.clone());
                let w0 = self.of_nat(wn.clone());
                // inner Nat motive NN(wn) := hypTy(z0, ofNat wn) → Eq Rat zr0 (invMk(ofNat wn, dp')).
                let nn_motive = {
                    let mut mb = EnvDeclBuilder::child_of(&ob);
                    let (k_id, k) = mb.fresh_local(self.nat.clone());
                    let k_int = self.of_nat(k.clone());
                    let wrep = inv_mk(&mb, &k_int, &dp2);
                    let concl = goal_eq(zr0, &wrep);
                    let hty = hyp_ty(z0, &k_int);
                    let (h_id, _h) = mb.fresh_local(hty.clone());
                    let pi = mb.mk_pi(h_id, BinderInfo::Default, hty, concl);
                    let lam = mb.mk_lam(k_id, BinderInfo::Default, self.nat.clone(), pi);
                    mb.finish_child(lam)
                };
                // inner zero leaf: w = ofNat 0 ; inner rep = Quot.mk raw_zero.
                let nn_zero = {
                    let zb = EnvDeclBuilder::child_of(&ob);
                    let w0z = self.of_nat(self.nat_zero.clone());
                    let nat_one = self.nsucc(self.nat_zero.clone());
                    let wr0 = self.quot_mk(self.raw_mk(self.int_zero.clone(), nat_one));
                    let body = self.inv_leaf(
                        &zb, okind, 0, z0, &w0z, zr0, &wr0, &ep, &ep2, &dp, &dp2, mk0, None,
                    );
                    zb.finish_child(body)
                };
                // inner succ leaf: w = ofNat (succ m') ; rep = Quot.mk (raw_mk ep' (succ m')).
                let nn_succ = {
                    let mut sb = EnvDeclBuilder::child_of(&ob);
                    let (m2_id, m2) = sb.fresh_local(self.nat.clone());
                    let ih_ty = {
                        let k_int = self.of_nat(m2.clone());
                        let wrep = inv_mk(&sb, &k_int, &dp2);
                        let concl = goal_eq(zr0, &wrep);
                        let hty = hyp_ty(z0, &k_int);
                        let mut tb = EnvDeclBuilder::child_of(&sb);
                        let (hh_id, _hh) = tb.fresh_local(hty.clone());
                        let pi = tb.mk_pi(hh_id, BinderInfo::Default, hty, concl);
                        tb.finish_child(pi)
                    };
                    let (ih_id, _ih) = sb.fresh_local(ih_ty.clone());
                    let w0p = self.of_nat(self.nsucc(m2.clone()));
                    let mk2 = self.of_nat(self.nsucc(m2.clone()));
                    let wr0 = self.quot_mk(self.raw_mk(ep2.clone(), self.nsucc(m2.clone())));
                    let body = self.inv_leaf(
                        &sb,
                        okind,
                        1,
                        z0,
                        &w0p,
                        zr0,
                        &wr0,
                        &ep,
                        &ep2,
                        &dp,
                        &dp2,
                        mk0,
                        Some(&mk2),
                    );
                    let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                    let lam = sb.mk_lam(m2_id, BinderInfo::Default, self.nat.clone(), lam);
                    sb.finish_child(lam)
                };
                let rec = Expr::apps(
                    self.nat_rec_prop.clone(),
                    [nn_motive, nn_zero, nn_succ, wn.clone()],
                );
                let lam = ob.mk_lam(wn_id, BinderInfo::Default, self.nat.clone(), rec);
                let _ = w0;
                ob.finish_child(lam)
            };

            // Inner negSucc case: w = negSucc k', magnitude mk2 = ofNat(succ k').
            let inner_negsucc = {
                let mut nb = EnvDeclBuilder::child_of(parent);
                let (k2_id, k2) = nb.fresh_local(self.nat.clone());
                let w0 = self.neg_succ(k2.clone());
                let mk2 = self.of_nat(self.nsucc(k2.clone()));
                let wr0 = self.quot_mk(self.raw_mk(self.neg(ep2.clone()), self.nsucc(k2.clone())));
                let body = self.inv_leaf(
                    &nb,
                    okind,
                    2,
                    z0,
                    &w0,
                    zr0,
                    &wr0,
                    &ep,
                    &ep2,
                    &dp,
                    &dp2,
                    mk0,
                    Some(&mk2),
                );
                let lam = nb.mk_lam(k2_id, BinderInfo::Default, self.nat.clone(), body);
                nb.finish_child(lam)
            };

            Expr::apps(
                self.int_rec_prop.clone(),
                [n_motive, inner_ofnat, inner_negsucc, np2.clone()],
            )
        };

        // ── Outer Int.rec on np ──
        // Outer motive M(z) := hypTy(z, np') → Eq Rat (invMk(z, dp)) (Quot.mk (Raw.inv p2)).
        let m_motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = mb.fresh_local(self.int.clone());
            let zrep = inv_mk(&mb, &z, &dp);
            let rinvp2 = self.raw_inv(&mb, p2);
            let concl = goal_eq(&zrep, &self.quot_mk(rinvp2));
            let hty = hyp_ty(&z, &np2);
            let (h_id, _h) = mb.fresh_local(hty.clone());
            let pi = mb.mk_pi(h_id, BinderInfo::Default, hty, concl);
            let lam = mb.mk_lam(z_id, BinderInfo::Default, self.int.clone(), pi);
            mb.finish_child(lam)
        };

        // Outer ofNat case: Nat.rec on np's magnitude → {zero, pos}.
        let outer_ofnat = {
            let mut ob = EnvDeclBuilder::child_of(parent);
            let (zn_id, zn) = ob.fresh_local(self.nat.clone());
            // outer Nat motive MM(zn) := M(ofNat zn) form.
            let mm_motive = {
                let mut mb = EnvDeclBuilder::child_of(&ob);
                let (k_id, k) = mb.fresh_local(self.nat.clone());
                let k_int = self.of_nat(k.clone());
                let zrep = inv_mk(&mb, &k_int, &dp);
                let rinvp2 = self.raw_inv(&mb, p2);
                let concl = goal_eq(&zrep, &self.quot_mk(rinvp2));
                let hty = hyp_ty(&k_int, &np2);
                let (h_id, _h) = mb.fresh_local(hty.clone());
                let pi = mb.mk_pi(h_id, BinderInfo::Default, hty, concl);
                let lam = mb.mk_lam(k_id, BinderInfo::Default, self.nat.clone(), pi);
                mb.finish_child(lam)
            };
            // outer zero leaf: np = ofNat 0; zr0 = Quot.mk raw_zero.
            let mm_zero = {
                let zb = EnvDeclBuilder::child_of(&ob);
                let z0 = self.of_nat(self.nat_zero.clone());
                let nat_one = self.nsucc(self.nat_zero.clone());
                let zr0 = self.quot_mk(self.raw_mk(self.int_zero.clone(), nat_one));
                let body = build_inner(&zb, 0, &z0, &zr0, None);
                zb.finish_child(body)
            };
            // outer succ leaf: np = ofNat (succ m); zr0 = Quot.mk (raw_mk Ep (succ m)).
            let mm_succ = {
                let mut sb = EnvDeclBuilder::child_of(&ob);
                let (m_id, m) = sb.fresh_local(self.nat.clone());
                let z0 = self.of_nat(self.nsucc(m.clone()));
                let mk0 = self.of_nat(self.nsucc(m.clone()));
                let zr0 = self.quot_mk(self.raw_mk(ep.clone(), self.nsucc(m.clone())));
                // ih binder type = MM(m).
                let mm_m_ty = {
                    let k_int = self.of_nat(m.clone());
                    let zrep = inv_mk(&sb, &k_int, &dp);
                    let rinvp2 = self.raw_inv(&sb, p2);
                    let concl = goal_eq(&zrep, &self.quot_mk(rinvp2));
                    let hty = hyp_ty(&k_int, &np2);
                    let mut tb = EnvDeclBuilder::child_of(&sb);
                    let (hh_id, _hh) = tb.fresh_local(hty.clone());
                    let pi = tb.mk_pi(hh_id, BinderInfo::Default, hty, concl);
                    tb.finish_child(pi)
                };
                let (ih_id, _ih) = sb.fresh_local(mm_m_ty.clone());
                let body = build_inner(&sb, 1, &z0, &zr0, Some(&mk0));
                let lam = sb.mk_lam(ih_id, BinderInfo::Default, mm_m_ty, body);
                let lam = sb.mk_lam(m_id, BinderInfo::Default, self.nat.clone(), lam);
                sb.finish_child(lam)
            };
            let rec = Expr::apps(
                self.nat_rec_prop.clone(),
                [mm_motive, mm_zero, mm_succ, zn.clone()],
            );
            let lam = ob.mk_lam(zn_id, BinderInfo::Default, self.nat.clone(), rec);
            ob.finish_child(lam)
        };

        // Outer negSucc case: np = negSucc k; zr0 = Quot.mk (raw_mk (neg Ep) (succ k)).
        let outer_negsucc = {
            let mut nb = EnvDeclBuilder::child_of(parent);
            let (k_id, k) = nb.fresh_local(self.nat.clone());
            let z0 = self.neg_succ(k.clone());
            let mk0 = self.of_nat(self.nsucc(k.clone()));
            let zr0 = self.quot_mk(self.raw_mk(self.neg(ep.clone()), self.nsucc(k.clone())));
            let body = build_inner(&nb, 2, &z0, &zr0, Some(&mk0));
            let lam = nb.mk_lam(k_id, BinderInfo::Default, self.nat.clone(), body);
            nb.finish_child(lam)
        };

        // @Int.rec.{0} M outer_ofnat outer_negsucc (num p) : M(num p)
        //   = hypTy(num p, num p') → goal ; apply to hp.
        let np = self.num(p.clone());
        let outer_rec = Expr::apps(
            self.int_rec_prop.clone(),
            [m_motive, outer_ofnat, outer_negsucc, np],
        );
        // M(num p) = hypTy(num p, num p') → goal ; apply to hp.
        Expr::app(outer_rec, hp.clone())
    }

    /// One sign-leaf of the `inv` respect proof: `λ (h : hypTy(z0,w0)) => …`.
    /// `okind`/`ikind`: 0 = zero, 1 = positive, 2 = negative for the outer / inner
    /// numerator. `ep`/`ep2` are the fixed effDenom factors (`ofNat (effDenom
    /// p/p')`). `zr0`/`wr0` are the inv-class reps (`Quot.mk (raw_mk …)`) for the
    /// two numerators; `mk_o`/`mk_i` the magnitudes `ofNat(succ ·)` for nonzero
    /// kinds. Matching same-sign leaves close by `Quot.sound`; the rest are
    /// impossible and discharged by `Int.noConfusion` / `Nat.noConfusion`.
    #[allow(clippy::too_many_arguments)]
    fn inv_leaf(
        &self,
        parent: &EnvDeclBuilder,
        okind: u8,
        ikind: u8,
        z0: &Expr,
        w0: &Expr,
        zr0: &Expr,
        wr0: &Expr,
        ep: &Expr,
        ep2: &Expr,
        dp: &Expr,
        dp2: &Expr,
        mk_o: Option<&Expr>,
        mk_i: Option<&Expr>,
    ) -> Expr {
        // h : Eq Int (z0·Ep')(w0·Ep).
        let hty = self.eq_int_ty(
            self.mul(z0.clone(), ep2.clone()),
            self.mul(w0.clone(), ep.clone()),
        );
        let (h_id, h) = {
            let mut hb = EnvDeclBuilder::child_of(parent);
            hb.fresh_local(hty.clone())
        };
        // goal : Eq Rat zr0 wr0.
        let goal = Expr::apps(
            self.eq_ratq.clone(),
            [self.ratq.clone(), zr0.clone(), wr0.clone()],
        );
        let mul_lhs = self.mul(z0.clone(), ep2.clone());
        let mul_rhs = self.mul(w0.clone(), ep.clone());

        // Magnitude `Nat.succ k` of an `ofNat (succ k)` lift (for nonzero kinds).
        let mag =
            |o: Option<&Expr>| -> Expr { self.mag_nat(o.expect("invariant: nonzero magnitude")) };

        let body = match (okind, ikind) {
            // ── matching signs ──
            (0, 0) => {
                // both zero: zr0 = wr0 = Quot.mk raw_zero ; Eq.refl.
                Expr::apps(
                    Expr::const_(
                        Name::from_string("Eq.refl"),
                        vec![Level::succ(Level::zero())],
                    ),
                    [self.ratq.clone(), zr0.clone()],
                )
            }
            (1, 1) => {
                // Goal Equiv raw_l raw_r ≡ Eq Int (Ep·A')(Ep'·A), A=z0, A'=w0,
                // raw_l = raw_mk Ep (succ m), raw_r = raw_mk Ep' (succ m').
                let eqv = self.inv_pos_equiv(z0, w0, ep, ep2, &h);
                let raw_l = self.inv_raw_pos(ep, mk_o.expect("invariant: pos outer magnitude"));
                let raw_r = self.inv_raw_pos(ep2, mk_i.expect("invariant: pos inner magnitude"));
                self.quot_sound(raw_l, raw_r, eqv)
            }
            (2, 2) => {
                let mko = mk_o.expect("invariant: neg outer magnitude");
                let mki = mk_i.expect("invariant: neg inner magnitude");
                let eqv = self.inv_neg_equiv(parent, mko, mki, ep, ep2, &h);
                let raw_l = self.inv_raw_neg(ep, mko);
                let raw_r = self.inv_raw_neg(ep2, mki);
                self.quot_sound(raw_l, raw_r, eqv)
            }
            // ── zero (outer) vs nonzero (inner) ──
            (0, 1) => {
                // Transport h's LHS (ofNat 0)·Ep' → Int.zero (Int.zero_mul Ep').
                // Then noConfusion: ofNat 0 = ofNat (Nat.mul (succ m') dp); field
                // 0 = Nat.mul (succ m')(effDenom p) (succ-headed) → Nat.noConfusion.
                let hz = self.zero_side_to_int_zero(&mul_lhs, &mul_rhs, ep2, &h, true);
                let nat_a = self.nat_zero.clone();
                let nat_b = self.nmul(mag(mk_i), dp.clone());
                self.nat_field_refute(
                    parent,
                    &goal,
                    &self.int_zero.clone(),
                    &mul_rhs,
                    &nat_a,
                    &nat_b,
                    &hz,
                )
            }
            (1, 0) => {
                let hz = self.zero_side_to_int_zero(&mul_lhs, &mul_rhs, ep, &h, false);
                let nat_a = self.nmul(mag(mk_o), dp2.clone());
                let nat_b = self.nat_zero.clone();
                self.nat_field_refute(
                    parent,
                    &goal,
                    &mul_lhs,
                    &self.int_zero.clone(),
                    &nat_a,
                    &nat_b,
                    &hz,
                )
            }
            (0, 2) => {
                // ofNat 0 vs negSucc — transport LHS to Int.zero, Int.noConfusion.
                let hz = self.zero_side_to_int_zero(&mul_lhs, &mul_rhs, ep2, &h, true);
                self.int_no_conf_refute(goal.clone(), self.int_zero.clone(), mul_rhs.clone(), hz)
            }
            (2, 0) => {
                let hz = self.zero_side_to_int_zero(&mul_lhs, &mul_rhs, ep, &h, false);
                self.int_no_conf_refute(goal.clone(), mul_lhs.clone(), self.int_zero.clone(), hz)
            }
            // ── cross-constructor (ofNat(succ) vs negSucc) refuted directly ──
            _ => self.int_no_conf_refute(goal.clone(), mul_lhs.clone(), mul_rhs.clone(), h.clone()),
        };
        parent.mk_lam(h_id, BinderInfo::Default, hty, body)
    }

    /// Transport one side of `h : Eq Int A B` where the relevant side is
    /// `(ofNat 0)·E ≡ Int.zero·E` into `Int.zero` via `Int.zero_mul E`.
    /// `lhs_is_zero = true` rewrites the LHS (`A`), else the RHS (`B`).
    /// Returns the transported `h'` whose zero side is the literal `Int.zero`.
    fn zero_side_to_int_zero(
        &self,
        a: &Expr,
        bb: &Expr,
        e: &Expr,
        h: &Expr,
        lhs_is_zero: bool,
    ) -> Expr {
        // zm : Int.zero·E = Int.zero ≡ (ofNat 0)·E = Int.zero (defeq).
        let zm = self.zero_mul(e.clone());
        if lhs_is_zero {
            // h : A=B with A ≡ (ofNat 0)·E. zm : A = Int.zero. Want Int.zero = B.
            // trans (symm zm) h.
            let symm_zm = self.symm_int(a.clone(), self.int_zero.clone(), zm);
            self.trans_int(
                self.int_zero.clone(),
                a.clone(),
                bb.clone(),
                symm_zm,
                h.clone(),
            )
        } else {
            // h : A=B with B ≡ (ofNat 0)·E. zm : B = Int.zero. Want A = Int.zero.
            self.trans_int(a.clone(), bb.clone(), self.int_zero.clone(), h.clone(), zm)
        }
    }

    /// `raw_mk ep (succ k)` where `mag = ofNat (succ k)` — the positive inv rep.
    /// `mag ≡ ofNat (succ (pred mag_nat))`; we extract `succ (pred …)` as the
    /// Nat denominator, which is def-eq to the recursor's `succ k`.
    fn inv_raw_pos(&self, ep: &Expr, mag: &Expr) -> Expr {
        self.raw_mk(ep.clone(), self.mag_nat(mag))
    }

    /// `raw_mk (neg ep) (succ k)` — the negative inv rep.
    fn inv_raw_neg(&self, ep: &Expr, mag: &Expr) -> Expr {
        self.raw_mk(self.neg(ep.clone()), self.mag_nat(mag))
    }

    /// The `Nat` magnitude `succ (pred ·)` underlying a magnitude `ofNat (succ k)`.
    /// We hold the magnitude as the `ofNat (succ k)` Int; the raw denom is the
    /// `Nat` `succ k`. Since the recursor binds `k` we already have `succ k`
    /// directly — `mag_nat` strips the `ofNat`.
    fn mag_nat(&self, mag: &Expr) -> Expr {
        // mag = Int.ofNat n ; return n.
        match mag.kind() {
            ExprKind::App(f, n) => {
                let _ = f;
                (**n).clone()
            }
            _ => self.pred_of_mag(mag),
        }
    }

    /// `pred` of the underlying nat of a magnitude `ofNat (succ k)` — i.e. `k`.
    fn pred_of_mag(&self, mag: &Expr) -> Expr {
        // mag = Int.ofNat (Nat.succ k) ; return k.
        if let ExprKind::App(_, n) = mag.kind() {
            if let ExprKind::App(_, k) = n.kind() {
                return (**k).clone();
            }
        }
        Expr::app(
            self.nat_pred.clone(),
            Expr::app(self.raw_eff_denom.clone(), mag.clone()),
        )
    }

    /// The `Quot.ind` minor of `mul_inv_cancel` for a rep `p`: a term of type
    /// `ne_ty(mk p) → Eq Rat (mul (mk p)(inv (mk p))) one`. An inner
    /// `Int.rec`/`Nat.rec` on `num p` carrying the scrutinee equation
    /// `heq : num p = z`.
    fn mul_inv_minor(&self, parent: &EnvDeclBuilder, p: &Expr) -> Expr {
        let ratq_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let ratq_one = Expr::const_(Name::from_string("Rat.one"), vec![]);
        let ratq_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let false_c = Expr::const_(Name::from_string("False"), vec![]);
        let mk_p = self.quot_mk(p.clone());
        let np = self.num(p.clone());
        let ep = self.eff(p.clone());
        let dp = Expr::app(self.raw_eff_denom.clone(), p.clone());
        let nat_one = self.nsucc(self.nat_zero.clone());
        let zero01 = self.raw_mk(self.int_zero.clone(), nat_one.clone());
        let one_raw = self.raw_mk(self.of_nat(nat_one.clone()), nat_one.clone());

        // invMk(z) := Quot.mk (raw_inv_from z dp).
        let inv_mk = |parent: &EnvDeclBuilder, z: &Expr| -> Expr {
            self.quot_mk(self.raw_inv_from(parent, z, &dp))
        };
        // ne_ty := Eq Rat (mk p) zero → False.
        let ne_ty = |parent: &EnvDeclBuilder| -> Expr {
            let mut bb = EnvDeclBuilder::child_of(parent);
            let eq0 = Expr::apps(
                self.eq_ratq.clone(),
                [self.ratq.clone(), mk_p.clone(), ratq_zero.clone()],
            );
            let (h_id, _h) = bb.fresh_local(eq0.clone());
            bb.mk_pi(h_id, BinderInfo::Default, eq0, false_c.clone())
        };
        // goal(invRep) := Eq Rat (mul (mk p) invRep) one.
        let goal_with = |invrep: &Expr| -> Expr {
            let lhs = Expr::apps(ratq_mul.clone(), [mk_p.clone(), invrep.clone()]);
            Expr::apps(
                self.eq_ratq.clone(),
                [self.ratq.clone(), lhs, ratq_one.clone()],
            )
        };
        // heq_ty(z) := Eq Int (num p) z.
        let heq_ty = |z: &Expr| -> Expr { self.eq_int_ty(np.clone(), z.clone()) };

        // Inner motive M(z) := heq_ty(z) → ne_ty → goal(invMk z).
        let m_motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = mb.fresh_local(self.int.clone());
            let invrep = inv_mk(&mb, &z);
            let g = goal_with(&invrep);
            let ne = ne_ty(&mb);
            let heq = heq_ty(&z);
            let (he_id, _he) = mb.fresh_local(heq.clone());
            let (ne_id, _ne) = mb.fresh_local(ne.clone());
            let pi = mb.mk_pi(ne_id, BinderInfo::Default, ne, g);
            let pi = mb.mk_pi(he_id, BinderInfo::Default, heq, pi);
            let lam = mb.mk_lam(z_id, BinderInfo::Default, self.int.clone(), pi);
            mb.finish_child(lam)
        };

        // ── ofNat case: Nat.rec on nat_n → {zero, positive}. ──
        let of_case = {
            let mut ob = EnvDeclBuilder::child_of(parent);
            let (nn_id, nn) = ob.fresh_local(self.nat.clone());
            // NN(nat_n) := heq_ty(ofNat nat_n) → ne_ty → goal(invMk (ofNat nat_n)).
            let nn_motive = {
                let mut mb = EnvDeclBuilder::child_of(&ob);
                let (k_id, k) = mb.fresh_local(self.nat.clone());
                let z = self.of_nat(k.clone());
                let invrep = inv_mk(&mb, &z);
                let g = goal_with(&invrep);
                let ne = ne_ty(&mb);
                let heq = heq_ty(&z);
                let (he_id, _he) = mb.fresh_local(heq.clone());
                let (ne_id, _ne) = mb.fresh_local(ne.clone());
                let pi = mb.mk_pi(ne_id, BinderInfo::Default, ne, g);
                let pi = mb.mk_pi(he_id, BinderInfo::Default, heq, pi);
                let lam = mb.mk_lam(k_id, BinderInfo::Default, self.nat.clone(), pi);
                mb.finish_child(lam)
            };
            // zero leaf: z = ofNat 0 ; invMk = Quot.mk raw_zero = zero.
            let nn_zero = {
                let mut zb = EnvDeclBuilder::child_of(&ob);
                let z0 = self.of_nat(self.nat_zero.clone());
                let heq = heq_ty(&z0);
                let (he_id, he) = zb.fresh_local(heq.clone());
                let ne = ne_ty(&zb);
                let (ne_id, ne_l) = zb.fresh_local(ne.clone());
                // mkp_eq_zero : Eq Rat (mk p) zero.
                let eqv = self.mul_inv_zero_equiv(&zb, p, &he);
                let mkp_eq_zero = self.quot_sound(p.clone(), zero01.clone(), eqv);
                // hfalse := ne_l mkp_eq_zero : False.
                let hfalse = Expr::app(ne_l, mkp_eq_zero);
                // goal := goal_with(invMk (ofNat 0)) = Eq Rat (mul (mk p) zero) one.
                let invrep = inv_mk(&zb, &z0);
                let g = goal_with(&invrep);
                let elim = Expr::apps(self.false_elim.clone(), [g, hfalse]);
                let lam = zb.mk_lam(ne_id, BinderInfo::Default, ne, elim);
                let lam = zb.mk_lam(he_id, BinderInfo::Default, heq, lam);
                zb.finish_child(lam)
            };
            // positive leaf: z = ofNat(succ m) ; invMk = Quot.mk (raw_mk Ep (succ m)).
            let nn_succ = {
                let mut sb = EnvDeclBuilder::child_of(&ob);
                let (m_id, m) = sb.fresh_local(self.nat.clone());
                // ih binder (unused).
                let ih_ty = {
                    let z = self.of_nat(m.clone());
                    let invrep = inv_mk(&sb, &z);
                    let g = goal_with(&invrep);
                    let ne = ne_ty(&sb);
                    let heq = heq_ty(&z);
                    let mut tb = EnvDeclBuilder::child_of(&sb);
                    let (he_id, _he) = tb.fresh_local(heq.clone());
                    let (ne_id, _ne) = tb.fresh_local(ne.clone());
                    let pi = tb.mk_pi(ne_id, BinderInfo::Default, ne, g);
                    let pi = tb.mk_pi(he_id, BinderInfo::Default, heq, pi);
                    tb.finish_child(pi)
                };
                let (ih_id, _ih) = sb.fresh_local(ih_ty.clone());
                let z = self.of_nat(self.nsucc(m.clone()));
                let heq = heq_ty(&z);
                let (he_id, he) = sb.fresh_local(heq.clone());
                let ne = ne_ty(&sb);
                let (ne_id, _ne) = sb.fresh_local(ne.clone());
                // inv rep raw = raw_mk Ep (succ m).
                let inv_raw = self.raw_mk(ep.clone(), self.nsucc(m.clone()));
                let raw_l = self.raw_mul(p, &inv_raw);
                let eqv = self.mul_inv_pos_equiv(&sb, p, &m, &he);
                let sound = self.quot_sound(raw_l, one_raw.clone(), eqv);
                let lam = sb.mk_lam(ne_id, BinderInfo::Default, ne, sound);
                let lam = sb.mk_lam(he_id, BinderInfo::Default, heq, lam);
                let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, lam);
                let lam = sb.mk_lam(m_id, BinderInfo::Default, self.nat.clone(), lam);
                sb.finish_child(lam)
            };
            let rec = Expr::apps(
                self.nat_rec_prop.clone(),
                [nn_motive, nn_zero, nn_succ, nn.clone()],
            );
            let lam = ob.mk_lam(nn_id, BinderInfo::Default, self.nat.clone(), rec);
            ob.finish_child(lam)
        };

        // ── negSucc case: z = negSucc k ; invMk = Quot.mk (raw_mk (neg Ep)(succ k)). ──
        let neg_case = {
            let mut nb = EnvDeclBuilder::child_of(parent);
            let (k_id, k) = nb.fresh_local(self.nat.clone());
            let z = self.neg_succ(k.clone());
            let heq = heq_ty(&z);
            let (he_id, he) = nb.fresh_local(heq.clone());
            let ne = ne_ty(&nb);
            let (ne_id, _ne) = nb.fresh_local(ne.clone());
            let inv_raw = self.raw_mk(self.neg(ep.clone()), self.nsucc(k.clone()));
            let raw_l = self.raw_mul(p, &inv_raw);
            let eqv = self.mul_inv_neg_equiv(&nb, p, &k, &he);
            let sound = self.quot_sound(raw_l, one_raw.clone(), eqv);
            let lam = nb.mk_lam(ne_id, BinderInfo::Default, ne, sound);
            let lam = nb.mk_lam(he_id, BinderInfo::Default, heq, lam);
            let lam = nb.mk_lam(k_id, BinderInfo::Default, self.nat.clone(), lam);
            nb.finish_child(lam)
        };

        // @Int.rec.{0} M of_case neg_case (num p) (Eq.refl (num p)) : ne_ty → goal.
        let rec = Expr::apps(
            self.int_rec_prop.clone(),
            [m_motive, of_case, neg_case, np.clone()],
        );
        let refl_np = self.refl_int(np.clone());
        Expr::app(rec, refl_np)
    }

    /// Zero-leaf Equiv of `mul_inv_cancel`: from `he : num p = ofNat 0` build
    /// `Equiv p (raw_mk 0 1)` = `Eq Int (np·ofNat1) (0·Ep)`.
    fn mul_inv_zero_equiv(&self, _parent: &EnvDeclBuilder, p: &Expr, he: &Expr) -> Expr {
        let np = self.num(p.clone());
        let ep = self.eff(p.clone());
        let nat_one = self.nsucc(self.nat_zero.clone());
        let one_i = self.of_nat(nat_one.clone());
        // lhs = np·(ofNat 1) ; rhs = Int.zero·Ep.  (E(zero01) ≡ ofNat 1 defeq.)
        let lhs = self.mul(np.clone(), one_i.clone());
        let rhs = self.mul(self.int_zero.clone(), ep.clone());
        // np·1 = np [mul_one] = ofNat0 [he] = Int.zero [defeq] ; Int.zero = 0·Ep [symm zero_mul].
        let s1 = self.mul_one(np.clone()); // np·1 = np
        let ofnat0 = self.of_nat(self.nat_zero.clone());
        let s2 = he.clone(); // np = ofNat 0 ; ofNat 0 ≡ Int.zero (defeq)
        let s3 = self.symm_int(
            rhs.clone(),
            self.int_zero.clone(),
            self.zero_mul(ep.clone()),
        );
        // chain lhs = np = ofNat0(≡Int.zero) = rhs.
        let t1 = self.trans_int(lhs.clone(), np.clone(), ofnat0.clone(), s1, s2);
        // ofNat0 ≡ Int.zero ; trans into rhs.
        self.trans_int(lhs, ofnat0, rhs, t1, s3)
    }

    /// Positive-leaf Equiv: `he : num p = ofNat(succ m)` ; build
    /// `Equiv (raw_mul p (raw_mk Ep (succ m))) (raw_mk 1 1)` =
    /// `Eq Int ((np·Ep)·ofNat1) (ofNat1·(Ep·ofNat(succ m)))`.
    fn mul_inv_pos_equiv(&self, parent: &EnvDeclBuilder, p: &Expr, m: &Expr, he: &Expr) -> Expr {
        let np = self.num(p.clone());
        let ep = self.eff(p.clone());
        let one_i = self.of_nat(self.nsucc(self.nat_zero.clone()));
        let a = self.of_nat(self.nsucc(m.clone())); // ofNat(succ m)
        let np_ep = self.mul(np.clone(), ep.clone());
        let lhs = self.mul(np_ep.clone(), one_i.clone()); // (np·Ep)·1
        let ep_a = self.mul(ep.clone(), a.clone()); // Ep·ofNat(succ m)
        let rhs = self.mul(one_i.clone(), ep_a.clone()); // 1·(Ep·ofNat(succ m))
                                                         // lhs = np·Ep [mul_one] = (ofNat(succ m))·Ep [congr (·*Ep) he] = a·Ep.
        let s1 = self.mul_one(np_ep.clone()); // (np·Ep)·1 = np·Ep
        let a_ep = self.mul(a.clone(), ep.clone());
        let s2 = self.congr_arg(
            np.clone(),
            a.clone(),
            self.mul_right_fn(parent, ep.clone()),
            he.clone(),
        );
        // a·Ep = Ep·a [mul_comm] ; rhs = 1·(Ep·a) = (Ep·a) [need]; (Ep·a) ≡ rhs? rhs = 1·(Ep·a).
        // chain to ep_a then to rhs via symm(one_mul-as-comm+mul_one).
        let s3 = self.mul_comm(a.clone(), ep.clone()); // a·Ep = Ep·a
                                                       // rhs = 1·(Ep·a) ; 1·(Ep·a) = (Ep·a)·1 [mul_comm] = (Ep·a) [mul_one]. So (Ep·a) = rhs via symm.
        let epa_1 = self.mul(ep_a.clone(), one_i.clone());
        let r1 = self.mul_comm(one_i.clone(), ep_a.clone()); // 1·(Ep·a) = (Ep·a)·1
        let r2 = self.mul_one(ep_a.clone()); // (Ep·a)·1 = Ep·a
        let rhs_to_epa = self.trans_int(rhs.clone(), epa_1.clone(), ep_a.clone(), r1, r2);
        let epa_to_rhs = self.symm_int(rhs.clone(), ep_a.clone(), rhs_to_epa);
        // chain: lhs = np·Ep = a·Ep = Ep·a = rhs.
        let c1 = self.trans_int(lhs.clone(), np_ep.clone(), a_ep.clone(), s1, s2);
        let c2 = self.trans_int(lhs.clone(), a_ep.clone(), ep_a.clone(), c1, s3);
        self.trans_int(lhs, ep_a, rhs, c2, epa_to_rhs)
    }

    /// Negative-leaf Equiv: `he : num p = negSucc k` ; build
    /// `Equiv (raw_mul p (raw_mk (neg Ep)(succ k))) (raw_mk 1 1)` =
    /// `Eq Int ((np·(neg Ep))·ofNat1) (ofNat1·(Ep·ofNat(succ k)))`.
    /// Uses `negSucc k ≡ neg(ofNat(succ k))` and
    /// `(neg M)·(neg Ep) = M·Ep` (`neg_mul_left`+`neg_mul_right`+`neg_neg`).
    fn mul_inv_neg_equiv(&self, parent: &EnvDeclBuilder, p: &Expr, k: &Expr, he: &Expr) -> Expr {
        let np = self.num(p.clone());
        let ep = self.eff(p.clone());
        let one_i = self.of_nat(self.nsucc(self.nat_zero.clone()));
        let mm = self.of_nat(self.nsucc(k.clone())); // M = ofNat(succ k) ; negSucc k ≡ neg M
        let neg_ep = self.neg(ep.clone());
        let np_negep = self.mul(np.clone(), neg_ep.clone());
        let lhs = self.mul(np_negep.clone(), one_i.clone()); // (np·(neg Ep))·1
        let ep_m = self.mul(ep.clone(), mm.clone()); // Ep·M
        let rhs = self.mul(one_i.clone(), ep_m.clone()); // 1·(Ep·M)

        // lhs = np·(neg Ep) [mul_one] = (neg M)·(neg Ep) [congr (·*(neg Ep)) he].
        let s1 = self.mul_one(np_negep.clone());
        let neg_m = self.neg(mm.clone());
        let negm_negep = self.mul(neg_m.clone(), neg_ep.clone());
        let s2 = self.congr_arg(
            np.clone(),
            neg_m.clone(),
            self.mul_right_fn(parent, neg_ep.clone()),
            he.clone(),
        );
        // (neg M)·(neg Ep) = neg(M·(neg Ep)) [neg_mul_left M (neg Ep)]
        let m_negep = self.mul(mm.clone(), neg_ep.clone());
        let neg_m_negep = self.neg(m_negep.clone());
        let s3 = self.neg_mul_left(mm.clone(), neg_ep.clone());
        // neg(M·(neg Ep)) = neg(neg(M·Ep)) [congr neg (neg_mul_right M Ep)]
        let m_ep = self.mul(mm.clone(), ep.clone());
        let neg_m_ep = self.neg(m_ep.clone());
        let neg_neg_m_ep = self.neg(neg_m_ep.clone());
        let s4 = self.congr_arg(
            m_negep.clone(),
            neg_m_ep.clone(),
            self.neg_fn(parent),
            self.neg_mul_right(mm.clone(), ep.clone()),
        );
        // neg(neg(M·Ep)) = M·Ep [neg_neg (M·Ep)]
        let s5 = self.neg_neg(m_ep.clone());
        // M·Ep = Ep·M [mul_comm]
        let s6 = self.mul_comm(mm.clone(), ep.clone());
        // Ep·M = rhs (= 1·(Ep·M)) via symm(comm+mul_one).
        let epm_1 = self.mul(ep_m.clone(), one_i.clone());
        let r1 = self.mul_comm(one_i.clone(), ep_m.clone());
        let r2 = self.mul_one(ep_m.clone());
        let rhs_to_epm = self.trans_int(rhs.clone(), epm_1.clone(), ep_m.clone(), r1, r2);
        let epm_to_rhs = self.symm_int(rhs.clone(), ep_m.clone(), rhs_to_epm);

        // chain: lhs = np·(neg Ep) = (neg M)·(neg Ep) = neg(M·(neg Ep))
        //        = neg(neg(M·Ep)) = M·Ep = Ep·M = rhs.
        let c1 = self.trans_int(lhs.clone(), np_negep.clone(), negm_negep.clone(), s1, s2);
        let c2 = self.trans_int(lhs.clone(), negm_negep.clone(), neg_m_negep.clone(), c1, s3);
        let c3 = self.trans_int(
            lhs.clone(),
            neg_m_negep.clone(),
            neg_neg_m_ep.clone(),
            c2,
            s4,
        );
        let c4 = self.trans_int(lhs.clone(), neg_neg_m_ep.clone(), m_ep.clone(), c3, s5);
        let c5 = self.trans_int(lhs.clone(), m_ep.clone(), ep_m.clone(), c4, s6);
        self.trans_int(lhs, ep_m, rhs, c5, epm_to_rhs)
    }

    /// Matching POSITIVE/POSITIVE leaf Equiv for the `inv` respect proof.
    /// `a := ofNat(succ m) = np`, `a2 := ofNat(succ m')`, `ep/ep2` the effDenom
    /// factors. From `h : a·ep2 = a2·ep` derive `ep·a2 = ep2·a` (the Equiv of
    /// the two `raw_mk ep (succ ·)` inverses), via `mul_comm` + `h`.
    fn inv_pos_equiv(&self, a: &Expr, a2: &Expr, ep: &Expr, ep2: &Expr, h: &Expr) -> Expr {
        // ep·a2 = a2·ep [comm] = a·ep2 [symm h] = ep2·a [comm].
        let ep_a2 = self.mul(ep.clone(), a2.clone());
        let a2_ep = self.mul(a2.clone(), ep.clone());
        let a_ep2 = self.mul(a.clone(), ep2.clone());
        let ep2_a = self.mul(ep2.clone(), a.clone());
        // s1 : ep·a2 = a2·ep   [mul_comm ep a2]
        let s1 = self.mul_comm(ep.clone(), a2.clone());
        // s2 : a2·ep = a·ep2   [symm h]  (h : a·ep2 = a2·ep)
        let s2 = self.symm_int(a_ep2.clone(), a2_ep.clone(), h.clone());
        // s3 : a·ep2 = ep2·a   [mul_comm a ep2]
        let s3 = self.mul_comm(a.clone(), ep2.clone());
        let t1 = self.trans_int(ep_a2.clone(), a2_ep.clone(), a_ep2.clone(), s1, s2);
        self.trans_int(ep_a2, a_ep2, ep2_a, t1, s3)
    }

    /// Matching NEGATIVE/NEGATIVE leaf Equiv for the `inv` respect proof.
    /// Magnitudes `mk := ofNat(succ k)` (so `negSucc k ≡ neg mk`), `mk2`, and
    /// effDenoms `ep/ep2`. The kernel's `Equiv raw_l raw_r`
    /// (raw_l = raw_mk (neg ep)(succ k), raw_r = raw_mk (neg ep2)(succ k')) is
    /// `num·eff` order, i.e. `Eq Int ((neg ep)·mk2) ((neg ep2)·mk)`. From
    /// `h : (neg mk)·ep2 = (neg mk2)·ep` (def-eq to `(negSucc k)·Ep' =
    /// (negSucc k')·Ep`) chain through `Int.neg_mul_left` + `mul_comm`.
    fn inv_neg_equiv(
        &self,
        parent: &EnvDeclBuilder,
        mk: &Expr,
        mk2: &Expr,
        ep: &Expr,
        ep2: &Expr,
        h: &Expr,
    ) -> Expr {
        // Target: (neg ep)·mk2 = (neg ep2)·mk.
        let neg_ep = self.neg(ep.clone());
        let neg_ep2 = self.neg(ep2.clone());
        let lhs = self.mul(neg_ep.clone(), mk2.clone()); // (neg ep)·mk2
        let rhs = self.mul(neg_ep2.clone(), mk.clone()); // (neg ep2)·mk
                                                         // Intermediate products.
        let ep_mk2 = self.mul(ep.clone(), mk2.clone());
        let mk2_ep = self.mul(mk2.clone(), ep.clone());
        let ep2_mk = self.mul(ep2.clone(), mk.clone());
        let mk_ep2 = self.mul(mk.clone(), ep2.clone());
        let neg_ep_mk2 = self.neg(ep_mk2.clone());
        let neg_mk2_ep = self.neg(mk2_ep.clone());
        let neg_ep2_mk = self.neg(ep2_mk.clone());
        let neg_mk_ep2 = self.neg(mk_ep2.clone());
        let neg_mk = self.neg(mk.clone());
        let neg_mk2 = self.neg(mk2.clone());
        let negmk_ep2 = self.mul(neg_mk.clone(), ep2.clone());
        let negmk2_ep = self.mul(neg_mk2.clone(), ep.clone());

        // s1 : (neg ep)·mk2 = neg(ep·mk2)   [neg_mul_left ep mk2]
        let s1 = self.neg_mul_left(ep.clone(), mk2.clone());
        // s2 : neg(ep·mk2) = neg(mk2·ep)    [congrArg neg (mul_comm ep mk2)]
        let s2 = self.congr_arg(
            ep_mk2.clone(),
            mk2_ep.clone(),
            self.neg_fn(parent),
            self.mul_comm(ep.clone(), mk2.clone()),
        );
        // s3 : neg(mk2·ep) = (neg mk2)·ep   [symm neg_mul_left mk2 ep]
        let s3 = self.symm_int(
            neg_mk2_ep.clone(),
            negmk2_ep.clone(),
            self.neg_mul_left(mk2.clone(), ep.clone()),
        );
        // s4 : (neg mk2)·ep = (neg mk)·ep2  [symm h]   (h : (neg mk)·ep2 = (neg mk2)·ep)
        let s4 = self.symm_int(negmk_ep2.clone(), negmk2_ep.clone(), h.clone());
        // s5 : (neg mk)·ep2 = neg(mk·ep2)   [neg_mul_left mk ep2]
        let s5 = self.neg_mul_left(mk.clone(), ep2.clone());
        // s6 : neg(mk·ep2) = neg(ep2·mk)    [congrArg neg (mul_comm mk ep2)]
        let s6 = self.congr_arg(
            mk_ep2.clone(),
            ep2_mk.clone(),
            self.neg_fn(parent),
            self.mul_comm(mk.clone(), ep2.clone()),
        );
        // s7 : neg(ep2·mk) = (neg ep2)·mk   [symm neg_mul_left ep2 mk]
        let s7 = self.symm_int(
            neg_ep2_mk.clone(),
            rhs.clone(),
            self.neg_mul_left(ep2.clone(), mk.clone()),
        );

        // chain lhs → neg(ep·mk2) → neg(mk2·ep) → (neg mk2)·ep → (neg mk)·ep2
        //       → neg(mk·ep2) → neg(ep2·mk) → rhs.
        let c1 = self.trans_int(lhs.clone(), neg_ep_mk2.clone(), neg_mk2_ep.clone(), s1, s2);
        let c2 = self.trans_int(lhs.clone(), neg_mk2_ep.clone(), negmk2_ep.clone(), c1, s3);
        let c3 = self.trans_int(lhs.clone(), negmk2_ep.clone(), negmk_ep2.clone(), c2, s4);
        let c4 = self.trans_int(lhs.clone(), negmk_ep2.clone(), neg_mk_ep2.clone(), c3, s5);
        let c5 = self.trans_int(lhs.clone(), neg_mk_ep2.clone(), neg_ep2_mk.clone(), c4, s6);
        self.trans_int(lhs, neg_ep2_mk, rhs, c5, s7)
    }

    // ── Generic Int product normalizer (for the distributive payoff axioms) ──
    //
    // The `Rat.left_distrib` / `Rat.right_distrib` Equiv obligations reduce to
    // degree-≥6 commutative-ring monomial equalities. Rather than hand-shuffle
    // each, we normalize any binary `Int.mul`-tree of atoms to a canonical
    // RIGHT-FOLDED product, then close a permutation between two such folds by
    // adjacent transpositions. Everything is built from `Int.mul_assoc` /
    // `Int.mul_comm` / `congrArg` / `Eq.trans`, so it stays `Constructive`.

    /// `rfold([a0, a1, …, a_{n-1}]) = a0 · (a1 · (… · a_{n-1}))` (right-folded
    /// product; a singleton list folds to its sole element). Panics on empty.
    fn rfold(&self, atoms: &[Expr]) -> Expr {
        let (last, init) = atoms
            .split_last()
            .expect("invariant: rfold requires a non-empty atom list");
        let mut acc = last.clone();
        for a in init.iter().rev() {
            acc = self.mul(a.clone(), acc);
        }
        acc
    }

    /// `tree_eq_rfold(parent, tree, atoms)` : a proof of
    /// `Eq Int <tree> (rfold atoms)`, where `tree` is a binary `Int.mul`-tree
    /// whose left-to-right leaf sequence is `atoms`. Built recursively: a leaf
    /// is `Eq.refl`; an internal node `l·r` is normalized by normalizing `l`
    /// and `r`, re-associating `rfold(l_atoms) · rfold(r_atoms)` into
    /// `rfold(l_atoms ++ r_atoms)`.
    ///
    /// `tree_atoms` describes the shape: `None` ⇒ `tree` is an atom (leaf);
    /// `Some((l_atoms, r_atoms))` ⇒ `tree ≡ mul (rebuild l)(rebuild r)`.
    fn prod_norm(&self, parent: &EnvDeclBuilder, tree: &ProdTree) -> Expr {
        match tree {
            ProdTree::Atom(a) => self.refl_int(a.clone()),
            ProdTree::Mul(l, r) => {
                let l_expr = l.to_expr(self);
                let r_expr = r.to_expr(self);
                let l_atoms = l.atoms();
                let r_atoms = r.atoms();
                let l_fold = self.rfold(&l_atoms);
                let r_fold = self.rfold(&r_atoms);
                // hl : l_expr = l_fold ; hr : r_expr = r_fold.
                let hl = self.prod_norm(parent, l);
                let hr = self.prod_norm(parent, r);
                // step1 : (l_expr · r_expr) = (l_fold · r_fold)  [congr hl, hr]
                let lhs = self.mul(l_expr.clone(), r_expr.clone());
                let mid = self.mul(l_fold.clone(), r_fold.clone());
                let cong1 = self.congr_arg(
                    l_expr.clone(),
                    l_fold.clone(),
                    self.mul_right_fn(parent, r_expr.clone()),
                    hl,
                );
                let cong2 = self.congr_arg(
                    r_expr.clone(),
                    r_fold.clone(),
                    self.mul_left_fn(parent, l_fold.clone()),
                    hr,
                );
                let step1 = self.trans_int(
                    lhs.clone(),
                    self.mul(l_fold.clone(), r_expr.clone()),
                    mid.clone(),
                    cong1,
                    cong2,
                );
                // step2 : (l_fold · r_fold) = rfold(l_atoms ++ r_atoms).
                let step2 = self.rfold_append(parent, &l_atoms, &r_atoms);
                let mut all = l_atoms.clone();
                all.extend(r_atoms.iter().cloned());
                let rhs = self.rfold(&all);
                self.trans_int(lhs, mid, rhs, step1, step2)
            }
        }
    }

    /// `rfold_append(parent, ls, rs)` : `Eq Int (rfold ls · rfold rs)
    /// (rfold (ls ++ rs))`. Proven by induction on `ls` with `mul_assoc`.
    fn rfold_append(&self, parent: &EnvDeclBuilder, ls: &[Expr], rs: &[Expr]) -> Expr {
        // Base: |ls| = 1 ⇒ rfold ls = ls[0], and rfold(ls++rs) = ls[0]·rfold(rs),
        // which is DEFINITIONALLY `rfold ls · rfold rs`. Close by refl.
        if ls.len() == 1 {
            let lhs = self.mul(ls[0].clone(), self.rfold(rs));
            return self.refl_int(lhs);
        }
        // ls = a :: tl.  rfold ls = a · rfold tl.
        let a = ls[0].clone();
        let tl = &ls[1..];
        let rfold_tl = self.rfold(tl);
        let rfold_rs = self.rfold(rs);
        // LHS = (a · rfold tl) · rfold rs.
        let lhs = self.mul(self.mul(a.clone(), rfold_tl.clone()), rfold_rs.clone());
        // s1 : (a · rfold tl) · rfold rs = a · (rfold tl · rfold rs)  [mul_assoc]
        let mid = self.mul(a.clone(), self.mul(rfold_tl.clone(), rfold_rs.clone()));
        let s1 = self.mul_assoc(a.clone(), rfold_tl.clone(), rfold_rs.clone());
        // s2 : a · (rfold tl · rfold rs) = a · rfold(tl ++ rs)  [congr ih]
        let ih = self.rfold_append(parent, tl, rs);
        let mut tl_rs = tl.to_vec();
        tl_rs.extend(rs.iter().cloned());
        let rfold_tlrs = self.rfold(&tl_rs);
        let rhs = self.mul(a.clone(), rfold_tlrs.clone());
        let s2 = self.congr_arg(
            self.mul(rfold_tl.clone(), rfold_rs.clone()),
            rfold_tlrs.clone(),
            self.mul_left_fn(parent, a.clone()),
            ih,
        );
        self.trans_int(lhs, mid, rhs, s1, s2)
    }

    /// `swap_head(parent, a, b, rest)` : `Eq Int (a · (b · R)) (b · (a · R))`
    /// where `R := rfold(rest)` (or, if `rest` is empty, the two-element fold
    /// `a · b = b · a`). The adjacent-transposition primitive.
    fn swap_head(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr, rest: &[Expr]) -> Expr {
        if rest.is_empty() {
            // a · b = b · a.
            return self.mul_comm(a.clone(), b.clone());
        }
        let r = self.rfold(rest);
        // a · (b · R) = (a · b) · R   [symm mul_assoc a b R]
        let lhs = self.mul(a.clone(), self.mul(b.clone(), r.clone()));
        let ab_r = self.mul(self.mul(a.clone(), b.clone()), r.clone());
        let s1 = self.symm_int(
            ab_r.clone(),
            lhs.clone(),
            self.mul_assoc(a.clone(), b.clone(), r.clone()),
        );
        // (a · b) · R = (b · a) · R   [congrArg (·*R)(mul_comm a b)]
        let ba_r = self.mul(self.mul(b.clone(), a.clone()), r.clone());
        let s2 = self.congr_arg(
            self.mul(a.clone(), b.clone()),
            self.mul(b.clone(), a.clone()),
            self.mul_right_fn(parent, r.clone()),
            self.mul_comm(a.clone(), b.clone()),
        );
        // (b · a) · R = b · (a · R)   [mul_assoc b a R]
        let rhs = self.mul(b.clone(), self.mul(a.clone(), r.clone()));
        let s3 = self.mul_assoc(b.clone(), a.clone(), r.clone());
        let t1 = self.trans_int(lhs.clone(), ab_r, ba_r.clone(), s1, s2);
        self.trans_int(lhs, ba_r, rhs, t1, s3)
    }

    /// `pull_front(parent, atoms, k)` : `Eq Int (rfold atoms)
    /// (rfold (atoms[k] :: remove(atoms, k)))` — bubble the `k`-th atom to the
    /// front via `k` adjacent transpositions.
    fn pull_front(&self, parent: &EnvDeclBuilder, atoms: &[Expr], k: usize) -> Expr {
        debug_assert!(k < atoms.len());
        if k == 0 {
            return self.refl_int(self.rfold(atoms));
        }
        // First recurse to pull index k to position 1 within the tail starting
        // at index 0? Simpler: bubble down from k to 0 with successive swaps.
        // Build the chain: at step i (from k down to 1) swap positions i-1, i.
        // We represent the running atom vector and accumulate the proof.
        let mut cur: Vec<Expr> = atoms.to_vec();
        let target = cur[k].clone();
        // proof : rfold(atoms) = rfold(cur) — starts as refl.
        let mut proof = self.refl_int(self.rfold(&cur));
        let start = self.rfold(atoms);
        let mut i = k;
        while i >= 1 {
            // Swap positions i-1 and i in cur. The prefix cur[0..i-1] is shared;
            // the swap acts at depth (i-1) of the right fold.
            let prefix = &cur[..i - 1];
            let a = cur[i - 1].clone();
            let b = cur[i].clone();
            let rest = &cur[i + 1..];
            // swap proof for the sub-fold a·(b·R) = b·(a·R).
            let swap = self.swap_head(parent, &a, &b, rest);
            // Lift the swap through the shared prefix via nested congrArg
            // (fun w => p0·(p1·(…·w))).
            let lifted = self.lift_through_prefix(parent, prefix, &a, &b, rest, &swap);
            // new cur after swap.
            let mut next = cur.clone();
            next.swap(i - 1, i);
            // chain proof ; lifted : rfold(atoms) = rfold(next).
            let from = self.rfold(&cur);
            let to = self.rfold(&next);
            proof = self.trans_int(start.clone(), from, to, proof, lifted);
            cur = next;
            i -= 1;
        }
        let _ = target;
        proof
    }

    /// Lift an equality `sub_lhs = sub_rhs` (acting at the head of the
    /// right-fold of `[a, b] ++ rest`) through a shared `prefix`, producing a
    /// proof between the full folds `rfold(prefix ++ [a,b] ++ rest)` and
    /// `rfold(prefix ++ [b,a] ++ rest)` via nested `congrArg`.
    fn lift_through_prefix(
        &self,
        parent: &EnvDeclBuilder,
        prefix: &[Expr],
        a: &Expr,
        b: &Expr,
        rest: &[Expr],
        swap: &Expr,
    ) -> Expr {
        // sub_lhs = a·(b·R), sub_rhs = b·(a·R).
        let r = if rest.is_empty() {
            None
        } else {
            Some(self.rfold(rest))
        };
        let sub_lhs = match &r {
            Some(rr) => self.mul(a.clone(), self.mul(b.clone(), rr.clone())),
            None => self.mul(a.clone(), b.clone()),
        };
        let sub_rhs = match &r {
            Some(rr) => self.mul(b.clone(), self.mul(a.clone(), rr.clone())),
            None => self.mul(b.clone(), a.clone()),
        };
        // Wrap from the innermost prefix element outward.
        let mut cur_lhs = sub_lhs;
        let mut cur_rhs = sub_rhs;
        let mut acc = swap.clone();
        for p in prefix.iter().rev() {
            let new_lhs = self.mul(p.clone(), cur_lhs.clone());
            let new_rhs = self.mul(p.clone(), cur_rhs.clone());
            acc = self.congr_arg(
                cur_lhs.clone(),
                cur_rhs.clone(),
                self.mul_left_fn(parent, p.clone()),
                acc,
            );
            cur_lhs = new_lhs;
            cur_rhs = new_rhs;
        }
        acc
    }

    /// `rfold_perm(parent, src, dst)` : `Eq Int (rfold src) (rfold dst)` for two
    /// atom lists that are permutations of each other (atoms compared by
    /// `Expr` structural equality). Selection-sort style: pull `src[0]` to the
    /// front of `dst`, then recurse on the tails.
    fn rfold_perm(&self, parent: &EnvDeclBuilder, src: &[Expr], dst: &[Expr]) -> Expr {
        debug_assert_eq!(src.len(), dst.len());
        if src.len() == 1 {
            return self.refl_int(self.rfold(src));
        }
        let head = &src[0];
        // Find head in dst.
        let k = dst
            .iter()
            .position(|e| e == head)
            .expect("invariant: rfold_perm: dst must be a permutation of src");
        // pf1 : rfold(dst) = rfold(head :: dst_without_k).
        let pull = self.pull_front(parent, dst, k);
        let mut dst_front: Vec<Expr> = Vec::with_capacity(dst.len());
        dst_front.push(dst[k].clone());
        for (i, e) in dst.iter().enumerate() {
            if i != k {
                dst_front.push(e.clone());
            }
        }
        // Recurse on the tails: rfold(src[1..]) = rfold(dst_front[1..]).
        let tail_perm = self.rfold_perm(parent, &src[1..], &dst_front[1..]);
        // rfold(head :: src_tail) = head · rfold(src_tail).
        let src_fold = self.rfold(src);
        let head_dst_fold = self.rfold(&dst_front);
        let dst_fold = self.rfold(dst);
        // congr: head · rfold(src_tail) = head · rfold(dst_tail)  [congrArg (head·) tail_perm]
        let src_tail_fold = self.rfold(&src[1..]);
        let dst_tail_fold = self.rfold(&dst_front[1..]);
        let cong = self.congr_arg(
            src_tail_fold,
            dst_tail_fold,
            self.mul_left_fn(parent, head.clone()),
            tail_perm,
        );
        // src_fold ≡ head · rfold(src_tail) (defeq), head_dst_fold ≡ head · rfold(dst_tail).
        // chain: src_fold =[cong] head_dst_fold =[symm pull] dst_fold.
        let pull_sym = self.symm_int(dst_fold.clone(), head_dst_fold.clone(), pull);
        self.trans_int(src_fold, head_dst_fold, dst_fold, cong, pull_sym)
    }

    /// `Raw.mul p q := Raw.mk (num p · num q) (effDenom p · effDenom q)`.
    fn raw_mul(&self, p: &Expr, q: &Expr) -> Expr {
        let new_num = self.mul(self.num(p.clone()), self.num(q.clone()));
        let new_den = self.nmul(
            Expr::app(self.raw_eff_denom.clone(), p.clone()),
            Expr::app(self.raw_eff_denom.clone(), q.clone()),
        );
        self.raw_mk(new_num, new_den)
    }

    /// `Raw.add p q := Raw.mk (num p · E q + num q · E p) (effDenom p · effDenom q)`.
    fn raw_add(&self, p: &Expr, q: &Expr) -> Expr {
        let np_eq = self.mul(self.num(p.clone()), self.eff(q.clone()));
        let nq_ep = self.mul(self.num(q.clone()), self.eff(p.clone()));
        let new_num = self.add(np_eq, nq_ep);
        let new_den = self.nmul(
            Expr::app(self.raw_eff_denom.clone(), p.clone()),
            Expr::app(self.raw_eff_denom.clone(), q.clone()),
        );
        self.raw_mk(new_num, new_den)
    }

    /// Build the distributive cross-multiplication `Equiv`, for `left_distrib`
    /// (`left = true`) or `right_distrib` (`left = false`). Returns a proof of
    /// `Eq Int (num X · eff Y) (num Y · eff X)`, which is DEFINITIONALLY
    /// `Equiv X Y` for the relevant raw products.
    #[allow(clippy::too_many_arguments)]
    fn distrib_cross(
        &self,
        parent: &EnvDeclBuilder,
        np: &Expr,
        nq: &Expr,
        nr: &Expr,
        ep: &Expr,
        eq: &Expr,
        er: &Expr,
        left: bool,
    ) -> Expr {
        // Atom shorthands as ProdTrees.
        let at = ProdTree::atom;
        // ── Assemble num_X, eff_X, num_Y, eff_Y as Int expressions, plus the
        //    two-monomial splits and their ProdTree forms. ──
        if left {
            // X = mul p (add q r) ; Y = add (mul p q)(mul p r).
            // num_X = np·(nq·Er + nr·Eq) ; eff_X = Ep·(Eq·Er).
            let nq_er = self.mul(nq.clone(), er.clone());
            let nr_eq = self.mul(nr.clone(), eq.clone());
            let num_x = self.mul(np.clone(), self.add(nq_er.clone(), nr_eq.clone()));
            let eff_x = self.mul(ep.clone(), self.mul(eq.clone(), er.clone()));
            // num_Y = (np·nq)·(Ep·Er) + (np·nr)·(Ep·Eq) ; eff_Y = (Ep·Eq)·(Ep·Er).
            let np_nq = self.mul(np.clone(), nq.clone());
            let np_nr = self.mul(np.clone(), nr.clone());
            let ep_er = self.mul(ep.clone(), er.clone());
            let ep_eq = self.mul(ep.clone(), eq.clone());
            let ymono1 = self.mul(np_nq.clone(), ep_er.clone());
            let ymono2 = self.mul(np_nr.clone(), ep_eq.clone());
            let num_y = self.add(ymono1.clone(), ymono2.clone());
            let eff_y = self.mul(ep_eq.clone(), ep_er.clone());

            // LHS = num_X · eff_Y. Distribute num_X first (left_distrib), then
            // the whole thing (right_distrib).
            let lhs = self.mul(num_x.clone(), eff_y.clone());
            // d_num : num_X = np·(nq·Er) + np·(nr·Eq).
            let np_nqer = self.mul(np.clone(), nq_er.clone());
            let np_nreq = self.mul(np.clone(), nr_eq.clone());
            let num_x_split = self.add(np_nqer.clone(), np_nreq.clone());
            let d_num = self.left_distrib(np.clone(), nq_er.clone(), nr_eq.clone());
            // lift d_num under (·*eff_Y): lhs = num_x_split · eff_Y.
            let lhs_split = self.mul(num_x_split.clone(), eff_y.clone());
            let c_num = self.congr_arg(
                num_x.clone(),
                num_x_split.clone(),
                self.mul_right_fn(parent, eff_y.clone()),
                d_num,
            );
            // d_lhs : num_x_split · eff_Y = LA + LB.
            let la = self.mul(np_nqer.clone(), eff_y.clone());
            let lb = self.mul(np_nreq.clone(), eff_y.clone());
            let la_lb = self.add(la.clone(), lb.clone());
            let d_lhs = self.right_distrib(np_nqer.clone(), np_nreq.clone(), eff_y.clone());
            // lhs = LA + LB.
            let lhs_to_lalb =
                self.trans_int(lhs.clone(), lhs_split.clone(), la_lb.clone(), c_num, d_lhs);

            // RHS = num_Y · eff_X. Distribute (right_distrib) into RA + RB.
            let rhs = self.mul(num_y.clone(), eff_x.clone());
            let ra = self.mul(ymono1.clone(), eff_x.clone());
            let rb = self.mul(ymono2.clone(), eff_x.clone());
            let ra_rb = self.add(ra.clone(), rb.clone());
            let d_rhs = self.right_distrib(ymono1.clone(), ymono2.clone(), eff_x.clone());

            // LA = RA, LB = RB via prod_eq on the ProdTrees.
            //   LA := (np·(nq·Er))·((Ep·Eq)·(Ep·Er))
            //   RA := ((np·nq)·(Ep·Er))·(Ep·(Eq·Er))
            let t_la = ProdTree::mul(
                ProdTree::mul(
                    at(np.clone()),
                    ProdTree::mul(at(nq.clone()), at(er.clone())),
                ),
                ProdTree::mul(
                    ProdTree::mul(at(ep.clone()), at(eq.clone())),
                    ProdTree::mul(at(ep.clone()), at(er.clone())),
                ),
            );
            let t_ra = ProdTree::mul(
                ProdTree::mul(
                    ProdTree::mul(at(np.clone()), at(nq.clone())),
                    ProdTree::mul(at(ep.clone()), at(er.clone())),
                ),
                ProdTree::mul(
                    at(ep.clone()),
                    ProdTree::mul(at(eq.clone()), at(er.clone())),
                ),
            );
            let la_eq_ra = self.prod_eq(parent, &t_la, &t_ra);
            //   LB := (np·(nr·Eq))·((Ep·Eq)·(Ep·Er))
            //   RB := ((np·nr)·(Ep·Eq))·(Ep·(Eq·Er))
            let t_lb = ProdTree::mul(
                ProdTree::mul(
                    at(np.clone()),
                    ProdTree::mul(at(nr.clone()), at(eq.clone())),
                ),
                ProdTree::mul(
                    ProdTree::mul(at(ep.clone()), at(eq.clone())),
                    ProdTree::mul(at(ep.clone()), at(er.clone())),
                ),
            );
            let t_rb = ProdTree::mul(
                ProdTree::mul(
                    ProdTree::mul(at(np.clone()), at(nr.clone())),
                    ProdTree::mul(at(ep.clone()), at(eq.clone())),
                ),
                ProdTree::mul(
                    at(ep.clone()),
                    ProdTree::mul(at(eq.clone()), at(er.clone())),
                ),
            );
            let lb_eq_rb = self.prod_eq(parent, &t_lb, &t_rb);

            // LA + LB = RA + RB.
            let mid = self.add_cong(parent, &la, &ra, &lb, &rb, &la_eq_ra, &lb_eq_rb);
            // chain: lhs = LA+LB = RA+RB = rhs.
            let d_rhs_sym = self.symm_int(rhs.clone(), ra_rb.clone(), d_rhs);
            let t1 = self.trans_int(lhs.clone(), la_lb.clone(), ra_rb.clone(), lhs_to_lalb, mid);
            self.trans_int(lhs, ra_rb, rhs, t1, d_rhs_sym)
        } else {
            // X = mul (add p q) r ; Y = add (mul p r)(mul q r).
            // num_X = (np·Eq + nq·Ep)·nr ; eff_X = (Ep·Eq)·Er.
            let np_eq = self.mul(np.clone(), eq.clone());
            let nq_ep = self.mul(nq.clone(), ep.clone());
            let num_x = self.mul(self.add(np_eq.clone(), nq_ep.clone()), nr.clone());
            let eff_x = self.mul(self.mul(ep.clone(), eq.clone()), er.clone());
            // num_Y = (np·nr)·(Eq·Er) + (nq·nr)·(Ep·Er) ; eff_Y = (Ep·Er)·(Eq·Er).
            let np_nr = self.mul(np.clone(), nr.clone());
            let nq_nr = self.mul(nq.clone(), nr.clone());
            let eq_er = self.mul(eq.clone(), er.clone());
            let ep_er = self.mul(ep.clone(), er.clone());
            let ymono1 = self.mul(np_nr.clone(), eq_er.clone());
            let ymono2 = self.mul(nq_nr.clone(), ep_er.clone());
            let num_y = self.add(ymono1.clone(), ymono2.clone());
            let eff_y = self.mul(ep_er.clone(), eq_er.clone());

            // LHS = num_X · eff_Y. Distribute num_X (right_distrib) then whole.
            let lhs = self.mul(num_x.clone(), eff_y.clone());
            // d_num : num_X = (np·Eq)·nr + (nq·Ep)·nr.
            let npeq_nr = self.mul(np_eq.clone(), nr.clone());
            let nqep_nr = self.mul(nq_ep.clone(), nr.clone());
            let num_x_split = self.add(npeq_nr.clone(), nqep_nr.clone());
            let d_num = self.right_distrib(np_eq.clone(), nq_ep.clone(), nr.clone());
            let lhs_split = self.mul(num_x_split.clone(), eff_y.clone());
            let c_num = self.congr_arg(
                num_x.clone(),
                num_x_split.clone(),
                self.mul_right_fn(parent, eff_y.clone()),
                d_num,
            );
            let la = self.mul(npeq_nr.clone(), eff_y.clone());
            let lb = self.mul(nqep_nr.clone(), eff_y.clone());
            let la_lb = self.add(la.clone(), lb.clone());
            let d_lhs = self.right_distrib(npeq_nr.clone(), nqep_nr.clone(), eff_y.clone());
            let lhs_to_lalb =
                self.trans_int(lhs.clone(), lhs_split.clone(), la_lb.clone(), c_num, d_lhs);

            // RHS = num_Y · eff_X → RA + RB.
            let rhs = self.mul(num_y.clone(), eff_x.clone());
            let ra = self.mul(ymono1.clone(), eff_x.clone());
            let rb = self.mul(ymono2.clone(), eff_x.clone());
            let ra_rb = self.add(ra.clone(), rb.clone());
            let d_rhs = self.right_distrib(ymono1.clone(), ymono2.clone(), eff_x.clone());

            // LA = RA, LB = RB.
            //   LA := ((np·Eq)·nr)·((Ep·Er)·(Eq·Er))
            //   RA := ((np·nr)·(Eq·Er))·((Ep·Eq)·Er)
            let t_la = ProdTree::mul(
                ProdTree::mul(
                    ProdTree::mul(at(np.clone()), at(eq.clone())),
                    at(nr.clone()),
                ),
                ProdTree::mul(
                    ProdTree::mul(at(ep.clone()), at(er.clone())),
                    ProdTree::mul(at(eq.clone()), at(er.clone())),
                ),
            );
            let t_ra = ProdTree::mul(
                ProdTree::mul(
                    ProdTree::mul(at(np.clone()), at(nr.clone())),
                    ProdTree::mul(at(eq.clone()), at(er.clone())),
                ),
                ProdTree::mul(
                    ProdTree::mul(at(ep.clone()), at(eq.clone())),
                    at(er.clone()),
                ),
            );
            let la_eq_ra = self.prod_eq(parent, &t_la, &t_ra);
            //   LB := ((nq·Ep)·nr)·((Ep·Er)·(Eq·Er))
            //   RB := ((nq·nr)·(Ep·Er))·((Ep·Eq)·Er)
            let t_lb = ProdTree::mul(
                ProdTree::mul(
                    ProdTree::mul(at(nq.clone()), at(ep.clone())),
                    at(nr.clone()),
                ),
                ProdTree::mul(
                    ProdTree::mul(at(ep.clone()), at(er.clone())),
                    ProdTree::mul(at(eq.clone()), at(er.clone())),
                ),
            );
            let t_rb = ProdTree::mul(
                ProdTree::mul(
                    ProdTree::mul(at(nq.clone()), at(nr.clone())),
                    ProdTree::mul(at(ep.clone()), at(er.clone())),
                ),
                ProdTree::mul(
                    ProdTree::mul(at(ep.clone()), at(eq.clone())),
                    at(er.clone()),
                ),
            );
            let lb_eq_rb = self.prod_eq(parent, &t_lb, &t_rb);

            let mid = self.add_cong(parent, &la, &ra, &lb, &rb, &la_eq_ra, &lb_eq_rb);
            let d_rhs_sym = self.symm_int(rhs.clone(), ra_rb.clone(), d_rhs);
            let t1 = self.trans_int(lhs.clone(), la_lb.clone(), ra_rb.clone(), lhs_to_lalb, mid);
            self.trans_int(lhs, ra_rb, rhs, t1, d_rhs_sym)
        }
    }

    /// Prove `Eq Int <tree_l> <tree_r>` for two `Int.mul`-trees whose leaf
    /// multisets coincide: normalize each to its right-fold, then close the
    /// permutation between the two folds. The end-to-end monomial-equality
    /// engine for the distributive axioms.
    fn prod_eq(&self, parent: &EnvDeclBuilder, tl: &ProdTree, tr: &ProdTree) -> Expr {
        let l_expr = tl.to_expr(self);
        let r_expr = tr.to_expr(self);
        let l_atoms = tl.atoms();
        let r_atoms = tr.atoms();
        let l_fold = self.rfold(&l_atoms);
        let r_fold = self.rfold(&r_atoms);
        // hl : l_expr = l_fold ; hr : r_expr = r_fold.
        let hl = self.prod_norm(parent, tl);
        let hr = self.prod_norm(parent, tr);
        // perm : l_fold = r_fold.
        let perm = self.rfold_perm(parent, &l_atoms, &r_atoms);
        // l_expr = l_fold = r_fold = r_expr.
        let hr_sym = self.symm_int(r_expr.clone(), r_fold.clone(), hr);
        let t1 = self.trans_int(l_expr.clone(), l_fold.clone(), r_fold.clone(), hl, perm);
        self.trans_int(l_expr, r_fold, r_expr, t1, hr_sym)
    }

    // ── Generic Int SUM normalizer (over ProdTree monomials) ────────────────
    //
    // `Rat.add_assoc` reduces to a commutative-ring SUM equality whose addends
    // are degree-≥6 monomials. We right-fold the `Int.add`-tree of monomials and
    // close the monomial permutation by adjacent transpositions, proving each
    // monomial pairing via `prod_eq`.

    /// `sfold([m0, …, m_{n-1}]) = m0 + (m1 + (… + m_{n-1}))` (right-folded sum of
    /// Int expressions). Panics on empty.
    fn sfold(&self, monos: &[Expr]) -> Expr {
        let (last, init) = monos
            .split_last()
            .expect("invariant: sfold requires a non-empty list");
        let mut acc = last.clone();
        for m in init.iter().rev() {
            acc = self.add(m.clone(), acc);
        }
        acc
    }

    /// `sum_to_sfold(parent, tree, monos)` : `Eq Int <tree> (sfold monos)` where
    /// `tree` is an `Int.add`-tree with left-to-right leaves `monos`. Mirrors
    /// `prod_norm`/`rfold_append` with `Int.add_assoc` in place of `mul_assoc`.
    fn sum_to_sfold(&self, parent: &EnvDeclBuilder, tree: &SumTree) -> Expr {
        match tree {
            SumTree::Mono(m) => self.refl_int(m.to_expr(self)),
            SumTree::Add(l, r) => {
                let l_expr = l.to_expr(self);
                let r_expr = r.to_expr(self);
                let l_monos = l.monos(self);
                let r_monos = r.monos(self);
                let l_fold = self.sfold(&l_monos);
                let r_fold = self.sfold(&r_monos);
                let hl = self.sum_to_sfold(parent, l);
                let hr = self.sum_to_sfold(parent, r);
                let lhs = self.add(l_expr.clone(), r_expr.clone());
                let mid = self.add(l_fold.clone(), r_fold.clone());
                let cong1 = self.congr_arg(
                    l_expr.clone(),
                    l_fold.clone(),
                    self.add_left_fn(parent, r_expr.clone()),
                    hl,
                );
                let cong2 = self.congr_arg(
                    r_expr.clone(),
                    r_fold.clone(),
                    self.add_right_fn(parent, l_fold.clone()),
                    hr,
                );
                let step1 = self.trans_int(
                    lhs.clone(),
                    self.add(l_fold.clone(), r_expr.clone()),
                    mid.clone(),
                    cong1,
                    cong2,
                );
                let step2 = self.sfold_append(parent, &l_monos, &r_monos);
                let mut all = l_monos.clone();
                all.extend(r_monos.iter().cloned());
                let rhs = self.sfold(&all);
                self.trans_int(lhs, mid, rhs, step1, step2)
            }
        }
    }

    /// `sfold_append(parent, ls, rs)` : `Eq Int (sfold ls + sfold rs)
    /// (sfold (ls ++ rs))` by induction on `ls` with `Int.add_assoc`.
    fn sfold_append(&self, parent: &EnvDeclBuilder, ls: &[Expr], rs: &[Expr]) -> Expr {
        if ls.len() == 1 {
            let lhs = self.add(ls[0].clone(), self.sfold(rs));
            return self.refl_int(lhs);
        }
        let a = ls[0].clone();
        let tl = &ls[1..];
        let sfold_tl = self.sfold(tl);
        let sfold_rs = self.sfold(rs);
        let lhs = self.add(self.add(a.clone(), sfold_tl.clone()), sfold_rs.clone());
        let mid = self.add(a.clone(), self.add(sfold_tl.clone(), sfold_rs.clone()));
        let s1 = self.add_assoc(a.clone(), sfold_tl.clone(), sfold_rs.clone());
        let ih = self.sfold_append(parent, tl, rs);
        let mut tl_rs = tl.to_vec();
        tl_rs.extend(rs.iter().cloned());
        let sfold_tlrs = self.sfold(&tl_rs);
        let rhs = self.add(a.clone(), sfold_tlrs.clone());
        let s2 = self.congr_arg(
            self.add(sfold_tl.clone(), sfold_rs.clone()),
            sfold_tlrs.clone(),
            self.add_right_fn(parent, a.clone()),
            ih,
        );
        self.trans_int(lhs, mid, rhs, s1, s2)
    }

    /// Adjacent-transposition primitive for the sum fold:
    /// `Eq Int (a + (b + R)) (b + (a + R))` (or `a + b = b + a` if `rest` empty).
    fn sum_swap_head(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr, rest: &[Expr]) -> Expr {
        if rest.is_empty() {
            return self.add_comm(a.clone(), b.clone());
        }
        let r = self.sfold(rest);
        let lhs = self.add(a.clone(), self.add(b.clone(), r.clone()));
        let ab_r = self.add(self.add(a.clone(), b.clone()), r.clone());
        let s1 = self.symm_int(
            ab_r.clone(),
            lhs.clone(),
            self.add_assoc(a.clone(), b.clone(), r.clone()),
        );
        let ba_r = self.add(self.add(b.clone(), a.clone()), r.clone());
        let s2 = self.congr_arg(
            self.add(a.clone(), b.clone()),
            self.add(b.clone(), a.clone()),
            self.add_left_fn(parent, r.clone()),
            self.add_comm(a.clone(), b.clone()),
        );
        let rhs = self.add(b.clone(), self.add(a.clone(), r.clone()));
        let s3 = self.add_assoc(b.clone(), a.clone(), r.clone());
        let t1 = self.trans_int(lhs.clone(), ab_r, ba_r.clone(), s1, s2);
        self.trans_int(lhs, ba_r, rhs, t1, s3)
    }

    /// Bubble the `k`-th monomial of a sum fold to the front (`k` swaps).
    fn sum_pull_front(&self, parent: &EnvDeclBuilder, monos: &[Expr], k: usize) -> Expr {
        if k == 0 {
            return self.refl_int(self.sfold(monos));
        }
        let mut cur: Vec<Expr> = monos.to_vec();
        let mut proof = self.refl_int(self.sfold(&cur));
        let start = self.sfold(monos);
        let mut i = k;
        while i >= 1 {
            let prefix = &cur[..i - 1];
            let a = cur[i - 1].clone();
            let b = cur[i].clone();
            let rest = &cur[i + 1..];
            let swap = self.sum_swap_head(parent, &a, &b, rest);
            let lifted = self.sum_lift_through_prefix(parent, prefix, &a, &b, rest, &swap);
            let mut next = cur.clone();
            next.swap(i - 1, i);
            let from = self.sfold(&cur);
            let to = self.sfold(&next);
            proof = self.trans_int(start.clone(), from, to, proof, lifted);
            cur = next;
            i -= 1;
        }
        proof
    }

    /// Lift a sum-swap through a shared prefix via nested `congrArg (p + ·)`.
    fn sum_lift_through_prefix(
        &self,
        parent: &EnvDeclBuilder,
        prefix: &[Expr],
        a: &Expr,
        b: &Expr,
        rest: &[Expr],
        swap: &Expr,
    ) -> Expr {
        let r = if rest.is_empty() {
            None
        } else {
            Some(self.sfold(rest))
        };
        let sub_lhs = match &r {
            Some(rr) => self.add(a.clone(), self.add(b.clone(), rr.clone())),
            None => self.add(a.clone(), b.clone()),
        };
        let sub_rhs = match &r {
            Some(rr) => self.add(b.clone(), self.add(a.clone(), rr.clone())),
            None => self.add(b.clone(), a.clone()),
        };
        let mut cur_lhs = sub_lhs;
        let mut cur_rhs = sub_rhs;
        let mut acc = swap.clone();
        for p in prefix.iter().rev() {
            let new_lhs = self.add(p.clone(), cur_lhs.clone());
            let new_rhs = self.add(p.clone(), cur_rhs.clone());
            acc = self.congr_arg(
                cur_lhs.clone(),
                cur_rhs.clone(),
                self.add_right_fn(parent, p.clone()),
                acc,
            );
            cur_lhs = new_lhs;
            cur_rhs = new_rhs;
        }
        acc
    }

    /// `Eq Int <tree_l> <tree_r>` for two `Int.add`-trees of `ProdTree`
    /// monomials whose monomials match (up to a permutation) by atom multiset:
    /// normalize each to its right-folded sum, prove the monomial permutation by
    /// adjacent transpositions, and discharge each aligned monomial pair by
    /// `prod_eq`. The end-to-end engine for `Rat.add_assoc`.
    fn sum_eq(&self, parent: &EnvDeclBuilder, tl: &SumTree, tr: &SumTree) -> Expr {
        let l_expr = tl.to_expr(self);
        let r_expr = tr.to_expr(self);
        let l_monos: Vec<ProdTree> = tl.mono_trees();
        let r_monos: Vec<ProdTree> = tr.mono_trees();
        let l_exprs = tl.monos(self);
        let r_exprs = tr.monos(self);
        // Normalize each tree to its sum-fold.
        let hl = self.sum_to_sfold(parent, tl);
        let hr = self.sum_to_sfold(parent, tr);
        let l_fold = self.sfold(&l_exprs);
        let r_fold = self.sfold(&r_exprs);
        // Reorder r's monomials to match l's, by atom-multiset key, recording the
        // permuted r monomial list (as exprs) and the per-position prod_eq proofs.
        let perm = self.sum_fold_perm(parent, &l_monos, &r_monos, &l_exprs, &r_exprs);
        let hr_sym = self.symm_int(r_expr.clone(), r_fold.clone(), hr);
        let t1 = self.trans_int(l_expr.clone(), l_fold.clone(), r_fold.clone(), hl, perm);
        self.trans_int(l_expr, r_fold, r_expr, t1, hr_sym)
    }

    /// Build the `Rat.add_assoc` cross `Equiv`:
    /// `Eq Int (num_L · eff_R) (num_R · eff_L)` for reps `p, q, r`, where
    ///   L = raw_add (raw_add p q) r,  R = raw_add p (raw_add q r).
    fn add_assoc_cross(&self, parent: &EnvDeclBuilder, p: &Expr, q: &Expr, r: &Expr) -> Expr {
        let np = self.num(p.clone());
        let nq = self.num(q.clone());
        let nr = self.num(r.clone());
        let ep = self.eff(p.clone());
        let eq = self.eff(q.clone());
        let er = self.eff(r.clone());
        let at = ProdTree::atom;

        // num_L = ((np·Eq + nq·Ep)·Er) + (nr·(Ep·Eq)) ; eff_L = (Ep·Eq)·Er.
        let np_eq = self.mul(np.clone(), eq.clone());
        let nq_ep = self.mul(nq.clone(), ep.clone());
        let num_pq = self.add(np_eq.clone(), nq_ep.clone());
        let ep_eq = self.mul(ep.clone(), eq.clone());
        let t1 = self.mul(num_pq.clone(), er.clone());
        let t2 = self.mul(nr.clone(), ep_eq.clone());
        let num_l = self.add(t1.clone(), t2.clone());
        let eff_l = self.mul(ep_eq.clone(), er.clone());

        // num_R = (np·(Eq·Er)) + ((nq·Er + nr·Eq)·Ep) ; eff_R = Ep·(Eq·Er).
        let eq_er = self.mul(eq.clone(), er.clone());
        let nq_er = self.mul(nq.clone(), er.clone());
        let nr_eq = self.mul(nr.clone(), eq.clone());
        let num_qr = self.add(nq_er.clone(), nr_eq.clone());
        let u1 = self.mul(np.clone(), eq_er.clone());
        let u2 = self.mul(num_qr.clone(), ep.clone());
        let num_r = self.add(u1.clone(), u2.clone());
        let eff_r = self.mul(ep.clone(), eq_er.clone());

        // ── LHS = num_L · eff_R.  Flatten num_L to 3 monomials, then scale. ──
        // Flatten T1 = (np·Eq + nq·Ep)·Er = (np·Eq)·Er + (nq·Ep)·Er.
        let np_eq_er = self.mul(np_eq.clone(), er.clone());
        let nq_ep_er = self.mul(nq_ep.clone(), er.clone());
        let t1_flat = self.add(np_eq_er.clone(), nq_ep_er.clone());
        let dt1 = self.right_distrib(np_eq.clone(), nq_ep.clone(), er.clone());
        // num_L_flat = t1_flat + t2 ; congr on left of (+t2).
        let num_l_flat = self.add(t1_flat.clone(), t2.clone());
        let p_numl = self.congr_arg(
            t1.clone(),
            t1_flat.clone(),
            self.add_left_fn(parent, t2.clone()),
            dt1,
        );
        // SumTree for num_L_flat monomials: ((np·Eq)·Er) , ((nq·Ep)·Er) , (nr·(Ep·Eq)).
        let sl_tree = SumTree::add(
            SumTree::add(
                SumTree::mono(ProdTree::mul(
                    ProdTree::mul(at(np.clone()), at(eq.clone())),
                    at(er.clone()),
                )),
                SumTree::mono(ProdTree::mul(
                    ProdTree::mul(at(nq.clone()), at(ep.clone())),
                    at(er.clone()),
                )),
            ),
            SumTree::mono(ProdTree::mul(
                at(nr.clone()),
                ProdTree::mul(at(ep.clone()), at(eq.clone())),
            )),
        );
        // Scale by eff_R (decomposed tree Ep·(Eq·Er)).
        let eff_r_tree = ProdTree::mul(
            at(ep.clone()),
            ProdTree::mul(at(eq.clone()), at(er.clone())),
        );
        let (sle_tree, p_scale_l) = self.mul_sum_right(parent, &sl_tree, &eff_r_tree);
        // LHS chain: num_L·eff_R = num_L_flat·eff_R = (sl_tree·eff_R) = sle_tree.
        let lhs0 = self.mul(num_l.clone(), eff_r.clone());
        let lhs1 = self.mul(num_l_flat.clone(), eff_r.clone());
        let c_l = self.congr_arg(
            num_l.clone(),
            num_l_flat.clone(),
            self.mul_right_fn(parent, eff_r.clone()),
            p_numl,
        );
        let p_left = self.trans_int(
            lhs0.clone(),
            lhs1.clone(),
            sle_tree.to_expr(self),
            c_l,
            p_scale_l,
        );

        // ── RHS = num_R · eff_L.  Flatten U2 = (nq·Er + nr·Eq)·Ep. ──
        let nq_er_ep = self.mul(nq_er.clone(), ep.clone());
        let nr_eq_ep = self.mul(nr_eq.clone(), ep.clone());
        let u2_flat = self.add(nq_er_ep.clone(), nr_eq_ep.clone());
        let du2 = self.right_distrib(nq_er.clone(), nr_eq.clone(), ep.clone());
        let num_r_flat = self.add(u1.clone(), u2_flat.clone());
        let p_numr = self.congr_arg(
            u2.clone(),
            u2_flat.clone(),
            self.add_right_fn(parent, u1.clone()),
            du2,
        );
        // SumTree for num_R_flat: (np·(Eq·Er)) , ((nq·Er)·Ep) , ((nr·Eq)·Ep).
        let sr_tree = SumTree::add(
            SumTree::mono(ProdTree::mul(
                at(np.clone()),
                ProdTree::mul(at(eq.clone()), at(er.clone())),
            )),
            SumTree::add(
                SumTree::mono(ProdTree::mul(
                    ProdTree::mul(at(nq.clone()), at(er.clone())),
                    at(ep.clone()),
                )),
                SumTree::mono(ProdTree::mul(
                    ProdTree::mul(at(nr.clone()), at(eq.clone())),
                    at(ep.clone()),
                )),
            ),
        );
        // Scale by eff_L (decomposed tree (Ep·Eq)·Er).
        let eff_l_tree = ProdTree::mul(
            ProdTree::mul(at(ep.clone()), at(eq.clone())),
            at(er.clone()),
        );
        let (sre_tree, p_scale_r) = self.mul_sum_right(parent, &sr_tree, &eff_l_tree);
        let rhs0 = self.mul(num_r.clone(), eff_l.clone());
        let rhs1 = self.mul(num_r_flat.clone(), eff_l.clone());
        let c_r = self.congr_arg(
            num_r.clone(),
            num_r_flat.clone(),
            self.mul_right_fn(parent, eff_l.clone()),
            p_numr,
        );
        let p_right = self.trans_int(
            rhs0.clone(),
            rhs1.clone(),
            sre_tree.to_expr(self),
            c_r,
            p_scale_r,
        );

        // ── Match the two scaled sums. ──
        let mid = self.sum_eq(parent, &sle_tree, &sre_tree);
        // num_L·eff_R = sle = sre = num_R·eff_R? No: sre = num_R·eff_L. Chain:
        //   lhs0 =[p_left] sle =[mid] sre =[symm p_right] rhs0.
        let p_right_sym = self.symm_int(rhs0.clone(), sre_tree.to_expr(self), p_right);
        let t = self.trans_int(
            lhs0.clone(),
            sle_tree.to_expr(self),
            sre_tree.to_expr(self),
            p_left,
            mid,
        );
        self.trans_int(lhs0, sre_tree.to_expr(self), rhs0, t, p_right_sym)
    }

    /// Distribute a right factor `eff` over a `SumTree` numerator: returns
    /// `(scaled_tree, proof)` where `proof : Eq Int (num·eff) (scaled_tree.to_expr)`
    /// and `scaled_tree` is `num` with every monomial `m` replaced by `m·eff`.
    /// Recurses with `Int.right_distrib`.
    fn mul_sum_right(
        &self,
        parent: &EnvDeclBuilder,
        num: &SumTree,
        eff_tree: &ProdTree,
    ) -> (SumTree, Expr) {
        let eff = &eff_tree.to_expr(self);
        match num {
            SumTree::Mono(m) => {
                let m_expr = m.to_expr(self);
                // Scale by the DECOMPOSED eff tree so the resulting monomial's
                // atom multiset includes eff's atoms (needed for sum_fold_perm).
                let scaled = ProdTree::mul(m.clone(), eff_tree.clone());
                // (m)·eff is DEFINITIONALLY scaled.to_expr ; refl.
                (
                    SumTree::mono(scaled),
                    self.refl_int(self.mul(m_expr, eff.clone())),
                )
            }
            SumTree::Add(l, r) => {
                let l_expr = l.to_expr(self);
                let r_expr = r.to_expr(self);
                let sum_expr = self.add(l_expr.clone(), r_expr.clone());
                // (L+R)·eff = L·eff + R·eff   [right_distrib]
                let d = self.right_distrib(l_expr.clone(), r_expr.clone(), eff.clone());
                let (l_tree, l_proof) = self.mul_sum_right(parent, l, eff_tree);
                let (r_tree, r_proof) = self.mul_sum_right(parent, r, eff_tree);
                // add_cong(l_proof, r_proof) : (L·eff + R·eff) = (l_tree + r_tree)
                let l_eff = self.mul(l_expr.clone(), eff.clone());
                let r_eff = self.mul(r_expr.clone(), eff.clone());
                let l_tree_e = l_tree.to_expr(self);
                let r_tree_e = r_tree.to_expr(self);
                let cong = self.add_cong(
                    parent, &l_eff, &l_tree_e, &r_eff, &r_tree_e, &l_proof, &r_proof,
                );
                let sum_eff = self.add(l_eff.clone(), r_eff.clone());
                let whole = self.mul(sum_expr.clone(), eff.clone());
                let scaled_tree = SumTree::add(l_tree, r_tree);
                let proof = self.trans_int(whole, sum_eff, scaled_tree.to_expr(self), d, cong);
                (scaled_tree, proof)
            }
        }
    }

    /// `Eq Int (sfold l_exprs)(sfold r_exprs)` where `l_monos`/`r_monos` are the
    /// corresponding `ProdTree`s. Selection-sort: bring `l_monos[0]`'s match to
    /// the front of `r`, close the head pair by `prod_eq`, recurse on the tails.
    fn sum_fold_perm(
        &self,
        parent: &EnvDeclBuilder,
        l_monos: &[ProdTree],
        r_monos: &[ProdTree],
        l_exprs: &[Expr],
        r_exprs: &[Expr],
    ) -> Expr {
        if l_monos.len() == 1 {
            // single monomial each: prod_eq directly.
            return self.prod_eq(parent, &l_monos[0], &r_monos[0]);
        }
        let head_key = prod_key(&l_monos[0]);
        let k = r_monos
            .iter()
            .position(|m| prod_key(m) == head_key)
            .expect("invariant: sum_fold_perm: monomial multisets must match");
        // Pull r[k] to front.
        let pull = self.sum_pull_front(parent, r_exprs, k);
        let mut r_front_monos: Vec<ProdTree> = Vec::with_capacity(r_monos.len());
        let mut r_front_exprs: Vec<Expr> = Vec::with_capacity(r_exprs.len());
        r_front_monos.push(r_monos[k].clone());
        r_front_exprs.push(r_exprs[k].clone());
        for (i, m) in r_monos.iter().enumerate() {
            if i != k {
                r_front_monos.push(m.clone());
                r_front_exprs.push(r_exprs[i].clone());
            }
        }
        // Head pair: prod_eq(l[0], r_front[0]).
        let head_eq = self.prod_eq(parent, &l_monos[0], &r_front_monos[0]);
        // Tail: sum_fold_perm on tails.
        let tail_eq = self.sum_fold_perm(
            parent,
            &l_monos[1..],
            &r_front_monos[1..],
            &l_exprs[1..],
            &r_front_exprs[1..],
        );
        // sfold l = head_l + sfold(l_tail) ; sfold r_front = head_r + sfold(r_tail).
        let l_fold = self.sfold(l_exprs);
        let head_l = l_exprs[0].clone();
        let l_tail_fold = self.sfold(&l_exprs[1..]);
        let head_r = r_front_exprs[0].clone();
        let r_tail_fold = self.sfold(&r_front_exprs[1..]);
        let r_front_fold = self.sfold(&r_front_exprs);
        let r_fold = self.sfold(r_exprs);
        // cong : (head_l + l_tail) = (head_r + r_tail)  via add_cong(head_eq, tail_eq).
        let cong = self.add_cong(
            parent,
            &head_l,
            &head_r,
            &l_tail_fold,
            &r_tail_fold,
            &head_eq,
            &tail_eq,
        );
        // l_fold ≡ head_l + l_tail (defeq) ; r_front_fold ≡ head_r + r_tail.
        // chain: l_fold =[cong] r_front_fold =[symm pull] r_fold.
        let pull_sym = self.symm_int(r_fold.clone(), r_front_fold.clone(), pull);
        self.trans_int(l_fold, r_front_fold, r_fold, cong, pull_sym)
    }
}

/// A binary `Int.mul`-tree of atoms, used by the generic product normalizer.
#[derive(Clone)]
enum ProdTree {
    Atom(Expr),
    Mul(Box<ProdTree>, Box<ProdTree>),
}

impl ProdTree {
    fn atom(e: Expr) -> Self {
        ProdTree::Atom(e)
    }

    fn mul(l: ProdTree, r: ProdTree) -> Self {
        ProdTree::Mul(Box::new(l), Box::new(r))
    }

    /// Rebuild the underlying `Int.mul` expression.
    fn to_expr(&self, c: &RatRawConsts) -> Expr {
        match self {
            ProdTree::Atom(e) => e.clone(),
            ProdTree::Mul(l, r) => c.mul(l.to_expr(c), r.to_expr(c)),
        }
    }

    /// Left-to-right leaf sequence.
    fn atoms(&self) -> Vec<Expr> {
        let mut out = Vec::new();
        self.collect(&mut out);
        out
    }

    fn collect(&self, out: &mut Vec<Expr>) {
        match self {
            ProdTree::Atom(e) => out.push(e.clone()),
            ProdTree::Mul(l, r) => {
                l.collect(out);
                r.collect(out);
            }
        }
    }
}

/// Atom-multiset key of a monomial `ProdTree` (sorted `Debug` strings of its
/// leaves) — two monomials with equal keys are `prod_eq`-equal.
fn prod_key(t: &ProdTree) -> Vec<String> {
    let mut keys: Vec<String> = t.atoms().iter().map(|a| format!("{a:?}")).collect();
    keys.sort();
    keys
}

/// A binary `Int.add`-tree of `ProdTree` monomials, for the sum normalizer.
#[derive(Clone)]
enum SumTree {
    Mono(ProdTree),
    Add(Box<SumTree>, Box<SumTree>),
}

impl SumTree {
    fn mono(t: ProdTree) -> Self {
        SumTree::Mono(t)
    }

    fn add(l: SumTree, r: SumTree) -> Self {
        SumTree::Add(Box::new(l), Box::new(r))
    }

    fn to_expr(&self, c: &RatRawConsts) -> Expr {
        match self {
            SumTree::Mono(t) => t.to_expr(c),
            SumTree::Add(l, r) => c.add(l.to_expr(c), r.to_expr(c)),
        }
    }

    /// Left-to-right monomial expressions.
    fn monos(&self, c: &RatRawConsts) -> Vec<Expr> {
        self.mono_trees().iter().map(|t| t.to_expr(c)).collect()
    }

    /// Left-to-right monomial `ProdTree`s.
    fn mono_trees(&self) -> Vec<ProdTree> {
        let mut out = Vec::new();
        self.collect_monos(&mut out);
        out
    }

    fn collect_monos(&self, out: &mut Vec<ProdTree>) {
        match self {
            SumTree::Mono(t) => out.push(t.clone()),
            SumTree::Add(l, r) => {
                l.collect_monos(out);
                r.collect_monos(out);
            }
        }
    }
}

impl Environment {
    /// Register the whole `Qat` (quotient rational) proof-of-concept.
    ///
    /// Builds, in dependency order, all via the CHECKED `self.add_decl`:
    ///
    /// 1. `Qat.Raw` inductive + `num`/`denom`/`effDenom` projections.
    /// 2. `Qat.Raw.Equiv` + a proof it is an equivalence (`refl`/`symm`/`trans`).
    /// 3. `Qat := Quot Qat.Raw.Equiv`, `Qat.mk`, `Qat.zero`, `Qat.one`.
    /// 4. `Qat.mul` (binary `Quot.lift`) and `Qat.le` (binary `Quot.lift` into
    ///    `Prop`), each with well-definedness discharged by real proofs.
    /// 5. The PAYOFF: `Qat.zero_mul` and `Qat.le_antisymm` as genuine
    ///    `Declaration::Theorem`s.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance.
    /// ENSURES: On success, all `Qat.*` constants above are registered and
    /// kernel-checked; idempotent (skip-if-present on the carrier).
    #[cfg(any(test, feature = "math-overlays"))]
    pub(crate) fn init_rat_quotient_poc(&mut self) -> Result<(), EnvError> {
        self.ensure_rat_quotient_deps()?;

        let c = RatRawConsts::new();

        // Full quotient `Rat` tower, built over a env that has NO free `Rat`.
        // This is the self-contained VALIDATOR (exercised by this module's
        // tests over a fresh `Environment`). The LIVE swap reuses the same
        // builder functions, but drives them from `init_rat` / `init_rat_arith`
        // / `init_rat_ord` (see the `rat_quotient_*_into_live` helpers).
        self.register_rat_raw(&c)?;
        self.register_rat_raw_projections(&c)?;
        self.register_rat_raw_equiv(&c)?;
        self.register_rat_raw_equiv_equivalence(&c)?;
        self.register_rat_quotient(&c)?;
        self.register_rat_q_mul(&c)?;
        self.register_rat_q_neg(&c)?;
        self.register_rat_q_add(&c)?;
        self.register_rat_q_le(&c)?;
        self.register_rat_q_lt(&c)?;
        self.register_rat_q_inv(&c)?;
        self.register_rat_q_div(&c)?;
        self.register_rat_q_payoff(&c)?;

        Ok(())
    }

    /// Register every `Int`/`Nat`/`Quot`/`propext` prerequisite the quotient
    /// `Rat` tower needs, each idempotent / skip-if-present.
    ///
    /// Used BOTH by the self-contained validator [`Self::init_rat_quotient_poc`]
    /// (over a fresh env with no free `Rat`) AND by the LIVE carrier swap (from
    /// `init_rat`). It must NOT pull in `init_rat` / `init_rat_ord`, so it
    /// depends on `init_int` + the pure-Int cross-trans registrations instead.
    pub(crate) fn ensure_rat_quotient_deps(&mut self) -> Result<(), EnvError> {
        self.init_int()?; // pulls Int, Nat, Int.ofNat, Nat.pred, Nat.mul, ...
        self.init_int_arith()?; // Int.mul
        self.init_int_linear_order()?; // Int.le, Int.le_antisymm carrier
        self.init_eq()?; // Eq, Eq.refl, Eq.symm, Eq.trans, congrArg
        self.init_propext()?; // propext (for Rat.le's Prop-valued lift respect)
        self.init_quot(); // Quot, Quot.mk, Quot.lift, Quot.ind
        self.init_quot_sound()?; // Quot.sound
                                 // Constructive Int lemmas used by the Equiv / payoff proofs.
        self.register_int_mul_comm_proof()?;
        self.register_int_mul_assoc_proof()?;
        self.register_int_mul_left_cancel_ofnat_succ_proof()?;
        self.register_int_le_antisymm_proof()?;
        self.register_int_zero_mul_proof()?;
        self.register_int_le_refl_proof()?;
        // Registers `Int.le_cross_trans` (+ `Int.mul_rearrange`,
        // `Int.le_of_mul_le_mul_left_succ`, the monotonicity lemmas) used by the
        // `Rat.le` order-respect proofs — WITHOUT building the free `Rat`.
        self.register_int_le_cross_trans_only()?;
        // Strict cross-multiplication transitivity (`Int.lt_cross_trans{,'}`)
        // used by the `Rat.lt` lift order-respect proofs.
        self.register_int_lt_cross_trans_only()?;
        // Additional Int lemmas for the additive / distributive / order theorems.
        self.register_int_add_comm_proof()?;
        self.register_int_add_assoc_proof()?;
        self.register_int_left_distrib_proof()?;
        self.register_int_right_distrib_proof()?;
        self.register_int_mul_zero_proof()?;
        self.register_int_neg_mul_left_proof()?;
        self.register_int_neg_mul_right_proof()?;
        self.register_int_add_le_add_left_proof()?;
        self.register_int_mul_le_mul_of_nonneg_right_proof()?;
        self.register_int_neg_add_self_proof()?;
        self.register_int_add_neg_self_proof()?;
        self.register_int_mul_one_proof()?;
        self.register_int_mul_nonneg_proof()?;
        self.register_int_add_zero_proof()?;
        self.register_int_ofnat_zero_le_proof()?;
        self.register_int_neg_neg_proof()?;
        self.init_true_false()?; // False / False.elim for mul_inv_cancel's zero leaf
                                 // `Int.noConfusion` / `Nat.noConfusion` discharge the impossible
                                 // mixed/zero-sign leaves of the `Rat.inv` respect proof.
        if self
            .get_const(&Name::from_string("Int.noConfusion"))
            .is_none()
            || self
                .get_const(&Name::from_string("Nat.noConfusion"))
                .is_none()
        {
            self.regenerate_missing_no_confusion();
        }
        Ok(())
    }

    /// LIVE carrier swap — step 1 (carrier): register the quotient `Rat`,
    /// `Rat.mk`, `Rat.zero`, `Rat.one` over `Rat.Raw`. Assumes `init_rat`
    /// already registered the `Rat.Raw` carrier + `Rat.Raw.Equiv`.
    pub(crate) fn rat_quotient_carrier_into_live(&mut self) -> Result<(), EnvError> {
        self.ensure_rat_quotient_deps()?;
        let c = RatRawConsts::new();
        self.register_rat_raw(&c)?;
        self.register_rat_raw_projections(&c)?;
        self.register_rat_raw_equiv(&c)?;
        self.register_rat_raw_equiv_equivalence(&c)?;
        self.register_rat_quotient(&c)?;
        Ok(())
    }

    /// LIVE carrier swap — step 2 (arithmetic ops): register the quotient
    /// `Rat.neg/add/sub/mul/inv/div` (each a checked `Quot.lift`).
    pub(crate) fn rat_quotient_arith_into_live(&mut self) -> Result<(), EnvError> {
        let c = RatRawConsts::new();
        self.register_rat_q_mul(&c)?;
        self.register_rat_q_neg(&c)?;
        self.register_rat_q_add(&c)?;
        self.register_rat_q_inv(&c)?;
        self.register_rat_q_div(&c)?;
        Ok(())
    }

    /// LIVE carrier swap — step 2 (order ops): register the quotient
    /// `Rat.le`/`Rat.lt` (binary `Quot.lift` into `Prop`).
    pub(crate) fn rat_quotient_ord_into_live(&mut self) -> Result<(), EnvError> {
        let c = RatRawConsts::new();
        self.register_rat_q_le(&c)?;
        self.register_rat_q_lt(&c)?;
        Ok(())
    }

    /// LIVE carrier swap — step 3 (payoff theorems): register all 11
    /// previously-false `Rat.*` axioms as genuine quotient `Theorem`s (plus
    /// `Rat.add_zero` / `Rat.add_assoc`). Ensures the full carrier + ops + order
    /// tower is in place first, so it is safe to call from any axiom-registration
    /// site that previously emitted these as `Declaration::Axiom`.
    pub(crate) fn rat_quotient_payoff_into_live(&mut self) -> Result<(), EnvError> {
        self.init_rat()?; // carrier (Rat, Rat.mk, Rat.Raw.*)
        self.init_rat_arith()?; // Rat.add/neg/mul/inv/div
        self.init_rat_ord()?; // Rat.le/Rat.lt (needed by the order payoffs)
        let c = RatRawConsts::new();
        self.register_rat_q_payoff(&c)?;
        Ok(())
    }

    /// Register ONLY the additive pre-quotient carrier: `Rat.Raw` inductive,
    /// its `num`/`denom`/`effDenom` projections, and the `Rat.Raw.Equiv`
    /// definition. All `Rat.Raw.*`, no collision with the live `Rat`.
    ///
    /// The `Rat.Raw.Equiv` *definition* only needs `Eq` (its body is
    /// `Eq Int (num p · eff q) (num q · eff p)`). The PROOFS that `Equiv` is an
    /// equivalence (refl/symm/trans) need additional Int lemmas and are
    /// registered by [`Self::register_rat_raw_equiv_equivalence`] at the point
    /// the quotient ops/payoff are built — NOT here — so this stays a cheap,
    /// dependency-light additive step callable from the foundational `init_rat`
    /// (which guarantees `init_eq` ran first).
    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    pub(crate) fn register_rat_raw_carrier(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        self.register_rat_raw(c)?;
        self.register_rat_raw_projections(c)?;
        self.register_rat_raw_equiv(c)?;
        Ok(())
    }

    /// 1a. `Qat.Raw` — the free pre-quotient inductive (identical shape to the
    /// live `Rat`): `Qat.Raw.mk : Int → Nat → Qat.Raw`, `Qat.Raw : Type 0`.
    fn register_rat_raw(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        if self.get_inductive(&Name::from_string("Rat.Raw")).is_some() {
            return Ok(());
        }
        // Qat.Raw : Type 0 = Sort 1
        let raw_type = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
        // Qat.Raw.mk : Int → Nat → Qat.Raw
        let raw_mk_type = Expr::pi(
            BinderInfo::Default,
            c.int.clone(),
            Expr::pi(BinderInfo::Default, c.nat.clone(), c.raw.clone()),
        );
        self.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string("Rat.Raw"),
                type_: raw_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Rat.Raw.mk"),
                    type_: raw_mk_type,
                }],
            }],
        })
    }

    /// 1b. Projections + effective denominator, mirroring `Rat.num`/`Rat.denom`/
    /// `Rat.effDenom` (via `Qat.Raw.rec`).
    fn register_rat_raw_projections(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        // `Qat.Raw.rec.{1}` eliminating into `Type 0 = Sort 1`.
        let raw_rec = Expr::const_(
            Name::from_string("Rat.Raw.rec"),
            vec![Level::succ(Level::zero())],
        );

        // Qat.Raw.num := λ p => Qat.Raw.rec (λ _ => Int) (λ num denom => num) p
        if self.get_const(&Name::from_string("Rat.Raw.num")).is_none() {
            let num_type = Expr::pi(BinderInfo::Default, c.raw.clone(), c.int.clone());
            let num_motive = Expr::lam(BinderInfo::Default, c.raw.clone(), c.int.clone());
            let num_mk_case = {
                let mut b = EnvDeclBuilder::new();
                let (num_id, num) = b.fresh_local(c.int.clone());
                let (denom_id, _denom) = b.fresh_local(c.nat.clone());
                let e = b.mk_lam(denom_id, BinderInfo::Default, c.nat.clone(), num);
                let e = b.mk_lam(num_id, BinderInfo::Default, c.int.clone(), e);
                b.finish(e)
            };
            let num_value = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(c.raw.clone());
                let body = Expr::apps(raw_rec.clone(), [num_motive, num_mk_case, p]);
                let e = b.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), body);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Rat.Raw.num"),
                level_params: vec![],
                type_: num_type,
                value: num_value,
                is_reducible: true,
            })?;
        }

        // Qat.Raw.denom := λ p => Qat.Raw.rec (λ _ => Nat) (λ num denom => denom) p
        if self
            .get_const(&Name::from_string("Rat.Raw.denom"))
            .is_none()
        {
            let denom_type = Expr::pi(BinderInfo::Default, c.raw.clone(), c.nat.clone());
            let denom_motive = Expr::lam(BinderInfo::Default, c.raw.clone(), c.nat.clone());
            let denom_mk_case = {
                let mut b = EnvDeclBuilder::new();
                let (num_id, _num) = b.fresh_local(c.int.clone());
                let (denom_id, denom) = b.fresh_local(c.nat.clone());
                let e = b.mk_lam(denom_id, BinderInfo::Default, c.nat.clone(), denom);
                let e = b.mk_lam(num_id, BinderInfo::Default, c.int.clone(), e);
                b.finish(e)
            };
            let denom_value = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(c.raw.clone());
                let body = Expr::apps(raw_rec.clone(), [denom_motive, denom_mk_case, p]);
                let e = b.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), body);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Rat.Raw.denom"),
                level_params: vec![],
                type_: denom_type,
                value: denom_value,
                is_reducible: true,
            })?;
        }

        // Qat.Raw.effDenom := λ p => Nat.succ (Nat.pred (Qat.Raw.denom p))
        if self
            .get_const(&Name::from_string("Rat.Raw.effDenom"))
            .is_none()
        {
            let eff_type = Expr::pi(BinderInfo::Default, c.raw.clone(), c.nat.clone());
            let eff_value = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(c.raw.clone());
                let denom_p = Expr::app(c.raw_denom.clone(), p);
                let body = Expr::app(c.nat_succ.clone(), Expr::app(c.nat_pred.clone(), denom_p));
                let e = b.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), body);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Rat.Raw.effDenom"),
                level_params: vec![],
                type_: eff_type,
                value: eff_value,
                is_reducible: true,
            })?;
        }

        Ok(())
    }

    /// 2. `Qat.Raw.Equiv : Qat.Raw → Qat.Raw → Prop`
    ///     `:= fun p q => @Eq Int (num p * ofNat (effDenom q))
    ///                            (num q * ofNat (effDenom p))`.
    fn register_rat_raw_equiv(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("Rat.Raw.Equiv"))
            .is_some()
        {
            return Ok(());
        }
        let equiv_type = Expr::pi(
            BinderInfo::Default,
            c.raw.clone(),
            Expr::pi(BinderInfo::Default, c.raw.clone(), c.prop.clone()),
        );
        let equiv_value = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(c.raw.clone());
            let (q_id, q) = b.fresh_local(c.raw.clone());
            // num p * ofNat (effDenom q)  =  num q * ofNat (effDenom p)
            let lhs = c.mul(c.num(p.clone()), c.eff(q.clone()));
            let rhs = c.mul(c.num(q.clone()), c.eff(p.clone()));
            let body = c.eq_int_ty(lhs, rhs);
            let e = b.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), body);
            let e = b.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("Rat.Raw.Equiv"),
            level_params: vec![],
            type_: equiv_type,
            value: equiv_value,
            is_reducible: true,
        })
    }

    /// Step 3 — prove `Qat.Raw.Equiv` is an equivalence (refl / symm / trans),
    /// all as checked `Declaration::Theorem`s.
    fn register_rat_raw_equiv_equivalence(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        // ── refl : ∀ p, Equiv p p ────────────────────────────────────────────
        // Equiv p p ≡ Eq Int (num p * eff p) (num p * eff p), closed by Eq.refl.
        if self
            .get_const(&Name::from_string("Rat.Raw.Equiv.refl"))
            .is_none()
        {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(c.raw.clone());
                let goal = c.equiv(p.clone(), p.clone());
                let e = b.mk_pi(p_id, BinderInfo::Default, c.raw.clone(), goal);
                b.finish(e)
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(c.raw.clone());
                // Eq.refl Int (num p * eff p) : Eq (..) (..) ≡ Equiv p p (def-eq).
                let side = c.mul(c.num(p.clone()), c.eff(p.clone()));
                let body = c.refl_int(side);
                let e = b.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), body);
                b.finish(e)
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Rat.Raw.Equiv.refl"),
                level_params: vec![],
                type_: ty,
                value,
            })?;
        }

        // ── symm : ∀ p q, Equiv p q → Equiv q p ──────────────────────────────
        // Equiv p q ≡ Eq A B ; Equiv q p ≡ Eq B A ; close with Eq.symm.
        if self
            .get_const(&Name::from_string("Rat.Raw.Equiv.symm"))
            .is_none()
        {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(c.raw.clone());
                let (q_id, q) = b.fresh_local(c.raw.clone());
                let hyp = c.equiv(p.clone(), q.clone());
                let goal = c.equiv(q.clone(), p.clone());
                let (h_id, _h) = b.fresh_local(hyp.clone());
                let e = b.mk_pi(h_id, BinderInfo::Default, hyp, goal);
                let e = b.mk_pi(q_id, BinderInfo::Default, c.raw.clone(), e);
                let e = b.mk_pi(p_id, BinderInfo::Default, c.raw.clone(), e);
                b.finish(e)
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(c.raw.clone());
                let (q_id, q) = b.fresh_local(c.raw.clone());
                let hyp = c.equiv(p.clone(), q.clone());
                let (h_id, h) = b.fresh_local(hyp.clone());
                // A := num p * eff q ; B := num q * eff p.
                let a = c.mul(c.num(p.clone()), c.eff(q.clone()));
                let bb = c.mul(c.num(q.clone()), c.eff(p.clone()));
                // h : Eq A B ; Eq.symm gives Eq B A ≡ Equiv q p.
                let body = c.symm_int(a, bb, h);
                let e = b.mk_lam(h_id, BinderInfo::Default, hyp, body);
                let e = b.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), e);
                let e = b.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Rat.Raw.Equiv.symm"),
                level_params: vec![],
                type_: ty,
                value,
            })?;
        }

        // ── trans : ∀ p q r, Equiv p q → Equiv q r → Equiv p r (THE HARD ONE) ─
        self.register_rat_raw_equiv_trans(c)?;
        Ok(())
    }

    /// `Qat.Raw.Equiv.trans : ∀ p q r, Equiv p q → Equiv q r → Equiv p r`.
    ///
    /// Write `E x := Int.ofNat (Qat.Raw.effDenom x)` and `nx := num x`. Then:
    ///   - `h1 : np·Eq = nq·Ep`,
    ///   - `h2 : nq·Er = nr·Eq`,
    ///   - goal : `np·Er = nr·Ep`.
    ///
    /// `Eq` is definitionally `Int.ofNat (Nat.succ (Nat.pred (denom q)))`, i.e.
    /// `ofNat (Nat.succ k)` with `k := Nat.pred (denom q)` — exactly the
    /// POSITIVE factor that `Int.mul_left_cancel_ofNat_succ` cancels.
    ///
    /// Multiply the goal through by `Eq` and rearrange to expose `Eq·X = Eq·Y`:
    ///   `Eq·(np·Er) = (np·Eq)·Er`  [comm+assoc]
    ///              `= (nq·Ep)·Er`  [h1 under ·Er]
    ///              `= (nq·Er)·Ep`  [rearrange]
    ///              `= (nr·Eq)·Ep`  [h2 under ·Ep]
    ///              `= Eq·(nr·Ep)`  [rearrange]
    /// then cancel `Eq` on the left.
    fn register_rat_raw_equiv_trans(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("Rat.Raw.Equiv.trans"))
            .is_some()
        {
            return Ok(());
        }

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(c.raw.clone());
            let (q_id, q) = b.fresh_local(c.raw.clone());
            let (r_id, r) = b.fresh_local(c.raw.clone());
            let h1 = c.equiv(p.clone(), q.clone());
            let h2 = c.equiv(q.clone(), r.clone());
            let goal = c.equiv(p.clone(), r.clone());
            let (h1_id, _h1) = b.fresh_local(h1.clone());
            let (h2_id, _h2) = b.fresh_local(h2.clone());
            let e = b.mk_pi(h2_id, BinderInfo::Default, h2, goal);
            let e = b.mk_pi(h1_id, BinderInfo::Default, h1, e);
            let e = b.mk_pi(r_id, BinderInfo::Default, c.raw.clone(), e);
            let e = b.mk_pi(q_id, BinderInfo::Default, c.raw.clone(), e);
            let e = b.mk_pi(p_id, BinderInfo::Default, c.raw.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(c.raw.clone());
            let (q_id, q) = b.fresh_local(c.raw.clone());
            let (r_id, r) = b.fresh_local(c.raw.clone());
            let h1_ty = c.equiv(p.clone(), q.clone());
            let h2_ty = c.equiv(q.clone(), r.clone());
            let (h1_id, h1) = b.fresh_local(h1_ty.clone());
            let (h2_id, h2) = b.fresh_local(h2_ty.clone());

            let np = c.num(p.clone());
            let nq = c.num(q.clone());
            let nr = c.num(r.clone());
            let ep = c.eff(p.clone());
            // `eq_factor` is the positive factor we cancel. It is
            // `Int.ofNat (effDenom q)` ≡ `Int.ofNat (Nat.succ (Nat.pred (denom q)))`.
            let eq_factor = c.eff(q.clone());
            let er = c.eff(r.clone());
            // `pred (denom q)` — the `n` in `Int.mul_left_cancel_ofNat_succ n …`.
            let k_q = Expr::app(
                c.nat_pred.clone(),
                Expr::app(c.raw_denom.clone(), q.clone()),
            );

            // Helper to build `f := fun w => w * z` for congrArg.
            let mul_right = |z: Expr| -> Expr {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (w_id, w) = ch.fresh_local(c.int.clone());
                let body = c.mul(w, z);
                let lam = ch.mk_lam(w_id, BinderInfo::Default, c.int.clone(), body);
                ch.finish_child(lam)
            };

            // ---- Build the chain proving  eq·(np·er) = eq·(nr·ep)  ----
            // X := np·er, Y := nr·ep, goal-of-cancellation: eq·X = eq·Y.
            let np_er = c.mul(np.clone(), er.clone());
            let nr_ep = c.mul(nr.clone(), ep.clone());

            // s0 : eq·(np·er) = (eq·np)·er          [mul_assoc eq np er, symm]
            let eq_np = c.mul(eq_factor.clone(), np.clone());
            let eq_np_er = c.mul(eq_np.clone(), er.clone());
            let eq_x = c.mul(eq_factor.clone(), np_er.clone());
            let s0 = c.symm_int(
                eq_np_er.clone(),
                eq_x.clone(),
                c.mul_assoc(eq_factor.clone(), np.clone(), er.clone()),
            );

            // s1 : (eq·np)·er = (np·eq)·er          [congrArg (·*er) (mul_comm eq np)]
            let np_eq = c.mul(np.clone(), eq_factor.clone());
            let np_eq_er = c.mul(np_eq.clone(), er.clone());
            let s1 = c.congr_arg(
                eq_np.clone(),
                np_eq.clone(),
                mul_right(er.clone()),
                c.mul_comm(eq_factor.clone(), np.clone()),
            );

            // s2 : (np·eq)·er = (nq·ep)·er          [congrArg (·*er) h1]
            //   h1 : np·eq = nq·ep   (Equiv p q ≡ Eq (np·eq) (nq·ep))
            let nq_ep = c.mul(nq.clone(), ep.clone());
            let nq_ep_er = c.mul(nq_ep.clone(), er.clone());
            let s2 = c.congr_arg(
                np_eq.clone(),
                nq_ep.clone(),
                mul_right(er.clone()),
                h1.clone(),
            );

            // s3 : (nq·ep)·er = (nq·er)·ep          [rearrange via assoc/comm]
            //   (nq·ep)·er = nq·(ep·er) = nq·(er·ep) = (nq·er)·ep
            let nq_er = c.mul(nq.clone(), er.clone());
            let nq_er_ep = c.mul(nq_er.clone(), ep.clone());
            let s3 = {
                // a1 : (nq·ep)·er = nq·(ep·er)       [mul_assoc nq ep er]
                let ep_er = c.mul(ep.clone(), er.clone());
                let nq_eper = c.mul(nq.clone(), ep_er.clone());
                let a1 = c.mul_assoc(nq.clone(), ep.clone(), er.clone());
                // f := fun w => nq * w
                let mul_left_nq = {
                    let mut ch = EnvDeclBuilder::child_of(&b);
                    let (w_id, w) = ch.fresh_local(c.int.clone());
                    let body = c.mul(nq.clone(), w);
                    let lam = ch.mk_lam(w_id, BinderInfo::Default, c.int.clone(), body);
                    ch.finish_child(lam)
                };
                // a2 : nq·(ep·er) = nq·(er·ep)       [congrArg (nq*·) (mul_comm ep er)]
                let er_ep = c.mul(er.clone(), ep.clone());
                let nq_erep = c.mul(nq.clone(), er_ep.clone());
                let a2 = c.congr_arg(
                    ep_er.clone(),
                    er_ep.clone(),
                    mul_left_nq,
                    c.mul_comm(ep.clone(), er.clone()),
                );
                // a3 : nq·(er·ep) = (nq·er)·ep       [mul_assoc nq er ep, symm]
                let a3 = c.symm_int(
                    nq_er_ep.clone(),
                    nq_erep.clone(),
                    c.mul_assoc(nq.clone(), er.clone(), ep.clone()),
                );
                // chain a1; a2; a3
                let t12 = c.trans_int(nq_ep_er.clone(), nq_eper.clone(), nq_erep.clone(), a1, a2);
                c.trans_int(nq_ep_er.clone(), nq_erep.clone(), nq_er_ep.clone(), t12, a3)
            };

            // s4 : (nq·er)·ep = (nr·eq)·ep          [congrArg (·*ep) h2]
            //   h2 : nq·er = nr·eq   (Equiv q r ≡ Eq (nq·er) (nr·eq))
            let nr_eq = c.mul(nr.clone(), eq_factor.clone());
            let nr_eq_ep = c.mul(nr_eq.clone(), ep.clone());
            let s4 = c.congr_arg(
                nq_er.clone(),
                nr_eq.clone(),
                mul_right(ep.clone()),
                h2.clone(),
            );

            // s5 : (nr·eq)·ep = eq·(nr·ep)          [rearrange to expose eq on the left]
            //   (nr·eq)·ep = nr·(eq·ep) = nr·(ep·eq) ... hmm, we want eq·(nr·ep).
            //   Simpler: (nr·eq)·ep = (eq·nr)·ep    [congrArg (·*ep)(mul_comm nr eq)]
            //                       = eq·(nr·ep)    [mul_assoc eq nr ep]
            let eq_nr = c.mul(eq_factor.clone(), nr.clone());
            let eq_nr_ep = c.mul(eq_nr.clone(), ep.clone());
            let eq_y = c.mul(eq_factor.clone(), nr_ep.clone());
            let s5 = {
                let b1 = c.congr_arg(
                    nr_eq.clone(),
                    eq_nr.clone(),
                    mul_right(ep.clone()),
                    c.mul_comm(nr.clone(), eq_factor.clone()),
                );
                let b2 = c.mul_assoc(eq_factor.clone(), nr.clone(), ep.clone());
                c.trans_int(nr_eq_ep.clone(), eq_nr_ep.clone(), eq_y.clone(), b1, b2)
            };

            // Chain s0..s5 :  eq·(np·er) = eq·(nr·ep).
            //   eq·X = (eq·np)·er = (np·eq)·er = (nq·ep)·er = (nq·er)·ep
            //        = (nr·eq)·ep = eq·Y.
            let c0 = c.trans_int(eq_x.clone(), eq_np_er.clone(), np_eq_er.clone(), s0, s1);
            let c1 = c.trans_int(eq_x.clone(), np_eq_er.clone(), nq_ep_er.clone(), c0, s2);
            let c2 = c.trans_int(eq_x.clone(), nq_ep_er.clone(), nq_er_ep.clone(), c1, s3);
            let c3 = c.trans_int(eq_x.clone(), nq_er_ep.clone(), nr_eq_ep.clone(), c2, s4);
            let chain = c.trans_int(eq_x.clone(), nr_eq_ep.clone(), eq_y.clone(), c3, s5);

            // Cancel the positive left factor `eq = ofNat (succ k_q)`:
            //   Int.mul_left_cancel_ofNat_succ k_q X Y chain : Eq X Y ≡ Equiv p r.
            let body = Expr::apps(
                c.int_mul_left_cancel.clone(),
                [k_q, np_er.clone(), nr_ep.clone(), chain],
            );

            let e = b.mk_lam(h2_id, BinderInfo::Default, h2_ty, body);
            let e = b.mk_lam(h1_id, BinderInfo::Default, h1_ty, e);
            let e = b.mk_lam(r_id, BinderInfo::Default, c.raw.clone(), e);
            let e = b.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), e);
            let e = b.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Rat.Raw.Equiv.trans"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }
    /// 4. The quotient itself + its constructor and the two units.
    ///   - `Qat := @Quot.{1} Qat.Raw Qat.Raw.Equiv` (a Definition).
    ///   - `Qat.mk n d := @Quot.mk Qat.Raw Qat.Raw.Equiv (Qat.Raw.mk n d)`.
    ///   - `Qat.zero := Qat.mk Int.zero 1`, `Qat.one := Qat.mk (Int.ofNat 1) 1`.
    fn register_rat_quotient(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        // Qat : Type 0 := @Quot.{1} Qat.Raw Qat.Raw.Equiv
        if self.get_const(&Name::from_string("Rat")).is_none() {
            let ratq_type = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
            // @Quot.{1} Qat.Raw Qat.Raw.Equiv (α implicit, r explicit — passed
            // positionally as in data_types_multiset.rs).
            let ratq_value = Expr::apps(c.quot.clone(), [c.raw.clone(), c.raw_equiv.clone()]);
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Rat"),
                level_params: vec![],
                type_: ratq_type,
                value: ratq_value,
                is_reducible: true,
            })?;
        }

        // Qat.mk : Int → Nat → Qat := fun n d => Quot.mk _ Equiv (Qat.Raw.mk n d)
        if self.get_const(&Name::from_string("Rat.mk")).is_none() {
            let mk_type = Expr::pi(
                BinderInfo::Default,
                c.int.clone(),
                Expr::pi(BinderInfo::Default, c.nat.clone(), c.ratq.clone()),
            );
            let mk_value = {
                let mut b = EnvDeclBuilder::new();
                let (n_id, n) = b.fresh_local(c.int.clone());
                let (d_id, d) = b.fresh_local(c.nat.clone());
                let body = c.quot_mk(c.raw_mk(n.clone(), d.clone()));
                let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), body);
                let e = b.mk_lam(n_id, BinderInfo::Default, c.int.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Rat.mk"),
                level_params: vec![],
                type_: mk_type,
                value: mk_value,
                is_reducible: true,
            })?;
        }

        // Qat.zero : Qat := Qat.mk Int.zero 1
        let nat_one = Expr::app(c.nat_succ.clone(), c.nat_zero.clone());
        if self.get_const(&Name::from_string("Rat.zero")).is_none() {
            let zero_value = Expr::apps(c.ratq_mk.clone(), [c.int_zero.clone(), nat_one.clone()]);
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Rat.zero"),
                level_params: vec![],
                type_: c.ratq.clone(),
                value: zero_value,
                is_reducible: true,
            })?;
        }

        // Qat.one : Qat := Qat.mk (Int.ofNat 1) 1
        if self.get_const(&Name::from_string("Rat.one")).is_none() {
            let int_one = c.of_nat(nat_one.clone());
            let one_value = Expr::apps(c.ratq_mk.clone(), [int_one, nat_one.clone()]);
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Rat.one"),
                level_params: vec![],
                type_: c.ratq.clone(),
                value: one_value,
                is_reducible: true,
            })?;
        }

        Ok(())
    }
    /// Helper: `Qat.Int.mulMulMulComm : ∀ a b c d,
    ///     Eq (Int.mul (Int.mul a b) (Int.mul c d))
    ///        (Int.mul (Int.mul a c) (Int.mul b d))`.
    ///
    /// A 4-factor commutative-monoid shuffle, used by the `Qat.mul`
    /// well-definedness proof. Built from `Int.mul_assoc` / `Int.mul_comm`.
    fn register_rat_int_mul_mul_mul_comm(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.Int.mulMulMulComm");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.int.clone());
            let (bb_id, bb) = b.fresh_local(c.int.clone());
            let (cc_id, cc) = b.fresh_local(c.int.clone());
            let (d_id, d) = b.fresh_local(c.int.clone());
            let lhs = c.mul(c.mul(a.clone(), bb.clone()), c.mul(cc.clone(), d.clone()));
            let rhs = c.mul(c.mul(a.clone(), cc.clone()), c.mul(bb.clone(), d.clone()));
            let goal = c.eq_int_ty(lhs, rhs);
            let e = b.mk_pi(d_id, BinderInfo::Default, c.int.clone(), goal);
            let e = b.mk_pi(cc_id, BinderInfo::Default, c.int.clone(), e);
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.int.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.int.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.int.clone());
            let (bb_id, bb) = b.fresh_local(c.int.clone());
            let (cc_id, cc) = b.fresh_local(c.int.clone());
            let (d_id, d) = b.fresh_local(c.int.clone());

            // f := fun w => w * z (congrArg on the left factor).
            let mul_right = |z: Expr| -> Expr {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (w_id, w) = ch.fresh_local(c.int.clone());
                let body = c.mul(w, z);
                let lam = ch.mk_lam(w_id, BinderInfo::Default, c.int.clone(), body);
                ch.finish_child(lam)
            };
            // g := fun w => z * w (congrArg on the right factor).
            let _mul_left = |z: Expr| -> Expr {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (w_id, w) = ch.fresh_local(c.int.clone());
                let body = c.mul(z, w);
                let lam = ch.mk_lam(w_id, BinderInfo::Default, c.int.clone(), body);
                ch.finish_child(lam)
            };

            // We prove (a·b)·(c·d) = (a·c)·(b·d) through fully-left-associated
            // normal form ((a·b)·c)·d for both sides.
            let ab = c.mul(a.clone(), bb.clone());
            let cd = c.mul(cc.clone(), d.clone());
            let ac = c.mul(a.clone(), cc.clone());
            let bd = c.mul(bb.clone(), d.clone());

            // LHS = (a·b)·(c·d).
            // l1 : (a·b)·(c·d) = ((a·b)·c)·d        [mul_assoc (a·b) c d, symm]
            let ab_c = c.mul(ab.clone(), cc.clone());
            let ab_c_d = c.mul(ab_c.clone(), d.clone());
            let lhs = c.mul(ab.clone(), cd.clone());
            let l1 = c.symm_int(
                ab_c_d.clone(),
                lhs.clone(),
                c.mul_assoc(ab.clone(), cc.clone(), d.clone()),
            );
            // l2 : ((a·b)·c)·d = (a·(b·c))·d        [congrArg (·*d)(mul_assoc a b c)]
            let bc = c.mul(bb.clone(), cc.clone());
            let a_bc = c.mul(a.clone(), bc.clone());
            let a_bc_d = c.mul(a_bc.clone(), d.clone());
            let l2 = c.congr_arg(
                ab_c.clone(),
                a_bc.clone(),
                mul_right(d.clone()),
                c.mul_assoc(a.clone(), bb.clone(), cc.clone()),
            );
            // l3 : (a·(b·c))·d = (a·(c·b))·d        [congrArg ((a*·)·d)(mul_comm b c)]
            let cb = c.mul(cc.clone(), bb.clone());
            let a_cb = c.mul(a.clone(), cb.clone());
            let a_cb_d = c.mul(a_cb.clone(), d.clone());
            // fun w => (a * w) * d
            let f_a_w_d = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (w_id, w) = ch.fresh_local(c.int.clone());
                let body = c.mul(c.mul(a.clone(), w), d.clone());
                let lam = ch.mk_lam(w_id, BinderInfo::Default, c.int.clone(), body);
                ch.finish_child(lam)
            };
            let l3 = c.congr_arg(
                bc.clone(),
                cb.clone(),
                f_a_w_d,
                c.mul_comm(bb.clone(), cc.clone()),
            );
            // l4 : (a·(c·b))·d = ((a·c)·b)·d        [congrArg (·*d)(mul_assoc a c b, symm)]
            let ac_b = c.mul(ac.clone(), bb.clone());
            let ac_b_d = c.mul(ac_b.clone(), d.clone());
            let l4 = c.congr_arg(
                a_cb.clone(),
                ac_b.clone(),
                mul_right(d.clone()),
                c.symm_int(
                    ac_b.clone(),
                    a_cb.clone(),
                    c.mul_assoc(a.clone(), cc.clone(), bb.clone()),
                ),
            );
            // l5 : ((a·c)·b)·d = (a·c)·(b·d)        [mul_assoc (a·c) b d]
            let rhs = c.mul(ac.clone(), bd.clone());
            let l5 = c.mul_assoc(ac.clone(), bb.clone(), d.clone());

            // Chain l1..l5 : (a·b)·(c·d) = (a·c)·(b·d).
            let t1 = c.trans_int(lhs.clone(), ab_c_d.clone(), a_bc_d.clone(), l1, l2);
            let t2 = c.trans_int(lhs.clone(), a_bc_d.clone(), a_cb_d.clone(), t1, l3);
            let t3 = c.trans_int(lhs.clone(), a_cb_d.clone(), ac_b_d.clone(), t2, l4);
            let body = c.trans_int(lhs.clone(), ac_b_d.clone(), rhs.clone(), t3, l5);

            let e = b.mk_lam(d_id, BinderInfo::Default, c.int.clone(), body);
            let e = b.mk_lam(cc_id, BinderInfo::Default, c.int.clone(), e);
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.int.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.int.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// 5a. `Qat.mul : Qat → Qat → Qat`, a NESTED binary `Quot.lift`.
    ///
    /// The raw operation multiplies numerators and EFFECTIVE denominators:
    ///   `Raw.mul p q := Raw.mk (num p * num q) (effDenom p * effDenom q)`.
    ///
    /// MIGRATION NOTE: the task's literal `Nat.mul (denom p)(denom q)` is NOT
    /// well-defined w.r.t. the `effDenom`-based `Equiv` on the pathological
    /// `denom = 0` representatives (e.g. `p = mk 1 0`, `q = mk 1 1 ≈ mk 2 2`
    /// gives `mul p (mk 1 1) = mk 1 0` but `mul p (mk 2 2) = mk 2 0`, and
    /// `mk 1 0 ̸≈ mk 2 0`). Multiplying the EFFECTIVE denominators (each a
    /// `Nat.succ _ ≥ 1`, so their product is again a `Nat.succ _` and equals
    /// the result's own `effDenom` DEFINITIONALLY) restores well-definedness:
    /// it is the cross-multiplication identity proved by the helper below.
    fn register_rat_q_mul(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("Rat.mul")).is_some() {
            return Ok(());
        }
        self.register_rat_int_mul_mul_mul_comm(c)?;

        // Local handles for the raw effDenom-as-Nat and the raw num.
        let raw_eff_nat = |x: Expr| Expr::app(c.raw_eff_denom.clone(), x);

        // `Raw.mul p q := Raw.mk (num p * num q) (effDenom p * effDenom q)`.
        let raw_mul = |p: &Expr, q: &Expr| -> Expr {
            let new_num = c.mul(c.num(p.clone()), c.num(q.clone()));
            let new_den = c.nmul(raw_eff_nat(p.clone()), raw_eff_nat(q.clone()));
            c.raw_mk(new_num, new_den)
        };
        // `Qat.mk-of-raw-mul` — the quotient class of `raw_mul p q`.
        let mk_mul = |p: &Expr, q: &Expr| -> Expr { c.quot_mk(raw_mul(p, q)) };

        let mul_type = Expr::pi(
            BinderInfo::Default,
            c.ratq.clone(),
            Expr::pi(BinderInfo::Default, c.ratq.clone(), c.ratq.clone()),
        );

        let mul_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let (bv_id, bv) = b.fresh_local(c.ratq.clone());

            // ---- Outer lift function:  fun (p : Raw) => innerLift_p bv ----
            let outer_f = {
                let mut bo = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bo.fresh_local(c.raw.clone());

                // Inner lift over the SECOND argument `bv`.
                //   g_p := fun (q : Raw) => Qat.mk-of-raw-mul p q
                let inner_f = {
                    let mut bi = EnvDeclBuilder::child_of(&bo);
                    let (q_id, q) = bi.fresh_local(c.raw.clone());
                    let body = mk_mul(&p, &q);
                    let lam = bi.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), body);
                    bi.finish_child(lam)
                };
                // Inner respect: ∀ q q', Equiv q q' → Eq Qat (g_p q) (g_p q').
                let inner_h = {
                    let mut bi = EnvDeclBuilder::child_of(&bo);
                    let (q_id, q) = bi.fresh_local(c.raw.clone());
                    let (q2_id, q2) = bi.fresh_local(c.raw.clone());
                    let hyp = c.equiv(q.clone(), q2.clone());
                    let (hq_id, hq) = bi.fresh_local(hyp.clone());
                    // hq : Equiv q q' ≡ Eq (nq·eq2) (nq2·eq). Build the products
                    // Equiv proof, then Quot.sound.
                    let eqv = c.mul_cross_right(
                        &bi,
                        &c.num(p.clone()),
                        &c.num(q.clone()),
                        &c.eff(p.clone()),
                        &c.eff(q.clone()),
                        &c.num(q2.clone()),
                        &c.eff(q2.clone()),
                        &hq,
                    );
                    let sound = c.quot_sound(raw_mul(&p, &q), raw_mul(&p, &q2), eqv);
                    let lam = bi.mk_lam(hq_id, BinderInfo::Default, hyp, sound);
                    let lam = bi.mk_lam(q2_id, BinderInfo::Default, c.raw.clone(), lam);
                    let lam = bi.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), lam);
                    bi.finish_child(lam)
                };
                // innerLift_p bv := @Quot.lift Raw Equiv Qat g_p inner_h bv
                let body = Expr::apps(
                    c.quot_lift.clone(),
                    [
                        c.raw.clone(),
                        c.raw_equiv.clone(),
                        c.ratq.clone(),
                        inner_f,
                        inner_h,
                        bv.clone(),
                    ],
                );
                let lam = bo.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), body);
                bo.finish_child(lam)
            };

            // ---- Outer respect: ∀ p p', Equiv p p' →
            //          Eq Qat (innerLift_p bv) (innerLift_p' bv).  ----
            // Discharged by `Quot.ind` on the (fixed) second operand `bv`: for a
            // representative `bv = Quot.mk q`, both inner lifts ι-reduce to
            // `Qat.mk-of-raw-mul p q` / `… p' q`, closed by `Quot.sound` of the
            // FIRST-argument cross-multiplication Equiv.
            let outer_h = {
                let mut bh = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bh.fresh_local(c.raw.clone());
                let (p2_id, p2) = bh.fresh_local(c.raw.clone());
                let hyp = c.equiv(p.clone(), p2.clone());
                let (hp_id, hp) = bh.fresh_local(hyp.clone());

                // innerLift over an arbitrary Qat `bb`, for a fixed first rep.
                let inner_lift = |first: &Expr, bb: &Expr| -> Expr {
                    // g_first := fun q => mk_mul first q   (matches outer_f's inner_f)
                    let g = {
                        let mut bi = EnvDeclBuilder::child_of(&bh);
                        let (q_id, q) = bi.fresh_local(c.raw.clone());
                        let body = mk_mul(first, &q);
                        let lam = bi.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), body);
                        bi.finish_child(lam)
                    };
                    let h = {
                        let mut bi = EnvDeclBuilder::child_of(&bh);
                        let (q_id, q) = bi.fresh_local(c.raw.clone());
                        let (q2_id, q2) = bi.fresh_local(c.raw.clone());
                        let hh = c.equiv(q.clone(), q2.clone());
                        let (hq_id, hq) = bi.fresh_local(hh.clone());
                        let eqv = c.mul_cross_right(
                            &bi,
                            &c.num(first.clone()),
                            &c.num(q.clone()),
                            &c.eff(first.clone()),
                            &c.eff(q.clone()),
                            &c.num(q2.clone()),
                            &c.eff(q2.clone()),
                            &hq,
                        );
                        let sound = c.quot_sound(raw_mul(first, &q), raw_mul(first, &q2), eqv);
                        let lam = bi.mk_lam(hq_id, BinderInfo::Default, hh, sound);
                        let lam = bi.mk_lam(q2_id, BinderInfo::Default, c.raw.clone(), lam);
                        let lam = bi.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), lam);
                        bi.finish_child(lam)
                    };
                    Expr::apps(
                        c.quot_lift.clone(),
                        [
                            c.raw.clone(),
                            c.raw_equiv.clone(),
                            c.ratq.clone(),
                            g,
                            h,
                            bb.clone(),
                        ],
                    )
                };

                // Motive β := fun bb => Eq Qat (inner_lift p bb) (inner_lift p' bb).
                let beta = {
                    let mut bm = EnvDeclBuilder::child_of(&bh);
                    let (bb_id, bb) = bm.fresh_local(c.ratq.clone());
                    let lhs = inner_lift(&p, &bb);
                    let rhs = inner_lift(&p2, &bb);
                    let body = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, rhs]);
                    let lam = bm.mk_lam(bb_id, BinderInfo::Default, c.ratq.clone(), body);
                    bm.finish_child(lam)
                };

                // Quot.ind minor: fun (q : Raw) => proof for bb = Quot.mk q.
                //   inner_lift p (mk q) ≡ mk_mul p q ; inner_lift p' (mk q) ≡ mk_mul p' q.
                //   Goal: Eq Qat (mk_mul p q) (mk_mul p' q) — Quot.sound + first-arg cross.
                let minor = {
                    let mut bn = EnvDeclBuilder::child_of(&bh);
                    let (q_id, q) = bn.fresh_local(c.raw.clone());
                    // First-arg cross-mult: Equiv (raw_mul p q) (raw_mul p' q).
                    //   ((np·nq)·(ep'·eq)) = ((np'·nq)·(ep·eq))   from hp: np·ep' = np'·ep.
                    let eqv = c.mul_cross_left(
                        &bn,
                        &c.num(p.clone()),
                        &c.eff(p.clone()),
                        &c.num(q.clone()),
                        &c.eff(q.clone()),
                        &c.num(p2.clone()),
                        &c.eff(p2.clone()),
                        &hp,
                    );
                    let sound = c.quot_sound(raw_mul(&p, &q), raw_mul(&p2, &q), eqv);
                    let lam = bn.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), sound);
                    bn.finish_child(lam)
                };

                // @Quot.ind Raw Equiv beta minor bv : beta bv
                //   ≡ Eq Qat (inner_lift p bv) (inner_lift p' bv).
                let ind = Expr::apps(
                    c.quot_ind.clone(),
                    [c.raw.clone(), c.raw_equiv.clone(), beta, minor, bv.clone()],
                );
                let lam = bh.mk_lam(hp_id, BinderInfo::Default, hyp, ind);
                let lam = bh.mk_lam(p2_id, BinderInfo::Default, c.raw.clone(), lam);
                let lam = bh.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), lam);
                bh.finish_child(lam)
            };

            // Qat.mul a b := @Quot.lift Raw Equiv Qat outer_f outer_h a
            let body = Expr::apps(
                c.quot_lift.clone(),
                [
                    c.raw.clone(),
                    c.raw_equiv.clone(),
                    c.ratq.clone(),
                    outer_f,
                    outer_h,
                    a.clone(),
                ],
            );
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.ratq.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Rat.mul"),
            level_params: vec![],
            type_: mul_type,
            value: mul_value,
            is_reducible: true,
        })
    }

    /// 5a'. `Qat.neg : Qat → Qat`, a unary `Quot.lift`.
    ///
    /// `Raw.neg p := Raw.mk (Int.neg (num p)) (effDenom p)` — the negated
    /// numerator over the (already-positive) EFFECTIVE denominator, so
    /// `effDenom (Raw.neg p) ≡ effDenom p` DEFINITIONALLY (`pred (succ k) = k`).
    /// Well-definedness: from `hp : Equiv p p'` (`np·Ep' = np'·Ep`) derive
    /// `Equiv (Raw.neg p)(Raw.neg p')` (`(neg np)·Ep' = (neg np')·Ep`) via
    /// `Int.neg_mul_left` + `congrArg Int.neg hp`, then `Quot.sound`.
    fn register_rat_q_neg(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("Rat.neg")).is_some() {
            return Ok(());
        }
        // `Raw.neg p := Raw.mk (Int.neg (num p)) (effDenom p)`.
        let raw_neg = |p: &Expr| -> Expr {
            c.raw_mk(
                c.neg(c.num(p.clone())),
                Expr::app(c.raw_eff_denom.clone(), p.clone()),
            )
        };
        let neg_type = Expr::pi(BinderInfo::Default, c.ratq.clone(), c.ratq.clone());
        let neg_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());

            // f := fun (p : Raw) => Quot.mk (Raw.neg p)
            let lift_f = {
                let mut bi = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bi.fresh_local(c.raw.clone());
                let body = c.quot_mk(raw_neg(&p));
                let lam = bi.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), body);
                bi.finish_child(lam)
            };
            // h := fun p p' hp => Quot.sound (Raw.neg p)(Raw.neg p') eqv
            let lift_h = {
                let mut bi = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bi.fresh_local(c.raw.clone());
                let (p2_id, p2) = bi.fresh_local(c.raw.clone());
                let hyp = c.equiv(p.clone(), p2.clone());
                let (hp_id, hp) = bi.fresh_local(hyp.clone());

                let np = c.num(p.clone());
                let np2 = c.num(p2.clone());
                let ep = c.eff(p.clone());
                let ep2 = c.eff(p2.clone());
                // goal : (neg np)·ep2 = (neg np2)·ep.
                let lhs = c.mul(c.neg(np.clone()), ep2.clone());
                let rhs = c.mul(c.neg(np2.clone()), ep.clone());
                // mid1 := neg (np·ep2) ; mid2 := neg (np2·ep).
                let np_ep2 = c.mul(np.clone(), ep2.clone());
                let np2_ep = c.mul(np2.clone(), ep.clone());
                let mid1 = c.neg(np_ep2.clone());
                let mid2 = c.neg(np2_ep.clone());
                // s1 : (neg np)·ep2 = neg (np·ep2)   [symm (neg_mul_left np ep2)]
                let s1 = c.symm_int(
                    mid1.clone(),
                    lhs.clone(),
                    c.neg_mul_left(np.clone(), ep2.clone()),
                );
                // s2 : neg (np·ep2) = neg (np2·ep)   [congrArg Int.neg hp]
                let neg_fn = {
                    let mut ch = EnvDeclBuilder::child_of(&bi);
                    let (w_id, w) = ch.fresh_local(c.int.clone());
                    let body = c.neg(w);
                    let lam = ch.mk_lam(w_id, BinderInfo::Default, c.int.clone(), body);
                    ch.finish_child(lam)
                };
                let s2 = c.congr_arg(np_ep2.clone(), np2_ep.clone(), neg_fn, hp.clone());
                // s3 : neg (np2·ep) = (neg np2)·ep   [neg_mul_left np2 ep]
                let s3 = c.neg_mul_left(np2.clone(), ep.clone());
                let t1 = c.trans_int(lhs.clone(), mid1.clone(), mid2.clone(), s1, s2);
                let eqv = c.trans_int(lhs, mid2, rhs, t1, s3);

                let sound = c.quot_sound(raw_neg(&p), raw_neg(&p2), eqv);
                let lam = bi.mk_lam(hp_id, BinderInfo::Default, hyp, sound);
                let lam = bi.mk_lam(p2_id, BinderInfo::Default, c.raw.clone(), lam);
                let lam = bi.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), lam);
                bi.finish_child(lam)
            };
            let body = Expr::apps(
                c.quot_lift.clone(),
                [
                    c.raw.clone(),
                    c.raw_equiv.clone(),
                    c.ratq.clone(),
                    lift_f,
                    lift_h,
                    a.clone(),
                ],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("Rat.neg"),
            level_params: vec![],
            type_: neg_type,
            value: neg_value,
            is_reducible: true,
        })
    }

    /// 5a''. `Qat.add : Qat → Qat → Qat`, a NESTED binary `Quot.lift` (same
    /// shape as `Qat.mul`).
    ///
    /// `Raw.add p q := Raw.mk (num p · E q + num q · E p) (effDenom p · effDenom q)`
    /// where `E x := Int.ofNat (effDenom x)`. The numerator uses the EFFECTIVE
    /// denominators (each `Nat.succ _ ≥ 1`) so well-definedness holds on the
    /// pathological `denom = 0` reps; the result `effDenom` reduces
    /// DEFINITIONALLY to `effDenom p · effDenom q`. Both respect obligations are
    /// discharged by `Quot.sound` + the additive cross-multiplication Equiv
    /// (`add_cross_right` / `add_cross_left`), with the FIRST-argument respect
    /// routed through `Quot.ind` on the fixed second operand (PoC `Qat.mul`
    /// trick).
    fn register_rat_q_add(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("Rat.add")).is_some() {
            return Ok(());
        }

        let raw_eff_nat = |x: Expr| Expr::app(c.raw_eff_denom.clone(), x);
        // `Raw.add p q := Raw.mk (np·Eq + nq·Ep) (effDenom p · effDenom q)`.
        let raw_add = |p: &Expr, q: &Expr| -> Expr {
            let np_eq = c.mul(c.num(p.clone()), c.eff(q.clone()));
            let nq_ep = c.mul(c.num(q.clone()), c.eff(p.clone()));
            let new_num = c.add(np_eq, nq_ep);
            let new_den = c.nmul(raw_eff_nat(p.clone()), raw_eff_nat(q.clone()));
            c.raw_mk(new_num, new_den)
        };
        let mk_add = |p: &Expr, q: &Expr| -> Expr { c.quot_mk(raw_add(p, q)) };

        let add_type = Expr::pi(
            BinderInfo::Default,
            c.ratq.clone(),
            Expr::pi(BinderInfo::Default, c.ratq.clone(), c.ratq.clone()),
        );

        let add_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let (bv_id, bv) = b.fresh_local(c.ratq.clone());

            // Outer lift: fun (p : Raw) => innerLift_p bv.
            let outer_f = {
                let mut bo = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bo.fresh_local(c.raw.clone());
                let inner_f = {
                    let mut bi = EnvDeclBuilder::child_of(&bo);
                    let (q_id, q) = bi.fresh_local(c.raw.clone());
                    let body = mk_add(&p, &q);
                    let lam = bi.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), body);
                    bi.finish_child(lam)
                };
                let inner_h = {
                    let mut bi = EnvDeclBuilder::child_of(&bo);
                    let (q_id, q) = bi.fresh_local(c.raw.clone());
                    let (q2_id, q2) = bi.fresh_local(c.raw.clone());
                    let hyp = c.equiv(q.clone(), q2.clone());
                    let (hq_id, hq) = bi.fresh_local(hyp.clone());
                    let eqv = c.add_cross_right(
                        &bi,
                        &c.num(p.clone()),
                        &c.num(q.clone()),
                        &c.eff(p.clone()),
                        &c.eff(q.clone()),
                        &c.num(q2.clone()),
                        &c.eff(q2.clone()),
                        &hq,
                    );
                    let sound = c.quot_sound(raw_add(&p, &q), raw_add(&p, &q2), eqv);
                    let lam = bi.mk_lam(hq_id, BinderInfo::Default, hyp, sound);
                    let lam = bi.mk_lam(q2_id, BinderInfo::Default, c.raw.clone(), lam);
                    let lam = bi.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), lam);
                    bi.finish_child(lam)
                };
                let body = Expr::apps(
                    c.quot_lift.clone(),
                    [
                        c.raw.clone(),
                        c.raw_equiv.clone(),
                        c.ratq.clone(),
                        inner_f,
                        inner_h,
                        bv.clone(),
                    ],
                );
                let lam = bo.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), body);
                bo.finish_child(lam)
            };

            // Outer respect via Quot.ind on bv.
            let outer_h = {
                let mut bh = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bh.fresh_local(c.raw.clone());
                let (p2_id, p2) = bh.fresh_local(c.raw.clone());
                let hyp = c.equiv(p.clone(), p2.clone());
                let (hp_id, hp) = bh.fresh_local(hyp.clone());

                let inner_lift = |first: &Expr, bb: &Expr| -> Expr {
                    let g = {
                        let mut bi = EnvDeclBuilder::child_of(&bh);
                        let (q_id, q) = bi.fresh_local(c.raw.clone());
                        let body = mk_add(first, &q);
                        let lam = bi.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), body);
                        bi.finish_child(lam)
                    };
                    let h = {
                        let mut bi = EnvDeclBuilder::child_of(&bh);
                        let (q_id, q) = bi.fresh_local(c.raw.clone());
                        let (q2_id, q2) = bi.fresh_local(c.raw.clone());
                        let hh = c.equiv(q.clone(), q2.clone());
                        let (hq_id, hq) = bi.fresh_local(hh.clone());
                        let eqv = c.add_cross_right(
                            &bi,
                            &c.num(first.clone()),
                            &c.num(q.clone()),
                            &c.eff(first.clone()),
                            &c.eff(q.clone()),
                            &c.num(q2.clone()),
                            &c.eff(q2.clone()),
                            &hq,
                        );
                        let sound = c.quot_sound(raw_add(first, &q), raw_add(first, &q2), eqv);
                        let lam = bi.mk_lam(hq_id, BinderInfo::Default, hh, sound);
                        let lam = bi.mk_lam(q2_id, BinderInfo::Default, c.raw.clone(), lam);
                        let lam = bi.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), lam);
                        bi.finish_child(lam)
                    };
                    Expr::apps(
                        c.quot_lift.clone(),
                        [
                            c.raw.clone(),
                            c.raw_equiv.clone(),
                            c.ratq.clone(),
                            g,
                            h,
                            bb.clone(),
                        ],
                    )
                };

                let beta = {
                    let mut bm = EnvDeclBuilder::child_of(&bh);
                    let (bb_id, bb) = bm.fresh_local(c.ratq.clone());
                    let lhs = inner_lift(&p, &bb);
                    let rhs = inner_lift(&p2, &bb);
                    let body = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, rhs]);
                    let lam = bm.mk_lam(bb_id, BinderInfo::Default, c.ratq.clone(), body);
                    bm.finish_child(lam)
                };

                let minor = {
                    let mut bn = EnvDeclBuilder::child_of(&bh);
                    let (q_id, q) = bn.fresh_local(c.raw.clone());
                    let eqv = c.add_cross_left(
                        &bn,
                        &c.num(p.clone()),
                        &c.eff(p.clone()),
                        &c.num(q.clone()),
                        &c.eff(q.clone()),
                        &c.num(p2.clone()),
                        &c.eff(p2.clone()),
                        &hp,
                    );
                    let sound = c.quot_sound(raw_add(&p, &q), raw_add(&p2, &q), eqv);
                    let lam = bn.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), sound);
                    bn.finish_child(lam)
                };

                let ind = Expr::apps(
                    c.quot_ind.clone(),
                    [c.raw.clone(), c.raw_equiv.clone(), beta, minor, bv.clone()],
                );
                let lam = bh.mk_lam(hp_id, BinderInfo::Default, hyp, ind);
                let lam = bh.mk_lam(p2_id, BinderInfo::Default, c.raw.clone(), lam);
                let lam = bh.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), lam);
                bh.finish_child(lam)
            };

            let body = Expr::apps(
                c.quot_lift.clone(),
                [
                    c.raw.clone(),
                    c.raw_equiv.clone(),
                    c.ratq.clone(),
                    outer_f,
                    outer_h,
                    a.clone(),
                ],
            );
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.ratq.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Rat.add"),
            level_params: vec![],
            type_: add_type,
            value: add_value,
            is_reducible: true,
        })
    }

    /// 5b. `Qat.le : Qat → Qat → Prop`, a NESTED binary `Quot.lift` into `Prop`.
    ///
    /// Lifts `Raw.le p q := Int.le (num p · eff q) (num q · eff p)`. Both
    /// respect obligations are `@Eq Prop`, discharged by `propext` of the two
    /// implications, each proved by `Int.le_cross_trans` (the cross-multiply
    /// order-monotonicity already registered for `Rat.le_trans`).
    fn register_rat_q_le(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("Rat.le")).is_some() {
            return Ok(());
        }

        let le_type = Expr::pi(
            BinderInfo::Default,
            c.ratq.clone(),
            Expr::pi(BinderInfo::Default, c.ratq.clone(), c.prop.clone()),
        );

        let le_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let (bv_id, bv) = b.fresh_local(c.ratq.clone());

            // innerLift over an arbitrary Qat `bb`, for a fixed first rep
            // `first`. `parent` MUST be a builder whose context tracks the
            // `first` fvar, so the child lifts leave it free for the enclosing
            // `mk_lam` to abstract.
            //   g_first := fun q => Raw.le first q   (Prop-valued)
            //   h       := fun q q' hq => propext … (le_respects_right)
            let inner_lift = |parent: &EnvDeclBuilder, first: &Expr, bb: &Expr| -> Expr {
                let g = {
                    let mut bi = EnvDeclBuilder::child_of(parent);
                    let (q_id, q) = bi.fresh_local(c.raw.clone());
                    let body = c.raw_le(first, &q);
                    let lam = bi.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), body);
                    bi.finish_child(lam)
                };
                let h = {
                    let mut bi = EnvDeclBuilder::child_of(parent);
                    let (q_id, q) = bi.fresh_local(c.raw.clone());
                    let (q2_id, q2) = bi.fresh_local(c.raw.clone());
                    let hh = c.equiv(q.clone(), q2.clone());
                    let (hq_id, hq) = bi.fresh_local(hh.clone());
                    let body = c.le_respects_right(&bi, first, &q, &q2, &hq);
                    let lam = bi.mk_lam(hq_id, BinderInfo::Default, hh, body);
                    let lam = bi.mk_lam(q2_id, BinderInfo::Default, c.raw.clone(), lam);
                    let lam = bi.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), lam);
                    bi.finish_child(lam)
                };
                Expr::apps(
                    c.quot_lift_prop.clone(),
                    [
                        c.raw.clone(),
                        c.raw_equiv.clone(),
                        c.prop.clone(),
                        g,
                        h,
                        bb.clone(),
                    ],
                )
            };

            // ---- Outer lift function: fun (p : Raw) => innerLift p bv ----
            let outer_f = {
                let mut bo = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bo.fresh_local(c.raw.clone());
                let body = inner_lift(&bo, &p, &bv);
                let lam = bo.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), body);
                bo.finish_child(lam)
            };

            // ---- Outer respect via Quot.ind on bv ----
            //   β := fun bb => @Eq Prop (innerLift p bb) (innerLift p' bb)
            //   minor: for bb = mk q, both reduce to Raw.le p q / Raw.le p' q —
            //   closed by `le_respects_left` (propext).
            let outer_h = {
                let mut bh = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bh.fresh_local(c.raw.clone());
                let (p2_id, p2) = bh.fresh_local(c.raw.clone());
                let hyp = c.equiv(p.clone(), p2.clone());
                let (hp_id, hp) = bh.fresh_local(hyp.clone());

                let beta = {
                    let mut bm = EnvDeclBuilder::child_of(&bh);
                    let (bb_id, bb) = bm.fresh_local(c.ratq.clone());
                    let lhs = inner_lift(&bm, &p, &bb);
                    let rhs = inner_lift(&bm, &p2, &bb);
                    let body = Expr::apps(c.eq_ratq.clone(), [c.prop.clone(), lhs, rhs]);
                    let lam = bm.mk_lam(bb_id, BinderInfo::Default, c.ratq.clone(), body);
                    bm.finish_child(lam)
                };

                let minor = {
                    let mut bn = EnvDeclBuilder::child_of(&bh);
                    let (q_id, q) = bn.fresh_local(c.raw.clone());
                    let body = c.le_respects_left(&bn, &p, &p2, &q, &hp);
                    let lam = bn.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), body);
                    bn.finish_child(lam)
                };

                let ind = Expr::apps(
                    c.quot_ind.clone(),
                    [c.raw.clone(), c.raw_equiv.clone(), beta, minor, bv.clone()],
                );
                let lam = bh.mk_lam(hp_id, BinderInfo::Default, hyp, ind);
                let lam = bh.mk_lam(p2_id, BinderInfo::Default, c.raw.clone(), lam);
                let lam = bh.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), lam);
                bh.finish_child(lam)
            };

            // Qat.le a b := @Quot.lift Raw Equiv Prop outer_f outer_h a
            let body = Expr::apps(
                c.quot_lift_prop.clone(),
                [
                    c.raw.clone(),
                    c.raw_equiv.clone(),
                    c.prop.clone(),
                    outer_f,
                    outer_h,
                    a.clone(),
                ],
            );
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.ratq.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Rat.le"),
            level_params: vec![],
            type_: le_type,
            value: le_value,
            is_reducible: true,
        })
    }

    /// 5b'. `Qat.lt : Qat → Qat → Prop`, a NESTED binary `Quot.lift` into
    /// `Prop` — the strict-order mirror of `Qat.le`.
    ///
    /// Lifts `Raw.lt p q := Int.lt (num p · eff q) (num q · eff p)`. Both
    /// respect obligations are `@Eq Prop`, discharged by `propext` of the two
    /// implications, each proved by the strict cross-multiplication
    /// transitivity `Int.lt_cross_trans{,'}` (the equality side of the `Equiv`
    /// hypothesis enters via `le_of_eq`, the strict order datum stays strict).
    fn register_rat_q_lt(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("Rat.lt")).is_some() {
            return Ok(());
        }

        let lt_type = Expr::pi(
            BinderInfo::Default,
            c.ratq.clone(),
            Expr::pi(BinderInfo::Default, c.ratq.clone(), c.prop.clone()),
        );

        let lt_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let (bv_id, bv) = b.fresh_local(c.ratq.clone());

            let inner_lift = |parent: &EnvDeclBuilder, first: &Expr, bb: &Expr| -> Expr {
                let g = {
                    let mut bi = EnvDeclBuilder::child_of(parent);
                    let (q_id, q) = bi.fresh_local(c.raw.clone());
                    let body = c.raw_lt(first, &q);
                    let lam = bi.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), body);
                    bi.finish_child(lam)
                };
                let h = {
                    let mut bi = EnvDeclBuilder::child_of(parent);
                    let (q_id, q) = bi.fresh_local(c.raw.clone());
                    let (q2_id, q2) = bi.fresh_local(c.raw.clone());
                    let hh = c.equiv(q.clone(), q2.clone());
                    let (hq_id, hq) = bi.fresh_local(hh.clone());
                    let body = c.lt_respects_right(&bi, first, &q, &q2, &hq);
                    let lam = bi.mk_lam(hq_id, BinderInfo::Default, hh, body);
                    let lam = bi.mk_lam(q2_id, BinderInfo::Default, c.raw.clone(), lam);
                    let lam = bi.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), lam);
                    bi.finish_child(lam)
                };
                Expr::apps(
                    c.quot_lift_prop.clone(),
                    [
                        c.raw.clone(),
                        c.raw_equiv.clone(),
                        c.prop.clone(),
                        g,
                        h,
                        bb.clone(),
                    ],
                )
            };

            let outer_f = {
                let mut bo = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bo.fresh_local(c.raw.clone());
                let body = inner_lift(&bo, &p, &bv);
                let lam = bo.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), body);
                bo.finish_child(lam)
            };

            let outer_h = {
                let mut bh = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bh.fresh_local(c.raw.clone());
                let (p2_id, p2) = bh.fresh_local(c.raw.clone());
                let hyp = c.equiv(p.clone(), p2.clone());
                let (hp_id, hp) = bh.fresh_local(hyp.clone());

                let beta = {
                    let mut bm = EnvDeclBuilder::child_of(&bh);
                    let (bb_id, bb) = bm.fresh_local(c.ratq.clone());
                    let lhs = inner_lift(&bm, &p, &bb);
                    let rhs = inner_lift(&bm, &p2, &bb);
                    let body = Expr::apps(c.eq_ratq.clone(), [c.prop.clone(), lhs, rhs]);
                    let lam = bm.mk_lam(bb_id, BinderInfo::Default, c.ratq.clone(), body);
                    bm.finish_child(lam)
                };

                let minor = {
                    let mut bn = EnvDeclBuilder::child_of(&bh);
                    let (q_id, q) = bn.fresh_local(c.raw.clone());
                    let body = c.lt_respects_left(&bn, &p, &p2, &q, &hp);
                    let lam = bn.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), body);
                    bn.finish_child(lam)
                };

                let ind = Expr::apps(
                    c.quot_ind.clone(),
                    [c.raw.clone(), c.raw_equiv.clone(), beta, minor, bv.clone()],
                );
                let lam = bh.mk_lam(hp_id, BinderInfo::Default, hyp, ind);
                let lam = bh.mk_lam(p2_id, BinderInfo::Default, c.raw.clone(), lam);
                let lam = bh.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), lam);
                bh.finish_child(lam)
            };

            let body = Expr::apps(
                c.quot_lift_prop.clone(),
                [
                    c.raw.clone(),
                    c.raw_equiv.clone(),
                    c.prop.clone(),
                    outer_f,
                    outer_h,
                    a.clone(),
                ],
            );
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.ratq.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Rat.lt"),
            level_params: vec![],
            type_: lt_type,
            value: lt_value,
            is_reducible: true,
        })
    }

    /// Step 6 (THE PAYOFF) — the two previously-FALSE structural axioms, now
    /// genuine `Declaration::Theorem`s over the quotient `Qat`.
    fn register_rat_q_payoff(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        self.register_ratq_zero_mul(c)?;
        self.register_rat_q_mul_zero(c)?;
        self.register_rat_q_add_left_neg(c)?;
        self.register_rat_q_add_neg_self(c)?;
        self.register_rat_q_le_antisymm(c)?;
        self.register_rat_q_add_le_add_left(c)?;
        self.register_rat_q_le_add_of_nonneg_right(c)?;
        self.register_rat_q_left_distrib(c)?;
        self.register_rat_q_right_distrib(c)?;
        self.register_rat_q_add_zero(c)?;
        self.register_rat_q_add_assoc(c)?;
        self.register_rat_q_add_right_cancel(c)?;
        self.register_rat_q_mul_inv_cancel(c)?;
        Ok(())
    }

    /// `Qat.add_neg_self : ∀ a : Qat, @Eq Qat (Qat.add a (Qat.neg a)) Qat.zero`.
    ///
    /// Mirror of `Qat.add_left_neg` with the addends swapped: for `a = mk p` the
    /// rep numerator is `np·ep + (-np)·ep`, `= (np + (-np))·ep = 0·ep = 0` via
    /// `Int.right_distrib` + `Int.add_neg_self` + `Int.zero_mul`. `Quot.sound`
    /// closes `Equiv (Raw.add p (Raw.neg p)) (Raw.mk 0 1)`.
    fn register_rat_q_add_neg_self(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.add_neg_self");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }
        let ratq_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let ratq_add = Expr::const_(Name::from_string("Rat.add"), vec![]);
        let ratq_neg = Expr::const_(Name::from_string("Rat.neg"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let neg_a = Expr::app(ratq_neg.clone(), a.clone());
            let lhs = Expr::apps(ratq_add.clone(), [a.clone(), neg_a]);
            let goal = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, ratq_zero.clone()]);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), goal);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());

            let beta = {
                let mut bm = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = bm.fresh_local(c.ratq.clone());
                let neg_x = Expr::app(ratq_neg.clone(), x.clone());
                let lhs = Expr::apps(ratq_add.clone(), [x.clone(), neg_x]);
                let body = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, ratq_zero.clone()]);
                let lam = bm.mk_lam(x_id, BinderInfo::Default, c.ratq.clone(), body);
                bm.finish_child(lam)
            };

            let minor = {
                let mut bn = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bn.fresh_local(c.raw.clone());

                let np = c.num(p.clone());
                let ep = c.eff(p.clone());
                let nat_one = Expr::app(c.nat_succ.clone(), c.nat_zero.clone());
                let raw_neg_p = c.raw_mk(
                    c.neg(np.clone()),
                    Expr::app(c.raw_eff_denom.clone(), p.clone()),
                );
                // raw_lhs := Raw.add p (raw_neg p) = mk (np·ep + (-np)·ep) (...).
                let np_ep = c.mul(np.clone(), ep.clone());
                let neg_np_ep = c.mul(c.neg(np.clone()), ep.clone());
                let l_num = c.add(np_ep.clone(), neg_np_ep.clone());
                let l_den = c.nmul(
                    Expr::app(c.raw_eff_denom.clone(), p.clone()),
                    Expr::app(c.raw_eff_denom.clone(), raw_neg_p.clone()),
                );
                let raw_lhs = c.raw_mk(l_num.clone(), l_den.clone());
                let raw_zero = c.raw_mk(c.int_zero.clone(), nat_one.clone());

                let e_r = c.eff(raw_zero.clone());
                let e_l = c.eff(raw_lhs.clone());
                let lhs_t = c.mul(l_num.clone(), e_r.clone());
                let rhs_t = c.mul(c.int_zero.clone(), e_l.clone());

                // numL_eq_zero : np·ep + (-np)·ep = 0.
                let np_plus_neg_np = c.add(np.clone(), c.neg(np.clone()));
                let sum_mul_ep = c.mul(np_plus_neg_np.clone(), ep.clone());
                let s_a = c.symm_int(
                    sum_mul_ep.clone(),
                    l_num.clone(),
                    c.right_distrib(np.clone(), c.neg(np.clone()), ep.clone()),
                );
                let zero_ep = c.mul(c.int_zero.clone(), ep.clone());
                let s_b = c.congr_arg(
                    np_plus_neg_np.clone(),
                    c.int_zero.clone(),
                    c.mul_right_fn(&bn, ep.clone()),
                    c.add_neg_self(np.clone()),
                );
                let s_c = c.zero_mul(ep.clone());
                let numl_to_zero = {
                    let t1 =
                        c.trans_int(l_num.clone(), sum_mul_ep.clone(), zero_ep.clone(), s_a, s_b);
                    c.trans_int(l_num.clone(), zero_ep.clone(), c.int_zero.clone(), t1, s_c)
                };

                let zero_er = c.mul(c.int_zero.clone(), e_r.clone());
                let l1 = c.congr_arg(
                    l_num.clone(),
                    c.int_zero.clone(),
                    c.mul_right_fn(&bn, e_r.clone()),
                    numl_to_zero,
                );
                let l2 = c.zero_mul(e_r.clone());
                let lhs_to_zero =
                    c.trans_int(lhs_t.clone(), zero_er.clone(), c.int_zero.clone(), l1, l2);
                let r1 = c.zero_mul(e_l.clone());
                let zero_to_rhs = c.symm_int(rhs_t.clone(), c.int_zero.clone(), r1);
                let eqv = c.trans_int(
                    lhs_t.clone(),
                    c.int_zero.clone(),
                    rhs_t.clone(),
                    lhs_to_zero,
                    zero_to_rhs,
                );

                let sound = c.quot_sound(raw_lhs.clone(), raw_zero.clone(), eqv);
                let lam = bn.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), sound);
                bn.finish_child(lam)
            };

            let ind = Expr::apps(
                c.quot_ind.clone(),
                [c.raw.clone(), c.raw_equiv.clone(), beta, minor, a.clone()],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), ind);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Qat.add_left_neg : ∀ a : Qat, @Eq Qat (Qat.add (Qat.neg a) a) Qat.zero`.
    ///
    /// FALSE over the free `Rat`, TRUE over `Qat`. `Quot.ind` on `a`; for
    /// `a = Quot.mk p` both `Qat.neg` and `Qat.add` ι-reduce, so the goal is
    /// `Eq Qat (Quot.mk (Raw.add (Raw.neg p) p)) Qat.zero`, closed by
    /// `Quot.sound` of `Equiv (Raw.add (Raw.neg p) p) (Raw.mk 0 1)`. That Equiv
    /// reduces to `Eq Int (((-np)·ep + np·ep)·1) (0·E_L)`, both sides `0` via
    /// `Int.right_distrib` + `Int.neg_add_self` + `Int.zero_mul`.
    fn register_rat_q_add_left_neg(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.add_left_neg");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }
        let ratq_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let ratq_add = Expr::const_(Name::from_string("Rat.add"), vec![]);
        let ratq_neg = Expr::const_(Name::from_string("Rat.neg"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let neg_a = Expr::app(ratq_neg.clone(), a.clone());
            let lhs = Expr::apps(ratq_add.clone(), [neg_a, a.clone()]);
            let goal = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, ratq_zero.clone()]);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), goal);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());

            // Motive β := fun a => Eq Qat (Qat.add (Qat.neg a) a) Qat.zero.
            let beta = {
                let mut bm = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = bm.fresh_local(c.ratq.clone());
                let neg_x = Expr::app(ratq_neg.clone(), x.clone());
                let lhs = Expr::apps(ratq_add.clone(), [neg_x, x.clone()]);
                let body = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, ratq_zero.clone()]);
                let lam = bm.mk_lam(x_id, BinderInfo::Default, c.ratq.clone(), body);
                bm.finish_child(lam)
            };

            // minor: fun (p : Raw) => Quot.sound (raw_add (raw_neg p) p)(Raw.mk 0 1) eqv.
            let minor = {
                let mut bn = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bn.fresh_local(c.raw.clone());

                let np = c.num(p.clone());
                let ep = c.eff(p.clone());
                let nat_one = Expr::app(c.nat_succ.clone(), c.nat_zero.clone());
                // raw_neg p := Raw.mk (Int.neg np) (effDenom p).
                let raw_neg_p = c.raw_mk(
                    c.neg(np.clone()),
                    Expr::app(c.raw_eff_denom.clone(), p.clone()),
                );
                // raw_lhs := Raw.add (raw_neg p) p
                //   = Raw.mk ((neg np)·E(neg p) ... ) (effDenom(neg p)·effDenom p).
                //   num(raw_neg p) ≡ neg np ; E(raw_neg p) ≡ ep (def-eq).
                let neg_np_ep = c.mul(c.neg(np.clone()), ep.clone());
                let np_ep = c.mul(np.clone(), ep.clone());
                let l_num = c.add(neg_np_ep.clone(), np_ep.clone());
                let l_den = c.nmul(
                    Expr::app(c.raw_eff_denom.clone(), raw_neg_p.clone()),
                    Expr::app(c.raw_eff_denom.clone(), p.clone()),
                );
                let raw_lhs = c.raw_mk(l_num.clone(), l_den.clone());
                let raw_zero = c.raw_mk(c.int_zero.clone(), nat_one.clone());

                // Equiv raw_lhs raw_zero ≡ Eq Int (l_num · E_R) (0 · E_L).
                let e_r = c.eff(raw_zero.clone()); // ≡ ofNat 1
                let e_l = c.eff(raw_lhs.clone());
                let lhs_t = c.mul(l_num.clone(), e_r.clone());
                let rhs_t = c.mul(c.int_zero.clone(), e_l.clone());

                // numL_eq_zero : (neg np)·ep + np·ep = 0.
                let neg_np_plus_np = c.add(c.neg(np.clone()), np.clone());
                let sum_mul_ep = c.mul(neg_np_plus_np.clone(), ep.clone());
                // s_a : (neg np)·ep + np·ep = ((neg np)+np)·ep  [symm right_distrib]
                let s_a = c.symm_int(
                    sum_mul_ep.clone(),
                    l_num.clone(),
                    c.right_distrib(c.neg(np.clone()), np.clone(), ep.clone()),
                );
                // s_b : ((neg np)+np)·ep = 0·ep  [congrArg (·*ep)(neg_add_self np)]
                let zero_ep = c.mul(c.int_zero.clone(), ep.clone());
                let s_b = c.congr_arg(
                    neg_np_plus_np.clone(),
                    c.int_zero.clone(),
                    c.mul_right_fn(&bn, ep.clone()),
                    c.neg_add_self(np.clone()),
                );
                // s_c : 0·ep = 0  [zero_mul ep]
                let s_c = c.zero_mul(ep.clone());
                let numl_to_zero = {
                    let t1 =
                        c.trans_int(l_num.clone(), sum_mul_ep.clone(), zero_ep.clone(), s_a, s_b);
                    c.trans_int(l_num.clone(), zero_ep.clone(), c.int_zero.clone(), t1, s_c)
                };

                // lhs_t = l_num · E_R = 0 · E_R = 0.
                let zero_er = c.mul(c.int_zero.clone(), e_r.clone());
                let l1 = c.congr_arg(
                    l_num.clone(),
                    c.int_zero.clone(),
                    c.mul_right_fn(&bn, e_r.clone()),
                    numl_to_zero,
                );
                let l2 = c.zero_mul(e_r.clone());
                let lhs_to_zero =
                    c.trans_int(lhs_t.clone(), zero_er.clone(), c.int_zero.clone(), l1, l2);
                // rhs_t = 0 · E_L = 0.
                let r1 = c.zero_mul(e_l.clone());
                let zero_to_rhs = c.symm_int(rhs_t.clone(), c.int_zero.clone(), r1);
                let eqv = c.trans_int(
                    lhs_t.clone(),
                    c.int_zero.clone(),
                    rhs_t.clone(),
                    lhs_to_zero,
                    zero_to_rhs,
                );

                let sound = c.quot_sound(raw_lhs.clone(), raw_zero.clone(), eqv);
                let lam = bn.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), sound);
                bn.finish_child(lam)
            };

            let ind = Expr::apps(
                c.quot_ind.clone(),
                [c.raw.clone(), c.raw_equiv.clone(), beta, minor, a.clone()],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), ind);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Qat.mul_zero : ∀ a : Qat, @Eq Qat (Qat.mul a Qat.zero) Qat.zero`.
    ///
    /// FALSE over the free `Rat`, TRUE over `Qat`. Mirror of `Qat.zero_mul`
    /// with the operands swapped: `Quot.ind` on `a`; for `a = Quot.mk q` the
    /// `Qat.mul` ι-reduces to `Quot.mk (Raw.mk (nq · 0) (effDenom q · 1))`,
    /// and `Quot.sound` of the cross-mult Equiv (both numerators collapse to
    /// `Int.zero` via `Int.mul_zero` / `Int.zero_mul`) closes it.
    fn register_rat_q_mul_zero(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.mul_zero");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }
        let ratq_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let ratq_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let lhs = Expr::apps(ratq_mul.clone(), [a.clone(), ratq_zero.clone()]);
            let goal = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, ratq_zero.clone()]);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), goal);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());

            // Motive β := fun a => Eq Qat (Qat.mul a Qat.zero) Qat.zero.
            let beta = {
                let mut bm = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = bm.fresh_local(c.ratq.clone());
                let lhs = Expr::apps(ratq_mul.clone(), [x.clone(), ratq_zero.clone()]);
                let body = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, ratq_zero.clone()]);
                let lam = bm.mk_lam(x_id, BinderInfo::Default, c.ratq.clone(), body);
                bm.finish_child(lam)
            };

            // minor: fun (q : Raw) => Quot.sound (raw_mul q zero01)(Raw.mk 0 1) eqv.
            let minor = {
                let mut bn = EnvDeclBuilder::child_of(&b);
                let (q_id, q) = bn.fresh_local(c.raw.clone());

                let nat_one = Expr::app(c.nat_succ.clone(), c.nat_zero.clone());
                let zero01 = c.raw_mk(c.int_zero.clone(), nat_one.clone());
                // raw_lhs := Raw.mk (Int.mul (num q) Int.zero) (Nat.mul (eff q)(eff zero01)).
                let aexpr = c.mul(c.num(q.clone()), c.int_zero.clone());
                let raw_den = c.nmul(
                    Expr::app(c.raw_eff_denom.clone(), q.clone()),
                    Expr::app(c.raw_eff_denom.clone(), zero01.clone()),
                );
                let raw_lhs = c.raw_mk(aexpr.clone(), raw_den.clone());
                let raw_zero = c.raw_mk(c.int_zero.clone(), nat_one.clone());

                // Equiv raw_lhs raw_zero ≡ Eq Int (A · eff(raw_zero)) (Int.zero · eff(raw_lhs)).
                let eff_zero = c.eff(raw_zero.clone());
                let eff_lhs = c.eff(raw_lhs.clone());
                let lhs_t = c.mul(aexpr.clone(), eff_zero.clone());
                let rhs_t = c.mul(c.int_zero.clone(), eff_lhs.clone());

                // f := fun w => w * eff_zero
                let mul_right_effzero = c.mul_right_fn(&bn, eff_zero.clone());
                // e1 : (nq · Int.zero) · eff_zero = Int.zero · eff_zero
                //        [congrArg (·*eff_zero) (Int.mul_zero nq)]
                let zero_effzero = c.mul(c.int_zero.clone(), eff_zero.clone());
                let e1 = c.congr_arg(
                    aexpr.clone(),
                    c.int_zero.clone(),
                    mul_right_effzero,
                    c.mul_zero(c.num(q.clone())),
                );
                // e2 : Int.zero · eff_zero = Int.zero   [Int.zero_mul eff_zero]
                let e2 = c.zero_mul(eff_zero.clone());
                // e3 : Int.zero · eff_lhs = Int.zero    [Int.zero_mul eff_lhs]
                let e3 = c.zero_mul(eff_lhs.clone());
                let lhs_to_zero = c.trans_int(
                    lhs_t.clone(),
                    zero_effzero.clone(),
                    c.int_zero.clone(),
                    e1,
                    e2,
                );
                let zero_to_rhs = c.symm_int(rhs_t.clone(), c.int_zero.clone(), e3);
                let eqv = c.trans_int(
                    lhs_t.clone(),
                    c.int_zero.clone(),
                    rhs_t.clone(),
                    lhs_to_zero,
                    zero_to_rhs,
                );

                let sound = c.quot_sound(raw_lhs.clone(), raw_zero.clone(), eqv);
                let lam = bn.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), sound);
                bn.finish_child(lam)
            };

            let ind = Expr::apps(
                c.quot_ind.clone(),
                [c.raw.clone(), c.raw_equiv.clone(), beta, minor, a.clone()],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), ind);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Qat.zero_mul : ∀ a : Qat, @Eq Qat (Qat.mul Qat.zero a) Qat.zero`.
    ///
    /// FALSE over the free `Rat` (`mul (mk 0 1)(mk 3 5) = mk 0 5 ≠ mk 0 1`),
    /// TRUE over `Qat`: `Quot.ind` on `a`; for `a = Quot.mk q` both `Quot.lift`s
    /// ι-reduce so the goal is `Eq Qat (Quot.mk (Raw.mk (0·nq) (1·Eq))) Qat.zero`,
    /// closed by `Quot.sound` of the cross-mult Equiv (both sides collapse to
    /// `Int.zero` via `Int.zero_mul`).
    fn register_ratq_zero_mul(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.zero_mul");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }
        let ratq_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let ratq_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let lhs = Expr::apps(ratq_mul.clone(), [ratq_zero.clone(), a.clone()]);
            let goal = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, ratq_zero.clone()]);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), goal);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());

            // Motive β := fun a => Eq Qat (Qat.mul Qat.zero a) Qat.zero.
            let beta = {
                let mut bm = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = bm.fresh_local(c.ratq.clone());
                let lhs = Expr::apps(ratq_mul.clone(), [ratq_zero.clone(), x.clone()]);
                let body = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, ratq_zero.clone()]);
                let lam = bm.mk_lam(x_id, BinderInfo::Default, c.ratq.clone(), body);
                bm.finish_child(lam)
            };

            // minor: fun (q : Raw) => Quot.sound (rawmul zero01 q) (Raw.mk 0 1) eqv.
            let minor = {
                let mut bn = EnvDeclBuilder::child_of(&b);
                let (q_id, q) = bn.fresh_local(c.raw.clone());

                // zero01 := Raw.mk Int.zero 1 ; A := Int.mul Int.zero (num q) ;
                // raw_lhs := Raw.mk A (Nat.mul (effDenom zero01) (effDenom q)).
                let nat_one = Expr::app(c.nat_succ.clone(), c.nat_zero.clone());
                let zero01 = c.raw_mk(c.int_zero.clone(), nat_one.clone());
                let aexpr = c.mul(c.int_zero.clone(), c.num(q.clone()));
                let raw_den = c.nmul(
                    Expr::app(c.raw_eff_denom.clone(), zero01.clone()),
                    Expr::app(c.raw_eff_denom.clone(), q.clone()),
                );
                let raw_lhs = c.raw_mk(aexpr.clone(), raw_den.clone());
                // raw_zero := Raw.mk Int.zero 1 (the rep of Qat.zero).
                let raw_zero = c.raw_mk(c.int_zero.clone(), nat_one.clone());

                // Equiv raw_lhs raw_zero
                //   ≡ Eq Int (A · eff(raw_zero)) (Int.zero · eff(raw_lhs))
                //   ≡ Eq Int (A · ofNat 1) (Int.zero · eff(raw_lhs)).
                let eff_zero = c.eff(raw_zero.clone()); // ≡ ofNat 1
                let eff_lhs = c.eff(raw_lhs.clone());
                let lhs_t = c.mul(aexpr.clone(), eff_zero.clone());
                let rhs_t = c.mul(c.int_zero.clone(), eff_lhs.clone());

                // f := fun w => w * eff_zero
                let mul_right_effzero = {
                    let mut ch = EnvDeclBuilder::child_of(&bn);
                    let (w_id, w) = ch.fresh_local(c.int.clone());
                    let body = c.mul(w, eff_zero.clone());
                    let lam = ch.mk_lam(w_id, BinderInfo::Default, c.int.clone(), body);
                    ch.finish_child(lam)
                };
                // e1 : (Int.zero · nq) · eff_zero = Int.zero · eff_zero
                //        [congrArg (·*eff_zero) (Int.zero_mul nq)]
                let zero_effzero = c.mul(c.int_zero.clone(), eff_zero.clone());
                let e1 = c.congr_arg(
                    aexpr.clone(),
                    c.int_zero.clone(),
                    mul_right_effzero,
                    c.zero_mul(c.num(q.clone())),
                );
                // e2 : Int.zero · eff_zero = Int.zero   [Int.zero_mul eff_zero]
                let e2 = c.zero_mul(eff_zero.clone());
                // e3 : Int.zero · eff_lhs = Int.zero    [Int.zero_mul eff_lhs]
                let e3 = c.zero_mul(eff_lhs.clone());
                // lhs_t = (0·nq)·eff_zero  -> 0·eff_zero -> 0 ; rhs_t = 0·eff_lhs -> 0.
                //   eqv : lhs_t = rhs_t  via  lhs_t = 0  then  0 = rhs_t (= symm e3).
                let lhs_to_zero = c.trans_int(
                    lhs_t.clone(),
                    zero_effzero.clone(),
                    c.int_zero.clone(),
                    e1,
                    e2,
                );
                let zero_to_rhs = c.symm_int(rhs_t.clone(), c.int_zero.clone(), e3);
                let eqv = c.trans_int(
                    lhs_t.clone(),
                    c.int_zero.clone(),
                    rhs_t.clone(),
                    lhs_to_zero,
                    zero_to_rhs,
                );

                let sound = c.quot_sound(raw_lhs.clone(), raw_zero.clone(), eqv);
                let lam = bn.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), sound);
                bn.finish_child(lam)
            };

            // @Quot.ind Raw Equiv beta minor a : beta a ≡ goal.
            let ind = Expr::apps(
                c.quot_ind.clone(),
                [c.raw.clone(), c.raw_equiv.clone(), beta, minor, a.clone()],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), ind);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Qat.le_antisymm : ∀ a b : Qat, Qat.le a b → Qat.le b a → @Eq Qat a b`.
    ///
    /// FALSE over the free `Rat` (`mk 1 1` and `mk 2 2` are `≤` both ways yet
    /// structurally distinct), TRUE over `Qat`: nested `Quot.ind` on `a, b`; for
    /// `a = Quot.mk p`, `b = Quot.mk q` the two `Qat.le`s ι-reduce to the raw
    /// `Int.le` cross-products, `Int.le_antisymm` yields the cross EQUALITY which
    /// is exactly `Equiv p q`, and `Quot.sound` closes `Eq Qat (mk p)(mk q)`.
    fn register_rat_q_le_antisymm(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.le_antisymm");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }
        let ratq_le = Expr::const_(Name::from_string("Rat.le"), vec![]);

        // Shared: the proposition `∀ b, le a b → le b a → Eq a b` for a given
        // Qat term `a` (used both as the outer motive body and in the type).
        let inner_forall = |a: &Expr, parent: &EnvDeclBuilder| -> Expr {
            let mut bb = EnvDeclBuilder::child_of(parent);
            let (b_id, bvar) = bb.fresh_local(c.ratq.clone());
            let le_ab = Expr::apps(ratq_le.clone(), [a.clone(), bvar.clone()]);
            let le_ba = Expr::apps(ratq_le.clone(), [bvar.clone(), a.clone()]);
            let eq_ab = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), a.clone(), bvar.clone()]);
            let (h1_id, _h1) = bb.fresh_local(le_ab.clone());
            let (h2_id, _h2) = bb.fresh_local(le_ba.clone());
            let e = bb.mk_pi(h2_id, BinderInfo::Default, le_ba, eq_ab);
            let e = bb.mk_pi(h1_id, BinderInfo::Default, le_ab, e);
            bb.mk_pi(b_id, BinderInfo::Default, c.ratq.clone(), e)
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let body = inner_forall(&a, &b);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), body);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());

            // Outer motive Ba := fun a => ∀ b, le a b → le b a → Eq a b.
            let beta_a = {
                let mut bm = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = bm.fresh_local(c.ratq.clone());
                let body = inner_forall(&x, &bm);
                let lam = bm.mk_lam(x_id, BinderInfo::Default, c.ratq.clone(), body);
                bm.finish_child(lam)
            };

            // Outer minor: fun (p : Raw) => <∀ b, le (mk p) b → le b (mk p) → Eq (mk p) b>.
            let minor_a = {
                let mut bp = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bp.fresh_local(c.raw.clone());
                let mk_p = c.quot_mk(p.clone());

                // Inner motive Bb := fun b => le (mk p) b → le b (mk p) → Eq (mk p) b.
                let beta_b = {
                    let mut bmb = EnvDeclBuilder::child_of(&bp);
                    let (y_id, y) = bmb.fresh_local(c.ratq.clone());
                    let le_py = Expr::apps(ratq_le.clone(), [mk_p.clone(), y.clone()]);
                    let le_yp = Expr::apps(ratq_le.clone(), [y.clone(), mk_p.clone()]);
                    let eq_py =
                        Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), mk_p.clone(), y.clone()]);
                    let (h1_id, _h1) = bmb.fresh_local(le_py.clone());
                    let (h2_id, _h2) = bmb.fresh_local(le_yp.clone());
                    let e = bmb.mk_pi(h2_id, BinderInfo::Default, le_yp, eq_py);
                    let e = bmb.mk_pi(h1_id, BinderInfo::Default, le_py, e);
                    // The MOTIVE binder over `y` is a LAMBDA (β : Qat → Prop),
                    // not a Pi — the implication chain is its Prop-valued body.
                    let e = bmb.mk_lam(y_id, BinderInfo::Default, c.ratq.clone(), e);
                    bmb.finish_child(e)
                };

                // Inner minor: fun (q : Raw) (h1 : le (mk p)(mk q)) (h2 : le (mk q)(mk p))
                //   => Quot.sound p q (Int.le_antisymm (np·Eq)(nq·Ep) h1 h2).
                let minor_b = {
                    let mut bq = EnvDeclBuilder::child_of(&bp);
                    let (q_id, q) = bq.fresh_local(c.raw.clone());
                    let mk_q = c.quot_mk(q.clone());
                    let le_pq = Expr::apps(ratq_le.clone(), [mk_p.clone(), mk_q.clone()]);
                    let le_qp = Expr::apps(ratq_le.clone(), [mk_q.clone(), mk_p.clone()]);
                    let (h1_id, h1) = bq.fresh_local(le_pq.clone());
                    let (h2_id, h2) = bq.fresh_local(le_qp.clone());

                    // h1 : le (mk p)(mk q) ≡ Int.le (np·Eq) (nq·Ep)
                    // h2 : le (mk q)(mk p) ≡ Int.le (nq·Ep) (np·Eq)
                    // Int.le_antisymm (np·Eq)(nq·Ep) h1 h2 : Eq Int (np·Eq)(nq·Ep) ≡ Equiv p q.
                    let np_eq = c.mul(c.num(p.clone()), c.eff(q.clone()));
                    let nq_ep = c.mul(c.num(q.clone()), c.eff(p.clone()));
                    let eqv = Expr::apps(
                        c.int_le_antisymm.clone(),
                        [np_eq.clone(), nq_ep.clone(), h1.clone(), h2.clone()],
                    );
                    let sound = c.quot_sound(p.clone(), q.clone(), eqv);
                    let lam = bq.mk_lam(h2_id, BinderInfo::Default, le_qp, sound);
                    let lam = bq.mk_lam(h1_id, BinderInfo::Default, le_pq, lam);
                    let lam = bq.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), lam);
                    bq.finish_child(lam)
                };

                // @Quot.ind Raw Equiv beta_b minor_b : ∀ b, beta_b b
                //   ≡ ∀ b, le (mk p) b → le b (mk p) → Eq (mk p) b.
                let ind_b = Expr::apps(
                    c.quot_ind.clone(),
                    [c.raw.clone(), c.raw_equiv.clone(), beta_b, minor_b],
                );
                let lam = bp.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), ind_b);
                bp.finish_child(lam)
            };

            // @Quot.ind Raw Equiv beta_a minor_a a : beta_a a ≡ ∀ b, ….
            let ind_a = Expr::apps(
                c.quot_ind.clone(),
                [
                    c.raw.clone(),
                    c.raw_equiv.clone(),
                    beta_a,
                    minor_a,
                    a.clone(),
                ],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), ind_a);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Qat.add_le_add_left : ∀ a b c : Qat,
    ///     Qat.le a b → Qat.le (Qat.add c a) (Qat.add c b)`.
    ///
    /// Nested `Quot.ind` on `a, b, c`. For reps `p, q, s` the goal `Int`-form is
    ///   `(ns·Ep + np·Es)·(Es·Eq)  ≤  (ns·Eq + nq·Es)·(Es·Ep)`
    /// from `h : np·Eq ≤ nq·Ep`. Both sides `right_distrib` into a common term
    /// `(ns·*)·*` (equal under `mulMulMulComm` + `mul_comm`) plus a term that
    /// scales `h` by the nonneg `Es·Es` (`mulMulMulComm2`), closed by
    /// `Int.add_le_add_left`.
    fn register_rat_q_add_le_add_left(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.add_le_add_left");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }
        // The triple `Quot.ind` proof is built most naturally with binder order
        // `∀ a b c, le a b → …`. The PUBLIC `Rat.add_le_add_left` (consumed
        // across nn_verify) has binder order `∀ a b, le a b → ∀ c, …`, so we
        // register the proof under a private worker name with the `…c, h…` order
        // and wrap it to the public signature below.
        let worker_name = Name::from_string("Rat.add_le_add_left.qworker");
        let ratq_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
        let ratq_add = Expr::const_(Name::from_string("Rat.add"), vec![]);

        // `∀ b c, le a b → le (add c a)(add c b)` for a given Qat term `a`.
        let inner_forall = |a: &Expr, parent: &EnvDeclBuilder| -> Expr {
            let mut bb = EnvDeclBuilder::child_of(parent);
            let (b_id, bvar) = bb.fresh_local(c.ratq.clone());
            let (cc_id, cvar) = bb.fresh_local(c.ratq.clone());
            let le_ab = Expr::apps(ratq_le.clone(), [a.clone(), bvar.clone()]);
            let add_ca = Expr::apps(ratq_add.clone(), [cvar.clone(), a.clone()]);
            let add_cb = Expr::apps(ratq_add.clone(), [cvar.clone(), bvar.clone()]);
            let goal = Expr::apps(ratq_le.clone(), [add_ca, add_cb]);
            let (h_id, _h) = bb.fresh_local(le_ab.clone());
            let e = bb.mk_pi(h_id, BinderInfo::Default, le_ab, goal);
            let e = bb.mk_pi(cc_id, BinderInfo::Default, c.ratq.clone(), e);
            bb.mk_pi(b_id, BinderInfo::Default, c.ratq.clone(), e)
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let body = inner_forall(&a, &b);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), body);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());

            // Outer motive Ba := fun a => ∀ b c, le a b → le (add c a)(add c b).
            let beta_a = {
                let mut bm = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = bm.fresh_local(c.ratq.clone());
                let body = inner_forall(&x, &bm);
                let lam = bm.mk_lam(x_id, BinderInfo::Default, c.ratq.clone(), body);
                bm.finish_child(lam)
            };

            // Outer minor: fun (p : Raw) => <∀ b c, ...> for a = mk p.
            let minor_a = {
                let mut bp = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bp.fresh_local(c.raw.clone());
                let mk_p = c.quot_mk(p.clone());

                // Inner motive Bb := fun b => ∀ c, le (mk p) b → le (add c (mk p))(add c b).
                let beta_b = {
                    let mut bmb = EnvDeclBuilder::child_of(&bp);
                    let (y_id, y) = bmb.fresh_local(c.ratq.clone());
                    let body = {
                        // ∀ c, le (mk p) y → le (add c (mk p))(add c y).
                        let mut bc = EnvDeclBuilder::child_of(&bmb);
                        let (cc_id, cvar) = bc.fresh_local(c.ratq.clone());
                        let le_py = Expr::apps(ratq_le.clone(), [mk_p.clone(), y.clone()]);
                        let add_cp = Expr::apps(ratq_add.clone(), [cvar.clone(), mk_p.clone()]);
                        let add_cy = Expr::apps(ratq_add.clone(), [cvar.clone(), y.clone()]);
                        let goal = Expr::apps(ratq_le.clone(), [add_cp, add_cy]);
                        let (h_id, _h) = bc.fresh_local(le_py.clone());
                        let e = bc.mk_pi(h_id, BinderInfo::Default, le_py, goal);
                        let e = bc.mk_pi(cc_id, BinderInfo::Default, c.ratq.clone(), e);
                        bc.finish_child(e)
                    };
                    let lam = bmb.mk_lam(y_id, BinderInfo::Default, c.ratq.clone(), body);
                    bmb.finish_child(lam)
                };

                // Inner minor over q: fun (q : Raw) => ∀ c, le (mk p)(mk q) → le (add c (mk p))(add c (mk q)).
                let minor_b = {
                    let mut bq = EnvDeclBuilder::child_of(&bp);
                    let (q_id, q) = bq.fresh_local(c.raw.clone());
                    let mk_q = c.quot_mk(q.clone());

                    // Innermost motive Bc := fun cc => le (mk p)(mk q) → le (add cc (mk p))(add cc (mk q)).
                    let beta_c = {
                        let mut bmc = EnvDeclBuilder::child_of(&bq);
                        let (z_id, z) = bmc.fresh_local(c.ratq.clone());
                        let le_pq = Expr::apps(ratq_le.clone(), [mk_p.clone(), mk_q.clone()]);
                        let add_zp = Expr::apps(ratq_add.clone(), [z.clone(), mk_p.clone()]);
                        let add_zq = Expr::apps(ratq_add.clone(), [z.clone(), mk_q.clone()]);
                        let goal = Expr::apps(ratq_le.clone(), [add_zp, add_zq]);
                        let (h_id, _h) = bmc.fresh_local(le_pq.clone());
                        let body = bmc.mk_pi(h_id, BinderInfo::Default, le_pq, goal);
                        let e = bmc.mk_lam(z_id, BinderInfo::Default, c.ratq.clone(), body);
                        bmc.finish_child(e)
                    };

                    // Innermost minor over s: fun (s : Raw)(h : le (mk p)(mk q)) => <Int proof>.
                    let minor_c = {
                        let mut bs = EnvDeclBuilder::child_of(&bq);
                        let (s_id, s) = bs.fresh_local(c.raw.clone());
                        let _mk_s = c.quot_mk(s.clone());
                        let le_pq = Expr::apps(ratq_le.clone(), [mk_p.clone(), mk_q.clone()]);
                        let (h_id, h) = bs.fresh_local(le_pq.clone());

                        let np = c.num(p.clone());
                        let nq = c.num(q.clone());
                        let ns = c.num(s.clone());
                        let ep = c.eff(p.clone());
                        let eq = c.eff(q.clone());
                        let es = c.eff(s.clone());

                        // h : Int.le (np·Eq) (nq·Ep).
                        // Goal: Int.le ((ns·Ep + np·Es)·(Es·Eq)) ((ns·Eq + nq·Es)·(Es·Ep)).
                        let es_eq = c.mul(es.clone(), eq.clone());
                        let es_ep = c.mul(es.clone(), ep.clone());
                        let ns_ep = c.mul(ns.clone(), ep.clone());
                        let np_es = c.mul(np.clone(), es.clone());
                        let ns_eq = c.mul(ns.clone(), eq.clone());
                        let nq_es = c.mul(nq.clone(), es.clone());
                        let l_num = c.add(ns_ep.clone(), np_es.clone());
                        let r_num = c.add(ns_eq.clone(), nq_es.clone());

                        // T1 := (ns·Ep)·(Es·Eq) ; U1 := (np·Es)·(Es·Eq).
                        let t1 = c.mul(ns_ep.clone(), es_eq.clone());
                        let u1 = c.mul(np_es.clone(), es_eq.clone());
                        // T2 := (ns·Eq)·(Es·Ep) ; U2 := (nq·Es)·(Es·Ep).
                        let t2 = c.mul(ns_eq.clone(), es_ep.clone());
                        let u2 = c.mul(nq_es.clone(), es_ep.clone());

                        // d1 : LHS = add T1 U1   [right_distrib (ns·Ep)(np·Es)(Es·Eq)]
                        let d1 = c.right_distrib(ns_ep.clone(), np_es.clone(), es_eq.clone());
                        // d2 : RHS = add T2 U2   [right_distrib (ns·Eq)(nq·Es)(Es·Ep)]
                        let d2 = c.right_distrib(ns_eq.clone(), nq_es.clone(), es_ep.clone());

                        // eqT : T1 = T2.
                        //   T1 = (ns·Es)·(Ep·Eq)  [mmmc ns Ep Es Eq]
                        let ns_es = c.mul(ns.clone(), es.clone());
                        let ep_eq = c.mul(ep.clone(), eq.clone());
                        let eq_ep = c.mul(eq.clone(), ep.clone());
                        let m_t1 = c.mul(ns_es.clone(), ep_eq.clone());
                        let m_t2 = c.mul(ns_es.clone(), eq_ep.clone());
                        let st1 =
                            c.mul_mul_mul_comm(ns.clone(), ep.clone(), es.clone(), eq.clone());
                        //   (ns·Es)·(Ep·Eq) = (ns·Es)·(Eq·Ep)  [congrArg ((ns·Es)·)(mul_comm Ep Eq)]
                        let st2 = c.congr_arg(
                            ep_eq.clone(),
                            eq_ep.clone(),
                            c.mul_left_fn(&bs, ns_es.clone()),
                            c.mul_comm(ep.clone(), eq.clone()),
                        );
                        //   (ns·Es)·(Eq·Ep) = (ns·Eq)·(Es·Ep) = T2  [symm (mmmc ns Eq Es Ep)]
                        let st3 = c.symm_int(
                            t2.clone(),
                            m_t2.clone(),
                            c.mul_mul_mul_comm(ns.clone(), eq.clone(), es.clone(), ep.clone()),
                        );
                        let eqt_a = c.trans_int(t1.clone(), m_t1.clone(), m_t2.clone(), st1, st2);
                        let eq_t = c.trans_int(t1.clone(), m_t2.clone(), t2.clone(), eqt_a, st3);

                        // leU : U1 ≤ U2.
                        //   U1 = (np·Eq)·(Es·Es)  [mmmc2 np Es Es Eq]
                        let es_es = c.mul(es.clone(), es.clone());
                        let np_eq = c.mul(np.clone(), eq.clone());
                        let nq_ep = c.mul(nq.clone(), ep.clone());
                        let scaled_l = c.mul(np_eq.clone(), es_es.clone());
                        let scaled_r = c.mul(nq_ep.clone(), es_es.clone());
                        let u1_eq = c.mul_mul_mul_comm2(&bs, &np, &es, &es, &eq); // U1 = scaled_l
                        let u2_eq = c.mul_mul_mul_comm2(&bs, &nq, &es, &es, &ep); // U2 = scaled_r
                                                                                  // hscale : scaled_l ≤ scaled_r  [mul_le_mul_right (np·Eq)(nq·Ep)(Es·Es) h (0≤Es·Es)]
                        let hes = c.nonneg_eff(&s); // 0 ≤ Es
                        let h_es_es = c.mul_nonneg(es.clone(), es.clone(), hes.clone(), hes); // 0 ≤ Es·Es
                        let hscale = c.mul_le_mul_right(
                            np_eq.clone(),
                            nq_ep.clone(),
                            es_es.clone(),
                            h.clone(),
                            h_es_es,
                        );
                        // leU : U1 ≤ U2  — transport hscale (scaled_l ≤ scaled_r) back:
                        //   subst left U1=scaled_l : need scaled_l→U1 i.e. symm u1_eq;
                        //   then subst right scaled_r→U2 i.e. u2_eq.
                        let u1_eq_sym = c.symm_int(u1.clone(), scaled_l.clone(), u1_eq);
                        let u2_eq_sym = c.symm_int(u2.clone(), scaled_r.clone(), u2_eq);
                        let le_u_l =
                            c.le_subst_left(&bs, &scaled_r, &scaled_l, &u1, &u1_eq_sym, &hscale);
                        let le_u = c.le_subst_right(&bs, &u1, &scaled_r, &u2, &u2_eq_sym, &le_u_l);

                        // Combine: add T1 U1 ≤ add T2 U2.
                        //   step : add T2 U1 ≤ add T2 U2   [add_le_add_left U1 U2 le_u T2]
                        let add_t2_u1 = c.add(t2.clone(), u1.clone());
                        let add_t1_u1 = c.add(t1.clone(), u1.clone());
                        let step = c.add_le_add_left_int(u1.clone(), u2.clone(), le_u, t2.clone());
                        //   rewrite add T2 U1 → add T1 U1 (left-arg) via symm eq_t:
                        let eq_t_sym = c.symm_int(t1.clone(), t2.clone(), eq_t);
                        //   congr_eq : add T2 U1 = add T1 U1   [congrArg (·+U1) (symm eq_t)]
                        let congr_eq = c.congr_arg(
                            t2.clone(),
                            t1.clone(),
                            c.add_left_fn(&bs, u1.clone()),
                            eq_t_sym,
                        );
                        // le_t1u1 : add T1 U1 ≤ add T2 U2   [subst step's LHS along congr_eq]
                        let add_t2_u2 = c.add(t2.clone(), u2.clone());
                        let le_t1u1 = c.le_subst_left(
                            &bs, &add_t2_u2, &add_t2_u1, &add_t1_u1, &congr_eq, &step,
                        );
                        // Transport endpoints to the actual goal via d1 (LHS=add T1 U1)
                        // and d2 (RHS=add T2 U2): goal is `Int.le LHS RHS`.
                        //   le_lhs : LHS ≤ add T2 U2  [subst le_t1u1 left along symm d1]
                        let lhs_mul = c.mul(l_num.clone(), es_eq.clone());
                        // d1 : lhs_mul = add T1 U1 ; d1_sym : add T1 U1 = lhs_mul.
                        let d1_sym = c.symm_int(lhs_mul.clone(), add_t1_u1.clone(), d1);
                        // d1 above is `lhs_mul = add T1 U1`; d1_sym : add T1 U1 = lhs_mul. We need
                        // to rewrite le_t1u1's LHS (add T1 U1) → lhs_mul, so use d1_sym.
                        let le_lhs = c.le_subst_left(
                            &bs, &add_t2_u2, &add_t1_u1, &lhs_mul, &d1_sym, &le_t1u1,
                        );
                        // d2 : (ns·Eq+nq·Es)·(Es·Ep) = add T2 U2 ; rewrite RHS (add T2 U2)→rhs_mul.
                        let rhs_mul = c.mul(r_num.clone(), es_ep.clone());
                        let d2_sym = c.symm_int(rhs_mul.clone(), add_t2_u2.clone(), d2);
                        let body =
                            c.le_subst_right(&bs, &lhs_mul, &add_t2_u2, &rhs_mul, &d2_sym, &le_lhs);

                        let lam = bs.mk_lam(h_id, BinderInfo::Default, le_pq, body);
                        let lam = bs.mk_lam(s_id, BinderInfo::Default, c.raw.clone(), lam);
                        bs.finish_child(lam)
                    };

                    // @Quot.ind Raw Equiv beta_c minor_c : ∀ c, beta_c c.
                    let ind_c = Expr::apps(
                        c.quot_ind.clone(),
                        [c.raw.clone(), c.raw_equiv.clone(), beta_c, minor_c],
                    );
                    let lam = bq.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), ind_c);
                    bq.finish_child(lam)
                };

                let ind_b = Expr::apps(
                    c.quot_ind.clone(),
                    [c.raw.clone(), c.raw_equiv.clone(), beta_b, minor_b],
                );
                let lam = bp.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), ind_b);
                bp.finish_child(lam)
            };

            let ind_a = Expr::apps(
                c.quot_ind.clone(),
                [
                    c.raw.clone(),
                    c.raw_equiv.clone(),
                    beta_a,
                    minor_a,
                    a.clone(),
                ],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), ind_a);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name: worker_name.clone(),
            level_params: vec![],
            type_: ty,
            value,
        })?;

        // Public wrapper with the canonical binder order
        // `∀ a b, le a b → ∀ c, le (add c a)(add c b)`:
        //   fun a b (h : le a b) c => worker a b c h.
        let pub_ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let (b_id, bvar) = b.fresh_local(c.ratq.clone());
            let le_ab = Expr::apps(ratq_le.clone(), [a.clone(), bvar.clone()]);
            let (h_id, _h) = b.fresh_local(le_ab.clone());
            let (cc_id, cvar) = b.fresh_local(c.ratq.clone());
            let add_ca = Expr::apps(ratq_add.clone(), [cvar.clone(), a.clone()]);
            let add_cb = Expr::apps(ratq_add.clone(), [cvar.clone(), bvar.clone()]);
            let goal = Expr::apps(ratq_le.clone(), [add_ca, add_cb]);
            let e = b.mk_pi(cc_id, BinderInfo::Default, c.ratq.clone(), goal);
            let e = b.mk_pi(h_id, BinderInfo::Default, le_ab, e);
            let e = b.mk_pi(b_id, BinderInfo::Default, c.ratq.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), e);
            b.finish(e)
        };
        let pub_val = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let (b_id, bvar) = b.fresh_local(c.ratq.clone());
            let le_ab = Expr::apps(ratq_le.clone(), [a.clone(), bvar.clone()]);
            let (h_id, h) = b.fresh_local(le_ab.clone());
            let (cc_id, cvar) = b.fresh_local(c.ratq.clone());
            let worker = Expr::const_(worker_name.clone(), vec![]);
            // worker a b c h.
            let body = Expr::apps(worker, [a.clone(), bvar.clone(), cvar.clone(), h.clone()]);
            let e = b.mk_lam(cc_id, BinderInfo::Default, c.ratq.clone(), body);
            let e = b.mk_lam(h_id, BinderInfo::Default, le_ab, e);
            let e = b.mk_lam(b_id, BinderInfo::Default, c.ratq.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: pub_ty,
            value: pub_val,
        })
    }

    /// `Qat.le_add_of_nonneg_right : ∀ a b : Qat,
    ///     Qat.le Qat.zero b → Qat.le a (Qat.add a b)`.
    ///
    /// Nested `Quot.ind` on `a, b`. For reps `p, q` the hypothesis
    /// `h : le 0 (mk q)` reduces to `Int.le (0·Eq) (nq·E0)` (≡ `0 ≤ nq` after
    /// the `0·Eq = 0` and `nq·ofNat 1 = nq` reductions), and the goal to
    ///   `np·(Ep·Eq)  ≤  (np·Eq + nq·Ep)·Ep`.
    /// RHS `right_distrib`s into `(np·Eq)·Ep + (nq·Ep)·Ep`; the first summand
    /// equals `np·(Ep·Eq)` (shuffle), and the second is `≥ 0` (scale `0 ≤ nq`
    /// by the nonneg `Ep·Ep`), so `a ≤ a + nonneg` via `Int.add_le_add_left` +
    /// `Int.add_zero`.
    fn register_rat_q_le_add_of_nonneg_right(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.le_add_of_nonneg_right");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }
        let ratq_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
        let ratq_add = Expr::const_(Name::from_string("Rat.add"), vec![]);
        let ratq_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);

        // `∀ b, le 0 b → le a (add a b)` for a given Qat term `a`.
        let inner_forall = |a: &Expr, parent: &EnvDeclBuilder| -> Expr {
            let mut bb = EnvDeclBuilder::child_of(parent);
            let (b_id, bvar) = bb.fresh_local(c.ratq.clone());
            let le_0b = Expr::apps(ratq_le.clone(), [ratq_zero.clone(), bvar.clone()]);
            let add_ab = Expr::apps(ratq_add.clone(), [a.clone(), bvar.clone()]);
            let goal = Expr::apps(ratq_le.clone(), [a.clone(), add_ab]);
            let (h_id, _h) = bb.fresh_local(le_0b.clone());
            let e = bb.mk_pi(h_id, BinderInfo::Default, le_0b, goal);
            bb.mk_pi(b_id, BinderInfo::Default, c.ratq.clone(), e)
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let body = inner_forall(&a, &b);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), body);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());

            let beta_a = {
                let mut bm = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = bm.fresh_local(c.ratq.clone());
                let body = inner_forall(&x, &bm);
                let lam = bm.mk_lam(x_id, BinderInfo::Default, c.ratq.clone(), body);
                bm.finish_child(lam)
            };

            let minor_a = {
                let mut bp = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bp.fresh_local(c.raw.clone());
                let mk_p = c.quot_mk(p.clone());

                // Inner motive Bb := fun b => le 0 b → le (mk p)(add (mk p) b).
                let beta_b = {
                    let mut bmb = EnvDeclBuilder::child_of(&bp);
                    let (y_id, y) = bmb.fresh_local(c.ratq.clone());
                    let le_0y = Expr::apps(ratq_le.clone(), [ratq_zero.clone(), y.clone()]);
                    let add_py = Expr::apps(ratq_add.clone(), [mk_p.clone(), y.clone()]);
                    let goal = Expr::apps(ratq_le.clone(), [mk_p.clone(), add_py]);
                    let (h_id, _h) = bmb.fresh_local(le_0y.clone());
                    let body = bmb.mk_pi(h_id, BinderInfo::Default, le_0y, goal);
                    let e = bmb.mk_lam(y_id, BinderInfo::Default, c.ratq.clone(), body);
                    bmb.finish_child(e)
                };

                let minor_b = {
                    let mut bq = EnvDeclBuilder::child_of(&bp);
                    let (q_id, q) = bq.fresh_local(c.raw.clone());
                    let mk_q = c.quot_mk(q.clone());
                    let le_0q = Expr::apps(ratq_le.clone(), [ratq_zero.clone(), mk_q.clone()]);
                    let (h_id, h) = bq.fresh_local(le_0q.clone());

                    let np = c.num(p.clone());
                    let nq = c.num(q.clone());
                    let ep = c.eff(p.clone());
                    let eq = c.eff(q.clone());

                    // h : le 0 (mk q) ≡ Int.le (Int.mul Int.zero Eq) (nq · E0)
                    //   where E0 = c.eff(raw_zero) ≡ ofNat 1.
                    //   Reductions: Int.mul Int.zero Eq = 0 [zero_mul]; nq · ofNat 1 = nq [mul_one].
                    // Convert h to h0 : Int.le 0 nq.
                    let nat_one = Expr::app(c.nat_succ.clone(), c.nat_zero.clone());
                    let raw_zero = c.raw_mk(c.int_zero.clone(), nat_one.clone());
                    let e0 = c.eff(raw_zero.clone());
                    let zero_eq = c.mul(c.int_zero.clone(), eq.clone());
                    let nq_e0 = c.mul(nq.clone(), e0.clone());
                    // h : Int.le zero_eq nq_e0. Rewrite LHS zero_eq → 0 and RHS nq_e0 → nq.
                    //   z1 : zero_eq = 0  [zero_mul Eq]
                    let z1 = c.zero_mul(eq.clone());
                    //   m1 : nq_e0 = nq    [mul_one nq]  (E0 ≡ ofNat 1 defeq)
                    let m1 = c.mul_one(nq.clone());
                    let h_a = c.le_subst_left(&bq, &nq_e0, &zero_eq, &c.int_zero.clone(), &z1, &h);
                    let h0 = c.le_subst_right(&bq, &c.int_zero.clone(), &nq_e0, &nq, &m1, &h_a);

                    // Goal: Int.le (np·E(Raw.add p q)) ((np·Eq + nq·Ep)·Ep)
                    //   E(Raw.add p q) ≡ Ep·Eq (defeq).
                    let ep_eq = c.mul(ep.clone(), eq.clone());
                    let np_epeq = c.mul(np.clone(), ep_eq.clone()); // LHS goal
                    let np_eq = c.mul(np.clone(), eq.clone());
                    let nq_ep = c.mul(nq.clone(), ep.clone());
                    let add_num = c.add(np_eq.clone(), nq_ep.clone());
                    let rhs_goal = c.mul(add_num.clone(), ep.clone());

                    // d : rhs_goal = add ((np·Eq)·Ep) ((nq·Ep)·Ep)  [right_distrib]
                    let t = c.mul(np_eq.clone(), ep.clone());
                    let u = c.mul(nq_ep.clone(), ep.clone());
                    let add_tu = c.add(t.clone(), u.clone());
                    let d = c.right_distrib(np_eq.clone(), nq_ep.clone(), ep.clone());

                    // eqT : np_epeq = t.
                    //   np·(Ep·Eq) = (np·Ep)·Eq  [symm mul_assoc np Ep Eq]
                    let np_ep = c.mul(np.clone(), ep.clone());
                    let np_ep_eq = c.mul(np_ep.clone(), eq.clone());
                    let a1 = c.symm_int(
                        np_ep_eq.clone(),
                        np_epeq.clone(),
                        c.mul_assoc(np.clone(), ep.clone(), eq.clone()),
                    );
                    //   (np·Ep)·Eq = (np·Eq)·Ep ? No: we want t = (np·Eq)·Ep.
                    //   (np·Ep)·Eq = (np·Eq)·Ep via mmmc2? mmc2 (a·b)·(c·d)=(a·d)·(c·b).
                    //   Treat (np·Ep)·Eq as (np·Ep)·(Eq·1)? messy. Use:
                    //   (np·Ep)·Eq = np·(Ep·Eq) [mul_assoc] = np·(Eq·Ep) [congr mul_comm]
                    //             = (np·Eq)·Ep [symm mul_assoc].
                    let eq_ep = c.mul(eq.clone(), ep.clone());
                    let np_eqep = c.mul(np.clone(), eq_ep.clone());
                    //   a2 : (np·Ep)·Eq = np·(Ep·Eq)  [mul_assoc np Ep Eq]
                    let a2 = c.mul_assoc(np.clone(), ep.clone(), eq.clone());
                    //   a3 : np·(Ep·Eq) = np·(Eq·Ep)  [congrArg (np·)(mul_comm Ep Eq)]
                    let a3 = c.congr_arg(
                        ep_eq.clone(),
                        eq_ep.clone(),
                        c.mul_left_fn(&bq, np.clone()),
                        c.mul_comm(ep.clone(), eq.clone()),
                    );
                    //   a4 : np·(Eq·Ep) = (np·Eq)·Ep = t  [symm mul_assoc np Eq Ep]
                    let a4 = c.symm_int(
                        t.clone(),
                        np_eqep.clone(),
                        c.mul_assoc(np.clone(), eq.clone(), ep.clone()),
                    );
                    let e1 = c.trans_int(np_epeq.clone(), np_ep_eq.clone(), np_eqep.clone(), a1, {
                        // a2 then a3 : (np·Ep)·Eq = np·(Eq·Ep)
                        c.trans_int(np_ep_eq.clone(), np_epeq.clone(), np_eqep.clone(), a2, a3)
                    });
                    let eq_t = c.trans_int(np_epeq.clone(), np_eqep.clone(), t.clone(), e1, a4);

                    // u ≥ 0 : 0 ≤ (nq·Ep)·Ep.
                    //   (nq·Ep)·Ep = nq·(Ep·Ep) [mul_assoc], and nq≥0, Ep·Ep≥0.
                    let ep_ep = c.mul(ep.clone(), ep.clone());
                    let nq_epep = c.mul(nq.clone(), ep_ep.clone());
                    let hep = c.nonneg_eff(&p); // 0 ≤ Ep
                    let h_epep = c.mul_nonneg(ep.clone(), ep.clone(), hep.clone(), hep); // 0 ≤ Ep·Ep
                    let u_nonneg0 = c.mul_nonneg(nq.clone(), ep_ep.clone(), h0, h_epep); // 0 ≤ nq·(Ep·Ep)
                                                                                         //   transport to 0 ≤ u along (nq·(Ep·Ep) = (nq·Ep)·Ep) = symm mul_assoc.
                    let u_eq = c.symm_int(
                        u.clone(),
                        nq_epep.clone(),
                        c.mul_assoc(nq.clone(), ep.clone(), ep.clone()),
                    );
                    let u_nonneg =
                        c.le_subst_right(&bq, &c.int_zero.clone(), &nq_epep, &u, &u_eq, &u_nonneg0);

                    // `t ≤ add t u`:  t = t + 0 ≤ t + u  via add_le_add_left 0 u u_nonneg t.
                    //   step : add t 0 ≤ add t u   [add_le_add_left 0 u u_nonneg t]
                    let add_t0 = c.add(t.clone(), c.int_zero.clone());
                    let step =
                        c.add_le_add_left_int(c.int_zero.clone(), u.clone(), u_nonneg, t.clone());
                    //   add_t0 = t  [add_zero t] ; rewrite step LHS add_t0 → t.
                    let t_eq = c.add_zero(t.clone());
                    let t_le_tu = c.le_subst_left(&bq, &add_tu, &add_t0, &t, &t_eq, &step);
                    //   rewrite LHS t → np_epeq (= goal LHS) via symm eq_t.
                    let eq_t_sym = c.symm_int(np_epeq.clone(), t.clone(), eq_t);
                    let lhs_le = c.le_subst_left(&bq, &add_tu, &t, &np_epeq, &eq_t_sym, &t_le_tu);
                    //   rewrite RHS add_tu → rhs_goal via symm d.
                    let d_sym = c.symm_int(rhs_goal.clone(), add_tu.clone(), d);
                    let body = c.le_subst_right(&bq, &np_epeq, &add_tu, &rhs_goal, &d_sym, &lhs_le);

                    let lam = bq.mk_lam(h_id, BinderInfo::Default, le_0q, body);
                    let lam = bq.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), lam);
                    bq.finish_child(lam)
                };

                let ind_b = Expr::apps(
                    c.quot_ind.clone(),
                    [c.raw.clone(), c.raw_equiv.clone(), beta_b, minor_b],
                );
                let lam = bp.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), ind_b);
                bp.finish_child(lam)
            };

            let ind_a = Expr::apps(
                c.quot_ind.clone(),
                [
                    c.raw.clone(),
                    c.raw_equiv.clone(),
                    beta_a,
                    minor_a,
                    a.clone(),
                ],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), ind_a);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// 5c. `Rat.inv : Rat → Rat`, a unary `Quot.lift` of the sign-split
    /// `Raw.inv`.
    ///
    /// Well-definedness (respect): from `hp : Equiv p p'` (`np·Ep' = np'·Ep`)
    /// build `Eq Rat (Quot.mk (Raw.inv p)) (Quot.mk (Raw.inv p'))` by a nested
    /// `Int.rec.{0}` on the numerators `np = num p`, `np' = num p'` (with the
    /// ofNat branch further split by `Nat.rec.{0}` into zero / positive). The
    /// motive generalizes the goal over the scrutinee AND carries `hp`'s type as
    /// a hypothesis, so each of the nine sign-leaves receives the specialized
    /// `h`. Six mixed/zero-cross leaves are impossible and discharged by
    /// `Int.noConfusion` (and one `Nat.noConfusion` for the `ofNat`-field
    /// `0 = succ _` collisions); the three matching leaves close by `Quot.sound`
    /// of an `Int` cross identity (`mul_comm` / `neg_mul_left`).
    fn register_rat_q_inv(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("Rat.inv")).is_some() {
            return Ok(());
        }

        let inv_type = Expr::pi(BinderInfo::Default, c.ratq.clone(), c.ratq.clone());
        let inv_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());

            // f := λ (p : Raw) => Quot.mk (Raw.inv p).
            let lift_f = {
                let mut bi = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bi.fresh_local(c.raw.clone());
                let body = c.quot_mk(c.raw_inv(&bi, &p));
                let lam = bi.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), body);
                bi.finish_child(lam)
            };

            // h := λ (p p' : Raw)(hp : Equiv p p') => <respect>.
            let lift_h = {
                let mut bi = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bi.fresh_local(c.raw.clone());
                let (p2_id, p2) = bi.fresh_local(c.raw.clone());
                let hyp = c.equiv(p.clone(), p2.clone());
                let (hp_id, hp) = bi.fresh_local(hyp.clone());

                let body = c.inv_respect(&bi, &p, &p2, &hp);
                let lam = bi.mk_lam(hp_id, BinderInfo::Default, hyp, body);
                let lam = bi.mk_lam(p2_id, BinderInfo::Default, c.raw.clone(), lam);
                let lam = bi.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), lam);
                bi.finish_child(lam)
            };

            let body = Expr::apps(
                c.quot_lift.clone(),
                [
                    c.raw.clone(),
                    c.raw_equiv.clone(),
                    c.ratq.clone(),
                    lift_f,
                    lift_h,
                    a.clone(),
                ],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("Rat.inv"),
            level_params: vec![],
            type_: inv_type,
            value: inv_value,
            is_reducible: true,
        })
    }

    /// 5c'. `Rat.div a b := Rat.mul a (Rat.inv b)`.
    fn register_rat_q_div(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("Rat.div")).is_some() {
            return Ok(());
        }
        let ratq_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let ratq_inv = Expr::const_(Name::from_string("Rat.inv"), vec![]);
        let div_type = Expr::pi(
            BinderInfo::Default,
            c.ratq.clone(),
            Expr::pi(BinderInfo::Default, c.ratq.clone(), c.ratq.clone()),
        );
        let div_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let (bv_id, bv) = b.fresh_local(c.ratq.clone());
            let inv_bv = Expr::app(ratq_inv.clone(), bv);
            let body = Expr::apps(ratq_mul.clone(), [a, inv_bv]);
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.ratq.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("Rat.div"),
            level_params: vec![],
            type_: div_type,
            value: div_value,
            is_reducible: true,
        })
    }

    /// `Rat.add_assoc : ∀ a b c : Rat,
    ///     @Eq Rat (Rat.add (Rat.add a b) c) (Rat.add a (Rat.add b c))`.
    ///
    /// Triple `Quot.ind`. The Equiv `num_L·eff_R = num_R·eff_L` is a
    /// commutative-ring SUM identity (three degree-6 monomials a side): each
    /// numerator is `right_distrib`-flattened to a 3-monomial sum, scaled by the
    /// opposite effDenom (`mul_sum_right`), and the two scaled sums matched by
    /// the generic `sum_eq` (monomial permutation + per-monomial `prod_eq`).
    fn register_rat_q_add_assoc(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.add_assoc");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }
        let ratq_add = Expr::const_(Name::from_string("Rat.add"), vec![]);

        let inner_forall = |a: &Expr, parent: &EnvDeclBuilder| -> Expr {
            let mut bb = EnvDeclBuilder::child_of(parent);
            let (b_id, bvar) = bb.fresh_local(c.ratq.clone());
            let (cc_id, cvar) = bb.fresh_local(c.ratq.clone());
            let add_ab = Expr::apps(ratq_add.clone(), [a.clone(), bvar.clone()]);
            let lhs = Expr::apps(ratq_add.clone(), [add_ab, cvar.clone()]);
            let add_bc = Expr::apps(ratq_add.clone(), [bvar.clone(), cvar.clone()]);
            let rhs = Expr::apps(ratq_add.clone(), [a.clone(), add_bc]);
            let goal = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, rhs]);
            let e = bb.mk_pi(cc_id, BinderInfo::Default, c.ratq.clone(), goal);
            bb.mk_pi(b_id, BinderInfo::Default, c.ratq.clone(), e)
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let body = inner_forall(&a, &b);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), body);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());

            let beta_a = {
                let mut bm = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = bm.fresh_local(c.ratq.clone());
                let body = inner_forall(&x, &bm);
                let lam = bm.mk_lam(x_id, BinderInfo::Default, c.ratq.clone(), body);
                bm.finish_child(lam)
            };

            let minor_a = {
                let mut bp = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bp.fresh_local(c.raw.clone());
                let mk_p = c.quot_mk(p.clone());

                let beta_b = {
                    let mut bmb = EnvDeclBuilder::child_of(&bp);
                    let (y_id, y) = bmb.fresh_local(c.ratq.clone());
                    let body = {
                        let mut bc = EnvDeclBuilder::child_of(&bmb);
                        let (cc_id, cvar) = bc.fresh_local(c.ratq.clone());
                        let add_py = Expr::apps(ratq_add.clone(), [mk_p.clone(), y.clone()]);
                        let lhs = Expr::apps(ratq_add.clone(), [add_py, cvar.clone()]);
                        let add_yc = Expr::apps(ratq_add.clone(), [y.clone(), cvar.clone()]);
                        let rhs = Expr::apps(ratq_add.clone(), [mk_p.clone(), add_yc]);
                        let goal = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, rhs]);
                        let e = bc.mk_pi(cc_id, BinderInfo::Default, c.ratq.clone(), goal);
                        bc.finish_child(e)
                    };
                    let lam = bmb.mk_lam(y_id, BinderInfo::Default, c.ratq.clone(), body);
                    bmb.finish_child(lam)
                };

                let minor_b = {
                    let mut bq = EnvDeclBuilder::child_of(&bp);
                    let (q_id, q) = bq.fresh_local(c.raw.clone());
                    let mk_q = c.quot_mk(q.clone());

                    let beta_c = {
                        let mut bmc = EnvDeclBuilder::child_of(&bq);
                        let (z_id, z) = bmc.fresh_local(c.ratq.clone());
                        let add_pq = Expr::apps(ratq_add.clone(), [mk_p.clone(), mk_q.clone()]);
                        let lhs = Expr::apps(ratq_add.clone(), [add_pq, z.clone()]);
                        let add_qz = Expr::apps(ratq_add.clone(), [mk_q.clone(), z.clone()]);
                        let rhs = Expr::apps(ratq_add.clone(), [mk_p.clone(), add_qz]);
                        let body = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, rhs]);
                        let e = bmc.mk_lam(z_id, BinderInfo::Default, c.ratq.clone(), body);
                        bmc.finish_child(e)
                    };

                    let minor_c = {
                        let mut br = EnvDeclBuilder::child_of(&bq);
                        let (r_id, r) = br.fresh_local(c.raw.clone());

                        let eqv = c.add_assoc_cross(&br, &p, &q, &r);
                        let raw_x = c.raw_add(&c.raw_add(&p, &q), &r);
                        let raw_y = c.raw_add(&p, &c.raw_add(&q, &r));
                        let sound = c.quot_sound(raw_x, raw_y, eqv);
                        let lam = br.mk_lam(r_id, BinderInfo::Default, c.raw.clone(), sound);
                        br.finish_child(lam)
                    };

                    let ind_c = Expr::apps(
                        c.quot_ind.clone(),
                        [c.raw.clone(), c.raw_equiv.clone(), beta_c, minor_c],
                    );
                    let lam = bq.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), ind_c);
                    bq.finish_child(lam)
                };

                let ind_b = Expr::apps(
                    c.quot_ind.clone(),
                    [c.raw.clone(), c.raw_equiv.clone(), beta_b, minor_b],
                );
                let lam = bp.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), ind_b);
                bp.finish_child(lam)
            };

            let ind_a = Expr::apps(
                c.quot_ind.clone(),
                [
                    c.raw.clone(),
                    c.raw_equiv.clone(),
                    beta_a,
                    minor_a,
                    a.clone(),
                ],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), ind_a);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.add_zero : ∀ a : Rat, @Eq Rat (Rat.add a Rat.zero) a`.
    ///
    /// `Quot.ind` on `a`. For rep `p`, `add p zero01 = raw_mk (np·E0 + 0·Ep)
    /// (Ep·1)` where `zero01 = raw_mk 0 1`, `E0 = ofNat 1`. The Equiv
    /// `(raw_add p zero01) ≈ p` is `Eq Int (num_L · Ep) (np · eff(raw_add …))`;
    /// `num_L → np` (`mul_one` + `zero_mul` + `add_zero`) and
    /// `eff(raw_add …) ≡ Ep·(ofNat 1)` (defeq), closing both sides to `np·Ep`.
    fn register_rat_q_add_zero(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.add_zero");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }
        let ratq_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let ratq_add = Expr::const_(Name::from_string("Rat.add"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let lhs = Expr::apps(ratq_add.clone(), [a.clone(), ratq_zero.clone()]);
            let goal = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, a.clone()]);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), goal);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());

            let beta = {
                let mut bm = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = bm.fresh_local(c.ratq.clone());
                let lhs = Expr::apps(ratq_add.clone(), [x.clone(), ratq_zero.clone()]);
                let body = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, x.clone()]);
                let lam = bm.mk_lam(x_id, BinderInfo::Default, c.ratq.clone(), body);
                bm.finish_child(lam)
            };

            let minor = {
                let mut bn = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bn.fresh_local(c.raw.clone());

                let np = c.num(p.clone());
                let ep = c.eff(p.clone());
                let nat_one = c.nsucc(c.nat_zero.clone());
                let zero01 = c.raw_mk(c.int_zero.clone(), nat_one.clone());
                let e0 = c.eff(zero01.clone()); // ≡ ofNat 1

                // raw_lhs := raw_add p zero01 ; num_L = np·E0 + n0·Ep with n0 = 0.
                let raw_lhs = c.raw_add(&p, &zero01);
                let np_e0 = c.mul(np.clone(), e0.clone());
                let zero_ep = c.mul(c.int_zero.clone(), ep.clone());
                let num_l = c.add(np_e0.clone(), zero_ep.clone());

                // Equiv (raw_lhs) p ≡ Eq Int (num_L · eff p) (np · eff raw_lhs).
                let eff_p = c.eff(p.clone());
                let eff_lhs = c.eff(raw_lhs.clone());
                let lhs_t = c.mul(num_l.clone(), eff_p.clone());
                let rhs_t = c.mul(np.clone(), eff_lhs.clone());

                // num_L → np :  np·E0 + 0·Ep = np + 0 = np.
                //   a1 : np·E0 = np    [mul_one np]  (E0 ≡ ofNat 1)
                let a1 = c.mul_one(np.clone());
                //   a2 : 0·Ep = 0      [zero_mul Ep]
                let a2 = c.zero_mul(ep.clone());
                //   numl = np + 0      [add_cong a1 a2]
                let np_plus_zero = c.add(np.clone(), c.int_zero.clone());
                let numl_to_np0 =
                    c.add_cong(&bn, &np_e0, &np, &zero_ep, &c.int_zero.clone(), &a1, &a2);
                //   np + 0 = np        [add_zero np]
                let a3 = c.add_zero(np.clone());
                let numl_to_np = c.trans_int(
                    num_l.clone(),
                    np_plus_zero.clone(),
                    np.clone(),
                    numl_to_np0,
                    a3,
                );

                // lhs_t = num_L·Ep → np·Ep   [congrArg (·*Ep) numl_to_np]
                let np_ep = c.mul(np.clone(), eff_p.clone());
                let lhs_to = c.congr_arg(
                    num_l.clone(),
                    np.clone(),
                    c.mul_right_fn(&bn, eff_p.clone()),
                    numl_to_np,
                );
                // rhs_t = np·eff_lhs. eff_lhs ≡ Ep·(ofNat 1) (defeq); np·(Ep·ofNat1)
                //   = np·Ep via congrArg (np·)(mul_one Ep).
                let ep_one = c.mul(ep.clone(), c.of_nat(nat_one.clone()));
                // m1 : Ep·ofNat1 = Ep  [mul_one Ep]
                let m1 = c.mul_one(ep.clone());
                // rhs_t = np·(Ep·ofNat1) [defeq to np·eff_lhs] ; rewrite to np·Ep.
                let np_epone = c.mul(np.clone(), ep_one.clone());
                let rhs_cong = c.congr_arg(
                    ep_one.clone(),
                    ep.clone(),
                    c.mul_left_fn(&bn, np.clone()),
                    m1,
                );
                // rhs_cong : np·(Ep·ofNat1) = np·Ep ; np·(Ep·ofNat1) ≡ rhs_t (defeq).
                // rhs_back : np·Ep = rhs_t  via symm.
                let rhs_back = c.symm_int(np_epone.clone(), np_ep.clone(), rhs_cong);
                // eqv : lhs_t = rhs_t  via  lhs_t = np·Ep = rhs_t.
                let eqv = c.trans_int(
                    lhs_t.clone(),
                    np_ep.clone(),
                    rhs_t.clone(),
                    lhs_to,
                    rhs_back,
                );

                let sound = c.quot_sound(raw_lhs.clone(), p.clone(), eqv);
                let lam = bn.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), sound);
                bn.finish_child(lam)
            };

            let ind = Expr::apps(
                c.quot_ind.clone(),
                [c.raw.clone(), c.raw_equiv.clone(), beta, minor, a.clone()],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), ind);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.left_distrib : ∀ a b c : Rat,
    ///     @Eq Rat (Rat.mul a (Rat.add b c)) (Rat.add (Rat.mul a b) (Rat.mul a c))`.
    ///
    /// Triple `Quot.ind` on `a, b, c`. For reps `p, q, r` the goal is
    /// `Eq Rat (mk X) (mk Y)` with
    ///   `X := raw_mul p (raw_add q r)`,
    ///   `Y := raw_add (raw_mul p q) (raw_mul p r)`,
    /// closed by `Quot.sound X Y eqv`. The Equiv `eqv : num X · eff Y =
    /// num Y · eff X` is a degree-7 commutative-ring monomial identity: both
    /// sides `right_distrib` into two monomials whose leaf multisets coincide,
    /// closed term-by-term by the generic `prod_eq` normalizer.
    fn register_rat_q_left_distrib(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.left_distrib");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }
        let ratq_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let ratq_add = Expr::const_(Name::from_string("Rat.add"), vec![]);

        // `∀ b c, mul a (add b c) = add (mul a b)(mul a c)` for a given `a`.
        let inner_forall = |a: &Expr, parent: &EnvDeclBuilder| -> Expr {
            let mut bb = EnvDeclBuilder::child_of(parent);
            let (b_id, bvar) = bb.fresh_local(c.ratq.clone());
            let (cc_id, cvar) = bb.fresh_local(c.ratq.clone());
            let add_bc = Expr::apps(ratq_add.clone(), [bvar.clone(), cvar.clone()]);
            let lhs = Expr::apps(ratq_mul.clone(), [a.clone(), add_bc]);
            let mul_ab = Expr::apps(ratq_mul.clone(), [a.clone(), bvar.clone()]);
            let mul_ac = Expr::apps(ratq_mul.clone(), [a.clone(), cvar.clone()]);
            let rhs = Expr::apps(ratq_add.clone(), [mul_ab, mul_ac]);
            let goal = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, rhs]);
            let e = bb.mk_pi(cc_id, BinderInfo::Default, c.ratq.clone(), goal);
            bb.mk_pi(b_id, BinderInfo::Default, c.ratq.clone(), e)
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let body = inner_forall(&a, &b);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), body);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());

            let beta_a = {
                let mut bm = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = bm.fresh_local(c.ratq.clone());
                let body = inner_forall(&x, &bm);
                let lam = bm.mk_lam(x_id, BinderInfo::Default, c.ratq.clone(), body);
                bm.finish_child(lam)
            };

            let minor_a = {
                let mut bp = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bp.fresh_local(c.raw.clone());
                let mk_p = c.quot_mk(p.clone());

                let beta_b = {
                    let mut bmb = EnvDeclBuilder::child_of(&bp);
                    let (y_id, y) = bmb.fresh_local(c.ratq.clone());
                    let body = {
                        let mut bc = EnvDeclBuilder::child_of(&bmb);
                        let (cc_id, cvar) = bc.fresh_local(c.ratq.clone());
                        let add_yc = Expr::apps(ratq_add.clone(), [y.clone(), cvar.clone()]);
                        let lhs = Expr::apps(ratq_mul.clone(), [mk_p.clone(), add_yc]);
                        let mul_py = Expr::apps(ratq_mul.clone(), [mk_p.clone(), y.clone()]);
                        let mul_pc = Expr::apps(ratq_mul.clone(), [mk_p.clone(), cvar.clone()]);
                        let rhs = Expr::apps(ratq_add.clone(), [mul_py, mul_pc]);
                        let goal = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, rhs]);
                        let e = bc.mk_pi(cc_id, BinderInfo::Default, c.ratq.clone(), goal);
                        bc.finish_child(e)
                    };
                    let lam = bmb.mk_lam(y_id, BinderInfo::Default, c.ratq.clone(), body);
                    bmb.finish_child(lam)
                };

                let minor_b = {
                    let mut bq = EnvDeclBuilder::child_of(&bp);
                    let (q_id, q) = bq.fresh_local(c.raw.clone());
                    let mk_q = c.quot_mk(q.clone());

                    let beta_c = {
                        let mut bmc = EnvDeclBuilder::child_of(&bq);
                        let (z_id, z) = bmc.fresh_local(c.ratq.clone());
                        let add_qz = Expr::apps(ratq_add.clone(), [mk_q.clone(), z.clone()]);
                        let lhs = Expr::apps(ratq_mul.clone(), [mk_p.clone(), add_qz]);
                        let mul_pq = Expr::apps(ratq_mul.clone(), [mk_p.clone(), mk_q.clone()]);
                        let mul_pz = Expr::apps(ratq_mul.clone(), [mk_p.clone(), z.clone()]);
                        let rhs = Expr::apps(ratq_add.clone(), [mul_pq, mul_pz]);
                        let body = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, rhs]);
                        let e = bmc.mk_lam(z_id, BinderInfo::Default, c.ratq.clone(), body);
                        bmc.finish_child(e)
                    };

                    let minor_c = {
                        let mut br = EnvDeclBuilder::child_of(&bq);
                        let (r_id, r) = br.fresh_local(c.raw.clone());

                        let np = c.num(p.clone());
                        let nq = c.num(q.clone());
                        let nr = c.num(r.clone());
                        let ep = c.eff(p.clone());
                        let eq = c.eff(q.clone());
                        let er = c.eff(r.clone());

                        let eqv =
                            c.distrib_cross(&br, &np, &nq, &nr, &ep, &eq, &er, /*left=*/ true);

                        // X := raw_mul p (raw_add q r) ; Y := raw_add (raw_mul p q)(raw_mul p r).
                        let raw_x = c.raw_mul(&p, &c.raw_add(&q, &r));
                        let raw_y = c.raw_add(&c.raw_mul(&p, &q), &c.raw_mul(&p, &r));
                        let sound = c.quot_sound(raw_x, raw_y, eqv);
                        let lam = br.mk_lam(r_id, BinderInfo::Default, c.raw.clone(), sound);
                        br.finish_child(lam)
                    };

                    let ind_c = Expr::apps(
                        c.quot_ind.clone(),
                        [c.raw.clone(), c.raw_equiv.clone(), beta_c, minor_c],
                    );
                    let lam = bq.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), ind_c);
                    bq.finish_child(lam)
                };

                let ind_b = Expr::apps(
                    c.quot_ind.clone(),
                    [c.raw.clone(), c.raw_equiv.clone(), beta_b, minor_b],
                );
                let lam = bp.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), ind_b);
                bp.finish_child(lam)
            };

            let ind_a = Expr::apps(
                c.quot_ind.clone(),
                [
                    c.raw.clone(),
                    c.raw_equiv.clone(),
                    beta_a,
                    minor_a,
                    a.clone(),
                ],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), ind_a);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.right_distrib : ∀ a b c : Rat,
    ///     @Eq Rat (Rat.mul (Rat.add a b) c) (Rat.add (Rat.mul a c) (Rat.mul b c))`.
    ///
    /// Same engine as `left_distrib`, with the sum on the LEFT factor of the
    /// multiplication.
    fn register_rat_q_right_distrib(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.right_distrib");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }
        let ratq_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let ratq_add = Expr::const_(Name::from_string("Rat.add"), vec![]);

        // `∀ b c, mul (add a b) c = add (mul a c)(mul b c)` for a given `a`.
        let inner_forall = |a: &Expr, parent: &EnvDeclBuilder| -> Expr {
            let mut bb = EnvDeclBuilder::child_of(parent);
            let (b_id, bvar) = bb.fresh_local(c.ratq.clone());
            let (cc_id, cvar) = bb.fresh_local(c.ratq.clone());
            let add_ab = Expr::apps(ratq_add.clone(), [a.clone(), bvar.clone()]);
            let lhs = Expr::apps(ratq_mul.clone(), [add_ab, cvar.clone()]);
            let mul_ac = Expr::apps(ratq_mul.clone(), [a.clone(), cvar.clone()]);
            let mul_bc = Expr::apps(ratq_mul.clone(), [bvar.clone(), cvar.clone()]);
            let rhs = Expr::apps(ratq_add.clone(), [mul_ac, mul_bc]);
            let goal = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, rhs]);
            let e = bb.mk_pi(cc_id, BinderInfo::Default, c.ratq.clone(), goal);
            bb.mk_pi(b_id, BinderInfo::Default, c.ratq.clone(), e)
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let body = inner_forall(&a, &b);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), body);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());

            let beta_a = {
                let mut bm = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = bm.fresh_local(c.ratq.clone());
                let body = inner_forall(&x, &bm);
                let lam = bm.mk_lam(x_id, BinderInfo::Default, c.ratq.clone(), body);
                bm.finish_child(lam)
            };

            let minor_a = {
                let mut bp = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bp.fresh_local(c.raw.clone());
                let mk_p = c.quot_mk(p.clone());

                let beta_b = {
                    let mut bmb = EnvDeclBuilder::child_of(&bp);
                    let (y_id, y) = bmb.fresh_local(c.ratq.clone());
                    let body = {
                        let mut bc = EnvDeclBuilder::child_of(&bmb);
                        let (cc_id, cvar) = bc.fresh_local(c.ratq.clone());
                        let add_py = Expr::apps(ratq_add.clone(), [mk_p.clone(), y.clone()]);
                        let lhs = Expr::apps(ratq_mul.clone(), [add_py, cvar.clone()]);
                        let mul_pc = Expr::apps(ratq_mul.clone(), [mk_p.clone(), cvar.clone()]);
                        let mul_yc = Expr::apps(ratq_mul.clone(), [y.clone(), cvar.clone()]);
                        let rhs = Expr::apps(ratq_add.clone(), [mul_pc, mul_yc]);
                        let goal = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, rhs]);
                        let e = bc.mk_pi(cc_id, BinderInfo::Default, c.ratq.clone(), goal);
                        bc.finish_child(e)
                    };
                    let lam = bmb.mk_lam(y_id, BinderInfo::Default, c.ratq.clone(), body);
                    bmb.finish_child(lam)
                };

                let minor_b = {
                    let mut bq = EnvDeclBuilder::child_of(&bp);
                    let (q_id, q) = bq.fresh_local(c.raw.clone());
                    let mk_q = c.quot_mk(q.clone());

                    let beta_c = {
                        let mut bmc = EnvDeclBuilder::child_of(&bq);
                        let (z_id, z) = bmc.fresh_local(c.ratq.clone());
                        let add_pq = Expr::apps(ratq_add.clone(), [mk_p.clone(), mk_q.clone()]);
                        let lhs = Expr::apps(ratq_mul.clone(), [add_pq, z.clone()]);
                        let mul_pz = Expr::apps(ratq_mul.clone(), [mk_p.clone(), z.clone()]);
                        let mul_qz = Expr::apps(ratq_mul.clone(), [mk_q.clone(), z.clone()]);
                        let rhs = Expr::apps(ratq_add.clone(), [mul_pz, mul_qz]);
                        let body = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, rhs]);
                        let e = bmc.mk_lam(z_id, BinderInfo::Default, c.ratq.clone(), body);
                        bmc.finish_child(e)
                    };

                    let minor_c = {
                        let mut br = EnvDeclBuilder::child_of(&bq);
                        let (r_id, r) = br.fresh_local(c.raw.clone());

                        let np = c.num(p.clone());
                        let nq = c.num(q.clone());
                        let nr = c.num(r.clone());
                        let ep = c.eff(p.clone());
                        let eq = c.eff(q.clone());
                        let er = c.eff(r.clone());

                        let eqv = c
                            .distrib_cross(&br, &np, &nq, &nr, &ep, &eq, &er, /*left=*/ false);

                        // X := raw_mul (raw_add p q) r ;
                        // Y := raw_add (raw_mul p r)(raw_mul q r).
                        let raw_x = c.raw_mul(&c.raw_add(&p, &q), &r);
                        let raw_y = c.raw_add(&c.raw_mul(&p, &r), &c.raw_mul(&q, &r));
                        let sound = c.quot_sound(raw_x, raw_y, eqv);
                        let lam = br.mk_lam(r_id, BinderInfo::Default, c.raw.clone(), sound);
                        br.finish_child(lam)
                    };

                    let ind_c = Expr::apps(
                        c.quot_ind.clone(),
                        [c.raw.clone(), c.raw_equiv.clone(), beta_c, minor_c],
                    );
                    let lam = bq.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), ind_c);
                    bq.finish_child(lam)
                };

                let ind_b = Expr::apps(
                    c.quot_ind.clone(),
                    [c.raw.clone(), c.raw_equiv.clone(), beta_b, minor_b],
                );
                let lam = bp.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), ind_b);
                bp.finish_child(lam)
            };

            let ind_a = Expr::apps(
                c.quot_ind.clone(),
                [
                    c.raw.clone(),
                    c.raw_equiv.clone(),
                    beta_a,
                    minor_a,
                    a.clone(),
                ],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), ind_a);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.add_right_cancel : ∀ a b c : Rat,
    ///     @Eq Rat (Rat.add a c) (Rat.add b c) → @Eq Rat a b`.
    ///
    /// Group-theoretic, from `Rat.add_assoc` + `Rat.add_zero` +
    /// `Rat.add_neg_self` (all proven over the quotient):
    ///   a = a+0 = a+(c+ -c) = (a+c)+ -c = (b+c)+ -c = b+(c+ -c) = b+0 = b.
    fn register_rat_q_add_right_cancel(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.add_right_cancel");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }
        let ratq_add = Expr::const_(Name::from_string("Rat.add"), vec![]);
        let ratq_neg = Expr::const_(Name::from_string("Rat.neg"), vec![]);
        let ratq_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let add_assoc = Expr::const_(Name::from_string("Rat.add_assoc"), vec![]);
        let add_zero = Expr::const_(Name::from_string("Rat.add_zero"), vec![]);
        let add_neg_self = Expr::const_(Name::from_string("Rat.add_neg_self"), vec![]);
        let radd = |x: &Expr, y: &Expr| Expr::apps(ratq_add.clone(), [x.clone(), y.clone()]);

        // PUBLIC signature (matches the original free-carrier axiom EXACTLY):
        //   ∀ a b c, @Eq Rat (add a b)(add c b) → @Eq Rat a c
        // i.e. the COMMON addend is the SECOND binder `b`, and the cancellation
        // compares the first `a` and third `c`. (Internally the algebra is "+b on
        // the right, cancel via -b".)
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let (bv_id, bv) = b.fresh_local(c.ratq.clone());
            let (cv_id, cv) = b.fresh_local(c.ratq.clone());
            let hyp = Expr::apps(
                c.eq_ratq.clone(),
                [c.ratq.clone(), radd(&a, &bv), radd(&cv, &bv)],
            );
            let concl = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), a.clone(), cv.clone()]);
            let (h_id, _h) = b.fresh_local(hyp.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let e = b.mk_pi(cv_id, BinderInfo::Default, c.ratq.clone(), e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.ratq.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            // `cmn` is the common (2nd) addend; `cv` is the second comparand
            // (3rd binder). The proof cancels `cmn` on the right.
            let (bv_id, cmn) = b.fresh_local(c.ratq.clone());
            let (cv_id, cv) = b.fresh_local(c.ratq.clone());
            let hyp = Expr::apps(
                c.eq_ratq.clone(),
                [c.ratq.clone(), radd(&a, &cmn), radd(&cv, &cmn)],
            );
            let (h_id, h) = b.fresh_local(hyp.clone());
            // Rebind the proof's internal names: the algebra below was written for
            // "cancel `cv` on the right, compare `a` and `bv`". Map cv → cmn (the
            // common addend) and bv → cv (the second comparand).
            let cv_alg = cmn.clone(); // common addend cancelled
            let bv = cv.clone(); // second comparand
            let cv = cv_alg;

            let neg_c = Expr::app(ratq_neg.clone(), cv.clone());
            let c_negc = radd(&cv, &neg_c); // c + -c
                                            // a = a + 0   [symm (add_zero a)]
            let a0 = radd(&a, &ratq_zero);
            let s1 = c.rsymm(
                a0.clone(),
                a.clone(),
                Expr::app(add_zero.clone(), a.clone()),
            );
            // a + 0 = a + (c + -c)   [congrArg (a + ·) (symm (add_neg_self c))]
            let ans = Expr::app(add_neg_self.clone(), cv.clone()); // c + -c = 0
            let ans_sym = c.rsymm(c_negc.clone(), ratq_zero.clone(), ans);
            // f := fun w => Rat.add a w
            let add_a_fn = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (w_id, w) = ch.fresh_local(c.ratq.clone());
                let body = Expr::apps(ratq_add.clone(), [a.clone(), w]);
                let lam = ch.mk_lam(w_id, BinderInfo::Default, c.ratq.clone(), body);
                ch.finish_child(lam)
            };
            let a_cnegc = radd(&a, &c_negc);
            let s2 = c.rcongr(ratq_zero.clone(), c_negc.clone(), add_a_fn, ans_sym);
            // a + (c + -c) = (a + c) + -c   [symm (add_assoc a c -c)]
            let ac = radd(&a, &cv);
            let ac_negc = radd(&ac, &neg_c);
            let assoc_a = Expr::apps(add_assoc.clone(), [a.clone(), cv.clone(), neg_c.clone()]);
            let s3 = c.rsymm(ac_negc.clone(), a_cnegc.clone(), assoc_a);
            // (a + c) + -c = (b + c) + -c   [congrArg (· + -c) h]
            let bc = radd(&bv, &cv);
            let bc_negc = radd(&bc, &neg_c);
            let s4 = c.rcongr(
                ac.clone(),
                bc.clone(),
                c.radd_left_fn(&b, neg_c.clone()),
                h.clone(),
            );
            // (b + c) + -c = b + (c + -c)   [add_assoc b c -c]
            let b_cnegc = radd(&bv, &c_negc);
            let assoc_b = Expr::apps(add_assoc.clone(), [bv.clone(), cv.clone(), neg_c.clone()]);
            let s5 = assoc_b;
            // b + (c + -c) = b + 0   [congrArg (b + ·) (add_neg_self c)]
            let add_b_fn = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (w_id, w) = ch.fresh_local(c.ratq.clone());
                let body = Expr::apps(ratq_add.clone(), [bv.clone(), w]);
                let lam = ch.mk_lam(w_id, BinderInfo::Default, c.ratq.clone(), body);
                ch.finish_child(lam)
            };
            let b0 = radd(&bv, &ratq_zero);
            let ans2 = Expr::app(add_neg_self.clone(), cv.clone());
            let s6 = c.rcongr(c_negc.clone(), ratq_zero.clone(), add_b_fn, ans2);
            // b + 0 = b   [add_zero b]
            let s7 = Expr::app(add_zero.clone(), bv.clone());

            // chain a = a+0 = a+(c+-c) = (a+c)+-c = (b+c)+-c = b+(c+-c) = b+0 = b.
            let c1 = c.rtrans(a.clone(), a0.clone(), a_cnegc.clone(), s1, s2);
            let c2 = c.rtrans(a.clone(), a_cnegc.clone(), ac_negc.clone(), c1, s3);
            let c3 = c.rtrans(a.clone(), ac_negc.clone(), bc_negc.clone(), c2, s4);
            let c4 = c.rtrans(a.clone(), bc_negc.clone(), b_cnegc.clone(), c3, s5);
            let c5 = c.rtrans(a.clone(), b_cnegc.clone(), b0.clone(), c4, s6);
            let body = c.rtrans(a.clone(), b0.clone(), bv.clone(), c5, s7);

            let e = b.mk_lam(h_id, BinderInfo::Default, hyp, body);
            let e = b.mk_lam(cv_id, BinderInfo::Default, c.ratq.clone(), e);
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.ratq.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.mul_inv_cancel : ∀ a : Rat,
    ///     (@Eq Rat a Rat.zero → False) → @Eq Rat (Rat.mul a (Rat.inv a)) Rat.one`.
    ///
    /// `Quot.ind` on `a`, then an inner `Int.rec`/`Nat.rec` on `num p` THAT
    /// CARRIES the scrutinee equation `heq : num p = z` (via the motive), so the
    /// zero leaf knows `np = 0` and derives `mk p = zero`, contradicting the
    /// `a ≠ 0` hypothesis through `False.elim`. The positive / negative leaves
    /// reduce `mul (mk p)(inv (mk p))` to a class whose cross-identity with
    /// `Rat.one = mk 1 1` closes by `Quot.sound` (`mul_one`/`mul_comm` +
    /// `neg_mul_left`/`neg_mul_right`/`neg_neg`).
    fn register_rat_q_mul_inv_cancel(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.mul_inv_cancel");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }
        let ratq_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let ratq_one = Expr::const_(Name::from_string("Rat.one"), vec![]);
        let ratq_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let ratq_inv = Expr::const_(Name::from_string("Rat.inv"), vec![]);
        let false_c = Expr::const_(Name::from_string("False"), vec![]);

        // ne_ty(a') := Eq Rat a' zero → False.
        let ne_ty = |a: &Expr, parent: &EnvDeclBuilder| -> Expr {
            let mut bb = EnvDeclBuilder::child_of(parent);
            let eq0 = Expr::apps(
                c.eq_ratq.clone(),
                [c.ratq.clone(), a.clone(), ratq_zero.clone()],
            );
            let (h_id, _h) = bb.fresh_local(eq0.clone());
            bb.mk_pi(h_id, BinderInfo::Default, eq0, false_c.clone())
        };
        // goal(a') := Eq Rat (mul a' (inv a')) one.
        let goal_at = |a: &Expr| -> Expr {
            let inv_a = Expr::app(ratq_inv.clone(), a.clone());
            let lhs = Expr::apps(ratq_mul.clone(), [a.clone(), inv_a]);
            Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, ratq_one.clone()])
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let ne = ne_ty(&a, &b);
            let concl = goal_at(&a);
            let (h_id, _h) = b.fresh_local(ne.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, ne, concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());

            // Outer motive β(a') := ne_ty(a') → goal(a').
            let beta = {
                let mut bm = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = bm.fresh_local(c.ratq.clone());
                let ne = ne_ty(&x, &bm);
                let g = goal_at(&x);
                let (h_id, _h) = bm.fresh_local(ne.clone());
                let pi = bm.mk_pi(h_id, BinderInfo::Default, ne, g);
                let lam = bm.mk_lam(x_id, BinderInfo::Default, c.ratq.clone(), pi);
                bm.finish_child(lam)
            };

            let minor = {
                let mut bp = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bp.fresh_local(c.raw.clone());
                let body = c.mul_inv_minor(&bp, &p);
                let lam = bp.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), body);
                bp.finish_child(lam)
            };

            let ind = Expr::apps(
                c.quot_ind.clone(),
                [c.raw.clone(), c.raw_equiv.clone(), beta, minor, a.clone()],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), ind);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// WS-A live-switch structural-commutative-ring laws over the quotient.
    /// These six were previously proved over the FREE carrier (relying on its
    /// `Rat.add (mk)(mk) ≡ mk(...)` definitional equality + `Rat.num`/`Rat.denom`
    /// projections); the quotient carrier shifts that def-eq (ops reduce through
    /// `effDenom`, and there are no live `Rat.num`/`Rat.denom`), so they are
    /// regenerated here as genuine `Quot.ind` + `Quot.sound` proofs whose
    /// representative-level `Equiv` is a commutative-(semi)ring monomial identity
    /// closed by the generic `prod_eq` / `sum_eq` normalizers.
    pub(crate) fn register_rat_q_structural(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        self.register_rat_q_mul_comm(c)?;
        self.register_rat_q_mul_assoc(c)?;
        self.register_rat_q_one_mul(c)?;
        self.register_rat_q_mul_one(c)?;
        self.register_rat_q_add_comm(c)?;
        self.register_rat_q_zero_add(c)?;
        Ok(())
    }

    /// `Rat.mul_comm : ∀ a b : Rat, @Eq Rat (Rat.mul a b) (Rat.mul b a)`.
    /// Double `Quot.ind`; the Equiv `num_L·eff_R = num_R·eff_L` is the 4-atom
    /// commutative-product identity `(np·nq)·(eq·ep) = (nq·np)·(ep·eq)`,
    /// `prod_eq`-closed (same atom multiset {np,nq,ep,eq}).
    fn register_rat_q_mul_comm(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.mul_comm");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }
        let ratq_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);

        let inner_forall = |a: &Expr, parent: &EnvDeclBuilder| -> Expr {
            let mut bb = EnvDeclBuilder::child_of(parent);
            let (b_id, bvar) = bb.fresh_local(c.ratq.clone());
            let lhs = Expr::apps(ratq_mul.clone(), [a.clone(), bvar.clone()]);
            let rhs = Expr::apps(ratq_mul.clone(), [bvar.clone(), a.clone()]);
            let goal = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, rhs]);
            bb.mk_pi(b_id, BinderInfo::Default, c.ratq.clone(), goal)
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let body = inner_forall(&a, &b);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), body);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());

            let beta_a = {
                let mut bm = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = bm.fresh_local(c.ratq.clone());
                let body = inner_forall(&x, &bm);
                let lam = bm.mk_lam(x_id, BinderInfo::Default, c.ratq.clone(), body);
                bm.finish_child(lam)
            };

            let minor_a = {
                let mut bp = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bp.fresh_local(c.raw.clone());
                let mk_p = c.quot_mk(p.clone());

                let beta_b = {
                    let mut bmb = EnvDeclBuilder::child_of(&bp);
                    let (y_id, y) = bmb.fresh_local(c.ratq.clone());
                    let lhs = Expr::apps(ratq_mul.clone(), [mk_p.clone(), y.clone()]);
                    let rhs = Expr::apps(ratq_mul.clone(), [y.clone(), mk_p.clone()]);
                    let body = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, rhs]);
                    let lam = bmb.mk_lam(y_id, BinderInfo::Default, c.ratq.clone(), body);
                    bmb.finish_child(lam)
                };

                let minor_b = {
                    let mut bq = EnvDeclBuilder::child_of(&bp);
                    let (q_id, q) = bq.fresh_local(c.raw.clone());

                    let np = c.num(p.clone());
                    let nq = c.num(q.clone());
                    let ep = c.eff(p.clone());
                    let eq = c.eff(q.clone());
                    let at = ProdTree::atom;
                    // L = raw_mul p q ; R = raw_mul q p.
                    // Equiv: (np·nq)·(eq·ep) = (nq·np)·(ep·eq).
                    let tl = ProdTree::mul(
                        ProdTree::mul(at(np.clone()), at(nq.clone())),
                        ProdTree::mul(at(eq.clone()), at(ep.clone())),
                    );
                    let tr = ProdTree::mul(
                        ProdTree::mul(at(nq.clone()), at(np.clone())),
                        ProdTree::mul(at(ep.clone()), at(eq.clone())),
                    );
                    let eqv = c.prod_eq(&bq, &tl, &tr);
                    let sound = c.quot_sound(c.raw_mul(&p, &q), c.raw_mul(&q, &p), eqv);
                    let lam = bq.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), sound);
                    bq.finish_child(lam)
                };

                let ind_b = Expr::apps(
                    c.quot_ind.clone(),
                    [c.raw.clone(), c.raw_equiv.clone(), beta_b, minor_b],
                );
                let lam = bp.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), ind_b);
                bp.finish_child(lam)
            };

            let ind_a = Expr::apps(
                c.quot_ind.clone(),
                [
                    c.raw.clone(),
                    c.raw_equiv.clone(),
                    beta_a,
                    minor_a,
                    a.clone(),
                ],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), ind_a);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.mul_assoc : ∀ a b c : Rat,
    ///     @Eq Rat (Rat.mul (Rat.mul a b) c) (Rat.mul a (Rat.mul b c))`.
    /// Triple `Quot.ind`; Equiv is the 6-atom commutative-product identity
    /// `((np·nq)·nr)·(ep·(eq·er)) = (np·(nq·nr))·((ep·eq)·er)`, `prod_eq`-closed.
    fn register_rat_q_mul_assoc(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.mul_assoc");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }
        let ratq_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);

        let inner_forall = |a: &Expr, parent: &EnvDeclBuilder| -> Expr {
            let mut bb = EnvDeclBuilder::child_of(parent);
            let (b_id, bvar) = bb.fresh_local(c.ratq.clone());
            let (cc_id, cvar) = bb.fresh_local(c.ratq.clone());
            let mul_ab = Expr::apps(ratq_mul.clone(), [a.clone(), bvar.clone()]);
            let lhs = Expr::apps(ratq_mul.clone(), [mul_ab, cvar.clone()]);
            let mul_bc = Expr::apps(ratq_mul.clone(), [bvar.clone(), cvar.clone()]);
            let rhs = Expr::apps(ratq_mul.clone(), [a.clone(), mul_bc]);
            let goal = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, rhs]);
            let e = bb.mk_pi(cc_id, BinderInfo::Default, c.ratq.clone(), goal);
            bb.mk_pi(b_id, BinderInfo::Default, c.ratq.clone(), e)
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let body = inner_forall(&a, &b);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), body);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());

            let beta_a = {
                let mut bm = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = bm.fresh_local(c.ratq.clone());
                let body = inner_forall(&x, &bm);
                let lam = bm.mk_lam(x_id, BinderInfo::Default, c.ratq.clone(), body);
                bm.finish_child(lam)
            };

            let minor_a = {
                let mut bp = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bp.fresh_local(c.raw.clone());
                let mk_p = c.quot_mk(p.clone());

                let beta_b = {
                    let mut bmb = EnvDeclBuilder::child_of(&bp);
                    let (y_id, y) = bmb.fresh_local(c.ratq.clone());
                    let body = {
                        let mut bc = EnvDeclBuilder::child_of(&bmb);
                        let (cc_id, cvar) = bc.fresh_local(c.ratq.clone());
                        let mul_py = Expr::apps(ratq_mul.clone(), [mk_p.clone(), y.clone()]);
                        let lhs = Expr::apps(ratq_mul.clone(), [mul_py, cvar.clone()]);
                        let mul_yc = Expr::apps(ratq_mul.clone(), [y.clone(), cvar.clone()]);
                        let rhs = Expr::apps(ratq_mul.clone(), [mk_p.clone(), mul_yc]);
                        let goal = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, rhs]);
                        let e = bc.mk_pi(cc_id, BinderInfo::Default, c.ratq.clone(), goal);
                        bc.finish_child(e)
                    };
                    let lam = bmb.mk_lam(y_id, BinderInfo::Default, c.ratq.clone(), body);
                    bmb.finish_child(lam)
                };

                let minor_b = {
                    let mut bq = EnvDeclBuilder::child_of(&bp);
                    let (q_id, q) = bq.fresh_local(c.raw.clone());
                    let mk_q = c.quot_mk(q.clone());

                    let beta_c = {
                        let mut bmc = EnvDeclBuilder::child_of(&bq);
                        let (z_id, z) = bmc.fresh_local(c.ratq.clone());
                        let mul_pq = Expr::apps(ratq_mul.clone(), [mk_p.clone(), mk_q.clone()]);
                        let lhs = Expr::apps(ratq_mul.clone(), [mul_pq, z.clone()]);
                        let mul_qz = Expr::apps(ratq_mul.clone(), [mk_q.clone(), z.clone()]);
                        let rhs = Expr::apps(ratq_mul.clone(), [mk_p.clone(), mul_qz]);
                        let body = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, rhs]);
                        let e = bmc.mk_lam(z_id, BinderInfo::Default, c.ratq.clone(), body);
                        bmc.finish_child(e)
                    };

                    let minor_c = {
                        let mut br = EnvDeclBuilder::child_of(&bq);
                        let (r_id, r) = br.fresh_local(c.raw.clone());

                        let np = c.num(p.clone());
                        let nq = c.num(q.clone());
                        let nr = c.num(r.clone());
                        let ep = c.eff(p.clone());
                        let eq = c.eff(q.clone());
                        let er = c.eff(r.clone());
                        let at = ProdTree::atom;
                        // L = raw_mul (raw_mul p q) r ; R = raw_mul p (raw_mul q r).
                        // num_L = (np·nq)·nr ; eff_L = (ep·eq)·er.
                        // num_R = np·(nq·nr) ; eff_R = ep·(eq·er).
                        // Equiv: num_L·eff_R = num_R·eff_L.
                        let tl = ProdTree::mul(
                            ProdTree::mul(
                                ProdTree::mul(at(np.clone()), at(nq.clone())),
                                at(nr.clone()),
                            ),
                            ProdTree::mul(
                                at(ep.clone()),
                                ProdTree::mul(at(eq.clone()), at(er.clone())),
                            ),
                        );
                        let tr = ProdTree::mul(
                            ProdTree::mul(
                                at(np.clone()),
                                ProdTree::mul(at(nq.clone()), at(nr.clone())),
                            ),
                            ProdTree::mul(
                                ProdTree::mul(at(ep.clone()), at(eq.clone())),
                                at(er.clone()),
                            ),
                        );
                        let eqv = c.prod_eq(&br, &tl, &tr);
                        let l_raw = c.raw_mul(&c.raw_mul(&p, &q), &r);
                        let r_raw = c.raw_mul(&p, &c.raw_mul(&q, &r));
                        let sound = c.quot_sound(l_raw, r_raw, eqv);
                        let lam = br.mk_lam(r_id, BinderInfo::Default, c.raw.clone(), sound);
                        br.finish_child(lam)
                    };

                    let ind_c = Expr::apps(
                        c.quot_ind.clone(),
                        [c.raw.clone(), c.raw_equiv.clone(), beta_c, minor_c],
                    );
                    let lam = bq.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), ind_c);
                    bq.finish_child(lam)
                };

                let ind_b = Expr::apps(
                    c.quot_ind.clone(),
                    [c.raw.clone(), c.raw_equiv.clone(), beta_b, minor_b],
                );
                let lam = bp.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), ind_b);
                bp.finish_child(lam)
            };

            let ind_a = Expr::apps(
                c.quot_ind.clone(),
                [
                    c.raw.clone(),
                    c.raw_equiv.clone(),
                    beta_a,
                    minor_a,
                    a.clone(),
                ],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), ind_a);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.one_mul : ∀ a : Rat, @Eq Rat (Rat.mul Rat.one a) a`.
    /// Single `Quot.ind`; `Rat.one ≡ Quot.mk (Raw.mk (ofNat 1) 1)`, so for rep
    /// `p` the lhs class is `raw_mul one11 p`. Equiv to `p`:
    /// `(1·np)·ep = np·(e1·ep)` with `e1 ≡ ofNat 1`, `prod_eq`-closed (atoms
    /// {ofNat1, np, ep} both sides).
    fn register_rat_q_one_mul(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.one_mul");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }
        let ratq_one = Expr::const_(Name::from_string("Rat.one"), vec![]);
        let ratq_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let lhs = Expr::apps(ratq_mul.clone(), [ratq_one.clone(), a.clone()]);
            let goal = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, a.clone()]);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), goal);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());

            let beta = {
                let mut bm = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = bm.fresh_local(c.ratq.clone());
                let lhs = Expr::apps(ratq_mul.clone(), [ratq_one.clone(), x.clone()]);
                let body = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, x.clone()]);
                let lam = bm.mk_lam(x_id, BinderInfo::Default, c.ratq.clone(), body);
                bm.finish_child(lam)
            };

            let minor = {
                let mut bn = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bn.fresh_local(c.raw.clone());

                let nat_one = c.nsucc(c.nat_zero.clone());
                let one_int = c.of_nat(nat_one.clone());
                let one11 = c.raw_mk(one_int.clone(), nat_one.clone());
                // `num one11` and `eff one11` both DEFINITIONALLY reduce to
                // `ofNat 1` (= `one_int`); use that literal atom on both sides so
                // their ProdTree atom multisets match syntactically. `Quot.sound`
                // accepts the def-eq Equiv goal.
                let np = c.num(p.clone());
                let ep = c.eff(p.clone());
                let at = ProdTree::atom;
                // L = raw_mul one11 p ; num_L ≡ 1·np ; eff_L ≡ 1·ep.
                // Equiv L p: (1·np)·ep = np·(1·ep).
                let tl = ProdTree::mul(
                    ProdTree::mul(at(one_int.clone()), at(np.clone())),
                    at(ep.clone()),
                );
                let tr = ProdTree::mul(
                    at(np.clone()),
                    ProdTree::mul(at(one_int.clone()), at(ep.clone())),
                );
                let eqv = c.prod_eq(&bn, &tl, &tr);
                let sound = c.quot_sound(c.raw_mul(&one11, &p), p.clone(), eqv);
                let lam = bn.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), sound);
                bn.finish_child(lam)
            };

            let ind = Expr::apps(
                c.quot_ind.clone(),
                [c.raw.clone(), c.raw_equiv.clone(), beta, minor, a.clone()],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), ind);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.mul_one : ∀ a : Rat, @Eq Rat (Rat.mul a Rat.one) a`.
    /// Mirror of `one_mul`: Equiv `(np·n1)·ep = np·(ep·e1)`, `prod_eq`-closed.
    fn register_rat_q_mul_one(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.mul_one");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }
        let ratq_one = Expr::const_(Name::from_string("Rat.one"), vec![]);
        let ratq_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let lhs = Expr::apps(ratq_mul.clone(), [a.clone(), ratq_one.clone()]);
            let goal = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, a.clone()]);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), goal);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());

            let beta = {
                let mut bm = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = bm.fresh_local(c.ratq.clone());
                let lhs = Expr::apps(ratq_mul.clone(), [x.clone(), ratq_one.clone()]);
                let body = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, x.clone()]);
                let lam = bm.mk_lam(x_id, BinderInfo::Default, c.ratq.clone(), body);
                bm.finish_child(lam)
            };

            let minor = {
                let mut bn = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bn.fresh_local(c.raw.clone());

                let nat_one = c.nsucc(c.nat_zero.clone());
                let one_int = c.of_nat(nat_one.clone());
                let one11 = c.raw_mk(one_int.clone(), nat_one.clone());
                // `num one11` / `eff one11` both ≡ `ofNat 1` (= `one_int`); use
                // that literal on both ProdTree sides (def-eq Equiv goal).
                let np = c.num(p.clone());
                let ep = c.eff(p.clone());
                let at = ProdTree::atom;
                // L = raw_mul p one11 ; num_L ≡ np·1 ; eff_L ≡ ep·1.
                // Equiv L p: (np·1)·ep = np·(ep·1).
                let tl = ProdTree::mul(
                    ProdTree::mul(at(np.clone()), at(one_int.clone())),
                    at(ep.clone()),
                );
                let tr = ProdTree::mul(
                    at(np.clone()),
                    ProdTree::mul(at(ep.clone()), at(one_int.clone())),
                );
                let eqv = c.prod_eq(&bn, &tl, &tr);
                let sound = c.quot_sound(c.raw_mul(&p, &one11), p.clone(), eqv);
                let lam = bn.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), sound);
                bn.finish_child(lam)
            };

            let ind = Expr::apps(
                c.quot_ind.clone(),
                [c.raw.clone(), c.raw_equiv.clone(), beta, minor, a.clone()],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), ind);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.add_comm : ∀ a b : Rat, @Eq Rat (Rat.add a b) (Rat.add b a)`.
    /// Double `Quot.ind`; the Equiv is the SUM identity
    /// `(np·eq + nq·ep)·(eq·ep) = (nq·ep + np·eq)·(ep·eq)`: each side
    /// `right_distrib`-flattens to two monomials, scaled by the opposite effDenom
    /// (`mul_sum_right`), matched by `sum_eq`.
    fn register_rat_q_add_comm(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.add_comm");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }
        let ratq_add = Expr::const_(Name::from_string("Rat.add"), vec![]);

        let inner_forall = |a: &Expr, parent: &EnvDeclBuilder| -> Expr {
            let mut bb = EnvDeclBuilder::child_of(parent);
            let (b_id, bvar) = bb.fresh_local(c.ratq.clone());
            let lhs = Expr::apps(ratq_add.clone(), [a.clone(), bvar.clone()]);
            let rhs = Expr::apps(ratq_add.clone(), [bvar.clone(), a.clone()]);
            let goal = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, rhs]);
            bb.mk_pi(b_id, BinderInfo::Default, c.ratq.clone(), goal)
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let body = inner_forall(&a, &b);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), body);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());

            let beta_a = {
                let mut bm = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = bm.fresh_local(c.ratq.clone());
                let body = inner_forall(&x, &bm);
                let lam = bm.mk_lam(x_id, BinderInfo::Default, c.ratq.clone(), body);
                bm.finish_child(lam)
            };

            let minor_a = {
                let mut bp = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bp.fresh_local(c.raw.clone());
                let mk_p = c.quot_mk(p.clone());

                let beta_b = {
                    let mut bmb = EnvDeclBuilder::child_of(&bp);
                    let (y_id, y) = bmb.fresh_local(c.ratq.clone());
                    let lhs = Expr::apps(ratq_add.clone(), [mk_p.clone(), y.clone()]);
                    let rhs = Expr::apps(ratq_add.clone(), [y.clone(), mk_p.clone()]);
                    let body = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, rhs]);
                    let lam = bmb.mk_lam(y_id, BinderInfo::Default, c.ratq.clone(), body);
                    bmb.finish_child(lam)
                };

                let minor_b = {
                    let mut bq = EnvDeclBuilder::child_of(&bp);
                    let (q_id, q) = bq.fresh_local(c.raw.clone());

                    let np = c.num(p.clone());
                    let nq = c.num(q.clone());
                    let ep = c.eff(p.clone());
                    let eq = c.eff(q.clone());
                    let at = ProdTree::atom;
                    // L = raw_add p q ; num_L = np·eq + nq·ep ; eff_L = ep·eq.
                    // R = raw_add q p ; num_R = nq·ep + np·eq ; eff_R = eq·ep.
                    // Equiv L R: num_L·eff_R = num_R·eff_L.
                    let np_eq = c.mul(np.clone(), eq.clone());
                    let nq_ep = c.mul(nq.clone(), ep.clone());
                    let num_l = c.add(np_eq.clone(), nq_ep.clone());
                    let num_r = c.add(nq_ep.clone(), np_eq.clone());
                    let eff_l = c.mul(ep.clone(), eq.clone());
                    let eff_r = c.mul(eq.clone(), ep.clone());
                    let lhs0 = c.mul(num_l.clone(), eff_r.clone());
                    let rhs0 = c.mul(num_r.clone(), eff_l.clone());

                    // LHS: scale {np·eq, nq·ep} by eff_R = (eq·ep).
                    let sl_tree = SumTree::add(
                        SumTree::mono(ProdTree::mul(at(np.clone()), at(eq.clone()))),
                        SumTree::mono(ProdTree::mul(at(nq.clone()), at(ep.clone()))),
                    );
                    let eff_r_tree = ProdTree::mul(at(eq.clone()), at(ep.clone()));
                    let (sle_tree, p_scale_l) = c.mul_sum_right(&bq, &sl_tree, &eff_r_tree);
                    // RHS: scale {nq·ep, np·eq} by eff_L = (ep·eq).
                    let sr_tree = SumTree::add(
                        SumTree::mono(ProdTree::mul(at(nq.clone()), at(ep.clone()))),
                        SumTree::mono(ProdTree::mul(at(np.clone()), at(eq.clone()))),
                    );
                    let eff_l_tree = ProdTree::mul(at(ep.clone()), at(eq.clone()));
                    let (sre_tree, p_scale_r) = c.mul_sum_right(&bq, &sr_tree, &eff_l_tree);

                    // Match the two scaled sums; chain.
                    let mid = c.sum_eq(&bq, &sle_tree, &sre_tree);
                    let p_right_sym = c.symm_int(rhs0.clone(), sre_tree.to_expr(c), p_scale_r);
                    let t = c.trans_int(
                        lhs0.clone(),
                        sle_tree.to_expr(c),
                        sre_tree.to_expr(c),
                        p_scale_l,
                        mid,
                    );
                    let eqv = c.trans_int(
                        lhs0.clone(),
                        sre_tree.to_expr(c),
                        rhs0.clone(),
                        t,
                        p_right_sym,
                    );

                    let sound = c.quot_sound(c.raw_add(&p, &q), c.raw_add(&q, &p), eqv);
                    let lam = bq.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), sound);
                    bq.finish_child(lam)
                };

                let ind_b = Expr::apps(
                    c.quot_ind.clone(),
                    [c.raw.clone(), c.raw_equiv.clone(), beta_b, minor_b],
                );
                let lam = bp.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), ind_b);
                bp.finish_child(lam)
            };

            let ind_a = Expr::apps(
                c.quot_ind.clone(),
                [
                    c.raw.clone(),
                    c.raw_equiv.clone(),
                    beta_a,
                    minor_a,
                    a.clone(),
                ],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), ind_a);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.zero_add : ∀ a : Rat, @Eq Rat (Rat.add Rat.zero a) a`.
    /// Single `Quot.ind`, mirror of `Rat.add_zero` (the zero is the FIRST
    /// addend). For rep `p`: `num_L = 0·ep + np·e0` (e0 ≡ ofNat 1), reduced to
    /// `np` by `zero_mul` / `mul_one` / `add` congruences; `eff_L ≡ e0·ep`.
    fn register_rat_q_zero_add(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.zero_add");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }
        let ratq_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let ratq_add = Expr::const_(Name::from_string("Rat.add"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let lhs = Expr::apps(ratq_add.clone(), [ratq_zero.clone(), a.clone()]);
            let goal = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, a.clone()]);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), goal);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());

            let beta = {
                let mut bm = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = bm.fresh_local(c.ratq.clone());
                let lhs = Expr::apps(ratq_add.clone(), [ratq_zero.clone(), x.clone()]);
                let body = Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, x.clone()]);
                let lam = bm.mk_lam(x_id, BinderInfo::Default, c.ratq.clone(), body);
                bm.finish_child(lam)
            };

            let minor = {
                let mut bn = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bn.fresh_local(c.raw.clone());

                let np = c.num(p.clone());
                let ep = c.eff(p.clone());
                let nat_one = c.nsucc(c.nat_zero.clone());
                let zero01 = c.raw_mk(c.int_zero.clone(), nat_one.clone());
                let e0 = c.eff(zero01.clone()); // ≡ ofNat 1

                // raw_lhs := raw_add zero01 p ; num_L = 0·Ep + np·E0.
                let raw_lhs = c.raw_add(&zero01, &p);
                let zero_ep = c.mul(c.int_zero.clone(), ep.clone());
                let np_e0 = c.mul(np.clone(), e0.clone());
                let num_l = c.add(zero_ep.clone(), np_e0.clone());

                // Equiv raw_lhs p ≡ Eq Int (num_L · eff p) (np · eff raw_lhs).
                let eff_p = c.eff(p.clone());
                let eff_lhs = c.eff(raw_lhs.clone());
                let lhs_t = c.mul(num_l.clone(), eff_p.clone());
                let rhs_t = c.mul(np.clone(), eff_lhs.clone());

                // num_L → np :  0·Ep + np·E0 = 0 + np = np.
                //   a1 : 0·Ep = 0    [zero_mul Ep]
                let a1 = c.zero_mul(ep.clone());
                //   a2 : np·E0 = np  [mul_one np]  (E0 ≡ ofNat 1)
                let a2 = c.mul_one(np.clone());
                //   numl = 0 + np    [add_cong a1 a2]
                let zero_plus_np = c.add(c.int_zero.clone(), np.clone());
                let numl_to_0np =
                    c.add_cong(&bn, &zero_ep, &c.int_zero.clone(), &np_e0, &np, &a1, &a2);
                //   0 + np = np      [zero_add np]  via congr? use Int.add_comm+add_zero?
                // Int has `Int.zero` add-left identity? We have add_zero (right). For
                // left, chain: 0 + np = np + 0 [add_comm] = np [add_zero].
                let np_plus_zero = c.add(np.clone(), c.int_zero.clone());
                let a3a = c.add_comm(c.int_zero.clone(), np.clone());
                let a3b = c.add_zero(np.clone());
                let a3 = c.trans_int(
                    zero_plus_np.clone(),
                    np_plus_zero.clone(),
                    np.clone(),
                    a3a,
                    a3b,
                );
                let numl_to_np = c.trans_int(
                    num_l.clone(),
                    zero_plus_np.clone(),
                    np.clone(),
                    numl_to_0np,
                    a3,
                );

                // lhs_t = num_L·Ep → np·Ep   [congrArg (·*Ep) numl_to_np]
                let np_ep = c.mul(np.clone(), eff_p.clone());
                let lhs_to = c.congr_arg(
                    num_l.clone(),
                    np.clone(),
                    c.mul_right_fn(&bn, eff_p.clone()),
                    numl_to_np,
                );
                // rhs_t = np·eff_lhs ; eff_lhs ≡ E0·Ep (defeq). np·(E0·Ep) = np·Ep
                //   via congrArg (np·)(symm? ) — actually we need np·(E0·Ep) -> np·Ep
                //   using E0·Ep = Ep? No: E0 ≡ ofNat 1, so E0·Ep = Ep via `one_mul`
                //   on Int: Int.one_mul? We use `mul` with E0 on the LEFT; bridge via
                //   commute then mul_one: E0·Ep = Ep·E0 [mul_comm] = Ep [mul_one].
                let e0_ep = c.mul(e0.clone(), ep.clone());
                let ep_e0 = c.mul(ep.clone(), e0.clone());
                let m_comm = c.mul_comm(e0.clone(), ep.clone());
                let m_one = c.mul_one(ep.clone());
                let e0ep_to_ep =
                    c.trans_int(e0_ep.clone(), ep_e0.clone(), ep.clone(), m_comm, m_one);
                // np·(E0·Ep) = np·Ep  [congrArg (np·) e0ep_to_ep]
                let np_e0ep = c.mul(np.clone(), e0_ep.clone());
                let rhs_cong = c.congr_arg(
                    e0_ep.clone(),
                    ep.clone(),
                    c.mul_left_fn(&bn, np.clone()),
                    e0ep_to_ep,
                );
                // rhs_cong : np·(E0·Ep) = np·Ep ; np·(E0·Ep) ≡ rhs_t (defeq).
                let rhs_back = c.symm_int(np_e0ep.clone(), np_ep.clone(), rhs_cong);
                let eqv = c.trans_int(
                    lhs_t.clone(),
                    np_ep.clone(),
                    rhs_t.clone(),
                    lhs_to,
                    rhs_back,
                );

                let sound = c.quot_sound(raw_lhs.clone(), p.clone(), eqv);
                let lam = bn.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), sound);
                bn.finish_child(lam)
            };

            let ind = Expr::apps(
                c.quot_ind.clone(),
                [c.raw.clone(), c.raw_equiv.clone(), beta, minor, a.clone()],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), ind);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.mul_neg : ∀ a b : Rat, Rat.mul a (Rat.neg b) = Rat.neg (Rat.mul a b)`.
    /// Double `Quot.ind`; over the quotient `Rat.neg`/`Rat.mul` the goal reduces
    /// to a `Quot.sound` of the raw cross-Equiv
    /// `(np·(neg nq))·(ep·eq) = (neg(np·nq))·(ep·eq)`, closed by
    /// `Int.neg_mul_right` under `congrArg (·*(ep·eq))`.
    #[cfg(any(test, feature = "math-overlays", feature = "farkas-constructive"))]
    pub(crate) fn register_rat_q_mul_neg(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.mul_neg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_int_neg_mul_right_proof()?;
        let ratq_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let ratq_neg = Expr::const_(Name::from_string("Rat.neg"), vec![]);

        // `raw_neg p := raw_mk (neg (num p)) (effDenom p)`.
        let raw_neg = |p: &Expr| -> Expr {
            c.raw_mk(
                c.neg(c.num(p.clone())),
                Expr::app(c.raw_eff_denom.clone(), p.clone()),
            )
        };

        let goal_at = |a: &Expr, bv: &Expr| -> Expr {
            let neg_b = Expr::app(ratq_neg.clone(), bv.clone());
            let lhs = Expr::apps(ratq_mul.clone(), [a.clone(), neg_b]);
            let mul_ab = Expr::apps(ratq_mul.clone(), [a.clone(), bv.clone()]);
            let rhs = Expr::app(ratq_neg.clone(), mul_ab);
            Expr::apps(c.eq_ratq.clone(), [c.ratq.clone(), lhs, rhs])
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let (bv_id, bv) = b.fresh_local(c.ratq.clone());
            let body = goal_at(&a, &bv);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.ratq.clone(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());

            let beta_a = {
                let mut bm = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = bm.fresh_local(c.ratq.clone());
                let body = {
                    let mut bb = EnvDeclBuilder::child_of(&bm);
                    let (y_id, y) = bb.fresh_local(c.ratq.clone());
                    let g = goal_at(&x, &y);
                    let e = bb.mk_pi(y_id, BinderInfo::Default, c.ratq.clone(), g);
                    bb.finish_child(e)
                };
                let lam = bm.mk_lam(x_id, BinderInfo::Default, c.ratq.clone(), body);
                bm.finish_child(lam)
            };

            let minor_a = {
                let mut bp = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bp.fresh_local(c.raw.clone());
                let mk_p = c.quot_mk(p.clone());
                let beta_b = {
                    let mut bmb = EnvDeclBuilder::child_of(&bp);
                    let (y_id, y) = bmb.fresh_local(c.ratq.clone());
                    let body = goal_at(&mk_p, &y);
                    let lam = bmb.mk_lam(y_id, BinderInfo::Default, c.ratq.clone(), body);
                    bmb.finish_child(lam)
                };
                let minor_b = {
                    let mut bq = EnvDeclBuilder::child_of(&bp);
                    let (q_id, q) = bq.fresh_local(c.raw.clone());

                    let np = c.num(p.clone());
                    let nq = c.num(q.clone());
                    let ep = c.eff(p.clone());
                    let eq = c.eff(q.clone());
                    // L = raw_mul p (raw_neg q) ; num_L = np·(neg nq) ; eff_L ≡ ep·eq.
                    // R = raw_neg (raw_mul p q) ; num_R = neg(np·nq) ; eff_R ≡ ep·eq.
                    // Equiv L R ≡ Eq Int (num_L·eff_R)(num_R·eff_L).
                    let neg_nq = c.neg(nq.clone());
                    let np_negnq = c.mul(np.clone(), neg_nq.clone());
                    let np_nq = c.mul(np.clone(), nq.clone());
                    let neg_npnq = c.neg(np_nq.clone());
                    let ep_eq = c.mul(ep.clone(), eq.clone());
                    let _lhs = c.mul(np_negnq.clone(), ep_eq.clone());
                    let _rhs = c.mul(neg_npnq.clone(), ep_eq.clone());
                    // h_num : np·(neg nq) = neg(np·nq)  [symm (neg_mul_right np nq)].
                    let h_num = c.symm_int(
                        neg_npnq.clone(),
                        np_negnq.clone(),
                        c.neg_mul_right(np.clone(), nq.clone()),
                    );
                    // eqv : lhs = rhs  [congrArg (·*(ep·eq)) h_num].
                    let eqv = c.congr_arg(
                        np_negnq.clone(),
                        neg_npnq.clone(),
                        c.mul_right_fn(&bq, ep_eq.clone()),
                        h_num,
                    );
                    let l_raw = c.raw_mul(&p, &raw_neg(&q));
                    let r_raw = raw_neg(&c.raw_mul(&p, &q));
                    let sound = c.quot_sound(l_raw, r_raw, eqv);
                    let lam = bq.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), sound);
                    bq.finish_child(lam)
                };
                let ind_b = Expr::apps(
                    c.quot_ind.clone(),
                    [c.raw.clone(), c.raw_equiv.clone(), beta_b, minor_b],
                );
                let lam = bp.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), ind_b);
                bp.finish_child(lam)
            };

            let ind_a = Expr::apps(
                c.quot_ind.clone(),
                [
                    c.raw.clone(),
                    c.raw_equiv.clone(),
                    beta_a,
                    minor_a,
                    a.clone(),
                ],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), ind_a);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// WS-A live-switch ORDER lemmas over the quotient. These were proved over
    /// the FREE carrier in `algebra_rat_order_proofs.rs` / `..._le_trans_proof.rs`
    /// relying on `Rat.le a a ≡ Int.le (cross a a)(cross a a)` definitional
    /// equality and the `Rat.num`/`Rat.effDenom` projections. The quotient
    /// `Rat.le`/`Rat.lt` are `Quot.lift`s, so `Rat.le a b` only reduces when
    /// `a`/`b` are representatives; these are regenerated with `Quot.ind` +
    /// the construction's raw cross-multiplication toolkit.
    pub(crate) fn register_rat_q_order_lemmas(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        self.register_int_le_total_proof()?;
        self.register_int_mul_pos_proof()?;
        self.register_rat_q_le_refl(c)?;
        self.register_rat_q_le_total(c)?;
        self.register_rat_q_lt_iff_le_not_le(c)?;
        self.register_rat_q_le_trans(c)?;
        self.register_rat_q_le_of_lt(c)?;
        self.register_rat_q_mul_pos(c)?;
        self.register_rat_q_mul_nonneg(c)?;
        Ok(())
    }

    /// `Rat.le_refl : ∀ a : Rat, Rat.le a a`. `Quot.ind` on `a`; for rep `p`,
    /// `Rat.le (mk p)(mk p) ≡ Raw.le p p = Int.le (np·ep)(np·ep)`, closed by
    /// `Int.le_refl (np·ep)`.
    fn register_rat_q_le_refl(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.le_refl");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }
        let ratq_le = Expr::const_(Name::from_string("Rat.le"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let body = Expr::apps(ratq_le.clone(), [a.clone(), a.clone()]);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), body);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let beta = {
                let mut bm = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = bm.fresh_local(c.ratq.clone());
                let body = Expr::apps(ratq_le.clone(), [x.clone(), x.clone()]);
                let lam = bm.mk_lam(x_id, BinderInfo::Default, c.ratq.clone(), body);
                bm.finish_child(lam)
            };
            let minor = {
                let mut bn = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bn.fresh_local(c.raw.clone());
                // Int.le_refl (np·ep) : Int.le (np·ep)(np·ep) ≡ Raw.le p p.
                let np_ep = c.mul(c.num(p.clone()), c.eff(p.clone()));
                let body = Expr::app(c.int_le_refl.clone(), np_ep);
                let lam = bn.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), body);
                bn.finish_child(lam)
            };
            let ind = Expr::apps(
                c.quot_ind.clone(),
                [c.raw.clone(), c.raw_equiv.clone(), beta, minor, a.clone()],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), ind);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.le_total : ∀ a b : Rat, Or (Rat.le a b) (Rat.le b a)`. Double
    /// `Quot.ind`; for reps p,q the goal ≡ `Or (Raw.le p q)(Raw.le q p)`, closed
    /// by `Int.le_total (np·eq)(nq·ep)`.
    fn register_rat_q_le_total(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.le_total");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }
        let ratq_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
        let or_c = Expr::const_(Name::from_string("Or"), vec![]);

        let goal_at = |a: &Expr, bv: &Expr| -> Expr {
            Expr::apps(
                or_c.clone(),
                [
                    Expr::apps(ratq_le.clone(), [a.clone(), bv.clone()]),
                    Expr::apps(ratq_le.clone(), [bv.clone(), a.clone()]),
                ],
            )
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let (bv_id, bv) = b.fresh_local(c.ratq.clone());
            let body = goal_at(&a, &bv);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.ratq.clone(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let beta_a = {
                let mut bm = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = bm.fresh_local(c.ratq.clone());
                let body = {
                    let mut bb = EnvDeclBuilder::child_of(&bm);
                    let (y_id, y) = bb.fresh_local(c.ratq.clone());
                    let g = goal_at(&x, &y);
                    let e = bb.mk_pi(y_id, BinderInfo::Default, c.ratq.clone(), g);
                    bb.finish_child(e)
                };
                let lam = bm.mk_lam(x_id, BinderInfo::Default, c.ratq.clone(), body);
                bm.finish_child(lam)
            };
            let minor_a = {
                let mut bp = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bp.fresh_local(c.raw.clone());
                let mk_p = c.quot_mk(p.clone());
                let beta_b = {
                    let mut bmb = EnvDeclBuilder::child_of(&bp);
                    let (y_id, y) = bmb.fresh_local(c.ratq.clone());
                    let body = goal_at(&mk_p, &y);
                    let lam = bmb.mk_lam(y_id, BinderInfo::Default, c.ratq.clone(), body);
                    bmb.finish_child(lam)
                };
                let minor_b = {
                    let mut bq = EnvDeclBuilder::child_of(&bp);
                    let (q_id, q) = bq.fresh_local(c.raw.clone());
                    // Int.le_total (np·eq)(nq·ep) : Or (Raw.le p q)(Raw.le q p).
                    let np_eq = c.mul(c.num(p.clone()), c.eff(q.clone()));
                    let nq_ep = c.mul(c.num(q.clone()), c.eff(p.clone()));
                    let body = Expr::apps(c.int_le_total.clone(), [np_eq, nq_ep]);
                    let lam = bq.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), body);
                    bq.finish_child(lam)
                };
                let ind_b = Expr::apps(
                    c.quot_ind.clone(),
                    [c.raw.clone(), c.raw_equiv.clone(), beta_b, minor_b],
                );
                let lam = bp.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), ind_b);
                bp.finish_child(lam)
            };
            let ind_a = Expr::apps(
                c.quot_ind.clone(),
                [
                    c.raw.clone(),
                    c.raw_equiv.clone(),
                    beta_a,
                    minor_a,
                    a.clone(),
                ],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), ind_a);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.le_of_lt : ∀ a b : Rat, Rat.lt a b → Rat.le a b`. Double `Quot.ind`
    /// on `a`, `b`. For reps `p`, `q`, both `Rat.lt (mk p)(mk q)` and
    /// `Rat.le (mk p)(mk q)` reduce to the SAME cross-products
    /// (`Raw.lt p q = Int.lt (np·eq)(nq·ep)`, `Raw.le p q = Int.le (np·eq)(nq·ep)`),
    /// so the minor case is `Int.le_of_lt (np·eq)(nq·ep) h`. `Int.le_of_lt` is a
    /// constructive `Declaration::Theorem` with empty closure (its census is
    /// `Int.subNatNat`/`Int.rec` only), so `Rat.le_of_lt` is constructive with
    /// empty admitted-axiom closure.
    fn register_rat_q_le_of_lt(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.le_of_lt");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }
        self.register_int_le_of_lt_proof()?;
        let int_le_of_lt = Expr::const_(Name::from_string("Int.le_of_lt"), vec![]);
        let ratq_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
        let ratq_lt = Expr::const_(Name::from_string("Rat.lt"), vec![]);

        // Goal at `(a, b)`: `Rat.lt a b → Rat.le a b`.
        let goal_at = |a: &Expr, bv: &Expr, parent: &EnvDeclBuilder| -> Expr {
            let mut bb = EnvDeclBuilder::child_of(parent);
            let lt_ab = Expr::apps(ratq_lt.clone(), [a.clone(), bv.clone()]);
            let le_ab = Expr::apps(ratq_le.clone(), [a.clone(), bv.clone()]);
            let (h_id, _h) = bb.fresh_local(lt_ab.clone());
            let e = bb.mk_pi(h_id, BinderInfo::Default, lt_ab, le_ab);
            bb.finish_child(e)
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let (bv_id, bv) = b.fresh_local(c.ratq.clone());
            let body = goal_at(&a, &bv, &b);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.ratq.clone(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let beta_a = {
                let mut bm = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = bm.fresh_local(c.ratq.clone());
                let body = {
                    let mut bb = EnvDeclBuilder::child_of(&bm);
                    let (y_id, y) = bb.fresh_local(c.ratq.clone());
                    let g = goal_at(&x, &y, &bb);
                    let e = bb.mk_pi(y_id, BinderInfo::Default, c.ratq.clone(), g);
                    bb.finish_child(e)
                };
                let lam = bm.mk_lam(x_id, BinderInfo::Default, c.ratq.clone(), body);
                bm.finish_child(lam)
            };
            let minor_a = {
                let mut bp = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bp.fresh_local(c.raw.clone());
                let mk_p = c.quot_mk(p.clone());
                let beta_b = {
                    let mut bmb = EnvDeclBuilder::child_of(&bp);
                    let (y_id, y) = bmb.fresh_local(c.ratq.clone());
                    let body = goal_at(&mk_p, &y, &bmb);
                    let lam = bmb.mk_lam(y_id, BinderInfo::Default, c.ratq.clone(), body);
                    bmb.finish_child(lam)
                };
                let minor_b = {
                    let mut bq = EnvDeclBuilder::child_of(&bp);
                    let (q_id, q) = bq.fresh_local(c.raw.clone());
                    // λ (h : Raw.lt p q) => Int.le_of_lt (np·eq)(nq·ep) h : Raw.le p q.
                    let np_eq = c.mul(c.num(p.clone()), c.eff(q.clone()));
                    let nq_ep = c.mul(c.num(q.clone()), c.eff(p.clone()));
                    let raw_lt = c.raw_lt(&p, &q);
                    let (h_id, h) = bq.fresh_local(raw_lt.clone());
                    let body = Expr::apps(int_le_of_lt.clone(), [np_eq, nq_ep, h]);
                    let lam = bq.mk_lam(h_id, BinderInfo::Default, raw_lt, body);
                    let lam = bq.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), lam);
                    bq.finish_child(lam)
                };
                let ind_b = Expr::apps(
                    c.quot_ind.clone(),
                    [c.raw.clone(), c.raw_equiv.clone(), beta_b, minor_b],
                );
                let lam = bp.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), ind_b);
                bp.finish_child(lam)
            };
            let ind_a = Expr::apps(
                c.quot_ind.clone(),
                [
                    c.raw.clone(),
                    c.raw_equiv.clone(),
                    beta_a,
                    minor_a,
                    a.clone(),
                ],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), ind_a);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.lt_iff_le_not_le : ∀ a b : Rat,
    ///    Iff (Rat.lt a b)(And (Rat.le a b)(Not (Rat.le b a)))`. Double
    /// `Quot.ind`; reduces to the Int analogue
    /// `Int.lt_iff_le_not_le (np·eq)(nq·ep)`. HONEST: closure includes the
    /// still-admitted Int axiom `Int.lt_iff_le_not_le` (so `AxiomDependent`).
    fn register_rat_q_lt_iff_le_not_le(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.lt_iff_le_not_le");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }
        let ratq_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
        let ratq_lt = Expr::const_(Name::from_string("Rat.lt"), vec![]);
        let iff_c = Expr::const_(Name::from_string("Iff"), vec![]);
        let and_c = Expr::const_(Name::from_string("And"), vec![]);
        let not_c = Expr::const_(Name::from_string("Not"), vec![]);

        let goal_at = |a: &Expr, bv: &Expr| -> Expr {
            let lt_ab = Expr::apps(ratq_lt.clone(), [a.clone(), bv.clone()]);
            let le_ab = Expr::apps(ratq_le.clone(), [a.clone(), bv.clone()]);
            let le_ba = Expr::apps(ratq_le.clone(), [bv.clone(), a.clone()]);
            let not_le_ba = Expr::app(not_c.clone(), le_ba);
            let and_e = Expr::apps(and_c.clone(), [le_ab, not_le_ba]);
            Expr::apps(iff_c.clone(), [lt_ab, and_e])
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let (bv_id, bv) = b.fresh_local(c.ratq.clone());
            let body = goal_at(&a, &bv);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.ratq.clone(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let beta_a = {
                let mut bm = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = bm.fresh_local(c.ratq.clone());
                let body = {
                    let mut bb = EnvDeclBuilder::child_of(&bm);
                    let (y_id, y) = bb.fresh_local(c.ratq.clone());
                    let g = goal_at(&x, &y);
                    let e = bb.mk_pi(y_id, BinderInfo::Default, c.ratq.clone(), g);
                    bb.finish_child(e)
                };
                let lam = bm.mk_lam(x_id, BinderInfo::Default, c.ratq.clone(), body);
                bm.finish_child(lam)
            };
            let minor_a = {
                let mut bp = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bp.fresh_local(c.raw.clone());
                let mk_p = c.quot_mk(p.clone());
                let beta_b = {
                    let mut bmb = EnvDeclBuilder::child_of(&bp);
                    let (y_id, y) = bmb.fresh_local(c.ratq.clone());
                    let body = goal_at(&mk_p, &y);
                    let lam = bmb.mk_lam(y_id, BinderInfo::Default, c.ratq.clone(), body);
                    bmb.finish_child(lam)
                };
                let minor_b = {
                    let mut bq = EnvDeclBuilder::child_of(&bp);
                    let (q_id, q) = bq.fresh_local(c.raw.clone());
                    let np_eq = c.mul(c.num(p.clone()), c.eff(q.clone()));
                    let nq_ep = c.mul(c.num(q.clone()), c.eff(p.clone()));
                    let body = Expr::apps(c.int_lt_iff_le_not_le.clone(), [np_eq, nq_ep]);
                    let lam = bq.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), body);
                    bq.finish_child(lam)
                };
                let ind_b = Expr::apps(
                    c.quot_ind.clone(),
                    [c.raw.clone(), c.raw_equiv.clone(), beta_b, minor_b],
                );
                let lam = bp.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), ind_b);
                bp.finish_child(lam)
            };
            let ind_a = Expr::apps(
                c.quot_ind.clone(),
                [
                    c.raw.clone(),
                    c.raw_equiv.clone(),
                    beta_a,
                    minor_a,
                    a.clone(),
                ],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), ind_a);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.le_trans : ∀ a b c : Rat, Rat.le a b → Rat.le b c → Rat.le a c`.
    /// Triple `Quot.ind`; for reps p,q,r the hyps def-reduce to `Raw.le p q` /
    /// `Raw.le q r` and the goal to `Raw.le p r`, closed by the constructive
    /// `Int.le_cross_trans`.
    fn register_rat_q_le_trans(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.le_trans");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }
        let ratq_le = Expr::const_(Name::from_string("Rat.le"), vec![]);

        // `∀ b c, le a b → le b c → le a c` for a given first element `a`.
        let inner_forall = |a: &Expr, parent: &EnvDeclBuilder| -> Expr {
            let mut bb = EnvDeclBuilder::child_of(parent);
            let (b_id, bvar) = bb.fresh_local(c.ratq.clone());
            let (cc_id, cvar) = bb.fresh_local(c.ratq.clone());
            let le_ab = Expr::apps(ratq_le.clone(), [a.clone(), bvar.clone()]);
            let le_bc = Expr::apps(ratq_le.clone(), [bvar.clone(), cvar.clone()]);
            let le_ac = Expr::apps(ratq_le.clone(), [a.clone(), cvar.clone()]);
            let (h1_id, _h1) = bb.fresh_local(le_ab.clone());
            let (h2_id, _h2) = bb.fresh_local(le_bc.clone());
            let e = bb.mk_pi(h2_id, BinderInfo::Default, le_bc, le_ac);
            let e = bb.mk_pi(h1_id, BinderInfo::Default, le_ab, e);
            let e = bb.mk_pi(cc_id, BinderInfo::Default, c.ratq.clone(), e);
            bb.mk_pi(b_id, BinderInfo::Default, c.ratq.clone(), e)
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let body = inner_forall(&a, &b);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), body);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());

            let beta_a = {
                let mut bm = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = bm.fresh_local(c.ratq.clone());
                let body = inner_forall(&x, &bm);
                let lam = bm.mk_lam(x_id, BinderInfo::Default, c.ratq.clone(), body);
                bm.finish_child(lam)
            };

            let minor_a = {
                let mut bp = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bp.fresh_local(c.raw.clone());
                let mk_p = c.quot_mk(p.clone());

                // `∀ c, le (mk p) y → le y c → le (mk p) c` for a fixed second `y`.
                let inner_p = |y: &Expr, parent: &EnvDeclBuilder| -> Expr {
                    let mut bb = EnvDeclBuilder::child_of(parent);
                    let (cc_id, cvar) = bb.fresh_local(c.ratq.clone());
                    let le_ab = Expr::apps(ratq_le.clone(), [mk_p.clone(), y.clone()]);
                    let le_bc = Expr::apps(ratq_le.clone(), [y.clone(), cvar.clone()]);
                    let le_ac = Expr::apps(ratq_le.clone(), [mk_p.clone(), cvar.clone()]);
                    let (h1_id, _h1) = bb.fresh_local(le_ab.clone());
                    let (h2_id, _h2) = bb.fresh_local(le_bc.clone());
                    let e = bb.mk_pi(h2_id, BinderInfo::Default, le_bc, le_ac);
                    let e = bb.mk_pi(h1_id, BinderInfo::Default, le_ab, e);
                    bb.mk_pi(cc_id, BinderInfo::Default, c.ratq.clone(), e)
                };

                let beta_b = {
                    let mut bmb = EnvDeclBuilder::child_of(&bp);
                    let (y_id, y) = bmb.fresh_local(c.ratq.clone());
                    let body = inner_p(&y, &bmb);
                    let lam = bmb.mk_lam(y_id, BinderInfo::Default, c.ratq.clone(), body);
                    bmb.finish_child(lam)
                };

                let minor_b = {
                    let mut bq = EnvDeclBuilder::child_of(&bp);
                    let (q_id, q) = bq.fresh_local(c.raw.clone());
                    let mk_q = c.quot_mk(q.clone());

                    let beta_c = {
                        let mut bmc = EnvDeclBuilder::child_of(&bq);
                        let (z_id, z) = bmc.fresh_local(c.ratq.clone());
                        let le_ab = Expr::apps(ratq_le.clone(), [mk_p.clone(), mk_q.clone()]);
                        let le_bc = Expr::apps(ratq_le.clone(), [mk_q.clone(), z.clone()]);
                        let le_ac = Expr::apps(ratq_le.clone(), [mk_p.clone(), z.clone()]);
                        let body = {
                            let mut bb = EnvDeclBuilder::child_of(&bmc);
                            let (h1_id, _h1) = bb.fresh_local(le_ab.clone());
                            let (h2_id, _h2) = bb.fresh_local(le_bc.clone());
                            let e =
                                bb.mk_pi(h2_id, BinderInfo::Default, le_bc.clone(), le_ac.clone());
                            let e = bb.mk_pi(h1_id, BinderInfo::Default, le_ab.clone(), e);
                            bb.finish_child(e)
                        };
                        let lam = bmc.mk_lam(z_id, BinderInfo::Default, c.ratq.clone(), body);
                        bmc.finish_child(lam)
                    };

                    let minor_c = {
                        let mut br = EnvDeclBuilder::child_of(&bq);
                        let (r_id, r) = br.fresh_local(c.raw.clone());
                        // λ (h1 : Raw.le p q)(h2 : Raw.le q r) =>
                        //   le_cross_trans np nq nr (kd p)(kd q)(kd r) h1 h2.
                        let le_pq = c.raw_le(&p, &q);
                        let le_qr = c.raw_le(&q, &r);
                        let (h1_id, h1) = br.fresh_local(le_pq.clone());
                        let (h2_id, h2) = br.fresh_local(le_qr.clone());
                        let body = c.le_cross_trans(
                            c.num(p.clone()),
                            c.num(q.clone()),
                            c.num(r.clone()),
                            c.kd(&p),
                            c.kd(&q),
                            c.kd(&r),
                            h1,
                            h2,
                        );
                        let lam = br.mk_lam(h2_id, BinderInfo::Default, le_qr, body);
                        let lam = br.mk_lam(h1_id, BinderInfo::Default, le_pq, lam);
                        let lam = br.mk_lam(r_id, BinderInfo::Default, c.raw.clone(), lam);
                        br.finish_child(lam)
                    };

                    let ind_c = Expr::apps(
                        c.quot_ind.clone(),
                        [c.raw.clone(), c.raw_equiv.clone(), beta_c, minor_c],
                    );
                    let lam = bq.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), ind_c);
                    bq.finish_child(lam)
                };

                let ind_b = Expr::apps(
                    c.quot_ind.clone(),
                    [c.raw.clone(), c.raw_equiv.clone(), beta_b, minor_b],
                );
                let lam = bp.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), ind_b);
                bp.finish_child(lam)
            };

            let ind_a = Expr::apps(
                c.quot_ind.clone(),
                [
                    c.raw.clone(),
                    c.raw_equiv.clone(),
                    beta_a,
                    minor_a,
                    a.clone(),
                ],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), ind_a);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.mul_pos : ∀ a b : Rat,
    ///    Rat.lt Rat.zero a → Rat.lt Rat.zero b → Rat.lt Rat.zero (Rat.mul a b)`.
    /// Double `Quot.ind`. `Rat.zero ≡ Quot.mk (Raw.mk 0 1)`, so for reps p,q the
    /// hyps def-reduce to `Int.lt (0·ep)(np·e1)` (e1 ≡ ofNat 1), normalized to
    /// `Int.lt 0 np` via `Int.zero_mul`/`Int.mul_one`; `Int.mul_pos` gives
    /// `Int.lt 0 (np·nq)`, transported back to `Raw.lt zero01 (raw_mul p q)`.
    fn register_rat_q_mul_pos(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.mul_pos");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }
        self.mul_pos_or_nonneg(c, /*strict=*/ true)
    }

    /// `Rat.mul_nonneg : ∀ a b : Rat,
    ///    Rat.le Rat.zero a → Rat.le Rat.zero b → Rat.le Rat.zero (Rat.mul a b)`.
    /// The `Rat.le` analogue of `mul_pos` (via `Int.mul_nonneg`).
    fn register_rat_q_mul_nonneg(&mut self, c: &RatRawConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.mul_nonneg");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }
        self.mul_pos_or_nonneg(c, /*strict=*/ false)
    }

    /// Shared body for `Rat.mul_pos` (`strict = true`, over `Rat.lt`/`Int.lt`/
    /// `Int.mul_pos`) and `Rat.mul_nonneg` (`strict = false`, over `Rat.le`/
    /// `Int.le`/`Int.mul_nonneg`).
    fn mul_pos_or_nonneg(&mut self, c: &RatRawConsts, strict: bool) -> Result<(), EnvError> {
        let name = Name::from_string(if strict {
            "Rat.mul_pos"
        } else {
            "Rat.mul_nonneg"
        });
        let ratq_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let ratq_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let rel = |c: &RatRawConsts, x: Expr, y: Expr| -> Expr {
            if strict {
                c.int_lt(x, y)
            } else {
                c.int_le(x, y)
            }
        };
        let ratq_rel = Expr::const_(
            Name::from_string(if strict { "Rat.lt" } else { "Rat.le" }),
            vec![],
        );
        // The Int multiplicativity lemma:
        //   strict : Int.mul_pos    : 0<na → 0<nb → 0<(na·nb)
        //   nonneg : Int.mul_nonneg : 0≤na → 0≤nb → 0≤(na·nb)
        let int_mul_rel = if strict {
            c.int_mul_pos.clone()
        } else {
            c.int_mul_nonneg.clone()
        };

        let nat_one = Expr::app(c.nat_succ.clone(), c.nat_zero.clone());
        let one_int = c.of_nat(nat_one.clone());
        let zero01 = c.raw_mk(c.int_zero.clone(), nat_one.clone());

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());
            let (bv_id, bv) = b.fresh_local(c.ratq.clone());
            let r0a = Expr::apps(ratq_rel.clone(), [ratq_zero.clone(), a.clone()]);
            let r0b = Expr::apps(ratq_rel.clone(), [ratq_zero.clone(), bv.clone()]);
            let (ha_id, _ha) = b.fresh_local(r0a.clone());
            let (hb_id, _hb) = b.fresh_local(r0b.clone());
            let mul_ab = Expr::apps(ratq_mul.clone(), [a.clone(), bv.clone()]);
            let concl = Expr::apps(ratq_rel.clone(), [ratq_zero.clone(), mul_ab]);
            let e = b.mk_pi(hb_id, BinderInfo::Default, r0b, concl);
            let e = b.mk_pi(ha_id, BinderInfo::Default, r0a, e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.ratq.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.ratq.clone(), e);
            b.finish(e)
        };

        // Build the per-representative minor (innermost), given reps p,q and the
        // two hypotheses (typed at the stated `Rat.rel 0 (mk _)` which def-reduces
        // to the raw Int relation).
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.ratq.clone());

            // motive over the first argument: r0a → r0b → concl, built as a Pi.
            let goal_pi = |a: &Expr, bv: &Expr, parent: &EnvDeclBuilder| -> Expr {
                let r0a = Expr::apps(ratq_rel.clone(), [ratq_zero.clone(), a.clone()]);
                let r0b = Expr::apps(ratq_rel.clone(), [ratq_zero.clone(), bv.clone()]);
                let mul_ab = Expr::apps(ratq_mul.clone(), [a.clone(), bv.clone()]);
                let concl = Expr::apps(ratq_rel.clone(), [ratq_zero.clone(), mul_ab]);
                let mut bb = EnvDeclBuilder::child_of(parent);
                let (ha_id, _ha) = bb.fresh_local(r0a.clone());
                let (hb_id, _hb) = bb.fresh_local(r0b.clone());
                let e = bb.mk_pi(hb_id, BinderInfo::Default, r0b, concl);
                let e = bb.mk_pi(ha_id, BinderInfo::Default, r0a, e);
                bb.finish_child(e)
            };

            let beta_a = {
                let mut bm = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = bm.fresh_local(c.ratq.clone());
                let body = {
                    let mut bb = EnvDeclBuilder::child_of(&bm);
                    let (y_id, y) = bb.fresh_local(c.ratq.clone());
                    let g = goal_pi(&x, &y, &bb);
                    let e = bb.mk_pi(y_id, BinderInfo::Default, c.ratq.clone(), g);
                    bb.finish_child(e)
                };
                let lam = bm.mk_lam(x_id, BinderInfo::Default, c.ratq.clone(), body);
                bm.finish_child(lam)
            };

            let minor_a = {
                let mut bp = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = bp.fresh_local(c.raw.clone());
                let mk_p = c.quot_mk(p.clone());
                let beta_b = {
                    let mut bmb = EnvDeclBuilder::child_of(&bp);
                    let (y_id, y) = bmb.fresh_local(c.ratq.clone());
                    let body = goal_pi(&mk_p, &y, &bmb);
                    let lam = bmb.mk_lam(y_id, BinderInfo::Default, c.ratq.clone(), body);
                    bmb.finish_child(lam)
                };
                let minor_b = {
                    let mut bq = EnvDeclBuilder::child_of(&bp);
                    let (q_id, q) = bq.fresh_local(c.raw.clone());

                    let np = c.num(p.clone());
                    let nq = c.num(q.clone());
                    let ep = c.eff(p.clone());
                    let eq = c.eff(q.clone());

                    // Hyp types (stated): rel (mk zero01) (mk p) — def-reduces to
                    //   Int.rel (0·ep) (np·E0)   with E0 ≡ ofNat 1.
                    let r0a = {
                        let lhs = c.mul(c.int_zero.clone(), ep.clone());
                        let rhs = c.mul(np.clone(), one_int.clone());
                        rel(c, lhs, rhs)
                    };
                    let r0b = {
                        let lhs = c.mul(c.int_zero.clone(), eq.clone());
                        let rhs = c.mul(nq.clone(), one_int.clone());
                        rel(c, lhs, rhs)
                    };
                    let (ha_id, ha) = bq.fresh_local(r0a.clone());
                    let (hb_id, hb) = bq.fresh_local(r0b.clone());

                    // Normalize ha : Int.rel (0·ep)(np·1) → Int.rel 0 np.
                    let norm = |c: &RatRawConsts,
                                parent: &EnvDeclBuilder,
                                den: &Expr,
                                num: &Expr,
                                h: Expr|
                     -> Expr {
                        // step A: rewrite LHS 0·den → 0 via Int.zero_mul.
                        let mul0 = c.mul(c.int_zero.clone(), den.clone());
                        let num1 = c.mul(num.clone(), one_int.clone());
                        let hzm = Expr::app(c.int_zero_mul_2.clone(), den.clone());
                        let motive_lhs = {
                            let mut ch = EnvDeclBuilder::child_of(parent);
                            let (x_id, x) = ch.fresh_local(c.int.clone());
                            let body = rel(c, x, num1.clone());
                            let r = ch.mk_lam(x_id, BinderInfo::Default, c.int.clone(), body);
                            ch.finish_child(r)
                        };
                        let h1 = Expr::apps(
                            c.eq_subst_int.clone(),
                            [c.int.clone(), motive_lhs, mul0, c.int_zero.clone(), hzm, h],
                        );
                        // step B: rewrite RHS num·1 → num via Int.mul_one.
                        let hmo = Expr::app(c.int_mul_one.clone(), num.clone());
                        let motive_rhs = {
                            let mut ch = EnvDeclBuilder::child_of(parent);
                            let (y_id, y) = ch.fresh_local(c.int.clone());
                            let body = rel(c, c.int_zero.clone(), y);
                            let r = ch.mk_lam(y_id, BinderInfo::Default, c.int.clone(), body);
                            ch.finish_child(r)
                        };
                        Expr::apps(
                            c.eq_subst_int.clone(),
                            [c.int.clone(), motive_rhs, num1, num.clone(), hmo, h1],
                        )
                    };
                    let ha_norm = norm(c, &bq, &ep, &np, ha);
                    let hb_norm = norm(c, &bq, &eq, &nq, hb);

                    // Int.mul_rel 0<np 0<nq : Int.rel 0 (np·nq).
                    let core = Expr::apps(
                        int_mul_rel.clone(),
                        [np.clone(), nq.clone(), ha_norm, hb_norm],
                    );

                    // Transport Int.rel 0 (np·nq) → Raw.rel zero01 (raw_mul p q),
                    // which is Int.rel (0·E(raw_mul p q)) ((np·nq)·E0).
                    // Step C: 0 → 0·E(raw_mul p q)  (symm Int.zero_mul).
                    let raw_lhs = c.raw_mul(&p, &q);
                    let eff_lhs = c.eff(raw_lhs.clone());
                    let num_lhs = c.mul(np.clone(), nq.clone()); // num (raw_mul p q)
                    let zero_eff = c.mul(c.int_zero.clone(), eff_lhs.clone());
                    let hzm2 = Expr::app(c.int_zero_mul_2.clone(), eff_lhs.clone()); // 0·E = 0
                    let motive_c = {
                        let mut ch = EnvDeclBuilder::child_of(&bq);
                        let (x_id, x) = ch.fresh_local(c.int.clone());
                        let body = rel(c, x, num_lhs.clone());
                        let r = ch.mk_lam(x_id, BinderInfo::Default, c.int.clone(), body);
                        ch.finish_child(r)
                    };
                    // hzm2_sym : 0 = 0·E.
                    let hzm2_sym = c.symm_int(zero_eff.clone(), c.int_zero.clone(), hzm2);
                    let core_c = Expr::apps(
                        c.eq_subst_int.clone(),
                        [
                            c.int.clone(),
                            motive_c,
                            c.int_zero.clone(),
                            zero_eff.clone(),
                            hzm2_sym,
                            core,
                        ],
                    );
                    // Step D: (np·nq) → (np·nq)·E0  (symm Int.mul_one) on the RHS.
                    let num_one = c.mul(num_lhs.clone(), one_int.clone());
                    let hmo2 = Expr::app(c.int_mul_one.clone(), num_lhs.clone()); // (np·nq)·1 = np·nq
                    let hmo2_sym = c.symm_int(num_one.clone(), num_lhs.clone(), hmo2);
                    let motive_d = {
                        let mut ch = EnvDeclBuilder::child_of(&bq);
                        let (y_id, y) = ch.fresh_local(c.int.clone());
                        let body = rel(c, zero_eff.clone(), y);
                        let r = ch.mk_lam(y_id, BinderInfo::Default, c.int.clone(), body);
                        ch.finish_child(r)
                    };
                    let body = Expr::apps(
                        c.eq_subst_int.clone(),
                        [
                            c.int.clone(),
                            motive_d,
                            num_lhs.clone(),
                            num_one,
                            hmo2_sym,
                            core_c,
                        ],
                    );
                    // body : Int.rel (0·E(raw_mul p q)) ((np·nq)·E0)
                    //      ≡ Raw.rel zero01 (raw_mul p q)
                    //      ≡ Rat.rel (mk zero01)(mul (mk p)(mk q)).
                    let lam = bq.mk_lam(hb_id, BinderInfo::Default, r0b, body);
                    let lam = bq.mk_lam(ha_id, BinderInfo::Default, r0a, lam);
                    let lam = bq.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), lam);
                    bq.finish_child(lam)
                };
                let ind_b = Expr::apps(
                    c.quot_ind.clone(),
                    [c.raw.clone(), c.raw_equiv.clone(), beta_b, minor_b],
                );
                let lam = bp.mk_lam(p_id, BinderInfo::Default, c.raw.clone(), ind_b);
                bp.finish_child(lam)
            };

            let ind_a = Expr::apps(
                c.quot_ind.clone(),
                [
                    c.raw.clone(),
                    c.raw_equiv.clone(),
                    beta_a,
                    minor_a,
                    a.clone(),
                ],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, c.ratq.clone(), ind_a);
            // silence the unused `zero01` binding when both branches share it.
            let _ = &zero01;
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn env() -> Environment {
        let mut env = Environment::new();
        env.init_rat_quotient_poc()
            .expect("init_rat_quotient_poc should succeed");
        env
    }

    #[test]
    fn test_carrier_registered() {
        let env = env();
        assert!(env.get_inductive(&Name::from_string("Rat.Raw")).is_some());
        for n in &["Rat.Raw.num", "Rat.Raw.denom", "Rat.Raw.effDenom"] {
            assert!(
                env.get_const(&Name::from_string(n)).is_some(),
                "{n} should be registered"
            );
        }
    }

    /// `Rat.inv` / `Rat.div` are registered Definitions whose well-definedness
    /// (`Quot.lift` respect) is a genuine kernel-checked proof, and applying
    /// `Rat.inv` to a concrete class type-checks (the sign-split respect proof
    /// reduces under the constructor).
    #[test]
    fn test_inv_div_instances_type_check() {
        use crate::tc::TypeChecker;
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nat = |k: u64| {
            let mut e = Expr::const_(Name::from_string("Nat.zero"), vec![]);
            let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
            for _ in 0..k {
                e = Expr::app(succ.clone(), e);
            }
            e
        };
        let of_nat =
            |k: u64| Expr::app(Expr::const_(Name::from_string("Int.ofNat"), vec![]), nat(k));
        let neg_of = |k: u64| {
            Expr::app(
                Expr::const_(Name::from_string("Int.negSucc"), vec![]),
                nat(k),
            )
        };
        let mk = |n: Expr, d: u64| {
            Expr::apps(
                Expr::const_(Name::from_string("Rat.mk"), vec![]),
                [n, nat(d)],
            )
        };
        let inv = Expr::const_(Name::from_string("Rat.inv"), vec![]);
        let div = Expr::const_(Name::from_string("Rat.div"), vec![]);
        // inv of a positive, negative, and zero rational all type-check.
        for r in [mk(of_nat(3), 5), mk(neg_of(2), 4), mk(of_nat(0), 7)] {
            let term = Expr::app(inv.clone(), r);
            let _ = tc
                .infer_type(&term)
                .unwrap_or_else(|e| panic!("Rat.inv instance must type-check: {e:?}"));
        }
        // div a b = mul a (inv b).
        let term = Expr::apps(div.clone(), [mk(of_nat(1), 2), mk(of_nat(3), 4)]);
        let _ = tc
            .infer_type(&term)
            .unwrap_or_else(|e| panic!("Rat.div instance must type-check: {e:?}"));
    }

    #[test]
    fn test_quotient_and_mul_type_check() {
        use crate::tc::TypeChecker;
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for n in &[
            "Rat",
            "Rat.mk",
            "Rat.zero",
            "Rat.one",
            "Rat.mul",
            "Rat.neg",
            "Rat.add",
            "Rat.le",
            "Rat.lt",
            "Rat.inv",
            "Rat.div",
            "Rat.Int.mulMulMulComm",
        ] {
            assert!(
                env.get_const(&Name::from_string(n)).is_some(),
                "{n} should be registered"
            );
            let _ = tc
                .infer_type(&Expr::const_(Name::from_string(n), vec![]))
                .unwrap_or_else(|e| panic!("{n} should kernel-type-check: {e:?}"));
        }
    }

    #[test]
    fn test_equiv_is_equivalence() {
        use crate::env::types::ConstantKind;
        use crate::tc::TypeChecker;
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for n in &[
            "Rat.Raw.Equiv.refl",
            "Rat.Raw.Equiv.symm",
            "Rat.Raw.Equiv.trans",
        ] {
            let info = env
                .get_const(&Name::from_string(n))
                .unwrap_or_else(|| panic!("{n} should be registered"));
            assert_eq!(info.kind, ConstantKind::Theorem, "{n} must be a Theorem");
            let _ = tc
                .infer_type(&Expr::const_(Name::from_string(n), vec![]))
                .unwrap_or_else(|e| panic!("{n} should kernel-type-check: {e:?}"));
        }
    }

    /// THE PAYOFF. The two axioms that are PROVABLY FALSE over the free `Rat`
    /// carrier are genuine kernel-checked `Theorem`s over the quotient `Qat`,
    /// each `Constructive` (transitive axiom closure ⊆ FOUNDATIONAL, i.e. only
    /// `Quot.sound` / `propext`).
    #[test]
    fn test_payoff_theorems_are_constructive() {
        use crate::env::types::ConstantKind;
        use crate::env::ProofQuality;
        use crate::tc::TypeChecker;
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for n in &[
            "Rat.zero_mul",
            "Rat.mul_zero",
            "Rat.add_left_neg",
            "Rat.add_neg_self",
            "Rat.le_antisymm",
            "Rat.add_le_add_left",
            "Rat.le_add_of_nonneg_right",
            "Rat.left_distrib",
            "Rat.right_distrib",
            "Rat.add_zero",
            "Rat.add_assoc",
            "Rat.add_right_cancel",
            "Rat.mul_inv_cancel",
        ] {
            let info = env
                .get_const(&Name::from_string(n))
                .unwrap_or_else(|| panic!("{n} should be registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{n} must be Declaration::Theorem (not Axiom), got {:?}",
                info.kind
            );
            assert!(
                info.value.is_some(),
                "{n} Theorem must retain a proof value"
            );
            let _ = tc
                .infer_type(&Expr::const_(Name::from_string(n), vec![]))
                .unwrap_or_else(|e| panic!("{n} should kernel-type-check: {e:?}"));
            let q = env
                .proof_quality(&Name::from_string(n))
                .unwrap_or_else(|| panic!("{n} proof_quality"));
            assert!(
                matches!(q, ProofQuality::Constructive),
                "{n} must be Constructive (closure ⊆ FOUNDATIONAL: Quot.sound / \
                 propext are foundational), got {q:?}"
            );
        }
    }

    /// The transitive axiom closure of each payoff theorem contains ONLY
    /// foundational axioms (no domain-specific axiom). This pins the
    /// `Constructive` classification to the precise axiom set.
    #[test]
    fn test_payoff_axiom_closure_is_foundational_only() {
        let env = env();
        for n in &[
            "Rat.zero_mul",
            "Rat.mul_zero",
            "Rat.add_left_neg",
            "Rat.add_neg_self",
            "Rat.le_antisymm",
            "Rat.add_le_add_left",
            "Rat.le_add_of_nonneg_right",
            "Rat.left_distrib",
            "Rat.right_distrib",
            "Rat.add_zero",
            "Rat.add_assoc",
            "Rat.add_right_cancel",
            "Rat.mul_inv_cancel",
        ] {
            let deps = env
                .axiom_deps(&Name::from_string(n))
                .unwrap_or_else(|| panic!("{n} axiom_deps"));
            assert!(
                deps.is_empty(),
                "{n} must have NO non-foundational axiom in its closure, got {:?}",
                deps.iter().map(|a| a.to_string()).collect::<Vec<_>>()
            );
        }
    }

    /// Witness the previously-FALSE instance is now a kernel-checked proof:
    /// `Qat.zero_mul (Qat.mk 3 5) : @Eq Qat (Qat.mul Qat.zero (Qat.mk 3 5)) Qat.zero`.
    /// Over the free `Rat` this exact statement is FALSE (`mul (mk 0 1)(mk 3 5)`
    /// is structurally `mk 0 5`, not `mk 0 1`); over `Qat` the application
    /// type-checks because the two classes are propositionally equal via
    /// `Quot.sound`.
    #[test]
    fn test_zero_mul_instance_type_checks() {
        use crate::tc::TypeChecker;
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());

        let nat = |k: u64| {
            let mut e = Expr::const_(Name::from_string("Nat.zero"), vec![]);
            let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
            for _ in 0..k {
                e = Expr::app(succ.clone(), e);
            }
            e
        };
        let of_nat =
            |k: u64| Expr::app(Expr::const_(Name::from_string("Int.ofNat"), vec![]), nat(k));
        // a := Qat.mk 3 5
        let a = Expr::apps(
            Expr::const_(Name::from_string("Rat.mk"), vec![]),
            [of_nat(3), nat(5)],
        );
        // Qat.zero_mul a  : Eq Qat (Qat.mul Qat.zero (Qat.mk 3 5)) Qat.zero
        let term = Expr::app(Expr::const_(Name::from_string("Rat.zero_mul"), vec![]), a);
        let _ = tc
            .infer_type(&term)
            .expect("Qat.zero_mul (Qat.mk 3 5) must kernel-type-check");
    }

    /// `Qat.le_antisymm` discharges the `mk 1 1` / `mk 2 2` counterexample:
    /// the application `Qat.le_antisymm (Qat.mk 1 1) (Qat.mk 2 2)` type-checks
    /// (its result is `le … → le … → Eq Qat (mk 1 1)(mk 2 2)`), whereas the
    /// structural `@Eq Rat (mk 1 1)(mk 2 2)` is FALSE.
    #[test]
    fn test_le_antisymm_instance_type_checks() {
        use crate::tc::TypeChecker;
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());

        let nat = |k: u64| {
            let mut e = Expr::const_(Name::from_string("Nat.zero"), vec![]);
            let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
            for _ in 0..k {
                e = Expr::app(succ.clone(), e);
            }
            e
        };
        let of_nat =
            |k: u64| Expr::app(Expr::const_(Name::from_string("Int.ofNat"), vec![]), nat(k));
        let mk = |n: u64, d: u64| {
            Expr::apps(
                Expr::const_(Name::from_string("Rat.mk"), vec![]),
                [of_nat(n), nat(d)],
            )
        };
        let term = Expr::apps(
            Expr::const_(Name::from_string("Rat.le_antisymm"), vec![]),
            [mk(1, 1), mk(2, 2)],
        );
        let _ = tc
            .infer_type(&term)
            .expect("Qat.le_antisymm (mk 1 1)(mk 2 2) must kernel-type-check");
    }

    /// `Rat.lt` is registered and its strict cross-multiplication toolkit
    /// (`Int.lt_cross_trans{,'}` + the two strict-mul building blocks) is a
    /// kernel-checked `Constructive` Theorem set. Also pins the `Rat.lt`
    /// application `Rat.lt (mk 1 2)(mk 3 4)` as type-checking.
    #[test]
    fn test_lt_lift_and_strict_int_toolkit() {
        use crate::env::types::ConstantKind;
        use crate::env::ProofQuality;
        use crate::tc::TypeChecker;
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());

        for n in &[
            "Int.lt_of_mul_lt_mul_left_succ",
            "Int.mul_lt_mul_of_pos_right_succ",
            "Int.lt_cross_trans",
            "Int.lt_cross_trans'",
        ] {
            let info = env
                .get_const(&Name::from_string(n))
                .unwrap_or_else(|| panic!("{n} should be registered"));
            assert_eq!(info.kind, ConstantKind::Theorem, "{n} must be a Theorem");
            let _ = tc
                .infer_type(&Expr::const_(Name::from_string(n), vec![]))
                .unwrap_or_else(|e| panic!("{n} should kernel-type-check: {e:?}"));
            let q = env
                .proof_quality(&Name::from_string(n))
                .unwrap_or_else(|| panic!("{n} proof_quality"));
            assert!(
                matches!(q, ProofQuality::Constructive),
                "{n} must be Constructive, got {q:?}"
            );
        }

        // `Rat.lt (Rat.mk 1 2) (Rat.mk 3 4)` type-checks (a Prop).
        let nat = |k: u64| {
            let mut e = Expr::const_(Name::from_string("Nat.zero"), vec![]);
            let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
            for _ in 0..k {
                e = Expr::app(succ.clone(), e);
            }
            e
        };
        let of_nat =
            |k: u64| Expr::app(Expr::const_(Name::from_string("Int.ofNat"), vec![]), nat(k));
        let mk = |n: u64, d: u64| {
            Expr::apps(
                Expr::const_(Name::from_string("Rat.mk"), vec![]),
                [of_nat(n), nat(d)],
            )
        };
        let term = Expr::apps(
            Expr::const_(Name::from_string("Rat.lt"), vec![]),
            [mk(1, 2), mk(3, 4)],
        );
        let _ = tc
            .infer_type(&term)
            .expect("Rat.lt (mk 1 2)(mk 3 4) must kernel-type-check");
    }

    /// Idempotent: a second `init_rat_quotient_poc` is a no-op success.
    #[test]
    fn test_idempotent() {
        let mut env = Environment::new();
        env.init_rat_quotient_poc().expect("first init");
        env.init_rat_quotient_poc().expect("second init idempotent");
    }
}
