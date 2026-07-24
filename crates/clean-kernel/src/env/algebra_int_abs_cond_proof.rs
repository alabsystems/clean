// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Constructive proofs of the conditional absolute-value identities:
//!
//! ```text
//! Int.abs_of_nonneg : ∀ a : Int, Int.le (Int.ofNat 0) a → Eq Int (Int.abs a) a
//! Int.abs_of_neg    : ∀ a : Int, Int.lt a (Int.ofNat 0) → Eq Int (Int.abs a) (Int.neg a)
//! ```
//!
//! These replace the prior `Declaration::Axiom` registrations of
//! `Int.abs_of_nonneg` / `Int.abs_of_neg` in
//! `algebra_abs_int.rs::init_int_abs_props` with kernel-checked
//! `Declaration::Theorem`s.
//!
//! # Definitions in play
//!
//! ```text
//! Int.abs i    := Int.ofNat (Int.natAbs i)                 -- reducible
//! Int.natAbs (Int.ofNat n)   ≡ n
//! Int.natAbs (Int.negSucc n) ≡ Nat.succ n
//! Int.neg (Int.ofNat 0)        ≡ Int.ofNat 0
//! Int.neg (Int.ofNat (succ n)) ≡ Int.negSucc n
//! Int.neg (Int.negSucc n)      ≡ Int.ofNat (Nat.succ n)
//! Int.le a b := Int.NonNeg (Int.sub b a)
//! Int.sub a b := Int.add a (Int.neg b)
//! Int.lt a b := Int.le (Int.add a (Int.ofNat 1)) b
//! inductive Int.NonNeg : Int → Prop where | mk (n : Nat) : Int.NonNeg (Int.ofNat n)
//! ```
//!
//! # Proof sketch — `Int.abs_of_nonneg`
//!
//! `h : Int.le 0 a` delta-reduces to `Int.NonNeg (Int.add a (Int.ofNat 0))`
//! (since `Int.neg (ofNat 0) ≡ ofNat 0` so `Int.sub a 0 ≡ Int.add a 0`).
//! Transport `h` across `Int.add_zero a : Int.add a 0 = a` via `@Eq.subst.{1}`
//! (motive `fun x => NonNeg x`) to `h' : NonNeg a`. Then `@Int.NonNeg.rec.{0}`
//! with motive `fun (i : Int) (_ : NonNeg i) => Eq Int (Int.abs i) i` and the
//! single minor `fun (n : Nat) => @Eq.refl.{1} Int (Int.ofNat n)` closes the
//! goal, because `Int.abs (Int.ofNat n) ≡ Int.ofNat n`.
//!
//! # Proof sketch — `Int.abs_of_neg`
//!
//! Recurse on `a` with `@Int.rec.{0}` whose motive
//! `fun (x : Int) => Int.lt x 0 → Eq Int (Int.abs x) (Int.neg x)` threads the
//! hypothesis through the case split; the recursor's result `motive a` is then
//! applied to the incoming `h`.
//!
//! * `Int.ofNat n` case: the threaded hypothesis
//!   `hn : Int.lt (ofNat n) 0` delta-reduces to
//!   `Int.NonNeg (Int.subNatNat Nat.zero (Nat.succ n))`
//!   (because `Int.add (ofNat n) (ofNat 1) ≡ ofNat (succ n)`,
//!   `Int.neg (ofNat (succ n)) ≡ negSucc n`,
//!   `Int.add (ofNat 0) (negSucc n) ≡ subNatNat 0 (succ n)`). Transport across
//!   `Int.subNatNat_zero_succ n : subNatNat 0 (succ n) = negSucc n` to
//!   `NonNeg (negSucc n)`, discriminate it to `False` with the
//!   `True`/`False` `@Int.rec.{1}` predicate, and conclude any goal via
//!   `@False.elim.{0}`. (This branch is vacuous.)
//! * `Int.negSucc n` case: `Int.abs (negSucc n) ≡ ofNat (succ n)` and
//!   `Int.neg (negSucc n) ≡ ofNat (succ n)`, so the goal is closed by
//!   `@Eq.refl.{1} Int (Int.ofNat (Nat.succ n))`.
//!
//! # Axiom closure
//!
//! Mentions only `Int`, `Int.abs`, `Int.neg`, `Int.le`, `Int.lt`, `Int.add`,
//! `Int.sub`, `Int.ofNat`, `Int.negSucc`, `Int.subNatNat`, `Int.natAbs`,
//! `Int.NonNeg`, `Int.NonNeg.rec`, `Int.rec`, `Nat`, `Nat.zero`, `Nat.succ`,
//! `True`, `True.intro`, `False`, `False.elim`, the constructive
//! `Int.add_zero` / `Int.subNatNat_zero_succ` theorems, and the foundational
//! `Eq.refl` / `Eq.subst` / `Eq.symm`. None is a `Declaration::Axiom`, so the
//! domain-axiom closure of each registered theorem is empty
//! (`ProofQuality::Constructive`).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across both proofs.
struct IntAbsCondConsts {
    int_type: Expr,
    nat_type: Expr,
    int_abs: Expr,
    int_neg: Expr,
    int_le: Expr,
    int_lt: Expr,
    int_add: Expr,
    int_of_nat: Expr,
    int_neg_succ: Expr,
    int_sub_nat_nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nonneg: Expr,
    nonneg_rec: Expr,
    int_rec_prop: Expr,
    int_rec_type: Expr,
    true_const: Expr,
    true_intro: Expr,
    false_const: Expr,
    false_elim: Expr,
    int_add_zero: Expr,
    sub_nat_nat_zero_succ: Expr,
    eq_const: Expr,
    eq_refl: Expr,
    eq_subst: Expr,
}

impl IntAbsCondConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            int_abs: Expr::const_(Name::from_string("Int.abs"), vec![]),
            int_neg: Expr::const_(Name::from_string("Int.neg"), vec![]),
            int_le: Expr::const_(Name::from_string("Int.le"), vec![]),
            int_lt: Expr::const_(Name::from_string("Int.lt"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            int_sub_nat_nat: Expr::const_(Name::from_string("Int.subNatNat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nonneg: Expr::const_(Name::from_string("Int.NonNeg"), vec![]),
            // NonNeg.rec into Prop — Sort 0.
            nonneg_rec: Expr::const_(Name::from_string("Int.NonNeg.rec"), vec![]),
            // Int.rec producing a `Prop : Sort 1` value (the discriminator) — Sort 1.
            int_rec_prop: Expr::const_(Name::from_string("Int.rec"), vec![type1.clone()]),
            // Int.rec producing a `Prop`-valued (Sort 0) proof — Sort 0.
            int_rec_type: Expr::const_(Name::from_string("Int.rec"), vec![Level::zero()]),
            true_const: Expr::const_(Name::from_string("True"), vec![]),
            true_intro: Expr::const_(Name::from_string("True.intro"), vec![]),
            false_const: Expr::const_(Name::from_string("False"), vec![]),
            // The goal closed by False.elim is an `Eq … : Prop` (Sort 0).
            false_elim: Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            int_add_zero: Expr::const_(Name::from_string("Int.add_zero"), vec![]),
            sub_nat_nat_zero_succ: Expr::const_(
                Name::from_string("Int.subNatNat_zero_succ"),
                vec![],
            ),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![type1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![type1]),
        }
    }

    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }

    fn int_zero(&self) -> Expr {
        self.of_nat(self.nat_zero.clone())
    }

    fn neg_succ(&self, n: Expr) -> Expr {
        Expr::app(self.int_neg_succ.clone(), n)
    }

    fn abs(&self, x: Expr) -> Expr {
        Expr::app(self.int_abs.clone(), x)
    }

    fn neg(&self, x: Expr) -> Expr {
        Expr::app(self.int_neg.clone(), x)
    }

    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), x), y)
    }

    fn le(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_le.clone(), x), y)
    }

    fn lt(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_lt.clone(), x), y)
    }

    fn nonneg_of(&self, x: Expr) -> Expr {
        Expr::app(self.nonneg.clone(), x)
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }

    /// `@Eq.refl.{1} Int v`.
    fn eq_refl_int(&self, v: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.int_type.clone(), v])
    }
}

// ---------------------------------------------------------------------------
// Int.abs_of_nonneg
// ---------------------------------------------------------------------------

/// `∀ a : Int, Int.le (Int.ofNat 0) a → Eq Int (Int.abs a) a`.
fn build_of_nonneg_type(c: &IntAbsCondConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let h_type = c.le(c.int_zero(), a.clone());
    let (h_id, _h) = b.fresh_local(h_type.clone());
    let concl = c.eq_int(c.abs(a.clone()), a.clone());
    let r = b.mk_pi(h_id, BinderInfo::Default, h_type, concl);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// ```text
/// λ (a : Int) (h : Int.le 0 a) =>
///   @Int.NonNeg.rec.{0}
///     (fun (i : Int) (_ : NonNeg i) => Eq Int (Int.abs i) i)
///     (fun (n : Nat) => @Eq.refl.{1} Int (Int.ofNat n))
///     a
///     (@Eq.subst.{1} Int (fun x => NonNeg x)
///        (Int.add a 0) a (Int.add_zero a) h)
/// ```
fn build_of_nonneg_value(c: &IntAbsCondConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let h_type = c.le(c.int_zero(), a.clone());
    let (h_id, h) = b.fresh_local(h_type.clone());

    // motive for transport: fun x : Int => Int.NonNeg x
    let subst_motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(c.int_type.clone());
        let body = c.nonneg_of(x);
        let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
        mb.finish_child(lam)
    };

    // h' : NonNeg a := @Eq.subst.{1} Int motive (add a 0) a (Int.add_zero a) h.
    // (h : le 0 a ≡ NonNeg (add a 0) up to defeq.)
    let add_a_zero = c.add(a.clone(), c.int_zero());
    let add_zero_a = Expr::app(c.int_add_zero.clone(), a.clone());
    let h_prime = Expr::apps(
        c.eq_subst.clone(),
        [
            c.int_type.clone(),
            subst_motive,
            add_a_zero,
            a.clone(),
            add_zero_a,
            h.clone(),
        ],
    );

    // NonNeg.rec motive: fun (i : Int) (_ : NonNeg i) => Eq Int (Int.abs i) i
    let rec_motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = mb.fresh_local(c.int_type.clone());
        let hi_type = c.nonneg_of(i.clone());
        let (hi_id, _hi) = mb.fresh_local(hi_type.clone());
        let body = c.eq_int(c.abs(i.clone()), i.clone());
        let lam = mb.mk_lam(hi_id, BinderInfo::Default, hi_type, body);
        let lam = mb.mk_lam(i_id, BinderInfo::Default, c.int_type.clone(), lam);
        mb.finish_child(lam)
    };

    // NonNeg.rec minor: fun (n : Nat) => @Eq.refl.{1} Int (Int.ofNat n)
    //   goal at minor is `Eq Int (Int.abs (ofNat n)) (ofNat n)` ≡ refl since
    //   `Int.abs (ofNat n) ≡ ofNat n`.
    let rec_minor = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (n_id, n) = mb.fresh_local(c.nat_type.clone());
        let body = c.eq_refl_int(c.of_nat(n.clone()));
        let lam = mb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), body);
        mb.finish_child(lam)
    };

    let rec_app = Expr::apps(
        c.nonneg_rec.clone(),
        [rec_motive, rec_minor, a.clone(), h_prime],
    );

    let val = b.mk_lam(h_id, BinderInfo::Default, h_type, rec_app);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    b.finish(val)
}

// ---------------------------------------------------------------------------
// Int.abs_of_neg
// ---------------------------------------------------------------------------

/// `∀ a : Int, Int.lt a (Int.ofNat 0) → Eq Int (Int.abs a) (Int.neg a)`.
fn build_of_neg_type(c: &IntAbsCondConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let h_type = c.lt(a.clone(), c.int_zero());
    let (h_id, _h) = b.fresh_local(h_type.clone());
    let concl = c.eq_int(c.abs(a.clone()), c.neg(a.clone()));
    let r = b.mk_pi(h_id, BinderInfo::Default, h_type, concl);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// `disc = @Int.rec.{1} (fun _ : Int => Prop) (fun _ : Nat => True)
///                      (fun _ : Nat => False)`.
///
/// `disc (Int.ofNat n)` reduces to `True`, `disc (Int.negSucc n)` to `False`.
fn discriminator(c: &IntAbsCondConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    // motive: fun _ : Int => Prop
    let prop_motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (i_id, _i) = mb.fresh_local(c.int_type.clone());
        let lam = mb.mk_lam(i_id, BinderInfo::Default, c.int_type.clone(), Expr::prop());
        mb.finish_child(lam)
    };
    // ofNat minor: fun _ : Nat => True
    let of_nat_minor = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (n_id, _n) = mb.fresh_local(c.nat_type.clone());
        let lam = mb.mk_lam(
            n_id,
            BinderInfo::Default,
            c.nat_type.clone(),
            c.true_const.clone(),
        );
        mb.finish_child(lam)
    };
    // negSucc minor: fun _ : Nat => False
    let neg_succ_minor = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (n_id, _n) = mb.fresh_local(c.nat_type.clone());
        let lam = mb.mk_lam(
            n_id,
            BinderInfo::Default,
            c.nat_type.clone(),
            c.false_const.clone(),
        );
        mb.finish_child(lam)
    };
    // disc = fun i : Int => @Int.rec.{1} prop_motive of_nat_minor neg_succ_minor i
    let (i_id, i) = b.fresh_local(c.int_type.clone());
    let rec_app = Expr::apps(
        c.int_rec_prop.clone(),
        [prop_motive, of_nat_minor, neg_succ_minor, i.clone()],
    );
    let lam = b.mk_lam(i_id, BinderInfo::Default, c.int_type.clone(), rec_app);
    b.finish_child(lam)
}

/// ```text
/// λ (a : Int) (h : Int.lt a 0) =>
///   @Int.rec.{0}
///     (fun (x : Int) => Int.lt x 0 → Eq Int (Int.abs x) (Int.neg x))
///     of_nat_case
///     neg_succ_case
///     a
///     h
/// ```
fn build_of_neg_value(c: &IntAbsCondConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let h_type = c.lt(a.clone(), c.int_zero());
    let (h_id, h) = b.fresh_local(h_type.clone());

    // Int.rec motive: fun (x : Int) => Int.lt x 0 → Eq Int (Int.abs x) (Int.neg x)
    let rec_motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(c.int_type.clone());
        let hyp = c.lt(x.clone(), c.int_zero());
        let (hyp_id, _hyp) = mb.fresh_local(hyp.clone());
        let concl = c.eq_int(c.abs(x.clone()), c.neg(x.clone()));
        let body = mb.mk_pi(hyp_id, BinderInfo::Default, hyp, concl);
        let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
        mb.finish_child(lam)
    };

    // ----- ofNat case (vacuous) -----
    // fun (n : Nat) (hn : Int.lt (ofNat n) 0) => False.elim (...)
    let of_nat_case = {
        let mut ob = EnvDeclBuilder::child_of(&b);
        let (n_id, n) = ob.fresh_local(c.nat_type.clone());
        let of_nat_n = c.of_nat(n.clone());
        let hn_type = c.lt(of_nat_n.clone(), c.int_zero());
        let (hn_id, hn) = ob.fresh_local(hn_type.clone());

        // subst motive: fun x : Int => Int.NonNeg x
        let subst_motive = {
            let mut mb = EnvDeclBuilder::child_of(&ob);
            let (x_id, x) = mb.fresh_local(c.int_type.clone());
            let body = c.nonneg_of(x);
            let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
            mb.finish_child(lam)
        };

        // subNatNat 0 (succ n)  ≡  Int.lt (ofNat n) 0  (defeq LHS of hn).
        let snn = Expr::app(
            Expr::app(c.int_sub_nat_nat.clone(), c.nat_zero.clone()),
            Expr::app(c.nat_succ.clone(), n.clone()),
        );
        let neg_succ_n = c.neg_succ(n.clone());
        // eq1 : subNatNat 0 (succ n) = negSucc n
        let eq1 = Expr::app(c.sub_nat_nat_zero_succ.clone(), n.clone());
        // hn' : NonNeg (negSucc n)
        //   = @Eq.subst.{1} Int motive (subNatNat 0 (succ n)) (negSucc n) eq1 hn
        let hn_prime = Expr::apps(
            c.eq_subst.clone(),
            [
                c.int_type.clone(),
                subst_motive,
                snn,
                neg_succ_n.clone(),
                eq1,
                hn.clone(),
            ],
        );

        // discriminator predicate
        let disc = discriminator(c, &ob);

        // NonNeg.rec motive: fun (i : Int) (_ : NonNeg i) => disc i
        let nn_rec_motive = {
            let mut mb = EnvDeclBuilder::child_of(&ob);
            let (i_id, i) = mb.fresh_local(c.int_type.clone());
            let hi_type = c.nonneg_of(i.clone());
            let (hi_id, _hi) = mb.fresh_local(hi_type.clone());
            let body = Expr::app(disc.clone(), i.clone());
            let lam = mb.mk_lam(hi_id, BinderInfo::Default, hi_type, body);
            let lam = mb.mk_lam(i_id, BinderInfo::Default, c.int_type.clone(), lam);
            mb.finish_child(lam)
        };

        // NonNeg.rec minor: fun (m : Nat) => True.intro   (goal `disc (ofNat m)` ≡ True)
        let nn_rec_minor = {
            let mut mb = EnvDeclBuilder::child_of(&ob);
            let (m_id, _m) = mb.fresh_local(c.nat_type.clone());
            let lam = mb.mk_lam(
                m_id,
                BinderInfo::Default,
                c.nat_type.clone(),
                c.true_intro.clone(),
            );
            mb.finish_child(lam)
        };

        // @Int.NonNeg.rec.{0} nn_rec_motive nn_rec_minor (negSucc n) hn'
        //   : disc (negSucc n) ≡ False
        let false_proof = Expr::apps(
            c.nonneg_rec.clone(),
            [nn_rec_motive, nn_rec_minor, neg_succ_n, hn_prime],
        );

        // goal type: Eq Int (Int.abs (ofNat n)) (Int.neg (ofNat n))
        let goal = c.eq_int(c.abs(of_nat_n.clone()), c.neg(of_nat_n.clone()));
        // @False.elim.{0} goal false_proof
        let elim = Expr::apps(c.false_elim.clone(), [goal, false_proof]);

        let lam = ob.mk_lam(hn_id, BinderInfo::Default, hn_type, elim);
        let lam = ob.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), lam);
        ob.finish_child(lam)
    };

    // ----- negSucc case -----
    // fun (n : Nat) (hn : Int.lt (negSucc n) 0) => @Eq.refl.{1} Int (ofNat (succ n))
    //   goal `Eq Int (abs (negSucc n)) (neg (negSucc n))` ≡ refl, both ≡ ofNat (succ n).
    let neg_succ_case = {
        let mut nb = EnvDeclBuilder::child_of(&b);
        let (n_id, n) = nb.fresh_local(c.nat_type.clone());
        let neg_succ_n = c.neg_succ(n.clone());
        let hn_type = c.lt(neg_succ_n.clone(), c.int_zero());
        let (hn_id, _hn) = nb.fresh_local(hn_type.clone());
        let of_nat_succ_n = c.of_nat(Expr::app(c.nat_succ.clone(), n.clone()));
        let body = c.eq_refl_int(of_nat_succ_n);
        let lam = nb.mk_lam(hn_id, BinderInfo::Default, hn_type, body);
        let lam = nb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), lam);
        nb.finish_child(lam)
    };

    // @Int.rec.{0} rec_motive of_nat_case neg_succ_case a : motive a
    //   ≡ (Int.lt a 0 → Eq Int (Int.abs a) (Int.neg a)); apply to h.
    let rec_app = Expr::apps(
        c.int_rec_type.clone(),
        [rec_motive, of_nat_case, neg_succ_case, a.clone()],
    );
    let applied = Expr::app(rec_app, h.clone());

    let val = b.mk_lam(h_id, BinderInfo::Default, h_type, applied);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register the conditional absolute-value identities `Int.abs_of_nonneg`
    /// and `Int.abs_of_neg` as kernel-checked `Declaration::Theorem`s in a
    /// standalone environment.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid `Environment`.
    /// ENSURES: On success, `Int.abs_of_nonneg` and `Int.abs_of_neg` are both
    ///          `Declaration::Theorem`s with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if a target is already registered with any
    ///          declaration kind, that target is left untouched.
    pub(crate) fn register_int_abs_cond(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        // Dependencies: Int.abs/natAbs, Int.le/lt/NonNeg, Int.neg/add/sub,
        // Eq primitives, and True/False logical primitives.
        self.init_int_sign_abs()?;
        self.init_int_ord()?;
        self.init_int_arith()?;
        self.init_eq()?;
        self.init_true_false()?;
        // Constructive helper theorems used by the proof terms.
        self.register_int_add_zero_proof()?;
        self.register_int_sub_nat_nat_zero_succ_proof()?;

        let c = IntAbsCondConsts::new();

        // ----- Int.abs_of_nonneg -----
        let name_nonneg = Name::from_string("Int.abs_of_nonneg");
        if self.get_const(&name_nonneg).is_none() {
            let type_ = build_of_nonneg_type(&c);
            let value = build_of_nonneg_value(&c);
            // SOUNDNESS: Real kernel-checked proof term. The hypothesis
            // `Int.le 0 a ≡ NonNeg (Int.add a 0)` is transported across the
            // constructive `Int.add_zero a` (via `@Eq.subst.{1}`) to `NonNeg a`,
            // then a single-minor `@Int.NonNeg.rec.{0}` rebuilds the index `n`
            // and closes the goal `Eq Int (Int.abs (ofNat n)) (ofNat n)` with
            // `@Eq.refl.{1}` because `Int.abs (ofNat n) ≡ ofNat n`. No `sorry`,
            // no self-reference, no domain-axiom dependency. Replaces the prior
            // `Declaration::Axiom` in `algebra_abs_int.rs::init_int_abs_props`.
            self.add_decl(Declaration::Theorem {
                name: name_nonneg,
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // ----- Int.abs_of_neg -----
        let name_neg = Name::from_string("Int.abs_of_neg");
        if self.get_const(&name_neg).is_none() {
            let type_ = build_of_neg_type(&c);
            let value = build_of_neg_value(&c);
            // SOUNDNESS: Real kernel-checked proof term. `@Int.rec.{0}` with a
            // hypothesis-threading motive splits on `a`: the `ofNat n` branch is
            // vacuous (the threaded `Int.lt (ofNat n) 0 ≡ NonNeg (subNatNat 0
            // (succ n))` transports across the constructive
            // `Int.subNatNat_zero_succ n` to `NonNeg (negSucc n)`, discriminated
            // to `False` by the `True`/`False` `@Int.rec.{1}` predicate and
            // discharged with `@False.elim.{0}`); the `negSucc n` branch closes
            // the goal with `@Eq.refl.{1}` because both `Int.abs (negSucc n)` and
            // `Int.neg (negSucc n)` reduce to `Int.ofNat (Nat.succ n)`. No
            // `sorry`, no self-reference, no domain-axiom dependency. Replaces
            // the prior `Declaration::Axiom` in
            // `algebra_abs_int.rs::init_int_abs_props`.
            self.add_decl(Declaration::Theorem {
                name: name_neg,
                level_params: vec![],
                type_,
                value,
            })?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::axiom_audit::ProofQuality;
    use crate::env::types::ConstantKind;
    use crate::tc::TypeChecker;

    fn registered_env() -> Environment {
        let mut env = Environment::new();
        env.register_int_abs_cond()
            .expect("register_int_abs_cond should succeed");
        env
    }

    fn assert_constructive_theorem(env: &Environment, name: &str) {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{name} must be a kernel-checked Theorem, got {:?}",
            info.kind
        );
        assert!(
            info.value.is_some(),
            "{name} Theorem must retain its proof value"
        );

        // Kernel re-checks the proof term against its canonical type.
        let tc = TypeChecker::with_mode(env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string(name), vec![]))
            .unwrap_or_else(|err| panic!("{name} should kernel-type-check, got {err:?}"));

        // Empty domain-axiom closure.
        let q = env
            .proof_quality(&Name::from_string(name))
            .expect("proof_quality should be reported");
        assert!(
            matches!(q, ProofQuality::Constructive),
            "{name} must be Constructive (no domain axiom in closure), got {q:?}"
        );
    }

    #[test]
    fn test_int_abs_of_nonneg_is_constructive_theorem() {
        let env = registered_env();
        assert_constructive_theorem(&env, "Int.abs_of_nonneg");
    }

    #[test]
    fn test_int_abs_of_neg_is_constructive_theorem() {
        let env = registered_env();
        assert_constructive_theorem(&env, "Int.abs_of_neg");
    }

    #[test]
    fn test_int_abs_cond_idempotent() {
        let mut env = Environment::new();
        env.register_int_abs_cond().expect("first registration");
        env.register_int_abs_cond()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.abs_of_nonneg"))
            .expect("Int.abs_of_nonneg should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
    }
}
