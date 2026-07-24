// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.le_antisymm : ∀ a b : Int, Int.le a b → Int.le b a → Eq Int a b`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `order_int.rs::init_int_ord_lemmas` with a `Declaration::Theorem` whose body
//! is a genuine kernel-checked proof term.
//!
//! # Definitions in play
//!
//! ```text
//! Int.le a b := Int.NonNeg (Int.sub b a)    -- reducible Definition
//! Int.sub a b := Int.add a (Int.neg b)      -- reducible Definition
//! Int.neg (Int.ofNat 0)        = Int.ofNat 0          -- iota + delta
//! Int.neg (Int.ofNat (succ k)) = Int.negSucc k        -- iota + delta
//! ```
//!
//! So the hypotheses delta-reduce to `h1 : NonNeg (Int.sub b a)` and
//! `h2 : NonNeg (Int.sub a b)`, and the goal is `Eq Int a b`.
//!
//! # Proof sketch
//!
//! The heart of the argument is the closed helper term
//!
//! ```text
//! core : ∀ x : Int, Int.NonNeg x → Int.NonNeg (Int.neg x) → Eq Int x (Int.ofNat 0)
//! ```
//!
//! built by `@Int.NonNeg.rec.{0}` on the first witness with the
//! implication-valued motive `C i := NonNeg (neg i) → Eq Int i (ofNat 0)`. The
//! single `ofNat n` minor inducts on `n` via `@Nat.rec.{0}` with motive
//! `Q t := NonNeg (neg (ofNat t)) → Eq Int (ofNat t) (ofNat 0)`:
//!
//! - **base (`t = 0`)**: `neg (ofNat 0)` reduces to `ofNat 0`; the goal
//!   `Eq Int (ofNat 0) (ofNat 0)` is closed by `@Eq.refl.{1} Int (ofNat 0)`.
//! - **step (`t = succ k`)**: `neg (ofNat (succ k))` reduces to `negSucc k`, so
//!   the supplied `NonNeg (neg (ofNat (succ k)))` is definitionally
//!   `NonNeg (negSucc k)`. Recursing on it with the discriminator predicate
//!   `disc i := @Int.rec.{1} (fun _ => Prop) (fun _ => True) (fun _ => False) i`
//!   (`True` on `ofNat`, `False` on `negSucc`) via `@Int.NonNeg.rec.{0}` yields
//!   `disc (negSucc k) ≡ False`, and `@False.elim.{0}` discharges the
//!   (impossible) goal `Eq Int (ofNat (succ k)) (ofNat 0)`.
//!
//! With `core` in hand:
//!
//! 1. `neg_sub : Eq Int (Int.neg (Int.sub b a)) (Int.add a (Int.neg b))`, the
//!    identity `-(b - a) = a - b`, assembled from the constructive
//!    `Int.neg_add`, `Int.neg_neg`, `Int.add_comm` via `Eq.trans` / `congrArg`.
//! 2. Transport `h2 : NonNeg (Int.sub a b)` (≡ `NonNeg (add a (neg b))`) along
//!    `Eq.symm neg_sub` with `@Eq.subst.{1}` (motive `fun x => NonNeg x`) to
//!    obtain `h2' : NonNeg (Int.neg (Int.sub b a))`.
//! 3. `hzero := core (Int.sub b a) h1 h2' : Eq Int (Int.sub b a) (Int.ofNat 0)`.
//! 4. Conclude `Eq Int a b` by `Int.add_right_cancel a (neg a) b` applied to
//!    `Eq.trans (Int.add_neg_self a) (Eq.symm hzero)`, since
//!    `add a (neg a) = 0 = sub b a = add b (neg a)`.
//!
//! # Axiom closure
//!
//! The proof term mentions only the auto-generated recursors `Int.NonNeg.rec`,
//! `Int.rec`, `Nat.rec`; the logical primitives `True`/`True.intro`/`False`/
//! `False.elim`; the foundational `Eq` family (`Eq.refl`, `Eq.symm`, `Eq.trans`,
//! `Eq.subst`, `congrArg`); and the constructive `Declaration::Theorem`s
//! `Int.neg_add`, `Int.neg_neg`, `Int.add_comm`, `Int.add_neg_self`,
//! `Int.add_right_cancel`. None are `Declaration::Axiom`, so
//! `env.axiom_deps("Int.le_antisymm")` is empty and
//! `env.proof_quality("Int.le_antisymm") == ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntLeAntisymmConsts {
    int_type: Expr,
    nat_type: Expr,
    int_le: Expr,
    int_sub: Expr,
    int_add: Expr,
    int_neg: Expr,
    int_of_nat: Expr,
    int_neg_succ: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_rec: Expr,
    nonneg: Expr,
    nonneg_rec: Expr,
    int_rec_prop: Expr,
    eq_const: Expr,
    eq_refl: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    eq_subst: Expr,
    congr_arg: Expr,
    neg_add: Expr,
    neg_neg: Expr,
    add_comm: Expr,
    add_neg_self: Expr,
    add_right_cancel: Expr,
    true_const: Expr,
    true_intro: Expr,
    false_const: Expr,
    false_elim: Expr,
}

impl IntLeAntisymmConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            int_le: Expr::const_(Name::from_string("Int.le"), vec![]),
            int_sub: Expr::const_(Name::from_string("Int.sub"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_neg: Expr::const_(Name::from_string("Int.neg"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            // Nat.rec.{0} — Prop-valued motive (`Q t : Prop`).
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            nonneg: Expr::const_(Name::from_string("Int.NonNeg"), vec![]),
            // NonNeg.rec into Prop — Sort 0.
            nonneg_rec: Expr::const_(Name::from_string("Int.NonNeg.rec"), vec![]),
            // Int.rec producing a `Prop : Sort 1` value — Sort 1.
            int_rec_prop: Expr::const_(Name::from_string("Int.rec"), vec![type1.clone()]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![type1.clone()]),
            // congrArg.{1,1} : {α β} {x y : α} (f : α → β) → Eq x y → Eq (f x) (f y)
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            neg_add: Expr::const_(Name::from_string("Int.neg_add"), vec![]),
            neg_neg: Expr::const_(Name::from_string("Int.neg_neg"), vec![]),
            add_comm: Expr::const_(Name::from_string("Int.add_comm"), vec![]),
            add_neg_self: Expr::const_(Name::from_string("Int.add_neg_self"), vec![]),
            add_right_cancel: Expr::const_(Name::from_string("Int.add_right_cancel"), vec![]),
            true_const: Expr::const_(Name::from_string("True"), vec![]),
            true_intro: Expr::const_(Name::from_string("True.intro"), vec![]),
            false_const: Expr::const_(Name::from_string("False"), vec![]),
            false_elim: Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
        }
    }

    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.int_le.clone(), [a, b])
    }

    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.int_sub.clone(), [a, b])
    }

    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.int_add.clone(), [a, b])
    }

    fn neg(&self, a: Expr) -> Expr {
        Expr::app(self.int_neg.clone(), a)
    }

    fn nonneg_of(&self, x: Expr) -> Expr {
        Expr::app(self.nonneg.clone(), x)
    }

    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }

    fn zero_int(&self) -> Expr {
        self.of_nat(self.nat_zero.clone())
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }

    /// `@Eq.refl.{1} Int x : Eq Int x x`.
    fn refl_int(&self, x: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.int_type.clone(), x])
    }

    /// `@Eq.symm.{1} Int a b h : Eq Int b a` from `h : Eq Int a b`.
    fn symm_int(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.int_type.clone(), a, b, h])
    }

    /// `@Eq.trans.{1} Int a b c h1 h2 : Eq Int a c`.
    fn trans_int(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.int_type.clone(), a, b, c, h1, h2],
        )
    }

    /// `@congrArg.{1,1} Int Int x y f h : Eq Int (f x) (f y)` from
    /// `h : Eq Int x y` and `f : Int → Int`.
    fn congr_int_int(&self, x: Expr, y: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.int_type.clone(), self.int_type.clone(), x, y, f, h],
        )
    }

    /// `disc = @Int.rec.{1} (fun _ : Int => Prop) (fun _ : Nat => True)
    ///                      (fun _ : Nat => False)`.
    ///
    /// `disc (Int.ofNat n)` reduces to `True`, `disc (Int.negSucc n)` to
    /// `False`. Built as a closed (no free fvar) term.
    fn discriminator(&self, parent: &EnvDeclBuilder) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let prop_motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (i_id, _i) = mb.fresh_local(self.int_type.clone());
            let lam = mb.mk_lam(
                i_id,
                BinderInfo::Default,
                self.int_type.clone(),
                Expr::prop(),
            );
            mb.finish_child(lam)
        };
        let of_nat_minor = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (n_id, _n) = mb.fresh_local(self.nat_type.clone());
            let lam = mb.mk_lam(
                n_id,
                BinderInfo::Default,
                self.nat_type.clone(),
                self.true_const.clone(),
            );
            mb.finish_child(lam)
        };
        let neg_succ_minor = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (n_id, _n) = mb.fresh_local(self.nat_type.clone());
            let lam = mb.mk_lam(
                n_id,
                BinderInfo::Default,
                self.nat_type.clone(),
                self.false_const.clone(),
            );
            mb.finish_child(lam)
        };
        let (i_id, i) = b.fresh_local(self.int_type.clone());
        let rec_app = Expr::apps(
            self.int_rec_prop.clone(),
            [prop_motive, of_nat_minor, neg_succ_minor, i.clone()],
        );
        let lam = b.mk_lam(i_id, BinderInfo::Default, self.int_type.clone(), rec_app);
        b.finish_child(lam)
    }
}

/// Build `∀ a b : Int, Int.le a b → Int.le b a → Eq Int a b`.
fn build_type(c: &IntLeAntisymmConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let le_ab = c.le(a.clone(), bv.clone());
    let le_ba = c.le(bv.clone(), a.clone());
    let concl = c.eq_int(a.clone(), bv.clone());
    let (h2_id, _h2) = b.fresh_local(le_ba.clone());
    let (h1_id, _h1) = b.fresh_local(le_ab.clone());
    let r = b.mk_pi(h2_id, BinderInfo::Default, le_ba, concl);
    let r = b.mk_pi(h1_id, BinderInfo::Default, le_ab, r);
    let r = b.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), r);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// The closed helper term
/// `core : ∀ x : Int, NonNeg x → NonNeg (neg x) → Eq Int x (ofNat 0)`.
fn build_core(c: &IntLeAntisymmConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = b.fresh_local(c.int_type.clone());
    let nonneg_x = c.nonneg_of(x.clone());
    let (hx_id, hx) = b.fresh_local(nonneg_x.clone());

    // `C i := NonNeg (neg i) → Eq Int i (ofNat 0)`.
    // NonNeg.rec motive: `fun (i : Int) (_ : NonNeg i) => C i`.
    let rec_motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = mb.fresh_local(c.int_type.clone());
        let nn_i = c.nonneg_of(i.clone());
        let (hi_id, _hi) = mb.fresh_local(nn_i.clone());
        let c_i = {
            let mut ib = EnvDeclBuilder::child_of(&mb);
            let nn_neg_i = c.nonneg_of(c.neg(i.clone()));
            let (h_id, _h) = ib.fresh_local(nn_neg_i.clone());
            let body = c.eq_int(i.clone(), c.zero_int());
            let imp = ib.mk_pi(h_id, BinderInfo::Default, nn_neg_i, body);
            ib.finish_child(imp)
        };
        let lam = mb.mk_lam(hi_id, BinderInfo::Default, nn_i, c_i);
        let lam = mb.mk_lam(i_id, BinderInfo::Default, c.int_type.clone(), lam);
        mb.finish_child(lam)
    };

    // NonNeg.rec minor: `fun (n : Nat) => <C (ofNat n)>`, where
    // `C (ofNat n) = NonNeg (neg (ofNat n)) → Eq Int (ofNat n) (ofNat 0)`,
    // proved by `@Nat.rec.{0}` on `n` with motive
    // `Q t := NonNeg (neg (ofNat t)) → Eq Int (ofNat t) (ofNat 0)`.
    let rec_minor = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (n_id, n) = mb.fresh_local(c.nat_type.clone());

        // Q motive: `fun t : Nat => NonNeg (neg (ofNat t)) → Eq Int (ofNat t) (ofNat 0)`.
        let q_motive = {
            let mut qb = EnvDeclBuilder::child_of(&mb);
            let (t_id, t) = qb.fresh_local(c.nat_type.clone());
            let nn_neg = c.nonneg_of(c.neg(c.of_nat(t.clone())));
            let (h_id, _h) = qb.fresh_local(nn_neg.clone());
            let body = c.eq_int(c.of_nat(t.clone()), c.zero_int());
            let imp = qb.mk_pi(h_id, BinderInfo::Default, nn_neg, body);
            let lam = qb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), imp);
            qb.finish_child(lam)
        };

        // base (t = 0): `fun (_ : NonNeg (neg (ofNat 0))) => @Eq.refl.{1} Int (ofNat 0)`.
        // `neg (ofNat 0)` reduces to `ofNat 0`; the goal `Eq (ofNat 0) (ofNat 0)`.
        let q_base = {
            let mut bb = EnvDeclBuilder::child_of(&mb);
            let nn_neg0 = c.nonneg_of(c.neg(c.zero_int()));
            let (h_id, _h) = bb.fresh_local(nn_neg0.clone());
            let refl = c.refl_int(c.zero_int());
            let lam = bb.mk_lam(h_id, BinderInfo::Default, nn_neg0, refl);
            bb.finish_child(lam)
        };

        // step (t = succ k): `fun (k : Nat) (_ih : Q k) =>
        //   fun (hns : NonNeg (neg (ofNat (succ k)))) => <False.elim>`.
        // `neg (ofNat (succ k))` reduces to `negSucc k`, so `hns` is
        // definitionally `NonNeg (negSucc k)`, discharged via the
        // discriminator recursion.
        let q_step = {
            let mut sb = EnvDeclBuilder::child_of(&mb);
            let (k_id, k) = sb.fresh_local(c.nat_type.clone());
            let q_k = {
                // Q k = NonNeg (neg (ofNat k)) → Eq Int (ofNat k) (ofNat 0).
                let mut ib = EnvDeclBuilder::child_of(&sb);
                let nn_neg = c.nonneg_of(c.neg(c.of_nat(k.clone())));
                let (h_id, _h) = ib.fresh_local(nn_neg.clone());
                let body = c.eq_int(c.of_nat(k.clone()), c.zero_int());
                let imp = ib.mk_pi(h_id, BinderInfo::Default, nn_neg, body);
                ib.finish_child(imp)
            };
            let (ih_id, _ih) = sb.fresh_local(q_k.clone());

            let succ_k = c.succ(k.clone());
            let neg_succ_k = Expr::app(c.int_neg_succ.clone(), k.clone());
            let nn_neg_sk = c.nonneg_of(c.neg(c.of_nat(succ_k.clone())));
            let (hns_id, hns) = sb.fresh_local(nn_neg_sk.clone());

            // Discriminator recursion: `@Int.NonNeg.rec.{0} disc_motive disc_minor
            //   (negSucc k) hns : disc (negSucc k) ≡ False`.
            let disc = c.discriminator(&sb);
            let disc_motive = {
                let mut db = EnvDeclBuilder::child_of(&sb);
                let (i_id, i) = db.fresh_local(c.int_type.clone());
                let nn_i = c.nonneg_of(i.clone());
                let (hi_id, _hi) = db.fresh_local(nn_i.clone());
                let body = Expr::app(disc.clone(), i.clone());
                let lam = db.mk_lam(hi_id, BinderInfo::Default, nn_i, body);
                let lam = db.mk_lam(i_id, BinderInfo::Default, c.int_type.clone(), lam);
                db.finish_child(lam)
            };
            // disc_minor: `fun (n : Nat) => True.intro` — goal `disc (ofNat n) ≡ True`.
            let disc_minor = {
                let mut db = EnvDeclBuilder::child_of(&sb);
                let (m_id, _m) = db.fresh_local(c.nat_type.clone());
                let lam = db.mk_lam(
                    m_id,
                    BinderInfo::Default,
                    c.nat_type.clone(),
                    c.true_intro.clone(),
                );
                db.finish_child(lam)
            };
            // `hns : NonNeg (neg (ofNat (succ k)))` ≡ `NonNeg (negSucc k)`, fed as
            // the recursor's major premise at index `negSucc k`.
            let false_proof = Expr::apps(
                c.nonneg_rec.clone(),
                [disc_motive, disc_minor, neg_succ_k, hns.clone()],
            );
            // `@False.elim.{0} (Eq Int (ofNat (succ k)) (ofNat 0)) false_proof`.
            let goal = c.eq_int(c.of_nat(succ_k), c.zero_int());
            let body = Expr::apps(c.false_elim.clone(), [goal, false_proof]);

            let lam_hns = sb.mk_lam(hns_id, BinderInfo::Default, nn_neg_sk, body);
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, q_k, lam_hns);
            let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
            sb.finish_child(lam_k)
        };

        // `@Nat.rec.{0} q_motive q_base q_step n : C (ofNat n)`.
        let nat_rec_app = Expr::apps(c.nat_rec.clone(), [q_motive, q_base, q_step, n.clone()]);
        let lam_n = mb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), nat_rec_app);
        mb.finish_child(lam_n)
    };

    // `@Int.NonNeg.rec.{0} rec_motive rec_minor x hx : C x
    //   = NonNeg (neg x) → Eq Int x (ofNat 0)`.
    let rec_app = Expr::apps(
        c.nonneg_rec.clone(),
        [rec_motive, rec_minor, x.clone(), hx.clone()],
    );

    // λ (x : Int) (hx : NonNeg x) (hnx : NonNeg (neg x)) => rec_app hnx.
    let nn_neg_x = c.nonneg_of(c.neg(x.clone()));
    let (hnx_id, hnx) = b.fresh_local(nn_neg_x.clone());
    let body = Expr::app(rec_app, hnx);
    let lam_hnx = b.mk_lam(hnx_id, BinderInfo::Default, nn_neg_x, body);
    let lam_hx = b.mk_lam(hx_id, BinderInfo::Default, nonneg_x, lam_hnx);
    let lam_x = b.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), lam_hx);
    b.finish_child(lam_x)
}

/// Build the full proof value.
fn build_value(c: &IntLeAntisymmConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let le_ab = c.le(a.clone(), bv.clone());
    let le_ba = c.le(bv.clone(), a.clone());
    // h1 : Int.le a b ≡ NonNeg (sub b a); h2 : Int.le b a ≡ NonNeg (sub a b).
    let (h1_id, h1) = b.fresh_local(le_ab.clone());
    let (h2_id, h2) = b.fresh_local(le_ba.clone());

    let core = build_core(c, &b);

    // neg_sub : Eq Int (neg (sub b a)) (add a (neg b)) — i.e. -(b - a) = a - b.
    //   sub b a ≡ add b (neg a).
    let sub_ba = c.sub(bv.clone(), a.clone()); // add b (neg a)
    let neg_b = c.neg(bv.clone());
    let neg_a = c.neg(a.clone());
    let neg_neg_a = c.neg(neg_a.clone());

    // e1 : neg (add b (neg a)) = add (neg b) (neg (neg a))  — Int.neg_add b (neg a).
    let e1 = Expr::apps(c.neg_add.clone(), [bv.clone(), neg_a.clone()]);
    // e2 : neg (neg a) = a  — Int.neg_neg a.
    let e2 = Expr::app(c.neg_neg.clone(), a.clone());
    // e3 : add (neg b) (neg (neg a)) = add (neg b) a
    //      — congrArg (fun x => add (neg b) x) e2.
    let congr_fn = {
        let mut fb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = fb.fresh_local(c.int_type.clone());
        let body = c.add(neg_b.clone(), x.clone());
        let lam = fb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
        fb.finish_child(lam)
    };
    let e3 = c.congr_int_int(neg_neg_a.clone(), a.clone(), congr_fn, e2);
    // e4 : add (neg b) a = add a (neg b)  — Int.add_comm (neg b) a.
    let e4 = Expr::apps(c.add_comm.clone(), [neg_b.clone(), a.clone()]);

    let add_nb_nna = c.add(neg_b.clone(), neg_neg_a.clone()); // add (neg b) (neg (neg a))
    let add_nb_a = c.add(neg_b.clone(), a.clone()); // add (neg b) a
    let add_a_nb = c.add(a.clone(), neg_b.clone()); // add a (neg b) ≡ sub a b

    // t1 : neg (sub b a) = add (neg b) a   — trans e1 e3.
    let t1 = c.trans_int(c.neg(sub_ba.clone()), add_nb_nna, add_nb_a.clone(), e1, e3);
    // neg_sub : neg (sub b a) = add a (neg b)   — trans t1 e4.
    let neg_sub = c.trans_int(c.neg(sub_ba.clone()), add_nb_a, add_a_nb.clone(), t1, e4);

    // Transport h2 : NonNeg (sub a b) ≡ NonNeg (add a (neg b)) along
    // `symm neg_sub : add a (neg b) = neg (sub b a)` to NonNeg (neg (sub b a)).
    let subst_motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(c.int_type.clone());
        let body = c.nonneg_of(x);
        let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
        mb.finish_child(lam)
    };
    let neg_sub_ba = c.neg(sub_ba.clone());
    // symm neg_sub : add a (neg b) = neg (sub b a).
    let symm_neg_sub = c.symm_int(neg_sub_ba.clone(), add_a_nb.clone(), neg_sub);
    // h2' = @Eq.subst.{1} Int motive (add a (neg b)) (neg (sub b a)) symm_neg_sub h2.
    let h2_prime = Expr::apps(
        c.eq_subst.clone(),
        [
            c.int_type.clone(),
            subst_motive,
            add_a_nb.clone(),
            neg_sub_ba.clone(),
            symm_neg_sub,
            h2.clone(),
        ],
    );

    // hzero : Eq Int (sub b a) (ofNat 0)   — core (sub b a) h1 h2'.
    let hzero = Expr::apps(core, [sub_ba.clone(), h1.clone(), h2_prime]);

    // Conclude a = b via Int.add_right_cancel a (neg a) b applied to
    //   `add a (neg a) = ofNat 0 = sub b a = add b (neg a)`.
    // pa : add a (neg a) = Int.zero (≡ ofNat 0)   — Int.add_neg_self a.
    let pa = Expr::app(c.add_neg_self.clone(), a.clone());
    let add_a_na = c.add(a.clone(), neg_a.clone());
    // pb : add b (neg a) = ofNat 0   — hzero (sub b a ≡ add b (neg a)).
    // eqq : add a (neg a) = add b (neg a)   — trans pa (symm hzero).
    let symm_hzero = c.symm_int(sub_ba.clone(), c.zero_int(), hzero);
    let eqq = c.trans_int(
        add_a_na.clone(),
        c.zero_int(),
        sub_ba.clone(),
        pa,
        symm_hzero,
    );
    // Int.add_right_cancel a (neg a) b eqq : Eq Int a b.
    //   (add_right_cancel A B C : add A B = add C B → A = C; here A=a, B=neg a, C=b.)
    let result = Expr::apps(
        c.add_right_cancel.clone(),
        [a.clone(), neg_a.clone(), bv.clone(), eqq],
    );

    let val = b.mk_lam(h2_id, BinderInfo::Default, le_ba, result);
    let val = b.mk_lam(h1_id, BinderInfo::Default, le_ab, val);
    let val = b.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `Int.le_antisymm` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_ord()` has registered `Int.le`, `Int.NonNeg`,
    ///           `Int.NonNeg.rec`, `Int.sub`, `Int.add`, `Int.neg`, `Int.rec`,
    ///           `Int.ofNat`, `Int.negSucc`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`, `Eq.symm`,
    ///           `Eq.trans`, `Eq.subst`, `congrArg`.
    /// REQUIRES: `self.init_true_false()` has registered `True`, `True.intro`,
    ///           `False`, `False.elim`.
    /// ENSURES: On success, `Int.le_antisymm` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.le_antisymm` is already registered with any
    ///          declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_int_le_antisymm_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.le_antisymm");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_ord()?;
        self.init_eq()?;
        self.init_true_false()?;
        // Constructive arithmetic dependencies.
        self.register_int_neg_add_proof()?;
        self.register_int_neg_neg_proof()?;
        self.register_int_add_comm_proof()?;
        self.register_int_add_neg_self_proof()?;
        self.register_int_add_right_cancel_proof()?;

        let c = IntLeAntisymmConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. The hypotheses
        // `Int.le a b` / `Int.le b a` delta-reduce to `NonNeg (Int.sub b a)` /
        // `NonNeg (Int.sub a b)`. A closed helper
        // `core : ∀ x, NonNeg x → NonNeg (neg x) → x = ofNat 0` (built by
        // `@Int.NonNeg.rec.{0}` with implication motive, an inner `@Nat.rec.{0}`,
        // and the `disc` discriminator for the impossible `negSucc` branch via
        // `@Int.NonNeg.rec.{0}` + `@False.elim.{0}`) is applied to `x := sub b a`,
        // `h1`, and the transported `h2' : NonNeg (neg (sub b a))` (obtained from
        // `h2` by `@Eq.subst.{1}` along the constructive identity
        // `-(b-a) = a-b`, assembled from `Int.neg_add` / `Int.neg_neg` /
        // `Int.add_comm`). This yields `hzero : sub b a = ofNat 0`, and
        // `Int.add_right_cancel a (neg a) b (Eq.trans (Int.add_neg_self a)
        // (Eq.symm hzero))` discharges the goal `Eq Int a b`. No `sorry`, no
        // self-reference, no domain-axiom dependency (all named lemmas are
        // constructive `Declaration::Theorem`s; the recursors and Eq/logical
        // primitives are foundational). Replaces the prior `Declaration::Axiom`
        // in `order_int.rs::init_int_ord_lemmas`.
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
    use crate::env::ConstantKind;

    #[test]
    fn test_int_le_antisymm_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_le_antisymm_proof()
            .expect("first registration");
        env.register_int_le_antisymm_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.le_antisymm"))
            .expect("Int.le_antisymm should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_le_antisymm_type_checks() {
        use crate::tc::TypeChecker;
        let mut env = Environment::new();
        env.register_int_le_antisymm_proof().unwrap();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string("Int.le_antisymm"), vec![]))
            .expect("Int.le_antisymm should type-check");
    }

    #[test]
    fn test_int_le_antisymm_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_le_antisymm_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.le_antisymm"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        // Peel the four outer λ binders (a, b, h1, h2); the head must be
        // Int.add_right_cancel (the cancellation closeout).
        let mut body: Expr = value.clone();
        for _ in 0..4 {
            body = match body.kind() {
                ExprKind::Lam(_, _, inner) => (**inner).clone(),
                k => panic!("expected outer λ, got {:?}", k),
            };
        }
        let mut head: Expr = body;
        while let ExprKind::App(f, _) = head.kind() {
            head = (**f).clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Int.add_right_cancel",
                "Int.le_antisymm proof root must be Int.add_right_cancel"
            ),
            k => panic!("expected Const(Int.add_right_cancel), got {:?}", k),
        }
    }

    #[test]
    fn test_int_le_antisymm_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_le_antisymm_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.le_antisymm"))
            .expect("Int.le_antisymm is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.le_antisymm must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }

    #[test]
    fn test_int_le_antisymm_proof_quality_constructive() {
        use crate::env::ProofQuality;
        let mut env = Environment::new();
        env.register_int_le_antisymm_proof().unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Int.le_antisymm"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.le_antisymm must be Constructive, got {:?}",
            quality
        );
    }
}
