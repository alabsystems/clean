// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Constructive proofs of the `Int.dist` symmetry law and its supporting
//! abs/neg helper lemmas:
//!
//! - `Int.abs_neg : ∀ a : Int, Eq Int (Int.abs (Int.neg a)) (Int.abs a)`
//! - `Int.neg_sub : ∀ a b : Int, Eq Int (Int.neg (Int.sub a b)) (Int.sub b a)`
//! - `Int.dist_comm : ∀ a b : Int, Eq Int (Int.dist a b) (Int.dist b a)`
//!
//! Each is registered as a `Declaration::Theorem`, replacing the prior
//! `Declaration::Axiom` registrations (`Int.abs_neg` in
//! `algebra_abs_int.rs::init_int_abs_props`, `Int.dist_comm` in
//! `algebra_dist.rs::init_int_dist`).
//!
//! # Definitions in play
//!
//! ```text
//! Int.abs i    := Int.ofNat (Int.natAbs i)              -- reducible
//! Int.natAbs (ofNat n)   = n
//! Int.natAbs (negSucc n) = Nat.succ n
//! Int.neg (ofNat 0)        = ofNat 0
//! Int.neg (ofNat (succ k)) = negSucc k
//! Int.neg (negSucc k)      = ofNat (succ k)
//! Int.sub a b  := Int.add a (Int.neg b)                 -- reducible
//! Int.dist a b := Int.abs (Int.sub a b)                 -- reducible
//! ```
//!
//! # Proof strategy
//!
//! `Int.abs_neg` — direct nested case-analysis on `a`. With
//! `Int.abs i ≡ Int.ofNat (Int.natAbs i)`, each constructor leaf has
//! `Int.natAbs (Int.neg a) ≡ Int.natAbs a` by iota + delta, so the goal closes
//! by `@Eq.refl.{1} Int (Int.abs a)`:
//! - `a = ofNat 0`:      `abs (neg (ofNat 0)) = ofNat 0 = abs (ofNat 0)`.
//! - `a = ofNat (succ k)`: `neg → negSucc k`, `natAbs → succ k`; both sides
//!   reduce to `ofNat (succ k)`.
//! - `a = negSucc k`:    `neg → ofNat (succ k)`, `natAbs → succ k`; both sides
//!   reduce to `ofNat (succ k)`.
//!   The outer `ofNat` case splits its `Nat` via `@Nat.rec.{0}` (so that the
//!   stuck `Int.neg (Int.ofNat n)` reduces on each constructor); the `negSucc`
//!   case needs no inner split.
//!
//! `Int.neg_sub` — algebraic chain. `Int.neg (Int.sub a b) ≡ neg (add a (neg b))`
//! and `Int.sub b a ≡ add b (neg a)`, so:
//! ```text
//! neg (add a (neg b))
//!   =[Int.neg_add a (neg b)]            add (neg a) (neg (neg b))
//!   =[congrArg (add (neg a) ·) (neg_neg b)]  add (neg a) b
//!   =[Int.add_comm (neg a) b]           add b (neg a)   ≡ sub b a
//! ```
//! glued with `@Eq.trans.{1}`.
//!
//! `Int.dist_comm` — `Int.dist a b ≡ abs (sub a b)`, `Int.dist b a ≡ abs (sub b a)`:
//! ```text
//! abs (sub a b)
//!   =[symm (Int.abs_neg (sub a b))]    abs (neg (sub a b))
//!   =[congrArg Int.abs (Int.neg_sub a b)]  abs (sub b a)   ≡ dist b a
//! ```
//!
//! # Axiom closure
//!
//! The proof terms mention only kernel machinery / constructors / reducible
//! Definitions (`Int`, `Int.abs`, `Int.natAbs`, `Int.neg`, `Int.add`,
//! `Int.sub`, `Int.dist`, `Int.ofNat`, `Int.negSucc`, `Int.rec`, `Nat`,
//! `Nat.zero`, `Nat.succ`, `Nat.rec`, `Eq`, `Eq.refl`, `Eq.symm`, `Eq.trans`,
//! `congrArg`) and the constructive `Declaration::Theorem`s `Int.neg_add`,
//! `Int.neg_neg`, `Int.add_comm`. None is a `Declaration::Axiom`, so the
//! domain-axiom closure of each registered lemma is empty and
//! `proof_quality == ProofQuality::Constructive`.

#[cfg(test)]
use super::decl_builder::EnvDeclBuilder;
#[cfg(test)]
use super::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::{BinderInfo, Expr};
#[cfg(test)]
use crate::level::Level;
#[cfg(test)]
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
#[cfg(test)]
struct IntAbsCondConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_rec: Expr,
    int_abs: Expr,
    int_neg: Expr,
    int_add: Expr,
    int_sub: Expr,
    int_dist: Expr,
    int_of_nat: Expr,
    int_neg_succ: Expr,
    int_rec: Expr,
    eq_const: Expr,
    eq_refl: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
}

#[cfg(test)]
impl IntAbsCondConsts {
    #[cfg(test)]
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            // Prop-/Int-valued motives both use the Sort-0 head form here.
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            int_abs: Expr::const_(Name::from_string("Int.abs"), vec![]),
            int_neg: Expr::const_(Name::from_string("Int.neg"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_sub: Expr::const_(Name::from_string("Int.sub"), vec![]),
            int_dist: Expr::const_(Name::from_string("Int.dist"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            int_rec: Expr::const_(Name::from_string("Int.rec"), vec![Level::zero()]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            // congrArg.{1,1} : {α β : Type} {x y : α} (f : α → β) → Eq x y → Eq (f x) (f y)
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
        }
    }

    #[cfg(test)]
    fn abs(&self, x: Expr) -> Expr {
        Expr::app(self.int_abs.clone(), x)
    }

    #[cfg(test)]
    fn neg(&self, x: Expr) -> Expr {
        Expr::app(self.int_neg.clone(), x)
    }

    #[cfg(test)]
    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), x), y)
    }

    #[cfg(test)]
    fn sub(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_sub.clone(), x), y)
    }

    #[cfg(test)]
    fn dist(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_dist.clone(), x), y)
    }

    #[cfg(test)]
    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }

    #[cfg(test)]
    fn neg_succ(&self, n: Expr) -> Expr {
        Expr::app(self.int_neg_succ.clone(), n)
    }

    #[cfg(test)]
    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }

    #[cfg(test)]
    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }

    #[cfg(test)]
    fn refl_int(&self, t: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.int_type.clone(), t])
    }

    /// `@Eq.symm.{1} Int a b h : Eq Int b a` from `h : Eq Int a b`.
    #[cfg(test)]
    fn symm_int(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.int_type.clone(), a, b, h])
    }

    /// `@Eq.trans.{1} Int a b c h1 h2 : Eq Int a c`.
    #[cfg(test)]
    fn trans_int(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.int_type.clone(), a, b, c, h1, h2],
        )
    }

    /// `@congrArg.{1,1} Int Int x y f h : Eq Int (f x) (f y)` from
    /// `h : Eq Int x y` and `f : Int → Int`.
    #[cfg(test)]
    fn congr_int_int(&self, x: Expr, y: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.int_type.clone(), self.int_type.clone(), x, y, f, h],
        )
    }
}

// ---------------------------------------------------------------------------
// Int.abs_neg
// ---------------------------------------------------------------------------

/// Build `∀ a : Int, Eq Int (Int.abs (Int.neg a)) (Int.abs a)`.
#[cfg(test)]
fn build_abs_neg_type(c: &IntAbsCondConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let concl = c.eq_int(c.abs(c.neg(a.clone())), c.abs(a));
    let ty = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), concl);
    b.finish(ty)
}

/// Body:
/// ```text
/// λ (a : Int) => @Int.rec.{0} outer_motive ofNat_case negSucc_case a
/// ```
/// with `outer_motive := λ (x : Int) => Eq Int (abs (neg x)) (abs x)`,
/// `ofNat_case := λ (n : Nat) => @Nat.rec.{0} inner_motive
///       (@Eq.refl Int (abs (ofNat 0)))
///       (λ (m : Nat) (_ih) => @Eq.refl Int (abs (ofNat (succ m)))) n`,
/// `negSucc_case := λ (n : Nat) => @Eq.refl Int (abs (negSucc n))`.
#[cfg(test)]
fn build_abs_neg_value(c: &IntAbsCondConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (a_id, a) = vb.fresh_local(c.int_type.clone());

    // outer motive: λ (x : Int) => Eq Int (abs (neg x)) (abs x)
    let outer_motive = {
        let mut mb = EnvDeclBuilder::child_of(&vb);
        let (x_id, x) = mb.fresh_local(c.int_type.clone());
        let body = c.eq_int(c.abs(c.neg(x.clone())), c.abs(x));
        let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
        mb.finish_child(lam)
    };

    // ofNat case: λ (n : Nat) => Nat.rec inner_motive zero succ n
    let of_nat_case = {
        let mut ob = EnvDeclBuilder::child_of(&vb);
        let (n_id, n) = ob.fresh_local(c.nat_type.clone());

        // inner motive: λ (k : Nat) => Eq Int (abs (neg (ofNat k))) (abs (ofNat k))
        let inner_motive = {
            let mut mb = EnvDeclBuilder::child_of(&ob);
            let (k_id, k) = mb.fresh_local(c.nat_type.clone());
            let body = c.eq_int(c.abs(c.neg(c.of_nat(k.clone()))), c.abs(c.of_nat(k)));
            let lam = mb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), body);
            mb.finish_child(lam)
        };

        // zero case: @Eq.refl Int (abs (ofNat 0))
        let zero_case = c.refl_int(c.abs(c.of_nat(c.nat_zero.clone())));

        // succ case: λ (m : Nat) (_ih) => @Eq.refl Int (abs (ofNat (succ m)))
        let succ_case = {
            let mut sb = EnvDeclBuilder::child_of(&ob);
            let (m_id, m) = sb.fresh_local(c.nat_type.clone());
            let ih_type = c.eq_int(
                c.abs(c.neg(c.of_nat(m.clone()))),
                c.abs(c.of_nat(m.clone())),
            );
            let (ih_id, _ih) = sb.fresh_local(ih_type.clone());
            let refl = c.refl_int(c.abs(c.of_nat(c.succ(m.clone()))));
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, refl);
            let lam_m = sb.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
            sb.finish_child(lam_m)
        };

        let rec_app = Expr::apps(c.nat_rec.clone(), [inner_motive, zero_case, succ_case, n]);
        let lam = ob.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
        ob.finish_child(lam)
    };

    // negSucc case: λ (n : Nat) => @Eq.refl Int (abs (negSucc n))
    let neg_succ_case = {
        let mut nb = EnvDeclBuilder::child_of(&vb);
        let (n_id, n) = nb.fresh_local(c.nat_type.clone());
        let refl = c.refl_int(c.abs(c.neg_succ(n)));
        let lam = nb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), refl);
        nb.finish_child(lam)
    };

    let rec_app = Expr::apps(
        c.int_rec.clone(),
        [outer_motive, of_nat_case, neg_succ_case, a],
    );
    let val = vb.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), rec_app);
    vb.finish(val)
}

// ---------------------------------------------------------------------------
// Int.neg_sub
// ---------------------------------------------------------------------------

/// Build `∀ a b : Int, Eq Int (Int.neg (Int.sub a b)) (Int.sub b a)`.
#[cfg(test)]
fn build_neg_sub_type(c: &IntAbsCondConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let concl = c.eq_int(
        c.neg(c.sub(a.clone(), bv.clone())),
        c.sub(bv.clone(), a.clone()),
    );
    let r = b.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), concl);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// Body:
/// ```text
/// λ (a b : Int) =>
///   -- neg (sub a b) ≡ neg (add a (neg b))
///   @Eq.trans.{1} Int
///     (neg (add a (neg b)))           -- ≡ neg (sub a b)
///     (add (neg a) b)
///     (add b (neg a))                 -- ≡ sub b a
///     (@Eq.trans.{1} Int
///        (neg (add a (neg b)))
///        (add (neg a) (neg (neg b)))
///        (add (neg a) b)
///        (Int.neg_add a (neg b))
///        (congrArg (fun y => add (neg a) y) (Int.neg_neg b)))
///     (Int.add_comm (neg a) b)
/// ```
#[cfg(test)]
fn build_neg_sub_value(c: &IntAbsCondConsts) -> Expr {
    let int_neg_add = Expr::const_(Name::from_string("Int.neg_add"), vec![]);
    let int_neg_neg = Expr::const_(Name::from_string("Int.neg_neg"), vec![]);
    let int_add_comm = Expr::const_(Name::from_string("Int.add_comm"), vec![]);

    let mut vb = EnvDeclBuilder::new();
    let (a_id, a) = vb.fresh_local(c.int_type.clone());
    let (b_id, bv) = vb.fresh_local(c.int_type.clone());

    let neg_a = c.neg(a.clone());
    let neg_b = c.neg(bv.clone());
    let neg_neg_b = c.neg(neg_b.clone());

    // key intermediate terms
    let t0 = c.neg(c.add(a.clone(), neg_b.clone())); // ≡ neg (sub a b)
    let t1 = c.add(neg_a.clone(), neg_neg_b.clone());
    let t2 = c.add(neg_a.clone(), bv.clone());
    let t3 = c.add(bv.clone(), neg_a.clone()); // ≡ sub b a

    // h_neg_add : Eq Int (neg (add a (neg b))) (add (neg a) (neg (neg b)))
    let h_neg_add = Expr::apps(int_neg_add, [a.clone(), neg_b.clone()]);

    // h_neg_neg : Eq Int (neg (neg b)) b
    let h_neg_neg = Expr::app(int_neg_neg, bv.clone());

    // f := fun y : Int => add (neg a) y
    let f = {
        let mut fb = EnvDeclBuilder::child_of(&vb);
        let (y_id, y) = fb.fresh_local(c.int_type.clone());
        let body = c.add(neg_a.clone(), y);
        let lam = fb.mk_lam(y_id, BinderInfo::Default, c.int_type.clone(), body);
        fb.finish_child(lam)
    };

    // h_cong : Eq Int (add (neg a) (neg (neg b))) (add (neg a) b)
    let h_cong = c.congr_int_int(neg_neg_b.clone(), bv.clone(), f, h_neg_neg);

    // h_add_comm : Eq Int (add (neg a) b) (add b (neg a))
    let h_add_comm = Expr::apps(int_add_comm, [neg_a.clone(), bv.clone()]);

    // inner : Eq Int t0 t2  (trans h_neg_add h_cong)
    let inner = c.trans_int(t0.clone(), t1.clone(), t2.clone(), h_neg_add, h_cong);

    // proof : Eq Int t0 t3  (trans inner h_add_comm)
    let proof = c.trans_int(t0, t2, t3, inner, h_add_comm);

    let val = vb.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), proof);
    let val = vb.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    vb.finish(val)
}

// ---------------------------------------------------------------------------
// Int.dist_comm
// ---------------------------------------------------------------------------

/// Build `∀ a b : Int, Eq Int (Int.dist a b) (Int.dist b a)`.
#[cfg(test)]
fn build_dist_comm_type(c: &IntAbsCondConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let concl = c.eq_int(c.dist(a.clone(), bv.clone()), c.dist(bv.clone(), a.clone()));
    let r = b.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), concl);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// Body:
/// ```text
/// λ (a b : Int) =>
///   -- dist a b ≡ abs (sub a b) ; dist b a ≡ abs (sub b a)
///   @Eq.trans.{1} Int
///     (abs (sub a b))
///     (abs (neg (sub a b)))
///     (abs (sub b a))
///     (@Eq.symm.{1} Int (abs (neg (sub a b))) (abs (sub a b))
///        (Int.abs_neg (sub a b)))
///     (congrArg Int.abs (Int.neg_sub a b))
/// ```
#[cfg(test)]
fn build_dist_comm_value(c: &IntAbsCondConsts) -> Expr {
    let int_abs_neg = Expr::const_(Name::from_string("Int.abs_neg"), vec![]);
    let int_neg_sub = Expr::const_(Name::from_string("Int.neg_sub"), vec![]);

    let mut vb = EnvDeclBuilder::new();
    let (a_id, a) = vb.fresh_local(c.int_type.clone());
    let (b_id, bv) = vb.fresh_local(c.int_type.clone());

    let sub_ab = c.sub(a.clone(), bv.clone());
    let sub_ba = c.sub(bv.clone(), a.clone());
    let neg_sub_ab = c.neg(sub_ab.clone());

    let abs_sub_ab = c.abs(sub_ab.clone()); // ≡ dist a b
    let abs_neg_sub_ab = c.abs(neg_sub_ab.clone());
    let abs_sub_ba = c.abs(sub_ba.clone()); // ≡ dist b a

    // h_abs_neg : Eq Int (abs (neg (sub a b))) (abs (sub a b))
    let h_abs_neg = Expr::app(int_abs_neg, sub_ab.clone());
    // symm : Eq Int (abs (sub a b)) (abs (neg (sub a b)))
    let h_symm = c.symm_int(abs_neg_sub_ab.clone(), abs_sub_ab.clone(), h_abs_neg);

    // h_neg_sub : Eq Int (neg (sub a b)) (sub b a)
    let h_neg_sub = Expr::apps(int_neg_sub, [a.clone(), bv.clone()]);
    // h_cong : Eq Int (abs (neg (sub a b))) (abs (sub b a))
    let h_cong = c.congr_int_int(
        neg_sub_ab.clone(),
        sub_ba.clone(),
        c.int_abs.clone(),
        h_neg_sub,
    );

    // proof : Eq Int (abs (sub a b)) (abs (sub b a))
    let proof = c.trans_int(abs_sub_ab, abs_neg_sub_ab, abs_sub_ba, h_symm, h_cong);

    let val = vb.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), proof);
    let val = vb.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    vb.finish(val)
}

#[cfg(test)]
impl Environment {
    /// Register `Int.dist` as a reducible `Declaration::Definition`
    /// `λ a b => Int.abs (Int.sub a b)`, so that this proof module is
    /// self-contained (does not depend on `init_int_dist`, which would
    /// register the opaque `Int.dist_comm` axiom).
    ///
    /// Idempotent — no-op if `Int.dist` is already present.
    #[cfg(test)]
    fn ensure_int_dist_def(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Int.dist");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = IntAbsCondConsts::new();
        let dist_type = Expr::pi(
            BinderInfo::Default,
            c.int_type.clone(),
            Expr::pi(BinderInfo::Default, c.int_type.clone(), c.int_type.clone()),
        );
        let dist_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.int_type.clone());
            let (b_id, bv) = b.fresh_local(c.int_type.clone());
            let body = c.abs(c.sub(a.clone(), bv.clone()));
            let e = b.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: dist_type,
            value: dist_value,
            is_reducible: true,
        })
    }

    /// Register the constructive helper `Int.abs_neg` as a
    /// `Declaration::Theorem`.
    ///
    /// `∀ a : Int, Eq Int (Int.abs (Int.neg a)) (Int.abs a)`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_sign_abs()` has registered `Int.abs`,
    ///           `Int.natAbs`, `Int.ofNat`, `Int.negSucc`, `Int.neg`,
    ///           `Int.rec`.
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`.
    /// ENSURES: On success, `Int.abs_neg` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`. Idempotent.
    #[cfg(test)]
    pub(crate) fn register_int_abs_neg_local(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.abs_neg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_sign_abs()?;
        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;

        let c = IntAbsCondConsts::new();
        let type_ = build_abs_neg_type(&c);
        let value = build_abs_neg_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. Outer `@Int.rec.{0}`
        // case-analysis on `a`; the `ofNat` branch recurses with
        // `@Nat.rec.{0}` so the otherwise-stuck `Int.neg (Int.ofNat n)`
        // reduces, and every leaf closes by pure `@Eq.refl.{1} Int (Int.abs a)`
        // because `Int.natAbs (Int.neg a) ≡ Int.natAbs a` on each constructor
        // (iota on `Int.rec`/`Nat.rec` + delta on the reducible `Int.abs`,
        // `Int.natAbs`, `Int.neg`). No `sorry`, no domain-axiom dependency.
        // Replaces the prior `Declaration::Axiom` in
        // `algebra_abs_int.rs::init_int_abs_props`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// Register the constructive helper `Int.neg_sub` as a
    /// `Declaration::Theorem`.
    ///
    /// `∀ a b : Int, Eq Int (Int.neg (Int.sub a b)) (Int.sub b a)`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int.neg`, `Int.add`,
    ///           `Int.sub`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.trans`.
    /// REQUIRES: the constructive `Int.neg_add`, `Int.neg_neg`, `Int.add_comm`
    ///           Theorems are registered.
    /// ENSURES: On success, `Int.neg_sub` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`. Idempotent.
    #[cfg(test)]
    pub(crate) fn register_int_neg_sub_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.neg_sub");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_eq()?;
        // Constructive dependencies.
        self.register_int_neg_add_proof()?;
        self.register_int_neg_neg_proof()?;
        self.register_int_add_comm_proof()?;

        let c = IntAbsCondConsts::new();
        let type_ = build_neg_sub_type(&c);
        let value = build_neg_sub_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. `Int.neg (Int.sub a b)`
        // ≡ `neg (add a (neg b))` and `Int.sub b a` ≡ `add b (neg a)`. The
        // chain `neg (add a (neg b)) =[Int.neg_add]= add (neg a) (neg (neg b))
        // =[congrArg (add (neg a) ·) Int.neg_neg]= add (neg a) b
        // =[Int.add_comm]= add b (neg a)` is glued with `@Eq.trans.{1}`. All
        // three Theorems are constructive; no `sorry`, no domain-axiom
        // dependency.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// Register the abs/neg/dist symmetry group as kernel-checked
    /// `Declaration::Theorem`s: `Int.abs_neg`, `Int.neg_sub`, `Int.dist_comm`.
    ///
    /// `Int.dist_comm : ∀ a b : Int, Eq Int (Int.dist a b) (Int.dist b a)`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment.
    /// ENSURES: On success, `Int.abs_neg`, `Int.neg_sub`, and `Int.dist_comm`
    ///          are `Declaration::Theorem`s with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.dist_comm` is already registered with any
    ///          declaration kind, this call returns `Ok(())` without
    ///          modification.
    #[cfg(test)]
    pub(crate) fn register_int_dist_comm(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.dist_comm");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        // Dependencies (standalone env — does NOT call init_int_dist, which
        // would register the opaque Int.dist_comm axiom).
        self.init_int_sign_abs()?;
        self.init_int_arith()?;
        self.init_int_ord()?;
        self.init_nat()?;
        self.init_eq()?;
        self.ensure_int_dist_def()?;

        // Constructive helper Theorems.
        self.register_int_abs_neg_local()?;
        self.register_int_neg_sub_proof()?;

        let c = IntAbsCondConsts::new();
        let type_ = build_dist_comm_type(&c);
        let value = build_dist_comm_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. `Int.dist a b`
        // ≡ `Int.abs (Int.sub a b)` and `Int.dist b a` ≡ `Int.abs (Int.sub b
        // a)` (reducible `Int.dist`). The chain
        // `abs (sub a b) =[symm (Int.abs_neg (sub a b))]= abs (neg (sub a b))
        // =[congrArg Int.abs (Int.neg_sub a b)]= abs (sub b a)` is glued with
        // `@Eq.trans.{1}`. Both `Int.abs_neg` and `Int.neg_sub` are
        // constructive Theorems; no `sorry`, no domain-axiom dependency.
        // Replaces the prior `Declaration::Axiom` in
        // `algebra_dist.rs::init_int_dist`.
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
    use crate::env::types::ConstantKind;
    use crate::tc::TypeChecker;

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
        assert!(info.value.is_some(), "{name} Theorem must retain its value");
        let tc = TypeChecker::with_mode(env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string(name), vec![]))
            .unwrap_or_else(|err| panic!("{name} should kernel-type-check, got {err:?}"));
        let q = env
            .proof_quality(&Name::from_string(name))
            .expect("proof_quality should be reported");
        assert!(
            matches!(q, ProofQuality::Constructive),
            "{name} must be Constructive (empty domain-axiom closure), got {q:?}"
        );
    }

    fn env() -> Environment {
        let mut env = Environment::new();
        env.register_int_dist_comm()
            .expect("register_int_dist_comm should succeed");
        env
    }

    #[test]
    fn test_int_abs_neg_is_constructive_theorem() {
        assert_constructive_theorem(&env(), "Int.abs_neg");
    }

    #[test]
    fn test_int_neg_sub_is_constructive_theorem() {
        assert_constructive_theorem(&env(), "Int.neg_sub");
    }

    #[test]
    fn test_int_dist_comm_is_constructive_theorem() {
        assert_constructive_theorem(&env(), "Int.dist_comm");
    }

    #[test]
    fn test_register_int_dist_comm_idempotent() {
        let mut env = Environment::new();
        env.register_int_dist_comm().expect("first registration");
        env.register_int_dist_comm()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.dist_comm"))
            .expect("Int.dist_comm should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_dist_comm_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_dist_comm().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.dist_comm"))
            .expect("Int.dist_comm is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.dist_comm must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }
}
