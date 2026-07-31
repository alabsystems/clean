// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of the integer *reverse triangle inequality*:
//!
//! ```text
//! Int.abs_sub_abs_le_abs_sub :
//!   ∀ a b : Int, Int.le (Int.sub (Int.abs a) (Int.abs b)) (Int.abs (Int.sub a b))
//! Int.abs_sub_abs_le_dist :
//!   ∀ a b : Int, Int.le (Int.abs (Int.sub (Int.abs a) (Int.abs b))) (Int.dist a b)
//! ```
//!
//! `Int.abs_sub_abs_le_dist` is the hard `||a| - |b|| ≤ |a - b|` bound; it
//! replaces the prior `Declaration::Axiom` registration in
//! `algebra_dist.rs::init_int_dist` (`Int.abs_sub_abs_le_dist`) with a
//! kernel-checked `Declaration::Theorem`.
//!
//! # Definitions in play
//!
//! ```text
//! Int.abs i    := Int.ofNat (Int.natAbs i)              -- reducible
//! Int.natAbs (ofNat n)   = n
//! Int.natAbs (negSucc n) = Nat.succ n
//! Int.neg (negSucc n)    = ofNat (Nat.succ n)
//! Int.le a b   := Int.NonNeg (Int.sub b a)              -- reducible
//! Int.sub a b  := Int.add a (Int.neg b)                 -- reducible
//! Int.dist a b := Int.abs (Int.sub a b)                 -- reducible
//! ```
//!
//! # Proof strategy
//!
//! Two pieces.
//!
//! ## 1. `Int.abs_sub_abs_le_abs_sub` — the forward half `|a| - |b| ≤ |a - b|`.
//!
//! Let `aa = |a|`, `ab = |b|`, `M = |a - b|`.
//!
//! * `Int.abs_add_le (a - b) b
//!     : Int.le (abs (add (sub a b) b)) (add (abs (sub a b)) (abs b))`.
//! * `add (sub a b) b ≡ a` is witnessed by the constructive
//!   `eq_sab : Eq Int (add (sub a b) b) a`, assembled from
//!   `Int.add_neg_cancel_right a (neg b) : ((a + (-b)) + (-(-b))) = a` and
//!   `Int.neg_neg b : (-(-b)) = b`. Transport the bound's LHS along
//!   `congrArg Int.abs eq_sab : abs (add (sub a b) b) = abs a` (motive
//!   `fun x => Int.le x (add M ab)`) to get `H1 : Int.le aa (add M ab)`.
//! * `Int.add_le_add_right aa (add M ab) H1 (neg ab)
//!     : Int.le (add aa (neg ab)) (add (add M ab) (neg ab))`.
//! * `Int.add_neg_cancel_right M ab : (M + ab) + (-ab) = M` transports the RHS
//!   (motive `fun x => Int.le (add aa (neg ab)) x`) to land on
//!   `Int.le (add aa (neg ab)) M ≡ Int.le (sub aa ab) M`. □
//!
//! ## 2. `Int.abs_sub_abs_le_dist` — `||a| - |b|| ≤ |a - b|`.
//!
//! Set `t = sub aa ab`. With `M = |a - b| ≡ Int.dist a b`:
//!
//! * `h_pos : Int.le t M` is exactly `Int.abs_sub_abs_le_abs_sub a b`.
//! * `h_neg : Int.le (neg t) M`. From `Int.abs_sub_abs_le_abs_sub b a` we get
//!   `Int.le (sub ab aa) (abs (sub b a))`; transport the RHS along
//!   `Eq.symm (Int.dist_comm a b) : abs (sub b a) = abs (sub a b)` to
//!   `Int.le (sub ab aa) M`, then transport the LHS along
//!   `Eq.symm (Int.neg_sub aa ab) : sub ab aa = neg (sub aa ab)` (since
//!   `Int.neg_sub aa ab : neg (sub aa ab) = sub ab aa`) to
//!   `Int.le (neg t) M`.
//! * The local lemma `abs_le_of_le_of_neg_le
//!     : ∀ t M, Int.le t M → Int.le (neg t) M → Int.le (abs t) M`
//!   (by `@Int.rec.{0}` on `t`: the `ofNat n` leaf returns `h1`
//!   because `abs (ofNat n) ≡ ofNat n ≡ t`; the `negSucc n` leaf returns `h2`
//!   because `abs (negSucc n) ≡ ofNat (succ n) ≡ neg (negSucc n)`) closes
//!   `Int.le (abs t) M ≡ Int.le (abs (sub aa ab)) (Int.dist a b)`. □
//!
//! # Axiom closure
//!
//! Mentions only kernel machinery / constructors / reducible Definitions and
//! the constructive Theorems `Int.abs_add_le`, `Int.add_le_add_right`,
//! `Int.add_neg_cancel_right`, `Int.neg_neg`, `Int.neg_sub`, `Int.dist_comm`.
//! None is a `Declaration::Axiom`, so each registered theorem has an empty
//! domain-axiom closure (`ProofQuality::Constructive`).

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

/// Cached kernel constants reused across the proof terms.
#[cfg(test)]
struct RevTriConsts {
    int_type: Expr,
    nat_type: Expr,
    int_abs: Expr,
    int_neg: Expr,
    int_add: Expr,
    int_sub: Expr,
    int_le: Expr,
    int_dist: Expr,
    int_rec_0: Expr,
    eq_subst: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
}

#[cfg(test)]
impl RevTriConsts {
    #[cfg(test)]
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            int_abs: Expr::const_(Name::from_string("Int.abs"), vec![]),
            int_neg: Expr::const_(Name::from_string("Int.neg"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_sub: Expr::const_(Name::from_string("Int.sub"), vec![]),
            int_le: Expr::const_(Name::from_string("Int.le"), vec![]),
            int_dist: Expr::const_(Name::from_string("Int.dist"), vec![]),
            // Prop-valued Int.rec motive — Sort 0.
            int_rec_0: Expr::const_(Name::from_string("Int.rec"), vec![Level::zero()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            // congrArg.{1,1}
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
        Expr::apps(self.int_add.clone(), [x, y])
    }
    #[cfg(test)]
    fn sub(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_sub.clone(), [x, y])
    }
    #[cfg(test)]
    fn le(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_le.clone(), [x, y])
    }
    #[cfg(test)]
    fn dist(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_dist.clone(), [x, y])
    }

    /// `@Eq.subst.{1} Int motive from to (h : Eq from to) (p : motive from)
    ///   : motive to`.
    #[cfg(test)]
    fn subst_int(&self, motive: Expr, from: Expr, to: Expr, h: Expr, p: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.int_type.clone(), motive, from, to, h, p],
        )
    }
    /// `@Eq.symm.{1} Int a b h : Eq Int b a`.
    #[cfg(test)]
    fn symm_int(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.int_type.clone(), a, b, h])
    }
    /// `@congrArg.{1,1} Int Int x y f h : Eq Int (f x) (f y)`.
    #[cfg(test)]
    fn congr_int_int(&self, x: Expr, y: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.int_type.clone(), self.int_type.clone(), x, y, f, h],
        )
    }
}

// ---------------------------------------------------------------------------
// Int.abs_sub_abs_le_abs_sub  (forward half:  |a| - |b| ≤ |a - b|)
// ---------------------------------------------------------------------------

/// `∀ a b : Int, Int.le (Int.sub (Int.abs a) (Int.abs b)) (Int.abs (Int.sub a b))`.
#[cfg(test)]
fn build_fwd_type(c: &RevTriConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bv_id, bv) = b.fresh_local(c.int_type.clone());
    let lhs = c.sub(c.abs(a.clone()), c.abs(bv.clone()));
    let rhs = c.abs(c.sub(a.clone(), bv.clone()));
    let concl = c.le(lhs, rhs);
    let r = b.mk_pi(bv_id, BinderInfo::Default, c.int_type.clone(), concl);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// Body — see module docs `## 1`.
#[cfg(test)]
fn build_fwd_value(c: &RevTriConsts) -> Expr {
    let abs_add_le = Expr::const_(Name::from_string("Int.abs_add_le"), vec![]);
    let add_le_add_right = Expr::const_(Name::from_string("Int.add_le_add_right"), vec![]);
    let add_neg_cancel_right = Expr::const_(Name::from_string("Int.add_neg_cancel_right"), vec![]);
    let neg_neg = Expr::const_(Name::from_string("Int.neg_neg"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bv_id, bv) = b.fresh_local(c.int_type.clone());

    let aa = c.abs(a.clone()); // |a|
    let ab = c.abs(bv.clone()); // |b|
    let dab = c.sub(a.clone(), bv.clone()); // a - b
    let big_m = c.abs(dab.clone()); // |a - b|
    let neg_b = c.neg(bv.clone());
    let neg_ab = c.neg(ab.clone());

    // ---- eq_sab : Eq Int (add (sub a b) b) a -----------------------------
    // c1 : Eq Int (add (sub a b) (neg (neg b))) a
    //    = Int.add_neg_cancel_right a (neg b)
    let c1 = Expr::apps(add_neg_cancel_right.clone(), [a.clone(), neg_b.clone()]);
    // f1 := fun (y : Int) => add (sub a b) y
    let f1 = {
        let mut fb = EnvDeclBuilder::child_of(&b);
        let (y_id, y) = fb.fresh_local(c.int_type.clone());
        let body = c.add(dab.clone(), y);
        let lam = fb.mk_lam(y_id, BinderInfo::Default, c.int_type.clone(), body);
        fb.finish_child(lam)
    };
    let neg_neg_b = c.neg(neg_b.clone());
    // hnn : Eq Int (neg (neg b)) b
    let hnn = Expr::app(neg_neg, bv.clone());
    // c2 : Eq Int (add (sub a b) (neg (neg b))) (add (sub a b) b)
    let c2 = c.congr_int_int(neg_neg_b.clone(), bv.clone(), f1, hnn);
    let add_dab_nnb = c.add(dab.clone(), neg_neg_b.clone());
    let add_dab_b = c.add(dab.clone(), bv.clone());
    // symm c2 : Eq Int (add (sub a b) b) (add (sub a b) (neg (neg b)))
    let c2_symm = c.symm_int(add_dab_nnb.clone(), add_dab_b.clone(), c2);
    // eq_sab : Eq Int (add (sub a b) b) a = trans (symm c2) c1
    let eq_trans = Expr::const_(
        Name::from_string("Eq.trans"),
        vec![Level::succ(Level::zero())],
    );
    let eq_sab = Expr::apps(
        eq_trans,
        [
            c.int_type.clone(),
            add_dab_b.clone(),
            add_dab_nnb.clone(),
            a.clone(),
            c2_symm,
            c1,
        ],
    );

    // ---- bound : abs_add_le (a-b) b --------------------------------------
    // bound : Int.le (abs (add (sub a b) b)) (add (abs (sub a b)) (abs b))
    //   ≡ Int.le (abs (add (sub a b) b)) (add M ab)
    let add_m_ab = c.add(big_m.clone(), ab.clone());
    let bound = Expr::apps(abs_add_le, [dab.clone(), bv.clone()]);

    // congr_abs : Eq Int (abs (add (sub a b) b)) (abs a)   [ = abs a ≡ aa ]
    let abs_add_dab_b = c.abs(add_dab_b.clone());
    let congr_abs = c.congr_int_int(add_dab_b.clone(), a.clone(), c.int_abs.clone(), eq_sab);

    // motive_h1 := fun (x : Int) => Int.le x (add M ab)
    let motive_h1 = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(c.int_type.clone());
        let body = c.le(x, add_m_ab.clone());
        let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
        mb.finish_child(lam)
    };
    // h1 : Int.le aa (add M ab)
    let h1 = c.subst_int(
        motive_h1,
        abs_add_dab_b.clone(),
        aa.clone(),
        congr_abs,
        bound,
    );

    // ---- add_le_add_right aa (add M ab) h1 (neg ab) ----------------------
    // step : Int.le (add aa (neg ab)) (add (add M ab) (neg ab))
    let step = Expr::apps(
        add_le_add_right,
        [aa.clone(), add_m_ab.clone(), h1, neg_ab.clone()],
    );

    // cancel : Eq Int (add (add M ab) (neg ab)) M
    //   = Int.add_neg_cancel_right M ab
    let cancel = Expr::apps(add_neg_cancel_right, [big_m.clone(), ab.clone()]);
    let add_m_ab_neg = c.add(add_m_ab.clone(), neg_ab.clone());
    let lhs_fixed = c.add(aa.clone(), neg_ab.clone()); // ≡ sub aa ab

    // motive_h2 := fun (x : Int) => Int.le (add aa (neg ab)) x
    let motive_h2 = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(c.int_type.clone());
        let body = c.le(lhs_fixed.clone(), x);
        let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
        mb.finish_child(lam)
    };
    // proof : Int.le (add aa (neg ab)) M ≡ Int.le (sub aa ab) (abs (sub a b))
    let proof = c.subst_int(motive_h2, add_m_ab_neg, big_m.clone(), cancel, step);

    let val = b.mk_lam(bv_id, BinderInfo::Default, c.int_type.clone(), proof);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    b.finish(val)
}

// ---------------------------------------------------------------------------
// Int.abs_le_of_le_of_neg_le  (local: case split on the sign of t)
// ---------------------------------------------------------------------------

/// `∀ t m : Int, Int.le t m → Int.le (Int.neg t) m → Int.le (Int.abs t) m`.
#[cfg(test)]
fn build_abs_le_type(c: &RevTriConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (t_id, t) = b.fresh_local(c.int_type.clone());
    let (m_id, m) = b.fresh_local(c.int_type.clone());
    let h1_type = c.le(t.clone(), m.clone());
    let (h1_id, _h1) = b.fresh_local(h1_type.clone());
    let h2_type = c.le(c.neg(t.clone()), m.clone());
    let (h2_id, _h2) = b.fresh_local(h2_type.clone());
    let concl = c.le(c.abs(t.clone()), m.clone());
    let r = b.mk_pi(h2_id, BinderInfo::Default, h2_type, concl);
    let r = b.mk_pi(h1_id, BinderInfo::Default, h1_type, r);
    let r = b.mk_pi(m_id, BinderInfo::Default, c.int_type.clone(), r);
    let r = b.mk_pi(t_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// Body:
/// ```text
/// λ (t m : Int) =>
///   @Int.rec.{0}
///     (fun (x : Int) => Int.le x m → Int.le (neg x) m → Int.le (abs x) m)
///     (fun (n : Nat) (h1 : ...) (h2 : ...) => h1)   -- abs (ofNat n) ≡ ofNat n ≡ x
///     (fun (n : Nat) (h1 : ...) (h2 : ...) => h2)   -- abs (negSucc n) ≡ neg (negSucc n)
///     t
/// ```
#[cfg(test)]
fn build_abs_le_value(c: &RevTriConsts) -> Expr {
    let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
    let int_neg_succ = Expr::const_(Name::from_string("Int.negSucc"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (t_id, t) = b.fresh_local(c.int_type.clone());
    let (m_id, m) = b.fresh_local(c.int_type.clone());

    // motive: fun (x : Int) => le x m → le (neg x) m → le (abs x) m
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(c.int_type.clone());
        let h1_ty = c.le(x.clone(), m.clone());
        let (h1_id, _h1) = mb.fresh_local(h1_ty.clone());
        let h2_ty = c.le(c.neg(x.clone()), m.clone());
        let (h2_id, _h2) = mb.fresh_local(h2_ty.clone());
        let concl = c.le(c.abs(x.clone()), m.clone());
        let pi2 = mb.mk_pi(h2_id, BinderInfo::Default, h2_ty, concl);
        let pi1 = mb.mk_pi(h1_id, BinderInfo::Default, h1_ty, pi2);
        let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), pi1);
        mb.finish_child(lam)
    };

    // ofNat case: fun (n : Nat) (h1) (h2) => h1
    //   goal: le (abs (ofNat n)) m ≡ le (ofNat n) m, h1 : le (ofNat n) m.
    let of_nat_case = {
        let mut ob = EnvDeclBuilder::child_of(&b);
        let (n_id, n) = ob.fresh_local(c.nat_type.clone());
        let of_nat_n = Expr::app(int_of_nat.clone(), n.clone());
        let h1_ty = c.le(of_nat_n.clone(), m.clone());
        let (h1_id, h1) = ob.fresh_local(h1_ty.clone());
        let h2_ty = c.le(c.neg(of_nat_n.clone()), m.clone());
        let (h2_id, _h2) = ob.fresh_local(h2_ty.clone());
        let lam = ob.mk_lam(h2_id, BinderInfo::Default, h2_ty, h1);
        let lam = ob.mk_lam(h1_id, BinderInfo::Default, h1_ty, lam);
        let lam = ob.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), lam);
        ob.finish_child(lam)
    };

    // negSucc case: fun (n : Nat) (h1) (h2) => h2
    //   goal: le (abs (negSucc n)) m ≡ le (ofNat (succ n)) m ≡ le (neg (negSucc n)) m,
    //   h2 : le (neg (negSucc n)) m.
    let neg_succ_case = {
        let mut nb = EnvDeclBuilder::child_of(&b);
        let (n_id, n) = nb.fresh_local(c.nat_type.clone());
        let neg_succ_n = Expr::app(int_neg_succ.clone(), n.clone());
        let h1_ty = c.le(neg_succ_n.clone(), m.clone());
        let (h1_id, _h1) = nb.fresh_local(h1_ty.clone());
        let h2_ty = c.le(c.neg(neg_succ_n.clone()), m.clone());
        let (h2_id, h2) = nb.fresh_local(h2_ty.clone());
        let lam = nb.mk_lam(h2_id, BinderInfo::Default, h2_ty, h2);
        let lam = nb.mk_lam(h1_id, BinderInfo::Default, h1_ty, lam);
        let lam = nb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), lam);
        nb.finish_child(lam)
    };

    let rec_app = Expr::apps(
        c.int_rec_0.clone(),
        [motive, of_nat_case, neg_succ_case, t.clone()],
    );
    let val = b.mk_lam(m_id, BinderInfo::Default, c.int_type.clone(), rec_app);
    let val = b.mk_lam(t_id, BinderInfo::Default, c.int_type.clone(), val);
    b.finish(val)
}

// ---------------------------------------------------------------------------
// Int.abs_sub_abs_le_dist
// ---------------------------------------------------------------------------

/// `∀ a b : Int,
///    Int.le (Int.abs (Int.sub (Int.abs a) (Int.abs b))) (Int.dist a b)`.
#[cfg(test)]
fn build_dist_type(c: &RevTriConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bv_id, bv) = b.fresh_local(c.int_type.clone());
    let lhs = c.abs(c.sub(c.abs(a.clone()), c.abs(bv.clone())));
    let rhs = c.dist(a.clone(), bv.clone());
    let concl = c.le(lhs, rhs);
    let r = b.mk_pi(bv_id, BinderInfo::Default, c.int_type.clone(), concl);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// Body — see module docs `## 2`.
#[cfg(test)]
fn build_dist_value(c: &RevTriConsts) -> Expr {
    let fwd = Expr::const_(Name::from_string("Int.abs_sub_abs_le_abs_sub"), vec![]);
    let abs_le = Expr::const_(Name::from_string("Int.abs_le_of_le_of_neg_le"), vec![]);
    let neg_sub = Expr::const_(Name::from_string("Int.neg_sub"), vec![]);
    let dist_comm = Expr::const_(Name::from_string("Int.dist_comm"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bv_id, bv) = b.fresh_local(c.int_type.clone());

    let aa = c.abs(a.clone()); // |a|
    let ab = c.abs(bv.clone()); // |b|
    let t = c.sub(aa.clone(), ab.clone()); // |a| - |b|
    let big_m = c.abs(c.sub(a.clone(), bv.clone())); // |a - b| ≡ dist a b

    // h_pos : Int.le t M  =  Int.abs_sub_abs_le_abs_sub a b
    let h_pos = Expr::apps(fwd.clone(), [a.clone(), bv.clone()]);

    // ---- h_neg : Int.le (neg t) M --------------------------------------
    // base_swap : Int.le (sub ab aa) (abs (sub b a))
    //   = Int.abs_sub_abs_le_abs_sub b a
    let sub_ba = c.sub(ab.clone(), aa.clone()); // |b| - |a|
    let abs_sub_b_a = c.abs(c.sub(bv.clone(), a.clone())); // |b - a|
    let base_swap = Expr::apps(fwd, [bv.clone(), a.clone()]);

    // dc : Eq Int (dist a b) (dist b a) ≡ Eq Int (abs (sub a b)) (abs (sub b a))
    //   = Int.dist_comm a b ; symm : Eq Int (abs (sub b a)) (abs (sub a b))
    let dc = Expr::apps(dist_comm, [a.clone(), bv.clone()]);
    let dc_symm = c.symm_int(big_m.clone(), abs_sub_b_a.clone(), dc);
    // motive_m := fun (x : Int) => Int.le (sub ab aa) x
    let motive_m = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(c.int_type.clone());
        let body = c.le(sub_ba.clone(), x);
        let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
        mb.finish_child(lam)
    };
    // mid : Int.le (sub ab aa) M
    let mid = c.subst_int(
        motive_m,
        abs_sub_b_a.clone(),
        big_m.clone(),
        dc_symm,
        base_swap,
    );

    // ns : Eq Int (neg (sub aa ab)) (sub ab aa)   = Int.neg_sub aa ab
    let neg_t = c.neg(t.clone());
    let ns = Expr::apps(neg_sub, [aa.clone(), ab.clone()]);
    // symm ns : Eq Int (sub ab aa) (neg (sub aa ab))
    let ns_symm = c.symm_int(neg_t.clone(), sub_ba.clone(), ns);
    // motive_t := fun (x : Int) => Int.le x M
    let motive_t = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(c.int_type.clone());
        let body = c.le(x, big_m.clone());
        let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
        mb.finish_child(lam)
    };
    // h_neg : Int.le (neg t) M
    let h_neg = c.subst_int(motive_t, sub_ba.clone(), neg_t.clone(), ns_symm, mid);

    // ---- abs_le_of_le_of_neg_le t M h_pos h_neg ------------------------
    // : Int.le (abs t) M ≡ Int.le (abs (sub aa ab)) (Int.dist a b)
    let body = Expr::apps(abs_le, [t.clone(), big_m.clone(), h_pos, h_neg]);

    let val = b.mk_lam(bv_id, BinderInfo::Default, c.int_type.clone(), body);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    b.finish(val)
}

#[cfg(test)]
impl Environment {
    /// Register the integer reverse triangle inequalities
    /// `Int.abs_sub_abs_le_abs_sub` (the forward half `|a| - |b| ≤ |a - b|`)
    /// and `Int.abs_sub_abs_le_dist` (`||a| - |b|| ≤ Int.dist a b`), plus the
    /// local sign-split lemma `Int.abs_le_of_le_of_neg_le`, as kernel-checked
    /// `Declaration::Theorem`s in a standalone environment.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid `Environment`.
    /// ENSURES: On success, `Int.abs_sub_abs_le_abs_sub` and
    ///          `Int.abs_sub_abs_le_dist` are `Declaration::Theorem`s with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent — each target is guarded by `get_const`.
    #[cfg(test)]
    pub(crate) fn register_int_abs_sub_abs_le_dist(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        // Dependencies (constants referenced directly by the proof terms).
        self.init_int_sign_abs()?; // Int.abs, Int.ofNat, Int.negSucc, Int.neg, Int.rec
        self.init_int_arith()?; // Int.add, Int.sub, Int.neg
        self.init_int_ord()?; // Int.le, Int.NonNeg
        self.init_nat()?; // Nat
        self.init_eq()?; // Eq, Eq.refl, Eq.symm, Eq.subst, Eq.trans, congrArg

        // Constructive helper Theorems (each registers `Int.dist` reducibly).
        self.register_int_abs_add_le()?; // Int.abs_add_le (+ Int.dist, dist_triangle)
        self.register_int_add_le_add_right_proof()?; // Int.add_le_add_right
        self.register_int_add_neg_cancel_right_proof()?; // Int.add_neg_cancel_right
        self.register_int_neg_neg_proof()?; // Int.neg_neg
        self.register_int_neg_sub_proof()?; // Int.neg_sub
        self.register_int_dist_comm()?; // Int.dist_comm (+ Int.abs_neg)

        let c = RevTriConsts::new();

        // Int.abs_sub_abs_le_abs_sub
        let name = Name::from_string("Int.abs_sub_abs_le_abs_sub");
        if self.get_const(&name).is_none() {
            let type_ = build_fwd_type(&c);
            let value = build_fwd_value(&c);
            // SOUNDNESS: Real kernel-checked proof term. From
            // `Int.abs_add_le (a-b) b` transport the LHS along
            // `congrArg Int.abs eq_sab` (where `eq_sab : (a-b)+b = a` is built
            // from `Int.add_neg_cancel_right a (neg b)` and `Int.neg_neg b`) to
            // `Int.le |a| (|a-b| + |b|)`; apply `Int.add_le_add_right ... (neg |b|)`
            // and transport the RHS along `Int.add_neg_cancel_right |a-b| |b|` to
            // land on `Int.le (|a| - |b|) |a-b|`. No `sorry`, no domain axiom.
            self.add_decl(Declaration::Theorem {
                name,
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // Int.abs_le_of_le_of_neg_le
        let name = Name::from_string("Int.abs_le_of_le_of_neg_le");
        if self.get_const(&name).is_none() {
            let type_ = build_abs_le_type(&c);
            let value = build_abs_le_value(&c);
            // SOUNDNESS: Real kernel-checked proof term. `@Int.rec.{0}` on `t`:
            // the `ofNat n` leaf returns the first hypothesis (`abs (ofNat n) ≡
            // ofNat n`), the `negSucc n` leaf returns the second (`abs (negSucc n)
            // ≡ ofNat (succ n) ≡ neg (negSucc n)`). No `sorry`, no domain axiom.
            self.add_decl(Declaration::Theorem {
                name,
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // Int.abs_sub_abs_le_dist
        let name = Name::from_string("Int.abs_sub_abs_le_dist");
        if self.get_const(&name).is_none() {
            let type_ = build_dist_type(&c);
            let value = build_dist_value(&c);
            // SOUNDNESS: Real kernel-checked proof term. With `t = |a| - |b|` and
            // `M = |a - b| ≡ Int.dist a b`: `h_pos : Int.le t M` is
            // `Int.abs_sub_abs_le_abs_sub a b`; `h_neg : Int.le (neg t) M` is
            // `Int.abs_sub_abs_le_abs_sub b a` transported along
            // `Int.dist_comm a b` (RHS) and `Int.neg_sub |a| |b|` (LHS). The local
            // `Int.abs_le_of_le_of_neg_le t M h_pos h_neg` then yields
            // `Int.le (abs t) M`. No `sorry`, no domain axiom. Replaces the prior
            // `Declaration::Axiom` in `algebra_dist.rs::init_int_dist`.
            self.add_decl(Declaration::Theorem {
                name,
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
    use crate::env::{ConstantKind, ProofQuality};
    use crate::tc::TypeChecker;

    fn registered_env() -> Environment {
        let mut env = Environment::new();
        env.register_int_abs_sub_abs_le_dist()
            .expect("register_int_abs_sub_abs_le_dist should succeed");
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
        assert!(info.value.is_some(), "{name} Theorem must retain its value");

        // Kernel re-checks the proof term against its canonical type.
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

    #[test]
    fn test_int_abs_sub_abs_le_abs_sub_is_constructive_theorem() {
        assert_constructive_theorem(&registered_env(), "Int.abs_sub_abs_le_abs_sub");
    }

    #[test]
    fn test_int_abs_le_of_le_of_neg_le_is_constructive_theorem() {
        assert_constructive_theorem(&registered_env(), "Int.abs_le_of_le_of_neg_le");
    }

    #[test]
    fn test_int_abs_sub_abs_le_dist_is_constructive_theorem() {
        assert_constructive_theorem(&registered_env(), "Int.abs_sub_abs_le_dist");
    }

    #[test]
    fn test_register_int_abs_sub_abs_le_dist_idempotent() {
        let mut env = Environment::new();
        env.register_int_abs_sub_abs_le_dist()
            .expect("first registration");
        env.register_int_abs_sub_abs_le_dist()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.abs_sub_abs_le_dist"))
            .expect("Int.abs_sub_abs_le_dist should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_abs_sub_abs_le_dist_axiom_deps_empty() {
        let env = registered_env();
        for name in [
            "Int.abs_sub_abs_le_abs_sub",
            "Int.abs_le_of_le_of_neg_le",
            "Int.abs_sub_abs_le_dist",
        ] {
            let deps = env
                .axiom_deps(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} registered, axiom_deps should return Some"));
            let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
            assert!(
                domain_deps.is_empty(),
                "{name} must have empty axiom closure, got {domain_deps:?}"
            );
        }
    }
}
