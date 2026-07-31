// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.left_distrib : ∀ a b c : Int,
//!     Eq Int (Int.mul a (Int.add b c)) (Int.add (Int.mul a b) (Int.mul a c))`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_int_lemmas.rs` with a `Declaration::Theorem` built by a triple
//! nested `@Int.rec.{0}` case analysis (outer on `a`, then `b`, then `c`),
//! producing eight constructor leaves.
//!
//! # Reductions used
//!
//! `Int.add` / `Int.mul` (reducible) on constructors:
//!
//! ```text
//! add (ofNat p)   (ofNat r)   = ofNat (Nat.add p r)
//! add (ofNat p)   (negSucc r) = subNatNat p (succ r)
//! add (negSucc p) (ofNat r)   = subNatNat r (succ p)
//! add (negSucc p) (negSucc r) = negSucc (succ (Nat.add p r))
//! mul (ofNat j)   (ofNat r)   = ofNat    (Nat.mul j r)
//! mul (ofNat j)   (negSucc r) = negOfNat (Nat.mul j (succ r))
//! mul (negSucc j) (ofNat r)   = negOfNat (Nat.mul (succ j) r)
//! mul (negSucc j) (negSucc r) = ofNat    (Nat.mul (succ j) (succ r))
//! ```
//!
//! # Leaf proofs
//!
//! With `s = succ j`. The same-sign leaves lift `Nat.left_distrib` through
//! `Int.ofNat` / `Int.negOfNat`; the mixed-sign leaves cross the normalized
//! `Int.subNatNat` with `Int.ofNat_mul_subNatNat` / `Int.negSucc_mul_subNatNat`
//! then re-express via `Int.subNatNat_eq_add` (and `Int.add_comm` where the
//! summand order differs). `Int.negOfNat_add` folds the all-negative leaves.
//!
//! ```text
//! a=ofNat j:
//!   (ofNat p, ofNat r)     congrArg ofNat (Nat.left_distrib j p r)
//!   (ofNat p, negSucc r)   trans (ofNat_mul_subNatNat j p (s r))
//!                                (subNatNat_eq_add (j*p) (j*(s r)))
//!   (negSucc p, ofNat r)   trans3 (ofNat_mul_subNatNat j r (s p))
//!                                 (subNatNat_eq_add (j*r) (j*(s p)))
//!                                 (Int.add_comm (ofNat (j*r)) (negOfNat (j*(s p))))
//!   (negSucc p, negSucc r) trans (congrArg negOfNat natEq[j])
//!                                (symm (negOfNat_add (j*(s p)) (j*(s r))))
//! a=negSucc j:
//!   (ofNat p, ofNat r)     trans (congrArg negOfNat (Nat.left_distrib s p r))
//!                                (symm (negOfNat_add (s*p) (s*r)))
//!   (ofNat p, negSucc r)   trans3 (negSucc_mul_subNatNat j p (s r))
//!                                 (subNatNat_eq_add (s*(s r)) (s*p))
//!                                 (Int.add_comm (ofNat (s*(s r))) (negOfNat (s*p)))
//!   (negSucc p, ofNat r)   trans (negSucc_mul_subNatNat j r (s p))
//!                                (subNatNat_eq_add (s*(s p)) (s*r))
//!   (negSucc p, negSucc r) congrArg ofNat natEq[s]
//! ```
//!
//! where `natEq[k] : Eq (Nat.mul k (succ (succ (Nat.add p r))))
//!                      (Nat.add (Nat.mul k (succ p)) (Nat.mul k (succ r)))`
//! is `trans (congrArg (Nat.mul k) hp) (Nat.left_distrib k (succ p) (succ r))`
//! with `hp : succ (succ (p+r)) = Nat.add (succ p) (succ r)` assembled from
//! `Nat.succ_add` and `Nat.add_succ`.
//!
//! # Axiom closure
//!
//! Mentions only kernel machinery / constructors / reducible Definitions and
//! the constructive `Declaration::Theorem`s `Int.ofNat_mul_subNatNat`,
//! `Int.negSucc_mul_subNatNat`, `Int.subNatNat_eq_add`, `Int.add_comm`,
//! `Int.negOfNat_add`, `Nat.left_distrib`, `Nat.succ_add`, `Nat.add_succ`
//! (all #3604). None are `Declaration::Axiom`, so
//! `env.axiom_deps("Int.left_distrib")` is empty and the proof quality is
//! `ProofQuality::Constructive`.
//!
//! Tracks #3604. Sibling: `algebra_int_right_distrib_proof.rs`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntLeftDistribConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_succ: Expr,
    nat_add: Expr,
    nat_mul: Expr,
    int_rec: Expr,
    int_add: Expr,
    int_mul: Expr,
    int_of_nat: Expr,
    int_neg_succ: Expr,
    int_neg_of_nat: Expr,
    eq_const: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
    oms: Expr,
    nms: Expr,
    snea: Expr,
    iac: Expr,
    nona: Expr,
    nld: Expr,
    nsa: Expr,
    nas: Expr,
}

impl IntLeftDistribConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            nat_mul: Expr::const_(Name::from_string("Nat.mul"), vec![]),
            int_rec: Expr::const_(Name::from_string("Int.rec"), vec![Level::zero()]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_mul: Expr::const_(Name::from_string("Int.mul"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            int_neg_of_nat: Expr::const_(Name::from_string("Int.negOfNat"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            oms: Expr::const_(Name::from_string("Int.ofNat_mul_subNatNat"), vec![]),
            nms: Expr::const_(Name::from_string("Int.negSucc_mul_subNatNat"), vec![]),
            snea: Expr::const_(Name::from_string("Int.subNatNat_eq_add"), vec![]),
            iac: Expr::const_(Name::from_string("Int.add_comm"), vec![]),
            nona: Expr::const_(Name::from_string("Int.negOfNat_add"), vec![]),
            nld: Expr::const_(Name::from_string("Nat.left_distrib"), vec![]),
            nsa: Expr::const_(Name::from_string("Nat.succ_add"), vec![]),
            nas: Expr::const_(Name::from_string("Nat.add_succ"), vec![]),
        }
    }

    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), x), y)
    }

    fn mul(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_mul.clone(), x), y)
    }

    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }

    fn neg_succ(&self, n: Expr) -> Expr {
        Expr::app(self.int_neg_succ.clone(), n)
    }

    fn neg_of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_neg_of_nat.clone(), n)
    }

    fn nmul(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.nat_mul.clone(), x), y)
    }

    fn nadd(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.nat_add.clone(), x), y)
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }

    fn symm_int(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.int_type.clone(), a, b, h])
    }

    fn trans_int(&self, x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.int_type.clone(), x, y, z, h1, h2],
        )
    }

    /// `congrArg Int Int a1 a2 f h : Eq Int (f a1) (f a2)`.
    #[cfg(test)]
    fn congr_arg_int(&self, a1: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.int_type.clone(), self.int_type.clone(), a1, a2, f, h],
        )
    }

    /// `congrArg Nat Int a1 a2 g h : Eq Int (g a1) (g a2)`.
    fn congr_arg_nat_int(&self, a1: Expr, a2: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.nat_type.clone(), self.int_type.clone(), a1, a2, g, h],
        )
    }

    /// `congrArg Nat Nat a1 a2 g h : Eq Nat (g a1) (g a2)`.
    fn congr_arg_nat_nat(&self, a1: Expr, a2: Expr, g: Expr, h: Expr) -> Expr {
        let type1 = Level::succ(Level::zero());
        let ca = Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]);
        Expr::apps(
            ca,
            [self.nat_type.clone(), self.nat_type.clone(), a1, a2, g, h],
        )
    }

    #[cfg(test)]
    fn eq_nat(&self, lhs: Expr, rhs: Expr) -> Expr {
        let type1 = Level::succ(Level::zero());
        let eqn = Expr::const_(Name::from_string("Eq"), vec![type1]);
        Expr::apps(eqn, [self.nat_type.clone(), lhs, rhs])
    }

    fn symm_nat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        let type1 = Level::succ(Level::zero());
        let es = Expr::const_(Name::from_string("Eq.symm"), vec![type1]);
        Expr::apps(es, [self.nat_type.clone(), a, b, h])
    }

    fn trans_nat(&self, x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr) -> Expr {
        let type1 = Level::succ(Level::zero());
        let et = Expr::const_(Name::from_string("Eq.trans"), vec![type1]);
        Expr::apps(et, [self.nat_type.clone(), x, y, z, h1, h2])
    }

    // ---- feeder lemma applications ----

    fn oms(&self, j: Expr, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.oms.clone(), [j, p, q])
    }

    fn nms(&self, j: Expr, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.nms.clone(), [j, p, q])
    }

    fn snea(&self, m: Expr, n: Expr) -> Expr {
        Expr::apps(self.snea.clone(), [m, n])
    }

    fn iac(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.iac.clone(), [x, y])
    }

    fn nona(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nona.clone(), [a, b])
    }

    fn nld(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.nld.clone(), [a, b, cc])
    }

    fn nsa(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nsa.clone(), [a, b])
    }

    fn nas(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nas.clone(), [a, b])
    }

    /// `λ n : Nat => Int.ofNat n`.
    fn of_nat_fn(&self, parent: &EnvDeclBuilder) -> Expr {
        let mut fb = EnvDeclBuilder::child_of(parent);
        let (n_id, n) = fb.fresh_local(self.nat_type.clone());
        let body = self.of_nat(n);
        let lam = fb.mk_lam(n_id, BinderInfo::Default, self.nat_type.clone(), body);
        fb.finish_child(lam)
    }

    /// `λ n : Nat => Int.negOfNat n`.
    fn neg_of_nat_fn(&self, parent: &EnvDeclBuilder) -> Expr {
        let mut fb = EnvDeclBuilder::child_of(parent);
        let (n_id, n) = fb.fresh_local(self.nat_type.clone());
        let body = self.neg_of_nat(n);
        let lam = fb.mk_lam(n_id, BinderInfo::Default, self.nat_type.clone(), body);
        fb.finish_child(lam)
    }

    /// `λ n : Nat => Nat.mul k n`.
    fn nmul_k_fn(&self, parent: &EnvDeclBuilder, k: &Expr) -> Expr {
        let mut fb = EnvDeclBuilder::child_of(parent);
        let (n_id, n) = fb.fresh_local(self.nat_type.clone());
        let body = self.nmul(k.clone(), n);
        let lam = fb.mk_lam(n_id, BinderInfo::Default, self.nat_type.clone(), body);
        fb.finish_child(lam)
    }

    /// `Eq.refl`-free Nat equality
    /// `natEq[k] : Eq (k*(succ(succ(p+r)))) (Nat.add (k*(succ p)) (k*(succ r)))`.
    ///
    /// `hp' : Nat.add (succ p) (succ r) = succ (succ (p+r))` is
    /// `trans (Nat.succ_add p (succ r)) (congrArg succ (Nat.add_succ p r))`.
    /// `hp := Eq.symm hp'`. Then
    /// `congrArg (Nat.mul k) hp : k*(succ(succ(p+r))) = k*(Nat.add (succ p)(succ r))`
    /// and `Nat.left_distrib k (succ p)(succ r)` finish.
    fn nat_eq_4(&self, parent: &EnvDeclBuilder, k: &Expr, p: &Expr, r: &Expr) -> Expr {
        let succ_p = self.succ(p.clone());
        let succ_r = self.succ(r.clone());
        let p_r = self.nadd(p.clone(), r.clone());
        let s_s_pr = self.succ(self.succ(p_r.clone()));
        let add_sp_sr = self.nadd(succ_p.clone(), succ_r.clone());

        // hp' : Nat.add (succ p) (succ r) = succ (succ (p+r))
        //   step1 : Nat.add (succ p) (succ r) = succ (Nat.add p (succ r))   [succ_add]
        //   step2 : succ (Nat.add p (succ r)) = succ (succ (p+r))           [congrArg succ (add_succ)]
        let step1 = self.nsa(p.clone(), succ_r.clone());
        let succ_fn = {
            let mut fb = EnvDeclBuilder::child_of(parent);
            let (n_id, n) = fb.fresh_local(self.nat_type.clone());
            let body = self.succ(n);
            let lam = fb.mk_lam(n_id, BinderInfo::Default, self.nat_type.clone(), body);
            fb.finish_child(lam)
        };
        let add_p_succ_r = self.nadd(p.clone(), succ_r.clone());
        let step2 = self.congr_arg_nat_nat(
            add_p_succ_r.clone(),
            self.succ(p_r.clone()),
            succ_fn,
            self.nas(p.clone(), r.clone()),
        );
        let succ_add_p_succ_r = self.succ(add_p_succ_r);
        let hp_prime = self.trans_nat(
            add_sp_sr.clone(),
            succ_add_p_succ_r,
            s_s_pr.clone(),
            step1,
            step2,
        );
        let hp = self.symm_nat(add_sp_sr.clone(), s_s_pr.clone(), hp_prime);

        // congrArg (Nat.mul k) hp : k*(succ(succ(p+r))) = k*(Nat.add (succ p)(succ r))
        let mul_fn = self.nmul_k_fn(parent, k);
        let c1 = self.congr_arg_nat_nat(s_s_pr.clone(), add_sp_sr.clone(), mul_fn, hp);
        // Nat.left_distrib k (succ p)(succ r) : k*(Nat.add(succ p)(succ r)) = Nat.add (k*(succ p))(k*(succ r))
        let nld = self.nld(k.clone(), succ_p.clone(), succ_r.clone());

        let lhs = self.nmul(k.clone(), s_s_pr);
        let mid = self.nmul(k.clone(), add_sp_sr);
        let rhs = self.nadd(self.nmul(k.clone(), succ_p), self.nmul(k.clone(), succ_r));
        self.trans_nat(lhs, mid, rhs, c1, nld)
    }
}

/// `∀ a b c : Int, Eq (mul a (add b c)) (add (mul a b) (mul a c))`.
fn build_type(c: &IntLeftDistribConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bv_id, bv) = b.fresh_local(c.int_type.clone());
    let (cv_id, cv) = b.fresh_local(c.int_type.clone());
    let lhs = c.mul(a.clone(), c.add(bv.clone(), cv.clone()));
    let rhs = c.add(c.mul(a.clone(), bv.clone()), c.mul(a.clone(), cv.clone()));
    let concl = c.eq_int(lhs, rhs);
    let ty = b.mk_pi(cv_id, BinderInfo::Default, c.int_type.clone(), concl);
    let ty = b.mk_pi(bv_id, BinderInfo::Default, c.int_type.clone(), ty);
    let ty = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), ty);
    b.finish(ty)
}

/// Motive `λ x : Int => ∀ b c : Int, Eq (mul x (add b c)) (add (mul x b)(mul x c))`,
/// reused at the outer level (`x = a`) and inner levels (`x` is a constructor).
fn dist_pi(c: &IntLeftDistribConsts, parent: &EnvDeclBuilder, x: &Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (bv_id, bv) = mb.fresh_local(c.int_type.clone());
    let (cv_id, cv) = mb.fresh_local(c.int_type.clone());
    let lhs = c.mul(x.clone(), c.add(bv.clone(), cv.clone()));
    let rhs = c.add(c.mul(x.clone(), bv.clone()), c.mul(x.clone(), cv.clone()));
    let body = c.eq_int(lhs, rhs);
    let pi = mb.mk_pi(cv_id, BinderInfo::Default, c.int_type.clone(), body);
    let pi = mb.mk_pi(bv_id, BinderInfo::Default, c.int_type.clone(), pi);
    mb.finish_child(pi)
}

fn outer_motive(c: &IntLeftDistribConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = mb.fresh_local(c.int_type.clone());
    let body = dist_pi(c, &mb, &x);
    let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
    mb.finish_child(lam)
}

/// b-level motive for fixed `a`: `λ y : Int => ∀ c, Eq (mul a (add y c))(...)`.
fn b_motive(c: &IntLeftDistribConsts, parent: &EnvDeclBuilder, a: &Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (y_id, y) = mb.fresh_local(c.int_type.clone());
    // ∀ cc, Eq (mul a (add y cc)) (add (mul a y)(mul a cc))
    let (cc_id, cc) = mb.fresh_local(c.int_type.clone());
    let lhs = c.mul(a.clone(), c.add(y.clone(), cc.clone()));
    let rhs = c.add(c.mul(a.clone(), y.clone()), c.mul(a.clone(), cc.clone()));
    let body = c.eq_int(lhs, rhs);
    let pi = mb.mk_pi(cc_id, BinderInfo::Default, c.int_type.clone(), body);
    let lam = mb.mk_lam(y_id, BinderInfo::Default, c.int_type.clone(), pi);
    mb.finish_child(lam)
}

/// c-level motive for fixed `a`, `bval`: `λ z : Int => Eq (mul a (add bval z))(...)`.
fn c_motive(c: &IntLeftDistribConsts, parent: &EnvDeclBuilder, a: &Expr, bval: &Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (z_id, z) = mb.fresh_local(c.int_type.clone());
    let lhs = c.mul(a.clone(), c.add(bval.clone(), z.clone()));
    let rhs = c.add(c.mul(a.clone(), bval.clone()), c.mul(a.clone(), z.clone()));
    let body = c.eq_int(lhs, rhs);
    let lam = mb.mk_lam(z_id, BinderInfo::Default, c.int_type.clone(), body);
    mb.finish_child(lam)
}

/// Build the c-level `Int.rec` for a fixed outer constructor.
///
/// `a` is the literal outer Int (`ofNat j` or `negSucc j`); `is_neg` selects
/// the leaf family; `j` is the outer Nat; `bval` is the literal `b` Int and
/// `bp`/`b_is_neg` describe its constructor (`p`/whether negSucc). The two
/// leaf closures take the inner `c` Nat `r`.
#[allow(clippy::too_many_arguments)]
fn build_c_rec(
    c: &IntLeftDistribConsts,
    parent: &EnvDeclBuilder,
    a: &Expr,
    bval: &Expr,
    leaf_c_ofnat: Expr,
    leaf_c_negsucc: Expr,
    cv: &Expr,
) -> Expr {
    let motive = c_motive(c, parent, a, bval);
    Expr::apps(
        c.int_rec.clone(),
        [motive, leaf_c_ofnat, leaf_c_negsucc, cv.clone()],
    )
}

/// Outer `ofNat` case: `λ j : Nat => λ b c : Int => (b-rec) ...`.
fn build_a_ofnat(c: &IntLeftDistribConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut jb = EnvDeclBuilder::child_of(parent);
    let (j_id, j) = jb.fresh_local(c.nat_type.clone());
    let a = c.of_nat(j.clone());
    let (bv_id, bv) = jb.fresh_local(c.int_type.clone());
    let (cv_id, cv) = jb.fresh_local(c.int_type.clone());

    // b = ofNat p case: λ p => λ cc => (c-rec on cc with bval = ofNat p).
    // The b-rec minor premise has type `∀ p, b_motive (ofNat p)` =
    // `∀ p, ∀ cc, Eq ...`, so it MUST abstract a fresh `cc` and scrutinize it
    // (NOT the outer `cv`). The c-rec's type is `c_motive cc`; binding `cc`
    // recovers the required `∀ cc` Pi.
    let b_ofnat = {
        let mut pb = EnvDeclBuilder::child_of(&jb);
        let (p_id, p) = pb.fresh_local(c.nat_type.clone());
        let (cc_id, cc) = pb.fresh_local(c.int_type.clone());
        let bval = c.of_nat(p.clone());

        // leaf (c = ofNat r): congrArg ofNat (Nat.left_distrib j p r)
        let leaf_oo = {
            let mut rb = EnvDeclBuilder::child_of(&pb);
            let (r_id, r) = rb.fresh_local(c.nat_type.clone());
            let f = c.of_nat_fn(&rb);
            let h = c.nld(j.clone(), p.clone(), r.clone());
            let a1 = c.nmul(j.clone(), c.nadd(p.clone(), r.clone()));
            let a2 = c.nadd(c.nmul(j.clone(), p.clone()), c.nmul(j.clone(), r.clone()));
            let proof = c.congr_arg_nat_int(a1, a2, f, h);
            let lam = rb.mk_lam(r_id, BinderInfo::Default, c.nat_type.clone(), proof);
            rb.finish_child(lam)
        };
        // leaf (c = negSucc r): trans (oms j p (succ r)) (snea (j*p) (j*(succ r)))
        let leaf_on = {
            let mut rb = EnvDeclBuilder::child_of(&pb);
            let (r_id, r) = rb.fresh_local(c.nat_type.clone());
            let sr = c.succ(r.clone());
            let e1 = c.oms(j.clone(), p.clone(), sr.clone());
            let jp = c.nmul(j.clone(), p.clone());
            let jsr = c.nmul(j.clone(), sr.clone());
            let mid = c.sub_nat_nat_expr(jp.clone(), jsr.clone());
            let e2 = c.snea(jp.clone(), jsr.clone());
            let lhs = c.mul(a.clone(), c.sub_nat_nat_expr(p.clone(), sr));
            let rhs = c.add(c.of_nat(jp), c.neg_of_nat(jsr));
            let proof = c.trans_int(lhs, mid, rhs, e1, e2);
            let lam = rb.mk_lam(r_id, BinderInfo::Default, c.nat_type.clone(), proof);
            rb.finish_child(lam)
        };
        let crec = build_c_rec(c, &pb, &a, &bval, leaf_oo, leaf_on, &cc);
        let lam = pb.mk_lam(cc_id, BinderInfo::Default, c.int_type.clone(), crec);
        let lam = pb.mk_lam(p_id, BinderInfo::Default, c.nat_type.clone(), lam);
        pb.finish_child(lam)
    };

    // b = negSucc p case: λ p => λ cc => (c-rec on cc with bval = negSucc p).
    let b_negsucc = {
        let mut pb = EnvDeclBuilder::child_of(&jb);
        let (p_id, p) = pb.fresh_local(c.nat_type.clone());
        let (cc_id, cc) = pb.fresh_local(c.int_type.clone());
        let bval = c.neg_succ(p.clone());
        let sp = c.succ(p.clone());

        // leaf (c = ofNat r): trans3 (oms j r (succ p)) (snea (j*r)(j*(succ p)))
        //                            (Int.add_comm (ofNat (j*r))(negOfNat (j*(succ p))))
        let leaf_no = {
            let mut rb = EnvDeclBuilder::child_of(&pb);
            let (r_id, r) = rb.fresh_local(c.nat_type.clone());
            let e1 = c.oms(j.clone(), r.clone(), sp.clone());
            let jr = c.nmul(j.clone(), r.clone());
            let jsp = c.nmul(j.clone(), sp.clone());
            let mid1 = c.sub_nat_nat_expr(jr.clone(), jsp.clone());
            let e2 = c.snea(jr.clone(), jsp.clone());
            let of_jr = c.of_nat(jr.clone());
            let no_jsp = c.neg_of_nat(jsp.clone());
            let mid2 = c.add(of_jr.clone(), no_jsp.clone());
            let e3 = c.iac(of_jr, no_jsp.clone());
            let lhs = c.mul(a.clone(), c.sub_nat_nat_expr(r.clone(), sp.clone()));
            let final_rhs = c.add(no_jsp, c.of_nat(jr));
            let t1 = c.trans_int(lhs.clone(), mid1, mid2.clone(), e1, e2);
            let proof = c.trans_int(lhs, mid2, final_rhs, t1, e3);
            let lam = rb.mk_lam(r_id, BinderInfo::Default, c.nat_type.clone(), proof);
            rb.finish_child(lam)
        };
        // leaf (c = negSucc r): trans (congrArg negOfNat natEq[j]) (symm (negOfNat_add (j*(succ p))(j*(succ r))))
        let leaf_nn = {
            let mut rb = EnvDeclBuilder::child_of(&pb);
            let (r_id, r) = rb.fresh_local(c.nat_type.clone());
            let sr = c.succ(r.clone());
            let p_r = c.nadd(p.clone(), r.clone());
            let s_s_pr = c.succ(c.succ(p_r));
            let lhs_arg = c.nmul(j.clone(), s_s_pr.clone());
            let jsp = c.nmul(j.clone(), sp.clone());
            let jsr = c.nmul(j.clone(), sr.clone());
            let add_jsp_jsr = c.nadd(jsp.clone(), jsr.clone());

            let neg_fn = c.neg_of_nat_fn(&rb);
            let nat_eq = c.nat_eq_4(&rb, &j, &p, &r);
            let e1 = c.congr_arg_nat_int(lhs_arg.clone(), add_jsp_jsr.clone(), neg_fn, nat_eq);
            // symm (negOfNat_add (j*(succ p)) (j*(succ r)))
            //   : negOfNat (Nat.add (j*(succ p))(j*(succ r))) = add (negOfNat (j*(succ p)))(negOfNat (j*(succ r)))
            let nona = c.nona(jsp.clone(), jsr.clone());
            let nona_lhs = c.add(c.neg_of_nat(jsp.clone()), c.neg_of_nat(jsr.clone()));
            let nona_rhs = c.neg_of_nat(add_jsp_jsr.clone());
            let e2 = c.symm_int(nona_lhs.clone(), nona_rhs.clone(), nona);

            let lhs = c.mul(
                a.clone(),
                c.add(c.neg_succ(p.clone()), c.neg_succ(r.clone())),
            );
            // `lhs` is defeq to `negOfNat lhs_arg` (mul (ofNat j) (negSucc (succ (p+r)))
            // reduces to negOfNat (j * succ (succ (p+r)))). The trans midpoint is
            // where `e1` ends = `negOfNat add_jsp_jsr` (= nona_rhs), NOT
            // `negOfNat lhs_arg`:
            //   e1 : Eq (negOfNat lhs_arg)        (negOfNat add_jsp_jsr)   [≡ Eq lhs mid]
            //   e2 : Eq (negOfNat add_jsp_jsr)    nona_lhs
            let mid = nona_rhs;
            let proof = c.trans_int(lhs, mid, nona_lhs, e1, e2);
            let lam = rb.mk_lam(r_id, BinderInfo::Default, c.nat_type.clone(), proof);
            rb.finish_child(lam)
        };
        let crec = build_c_rec(c, &pb, &a, &bval, leaf_no, leaf_nn, &cc);
        let lam = pb.mk_lam(cc_id, BinderInfo::Default, c.int_type.clone(), crec);
        let lam = pb.mk_lam(p_id, BinderInfo::Default, c.nat_type.clone(), lam);
        pb.finish_child(lam)
    };

    let brec = Expr::apps(
        c.int_rec.clone(),
        [b_motive(c, &jb, &a), b_ofnat, b_negsucc, bv.clone()],
    );
    let body = Expr::app(brec, cv);
    let lam = jb.mk_lam(cv_id, BinderInfo::Default, c.int_type.clone(), body);
    let lam = jb.mk_lam(bv_id, BinderInfo::Default, c.int_type.clone(), lam);
    let lam = jb.mk_lam(j_id, BinderInfo::Default, c.nat_type.clone(), lam);
    jb.finish_child(lam)
}

/// Outer `negSucc` case: `λ j : Nat => λ b c : Int => (b-rec) ...`.
fn build_a_negsucc(c: &IntLeftDistribConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut jb = EnvDeclBuilder::child_of(parent);
    let (j_id, j) = jb.fresh_local(c.nat_type.clone());
    let s = c.succ(j.clone());
    let a = c.neg_succ(j.clone());
    let (bv_id, bv) = jb.fresh_local(c.int_type.clone());
    let (cv_id, cv) = jb.fresh_local(c.int_type.clone());

    // b = ofNat p case: λ p => λ cc => (c-rec on cc). The b-rec minor premise
    // type is `∀ p, ∀ cc, Eq ...`, so a fresh `cc` is bound and scrutinized.
    let b_ofnat = {
        let mut pb = EnvDeclBuilder::child_of(&jb);
        let (p_id, p) = pb.fresh_local(c.nat_type.clone());
        let (cc_id, cc) = pb.fresh_local(c.int_type.clone());
        let bval = c.of_nat(p.clone());

        // leaf (c = ofNat r): trans (congrArg negOfNat (Nat.left_distrib s p r))
        //                          (symm (negOfNat_add (s*p)(s*r)))
        let leaf_oo = {
            let mut rb = EnvDeclBuilder::child_of(&pb);
            let (r_id, r) = rb.fresh_local(c.nat_type.clone());
            let neg_fn = c.neg_of_nat_fn(&rb);
            let h = c.nld(s.clone(), p.clone(), r.clone());
            let a1 = c.nmul(s.clone(), c.nadd(p.clone(), r.clone()));
            let sp = c.nmul(s.clone(), p.clone());
            let sr = c.nmul(s.clone(), r.clone());
            let a2 = c.nadd(sp.clone(), sr.clone());
            let e1 = c.congr_arg_nat_int(a1, a2.clone(), neg_fn, h);
            let nona = c.nona(sp.clone(), sr.clone());
            let nona_lhs = c.add(c.neg_of_nat(sp.clone()), c.neg_of_nat(sr.clone()));
            let nona_rhs = c.neg_of_nat(a2.clone());
            let e2 = c.symm_int(nona_lhs.clone(), nona_rhs.clone(), nona);
            let lhs = c.mul(a.clone(), c.add(c.of_nat(p.clone()), c.of_nat(r.clone())));
            // `lhs` is defeq to `negOfNat a1`; the trans midpoint is the endpoint
            // of `e1` = `negOfNat a2` (= nona_rhs), NOT `negOfNat a1`.
            let mid = nona_rhs;
            let proof = c.trans_int(lhs, mid, nona_lhs, e1, e2);
            let lam = rb.mk_lam(r_id, BinderInfo::Default, c.nat_type.clone(), proof);
            rb.finish_child(lam)
        };
        // leaf (c = negSucc r): trans3 (nms j p (succ r)) (snea (s*(succ r))(s*p))
        //                              (Int.add_comm (ofNat (s*(succ r)))(negOfNat (s*p)))
        let leaf_on = {
            let mut rb = EnvDeclBuilder::child_of(&pb);
            let (r_id, r) = rb.fresh_local(c.nat_type.clone());
            let sr = c.succ(r.clone());
            let e1 = c.nms(j.clone(), p.clone(), sr.clone());
            let s_sr = c.nmul(s.clone(), sr.clone());
            let sp = c.nmul(s.clone(), p.clone());
            let mid1 = c.sub_nat_nat_expr(s_sr.clone(), sp.clone());
            let e2 = c.snea(s_sr.clone(), sp.clone());
            let of_ssr = c.of_nat(s_sr.clone());
            let no_sp = c.neg_of_nat(sp.clone());
            let mid2 = c.add(of_ssr.clone(), no_sp.clone());
            let e3 = c.iac(of_ssr, no_sp.clone());
            let lhs = c.mul(a.clone(), c.sub_nat_nat_expr(p.clone(), sr));
            let final_rhs = c.add(no_sp, c.of_nat(s_sr));
            let t1 = c.trans_int(lhs.clone(), mid1, mid2.clone(), e1, e2);
            let proof = c.trans_int(lhs, mid2, final_rhs, t1, e3);
            let lam = rb.mk_lam(r_id, BinderInfo::Default, c.nat_type.clone(), proof);
            rb.finish_child(lam)
        };
        let crec = build_c_rec(c, &pb, &a, &bval, leaf_oo, leaf_on, &cc);
        let lam = pb.mk_lam(cc_id, BinderInfo::Default, c.int_type.clone(), crec);
        let lam = pb.mk_lam(p_id, BinderInfo::Default, c.nat_type.clone(), lam);
        pb.finish_child(lam)
    };

    // b = negSucc p case: λ p => λ cc => (c-rec on cc).
    let b_negsucc = {
        let mut pb = EnvDeclBuilder::child_of(&jb);
        let (p_id, p) = pb.fresh_local(c.nat_type.clone());
        let (cc_id, cc) = pb.fresh_local(c.int_type.clone());
        let bval = c.neg_succ(p.clone());
        let sp = c.succ(p.clone());

        // leaf (c = ofNat r): trans (nms j r (succ p)) (snea (s*(succ p))(s*r))
        let leaf_no = {
            let mut rb = EnvDeclBuilder::child_of(&pb);
            let (r_id, r) = rb.fresh_local(c.nat_type.clone());
            let e1 = c.nms(j.clone(), r.clone(), sp.clone());
            let s_sp = c.nmul(s.clone(), sp.clone());
            let sr = c.nmul(s.clone(), r.clone());
            let mid = c.sub_nat_nat_expr(s_sp.clone(), sr.clone());
            let e2 = c.snea(s_sp.clone(), sr.clone());
            let lhs = c.mul(a.clone(), c.sub_nat_nat_expr(r.clone(), sp.clone()));
            let rhs = c.add(c.of_nat(s_sp), c.neg_of_nat(sr));
            let proof = c.trans_int(lhs, mid, rhs, e1, e2);
            let lam = rb.mk_lam(r_id, BinderInfo::Default, c.nat_type.clone(), proof);
            rb.finish_child(lam)
        };
        // leaf (c = negSucc r): congrArg ofNat natEq[s]
        let leaf_nn = {
            let mut rb = EnvDeclBuilder::child_of(&pb);
            let (r_id, r) = rb.fresh_local(c.nat_type.clone());
            let p_r = c.nadd(p.clone(), r.clone());
            let s_s_pr = c.succ(c.succ(p_r));
            let lhs_arg = c.nmul(s.clone(), s_s_pr.clone());
            let ssp = c.nmul(s.clone(), c.succ(p.clone()));
            let ssr = c.nmul(s.clone(), c.succ(r.clone()));
            let add_ssp_ssr = c.nadd(ssp, ssr);
            let f = c.of_nat_fn(&rb);
            let nat_eq = c.nat_eq_4(&rb, &s, &p, &r);
            let proof = c.congr_arg_nat_int(lhs_arg, add_ssp_ssr, f, nat_eq);
            let lam = rb.mk_lam(r_id, BinderInfo::Default, c.nat_type.clone(), proof);
            rb.finish_child(lam)
        };
        let crec = build_c_rec(c, &pb, &a, &bval, leaf_no, leaf_nn, &cc);
        let lam = pb.mk_lam(cc_id, BinderInfo::Default, c.int_type.clone(), crec);
        let lam = pb.mk_lam(p_id, BinderInfo::Default, c.nat_type.clone(), lam);
        pb.finish_child(lam)
    };

    let brec = Expr::apps(
        c.int_rec.clone(),
        [b_motive(c, &jb, &a), b_ofnat, b_negsucc, bv.clone()],
    );
    let body = Expr::app(brec, cv);
    let lam = jb.mk_lam(cv_id, BinderInfo::Default, c.int_type.clone(), body);
    let lam = jb.mk_lam(bv_id, BinderInfo::Default, c.int_type.clone(), lam);
    let lam = jb.mk_lam(j_id, BinderInfo::Default, c.nat_type.clone(), lam);
    jb.finish_child(lam)
}

/// Body: `λ (a b c : Int) => (@Int.rec.{0} outer_motive a_ofNat a_negSucc a) b c`.
fn build_value(c: &IntLeftDistribConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (a_id, a) = vb.fresh_local(c.int_type.clone());
    let (bv_id, bv) = vb.fresh_local(c.int_type.clone());
    let (cv_id, cv) = vb.fresh_local(c.int_type.clone());

    let motive = outer_motive(c, &vb);
    let a_ofnat = build_a_ofnat(c, &vb);
    let a_negsucc = build_a_negsucc(c, &vb);
    let rec_a = Expr::apps(c.int_rec.clone(), [motive, a_ofnat, a_negsucc, a]);
    let body = Expr::app(Expr::app(rec_a, bv), cv);
    let val = vb.mk_lam(cv_id, BinderInfo::Default, c.int_type.clone(), body);
    let val = vb.mk_lam(bv_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = vb.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    vb.finish(val)
}

impl IntLeftDistribConsts {
    fn sub_nat_nat_expr(&self, m: Expr, n: Expr) -> Expr {
        let snn = Expr::const_(Name::from_string("Int.subNatNat"), vec![]);
        Expr::app(Expr::app(snn, m), n)
    }
}

impl Environment {
    /// Register `Int.left_distrib` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int`, `Int.ofNat`,
    ///           `Int.negSucc`, `Int.negOfNat`, `Int.add`, `Int.mul`,
    ///           `Int.subNatNat`, `Int.rec`.
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.succ`,
    ///           `Nat.add`, `Nat.mul`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.symm`, `Eq.trans`,
    ///           `congrArg`.
    /// REQUIRES: `Int.ofNat_mul_subNatNat`, `Int.negSucc_mul_subNatNat`,
    ///           `Int.subNatNat_eq_add`, `Int.add_comm`, `Int.negOfNat_add`,
    ///           `Nat.left_distrib`, `Nat.succ_add`, `Nat.add_succ` are
    ///           registered as constructive `Declaration::Theorem`s.
    /// ENSURES: On success, `Int.left_distrib` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_int_left_distrib_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.left_distrib");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;
        self.register_int_ofnat_mul_sub_nat_nat_proof()?;
        self.register_int_negsucc_mul_sub_nat_nat_proof()?;
        self.register_int_sub_nat_nat_eq_add_proof()?;
        self.register_int_add_comm_proof()?;
        self.register_int_negofnat_add_proof()?;
        self.register_nat_left_distrib_proof()?;
        self.register_nat_succ_add_proof()?;
        self.register_nat_add_succ_proof()?;

        let c = IntLeftDistribConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Triple nested
        // `@Int.rec.{0}` (outer on `a`, then `b`, then `c`) with eight
        // constructor leaves. Same-sign leaves lift `Nat.left_distrib`
        // through `Int.ofNat` / `Int.negOfNat` (`congrArg`, `Int.negOfNat_add`);
        // mixed-sign leaves cross the normalized `Int.subNatNat` via
        // `Int.ofNat_mul_subNatNat` / `Int.negSucc_mul_subNatNat`, then
        // `Int.subNatNat_eq_add` (and `Int.add_comm` for the swapped-summand
        // corners), all glued by `Eq.trans`. No `sorry`, no self-reference,
        // no domain-axiom dependency (every feeder lemma is constructive
        // #3604). Replaces the prior `Declaration::Axiom` in
        // `data_types_int_lemmas.rs::init_int_arith_lemmas`.
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
    use crate::env::{ConstantKind, ProofQuality};

    #[test]
    fn test_int_left_distrib_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_left_distrib_proof()
            .expect("first registration");
        env.register_int_left_distrib_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.left_distrib"))
            .expect("Int.left_distrib should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_left_distrib_proof_uses_int_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_left_distrib_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.left_distrib"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        // Peel three outer λ (a, b, c); body is `(Int.rec ... a) b c`.
        let mut body = value.clone();
        for _ in 0..3 {
            body = match body.kind() {
                ExprKind::Lam(_, _, inner) => (**inner).clone(),
                k => panic!("expected outer λ, got {:?}", k),
            };
        }
        let mut head = body;
        while let ExprKind::App(f, _) = head.kind() {
            head = (**f).clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Int.rec",
                "proof root must be Int.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Int.rec, ..) at proof root, got {:?}", k),
        }
    }

    #[test]
    fn test_int_left_distrib_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_left_distrib_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.left_distrib"))
            .expect("registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.left_distrib must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }

    #[test]
    fn test_int_left_distrib_proof_quality_constructive() {
        let mut env = Environment::new();
        env.register_int_left_distrib_proof().unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Int.left_distrib"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.left_distrib must be Constructive, got {:?}",
            quality
        );
    }
}
