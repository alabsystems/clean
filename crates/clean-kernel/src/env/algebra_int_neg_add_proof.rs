// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.neg_add : forall a b : Int,
//!     Eq Int (Int.neg (Int.add a b)) (Int.add (Int.neg a) (Int.neg b))`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_int_lemmas.rs` with a `Declaration::Theorem`. This is the
//! long-deferred negation-distributes-over-addition law `-(a + b) = (-a) + (-b)`.
//!
//! # Proof sketch
//!
//! `Int.neg` / `Int.add` / `Int.subNatNat` are reducible Definitions:
//!
//! ```text
//! Int.neg (ofNat 0)        = ofNat 0
//! Int.neg (ofNat (succ k)) = negSucc k
//! Int.neg (negSucc k)      = ofNat (succ k)
//!
//! Int.add (ofNat m)   (ofNat n)   = ofNat (m + n)
//! Int.add (ofNat m)   (negSucc n) = subNatNat m (succ n)
//! Int.add (negSucc m) (ofNat n)   = subNatNat n (succ m)
//! Int.add (negSucc m) (negSucc n) = negSucc (succ (m + n))
//!
//! Int.subNatNat m 0           = ofNat m
//! Int.subNatNat 0 (succ n)    = negSucc n
//! Int.subNatNat (succ m) (succ n) = subNatNat m n
//! ```
//!
//! Built by a nested `@Int.rec.{0}` case-analysis (outer on `a`, inner on
//! `b`). The outer `ofNat m` case splits the underlying `Nat` `m` via
//! `@Nat.rec.{0}` (so `Int.neg (Int.ofNat m)` reduces to a constructor); the
//! inner `ofNat n` leaves likewise split `n` where `Int.neg (Int.ofNat n)` is
//! otherwise stuck. The leaves close as follows (all `congrArg` / `Eq.symm` /
//! `Eq.trans` glue over the constructive `Int.neg_subNatNat`,
//! `Int.subNatNat_zero_succ`, `Nat.zero_add`, `Nat.succ_add`):
//!
//! ```text
//! a=ofNat 0,      b=ofNat 0      : Eq.refl (ofNat 0)
//! a=ofNat 0,      b=ofNat(succ p): trans (congrArg negSucc (zero_add p))
//!                                        (symm (subNatNat_zero_succ p))
//! a=ofNat 0,      b=negSucc n    : trans (neg_subNatNat 0 (succ n))
//!                                        (symm (congrArg ofNat (zero_add (succ n))))
//! a=ofNat(succ j),b=ofNat 0      : symm (subNatNat_zero_succ j)
//! a=ofNat(succ j),b=ofNat(succ p): congrArg (fun x => neg (ofNat x))
//!                                          (congrArg succ (succ_add j p))
//! a=ofNat(succ j),b=negSucc n    : trans (congrArg neg (subNatNat_succ_succ j n))
//!                                        (trans (neg_subNatNat j n)
//!                                               (symm (subNatNat_succ_succ n j)))
//! a=negSucc m,    b=ofNat 0      : neg_subNatNat 0 (succ m)
//! a=negSucc m,    b=ofNat(succ p): trans (congrArg neg (subNatNat_succ_succ p m))
//!                                        (trans (neg_subNatNat p m)
//!                                               (symm (subNatNat_succ_succ m p)))
//! a=negSucc m,    b=negSucc n    : congrArg ofNat (symm (congrArg succ (succ_add m n)))
//! ```
//!
//! The two mixed-sign successor/successor leaves (`a=ofNat(succ j),b=negSucc n`
//! and `a=negSucc m,b=ofNat(succ p)`) cannot close with a bare `neg_subNatNat`:
//! `Int.subNatNat` iota-reduces on its SECOND argument only, so
//! `subNatNat (succ _) (succ _)` is STUCK, not definitionally equal to the
//! dropped-successor form. Both are bridged via the constructive
//! `Int.subNatNat_succ_succ`.
//!
//! # Axiom closure
//!
//! The proof term mentions only kernel machinery / constructors / reducible
//! Definitions (`Int`, `Int.neg`, `Int.add`, `Int.subNatNat`, `Int.ofNat`,
//! `Int.negSucc`, `Int.rec`, `Nat`, `Nat.zero`, `Nat.succ`, `Nat.rec`, `Eq`,
//! `Eq.refl`, `Eq.symm`, `Eq.trans`, `congrArg`) and the constructive
//! `Declaration::Theorem`s `Int.neg_subNatNat`, `Int.subNatNat_zero_succ`,
//! `Int.subNatNat_succ_succ`, `Nat.zero_add`, `Nat.succ_add` (all #3604, empty
//! domain-axiom closures).
//! None are `Declaration::Axiom`, so `env.axiom_deps("Int.neg_add")` is empty
//! and the proof quality is `ProofQuality::Constructive`.
//!
//! Tracks #3604. Dependency: `algebra_int_neg_sub_nat_nat_proof.rs`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntNegAddConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_rec: Expr,
    int_neg: Expr,
    int_add: Expr,
    int_of_nat: Expr,
    int_neg_succ: Expr,
    int_sub_nat_nat: Expr,
    int_rec: Expr,
    eq_const: Expr,
    eq_refl: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
    nat_zero_add: Expr,
    nat_succ_add: Expr,
    int_neg_sub_nat_nat: Expr,
    int_sub_nat_nat_zero_succ: Expr,
    int_sub_nat_nat_succ_succ: Expr,
}

impl IntNegAddConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            int_neg: Expr::const_(Name::from_string("Int.neg"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            int_sub_nat_nat: Expr::const_(Name::from_string("Int.subNatNat"), vec![]),
            int_rec: Expr::const_(Name::from_string("Int.rec"), vec![Level::zero()]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            // congrArg.{1,1} : {a b : Type} -> {x y : a} -> (f : a -> b) -> Eq x y -> Eq (f x) (f y)
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            nat_zero_add: Expr::const_(Name::from_string("Nat.zero_add"), vec![]),
            nat_succ_add: Expr::const_(Name::from_string("Nat.succ_add"), vec![]),
            int_neg_sub_nat_nat: Expr::const_(Name::from_string("Int.neg_subNatNat"), vec![]),
            int_sub_nat_nat_zero_succ: Expr::const_(
                Name::from_string("Int.subNatNat_zero_succ"),
                vec![],
            ),
            int_sub_nat_nat_succ_succ: Expr::const_(
                Name::from_string("Int.subNatNat_succ_succ"),
                vec![],
            ),
        }
    }

    fn neg(&self, x: Expr) -> Expr {
        Expr::app(self.int_neg.clone(), x)
    }

    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), x), y)
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

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }

    fn refl_int(&self, t: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.int_type.clone(), t])
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

    /// `@congrArg.{1,1} Nat Int x y f h : Eq Int (f x) (f y)` from
    /// `h : Eq Nat x y` and `f : Nat -> Int`.
    fn congr_nat_int(&self, x: Expr, y: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.nat_type.clone(), self.int_type.clone(), x, y, f, h],
        )
    }

    /// `Nat.zero_add k : Eq Nat (Nat.add 0 k) k`.
    fn zero_add(&self, k: Expr) -> Expr {
        Expr::app(self.nat_zero_add.clone(), k)
    }

    /// `Nat.succ_add a b : Eq Nat (Nat.add (succ a) b) (Nat.succ (Nat.add a b))`.
    fn succ_add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_succ_add.clone(), [a, b])
    }

    /// `Int.neg_subNatNat m n : Eq Int (Int.neg (Int.subNatNat m n)) (Int.subNatNat n m)`.
    fn neg_sub(&self, m: Expr, n: Expr) -> Expr {
        Expr::apps(self.int_neg_sub_nat_nat.clone(), [m, n])
    }

    /// `Int.subNatNat_zero_succ n : Eq Int (Int.subNatNat 0 (succ n)) (Int.negSucc n)`.
    fn snn_zero_succ(&self, n: Expr) -> Expr {
        Expr::app(self.int_sub_nat_nat_zero_succ.clone(), n)
    }

    /// `Int.subNatNat_succ_succ m n :
    ///   Eq Int (Int.subNatNat (succ m) (succ n)) (Int.subNatNat m n)`.
    fn snn_succ_succ(&self, m: Expr, n: Expr) -> Expr {
        Expr::apps(self.int_sub_nat_nat_succ_succ.clone(), [m, n])
    }

    /// `@congrArg.{1,1} Int Int a b Int.neg h : Eq Int (neg a) (neg b)` from
    /// `h : Eq Int a b`.
    fn congr_neg(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [
                self.int_type.clone(),
                self.int_type.clone(),
                a,
                b,
                self.int_neg.clone(),
                h,
            ],
        )
    }
}

/// Build `forall a b : Int, Eq Int (Int.neg (Int.add a b)) (Int.add (Int.neg a) (Int.neg b))`.
fn build_type(c: &IntNegAddConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bv_id, bv) = b.fresh_local(c.int_type.clone());
    let lhs = c.neg(c.add(a.clone(), bv.clone()));
    let rhs = c.add(c.neg(a), c.neg(bv));
    let concl = c.eq_int(lhs, rhs);
    let ty_raw = b.mk_pi(bv_id, BinderInfo::Default, c.int_type.clone(), concl);
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), ty_raw);
    b.finish(ty_raw)
}

/// Outer motive: `lambda (x : Int) => forall b : Int,
///   Eq Int (Int.neg (Int.add x b)) (Int.add (Int.neg x) (Int.neg b))`.
fn build_outer_motive(c: &IntNegAddConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = mb.fresh_local(c.int_type.clone());
    let (b_id, bv) = mb.fresh_local(c.int_type.clone());
    let body = c.eq_int(
        c.neg(c.add(x.clone(), bv.clone())),
        c.add(c.neg(x), c.neg(bv)),
    );
    let pi = mb.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), body);
    let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), pi);
    mb.finish_child(lam)
}

/// Inner `Int.rec` motive for a fixed `a_lit : Int`:
/// `lambda (b : Int) => Eq Int (neg (add a_lit b)) (add (neg a_lit) (neg b))`.
fn build_inner_motive(c: &IntNegAddConsts, parent: &EnvDeclBuilder, a_lit: &Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (b_id, bv) = mb.fresh_local(c.int_type.clone());
    let body = c.eq_int(
        c.neg(c.add(a_lit.clone(), bv.clone())),
        c.add(c.neg(a_lit.clone()), c.neg(bv)),
    );
    let lam = mb.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), body);
    mb.finish_child(lam)
}

/// `lambda x : Nat => Int.neg (Int.ofNat x)` — used as a `congrArg` function.
fn neg_of_nat_fn(c: &IntNegAddConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut fb = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = fb.fresh_local(c.nat_type.clone());
    let body = c.neg(c.of_nat(x));
    let lam = fb.mk_lam(x_id, BinderInfo::Default, c.nat_type.clone(), body);
    fb.finish_child(lam)
}

/// Outer `ofNat` case: `lambda (m : Nat) => @Nat.rec.{0} nat_motive m0 msucc m`
/// where each branch returns `lambda (b : Int) => @Int.rec.{0} inner_motive ...`.
fn build_outer_ofnat_case(c: &IntNegAddConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut cb = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = cb.fresh_local(c.nat_type.clone());

    // nat_motive : lambda (w : Nat) => forall b : Int,
    //   Eq Int (neg (add (ofNat w) b)) (add (neg (ofNat w)) (neg b))
    let nat_motive = {
        let mut mb = EnvDeclBuilder::child_of(&cb);
        let (w_id, w) = mb.fresh_local(c.nat_type.clone());
        let of_w = c.of_nat(w);
        let (b_id, bv) = mb.fresh_local(c.int_type.clone());
        let body = c.eq_int(
            c.neg(c.add(of_w.clone(), bv.clone())),
            c.add(c.neg(of_w), c.neg(bv)),
        );
        let pi = mb.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), body);
        let lam = mb.mk_lam(w_id, BinderInfo::Default, c.nat_type.clone(), pi);
        mb.finish_child(lam)
    };

    // m = 0 branch: lambda (b : Int) => @Int.rec.{0} (inner_motive (ofNat 0)) oo on b
    let zero_branch = {
        let mut zb = EnvDeclBuilder::child_of(&cb);
        let (b_id, bv) = zb.fresh_local(c.int_type.clone());
        let a_lit = c.of_nat(c.nat_zero.clone());
        let inner_motive = build_inner_motive(c, &zb, &a_lit);

        // inner ofNat leaf: lambda (n : Nat) => @Nat.rec.{0} n_motive n0 nsucc n
        let oo = {
            let mut ob = EnvDeclBuilder::child_of(&zb);
            let (n_id, n) = ob.fresh_local(c.nat_type.clone());
            // n_motive : lambda (w : Nat) =>
            //   Eq Int (neg (add (ofNat 0) (ofNat w))) (add (neg (ofNat 0)) (neg (ofNat w)))
            let n_motive = {
                let mut nm = EnvDeclBuilder::child_of(&ob);
                let (w_id, w) = nm.fresh_local(c.nat_type.clone());
                let body = c.eq_int(
                    c.neg(c.add(a_lit.clone(), c.of_nat(w.clone()))),
                    c.add(c.neg(a_lit.clone()), c.neg(c.of_nat(w))),
                );
                let lam = nm.mk_lam(w_id, BinderInfo::Default, c.nat_type.clone(), body);
                nm.finish_child(lam)
            };
            // n = 0: refl (ofNat 0).
            let n0 = c.refl_int(c.of_nat(c.nat_zero.clone()));
            // n = succ p: trans (congrArg negSucc (zero_add p)) (symm (snn_zero_succ p)).
            let nsucc = {
                let mut sb = EnvDeclBuilder::child_of(&ob);
                let (p_id, p) = sb.fresh_local(c.nat_type.clone());
                let ih_ty = c.eq_int(
                    c.neg(c.add(a_lit.clone(), c.of_nat(p.clone()))),
                    c.add(c.neg(a_lit.clone()), c.neg(c.of_nat(p.clone()))),
                );
                let (ih_id, _ih) = sb.fresh_local(ih_ty.clone());
                // h1 : negSucc (0 + p) = negSucc p
                let zero_p = Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Nat.add"), vec![]),
                        c.nat_zero.clone(),
                    ),
                    p.clone(),
                );
                let h1 = c.congr_nat_int(
                    zero_p.clone(),
                    p.clone(),
                    c.int_neg_succ.clone(),
                    c.zero_add(p.clone()),
                );
                // h2 : negSucc p = subNatNat 0 (succ p)  [symm of snn_zero_succ p]
                let snn = Expr::app(
                    Expr::app(c.int_sub_nat_nat.clone(), c.nat_zero.clone()),
                    c.succ(p.clone()),
                );
                let h2 = c.symm_int(
                    snn.clone(),
                    c.neg_succ(p.clone()),
                    c.snn_zero_succ(p.clone()),
                );
                let proof = c.trans_int(c.neg_succ(zero_p), c.neg_succ(p.clone()), snn, h1, h2);
                let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, proof);
                let lam_p = sb.mk_lam(p_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
                sb.finish_child(lam_p)
            };
            let rec_n = Expr::apps(c.nat_rec.clone(), [n_motive, n0, nsucc, n]);
            let lam = ob.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), rec_n);
            ob.finish_child(lam)
        };

        // inner negSucc leaf: lambda (n : Nat) =>
        //   trans (neg_sub 0 (succ n)) (symm (congrArg ofNat (zero_add (succ n))))
        let on = {
            let mut ob = EnvDeclBuilder::child_of(&zb);
            let (n_id, n) = ob.fresh_local(c.nat_type.clone());
            let succ_n = c.succ(n.clone());
            // h1 : neg (subNatNat 0 (succ n)) = subNatNat (succ n) 0
            let h1 = c.neg_sub(c.nat_zero.clone(), succ_n.clone());
            let snn_lhs = Expr::app(
                Expr::app(c.int_sub_nat_nat.clone(), c.nat_zero.clone()),
                succ_n.clone(),
            );
            let snn_rhs = Expr::app(
                Expr::app(c.int_sub_nat_nat.clone(), succ_n.clone()),
                c.nat_zero.clone(),
            );
            // h2 : subNatNat (succ n) 0 = ofNat (0 + succ n)
            //   via symm of congrArg ofNat (zero_add (succ n)) : ofNat (0 + succ n) = ofNat (succ n)
            //   (subNatNat (succ n) 0 is defeq ofNat (succ n)).
            let zero_succ_n = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Nat.add"), vec![]),
                    c.nat_zero.clone(),
                ),
                succ_n.clone(),
            );
            let of_zero_succ_n = c.of_nat(zero_succ_n.clone());
            let of_succ_n = c.of_nat(succ_n.clone());
            let congr = c.congr_nat_int(
                zero_succ_n,
                succ_n.clone(),
                c.int_of_nat.clone(),
                c.zero_add(succ_n.clone()),
            );
            let h2 = c.symm_int(of_zero_succ_n.clone(), of_succ_n, congr);
            let proof = c.trans_int(c.neg(snn_lhs), snn_rhs, of_zero_succ_n, h1, h2);
            let lam = ob.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), proof);
            ob.finish_child(lam)
        };

        let rec_b = Expr::apps(c.int_rec.clone(), [inner_motive, oo, on, bv.clone()]);
        let lam = zb.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), rec_b);
        zb.finish_child(lam)
    };

    // m = succ j branch.
    let succ_branch = {
        let mut sb = EnvDeclBuilder::child_of(&cb);
        let (j_id, j) = sb.fresh_local(c.nat_type.clone());
        // outer Nat ih (unused): forall b, ...
        let ih_ty = {
            let mut ib = EnvDeclBuilder::child_of(&sb);
            let of_j = c.of_nat(j.clone());
            let (b_id, bv) = ib.fresh_local(c.int_type.clone());
            let body = c.eq_int(
                c.neg(c.add(of_j.clone(), bv.clone())),
                c.add(c.neg(of_j), c.neg(bv)),
            );
            let pi = ib.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), body);
            ib.finish_child(pi)
        };
        let (ih_id, _ih) = sb.fresh_local(ih_ty.clone());

        let succ_j = c.succ(j.clone());
        let a_lit = c.of_nat(succ_j.clone());
        let (b_id, bv) = sb.fresh_local(c.int_type.clone());
        let inner_motive = build_inner_motive(c, &sb, &a_lit);

        // inner ofNat leaf: lambda (n : Nat) => @Nat.rec.{0} n_motive n0 nsucc n
        let oo = {
            let mut ob = EnvDeclBuilder::child_of(&sb);
            let (n_id, n) = ob.fresh_local(c.nat_type.clone());
            let n_motive = {
                let mut nm = EnvDeclBuilder::child_of(&ob);
                let (w_id, w) = nm.fresh_local(c.nat_type.clone());
                let body = c.eq_int(
                    c.neg(c.add(a_lit.clone(), c.of_nat(w.clone()))),
                    c.add(c.neg(a_lit.clone()), c.neg(c.of_nat(w))),
                );
                let lam = nm.mk_lam(w_id, BinderInfo::Default, c.nat_type.clone(), body);
                nm.finish_child(lam)
            };
            // n = 0: symm (snn_zero_succ j).
            // goal: Eq Int (negSucc j) (subNatNat 0 (succ j))
            let n0 = {
                let snn = Expr::app(
                    Expr::app(c.int_sub_nat_nat.clone(), c.nat_zero.clone()),
                    c.succ(j.clone()),
                );
                c.symm_int(snn, c.neg_succ(j.clone()), c.snn_zero_succ(j.clone()))
            };
            // n = succ p: congrArg (fun x => neg (ofNat x)) (congrArg succ (succ_add j p)).
            let nsucc = {
                let mut spb = EnvDeclBuilder::child_of(&ob);
                let (p_id, p) = spb.fresh_local(c.nat_type.clone());
                let ih2_ty = c.eq_int(
                    c.neg(c.add(a_lit.clone(), c.of_nat(p.clone()))),
                    c.add(c.neg(a_lit.clone()), c.neg(c.of_nat(p.clone()))),
                );
                let (ih2_id, _ih2) = spb.fresh_local(ih2_ty.clone());
                // hsucc : succ ((succ j) + p) = succ (succ (j + p))
                //   via congrArg succ (succ_add j p), where succ_add j p : (succ j)+p = succ(j+p).
                let succ_j_plus_p = Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Nat.add"), vec![]),
                        succ_j.clone(),
                    ),
                    p.clone(),
                );
                let succ_succ_j_plus_p = c.succ(succ_j_plus_p.clone());
                let j_plus_p = Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Nat.add"), vec![]),
                        j.clone(),
                    ),
                    p.clone(),
                );
                let succ_succ_jp = c.succ(c.succ(j_plus_p.clone()));
                // congrArg Nat Nat succ (succ_add j p) : succ((succ j)+p) = succ(succ(j+p))
                let succ_fn = {
                    let mut fb = EnvDeclBuilder::child_of(&spb);
                    let (x_id, x) = fb.fresh_local(c.nat_type.clone());
                    let body = c.succ(x);
                    let lam = fb.mk_lam(x_id, BinderInfo::Default, c.nat_type.clone(), body);
                    fb.finish_child(lam)
                };
                let hsucc = Expr::apps(
                    Expr::const_(
                        Name::from_string("congrArg"),
                        vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
                    ),
                    [
                        c.nat_type.clone(),
                        c.nat_type.clone(),
                        succ_j_plus_p.clone(),
                        c.succ(j_plus_p.clone()),
                        succ_fn,
                        c.succ_add(j.clone(), p.clone()),
                    ],
                );
                // outer: congrArg Nat Int (fun x => neg (ofNat x)) hsucc
                //   : neg (ofNat (succ ((succ j)+p))) = neg (ofNat (succ (succ (j+p))))
                let nfn = neg_of_nat_fn(c, &spb);
                let proof = c.congr_nat_int(succ_succ_j_plus_p, succ_succ_jp, nfn, hsucc);
                let lam_ih = spb.mk_lam(ih2_id, BinderInfo::Default, ih2_ty, proof);
                let lam_p = spb.mk_lam(p_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
                spb.finish_child(lam_p)
            };
            let rec_n = Expr::apps(c.nat_rec.clone(), [n_motive, n0, nsucc, n]);
            let lam = ob.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), rec_n);
            ob.finish_child(lam)
        };

        // inner negSucc leaf: a = ofNat (succ j), b = negSucc n.
        // Reduced goal: Eq Int (neg (subNatNat (succ j) (succ n)))
        //                      (subNatNat (succ n) (succ j))
        // because add (ofNat (succ j)) (negSucc n) = subNatNat (succ j) (succ n)
        // and add (neg (ofNat (succ j))) (neg (negSucc n))
        //       = add (negSucc j) (ofNat (succ n)) = subNatNat (succ n) (succ j).
        // `Int.subNatNat` recurses on its SECOND argument only, so
        // `subNatNat (succ _) (succ _)` is STUCK, not defeq to the dropped-successor
        // form. Bridge through `Int.subNatNat_succ_succ` on both sides:
        //   congrArg neg (subNatNat_succ_succ j n) : neg (snn (S j) (S n)) = neg (snn j n)
        //   neg_subNatNat j n                       : neg (snn j n)         = snn n j
        //   symm (subNatNat_succ_succ n j)          : snn n j               = snn (S n) (S j)
        let on = {
            let mut ob = EnvDeclBuilder::child_of(&sb);
            let (n_id, n) = ob.fresh_local(c.nat_type.clone());
            let snn = |x: Expr, y: Expr| Expr::app(Expr::app(c.int_sub_nat_nat.clone(), x), y);
            let snn_ssjsn = snn(c.succ(j.clone()), c.succ(n.clone())); // subNatNat (S j) (S n)
            let snn_jn = snn(j.clone(), n.clone()); // subNatNat j n
            let snn_nj = snn(n.clone(), j.clone()); // subNatNat n j
            let snn_ssnsj = snn(c.succ(n.clone()), c.succ(j.clone())); // subNatNat (S n) (S j)

            // h1 : neg (snn (S j) (S n)) = neg (snn j n)
            let h1 = c.congr_neg(
                snn_ssjsn.clone(),
                snn_jn.clone(),
                c.snn_succ_succ(j.clone(), n.clone()),
            );
            // h2 : neg (snn j n) = snn n j
            let h2 = c.neg_sub(j.clone(), n.clone());
            // h3 : snn n j = snn (S n) (S j)
            let h3 = c.symm_int(
                snn_ssnsj.clone(),
                snn_nj.clone(),
                c.snn_succ_succ(n.clone(), j.clone()),
            );
            // h2h3 : neg (snn j n) = snn (S n) (S j)
            let h2h3 = c.trans_int(c.neg(snn_jn.clone()), snn_nj, snn_ssnsj.clone(), h2, h3);
            // proof : neg (snn (S j) (S n)) = snn (S n) (S j)
            let proof = c.trans_int(c.neg(snn_ssjsn), c.neg(snn_jn), snn_ssnsj, h1, h2h3);
            let lam = ob.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), proof);
            ob.finish_child(lam)
        };

        let rec_b = Expr::apps(c.int_rec.clone(), [inner_motive, oo, on, bv.clone()]);
        let lam_b = sb.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), rec_b);
        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, lam_b);
        let lam_j = sb.mk_lam(j_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
        sb.finish_child(lam_j)
    };

    let rec_m = Expr::apps(
        c.nat_rec.clone(),
        [nat_motive, zero_branch, succ_branch, m.clone()],
    );
    let lam_m = cb.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), rec_m);
    cb.finish_child(lam_m)
}

/// Outer `negSucc` case: `lambda (m : Nat) => lambda (b : Int) =>
///   @Int.rec.{0} (inner_motive (negSucc m)) oo on b`.
fn build_outer_negsucc_case(c: &IntNegAddConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut cb = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = cb.fresh_local(c.nat_type.clone());
    let a_lit = c.neg_succ(m.clone());
    let (b_id, bv) = cb.fresh_local(c.int_type.clone());
    let inner_motive = build_inner_motive(c, &cb, &a_lit);

    // inner ofNat leaf: lambda (n : Nat) => @Nat.rec.{0} n_motive n0 nsucc n
    let oo = {
        let mut ob = EnvDeclBuilder::child_of(&cb);
        let (n_id, n) = ob.fresh_local(c.nat_type.clone());
        let n_motive = {
            let mut nm = EnvDeclBuilder::child_of(&ob);
            let (w_id, w) = nm.fresh_local(c.nat_type.clone());
            let body = c.eq_int(
                c.neg(c.add(a_lit.clone(), c.of_nat(w.clone()))),
                c.add(c.neg(a_lit.clone()), c.neg(c.of_nat(w))),
            );
            let lam = nm.mk_lam(w_id, BinderInfo::Default, c.nat_type.clone(), body);
            nm.finish_child(lam)
        };
        // n = 0: neg_sub 0 (succ m).
        let n0 = c.neg_sub(c.nat_zero.clone(), c.succ(m.clone()));
        // n = succ p: a = negSucc m, b = ofNat (succ p).
        // Reduced goal: Eq Int (neg (subNatNat (succ p) (succ m)))
        //                      (subNatNat (succ m) (succ p))
        // because add (negSucc m) (ofNat (succ p)) = subNatNat (succ p) (succ m)
        // and add (neg (negSucc m)) (neg (ofNat (succ p)))
        //       = add (ofNat (succ m)) (negSucc p) = subNatNat (succ m) (succ p).
        // Both `subNatNat (succ _) (succ _)` are STUCK (recursion is on the
        // second argument only), so bridge through `Int.subNatNat_succ_succ`:
        //   congrArg neg (subNatNat_succ_succ p m) : neg (snn (S p) (S m)) = neg (snn p m)
        //   neg_subNatNat p m                       : neg (snn p m)         = snn m p
        //   symm (subNatNat_succ_succ m p)          : snn m p               = snn (S m) (S p)
        let nsucc = {
            let mut spb = EnvDeclBuilder::child_of(&ob);
            let (p_id, p) = spb.fresh_local(c.nat_type.clone());
            let ih2_ty = c.eq_int(
                c.neg(c.add(a_lit.clone(), c.of_nat(p.clone()))),
                c.add(c.neg(a_lit.clone()), c.neg(c.of_nat(p.clone()))),
            );
            let (ih2_id, _ih2) = spb.fresh_local(ih2_ty.clone());
            let snn = |x: Expr, y: Expr| Expr::app(Expr::app(c.int_sub_nat_nat.clone(), x), y);
            let snn_spsm = snn(c.succ(p.clone()), c.succ(m.clone())); // subNatNat (S p) (S m)
            let snn_pm = snn(p.clone(), m.clone()); // subNatNat p m
            let snn_mp = snn(m.clone(), p.clone()); // subNatNat m p
            let snn_smsp = snn(c.succ(m.clone()), c.succ(p.clone())); // subNatNat (S m) (S p)

            // h1 : neg (snn (S p) (S m)) = neg (snn p m)
            let h1 = c.congr_neg(
                snn_spsm.clone(),
                snn_pm.clone(),
                c.snn_succ_succ(p.clone(), m.clone()),
            );
            // h2 : neg (snn p m) = snn m p
            let h2 = c.neg_sub(p.clone(), m.clone());
            // h3 : snn m p = snn (S m) (S p)
            let h3 = c.symm_int(
                snn_smsp.clone(),
                snn_mp.clone(),
                c.snn_succ_succ(m.clone(), p.clone()),
            );
            // h2h3 : neg (snn p m) = snn (S m) (S p)
            let h2h3 = c.trans_int(c.neg(snn_pm.clone()), snn_mp, snn_smsp.clone(), h2, h3);
            // proof : neg (snn (S p) (S m)) = snn (S m) (S p)
            let proof = c.trans_int(c.neg(snn_spsm), c.neg(snn_pm), snn_smsp, h1, h2h3);
            let lam_ih = spb.mk_lam(ih2_id, BinderInfo::Default, ih2_ty, proof);
            let lam_p = spb.mk_lam(p_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
            spb.finish_child(lam_p)
        };
        let rec_n = Expr::apps(c.nat_rec.clone(), [n_motive, n0, nsucc, n]);
        let lam = ob.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), rec_n);
        ob.finish_child(lam)
    };

    // inner negSucc leaf: lambda (n : Nat) =>
    //   congrArg ofNat (symm (congrArg succ (succ_add m n))).
    let on = {
        let mut ob = EnvDeclBuilder::child_of(&cb);
        let (n_id, n) = ob.fresh_local(c.nat_type.clone());
        // succ_add m n : (succ m) + n = succ (m + n)
        let succ_m_plus_n = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Nat.add"), vec![]),
                c.succ(m.clone()),
            ),
            n.clone(),
        );
        let m_plus_n = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Nat.add"), vec![]),
                m.clone(),
            ),
            n.clone(),
        );
        let succ_fn = {
            let mut fb = EnvDeclBuilder::child_of(&ob);
            let (x_id, x) = fb.fresh_local(c.nat_type.clone());
            let body = c.succ(x);
            let lam = fb.mk_lam(x_id, BinderInfo::Default, c.nat_type.clone(), body);
            fb.finish_child(lam)
        };
        // congrArg Nat Nat succ (succ_add m n) : succ ((succ m)+n) = succ (succ (m+n))
        let inner_congr = Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
            ),
            [
                c.nat_type.clone(),
                c.nat_type.clone(),
                succ_m_plus_n.clone(),
                c.succ(m_plus_n.clone()),
                succ_fn,
                c.succ_add(m.clone(), n.clone()),
            ],
        );
        // symm : succ (succ (m+n)) = succ ((succ m)+n)  [Eq Nat]
        let succ_succ_mn = c.succ(c.succ(m_plus_n.clone()));
        let succ_succ_m_n = c.succ(succ_m_plus_n.clone());
        let symm_nat = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.symm"),
                vec![Level::succ(Level::zero())],
            ),
            [
                c.nat_type.clone(),
                succ_succ_m_n.clone(),
                succ_succ_mn.clone(),
                inner_congr,
            ],
        );
        // congrArg Nat Int ofNat symm_nat
        //   : ofNat (succ (succ (m+n))) = ofNat (succ ((succ m)+n))
        let proof = c.congr_nat_int(succ_succ_mn, succ_succ_m_n, c.int_of_nat.clone(), symm_nat);
        let lam = ob.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), proof);
        ob.finish_child(lam)
    };

    let rec_b = Expr::apps(c.int_rec.clone(), [inner_motive, oo, on, bv.clone()]);
    let lam_b = cb.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), rec_b);
    let lam_m = cb.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), lam_b);
    cb.finish_child(lam_m)
}

/// Body: `lambda (a b : Int) => @Int.rec.{0} outer_motive outer_ofNat outer_negSucc a b`.
fn build_value(c: &IntNegAddConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (va_id, va) = vb.fresh_local(c.int_type.clone());
    let (vb_id, vbv) = vb.fresh_local(c.int_type.clone());
    let outer_motive = build_outer_motive(c, &vb);
    let outer_ofnat = build_outer_ofnat_case(c, &vb);
    let outer_negsucc = build_outer_negsucc_case(c, &vb);
    let rec_a = Expr::apps(
        c.int_rec.clone(),
        [outer_motive, outer_ofnat, outer_negsucc, va],
    );
    let body = Expr::app(rec_a, vbv);
    let val_raw = vb.mk_lam(vb_id, BinderInfo::Default, c.int_type.clone(), body);
    let val_raw = vb.mk_lam(va_id, BinderInfo::Default, c.int_type.clone(), val_raw);
    vb.finish(val_raw)
}

impl Environment {
    /// Register `Int.neg_add` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int`, `Int.ofNat`,
    ///           `Int.negSucc`, `Int.neg`, `Int.add`, `Int.subNatNat`,
    ///           `Int.rec`.
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.add`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`, `Eq.symm`,
    ///           `Eq.trans`, `congrArg`.
    /// REQUIRES: `Int.neg_subNatNat`, `Int.subNatNat_zero_succ`,
    ///           `Nat.zero_add`, `Nat.succ_add` are registered as constructive
    ///           `Declaration::Theorem`s.
    /// ENSURES: On success, `Int.neg_add` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_int_neg_add_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.neg_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;
        // Constructive dependencies.
        self.register_int_neg_sub_nat_nat_proof()?;
        self.register_int_sub_nat_nat_zero_succ_proof()?;
        self.register_int_sub_nat_nat_succ_succ_proof()?;
        self.register_nat_zero_add_proof()?;
        self.register_nat_succ_add_proof()?;

        let c = IntNegAddConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Nested
        // `@Int.rec.{0}` (outer on `a`, inner on `b`) with `@Nat.rec.{0}`
        // splits on the underlying `Nat` wherever `Int.neg (Int.ofNat _)` is
        // otherwise stuck. The nine leaves close via the constructive
        // `Int.neg_subNatNat`, `Int.subNatNat_zero_succ`, `Nat.zero_add`,
        // `Nat.succ_add` glued with `congrArg` / `Eq.symm` / `Eq.trans` /
        // `Eq.refl`. No `sorry`, no self-reference, no domain-axiom
        // dependency. Replaces the prior `Declaration::Axiom` in
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
    use crate::env::ConstantKind;

    #[test]
    fn test_int_neg_add_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_neg_add_proof()
            .expect("first registration");
        env.register_int_neg_add_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.neg_add"))
            .expect("Int.neg_add should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_neg_add_proof_uses_int_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_neg_add_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.neg_add"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let mut body = value.clone();
        for _ in 0..2 {
            body = match body.kind() {
                ExprKind::Lam(_, _, inner) => (**inner).clone(),
                k => panic!("expected outer lambda, got {:?}", k),
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
                "Int.neg_add proof root must be Int.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Int.rec, ..) at proof root, got {:?}", k),
        }
    }

    #[test]
    fn test_int_neg_add_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_neg_add_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.neg_add"))
            .expect("Int.neg_add is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.neg_add must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }
}
