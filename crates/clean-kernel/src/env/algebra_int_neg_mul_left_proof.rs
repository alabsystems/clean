// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.neg_mul_left : ∀ a b : Int, Eq Int (Int.neg (Int.mul a b)) (Int.mul (Int.neg a) b)`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_int_lemmas.rs` with a `Declaration::Theorem` whose proof
//! term is built by a nested `@Int.rec.{0}` case-analysis (outer on `a`,
//! inner on `b`), with the outer `ofNat` case performing an extra
//! `@Nat.rec.{0}` split on the underlying `Nat` (so `Int.neg (Int.ofNat m)`
//! reduces to a constructor and the right-hand `Int.mul` fires).
//!
//! # Proof sketch
//!
//! `Int.neg`, `Int.negOfNat`, `Int.mul` are reducible Definitions:
//!
//! ```text
//! Int.neg (ofNat 0)        = ofNat 0
//! Int.neg (ofNat (succ k)) = negSucc k
//! Int.neg (negSucc k)      = ofNat (succ k)
//! Int.negOfNat 0           = ofNat 0
//! Int.negOfNat (succ k)    = negSucc k
//! Int.mul (ofNat m)   (ofNat n)   = ofNat    (Nat.mul m n)
//! Int.mul (ofNat m)   (negSucc n) = negOfNat (Nat.mul m (succ n))
//! Int.mul (negSucc m) (ofNat n)   = negOfNat (Nat.mul (succ m) n)
//! Int.mul (negSucc m) (negSucc n) = ofNat    (Nat.mul (succ m) (succ n))
//! ```
//!
//! `Int.neg (Int.mul a b)` only reduces once `a` (and, after the inner
//! `Int.rec`, `b`) is a constructor, and the right-hand `Int.mul
//! (Int.neg a) b` only reduces once `Int.neg a` is a constructor — which,
//! for `a = ofNat m`, requires knowing whether `m` is `zero` or `succ`.
//! Hence the outer `ofNat` case splits `m` with `Nat.rec`.
//!
//! Two reusable `Nat.rec` helper lemmas (both branches pure `@Eq.refl.{1}`,
//! the inductive hypothesis unused) are built inline and applied:
//!
//! ```text
//! H1 : ∀ k : Nat, Eq Int (Int.neg (Int.negOfNat k)) (Int.ofNat k)
//! H2 : ∀ k : Nat, Eq Int (Int.neg (Int.ofNat k))    (Int.negOfNat k)
//! ```
//!
//! - `H1 0`: `neg (negOfNat 0) = neg (ofNat 0) = ofNat 0`, matches `ofNat 0`.
//! - `H1 (succ j)`: `neg (negOfNat (succ j)) = neg (negSucc j) = ofNat (succ j)`.
//! - `H2 0`: `neg (ofNat 0) = ofNat 0`, matches `negOfNat 0 = ofNat 0`.
//! - `H2 (succ j)`: `neg (ofNat (succ j)) = negSucc j`, matches
//!   `negOfNat (succ j) = negSucc j`.
//!
//! The six leaf goals (3 forms of `a` × 2 inner `b` constructors) close as:
//!
//! ```text
//! a = ofNat 0,      b = ofNat n   : Eq.subst (Nat.zero_mul n)        on  λz. neg(ofNat z)=ofNat z
//! a = ofNat 0,      b = negSucc n : Eq.subst (Nat.zero_mul (succ n)) on  λz. neg(negOfNat z)=negOfNat z
//! a = ofNat(succ p),b = ofNat n   : H2 (Nat.mul (succ p) n)
//! a = ofNat(succ p),b = negSucc n : H1 (Nat.mul (succ p) (succ n))
//! a = negSucc p,    b = ofNat n   : H1 (Nat.mul (succ p) n)
//! a = negSucc p,    b = negSucc n : H2 (Nat.mul (succ p) (succ n))
//! ```
//!
//! For `a = ofNat 0`, `Int.mul (ofNat 0) (ofNat n) = ofNat (Nat.mul 0 n)`
//! does not reduce further (`Nat.mul` recurses on its second argument), so
//! `neg (ofNat (0*n)) = ofNat (0*n)` is NOT definitional; it is discharged
//! by transporting the literal `@Eq.refl.{1} Int (ofNat 0)` along
//! `Nat.zero_mul` via `@Eq.subst.{1}`.
//!
//! # Axiom closure
//!
//! The proof term mentions only `Int`, `Int.neg`, `Int.mul`, `Int.ofNat`,
//! `Int.negSucc`, `Int.negOfNat`, `Int.rec`, `Nat`, `Nat.zero`, `Nat.succ`,
//! `Nat.mul`, `Nat.rec`, `Eq`, `Eq.refl`, `Eq.symm`, `Eq.subst`
//! (kernel machinery / constructors / reducible Definitions / constructive
//! Theorems) and the constructive `Declaration::Theorem` `Nat.zero_mul`
//! (#3551). None are `Declaration::Axiom`, so
//! `env.axiom_deps("Int.neg_mul_left")` is empty and
//! `env.proof_quality("Int.neg_mul_left") == ProofQuality::Constructive`.
//!
//! Tracks #3604. Sibling proofs:
//! - `algebra_int_mul_comm_proof.rs` (nested Int.rec + congrArg — same shape).
//! - `algebra_int_neg_mul_right_proof.rs` (mirror, `a * (-b)`).
//! - `algebra_int_neg_neg_proof.rs` (Int.neg_neg via Int.rec / Nat.rec).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntNegMulLeftConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_mul: Expr,
    int_neg: Expr,
    int_mul: Expr,
    int_of_nat: Expr,
    int_neg_succ: Expr,
    int_neg_of_nat: Expr,
    int_rec: Expr,
    nat_rec: Expr,
    eq_const: Expr,
    eq_refl: Expr,
    eq_symm: Expr,
    eq_subst: Expr,
    nat_zero_mul: Expr,
}

impl IntNegMulLeftConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_mul: Expr::const_(Name::from_string("Nat.mul"), vec![]),
            int_neg: Expr::const_(Name::from_string("Int.neg"), vec![]),
            int_mul: Expr::const_(Name::from_string("Int.mul"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            int_neg_of_nat: Expr::const_(Name::from_string("Int.negOfNat"), vec![]),
            int_rec: Expr::const_(Name::from_string("Int.rec"), vec![Level::zero()]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![type1]),
            nat_zero_mul: Expr::const_(Name::from_string("Nat.zero_mul"), vec![]),
        }
    }

    fn neg(&self, x: Expr) -> Expr {
        Expr::app(self.int_neg.clone(), x)
    }

    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.int_mul.clone(), a), b)
    }

    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }

    fn neg_of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_neg_of_nat.clone(), n)
    }

    fn neg_succ(&self, n: Expr) -> Expr {
        Expr::app(self.int_neg_succ.clone(), n)
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }

    fn nmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.nat_mul.clone(), a), b)
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }

    fn refl_int(&self, t: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.int_type.clone(), t])
    }

    fn symm_nat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.nat_type.clone(), a, b, h])
    }

    fn subst_nat(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_motive_a: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.nat_type.clone(), motive, a, b, h_eq, h_motive_a],
        )
    }
}

/// Build `∀ a b : Int, Eq Int (Int.neg (Int.mul a b)) (Int.mul (Int.neg a) b)`.
fn build_type(c: &IntNegMulLeftConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bv_id, bv) = b.fresh_local(c.int_type.clone());
    let lhs = c.neg(c.mul(a.clone(), bv.clone()));
    let rhs = c.mul(c.neg(a), bv);
    let concl = c.eq_int(lhs, rhs);
    let ty_raw = b.mk_pi(bv_id, BinderInfo::Default, c.int_type.clone(), concl);
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), ty_raw);
    b.finish(ty_raw)
}

/// Helper `H1 : ∀ k : Nat, Eq Int (Int.neg (Int.negOfNat k)) (Int.ofNat k)`.
fn build_h1(c: &IntNegMulLeftConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut hb = EnvDeclBuilder::child_of(parent);
    let (k_id, k) = hb.fresh_local(c.nat_type.clone());

    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&hb);
        let (z_id, z) = mb.fresh_local(c.nat_type.clone());
        let body = c.eq_int(c.neg(c.neg_of_nat(z.clone())), c.of_nat(z));
        let lam = mb.mk_lam(z_id, BinderInfo::Default, c.nat_type.clone(), body);
        mb.finish_child(lam)
    };

    let zero_case = c.refl_int(c.of_nat(c.nat_zero.clone()));

    let succ_case = {
        let mut sb = EnvDeclBuilder::child_of(&hb);
        let (j_id, j) = sb.fresh_local(c.nat_type.clone());
        let ih_ty = c.eq_int(c.neg(c.neg_of_nat(j.clone())), c.of_nat(j.clone()));
        let (ih_id, _ih) = sb.fresh_local(ih_ty.clone());
        let refl = c.refl_int(c.of_nat(c.succ(j.clone())));
        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, refl);
        let lam_j = sb.mk_lam(j_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
        sb.finish_child(lam_j)
    };

    let rec_app = Expr::apps(c.nat_rec.clone(), [motive, zero_case, succ_case, k]);
    let lam = hb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
    hb.finish_child(lam)
}

/// Helper `H2 : ∀ k : Nat, Eq Int (Int.neg (Int.ofNat k)) (Int.negOfNat k)`.
fn build_h2(c: &IntNegMulLeftConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut hb = EnvDeclBuilder::child_of(parent);
    let (k_id, k) = hb.fresh_local(c.nat_type.clone());

    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&hb);
        let (z_id, z) = mb.fresh_local(c.nat_type.clone());
        let body = c.eq_int(c.neg(c.of_nat(z.clone())), c.neg_of_nat(z));
        let lam = mb.mk_lam(z_id, BinderInfo::Default, c.nat_type.clone(), body);
        mb.finish_child(lam)
    };

    let zero_case = c.refl_int(c.of_nat(c.nat_zero.clone()));

    let succ_case = {
        let mut sb = EnvDeclBuilder::child_of(&hb);
        let (j_id, j) = sb.fresh_local(c.nat_type.clone());
        let ih_ty = c.eq_int(c.neg(c.of_nat(j.clone())), c.neg_of_nat(j.clone()));
        let (ih_id, _ih) = sb.fresh_local(ih_ty.clone());
        let refl = c.refl_int(c.neg_succ(j.clone()));
        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, refl);
        let lam_j = sb.mk_lam(j_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
        sb.finish_child(lam_j)
    };

    let rec_app = Expr::apps(c.nat_rec.clone(), [motive, zero_case, succ_case, k]);
    let lam = hb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
    hb.finish_child(lam)
}

/// Inner `Int.rec` motive for a fixed `a : Int` (passed as `a_lit`):
/// `λ (b : Int) => Eq Int (Int.neg (Int.mul a b)) (Int.mul (Int.neg a) b)`.
fn build_inner_motive(c: &IntNegMulLeftConsts, parent: &EnvDeclBuilder, a_lit: &Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (b_id, bv) = mb.fresh_local(c.int_type.clone());
    let lhs = c.neg(c.mul(a_lit.clone(), bv.clone()));
    let rhs = c.mul(c.neg(a_lit.clone()), bv);
    let body = c.eq_int(lhs, rhs);
    let lam = mb.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), body);
    mb.finish_child(lam)
}

/// Leaf for `a = ofNat 0`, inner `b = ofNat n`.
fn build_zero_ofnat_leaf(c: &IntNegMulLeftConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut lb = EnvDeclBuilder::child_of(parent);
    let (n_id, n) = lb.fresh_local(c.nat_type.clone());

    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&lb);
        let (z_id, z) = mb.fresh_local(c.nat_type.clone());
        let body = c.eq_int(c.neg(c.of_nat(z.clone())), c.of_nat(z));
        let lam = mb.mk_lam(z_id, BinderInfo::Default, c.nat_type.clone(), body);
        mb.finish_child(lam)
    };

    let prod = c.nmul(c.nat_zero.clone(), n.clone());
    let zm = Expr::app(c.nat_zero_mul.clone(), n.clone());
    let h_eq = c.symm_nat(prod.clone(), c.nat_zero.clone(), zm);
    let base = c.refl_int(c.of_nat(c.nat_zero.clone()));
    let subst = c.subst_nat(motive, c.nat_zero.clone(), prod, h_eq, base);
    let lam = lb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), subst);
    lb.finish_child(lam)
}

/// Leaf for `a = ofNat 0`, inner `b = negSucc n`.
fn build_zero_negsucc_leaf(c: &IntNegMulLeftConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut lb = EnvDeclBuilder::child_of(parent);
    let (n_id, n) = lb.fresh_local(c.nat_type.clone());

    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&lb);
        let (z_id, z) = mb.fresh_local(c.nat_type.clone());
        let body = c.eq_int(c.neg(c.neg_of_nat(z.clone())), c.neg_of_nat(z));
        let lam = mb.mk_lam(z_id, BinderInfo::Default, c.nat_type.clone(), body);
        mb.finish_child(lam)
    };

    let succ_n = c.succ(n.clone());
    let prod = c.nmul(c.nat_zero.clone(), succ_n.clone());
    let zm = Expr::app(c.nat_zero_mul.clone(), succ_n);
    let h_eq = c.symm_nat(prod.clone(), c.nat_zero.clone(), zm);
    let base = c.refl_int(c.of_nat(c.nat_zero.clone()));
    let subst = c.subst_nat(motive, c.nat_zero.clone(), prod, h_eq, base);
    let lam = lb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), subst);
    lb.finish_child(lam)
}

/// Outer `ofNat` case.
fn build_outer_ofnat_case(
    c: &IntNegMulLeftConsts,
    parent: &EnvDeclBuilder,
    h1: &Expr,
    h2: &Expr,
) -> Expr {
    let mut cb = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = cb.fresh_local(c.nat_type.clone());

    let nat_motive = {
        let mut mb = EnvDeclBuilder::child_of(&cb);
        let (w_id, w) = mb.fresh_local(c.nat_type.clone());
        let of_w = c.of_nat(w);
        let (b_id, bv) = mb.fresh_local(c.int_type.clone());
        let body = c.eq_int(
            c.neg(c.mul(of_w.clone(), bv.clone())),
            c.mul(c.neg(of_w), bv),
        );
        let pi = mb.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), body);
        let lam = mb.mk_lam(w_id, BinderInfo::Default, c.nat_type.clone(), pi);
        mb.finish_child(lam)
    };

    let zero_case = {
        let mut zb = EnvDeclBuilder::child_of(&cb);
        let (b_id, bv) = zb.fresh_local(c.int_type.clone());
        let a_lit = c.of_nat(c.nat_zero.clone());
        let inner_motive = build_inner_motive(c, &zb, &a_lit);
        let leaf_oo = build_zero_ofnat_leaf(c, &zb);
        let leaf_on = build_zero_negsucc_leaf(c, &zb);
        let rec_app = Expr::apps(
            c.int_rec.clone(),
            [inner_motive, leaf_oo, leaf_on, bv.clone()],
        );
        let lam = zb.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), rec_app);
        zb.finish_child(lam)
    };

    let succ_case = {
        let mut sb = EnvDeclBuilder::child_of(&cb);
        let (p_id, p) = sb.fresh_local(c.nat_type.clone());
        let succ_p = c.succ(p.clone());
        let ih_ty = {
            let mut ib = EnvDeclBuilder::child_of(&sb);
            let of_p = c.of_nat(p.clone());
            let (b_id, bv) = ib.fresh_local(c.int_type.clone());
            let body = c.eq_int(
                c.neg(c.mul(of_p.clone(), bv.clone())),
                c.mul(c.neg(of_p), bv),
            );
            let pi = ib.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), body);
            ib.finish_child(pi)
        };
        let (ih_id, _ih) = sb.fresh_local(ih_ty.clone());

        let a_lit = c.of_nat(succ_p.clone());
        let (b_id, bv) = sb.fresh_local(c.int_type.clone());
        let inner_motive = build_inner_motive(c, &sb, &a_lit);

        let leaf_oo = {
            let mut ob = EnvDeclBuilder::child_of(&sb);
            let (n_id, n) = ob.fresh_local(c.nat_type.clone());
            let prod = c.nmul(succ_p.clone(), n.clone());
            let app = Expr::app(h2.clone(), prod);
            let lam = ob.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), app);
            ob.finish_child(lam)
        };
        let leaf_on = {
            let mut ob = EnvDeclBuilder::child_of(&sb);
            let (n_id, n) = ob.fresh_local(c.nat_type.clone());
            let prod = c.nmul(succ_p.clone(), c.succ(n.clone()));
            let app = Expr::app(h1.clone(), prod);
            let lam = ob.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), app);
            ob.finish_child(lam)
        };

        let rec_app = Expr::apps(
            c.int_rec.clone(),
            [inner_motive, leaf_oo, leaf_on, bv.clone()],
        );
        let lam_b = sb.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), rec_app);
        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, lam_b);
        let lam_p = sb.mk_lam(p_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
        sb.finish_child(lam_p)
    };

    let rec_app = Expr::apps(
        c.nat_rec.clone(),
        [nat_motive, zero_case, succ_case, m.clone()],
    );
    let lam = cb.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
    cb.finish_child(lam)
}

/// Outer `negSucc` case (a = negSucc p).
fn build_outer_negsucc_case(
    c: &IntNegMulLeftConsts,
    parent: &EnvDeclBuilder,
    h1: &Expr,
    h2: &Expr,
) -> Expr {
    let mut cb = EnvDeclBuilder::child_of(parent);
    let (p_id, p) = cb.fresh_local(c.nat_type.clone());
    let succ_p = c.succ(p.clone());
    let a_lit = c.neg_succ(p.clone());
    let (b_id, bv) = cb.fresh_local(c.int_type.clone());
    let inner_motive = build_inner_motive(c, &cb, &a_lit);

    let leaf_no = {
        let mut ob = EnvDeclBuilder::child_of(&cb);
        let (n_id, n) = ob.fresh_local(c.nat_type.clone());
        let prod = c.nmul(succ_p.clone(), n.clone());
        let app = Expr::app(h1.clone(), prod);
        let lam = ob.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), app);
        ob.finish_child(lam)
    };
    let leaf_nn = {
        let mut ob = EnvDeclBuilder::child_of(&cb);
        let (n_id, n) = ob.fresh_local(c.nat_type.clone());
        let prod = c.nmul(succ_p.clone(), c.succ(n.clone()));
        let app = Expr::app(h2.clone(), prod);
        let lam = ob.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), app);
        ob.finish_child(lam)
    };

    let rec_app = Expr::apps(
        c.int_rec.clone(),
        [inner_motive, leaf_no, leaf_nn, bv.clone()],
    );
    let lam_b = cb.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), rec_app);
    let lam_p = cb.mk_lam(p_id, BinderInfo::Default, c.nat_type.clone(), lam_b);
    cb.finish_child(lam_p)
}

/// Outer motive: `λ (x : Int) => ∀ b : Int,
///   Eq Int (Int.neg (Int.mul x b)) (Int.mul (Int.neg x) b)`.
fn build_outer_motive(c: &IntNegMulLeftConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = mb.fresh_local(c.int_type.clone());
    let (b_id, bv) = mb.fresh_local(c.int_type.clone());
    let body = c.eq_int(
        c.neg(c.mul(x.clone(), bv.clone())),
        c.mul(c.neg(x.clone()), bv),
    );
    let pi = mb.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), body);
    let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), pi);
    mb.finish_child(lam)
}

/// Body: `λ (a b : Int) => @Int.rec.{0} outer_motive outer_ofNat outer_negSucc a b`.
fn build_value(c: &IntNegMulLeftConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (va_id, va) = vb.fresh_local(c.int_type.clone());
    let (vb_id, vbv) = vb.fresh_local(c.int_type.clone());
    let h1 = build_h1(c, &vb);
    let h2 = build_h2(c, &vb);
    let outer_motive = build_outer_motive(c, &vb);
    let outer_ofnat = build_outer_ofnat_case(c, &vb, &h1, &h2);
    let outer_negsucc = build_outer_negsucc_case(c, &vb, &h1, &h2);
    let rec_app_a = Expr::apps(
        c.int_rec.clone(),
        [outer_motive, outer_ofnat, outer_negsucc, va],
    );
    let body = Expr::app(rec_app_a, vbv);
    let val_raw = vb.mk_lam(vb_id, BinderInfo::Default, c.int_type.clone(), body);
    let val_raw = vb.mk_lam(va_id, BinderInfo::Default, c.int_type.clone(), val_raw);
    vb.finish(val_raw)
}

impl Environment {
    /// Register `Int.neg_mul_left` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int`, `Int.ofNat`,
    ///           `Int.negSucc`, `Int.negOfNat`, `Int.neg`, `Int.mul`,
    ///           `Int.rec`.
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.mul`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`,
    ///           `Eq.symm`, `Eq.subst`.
    /// REQUIRES: `Nat.zero_mul` is registered as `Declaration::Theorem`
    ///           (constructive — see `register_nat_zero_mul_proof`).
    /// ENSURES: On success, `Int.neg_mul_left` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_int_neg_mul_left_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.neg_mul_left");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;
        self.register_nat_zero_mul_proof()?;

        let c = IntNegMulLeftConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Nested
        // `@Int.rec.{0}` induction (outer on `a`, inner on `b`), with the
        // outer `ofNat` case further splitting the underlying `Nat` via
        // `@Nat.rec.{0}` so that `Int.neg (Int.ofNat m)` reduces to a
        // constructor. Two inline `@Nat.rec.{0}` helper lemmas
        // (H1 : neg (negOfNat k) = ofNat k, H2 : neg (ofNat k) = negOfNat k,
        // both branches pure `@Eq.refl.{1}`) discharge the constructor-form
        // leaves; the two `a = ofNat 0` leaves transport
        // `@Eq.refl.{1} Int (ofNat 0)` along the constructive `Nat.zero_mul`
        // via `@Eq.subst.{1}`. No `sorry`, no self-reference, no
        // domain-axiom dependency (`Nat.zero_mul` is itself constructive
        // #3551). Replaces the prior `Declaration::Axiom` in
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
    fn test_int_neg_mul_left_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_neg_mul_left_proof()
            .expect("first registration");
        env.register_int_neg_mul_left_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.neg_mul_left"))
            .expect("Int.neg_mul_left should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_neg_mul_left_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_neg_mul_left_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.neg_mul_left"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        assert!(
            matches!(value.kind(), ExprKind::Lam(..)),
            "Int.neg_mul_left proof must be a λ-abstraction, got {:?}",
            value.kind()
        );
    }

    #[test]
    fn test_int_neg_mul_left_proof_uses_int_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_neg_mul_left_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.neg_mul_left"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let mut body = value.clone();
        for _ in 0..2 {
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
                "Int.neg_mul_left proof root must be Int.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Int.rec, ..) at proof root, got {:?}", k),
        }
    }

    #[test]
    fn test_int_neg_mul_left_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_neg_mul_left_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.neg_mul_left"))
            .expect("Int.neg_mul_left is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.neg_mul_left must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }
}
