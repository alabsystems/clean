// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.neg_mul_right : ∀ a b : Int, Eq Int (Int.neg (Int.mul a b)) (Int.mul a (Int.neg b))`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_int_lemmas.rs` with a `Declaration::Theorem` whose proof
//! term is built by a nested `@Int.rec.{0}` case-analysis (outer on `b`,
//! inner on `a`), with the outer `ofNat` case performing an extra
//! `@Nat.rec.{0}` split on the underlying `Nat` (so `Int.neg (Int.ofNat n)`
//! reduces to a constructor and the right-hand `Int.mul a (Int.neg b)`
//! fires).
//!
//! # Proof sketch
//!
//! `Int.neg`, `Int.negOfNat`, `Int.mul` are reducible Definitions (see
//! `algebra_int_neg_mul_left_proof.rs` for the full reduction table).
//! `Nat.mul m n` recurses on its SECOND argument, so `Nat.mul m 0` reduces
//! to `0` definitionally; that is why — unlike the left variant — the
//! `b = ofNat 0` row here closes by pure `@Eq.refl.{1}` with NO
//! `Nat.zero_mul` / `Eq.subst` transport.
//!
//! Two reusable `Nat.rec` helper lemmas (both branches pure `@Eq.refl.{1}`,
//! the inductive hypothesis unused) are built inline and applied:
//!
//! ```text
//! H1 : ∀ k : Nat, Eq Int (Int.neg (Int.negOfNat k)) (Int.ofNat k)
//! H2 : ∀ k : Nat, Eq Int (Int.neg (Int.ofNat k))    (Int.negOfNat k)
//! ```
//!
//! The six leaf goals (3 forms of `b` × 2 inner `a` constructors) close as:
//!
//! ```text
//! b = ofNat 0,      a = ofNat m   : @Eq.refl.{1} Int (ofNat 0)
//! b = ofNat 0,      a = negSucc m : @Eq.refl.{1} Int (ofNat 0)
//! b = ofNat(succ q),a = ofNat m   : H2 (Nat.mul m (succ q))
//! b = ofNat(succ q),a = negSucc m : H1 (Nat.mul (succ m) (succ q))
//! b = negSucc q,    a = ofNat m   : H1 (Nat.mul m (succ q))
//! b = negSucc q,    a = negSucc m : H2 (Nat.mul (succ m) (succ q))
//! ```
//!
//! # Axiom closure
//!
//! The proof term mentions only `Int`, `Int.neg`, `Int.mul`, `Int.ofNat`,
//! `Int.negSucc`, `Int.negOfNat`, `Int.rec`, `Nat`, `Nat.zero`, `Nat.succ`,
//! `Nat.mul`, `Nat.rec`, `Eq`, `Eq.refl` — none of which are
//! `Declaration::Axiom`. Therefore `env.axiom_deps("Int.neg_mul_right")`
//! is empty and
//! `env.proof_quality("Int.neg_mul_right") == ProofQuality::Constructive`.
//!
//! Tracks #3604. Sibling proofs:
//! - `algebra_int_neg_mul_left_proof.rs` (mirror, `(-a) * b`).
//! - `algebra_int_mul_comm_proof.rs` (nested Int.rec — same shape).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntNegMulRightConsts {
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
}

impl IntNegMulRightConsts {
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
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![type1]),
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

    fn neg_succ(&self, n: Expr) -> Expr {
        Expr::app(self.int_neg_succ.clone(), n)
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }

    fn nmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.nat_mul.clone(), a), b)
    }

    fn neg_of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_neg_of_nat.clone(), n)
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }

    fn refl_int(&self, t: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.int_type.clone(), t])
    }
}

/// Build `∀ a b : Int, Eq Int (Int.neg (Int.mul a b)) (Int.mul a (Int.neg b))`.
fn build_type(c: &IntNegMulRightConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bv_id, bv) = b.fresh_local(c.int_type.clone());
    let lhs = c.neg(c.mul(a.clone(), bv.clone()));
    let rhs = c.mul(a, c.neg(bv));
    let concl = c.eq_int(lhs, rhs);
    let ty_raw = b.mk_pi(bv_id, BinderInfo::Default, c.int_type.clone(), concl);
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), ty_raw);
    b.finish(ty_raw)
}

/// Helper `H1 : ∀ k : Nat, Eq Int (Int.neg (Int.negOfNat k)) (Int.ofNat k)`.
fn build_h1(c: &IntNegMulRightConsts, parent: &EnvDeclBuilder) -> Expr {
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
fn build_h2(c: &IntNegMulRightConsts, parent: &EnvDeclBuilder) -> Expr {
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

/// Inner `Int.rec` motive for a fixed `b : Int` (passed as `b_lit`):
/// `λ (a : Int) => Eq Int (Int.neg (Int.mul a b)) (Int.mul a (Int.neg b))`.
fn build_inner_motive(c: &IntNegMulRightConsts, parent: &EnvDeclBuilder, b_lit: &Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (a_id, a) = mb.fresh_local(c.int_type.clone());
    let lhs = c.neg(c.mul(a.clone(), b_lit.clone()));
    let rhs = c.mul(a, c.neg(b_lit.clone()));
    let body = c.eq_int(lhs, rhs);
    let lam = mb.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), body);
    mb.finish_child(lam)
}

/// Outer `ofNat` case (split `b`'s payload `n` into zero / succ).
fn build_outer_ofnat_case(
    c: &IntNegMulRightConsts,
    parent: &EnvDeclBuilder,
    h1: &Expr,
    h2: &Expr,
) -> Expr {
    let mut cb = EnvDeclBuilder::child_of(parent);
    let (n_id, n) = cb.fresh_local(c.nat_type.clone());

    // inner Nat.rec motive: λ (w : Nat) => ∀ a : Int,
    //   Eq Int (neg (mul a (ofNat w))) (mul a (neg (ofNat w)))
    let nat_motive = {
        let mut mb = EnvDeclBuilder::child_of(&cb);
        let (w_id, w) = mb.fresh_local(c.nat_type.clone());
        let of_w = c.of_nat(w);
        let (a_id, a) = mb.fresh_local(c.int_type.clone());
        let body = c.eq_int(c.neg(c.mul(a.clone(), of_w.clone())), c.mul(a, c.neg(of_w)));
        let pi = mb.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), body);
        let lam = mb.mk_lam(w_id, BinderInfo::Default, c.nat_type.clone(), pi);
        mb.finish_child(lam)
    };

    // zero case (b = ofNat 0): λ (a : Int) => @Int.rec.{0} (inner_motive (ofNat 0)) leaf_oo leaf_no a
    // both leaves close by pure refl (m*0 reduces to 0 definitionally).
    let zero_case = {
        let mut zb = EnvDeclBuilder::child_of(&cb);
        let (a_id, a) = zb.fresh_local(c.int_type.clone());
        let b_lit = c.of_nat(c.nat_zero.clone());
        let inner_motive = build_inner_motive(c, &zb, &b_lit);
        // leaf for a = ofNat m: λ m => @Eq.refl.{1} Int (ofNat 0)
        let leaf_oo = {
            let mut ob = EnvDeclBuilder::child_of(&zb);
            let (m_id, _m) = ob.fresh_local(c.nat_type.clone());
            let refl = c.refl_int(c.of_nat(c.nat_zero.clone()));
            let lam = ob.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), refl);
            ob.finish_child(lam)
        };
        // leaf for a = negSucc m: λ m => @Eq.refl.{1} Int (ofNat 0)
        let leaf_no = {
            let mut ob = EnvDeclBuilder::child_of(&zb);
            let (m_id, _m) = ob.fresh_local(c.nat_type.clone());
            let refl = c.refl_int(c.of_nat(c.nat_zero.clone()));
            let lam = ob.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), refl);
            ob.finish_child(lam)
        };
        let rec_app = Expr::apps(
            c.int_rec.clone(),
            [inner_motive, leaf_oo, leaf_no, a.clone()],
        );
        let lam = zb.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), rec_app);
        zb.finish_child(lam)
    };

    // succ case (b = ofNat (succ q)): λ (q : Nat) => λ (_ih : motive q) =>
    //   λ (a : Int) => @Int.rec.{0} (inner_motive (ofNat (succ q))) leaf_oo leaf_no a
    // leaf_oo (a = ofNat m)   : λ m => H2 (Nat.mul m (succ q))
    // leaf_no (a = negSucc m) : λ m => H1 (Nat.mul (succ m) (succ q))
    let succ_case = {
        let mut sb = EnvDeclBuilder::child_of(&cb);
        let (q_id, q) = sb.fresh_local(c.nat_type.clone());
        let succ_q = c.succ(q.clone());
        let ih_ty = {
            let mut ib = EnvDeclBuilder::child_of(&sb);
            let of_q = c.of_nat(q.clone());
            let (a_id, a) = ib.fresh_local(c.int_type.clone());
            let body = c.eq_int(c.neg(c.mul(a.clone(), of_q.clone())), c.mul(a, c.neg(of_q)));
            let pi = ib.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), body);
            ib.finish_child(pi)
        };
        let (ih_id, _ih) = sb.fresh_local(ih_ty.clone());

        let b_lit = c.of_nat(succ_q.clone());
        let (a_id, a) = sb.fresh_local(c.int_type.clone());
        let inner_motive = build_inner_motive(c, &sb, &b_lit);

        let leaf_oo = {
            let mut ob = EnvDeclBuilder::child_of(&sb);
            let (m_id, m) = ob.fresh_local(c.nat_type.clone());
            let prod = c.nmul(m.clone(), succ_q.clone());
            let app = Expr::app(h2.clone(), prod);
            let lam = ob.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), app);
            ob.finish_child(lam)
        };
        let leaf_no = {
            let mut ob = EnvDeclBuilder::child_of(&sb);
            let (m_id, m) = ob.fresh_local(c.nat_type.clone());
            let prod = c.nmul(c.succ(m.clone()), succ_q.clone());
            let app = Expr::app(h1.clone(), prod);
            let lam = ob.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), app);
            ob.finish_child(lam)
        };

        let rec_app = Expr::apps(
            c.int_rec.clone(),
            [inner_motive, leaf_oo, leaf_no, a.clone()],
        );
        let lam_a = sb.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), rec_app);
        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, lam_a);
        let lam_q = sb.mk_lam(q_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
        sb.finish_child(lam_q)
    };

    let rec_app = Expr::apps(
        c.nat_rec.clone(),
        [nat_motive, zero_case, succ_case, n.clone()],
    );
    let lam = cb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
    cb.finish_child(lam)
}

/// Outer `negSucc` case (b = negSucc q):
/// leaf_oo (a = ofNat m)   : λ m => H1 (Nat.mul m (succ q))
/// leaf_no (a = negSucc m) : λ m => H2 (Nat.mul (succ m) (succ q))
fn build_outer_negsucc_case(
    c: &IntNegMulRightConsts,
    parent: &EnvDeclBuilder,
    h1: &Expr,
    h2: &Expr,
) -> Expr {
    let mut cb = EnvDeclBuilder::child_of(parent);
    let (q_id, q) = cb.fresh_local(c.nat_type.clone());
    let succ_q = c.succ(q.clone());
    let b_lit = c.neg_succ(q.clone());
    let (a_id, a) = cb.fresh_local(c.int_type.clone());
    let inner_motive = build_inner_motive(c, &cb, &b_lit);

    let leaf_oo = {
        let mut ob = EnvDeclBuilder::child_of(&cb);
        let (m_id, m) = ob.fresh_local(c.nat_type.clone());
        let prod = c.nmul(m.clone(), succ_q.clone());
        let app = Expr::app(h1.clone(), prod);
        let lam = ob.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), app);
        ob.finish_child(lam)
    };
    let leaf_no = {
        let mut ob = EnvDeclBuilder::child_of(&cb);
        let (m_id, m) = ob.fresh_local(c.nat_type.clone());
        let prod = c.nmul(c.succ(m.clone()), succ_q.clone());
        let app = Expr::app(h2.clone(), prod);
        let lam = ob.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), app);
        ob.finish_child(lam)
    };

    let rec_app = Expr::apps(
        c.int_rec.clone(),
        [inner_motive, leaf_oo, leaf_no, a.clone()],
    );
    let lam_a = cb.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), rec_app);
    let lam_q = cb.mk_lam(q_id, BinderInfo::Default, c.nat_type.clone(), lam_a);
    cb.finish_child(lam_q)
}

/// Outer motive: `λ (y : Int) => ∀ a : Int,
///   Eq Int (Int.neg (Int.mul a y)) (Int.mul a (Int.neg y))`.
fn build_outer_motive(c: &IntNegMulRightConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (y_id, y) = mb.fresh_local(c.int_type.clone());
    let (a_id, a) = mb.fresh_local(c.int_type.clone());
    let body = c.eq_int(
        c.neg(c.mul(a.clone(), y.clone())),
        c.mul(a, c.neg(y.clone())),
    );
    let pi = mb.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), body);
    let lam = mb.mk_lam(y_id, BinderInfo::Default, c.int_type.clone(), pi);
    mb.finish_child(lam)
}

/// Body: `λ (a b : Int) => @Int.rec.{0} outer_motive outer_ofNat outer_negSucc b a`.
fn build_value(c: &IntNegMulRightConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (va_id, va) = vb.fresh_local(c.int_type.clone());
    let (vb_id, vbv) = vb.fresh_local(c.int_type.clone());
    let h1 = build_h1(c, &vb);
    let h2 = build_h2(c, &vb);
    let outer_motive = build_outer_motive(c, &vb);
    let outer_ofnat = build_outer_ofnat_case(c, &vb, &h1, &h2);
    let outer_negsucc = build_outer_negsucc_case(c, &vb, &h1, &h2);
    // Recurse on b (the second binder), then apply to a.
    let rec_app_b = Expr::apps(
        c.int_rec.clone(),
        [outer_motive, outer_ofnat, outer_negsucc, vbv],
    );
    let body = Expr::app(rec_app_b, va);
    let val_raw = vb.mk_lam(vb_id, BinderInfo::Default, c.int_type.clone(), body);
    let val_raw = vb.mk_lam(va_id, BinderInfo::Default, c.int_type.clone(), val_raw);
    vb.finish(val_raw)
}

impl Environment {
    /// Register `Int.neg_mul_right` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int`, `Int.ofNat`,
    ///           `Int.negSucc`, `Int.negOfNat`, `Int.neg`, `Int.mul`,
    ///           `Int.rec`.
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.mul`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`.
    /// ENSURES: On success, `Int.neg_mul_right` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_int_neg_mul_right_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.neg_mul_right");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;

        let c = IntNegMulRightConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Nested
        // `@Int.rec.{0}` induction (outer on `b`, inner on `a`), with the
        // outer `ofNat` case further splitting the underlying `Nat` via
        // `@Nat.rec.{0}` so that `Int.neg (Int.ofNat n)` reduces to a
        // constructor. Two inline `@Nat.rec.{0}` helper lemmas (both
        // branches pure `@Eq.refl.{1}`) discharge the `b ≠ ofNat 0` leaves;
        // the `b = ofNat 0` leaves close by pure `@Eq.refl.{1}` because
        // `Nat.mul _ 0` reduces to `0` definitionally (`Nat.mul` recurses on
        // its second argument). No `sorry`, no self-reference, no
        // domain-axiom dependency. Replaces the prior `Declaration::Axiom`
        // in `data_types_int_lemmas.rs::init_int_arith_lemmas`.
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
    fn test_int_neg_mul_right_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_neg_mul_right_proof()
            .expect("first registration");
        env.register_int_neg_mul_right_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.neg_mul_right"))
            .expect("Int.neg_mul_right should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_neg_mul_right_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_neg_mul_right_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.neg_mul_right"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        assert!(
            matches!(value.kind(), ExprKind::Lam(..)),
            "Int.neg_mul_right proof must be a λ-abstraction, got {:?}",
            value.kind()
        );
    }

    #[test]
    fn test_int_neg_mul_right_proof_uses_int_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_neg_mul_right_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.neg_mul_right"))
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
                "Int.neg_mul_right proof root must be Int.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Int.rec, ..) at proof root, got {:?}", k),
        }
    }

    #[test]
    fn test_int_neg_mul_right_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_neg_mul_right_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.neg_mul_right"))
            .expect("Int.neg_mul_right is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.neg_mul_right must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }
}
