// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.mul_comm : ∀ a b : Int, Eq Int (Int.mul a b) (Int.mul b a)`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_int_lemmas.rs` with a `Declaration::Theorem` whose proof
//! term is built by NESTED induction on `a` (outer `@Int.rec.{0}`) and
//! on `b` (inner `@Int.rec.{0}`).
//!
//! # Proof sketch
//!
//! `Int.mul` is a reducible Definition (see `data_types_arithmetic.rs`)
//! implemented as a 4-case split via two nested `Int.rec`:
//!
//! ```text
//! Int.mul (ofNat m)  (ofNat n)   = ofNat    (Nat.mul m n)
//! Int.mul (ofNat m)  (negSucc n) = negOfNat (Nat.mul m (Nat.succ n))
//! Int.mul (negSucc m) (ofNat n)  = negOfNat (Nat.mul (Nat.succ m) n)
//! Int.mul (negSucc m) (negSucc n) = ofNat   (Nat.mul (Nat.succ m) (Nat.succ n))
//! ```
//!
//! The swapped expressions reduce similarly:
//!
//! ```text
//! Int.mul (ofNat n)   (ofNat m)   = ofNat    (Nat.mul n m)
//! Int.mul (negSucc n) (ofNat m)   = negOfNat (Nat.mul (Nat.succ n) m)
//! Int.mul (ofNat n)   (negSucc m) = negOfNat (Nat.mul n (Nat.succ m))
//! Int.mul (negSucc n) (negSucc m) = ofNat   (Nat.mul (Nat.succ n) (Nat.succ m))
//! ```
//!
//! Per case (applying `Nat.mul_comm` to swap the Nat factors, lifted
//! through `Int.ofNat` or `Int.negOfNat` via `congrArg`):
//! - `ofNat × ofNat`: `Eq (ofNat (m*n)) (ofNat (n*m))` witnessed by
//!   `congrArg Int.ofNat (Nat.mul_comm m n)`.
//! - `ofNat × negSucc`: LHS `negOfNat (m * succ n)`, RHS (negSucc n × ofNat m)
//!   `negOfNat (succ n * m)` — witnessed by
//!   `congrArg Int.negOfNat (Nat.mul_comm m (succ n))`.
//! - `negSucc × ofNat`: symmetric — `congrArg Int.negOfNat (Nat.mul_comm (succ m) n)`.
//! - `negSucc × negSucc`: `Eq (ofNat (succ m * succ n)) (ofNat (succ n * succ m))`
//!   witnessed by `congrArg Int.ofNat (Nat.mul_comm (succ m) (succ n))`.
//!
//! The proof term is
//!
//! ```text
//! λ (a b : Int) =>
//!   @Int.rec.{0} outer_motive outer_ofNat_case outer_negSucc_case a b
//! ```
//!
//! with an inner `@Int.rec.{0}` per outer branch. See the sibling
//! `algebra_int_add_comm_proof.rs` for the exact nested shape.
//!
//! # Axiom closure
//!
//! The proof term mentions:
//! - `Int`, `Int.mul`, `Int.ofNat`, `Int.negSucc`, `Int.negOfNat`,
//!   `Int.rec` (kernel machinery / reducible definitions, none `Axiom`),
//! - `Nat`, `Nat.mul`, `Nat.succ`, `Nat.rec` (kernel machinery),
//! - `Eq`, `congrArg` (kernel Theorems / constructors),
//! - `Nat.mul_comm` (constructive `Declaration::Theorem`, #3604).
//!
//! None are `Declaration::Axiom`, so
//! `env.axiom_deps("Int.mul_comm")` is empty and
//! `env.proof_quality("Int.mul_comm") == ProofQuality::Constructive`.
//!
//! Tracks #3604. Sibling proofs:
//! - `algebra_int_add_comm_proof.rs` (Int.add_comm via nested Int.rec).
//! - `algebra_nat_mul_comm_proof.rs` (#3604, Nat.mul_comm — dependency).
//! - `algebra_int_ofnat_mul_proof.rs` (#3604, Int.ofNat_mul — pure refl).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntMulCommConsts {
    int_type: Expr,
    nat_type: Expr,
    int_mul: Expr,
    int_of_nat: Expr,
    int_neg_succ: Expr,
    int_neg_of_nat: Expr,
    int_rec: Expr,
    nat_mul: Expr,
    nat_succ: Expr,
    eq_const: Expr,
    congr_arg: Expr,
    nat_mul_comm: Expr,
}

impl IntMulCommConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            int_mul: Expr::const_(Name::from_string("Int.mul"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            int_neg_of_nat: Expr::const_(Name::from_string("Int.negOfNat"), vec![]),
            int_rec: Expr::const_(Name::from_string("Int.rec"), vec![Level::zero()]),
            nat_mul: Expr::const_(Name::from_string("Nat.mul"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            nat_mul_comm: Expr::const_(Name::from_string("Nat.mul_comm"), vec![]),
        }
    }
}

/// Build `∀ a b : Int, Eq Int (Int.mul a b) (Int.mul b a)`.
fn build_type(c: &IntMulCommConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bv_id, bv) = b.fresh_local(c.int_type.clone());
    let lhs = Expr::app(Expr::app(c.int_mul.clone(), a.clone()), bv.clone());
    let rhs = Expr::app(Expr::app(c.int_mul.clone(), bv), a);
    let concl = Expr::apps(c.eq_const.clone(), [c.int_type.clone(), lhs, rhs]);
    let ty_raw = b.mk_pi(bv_id, BinderInfo::Default, c.int_type.clone(), concl);
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), ty_raw);
    b.finish(ty_raw)
}

/// Outer motive: `λ (x : Int) => ∀ b : Int, Eq Int (Int.mul x b) (Int.mul b x)`.
fn build_outer_motive(c: &IntMulCommConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = mb.fresh_local(c.int_type.clone());
    let (b_id, bv) = mb.fresh_local(c.int_type.clone());
    let lhs = Expr::app(Expr::app(c.int_mul.clone(), x.clone()), bv.clone());
    let rhs = Expr::app(Expr::app(c.int_mul.clone(), bv), x);
    let concl = Expr::apps(c.eq_const.clone(), [c.int_type.clone(), lhs, rhs]);
    let pi = mb.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), concl);
    let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), pi);
    mb.finish_child(lam)
}

/// Inner motive for outer ofNat-case (parameterized by `m : Nat`):
/// `λ (b : Int) => Eq Int (Int.mul (ofNat m) b) (Int.mul b (ofNat m))`.
fn build_inner_motive_ofnat(c: &IntMulCommConsts, parent: &EnvDeclBuilder, m: &Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (b_id, bv) = mb.fresh_local(c.int_type.clone());
    let of_m = Expr::app(c.int_of_nat.clone(), m.clone());
    let lhs = Expr::app(Expr::app(c.int_mul.clone(), of_m.clone()), bv.clone());
    let rhs = Expr::app(Expr::app(c.int_mul.clone(), bv), of_m);
    let body = Expr::apps(c.eq_const.clone(), [c.int_type.clone(), lhs, rhs]);
    let lam = mb.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), body);
    mb.finish_child(lam)
}

/// Inner motive for outer negSucc-case (parameterized by `m : Nat`):
/// `λ (b : Int) => Eq Int (Int.mul (negSucc m) b) (Int.mul b (negSucc m))`.
fn build_inner_motive_negsucc(c: &IntMulCommConsts, parent: &EnvDeclBuilder, m: &Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (b_id, bv) = mb.fresh_local(c.int_type.clone());
    let ns_m = Expr::app(c.int_neg_succ.clone(), m.clone());
    let lhs = Expr::app(Expr::app(c.int_mul.clone(), ns_m.clone()), bv.clone());
    let rhs = Expr::app(Expr::app(c.int_mul.clone(), bv), ns_m);
    let body = Expr::apps(c.eq_const.clone(), [c.int_type.clone(), lhs, rhs]);
    let lam = mb.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), body);
    mb.finish_child(lam)
}

/// Outer ofNat case: `λ (m : Nat) => λ (b : Int) =>
///     @Int.rec.{0} (inner_motive_ofNat m) oo on b`
/// where
///   oo := λ (n : Nat) => congrArg Int.ofNat    (Nat.mul_comm m n)
///       :: Eq Int (ofNat (m*n)) (ofNat (n*m))
///   on := λ (n : Nat) => congrArg Int.negOfNat (Nat.mul_comm m (succ n))
///       :: Eq Int (negOfNat (m * succ n)) (negOfNat (succ n * m))
fn build_outer_ofnat_case(c: &IntMulCommConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut cb = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = cb.fresh_local(c.nat_type.clone());
    let (b_id, bv) = cb.fresh_local(c.int_type.clone());

    // oo: Nat.mul_comm m n lifted through Int.ofNat
    let oo = {
        let mut ob = EnvDeclBuilder::child_of(&cb);
        let (n_id, n) = ob.fresh_local(c.nat_type.clone());
        let mul_m_n = Expr::app(Expr::app(c.nat_mul.clone(), m.clone()), n.clone());
        let mul_n_m = Expr::app(Expr::app(c.nat_mul.clone(), n.clone()), m.clone());
        let comm_witness = Expr::apps(c.nat_mul_comm.clone(), [m.clone(), n.clone()]);
        let congr_app = Expr::apps(
            c.congr_arg.clone(),
            [
                c.nat_type.clone(),
                c.int_type.clone(),
                mul_m_n,
                mul_n_m,
                c.int_of_nat.clone(),
                comm_witness,
            ],
        );
        let lam = ob.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), congr_app);
        ob.finish_child(lam)
    };

    // on: Nat.mul_comm m (succ n) lifted through Int.negOfNat
    let on = {
        let mut nb = EnvDeclBuilder::child_of(&cb);
        let (n_id, n) = nb.fresh_local(c.nat_type.clone());
        let succ_n = Expr::app(c.nat_succ.clone(), n);
        let mul_m_sn = Expr::app(Expr::app(c.nat_mul.clone(), m.clone()), succ_n.clone());
        let mul_sn_m = Expr::app(Expr::app(c.nat_mul.clone(), succ_n.clone()), m.clone());
        let comm_witness = Expr::apps(c.nat_mul_comm.clone(), [m.clone(), succ_n]);
        let congr_app = Expr::apps(
            c.congr_arg.clone(),
            [
                c.nat_type.clone(),
                c.int_type.clone(),
                mul_m_sn,
                mul_sn_m,
                c.int_neg_of_nat.clone(),
                comm_witness,
            ],
        );
        let lam = nb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), congr_app);
        nb.finish_child(lam)
    };

    let inner_motive = build_inner_motive_ofnat(c, &cb, &m);
    let rec_app = Expr::apps(c.int_rec.clone(), [inner_motive, oo, on, bv.clone()]);
    let lam_b = cb.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), rec_app);
    let lam_m = cb.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), lam_b);
    cb.finish_child(lam_m)
}

/// Outer negSucc case: `λ (m : Nat) => λ (b : Int) =>
///     @Int.rec.{0} (inner_motive_negSucc m) no nn b`
/// where
///   no := λ (n : Nat) => congrArg Int.negOfNat (Nat.mul_comm (succ m) n)
///   nn := λ (n : Nat) => congrArg Int.ofNat    (Nat.mul_comm (succ m) (succ n))
fn build_outer_negsucc_case(c: &IntMulCommConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut cb = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = cb.fresh_local(c.nat_type.clone());
    let (b_id, bv) = cb.fresh_local(c.int_type.clone());

    // no: Nat.mul_comm (succ m) n lifted through Int.negOfNat
    let no = {
        let mut ob = EnvDeclBuilder::child_of(&cb);
        let (n_id, n) = ob.fresh_local(c.nat_type.clone());
        let succ_m = Expr::app(c.nat_succ.clone(), m.clone());
        let mul_sm_n = Expr::app(Expr::app(c.nat_mul.clone(), succ_m.clone()), n.clone());
        let mul_n_sm = Expr::app(Expr::app(c.nat_mul.clone(), n.clone()), succ_m.clone());
        let comm_witness = Expr::apps(c.nat_mul_comm.clone(), [succ_m, n.clone()]);
        let congr_app = Expr::apps(
            c.congr_arg.clone(),
            [
                c.nat_type.clone(),
                c.int_type.clone(),
                mul_sm_n,
                mul_n_sm,
                c.int_neg_of_nat.clone(),
                comm_witness,
            ],
        );
        let lam = ob.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), congr_app);
        ob.finish_child(lam)
    };

    // nn: Nat.mul_comm (succ m) (succ n) lifted through Int.ofNat
    let nn = {
        let mut ob = EnvDeclBuilder::child_of(&cb);
        let (n_id, n) = ob.fresh_local(c.nat_type.clone());
        let succ_m = Expr::app(c.nat_succ.clone(), m.clone());
        let succ_n = Expr::app(c.nat_succ.clone(), n);
        let mul_sm_sn = Expr::app(Expr::app(c.nat_mul.clone(), succ_m.clone()), succ_n.clone());
        let mul_sn_sm = Expr::app(Expr::app(c.nat_mul.clone(), succ_n.clone()), succ_m.clone());
        let comm_witness = Expr::apps(c.nat_mul_comm.clone(), [succ_m, succ_n]);
        let congr_app = Expr::apps(
            c.congr_arg.clone(),
            [
                c.nat_type.clone(),
                c.int_type.clone(),
                mul_sm_sn,
                mul_sn_sm,
                c.int_of_nat.clone(),
                comm_witness,
            ],
        );
        let lam = ob.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), congr_app);
        ob.finish_child(lam)
    };

    let inner_motive = build_inner_motive_negsucc(c, &cb, &m);
    let rec_app = Expr::apps(c.int_rec.clone(), [inner_motive, no, nn, bv.clone()]);
    let lam_b = cb.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), rec_app);
    let lam_m = cb.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), lam_b);
    cb.finish_child(lam_m)
}

/// Body: `λ (a b : Int) => @Int.rec.{0} outer_motive outer_ofNat outer_negSucc a b`.
fn build_value(c: &IntMulCommConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (va_id, va) = vb.fresh_local(c.int_type.clone());
    let (vb_id, vbv) = vb.fresh_local(c.int_type.clone());
    let outer_motive = build_outer_motive(c, &vb);
    let outer_ofnat = build_outer_ofnat_case(c, &vb);
    let outer_negsucc = build_outer_negsucc_case(c, &vb);
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
    /// Register `Int.mul_comm` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int`, `Int.ofNat`,
    ///           `Int.negSucc`, `Int.mul`, `Int.negOfNat`, `Int.rec`.
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.mul`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `congrArg`.
    /// REQUIRES: `Nat.mul_comm` is registered as `Declaration::Theorem`
    ///           (constructive — see `register_nat_mul_comm_proof`).
    /// ENSURES: On success, `Int.mul_comm` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_int_mul_comm_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.mul_comm");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;
        self.register_nat_mul_comm_proof()?;

        let c = IntMulCommConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Nested
        // `@Int.rec.{0}` induction: outer on `a`, inner on `b`. Four
        // cases, each lifting `Nat.mul_comm` through `Int.ofNat` /
        // `Int.negOfNat` via `congrArg`:
        // (ofNat m, ofNat n)   : congrArg Int.ofNat    (Nat.mul_comm m n)
        // (ofNat m, negSucc n) : congrArg Int.negOfNat (Nat.mul_comm m (succ n))
        // (negSucc m, ofNat n) : congrArg Int.negOfNat (Nat.mul_comm (succ m) n)
        // (negSucc m, negSucc n): congrArg Int.ofNat   (Nat.mul_comm (succ m) (succ n))
        // Replaces the prior `Declaration::Axiom` in
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
    fn test_int_mul_comm_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_mul_comm_proof()
            .expect("first registration");
        env.register_int_mul_comm_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.mul_comm"))
            .expect("Int.mul_comm should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_mul_comm_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_mul_comm_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.mul_comm"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        assert!(
            matches!(value.kind(), ExprKind::Lam(..)),
            "Int.mul_comm proof must be a λ-abstraction, got {:?}",
            value.kind()
        );
    }

    /// Proof root (after peeling two outer λ binders) must be an
    /// `@Int.rec.{0}` application. Guards against a trivial masquerade.
    #[test]
    fn test_int_mul_comm_proof_uses_int_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_mul_comm_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.mul_comm"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let outer_body = match value.kind() {
            ExprKind::Lam(_, _, body) => body,
            k => panic!("expected outer λ, got {:?}", k),
        };
        let inner_body = match outer_body.kind() {
            ExprKind::Lam(_, _, body) => body,
            k => panic!("expected inner λ, got {:?}", k),
        };
        let mut head = inner_body.clone();
        while let ExprKind::App(f, _) = head.kind() {
            head = f.clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Int.rec",
                "Int.mul_comm proof root must be Int.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Int.rec, ..) at proof root, got {:?}", k),
        }
    }

    /// Axiom closure is empty.
    #[test]
    fn test_int_mul_comm_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_mul_comm_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.mul_comm"))
            .expect("Int.mul_comm is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.mul_comm must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }
}
