// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.one_mul : ∀ a : Int, Eq Int (Int.mul (Int.ofNat 1) a) a`
//! (`Int.ofNat 1 = Int.ofNat (Nat.succ Nat.zero)`).
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_int_lemmas.rs` with a `Declaration::Theorem` whose proof
//! term is built by a single `@Int.rec.{0}` case-analysis on `a`, each
//! branch lifting `Nat.one_mul` through `Int.ofNat` / `Int.negOfNat` via
//! `congrArg`.
//!
//! # Proof sketch
//!
//! `Int.mul` is a reducible Definition (see `data_types_arithmetic.rs`)
//! that recurses on its FIRST argument. With the first argument fixed to
//! the constructor `Int.ofNat (Nat.succ Nat.zero)`, the outer `Int.rec`
//! fires; the remaining inner `Int.rec` recurses on `a`, so a case-split
//! on `a` reduces each branch:
//!
//! ```text
//! Int.mul (ofNat 1) (ofNat n)   = ofNat    (Nat.mul (Nat.succ Nat.zero) n)
//! Int.mul (ofNat 1) (negSucc n) = negOfNat (Nat.mul (Nat.succ Nat.zero) (Nat.succ n))
//! ```
//!
//! `Nat.one_mul : ∀ a, Eq (Nat.mul (Nat.succ Nat.zero) a) a` is a
//! constructive `Declaration::Theorem`. Per branch:
//! - `ofNat n`: `congrArg Int.ofNat (Nat.one_mul n)` has type
//!   `Eq Int (ofNat (Nat.mul 1 n)) (ofNat n)`, matching the motive at
//!   `ofNat n` (`Int.mul (ofNat 1) (ofNat n)` ≡ LHS).
//! - `negSucc n`: `congrArg Int.negOfNat (Nat.one_mul (Nat.succ n))` has
//!   type `Eq Int (negOfNat (Nat.mul 1 (succ n))) (negOfNat (succ n))`.
//!   Since `negOfNat (Nat.succ n)` reduces to `negSucc n` by iota on
//!   `Int.negOfNat` (succ-case), this matches the motive at `negSucc n`.
//!
//! The proof has the outer shape
//!
//! ```text
//! λ a : Int => @Int.rec.{0} motive
//!   (λ n : Nat => congrArg Int.ofNat    (Nat.one_mul n))
//!   (λ n : Nat => congrArg Int.negOfNat (Nat.one_mul (Nat.succ n)))
//!   a
//! ```
//!
//! against the type
//! `∀ a : Int, @Eq.{1} Int (Int.mul (Int.ofNat (Nat.succ Nat.zero)) a) a`.
//!
//! # Axiom closure
//!
//! The proof term mentions `Int`, `Int.mul`, `Int.ofNat`, `Int.negSucc`,
//! `Int.negOfNat`, `Int.rec`, `Nat`, `Nat.succ`, `Nat.mul`, `Eq`,
//! `congrArg` (kernel machinery / constructors / reducible Definitions /
//! Theorems), and `Nat.one_mul` (constructive `Declaration::Theorem`).
//! None are `Declaration::Axiom`, so `env.axiom_deps("Int.one_mul")` is
//! empty and `env.proof_quality("Int.one_mul") == ProofQuality::Constructive`.
//!
//! Tracks #3604. Sibling proofs:
//! - `algebra_int_mul_one_proof.rs` (Int.mul_one via `Nat.mul_one`).
//! - `algebra_int_zero_mul_proof.rs` (Int.zero_mul via `Nat.zero_mul`).
//! - `algebra_int_mul_comm_proof.rs` (#3604, nested Int.rec — same shape).
//! - `algebra_nat_one_mul_proof.rs` (#3551, dependency — Nat.one_mul).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntOneMulConsts {
    int_type: Expr,
    nat_type: Expr,
    int_mul: Expr,
    int_of_nat: Expr,
    int_neg_of_nat: Expr,
    int_rec: Expr,
    nat_mul: Expr,
    nat_succ: Expr,
    nat_one: Expr,
    eq_const: Expr,
    congr_arg: Expr,
    nat_one_mul: Expr,
}

impl IntOneMulConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            int_mul: Expr::const_(Name::from_string("Int.mul"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_of_nat: Expr::const_(Name::from_string("Int.negOfNat"), vec![]),
            int_rec: Expr::const_(Name::from_string("Int.rec"), vec![Level::zero()]),
            nat_mul: Expr::const_(Name::from_string("Nat.mul"), vec![]),
            nat_succ: nat_succ.clone(),
            nat_one: Expr::app(nat_succ, nat_zero),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            nat_one_mul: Expr::const_(Name::from_string("Nat.one_mul"), vec![]),
        }
    }

    /// `Int.ofNat (Nat.succ Nat.zero)` — the literal `1 : Int` used by the
    /// axiom statement in `data_types_int_lemmas.rs`.
    fn int_one(&self) -> Expr {
        Expr::app(self.int_of_nat.clone(), self.nat_one.clone())
    }
}

/// Build `∀ a : Int, Eq Int (Int.mul (Int.ofNat 1) a) a`.
fn build_type(c: &IntOneMulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let lhs = Expr::app(Expr::app(c.int_mul.clone(), c.int_one()), a.clone());
    let concl = Expr::apps(c.eq_const.clone(), [c.int_type.clone(), lhs, a]);
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), concl);
    b.finish(ty_raw)
}

/// Outer motive: `λ (x : Int) => Eq Int (Int.mul (Int.ofNat 1) x) x`.
fn build_motive(c: &IntOneMulConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = mb.fresh_local(c.int_type.clone());
    let lhs = Expr::app(Expr::app(c.int_mul.clone(), c.int_one()), x.clone());
    let body = Expr::apps(c.eq_const.clone(), [c.int_type.clone(), lhs, x]);
    let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
    mb.finish_child(lam)
}

/// Build a `congrArg f (Nat.one_mul k)` witness of type
/// `Eq Int (f (Nat.mul 1 k)) (f k)`.
fn lift_one_mul(c: &IntOneMulConsts, f: &Expr, k: &Expr) -> Expr {
    let mul_one_k = Expr::app(Expr::app(c.nat_mul.clone(), c.nat_one.clone()), k.clone());
    let witness = Expr::app(c.nat_one_mul.clone(), k.clone());
    Expr::apps(
        c.congr_arg.clone(),
        [
            c.nat_type.clone(),
            c.int_type.clone(),
            mul_one_k,
            k.clone(),
            f.clone(),
            witness,
        ],
    )
}

/// Outer ofNat case: `λ (n : Nat) => congrArg Int.ofNat (Nat.one_mul n)`.
fn build_ofnat_case(c: &IntOneMulConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut cb = EnvDeclBuilder::child_of(parent);
    let (n_id, n) = cb.fresh_local(c.nat_type.clone());
    let congr = lift_one_mul(c, &c.int_of_nat, &n);
    let lam = cb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), congr);
    cb.finish_child(lam)
}

/// Outer negSucc case:
/// `λ (n : Nat) => congrArg Int.negOfNat (Nat.one_mul (Nat.succ n))`.
fn build_negsucc_case(c: &IntOneMulConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut cb = EnvDeclBuilder::child_of(parent);
    let (n_id, n) = cb.fresh_local(c.nat_type.clone());
    let succ_n = Expr::app(c.nat_succ.clone(), n);
    let congr = lift_one_mul(c, &c.int_neg_of_nat, &succ_n);
    let lam = cb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), congr);
    cb.finish_child(lam)
}

/// Body: `λ (a : Int) => @Int.rec.{0} motive ofNat_case negSucc_case a`.
fn build_value(c: &IntOneMulConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (va_id, va) = vb.fresh_local(c.int_type.clone());
    let motive = build_motive(c, &vb);
    let of_nat_case = build_ofnat_case(c, &vb);
    let neg_succ_case = build_negsucc_case(c, &vb);
    let rec_app = Expr::apps(c.int_rec.clone(), [motive, of_nat_case, neg_succ_case, va]);
    let val_raw = vb.mk_lam(va_id, BinderInfo::Default, c.int_type.clone(), rec_app);
    vb.finish(val_raw)
}

impl Environment {
    /// Register `Int.one_mul` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int`, `Int.ofNat`,
    ///           `Int.negSucc`, `Int.negOfNat`, `Int.mul`, `Int.rec`.
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.mul`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `congrArg`.
    /// REQUIRES: `Nat.one_mul` is registered as `Declaration::Theorem`
    ///           (constructive — see `register_nat_one_mul_proof`).
    /// ENSURES: On success, `Int.one_mul` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.one_mul` is already registered with
    ///          any declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_int_one_mul_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.one_mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;
        self.register_nat_one_mul_proof()?;

        let c = IntOneMulConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Single
        // `@Int.rec.{0}` case-analysis on `a`, each branch lifting the
        // constructive `Nat.one_mul` through `Int.ofNat` / `Int.negOfNat`
        // via `congrArg`. The kernel reduces `Int.mul (Int.ofNat 1) a` to
        // `Int.ofNat (Nat.mul 1 n)` / `Int.negOfNat (Nat.mul 1 (succ n))`
        // by iota on the outer `Int.rec` (first arg `ofNat 1` constructor)
        // + iota on the inner `Int.rec` (case-split on `a`) + delta on the
        // reducible `Int.mul`. No `sorry`, no self-reference, no
        // domain-axiom dependency (`Nat.one_mul` is itself constructive
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

    /// Kernel accepts the `Int.rec` / `congrArg` proof term. Verifies the
    /// theorem is registered as a Theorem (not Axiom) and idempotent
    /// re-invocation is a no-op.
    #[test]
    fn test_int_one_mul_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_one_mul_proof()
            .expect("first registration");
        env.register_int_one_mul_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.one_mul"))
            .expect("Int.one_mul should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    /// The proof is not a trivial axiom reference — it is a `λ`
    /// abstraction. Guards against the axiom-wrapping masquerade (#3559).
    #[test]
    fn test_int_one_mul_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_one_mul_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.one_mul"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        assert!(
            matches!(value.kind(), ExprKind::Lam(..)),
            "Int.one_mul proof must be a λ-abstraction, got {:?}",
            value.kind()
        );
    }

    /// Proof root (after peeling the outer λ binder) must be an
    /// `@Int.rec.{0}` application. Guards against a trivial masquerade.
    #[test]
    fn test_int_one_mul_proof_uses_int_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_one_mul_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.one_mul"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let outer_body = match value.kind() {
            ExprKind::Lam(_, _, body) => body,
            k => panic!("expected outer λ, got {:?}", k),
        };
        let mut head = outer_body.clone();
        while let ExprKind::App(f, _) = head.kind() {
            head = f.clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Int.rec",
                "Int.one_mul proof root must be Int.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Int.rec, ..) at proof root, got {:?}", k),
        }
    }

    /// Axiom closure is empty (constructive proof). `Nat.one_mul` is
    /// constructive (#3551), so `Int.one_mul` inherits empty deps.
    #[test]
    fn test_int_one_mul_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_one_mul_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.one_mul"))
            .expect("Int.one_mul is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.one_mul must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }
}
