// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.mul_zero : ∀ a : Int, Eq Int (Int.mul a Int.zero) Int.zero`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `data_types_int_lemmas.rs` with a `Declaration::Theorem` whose proof
//! term is built by a single `@Int.rec.{0}` case-analysis on `a`.
//!
//! # Proof sketch
//!
//! `Int.zero` is the reducible Definition `Int.ofNat Nat.zero`, and
//! `Int.mul` is a reducible Definition (see `data_types_arithmetic.rs`).
//! Specializing the second argument to `Int.zero ≡ ofNat zero`, each
//! `Int.rec` branch on `a` reduces fully (the inner `Int.rec` major is
//! the constructor `ofNat Nat.zero`):
//!
//! ```text
//! Int.mul (ofNat m)   Int.zero = ofNat    (Nat.mul m Nat.zero)
//! Int.mul (negSucc m) Int.zero = negOfNat (Nat.mul (Nat.succ m) Nat.zero)
//! ```
//!
//! `Nat.mul _ Nat.zero` reduces to `Nat.zero` by iota on `Nat.rec`
//! (zero-case, `Nat.mul` recurses on its SECOND argument). Therefore
//! - `ofNat (Nat.mul m Nat.zero)` ≡ `ofNat Nat.zero` ≡ `Int.zero`, and
//! - `negOfNat (Nat.mul (Nat.succ m) Nat.zero)` ≡ `negOfNat Nat.zero`
//!   ≡ `ofNat Nat.zero` ≡ `Int.zero` (iota on `Int.negOfNat`, zero-case).
//!
//! So each branch is closed by the pure proof term
//! `@Eq.refl.{1} Int Int.zero`, and the proof has the outer shape
//!
//! ```text
//! λ a : Int => @Int.rec.{0} motive
//!   (λ m : Nat => @Eq.refl.{1} Int Int.zero)
//!   (λ m : Nat => @Eq.refl.{1} Int Int.zero)
//!   a
//! ```
//!
//! against the type `∀ a : Int, @Eq.{1} Int (Int.mul a Int.zero) Int.zero`.
//!
//! # Axiom closure
//!
//! The proof term mentions only `Int`, `Int.mul`, `Int.zero`, `Int.rec`,
//! `Eq`, `Eq.refl` — none of which are `Declaration::Axiom` (`Int.rec`
//! is auto-generated kernel machinery; `Int.mul` / `Int.zero` are
//! reducible Definitions). Therefore `env.axiom_deps("Int.mul_zero")` is
//! empty and `env.proof_quality("Int.mul_zero") == ProofQuality::Constructive`.
//!
//! Tracks #3604. Sibling proofs:
//! - `algebra_int_zero_mul_proof.rs` (Int.zero_mul via `congrArg`/`Nat.zero_mul`).
//! - `algebra_int_mul_one_proof.rs` (Int.mul_one via `congrArg`/`Nat.mul_one`).
//! - `algebra_int_mul_comm_proof.rs` (#3604, nested Int.rec — same shape).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntMulZeroConsts {
    int_type: Expr,
    nat_type: Expr,
    int_mul: Expr,
    int_zero: Expr,
    int_rec: Expr,
    eq_const: Expr,
    eq_refl: Expr,
}

impl IntMulZeroConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            int_mul: Expr::const_(Name::from_string("Int.mul"), vec![]),
            int_zero: Expr::const_(Name::from_string("Int.zero"), vec![]),
            int_rec: Expr::const_(Name::from_string("Int.rec"), vec![Level::zero()]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![type1]),
        }
    }
}

/// Build `∀ a : Int, Eq Int (Int.mul a Int.zero) Int.zero`.
fn build_type(c: &IntMulZeroConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let lhs = Expr::app(Expr::app(c.int_mul.clone(), a), c.int_zero.clone());
    let concl = Expr::apps(
        c.eq_const.clone(),
        [c.int_type.clone(), lhs, c.int_zero.clone()],
    );
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), concl);
    b.finish(ty_raw)
}

/// Outer motive: `λ (x : Int) => Eq Int (Int.mul x Int.zero) Int.zero`.
fn build_motive(c: &IntMulZeroConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = mb.fresh_local(c.int_type.clone());
    let lhs = Expr::app(Expr::app(c.int_mul.clone(), x), c.int_zero.clone());
    let body = Expr::apps(
        c.eq_const.clone(),
        [c.int_type.clone(), lhs, c.int_zero.clone()],
    );
    let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
    mb.finish_child(lam)
}

/// A constructor branch `λ (m : Nat) => @Eq.refl.{1} Int Int.zero`.
///
/// Closes both the `ofNat` and `negSucc` cases, since both reduce the
/// `Int.mul _ Int.zero` major to `Int.zero`.
fn build_refl_case(c: &IntMulZeroConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut cb = EnvDeclBuilder::child_of(parent);
    let (m_id, _m) = cb.fresh_local(c.nat_type.clone());
    let refl = Expr::apps(c.eq_refl.clone(), [c.int_type.clone(), c.int_zero.clone()]);
    let lam = cb.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), refl);
    cb.finish_child(lam)
}

/// Body: `λ (a : Int) => @Int.rec.{0} motive ofNat_case negSucc_case a`.
fn build_value(c: &IntMulZeroConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (va_id, va) = vb.fresh_local(c.int_type.clone());
    let motive = build_motive(c, &vb);
    let of_nat_case = build_refl_case(c, &vb);
    let neg_succ_case = build_refl_case(c, &vb);
    let rec_app = Expr::apps(c.int_rec.clone(), [motive, of_nat_case, neg_succ_case, va]);
    let val_raw = vb.mk_lam(va_id, BinderInfo::Default, c.int_type.clone(), rec_app);
    vb.finish(val_raw)
}

impl Environment {
    /// Register `Int.mul_zero` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int`, `Int.ofNat`,
    ///           `Int.negSucc`, `Int.negOfNat`, `Int.mul`, `Int.zero`,
    ///           `Int.rec`.
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.mul`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`.
    /// ENSURES: On success, `Int.mul_zero` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.mul_zero` is already registered with
    ///          any declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_int_mul_zero_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.mul_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;

        let c = IntMulZeroConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Single
        // `@Int.rec.{0}` case-analysis on `a`; both the `ofNat` and
        // `negSucc` branches are closed by pure `@Eq.refl.{1} Int Int.zero`
        // because `Int.mul a Int.zero` reduces to `Int.zero` by iota on
        // `Nat.rec` (Nat.mul zero-case) + iota on `Int.negOfNat`
        // (zero-case) + delta on the reducible `Int.mul` / `Int.zero`
        // definitions. No `sorry`, no self-reference, no domain-axiom
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

    /// Kernel accepts the `Int.rec` / `Eq.refl` proof term. Verifies the
    /// theorem is registered as a Theorem (not Axiom) and idempotent
    /// re-invocation is a no-op.
    #[test]
    fn test_int_mul_zero_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_mul_zero_proof()
            .expect("first registration");
        env.register_int_mul_zero_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.mul_zero"))
            .expect("Int.mul_zero should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    /// The proof is not a trivial axiom reference — it is a `λ`
    /// abstraction. Guards against the axiom-wrapping masquerade (#3559).
    #[test]
    fn test_int_mul_zero_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_mul_zero_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.mul_zero"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        assert!(
            matches!(value.kind(), ExprKind::Lam(..)),
            "Int.mul_zero proof must be a λ-abstraction, got {:?}",
            value.kind()
        );
    }

    /// Proof root (after peeling the outer λ binder) must be an
    /// `@Int.rec.{0}` application. Guards against a trivial masquerade.
    #[test]
    fn test_int_mul_zero_proof_uses_int_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_mul_zero_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.mul_zero"))
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
                "Int.mul_zero proof root must be Int.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Int.rec, ..) at proof root, got {:?}", k),
        }
    }

    /// Axiom closure is empty (constructive proof).
    #[test]
    fn test_int_mul_zero_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_mul_zero_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.mul_zero"))
            .expect("Int.mul_zero is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.mul_zero must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }
}
