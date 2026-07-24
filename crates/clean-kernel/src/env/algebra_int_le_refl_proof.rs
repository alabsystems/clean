// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `Int.le_refl : ∀ a : Int, Int.le a a`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `order_int.rs::init_int_ord_lemmas` with a `Declaration::Theorem`.
//!
//! # Definitions in play
//!
//! ```text
//! Int.le a b := Int.NonNeg (Int.sub b a)        -- reducible Definition
//! Int.sub m n := Int.add m (Int.neg n)          -- reducible Definition
//! Int.zero    := Int.ofNat Nat.zero             -- reducible Definition
//! inductive Int.NonNeg : Int → Prop where
//!   | mk (n : Nat) : Int.NonNeg (Int.ofNat n)
//! ```
//!
//! So `Int.le a a` unfolds (delta) to `Int.NonNeg (Int.sub a a)`.
//!
//! # Proof sketch
//!
//! For a *general* variable `a : Int`, `Int.sub a a` does **not** reduce to
//! `Int.ofNat 0` definitionally (that requires case analysis on `a`). Instead
//! we transport the canonical witness `@Int.NonNeg.mk Nat.zero`, whose type is
//! `Int.NonNeg (Int.ofNat Nat.zero)` ≡ `Int.NonNeg Int.zero`, along the
//! constructive identity `Int.sub_self a : Eq Int (Int.sub a a) Int.zero`.
//!
//! Concretely, with motive `fun x : Int => Int.NonNeg x`:
//!
//! ```text
//! @Eq.subst.{1} Int (fun x => Int.NonNeg x)
//!   Int.zero (Int.sub a a)
//!   (@Eq.symm.{1} Int (Int.sub a a) Int.zero (Int.sub_self a))   -- 0 = a - a
//!   (@Int.NonNeg.mk Nat.zero)                                    -- NonNeg 0
//!   : Int.NonNeg (Int.sub a a)
//! ```
//!
//! and `Int.NonNeg (Int.sub a a)` is definitionally `Int.le a a`.
//!
//! # Axiom closure
//!
//! The proof mentions only `Int`, `Int.NonNeg`, `Int.NonNeg.mk`, `Int.zero`,
//! `Int.sub`, `Nat.zero`, `Eq.subst`, `Eq.symm`, and the constructive
//! `Int.sub_self` (`algebra_int_sub_self_proof.rs`, #3604). None are
//! `Declaration::Axiom` (`Eq.subst`/`Eq.symm` are foundational `Eq` machinery,
//! `Int.sub`/`Int.zero` reducible Definitions). Therefore
//! `env.axiom_deps("Int.le_refl")` is empty and
//! `env.proof_quality("Int.le_refl") == ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntLeReflConsts {
    int_type: Expr,
    int_le: Expr,
    int_sub: Expr,
    int_zero: Expr,
    nonneg: Expr,
    nonneg_mk: Expr,
    nat_zero: Expr,
    sub_self: Expr,
    eq_subst: Expr,
    eq_symm: Expr,
}

impl IntLeReflConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            int_le: Expr::const_(Name::from_string("Int.le"), vec![]),
            int_sub: Expr::const_(Name::from_string("Int.sub"), vec![]),
            int_zero: Expr::const_(Name::from_string("Int.zero"), vec![]),
            nonneg: Expr::const_(Name::from_string("Int.NonNeg"), vec![]),
            nonneg_mk: Expr::const_(Name::from_string("Int.NonNeg.mk"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            sub_self: Expr::const_(Name::from_string("Int.sub_self"), vec![]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1]),
        }
    }

    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.int_le.clone(), a), b)
    }

    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.int_sub.clone(), a), b)
    }
}

/// Build `∀ a : Int, Int.le a a`.
fn build_type(c: &IntLeReflConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let concl = c.le(a.clone(), a);
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), concl);
    b.finish(ty_raw)
}

/// Body:
/// ```text
/// λ (a : Int) =>
///   @Eq.subst.{1} Int (fun x => Int.NonNeg x)
///     Int.zero (Int.sub a a)
///     (@Eq.symm.{1} Int (Int.sub a a) Int.zero (Int.sub_self a))
///     (@Int.NonNeg.mk Nat.zero)
/// ```
fn build_value(c: &IntLeReflConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());

    // motive: fun x : Int => Int.NonNeg x
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(c.int_type.clone());
        let body = Expr::app(c.nonneg.clone(), x);
        let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
        mb.finish_child(lam)
    };

    let sub_aa = c.sub(a.clone(), a.clone());

    // Int.sub_self a : Eq Int (Int.sub a a) Int.zero
    let sub_self_a = Expr::app(c.sub_self.clone(), a.clone());

    // @Eq.symm.{1} Int (Int.sub a a) Int.zero (Int.sub_self a) : Eq Int Int.zero (Int.sub a a)
    let symm = Expr::apps(
        c.eq_symm.clone(),
        [
            c.int_type.clone(),
            sub_aa.clone(),
            c.int_zero.clone(),
            sub_self_a,
        ],
    );

    // @Int.NonNeg.mk Nat.zero : Int.NonNeg (Int.ofNat Nat.zero) ≡ Int.NonNeg Int.zero
    let witness = Expr::app(c.nonneg_mk.clone(), c.nat_zero.clone());

    // @Eq.subst.{1} Int motive Int.zero (Int.sub a a) symm witness
    let proof = Expr::apps(
        c.eq_subst.clone(),
        [
            c.int_type.clone(),
            motive,
            c.int_zero.clone(),
            sub_aa,
            symm,
            witness,
        ],
    );

    let val_raw = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), proof);
    b.finish(val_raw)
}

impl Environment {
    /// Register `Int.le_refl` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_ord()` has registered `Int.le`, `Int.NonNeg`,
    ///           `Int.NonNeg.mk`, `Int.sub`, `Int.zero`.
    /// REQUIRES: `self.init_eq()` has registered `Eq.subst`, `Eq.symm`.
    /// ENSURES: On success, `Int.le_refl` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.le_refl` is already registered with any
    ///          declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_int_le_refl_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.le_refl");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_ord()?;
        self.init_eq()?;
        // Constructive dependency: a - a = 0.
        self.register_int_sub_self_proof()?;

        let c = IntLeReflConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. Transports the canonical
        // `@Int.NonNeg.mk Nat.zero : NonNeg (ofNat 0)` (≡ `NonNeg Int.zero`)
        // along `Eq.symm (Int.sub_self a) : Eq Int.zero (Int.sub a a)` via
        // `@Eq.subst.{1}` with motive `fun x => Int.NonNeg x`, yielding
        // `Int.NonNeg (Int.sub a a)` ≡ `Int.le a a`. No `sorry`, no
        // self-reference, no domain-axiom dependency. Replaces the prior
        // `Declaration::Axiom` in `order_int.rs::init_int_ord_lemmas`.
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
    fn test_int_le_refl_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_le_refl_proof()
            .expect("first registration");
        env.register_int_le_refl_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.le_refl"))
            .expect("Int.le_refl should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_le_refl_proof_body_not_axiom_reference() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_le_refl_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.le_refl"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        // Top level is the outer λ over `a : Int`.
        let body: Expr = match value.kind() {
            ExprKind::Lam(_, _, inner) => (**inner).clone(),
            k => panic!("expected outer λ, got {:?}", k),
        };
        // Head must be Eq.subst (transport), not a bare axiom self-reference.
        let mut head: Expr = body;
        while let ExprKind::App(f, _) = head.kind() {
            head = (**f).clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Eq.subst",
                "Int.le_refl proof root must be Eq.subst"
            ),
            k => panic!("expected Const(Eq.subst), got {:?}", k),
        }
    }

    #[test]
    fn test_int_le_refl_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_le_refl_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.le_refl"))
            .expect("Int.le_refl is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.le_refl must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }

    #[test]
    fn test_int_le_refl_proof_quality_constructive() {
        use crate::env::ProofQuality;
        let mut env = Environment::new();
        env.register_int_le_refl_proof().unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Int.le_refl"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.le_refl must be Constructive, got {:?}",
            quality
        );
    }
}
