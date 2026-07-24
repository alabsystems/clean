// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.le_self_add_one : ∀ a : Int,
//!    Int.le a (Int.add a (Int.ofNat (Nat.succ Nat.zero)))`.
//!
//! This is the "successor step" bridge `a ≤ a + 1`, with `1` in the canonical
//! `Int.ofNat (Nat.succ Nat.zero)` form matching the `Int.lt` definition. It is
//! a fresh constructive building block used by `algebra_int_le_of_lt_proof.rs`
//! and `algebra_int_lt_trans_proof.rs`.
//!
//! # Definitions in play
//!
//! ```text
//! Int.le a b := Int.NonNeg (Int.sub b a)        -- reducible Definition
//! inductive Int.NonNeg : Int → Prop where
//!   | mk (n : Nat) : Int.NonNeg (Int.ofNat n)
//! ```
//!
//! So `Int.le a (a + 1)` unfolds (delta) to `Int.NonNeg (Int.sub (a + 1) a)`.
//!
//! # Proof sketch
//!
//! Transport the canonical witness `@Int.NonNeg.mk (Nat.succ Nat.zero)`, whose
//! type is `Int.NonNeg (Int.ofNat (Nat.succ Nat.zero))` ≡ `Int.NonNeg one`,
//! along the constructive identity
//! `Int.add_one_sub_self a : Eq Int (Int.sub (a + 1) a) one`. With motive
//! `fun x : Int => Int.NonNeg x`:
//!
//! ```text
//! @Eq.subst.{1} Int (fun x => Int.NonNeg x)
//!   one (Int.sub (a + 1) a)
//!   (@Eq.symm.{1} Int (Int.sub (a + 1) a) one (Int.add_one_sub_self a))
//!   (@Int.NonNeg.mk (Nat.succ Nat.zero))
//!   : Int.NonNeg (Int.sub (a + 1) a)
//! ```
//!
//! and `Int.NonNeg (Int.sub (a + 1) a)` is definitionally `Int.le a (a + 1)`.
//!
//! # Axiom closure
//!
//! Depends only on the constructive `Int.add_one_sub_self`, the foundational
//! `Eq.subst` / `Eq.symm`, the inductive constructor `Int.NonNeg.mk`, and the
//! reducible `Int.sub`. None are `Declaration::Axiom`, so
//! `env.axiom_deps("Int.le_self_add_one")` is empty and
//! `env.proof_quality("Int.le_self_add_one") == ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntLeSelfAddOneConsts {
    int_type: Expr,
    int_le: Expr,
    int_add: Expr,
    int_sub: Expr,
    int_of_nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nonneg: Expr,
    nonneg_mk: Expr,
    add_one_sub_self: Expr,
    eq_subst: Expr,
    eq_symm: Expr,
}

impl IntLeSelfAddOneConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            int_le: Expr::const_(Name::from_string("Int.le"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_sub: Expr::const_(Name::from_string("Int.sub"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nonneg: Expr::const_(Name::from_string("Int.NonNeg"), vec![]),
            nonneg_mk: Expr::const_(Name::from_string("Int.NonNeg.mk"), vec![]),
            add_one_sub_self: Expr::const_(Name::from_string("Int.add_one_sub_self"), vec![]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1]),
        }
    }

    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), x), y)
    }

    fn sub(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_sub.clone(), x), y)
    }

    fn le(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_le.clone(), x), y)
    }

    /// `Nat.succ Nat.zero`.
    fn nat_one(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.nat_zero.clone())
    }

    /// `Int.ofNat (Nat.succ Nat.zero)`.
    fn one(&self) -> Expr {
        Expr::app(self.int_of_nat.clone(), self.nat_one())
    }
}

/// Build `∀ a : Int, Int.le a (Int.add a one)`.
fn build_type(c: &IntLeSelfAddOneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let concl = c.le(a.clone(), c.add(a.clone(), c.one()));
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), concl);
    b.finish(r)
}

/// Body:
/// ```text
/// λ (a : Int) =>
///   @Eq.subst.{1} Int (fun x => Int.NonNeg x)
///     one (Int.sub (a + one) a)
///     (@Eq.symm.{1} Int (Int.sub (a + one) a) one (Int.add_one_sub_self a))
///     (@Int.NonNeg.mk (Nat.succ Nat.zero))
/// ```
fn build_value(c: &IntLeSelfAddOneConsts) -> Expr {
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

    let one = c.one();
    let a_plus_one = c.add(a.clone(), one.clone());
    let sub_term = c.sub(a_plus_one, a.clone()); // (a + 1) - a

    // Int.add_one_sub_self a : Eq Int (Int.sub (a + 1) a) one
    let id_eq = Expr::app(c.add_one_sub_self.clone(), a.clone());

    // @Eq.symm.{1} Int (sub (a+1) a) one id_eq : Eq Int one (sub (a+1) a)
    let symm = Expr::apps(
        c.eq_symm.clone(),
        [c.int_type.clone(), sub_term.clone(), one.clone(), id_eq],
    );

    // @Int.NonNeg.mk (Nat.succ Nat.zero) : Int.NonNeg (Int.ofNat 1) ≡ Int.NonNeg one
    let witness = Expr::app(c.nonneg_mk.clone(), c.nat_one());

    // @Eq.subst.{1} Int motive one (sub (a+1) a) symm witness : NonNeg (sub (a+1) a)
    let proof = Expr::apps(
        c.eq_subst.clone(),
        [c.int_type.clone(), motive, one, sub_term, symm, witness],
    );

    let val = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), proof);
    b.finish(val)
}

impl Environment {
    /// Register `Int.le_self_add_one` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_ord()` has registered `Int.le`, `Int.NonNeg`,
    ///           `Int.NonNeg.mk`, `Int.add`, `Int.sub`, `Int.ofNat`.
    /// REQUIRES: `self.init_eq()` has registered `Eq.subst`, `Eq.symm`.
    /// ENSURES: On success, `Int.le_self_add_one` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_int_le_self_add_one_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.le_self_add_one");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_ord()?;
        self.init_eq()?;
        // Constructive dependency: (a + 1) - a = 1.
        self.register_int_add_one_sub_self_proof()?;

        let c = IntLeSelfAddOneConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. Transports the canonical
        // `@Int.NonNeg.mk (Nat.succ Nat.zero) : NonNeg (Int.ofNat 1)` (≡
        // `NonNeg one`) along `Eq.symm (Int.add_one_sub_self a) : Eq one (sub
        // (a+1) a)` via `@Eq.subst.{1}` with motive `fun x => Int.NonNeg x`,
        // yielding `Int.NonNeg (Int.sub (a + 1) a)` ≡ `Int.le a (a + 1)`. No
        // `sorry`, no self-reference, no domain-axiom dependency.
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
    fn test_int_le_self_add_one_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_le_self_add_one_proof()
            .expect("first registration");
        env.register_int_le_self_add_one_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.le_self_add_one"))
            .expect("Int.le_self_add_one should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_le_self_add_one_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_le_self_add_one_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.le_self_add_one"))
            .expect("registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.le_self_add_one must have empty axiom closure, got {:?}",
            domain_deps
        );
    }
}
