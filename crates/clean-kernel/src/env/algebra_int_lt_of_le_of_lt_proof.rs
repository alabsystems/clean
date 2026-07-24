// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.lt_of_le_of_lt : ∀ a b c : Int, Int.le a b → Int.lt b c → Int.lt a c`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `order_int.rs::init_int_ord_lemmas` with a `Declaration::Theorem`.
//!
//! # Definitions in play
//!
//! ```text
//! Int.lt a b := Int.le (Int.add a (Int.ofNat 1)) b   -- reducible Definition
//! ```
//!
//! So `h2 : Int.lt b c` delta-reduces to `Int.le (b + 1) c` and the goal
//! `Int.lt a c` to `Int.le (a + 1) c`.
//!
//! # Proof sketch
//!
//! Add `1` on the right of `h1 : Int.le a b` to get `Int.le (a+1) (b+1)`
//! (`Int.add_le_add_right a b h1 1`), then chain with `h2` via `Int.le_trans`:
//!
//! ```text
//! step1 := Int.add_le_add_right a b h1 one : Int.le (a + 1) (b + 1)
//! Int.le_trans (a+1) (b+1) c step1 h2 : Int.le (a + 1) c   ≡   Int.lt a c
//! ```
//!
//! where `h2 : Int.lt b c ≡ Int.le (b+1) c` fills the second `le` slot.
//!
//! # Axiom closure
//!
//! Depends only on the constructive `Int.add_le_add_right` and `Int.le_trans`
//! theorems. Neither is a `Declaration::Axiom`, so
//! `env.axiom_deps("Int.lt_of_le_of_lt")` is empty and
//! `env.proof_quality("Int.lt_of_le_of_lt") == ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntLtOfLeOfLtConsts {
    int_type: Expr,
    int_le: Expr,
    int_lt: Expr,
    int_add: Expr,
    int_of_nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    le_trans: Expr,
    add_le_add_right: Expr,
}

impl IntLtOfLeOfLtConsts {
    fn new() -> Self {
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            int_le: Expr::const_(Name::from_string("Int.le"), vec![]),
            int_lt: Expr::const_(Name::from_string("Int.lt"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            le_trans: Expr::const_(Name::from_string("Int.le_trans"), vec![]),
            add_le_add_right: Expr::const_(Name::from_string("Int.add_le_add_right"), vec![]),
        }
    }

    fn le(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_le.clone(), x), y)
    }

    fn lt(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_lt.clone(), x), y)
    }

    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), x), y)
    }

    /// `Int.ofNat (Nat.succ Nat.zero)`.
    fn one(&self) -> Expr {
        Expr::app(
            self.int_of_nat.clone(),
            Expr::app(self.nat_succ.clone(), self.nat_zero.clone()),
        )
    }
}

/// Build `∀ a b c : Int, Int.le a b → Int.lt b c → Int.lt a c`.
fn build_type(c: &IntLtOfLeOfLtConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let (c_id, cc) = b.fresh_local(c.int_type.clone());
    let le_ab = c.le(a.clone(), bv.clone());
    let lt_bc = c.lt(bv.clone(), cc.clone());
    let lt_ac = c.lt(a.clone(), cc.clone());
    let (h2_id, _h2) = b.fresh_local(lt_bc.clone());
    let (h1_id, _h1) = b.fresh_local(le_ab.clone());
    let r = b.mk_pi(h2_id, BinderInfo::Default, lt_bc, lt_ac);
    let r = b.mk_pi(h1_id, BinderInfo::Default, le_ab, r);
    let r = b.mk_pi(c_id, BinderInfo::Default, c.int_type.clone(), r);
    let r = b.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), r);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// Body:
/// ```text
/// λ (a b c : Int) (h1 : Int.le a b) (h2 : Int.lt b c) =>
///   Int.le_trans (a+1) (b+1) c (Int.add_le_add_right a b h1 one) h2
/// ```
fn build_value(c: &IntLtOfLeOfLtConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let (c_id, cc) = b.fresh_local(c.int_type.clone());
    let le_ab = c.le(a.clone(), bv.clone());
    let lt_bc = c.lt(bv.clone(), cc.clone());
    let (h1_id, h1) = b.fresh_local(le_ab.clone());
    let (h2_id, h2) = b.fresh_local(lt_bc.clone());

    let one = c.one();
    let a_plus_one = c.add(a.clone(), one.clone());
    let b_plus_one = c.add(bv.clone(), one.clone());

    // step1 := Int.add_le_add_right a b h1 one : Int.le (a+1) (b+1)
    let step1 = Expr::apps(
        c.add_le_add_right.clone(),
        [a.clone(), bv.clone(), h1.clone(), one],
    );

    // Int.le_trans (a+1) (b+1) c step1 h2 : Int.le (a+1) c ≡ Int.lt a c
    //   (h2 : Int.lt b c ≡ Int.le (b+1) c fills the second le slot.)
    let proof = Expr::apps(
        c.le_trans.clone(),
        [a_plus_one, b_plus_one, cc.clone(), step1, h2.clone()],
    );

    let val = b.mk_lam(h2_id, BinderInfo::Default, lt_bc, proof);
    let val = b.mk_lam(h1_id, BinderInfo::Default, le_ab, val);
    let val = b.mk_lam(c_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = b.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `Int.lt_of_le_of_lt` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_ord()` has registered `Int.lt`, `Int.le`,
    ///           `Int.add`, `Int.ofNat`.
    /// ENSURES: On success, `Int.lt_of_le_of_lt` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.lt_of_le_of_lt` is already registered with
    ///          any declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_int_lt_of_le_of_lt_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.lt_of_le_of_lt");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_ord()?;
        // Constructive dependencies.
        self.register_int_le_trans_proof()?;
        self.register_int_add_le_add_right_proof()?;

        let c = IntLtOfLeOfLtConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. Adds `1` on the right of
        // `h1 : Int.le a b` (constructive `Int.add_le_add_right`) to get
        // `Int.le (a+1) (b+1)`, then chains with `h2 : Int.lt b c` (≡
        // `Int.le (b+1) c`) via `Int.le_trans` to yield `Int.le (a+1) c`, which
        // matches the goal `Int.lt a c` by delta on `Int.lt`. No `sorry`, no
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
    fn test_int_lt_of_le_of_lt_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_lt_of_le_of_lt_proof()
            .expect("first registration");
        env.register_int_lt_of_le_of_lt_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.lt_of_le_of_lt"))
            .expect("Int.lt_of_le_of_lt should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_lt_of_le_of_lt_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_lt_of_le_of_lt_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.lt_of_le_of_lt"))
            .expect("Int.lt_of_le_of_lt is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.lt_of_le_of_lt must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }

    #[test]
    fn test_int_lt_of_le_of_lt_proof_quality_constructive() {
        use crate::env::ProofQuality;
        let mut env = Environment::new();
        env.register_int_lt_of_le_of_lt_proof().unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Int.lt_of_le_of_lt"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.lt_of_le_of_lt must be Constructive, got {:?}",
            quality
        );
    }
}
