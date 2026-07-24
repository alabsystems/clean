// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.lt_of_add_lt_add_left : ∀ a b c : Int,
//!    Int.lt (Int.add a b) (Int.add a c) → Int.lt b c`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `order_int.rs::init_int_ord_lemmas` with a `Declaration::Theorem`.
//!
//! # Definitions in play
//!
//! ```text
//! Int.le a b := Int.NonNeg (Int.sub b a)             -- reducible Definition
//! Int.lt a b := Int.le (Int.add a (Int.ofNat 1)) b   -- reducible Definition
//! ```
//!
//! So `h : Int.lt (a+b) (a+c)` delta-reduces to `Int.le ((a+b)+1) (a+c)` ≡
//! `Int.NonNeg (Int.sub (a+c) ((a+b)+1))` and the goal `Int.lt b c` to
//! `Int.le (b+1) c`.
//!
//! # Proof sketch
//!
//! First reassociate the strict premise into a common-left-addend `le`:
//! `(a+b)+1 = a+(b+1)` (`Int.add_assoc a b 1`). Transport `h` forward with
//! motive `fun x => Int.NonNeg (Int.sub (a+c) x)`:
//!
//! ```text
//! reassoc := @Eq.subst.{1} Int (fun x => Int.NonNeg (Int.sub (a+c) x))
//!   ((a+b)+1) (a+(b+1))
//!   (Int.add_assoc a b 1)
//!   h
//!   : Int.NonNeg (Int.sub (a+c) (a+(b+1)))   ≡   Int.le (a+(b+1)) (a+c)
//! ```
//!
//! Then cancel the common left addend `a` with the constructive
//! `Int.le_of_add_le_add_left a (b+1) c reassoc : Int.le (b+1) c`, which is
//! definitionally the goal `Int.lt b c`.
//!
//! # Axiom closure
//!
//! Depends only on the constructive `Int.add_assoc` and
//! `Int.le_of_add_le_add_left` theorems plus the foundational `Eq.subst`.
//! Neither is a `Declaration::Axiom`, so
//! `env.axiom_deps("Int.lt_of_add_lt_add_left")` is empty and
//! `env.proof_quality("Int.lt_of_add_lt_add_left") == ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntLtOfAddLtAddLeftConsts {
    int_type: Expr,
    int_le: Expr,
    int_lt: Expr,
    int_add: Expr,
    int_sub: Expr,
    int_of_nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nonneg: Expr,
    add_assoc: Expr,
    le_of_add_le_add_left: Expr,
    eq_subst: Expr,
}

impl IntLtOfAddLtAddLeftConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            int_le: Expr::const_(Name::from_string("Int.le"), vec![]),
            int_lt: Expr::const_(Name::from_string("Int.lt"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_sub: Expr::const_(Name::from_string("Int.sub"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nonneg: Expr::const_(Name::from_string("Int.NonNeg"), vec![]),
            add_assoc: Expr::const_(Name::from_string("Int.add_assoc"), vec![]),
            le_of_add_le_add_left: Expr::const_(
                Name::from_string("Int.le_of_add_le_add_left"),
                vec![],
            ),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![type1]),
        }
    }

    fn lt(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_lt.clone(), x), y)
    }

    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), x), y)
    }

    fn sub(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_sub.clone(), x), y)
    }

    /// `Int.ofNat (Nat.succ Nat.zero)`.
    fn one(&self) -> Expr {
        Expr::app(
            self.int_of_nat.clone(),
            Expr::app(self.nat_succ.clone(), self.nat_zero.clone()),
        )
    }
}

/// Build `∀ a b c : Int, Int.lt (a+b) (a+c) → Int.lt b c`.
fn build_type(c: &IntLtOfAddLtAddLeftConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let (c_id, cc) = b.fresh_local(c.int_type.clone());
    let premise = c.lt(c.add(a.clone(), bv.clone()), c.add(a.clone(), cc.clone()));
    let conclusion = c.lt(bv.clone(), cc.clone());
    let (h_id, _h) = b.fresh_local(premise.clone());
    let r = b.mk_pi(h_id, BinderInfo::Default, premise, conclusion);
    let r = b.mk_pi(c_id, BinderInfo::Default, c.int_type.clone(), r);
    let r = b.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), r);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// Body:
/// ```text
/// λ (a b c : Int) (h : Int.lt (a+b) (a+c)) =>
///   Int.le_of_add_le_add_left a (b+1) c
///     (@Eq.subst.{1} Int (fun x => Int.NonNeg (Int.sub (a+c) x))
///        ((a+b)+1) (a+(b+1)) (Int.add_assoc a b 1) h)
/// ```
fn build_value(c: &IntLtOfAddLtAddLeftConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let (c_id, cc) = b.fresh_local(c.int_type.clone());
    let premise = c.lt(c.add(a.clone(), bv.clone()), c.add(a.clone(), cc.clone()));
    let (h_id, h) = b.fresh_local(premise.clone());

    let one = c.one();
    let b_plus_one = c.add(bv.clone(), one.clone());
    let a_plus_c = c.add(a.clone(), cc.clone());
    let a_plus_b = c.add(a.clone(), bv.clone());
    // premise subtrahend term: (a+b)+1
    let ab_plus_one = c.add(a_plus_b.clone(), one.clone());
    // reassociated term: a+(b+1)
    let a_plus_b1 = c.add(a.clone(), b_plus_one.clone());

    // motive: fun x : Int => Int.NonNeg (Int.sub (a+c) x)
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(c.int_type.clone());
        let body = Expr::app(c.nonneg.clone(), c.sub(a_plus_c.clone(), x));
        let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
        mb.finish_child(lam)
    };

    // Int.add_assoc a b 1 : Eq Int ((a+b)+1) (a+(b+1))
    let assoc = Expr::apps(c.add_assoc.clone(), [a.clone(), bv.clone(), one.clone()]);

    // reassoc := @Eq.subst.{1} Int motive ((a+b)+1) (a+(b+1)) assoc h
    //   : Int.NonNeg (Int.sub (a+c) (a+(b+1))) ≡ Int.le (a+(b+1)) (a+c)
    let reassoc = Expr::apps(
        c.eq_subst.clone(),
        [
            c.int_type.clone(),
            motive,
            ab_plus_one,
            a_plus_b1.clone(),
            assoc,
            h.clone(),
        ],
    );

    // Int.le_of_add_le_add_left a (b+1) c reassoc : Int.le (b+1) c ≡ Int.lt b c
    let proof = Expr::apps(
        c.le_of_add_le_add_left.clone(),
        [a.clone(), b_plus_one, cc.clone(), reassoc],
    );

    let val = b.mk_lam(h_id, BinderInfo::Default, premise, proof);
    let val = b.mk_lam(c_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = b.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `Int.lt_of_add_lt_add_left` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_ord()` has registered `Int.lt`, `Int.le`,
    ///           `Int.NonNeg`, `Int.add`, `Int.sub`, `Int.ofNat`.
    /// REQUIRES: `self.init_eq()` has registered `Eq.subst`.
    /// ENSURES: On success, `Int.lt_of_add_lt_add_left` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.lt_of_add_lt_add_left` is already registered
    ///          with any declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_int_lt_of_add_lt_add_left_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.lt_of_add_lt_add_left");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_ord()?;
        self.init_eq()?;
        // Constructive dependencies.
        self.register_int_add_assoc_proof()?;
        self.register_int_le_of_add_le_add_left_proof()?;

        let c = IntLtOfAddLtAddLeftConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. Reassociates the strict
        // premise `h : Int.lt (a+b) (a+c) ≡ Int.le ((a+b)+1) (a+c)` along
        // `Int.add_assoc a b 1 : Eq ((a+b)+1) (a+(b+1))` via `@Eq.subst.{1}`
        // (motive `fun x => Int.NonNeg (Int.sub (a+c) x)`) to obtain
        // `Int.le (a+(b+1)) (a+c)`, then cancels the common left addend with the
        // constructive `Int.le_of_add_le_add_left a (b+1) c`, yielding
        // `Int.le (b+1) c` ≡ `Int.lt b c`. No `sorry`, no self-reference, no
        // domain-axiom dependency. Replaces the prior `Declaration::Axiom` in
        // `order_int.rs::init_int_ord_lemmas`.
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
    fn test_int_lt_of_add_lt_add_left_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_lt_of_add_lt_add_left_proof()
            .expect("first registration");
        env.register_int_lt_of_add_lt_add_left_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.lt_of_add_lt_add_left"))
            .expect("Int.lt_of_add_lt_add_left should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_lt_of_add_lt_add_left_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_lt_of_add_lt_add_left_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.lt_of_add_lt_add_left"))
            .expect("Int.lt_of_add_lt_add_left is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.lt_of_add_lt_add_left must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }

    #[test]
    fn test_int_lt_of_add_lt_add_left_proof_quality_constructive() {
        use crate::env::ProofQuality;
        let mut env = Environment::new();
        env.register_int_lt_of_add_lt_add_left_proof().unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Int.lt_of_add_lt_add_left"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.lt_of_add_lt_add_left must be Constructive, got {:?}",
            quality
        );
    }
}
