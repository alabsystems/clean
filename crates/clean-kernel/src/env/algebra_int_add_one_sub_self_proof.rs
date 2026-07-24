// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.add_one_sub_self : ∀ a : Int,
//!    Eq Int (Int.sub (Int.add a (Int.ofNat (Nat.succ Nat.zero))) a)
//!           (Int.ofNat (Nat.succ Nat.zero))`.
//!
//! This is the arithmetic identity `(a + 1) - a = 1` (with `1` in the canonical
//! `Int.ofNat (Nat.succ Nat.zero)` form matching the `Int.lt` definition). It is
//! a fresh constructive building block used by
//! `algebra_int_le_self_add_one_proof.rs`.
//!
//! # Proof sketch
//!
//! Let `one = Int.ofNat (Nat.succ Nat.zero)`, `na = Int.neg a`. `Int.sub x y` is
//! the reducible Definition `Int.add x (Int.neg y)`, so the goal LHS is
//! definitionally `Int.add (Int.add a one) (Int.neg a)`. The chain (over
//! `Int.add`):
//!
//! ```text
//! (a + one) + na
//!   = (one + a) + na        -- congrArg (· + na) (Int.add_comm a one)
//!   = one + (a + na)        -- Int.add_assoc one a na
//!   = one + Int.zero        -- congrArg (one + ·) (Int.add_neg_self a)
//!   = one                   -- Int.add_zero one
//! ```
//!
//! composed by `@Eq.trans.{1}`.
//!
//! # Axiom closure
//!
//! Depends only on the constructive `Int.add_comm`, `Int.add_assoc`,
//! `Int.add_neg_self`, `Int.add_zero` theorems and `Eq.trans` / `congrArg`.
//! Empty domain-axiom closure.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntAddOneSubSelfConsts {
    int_type: Expr,
    int_add: Expr,
    int_neg: Expr,
    int_sub: Expr,
    int_of_nat: Expr,
    int_zero: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    add_comm: Expr,
    add_assoc: Expr,
    add_neg_self: Expr,
    add_zero: Expr,
    eq_const: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
}

impl IntAddOneSubSelfConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_neg: Expr::const_(Name::from_string("Int.neg"), vec![]),
            int_sub: Expr::const_(Name::from_string("Int.sub"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_zero: Expr::const_(Name::from_string("Int.zero"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            add_comm: Expr::const_(Name::from_string("Int.add_comm"), vec![]),
            add_assoc: Expr::const_(Name::from_string("Int.add_assoc"), vec![]),
            add_neg_self: Expr::const_(Name::from_string("Int.add_neg_self"), vec![]),
            add_zero: Expr::const_(Name::from_string("Int.add_zero"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
        }
    }

    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), x), y)
    }

    fn neg(&self, x: Expr) -> Expr {
        Expr::app(self.int_neg.clone(), x)
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

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }

    fn trans(&self, x: Expr, y: Expr, z: Expr, hxy: Expr, hyz: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.int_type.clone(), x, y, z, hxy, hyz],
        )
    }

    fn congr_arg(&self, a1: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.int_type.clone(), self.int_type.clone(), a1, a2, f, h],
        )
    }

    fn add_assoc(&self, x: Expr, y: Expr, z: Expr) -> Expr {
        Expr::app(Expr::app(Expr::app(self.add_assoc.clone(), x), y), z)
    }

    fn add_comm(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.add_comm.clone(), x), y)
    }
}

/// Build `∀ a : Int, Eq Int (Int.sub (Int.add a one) a) one`.
fn build_type(c: &IntAddOneSubSelfConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let lhs = c.sub(c.add(a.clone(), c.one()), a.clone());
    let concl = c.eq_int(lhs, c.one());
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), concl);
    b.finish(r)
}

fn build_value(c: &IntAddOneSubSelfConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());

    let one = c.one();
    let na = c.neg(a.clone());
    let a_plus_one = c.add(a.clone(), one.clone());
    let one_plus_a = c.add(one.clone(), a.clone());
    let a_plus_na = c.add(a.clone(), na.clone());

    // e0 : (a + one) + na   (= goal LHS after Int.sub delta)
    let e0 = c.add(a_plus_one.clone(), na.clone());
    // e1 : (one + a) + na
    let e1 = c.add(one_plus_a.clone(), na.clone());
    // e2 : one + (a + na)
    let e2 = c.add(one.clone(), a_plus_na.clone());
    // e3 : one + Int.zero
    let e3 = c.add(one.clone(), c.int_zero.clone());
    // e4 : one  (= goal RHS)
    let e4 = one.clone();

    // Step 0→1: congrArg (· + na) (Int.add_comm a one : a + one = one + a).
    let comm_a_one = c.add_comm(a.clone(), one.clone());
    let f_plus_na = {
        let mut fb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = fb.fresh_local(c.int_type.clone());
        let body = c.add(t.clone(), na.clone());
        let lam = fb.mk_lam(t_id, BinderInfo::Default, c.int_type.clone(), body);
        fb.finish_child(lam)
    };
    let step01 = c.congr_arg(
        a_plus_one.clone(),
        one_plus_a.clone(),
        f_plus_na,
        comm_a_one,
    );

    // Step 1→2: Int.add_assoc one a na : (one + a) + na = one + (a + na).
    let step12 = c.add_assoc(one.clone(), a.clone(), na.clone());

    // Step 2→3: congrArg (one + ·) (Int.add_neg_self a : a + na = Int.zero).
    let add_neg_self_a = Expr::app(c.add_neg_self.clone(), a.clone());
    let f_one_plus = {
        let mut fb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = fb.fresh_local(c.int_type.clone());
        let body = c.add(one.clone(), t.clone());
        let lam = fb.mk_lam(t_id, BinderInfo::Default, c.int_type.clone(), body);
        fb.finish_child(lam)
    };
    let step23 = c.congr_arg(
        a_plus_na.clone(),
        c.int_zero.clone(),
        f_one_plus,
        add_neg_self_a,
    );

    // Step 3→4: Int.add_zero one : one + Int.zero = one.
    let step34 = Expr::app(c.add_zero.clone(), one.clone());

    // Compose e0 = e1 = e2 = e3 = e4.
    let t01_2 = c.trans(e0.clone(), e1.clone(), e2.clone(), step01, step12);
    let t01_3 = c.trans(e0.clone(), e2.clone(), e3.clone(), t01_2, step23);
    let proof = c.trans(e0, e3, e4, t01_3, step34);

    let val = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), proof);
    b.finish(val)
}

impl Environment {
    /// Register `Int.add_one_sub_self` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int.add`, `Int.neg`,
    ///           `Int.sub`, `Int.ofNat`, `Int.zero`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.trans`, `congrArg`.
    /// ENSURES: On success, `Int.add_one_sub_self` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_int_add_one_sub_self_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.add_one_sub_self");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_eq()?;
        self.register_int_add_comm_proof()?;
        self.register_int_add_assoc_proof()?;
        self.register_int_add_neg_self_proof()?;
        self.register_int_add_zero_proof()?;

        let c = IntAddOneSubSelfConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. A four-step `@Eq.trans.{1}`
        // chain rewriting `(a + 1) - a` to `1` via the constructive
        // `Int.add_comm`, `Int.add_assoc`, `Int.add_neg_self`, `Int.add_zero`
        // theorems plus `congrArg`. `Int.sub` delta-reduces to `Int.add _ (Int.neg
        // _)`, so the chain endpoints are definitionally the stated goal. No
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
    fn test_int_add_one_sub_self_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_add_one_sub_self_proof()
            .expect("first registration");
        env.register_int_add_one_sub_self_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.add_one_sub_self"))
            .expect("Int.add_one_sub_self should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_add_one_sub_self_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_add_one_sub_self_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.add_one_sub_self"))
            .expect("registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.add_one_sub_self must have empty axiom closure, got {:?}",
            domain_deps
        );
    }
}
