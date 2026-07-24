// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.sub_add_one_self : ∀ a : Int,
//!    Eq Int (Int.sub a (Int.add a (Int.ofNat (Nat.succ Nat.zero)))) (Int.negSucc Nat.zero)`.
//!
//! This is the arithmetic identity `a - (a + 1) = -1` (with `-1` in canonical
//! `Int.negSucc 0` form). It is a fresh constructive building block used by
//! `algebra_int_lt_irrefl_proof.rs`.
//!
//! # Proof sketch
//!
//! Let `one = Int.ofNat (Nat.succ Nat.zero)`, `n1 = Int.neg one`. `Int.sub x y`
//! is the reducible Definition `Int.add x (Int.neg y)`, so the goal LHS is
//! definitionally `Int.add a (Int.neg (Int.add a one))`. The chain (over
//! `Int.add`):
//!
//! ```text
//! a + neg(a + one)
//!   = a + (neg a + n1)        -- congrArg (a + ·) (Int.neg_add a one)
//!   = (a + neg a) + n1        -- Eq.symm (Int.add_assoc a (neg a) n1)
//!   = Int.zero + n1           -- congrArg (· + n1) (Int.add_neg_self a)
//!   = n1                      -- Int.zero_add n1
//! ```
//!
//! and `n1 = Int.neg (Int.ofNat (Nat.succ Nat.zero))` reduces (delta on
//! `Int.neg` + iota) to `Int.negSucc Nat.zero`, so the final endpoint is
//! definitionally the stated RHS.
//!
//! # Axiom closure
//!
//! Depends only on the constructive `Int.neg_add`, `Int.add_assoc`,
//! `Int.add_neg_self`, `Int.zero_add` theorems and `Eq.trans` / `Eq.symm` /
//! `congrArg`. Empty domain-axiom closure.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntSubAddOneSelfConsts {
    int_type: Expr,
    int_add: Expr,
    int_neg: Expr,
    int_sub: Expr,
    int_of_nat: Expr,
    int_neg_succ: Expr,
    int_zero: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    neg_add: Expr,
    add_assoc: Expr,
    add_neg_self: Expr,
    zero_add: Expr,
    eq_const: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
}

impl IntSubAddOneSelfConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_neg: Expr::const_(Name::from_string("Int.neg"), vec![]),
            int_sub: Expr::const_(Name::from_string("Int.sub"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            int_zero: Expr::const_(Name::from_string("Int.zero"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            neg_add: Expr::const_(Name::from_string("Int.neg_add"), vec![]),
            add_assoc: Expr::const_(Name::from_string("Int.add_assoc"), vec![]),
            add_neg_self: Expr::const_(Name::from_string("Int.add_neg_self"), vec![]),
            zero_add: Expr::const_(Name::from_string("Int.zero_add"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
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

    /// `Int.negSucc Nat.zero`.
    fn neg_succ_zero(&self) -> Expr {
        Expr::app(self.int_neg_succ.clone(), self.nat_zero.clone())
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

    fn symm(&self, x: Expr, y: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.int_type.clone(), x, y, h])
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
}

/// Build `∀ a : Int, Eq Int (Int.sub a (Int.add a one)) (Int.negSucc Nat.zero)`.
fn build_type(c: &IntSubAddOneSelfConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let lhs = c.sub(a.clone(), c.add(a.clone(), c.one()));
    let concl = c.eq_int(lhs, c.neg_succ_zero());
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), concl);
    b.finish(r)
}

fn build_value(c: &IntSubAddOneSelfConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());

    let one = c.one();
    let neg_a = c.neg(a.clone());
    let n1 = c.neg(one.clone()); // neg one (≡ negSucc 0)
    let a_plus_one = c.add(a.clone(), one.clone());

    // e0 : a + neg(a + one)   (= goal LHS after Int.sub delta)
    let neg_a_one = c.neg(a_plus_one.clone());
    let e0 = c.add(a.clone(), neg_a_one.clone());
    // e1 : a + (neg a + n1)
    let neg_a_plus_n1 = c.add(neg_a.clone(), n1.clone());
    let e1 = c.add(a.clone(), neg_a_plus_n1.clone());
    // e2 : (a + neg a) + n1
    let a_plus_neg_a = c.add(a.clone(), neg_a.clone());
    let e2 = c.add(a_plus_neg_a.clone(), n1.clone());
    // e3 : Int.zero + n1
    let e3 = c.add(c.int_zero.clone(), n1.clone());
    // e4 : n1   (≡ negSucc 0 = goal RHS)
    let e4 = n1.clone();

    // Step 0→1: congrArg (a + ·) (Int.neg_add a one : neg(a+one) = neg a + n1).
    let neg_add_a_one = Expr::app(Expr::app(c.neg_add.clone(), a.clone()), one.clone());
    let f_a_plus = {
        let mut fb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = fb.fresh_local(c.int_type.clone());
        let body = c.add(a.clone(), t.clone());
        let lam = fb.mk_lam(t_id, BinderInfo::Default, c.int_type.clone(), body);
        fb.finish_child(lam)
    };
    let step01 = c.congr_arg(
        neg_a_one.clone(),
        neg_a_plus_n1.clone(),
        f_a_plus,
        neg_add_a_one,
    );

    // Step 1→2: Eq.symm (Int.add_assoc a (neg a) n1 : (a+neg a)+n1 = a+(neg a+n1)).
    let assoc = c.add_assoc(a.clone(), neg_a.clone(), n1.clone()); // Eq e2 e1
    let step12 = c.symm(e2.clone(), e1.clone(), assoc);

    // Step 2→3: congrArg (· + n1) (Int.add_neg_self a : a + neg a = Int.zero).
    let add_neg_self_a = Expr::app(c.add_neg_self.clone(), a.clone());
    let f_plus_n1 = {
        let mut fb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = fb.fresh_local(c.int_type.clone());
        let body = c.add(t.clone(), n1.clone());
        let lam = fb.mk_lam(t_id, BinderInfo::Default, c.int_type.clone(), body);
        fb.finish_child(lam)
    };
    let step23 = c.congr_arg(
        a_plus_neg_a.clone(),
        c.int_zero.clone(),
        f_plus_n1,
        add_neg_self_a,
    );

    // Step 3→4: Int.zero_add n1 : Int.zero + n1 = n1.
    let step34 = Expr::app(c.zero_add.clone(), n1.clone());

    // Compose e0 = e1 = e2 = e3 = e4.
    let t01_2 = c.trans(e0.clone(), e1.clone(), e2.clone(), step01, step12);
    let t01_3 = c.trans(e0.clone(), e2.clone(), e3.clone(), t01_2, step23);
    let proof = c.trans(e0, e3, e4, t01_3, step34);

    let val = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), proof);
    b.finish(val)
}

impl Environment {
    /// Register `Int.sub_add_one_self` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int.add`, `Int.neg`,
    ///           `Int.sub`, `Int.ofNat`, `Int.negSucc`, `Int.zero`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.trans`, `Eq.symm`,
    ///           `congrArg`.
    /// ENSURES: On success, `Int.sub_add_one_self` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_int_sub_add_one_self_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.sub_add_one_self");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_eq()?;
        self.register_int_neg_add_proof()?;
        self.register_int_add_assoc_proof()?;
        self.register_int_add_neg_self_proof()?;
        self.register_int_zero_add_proof()?;

        let c = IntSubAddOneSelfConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. A four-step `@Eq.trans.{1}`
        // chain rewriting `a - (a + 1)` to `-1` via the constructive
        // `Int.neg_add`, `Int.add_assoc`, `Int.add_neg_self`, `Int.zero_add`
        // theorems plus `congrArg`/`Eq.symm`. `Int.sub` delta-reduces and
        // `Int.neg (Int.ofNat 1)` iota-reduces to `Int.negSucc 0`, so the chain
        // endpoints are definitionally the stated goal. No `sorry`, no
        // self-reference, no domain-axiom dependency.
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
    fn test_int_sub_add_one_self_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_sub_add_one_self_proof()
            .expect("first registration");
        env.register_int_sub_add_one_self_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.sub_add_one_self"))
            .expect("Int.sub_add_one_self should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_sub_add_one_self_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_sub_add_one_self_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.sub_add_one_self"))
            .expect("registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.sub_add_one_self must have empty axiom closure, got {:?}",
            domain_deps
        );
    }
}
