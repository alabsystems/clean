// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.lt_trans : ∀ a b c : Int, Int.lt a b → Int.lt b c → Int.lt a c`.
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
//! So the hypotheses delta-reduce to `h1 : Int.le (a + 1) b` and
//! `h2 : Int.le (b + 1) c`, and the goal `Int.lt a c` to `Int.le (a + 1) c`.
//!
//! # Proof sketch
//!
//! Two `Int.le_trans` steps with the `+1` bridge `Int.le_self_add_one`:
//!
//! ```text
//! step1 := Int.le_trans (a+1) b (b+1) h1 (Int.le_self_add_one b)
//!            : Int.le (a + 1) (b + 1)
//! Int.le_trans (a+1) (b+1) c step1 h2 : Int.le (a + 1) c   ≡   Int.lt a c
//! ```
//!
//! The kernel accepts `h1 : Int.lt a b` / `h2 : Int.lt b c` in the
//! `Int.le (a+1) b` / `Int.le (b+1) c` slots and the final `Int.le (a+1) c`
//! against the goal `Int.lt a c`, all by delta-reduction of `Int.lt`.
//!
//! # Axiom closure
//!
//! Depends only on the constructive `Int.le_trans` and `Int.le_self_add_one`
//! theorems. Neither is a `Declaration::Axiom`, so
//! `env.axiom_deps("Int.lt_trans")` is empty and
//! `env.proof_quality("Int.lt_trans") == ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntLtTransConsts {
    int_type: Expr,
    int_lt: Expr,
    int_add: Expr,
    int_of_nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    le_trans: Expr,
    le_self_add_one: Expr,
}

impl IntLtTransConsts {
    fn new() -> Self {
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            int_lt: Expr::const_(Name::from_string("Int.lt"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            le_trans: Expr::const_(Name::from_string("Int.le_trans"), vec![]),
            le_self_add_one: Expr::const_(Name::from_string("Int.le_self_add_one"), vec![]),
        }
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

/// Build `∀ a b c : Int, Int.lt a b → Int.lt b c → Int.lt a c`.
fn build_type(c: &IntLtTransConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let (c_id, cc) = b.fresh_local(c.int_type.clone());
    let lt_ab = c.lt(a.clone(), bv.clone());
    let lt_bc = c.lt(bv.clone(), cc.clone());
    let lt_ac = c.lt(a.clone(), cc.clone());
    let (h2_id, _h2) = b.fresh_local(lt_bc.clone());
    let (h1_id, _h1) = b.fresh_local(lt_ab.clone());
    let r = b.mk_pi(h2_id, BinderInfo::Default, lt_bc, lt_ac);
    let r = b.mk_pi(h1_id, BinderInfo::Default, lt_ab, r);
    let r = b.mk_pi(c_id, BinderInfo::Default, c.int_type.clone(), r);
    let r = b.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), r);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// Body:
/// ```text
/// λ (a b c : Int) (h1 : Int.lt a b) (h2 : Int.lt b c) =>
///   Int.le_trans (a+1) (b+1) c
///     (Int.le_trans (a+1) b (b+1) h1 (Int.le_self_add_one b))
///     h2
/// ```
fn build_value(c: &IntLtTransConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let (c_id, cc) = b.fresh_local(c.int_type.clone());
    let lt_ab = c.lt(a.clone(), bv.clone());
    let lt_bc = c.lt(bv.clone(), cc.clone());
    let (h1_id, h1) = b.fresh_local(lt_ab.clone());
    let (h2_id, h2) = b.fresh_local(lt_bc.clone());

    let a_plus_one = c.add(a.clone(), c.one());
    let b_plus_one = c.add(bv.clone(), c.one());

    // Int.le_self_add_one b : Int.le b (b + 1)
    let bridge_b = Expr::app(c.le_self_add_one.clone(), bv.clone());

    // step1 := Int.le_trans (a+1) b (b+1) h1 bridge_b : Int.le (a+1) (b+1)
    //   (h1 : Int.lt a b ≡ Int.le (a+1) b fills the first le slot.)
    let step1 = Expr::apps(
        c.le_trans.clone(),
        [
            a_plus_one.clone(),
            bv.clone(),
            b_plus_one.clone(),
            h1.clone(),
            bridge_b,
        ],
    );

    // Int.le_trans (a+1) (b+1) c step1 h2 : Int.le (a+1) c ≡ Int.lt a c
    //   (h2 : Int.lt b c ≡ Int.le (b+1) c fills the second le slot.)
    let proof = Expr::apps(
        c.le_trans.clone(),
        [a_plus_one, b_plus_one, cc.clone(), step1, h2.clone()],
    );

    let val = b.mk_lam(h2_id, BinderInfo::Default, lt_bc, proof);
    let val = b.mk_lam(h1_id, BinderInfo::Default, lt_ab, val);
    let val = b.mk_lam(c_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = b.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `Int.lt_trans` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_ord()` has registered `Int.lt`, `Int.le`,
    ///           `Int.add`, `Int.ofNat`.
    /// ENSURES: On success, `Int.lt_trans` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.lt_trans` is already registered with any
    ///          declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_int_lt_trans_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.lt_trans");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_ord()?;
        // Constructive dependencies.
        self.register_int_le_trans_proof()?;
        self.register_int_le_self_add_one_proof()?;

        let c = IntLtTransConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. Two `Int.le_trans` steps
        // with the constructive `+1` bridge `Int.le_self_add_one b`: the
        // hypotheses `h1 : Int.lt a b` / `h2 : Int.lt b c` delta-reduce to
        // `Int.le (a+1) b` / `Int.le (b+1) c`, and the result `Int.le (a+1) c`
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
    fn test_int_lt_trans_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_lt_trans_proof()
            .expect("first registration");
        env.register_int_lt_trans_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.lt_trans"))
            .expect("Int.lt_trans should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_lt_trans_proof_body_uses_le_trans() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_lt_trans_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.lt_trans"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        // Peel the five outer λ binders (a, b, c, h1, h2), then the head must be
        // Int.le_trans (the outer transitivity step).
        let mut body: Expr = value.clone();
        for _ in 0..5 {
            body = match body.kind() {
                ExprKind::Lam(_, _, inner) => (**inner).clone(),
                k => panic!("expected outer λ, got {:?}", k),
            };
        }
        let mut head: Expr = body;
        while let ExprKind::App(f, _) = head.kind() {
            head = (**f).clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Int.le_trans",
                "Int.lt_trans proof root must be Int.le_trans"
            ),
            k => panic!("expected Const(Int.le_trans), got {:?}", k),
        }
    }

    #[test]
    fn test_int_lt_trans_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_lt_trans_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.lt_trans"))
            .expect("Int.lt_trans is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.lt_trans must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }

    #[test]
    fn test_int_lt_trans_proof_quality_constructive() {
        use crate::env::ProofQuality;
        let mut env = Environment::new();
        env.register_int_lt_trans_proof().unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Int.lt_trans"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.lt_trans must be Constructive, got {:?}",
            quality
        );
    }
}
