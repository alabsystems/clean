// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.negOfNat_add : ∀ a b : Nat,
//!     Eq Int (Int.add (Int.negOfNat a) (Int.negOfNat b)) (Int.negOfNat (Nat.add a b))`.
//!
//! Adding two non-positive integers `(-a) + (-b)` collapses to `-(a + b)`.
//! Used by the all-negative leaves of `Int.left_distrib`
//! (`a * (negSucc p + negSucc r)`) to fold a sum of two `Int.negOfNat`
//! products back into a single `Int.negOfNat`.
//!
//! # Proof sketch
//!
//! `Int.neg` and `Int.negOfNat` are BOTH the reducible Definition
//! `λ n => Nat.rec (Int.ofNat 0) (λ k _ => Int.negSucc k) n` on a `Nat`, so
//! `Int.neg (Int.ofNat a)` and `Int.negOfNat a` are *definitionally equal*.
//! `Int.add (Int.ofNat a) (Int.ofNat b) ι→ Int.ofNat (Nat.add a b)`. Hence:
//!
//! ```text
//! Int.add (negOfNat a) (negOfNat b)
//!   ≡ Int.add (neg (ofNat a)) (neg (ofNat b))            (neg ofNat ≡ negOfNat)
//! Int.neg_add (ofNat a) (ofNat b)
//!   : Eq (neg (add (ofNat a) (ofNat b))) (add (neg (ofNat a)) (neg (ofNat b)))
//! neg (add (ofNat a) (ofNat b)) ≡ neg (ofNat (Nat.add a b)) ≡ negOfNat (Nat.add a b)
//! ```
//!
//! So the proof term is simply
//! `Eq.symm (Int.neg_add (Int.ofNat a) (Int.ofNat b))`: its type
//! `Eq (add (neg (ofNat a)) (neg (ofNat b))) (neg (add (ofNat a) (ofNat b)))`
//! is definitionally equal to the declared
//! `Eq (add (negOfNat a) (negOfNat b)) (negOfNat (Nat.add a b))`.
//!
//! # Axiom closure
//!
//! Mentions only `Int`, `Int.add`, `Int.neg`, `Int.ofNat`, `Int.negOfNat`,
//! `Nat`, `Nat.add`, `Eq`, `Eq.symm`, and the constructive
//! `Declaration::Theorem` `Int.neg_add` (#3604). None are
//! `Declaration::Axiom`, so `env.axiom_deps("Int.negOfNat_add")` is empty and
//! the proof quality is `ProofQuality::Constructive`.
//!
//! Tracks #3604. Consumer: `algebra_int_left_distrib_proof.rs`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntNegOfNatAddConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_add: Expr,
    int_add: Expr,
    int_of_nat: Expr,
    int_neg: Expr,
    int_neg_of_nat: Expr,
    eq_const: Expr,
    eq_symm: Expr,
    int_neg_add: Expr,
}

impl IntNegOfNatAddConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg: Expr::const_(Name::from_string("Int.neg"), vec![]),
            int_neg_of_nat: Expr::const_(Name::from_string("Int.negOfNat"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1]),
            int_neg_add: Expr::const_(Name::from_string("Int.neg_add"), vec![]),
        }
    }

    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), x), y)
    }

    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }

    fn neg(&self, x: Expr) -> Expr {
        Expr::app(self.int_neg.clone(), x)
    }

    fn neg_of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_neg_of_nat.clone(), n)
    }

    fn nadd(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.nat_add.clone(), x), y)
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }

    fn symm_int(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.int_type.clone(), a, b, h])
    }

    /// `Int.neg_add x y : Eq (neg (add x y)) (add (neg x) (neg y))`.
    fn neg_add(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_neg_add.clone(), [x, y])
    }
}

/// Build
/// `∀ a b : Nat, Eq Int (Int.add (negOfNat a) (negOfNat b)) (negOfNat (Nat.add a b))`.
fn build_type(c: &IntNegOfNatAddConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat_type.clone());
    let (bv_id, bv) = b.fresh_local(c.nat_type.clone());
    let lhs = c.add(c.neg_of_nat(a.clone()), c.neg_of_nat(bv.clone()));
    let rhs = c.neg_of_nat(c.nadd(a.clone(), bv.clone()));
    let concl = c.eq_int(lhs, rhs);
    let ty = b.mk_pi(bv_id, BinderInfo::Default, c.nat_type.clone(), concl);
    let ty = b.mk_pi(a_id, BinderInfo::Default, c.nat_type.clone(), ty);
    b.finish(ty)
}

/// Body: `λ (a b : Nat) => Eq.symm (Int.neg_add (ofNat a) (ofNat b))`.
fn build_value(c: &IntNegOfNatAddConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (a_id, a) = vb.fresh_local(c.nat_type.clone());
    let (bv_id, bv) = vb.fresh_local(c.nat_type.clone());

    let of_a = c.of_nat(a.clone());
    let of_b = c.of_nat(bv.clone());
    // Int.neg_add (ofNat a) (ofNat b)
    //   : Eq (neg (add (ofNat a) (ofNat b))) (add (neg (ofNat a)) (neg (ofNat b)))
    let inner = c.neg_add(of_a.clone(), of_b.clone());
    let neg_sum = c.neg(c.add(of_a.clone(), of_b.clone()));
    let sum_negs = c.add(c.neg(of_a), c.neg(of_b));
    // Eq.symm: Eq (add (neg (ofNat a)) (neg (ofNat b))) (neg (add (ofNat a) (ofNat b)))
    let proof = c.symm_int(neg_sum, sum_negs, inner);

    let val = vb.mk_lam(bv_id, BinderInfo::Default, c.nat_type.clone(), proof);
    let val = vb.mk_lam(a_id, BinderInfo::Default, c.nat_type.clone(), val);
    vb.finish(val)
}

impl Environment {
    /// Register `Int.negOfNat_add` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int`, `Int.ofNat`,
    ///           `Int.negOfNat`, `Int.neg`, `Int.add`.
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.add`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.symm`.
    /// REQUIRES: `Int.neg_add` is registered as a constructive
    ///           `Declaration::Theorem`.
    /// ENSURES: On success, `Int.negOfNat_add` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_int_negofnat_add_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.negOfNat_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;
        self.register_int_neg_add_proof()?;

        let c = IntNegOfNatAddConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). The proof is
        // `Eq.symm (Int.neg_add (Int.ofNat a) (Int.ofNat b))`. It type-checks
        // because `Int.neg (Int.ofNat n)` and `Int.negOfNat n` are the SAME
        // reducible `Nat.rec` Definition (definitionally equal) and
        // `Int.add (Int.ofNat a) (Int.ofNat b) ι→ Int.ofNat (Nat.add a b)`,
        // making the symm'd `Int.neg_add` type defn-equal to the declared
        // conclusion. No `sorry`, no self-reference, no domain-axiom
        // dependency (`Int.neg_add` is constructive #3604).
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
    use crate::env::{ConstantKind, ProofQuality};

    #[test]
    fn test_int_negofnat_add_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_negofnat_add_proof()
            .expect("first registration");
        env.register_int_negofnat_add_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.negOfNat_add"))
            .expect("Int.negOfNat_add should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_negofnat_add_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_negofnat_add_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.negOfNat_add"))
            .expect("registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.negOfNat_add must have empty axiom closure, got {:?}",
            domain_deps
        );
    }

    #[test]
    fn test_int_negofnat_add_proof_quality_constructive() {
        let mut env = Environment::new();
        env.register_int_negofnat_add_proof().unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Int.negOfNat_add"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.negOfNat_add must be Constructive, got {:?}",
            quality
        );
    }
}
