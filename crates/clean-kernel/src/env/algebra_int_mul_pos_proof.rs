// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.mul_pos : ∀ a b : Int,
//!    Int.lt (Int.ofNat 0) a → Int.lt (Int.ofNat 0) b →
//!    Int.lt (Int.ofNat 0) (Int.mul a b)`.
//!
//! Registered as a `Declaration::Theorem` in `order_int.rs::init_int_ord_lemmas`.
//! Strict positivity of a product of two positives, derived from the general
//! product-monotonicity lemma `Int.mul_le_mul` (#3604).
//!
//! # Definitions in play
//!
//! ```text
//! Int.lt a b := Int.le (Int.add a (Int.ofNat 1)) b   -- reducible Definition
//! Int.le a b := Int.NonNeg (Int.sub b a)             -- reducible Definition
//! ```
//!
//! Hence `Int.lt 0 a ≡ Int.le (Int.add 0 1) a`, and `Int.add (ofNat 0) (ofNat 1)`
//! kernel-reduces to `Int.ofNat (Nat.add 0 1) ≡ Int.ofNat 1 = 1`, so
//! `Int.lt 0 a ≡ Int.le 1 a` definitionally. Likewise the goal `Int.lt 0 (a*b)`
//! ≡ `Int.le 1 (a*b)`.
//!
//! # Proof sketch
//!
//! Given `ha : Int.lt 0 a` (≡ `Int.le 1 a`) and `hb : Int.lt 0 b`
//! (≡ `Int.le 1 b`):
//!
//! 1. `h01 : Int.le 0 1 := Int.ofNat_zero_le (Nat.succ Nat.zero)`
//!    (`Int.ofNat_zero_le n : Int.le (ofNat 0) (ofNat n)`, here at `n = 1`).
//! 2. `Int.mul_le_mul 1 a 1 b ha hb h01 h01 : Int.le (Int.mul 1 1) (Int.mul a b)`.
//!    Since `Int.mul (ofNat 1) (ofNat 1)` reduces to `Int.ofNat (Nat.mul 1 1) ≡
//!    Int.ofNat 1 = 1`, this term is definitionally `Int.le 1 (a*b)` ≡
//!    `Int.lt 0 (a*b)`, the goal. No explicit transport needed.
//!
//! # Axiom closure
//!
//! Depends only on the constructive `Int.mul_le_mul` and `Int.ofNat_zero_le`
//! theorems. None is a `Declaration::Axiom`, so `env.axiom_deps("Int.mul_pos")`
//! is empty and the proof quality is `Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntMulPosConsts {
    int_type: Expr,
    int_lt: Expr,
    int_mul: Expr,
    int_of_nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    mul_le_mul: Expr,
    ofnat_zero_le: Expr,
}

impl IntMulPosConsts {
    fn new() -> Self {
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            int_lt: Expr::const_(Name::from_string("Int.lt"), vec![]),
            int_mul: Expr::const_(Name::from_string("Int.mul"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            mul_le_mul: Expr::const_(Name::from_string("Int.mul_le_mul"), vec![]),
            ofnat_zero_le: Expr::const_(Name::from_string("Int.ofNat_zero_le"), vec![]),
        }
    }

    fn nat_one(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.nat_zero.clone())
    }

    fn int_zero(&self) -> Expr {
        Expr::app(self.int_of_nat.clone(), self.nat_zero.clone())
    }

    fn int_one(&self) -> Expr {
        Expr::app(self.int_of_nat.clone(), self.nat_one())
    }

    fn mul(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_mul.clone(), x), y)
    }

    fn lt(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_lt.clone(), x), y)
    }

    fn pos(&self, x: Expr) -> Expr {
        self.lt(self.int_zero(), x)
    }
}

/// Build `∀ a b : Int, 0 < a → 0 < b → 0 < a*b`.
fn build_type(c: &IntMulPosConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let pos_a = c.pos(a.clone());
    let pos_b = c.pos(bv.clone());
    let concl = c.pos(c.mul(a.clone(), bv.clone()));
    let (hb_id, _hb) = b.fresh_local(pos_b.clone());
    let (ha_id, _ha) = b.fresh_local(pos_a.clone());
    let r = b.mk_pi(hb_id, BinderInfo::Default, pos_b, concl);
    let r = b.mk_pi(ha_id, BinderInfo::Default, pos_a, r);
    let r = b.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), r);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// Body of `Int.mul_pos`.
fn build_value(c: &IntMulPosConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let pos_a = c.pos(a.clone());
    let (ha_id, ha) = b.fresh_local(pos_a.clone());
    let pos_b = c.pos(bv.clone());
    let (hb_id, hb) = b.fresh_local(pos_b.clone());

    let one = c.int_one();

    // h01 : Int.le 0 1 := Int.ofNat_zero_le 1
    let h01 = Expr::app(c.ofnat_zero_le.clone(), c.nat_one());

    // Int.mul_le_mul 1 a 1 b ha hb h01 h01 : Int.le (1*1) (a*b)
    //   ≡ Int.le 1 (a*b) ≡ Int.lt 0 (a*b)  (kernel reduces 1*1 to 1, and
    //   0+1 to 1 inside Int.lt).
    // `ha : Int.lt 0 a ≡ Int.le 1 a` and `hb : Int.lt 0 b ≡ Int.le 1 b` slot
    // directly into the `1 ≤ a` / `1 ≤ b` hypotheses.
    let proof = Expr::apps(
        c.mul_le_mul.clone(),
        [
            one.clone(),
            a.clone(),
            one.clone(),
            bv.clone(),
            ha.clone(),
            hb.clone(),
            h01.clone(),
            h01,
        ],
    );

    let val = b.mk_lam(hb_id, BinderInfo::Default, pos_b, proof);
    let val = b.mk_lam(ha_id, BinderInfo::Default, pos_a, val);
    let val = b.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `Int.mul_pos` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_ord()` has registered `Int.lt`, `Int.le`,
    ///           `Int.mul`, `Int.ofNat`.
    /// REQUIRES: The constructive `Int.mul_le_mul` and `Int.ofNat_zero_le`
    ///           theorems are available.
    /// ENSURES: On success, `Int.mul_pos` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_int_mul_pos_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.mul_pos");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_ord()?;
        self.init_eq()?;
        // Constructive dependencies.
        self.register_int_ofnat_zero_le_proof()?;
        self.register_int_mul_le_mul_proof()?;

        let c = IntMulPosConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). From `0 < a ≡ 1 ≤ a`
        // and `0 < b ≡ 1 ≤ b` applies `Int.mul_le_mul 1 a 1 b ha hb h01 h01`
        // (with `h01 : 0 ≤ 1 := Int.ofNat_zero_le 1`), whose conclusion
        // `Int.le (1*1) (a*b)` is definitionally `Int.le 1 (a*b)` ≡
        // `Int.lt 0 (a*b)` because the kernel reduces `Int.mul 1 1` to
        // `Int.ofNat 1` and `Int.add 0 1` (inside `Int.lt`) likewise to
        // `Int.ofNat 1`. No `sorry`, no self-reference, no domain-axiom
        // dependency.
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
    fn test_int_mul_pos_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_mul_pos_proof()
            .expect("first registration");
        env.register_int_mul_pos_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.mul_pos"))
            .expect("Int.mul_pos should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_mul_pos_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_mul_pos_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.mul_pos"))
            .expect("registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.mul_pos must have empty axiom closure, got {:?}",
            domain_deps
        );
    }

    #[test]
    fn test_int_mul_pos_proof_quality_constructive() {
        use crate::env::ProofQuality;
        let mut env = Environment::new();
        env.register_int_mul_pos_proof().unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Int.mul_pos"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.mul_pos must be Constructive, got {:?}",
            quality
        );
    }
}
