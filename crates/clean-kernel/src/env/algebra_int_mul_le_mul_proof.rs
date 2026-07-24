// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.mul_le_mul : ∀ a b c d : Int,
//!    Int.le a b → Int.le c d → Int.le (Int.ofNat 0) a →
//!    Int.le (Int.ofNat 0) c → Int.le (Int.mul a c) (Int.mul b d)`.
//!
//! Registered as a `Declaration::Theorem` in `order_int.rs::init_int_ord_lemmas`.
//! This is the general ordered-ring product monotonicity lemma, composed from
//! the two one-sided lemmas (#3604) and `Int.le_trans`.
//!
//! # Definition in play
//!
//! ```text
//! Int.le a b := Int.NonNeg (Int.sub b a)        -- reducible Definition
//! ```
//!
//! # Proof sketch
//!
//! Given `a b c d : Int`, `hab : a ≤ b`, `hcd : c ≤ d`, `ha0 : 0 ≤ a`,
//! `hc0 : 0 ≤ c`, take the midpoint `b*c`:
//!
//! 1. `hb0 : 0 ≤ b := Int.le_trans 0 a b ha0 hab`.
//! 2. `left  : a*c ≤ b*c := Int.mul_le_mul_of_nonneg_right a b c hab hc0`.
//! 3. `right : b*c ≤ b*d := Int.mul_le_mul_of_nonneg_left c d b hcd hb0`.
//! 4. `Int.le_trans (a*c) (b*c) (b*d) left right : a*c ≤ b*d`.
//!
//! # Axiom closure
//!
//! Depends only on the constructive `Int.le_trans`,
//! `Int.mul_le_mul_of_nonneg_right`, `Int.mul_le_mul_of_nonneg_left` theorems.
//! None is a `Declaration::Axiom`, so `env.axiom_deps("Int.mul_le_mul")` is
//! empty and the proof quality is `Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntMulLeMulConsts {
    int_type: Expr,
    int_le: Expr,
    int_mul: Expr,
    int_of_nat: Expr,
    nat_zero: Expr,
    le_trans: Expr,
    mul_le_mul_left: Expr,
    mul_le_mul_right: Expr,
}

impl IntMulLeMulConsts {
    fn new() -> Self {
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            int_le: Expr::const_(Name::from_string("Int.le"), vec![]),
            int_mul: Expr::const_(Name::from_string("Int.mul"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            le_trans: Expr::const_(Name::from_string("Int.le_trans"), vec![]),
            mul_le_mul_left: Expr::const_(
                Name::from_string("Int.mul_le_mul_of_nonneg_left"),
                vec![],
            ),
            mul_le_mul_right: Expr::const_(
                Name::from_string("Int.mul_le_mul_of_nonneg_right"),
                vec![],
            ),
        }
    }

    fn int_zero(&self) -> Expr {
        Expr::app(self.int_of_nat.clone(), self.nat_zero.clone())
    }

    fn mul(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_mul.clone(), x), y)
    }

    fn le(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_le.clone(), x), y)
    }

    fn nonneg_le(&self, x: Expr) -> Expr {
        self.le(self.int_zero(), x)
    }

    /// `Int.le_trans a b c hab hbc : Int.le a c`.
    fn le_trans(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(self.le_trans.clone(), [a, b, cc, hab, hbc])
    }
}

/// Build `∀ a b c d : Int, a ≤ b → c ≤ d → 0 ≤ a → 0 ≤ c → a*c ≤ b*d`.
fn build_type(c: &IntMulLeMulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let (c_id, cv) = b.fresh_local(c.int_type.clone());
    let (d_id, dv) = b.fresh_local(c.int_type.clone());
    let le_ab = c.le(a.clone(), bv.clone());
    let le_cd = c.le(cv.clone(), dv.clone());
    let nonneg_a = c.nonneg_le(a.clone());
    let nonneg_c = c.nonneg_le(cv.clone());
    let concl = c.le(c.mul(a.clone(), cv.clone()), c.mul(bv.clone(), dv.clone()));
    let (hc0_id, _hc0) = b.fresh_local(nonneg_c.clone());
    let (ha0_id, _ha0) = b.fresh_local(nonneg_a.clone());
    let (hcd_id, _hcd) = b.fresh_local(le_cd.clone());
    let (hab_id, _hab) = b.fresh_local(le_ab.clone());
    let r = b.mk_pi(hc0_id, BinderInfo::Default, nonneg_c, concl);
    let r = b.mk_pi(ha0_id, BinderInfo::Default, nonneg_a, r);
    let r = b.mk_pi(hcd_id, BinderInfo::Default, le_cd, r);
    let r = b.mk_pi(hab_id, BinderInfo::Default, le_ab, r);
    let r = b.mk_pi(d_id, BinderInfo::Default, c.int_type.clone(), r);
    let r = b.mk_pi(c_id, BinderInfo::Default, c.int_type.clone(), r);
    let r = b.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), r);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// Body of `Int.mul_le_mul`.
fn build_value(c: &IntMulLeMulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let (c_id, cv) = b.fresh_local(c.int_type.clone());
    let (d_id, dv) = b.fresh_local(c.int_type.clone());
    let le_ab = c.le(a.clone(), bv.clone());
    let (hab_id, hab) = b.fresh_local(le_ab.clone());
    let le_cd = c.le(cv.clone(), dv.clone());
    let (hcd_id, hcd) = b.fresh_local(le_cd.clone());
    let nonneg_a = c.nonneg_le(a.clone());
    let (ha0_id, ha0) = b.fresh_local(nonneg_a.clone());
    let nonneg_c = c.nonneg_le(cv.clone());
    let (hc0_id, hc0) = b.fresh_local(nonneg_c.clone());

    let zero = c.int_zero();
    let mul_ac = c.mul(a.clone(), cv.clone()); // a*c
    let mul_bc = c.mul(bv.clone(), cv.clone()); // b*c
    let mul_bd = c.mul(bv.clone(), dv.clone()); // b*d

    // hb0 : 0 ≤ b := Int.le_trans 0 a b ha0 hab
    let hb0 = c.le_trans(zero, a.clone(), bv.clone(), ha0.clone(), hab.clone());

    // left : a*c ≤ b*c := Int.mul_le_mul_of_nonneg_right a b c hab hc0
    let left = Expr::apps(
        c.mul_le_mul_right.clone(),
        [a.clone(), bv.clone(), cv.clone(), hab.clone(), hc0.clone()],
    );

    // right : b*c ≤ b*d := Int.mul_le_mul_of_nonneg_left c d b hcd hb0
    let right = Expr::apps(
        c.mul_le_mul_left.clone(),
        [cv.clone(), dv.clone(), bv.clone(), hcd.clone(), hb0],
    );

    // proof : a*c ≤ b*d := Int.le_trans (a*c) (b*c) (b*d) left right
    let proof = c.le_trans(mul_ac, mul_bc, mul_bd, left, right);

    let val = b.mk_lam(hc0_id, BinderInfo::Default, nonneg_c, proof);
    let val = b.mk_lam(ha0_id, BinderInfo::Default, nonneg_a, val);
    let val = b.mk_lam(hcd_id, BinderInfo::Default, le_cd, val);
    let val = b.mk_lam(hab_id, BinderInfo::Default, le_ab, val);
    let val = b.mk_lam(d_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = b.mk_lam(c_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = b.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `Int.mul_le_mul` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_ord()` has registered `Int.le`, `Int.mul`,
    ///           `Int.ofNat`.
    /// REQUIRES: The constructive `Int.le_trans`,
    ///           `Int.mul_le_mul_of_nonneg_left`,
    ///           `Int.mul_le_mul_of_nonneg_right` theorems are available.
    /// ENSURES: On success, `Int.mul_le_mul` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_int_mul_le_mul_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.mul_le_mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_ord()?;
        self.init_eq()?;
        // Constructive dependencies.
        self.register_int_le_trans_proof()?;
        self.register_int_mul_le_mul_of_nonneg_left_proof()?;
        self.register_int_mul_le_mul_of_nonneg_right_proof()?;

        let c = IntMulLeMulConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Composition of the
        // two one-sided monotonicity lemmas with an `Int.le_trans` midpoint at
        // `b*c`: `Int.mul_le_mul_of_nonneg_right a b c hab hc0 : a*c ≤ b*c` and
        // `Int.mul_le_mul_of_nonneg_left c d b hcd hb0 : b*c ≤ b*d`, where
        // `hb0 : 0 ≤ b := Int.le_trans 0 a b ha0 hab`. No `sorry`, no
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
    fn test_int_mul_le_mul_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_mul_le_mul_proof()
            .expect("first registration");
        env.register_int_mul_le_mul_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.mul_le_mul"))
            .expect("Int.mul_le_mul should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_mul_le_mul_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_mul_le_mul_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.mul_le_mul"))
            .expect("registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.mul_le_mul must have empty axiom closure, got {:?}",
            domain_deps
        );
    }

    #[test]
    fn test_int_mul_le_mul_proof_quality_constructive() {
        use crate::env::ProofQuality;
        let mut env = Environment::new();
        env.register_int_mul_le_mul_proof().unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Int.mul_le_mul"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.mul_le_mul must be Constructive, got {:?}",
            quality
        );
    }
}
