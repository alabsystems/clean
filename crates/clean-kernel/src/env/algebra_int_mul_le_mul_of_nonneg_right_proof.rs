// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.mul_le_mul_of_nonneg_right : ∀ a b c : Int,
//!    Int.le a b → Int.le (Int.ofNat 0) c →
//!    Int.le (Int.mul a c) (Int.mul b c)`.
//!
//! Registered as a `Declaration::Theorem` in `order_int.rs::init_int_ord_lemmas`.
//! This is the right-multiplication mirror of the landed
//! `Int.mul_le_mul_of_nonneg_left` (#3604) — same `Int.NonNeg.mul` gateway, the
//! distributivity bridge using `Int.right_distrib` / `Int.neg_mul_left` instead
//! of the left-distributivity versions.
//!
//! # Definitions in play
//!
//! ```text
//! Int.le a b := Int.NonNeg (Int.sub b a)        -- reducible Definition
//! Int.zero := Int.ofNat Nat.zero                -- reducible Definition
//! ```
//!
//! So `hab : Int.le a b` ≡ `NonNeg (Int.sub b a)`, `hc : Int.le 0 c` ≡
//! `NonNeg (Int.add c 0)` (since `Int.neg (ofNat 0) ≡ ofNat 0`), and the goal
//! `Int.le (Int.mul a c) (Int.mul b c)` ≡ `NonNeg (Int.sub (b*c) (a*c))`.
//!
//! # Proof sketch
//!
//! 1. `nc : NonNeg c := @Eq.subst NonNeg (add c 0) c (Int.add_zero c) hc`.
//! 2. `nprod : NonNeg (Int.mul (Int.sub b a) c) := Int.NonNeg.mul (b-a) c hab nc`
//!    (`hab : NonNeg (b-a)` directly).
//! 3. The distributivity bridge `(b-a)*c = b*c - a*c`, assembled as a four-link
//!    `Eq.trans` chain:
//!    ```text
//!    (b-a)*c
//!      = (b + (-a))*c        -- congrArg (· * c) (sub_eq_add_neg b a)
//!      = b*c + (-a)*c        -- right_distrib b (-a) c
//!      = b*c + (-(a*c))      -- congrArg (b*c + ·) (symm (neg_mul_left a c))
//!      = b*c - a*c           -- symm (sub_eq_add_neg (b*c) (a*c))
//!    ```
//! 4. Transport `nprod` along the bridge with `@Eq.subst NonNeg`, giving
//!    `NonNeg (b*c - a*c)` ≡ `Int.le (a*c) (b*c)`.
//!
//! # Axiom closure
//!
//! Depends only on the constructive `Int.NonNeg.mul`, `Int.add_zero`,
//! `Int.right_distrib`, `Int.neg_mul_left`, `Int.sub_eq_add_neg` theorems and
//! the foundational `Eq.subst` / `Eq.symm` / `Eq.trans` / `congrArg`. None is a
//! `Declaration::Axiom`, so `env.axiom_deps("Int.mul_le_mul_of_nonneg_right")`
//! is empty and the proof quality is `Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntMulLeMulRightConsts {
    int_type: Expr,
    int_le: Expr,
    int_mul: Expr,
    int_add: Expr,
    int_sub: Expr,
    int_neg: Expr,
    int_of_nat: Expr,
    nat_zero: Expr,
    nonneg: Expr,
    nonneg_mul: Expr,
    add_zero: Expr,
    right_distrib: Expr,
    neg_mul_left: Expr,
    sub_eq_add_neg: Expr,
    eq_subst: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
}

impl IntMulLeMulRightConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            int_le: Expr::const_(Name::from_string("Int.le"), vec![]),
            int_mul: Expr::const_(Name::from_string("Int.mul"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_sub: Expr::const_(Name::from_string("Int.sub"), vec![]),
            int_neg: Expr::const_(Name::from_string("Int.neg"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nonneg: Expr::const_(Name::from_string("Int.NonNeg"), vec![]),
            nonneg_mul: Expr::const_(Name::from_string("Int.NonNeg.mul"), vec![]),
            add_zero: Expr::const_(Name::from_string("Int.add_zero"), vec![]),
            right_distrib: Expr::const_(Name::from_string("Int.right_distrib"), vec![]),
            neg_mul_left: Expr::const_(Name::from_string("Int.neg_mul_left"), vec![]),
            sub_eq_add_neg: Expr::const_(Name::from_string("Int.sub_eq_add_neg"), vec![]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
        }
    }

    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }

    fn int_zero(&self) -> Expr {
        self.of_nat(self.nat_zero.clone())
    }

    fn mul(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_mul.clone(), x), y)
    }

    fn add(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), x), y)
    }

    fn sub(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_sub.clone(), x), y)
    }

    fn neg(&self, x: Expr) -> Expr {
        Expr::app(self.int_neg.clone(), x)
    }

    fn le(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_le.clone(), x), y)
    }

    fn nonneg_of(&self, x: Expr) -> Expr {
        Expr::app(self.nonneg.clone(), x)
    }

    fn nonneg_le(&self, x: Expr) -> Expr {
        self.le(self.int_zero(), x)
    }

    /// `@Eq.subst.{1} Int (fun z => NonNeg z) lhs rhs h m : NonNeg rhs`.
    fn subst_nonneg(
        &self,
        parent: &EnvDeclBuilder,
        lhs: Expr,
        rhs: Expr,
        h: Expr,
        m: Expr,
    ) -> Expr {
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = mb.fresh_local(self.int_type.clone());
            let body = self.nonneg_of(z);
            let lam = mb.mk_lam(z_id, BinderInfo::Default, self.int_type.clone(), body);
            mb.finish_child(lam)
        };
        Expr::apps(
            self.eq_subst.clone(),
            [self.int_type.clone(), motive, lhs, rhs, h, m],
        )
    }

    /// `@Eq.symm.{1} Int a b h : Eq b a`.
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.int_type.clone(), a, b, h])
    }

    /// `@Eq.trans.{1} Int a b c h1 h2 : Eq a c`.
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.int_type.clone(), a, b, cc, h1, h2],
        )
    }

    /// `@congrArg.{1,1} Int Int a b f h : Eq (f a) (f b)`.
    fn congr_arg(&self, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.int_type.clone(), self.int_type.clone(), a, b, f, h],
        )
    }
}

/// Build `∀ a b c : Int, Int.le a b → Int.le 0 c → Int.le (a*c) (b*c)`.
fn build_type(c: &IntMulLeMulRightConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let (c_id, cv) = b.fresh_local(c.int_type.clone());
    let le_ab = c.le(a.clone(), bv.clone());
    let nonneg_c = c.nonneg_le(cv.clone());
    let concl = c.le(c.mul(a.clone(), cv.clone()), c.mul(bv.clone(), cv.clone()));
    let (hc_id, _hc) = b.fresh_local(nonneg_c.clone());
    let (hab_id, _hab) = b.fresh_local(le_ab.clone());
    let r = b.mk_pi(hc_id, BinderInfo::Default, nonneg_c, concl);
    let r = b.mk_pi(hab_id, BinderInfo::Default, le_ab, r);
    let r = b.mk_pi(c_id, BinderInfo::Default, c.int_type.clone(), r);
    let r = b.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), r);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// Assemble the distributivity bridge `(b-a)*c = b*c - a*c`.
fn build_distrib_bridge(
    c: &IntMulLeMulRightConsts,
    parent: &EnvDeclBuilder,
    a: &Expr,
    bv: &Expr,
    cv: &Expr,
) -> Expr {
    let neg_a = c.neg(a.clone());
    let sub_ba = c.sub(bv.clone(), a.clone()); // b - a
    let add_b_neg_a = c.add(bv.clone(), neg_a.clone()); // b + (-a)
    let mul_sub_c = c.mul(sub_ba.clone(), cv.clone()); // (b-a)*c
    let mul_add_c = c.mul(add_b_neg_a.clone(), cv.clone()); // (b + (-a))*c
    let mul_bc = c.mul(bv.clone(), cv.clone()); // b*c
    let mul_ac = c.mul(a.clone(), cv.clone()); // a*c
    let mul_neg_a_c = c.mul(neg_a.clone(), cv.clone()); // (-a)*c
    let neg_mul_ac = c.neg(mul_ac.clone()); // -(a*c)
    let add_bc_negac = c.add(mul_bc.clone(), mul_neg_a_c.clone()); // b*c + (-a)*c
    let add_bc_neg_ac = c.add(mul_bc.clone(), neg_mul_ac.clone()); // b*c + (-(a*c))
    let sub_bc_ac = c.sub(mul_bc.clone(), mul_ac.clone()); // b*c - a*c

    // f1 := fun y => Int.mul y c
    let f_mul_c = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (y_id, y) = mb.fresh_local(c.int_type.clone());
        let body = c.mul(y, cv.clone());
        let lam = mb.mk_lam(y_id, BinderInfo::Default, c.int_type.clone(), body);
        mb.finish_child(lam)
    };
    // f2 := fun y => Int.add (b*c) y
    let f_add_bc = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (y_id, y) = mb.fresh_local(c.int_type.clone());
        let body = c.add(mul_bc.clone(), y);
        let lam = mb.mk_lam(y_id, BinderInfo::Default, c.int_type.clone(), body);
        mb.finish_child(lam)
    };

    // h_sub_eq : (b - a) = (b + (-a))   := Int.sub_eq_add_neg b a
    let h_sub_eq = Expr::apps(c.sub_eq_add_neg.clone(), [bv.clone(), a.clone()]);
    // step1 : (b-a)*c = (b + (-a))*c    := congrArg (·*c) h_sub_eq
    let step1 = c.congr_arg(sub_ba.clone(), add_b_neg_a.clone(), f_mul_c, h_sub_eq);

    // step2 : (b + (-a))*c = b*c + (-a)*c   := Int.right_distrib b (-a) c
    let step2 = Expr::apps(
        c.right_distrib.clone(),
        [bv.clone(), neg_a.clone(), cv.clone()],
    );

    // h_neg_mul : (-a)*c = -(a*c)   := Eq.symm (Int.neg_mul_left a c)
    //   (Int.neg_mul_left a c : -(a*c) = (-a)*c)
    let neg_mul_fwd = Expr::apps(c.neg_mul_left.clone(), [a.clone(), cv.clone()]);
    let h_neg_mul = c.symm(neg_mul_ac.clone(), mul_neg_a_c.clone(), neg_mul_fwd);
    // step3 : b*c + (-a)*c = b*c + (-(a*c))   := congrArg (b*c + ·) h_neg_mul
    let step3 = c.congr_arg(mul_neg_a_c.clone(), neg_mul_ac.clone(), f_add_bc, h_neg_mul);

    // step4 : b*c + (-(a*c)) = b*c - a*c
    //   := Eq.symm (Int.sub_eq_add_neg (b*c) (a*c))
    let sub_eq_bc_ac = Expr::apps(c.sub_eq_add_neg.clone(), [mul_bc.clone(), mul_ac.clone()]);
    let step4 = c.symm(sub_bc_ac.clone(), add_bc_neg_ac.clone(), sub_eq_bc_ac);

    // Fold the four links left-to-right with Eq.trans.
    // t1 : (b-a)*c = b*c + (-a)*c
    let t1 = c.trans(
        mul_sub_c.clone(),
        mul_add_c.clone(),
        add_bc_negac.clone(),
        step1,
        step2,
    );
    // t2 : (b-a)*c = b*c + (-(a*c))
    let t2 = c.trans(
        mul_sub_c.clone(),
        add_bc_negac.clone(),
        add_bc_neg_ac.clone(),
        t1,
        step3,
    );
    // t3 : (b-a)*c = b*c - a*c
    c.trans(mul_sub_c, add_bc_neg_ac, sub_bc_ac, t2, step4)
}

/// Body of `Int.mul_le_mul_of_nonneg_right`.
fn build_value(c: &IntMulLeMulRightConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let (c_id, cv) = b.fresh_local(c.int_type.clone());
    let le_ab = c.le(a.clone(), bv.clone());
    let (hab_id, hab) = b.fresh_local(le_ab.clone());
    let nonneg_c = c.nonneg_le(cv.clone());
    let (hc_id, hc) = b.fresh_local(nonneg_c.clone());

    let zero = c.int_zero();
    let add_c0 = c.add(cv.clone(), zero); // c + 0
    let sub_ba = c.sub(bv.clone(), a.clone()); // b - a
    let mul_sub_c = c.mul(sub_ba.clone(), cv.clone()); // (b-a)*c
    let mul_bc = c.mul(bv.clone(), cv.clone()); // b*c
    let mul_ac = c.mul(a.clone(), cv.clone()); // a*c
    let sub_bc_ac = c.sub(mul_bc.clone(), mul_ac.clone()); // b*c - a*c

    // add_zero c : (c + 0) = c
    let add_zero_c = Expr::app(c.add_zero.clone(), cv.clone());
    // nc : NonNeg c := Eq.subst NonNeg (c+0) c (add_zero c) hc
    let nc = c.subst_nonneg(&b, add_c0, cv.clone(), add_zero_c, hc.clone());

    // nprod : NonNeg ((b-a)*c) := Int.NonNeg.mul (b-a) c hab nc
    // (hab : Int.le a b ≡ NonNeg (b-a) up to defeq, matching the NonNeg.mul slot.)
    let nprod = Expr::apps(
        c.nonneg_mul.clone(),
        [sub_ba.clone(), cv.clone(), hab.clone(), nc],
    );

    // bridge : (b-a)*c = b*c - a*c
    let bridge = build_distrib_bridge(c, &b, &a, &bv, &cv);

    // proof : NonNeg (b*c - a*c) ≡ Int.le (a*c) (b*c)
    //   := Eq.subst NonNeg ((b-a)*c) (b*c - a*c) bridge nprod
    let proof = c.subst_nonneg(&b, mul_sub_c, sub_bc_ac, bridge, nprod);

    let val = b.mk_lam(hc_id, BinderInfo::Default, nonneg_c, proof);
    let val = b.mk_lam(hab_id, BinderInfo::Default, le_ab, val);
    let val = b.mk_lam(c_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = b.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `Int.mul_le_mul_of_nonneg_right` as a kernel-checked
    /// `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_ord()` has registered `Int.le`, `Int.NonNeg`,
    ///           `Int.mul`, `Int.add`, `Int.sub`, `Int.neg`, `Int.ofNat`.
    /// REQUIRES: `self.init_eq()` has registered `Eq.subst`, `Eq.symm`,
    ///           `Eq.trans`, `congrArg`.
    /// ENSURES: On success, `Int.mul_le_mul_of_nonneg_right` is a
    ///          `Declaration::Theorem` with `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_int_mul_le_mul_of_nonneg_right_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.mul_le_mul_of_nonneg_right");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_ord()?;
        self.init_eq()?;
        // Constructive dependencies.
        self.register_int_add_zero_proof()?;
        self.register_int_nonneg_mul_proof()?;
        self.register_int_right_distrib_proof()?;
        self.register_int_neg_mul_left_proof()?;
        self.register_int_sub_eq_add_neg_proof()?;

        let c = IntMulLeMulRightConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Right-multiplication
        // mirror of `Int.mul_le_mul_of_nonneg_left`. Converts `hc : Int.le 0 c`
        // to `NonNeg c` (transport along `Int.add_zero c`), forms
        // `Int.NonNeg.mul (b-a) c hab nc : NonNeg ((b-a)*c)` (the `Int.le a b`
        // witness `hab` is `NonNeg (b-a)` definitionally), then transports along
        // the constructive distributivity bridge `(b-a)*c = b*c - a*c` via
        // `@Eq.subst.{1}` to obtain `NonNeg (b*c - a*c)` ≡ `Int.le (a*c) (b*c)`.
        // No `sorry`, no self-reference, no domain-axiom dependency.
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
    fn test_int_mul_le_mul_of_nonneg_right_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_mul_le_mul_of_nonneg_right_proof()
            .expect("first registration");
        env.register_int_mul_le_mul_of_nonneg_right_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.mul_le_mul_of_nonneg_right"))
            .expect("Int.mul_le_mul_of_nonneg_right should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_mul_le_mul_of_nonneg_right_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_mul_le_mul_of_nonneg_right_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.mul_le_mul_of_nonneg_right"))
            .expect("registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.mul_le_mul_of_nonneg_right must have empty axiom closure, got {:?}",
            domain_deps
        );
    }

    #[test]
    fn test_int_mul_le_mul_of_nonneg_right_proof_quality_constructive() {
        use crate::env::ProofQuality;
        let mut env = Environment::new();
        env.register_int_mul_le_mul_of_nonneg_right_proof().unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Int.mul_le_mul_of_nonneg_right"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.mul_le_mul_of_nonneg_right must be Constructive, got {:?}",
            quality
        );
    }
}
