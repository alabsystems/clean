// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.mul_nonneg : ∀ a b : Int,
//!    Int.le (Int.ofNat 0) a → Int.le (Int.ofNat 0) b →
//!    Int.le (Int.ofNat 0) (Int.mul a b)`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `order_int.rs::init_int_ord_lemmas` with a `Declaration::Theorem`.
//!
//! This is the multiplicative-monotonicity gateway into the ordered-ring
//! lemmas: `Int.mul_le_mul_of_nonneg_left/right` reduce to it via
//! `right_distrib`.
//!
//! # Definitions in play
//!
//! ```text
//! Int.le a b := Int.NonNeg (Int.sub b a)        -- reducible Definition
//! Int.sub a b := Int.add a (Int.neg b)          -- reducible Definition
//! Int.neg (Int.ofNat 0) ≡ Int.ofNat 0
//! Int.zero := Int.ofNat Nat.zero                -- reducible Definition
//! inductive Int.NonNeg : Int → Prop where
//!   | mk (n : Nat) : Int.NonNeg (Int.ofNat n)
//! ```
//!
//! A hypothesis `h : Int.le (Int.ofNat 0) x` delta-reduces to
//! `Int.NonNeg (Int.sub x (Int.ofNat 0))` ≡
//! `Int.NonNeg (Int.add x (Int.ofNat 0))` (since `Int.neg (ofNat 0) ≡ ofNat 0`).
//! Note this does **not** reduce to `Int.NonNeg x` when `x` is a free variable,
//! because `Int.add` recurses on its first argument, which is stuck on `x`.
//!
//! # Proof strategy
//!
//! 1. A reusable building block
//!    `Int.NonNeg.mul : ∀ x y : Int, NonNeg x → NonNeg y → NonNeg (Int.mul x y)`,
//!    proved by double `@Int.NonNeg.rec.{0}` on the genuine `NonNeg` indices
//!    `x`, `y`: the minors receive `n`, `m : Nat` (so `x = ofNat n`,
//!    `y = ofNat m`) and `@Int.NonNeg.mk (Nat.mul n m)` inhabits
//!    `NonNeg (Int.mul (ofNat n) (ofNat m))` because that product reduces to
//!    `Int.ofNat (Nat.mul n m)`.
//!
//! 2. `Int.mul_nonneg` then transports across the `Int.add_zero` bridge
//!    `Int.add x (Int.ofNat 0) = x` (the LHS is defeq to `Int.sub x (ofNat 0)`):
//!    - `na := @Eq.subst NonNeg (add a 0) a (Int.add_zero a) ha : NonNeg a`
//!    - `nb := @Eq.subst NonNeg (add b 0) b (Int.add_zero b) hb : NonNeg b`
//!    - `nab := Int.NonNeg.mul a b na nb : NonNeg (Int.mul a b)`
//!    - the goal `Int.le 0 (Int.mul a b)` ≡ `NonNeg (add (Int.mul a b) 0)` is
//!      obtained by transporting `nab` along
//!      `Eq.symm (Int.add_zero (Int.mul a b)) : (Int.mul a b) = add (Int.mul a b) 0`.
//!
//! # Axiom closure
//!
//! Mentions only `Int`, `Int.le`, `Int.mul`, `Int.add`, `Int.ofNat`,
//! `Int.NonNeg`, `Int.NonNeg.rec`, `Int.NonNeg.mk`, `Nat`, `Nat.mul`,
//! `Nat.zero`, the constructive `Int.add_zero`, and the foundational `Eq.subst`
//! / `Eq.symm`. None is a `Declaration::Axiom`, so
//! `env.axiom_deps("Int.mul_nonneg")` is empty and
//! `env.proof_quality("Int.mul_nonneg") == ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntMulNonNegConsts {
    int_type: Expr,
    nat_type: Expr,
    int_le: Expr,
    int_mul: Expr,
    int_add: Expr,
    int_of_nat: Expr,
    nat_mul: Expr,
    nat_zero: Expr,
    nonneg: Expr,
    nonneg_rec: Expr,
    nonneg_mk: Expr,
    int_add_zero: Expr,
    eq_subst: Expr,
    eq_symm: Expr,
}

impl IntMulNonNegConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            int_le: Expr::const_(Name::from_string("Int.le"), vec![]),
            int_mul: Expr::const_(Name::from_string("Int.mul"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            nat_mul: Expr::const_(Name::from_string("Nat.mul"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nonneg: Expr::const_(Name::from_string("Int.NonNeg"), vec![]),
            // Prop-valued motive — Sort 0.
            nonneg_rec: Expr::const_(Name::from_string("Int.NonNeg.rec"), vec![]),
            nonneg_mk: Expr::const_(Name::from_string("Int.NonNeg.mk"), vec![]),
            int_add_zero: Expr::const_(Name::from_string("Int.add_zero"), vec![]),
            // Eq lives in Type 1 here (Int : Type 0), so Eq.subst/Eq.symm.{1}.
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1]),
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

    fn le(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.int_le.clone(), x), y)
    }

    fn nonneg_of(&self, x: Expr) -> Expr {
        Expr::app(self.nonneg.clone(), x)
    }

    /// `Int.le (Int.ofNat 0) x`.
    fn nonneg_le(&self, x: Expr) -> Expr {
        self.le(self.int_zero(), x)
    }

    /// `Int.add_zero x : Eq Int (Int.add x (Int.ofNat 0)) x`.
    /// (`Int.add_zero` is stated with `Int.zero`, which is the reducible
    /// abbreviation `Int.ofNat Nat.zero`, so this application's LHS is defeq to
    /// `Int.add x (Int.ofNat 0)` and to `Int.sub x (Int.ofNat 0)`.)
    fn add_zero(&self, x: Expr) -> Expr {
        Expr::app(self.int_add_zero.clone(), x)
    }
}

// ---------------------------------------------------------------------------
// Helper: Int.NonNeg.mul
// ---------------------------------------------------------------------------

/// Build `∀ x y : Int, NonNeg x → NonNeg y → NonNeg (Int.mul x y)`.
fn build_nonneg_mul_type(c: &IntMulNonNegConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.int_type.clone());
    let (y_id, y) = b.fresh_local(c.int_type.clone());
    let hx_type = c.nonneg_of(x.clone());
    let (hx_id, _hx) = b.fresh_local(hx_type.clone());
    let hy_type = c.nonneg_of(y.clone());
    let (hy_id, _hy) = b.fresh_local(hy_type.clone());
    let concl = c.nonneg_of(c.mul(x.clone(), y.clone()));
    let r = b.mk_pi(hy_id, BinderInfo::Default, hy_type, concl);
    let r = b.mk_pi(hx_id, BinderInfo::Default, hx_type, r);
    let r = b.mk_pi(y_id, BinderInfo::Default, c.int_type.clone(), r);
    let r = b.mk_pi(x_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// Body:
/// ```text
/// λ (x y : Int) (hx : NonNeg x) (hy : NonNeg y) =>
///   @Int.NonNeg.rec.{0}
///     (fun (i : Int) (_ : NonNeg i) => NonNeg (Int.mul i y))
///     (fun (n : Nat) =>
///        @Int.NonNeg.rec.{0}
///          (fun (j : Int) (_ : NonNeg j) => NonNeg (Int.mul (Int.ofNat n) j))
///          (fun (m : Nat) => @Int.NonNeg.mk (Nat.mul n m))
///          y hy)
///     x hx
/// ```
fn build_nonneg_mul_value(c: &IntMulNonNegConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.int_type.clone());
    let (y_id, y) = b.fresh_local(c.int_type.clone());
    let hx_type = c.nonneg_of(x.clone());
    let (hx_id, hx) = b.fresh_local(hx_type.clone());
    let hy_type = c.nonneg_of(y.clone());
    let (hy_id, hy) = b.fresh_local(hy_type.clone());

    // Outer motive: fun (i : Int) (_ : NonNeg i) => NonNeg (Int.mul i y)
    let outer_motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = mb.fresh_local(c.int_type.clone());
        let hi_type = c.nonneg_of(i.clone());
        let (hi_id, _hi) = mb.fresh_local(hi_type.clone());
        let body = c.nonneg_of(c.mul(i.clone(), y.clone()));
        let lam = mb.mk_lam(hi_id, BinderInfo::Default, hi_type, body);
        let lam = mb.mk_lam(i_id, BinderInfo::Default, c.int_type.clone(), lam);
        mb.finish_child(lam)
    };

    // Outer minor: fun (n : Nat) => inner_rec
    let outer_minor = {
        let mut ob = EnvDeclBuilder::child_of(&b);
        let (n_id, n) = ob.fresh_local(c.nat_type.clone());
        let of_nat_n = c.of_nat(n.clone());

        // Inner motive:
        //   fun (j : Int) (_ : NonNeg j) => NonNeg (Int.mul (ofNat n) j)
        let inner_motive = {
            let mut mb = EnvDeclBuilder::child_of(&ob);
            let (j_id, j) = mb.fresh_local(c.int_type.clone());
            let hj_type = c.nonneg_of(j.clone());
            let (hj_id, _hj) = mb.fresh_local(hj_type.clone());
            let body = c.nonneg_of(c.mul(of_nat_n.clone(), j.clone()));
            let lam = mb.mk_lam(hj_id, BinderInfo::Default, hj_type, body);
            let lam = mb.mk_lam(j_id, BinderInfo::Default, c.int_type.clone(), lam);
            mb.finish_child(lam)
        };

        // Inner minor: fun (m : Nat) => @Int.NonNeg.mk (Nat.mul n m)
        let inner_minor = {
            let mut ib = EnvDeclBuilder::child_of(&ob);
            let (m_id, m) = ib.fresh_local(c.nat_type.clone());
            let nat_mul_nm = Expr::app(Expr::app(c.nat_mul.clone(), n.clone()), m.clone());
            let mk_app = Expr::app(c.nonneg_mk.clone(), nat_mul_nm);
            let lam = ib.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), mk_app);
            ib.finish_child(lam)
        };

        // @Int.NonNeg.rec.{0} inner_motive inner_minor y hy
        let inner_rec = Expr::apps(
            c.nonneg_rec.clone(),
            [inner_motive, inner_minor, y.clone(), hy.clone()],
        );
        let lam = ob.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), inner_rec);
        ob.finish_child(lam)
    };

    // @Int.NonNeg.rec.{0} outer_motive outer_minor x hx
    let outer_rec = Expr::apps(
        c.nonneg_rec.clone(),
        [outer_motive, outer_minor, x.clone(), hx.clone()],
    );

    let val = b.mk_lam(hy_id, BinderInfo::Default, hy_type, outer_rec);
    let val = b.mk_lam(hx_id, BinderInfo::Default, hx_type, val);
    let val = b.mk_lam(y_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = b.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), val);
    b.finish(val)
}

// ---------------------------------------------------------------------------
// Int.mul_nonneg
// ---------------------------------------------------------------------------

/// Build the goal type
/// `∀ a b : Int, Int.le 0 a → Int.le 0 b → Int.le 0 (Int.mul a b)`.
fn build_type(c: &IntMulNonNegConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let ha_type = c.nonneg_le(a.clone());
    let hb_type = c.nonneg_le(bv.clone());
    let (ha_id, _ha) = b.fresh_local(ha_type.clone());
    let (hb_id, _hb) = b.fresh_local(hb_type.clone());
    let concl = c.nonneg_le(c.mul(a.clone(), bv.clone()));
    let r = b.mk_pi(hb_id, BinderInfo::Default, hb_type, concl);
    let r = b.mk_pi(ha_id, BinderInfo::Default, ha_type, r);
    let r = b.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), r);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// Motive `fun (z : Int) => Int.NonNeg z`, reused for every `Eq.subst`.
fn nonneg_motive(c: &IntMulNonNegConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (z_id, z) = mb.fresh_local(c.int_type.clone());
    let body = c.nonneg_of(z);
    let lam = mb.mk_lam(z_id, BinderInfo::Default, c.int_type.clone(), body);
    mb.finish_child(lam)
}

/// Body:
/// ```text
/// λ (a b : Int) (ha : le 0 a) (hb : le 0 b) =>
///   @Eq.subst.{1} Int (fun z => NonNeg z)
///     (Int.mul a b) (Int.add (Int.mul a b) 0)
///     (@Eq.symm.{1} Int (Int.add (Int.mul a b) 0) (Int.mul a b)
///        (Int.add_zero (Int.mul a b)))
///     (Int.NonNeg.mul a b
///        (@Eq.subst.{1} Int (fun z => NonNeg z)
///           (Int.add a 0) a (Int.add_zero a) ha)
///        (@Eq.subst.{1} Int (fun z => NonNeg z)
///           (Int.add b 0) b (Int.add_zero b) hb))
/// ```
fn build_value(c: &IntMulNonNegConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let ha_type = c.nonneg_le(a.clone());
    let (ha_id, ha) = b.fresh_local(ha_type.clone());
    let hb_type = c.nonneg_le(bv.clone());
    let (hb_id, hb) = b.fresh_local(hb_type.clone());

    let nonneg_mul = Expr::const_(Name::from_string("Int.NonNeg.mul"), vec![]);

    let zero = c.int_zero();
    let add_a0 = c.add(a.clone(), zero.clone());
    let add_b0 = c.add(bv.clone(), zero.clone());
    let mul_ab = c.mul(a.clone(), bv.clone());
    let add_mul_ab_0 = c.add(mul_ab.clone(), zero.clone());

    // na : NonNeg a  := Eq.subst NonNeg (add a 0) a (add_zero a) ha
    // (ha : le 0 a ≡ NonNeg (add a 0) up to defeq.)
    let na = Expr::apps(
        c.eq_subst.clone(),
        [
            c.int_type.clone(),
            nonneg_motive(c, &b),
            add_a0,
            a.clone(),
            c.add_zero(a.clone()),
            ha.clone(),
        ],
    );

    // nb : NonNeg b  := Eq.subst NonNeg (add b 0) b (add_zero b) hb
    let nb = Expr::apps(
        c.eq_subst.clone(),
        [
            c.int_type.clone(),
            nonneg_motive(c, &b),
            add_b0,
            bv.clone(),
            c.add_zero(bv.clone()),
            hb.clone(),
        ],
    );

    // nab : NonNeg (Int.mul a b) := Int.NonNeg.mul a b na nb
    let nab = Expr::apps(nonneg_mul, [a.clone(), bv.clone(), na, nb]);

    // sym : (Int.mul a b) = Int.add (Int.mul a b) 0
    //     := Eq.symm Int (add (mul a b) 0) (mul a b) (add_zero (mul a b))
    let sym = Expr::apps(
        c.eq_symm.clone(),
        [
            c.int_type.clone(),
            add_mul_ab_0.clone(),
            mul_ab.clone(),
            c.add_zero(mul_ab.clone()),
        ],
    );

    // goal : Int.le 0 (mul a b) ≡ NonNeg (add (mul a b) 0)
    //      := Eq.subst NonNeg (mul a b) (add (mul a b) 0) sym nab
    let proof = Expr::apps(
        c.eq_subst.clone(),
        [
            c.int_type.clone(),
            nonneg_motive(c, &b),
            mul_ab,
            add_mul_ab_0,
            sym,
            nab,
        ],
    );

    let val = b.mk_lam(hb_id, BinderInfo::Default, hb_type, proof);
    let val = b.mk_lam(ha_id, BinderInfo::Default, ha_type, val);
    let val = b.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register the constructive helper `Int.NonNeg.mul` as a
    /// `Declaration::Theorem`.
    ///
    /// `∀ x y : Int, Int.NonNeg x → Int.NonNeg y → Int.NonNeg (Int.mul x y)`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_ord()` has registered `Int.NonNeg`,
    ///           `Int.NonNeg.mk`, `Int.NonNeg.rec`, `Int.mul`, `Int.ofNat`.
    /// ENSURES: On success, `Int.NonNeg.mul` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_int_nonneg_mul_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.NonNeg.mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_ord()?;

        let c = IntMulNonNegConsts::new();
        let type_ = build_nonneg_mul_type(&c);
        let value = build_nonneg_mul_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. Double `@Int.NonNeg.rec.{0}`
        // recursion extracts the two `Nat` witnesses `n`, `m` and rebuilds
        // `@Int.NonNeg.mk (Nat.mul n m)`, which type-checks against the goal
        // `NonNeg (Int.mul (Int.ofNat n) (Int.ofNat m))` because the product
        // reduces to `Int.ofNat (Nat.mul n m)` by iota on `Int.rec`
        // (ofNat/ofNat case) + delta on the reducible `Int.mul`. No `sorry`,
        // no self-reference, no domain-axiom dependency.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// Register `Int.mul_nonneg` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_ord()` has registered `Int.le`, `Int.NonNeg`,
    ///           `Int.NonNeg.mk`, `Int.NonNeg.rec`, `Int.mul`, `Int.add`,
    ///           `Int.ofNat`.
    /// REQUIRES: `self.init_eq()` has registered `Eq.subst`, `Eq.symm`.
    /// ENSURES: On success, `Int.mul_nonneg` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.mul_nonneg` is already registered with any
    ///          declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_int_mul_nonneg_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.mul_nonneg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_ord()?;
        self.init_eq()?;
        // Constructive dependencies.
        self.register_int_add_zero_proof()?;
        self.register_int_nonneg_mul_proof()?;

        let c = IntMulNonNegConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. Converts the two
        // `Int.le 0 _` hypotheses (each ≡ `NonNeg (Int.add _ 0)`) to `NonNeg _`
        // by transporting along the constructive `Int.add_zero` via
        // `@Eq.subst.{1}`, combines them with the constructive `Int.NonNeg.mul`,
        // and transports the result back to the goal
        // `Int.le 0 (Int.mul a b)` ≡ `NonNeg (Int.add (Int.mul a b) 0)` via a
        // `@Eq.symm.{1}` / `@Eq.subst.{1}` pair over `Int.add_zero (Int.mul a b)`.
        // No `sorry`, no self-reference, no domain-axiom dependency. Replaces the
        // prior `Declaration::Axiom` in `order_int.rs::init_int_ord_lemmas`.
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
    fn test_int_nonneg_mul_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_nonneg_mul_proof()
            .expect("first registration");
        env.register_int_nonneg_mul_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.NonNeg.mul"))
            .expect("Int.NonNeg.mul should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_nonneg_mul_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_nonneg_mul_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.NonNeg.mul"))
            .expect("Int.NonNeg.mul is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.NonNeg.mul must have empty axiom closure, got {:?}",
            domain_deps
        );
    }

    #[test]
    fn test_int_mul_nonneg_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_mul_nonneg_proof()
            .expect("first registration");
        env.register_int_mul_nonneg_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.mul_nonneg"))
            .expect("Int.mul_nonneg should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_mul_nonneg_proof_root_is_eq_subst() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_mul_nonneg_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.mul_nonneg"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        // Peel the four outer λ binders, then the head must be Eq.subst.
        let mut body: Expr = value.clone();
        for _ in 0..4 {
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
                "Eq.subst",
                "Int.mul_nonneg proof root must be Eq.subst"
            ),
            k => panic!("expected Const(Eq.subst), got {:?}", k),
        }
    }

    #[test]
    fn test_int_mul_nonneg_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_mul_nonneg_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.mul_nonneg"))
            .expect("Int.mul_nonneg is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.mul_nonneg must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }

    #[test]
    fn test_int_mul_nonneg_proof_quality_constructive() {
        use crate::env::ProofQuality;
        let mut env = Environment::new();
        env.register_int_mul_nonneg_proof().unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Int.mul_nonneg"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.mul_nonneg must be Constructive, got {:?}",
            quality
        );
    }
}
