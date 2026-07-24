// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.add_lt_add_left : ∀ a b : Int, Int.lt a b → ∀ c : Int,
//!    Int.lt (Int.add c a) (Int.add c b)`.
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
//! So `h : Int.lt a b` delta-reduces to `Int.le (a+1) b` and the goal
//! `Int.lt (c+a) (c+b)` to `Int.le ((c+a)+1) (c+b)` ≡
//! `Int.NonNeg (Int.sub (c+b) ((c+a)+1))`.
//!
//! # Proof sketch
//!
//! Apply the constructive `Int.add_le_add_left` to `h : Int.le (a+1) b`,
//! adding `c` on the left:
//!
//! ```text
//! step := Int.add_le_add_left (a+1) b h c
//!       : Int.le (c+(a+1)) (c+b)   ≡   Int.NonNeg (Int.sub (c+b) (c+(a+1)))
//! ```
//!
//! The goal's subtrahend is `(c+a)+1`, the step's is `c+(a+1)`. They are
//! equal by `Int.add_assoc c a 1 : Eq ((c+a)+1) (c+(a+1))`. Transport `step`
//! along `Eq.symm` of it with motive `fun x => Int.NonNeg (Int.sub (c+b) x)`:
//!
//! ```text
//! @Eq.subst.{1} Int (fun x => Int.NonNeg (Int.sub (c+b) x))
//!   (c+(a+1)) ((c+a)+1)
//!   (@Eq.symm.{1} Int ((c+a)+1) (c+(a+1)) (Int.add_assoc c a 1))
//!   step
//!   : Int.NonNeg (Int.sub (c+b) ((c+a)+1))   ≡   Int.lt (c+a) (c+b)
//! ```
//!
//! # Axiom closure
//!
//! Depends only on the constructive `Int.add_le_add_left` and `Int.add_assoc`
//! theorems plus the foundational `Eq.subst` / `Eq.symm`. None is a
//! `Declaration::Axiom`, so `env.axiom_deps("Int.add_lt_add_left")` is empty and
//! `env.proof_quality("Int.add_lt_add_left") == ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntAddLtAddLeftConsts {
    int_type: Expr,
    int_le: Expr,
    int_lt: Expr,
    int_add: Expr,
    int_sub: Expr,
    int_of_nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nonneg: Expr,
    add_le_add_left: Expr,
    add_assoc: Expr,
    eq_subst: Expr,
    eq_symm: Expr,
}

impl IntAddLtAddLeftConsts {
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
            add_le_add_left: Expr::const_(Name::from_string("Int.add_le_add_left"), vec![]),
            add_assoc: Expr::const_(Name::from_string("Int.add_assoc"), vec![]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1]),
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

/// Build `∀ a b : Int, Int.lt a b → ∀ c : Int, Int.lt (c+a) (c+b)`.
fn build_type(c: &IntAddLtAddLeftConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let lt_ab = c.lt(a.clone(), bv.clone());
    let (h_id, _h) = b.fresh_local(lt_ab.clone());
    let (c_id, cc) = b.fresh_local(c.int_type.clone());
    let concl = c.lt(c.add(cc.clone(), a.clone()), c.add(cc.clone(), bv.clone()));
    let r = b.mk_pi(c_id, BinderInfo::Default, c.int_type.clone(), concl);
    let r = b.mk_pi(h_id, BinderInfo::Default, lt_ab, r);
    let r = b.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), r);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// Body:
/// ```text
/// λ (a b : Int) (h : Int.lt a b) (c : Int) =>
///   @Eq.subst.{1} Int (fun x => Int.NonNeg (Int.sub (c+b) x))
///     (c+(a+1)) ((c+a)+1)
///     (@Eq.symm.{1} Int ((c+a)+1) (c+(a+1)) (Int.add_assoc c a 1))
///     (Int.add_le_add_left (a+1) b h c)
/// ```
fn build_value(c: &IntAddLtAddLeftConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let lt_ab = c.lt(a.clone(), bv.clone());
    let (h_id, h) = b.fresh_local(lt_ab.clone());
    let (c_id, cc) = b.fresh_local(c.int_type.clone());

    let one = c.one();
    let a_plus_one = c.add(a.clone(), one.clone());
    let c_plus_b = c.add(cc.clone(), bv.clone());
    let c_plus_a = c.add(cc.clone(), a.clone());
    // step subtrahend: c + (a + 1)
    let c_plus_a1 = c.add(cc.clone(), a_plus_one.clone());
    // goal subtrahend: (c + a) + 1
    let ca_plus_one = c.add(c_plus_a.clone(), one.clone());

    // step := Int.add_le_add_left (a+1) b h c : Int.le (c+(a+1)) (c+b)
    //       ≡ Int.NonNeg (Int.sub (c+b) (c+(a+1)))
    let step = Expr::apps(
        c.add_le_add_left.clone(),
        [a_plus_one, bv.clone(), h.clone(), cc.clone()],
    );

    // motive: fun x : Int => Int.NonNeg (Int.sub (c+b) x)
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(c.int_type.clone());
        let body = Expr::app(c.nonneg.clone(), c.sub(c_plus_b.clone(), x));
        let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
        mb.finish_child(lam)
    };

    // Int.add_assoc c a 1 : Eq Int ((c+a)+1) (c+(a+1))
    let assoc = Expr::apps(c.add_assoc.clone(), [cc.clone(), a.clone(), one.clone()]);
    // @Eq.symm.{1} Int ((c+a)+1) (c+(a+1)) assoc : Eq Int (c+(a+1)) ((c+a)+1)
    let symm = Expr::apps(
        c.eq_symm.clone(),
        [
            c.int_type.clone(),
            ca_plus_one.clone(),
            c_plus_a1.clone(),
            assoc,
        ],
    );

    // @Eq.subst.{1} Int motive (c+(a+1)) ((c+a)+1) symm step
    //   : Int.NonNeg (Int.sub (c+b) ((c+a)+1)) ≡ Int.lt (c+a) (c+b)
    let proof = Expr::apps(
        c.eq_subst.clone(),
        [
            c.int_type.clone(),
            motive,
            c_plus_a1,
            ca_plus_one,
            symm,
            step,
        ],
    );

    let val = b.mk_lam(c_id, BinderInfo::Default, c.int_type.clone(), proof);
    let val = b.mk_lam(h_id, BinderInfo::Default, lt_ab, val);
    let val = b.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), val);
    let val = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `Int.add_lt_add_left` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_ord()` has registered `Int.lt`, `Int.le`,
    ///           `Int.NonNeg`, `Int.add`, `Int.sub`, `Int.ofNat`.
    /// REQUIRES: `self.init_eq()` has registered `Eq.subst`, `Eq.symm`.
    /// ENSURES: On success, `Int.add_lt_add_left` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.add_lt_add_left` is already registered with
    ///          any declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_int_add_lt_add_left_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.add_lt_add_left");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_ord()?;
        self.init_eq()?;
        // Constructive dependencies.
        self.register_int_add_le_add_left_proof()?;
        self.register_int_add_assoc_proof()?;

        let c = IntAddLtAddLeftConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. Applies the constructive
        // `Int.add_le_add_left (a+1) b h c : Int.le (c+(a+1)) (c+b)` to the
        // delta-unfolded `h : Int.lt a b ≡ Int.le (a+1) b`, then transports its
        // `NonNeg (Int.sub (c+b) (c+(a+1)))` along
        // `Eq.symm (Int.add_assoc c a 1) : Eq (c+(a+1)) ((c+a)+1)` via
        // `@Eq.subst.{1}` with motive `fun x => Int.NonNeg (Int.sub (c+b) x)`,
        // yielding `Int.NonNeg (Int.sub (c+b) ((c+a)+1))` ≡
        // `Int.lt (c+a) (c+b)`. No `sorry`, no self-reference, no domain-axiom
        // dependency. Replaces the prior `Declaration::Axiom` in
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
    fn test_int_add_lt_add_left_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_add_lt_add_left_proof()
            .expect("first registration");
        env.register_int_add_lt_add_left_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.add_lt_add_left"))
            .expect("Int.add_lt_add_left should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_add_lt_add_left_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_add_lt_add_left_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.add_lt_add_left"))
            .expect("Int.add_lt_add_left is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.add_lt_add_left must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }

    #[test]
    fn test_int_add_lt_add_left_proof_quality_constructive() {
        use crate::env::ProofQuality;
        let mut env = Environment::new();
        env.register_int_add_lt_add_left_proof().unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Int.add_lt_add_left"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.add_lt_add_left must be Constructive, got {:?}",
            quality
        );
    }
}
