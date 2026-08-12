// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.add_lt_add_right : ∀ a b : Int, Int.lt a b → ∀ c : Int,
//!    Int.lt (Int.add a c) (Int.add b c)`.
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
//! `Int.lt (a+c) (b+c)` to `Int.le ((a+c)+1) (b+c)` ≡
//! `Int.NonNeg (Int.sub (b+c) ((a+c)+1))`.
//!
//! # Proof sketch
//!
//! Apply the constructive `Int.add_le_add_right` to `h : Int.le (a+1) b`,
//! adding `c` on the right:
//!
//! ```text
//! step := Int.add_le_add_right (a+1) b h c
//!       : Int.le ((a+1)+c) (b+c)   ≡   Int.NonNeg (Int.sub (b+c) ((a+1)+c))
//! ```
//!
//! The goal's subtrahend is `(a+c)+1`, the step's is `(a+1)+c`. They are
//! equal via the constructive associativity/commutativity bridge
//! `(a+1)+c = a+(1+c) = a+(c+1) = (a+c)+1`, assembled with `Eq.trans` over
//! `Int.add_assoc` / `Int.add_comm` (the middle commutation lifted through
//! `Int.add a ·` by `congrArg`). Transport `step` forward along it with motive
//! `fun x => Int.NonNeg (Int.sub (b+c) x)`:
//!
//! ```text
//! @Eq.subst.{1} Int (fun x => Int.NonNeg (Int.sub (b+c) x))
//!   ((a+1)+c) ((a+c)+1)
//!   bridge
//!   step
//!   : Int.NonNeg (Int.sub (b+c) ((a+c)+1))   ≡   Int.lt (a+c) (b+c)
//! ```
//!
//! # Axiom closure
//!
//! Depends only on the constructive `Int.add_le_add_right`, `Int.add_assoc`,
//! `Int.add_comm` theorems plus the foundational `Eq.subst` / `Eq.trans` /
//! `Eq.symm` / `congrArg`. None is a `Declaration::Axiom`, so
//! `env.axiom_deps("Int.add_lt_add_right")` is empty and
//! `env.proof_quality("Int.add_lt_add_right") == ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntAddLtAddRightConsts {
    int_type: Expr,
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    int_le: Expr,
    int_lt: Expr,
    int_add: Expr,
    int_sub: Expr,
    int_of_nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nonneg: Expr,
    add_le_add_right: Expr,
    add_assoc: Expr,
    add_comm: Expr,
    congr_arg: Expr,
    eq_subst: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
}

impl IntAddLtAddRightConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            #[cfg(test)]
            int_le: Expr::const_(Name::from_string("Int.le"), vec![]),
            int_lt: Expr::const_(Name::from_string("Int.lt"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_sub: Expr::const_(Name::from_string("Int.sub"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nonneg: Expr::const_(Name::from_string("Int.NonNeg"), vec![]),
            add_le_add_right: Expr::const_(Name::from_string("Int.add_le_add_right"), vec![]),
            add_assoc: Expr::const_(Name::from_string("Int.add_assoc"), vec![]),
            add_comm: Expr::const_(Name::from_string("Int.add_comm"), vec![]),
            // congrArg.{1,1} : {α β : Type} → {a₁ a₂ : α} → (f : α → β) →
            //   a₁ = a₂ → f a₁ = f a₂
            congr_arg: Expr::const_(
                Name::from_string("congrArg"),
                vec![type1.clone(), type1.clone()],
            ),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1]),
        }
    }

    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
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

    /// `Eq.trans Int x y z h1 h2 : Eq Int x z`.
    fn trans(&self, x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.int_type.clone(), x, y, z, h1, h2],
        )
    }

    /// `Int.ofNat (Nat.succ Nat.zero)`.
    fn one(&self) -> Expr {
        Expr::app(
            self.int_of_nat.clone(),
            Expr::app(self.nat_succ.clone(), self.nat_zero.clone()),
        )
    }
}

/// Build `∀ a b : Int, Int.lt a b → ∀ c : Int, Int.lt (a+c) (b+c)`.
fn build_type(c: &IntAddLtAddRightConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let lt_ab = c.lt(a.clone(), bv.clone());
    let (h_id, _h) = b.fresh_local(lt_ab.clone());
    let (c_id, cc) = b.fresh_local(c.int_type.clone());
    let concl = c.lt(c.add(a.clone(), cc.clone()), c.add(bv.clone(), cc.clone()));
    let r = b.mk_pi(c_id, BinderInfo::Default, c.int_type.clone(), concl);
    let r = b.mk_pi(h_id, BinderInfo::Default, lt_ab, r);
    let r = b.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), r);
    let r = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), r);
    b.finish(r)
}

/// Body:
/// ```text
/// λ (a b : Int) (h : Int.lt a b) (c : Int) =>
///   @Eq.subst.{1} Int (fun x => Int.NonNeg (Int.sub (b+c) x))
///     ((a+1)+c) ((a+c)+1)
///     bridge
///     (Int.add_le_add_right (a+1) b h c)
/// ```
fn build_value(c: &IntAddLtAddRightConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let lt_ab = c.lt(a.clone(), bv.clone());
    let (h_id, h) = b.fresh_local(lt_ab.clone());
    let (c_id, cc) = b.fresh_local(c.int_type.clone());

    let one = c.one();
    let a_plus_one = c.add(a.clone(), one.clone());
    let b_plus_c = c.add(bv.clone(), cc.clone());
    let a_plus_c = c.add(a.clone(), cc.clone());
    // step subtrahend: (a + 1) + c
    let a1_plus_c = c.add(a_plus_one.clone(), cc.clone());
    // goal subtrahend: (a + c) + 1
    let ac_plus_one = c.add(a_plus_c.clone(), one.clone());
    // intermediates of the bridge
    let one_plus_c = c.add(one.clone(), cc.clone()); // 1 + c
    let c_plus_one = c.add(cc.clone(), one.clone()); // c + 1
    let a_plus_1c = c.add(a.clone(), one_plus_c.clone()); // a + (1 + c)
    let a_plus_c1 = c.add(a.clone(), c_plus_one.clone()); // a + (c + 1)

    // step := Int.add_le_add_right (a+1) b h c : Int.le ((a+1)+c) (b+c)
    //       ≡ Int.NonNeg (Int.sub (b+c) ((a+1)+c))
    let step = Expr::apps(
        c.add_le_add_right.clone(),
        [a_plus_one.clone(), bv.clone(), h.clone(), cc.clone()],
    );

    // bridge step 1: Int.add_assoc a 1 c : Eq ((a+1)+c) (a+(1+c))
    let s1 = Expr::apps(c.add_assoc.clone(), [a.clone(), one.clone(), cc.clone()]);

    // comm := Int.add_comm 1 c : Eq (1+c) (c+1)
    let comm = Expr::apps(c.add_comm.clone(), [one.clone(), cc.clone()]);
    // func := fun x : Int => Int.add a x
    let func = {
        let mut fb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = fb.fresh_local(c.int_type.clone());
        let body = c.add(a.clone(), x);
        let lam = fb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
        fb.finish_child(lam)
    };
    // s2 := congrArg Int Int (1+c) (c+1) func comm : Eq (a+(1+c)) (a+(c+1))
    let s2 = Expr::apps(
        c.congr_arg.clone(),
        [
            c.int_type.clone(),
            c.int_type.clone(),
            one_plus_c.clone(),
            c_plus_one.clone(),
            func,
            comm,
        ],
    );

    // s3 := Int.add_assoc a c 1 : Eq ((a+c)+1) (a+(c+1))
    let s3_raw = Expr::apps(c.add_assoc.clone(), [a.clone(), cc.clone(), one.clone()]);
    // Eq.symm of it : Eq (a+(c+1)) ((a+c)+1)
    let s3 = Expr::apps(
        c.eq_symm.clone(),
        [
            c.int_type.clone(),
            ac_plus_one.clone(),
            a_plus_c1.clone(),
            s3_raw,
        ],
    );

    // inner := Eq.trans (a+(1+c)) (a+(c+1)) ((a+c)+1) s2 s3 : Eq (a+(1+c)) ((a+c)+1)
    let inner = c.trans(
        a_plus_1c.clone(),
        a_plus_c1.clone(),
        ac_plus_one.clone(),
        s2,
        s3,
    );
    // bridge := Eq.trans ((a+1)+c) (a+(1+c)) ((a+c)+1) s1 inner : Eq ((a+1)+c) ((a+c)+1)
    let bridge = c.trans(a1_plus_c.clone(), a_plus_1c, ac_plus_one.clone(), s1, inner);

    // motive: fun x : Int => Int.NonNeg (Int.sub (b+c) x)
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(c.int_type.clone());
        let body = Expr::app(c.nonneg.clone(), c.sub(b_plus_c.clone(), x));
        let lam = mb.mk_lam(x_id, BinderInfo::Default, c.int_type.clone(), body);
        mb.finish_child(lam)
    };

    // @Eq.subst.{1} Int motive ((a+1)+c) ((a+c)+1) bridge step
    //   : Int.NonNeg (Int.sub (b+c) ((a+c)+1)) ≡ Int.lt (a+c) (b+c)
    let proof = Expr::apps(
        c.eq_subst.clone(),
        [
            c.int_type.clone(),
            motive,
            a1_plus_c,
            ac_plus_one,
            bridge,
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
    /// Register `Int.add_lt_add_right` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_ord()` has registered `Int.lt`, `Int.le`,
    ///           `Int.NonNeg`, `Int.add`, `Int.sub`, `Int.ofNat`.
    /// REQUIRES: `self.init_eq()` has registered `Eq.subst`, `Eq.trans`,
    ///           `Eq.symm`, `congrArg`.
    /// ENSURES: On success, `Int.add_lt_add_right` is a `Declaration::Theorem`
    ///          with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.add_lt_add_right` is already registered with
    ///          any declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_int_add_lt_add_right_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.add_lt_add_right");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_ord()?;
        self.init_eq()?;
        // Constructive dependencies.
        self.register_int_add_le_add_right_proof()?;
        self.register_int_add_assoc_proof()?;
        self.register_int_add_comm_proof()?;

        let c = IntAddLtAddRightConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term. Applies the constructive
        // `Int.add_le_add_right (a+1) b h c : Int.le ((a+1)+c) (b+c)` to the
        // delta-unfolded `h : Int.lt a b ≡ Int.le (a+1) b`, then transports its
        // `NonNeg (Int.sub (b+c) ((a+1)+c))` forward along the constructive
        // `Eq.trans` bridge `(a+1)+c = a+(1+c) = a+(c+1) = (a+c)+1`
        // (`Int.add_assoc` / `Int.add_comm`, the commutation lifted through
        // `Int.add a ·` by `congrArg`) via `@Eq.subst.{1}` with motive
        // `fun x => Int.NonNeg (Int.sub (b+c) x)`, yielding
        // `Int.NonNeg (Int.sub (b+c) ((a+c)+1))` ≡ `Int.lt (a+c) (b+c)`. No
        // `sorry`, no self-reference, no domain-axiom dependency. Replaces the
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
    fn test_int_add_lt_add_right_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_add_lt_add_right_proof()
            .expect("first registration");
        env.register_int_add_lt_add_right_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.add_lt_add_right"))
            .expect("Int.add_lt_add_right should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_add_lt_add_right_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_add_lt_add_right_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.add_lt_add_right"))
            .expect("Int.add_lt_add_right is registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.add_lt_add_right must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }

    #[test]
    fn test_int_add_lt_add_right_proof_quality_constructive() {
        use crate::env::ProofQuality;
        let mut env = Environment::new();
        env.register_int_add_lt_add_right_proof().unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Int.add_lt_add_right"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.add_lt_add_right must be Constructive, got {:?}",
            quality
        );
    }
}
