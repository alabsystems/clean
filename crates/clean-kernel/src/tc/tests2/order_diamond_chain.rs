// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Multi-hop typeclass-instance-diamond def-eq for the `LE.le` / `LT.lt`
//! projection chain through `Preorder` / `PartialOrder` / `LinearOrder`.
//!
//! ## What this pins (the real-Mathlib `Order/Basic`, `Nat/Defs` residual)
//!
//! A `stamp-verified` faildump over `Mathlib/Data/Nat/Defs` shows the dominant
//! masked-fallback class is same-head `LE.le`/`LT.lt`/`Eq` comparisons whose
//! INSTANCE argument differs:
//!
//! ```text
//!   expected  @LE.le Nat instLENat a b
//!   got       @LE.le Nat (Preorder.toLE
//!                          (PartialOrder.toPreorder
//!                           (LinearOrder.toPartialOrder Nat.instLinearOrder))) a b
//! ```
//!
//! Both sides are the SAME head `LE.le`; the instance args are a bare instance
//! vs a parent-projection chain. They ARE definitionally equal because BOTH the
//! bare `instLENat` and the `Preorder.toLE(…LinearOrder…)` projection chain
//! delta+projection-reduce to the SAME `LE.mk Nat.le`.
//!
//! These tests register the faithful multi-hop `extends` chain — with a
//! VALUE-BEARING `Nat.instLinearOrder` — and prove the kernel's `is_def_eq`
//! reduces the whole chain and recognises the diamond. This DEMONSTRATES the
//! kernel def-eq is COMPLETE for the instance-diamond class: when the root
//! instance carries its value, the multi-hop `Preorder.toLE(…)` chain converges
//! to the bare `instLENat` form. (The real-corpus residual is therefore NOT a
//! kernel def-eq gap but an import-side cascade: when the ROOT instance
//! `Nat.instLinearOrder` itself fails to kernel-verify and is masked to a
//! value-less axiom, the projection chain is genuinely irreducible and the
//! kernel correctly rejects — confirmed by the `…_root_axiom_…` counter-test.)
//!
//! ## Soundness pins
//!
//! The negative tests confirm the reduction is COMPLETENESS, never relaxation:
//! a chain rooted at a DIFFERENT carrier's instance (`Int`), and a chain whose
//! root instance is a value-less axiom, both correctly stay NON-def-eq.

use super::*;
use crate::env::Declaration;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};

/// Register a single-field "extends parent" structure `Child α` with
/// constructor `Child.mk : {α} → (toParent : Parent α) → Child α` and the
/// parent-projection function `Child.toParent : {α} → [Child α] → Parent α`
/// whose body is `λ {α} inst => Proj(Child, 0, inst)` (the genuine Lean
/// parent-projection shape).
///
/// `parent_app` builds `Parent α` under the `α` binder (BVar(0)).
fn add_extends_structure(env: &mut Environment, child: &str, parent: &str) {
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());
    let type_u = Expr::sort(Level::succ(u_level.clone()));

    let child_name = Name::from_string(child);
    let child_const =
        |a: Expr| Expr::app(Expr::const_(child_name.clone(), vec![u_level.clone()]), a);
    let parent_const = |a: Expr| {
        Expr::app(
            Expr::const_(Name::from_string(parent), vec![u_level.clone()]),
            a,
        )
    };

    // Child : Type u → Type u
    let child_type = Expr::pi(BinderInfo::Implicit, type_u.clone(), type_u.clone());

    // Child.mk : {α : Type u} → (toParent : Parent α) → Child α
    // under α (BVar after binder): Parent (BVar 0) → Child (BVar 1)
    let mk_type = Expr::pi(
        BinderInfo::Implicit,
        type_u.clone(),
        Expr::pi(
            BinderInfo::Default,
            parent_const(Expr::bvar(0)),
            child_const(Expr::bvar(1)),
        ),
    );

    env.add_inductive(InductiveDecl {
        level_params: vec![u.clone()],
        num_params: 1,
        types: vec![InductiveType {
            name: child_name.clone(),
            type_: child_type,
            constructors: vec![Constructor {
                name: Name::from_string(&format!("{child}.mk")),
                type_: mk_type,
            }],
        }],
    })
    .unwrap_or_else(|e| panic!("{child} inductive registers: {e:?}"));

    env.register_structure_fields(
        child_name.clone(),
        vec![Name::from_string(&format!("to{parent}"))],
    )
    .expect("structure fields register");

    // Child.toParent : {α} → [inst : Child α] → Parent α
    //   value: λ {α} [inst] => Proj(Child, 0, inst)
    let proj_name = Name::from_string(&format!("{child}.to{parent}"));
    let proj_type = Expr::pi(
        BinderInfo::Implicit,
        type_u.clone(),
        Expr::pi(
            BinderInfo::InstImplicit,
            child_const(Expr::bvar(0)),
            parent_const(Expr::bvar(1)),
        ),
    );
    let proj_value = Expr::lam(
        BinderInfo::Implicit,
        type_u,
        Expr::lam(
            BinderInfo::InstImplicit,
            child_const(Expr::bvar(0)),
            Expr::proj(child_name, 0, Expr::bvar(0)),
        ),
    );
    env.add_decl(Declaration::Definition {
        name: proj_name,
        level_params: vec![u],
        type_: proj_type,
        value: proj_value,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("{child}.to{parent} projection registers: {e:?}"));
}

/// Build the full faithful chain on top of the kernel `LE`/`LT` classes:
///   `Preorder extends LE`, `PartialOrder extends Preorder`,
///   `LinearOrder extends PartialOrder`,
/// plus a VALUE-BEARING `Nat.instLinearOrder` whose `LE` parent reduces to
/// `LE.mk Nat.le`.
///
/// Returns the environment with `instLENat` (kernel's `init_le`) and the full
/// chain registered.
fn order_chain_env() -> Environment {
    let mut env = Environment::new();
    env.init_le().expect("init_le");
    env.init_lt().expect("init_lt");

    add_extends_structure(&mut env, "Preorder", "LE");
    add_extends_structure(&mut env, "PartialOrder", "Preorder");
    add_extends_structure(&mut env, "LinearOrder", "PartialOrder");

    // Nat.instLinearOrder : LinearOrder Nat, value-bearing, rooted at instLENat.
    //   LinearOrder.mk Nat (PartialOrder.mk Nat (Preorder.mk Nat instLENat))
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let u0 = vec![Level::zero()];
    let mk = |s: &str, arg: Expr| {
        Expr::app(
            Expr::app(Expr::const_(Name::from_string(s), u0.clone()), nat.clone()),
            arg,
        )
    };
    let inst_le_nat = Expr::const_(Name::from_string("instLENat"), vec![]);
    let preorder_nat = mk("Preorder.mk", inst_le_nat);
    let partial_nat = mk("PartialOrder.mk", preorder_nat);
    let linear_nat = mk("LinearOrder.mk", partial_nat);

    let linord_nat_ty = Expr::app(
        Expr::const_(Name::from_string("LinearOrder"), u0.clone()),
        nat.clone(),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("Nat.instLinearOrder"),
        level_params: vec![],
        type_: linord_nat_ty,
        value: linear_nat,
        is_reducible: true,
    })
    .expect("Nat.instLinearOrder registers");

    env
}

/// `@LE.le Nat (Preorder.toLE (PartialOrder.toPreorder (LinearOrder.toPartialOrder
/// Nat.instLinearOrder))) a b` — the parent-projection-chain instance form.
fn le_via_chain(a: Expr, b: Expr) -> Expr {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let u0 = vec![Level::zero()];
    let proj = |s: &str, arg: Expr| {
        Expr::app(
            Expr::app(Expr::const_(Name::from_string(s), u0.clone()), nat.clone()),
            arg,
        )
    };
    let inst = Expr::const_(Name::from_string("Nat.instLinearOrder"), vec![]);
    let to_partial = proj("LinearOrder.toPartialOrder", inst);
    let to_preorder = proj("PartialOrder.toPreorder", to_partial);
    let to_le = proj("Preorder.toLE", to_preorder);
    // @LE.le Nat to_le a b
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::const_(Name::from_string("LE.le"), u0), nat),
                to_le,
            ),
            a,
        ),
        b,
    )
}

/// `@LE.le Nat instLENat a b` — the bare instance form.
fn le_via_bare(a: Expr, b: Expr) -> Expr {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
                    nat,
                ),
                Expr::const_(Name::from_string("instLENat"), vec![]),
            ),
            a,
        ),
        b,
    )
}

fn nat(v: u64) -> Expr {
    Expr::nat_lit(v)
}

/// COMPLETENESS: the multi-hop parent-projection-chain instance form is
/// definitionally equal to the bare instance form. Both reduce (delta +
/// projection) to `Nat.le 2 5`.
#[test]
fn test_le_via_preorder_chain_defeq_bare_instance() {
    let env = order_chain_env();
    let tc = TypeChecker::new(&env);

    let chain = le_via_chain(nat(2), nat(5));
    let bare = le_via_bare(nat(2), nat(5));

    assert!(
        tc.is_def_eq(&chain, &bare),
        "@LE.le Nat (Preorder.toLE (… LinearOrder.toPartialOrder Nat.instLinearOrder)) 2 5 \
         must be def-eq to @LE.le Nat instLENat 2 5 (both reduce to Nat.le 2 5)"
    );
    // Symmetric.
    assert!(
        tc.is_def_eq(&bare, &chain),
        "def-eq must be symmetric for the instance-diamond"
    );
}

/// COMPLETENESS: the chain form also reduces directly to the bare relation
/// `Nat.le 2 5` (whnf reaches the underlying operation through the whole chain).
#[test]
fn test_le_via_preorder_chain_defeq_nat_le() {
    let env = order_chain_env();
    let tc = TypeChecker::new(&env);

    let chain = le_via_chain(nat(2), nat(5));
    let nat_le = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.le"), vec![]), nat(2)),
        nat(5),
    );
    assert!(
        tc.is_def_eq(&chain, &nat_le),
        "the full Preorder.toLE projection chain must reduce to Nat.le 2 5"
    );
}

/// SOUNDNESS (counter-test): when the ROOT instance is a VALUE-LESS axiom (the
/// real-corpus masked-fallback situation for `Nat.instLinearOrder`), the
/// projection chain is genuinely irreducible, so the chain form is NOT def-eq
/// to the bare instance form. The kernel MUST reject it — this is exactly the
/// behaviour that produces the real-corpus residual, and it is CORRECT.
#[test]
fn test_le_via_chain_rooted_at_axiom_is_not_defeq() {
    let mut env = Environment::new();
    env.init_le().expect("init_le");
    env.init_lt().expect("init_lt");
    add_extends_structure(&mut env, "Preorder", "LE");
    add_extends_structure(&mut env, "PartialOrder", "Preorder");
    add_extends_structure(&mut env, "LinearOrder", "PartialOrder");

    // Nat.instLinearOrder as a VALUE-LESS axiom (masked fallback shape).
    let linord_nat_ty = Expr::app(
        Expr::const_(Name::from_string("LinearOrder"), vec![Level::zero()]),
        Expr::const_(Name::from_string("Nat"), vec![]),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat.instLinearOrder"),
        level_params: vec![],
        type_: linord_nat_ty,
    })
    .expect("axiom registers");

    let tc = TypeChecker::new(&env);
    let chain = le_via_chain(nat(2), nat(5));
    let bare = le_via_bare(nat(2), nat(5));
    assert!(
        !tc.is_def_eq(&chain, &bare),
        "SOUNDNESS: a projection chain rooted at a VALUE-LESS axiom instance is \
         irreducible and must NOT be def-eq to the bare instance form (this is the \
         real-corpus residual root cause, and rejecting it is correct)"
    );
}

/// SOUNDNESS (counter-test): the chain instance form `@LE.le Nat (…) a b` must
/// NOT be def-eq to a DIFFERENT relation `@LT.lt Nat instLTNat a b` (Nat.le vs
/// Nat.lt). Confirms the completeness reduction never equates distinct relations.
#[test]
fn test_le_chain_not_defeq_lt() {
    let env = order_chain_env();
    let tc = TypeChecker::new(&env);

    let le_chain = le_via_chain(nat(2), nat(5));
    let lt_bare = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
                    Expr::const_(Name::from_string("Nat"), vec![]),
                ),
                Expr::const_(Name::from_string("instLTNat"), vec![]),
            ),
            nat(2),
        ),
        nat(5),
    );
    assert!(
        !tc.is_def_eq(&le_chain, &lt_bare),
        "SOUNDNESS: LE chain (Nat.le) must NOT be def-eq to LT.lt (Nat.lt)"
    );
}
