// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests: every rule reads the kernel VALUE, so a renamed or re-pointed
//! alias resolves by what it is, and a near-miss shape resolves to nothing.

use crate::carrier_prims::{BoolOp, CarrierPrim, ScalarCmp, UIntWidth};
use crate::opt::resolve_carrier_prims::*;
use clean_kernel::env::Declaration;
use clean_kernel::{BinderInfo, Environment, Expr, Name};

fn name(s: &str) -> Name {
    Name::from_string(s)
}

/// `(a b : UInt64) → Decidable (rel UInt64 inst a b)`, or with `b` and `a`
/// exchanged when `swapped`.
fn u64_decision_type(rel: &str, inst: &str, swapped: bool) -> Expr {
    let u = Expr::const_str("UInt64");
    let (x, y) = if swapped { (0, 1) } else { (1, 0) };
    let prop = Expr::apps(
        Expr::const_(name(rel), vec![clean_kernel::Level::zero()]),
        [
            u.clone(),
            Expr::const_str(inst),
            Expr::bvar(x),
            Expr::bvar(y),
        ],
    );
    Expr::arrow(
        u.clone(),
        Expr::arrow(u, Expr::app(Expr::const_str("Decidable"), prop)),
    )
}

/// The prelude plus three user aliases over `UInt64.decLt`/`decLe`.
fn env() -> Environment {
    let mut env = Environment::with_prelude();
    let u = Expr::const_str("UInt64");
    // `myLt := UInt64.decLt` — a bare-constant alias with an unrelated name.
    env.add_decl(Declaration::Definition {
        name: name("myLt"),
        level_params: vec![],
        type_: u64_decision_type("LT.lt", "instLTUInt64", false),
        value: Expr::const_str("UInt64.decLt"),
        is_reducible: true,
    })
    .expect("myLt");
    // `myLeEta := fun a b => UInt64.decLe a b` — the η-expanded alias.
    env.add_decl(Declaration::Definition {
        name: name("myLeEta"),
        level_params: vec![],
        type_: u64_decision_type("LE.le", "instLEUInt64", false),
        value: Expr::lam(
            BinderInfo::Default,
            u.clone(),
            Expr::lam(
                BinderInfo::Default,
                u.clone(),
                Expr::apps(
                    Expr::const_str("UInt64.decLe"),
                    [Expr::bvar(1), Expr::bvar(0)],
                ),
            ),
        ),
        is_reducible: true,
    })
    .expect("myLeEta");
    // `myGe := fun a b => UInt64.decLe b a` — swapped arguments: NOT an alias.
    env.add_decl(Declaration::Definition {
        name: name("myGe"),
        level_params: vec![],
        type_: u64_decision_type("LE.le", "instLEUInt64", true),
        value: Expr::lam(
            BinderInfo::Default,
            u.clone(),
            Expr::lam(
                BinderInfo::Default,
                u,
                Expr::apps(
                    Expr::const_str("UInt64.decLe"),
                    [Expr::bvar(0), Expr::bvar(1)],
                ),
            ),
        ),
        is_reducible: true,
    })
    .expect("myGe");
    env
}

#[test]
fn the_prelude_aliases_resolve_to_their_primitives() {
    let env = env();
    let cases = [
        (
            "instDecidableUInt64Le",
            "UInt64.decLe",
            CarrierPrim::Cmp(ScalarCmp::Ule, UIntWidth::W64),
        ),
        (
            "instDecidableUInt8Lt",
            "UInt8.decLt",
            CarrierPrim::Cmp(ScalarCmp::Ult, UIntWidth::W8),
        ),
        (
            "instDecidableEqUInt32",
            "UInt32.decEq",
            CarrierPrim::Cmp(ScalarCmp::Eq, UIntWidth::W32),
        ),
        ("and", "Bool.and", CarrierPrim::Bool(BoolOp::And)),
        ("or", "Bool.or", CarrierPrim::Bool(BoolOp::Or)),
        ("decide", "Decidable.decide", CarrierPrim::Decide),
        (
            "instDecidableEqBool",
            "Bool.decEq",
            CarrierPrim::Bool(BoolOp::Eq),
        ),
    ];
    for (alias, target, prim) in cases {
        assert_eq!(
            alias_target(&env, &name(alias), false),
            Some((name(target), prim)),
            "{alias}"
        );
    }
}

#[test]
fn an_alias_resolves_by_its_value_not_its_name() {
    let env = env();
    assert_eq!(
        alias_target(&env, &name("myLt"), false),
        Some((
            name("UInt64.decLt"),
            CarrierPrim::Cmp(ScalarCmp::Ult, UIntWidth::W64)
        ))
    );
    assert_eq!(
        alias_target(&env, &name("myLeEta"), false),
        Some((
            name("UInt64.decLe"),
            CarrierPrim::Cmp(ScalarCmp::Ule, UIntWidth::W64)
        ))
    );
    // Swapped arguments compute `b ≤ a`: not an alias of anything.
    assert_eq!(alias_target(&env, &name("myGe"), false), None);
}

#[test]
fn nat_aliases_resolve_only_at_the_pinned_handle() {
    let env = env();
    assert_eq!(alias_target(&env, &name("instDecidableEqNat"), false), None);
    assert!(matches!(
        alias_target(&env, &name("instDecidableEqNat"), true),
        Some((_, CarrierPrim::Nat(_)))
    ));
}

#[test]
fn the_beq_bridge_and_method_shapes_are_recognized_from_their_values() {
    let env = env();
    assert!(is_beq_of_decidable_eq(&env, &name("instBEqOfDecidableEq")));
    assert!(is_beq_method(&env, &name("BEq.beq")));
    // A different instance of the same class is not the bridge.
    assert!(!is_beq_of_decidable_eq(&env, &name("instBEqNat")));
    // `HAdd.hAdd` is a class method, but not `BEq.beq`'s recursor shape.
    assert!(!is_beq_method(&env, &name("HAdd.hAdd")));
}

#[test]
fn the_ofnat_instance_selects_its_own_argument() {
    let env = env();
    let class = name("OfNat");
    assert_eq!(
        instance_field_is_argument(&env, &name("instOfNatNat"), &class, 0, 1),
        Some(0)
    );
    // Applied to the wrong number of arguments: no reading.
    assert_eq!(
        instance_field_is_argument(&env, &name("instOfNatNat"), &class, 0, 2),
        None
    );
}
