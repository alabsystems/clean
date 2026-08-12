// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Environment::adopt_instance_priority` — the registry primitive that lets
//! `.olean` import overwrite a GUESSED prelude instance priority with the value
//! Lean serialized, instead of letting first-registered-wins freeze the guess.
//!
//! Instance priority decides which candidate `synthInstance` reaches first, so a
//! wrong value silently changes the shape of every elaborated term. Three such
//! defects were dug out one at a time (`instOfNatNat` 100-vs-1000 `8d80c9d98`,
//! `instLTNat` 100-vs-1000 `066a1173f`, the B101 hetero bridges `28e7834a1`)
//! before this path existed.
//!
//! The decoys below are `Axiom`-kind constants with no value — the shape a
//! constant actually has after import. A `@[reducible]` definition decoy can be
//! delta-reduced away and would pass with or without the fix.

use super::{Environment, KernelClassInfo, KernelInstanceInfo};
use crate::name::Name;
use crate::{Declaration, Expr, Level};

fn env_with_axiom_instances(class: &str, instances: &[(&str, u32)]) -> Environment {
    let mut env = Environment::new();
    let class_name = Name::from_string(class);
    env.add_decl(Declaration::Axiom {
        name: class_name.clone(),
        level_params: vec![],
        type_: Expr::sort(Level::zero()),
    })
    .expect("class constant");
    env.register_class(KernelClassInfo {
        name: class_name.clone(),
        num_params: 0,
        out_params: Vec::new(),
        semi_out_params: Vec::new(),
    });
    for (name, priority) in instances {
        // AXIOM, NO VALUE — the imported shape.
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::const_str(class),
        })
        .unwrap_or_else(|e| panic!("axiom decoy {name}: {e}"));
        env.register_instance(KernelInstanceInfo {
            name: Name::from_string(name),
            class_name: class_name.clone(),
            priority: *priority,
            type_: None,
            value: None,
        });
    }
    env
}

fn order(env: &Environment, class: &str) -> Vec<(String, u32)> {
    env.get_class_instances(&Name::from_string(class))
        .iter()
        .map(|i| (i.name.to_string(), i.priority))
        .collect()
}

#[test]
fn test_adopt_instance_priority_raises_and_reseats() {
    let mut env = env_with_axiom_instances("C", &[("instLow", 100), ("instMid", 300)]);
    assert_eq!(
        order(&env, "C"),
        vec![("instMid".into(), 300), ("instLow".into(), 100)]
    );

    let previous = env.adopt_instance_priority(&Name::from_string("instLow"), 1000);
    assert_eq!(previous, Some(100), "returns the priority it replaced");
    assert_eq!(
        order(&env, "C"),
        vec![("instLow".into(), 1000), ("instMid".into(), 300)],
        "the raised instance must move to the front of the priority-descending list"
    );
}

#[test]
fn test_adopt_instance_priority_lowers_and_reseats() {
    // Lean serializes 500 for `instBEqOfDecidableEq`, so a raise-only path
    // would leave an over-guessed 1000 wrong in the other direction.
    let mut env = env_with_axiom_instances("C", &[("instMid", 300), ("instHigh", 1000)]);
    assert_eq!(
        order(&env, "C"),
        vec![("instHigh".into(), 1000), ("instMid".into(), 300)]
    );

    assert_eq!(
        env.adopt_instance_priority(&Name::from_string("instHigh"), 200),
        Some(1000)
    );
    assert_eq!(
        order(&env, "C"),
        vec![("instMid".into(), 300), ("instHigh".into(), 200)],
        "adoption is exact, not monotone"
    );
}

#[test]
fn test_adopt_instance_priority_never_duplicates_or_drops() {
    let mut env = env_with_axiom_instances("C", &[("instA", 100), ("instB", 100), ("instC", 100)]);
    assert_eq!(env.num_instances(), 3);

    env.adopt_instance_priority(&Name::from_string("instB"), 1000);
    let live = order(&env, "C");
    assert_eq!(env.num_instances(), 3, "re-seating must not add an entry");
    assert_eq!(live.len(), 3);
    assert_eq!(live[0], ("instB".to_owned(), 1000));
    let names: Vec<&str> = live.iter().map(|(n, _)| n.as_str()).collect();
    for expected in ["instA", "instB", "instC"] {
        assert!(names.contains(&expected), "{expected} must survive");
    }
    assert!(env.is_instance(&Name::from_string("instB")));
}

#[test]
fn test_adopt_instance_priority_is_idempotent() {
    let mut env = env_with_axiom_instances("C", &[("instA", 100), ("instB", 100)]);
    for _ in 0..3 {
        env.adopt_instance_priority(&Name::from_string("instA"), 1000);
    }
    assert_eq!(env.num_instances(), 2);
    assert_eq!(
        order(&env, "C"),
        vec![("instA".into(), 1000), ("instB".into(), 100)]
    );
}

#[test]
fn test_adopt_instance_priority_unchanged_value_is_a_no_op() {
    let mut env = env_with_axiom_instances("C", &[("instA", 100), ("instB", 100)]);
    let before = order(&env, "C");
    assert_eq!(
        env.adopt_instance_priority(&Name::from_string("instA"), 100),
        Some(100)
    );
    assert_eq!(
        order(&env, "C"),
        before,
        "an equal priority must not shuffle the intra-tier order"
    );
}

#[test]
fn test_adopt_instance_priority_never_fabricates_an_entry() {
    let mut env = env_with_axiom_instances("C", &[("instA", 100)]);
    assert_eq!(
        env.adopt_instance_priority(&Name::from_string("notAnInstance"), 1000),
        None,
        "an unregistered name must register nothing"
    );
    assert_eq!(env.num_instances(), 1);
    assert!(!env.is_instance(&Name::from_string("notAnInstance")));
}

/// The whole point, stated as the property that matters: after adoption the
/// bucket is still sorted priority-descending, which is the contract
/// `get_class_instances` and the elaborator's `InstanceTable` rebuild rely on.
#[test]
fn test_adopt_instance_priority_preserves_descending_order_invariant() {
    let mut env = env_with_axiom_instances(
        "C",
        &[
            ("i0", 100),
            ("i1", 200),
            ("i2", 300),
            ("i3", 400),
            ("i4", 500),
        ],
    );
    for (name, new_priority) in [("i4", 50), ("i0", 1000), ("i2", 250), ("i3", 400)] {
        env.adopt_instance_priority(&Name::from_string(name), new_priority);
        let live = order(&env, "C");
        assert_eq!(live.len(), 5, "after adopting {name}");
        assert!(
            live.windows(2).all(|w| w[0].1 >= w[1].1),
            "priority-descending invariant broken after adopting {name}: {live:?}"
        );
        assert_eq!(
            live.iter().find(|(n, _)| n == name).map(|(_, p)| *p),
            Some(new_priority)
        );
    }
}
