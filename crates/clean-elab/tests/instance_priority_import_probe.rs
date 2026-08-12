// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Measurement probe + regression: what the corrected instance priorities
//! change under a real `import Init`.**
//!
//! Clean's hand-rolled prelude used to register 54 of the 56 instances Lean also
//! declares with a priority the shipped `.olean` contradicts (census:
//! `data/prelude_instance_priority_census.json`). Priority DOMINATES
//! `candidate_order`, so each of those sank below every imported instance of the
//! same class.
//!
//! This file is the batched probe — ONE `import Init` (the expensive step)
//! covering every measured row — and it doubles as the standing regression:
//!
//!  * [`probe_dump_measured_instance_ranks`] prints, for every measured
//!    instance, its RANK and priority inside its class's candidate list under a
//!    real import. Run with `--nocapture` to read it; diff two builds to see
//!    exactly what a priority change moved.
//!  * [`imported_ground_goals_resolve_to_the_concrete_prelude_instance`] is the
//!    assertion: for every single-parameter class where the prelude ships a
//!    concrete instance, the ground goal `Class Carrier` must resolve to THAT
//!    instance and not to some imported general one.
//!
//! Both lanes skip when the pinned toolchain is absent.
//!
//! Decoy discipline: this probe needs no synthetic decoy at all — the ~3,000
//! competing instances come from the real `.olean`, so they are exactly the
//! `Axiom`/opaque, non-`@[reducible]` shape that a hand-built fixture has to
//! imitate. That is the point of paying for a real import here; the synthetic
//! counterparts live in `le_nat_instance_priority_regression.rs` and
//! `lt_nat_instance_priority_regression.rs`.

use clean_elab::ElabCtx;
use clean_kernel::env::Environment;
use clean_kernel::expr::{Expr, ExprKind};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_olean::load_module_with_deps;
use std::path::PathBuf;

/// The pinned toolchain whose `InstanceEntry` layout the decoder targets.
const PINNED_TOOLCHAIN: &str = "leanprover--lean4---v4.30.0-rc2";

const IMPORT_ROOT: &str = "Init";

/// Every measured instance, as `(instance, class)`. Mirrors the rows of
/// `data/prelude_instance_priority_census.json`; kept as a literal so this test
/// needs no JSON dependency and so a reader sees the surface at a glance.
const MEASURED: &[(&str, &str)] = &[
    ("Array.instGetElem?NatLtSize", "GetElem?"),
    ("Array.instGetElemNatLtSize", "GetElem"),
    ("List.instGetElem?NatLtLength", "GetElem?"),
    ("List.instGetElemNatLtLength", "GetElem"),
    ("List.instMembership", "Membership"),
    ("instBEqOfDecidableEq", "BEq"),
    ("instBEqOption", "BEq"),
    ("instDecidableAnd", "Decidable"),
    ("instDecidableEqBool", "DecidableEq"),
    ("instDecidableEqChar", "DecidableEq"),
    ("instDecidableEqNat", "DecidableEq"),
    ("instDecidableEqString", "DecidableEq"),
    ("instDecidableEqUInt16", "DecidableEq"),
    ("instDecidableEqUInt32", "DecidableEq"),
    ("instDecidableEqUInt64", "DecidableEq"),
    ("instDecidableEqUInt8", "DecidableEq"),
    ("instDecidableEqUSize", "DecidableEq"),
    ("instDecidableFalse", "Decidable"),
    ("instDecidableNot", "Decidable"),
    ("instDecidableOr", "Decidable"),
    ("instDecidableTrue", "Decidable"),
    ("instFunctorOption", "Functor"),
    ("instHashableBool", "Hashable"),
    ("instHashableNat", "Hashable"),
    ("instInhabitedBool", "Inhabited"),
    ("instInhabitedList", "Inhabited"),
    ("instInhabitedNat", "Inhabited"),
    ("instInhabitedOption", "Inhabited"),
    ("instInhabitedOrdering", "Inhabited"),
    ("instLEFloat", "LE"),
    ("instLENat", "LE"),
    ("instLEUInt16", "LE"),
    ("instLEUInt32", "LE"),
    ("instLEUInt64", "LE"),
    ("instLEUInt8", "LE"),
    ("instLEUSize", "LE"),
    ("instLTFloat", "LT"),
    ("instLTNat", "LT"),
    ("instLTUInt16", "LT"),
    ("instLTUInt32", "LT"),
    ("instLTUInt64", "LT"),
    ("instLTUInt8", "LT"),
    ("instLTUSize", "LT"),
    ("instMinNat", "Min"),
    ("instNegFloat", "Neg"),
    ("instOfNatNat", "OfNat"),
    ("instOrdBool", "Ord"),
    ("instOrdNat", "Ord"),
    ("instOrdOrdering", "Ord"),
    ("instReprBool", "Repr"),
    ("instReprList", "Repr"),
    ("instReprNat", "Repr"),
    ("instReprString", "Repr"),
    ("instToStringBool", "ToString"),
    ("instToStringNat", "ToString"),
    ("instToStringString", "ToString"),
];

/// Single-parameter classes whose ground goal `Class Carrier` can be built
/// directly, with the prelude instance that must win it.
///
/// `Decidable`, `GetElem`/`GetElem?` and `Membership` are omitted: their goals
/// need a proposition / an index + bound / a collection element, so they are
/// covered by the rank dump rather than by a resolution assertion.
const GROUND_GOALS: &[(&str, &str, &str)] = &[
    // (class, carrier, expected instance)
    ("LE", "Nat", "instLENat"),
    ("LE", "UInt8", "instLEUInt8"),
    ("LE", "UInt16", "instLEUInt16"),
    ("LE", "UInt32", "instLEUInt32"),
    ("LE", "UInt64", "instLEUInt64"),
    ("LE", "USize", "instLEUSize"),
    ("LE", "Float", "instLEFloat"),
    ("LT", "Nat", "instLTNat"),
    ("LT", "UInt8", "instLTUInt8"),
    ("LT", "UInt16", "instLTUInt16"),
    ("LT", "UInt32", "instLTUInt32"),
    ("LT", "UInt64", "instLTUInt64"),
    ("LT", "USize", "instLTUSize"),
    ("LT", "Float", "instLTFloat"),
    ("Ord", "Nat", "instOrdNat"),
    ("Ord", "Bool", "instOrdBool"),
    ("Min", "Nat", "instMinNat"),
    ("Hashable", "Nat", "instHashableNat"),
    ("Hashable", "Bool", "instHashableBool"),
    ("ToString", "Nat", "instToStringNat"),
    ("ToString", "Bool", "instToStringBool"),
    ("ToString", "String", "instToStringString"),
    ("Repr", "Nat", "instReprNat"),
    ("Repr", "Bool", "instReprBool"),
    ("Repr", "String", "instReprString"),
    ("Inhabited", "Nat", "instInhabitedNat"),
    ("Inhabited", "Bool", "instInhabitedBool"),
    ("Neg", "Float", "instNegFloat"),
];

fn v4_30_lib_path() -> Option<PathBuf> {
    let home = std::env::var("HOME").ok()?;
    let lib = PathBuf::from(home)
        .join(".elan/toolchains")
        .join(PINNED_TOOLCHAIN)
        .join("lib/lean");
    lib.join("Init.olean").is_file().then_some(lib)
}

/// A prelude environment with a real `import Init` on top — the configuration
/// where a hand-registered priority actually competes with Lean's.
fn imported_env() -> Option<Environment> {
    let lib = v4_30_lib_path()?;
    let mut env = Environment::with_prelude();
    load_module_with_deps(&mut env, IMPORT_ROOT, &[lib])
        .unwrap_or_else(|e| panic!("importing {IMPORT_ROOT} must succeed: {e}"));
    Some(env)
}

fn head_name(e: &Expr) -> Option<Name> {
    match e.get_app_fn().kind() {
        ExprKind::Const(n, _) => Some(n.clone()),
        _ => None,
    }
}

/// Rank (0-based) and priority of `instance` inside `class`'s candidate list.
fn rank_of(env: &Environment, class: &str, instance: &str) -> Option<(usize, usize, u32)> {
    let entries = env.get_class_instances(&Name::from_string(class));
    let target = Name::from_string(instance);
    let idx = entries.iter().position(|i| i.name == target)?;
    Some((idx, entries.len(), entries[idx].priority))
}

/// MEASUREMENT: rank + priority of every measured instance under a real
/// `import Init`. Prints with `--nocapture`; diff two builds to attribute a
/// change. Asserts only that nothing vanished, so the dump is always readable.
#[test]
fn probe_dump_measured_instance_ranks() {
    let Some(env) = imported_env() else {
        eprintln!("Skipping: {PINNED_TOOLCHAIN} not installed");
        return;
    };
    eprintln!(
        "\n=== instance ranks under real `import {IMPORT_ROOT}` ({} constants) ===",
        env.num_constants()
    );
    eprintln!(
        "{:<32} {:<12} {:>10} {:>12}",
        "instance", "class", "priority", "rank/total"
    );
    let mut absent = Vec::new();
    for (instance, class) in MEASURED {
        match rank_of(&env, class, instance) {
            Some((idx, total, priority)) => eprintln!(
                "{instance:<32} {class:<12} {priority:>10} {:>12}",
                format!("{}/{}", idx + 1, total)
            ),
            None => {
                eprintln!("{instance:<32} {class:<12} {:>10} {:>12}", "-", "ABSENT");
                absent.push(*instance);
            }
        }
    }
    eprintln!();
    assert!(
        absent.is_empty(),
        "measured instances vanished from their class bucket after import: {absent:?}"
    );
}

/// REGRESSION: under a real `import Init`, every ground goal whose carrier the
/// prelude ships a concrete instance for must resolve to THAT instance.
///
/// Pre-fix these lost outright: the prelude's 100 ranks below every imported
/// instance, all of which carry Lean's real 1000.
#[test]
fn imported_ground_goals_resolve_to_the_concrete_prelude_instance() {
    let Some(env) = imported_env() else {
        eprintln!("Skipping: {PINNED_TOOLCHAIN} not installed");
        return;
    };
    let mut ctx = ElabCtx::new(&env);

    let mut wrong = Vec::new();
    let mut unresolved = Vec::new();
    for (class, carrier, expected) in GROUND_GOALS {
        if env.get_const(&Name::from_string(carrier)).is_none()
            || env.get_const(&Name::from_string(class)).is_none()
        {
            continue; // carrier/class absent from this import: nothing to claim
        }
        let goal = Expr::app(
            Expr::const_(Name::from_string(class), vec![Level::zero()]),
            Expr::const_(Name::from_string(carrier), Vec::<Level>::new()),
        );
        match ctx.resolve_instance(&goal).as_ref().and_then(head_name) {
            Some(winner) if winner == Name::from_string(expected) => {}
            Some(winner) => wrong.push(format!("{class} {carrier}: got {winner}, want {expected}")),
            None => unresolved.push(format!("{class} {carrier} (want {expected})")),
        }
    }

    assert!(
        wrong.is_empty(),
        "under real `import {IMPORT_ROOT}`, ground goals resolved to an imported general \
         instance instead of the concrete prelude one:\n  {}\nThis is the guessed-priority \
         defect: the prelude registration must carry the priority the shipped `.olean` \
         serializes (see data/prelude_instance_priority_census.json).",
        wrong.join("\n  ")
    );
    // Unresolved is reported, not asserted: a goal Clean cannot synthesize at
    // all is a different (pre-existing) gap and must not masquerade as this one.
    if !unresolved.is_empty() {
        eprintln!("NOTE: goals that did not resolve at all (separate gap): {unresolved:?}");
    }
}
