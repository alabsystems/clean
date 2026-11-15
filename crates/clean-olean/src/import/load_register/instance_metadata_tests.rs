// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Exact metadata membership, not kernel admission or whole-program semantics.
use super::*;
use crate::test_support::{compiled_fixture_dir, run_oracle};
use clean_kernel::env::ConstantInfo;
use serde_json::Value;
use std::collections::BTreeSet;
use std::sync::OnceLock;

/// The `instance_parity` family (`tests/fixtures/lean/v4.30.0-rc2/instance_parity/
/// README.md`) — a `prelude`, import-free, non-`module` source, so a single base
/// `InstanceParity.olean` is all that is written and all `parse_load_module`
/// reads — compiled by the pinned Lean on first use, plus the independent
/// upstream oracle's two readings of it (`oracle/DumpOlean.lean`): raw mode over
/// the file (constants and extension rows) and env mode (`importModules` of the
/// module, then Lean's own `Meta.isInstanceCore` / `isClass` per constant). Both
/// oracle documents are read once per process; the module is re-parsed from the
/// cached bytes per test because tests mutate the environments they load it
/// into. Measured 2026-09-15 with the README recipe: 20 constants, 17
/// extensions / 83 rows, 4 decoded `instance`+`class` rows, env mode 20 rows +
/// 20 classes with 2 + 2 positive verdicts — figures the tests derive, quoted
/// so a drift can be recognised. Fails closed when the toolchain is absent.
fn fixture() -> (LoadModule, Value, Value) {
    static ORACLES: OnceLock<(Vec<u8>, Value, Value)> = OnceLock::new();
    let (bytes, raw, env) = ORACLES.get_or_init(|| {
        let dir = compiled_fixture_dir("instance_parity");
        let olean = dir.join("InstanceParity.olean");
        let bytes = std::fs::read(&olean).expect("pinned-Lean compiled InstanceParity.olean");
        let raw = run_oracle(&[olean.to_str().expect("utf-8 fixture path")]);
        let env = run_oracle(&[
            "--env",
            "InstanceParity",
            "--search-path",
            dir.to_str().expect("utf-8 fixture path"),
        ]);
        (bytes, raw, env)
    });
    let module = super::super::load_parse::parse_load_module(bytes.clone())
        .expect("pinned-Lean InstanceParity module");
    (module, raw.clone(), env.clone())
}

/// `(positive, total)` verdicts the env oracle must contain, derived from the
/// RAW oracle rather than typed: every decoded `Lean.Meta.instanceExtension` row
/// is a live instance and every decoded `Lean.classExtension` row a live class,
/// nothing else is either, and the total is the env probe's own size (`rows` +
/// `classes`). The lost original's `9 / 5 / 4` is unreachable under the oracle's
/// schema — `rows` and `classes` probe the same name list, so the total is
/// always even (family README, "Literals that do NOT hold").
fn expected_verdicts(raw: &Value, oracle: &Value) -> (usize, usize) {
    let positive = raw["parts"][0]["entries"]
        .as_array()
        .unwrap()
        .iter()
        .flat_map(|entry| entry["rows"].as_array().unwrap())
        .filter(|row| matches!(row["value"]["kind"].as_str(), Some("instance" | "class")))
        .count();
    let total =
        oracle["rows"].as_array().unwrap().len() + oracle["classes"].as_array().unwrap().len();
    assert!(
        positive > 0 && positive < total,
        "the fixture must carry both registrations and non-registrations ({positive} of {total})"
    );
    (positive, total)
}

fn name(value: &Value) -> Name {
    value
        .as_array()
        .unwrap()
        .iter()
        .fold(Name::anon(), |parent, part| {
            match part["kind"].as_str().unwrap() {
                "str" => parent.str(part["value"].as_str().unwrap()),
                "num" => parent.num(part["value"].as_u64().unwrap()),
                _ => panic!("unknown Name constructor"),
            }
        })
}

fn load(env: &mut Environment, module: &LoadModule, policy: OleanImportPolicy) -> LoadSummary {
    load_module_direct_with_cache_and_policy(
        env,
        module,
        Some("InstanceParity".into()),
        &mut ExprInternCache::with_capacity(128),
        policy,
    )
    .expect("direct metadata load in assumed environment")
}

fn assert_membership(env: &Environment, oracle: &Value, raw: &Value, selection: Option<bool>) {
    let (positive, total) = expected_verdicts(raw, oracle);
    let mut checked = 0;
    for (field, property) in [("rows", "is_instance"), ("classes", "is_class")] {
        for row in oracle[field].as_array().unwrap() {
            let expected = row[property].as_bool().unwrap();
            if selection.is_some_and(|selected| selected != expected) {
                continue;
            }
            let name = name(&row["name"]);
            assert!(row["constant_present"].as_bool().unwrap());
            assert!(env.get_const(&name).is_some(), "missing original {name:?}");
            let actual = if property == "is_instance" {
                env.is_instance(&name)
            } else {
                env.is_class(&name)
            };
            assert_eq!(actual, expected, "{property} for exact {name:?}");
            checked += 1;
        }
    }
    assert_eq!(
        checked,
        match selection {
            None => total,
            Some(true) => positive,
            Some(false) => total - positive,
        },
        "verdicts checked for selection {selection:?}"
    );
}

fn assert_priorities(env: &Environment, raw: &Value) {
    let entries = raw["parts"][0]["entries"].as_array().unwrap();
    let extension = entries
        .iter()
        .find(|entry| {
            name(&entry["name"])
                == Name::anon()
                    .str("Lean")
                    .str("Meta")
                    .str("instanceExtension")
        })
        .expect("original instance extension");
    for (instance, class, measured_priority) in [
        ("registered.dot", "Actual", 731),
        ("removed", "Removed", 1000),
    ] {
        let instance = Name::anon().str("InstanceParity").str(instance);
        let class = Name::anon().str("InstanceParity").str(class);
        let rows: Vec<_> = extension["rows"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|row| name(&row["value"]["name"]) == instance)
            .collect();
        assert_eq!(rows.len(), 1, "exact original instance row");
        let priority = u32::try_from(rows[0]["value"]["priority"].as_u64().unwrap()).unwrap();
        assert_eq!(
            priority, measured_priority,
            "unchanged upstream serialized priority"
        );
        let registered: Vec<_> = env
            .get_class_instances(&class)
            .iter()
            .filter(|info| info.name == instance)
            .collect();
        assert_eq!(registered.len(), 1, "no duplicate registered instance");
        assert_eq!(registered[0].priority, priority);
    }
}

/// The roster property is `module.constants.len() == expected.len()` against the
/// oracle's own duplicate-free name set; the lost original's whole-module census
/// (`54`) was a literal nothing can re-derive and is gone.
#[test]
fn raw_constant_and_extension_rosters_remain_complete() {
    let (module, raw, _) = fixture();
    let mut env = Environment::new();
    let summary = load(&mut env, &module, OleanImportPolicy::default());
    let parts = raw["parts"].as_array().unwrap();
    assert_eq!(parts.len(), 1);
    let constants = parts[0]["constants"].as_array().unwrap();
    let expected: BTreeSet<Name> = constants.iter().map(|row| name(&row["name"])).collect();
    assert_eq!(
        expected.len(),
        constants.len(),
        "no oracle identity duplicates"
    );
    assert!(!expected.is_empty(), "upstream module has constants");
    assert_eq!(module.constants.len(), expected.len());
    for name in expected {
        assert!(
            env.get_const(&name).is_some(),
            "missing raw constant {name:?}"
        );
    }
    assert_eq!(summary.added_constants, constants.len());
    assert!(summary.skipped_constants.is_empty());
    let entries = parts[0]["entries"].as_array().unwrap();
    assert_eq!(summary.extension_accounting.len(), entries.len());
    for (actual, source) in summary.extension_accounting.iter().zip(entries) {
        assert_eq!(actual.extension_name, name(&source["name"]));
        let count = usize::try_from(source["count"].as_u64().unwrap()).unwrap();
        assert_eq!(actual.source_rows, Some(count));
        assert_eq!(actual.decoded_rows + actual.undecoded_rows, count);
    }
    assert!(
        summary.extension_undecoded_entries > 0,
        "unknown rows stay visible"
    );
}

/// `instance (priority := 731) InstanceParity.«registered.dot» : Actual` and a
/// default-priority `InstanceParity.removed : Removed` are the fixture's two
/// instance rows; both priorities are read from the raw oracle by `assert_priorities`.
#[test]
fn explicit_classes_and_instances_match_upstream() {
    let (module, raw, oracle) = fixture();
    let mut env = Environment::new();
    load(&mut env, &module, OleanImportPolicy::default());
    assert_membership(&env, &oracle, &raw, Some(true));
    assert_priorities(&env, &raw);
}

#[test]
fn ordinary_values_and_plain_structure_are_not_registrations() {
    let (module, raw, oracle) = fixture();
    let mut env = Environment::new();
    load(&mut env, &module, OleanImportPolicy::default());
    assert_membership(&env, &oracle, &raw, Some(false));
}

#[test]
fn deferred_finalization_only_retries_explicit_metadata() {
    let (module, raw, oracle) = fixture();
    let mut env = Environment::new();
    load(
        &mut env,
        &module,
        OleanImportPolicy::default().with_deferred_global_instance_backfill(),
    );
    for _ in 0..3 {
        finalize_global_instance_backfill(&mut env);
        assert_membership(&env, &oracle, &raw, None);
        assert_priorities(&env, &raw);
    }
}

#[test]
fn repeated_import_does_not_invent_registrations() {
    let (module, raw, oracle) = fixture();
    let mut env = Environment::new();
    load(&mut env, &module, OleanImportPolicy::default());
    let instance = Name::anon().str("InstanceParity").str("registered.dot");
    assert_eq!(env.adopt_instance_priority(&instance, 13), Some(731));
    let repeated = load(&mut env, &module, OleanImportPolicy::default());
    assert_eq!(repeated.added_constants, 0);
    assert_membership(&env, &oracle, &raw, None);
    assert_priorities(&env, &raw);
}

#[test]
fn unrelated_preexisting_class_value_is_not_discovered_as_an_instance() {
    let (module, raw, oracle) = fixture();
    let mut env = Environment::new();
    load(&mut env, &module, OleanImportPolicy::default());
    let seeded = Name::anon().str("unattributed seed");
    env.extend_constants_unchecked(std::iter::once(ConstantInfo::new(
        seeded.clone(),
        vec![],
        Expr::const_(Name::anon().str("InstanceParity").str("Actual"), vec![]),
        Some(Expr::const_(
            Name::anon().str("InstanceParity").str("registered.dot"),
            vec![],
        )),
        true,
    )));
    assert!(!env.is_instance(&seeded));
    load(&mut env, &module, OleanImportPolicy::default());
    finalize_global_instance_backfill(&mut env);
    assert!(env.get_const(&seeded).is_some());
    assert!(
        !env.is_instance(&seeded),
        "metadata import must not inspect unrelated definitions for candidates"
    );
    assert_membership(&env, &oracle, &raw, None);
}
