// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Plan unit E2's meaning pins for the declarations of `theories/cic_l` that
//! are not theorems.
//!
//! `evidence.rs` pins every theorem target of `theories/cic_l` by its meaning
//! digest (`../support/meaning_digest.rs`). Every other target the fenced
//! reference replay admits (definition, opaque, axiom, inductive type,
//! constructor, recursor) is pinned here, in `definition_pins.json`, by the
//! same digest: keyed by `Name::to_unambiguous_string()`, each row binds the
//! origin module, the kind and the meaning digest, which holds the
//! declaration's own kernel record (universe parameters, type, value and the
//! unfolding flag and hint; the inductive, constructor and recursor tables)
//! and the record of every package constant it reaches, down to Init.
//! `evidence.rs` measures and compares both pin files before anything else
//! is checked, so one re-pin run (`CLEAN_REPIN_STATEMENT_PINS=1`) rewrites
//! both. Planted controls here verify that an unlisted target, a missing
//! target, a mutated definition body and a renamed universe parameter each
//! fail closed, and that the selection partitions into theorem and
//! non-theorem pins.

use std::collections::{BTreeMap, BTreeSet};

use clean_kernel::env::Environment;
use clean_kernel::{ConstantKind, Expr, Name};
use serde::{Deserialize, Serialize};

use super::evidence::meaning_digest::{MeaningDigests, Package};

const DEFINITION_PINS: &str = include_str!("definition_pins.json");

/// The committed pin file, relative to the workspace root.
pub(crate) const PIN_FILE: &str = "crates/clean-olean/tests/cic_l_level/definition_pins.json";
const LAKEFILE: &str = include_str!("../../../../theories/cic_l/lakefile.toml");

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct DefinitionPinRow {
    pub module: String,
    pub kind: String,
    pub meaning_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum DefinitionPinRefusal {
    LakefileOrder {
        lakefile_roots: Vec<String>,
        order_modules: Vec<String>,
    },
    Partition {
        uncovered: Vec<String>,
        overlap: Vec<String>,
    },
    Pins {
        unlisted: Vec<String>,
        missing: Vec<String>,
        changed: Vec<String>,
    },
}

pub(crate) fn parse_lakefile_roots(lakefile_toml: &str) -> Vec<String> {
    let parsed: toml::Value =
        toml::from_str(lakefile_toml).expect("parse theories/cic_l/lakefile.toml");
    let libs = parsed["lean_lib"]
        .as_array()
        .expect("lakefile.toml [[lean_lib]] array");
    assert_eq!(libs.len(), 1, "expected exactly one [[lean_lib]] in cic_l");
    libs[0]["roots"]
        .as_array()
        .expect("lean_lib.roots array")
        .iter()
        .map(|v| v.as_str().expect("string root").to_owned())
        .collect()
}

pub(crate) fn check_lakefile_roots_order(
    lakefile_roots: &[String],
    order_modules: &[String],
) -> Result<(), DefinitionPinRefusal> {
    if lakefile_roots == order_modules {
        Ok(())
    } else {
        Err(DefinitionPinRefusal::LakefileOrder {
            lakefile_roots: lakefile_roots.to_vec(),
            order_modules: order_modules.to_vec(),
        })
    }
}

pub(crate) fn non_theorem_kind(env: &Environment, subject: &Name) -> Option<String> {
    if let Some(constant) = env.get_const(subject) {
        if constant.kind == ConstantKind::Theorem {
            return None;
        }
        return Some(format!("{:?}", constant.kind));
    }
    if env.get_inductive(subject).is_some() {
        return Some("Inductive".to_owned());
    }
    if env.get_constructor(subject).is_some() {
        return Some("Constructor".to_owned());
    }
    if env.get_recursor(subject).is_some() {
        return Some("Recursor".to_owned());
    }
    panic!("replayable target {subject} missing from all admitted environment tables");
}

/// Unambiguous name → pin row, for every replayable non-theorem target of
/// `modules`, each digest taken by `digests` over `env`.
pub(crate) fn non_theorem_inventory(
    digests: &MeaningDigests<'_>,
    env: &Environment,
    modules: &BTreeMap<String, Vec<Name>>,
    not_replayable: &BTreeSet<String>,
) -> BTreeMap<String, DefinitionPinRow> {
    let mut out = BTreeMap::new();
    for (module, names) in modules {
        for subject in names {
            if not_replayable.contains(&subject.to_string()) {
                continue;
            }
            let Some(kind) = non_theorem_kind(env, subject) else {
                continue;
            };
            let key = subject.to_unambiguous_string();
            let row = DefinitionPinRow {
                module: module.clone(),
                kind,
                meaning_sha256: digests
                    .digest(subject)
                    .unwrap_or_else(|error| panic!("{error}")),
            };
            let prev = out.insert(key.clone(), row);
            assert!(
                prev.is_none(),
                "duplicate unambiguous non-theorem target identity: {key}"
            );
        }
    }
    out
}

pub(crate) fn check_target_partition(
    env: &Environment,
    modules: &BTreeMap<String, Vec<Name>>,
    not_replayable: &BTreeSet<String>,
    theorem_inventory: &BTreeMap<String, String>,
    non_theorems: &BTreeMap<String, DefinitionPinRow>,
) -> Result<(), DefinitionPinRefusal> {
    let mut uncovered = Vec::new();
    let mut overlap = Vec::new();
    for names in modules.values() {
        for subject in names {
            let display = subject.to_string();
            if not_replayable.contains(&display) {
                continue;
            }
            let unambiguous = subject.to_unambiguous_string();
            let in_thm = theorem_inventory.contains_key(&display)
                && env
                    .get_const(subject)
                    .is_some_and(|c| c.kind == ConstantKind::Theorem);
            let in_def = non_theorems.contains_key(&unambiguous);
            match (in_thm, in_def) {
                (true, false) | (false, true) => {}
                (false, false) => uncovered.push(unambiguous),
                (true, true) => overlap.push(unambiguous),
            }
        }
    }
    if uncovered.is_empty() && overlap.is_empty() {
        Ok(())
    } else {
        Err(DefinitionPinRefusal::Partition { uncovered, overlap })
    }
}

pub(crate) fn check_definition_pins(
    actual: &BTreeMap<String, DefinitionPinRow>,
    pins: &BTreeMap<String, DefinitionPinRow>,
) -> Result<(), DefinitionPinRefusal> {
    let unlisted: Vec<String> = actual
        .keys()
        .filter(|k| !pins.contains_key(*k))
        .cloned()
        .collect();
    let missing: Vec<String> = pins
        .keys()
        .filter(|k| !actual.contains_key(*k))
        .cloned()
        .collect();
    let changed: Vec<String> = actual
        .iter()
        .filter(|(k, row)| pins.get(*k).is_some_and(|pinned| pinned != *row))
        .map(|(k, _)| k.clone())
        .collect();
    if unlisted.is_empty() && missing.is_empty() && changed.is_empty() {
        Ok(())
    } else {
        Err(DefinitionPinRefusal::Pins {
            unlisted,
            missing,
            changed,
        })
    }
}

pub(crate) fn committed_pins() -> BTreeMap<String, DefinitionPinRow> {
    serde_json::from_str(DEFINITION_PINS)
        .expect("definition_pins.json maps unambiguous names to DefinitionPinRow")
}

/// The checks and planted controls of the non-theorem pins over the
/// measured rows `actual`, which `evidence.rs` has already compared with the
/// committed file.
pub(crate) fn verify_and_run_controls(
    admitted: &Environment,
    modules: &BTreeMap<String, Vec<Name>>,
    not_replayable: &BTreeSet<String>,
    theorem_inventory: &BTreeMap<String, String>,
    actual: &BTreeMap<String, DefinitionPinRow>,
) {
    let order_modules = super::evidence::order_modules();
    let lakefile_roots = parse_lakefile_roots(LAKEFILE);
    check_lakefile_roots_order(&lakefile_roots, &order_modules)
        .expect("theories/cic_l/lakefile.toml roots must equal ORDER in exact sequence");
    let mut swapped_roots = lakefile_roots.clone();
    assert!(swapped_roots.len() >= 2, "cic_l has multiple roots");
    swapped_roots.swap(0, 1);
    assert!(
        matches!(
            check_lakefile_roots_order(&swapped_roots, &order_modules),
            Err(DefinitionPinRefusal::LakefileOrder { .. })
        ),
        "out-of-order lakefile roots must fail closed"
    );

    assert!(
        !actual.is_empty(),
        "CIC_L non-theorem definition inventory cannot be empty"
    );
    check_target_partition(admitted, modules, not_replayable, theorem_inventory, actual)
        .expect("every replayable CIC_L target is pinned as either a theorem or a non-theorem");
    let pins = committed_pins();
    check_definition_pins(actual, &pins)
        .expect("evidence.rs compared the measured non-theorem pins first");

    // Planted controls:
    // 1. Partition control: dropping a non-theorem row leaves its target uncovered.
    let sample_key = "CICL.CoreJudgmentIn".to_owned();
    assert!(
        actual.contains_key(&sample_key),
        "CICL.CoreJudgmentIn must be a pinned non-theorem target"
    );
    let mut dropped_actual = actual.clone();
    dropped_actual.remove(&sample_key);
    assert_eq!(
        check_target_partition(
            admitted,
            modules,
            not_replayable,
            theorem_inventory,
            &dropped_actual
        ),
        Err(DefinitionPinRefusal::Partition {
            uncovered: vec![sample_key.clone()],
            overlap: vec![],
        }),
        "dropping a non-theorem pin must fail partition check"
    );

    // 2. Pin-set controls: unlisted, missing, and mutated meaning/kind/module.
    assert_eq!(
        check_definition_pins(actual, &dropped_actual),
        Err(DefinitionPinRefusal::Pins {
            unlisted: vec![sample_key.clone()],
            missing: vec![],
            changed: vec![],
        }),
        "an unpinned non-theorem target must fail as unlisted"
    );
    assert_eq!(
        check_definition_pins(&dropped_actual, &pins),
        Err(DefinitionPinRefusal::Pins {
            unlisted: vec![],
            missing: vec![sample_key.clone()],
            changed: vec![],
        }),
        "a missing non-theorem target must fail as missing"
    );

    // 3. Kernel-meaning sensitivity controls on real declarations:
    //    mutating a definition body or renaming a universe parameter in a
    //    scratch environment must change the meaning digest and fail
    //    `check_definition_pins`.
    let def_name = Name::from_string("CICL.BaseFamilies.Eq.type");
    let def_key = def_name.to_unambiguous_string();
    assert!(
        actual.contains_key(&def_key),
        "CICL.BaseFamilies.Eq.type must be pinned"
    );
    let orig_def = admitted.get_const(&def_name).expect("Eq.type constant");
    let mut body_mut_env = Environment::new();
    body_mut_env
        .add_decl(clean_kernel::env::Declaration::Definition {
            name: def_name.clone(),
            level_params: vec![Name::from_string("u_mut")],
            type_: Expr::sort(clean_kernel::Level::succ(clean_kernel::Level::zero())),
            value: Expr::prop(),
            is_reducible: orig_def.is_reducible,
        })
        .expect("scratch definition");
    let mut level_mut_env = Environment::new();
    level_mut_env
        .add_decl(clean_kernel::env::Declaration::Definition {
            name: def_name.clone(),
            level_params: vec![Name::from_string("v_mut")],
            type_: Expr::sort(clean_kernel::Level::succ(clean_kernel::Level::zero())),
            value: Expr::prop(),
            is_reducible: orig_def.is_reducible,
        })
        .expect("scratch definition with renamed level_param");
    let mut val_mut_env = Environment::new();
    val_mut_env
        .add_decl(clean_kernel::env::Declaration::Definition {
            name: def_name.clone(),
            level_params: vec![Name::from_string("u_mut")],
            type_: Expr::sort(clean_kernel::Level::succ(clean_kernel::Level::zero())),
            value: Expr::pi(
                clean_kernel::BinderInfo::Default,
                Expr::prop(),
                Expr::prop(),
            ),
            is_reducible: orig_def.is_reducible,
        })
        .expect("scratch definition with altered body and identical type/levels");
    let scratch = Package::of_names(BTreeSet::from([def_name.clone()]));
    let digest_in = |env: &Environment| {
        MeaningDigests::new(env, &scratch)
            .digest(&def_name)
            .unwrap_or_else(|error| panic!("{error}"))
    };
    let base_digest = digest_in(&body_mut_env);
    let level_digest = digest_in(&level_mut_env);
    let val_digest = digest_in(&val_mut_env);
    assert_ne!(
        base_digest, level_digest,
        "renaming level_params must move the meaning digest"
    );
    assert_ne!(
        base_digest, val_digest,
        "changing a definition body while keeping type and level_params fixed must move the meaning digest"
    );
    let mut mutated_actual = actual.clone();
    mutated_actual.get_mut(&def_key).unwrap().meaning_sha256 = val_digest;
    assert_eq!(
        check_definition_pins(&mutated_actual, &pins),
        Err(DefinitionPinRefusal::Pins {
            unlisted: vec![],
            missing: vec![],
            changed: vec![def_key],
        }),
        "a mutated definition meaning digest must fail as changed"
    );

    eprintln!(
        "E2 definition pins: {} non-theorem CIC_L targets pinned by unambiguous name, \
         origin module, kind and meaning digest; partition + unlisted/missing/body/level_params \
         controls passed",
        actual.len()
    );
}
