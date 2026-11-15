// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Plan unit E2 meaning-pinning follow-up for `theories/cic_l`:
//!
//! `evidence.rs` pins `(level_params, type_)` for every `ConstantKind::Theorem`
//! among the replayable targets of `theories/cic_l`, and explicitly notes that a
//! theorem statement pin alone does not bind the definitions or inductive
//! families that statement mentions.
//!
//! This module closes that gap on `theories/cic_l` without altering the
//! gate-pinned `evidence.rs` file: every non-theorem target admitted by the
//! fenced reference replay (`Definition`, `Inductive`, `Constructor`,
//! `Recursor`, `Opaque`, `Axiom`, `Quot`) has its full kernel meaning pinned in
//! `definition_pins.json` — keyed by `Name::to_unambiguous_string()`, binding
//! origin module, `ConstantKind`, `level_params`, `type_`, `value`,
//! `is_reducible`, and any `InductiveVal`, `ConstructorVal`, or `RecursorVal`
//! table entry. Planted controls verify that an unlisted target, a missing
//! target, a mutated definition body, a mutated universe parameter list, or a
//! mutated inductive/constructor/recursor table entry each fails closed.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use clean_kernel::env::Environment;
use clean_kernel::{ConstantKind, Expr, Name};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const DEFINITION_PINS: &str = include_str!("definition_pins.json");
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

fn hex_sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
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

pub(crate) fn meaning_digest(env: &Environment, subject: &Name) -> String {
    let const_part = env.get_const(subject).map(|constant| {
        let level_params: Vec<String> = constant
            .level_params
            .iter()
            .map(Name::to_unambiguous_string)
            .collect();
        (
            format!("{:?}", constant.kind),
            level_params,
            constant.is_reducible,
            &constant.type_,
            &constant.value,
        )
    });
    let ind_part = env.get_inductive(subject);
    let ctor_part = env.get_constructor(subject);
    let rec_part = env.get_recursor(subject);
    assert!(
        const_part.is_some() || ind_part.is_some() || ctor_part.is_some() || rec_part.is_some(),
        "non-theorem target {subject} must reside in at least one kernel table"
    );
    let payload = (const_part, ind_part, ctor_part, rec_part);
    let bytes = bincode::serde::encode_to_vec(&payload, bincode::config::standard())
        .expect("serialize non-theorem declaration meaning");
    hex_sha256(&bytes)
}

pub(crate) fn non_theorem_inventory(
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
                meaning_sha256: meaning_digest(env, subject),
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

fn write_measured_pins(actual: &BTreeMap<String, DefinitionPinRow>) -> String {
    let path = Path::new(env!("CARGO_TARGET_TMPDIR")).join("cic_l_level_definition_pins.json");
    let json = serde_json::to_string_pretty(actual).expect("serialize definition pins") + "\n";
    std::fs::write(&path, json).expect("write measured definition pins");
    path.display().to_string()
}

pub(crate) fn verify_and_run_controls(
    admitted: &Environment,
    compiled: &Path,
    modules: &BTreeMap<String, Vec<Name>>,
    theorem_inventory: &BTreeMap<String, String>,
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

    let not_replayable = super::evidence::stored_not_replayable(compiled, modules.keys());
    let actual = non_theorem_inventory(admitted, modules, &not_replayable);
    assert!(
        !actual.is_empty(),
        "CIC_L non-theorem definition inventory cannot be empty"
    );
    check_target_partition(
        admitted,
        modules,
        &not_replayable,
        theorem_inventory,
        &actual,
    )
    .expect("every replayable CIC_L target is pinned as either a theorem or a non-theorem");
    let pins = committed_pins();
    if let Err(refusal) = check_definition_pins(&actual, &pins) {
        let measured = write_measured_pins(&actual);
        panic!(
            "CIC_L non-theorem definition/inductive meaning pins failed: {refusal:?}\n\
             measured pins written to {measured}"
        );
    }

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
            &not_replayable,
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
        check_definition_pins(&actual, &dropped_actual),
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
    //    mutating a definition body, mutating `level_params`, or mutating an
    //    inductive's constructor list in a scratch environment must change
    //    `meaning_digest` and fail `check_definition_pins`.
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
    let base_digest = meaning_digest(&body_mut_env, &def_name);
    let level_digest = meaning_digest(&level_mut_env, &def_name);
    let val_digest = meaning_digest(&val_mut_env, &def_name);
    assert_ne!(
        base_digest, level_digest,
        "renaming level_params must move meaning_digest"
    );
    assert_ne!(
        base_digest, val_digest,
        "changing a definition body while keeping type and level_params fixed must move meaning_digest"
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
         origin module, kind, level_params, type, value and inductive/constructor/recursor \
         tables; partition + unlisted/missing/body/level_params controls passed",
        actual.len()
    );
}
