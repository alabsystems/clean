// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0

//! Untrusted actual-environment capture, never an authority or pin writer.
//! The identical test is compiled at each selected old/new source revision.

#[path = "mixed_world_pin_capture_dag.rs"]
mod dag;
#[path = "mixed_world_pin_capture_records.rs"]
mod records;

use super::{Annotations, Fingerprinter};
use crate::recheck_closed::extension_binding::{encode_hex, EXTENSION_KEYS};
use crate::recheck_closed::extension_binding_pins::PINNED_WORLDS;
use clean_kernel::env::{ConstantKind, Environment};
use clean_kernel::expr::Expr;
use clean_kernel::name::Name;
use dag::Tables;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fs::OpenOptions;
use std::io::Write;

const KEY_MODULES: &[&str] = &[
    "Init.Prelude",
    "Init.Core",
    "Init.Tactics",
    "Init.Data.Int.Basic",
    "Init.Data.Nat.Bitwise.Basic",
    "Init.Data.Nat.Gcd",
];

fn declares(env: &Environment, name: &Name) -> bool {
    env.get_const(name).is_some()
        || env.get_inductive(name).is_some()
        || env.get_constructor(name).is_some()
        || env.get_recursor(name).is_some()
}

fn term_field<'a>(
    fp: &mut Fingerprinter<'a>,
    tables: &mut Tables,
    field: String,
    expr: &'a Expr,
    mode: Annotations,
    refs: &mut BTreeSet<Name>,
    fields: &mut Vec<Value>,
) {
    let digest = fp.expr(expr, refs, mode);
    fields.push(json!({"field":field,"expr":tables.expr(expr),
        "annotations":if mode == Annotations::Kept {"kept"} else {"erased"},
        "digest":encode_hex(&digest)}));
}

fn unit<'a>(
    env: &'a Environment,
    head: &Name,
    fp: &mut Fingerprinter<'a>,
    tables: &mut Tables,
) -> (Value, Vec<Name>) {
    let mut names = BTreeSet::from([head.clone()]);
    let mut own = BTreeSet::new();
    let mut refs = BTreeSet::new();
    let mut fields = Vec::new();
    let (kind, header) = if let Some(ind) = env.get_inductive(head) {
        let members = if ind.all_names.is_empty() {
            vec![ind.name.clone()]
        } else {
            ind.all_names.clone()
        };
        for member in &members {
            own.insert(member.clone());
            names.insert(member.clone());
            let i = env.get_inductive(member).expect("complete family member");
            term_field(
                fp,
                tables,
                format!("{}.type_", member.to_unambiguous_string()),
                &i.type_,
                Annotations::Kept,
                &mut refs,
                &mut fields,
            );
            for ctor in &i.constructor_names {
                own.insert(ctor.clone());
                names.insert(ctor.clone());
                let c = env.get_constructor(ctor).expect("complete constructor");
                term_field(
                    fp,
                    tables,
                    format!("{}.type_", ctor.to_unambiguous_string()),
                    &c.type_,
                    Annotations::Kept,
                    &mut refs,
                    &mut fields,
                );
            }
        }
        for rec in env
            .recursors()
            .filter(|r| members.contains(&r.inductive_name))
        {
            names.insert(rec.name.clone());
        }
        let member_headers: Vec<_> = members.iter().map(|name| {
            let i = env.get_inductive(name).expect("complete family");
            json!({"name":tables.name(name),"constructor_names":tables.names(&i.constructor_names)})
        }).collect();
        (
            "family",
            json!({"level_params":tables.names(&ind.level_params),
            "num_params":ind.num_params,"members":member_headers}),
        )
    } else if let Some(c) = env.get_const(head) {
        term_field(
            fp,
            tables,
            "type_".into(),
            &c.type_,
            Annotations::Erased,
            &mut refs,
            &mut fields,
        );
        let hashes_value = matches!(c.kind, ConstantKind::Definition | ConstantKind::Opaque);
        if let Some(value) = c.value.as_ref().filter(|_| hashes_value) {
            term_field(
                fp,
                tables,
                "value".into(),
                value,
                Annotations::Erased,
                &mut refs,
                &mut fields,
            );
        }
        refs.remove(head);
        (
            "ordinary",
            json!({"name":tables.name(head),"kind":c.kind,
            "level_params":tables.names(&c.level_params),"value_is_fingerprinted":hashes_value && c.value.is_some()}),
        )
    } else {
        ("absent", json!({"name":tables.name(head)}))
    };
    let mut edges = Vec::new();
    let mut next = Vec::new();
    for reference in refs.into_iter().filter(|name| !own.contains(name)) {
        let target = fp
            .family_head(&reference)
            .unwrap_or_else(|| reference.clone());
        let digest = fp.constant(&reference);
        edges.push(json!({"reference":tables.name(&reference),
            "reference_name":reference.to_unambiguous_string(),"unit":target.to_unambiguous_string(),
            "fingerprint":encode_hex(&digest)}));
        next.push(target);
    }
    let fingerprint = fp.constant(head);
    (
        json!({"head":tables.name(head),"kind":kind,"fingerprint":encode_hex(&fingerprint),
        "fingerprint_header":header,"fingerprint_fields":fields,
        "fields":records::selected(env, &names, tables),"edges":edges}),
        next,
    )
}

fn reachability(root: &str, units: &BTreeMap<String, Value>) -> Vec<String> {
    let mut pending = vec![root.to_owned()];
    let mut seen = BTreeSet::new();
    while let Some(name) = pending.pop() {
        if !seen.insert(name.clone()) {
            continue;
        }
        let unit = units.get(&name).expect("every graph unit emitted");
        for edge in unit["edges"].as_array().expect("edge array") {
            let target = edge["unit"].as_str().expect("edge unit");
            assert_eq!(
                edge["fingerprint"], units[target]["fingerprint"],
                "edge digest differs from captured target"
            );
            pending.push(target.to_owned());
        }
    }
    seen.into_iter().collect()
}

#[test]
fn capture_actual_mixed_world() {
    for forbidden in [
        "CLEAN_NATIVE_FOLD_REPIN",
        "CLEAN_NATIVE_FOLD_BOOTSTRAP_LOAD",
    ] {
        assert!(
            std::env::var_os(forbidden).is_none(),
            "capture cannot repin/bootstrap: {forbidden}"
        );
    }
    assert_eq!(
        include_str!("../../../../lean-toolchain").trim(),
        "leanprover/lean4:v4.30.0-rc2"
    );
    let lib = crate::require_pinned_lean_lib_path().expect("actual repository-pinned Lean library");
    let base = Environment::try_with_prelude_for_import().expect("actual import prelude");
    let mut tables = Tables::default();
    // Capture before importing; the original base stays alive and immutable.
    let base_records = records::base(&base, &mut tables);
    let mut env = base.clone();
    let mut visited = hashbrown::HashSet::new();
    for module in KEY_MODULES {
        crate::load_module_with_deps_shared(
            &mut env,
            module,
            std::slice::from_ref(&lib),
            &mut visited,
        )
        .unwrap_or_else(|e| panic!("actual pinned import {module} failed: {e}"));
    }
    let roots: Vec<Name> = EXTENSION_KEYS
        .iter()
        .map(|k| Name::from_string(k.name))
        .filter(|name| declares(&env, name) && !declares(&base, name))
        .collect();
    assert_eq!(
        roots.len(),
        27,
        "actual mixed world must have exactly 27 imported keys"
    );
    assert_eq!(
        roots.iter().collect::<BTreeSet<_>>().len(),
        27,
        "duplicate root"
    );
    let mut expected_worlds = BTreeMap::new();
    for world in PINNED_WORLDS {
        let rows: BTreeMap<_, _> = world
            .rows
            .iter()
            .map(|(n, h)| ((*n).to_owned(), (*h).to_owned()))
            .collect();
        assert_eq!(rows.len(), world.rows.len(), "duplicate expected pin");
        assert!(expected_worlds
            .insert(world.label.to_owned(), rows)
            .is_none());
    }
    assert_eq!(expected_worlds.len(), 4, "unexpected reviewed world");
    assert_eq!(EXTENSION_KEYS.len(), 41, "unexpected extension-key census");
    for (label, count) in [
        ("lean-v4.8.0-core", 40),
        ("lean-v4.30.0-rc2-core", 41),
        ("clean-import+lean-v4.30.0-rc2-core", 27),
        ("lean-v4.35.0-literals-div-mod", 5),
    ] {
        assert_eq!(
            expected_worlds
                .get(label)
                .expect("every expected world")
                .len(),
            count
        );
    }
    let actual_root_names: BTreeSet<_> = roots.iter().map(Name::to_unambiguous_string).collect();
    assert_eq!(
        actual_root_names,
        expected_worlds["clean-import+lean-v4.30.0-rc2-core"]
            .keys()
            .cloned()
            .collect()
    );
    let mut fp = Fingerprinter::new(&env);
    let mut pending: BTreeSet<_> = roots
        .iter()
        .map(|n| fp.family_head(n).unwrap_or_else(|| n.clone()))
        .collect();
    let mut units = BTreeMap::new();
    while let Some(head) = pending.pop_first() {
        let key = head.to_unambiguous_string();
        if units.contains_key(&key) {
            continue;
        }
        let (record, dependencies) = unit(&env, &head, &mut fp, &mut tables);
        assert!(units.insert(key, record).is_none());
        pending.extend(
            dependencies
                .into_iter()
                .filter(|n| !units.contains_key(&n.to_unambiguous_string())),
        );
    }
    let mut root_records = BTreeMap::new();
    let mut minted = BTreeMap::new();
    let mut all_reachable = BTreeSet::new();
    for name in &roots {
        let digest = fp.constant(name);
        assert_eq!(
            digest,
            Fingerprinter::new(&env).constant(name),
            "query-order drift"
        );
        let head = fp.family_head(name).unwrap_or_else(|| name.clone());
        let head = head.to_unambiguous_string();
        let reachable = reachability(&head, &units);
        all_reachable.extend(reachable.iter().cloned());
        let key = name.to_unambiguous_string();
        assert!(minted.insert(key.clone(), encode_hex(&digest)).is_none());
        assert!(root_records
            .insert(
                key,
                json!({"name":tables.name(name),"unit":head,
            "fingerprint":encode_hex(&digest),"reachable_units":reachable})
            )
            .is_none());
    }
    assert_eq!(
        all_reachable,
        units.keys().cloned().collect(),
        "unreachable or missing unit"
    );
    let absent: Vec<_> = units
        .iter()
        .filter(|(_, unit)| unit["kind"] == "absent")
        .map(|(name, _)| name.clone())
        .collect();
    assert!(
        absent.is_empty(),
        "capture requires actual records for every reachable unit: {absent:?}"
    );
    let mut loaded_modules: Vec<_> = visited.into_iter().collect();
    loaded_modules.sort();
    let document = json!({"schema":"clean-mixed-world-pin-capture/v1",
        "lean_toolchain":"leanprover/lean4:v4.30.0-rc2", "lean_library":lib,
        "modules":KEY_MODULES, "loaded_modules":loaded_modules,
        "extension_keys":EXTENSION_KEYS.iter().map(|k| k.name).collect::<Vec<_>>(),
        "extension_hooks":EXTENSION_KEYS.iter().map(|k| (k.name,k.hook)).collect::<BTreeMap<_,_>>(),
        "minted":minted,"expected_worlds":expected_worlds,"roots":root_records,
        "base":base_records,"units":units,"tables":tables.finish(),
        "authority":false,"source_revision_supplied_by_outer_bookends":true});
    let bytes = serde_json::to_vec_pretty(&document).expect("encode complete capture");
    let private = tempfile::tempdir().expect("private capture directory");
    let output = std::env::var_os("MIXED_WORLD_CAPTURE_OUT")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| private.path().join("capture.json"));
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&output)
        .expect("new capture output only");
    file.write_all(&bytes).expect("write complete capture");
    file.sync_all().expect("retain complete capture");
    let restored: Value =
        serde_json::from_slice(&std::fs::read(&output).expect("reread actual capture"))
            .expect("read capture JSON");
    assert_eq!(restored, document, "capture transport changed data");
    let capture_sha256 = Sha256::digest(&bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    println!(
        "MIXED_WORLD_CAPTURE roots=27 units={} bytes={} sha256={} output={}",
        document["units"].as_object().expect("unit object").len(),
        bytes.len(),
        capture_sha256,
        output.display()
    );
}
