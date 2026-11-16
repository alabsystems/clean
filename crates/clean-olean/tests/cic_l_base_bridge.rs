// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Primitive model / labelled checker-base bridge. Every own-module declaration
//! is replayed from compiled bytes by pinned Lean and the fenced reference
//! entry. Every theorem has an actual positive/False pair, four headlines have
//! independent schemas, and four scope-strengthening statements are refused.
//! No native compiler, whole M4 or checker soundness claim follows.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::process::Command;

use clean_kernel::env::{ConstantInfo, ConstantKind, Declaration, Environment};
use clean_kernel::{Expr, KernelEnvError, KernelTypeError, Name, ReferenceRefusal};
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::{
    load_module_with_deps, read_artifact, reference_base_closed, require_pinned_lean_lib_path,
    ArtifactDepth,
};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

const ROOT: &str = "CICLBaseBridge";
const CONTRACTS: &[(&str, &str)] = &[
    (
        "CICLBaseBridge.primitive_assignment_std_related",
        "primitiveAssignmentRelated",
    ),
    (
        "CICLBaseBridge.primitive_eval_std_equal",
        "primitiveEvaluationEqual",
    ),
    (
        "CICLBaseBridge.punit_eval_std_equal",
        "punitEvaluationEqual",
    ),
    (
        "CICLBaseBridge.primitive_comparison_inhabited",
        "comparisonInhabited",
    ),
];
const FORGED: &[(&str, &str)] = &[
    (
        "CICLBaseBridge.primitive_eval_std_equal",
        "forgedEvaluationWithoutSorts",
    ),
    (
        "CICLBaseBridge.primitive_eval_std_equal",
        "forgedEvaluationAnyName",
    ),
    (
        "CICLBaseBridge.primitive_eval_std_equal",
        "forgedRawEquality",
    ),
    (
        "CICLBaseBridge.primitive_assignment_std_related",
        "forgedAssignmentAllNames",
    ),
];

fn name(text: &str) -> Name {
    Name::from_string(text)
}

fn digest<T: serde::Serialize>(value: &T) -> String {
    let bytes = bincode::serde::encode_to_vec(value, bincode::config::standard())
        .expect("serialize structural pin");
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn modules(directory: &Path, root: &Path, found: &mut BTreeSet<String>) {
    for entry in std::fs::read_dir(directory).expect("read bridge source directory") {
        let entry = entry.expect("source entry");
        let path = entry.path();
        if path.is_dir() {
            if entry.file_name() != ".lake" {
                modules(&path, root, found);
            }
        } else if path
            .extension()
            .is_some_and(|extension| extension == "lean")
        {
            let stem = path
                .strip_prefix(root)
                .expect("package path")
                .with_extension("");
            assert!(found.insert(
                stem.to_string_lossy()
                    .replace(std::path::MAIN_SEPARATOR, ".")
            ));
        }
    }
}

fn mismatch<T>(result: &Result<T, ReferenceRefusal>) -> bool {
    matches!(
        result,
        Err(ReferenceRefusal::Kernel(KernelEnvError::TypeCheckFailed {
            source: KernelTypeError::TypeMismatch { .. },
            ..
        }))
    )
}

#[test]
fn bridge_replays_with_exact_scope_and_real_negative_controls() {
    let lib = require_pinned_lean_lib_path().expect("install pinned Lean");
    let compiled = compiled_fixture_dir("cic_l_base_bridge");
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean binary");
    let bin = lean.parent().expect("pinned Lean bin");
    let mut binary_paths = vec![bin.to_path_buf()];
    binary_paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));
    let binary_path = std::env::join_paths(binary_paths).expect("pinned reference binary path");
    let independent = Command::new(lean.parent().expect("Lean bin").join("leanchecker"))
        .args(["--fresh", ROOT])
        .env("PATH", &binary_path)
        .current_dir(&compiled)
        .env(
            "LEAN_PATH",
            std::env::join_paths([&compiled, &lib]).expect("Lean path"),
        )
        .output()
        .expect("run independent pinned Lean kernel");
    assert!(
        independent.status.success(),
        "leanchecker failed: {}\n{}",
        String::from_utf8_lossy(&independent.stdout),
        String::from_utf8_lossy(&independent.stderr)
    );

    let declared: Vec<String> = include_str!("../../../theories/cic_l_base_bridge/ORDER")
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(|stem| stem.replace('/', "."))
        .collect();
    let declared_set: BTreeSet<String> =
        declared.iter().map(|module| (*module).to_owned()).collect();
    assert_eq!(declared.len(), declared_set.len(), "duplicate ORDER module");
    let package = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../theories/cic_l_base_bridge");
    let mut source_modules = BTreeSet::new();
    modules(&package, &package, &mut source_modules);
    assert_eq!(
        declared_set, source_modules,
        "own source module census changed"
    );
    assert_eq!(declared.len(), 7, "review own-module denominator");

    let mut loaded = Environment::for_lean_replay();
    let summaries = load_module_with_deps(&mut loaded, ROOT, &[compiled.clone(), lib])
        .expect("load bridge and its dependency closure");
    let skipped: BTreeSet<&str> = summaries
        .iter()
        .flat_map(|summary| summary.skipped_not_replayable.iter().map(String::as_str))
        .collect();
    let mut targets = BTreeSet::new();
    let mut compiler_copies = BTreeSet::new();
    for module in &declared {
        let stem = module.replace('.', "/");
        let artifact = read_artifact(
            module,
            &compiled.join(format!("{stem}.olean")),
            ArtifactDepth::Names,
        )
        .unwrap_or_else(|error| panic!("read {module}: {error}"));
        assert!(
            !artifact.names.is_empty() || module.as_str() == ROOT,
            "only the import-only aggregate may be empty"
        );
        for subject in artifact.names {
            if loaded.get_const(&subject).is_none() {
                let text = subject.to_string();
                assert!(
                    text.ends_with("._unsafe_rec") && skipped.contains(text.as_str()),
                    "{module}: missing resident declaration {subject}"
                );
                assert!(compiler_copies.insert(text));
                continue;
            }
            assert!(
                !loaded.is_unsafe(&subject) && !loaded.is_partial(&subject),
                "unsafe subject {subject}"
            );
            assert!(
                targets.insert(subject.clone()),
                "duplicate module owner for {subject}"
            );
        }
    }
    for copy in &compiler_copies {
        assert!(targets.contains(&name(
            copy.strip_suffix("._unsafe_rec").expect("copy suffix")
        )));
    }
    assert_eq!(targets.len(), 58, "review bridge subject denominator");
    let authored: Vec<String> = serde_json::from_str(include_str!(
        "../../../theories/cic_l_base_bridge/authored_theorems.json"
    ))
    .expect("explicit authored theorem roster");
    assert_eq!(authored.len(), 28, "review authored theorem denominator");
    let authored_set: BTreeSet<_> = authored.iter().collect();
    assert_eq!(
        authored_set.len(),
        authored.len(),
        "duplicate authored theorem"
    );
    for theorem in &authored {
        let subject = name(theorem);
        assert!(
            targets.contains(&subject),
            "missing authored theorem {theorem}"
        );
        assert_eq!(
            loaded
                .get_const(&subject)
                .expect("resident authored theorem")
                .kind,
            ConstantKind::Theorem,
            "authored subject is not a theorem: {theorem}"
        );
    }
    let checked = reference_base_closed(&loaded, &targets, &ClosedRecheckOptions::default())
        .expect("construct dependency-closed fenced replay");
    assert!(
        checked.report.passed() && checked.entry_refusals.is_empty(),
        "{}\n{:?}",
        checked.report.verdict_sentence(),
        checked.entry_refusals
    );
    let mut kernel = checked.into_kernel().expect("reference admissions passed");

    let allowed: BTreeSet<String> = [
        "propext",
        "Quot.sound",
        "Quot",
        "Quot.mk",
        "Quot.lift",
        "Quot.ind",
    ]
    .into_iter()
    .map(str::to_owned)
    .collect();
    let mut inventory = BTreeMap::<String, Value>::new();
    let mut theorem_count = 0;
    for subject in &targets {
        let info: &ConstantInfo = loaded.get_const(subject).expect("resident subject");
        let mut closure = kernel
            .environment()
            .axiom_deps(subject)
            .expect("axiom closure");
        closure.extend(
            kernel
                .environment()
                .foundational_axiom_deps(subject)
                .expect("foundational closure"),
        );
        let closure: BTreeSet<String> = closure.iter().map(ToString::to_string).collect();
        assert!(closure.is_subset(&allowed), "{subject}: {closure:?}");
        assert!(inventory.insert(subject.to_string(), json!({
            "constant_sha256": digest(info), "kind": format!("{:?}", info.kind),
            "level_params": info.level_params.iter().map(ToString::to_string).collect::<Vec<_>>(),
            "axiom_closure": closure,
        })).is_none(), "ambiguous printed declaration name {subject}");
        if info.kind == ConstantKind::Theorem {
            let value = info.value.clone().expect("actual theorem proof");
            kernel
                .add_checked(Declaration::Theorem {
                    name: name(&format!("CICLBaseBridge.Controls.positive_{theorem_count}")),
                    level_params: info.level_params.clone(),
                    type_: info.type_.clone(),
                    value: value.clone(),
                })
                .unwrap_or_else(|error| panic!("{subject} positive: {error:?}"));
            let bad = kernel.add_checked(Declaration::Theorem {
                name: name(&format!("CICLBaseBridge.Controls.false_{theorem_count}")),
                level_params: info.level_params.clone(),
                type_: Expr::const_(name("False"), vec![]),
                value,
            });
            assert!(mismatch(&bad), "{subject} at False: {bad:?}");
            theorem_count += 1;
        }
    }
    assert_eq!(theorem_count, 40, "review complete theorem denominator");
    let statement = |pin: &str| {
        loaded
            .get_const(&name(&format!("CICLBaseBridge.Contracts.{pin}")))
            .unwrap_or_else(|| panic!("missing schema {pin}"))
            .value
            .clone()
            .expect("schema definition")
    };
    let mut pins = BTreeMap::new();
    for (_, pin) in CONTRACTS.iter().chain(FORGED) {
        assert!(pins
            .insert((*pin).to_owned(), digest(&statement(pin)))
            .is_none());
    }
    for (index, (theorem, pin)) in CONTRACTS.iter().enumerate() {
        let proof = loaded.get_const(&name(theorem)).expect("headline theorem");
        assert!(targets.contains(&name(theorem)));
        kernel
            .add_checked(Declaration::Theorem {
                name: name(&format!("CICLBaseBridge.Controls.contract_{index}")),
                level_params: proof.level_params.clone(),
                type_: statement(pin),
                value: proof.value.clone().expect("headline proof"),
            })
            .unwrap_or_else(|error| panic!("{theorem} at {pin}: {error:?}"));
    }
    for (index, (theorem, pin)) in FORGED.iter().enumerate() {
        let proof = loaded
            .get_const(&name(theorem))
            .expect("real proof for forged control");
        let bad = kernel.add_checked(Declaration::Theorem {
            name: name(&format!("CICLBaseBridge.Controls.forged_{index}")),
            level_params: proof.level_params.clone(),
            type_: statement(pin),
            value: proof.value.clone().expect("actual proof"),
        });
        assert!(mismatch(&bad), "{theorem} at forged {pin}: {bad:?}");
    }
    eprintln!(
        "bridge-inventory {}",
        serde_json::to_string(&inventory).expect("inventory JSON")
    );
    eprintln!(
        "bridge-pins {}",
        serde_json::to_string(&pins).expect("pin JSON")
    );
    eprintln!(
        "bridge-replay subjects={} theorems={} modules=7 contracts=4 forged=4 compiler_copies={}",
        targets.len(),
        theorem_count,
        compiler_copies.len()
    );
    let committed_inventory: BTreeMap<String, Value> = serde_json::from_str(include_str!(
        "../../../theories/cic_l_base_bridge/native_inventory.json"
    ))
    .expect("committed exact native inventory");
    let committed_pins: BTreeMap<String, String> = serde_json::from_str(include_str!(
        "../../../theories/cic_l_base_bridge/statement_pins.json"
    ))
    .expect("committed statement pins");
    assert_eq!(
        inventory, committed_inventory,
        "bridge declaration/axiom inventory changed"
    );
    assert_eq!(pins, committed_pins, "bridge contract statements changed");
}
