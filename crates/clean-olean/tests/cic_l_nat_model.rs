// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Canonical Nat semantics and bounded admission. Every selected declaration
//! is replayed from compiled bytes by pinned Lean and the fenced reference
//! entry. Every theorem has an actual positive/False pair, nine headlines have
//! independent schemas, and nine forged statements are refused.
//! No native compiler, whole M4 or checker soundness claim follows.
//!
//! A contract's or forged statement's pin is the meaning digest
//! (`support/meaning_digest.rs`) of its proposition definition in
//! `CICLNatModel.Contracts` over the package of the fixture family `cic_l_nat_model`
//! (`cic_l`, `cic_l_model`, `kcheck_spec`, `cic_l_nat_model`): the definition and every
//! package definition, inductive type, constructor and compiler auxiliary it
//! reaches, down to Init, so a pin moves when a relation or function the
//! statement names is redefined. The native inventory's per-declaration
//! digests are unchanged. Re-pin with `CLEAN_REPIN_STATEMENT_PINS=1
//! scripts/heavy_gate.sh run 16 cic-l-nat-model-repin -- "$(rustup run trust rustc
//! --print sysroot)/bin/targo" --unverified test -p clean-olean --locked --test
//! cic_l_nat_model`: the run rewrites `theories/cic_l_nat_model/statement_pins.json` and still fails, and the next
//! run without the variable, after a rebuild, confirms it. Until the pending
//! re-qualification of `CICLModel.NatStoredSubstitution` lands (merge
//! `ce7d8d2905` added the private `instantiate_expansion` and four `match_1`
//! auxiliaries there and stopped realizing `CICL.Expr.instantiate.eq_1`, so
//! the subject denominator below no longer reads 373: 377 at that merge, 376
//! at the merge of 2026-11-19), the test stops before
//! its pins and that file still holds the proposition expressions' digests;
//! that re-qualification re-pins it with this command.

#[path = "support/meaning_digest.rs"]
mod meaning_digest;

use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};

use clean_kernel::env::{ConstantInfo, ConstantKind, Declaration, Environment};
use clean_kernel::name::NameInner;
use clean_kernel::{Expr, KernelEnvError, KernelTypeError, Name, ReferenceRefusal};
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::{
    load_module_with_deps, read_artifact, reference_base_closed, require_pinned_lean_lib_path,
    ArtifactDepth,
};
use meaning_digest::{MeaningDigests, Package};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

const ROOT: &str = "CICLNatModel";
const CONTRACTS: &[(&str, &str)] = &[
    (
        "CICL.Model.valid_assignment_installNat",
        "extensionValidity",
    ),
    (
        "CICL.Model.nat_extension_consistent",
        "extensionConsistency",
    ),
    (
        "CICL.Model.NatHistoryWitness.witness_consistent",
        "populatedExtensionConsistency",
    ),
    (
        "CICL.Model.Nat.StoredRules.syntax_zero_stored_rhs",
        "storedZeroEquation",
    ),
    (
        "CICL.Model.Nat.StoredRules.syntax_succ_stored_rhs",
        "storedSuccessorEquation",
    ),
    ("CICL.Model.Nat.constants_typed", "entriesTyped"),
    ("CICL.Model.Nat.only_valid", "boundedValidity"),
    ("CICL.Model.Nat.syntax_zero", "zeroEquation"),
    ("CICL.Model.Nat.syntax_succ", "successorEquation"),
];
const FORGED: &[(&str, &str)] = &[
    (
        "CICL.Model.valid_assignment_installNat",
        "forgedExtensionWithoutReferenceClosure",
    ),
    (
        "CICL.Model.nat_extension_consistent",
        "forgedExtensionWithoutIndexedClosure",
    ),
    (
        "CICL.Model.NatHistoryWitness.witness_consistent",
        "forgedPopulatedAboveBound",
    ),
    (
        "CICL.Model.Nat.StoredRules.syntax_zero_stored_rhs",
        "forgedStoredZeroWithoutCompatibility",
    ),
    (
        "CICL.Model.Nat.StoredRules.syntax_succ_stored_rhs",
        "forgedStoredSuccessorWithoutConstructorInput",
    ),
    (
        "CICL.Model.Nat.constants_typed",
        "forgedEntriesWithoutBound",
    ),
    (
        "CICL.Model.Nat.only_valid",
        "forgedValidityWithoutChosenBound",
    ),
    ("CICL.Model.Nat.syntax_zero", "forgedZeroAtAnyPoint"),
    (
        "CICL.Model.Nat.syntax_succ",
        "forgedSuccessorWithoutConstructorInput",
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

fn nat_data_subject(subject: &Name) -> bool {
    let mut components: Vec<Option<String>> = Vec::new();
    let mut current = subject;
    loop {
        match current.inner() {
            NameInner::Anon => break,
            NameInner::Str(parent, component) => {
                components.push(Some(component.to_string()));
                current = parent;
            }
            NameInner::Num(parent, _) => {
                components.push(None);
                current = parent;
            }
        }
    }
    components.reverse();
    let parts: Vec<Option<&str>> = components.iter().map(|part| part.as_deref()).collect();
    let namespace = [Some("CICL"), Some("BaseFamilies"), Some("Nat")];
    parts.starts_with(&namespace)
        || (parts.len() >= 7
            && parts[..3] == [Some("_private"), Some("CICL"), Some("BaseFamilies")]
            && parts[3].is_none()
            && parts[4..].starts_with(&namespace))
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
fn nat_model_replays_with_exact_scope_and_real_negative_controls() {
    let declared: Vec<String> = include_str!("../../../theories/cic_l_nat_model/ORDER")
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(|stem| stem.replace('/', "."))
        .collect();
    let declared_set: BTreeSet<String> =
        declared.iter().map(|module| (*module).to_owned()).collect();
    assert_eq!(declared.len(), declared_set.len(), "duplicate ORDER module");
    let package = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../theories/cic_l_nat_model");
    let mut source_modules = BTreeSet::new();
    modules(&package, &package, &mut source_modules);
    assert_eq!(
        declared_set, source_modules,
        "own source module census changed"
    );
    assert_eq!(declared.len(), 2, "review own-module denominator");

    let lib = require_pinned_lean_lib_path().expect("install pinned Lean");
    let compiled = compiled_fixture_dir("cic_l_nat_model");
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean binary");
    let bin = lean.parent().expect("pinned Lean bin");
    let mut binary_paths = vec![bin.to_path_buf()];
    binary_paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));
    let binary_path = std::env::join_paths(binary_paths).expect("pinned reference binary path");
    let mut pin_probe = Command::new(&lean)
        .args(["--stdin"])
        .current_dir(&compiled)
        .env("PATH", &binary_path)
        .env(
            "LEAN_PATH",
            std::env::join_paths([&compiled, &lib]).expect("pin probe path"),
        )
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("actual Nat payload probe");
    pin_probe
        .stdin
        .take()
        .expect("pin probe input")
        .write_all(include_str!("support/canonical_base_pins.lean").as_bytes())
        .expect("write exact Nat pin probe");
    let pin_probe = pin_probe
        .wait_with_output()
        .expect("actual Nat payload result");
    let pin_output = format!(
        "{}\n{}",
        String::from_utf8_lossy(&pin_probe.stdout),
        String::from_utf8_lossy(&pin_probe.stderr)
    );
    assert!(
        pin_probe.status.success(),
        "actual Nat payload mismatch: {pin_output}"
    );
    for marker in [
        "CANONICAL_NAT_PIN Nat exact-type-and-payload=ok",
        "CANONICAL_NAT_PIN Nat.zero exact-type-and-payload=ok",
        "CANONICAL_NAT_PIN Nat.succ exact-type-and-payload=ok",
        "CANONICAL_NAT_PIN Nat.rec exact-type-and-payload=ok",
        "CANONICAL_NAT_FAMILY record-and-block=ok",
        "CANONICAL_NAT_COMPARATOR alpha-equal-binder-mutations-refused=ok",
        "CANONICAL_BASE_FAMILY_CENSUS count=3",
    ] {
        assert_eq!(
            pin_output.matches(marker).count(),
            1,
            "missing or duplicate exact Nat pin result: {pin_output}"
        );
    }
    eprintln!("{pin_output}");
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

    let mut loaded = Environment::for_lean_replay();
    let summaries = load_module_with_deps(&mut loaded, ROOT, &[compiled.clone(), lib])
        .expect("load bridge and its dependency closure");
    let skipped: BTreeSet<&str> = summaries
        .iter()
        .flat_map(|summary| summary.skipped_not_replayable.iter().map(String::as_str))
        .collect();
    let extra_modules: Vec<String> = serde_json::from_str(include_str!(
        "../../../theories/cic_l_nat_model/replay_modules.json"
    ))
    .expect("reviewed shared Nat implementation modules");
    assert_eq!(extra_modules.len(), 18);
    assert_eq!(extra_modules.iter().collect::<BTreeSet<_>>().len(), 18);
    let replay_modules: Vec<String> = declared
        .iter()
        .cloned()
        .chain(extra_modules)
        .chain(std::iter::once("CICL.BaseFamilies".to_owned()))
        .collect();
    assert_eq!(replay_modules.iter().collect::<BTreeSet<_>>().len(), 21);
    let mut targets = BTreeSet::new();
    let mut compiler_copies = BTreeSet::new();
    for module in &replay_modules {
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
            if module == "CICL.BaseFamilies" && !nat_data_subject(&subject) {
                continue;
            }
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
                "duplicate current Nat declaration owner: {module}: {subject}"
            );
        }
    }
    assert!(
        compiler_copies.is_empty(),
        "review unexpected Nat compiler-copy population: {compiler_copies:?}"
    );
    for copy in &compiler_copies {
        assert!(targets.contains(&name(
            copy.strip_suffix("._unsafe_rec").expect("copy suffix")
        )));
    }
    assert_eq!(targets.len(), 373, "review bridge subject denominator");
    let legacy: Value = serde_json::from_str(include_str!(
        "../../../theories/cic_l_nat_model/legacy_obligations.json"
    ))
    .expect("original logical obligation ledger");
    let original: BTreeMap<String, Value> = serde_json::from_str(include_str!(
        "../../../theories/cic_l_nat_model/legacy_native_inventory.json"
    ))
    .expect("retained original Native inventory");
    assert_eq!(original.len(), 285);
    let current = legacy["current"]
        .as_object()
        .expect("current obligation bindings");
    let historical = legacy["historical"]
        .as_object()
        .expect("historical obligations");
    let retired = legacy["retained_equations"]
        .as_array()
        .expect("conserved old equations");
    assert_eq!(current.len(), 276);
    assert_eq!(historical.len(), 7);
    assert_eq!(retired.len(), 2);
    let mut old_names = BTreeSet::new();
    for old in current.keys().chain(historical.keys()) {
        assert!(
            old_names.insert(old.clone()),
            "duplicate original obligation"
        );
    }
    for old in retired {
        assert!(old_names.insert(old.as_str().expect("equation name").to_owned()));
    }
    assert_eq!(old_names, original.keys().cloned().collect());
    let actual_names: BTreeMap<String, &Name> = targets
        .iter()
        .map(|subject| (subject.to_unambiguous_string(), subject))
        .collect();
    assert_eq!(actual_names.len(), targets.len());
    for target in current.values() {
        assert!(actual_names.contains_key(target.as_str().expect("current subject")));
    }
    let authored: Vec<String> = serde_json::from_str(include_str!(
        "../../../theories/cic_l_nat_model/authored_theorems.json"
    ))
    .expect("retained original authored theorem roster");
    assert_eq!(authored.len(), 128);
    let bindings = legacy["authored"]
        .as_object()
        .expect("authored obligation bindings");
    assert_eq!(
        bindings.keys().cloned().collect::<BTreeSet<_>>(),
        authored.iter().cloned().collect()
    );
    let mut current_authored = 0;
    let mut historical_authored = 0;
    for old in &authored {
        let target = bindings[old].as_str().expect("authored target");
        if target.starts_with("Reference.NatCatalogControls.") {
            assert_eq!(historical.get(old).and_then(Value::as_str), Some(target));
            historical_authored += 1;
        } else {
            assert_eq!(current.get(old).and_then(Value::as_str), Some(target));
            let subject = actual_names.get(target).expect("current authored theorem");
            assert_eq!(
                loaded.get_const(subject).expect("resident theorem").kind,
                ConstantKind::Theorem
            );
            current_authored += 1;
        }
    }
    assert_eq!(current_authored, 125);
    assert_eq!(historical_authored, 3);
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
    let declared_kinds: BTreeMap<String, String> = serde_json::from_str(include_str!(
        "../../../theories/cic_l_nat_model/declaration_kinds.json"
    ))
    .expect("independent module-origin declaration kinds");
    assert_eq!(
        declared_kinds.len(),
        targets.len(),
        "declaration-kind census denominator"
    );
    let choice_labels: Vec<String> = serde_json::from_str(include_str!(
        "../../../theories/cic_l_nat_model/named_choice_exceptions.json"
    ))
    .expect("exact canonical Nat derived-choice subjects");
    assert_eq!(choice_labels.len(), 6);
    let choice_exceptions: BTreeSet<Name> = choice_labels
        .iter()
        .map(|label| {
            (*actual_names
                .get(label)
                .expect("actual uniquely disclosed choice subject"))
            .clone()
        })
        .collect();
    assert_eq!(choice_exceptions.len(), 6);
    assert!(
        choice_exceptions.is_subset(&targets),
        "missing named choice subject"
    );
    let mut observed_choice = BTreeSet::new();
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
        let mut subject_allowed = allowed.clone();
        if choice_exceptions.contains(subject) {
            subject_allowed.insert("Classical.choice".to_owned());
        }
        if closure.contains("Classical.choice") {
            observed_choice.insert(subject.clone());
        }
        assert!(
            closure.is_subset(&subject_allowed),
            "{subject}: {closure:?}"
        );
        let semantic_kind = if loaded.get_inductive(subject).is_some() {
            "inductive"
        } else if loaded.get_constructor(subject).is_some() {
            "constructor"
        } else if loaded.get_recursor(subject).is_some() {
            "recursor"
        } else {
            match info.kind {
                ConstantKind::Definition => "definition",
                ConstantKind::Theorem => "theorem",
                ConstantKind::Opaque => "opaque",
                ConstantKind::Axiom => "axiom",
            }
        };
        assert_eq!(
            declared_kinds.get(&subject.to_string()).map(String::as_str),
            Some(semantic_kind),
            "module-origin declaration role changed for {subject}"
        );
        assert!(inventory.insert(subject.to_string(), json!({
            "constant_sha256": digest(info), "kind": format!("{:?}", info.kind),
            "semantic_kind": semantic_kind,
            "inductive_sha256": loaded.get_inductive(subject).map(digest),
            "constructor_sha256": loaded.get_constructor(subject).map(digest),
            "recursor_sha256": loaded.get_recursor(subject).map(digest),
            "level_params": info.level_params.iter().map(ToString::to_string).collect::<Vec<_>>(),
            "axiom_closure": closure,
        })).is_none(), "ambiguous printed declaration name {subject}");
        if info.kind == ConstantKind::Theorem {
            let value = info.value.clone().expect("actual theorem proof");
            kernel
                .add_checked(Declaration::Theorem {
                    name: name(&format!("CICLNatModel.Controls.positive_{theorem_count}")),
                    level_params: info.level_params.clone(),
                    type_: info.type_.clone(),
                    value: value.clone(),
                })
                .unwrap_or_else(|error| panic!("{subject} positive: {error:?}"));
            let bad = kernel.add_checked(Declaration::Theorem {
                name: name(&format!("CICLNatModel.Controls.false_{theorem_count}")),
                level_params: info.level_params.clone(),
                type_: Expr::const_(name("False"), vec![]),
                value,
            });
            assert!(mismatch(&bad), "{subject} at False: {bad:?}");
            theorem_count += 1;
        }
    }
    assert_eq!(
        observed_choice, choice_exceptions,
        "exact named choice closure population"
    );
    assert_eq!(theorem_count, 240, "review complete theorem denominator");
    let statement = |pin: &str| {
        loaded
            .get_const(&name(&format!("CICLNatModel.Contracts.{pin}")))
            .unwrap_or_else(|| panic!("missing schema {pin}"))
            .value
            .clone()
            .expect("schema definition")
    };
    let package = Package::of_fixture(
        &compiled,
        "cic_l_nat_model",
        &["cic_l", "cic_l_model", "kcheck_spec", "cic_l_nat_model"],
    );
    let mut pins = BTreeMap::new();
    {
        let digests = MeaningDigests::new(kernel.environment(), &package);
        let mut roots = Vec::new();
        for (_, pin) in CONTRACTS.iter().chain(FORGED) {
            let root = name(&format!("CICLNatModel.Contracts.{pin}"));
            let digest = digests
                .digest(&root)
                .unwrap_or_else(|error| panic!("{error}"));
            assert!(pins.insert((*pin).to_owned(), digest).is_none());
            roots.push(root);
        }
        eprintln!(
            "{}",
            digests
                .describe(&package, &roots)
                .unwrap_or_else(|error| panic!("{error}"))
        );
    }
    assert_eq!(pins.len(), 18, "9 contracts and 9 forged statements");
    for (index, (theorem, pin)) in CONTRACTS.iter().enumerate() {
        let proof = loaded.get_const(&name(theorem)).expect("headline theorem");
        assert!(targets.contains(&name(theorem)));
        kernel
            .add_checked(Declaration::Theorem {
                name: name(&format!("CICLNatModel.Controls.contract_{index}")),
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
            name: name(&format!("CICLNatModel.Controls.forged_{index}")),
            level_params: proof.level_params.clone(),
            type_: statement(pin),
            value: proof.value.clone().expect("actual proof"),
        });
        assert!(mismatch(&bad), "{theorem} at forged {pin}: {bad:?}");
    }
    eprintln!(
        "nat-model-inventory {}",
        serde_json::to_string(&inventory).expect("inventory JSON")
    );
    eprintln!(
        "nat-model-pins {}",
        serde_json::to_string(&pins).expect("pin JSON")
    );
    eprintln!(
        "nat-model-replay subjects={} theorems={} module_artifacts=21 nat_data=42 legacy=285 current_authored=125 historical_authored=3 contracts=9 forged=9 compiler_copies={}",
        targets.len(),
        theorem_count,
        compiler_copies.len()
    );
    let committed_inventory: BTreeMap<String, Value> = serde_json::from_str(include_str!(
        "../../../theories/cic_l_nat_model/native_inventory.json"
    ))
    .expect("committed exact native inventory");
    let committed_pins: BTreeMap<String, String> = serde_json::from_str(include_str!(
        "../../../theories/cic_l_nat_model/statement_pins.json"
    ))
    .expect("committed statement pins");
    assert_eq!(
        inventory, committed_inventory,
        "Nat model declaration/axiom inventory changed"
    );
    if let Err(failure) = meaning_digest::check_pins(
        &pins,
        &committed_pins,
        "theories/cic_l_nat_model/statement_pins.json",
    ) {
        panic!("Nat model contract statements changed: {failure}");
    }
}
