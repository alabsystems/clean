// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Qualification for C5's proof-only native framed-run package.
//!
//! The package proves facts about the actual `KCheck.kcheckRun`: framing,
//! fail-fast ordered calls, receipt alignment and conditional semantic
//! transport.  A green run means pinned Lean replayed the fresh package,
//! Clean's fenced reference kernel re-admitted every owned declaration from an
//! empty base, every owned theorem's proof was accepted at its exact statement
//! and rejected at `False`, and the committed statement/body and axiom pins
//! match.  Concrete dependency controls retain one successful two-declaration
//! run plus wrong-order, frame-count and truncated-frame refusals.
//!
//! This is a package-local census.  It deliberately does not widen the current
//! E7 census, establish `kcheck_sound_N`, prove loader correctness, or transfer
//! authority from `clean-kernel`.

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
use sha2::{Digest, Sha256};

const ROOT: &str = "KCheckFramedRun";
const MINT_ENV: &str = "CLEAN_MINT_KCHECK_FRAMED_RUN_PINS";

/// Definitions whose exact type, value and generated/nested auxiliaries are
/// part of this theorem's meaning.  These are imported roots, not additions to
/// the fresh package's declaration denominator.
const DEPENDENCY_DEFINITIONS: &[&str] = &[
    "CICL.Model.SetValue.IndexedUnionClosed",
    "KCheck.readNat",
    "KCheck.splitFramesAux",
    "KCheck.splitFrames",
    "KCheck.Advice.start",
    "KCheck.kcheck",
    "KCheck.base",
    "KCheck.kcheckRun",
    "KCheck.checker",
    "KCheckSpec.PSigmaSeed.seed",
    "KCheckSpec.PSigmaBase.base",
    "KCheckSpec.Extends",
    "KCheckSpec.Env.Valid",
    "KCheckSpec.Rooted",
    "KCheckSpec.kcheck_sound_N",
];

/// Concrete actual-caller controls imported from C2.  Their statements are
/// pinned here and their proof terms are independently re-admitted.  The first
/// inhabits the successful-run premise; the remaining three retain the exact
/// fail-fast order/framing refusals.
const RUN_CONTROLS: &[&str] = &[
    "KCheck.CheckerCases.sequence_accepted",
    "KCheck.CheckerCases.sequence_order_refused",
    "KCheck.CheckerCases.sequence_frame_count_refused",
    "KCheck.CheckerCases.sequence_frames_truncated_refused",
];

/// Headline declarations that must remain owned by the fresh package.  The
/// complete owned-theorem census below is dynamic; this list prevents a green
/// run after the intended theorem is silently deleted or renamed.
const REQUIRED_THEOREMS: &[&str] = &[
    "KCheckFramedRun.RunTrace.length",
    "KCheckFramedRun.kcheckRun_trace",
    "KCheckFramedRun.RunTrace.rooted_valid",
    "KCheckFramedRun.kcheckRun_rooted_valid",
    "KCheckFramedRun.Controls.sequence_trace",
    "KCheckFramedRun.Controls.sequence_rooted_valid",
];

/// Actual proofs replayed at separately written contract bodies.  This keeps a
/// proof green only while it inhabits the independently stated proposition,
/// not merely its own declaration's type.
const INDEPENDENT_CONTRACTS: &[(&str, &str)] = &[
    (
        "KCheckFramedRun.RunTrace.length",
        "KCheckFramedRun.Contracts.traceLength",
    ),
    (
        "KCheckFramedRun.kcheckRun_trace",
        "KCheckFramedRun.Contracts.runTrace",
    ),
    (
        "KCheckFramedRun.RunTrace.rooted_valid",
        "KCheckFramedRun.Contracts.traceRootedValid",
    ),
    (
        "KCheckFramedRun.kcheckRun_rooted_valid",
        "KCheckFramedRun.Contracts.runRootedValid",
    ),
];

/// Positive full-result proofs offered at exact forged propositions.  Each
/// must be rejected specifically by type mismatch; the separate owned
/// refutation theorems prove the forged propositions false as well.
const FORGED_CONTROLS: &[(&str, &str)] = &[
    (
        "KCheckFramedRun.Controls.sequence_count",
        "KCheckFramedRun.Contracts.forged_receipt_count",
    ),
    (
        "KCheckFramedRun.Controls.sequence_names",
        "KCheckFramedRun.Contracts.forged_receipt_order",
    ),
    (
        "KCheckFramedRun.Controls.frame_count_refused",
        "KCheckFramedRun.Contracts.forged_frame_count",
    ),
    (
        "KCheckFramedRun.Controls.truncated_frame_refused",
        "KCheckFramedRun.Contracts.forged_truncated_frame",
    ),
];

fn name(text: &str) -> Name {
    Name::from_string(text)
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

/// Pin a declaration's complete signature metadata while deliberately omitting
/// a theorem proof body.  The proof body is re-admitted below; proof
/// irrelevance means its particular bytes are not part of the theorem's
/// statement contract.
fn statement_digest(constant: &ConstantInfo) -> String {
    let bytes = bincode::serde::encode_to_vec(
        (
            &constant.name,
            &constant.level_params,
            &constant.type_,
            constant.is_reducible,
            constant.reducibility,
            constant.kind,
        ),
        bincode::config::standard(),
    )
    .expect("serialize declaration signature");
    hex(&Sha256::digest(bytes))
}

fn feed_constant(hasher: &mut Sha256, constant: &ConstantInfo) {
    let bytes = bincode::serde::encode_to_vec(
        (
            &constant.name,
            &constant.level_params,
            &constant.type_,
            &constant.value,
            constant.is_reducible,
            constant.reducibility,
            constant.kind,
        ),
        bincode::config::standard(),
    )
    .expect("serialize complete constant");
    hasher.update((bytes.len() as u64).to_le_bytes());
    hasher.update(bytes);
}

fn constant_digest(constant: &ConstantInfo) -> String {
    let mut hasher = Sha256::new();
    feed_constant(&mut hasher, constant);
    hex(&hasher.finalize())
}

/// A definition's complete `ConstantInfo` followed by every resident safe
/// constant nested below `<definition>.`, in name order. Structural recursion
/// commonly keeps the executable body in one of these auxiliaries rather than
/// in the public constant itself.
fn definition_digest(constant: &ConstantInfo, auxiliaries: &[(String, &ConstantInfo)]) -> String {
    let mut hasher = Sha256::new();
    feed_constant(&mut hasher, constant);
    for (auxiliary, info) in auxiliaries {
        hasher.update((auxiliary.len() as u64).to_le_bytes());
        hasher.update(auxiliary.as_bytes());
        feed_constant(&mut hasher, info);
    }
    hex(&hasher.finalize())
}

fn source_modules(root: &Path, directory: &Path, modules: &mut BTreeSet<String>) {
    for entry in std::fs::read_dir(directory).expect("read framed-run package directory") {
        let entry = entry.expect("framed-run package directory entry");
        let path = entry.path();
        let filename = entry.file_name();
        if filename.to_string_lossy().starts_with('.') {
            continue;
        }
        if entry
            .file_type()
            .expect("framed-run source file type")
            .is_dir()
        {
            source_modules(root, &path, modules);
        } else if path
            .extension()
            .is_some_and(|extension| extension == "lean")
            && filename != "lakefile.lean"
        {
            let stem = path
                .strip_prefix(root)
                .expect("framed-run source inside package")
                .with_extension("");
            let module = stem
                .to_string_lossy()
                .replace(std::path::MAIN_SEPARATOR, ".");
            assert!(modules.insert(module), "duplicate source module");
        }
    }
}

fn is_type_mismatch<T>(result: &Result<T, ReferenceRefusal>) -> bool {
    matches!(
        result,
        Err(ReferenceRefusal::Kernel(KernelEnvError::TypeCheckFailed {
            source: KernelTypeError::TypeMismatch { .. },
            ..
        }))
    )
}

fn closure_of(environment: &Environment, subject: &Name) -> BTreeSet<String> {
    let mut closure = environment
        .axiom_deps(subject)
        .expect("replayed declaration has an axiom closure");
    closure.extend(
        environment
            .foundational_axiom_deps(subject)
            .expect("replayed declaration has a foundational closure"),
    );
    closure.iter().map(ToString::to_string).collect()
}

/// Keep compiler-owned bodies/projections/equations beneath a dependency root,
/// but do not sweep unrelated manually named theorems merely because their
/// namespace begins with the definition's name (`IndexedUnionClosed.lift`,
/// `Rooted.extend`, and so on).
fn is_dependency_auxiliary(definition: &str, candidate: &ConstantInfo) -> bool {
    let text = candidate.name.to_string();
    let Some(suffix) = text.strip_prefix(&format!("{definition}.")) else {
        return false;
    };
    candidate.kind != ConstantKind::Theorem
        || suffix.starts_with("eq_")
        || suffix.starts_with("_eq_")
        || suffix.starts_with("_proof_")
        || suffix.starts_with("_match_")
        || suffix.starts_with("match_")
}

#[test]
fn framed_run_provenance_rechecks_with_pins_and_controls() {
    let lib = require_pinned_lean_lib_path().expect("install repository-pinned Lean");
    let compiled = compiled_fixture_dir("kcheck_framed_run");
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean binary");
    let bin = lean.parent().expect("pinned Lean bin directory");
    let mut binary_paths = vec![bin.to_path_buf()];
    binary_paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));

    // Kernel one: upstream Lean replays the root and its dependency graph from
    // compiled bytes, without importing an already-populated environment.
    let independent = Command::new(bin.join("leanchecker"))
        .args(["--fresh", ROOT])
        .current_dir(&compiled)
        .env(
            "LEAN_PATH",
            std::env::join_paths([&compiled, &lib]).expect("pinned Lean search path"),
        )
        .env(
            "PATH",
            std::env::join_paths(binary_paths).expect("pinned Lean binary path"),
        )
        .output()
        .expect("run independent pinned Lean kernel");
    assert!(
        independent.status.success(),
        "leanchecker --fresh {ROOT}: {}\n{}",
        String::from_utf8_lossy(&independent.stdout),
        String::from_utf8_lossy(&independent.stderr)
    );

    let package = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../theories/kcheck_framed_run");
    let order: Vec<String> = std::fs::read_to_string(package.join("ORDER"))
        .expect("read theories/kcheck_framed_run/ORDER")
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(|line| line.replace('/', "."))
        .collect();
    let modules: BTreeSet<String> = order.iter().cloned().collect();
    assert_eq!(
        modules.len(),
        order.len(),
        "duplicate framed-run ORDER entry"
    );
    assert!(
        modules.contains(ROOT),
        "ORDER must include the package root"
    );
    let mut sources = BTreeSet::new();
    source_modules(&package, &package, &mut sources);
    assert_eq!(modules, sources, "ORDER equals every package Lean source");

    let mut loaded = Environment::for_lean_replay();
    let summaries = load_module_with_deps(&mut loaded, ROOT, &[compiled.clone(), lib])
        .expect("load framed-run compiled bytes");
    let loaded_modules: BTreeSet<String> = summaries
        .iter()
        .filter_map(|summary| summary.module_name.as_ref())
        .filter(|module| modules.contains(*module))
        .cloned()
        .collect();
    assert_eq!(modules, loaded_modules, "every ORDER module was loaded");

    let not_replayable: BTreeSet<&str> = summaries
        .iter()
        .flat_map(|summary| summary.skipped_not_replayable.iter().map(String::as_str))
        .collect();
    let mut targets = BTreeSet::new();
    let mut compiler_copies = BTreeSet::new();
    for module in &modules {
        let artifact = read_artifact(
            module,
            &compiled.join(format!("{}.olean", module.replace('.', "/"))),
            ArtifactDepth::Names,
        )
        .unwrap_or_else(|error| panic!("read framed-run artifact {module}: {error}"));
        for subject in artifact.names {
            let text = subject.to_string();
            if loaded.get_const(&subject).is_none() {
                assert!(
                    text.ends_with("._unsafe_rec") && not_replayable.contains(text.as_str()),
                    "{module} declares absent non-compiler-copy {subject}"
                );
                assert!(compiler_copies.insert(text), "compiler copy declared twice");
                continue;
            }
            assert!(
                !loaded.is_unsafe(&subject) && !loaded.is_partial(&subject),
                "unsafe or partial owned declaration {subject}"
            );
            assert!(targets.insert(subject.clone()), "{subject} declared twice");
            assert_eq!(
                loaded
                    .get_constant_origin(&subject)
                    .and_then(|origin| origin.module_name()),
                Some(module.as_str()),
                "owned declaration origin"
            );
        }
    }
    assert!(
        !targets.is_empty(),
        "nonempty framed-run declaration census"
    );
    for copy in &compiler_copies {
        let definition = copy
            .strip_suffix("._unsafe_rec")
            .expect("checked compiler-copy suffix");
        assert!(
            targets.contains(&name(definition)),
            "{copy} has no safe owned definition"
        );
    }

    let own_theorems: BTreeSet<Name> = targets
        .iter()
        .filter(|subject| {
            loaded
                .get_const(subject)
                .is_some_and(|constant| constant.kind == ConstantKind::Theorem)
        })
        .cloned()
        .collect();
    for theorem in REQUIRED_THEOREMS {
        assert!(
            own_theorems.contains(&name(theorem)),
            "required framed-run theorem {theorem}"
        );
    }

    // Explicit imported roots and all safe nested auxiliaries join the replay
    // and pin sets.  This catches a caller/body change even when every theorem
    // statement remains textually identical.
    let mut replay_targets = targets.clone();
    let mut dependency_groups: BTreeMap<String, (Name, Vec<Name>)> = BTreeMap::new();
    for definition in DEPENDENCY_DEFINITIONS {
        let subject = name(definition);
        let constant = loaded
            .get_const(&subject)
            .unwrap_or_else(|| panic!("missing dependency definition {definition}"));
        assert_ne!(
            constant.kind,
            ConstantKind::Axiom,
            "dependency root {definition} is an axiom"
        );
        assert!(
            !loaded.is_unsafe(&subject) && !loaded.is_partial(&subject),
            "unsafe or partial dependency root {definition}"
        );
        let prefix = format!("{definition}.");
        let auxiliaries: Vec<Name> = loaded
            .constants()
            .filter(|candidate| {
                candidate.name.to_string().starts_with(&prefix)
                    && is_dependency_auxiliary(definition, candidate)
                    && !loaded.is_unsafe(&candidate.name)
                    && !loaded.is_partial(&candidate.name)
            })
            .map(|candidate| candidate.name.clone())
            .collect();
        let mut auxiliaries = auxiliaries;
        auxiliaries.sort_by_key(|auxiliary| auxiliary.to_string());
        replay_targets.insert(subject.clone());
        replay_targets.extend(auxiliaries.iter().cloned());
        assert!(
            dependency_groups
                .insert((*definition).to_owned(), (subject, auxiliaries))
                .is_none(),
            "duplicate dependency group {definition}"
        );
    }
    for control in RUN_CONTROLS {
        let subject = name(control);
        let constant = loaded
            .get_const(&subject)
            .unwrap_or_else(|| panic!("missing actual-run control {control}"));
        assert_eq!(constant.kind, ConstantKind::Theorem, "{control} theorem");
        assert!(constant.value.is_some(), "{control} has a proof");
        replay_targets.insert(subject);
    }

    // Kernel two: Clean's reference kernel admits the exact roots and their
    // complete dependency closure from an empty base.
    let checked = reference_base_closed(&loaded, &replay_targets, &ClosedRecheckOptions::default())
        .expect("dependency-closed fenced framed-run replay");
    assert!(
        checked.report.passed() && checked.entry_refusals.is_empty(),
        "{}\n{:?}",
        checked.report.verdict_sentence(),
        checked.entry_refusals
    );
    eprintln!(
        "fenced-framed-run-replay {}",
        checked.report.verdict_sentence()
    );
    let mut kernel = checked.into_kernel().expect("all fenced admissions passed");

    // Package-local axiom census.  The generic structural and conditional
    // semantic theorems are choice-free.  Only the named concrete three-level
    // witness may inherit `Classical.choice` from its model base witness.
    let allowed_choice_free: BTreeSet<String> = [
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
    let mut allowed_with_named_choice = allowed_choice_free.clone();
    allowed_with_named_choice.insert("Classical.choice".to_owned());
    let mut observed_closures = BTreeMap::new();
    let mut choice_subjects = BTreeSet::new();
    for subject in &replay_targets {
        let closure = closure_of(kernel.environment(), subject);
        if closure.contains("Classical.choice") {
            assert!(
                closure.is_subset(&allowed_with_named_choice),
                "{subject}: {closure:?}"
            );
            choice_subjects.insert(subject.to_string());
        } else {
            assert!(
                closure.is_subset(&allowed_choice_free),
                "{subject}: {closure:?}"
            );
        }
        observed_closures.insert(subject.to_string(), closure);
    }
    assert_eq!(
        choice_subjects,
        BTreeSet::from(["KCheckFramedRun.Controls.sequence_rooted_valid".to_owned()]),
        "Classical.choice is allowed only in the named concrete three-level witness"
    );

    // Pin every owned theorem statement, every other owned declaration's type
    // and value, the four concrete run-control statements, and each selected
    // imported definition together with its generated/nested auxiliaries.
    let mut observed_pins = BTreeMap::new();
    for subject in &targets {
        let constant = loaded
            .get_const(subject)
            .expect("resident owned declaration");
        let (key, pin) = if constant.kind == ConstantKind::Theorem {
            (subject.to_string(), statement_digest(constant))
        } else {
            (
                format!("{subject}::type-and-value"),
                constant_digest(constant),
            )
        };
        assert!(
            observed_pins.insert(key.clone(), pin).is_none(),
            "duplicate {key}"
        );
    }
    for control in RUN_CONTROLS {
        let constant = loaded
            .get_const(&name(control))
            .expect("resident actual-run control");
        assert!(
            observed_pins
                .insert((*control).to_owned(), statement_digest(constant))
                .is_none(),
            "duplicate control pin {control}"
        );
    }
    for (definition, (subject, auxiliary_names)) in &dependency_groups {
        let constant = loaded
            .get_const(subject)
            .expect("resident dependency definition");
        let auxiliaries: Vec<(String, &ConstantInfo)> = auxiliary_names
            .iter()
            .map(|auxiliary| {
                (
                    auxiliary.to_string(),
                    loaded
                        .get_const(auxiliary)
                        .expect("resident dependency auxiliary"),
                )
            })
            .collect();
        eprintln!(
            "dependency-pin {definition} auxiliaries [{}]",
            auxiliaries
                .iter()
                .map(|(auxiliary, _)| auxiliary.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        );
        assert!(
            observed_pins
                .insert(
                    format!("{definition}::definition-and-auxiliaries"),
                    definition_digest(constant, &auxiliaries),
                )
                .is_none(),
            "duplicate dependency pin {definition}"
        );
    }

    eprintln!(
        "framed-run-axiom-closures {}",
        serde_json::to_string_pretty(&observed_closures).expect("closure JSON")
    );
    eprintln!(
        "framed-run-statement-pins {}",
        serde_json::to_string_pretty(&observed_pins).expect("pin JSON")
    );
    if std::env::var_os(MINT_ENV).is_some() {
        std::fs::write(
            package.join("axiom_closures.json"),
            format!(
                "{}\n",
                serde_json::to_string_pretty(&observed_closures)
                    .expect("serialize framed-run axiom closures")
            ),
        )
        .expect("mint theories/kcheck_framed_run/axiom_closures.json");
        std::fs::write(
            package.join("statement_pins.json"),
            format!(
                "{}\n",
                serde_json::to_string_pretty(&observed_pins)
                    .expect("serialize framed-run statement pins")
            ),
        )
        .expect("mint theories/kcheck_framed_run/statement_pins.json");
        eprintln!("framed-run-pins-minted via {MINT_ENV}");
    }
    let committed_closures: BTreeMap<String, BTreeSet<String>> = serde_json::from_str(
        &std::fs::read_to_string(package.join("axiom_closures.json"))
            .expect("mint theories/kcheck_framed_run/axiom_closures.json"),
    )
    .expect("committed framed-run axiom closures");
    let committed_pins: BTreeMap<String, String> = serde_json::from_str(
        &std::fs::read_to_string(package.join("statement_pins.json"))
            .expect("mint theories/kcheck_framed_run/statement_pins.json"),
    )
    .expect("committed framed-run statement pins");
    assert_eq!(
        observed_closures, committed_closures,
        "exact package-local framed-run axiom census"
    );
    assert_eq!(
        observed_pins, committed_pins,
        "exact framed-run statement and body pins"
    );

    // Every theorem the fresh package owns is controlled uniformly: its actual
    // proof must re-enter at the exact compiled statement and must be rejected
    // at `False` specifically by type mismatch.
    for (index, subject) in own_theorems.iter().enumerate() {
        let theorem = loaded.get_const(subject).expect("resident owned theorem");
        let value = theorem.value.clone().expect("owned theorem has a proof");
        kernel
            .add_checked(Declaration::Theorem {
                name: name(&format!("KCheckFramedRun.Recheck.own_{index}")),
                level_params: theorem.level_params.clone(),
                type_: theorem.type_.clone(),
                value: value.clone(),
            })
            .unwrap_or_else(|refusal| panic!("{subject} at its own statement: {refusal:?}"));
        let at_false = kernel.add_checked(Declaration::Theorem {
            name: name(&format!("KCheckFramedRun.Recheck.false_{index}")),
            level_params: theorem.level_params.clone(),
            type_: Expr::const_(name("False"), vec![]),
            value,
        });
        assert!(
            is_type_mismatch(&at_false),
            "{subject} at False must fail by type mismatch: {at_false:?}"
        );
    }

    // The four core proofs must also inhabit independently written contract
    // bodies.  A self-consistent theorem declaration alone would not detect a
    // theorem and its own statement drifting together.
    for (index, (theorem_name, contract_name)) in INDEPENDENT_CONTRACTS.iter().enumerate() {
        let theorem = loaded
            .get_const(&name(theorem_name))
            .unwrap_or_else(|| panic!("missing contract proof {theorem_name}"));
        let contract = loaded
            .get_const(&name(contract_name))
            .unwrap_or_else(|| panic!("missing independent contract {contract_name}"));
        let statement = contract
            .value
            .clone()
            .unwrap_or_else(|| panic!("{contract_name} has no proposition body"));
        let value = theorem
            .value
            .clone()
            .unwrap_or_else(|| panic!("{theorem_name} has no proof"));
        kernel
            .add_checked(Declaration::Theorem {
                name: name(&format!("KCheckFramedRun.Recheck.contract_{index}")),
                level_params: theorem.level_params.clone(),
                type_: statement,
                value: value.clone(),
            })
            .unwrap_or_else(|refusal| panic!("{theorem_name} at {contract_name}: {refusal:?}"));
        let at_false = kernel.add_checked(Declaration::Theorem {
            name: name(&format!("KCheckFramedRun.Recheck.contract_false_{index}")),
            level_params: theorem.level_params.clone(),
            type_: Expr::const_(name("False"), vec![]),
            value,
        });
        assert!(
            is_type_mismatch(&at_false),
            "{theorem_name} at False must fail by type mismatch: {at_false:?}"
        );
    }

    // Full-result/count/order proofs are not admitted at concrete forged
    // propositions.  The contract bodies themselves are owned and pinned, and
    // the package also contains direct refutations of all four propositions.
    for (index, (proof_name, forged_name)) in FORGED_CONTROLS.iter().enumerate() {
        let proof = loaded
            .get_const(&name(proof_name))
            .unwrap_or_else(|| panic!("missing positive control {proof_name}"));
        let forged = loaded
            .get_const(&name(forged_name))
            .unwrap_or_else(|| panic!("missing forged contract {forged_name}"));
        let forged_statement = forged
            .value
            .clone()
            .unwrap_or_else(|| panic!("{forged_name} has no proposition body"));
        let bad = kernel.add_checked(Declaration::Theorem {
            name: name(&format!("KCheckFramedRun.Recheck.forged_{index}")),
            level_params: proof.level_params.clone(),
            type_: forged_statement,
            value: proof
                .value
                .clone()
                .unwrap_or_else(|| panic!("{proof_name} has no proof")),
        });
        assert!(
            is_type_mismatch(&bad),
            "{proof_name} at {forged_name} must fail by type mismatch: {bad:?}"
        );
    }

    // Retain actual computation at the caller boundary, not merely statement
    // shape: the success and each exact refusal proof re-enter, then fail at
    // `False`.  Their statement digests above prevent a renamed control from
    // silently changing the behavior under test.
    for (index, control) in RUN_CONTROLS.iter().enumerate() {
        let theorem = loaded
            .get_const(&name(control))
            .expect("resident actual-run control");
        let value = theorem.value.clone().expect("actual-run control proof");
        kernel
            .add_checked(Declaration::Theorem {
                name: name(&format!("KCheckFramedRun.Recheck.control_{index}")),
                level_params: theorem.level_params.clone(),
                type_: theorem.type_.clone(),
                value: value.clone(),
            })
            .unwrap_or_else(|refusal| panic!("{control} at its own statement: {refusal:?}"));
        let at_false = kernel.add_checked(Declaration::Theorem {
            name: name(&format!("KCheckFramedRun.Recheck.control_false_{index}")),
            level_params: theorem.level_params.clone(),
            type_: Expr::const_(name("False"), vec![]),
            value,
        });
        assert!(
            is_type_mismatch(&at_false),
            "{control} at False must fail by type mismatch: {at_false:?}"
        );
    }

    eprintln!(
        "framed-run modules {}, owned subjects {}, owned theorems {}, compiler copies {}, replay roots {}, dependency groups {}, independent contracts {}, forged controls {}, imported actual-run controls {}",
        modules.len(),
        targets.len(),
        own_theorems.len(),
        compiler_copies.len(),
        replay_targets.len(),
        dependency_groups.len(),
        INDEPENDENT_CONTRACTS.len(),
        FORGED_CONTROLS.len(),
        RUN_CONTROLS.len()
    );
}
