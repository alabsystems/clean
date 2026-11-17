// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![deny(
    clippy::wildcard_enum_match_arm,
    clippy::match_wildcard_for_single_variants,
    clippy::wildcard_in_or_patterns
)]

//! A1.2's logical arithmetic prerequisite only. The existing public fixture
//! compiler, meaning digests and default fenced entry qualify the two bridges;
//! no Rust-byte, extern, compiler, runtime or authority alignment follows.

#[path = "support/lean_axiom_census.rs"]
mod lean_axiom_census;
#[path = "support/meaning_digest.rs"]
mod meaning_digest;

use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};

use clean_kernel::env::{Declaration, Environment};
use clean_kernel::expr::{ExprFolder, LevelVec};
use clean_kernel::{ConstantKind, Expr, KernelEnvError, KernelTypeError, Name, ReferenceRefusal};
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::{
    load_module_with_deps, read_artifact, reference_base_closed, require_pinned_lean_lib_path,
    ArtifactDepth,
};
use serde_json::{json, Value};

const FAMILY: &str = "align_nat_word";
const ROOT: &str = "AlignNatWordQualification";
const MODEL_EVAL: &str = "CICL.LiteralRules.NatBinOp.eval";
const PIN_FILE: &str = "theories/align_nat_word/checked_inventory.json";
const CONTRACTS: &[(&str, &str, &str, &str, &str)] = &[
    (
        "AlignNatWord.div64_toNat",
        "AlignNatWordContracts.divBridge",
        "AlignNatWordContracts.swappedDivBridge",
        "AlignNatWord.div64",
        "AlignNatWord.mod64",
    ),
    (
        "AlignNatWord.mod64_toNat",
        "AlignNatWordContracts.modBridge",
        "AlignNatWordContracts.swappedModBridge",
        "AlignNatWord.mod64",
        "AlignNatWord.div64",
    ),
];

fn name(text: &str) -> Name {
    Name::from_string(text)
}

fn order(text: &str) -> Vec<String> {
    text.lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(str::to_owned)
        .collect()
}

fn source_modules(directory: &Path, root: &Path, found: &mut BTreeSet<String>) {
    for entry in std::fs::read_dir(directory).expect("read own source directory") {
        let entry = entry.expect("source entry");
        let path = entry.path();
        if path.is_dir() {
            if entry.file_name() != ".lake" {
                source_modules(&path, root, found);
            }
        } else if path
            .extension()
            .is_some_and(|extension| extension == "lean")
        {
            let module = path
                .strip_prefix(root)
                .expect("source within package")
                .with_extension("")
                .to_string_lossy()
                .replace(std::path::MAIN_SEPARATOR, ".");
            assert!(found.insert(module), "duplicate own source module");
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

struct ReplaceConstant<'a> {
    from: &'a Name,
    to: &'a Name,
    changed: usize,
}

impl ExprFolder for ReplaceConstant<'_> {
    fn fold_const(&mut self, constant: &Name, levels: &LevelVec) -> Expr {
        if constant == self.from {
            self.changed += 1;
            Expr::const_(self.to.clone(), levels.clone())
        } else {
            Expr::const_(constant.clone(), levels.clone())
        }
    }
}

#[test]
fn logical_word_arithmetic_replays_with_exact_meanings_and_controls() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let package_source = workspace.join("theories/align_nat_word");
    assert_eq!(
        std::fs::read_to_string(package_source.join("lean-toolchain"))
            .expect("package Lean pin")
            .trim(),
        include_str!("../../../lean-toolchain").trim()
    );
    let declared = order(include_str!("../../../theories/align_nat_word/ORDER"))
        .into_iter()
        .map(|stem| stem.replace('/', "."))
        .collect::<Vec<_>>();
    assert_eq!(declared, ["AlignNatWord.Arithmetic", "AlignNatWord"]);
    let mut actual_sources = BTreeSet::new();
    source_modules(&package_source, &package_source, &mut actual_sources);
    assert_eq!(actual_sources, declared.iter().cloned().collect());
    let descriptor: toml::Value = toml::from_str(include_str!(
        "../../../theories/align_nat_word/lakefile.toml"
    ))
    .expect("complete Lake descriptor");
    let roots = descriptor["lean_lib"][0]["roots"]
        .as_array()
        .expect("Lake roots")
        .iter()
        .map(|root| root.as_str().expect("root string").to_owned())
        .collect::<Vec<_>>();
    assert_eq!(
        roots, declared,
        "Lake and ORDER have the same complete roots"
    );
    assert_eq!(descriptor["require"][0]["name"].as_str(), Some("cic_l"));
    assert_eq!(descriptor["require"][0]["path"].as_str(), Some("../cic_l"));
    assert_eq!(
        order(include_str!(
            "fixtures/lean/v4.30.0-rc2/align_nat_word/ORDER"
        )),
        [
            "theory cic_l",
            "theory align_nat_word",
            "AlignNatWordContracts",
            "AlignNatWordQualification",
        ]
    );

    let compiled = compiled_fixture_dir(FAMILY);
    let lib = require_pinned_lean_lib_path().expect("exact installed Lean SDK");
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean binary");
    let bin = lean.parent().expect("pinned Lean bin");
    let mut paths = vec![bin.to_path_buf()];
    paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));
    let binary_path = std::env::join_paths(paths).expect("pinned binary path");
    let lean_path = std::env::join_paths([&compiled, &lib]).expect("compiled and SDK path");
    let independent = Command::new(bin.join("leanchecker"))
        .args(["--fresh", ROOT])
        .current_dir(&compiled)
        .env("PATH", &binary_path)
        .env("LEAN_PATH", &lean_path)
        .output()
        .expect("pinned fresh Lean kernel");
    assert!(
        independent.status.success(),
        "fresh Lean replay: {}\n{}",
        String::from_utf8_lossy(&independent.stdout),
        String::from_utf8_lossy(&independent.stderr)
    );

    let mut loaded = Environment::for_lean_replay();
    load_module_with_deps(&mut loaded, ROOT, &[compiled.clone(), lib])
        .expect("load actual source and independent contracts");
    let mut modules = declared;
    modules.extend(["AlignNatWordContracts".to_owned(), ROOT.to_owned()]);
    let mut targets = BTreeSet::new();
    let mut physical_origins = BTreeMap::new();
    for module in &modules {
        let artifact = read_artifact(
            module,
            &compiled.join(format!("{}.olean", module.replace('.', "/"))),
            ArtifactDepth::Names,
        )
        .unwrap_or_else(|error| panic!("read {module}: {error}"));
        if !["AlignNatWord", ROOT].contains(&module.as_str()) {
            assert!(
                !artifact.names.is_empty(),
                "empty declaration module {module}"
            );
        }
        for subject in artifact.names {
            assert!(!loaded.is_unsafe(&subject) && !loaded.is_partial(&subject));
            let info = loaded
                .get_const(&subject)
                .expect("every physical subject is resident");
            assert!(matches!(
                info.kind,
                ConstantKind::Definition | ConstantKind::Theorem
            ));
            assert_eq!(
                loaded
                    .get_constant_origin(&subject)
                    .and_then(|origin| origin.module_name()),
                Some(module.as_str()),
                "physical/logical origin mismatch for {subject}"
            );
            assert!(
                targets.insert(subject.clone()),
                "duplicate declaration owner"
            );
            assert!(physical_origins
                .insert(subject.clone(), module.clone())
                .is_none());
        }
    }
    assert!(!targets.is_empty(), "an empty census is not qualification");
    let model_eval = name(MODEL_EVAL);
    assert_eq!(
        loaded
            .get_const(&model_eval)
            .expect("resident model relation")
            .kind,
        ConstantKind::Definition
    );
    let mut replay_roots = targets.clone();
    assert!(replay_roots.insert(model_eval.clone()));
    let checked = reference_base_closed(&loaded, &replay_roots, &ClosedRecheckOptions::default())
        .expect("dependency-closed default fenced replay");
    assert!(
        checked.report.passed() && checked.entry_refusals.is_empty(),
        "{}\n{:?}",
        checked.report.verdict_sentence(),
        checked.entry_refusals
    );
    let mut kernel = checked
        .into_kernel()
        .expect("all reference admissions passed");

    let mut closures = BTreeMap::<String, BTreeSet<String>>::new();
    let mut theorem_count = 0;
    for subject in &replay_roots {
        let info = loaded
            .get_const(subject)
            .expect("original resident declaration");
        let mut axioms = kernel
            .environment()
            .axiom_deps(subject)
            .expect("domain axiom closure");
        axioms.extend(
            kernel
                .environment()
                .foundational_axiom_deps(subject)
                .expect("foundational closure"),
        );
        let axioms = axioms
            .iter()
            .map(ToString::to_string)
            .collect::<BTreeSet<_>>();
        let ax0 = [
            "propext",
            "Quot.sound",
            "Classical.choice",
            "Quot",
            "Quot.mk",
            "Quot.lift",
            "Quot.ind",
        ]
        .into_iter()
        .map(str::to_owned)
        .collect::<BTreeSet<_>>();
        assert!(axioms.is_subset(&ax0), "{subject} uses {axioms:?}");
        assert!(closures.insert(subject.to_string(), axioms).is_none());
        if info.kind == ConstantKind::Theorem {
            let value = info.value.clone().expect("actual original proof");
            kernel
                .add_checked(Declaration::Theorem {
                    name: name(&format!("A1ReferenceControls.positive{theorem_count}")),
                    level_params: info.level_params.clone(),
                    type_: info.type_.clone(),
                    value: value.clone(),
                })
                .unwrap_or_else(|error| panic!("{subject} original body: {error:?}"));
            let false_name = name(&format!("A1ReferenceControls.false{theorem_count}"));
            let bad = kernel.add_checked(Declaration::Theorem {
                name: false_name.clone(),
                level_params: info.level_params.clone(),
                type_: Expr::const_(name("False"), vec![]),
                value,
            });
            assert!(mismatch(&bad), "{subject} at False: {bad:?}");
            assert!(kernel.environment().get_const(&false_name).is_none());
            theorem_count += 1;
        }
    }
    assert!(
        theorem_count >= 6,
        "both bridges, zero facts and swap refutations must execute"
    );
    let expected_axioms = closures
        .iter()
        .map(|(subject, axioms)| {
            (
                subject.as_str(),
                axioms.iter().map(String::as_str).collect::<Vec<_>>(),
            )
        })
        .collect::<Vec<_>>();
    let expected_axioms = expected_axioms
        .iter()
        .map(|(subject, axioms)| (*subject, axioms.as_slice()))
        .collect::<Vec<_>>();
    lean_axiom_census::check(&lean, &compiled, ROOT, &expected_axioms);

    for (index, (theorem, literal, forged, from, to)) in CONTRACTS.iter().enumerate() {
        let proof = loaded
            .get_const(&name(theorem))
            .expect("real bridge theorem");
        let literal = loaded
            .get_const(&name(literal))
            .and_then(|info| info.value.clone())
            .expect("independent full literal");
        let forged = loaded
            .get_const(&name(forged))
            .and_then(|info| info.value.clone())
            .expect("independent swapped literal");
        assert_eq!(proof.type_, literal, "complete literal contract");
        let from = name(from);
        let to = name(to);
        let mut replacement = ReplaceConstant {
            from: &from,
            to: &to,
            changed: 0,
        };
        let mutated = replacement.fold_expr(&proof.type_);
        assert_eq!(replacement.changed, 1, "exactly one operation changes");
        assert_ne!(mutated, proof.type_);
        assert_eq!(
            mutated, forged,
            "forged literal is exactly the declared substitution"
        );
        kernel
            .add_checked(Declaration::Theorem {
                name: name(&format!("A1ReferenceControls.literal{index}")),
                level_params: proof.level_params.clone(),
                type_: literal,
                value: proof.value.clone().expect("original bridge body"),
            })
            .expect("real body at the independent complete literal");
        let forged_name = name(&format!("A1ReferenceControls.swap{index}"));
        let bad = kernel.add_checked(Declaration::Theorem {
            name: forged_name.clone(),
            level_params: proof.level_params.clone(),
            type_: mutated,
            value: proof.value.clone().expect("original bridge body"),
        });
        assert!(mismatch(&bad), "{theorem} swapped operation: {bad:?}");
        assert!(kernel.environment().get_const(&forged_name).is_none());
    }

    let mut controls = Command::new(&lean)
        .arg("--stdin")
        .current_dir(&compiled)
        .env("PATH", &binary_path)
        .env("LEAN_PATH", &lean_path)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("pinned Lean original/False/exact-swap controls");
    controls
        .stdin
        .take()
        .expect("SDK control input")
        .write_all(
            include_str!("fixtures/lean/v4.30.0-rc2/align_nat_word/KernelControls.lean").as_bytes(),
        )
        .expect("write SDK control source");
    let controls = controls.wait_with_output().expect("reap SDK controls");
    let sdk_output = format!(
        "{}\n{}",
        String::from_utf8_lossy(&controls.stdout),
        String::from_utf8_lossy(&controls.stderr)
    );
    eprintln!("{sdk_output}");
    assert!(
        controls.status.success(),
        "SDK original/False/swap controls failed"
    );
    assert_eq!(
        sdk_output.matches("A1_SDK_ORIGINAL ").count(),
        theorem_count
    );
    assert_eq!(sdk_output.matches("A1_SDK_FALSE ").count(), theorem_count);
    assert_eq!(sdk_output.matches("A1_SDK_LITERAL ").count(), 2);
    assert_eq!(sdk_output.matches("A1_SDK_SWAP ").count(), 2);
    assert!(sdk_output.contains(&format!("A1_SDK_OWNED_THEOREMS {theorem_count}")));

    let mut meaning_modules = order(include_str!("../../../theories/cic_l/ORDER"))
        .into_iter()
        .map(|module| module.replace('/', "."))
        .collect::<Vec<_>>();
    meaning_modules.extend(modules);
    let package = meaning_digest::Package::of_modules(&compiled, meaning_modules);
    assert!(replay_roots.is_subset(package.names()));
    let meanings = meaning_digest::MeaningDigests::new(kernel.environment(), &package);
    let mut observed = BTreeMap::<String, Value>::new();
    for subject in &replay_roots {
        let info = kernel
            .environment()
            .get_const(subject)
            .expect("checked pin subject");
        let module = if subject == &model_eval {
            "CICL.LiteralRules"
        } else {
            physical_origins
                .get(subject)
                .expect("complete physical owner")
        };
        assert!(observed.insert(subject.to_string(), json!({
            "kind": format!("{:?}", info.kind), "module": module,
            "level_params": info.level_params.iter().map(ToString::to_string).collect::<Vec<_>>(),
            "meaning_sha256": meanings.digest(subject).expect("checked environment meaning"),
            "axiom_closure": closures[&subject.to_string()],
        })).is_none());
    }
    eprintln!(
        "{}",
        meanings
            .describe(&package, &replay_roots.iter().cloned().collect::<Vec<_>>())
            .expect("meaning footprint")
    );
    eprintln!("align-nat-word subjects={} theorem_body_false={} complete_literals=2 exact_swaps=2 model_eval_pins=1 checking_limits=default", targets.len(), theorem_count);
    let committed = match std::fs::read_to_string(workspace.join(PIN_FILE)) {
        Ok(text) => serde_json::from_str::<BTreeMap<String, Value>>(&text)
            .expect("committed checked inventory"),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => BTreeMap::new(),
        Err(error) => panic!("read checked inventory: {error}"),
    };
    if observed != committed {
        panic!(
            "checked A1.2 meanings/roles/closures differ: {}",
            meaning_digest::record_measured(&observed, PIN_FILE)
        );
    }
}
