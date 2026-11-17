// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![deny(
    clippy::wildcard_enum_match_arm,
    clippy::match_wildcard_for_single_variants,
    clippy::wildcard_in_or_patterns
)]

//! Canonical SemR-to-UInt64 scalar semantics only. No Rust bytes, compiler
//! capture, Assert execution, runtime or alignment figure follows.

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
use clean_kernel::{
    ConstantKind, Expr, ExprKind, KernelEnvError, KernelTypeError, Name, ReferenceRefusal,
};
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::{
    load_module_with_deps, read_artifact, reference_base_closed, require_pinned_lean_lib_path,
    ArtifactDepth,
};
use serde_json::{json, Value};

const FAMILY: &str = "align_nat_word_semr";
const ROOT: &str = "AlignNatWordSemRQualification";
const PIN_FILE: &str =
    "crates/clean-olean/tests/fixtures/lean/v4.30.0-rc2/align_nat_word_semr/checked_inventory.json";
const SEMANTICS: &[(&str, &str)] = &[
    ("CICL.LiteralRules.NatBinOp.eval", "CICL.LiteralRules"),
    ("AlignNatWord.div64", "AlignNatWord.Arithmetic"),
    ("AlignNatWord.mod64", "AlignNatWord.Arithmetic"),
    ("SemR.evalBinop", "SemR"),
    ("SemR.intBin", "SemR"),
];
// Canonical SemR's maintained oracle uses this same distinction:
// quotient primitive formers belong to the theory, not Lean's printed axioms.
// Preserve every one in the full native closure and Ax0 gate below.
const QUOT_FORMERS: &[&str] = &["Quot", "Quot.mk", "Quot.lift", "Quot.ind"];
const LITERALS: &[(&str, &str)] = &[
    (
        "AlignNatWordSemR.udiv_word",
        "AlignNatWordSemRContracts.divGuarded",
    ),
    (
        "AlignNatWordSemR.urem_word",
        "AlignNatWordSemRContracts.modGuarded",
    ),
    (
        "AlignNatWordSemR.udiv_success_iff",
        "AlignNatWordSemRContracts.divSuccess",
    ),
    (
        "AlignNatWordSemR.urem_success_iff",
        "AlignNatWordSemRContracts.modSuccess",
    ),
    (
        "AlignNatWordSemR.udiv_zero",
        "AlignNatWordSemRContracts.divZero",
    ),
    (
        "AlignNatWordSemR.urem_zero",
        "AlignNatWordSemRContracts.modZero",
    ),
];
const SWAPS: &[(&str, &str, &str, &str)] = &[
    (
        "AlignNatWordSemR.udiv_word",
        "AlignNatWordSemRContracts.swappedDiv",
        "AlignNatWord.div64",
        "AlignNatWord.mod64",
    ),
    (
        "AlignNatWordSemR.urem_word",
        "AlignNatWordSemRContracts.swappedMod",
        "AlignNatWord.mod64",
        "AlignNatWord.div64",
    ),
];
const OMISSIONS: &[(&str, &str)] = &[
    (
        "AlignNatWordSemR.udiv_word",
        "AlignNatWordSemRContracts.unguardedDiv",
    ),
    (
        "AlignNatWordSemR.urem_word",
        "AlignNatWordSemRContracts.unguardedMod",
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

fn erase_binder(expression: &Expr, index: u32) -> Expr {
    let ExprKind::Pi(binder, domain, body) = expression.kind() else {
        panic!("mutation binder index exceeds original telescope")
    };
    if index == 0 {
        assert!(
            !body.has_loose_bvar(0),
            "deleted premise occurs in remaining type"
        );
        body.instantiate(&Expr::prop())
    } else {
        Expr::pi(*binder, (**domain).clone(), erase_binder(body, index - 1))
    }
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
fn scalar_word_semantics_replays_with_exact_meanings_and_controls() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let source =
        workspace.join("crates/clean-olean/tests/fixtures/lean/v4.30.0-rc2/align_nat_word_semr");
    let mut actual_sources = BTreeSet::new();
    source_modules(&source, &source, &mut actual_sources);
    assert_eq!(
        actual_sources,
        [
            "AlignNatWordSemR",
            "AlignNatWordSemRContracts",
            ROOT,
            "KernelControls"
        ]
        .into_iter()
        .map(str::to_owned)
        .collect()
    );
    assert_eq!(
        order(include_str!(
            "fixtures/lean/v4.30.0-rc2/align_nat_word_semr/ORDER"
        )),
        [
            "theory cic_l",
            "theory align_nat_word",
            "from semr SemR",
            "AlignNatWordSemR",
            "AlignNatWordSemRContracts",
            ROOT
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
    let modules = [
        "AlignNatWordSemR".to_owned(),
        "AlignNatWordSemRContracts".to_owned(),
        ROOT.to_owned(),
    ];
    let mut targets = BTreeSet::new();
    let mut physical_origins = BTreeMap::new();
    for module in &modules {
        let artifact = read_artifact(
            module,
            &compiled.join(format!("{}.olean", module.replace('.', "/"))),
            ArtifactDepth::Names,
        )
        .unwrap_or_else(|error| panic!("read {module}: {error}"));
        if module != ROOT {
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
    let mut replay_roots = targets.clone();
    for (semantic, module) in SEMANTICS {
        let semantic = name(semantic);
        assert_eq!(
            loaded
                .get_const(&semantic)
                .expect("resident actual semantics")
                .kind,
            ConstantKind::Definition
        );
        assert_eq!(
            loaded
                .get_constant_origin(&semantic)
                .and_then(|origin| origin.module_name()),
            Some(*module)
        );
        assert!(replay_roots.insert(semantic));
    }
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
                    name: name(&format!(
                        "SemRWordReferenceControls.positive{theorem_count}"
                    )),
                    level_params: info.level_params.clone(),
                    type_: info.type_.clone(),
                    value: value.clone(),
                })
                .unwrap_or_else(|error| panic!("{subject} original body: {error:?}"));
            let false_name = name(&format!("SemRWordReferenceControls.false{theorem_count}"));
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
        theorem_count >= 13,
        "semantic bridges, successful iff, zero facts, helpers and four refutations must execute"
    );
    let expected_axioms = closures
        .iter()
        .map(|(subject, axioms)| {
            (
                subject.as_str(),
                axioms
                    .iter()
                    .map(String::as_str)
                    .filter(|axiom| !QUOT_FORMERS.contains(axiom))
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<Vec<_>>();
    let expected_axioms = expected_axioms
        .iter()
        .map(|(subject, axioms)| (*subject, axioms.as_slice()))
        .collect::<Vec<_>>();
    lean_axiom_census::check(&lean, &compiled, ROOT, &expected_axioms);

    for (index, (theorem, literal)) in LITERALS.iter().enumerate() {
        let proof = loaded
            .get_const(&name(theorem))
            .expect("original semantic theorem");
        let literal = loaded
            .get_const(&name(literal))
            .and_then(|info| info.value.clone())
            .expect("complete independent proposition");
        assert_eq!(proof.type_, literal, "full independent literal {theorem}");
        kernel
            .add_checked(Declaration::Theorem {
                name: name(&format!("SemRWordReferenceControls.literal{index}")),
                level_params: proof.level_params.clone(),
                type_: literal,
                value: proof.value.clone().expect("actual original proof"),
            })
            .expect("original proof at complete literal");
    }
    for (index, (theorem, forged, from, to)) in SWAPS.iter().enumerate() {
        let proof = loaded
            .get_const(&name(theorem))
            .expect("original guarded theorem");
        let forged = loaded
            .get_const(&name(forged))
            .and_then(|info| info.value.clone())
            .expect("full swap literal");
        let (from, to) = (name(from), name(to));
        let mut replacement = ReplaceConstant {
            from: &from,
            to: &to,
            changed: 0,
        };
        let mutated = replacement.fold_expr(&proof.type_);
        assert_eq!(
            replacement.changed, 1,
            "exactly one logical operation changes"
        );
        assert_ne!(mutated, proof.type_);
        assert_eq!(mutated, forged, "complete exact swap");
        let refused_name = name(&format!("SemRWordReferenceControls.swap{index}"));
        let bad = kernel.add_checked(Declaration::Theorem {
            name: refused_name.clone(),
            level_params: proof.level_params.clone(),
            type_: mutated,
            value: proof.value.clone().expect("actual original proof"),
        });
        assert!(mismatch(&bad), "swap {theorem}: {bad:?}");
        assert!(kernel.environment().get_const(&refused_name).is_none());
    }
    for (index, (theorem, omitted)) in OMISSIONS.iter().enumerate() {
        let proof = loaded
            .get_const(&name(theorem))
            .expect("original guarded theorem");
        let literal = loaded
            .get_const(&name(omitted))
            .and_then(|info| info.value.clone())
            .expect("complete omission literal");
        let mutated = erase_binder(&proof.type_, 3);
        assert_ne!(mutated, proof.type_);
        assert_eq!(mutated, literal, "delete exactly nonzero binder3");
        let refused_name = name(&format!("SemRWordReferenceControls.omitted{index}"));
        let bad = kernel.add_checked(Declaration::Theorem {
            name: refused_name.clone(),
            level_params: proof.level_params.clone(),
            type_: mutated,
            value: proof.value.clone().expect("actual original proof"),
        });
        assert!(mismatch(&bad), "omission {theorem}: {bad:?}");
        assert!(kernel.environment().get_const(&refused_name).is_none());
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
            include_str!("fixtures/lean/v4.30.0-rc2/align_nat_word_semr/KernelControls.lean")
                .as_bytes(),
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
        sdk_output.matches("SEMR_WORD_SDK_ORIGINAL ").count(),
        theorem_count
    );
    assert_eq!(
        sdk_output.matches("SEMR_WORD_SDK_FALSE ").count(),
        theorem_count
    );
    assert_eq!(sdk_output.matches("SEMR_WORD_SDK_LITERAL ").count(), 6);
    assert_eq!(sdk_output.matches("SEMR_WORD_SDK_SWAP ").count(), 2);
    assert!(sdk_output.contains(&format!("SEMR_WORD_SDK_OWNED_THEOREMS {theorem_count}")));

    assert_eq!(sdk_output.matches("SEMR_WORD_SDK_OMIT ").count(), 2);

    let mut meaning_modules = order(include_str!("../../../theories/cic_l/ORDER"))
        .into_iter()
        .map(|module| module.replace('/', "."))
        .collect::<Vec<_>>();
    meaning_modules.extend(
        order(include_str!("../../../theories/align_nat_word/ORDER"))
            .into_iter()
            .map(|module| module.replace('/', ".")),
    );
    meaning_modules.push("SemR".to_owned());
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
        let module = SEMANTICS
            .iter()
            .find(|(semantic, _)| name(semantic) == *subject)
            .map(|(_, module)| *module)
            .unwrap_or_else(|| {
                physical_origins
                    .get(subject)
                    .expect("complete physical owner")
                    .as_str()
            });
        assert!(observed.insert(subject.to_string(), json!({
            "kind": format!("{:?}", info.kind), "module": module,
            "level_params": info.level_params.iter().map(ToString::to_string).collect::<Vec<_>>(),
            "meaning_sha256": meanings.digest(subject).expect("checked environment meaning"),
            "axiom_closure": closures[&subject.to_string()],
            "lean_axiom_closure": closures[&subject.to_string()].iter().filter(|axiom| !QUOT_FORMERS.contains(&axiom.as_str())).collect::<Vec<_>>(),
        })).is_none());
    }
    eprintln!(
        "{}",
        meanings
            .describe(&package, &replay_roots.iter().cloned().collect::<Vec<_>>())
            .expect("meaning footprint")
    );
    eprintln!("align-nat-word-semr subjects={} theorem_body_false={} complete_literals=6 exact_swaps=2 exact_omissions=2 semantic_roots=5 checking_limits=default", targets.len(), theorem_count);
    let committed = match std::fs::read_to_string(workspace.join(PIN_FILE)) {
        Ok(text) => serde_json::from_str::<BTreeMap<String, Value>>(&text)
            .expect("committed checked inventory"),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => BTreeMap::new(),
        Err(error) => panic!("read checked inventory: {error}"),
    };
    if observed != committed {
        panic!(
            "checked scalar meanings/roles/closures differ: {}",
            meaning_digest::record_measured(&observed, PIN_FILE)
        );
    }
}
