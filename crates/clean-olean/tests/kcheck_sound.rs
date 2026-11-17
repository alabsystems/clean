// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Plan unit C3, its checker-independent remainder
//! (`docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`, design
//! `designs/2026-11-12-kcheck-model-first.md`): the proof package
//! `theories/kcheck_sound`, built cold by its own `lakefile.toml`, compiled by
//! pinned Lean over `theories/cic_l`, `theories/cic_l_model` and
//! `theories/kcheck_spec`, replayed by `leanchecker --fresh`, and re-admitted
//! constant by constant through Clean's reference kernel from an empty base. The
//! machinery is `kcheck_spec.rs`'s.
//!
//! What a green run shows: a cold `lake build` of the package succeeds and a
//! one-root lakefile fails cold; every constant the package's six modules
//! declare is admitted by two kernels; each pinned theorem's axiom closure is the
//! committed one, inside `propext`, `Quot.sound` and `Classical.choice`; each
//! pinned theorem proves the statement pinned for it, and neither `False` nor the
//! forged statement beside it; the two lemmas Revision 5.1 is to copy are
//! declared at their named propositions themselves; and the definitions the pins
//! mention have the committed digests. Among the pinned theorems: the
//! substitution at index `k` under `k` binders and the per-argument IOTA bridge
//! that Revision 5.1 is to pin; `family_former_kind` and the run-level corollary;
//! appending a fresh entry keeps `Env.Valid` given the new entry's facts at the
//! old environment; the rooted theorem entry `idP` over `Env.base` is valid,
//! extends, is rooted and inhabits the consumer's lemma; a checker sound at the
//! standard base inhabits every hypothesis of the run-level corollary; and each
//! bridge lemma with one hypothesis dropped is false, while the real proof
//! (`kcheck_spec`'s `*_proved` for the seven bridges of `C3Owes`, this package's
//! for the rest) is refused at that statement. What it does not show: the seven
//! bridges or `C3Owes` themselves, which `kcheck_spec.rs` and `kcheck_labelled.rs`
//! qualify.

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsStr;
use std::path::Path;
use std::process::Command;

use clean_kernel::env::{ConstantInfo, Declaration, Environment};
use clean_kernel::{ConstantKind, Expr, KernelEnvError, KernelTypeError, Name, ReferenceRefusal};
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::{
    load_module_with_deps, read_artifact, reference_base_closed, require_pinned_lean_lib_path,
    ArtifactDepth,
};
use sha2::{Digest, Sha256};

/// The module that imports every other module of the package.
const ROOT: &str = "KCheckSound.Contracts";

/// The packages `theories/kcheck_sound/lakefile.toml` requires by path.
const REQUIRES: &[&str] = &["kcheck_spec", "cic_l_model", "cic_l"];

/// `(theorem, statement pin in KCheckSound.Contracts)`.
const CONTRACTS: &[(&str, &str)] = &[
    // What Revision 5.1 is to pin.
    ("KCheckSound.inst_value_holds", "instValue"),
    (
        "KCheckSound.value_inst_of_inst_value",
        "valueInstOfInstValue",
    ),
    ("KCheckSound.value_stored_holds", "valueStored"),
    ("KCheckSound.family_former_kind", "familyFormerKind"),
    ("KCheckSound.run_receipt_holds", "runReceiptHolds"),
    // Appending one entry.
    ("KCheckSound.valid_append", "validAppend"),
    ("KCheckSound.valid_append_of", "validAppendOf"),
    // The ground cases.
    ("KCheckSound.baseId_valid", "baseIdValid"),
    ("KCheckSound.baseId_extends", "baseIdExtends"),
    ("KCheckSound.baseId_rooted", "baseIdRooted"),
    ("KCheckSound.baseId_receipt", "baseIdReceipt"),
    ("KCheckSound.oneChecker_sound", "oneCheckerSound"),
    ("KCheckSound.run_receipt_nonvacuous", "runReceiptNonvacuous"),
    // The negative controls.
    (
        "KCheckSound.Controls.ann_extend_needs_levels",
        "notAnnExtendNoLevels",
    ),
    ("KCheckSound.Controls.ann_inst_needs_arg", "notAnnInstNoArg"),
    (
        "KCheckSound.Controls.value_inst_needs_scoped",
        "notValueInstUnscoped",
    ),
    (
        "KCheckSound.Controls.ann_instLevels_needs_levels",
        "notAnnInstLevelsPlain",
    ),
    (
        "KCheckSound.Controls.ann_closed_transport_needs_scoped",
        "notAnnClosedTransportUnscoped",
    ),
    (
        "KCheckSound.Controls.value_scope_transport_needs_agree",
        "notValueScopeTransportNoAgree",
    ),
    (
        "KCheckSound.Controls.walkTele_inTele_needs_arity",
        "notWalkTeleInTeleRev4",
    ),
    (
        "KCheckSound.Controls.value_stored_needs_scoped",
        "notValueStoredUnscoped",
    ),
    (
        "KCheckSound.Controls.family_former_kind_needs_formers",
        "notFamilyFormerKindNoFormers",
    ),
    (
        "KCheckSound.Controls.rooted_family_former_kind_refuted",
        "notRootedFamilyFormerKind",
    ),
];

/// The theorems whose declared type must be the pin's value itself: the two
/// lemmas Revision 5.1 is to copy are proved at the propositions this package
/// names (`KCheckSound.inst_value`, `KCheckSound.value_stored`), not at a
/// restatement that is only definitionally equal to them.
const EXACT: &[&str] = &["instValue", "valueStored"];

/// `(real proof, statement nobody proves)`. Each forged statement is the
/// lemma with one hypothesis dropped, and a negative control above refutes it.
/// The seven bridges of `C3Owes` are proved in `kcheck_spec`
/// (`KCheckSpec.Bridges`), so their real proofs are those.
const FORGED_STATEMENTS: &[(&str, &str)] = &[
    ("KCheckSpec.ann_extend_proved", "forged_annExtendNoLevels"),
    ("KCheckSpec.ann_inst_proved", "forged_annInstNoArg"),
    ("KCheckSpec.value_inst_proved", "forged_valueInstUnscoped"),
    (
        "KCheckSpec.ann_instLevels_proved",
        "forged_annInstLevelsPlain",
    ),
    (
        "KCheckSpec.ann_closed_transport_proved",
        "forged_annClosedTransportUnscoped",
    ),
    (
        "KCheckSpec.value_scope_transport_proved",
        "forged_valueScopeTransportNoAgree",
    ),
    (
        "KCheckSpec.walkTele_inTele_proved",
        "forged_walkTeleInTeleRev4",
    ),
    (
        "KCheckSound.value_stored_holds",
        "forged_valueStoredUnscoped",
    ),
    (
        "KCheckSound.family_former_kind",
        "forged_familyFormerKindNoFormers",
    ),
    ("KCheckSound.baseId_valid", "forged_baseIdValidAnyTower"),
    (
        "KCheckSound.family_former_kind",
        "forged_rootedFamilyFormerKind",
    ),
];

/// The package's definitions the pins mention, by type and value. The
/// propositions of `kcheck_spec` they also mention are pinned by
/// `kcheck_spec.rs`.
const SPECIFICATION: &[&str] = &[
    "KCheckSound.appendEntry",
    "KCheckSound.instArgs",
    "KCheckSound.inst_value",
    "KCheckSound.value_stored",
    "KCheckSound.baseId",
    "KCheckSound.oneChecker",
    "KCheckSound.Controls.AnnExtendNoLevels",
    "KCheckSound.Controls.AnnInstNoArg",
    "KCheckSound.Controls.ValueInstUnscoped",
    "KCheckSound.Controls.AnnInstLevelsPlain",
    "KCheckSound.Controls.AnnClosedTransportUnscoped",
    "KCheckSound.Controls.ValueScopeTransportNoAgree",
    "KCheckSound.Controls.ValueStoredUnscoped",
    "KCheckSound.Controls.FamilyFormerKindNoFormers",
    "KCheckSound.FamilyFormers",
    "KCheckSound.Controls.RootedFamilyFormerKind",
];

fn name(s: &str) -> Name {
    Name::from_string(s)
}

/// The constant a name is an equation of, when it is one Lean generates on
/// demand in the module that first needs it: an equation lemma (`f.eq_<n>`,
/// `f.eq_def`) or a sparse case split's fallthrough equation
/// (`f._sparseCasesOn_<n>.else_eq`). A proof here that unfolds a specification
/// function realises them in this package's modules under that function's name.
fn generated_equation_base(text: &str) -> Option<&str> {
    let (base, last) = text.rsplit_once('.')?;
    let numbered = last
        .strip_prefix("eq_")
        .is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()));
    (numbered || last == "eq_def" || last == "else_eq").then_some(base)
}

/// The module stems of `theories/kcheck_sound/ORDER`.
fn order_stems() -> Vec<&'static str> {
    include_str!("../../../theories/kcheck_sound/ORDER")
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .collect()
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn digest(statement: &Expr) -> String {
    let bytes = bincode::serde::encode_to_vec(statement, bincode::config::standard())
        .expect("serialize a statement");
    hex(&Sha256::digest(&bytes))
}

/// A definition's type and value, in that order, in one digest.
fn constant_digest(constant: &ConstantInfo) -> String {
    let mut hasher = Sha256::new();
    for part in std::iter::once(&constant.type_).chain(constant.value.as_ref()) {
        let bytes = bincode::serde::encode_to_vec(part, bincode::config::standard())
            .expect("serialize a specification part");
        hasher.update((bytes.len() as u64).to_le_bytes());
        hasher.update(&bytes);
    }
    hex(&hasher.finalize())
}

/// Copy a package directory without its `.lake` build directory.
fn copy_package(from: &Path, to: &Path) {
    std::fs::create_dir_all(to).unwrap_or_else(|error| panic!("create {}: {error}", to.display()));
    for entry in
        std::fs::read_dir(from).unwrap_or_else(|error| panic!("read {}: {error}", from.display()))
    {
        let entry = entry.expect("directory entry");
        if entry.file_name() == ".lake" {
            continue;
        }
        let target = to.join(entry.file_name());
        if entry.file_type().expect("entry type").is_dir() {
            copy_package(&entry.path(), &target);
        } else {
            std::fs::copy(entry.path(), &target)
                .unwrap_or_else(|error| panic!("copy {}: {error}", entry.path().display()));
        }
    }
}

/// The package's own `lake build`, cold, as `kcheck_spec.rs` runs its: the
/// package is copied without its `.lake` directory beside links to the three
/// packages it requires, so no module of `kcheck_sound` is built and Lake must
/// find every import of `KCheckSound.Contracts` in the library. The control is
/// a lakefile whose only root is that module: Lake does not count the other
/// modules as the library's, and its cold build fails at an import's missing
/// object file.
fn cold_lake_build(bin: &Path, binary_path: &OsStr) {
    let theories = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../theories")
        .canonicalize()
        .expect("theories directory");
    let lakefile = std::fs::read_to_string(theories.join("kcheck_sound/lakefile.toml"))
        .expect("kcheck_sound lakefile.toml");
    for stem in order_stems() {
        let module = stem.replace('/', ".");
        assert!(
            lakefile.contains(&format!("\"{module}\"")),
            "theories/kcheck_sound/lakefile.toml lists {module} as a root"
        );
    }
    for dependency in REQUIRES {
        assert!(
            lakefile.contains(&format!("path = \"../{dependency}\"")),
            "theories/kcheck_sound/lakefile.toml requires {dependency} by path"
        );
    }
    let one_root: String = lakefile
        .lines()
        .map(|line| {
            if line.starts_with("roots = ") {
                "roots = [\"KCheckSound.Contracts\"]"
            } else {
                line
            }
        })
        .flat_map(|line| [line, "\n"])
        .collect();
    assert_ne!(one_root, lakefile, "the control changes the roots line");
    for (label, text, accepted) in [
        ("committed", &lakefile, true),
        ("one-root", &one_root, false),
    ] {
        let scratch = tempfile::tempdir().expect("scratch directory");
        let package = scratch.path().join("kcheck_sound");
        copy_package(&theories.join("kcheck_sound"), &package);
        std::fs::write(package.join("lakefile.toml"), text).expect("write lakefile.toml");
        for dependency in REQUIRES {
            std::os::unix::fs::symlink(theories.join(dependency), scratch.path().join(dependency))
                .unwrap_or_else(|error| panic!("link {dependency}: {error}"));
        }
        let build = Command::new(bin.join("lake"))
            .arg("build")
            .current_dir(&package)
            .env("PATH", binary_path)
            .env_remove("LEAN_PATH")
            .output()
            .expect("run pinned lake build");
        let output = format!(
            "{}\n{}",
            String::from_utf8_lossy(&build.stdout),
            String::from_utf8_lossy(&build.stderr)
        );
        assert_eq!(
            build.status.success(),
            accepted,
            "cold lake build with the {label} lakefile: {output}"
        );
        if !accepted {
            assert!(
                output.contains("of module KCheckSound.") && output.contains("does not exist"),
                "the one-root lakefile must fail at an import's missing object file: {output}"
            );
        }
        eprintln!("lake-build {label} accepted={accepted}");
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

#[test]
fn kcheck_sound_rechecks_through_two_kernels_with_pinned_statements() {
    let lib = require_pinned_lean_lib_path().expect("install the repository-pinned Lean toolchain");
    let compiled = compiled_fixture_dir("kcheck_sound");
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean binary");
    let bin = lean.parent().expect("Lean bin directory");
    let mut paths = vec![bin.to_path_buf()];
    paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));
    let binary_path = std::env::join_paths(paths).expect("binary path");
    cold_lake_build(bin, &binary_path);

    // Kernel one: Lean's own, replaying the root module and everything below
    // it, the specification and the model included, from nothing.
    let independent = Command::new(bin.join("leanchecker"))
        .args(["--fresh", ROOT])
        .current_dir(&compiled)
        .env(
            "LEAN_PATH",
            std::env::join_paths([&compiled, &lib]).expect("Lean path"),
        )
        .env("PATH", &binary_path)
        .output()
        .expect("run pinned independent Lean kernel");
    assert!(
        independent.status.success(),
        "leanchecker --fresh {ROOT} failed: {}\n{}",
        String::from_utf8_lossy(&independent.stdout),
        String::from_utf8_lossy(&independent.stderr)
    );

    let mut loaded = Environment::for_lean_replay();
    let summaries = load_module_with_deps(&mut loaded, ROOT, &[compiled.clone(), lib])
        .expect("load the compiled package");

    // The subjects are the constants the package's own modules declare, read
    // from each artifact's name table: a `KCheckSpec.*` or `CICL.*` constant is
    // counted as this package's only when one of its modules declares it, as an
    // equation Lean generated there.
    let stems = order_stems();
    assert_eq!(
        stems.len(),
        6,
        "module denominator of theories/kcheck_sound/ORDER"
    );
    let not_replayable: BTreeSet<&str> = summaries
        .iter()
        .flat_map(|summary| summary.skipped_not_replayable.iter().map(String::as_str))
        .collect();
    let mut targets: BTreeSet<Name> = BTreeSet::new();
    let mut compiler_copies: BTreeSet<String> = BTreeSet::new();
    for stem in &stems {
        let module = stem.replace('/', ".");
        let artifact = read_artifact(
            &module,
            &compiled.join(format!("{stem}.olean")),
            ArtifactDepth::Names,
        )
        .unwrap_or_else(|error| panic!("read {module}: {error}"));
        assert!(!artifact.names.is_empty(), "{module} declares nothing");
        let mut generated = 0usize;
        for constant in &artifact.names {
            let text = constant.to_string();
            if loaded.get_const(constant).is_none() {
                assert!(
                    text.ends_with("._unsafe_rec") && not_replayable.contains(text.as_str()),
                    "{module} declares {constant}, which the load did not make resident and \
                     the artifact does not mark as a compiler's unsafe copy"
                );
                assert!(compiler_copies.insert(text), "{constant} is declared twice");
                continue;
            }
            // Every name is the package's own, private to its module (a
            // matcher's splitter for a specification function, say, carries
            // the module's mangled prefix), or a theorem Lean generated here as
            // an equation of a constant a required package declares.
            let own = text.starts_with("KCheckSound.")
                || text.starts_with(&format!("_private.{module}.0."));
            if !own {
                let base = generated_equation_base(&text).unwrap_or_else(|| {
                    panic!(
                        "{module} declares {constant} outside the package's namespace, not \
                         private to it and not an equation Lean generates"
                    )
                });
                assert!(
                    !base.starts_with("KCheckSound.")
                        && !base.starts_with("_private.KCheckSound.")
                        && loaded.get_const(&name(base)).is_some(),
                    "{module} declares {constant}, an equation of {base}, which no required \
                     package declares"
                );
                assert!(
                    loaded
                        .get_const(constant)
                        .is_some_and(|info| info.kind == ConstantKind::Theorem),
                    "{module} declares {constant}, which is not a theorem"
                );
                generated += 1;
            }
            assert!(
                !loaded.is_unsafe(constant) && !loaded.is_partial(constant),
                "{module} declares {constant} unsafe or partial"
            );
            assert!(
                targets.insert(constant.clone()),
                "{constant} is declared by two modules"
            );
        }
        eprintln!(
            "module {module}: {} constants, {generated} of them equations generated for \
             required constants",
            artifact.names.len()
        );
    }
    for copy in &compiler_copies {
        let definition = copy
            .strip_suffix("._unsafe_rec")
            .expect("checked when collected");
        assert!(
            targets.contains(&name(definition)),
            "{copy} has no definition among the subjects"
        );
    }

    // Statement and specification pins, digested and printed before the
    // reference replay (they read only the loaded artifacts) and compared after
    // it, so one run of a changed set shows every pin and every closure.
    let statement = |pin: &str| -> Expr {
        loaded
            .get_const(&name(&format!("KCheckSound.Contracts.{pin}")))
            .unwrap_or_else(|| panic!("missing statement {pin}"))
            .value
            .clone()
            .unwrap_or_else(|| panic!("{pin} is not a proposition definition"))
    };
    let mut observed_pins: BTreeMap<String, String> = BTreeMap::new();
    for pin in CONTRACTS
        .iter()
        .chain(FORGED_STATEMENTS)
        .map(|(_, pin)| *pin)
    {
        assert!(
            observed_pins
                .insert(pin.to_owned(), digest(&statement(pin)))
                .is_none(),
            "{pin} is listed twice"
        );
    }
    for object in SPECIFICATION {
        let subject = name(object);
        assert!(targets.contains(&subject), "{object} is not a subject");
        let constant = loaded.get_const(&subject).expect("resident subject");
        assert!(
            observed_pins
                .insert((*object).to_owned(), constant_digest(constant))
                .is_none(),
            "{object} is listed twice"
        );
    }
    for (pin, value) in &observed_pins {
        eprintln!("statement-pin {pin} {value}");
    }
    assert_eq!(
        observed_pins.len(),
        CONTRACTS.len() + FORGED_STATEMENTS.len() + SPECIFICATION.len(),
        "pin denominator"
    );

    // Kernel two: Clean's reference kernel, from an empty base.
    let checked = reference_base_closed(&loaded, &targets, &ClosedRecheckOptions::default())
        .expect("construct dependency-closed reference replay");
    assert!(
        checked.report.passed() && checked.entry_refusals.is_empty(),
        "{}\n{:?}",
        checked.report.verdict_sentence(),
        checked.entry_refusals
    );
    let mut kernel = checked
        .into_kernel()
        .expect("all reference admissions passed");

    // Axiom closures: nothing past `propext`, `Quot.sound` (with `Quot`'s
    // built-ins) and `Classical.choice`, and the committed closure per theorem.
    let allowed: BTreeSet<String> = [
        "propext",
        "Quot.sound",
        "Quot",
        "Quot.mk",
        "Quot.lift",
        "Quot.ind",
        "Classical.choice",
    ]
    .into_iter()
    .map(str::to_owned)
    .collect();
    let closure_of = |env: &Environment, subject: &Name| -> BTreeSet<String> {
        let mut closure = env.axiom_deps(subject).expect("admitted declaration");
        closure.extend(env.foundational_axiom_deps(subject).expect("closure"));
        closure.iter().map(ToString::to_string).collect()
    };
    let mut union: BTreeSet<String> = BTreeSet::new();
    for subject in &targets {
        let closure = closure_of(kernel.environment(), subject);
        assert!(closure.is_subset(&allowed), "{subject}: {closure:?}");
        union.extend(closure);
    }
    let mut observed_closures: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    observed_closures.insert("*".to_owned(), union);
    for (theorem, _) in CONTRACTS {
        let subject = name(theorem);
        assert!(targets.contains(&subject), "missing theorem {theorem}");
        observed_closures.insert(
            (*theorem).to_owned(),
            closure_of(kernel.environment(), &subject),
        );
    }
    for (subject, closure) in &observed_closures {
        eprintln!("axiom-closure {subject} {closure:?}");
    }

    let committed_closures: BTreeMap<String, BTreeSet<String>> = serde_json::from_str(
        include_str!("../../../theories/kcheck_sound/axiom_closures.json"),
    )
    .expect("committed axiom closures");
    let committed_pins: BTreeMap<String, String> = serde_json::from_str(include_str!(
        "../../../theories/kcheck_sound/statement_pins.json"
    ))
    .expect("committed statement pins");
    assert_eq!(
        observed_closures, committed_closures,
        "observed axiom closures differ from theories/kcheck_sound/axiom_closures.json"
    );
    assert_eq!(
        observed_pins, committed_pins,
        "observed statements differ from theories/kcheck_sound/statement_pins.json"
    );

    // The lemmas Revision 5.1 is to copy are declared at the propositions this
    // package names.
    for pin in EXACT {
        let (theorem, _) = CONTRACTS
            .iter()
            .find(|(_, contract)| contract == pin)
            .unwrap_or_else(|| panic!("{pin} is not a contract"));
        let declared = &loaded
            .get_const(&name(theorem))
            .expect("pinned theorem")
            .type_;
        assert!(
            *declared == statement(pin),
            "{theorem} is not declared at the statement {pin} pins"
        );
    }

    // Each theorem's own proof is admitted at the statement pinned for it, and
    // refused at `False`.
    for (theorem, pin) in CONTRACTS {
        let proof = loaded.get_const(&name(theorem)).expect("pinned theorem");
        let value = proof.value.clone().expect("the theorem has a proof");
        kernel
            .add_checked(Declaration::Theorem {
                name: name(&format!("KCheckSound.Qualification.{pin}_positive")),
                level_params: proof.level_params.clone(),
                type_: statement(pin),
                value: value.clone(),
            })
            .unwrap_or_else(|refusal| {
                panic!("{theorem} at its pinned statement {pin}: {refusal:?}")
            });
        let bad = kernel.add_checked(Declaration::Theorem {
            name: name(&format!("KCheckSound.Qualification.{pin}_false")),
            level_params: proof.level_params.clone(),
            type_: Expr::const_(name("False"), vec![]),
            value,
        });
        assert!(
            is_type_mismatch(&bad),
            "{theorem} at False must fail by type mismatch: {bad:?}"
        );
    }

    // A real proof is refused at the statement with one hypothesis dropped.
    for (theorem, forged) in FORGED_STATEMENTS {
        let proof = loaded.get_const(&name(theorem)).expect("pinned theorem");
        let bad = kernel.add_checked(Declaration::Theorem {
            name: name(&format!("KCheckSound.Qualification.{forged}")),
            level_params: proof.level_params.clone(),
            type_: statement(forged),
            value: proof.value.clone().expect("the theorem has a proof"),
        });
        assert!(
            is_type_mismatch(&bad),
            "{theorem} at {forged} must fail by type mismatch: {bad:?}"
        );
    }

    eprintln!(
        "kcheck_sound subjects {}, modules {}, contracts {}, exact {}, forged statements {}, \
         specification pins {}",
        targets.len(),
        stems.len(),
        CONTRACTS.len(),
        EXACT.len(),
        FORGED_STATEMENTS.len(),
        SPECIFICATION.len()
    );
}
