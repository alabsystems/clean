// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Plan unit D1, Revision 5 (`designs/2026-11-12-kcheck-model-first.md`): the
//! specification package `theories/kcheck_spec`, built cold by its own
//! `lakefile.toml`, compiled by pinned Lean over `theories/cic_l` and
//! `theories/cic_l_model`, replayed by `leanchecker --fresh`, and re-admitted
//! constant by constant through Clean's reference kernel from an empty base.
//!
//! What a green run shows: a cold `lake build` of the package succeeds, and the
//! lakefile Revision 3 landed (one root) fails cold; every constant the
//! package's thirteen modules declare is admitted by two kernels; each pinned
//! theorem's axiom closure is the committed one; each contract theorem proves
//! the statement pinned for it and not `False`; seven selected proofs are also
//! refused at forged statements; and the definitions units C2 and C3 are
//! written against (`Env.Valid` and
//! its clauses, `Setting`, `Checker`, the receipt, the loader, the step
//! statements, `Rooted`, the bridge lemmas C3 owes and `C3Owes`) have the
//! committed digests. Among the pinned theorems: the base environment over
//! `Eq`, `PUnit` and `Nat` satisfies `Env.Valid` at every tower whose first
//! universe holds the naturals, which every tower built from
//! `UniverseTower.empty` by `UniverseTower.extend` does; Revision 2's reading of
//! the iota clause is false there; the receipt of an accepted theorem is
//! inhabited and its sorts are inside the tower, and a valid environment with a
//! theorem entry inhabits that lemma's hypotheses; a checker that accepts the
//! re-check's V1 declaration (`theorem t : Sort 4 -> False` at bound 0) is not
//! sound at the height-3 tower, though V1 meets every clause Revision 3 had;
//! the consumer's corollary to `formula.holds` holds over a rooted environment,
//! and every handle a run from `Env.base` returns is rooted and valid; Revision
//! 4's walk lemma is false; a recursor stored with too few binders is refused
//! by `FamilyValid.arity`; and under a binder of type `Sort 4 -> Prop` a
//! `Setting` exists. It also checks seven checker-independent C3 bridges
//! (`ann_extend`, `value_inst`, `ann_inst`, `ann_instLevels`,
//! `ann_closed_transport`, `value_scope_transport`, and `walkTele_inTele`).
//! What it does not show: any step theorem (unit C3) or the landed C2 checker
//! itself.

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsStr;
use std::path::Path;
use std::process::Command;

use clean_kernel::env::{ConstantInfo, Declaration, Environment};
use clean_kernel::{Expr, KernelEnvError, KernelTypeError, Name, ReferenceRefusal};
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::{
    load_module_with_deps, read_artifact, reference_base_closed, require_pinned_lean_lib_path,
    ArtifactDepth,
};
use sha2::{Digest, Sha256};

/// The module that imports every other module of the package.
const ROOT: &str = "KCheckSpec.Contracts";

/// `(theorem, statement pin in KCheckSpec.Contracts)`.
const CONTRACTS: &[(&str, &str)] = &[
    (
        "KCheckSpec.Base.signature_eq_family",
        "baseSignatureEqFamily",
    ),
    (
        "KCheckSpec.Base.signature_punit_family",
        "baseSignaturePUnitFamily",
    ),
    (
        "KCheckSpec.Base.signature_nat_family",
        "baseSignatureNatFamily",
    ),
    (
        "KCheckSpec.Base.signature_constructor_payloads",
        "baseSignatureConstructors",
    ),
    (
        "KCheckSpec.Base.signature_family_headers",
        "baseSignatureFamilyHeaders",
    ),
    ("KCheckSpec.Base.signature_entry_type", "baseSignatureTypes"),
    (
        "KCheckSpec.Base.signature_assignment",
        "baseSignatureAssignment",
    ),
    (
        "KCheckSpec.Base.signature_semantic_bridge",
        "baseSignatureBridge",
    ),
    (
        "KCheckSpec.Base.signature_wrong_type_refused",
        "baseSignatureWrongType",
    ),
    ("CICL.Model.quote_correct", "quotationCorrect"),
    ("CICL.Model.quote_witness", "quotationWitness"),
    ("CICL.Model.quote_sound", "quotationSound"),
    ("CICL.Model.quote_closed", "quotationClosed"),
    ("CICL.Model.quote_base_names", "quotationBaseNames"),
    ("CICL.Model.quoted_false_refuted", "quotationRefutesFalse"),
    ("CICL.Model.quoted_identity", "quotationIdentity"),
    ("CICL.Model.quoted_equality", "quotationEquality"),
    ("CICL.Model.quoted_universal", "quotationUniversal"),
    ("KCheckSpec.Base.base_valid", "baseValid"),
    ("KCheckSpec.Base.base_valid_extend", "baseValidExtend"),
    ("KCheckSpec.Base.HasNat.extend", "hasNatExtend"),
    ("KCheckSpec.Base.base_ready_two", "baseReadyTwo"),
    ("KCheckSpec.Base.base_ready_three", "baseReadyThree"),
    ("KCheckSpec.Base.conflated_false", "conflatedFalse"),
    ("KCheckSpec.kcheck_accepts_true_N", "acceptsTrue"),
    ("KCheckSpec.receipt_sound", "receiptSound"),
    ("KCheckSpec.step_sound", "stepSound"),
    ("KCheckSpec.Rooted.extend", "rootedExtend"),
    ("KCheckSpec.Base.v1_extends", "v1Extends"),
    ("KCheckSpec.Base.v1_refused", "v1Refused"),
    ("KCheckSpec.Base.v1_unsound", "v1Unsound"),
    ("KCheckSpec.Base.v1Checker_unsound", "v1CheckerUnsound"),
    ("KCheckSpec.Base.rooted_receipt_holds", "rootedHolds"),
    // Revision 5.
    (
        "KCheckSpec.Contracts.not_forged_v1Sound",
        "notForgedV1Sound",
    ),
    (
        "KCheckSpec.Contracts.not_forged_conflatedHolds",
        "notForgedConflatedHolds",
    ),
    ("KCheckSpec.Base.v1_rev3_clauses", "v1Rev3Clauses"),
    (
        "KCheckSpec.Base.walkTele_inTele_rev4_false",
        "walkTeleInTeleRev4False",
    ),
    ("KCheckSpec.Base.overrun_tele_false", "overrunTeleFalse"),
    ("KCheckSpec.Base.overrun_invalid", "overrunInvalid"),
    ("KCheckSpec.Base.inner_setting", "innerSetting"),
    ("KCheckSpec.Base.run_rooted_valid", "runRootedValid"),
    ("KCheckSpec.Witness.idEnv_valid", "idEnvValid"),
    ("KCheckSpec.Witness.receipt_nonvacuous", "receiptNonvacuous"),
    ("KCheckSpec.receipt_unique", "receiptUnique"),
    ("KCheckSpec.Env.Valid.bounded", "validBounded"),
    ("KCheckSpec.Term.sortsWithin_inst", "sortsWithinInst"),
    ("KCheckSpec.sortsWithin_instLevels", "sortsWithinInstLevels"),
    ("KCheckSpec.citesWithin_inst", "citesWithinInst"),
    ("KCheckSpec.citesWithin_instLevels", "citesWithinInstLevels"),
    ("KCheckSpec.Term.sortsWithin_openAt", "sortsWithinOpenAt"),
    ("KCheckSpec.citesWithin_openAt", "citesWithinOpenAt"),
    ("KCheckSpec.value_instLevels", "valueInstLevels"),
    ("KCheckSpec.value_inst_proved", "valueInstBridge"),
    ("KCheckSpec.ann_extend_proved", "annExtendBridge"),
    ("KCheckSpec.ann_inst_proved", "annInstBridge"),
    ("KCheckSpec.ann_instLevels_proved", "annInstLevelsBridge"),
    (
        "KCheckSpec.ann_closed_transport_proved",
        "annClosedTransportBridge",
    ),
    (
        "KCheckSpec.value_scope_transport_proved",
        "valueScopeTransportBridge",
    ),
    ("KCheckSpec.walkTele_inTele_proved", "walkTeleInTeleBridge"),
    ("KCheckSpec.walkTele_inTele.fits", "walkTeleFits"),
];

/// `(real proof, statement nobody proves)`.
const FORGED_STATEMENTS: &[(&str, &str)] = &[
    (
        "KCheckSpec.Base.signature_entry_type",
        "forged_baseSignatureTypes",
    ),
    (
        "KCheckSpec.Base.signature_wrong_type_refused",
        "forged_baseSignatureWrongType",
    ),
    ("CICL.Model.quoted_identity", "forged_quotationFalse"),
    ("KCheckSpec.Base.base_valid", "forged_baseValidAnyTower"),
    ("KCheckSpec.Base.conflated_false", "forged_conflatedHolds"),
    ("KCheckSpec.kcheck_accepts_true_N", "forged_acceptsAnyEntry"),
    ("KCheckSpec.receipt_sound", "forged_receiptAnyKind"),
    ("KCheckSpec.Base.v1_unsound", "forged_v1Sound"),
    (
        "KCheckSpec.Base.rooted_receipt_holds",
        "forged_holdsUnrooted",
    ),
];

/// The definitions C2 and C3 are written against. A structure is pinned by its
/// constructor, an inductive type by its constructors, a definition by its type
/// and value together.
const SPECIFICATION: &[&str] = &[
    "KCheckSpec.Base.signatureEntry",
    "KCheckSpec.Base.SignatureFamilyMatches",
    "CICL.Model.NatTerm.quote",
    "CICL.Model.FormulaAt.quoteAt",
    "CICL.Model.Formula.quote",
    "KCheckSpec.Term.bvar",
    "KCheckSpec.Term.local",
    "KCheckSpec.Term.sort",
    "KCheckSpec.Term.const",
    "KCheckSpec.Term.app",
    "KCheckSpec.Term.lam",
    "KCheckSpec.Term.pi",
    "KCheckSpec.Term.letE",
    "KCheckSpec.Term.toExpr",
    "KCheckSpec.Term.Scoped",
    "KCheckSpec.Term.openAt",
    "KCheckSpec.Term.inst",
    "KCheckSpec.Term.instLevels",
    "KCheckSpec.Term.SortsWithin",
    "KCheckSpec.Term.piArity",
    "KCheckSpec.Term.dropPis",
    "KCheckSpec.Term.instPis",
    "KCheckSpec.Term.spineArgs",
    "KCheckSpec.spine",
    "KCheckSpec.Report.mk",
    "KCheckSpec.Report.eval",
    "KCheckSpec.Report.Extends",
    "KCheckSpec.EntryKind.definition",
    "KCheckSpec.EntryKind.theoremDecl",
    "KCheckSpec.EntryKind.opaqueDecl",
    "KCheckSpec.EntryKind.familyConstant",
    "KCheckSpec.Entry.mk",
    "KCheckSpec.Rule.mk",
    "KCheckSpec.Family.mk",
    "KCheckSpec.Env.mk",
    "KCheckSpec.Env.find",
    "KCheckSpec.Term.namesIn",
    "KCheckSpec.Env.Scoped",
    "KCheckSpec.Family.names",
    "KCheckSpec.Term.CitesWithin",
    "KCheckSpec.Term.Bounded",
    "KCheckSpec.Env.Bounded",
    "KCheckSpec.Base.mk",
    "KCheckSpec.Base.assignment",
    "KCheckSpec.Entry.define",
    "KCheckSpec.Env.assignment",
    "KCheckSpec.value",
    "KCheckSpec.Ann",
    "KCheckSpec.CtxEntry.mk",
    "KCheckSpec.Satisfies",
    "KCheckSpec.Context.Scoped",
    "KCheckSpec.pushAll",
    "KCheckSpec.RelatedList",
    "KCheckSpec.InTele",
    "KCheckSpec.Context.Bounded",
    "KCheckSpec.closedValue",
    "KCheckSpec.EntryValid.mk",
    "KCheckSpec.RuleValid.mk",
    "KCheckSpec.KValid",
    "KCheckSpec.FamilyValid.mk",
    "KCheckSpec.Env.Valid.mk",
    "KCheckSpec.Setting.mk",
    "KCheckSpec.stripped",
    "KCheckSpec.OrdinaryMatches",
    "KCheckSpec.BlockMatches",
    "KCheckSpec.Receipt.mk",
    "KCheckSpec.Receipt.of",
    "KCheckSpec.Extends",
    "KCheckSpec.Checker.mk",
    "KCheckSpec.Loader.mk",
    "KCheckSpec.Checker.step",
    "KCheckSpec.Checker.StartsAtBase",
    "KCheckSpec.Checker.runStep",
    "KCheckSpec.Checker.run",
    "KCheckSpec.whnf_sound",
    "KCheckSpec.conv_sound",
    "KCheckSpec.inferAnn_sound",
    "KCheckSpec.check_sound",
    "KCheckSpec.walk_sound",
    "KCheckSpec.walk_sound.WalkTele",
    "KCheckSpec.block_sound",
    "KCheckSpec.whnf_bounded",
    "KCheckSpec.inferAnn_bounded",
    "KCheckSpec.check_bounded",
    "KCheckSpec.report_upper_bound",
    "KCheckSpec.kcheck_sound_N",
    "KCheckSpec.kcheck_sound",
    "KCheckSpec.ann_extend",
    "KCheckSpec.ann_inst",
    "KCheckSpec.value_inst",
    "KCheckSpec.ann_instLevels",
    "KCheckSpec.ann_closed_transport",
    "KCheckSpec.value_scope_transport",
    "KCheckSpec.walkTele_inTele",
    "KCheckSpec.C3Owes",
    "KCheckSpec.Rooted",
    "KCheckSpec.Env.base",
    "KCheckSpec.Base.entries",
    "KCheckSpec.Base.families",
    "KCheckSpec.Base.QuoteSound",
    "KCheckSpec.Base.WalkTeleInTeleRev4",
];

/// Interface definitions supplied by dependencies: preserve their pins and require
/// their exact origin, without counting them as specification-owned subjects.
const IMPORTED_SPECIFICATION: &[(&str, &str)] = &[
    ("KCheckSpec.Mem", "CICLModel.BaseRaw"),
    ("KCheckSpec.applyN", "CICLModel.BaseRaw"),
    ("KCheckSpec.pad", "CICL.ListSupport"),
];

fn name(s: &str) -> Name {
    Name::from_string(s)
}

/// The module stems of `theories/kcheck_spec/ORDER`.
fn order_stems() -> Vec<&'static str> {
    include_str!("../../../theories/kcheck_spec/ORDER")
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

/// Revision 4, finding LE-1 of the re-check of Revision 3: the package's own
/// `lake build`, cold. The package is copied without its `.lake` directory
/// beside links to the two packages it requires, so no module of
/// `kcheck_spec` is built and Lake must find every import of
/// `KCheckSpec.Contracts` in the library. The control is the lakefile Revision
/// 3 landed, whose only root was that module: Lake does not count the other
/// modules as the library's, and its cold build fails at an import's missing
/// object file.
fn cold_lake_build(bin: &Path, binary_path: &OsStr) {
    let theories = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../theories")
        .canonicalize()
        .expect("theories directory");
    let lakefile = std::fs::read_to_string(theories.join("kcheck_spec/lakefile.toml"))
        .expect("kcheck_spec lakefile.toml");
    for stem in order_stems() {
        let module = stem.replace('/', ".");
        assert!(
            lakefile.contains(&format!("\"{module}\"")),
            "theories/kcheck_spec/lakefile.toml lists {module} as a root"
        );
    }
    let one_root: String = lakefile
        .lines()
        .map(|line| {
            if line.starts_with("roots = ") {
                "roots = [\"KCheckSpec.Contracts\"]"
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
        let package = scratch.path().join("kcheck_spec");
        copy_package(&theories.join("kcheck_spec"), &package);
        std::fs::write(package.join("lakefile.toml"), text).expect("write lakefile.toml");
        for dependency in ["cic_l", "cic_l_model"] {
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
                output.contains("of module KCheckSpec.") && output.contains("does not exist"),
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
fn kcheck_spec_rechecks_through_two_kernels_with_pinned_statements() {
    let lib = require_pinned_lean_lib_path().expect("install the repository-pinned Lean toolchain");
    let compiled = compiled_fixture_dir("kcheck_spec");
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean binary");
    let bin = lean.parent().expect("Lean bin directory");
    let mut paths = vec![bin.to_path_buf()];
    paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));
    let binary_path = std::env::join_paths(paths).expect("binary path");
    cold_lake_build(bin, &binary_path);

    // Kernel one: Lean's own, replaying the root module and everything below
    // it from nothing.
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
        .expect("load the compiled specification");

    // The subjects are the constants the package's own modules declare, read
    // from each artifact's name table, as in `kcheck_core.rs`: a `CICL.*`
    // constant is never counted as the specification's, and a compiler's
    // `unsafe` copy must be marked so by its own artifact.
    let stems = order_stems();
    assert_eq!(
        stems.len(),
        15,
        "module denominator of theories/kcheck_spec/ORDER"
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
            assert!(
                !loaded.is_unsafe(constant) && !loaded.is_partial(constant),
                "{module} declares {constant} unsafe or partial"
            );
            assert!(
                targets.insert(constant.clone()),
                "{constant} is declared by two modules"
            );
        }
        eprintln!("module {module}: {} constants", artifact.names.len());
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

    // Axiom closures. `Classical.choice` is admitted only where the committed
    // closure names it: the indexed-union lemmas of the model use it, the
    // base environment's validity does not.
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
        if *theorem == "KCheckSpec.Base.HasNat.extend" {
            assert!(!targets.contains(&subject), "{theorem} must be model-owned");
            assert_eq!(
                loaded
                    .get_constant_origin(&subject)
                    .and_then(|origin| origin.module_name()),
                Some("CICLModel.BaseTower"),
                "{theorem} has the wrong dependency origin"
            );
            assert!(kernel.environment().get_const(&subject).is_some());
        } else {
            assert!(targets.contains(&subject), "missing theorem {theorem}");
        }
        let closure = closure_of(kernel.environment(), &subject);
        assert!(closure.is_subset(&allowed), "{theorem}: {closure:?}");
        observed_closures.insert((*theorem).to_owned(), closure);
    }
    for (subject, closure) in &observed_closures {
        eprintln!("axiom-closure {subject} {closure:?}");
    }

    // Statement and specification pins. Every digest is printed before any is
    // compared, so one run of a changed set shows all of them.
    let statement = |pin: &str| -> Expr {
        loaded
            .get_const(&name(&format!("KCheckSpec.Contracts.{pin}")))
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
    for (object, imported_from) in SPECIFICATION.iter().map(|object| (*object, None)).chain(
        IMPORTED_SPECIFICATION
            .iter()
            .map(|(object, module)| (*object, Some(*module))),
    ) {
        let subject = name(object);
        if let Some(module) = imported_from {
            assert!(
                !targets.contains(&subject),
                "{object} must remain dependency-owned"
            );
            assert_eq!(
                loaded
                    .get_constant_origin(&subject)
                    .and_then(|origin| origin.module_name()),
                Some(module),
                "{object} has the wrong dependency origin"
            );
            assert!(
                kernel.environment().get_const(&subject).is_some(),
                "{object} was not reference-admitted as a dependency"
            );
        } else {
            assert!(targets.contains(&subject), "{object} is not a subject");
        }
        let constant = loaded.get_const(&subject).expect("resident subject");
        assert!(
            observed_pins
                .insert(object.to_owned(), constant_digest(constant))
                .is_none(),
            "{object} is listed twice"
        );
    }
    for (pin, value) in &observed_pins {
        eprintln!("statement-pin {pin} {value}");
    }
    assert_eq!(
        observed_pins.len(),
        CONTRACTS.len()
            + FORGED_STATEMENTS.len()
            + SPECIFICATION.len()
            + IMPORTED_SPECIFICATION.len(),
        "pin denominator"
    );
    let committed_closures: BTreeMap<String, BTreeSet<String>> = serde_json::from_str(
        include_str!("../../../theories/kcheck_spec/axiom_closures.json"),
    )
    .expect("committed axiom closures");
    let committed_pins: BTreeMap<String, String> = serde_json::from_str(include_str!(
        "../../../theories/kcheck_spec/statement_pins.json"
    ))
    .expect("committed statement pins");
    assert_eq!(
        observed_closures, committed_closures,
        "observed axiom closures differ from theories/kcheck_spec/axiom_closures.json"
    );
    assert_eq!(
        observed_pins, committed_pins,
        "observed statements differ from theories/kcheck_spec/statement_pins.json"
    );

    // Each theorem's own proof is admitted at the statement pinned for it, and
    // refused at `False`.
    for (theorem, pin) in CONTRACTS {
        let proof = loaded.get_const(&name(theorem)).expect("pinned theorem");
        let value = proof.value.clone().expect("the theorem has a proof");
        kernel
            .add_checked(Declaration::Theorem {
                name: name(&format!("KCheckSpec.Controls.{pin}_positive")),
                level_params: proof.level_params.clone(),
                type_: statement(pin),
                value: value.clone(),
            })
            .unwrap_or_else(|refusal| {
                panic!("{theorem} at its pinned statement {pin}: {refusal:?}")
            });
        let bad = kernel.add_checked(Declaration::Theorem {
            name: name(&format!("KCheckSpec.Controls.{pin}_false")),
            level_params: proof.level_params.clone(),
            type_: Expr::const_(name("False"), vec![]),
            value,
        });
        assert!(
            is_type_mismatch(&bad),
            "{theorem} at False must fail by type mismatch: {bad:?}"
        );
    }

    // A real proof is refused at a statement it does not prove.
    for (theorem, forged) in FORGED_STATEMENTS {
        let proof = loaded.get_const(&name(theorem)).expect("pinned theorem");
        let bad = kernel.add_checked(Declaration::Theorem {
            name: name(&format!("KCheckSpec.Controls.{forged}")),
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
        "kcheck_spec subjects {}, modules {}, contracts {}, forged statements {}, \
         specification pins {}",
        targets.len(),
        stems.len(),
        CONTRACTS.len(),
        FORGED_STATEMENTS.len(),
        SPECIFICATION.len() + IMPORTED_SPECIFICATION.len()
    );
}
