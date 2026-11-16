// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The CIC_L qualification test, and what a pass is evidence OF (self-proof
//! plan units E1 and E2).
//!
//! The `#[test]` is here, not beside the hand tables in `cic_l_level.rs`: this
//! file is what `data/gate_registry.json` pins (row `cic-l-qualification`), so
//! what a pass means cannot change without the row going stale, while a new
//! theorem in the tables moves no pin. The test first checks the Lean its
//! inputs name, then compiles the theory with pinned Lean, has Lean's own
//! kernel replay it, re-admits it through the fenced reference entry, runs
//! the checks below, and then hands the kernel to the tables' rule witnesses
//! and forged-statement controls.
//!
//! Every check this file makes is a function over plain data returning a
//! [`Refusal`], and every one is run again on a planted defect and must refuse
//! with the variant and the names it states: [`input_controls`],
//! [`selection_controls`], [`negative_controls`] and [`census_controls`]. Each
//! control runs after its check passed on the real theory, so no control can
//! pass because its check refuses everything. Not this file's checks, and so
//! not planted here: the verdicts of Lean's kernel (`leanchecker --fresh`) and
//! of the reference entry, which the registry row's arms demonstrate on a
//! mutated theory (an added private axiom is refused by the entry).
//!
//! * **The Lean.** The package's `lean-toolchain` is the workspace pin, so
//!   `lake build` and this test compile the theory with one Lean, and E7's
//!   census below was minted with that Lean. Both are read before anything
//!   compiles, so a mismatch refuses first.
//! * **Module of origin.** The targets are the names each theory module's own
//!   `.olean` declares, read with [`clean_olean::read_artifact`], and not the
//!   constants whose name begins `CICL.`: Lean stores a `private` declaration
//!   under `_private.<module>.0.<name>`, so a name filter never made one a
//!   direct target. The one exclusion is what a module stores as `unsafe` or
//!   `partial`, which Lean's replay never admits and the loader leaves out;
//!   here that may only be an `_unsafe_rec` compiler auxiliary, and any other
//!   such declaration refuses. The selection partitions the declared names
//!   (each stored-unsafe name is declared, and each declared name is a target
//!   or stored-unsafe, never both), and it keeps every constant the loader
//!   holds under the old `CICL.` filter: the two readers, the artifact's
//!   declared names and the loader's environment, must agree.
//! * **`ORDER`.** The modules reached from this test's root are exactly the
//!   `ORDER` entries, so a module that is compiled but imported by nothing the
//!   test loads is a refusal. The lakefile's roots are `ORDER`'s modules, so
//!   `lake build` covers the same modules. The model is a package of its own
//!   (`theories/cic_l_model`) with its own test.
//! * **Statements.** `statement_pins.json` holds one meaning digest per
//!   theorem the level modules declare, private ones included: a theorem with
//!   no pin, a pin with no theorem and a theorem whose meaning moved each
//!   refuse. The digest (`../support/meaning_digest.rs`, shared with the
//!   model's and kcheck's tests) binds the stated type and universe parameters
//!   AND every definition, inductive and compiler auxiliary of the package the
//!   statement reaches, down to Init; it binds no proof. Every other target
//!   has the same digest in `definition_pins.json` (`definition_pins.rs`),
//!   and both files are compared before either refuses. The package is
//!   `theories/cic_l`, the one theory the fixture family `cic_l_level`
//!   compiles, selected by module of origin. This file pins the digest's
//!   source by its SHA-256, so the definition of a pin cannot change without
//!   this file, and the registry row that pins it, moving. Re-pin both files
//!   with one command, `CLEAN_REPIN_STATEMENT_PINS=1 scripts/heavy_gate.sh run
//!   16 cic-l-level-repin -- "$(rustup run trust rustc --print sysroot)/bin/targo"
//!   --unverified test -p clean-olean --locked --test cic_l_level
//!   level_theory_rechecks_with_false_computation_controls`: the run rewrites
//!   each file that differs and still fails, and the next run without the
//!   variable confirms.
//! * **Axioms.** The union of every target's axiom closure equals
//!   [`OBSERVED_AXIOM_CLOSURE`]. It is a ratchet in both directions: a closure
//!   that reaches anything else refuses, and so does a pinned name nothing
//!   reaches (the old allow-list admitted `Classical.choice`, which no closure
//!   here uses).
//! * **E7's census.** `data/lean_axiom_census.json` (plan unit E7, gate
//!   `check_lean_axiom_census`) records, per declaration of these modules,
//!   the closure Lean's own `collectAxioms` reports. This test registers no
//!   census of its own; it requires the census to describe what the reference
//!   replay admitted. It names each declaration once (keyed by name, a second
//!   row would silently replace the first), it names the same declarations as
//!   the selection, and its union is
//!   [`OBSERVED_AXIOM_CLOSURE`] as Lean names axioms (Lean counts no quotient
//!   former, `Quot`, `Quot.mk`, `Quot.lift` or `Quot.ind`, as one). Per
//!   target the census is bounded on both sides by walks of the admitted
//!   declaration: it contains the kernel's own closure, so a census row cannot
//!   hide an axiom the kernel sees, and it is contained in everything Lean's
//!   rule reaches ([`lean_rule_closures`]), so it names no axiom the admitted
//!   declaration cannot reach. Neither bound is equality, by rule: Lean enters
//!   an inductive's constructors wherever it meets the inductive and the
//!   kernel's walk does not; and pinned Lean's `collectAxioms` marks a
//!   constant it is still collecting with an empty sentinel, so through an
//!   inductive and its constructors, which reach each other, a row can miss
//!   what a full walk reaches.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt;
use std::path::Path;
use std::process::Command;

use clean_kernel::env::{Declaration, Environment};
use clean_kernel::expr::UsedConstants;
use clean_kernel::{BinderInfo, ConstantKind, Expr, Level, Name, QuotKind, TheoryId};
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::{
    load_module_with_deps, parse_module_file, read_artifact, reference_base_closed,
    require_pinned_lean_lib_path, ArtifactDepth, ConstantKind as StoredKind, DefinitionSafety,
};
use sha2::{Digest, Sha256};

use super::definition_pins;
use super::{rule_witnesses_and_forged_controls, THEOREMS, THEORY_ROOT};

/// The meaning digest every statement pin uses, shared with the model's and
/// kcheck's qualification tests.
#[path = "../support/meaning_digest.rs"]
pub(crate) mod meaning_digest;

use meaning_digest::{MeaningDigests, Package};

/// The digest's source, which this file pins (see [`check_digest_source`]).
const MEANING_DIGEST_SOURCE: &[u8] = include_bytes!("../support/meaning_digest.rs");

/// The SHA-256 of `../support/meaning_digest.rs`. The registry row
/// `cic-l-qualification` pins this file and no other, so this file pins that
/// one: an edit to what a pin means refuses here until this line moves, and
/// moving it stales the row, whose re-pin replays its arms.
const MEANING_DIGEST_SOURCE_SHA256: &str =
    "0a53b73d9d0932c17f8955432fcd20ecde87b124622bee998fe1db03dd15eacb";

/// The fixture family whose compiled directory the test loads.
const FAMILY: &str = "cic_l_level";

/// The package the statement pins' closures range over: the theories the
/// fixture family compiles.
const PACKAGE_THEORIES: &[&str] = &["cic_l"];

/// The committed pin file, relative to the workspace root.
const PIN_FILE: &str = "crates/clean-olean/tests/cic_l_level/statement_pins.json";

/// The theory's compile order: one module stem per line.
const ORDER: &str = include_str!("../../../../theories/cic_l/ORDER");

/// The package's own module list, which `lake build` follows.
const LAKEFILE: &str = include_str!("../../../../theories/cic_l/lakefile.toml");

/// The Lean the package names, and the Lean this workspace compiles it with.
const THEORY_TOOLCHAIN: &str = include_str!("../../../../theories/cic_l/lean-toolchain");
const WORKSPACE_TOOLCHAIN: &str = include_str!("../../../../lean-toolchain");

/// One digest per theorem of the level modules, keyed by its printed name.
const STATEMENT_PINS: &str = include_str!("statement_pins.json");

/// Every value-less constant some target's closure reaches, as the kernel's
/// closure walk names them and as measured on 2026-11-12: `propext`, and the
/// quotient primitives with `Quot.sound` (`Quot.ind` is not reached).
/// `Classical.choice` is absent because nothing here uses it; a proof that
/// starts to is refused until this list, and a decision entry, say so.
pub(crate) const OBSERVED_AXIOM_CLOSURE: &[&str] =
    &["Quot", "Quot.lift", "Quot.mk", "Quot.sound", "propext"];

/// E7's census of the three Lean packages, minted by
/// `scripts/check_lean_axiom_census.py --mint`.
const LEAN_AXIOM_CENSUS: &str = include_str!("../../../../data/lean_axiom_census.json");

/// The census package whose rows are this theory's declarations.
const CENSUS_PACKAGE: &str = "cic_l";

/// Why a check refused. One variant per stated reason, so a negative control
/// can require the reason and not merely a failure.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Refusal {
    /// The package's `lean-toolchain` is not the workspace pin.
    ToolchainPin { theory: String, workspace: String },
    /// The meaning digest's source is not the one this file pins.
    DigestSource { measured: String, pinned: String },
    /// E7's census was minted with another Lean than the theory names.
    CensusToolchain { census: String, theory: String },
    /// E7's census has more than one row for a declaration.
    CensusDuplicateRows { names: Vec<String> },
    /// The selection does not partition the declared names.
    Selection {
        /// Stored as `unsafe` or `partial` by a level module whose own
        /// artifact does not declare it.
        unsafe_not_declared: Vec<String>,
        /// Declared, not stored-unsafe, and no target.
        dropped: Vec<String>,
        /// A target that is not declared, or is stored-unsafe.
        stray: Vec<String>,
    },
    /// A constant the loader holds under the old `CICL.` name filter is no
    /// target.
    PrefixFilterLost { names: Vec<String> },
    /// The modules reached from the root are not the `ORDER` entries.
    Order {
        /// Listed in `ORDER`, not reached from the root.
        listed_not_loaded: Vec<String>,
        /// Reached from the root, absent from `ORDER`.
        loaded_not_listed: Vec<String>,
    },
    /// The lakefile's library roots are not `ORDER`'s modules.
    LakefileRoots {
        /// In `ORDER`, absent from the lakefile's roots.
        listed_not_root: Vec<String>,
        /// A lakefile root `ORDER` does not list.
        root_not_listed: Vec<String>,
    },
    /// A level module stores an `unsafe` or `partial` declaration that is not
    /// one of Lean's `_unsafe_rec` compiler auxiliaries.
    NotReplayable { names: Vec<String> },
    /// A name a level module declares is not resident after the load or the
    /// reference replay.
    NotResident {
        stage: &'static str,
        names: Vec<String>,
    },
    /// The theorem inventory and the statement pins disagree.
    Statements {
        /// Theorems the modules declare that carry no pin.
        unlisted: Vec<String>,
        /// Pins whose theorem the modules no longer declare.
        missing: Vec<String>,
        /// Theorems whose statement digest is not the pinned one.
        changed: Vec<String>,
    },
    /// A hand-table entry is not a theorem the level modules declare.
    HandTable { names: Vec<String> },
    /// A closure reaches an axiom outside the observed set.
    OutsideObservedClosure { subject: String, extra: Vec<String> },
    /// The pinned set names an axiom no closure reaches.
    ObservedClosureUnused { unused: Vec<String> },
    /// E7's census and the module-of-origin selection name different
    /// declarations.
    CensusInventory {
        /// A census row for a name no level module declares.
        census_only: Vec<String>,
        /// A declared name the census has no row for.
        test_only: Vec<String>,
    },
    /// A census row names an axiom Lean's rule cannot reach from the admitted
    /// declaration, one line per declaration.
    CensusBeyondReach { disagreements: Vec<String> },
    /// The kernel's walk reaches an axiom the census does not list for that
    /// declaration, one line per declaration.
    KernelBeyondCensus { disagreements: Vec<String> },
    /// The union of the census's closures is not the observed set, both named
    /// as Lean names axioms.
    CensusUnion {
        census: Vec<String>,
        observed: Vec<String>,
    },
}

impl fmt::Display for Refusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ToolchainPin { theory, workspace } => write!(
                f,
                "theories/cic_l/lean-toolchain names {theory:?}, the workspace pins {workspace:?}: \
                 `lake build` and this test would compile the theory with different Leans"
            ),
            Self::DigestSource { measured, pinned } => write!(
                f,
                "tests/support/meaning_digest.rs has SHA-256 {measured}, this file pins \
                 {pinned}: what a statement pin means changed; move MEANING_DIGEST_SOURCE_SHA256 \
                 with a decision entry, re-pin the four pin files and the registry row \
                 `cic-l-qualification`"
            ),
            Self::CensusToolchain { census, theory } => write!(
                f,
                "the census was minted with {census:?}, the theory names {theory:?}: re-mint it \
                 with `python3 scripts/check_lean_axiom_census.py --mint` under the theory's Lean"
            ),
            Self::CensusDuplicateRows { names } => {
                write!(f, "the census names a declaration twice: {names:?}")
            }
            Self::Selection {
                unsafe_not_declared,
                dropped,
                stray,
            } => write!(
                f,
                "the selection does not partition the declared names: stored unsafe but not \
                 declared {unsafe_not_declared:?}; declared but neither a target nor stored \
                 unsafe {dropped:?}; a target not declared or stored unsafe {stray:?}"
            ),
            Self::PrefixFilterLost { names } => write!(
                f,
                "module-of-origin selection lost names the `CICL.` prefix filter had: {names:?}"
            ),
            Self::Order {
                listed_not_loaded,
                loaded_not_listed,
            } => write!(
                f,
                "ORDER mismatch: listed but not loaded {listed_not_loaded:?}; loaded but not \
                 listed {loaded_not_listed:?}"
            ),
            Self::LakefileRoots {
                listed_not_root,
                root_not_listed,
            } => write!(
                f,
                "lakefile roots mismatch: in ORDER but not a root {listed_not_root:?}; a root \
                 but not in ORDER {root_not_listed:?}"
            ),
            Self::NotReplayable { names } => write!(
                f,
                "a level module stores an unsafe or partial declaration that is no \
                 `_unsafe_rec` compiler auxiliary: {names:?}"
            ),
            Self::NotResident { stage, names } => {
                write!(
                    f,
                    "declared by a level module but not resident after {stage}: {names:?}"
                )
            }
            Self::Statements {
                unlisted,
                missing,
                changed,
            } => write!(
                f,
                "statement pins: unlisted theorem {unlisted:?}; pinned theorem missing \
                 {missing:?}; statement changed {changed:?}"
            ),
            Self::HandTable { names } => {
                write!(
                    f,
                    "hand table names no theorem of the level modules: {names:?}"
                )
            }
            Self::OutsideObservedClosure { subject, extra } => write!(
                f,
                "axiom closure of {subject} reaches {extra:?}, outside the observed set \
                 {OBSERVED_AXIOM_CLOSURE:?}"
            ),
            Self::ObservedClosureUnused { unused } => write!(
                f,
                "the observed axiom set pins {unused:?}, which no closure reaches: tighten it"
            ),
            Self::CensusInventory {
                census_only,
                test_only,
            } => write!(
                f,
                "census inventory: rows no level module declares {census_only:?}; declarations \
                 with no census row {test_only:?} (re-mint with `python3 \
                 scripts/check_lean_axiom_census.py --mint` after a theory change)"
            ),
            Self::CensusBeyondReach { disagreements } => write!(
                f,
                "the census names an axiom Lean's rule cannot reach from the admitted \
                 declaration: {disagreements:#?}"
            ),
            Self::KernelBeyondCensus { disagreements } => write!(
                f,
                "the kernel's closure walk reaches beyond the census: {disagreements:#?}"
            ),
            Self::CensusUnion { census, observed } => write!(
                f,
                "census union {census:?} is not the observed set {observed:?}, both without \
                 the quotient formers"
            ),
        }
    }
}

/// A refusal of the real theory fails the test with the reason it states.
fn hold<T>(checked: Result<T, Refusal>) -> T {
    checked.unwrap_or_else(|refusal| panic!("{refusal}"))
}

/// Lean's own kernel replays the compiled theory from its bytes.
fn independent_lean_replay(compiled: &Path, lib: &Path) {
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean binary");
    let bin = lean.parent().expect("Lean bin directory");
    let mut paths = vec![bin.to_path_buf()];
    paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));
    let independent = Command::new(bin.join("leanchecker"))
        .args(["--fresh", THEORY_ROOT])
        .current_dir(compiled)
        .env(
            "LEAN_PATH",
            std::env::join_paths([compiled, lib]).expect("Lean path"),
        )
        .env("PATH", std::env::join_paths(paths).expect("binary path"))
        .output()
        .expect("run pinned independent Lean kernel");
    assert!(
        independent.status.success(),
        "independent replay failed: {}\n{}",
        String::from_utf8_lossy(&independent.stdout),
        String::from_utf8_lossy(&independent.stderr)
    );
}

#[test]
fn level_theory_rechecks_with_false_computation_controls() {
    // The Lean the inputs name, before anything compiles: the package's pin is
    // the workspace's, and E7's census names each declaration once and was
    // minted with that Lean.
    hold(check_toolchain_pin(THEORY_TOOLCHAIN, WORKSPACE_TOOLCHAIN));
    hold(check_digest_source(
        MEANING_DIGEST_SOURCE,
        MEANING_DIGEST_SOURCE_SHA256,
    ));
    let census_document = census_document();
    let (census_toolchain, census) = hold(census_rows(&census_document));
    hold(check_census_toolchain(&census_toolchain, THEORY_TOOLCHAIN));

    let lib = require_pinned_lean_lib_path().expect("install the repository-pinned Lean toolchain");
    let compiled = compiled_fixture_dir(FAMILY);
    independent_lean_replay(&compiled, &lib);

    // The modules, read from the compiled artifacts: this root reaches exactly
    // ORDER's entries, and each module's own artifact says what it declares.
    let order = order_modules();
    hold(check_lakefile_roots(&order, &lakefile_roots()));
    let level_modules = import_closure(&compiled, THEORY_ROOT);
    let level: BTreeSet<String> = level_modules.keys().cloned().collect();
    hold(check_order(&order, &level));
    eprintln!(
        "modules: ORDER lists {}, this root reaches {}",
        order.len(),
        level.len()
    );

    let compiled_dir = compiled.clone();
    let mut loaded = Environment::for_lean_replay();
    load_module_with_deps(&mut loaded, THEORY_ROOT, &[compiled, lib])
        .expect("load the real compiled syntax theory");

    // Every declaration of the level modules that Lean's own replay admits is
    // a direct target, selected by module of origin. What it does not admit is
    // what the module stores as `unsafe` or `partial`, and here that may only
    // be the `_unsafe_rec` twin Lean's compiler keeps of a structural
    // recursion: the loader leaves those out and no safe declaration may use
    // one. The closure builder starts from an empty base; loading above is
    // parsing, never evidence of admission.
    let declared: BTreeSet<Name> = level_modules.values().flatten().cloned().collect();
    let not_replayable = stored_not_replayable(&compiled_dir, level_modules.keys());
    hold(check_not_replayable(&not_replayable));
    let targets: BTreeSet<Name> = declared
        .iter()
        .filter(|name| !not_replayable.contains(&name.to_string()))
        .cloned()
        .collect();
    hold(check_selection(&declared, &not_replayable, &targets));
    hold(check_resident("the .olean load", &loaded, &targets));
    let by_prefix = prefix_filter(&loaded);
    hold(check_prefix_filter_kept(&by_prefix, &targets));
    eprintln!(
        "targets: {} by module of origin, {} of them outside the `CICL.` name filter; {} \
         `_unsafe_rec` compiler auxiliaries are stored unsafe and are no target",
        targets.len(),
        targets.difference(&by_prefix).count(),
        not_replayable.len()
    );
    let checked = reference_base_closed(&loaded, &targets, &ClosedRecheckOptions::default())
        .unwrap_or_else(|refusal| panic!("the reference replay refused: {refusal}"));
    // Each entry refusal in its own words, so a failing run names the reason
    // (an axiom outside the canonical base, a tripwire, a theory exclusion).
    let entry_refusals: Vec<String> = checked
        .entry_refusals
        .iter()
        .map(|(unit, refusal)| format!("{unit}: {refusal}"))
        .collect();
    assert!(
        checked.report.passed() && entry_refusals.is_empty(),
        "{}\nthe reference entry refused: {entry_refusals:#?}",
        checked.report.verdict_sentence(),
    );
    let kernel = checked
        .into_kernel()
        .expect("all reference admissions passed");
    assert_eq!(kernel.theory_id(), TheoryId::LeanReferenceV1);
    let env = kernel.environment();
    hold(check_resident("the reference replay", env, &targets));

    // Statements: every theorem the level modules declare is pinned by its
    // meaning digest over the package, and the hand table names only such
    // theorems. The package, read from the theory's ORDER, is the declared
    // names the import closure read: two readers of one selection.
    let package = Package::of_fixture(&compiled_dir, FAMILY, PACKAGE_THEORIES);
    assert_eq!(
        package.names(),
        &declared,
        "the package by ORDER and the declared names by import closure differ"
    );
    // Every other target is pinned by the same digest in
    // `definition_pins.json`; both files are compared before either refuses,
    // so one re-pin run rewrites both.
    let digests = MeaningDigests::new(env, &package);
    let inventory = theorem_inventory(&digests, env, &targets);
    let definitions =
        definition_pins::non_theorem_inventory(&digests, env, &level_modules, &not_replayable);
    let pins = statement_pins();
    let mut pin_failures = Vec::new();
    if let Err(refusal) = check_statements(&inventory, &pins) {
        pin_failures.push(format!(
            "{refusal}\n{}",
            meaning_digest::record_measured(&inventory, PIN_FILE)
        ));
    }
    if let Err(refusal) =
        definition_pins::check_definition_pins(&definitions, &definition_pins::committed_pins())
    {
        pin_failures.push(format!(
            "the non-theorem meaning pins differ from {}: {refusal:?}\n{}",
            definition_pins::PIN_FILE,
            meaning_digest::record_measured(&definitions, definition_pins::PIN_FILE)
        ));
    }
    assert!(pin_failures.is_empty(), "{}", pin_failures.join("\n"));
    hold(check_hand_table(THEOREMS, &inventory));
    definition_pins::verify_and_run_controls(
        env,
        &level_modules,
        &not_replayable,
        &inventory,
        &definitions,
    );
    let pinned: Vec<Name> = targets
        .iter()
        .filter(|name| {
            env.get_const(name)
                .is_some_and(|c| c.kind == ConstantKind::Theorem)
        })
        .cloned()
        .collect();
    eprintln!(
        "statement pins: {} theorems, {} of them private, {} in the hand table; {} other \
         declarations pinned in {}; {}",
        inventory.len(),
        inventory
            .keys()
            .filter(|n| n.starts_with("_private."))
            .count(),
        THEOREMS.len(),
        definitions.len(),
        definition_pins::PIN_FILE,
        digests
            .describe(&package, &pinned)
            .unwrap_or_else(|error| panic!("{error}"))
    );
    drop(digests);

    // Axioms: a ratchet on the closure every target was observed to have, not
    // an allow-list of what it may have.
    let (kernel_closures, family_members) = hold(check_axiom_ratchet(env, &targets));
    eprintln!(
        "axiom closure: {} targets inside {OBSERVED_AXIOM_CLOSURE:?}, each name of it reached; \
         {family_members} family members carry no constant record",
        kernel_closures.len()
    );

    // E7's census: the same declarations, each row between the kernel's walk
    // and everything Lean's rule reaches over what the replay admitted, and
    // the union the observed set. Every result is printed before the first
    // refusal, so one failing run shows all of them. The census's Lean was
    // checked before the compile.
    let declared_names: BTreeSet<String> = declared.iter().map(ToString::to_string).collect();
    let lean_rule = lean_rule_closures(env, &targets);
    let kernel_named: BTreeMap<String, BTreeSet<String>> = kernel_closures
        .iter()
        .map(|(name, closure)| (name.clone(), as_lean_axioms(env, closure)))
        .collect();
    let observed_named = as_lean_axioms(env, &observed_axioms());
    let census_checks = [
        check_census_inventory(&declared_names, &census).map(|()| 0),
        check_census_within_reach(&lean_rule, &census),
        check_kernel_within_census(&kernel_named, &census),
        check_census_union(&census, &observed_named).map(|()| 0),
    ];
    for refusal in census_checks
        .iter()
        .filter_map(|checked| checked.as_ref().err())
    {
        eprintln!("census: {refusal}");
    }
    let [inventory_ok, reach_ok, kernel_ok, union_ok] = census_checks;
    hold(inventory_ok);
    let census_narrower = hold(reach_ok);
    let kernel_narrower = hold(kernel_ok);
    hold(union_ok);
    eprintln!(
        "census: {} rows of {CENSUS_PACKAGE}, minted with {census_toolchain}, name exactly the \
         declared names ({} are `_unsafe_rec` auxiliaries the replay does not load); for each \
         of {} targets the row contains the kernel's closure (strictly, for {kernel_narrower}) \
         and lies inside what Lean's rule reaches over the replay (strictly, for \
         {census_narrower}); the rows' union is the observed set {observed_named:?}",
        census.len(),
        census.len() - lean_rule.len(),
        lean_rule.len(),
    );

    input_controls(&census_document);
    selection_controls(&declared, &not_replayable, &targets, &by_prefix);
    negative_controls(&loaded, &order, &level, &inventory, &pins, THEOREMS);
    census_controls(&census, &lean_rule, &kernel_named, &observed_named);
    rule_witnesses_and_forged_controls(&loaded, kernel, &package, &inventory, &pins);
}

/// `ORDER`'s stems as module names (`CICL/Level` → `CICL.Level`).
pub(crate) fn order_modules() -> Vec<String> {
    ORDER
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(|stem| stem.replace('/', "."))
        .collect()
}

/// The package names the Lean this workspace pins, so `lake build` and this
/// test compile the theory with one toolchain. Each file is compared without
/// its surrounding whitespace.
pub(crate) fn check_toolchain_pin(theory: &str, workspace: &str) -> Result<(), Refusal> {
    let (theory, workspace) = (theory.trim(), workspace.trim());
    if theory == workspace {
        Ok(())
    } else {
        Err(Refusal::ToolchainPin {
            theory: theory.to_owned(),
            workspace: workspace.to_owned(),
        })
    }
}

/// E7's census was minted with the Lean the theory names: another Lean's
/// `collectAxioms` described other artifacts.
pub(crate) fn check_census_toolchain(census: &str, theory: &str) -> Result<(), Refusal> {
    let (census, theory) = (census.trim(), theory.trim());
    if census == theory {
        Ok(())
    } else {
        Err(Refusal::CensusToolchain {
            census: census.to_owned(),
            theory: theory.to_owned(),
        })
    }
}

/// The quoted module names of the lakefile's `roots = [...]` list.
pub(crate) fn lakefile_roots() -> BTreeSet<String> {
    let list = LAKEFILE
        .lines()
        .find_map(|line| line.trim().strip_prefix("roots"))
        .and_then(|rest| rest.split_once('['))
        .and_then(|(_, rest)| rest.split_once(']'))
        .map(|(list, _)| list)
        .expect("theories/cic_l/lakefile.toml has a one-line `roots = [...]`");
    list.split(',')
        .map(|entry| entry.trim().trim_matches('"').to_owned())
        .filter(|entry| !entry.is_empty())
        .collect()
}

/// The lakefile builds exactly the modules `ORDER` compiles.
pub(crate) fn check_lakefile_roots(
    order: &[String],
    roots: &BTreeSet<String>,
) -> Result<(), Refusal> {
    let listed: BTreeSet<&String> = order.iter().collect();
    let listed_not_root: Vec<String> = order
        .iter()
        .filter(|m| !roots.contains(*m))
        .cloned()
        .collect();
    let root_not_listed: Vec<String> = roots
        .iter()
        .filter(|m| !listed.contains(m))
        .cloned()
        .collect();
    if listed_not_root.is_empty() && root_not_listed.is_empty() {
        Ok(())
    } else {
        Err(Refusal::LakefileRoots {
            listed_not_root,
            root_not_listed,
        })
    }
}

/// Each `CICL` module reached from `root` through compiled import lists, with
/// the names its own artifact declares, in declaration order.
pub(crate) fn import_closure(compiled: &Path, root: &str) -> BTreeMap<String, Vec<Name>> {
    let mut reached = BTreeMap::new();
    let mut pending = vec![root.to_owned()];
    while let Some(module) = pending.pop() {
        if reached.contains_key(&module) {
            continue;
        }
        let path = compiled.join(format!("{}.olean", module.replace('.', "/")));
        let artifact = read_artifact(&module, &path, ArtifactDepth::Names)
            .unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
        pending.extend(
            artifact
                .imports
                .iter()
                .map(|import| import.module_name.clone())
                .filter(|import| import.starts_with("CICL.")),
        );
        reached.insert(module, artifact.names);
    }
    reached
}

/// The root reaches exactly the `ORDER` entries.
pub(crate) fn check_order(order: &[String], level: &BTreeSet<String>) -> Result<(), Refusal> {
    let listed: BTreeSet<&String> = order.iter().collect();
    let listed_not_loaded: Vec<String> = order
        .iter()
        .filter(|m| !level.contains(*m))
        .cloned()
        .collect();
    let loaded_not_listed: Vec<String> = level
        .iter()
        .filter(|m| !listed.contains(m))
        .cloned()
        .collect();
    if listed_not_loaded.is_empty() && loaded_not_listed.is_empty() {
        Ok(())
    } else {
        Err(Refusal::Order {
            listed_not_loaded,
            loaded_not_listed,
        })
    }
}

/// The names the given modules store as `unsafe` or `partial`: the
/// declarations `Lean.Environment.replay` never admits.
pub(crate) fn stored_not_replayable<'a>(
    compiled: &Path,
    modules: impl IntoIterator<Item = &'a String>,
) -> BTreeSet<String> {
    modules
        .into_iter()
        .flat_map(|module| {
            let path = compiled.join(format!("{}.olean", module.replace('.', "/")));
            parse_module_file(&path)
                .unwrap_or_else(|error| panic!("parse {}: {error}", path.display()))
                .constants
        })
        .filter(|c| {
            matches!(
                c.kind,
                StoredKind::Definition | StoredKind::Axiom | StoredKind::Opaque
            ) && matches!(
                c.definition_safety,
                Some(DefinitionSafety::Unsafe | DefinitionSafety::Partial)
            )
        })
        .map(|c| c.name)
        .collect()
}

/// Each stored-unsafe name is an `_unsafe_rec` compiler auxiliary; a
/// hand-written `unsafe` or `partial` declaration is refused.
pub(crate) fn check_not_replayable(names: &BTreeSet<String>) -> Result<(), Refusal> {
    let other: Vec<String> = names
        .iter()
        .filter(|name| name.rsplit('.').next() != Some("_unsafe_rec"))
        .cloned()
        .collect();
    if other.is_empty() {
        Ok(())
    } else {
        Err(Refusal::NotReplayable { names: other })
    }
}

/// The selection partitions what the level modules declare: every name a
/// level module stores as `unsafe` or `partial` is one its own artifact
/// declares (the two readers agree), and every declared name is a target or
/// stored-unsafe, never both.
pub(crate) fn check_selection(
    declared: &BTreeSet<Name>,
    not_replayable: &BTreeSet<String>,
    targets: &BTreeSet<Name>,
) -> Result<(), Refusal> {
    let declared: BTreeSet<String> = declared.iter().map(ToString::to_string).collect();
    let targets: BTreeSet<String> = targets.iter().map(ToString::to_string).collect();
    let unsafe_not_declared: Vec<String> = not_replayable.difference(&declared).cloned().collect();
    let dropped: Vec<String> = declared
        .iter()
        .filter(|name| !targets.contains(*name) && !not_replayable.contains(*name))
        .cloned()
        .collect();
    let stray: Vec<String> = targets
        .iter()
        .filter(|name| !declared.contains(*name) || not_replayable.contains(*name))
        .cloned()
        .collect();
    if unsafe_not_declared.is_empty() && dropped.is_empty() && stray.is_empty() {
        Ok(())
    } else {
        Err(Refusal::Selection {
            unsafe_not_declared,
            dropped,
            stray,
        })
    }
}

/// The constants the loader holds whose printed name begins `CICL.`: the
/// selection this test made before E2.
pub(crate) fn prefix_filter(loaded: &Environment) -> BTreeSet<Name> {
    loaded
        .constants()
        .filter(|c| c.name.to_string().starts_with("CICL."))
        .map(|c| c.name.clone())
        .collect()
}

/// Module-of-origin selection keeps every name the old prefix filter had, so
/// the loader holds no `CICL.` constant this test does not re-admit.
pub(crate) fn check_prefix_filter_kept(
    by_prefix: &BTreeSet<Name>,
    targets: &BTreeSet<Name>,
) -> Result<(), Refusal> {
    let names: Vec<String> = by_prefix
        .difference(targets)
        .map(ToString::to_string)
        .collect();
    if names.is_empty() {
        Ok(())
    } else {
        Err(Refusal::PrefixFilterLost { names })
    }
}

fn resident(env: &Environment, name: &Name) -> bool {
    env.get_const(name).is_some()
        || env.get_inductive(name).is_some()
        || env.get_constructor(name).is_some()
        || env.get_recursor(name).is_some()
}

/// Every one of `names` is resident in `env`.
pub(crate) fn check_resident<'a>(
    stage: &'static str,
    env: &Environment,
    names: impl IntoIterator<Item = &'a Name>,
) -> Result<(), Refusal> {
    let absent: Vec<String> = names
        .into_iter()
        .filter(|name| !resident(env, name))
        .map(ToString::to_string)
        .collect();
    if absent.is_empty() {
        Ok(())
    } else {
        Err(Refusal::NotResident {
            stage,
            names: absent,
        })
    }
}

/// The meaning digest's source is the one this file pins.
pub(crate) fn check_digest_source(source: &[u8], pinned: &str) -> Result<(), Refusal> {
    let measured: String = Sha256::digest(source)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect();
    if measured == pinned {
        Ok(())
    } else {
        Err(Refusal::DigestSource {
            measured,
            pinned: pinned.to_owned(),
        })
    }
}

/// Printed name → meaning digest, for every theorem among `targets` in `env`.
pub(crate) fn theorem_inventory(
    digests: &MeaningDigests<'_>,
    env: &Environment,
    targets: &BTreeSet<Name>,
) -> BTreeMap<String, String> {
    targets
        .iter()
        .filter_map(|name| env.get_const(name))
        .filter(|c| c.kind == ConstantKind::Theorem)
        .map(|c| {
            let digest = digests
                .digest(&c.name)
                .unwrap_or_else(|error| panic!("{error}"));
            (c.name.to_string(), digest)
        })
        .collect()
}

/// The committed pins.
pub(crate) fn statement_pins() -> BTreeMap<String, String> {
    serde_json::from_str(STATEMENT_PINS).expect("statement_pins.json is a name-to-digest object")
}

/// The inventory and the pins name the same theorems with the same digests.
pub(crate) fn check_statements(
    inventory: &BTreeMap<String, String>,
    pins: &BTreeMap<String, String>,
) -> Result<(), Refusal> {
    let unlisted: Vec<String> = inventory
        .keys()
        .filter(|name| !pins.contains_key(*name))
        .cloned()
        .collect();
    let missing: Vec<String> = pins
        .keys()
        .filter(|name| !inventory.contains_key(*name))
        .cloned()
        .collect();
    let changed: Vec<String> = inventory
        .iter()
        .filter(|(name, digest)| pins.get(*name).is_some_and(|pin| pin != *digest))
        .map(|(name, _)| name.clone())
        .collect();
    if unlisted.is_empty() && missing.is_empty() && changed.is_empty() {
        Ok(())
    } else {
        Err(Refusal::Statements {
            unlisted,
            missing,
            changed,
        })
    }
}

/// Every hand-table entry is a theorem of the inventory.
pub(crate) fn check_hand_table(
    table: &[&str],
    inventory: &BTreeMap<String, String>,
) -> Result<(), Refusal> {
    let names: Vec<String> = table
        .iter()
        .filter(|entry| !inventory.contains_key(**entry))
        .map(|entry| (*entry).to_owned())
        .collect();
    if names.is_empty() {
        Ok(())
    } else {
        Err(Refusal::HandTable { names })
    }
}

/// The full axiom closure of `name`, foundational axioms included; `None` for
/// a name with no constant record (an inductive family member).
pub(crate) fn axiom_closure(env: &Environment, name: &Name) -> Option<BTreeSet<String>> {
    let mut closure = env.axiom_deps(name)?;
    closure.extend(env.foundational_axiom_deps(name)?);
    Some(closure.iter().map(ToString::to_string).collect())
}

/// `closure` stays inside `observed`.
pub(crate) fn check_closure_within(
    subject: &str,
    closure: &BTreeSet<String>,
    observed: &BTreeSet<String>,
) -> Result<(), Refusal> {
    let extra: Vec<String> = closure.difference(observed).cloned().collect();
    if extra.is_empty() {
        Ok(())
    } else {
        Err(Refusal::OutsideObservedClosure {
            subject: subject.to_owned(),
            extra,
        })
    }
}

/// Every pinned axiom is reached by some closure.
pub(crate) fn check_closure_used(
    reached: &BTreeSet<String>,
    observed: &BTreeSet<String>,
) -> Result<(), Refusal> {
    let unused: Vec<String> = observed.difference(reached).cloned().collect();
    if unused.is_empty() {
        Ok(())
    } else {
        Err(Refusal::ObservedClosureUnused { unused })
    }
}

/// The pinned set, as owned strings.
pub(crate) fn observed_axioms() -> BTreeSet<String> {
    OBSERVED_AXIOM_CLOSURE
        .iter()
        .map(|axiom| (*axiom).to_owned())
        .collect()
}

/// Run the ratchet over every target: each closure inside the observed set,
/// and the observed set no wider than their union. Returns each target's
/// closure and how many are family members with no constant record.
pub(crate) fn check_axiom_ratchet(
    env: &Environment,
    targets: &BTreeSet<Name>,
) -> Result<(BTreeMap<String, BTreeSet<String>>, usize), Refusal> {
    let observed = observed_axioms();
    let mut reached = BTreeSet::new();
    let mut outside = Ok(());
    let mut closures = BTreeMap::new();
    let mut family_members = 0;
    for name in targets {
        match axiom_closure(env, name) {
            Some(closure) => {
                if outside.is_ok() {
                    outside = check_closure_within(&name.to_string(), &closure, &observed);
                }
                reached.extend(closure.iter().cloned());
                closures.insert(name.to_string(), closure);
            }
            None => family_members += 1,
        }
    }
    // The first target outside the set is the refusal; the union is printed
    // whole, so one failing run shows everything the theory now reaches.
    eprintln!(
        "axiom closure, union over {} targets: {reached:?}",
        closures.len()
    );
    outside?;
    check_closure_used(&reached, &observed)?;
    Ok((closures, family_members))
}

/// One census row: the kind Lean reported and the closure it printed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CensusRow {
    pub(crate) kind: String,
    pub(crate) closure: BTreeSet<String>,
}

/// The committed census, parsed.
pub(crate) fn census_document() -> serde_json::Value {
    serde_json::from_str(LEAN_AXIOM_CENSUS).expect("data/lean_axiom_census.json is JSON")
}

/// The index of [`CENSUS_PACKAGE`] in the census's `packages`.
fn census_package_index(census: &serde_json::Value) -> usize {
    census["packages"]
        .as_array()
        .and_then(|packages| {
            packages
                .iter()
                .position(|package| package["package"] == CENSUS_PACKAGE)
        })
        .expect("the census has a package for this theory")
}

/// The census's rows for [`CENSUS_PACKAGE`], keyed by printed name, and the
/// Lean that minted them. A declaration with two rows refuses: keyed by name,
/// the later row would silently replace the earlier one. A census that is not
/// of the committed shape panics.
pub(crate) fn census_rows(
    census: &serde_json::Value,
) -> Result<(String, BTreeMap<String, CensusRow>), Refusal> {
    let package = &census["packages"][census_package_index(census)];
    let toolchain = package["lean_toolchain"]
        .as_str()
        .expect("the census names the Lean that minted it")
        .to_owned();
    let declarations = package["declarations"]
        .as_array()
        .expect("the census package lists its declarations");
    let mut rows = BTreeMap::new();
    let mut twice = BTreeSet::new();
    for row in declarations {
        let text = |key: &str| {
            row[key]
                .as_str()
                .unwrap_or_else(|| panic!("census row without `{key}`: {row}"))
                .to_owned()
        };
        let closure = row["axiom_closure"]
            .as_array()
            .unwrap_or_else(|| panic!("census row without a closure: {row}"))
            .iter()
            .map(|axiom| axiom.as_str().expect("an axiom name").to_owned())
            .collect();
        let name = text("declaration");
        let parsed = CensusRow {
            kind: text("kind"),
            closure,
        };
        if rows.insert(name.clone(), parsed).is_some() {
            twice.insert(name);
        }
    }
    if twice.is_empty() {
        Ok((toolchain, rows))
    } else {
        Err(Refusal::CensusDuplicateRows {
            names: twice.into_iter().collect(),
        })
    }
}

/// Whether `name` is a quotient former: `Quot`, `Quot.mk`, `Quot.lift` or
/// `Quot.ind`, which Lean declares as `quotInfo` and the kernel's walk sees as
/// value-less constants. `Quot.sound` is an axiom to both.
fn is_quotient_former(env: &Environment, name: &Name) -> bool {
    env.get_quot(name)
        .is_some_and(|quotient| quotient.kind != QuotKind::Sound)
}

/// `closure` without the quotient formers: the set as Lean's `collectAxioms`
/// names it.
pub(crate) fn as_lean_axioms(env: &Environment, closure: &BTreeSet<String>) -> BTreeSet<String> {
    closure
        .iter()
        .filter(|axiom| !is_quotient_former(env, &Name::from_string(axiom)))
        .cloned()
        .collect()
}

/// One step of pinned Lean's `collectAxioms` (`Lean.Util.CollectAxioms.collect`
/// in v4.30.0-rc2) at `name`, over the declarations the replay admitted:
/// whether `name` is an axiom, and the constants the rule visits next. An
/// axiom leads to the constants of its type, a quotient former nowhere; a
/// constructor or recursor to the constants of its type; an inductive to
/// those of its type and to its constructors (the step the kernel's walk does
/// not take); a definition, theorem or opaque declaration to those of its type
/// and value. A name with no declaration leads nowhere, as in Lean. Lean's own
/// walk also stops at a constant it is still collecting; this one does not,
/// so it reaches everything Lean's could.
fn lean_rule_step(env: &Environment, name: &Name) -> (bool, Vec<Name>) {
    let mut next = HashSet::new();
    if is_quotient_former(env, name) {
        return (false, Vec::new());
    }
    if let Some(inductive) = env.get_inductive(name) {
        inductive
            .type_
            .used_constants_dag(UsedConstants::ConstantsOnly, &mut next);
        next.extend(inductive.constructor_names.iter().cloned());
    } else if let Some(constructor) = env.get_constructor(name) {
        constructor
            .type_
            .used_constants_dag(UsedConstants::ConstantsOnly, &mut next);
    } else if let Some(recursor) = env.get_recursor(name) {
        recursor
            .type_
            .used_constants_dag(UsedConstants::ConstantsOnly, &mut next);
    } else if let Some(constant) = env.get_const(name) {
        constant
            .type_
            .used_constants_dag(UsedConstants::ConstantsOnly, &mut next);
        if constant.kind == ConstantKind::Axiom {
            return (true, next.into_iter().collect());
        }
        if let Some(value) = &constant.value {
            value.used_constants_dag(UsedConstants::ConstantsOnly, &mut next);
        }
    }
    (false, next.into_iter().collect())
}

/// Each root's reach by Lean's rule ([`lean_rule_step`]), keyed by printed
/// name: every axiom reachable from it. The graph is built once and each axiom
/// is propagated back along it, so a declaration's dependencies are walked
/// once, not once per root.
pub(crate) fn lean_rule_closures(
    env: &Environment,
    roots: &BTreeSet<Name>,
) -> BTreeMap<String, BTreeSet<String>> {
    let mut successors: HashMap<Name, Vec<Name>> = HashMap::new();
    let mut axioms: Vec<Name> = Vec::new();
    let mut pending: Vec<Name> = roots.iter().cloned().collect();
    while let Some(name) = pending.pop() {
        if successors.contains_key(&name) {
            continue;
        }
        let (is_axiom, next) = lean_rule_step(env, &name);
        if is_axiom {
            axioms.push(name.clone());
        }
        pending.extend(
            next.iter()
                .filter(|after| !successors.contains_key(*after))
                .cloned(),
        );
        successors.insert(name, next);
    }
    let mut predecessors: HashMap<&Name, Vec<&Name>> = HashMap::new();
    for (from, next) in &successors {
        for to in next {
            predecessors.entry(to).or_default().push(from);
        }
    }
    let mut reaches: HashMap<&Name, BTreeSet<String>> = HashMap::new();
    for axiom in &axioms {
        let mut seen: HashSet<&Name> = HashSet::new();
        let mut stack: Vec<&Name> = vec![axiom];
        while let Some(name) = stack.pop() {
            if !seen.insert(name) {
                continue;
            }
            reaches.entry(name).or_default().insert(axiom.to_string());
            if let Some(before) = predecessors.get(name) {
                stack.extend(before.iter().copied());
            }
        }
    }
    roots
        .iter()
        .map(|root| {
            (
                root.to_string(),
                reaches.get(root).cloned().unwrap_or_default(),
            )
        })
        .collect()
}

/// The census and the module-of-origin selection name the same declarations.
pub(crate) fn check_census_inventory(
    declared: &BTreeSet<String>,
    census: &BTreeMap<String, CensusRow>,
) -> Result<(), Refusal> {
    let census_only: Vec<String> = census
        .keys()
        .filter(|name| !declared.contains(*name))
        .cloned()
        .collect();
    let test_only: Vec<String> = declared
        .iter()
        .filter(|name| !census.contains_key(*name))
        .cloned()
        .collect();
    if census_only.is_empty() && test_only.is_empty() {
        Ok(())
    } else {
        Err(Refusal::CensusInventory {
            census_only,
            test_only,
        })
    }
}

/// Each census row lies inside what Lean's rule reaches from the admitted
/// declaration. Returns how many are strictly inside: there pinned Lean's
/// sentinel cut a walk through an inductive and its constructors. A name with
/// no row is the inventory's refusal, not this one's.
pub(crate) fn check_census_within_reach(
    reach: &BTreeMap<String, BTreeSet<String>>,
    census: &BTreeMap<String, CensusRow>,
) -> Result<usize, Refusal> {
    let mut narrower = 0;
    let mut disagreements = Vec::new();
    for (name, reached) in reach {
        let Some(row) = census.get(name) else {
            continue;
        };
        if !row.closure.is_subset(reached) {
            disagreements.push(format!(
                "{name} ({}): census {:?}, Lean's rule over the replay reaches {reached:?}",
                row.kind, row.closure
            ));
        } else if &row.closure != reached {
            narrower += 1;
        }
    }
    if disagreements.is_empty() {
        Ok(narrower)
    } else {
        Err(Refusal::CensusBeyondReach { disagreements })
    }
}

/// Each kernel closure, named as Lean names axioms, is inside its census row,
/// so no row hides an axiom the kernel's walk of the admitted declaration
/// sees. Returns how many are strictly narrower: there the census reaches an
/// axiom through an inductive's constructors, which the kernel's walk does not
/// enter.
pub(crate) fn check_kernel_within_census(
    kernel: &BTreeMap<String, BTreeSet<String>>,
    census: &BTreeMap<String, CensusRow>,
) -> Result<usize, Refusal> {
    let mut narrower = 0;
    let mut disagreements = Vec::new();
    for (name, closure) in kernel {
        let Some(row) = census.get(name) else {
            continue;
        };
        if !closure.is_subset(&row.closure) {
            disagreements.push(format!(
                "{name} ({}): kernel {closure:?}, census {:?}",
                row.kind, row.closure
            ));
        } else if closure != &row.closure {
            narrower += 1;
        }
    }
    if disagreements.is_empty() {
        Ok(narrower)
    } else {
        Err(Refusal::KernelBeyondCensus { disagreements })
    }
}

/// The census's closures, `_unsafe_rec` rows included, together reach exactly
/// the observed set (both without the quotient formers).
pub(crate) fn check_census_union(
    census: &BTreeMap<String, CensusRow>,
    observed: &BTreeSet<String>,
) -> Result<(), Refusal> {
    let union: BTreeSet<String> = census
        .values()
        .flat_map(|row| row.closure.iter().cloned())
        .collect();
    if &union == observed {
        Ok(())
    } else {
        Err(Refusal::CensusUnion {
            census: union.into_iter().collect(),
            observed: observed.iter().cloned().collect(),
        })
    }
}

/// A real theorem that uses `Classical.choice`, admitted through its own
/// reference entry over `loaded`, and the closure the same walk reports for
/// it: `∀ p : Prop, Nonempty p → p := fun p h => Classical.choice h`.
pub(crate) fn choice_user_closure(loaded: &Environment) -> BTreeSet<String> {
    let choice = Name::from_string("Classical.choice");
    let targets: BTreeSet<Name> = [choice.clone()].into_iter().collect();
    let base = reference_base_closed(loaded, &targets, &ClosedRecheckOptions::default())
        .expect("reference replay of Classical.choice");
    assert!(
        base.report.passed() && base.entry_refusals.is_empty(),
        "{}\n{:?}",
        base.report.verdict_sentence(),
        base.entry_refusals
    );
    let mut kernel = base.into_kernel().expect("Classical.choice is canonical");
    let nonempty = |p: Expr| {
        Expr::app(
            Expr::const_(Name::from_string("Nonempty"), vec![Level::zero()]),
            p,
        )
    };
    let subject = Name::from_string("CICL.Controls.choice_user");
    kernel
        .add_checked(Declaration::Theorem {
            name: subject.clone(),
            level_params: Vec::new(),
            type_: Expr::pi(
                BinderInfo::Default,
                Expr::prop(),
                Expr::pi(BinderInfo::Default, nonempty(Expr::bvar(0)), Expr::bvar(1)),
            ),
            value: Expr::lam(
                BinderInfo::Default,
                Expr::prop(),
                Expr::lam(
                    BinderInfo::Default,
                    nonempty(Expr::bvar(0)),
                    Expr::app(
                        Expr::app(Expr::const_(choice, vec![Level::zero()]), Expr::bvar(1)),
                        Expr::bvar(0),
                    ),
                ),
            ),
        })
        .expect("a real proof by Classical.choice is admitted");
    axiom_closure(kernel.environment(), &subject).expect("the control theorem was admitted")
}

/// `subject` restated as `forged` is refused as a changed statement, and as
/// nothing else. Restated at its own statement `stated` it keeps its pin, so
/// the refusal is the statement's and not the environment's or the package's.
pub(crate) fn forged_statement_refused(
    digests: &MeaningDigests<'_>,
    inventory: &BTreeMap<String, String>,
    pins: &BTreeMap<String, String>,
    subject: &Name,
    level_params: &[Name],
    stated: &Expr,
    forged: &Expr,
) {
    let restate = |type_: &Expr| {
        digests
            .statement_digest(subject, level_params, type_)
            .unwrap_or_else(|error| panic!("{error}"))
    };
    let subject_name = subject.to_string();
    assert_eq!(
        inventory.get(&subject_name),
        Some(&restate(stated)),
        "control theorem {subject} restated at its own statement must keep its pin"
    );
    let subject = subject_name;
    let mut forged_inventory = inventory.clone();
    forged_inventory.insert(subject.clone(), restate(forged));
    assert_eq!(
        check_statements(&forged_inventory, pins),
        Err(Refusal::Statements {
            unlisted: Vec::new(),
            missing: Vec::new(),
            changed: vec![subject],
        }),
        "a forged statement must be refused as changed"
    );
}

/// The checks on the Lean the inputs name and on the census's rows, each run
/// again on a planted defect. They run after the real inputs passed them.
pub(crate) fn input_controls(census: &serde_json::Value) {
    let pin = WORKSPACE_TOOLCHAIN.trim();
    let theory = THEORY_TOOLCHAIN.trim();
    let other = "leanprover/lean4:v4.29.0";
    assert_ne!(other, pin, "the controls need a Lean other than the pin");

    // The digest's source with one byte appended: what a pin means moved.
    let mut edited = MEANING_DIGEST_SOURCE.to_vec();
    edited.push(b'\n');
    assert!(
        matches!(
            check_digest_source(&edited, MEANING_DIGEST_SOURCE_SHA256),
            Err(Refusal::DigestSource { ref pinned, .. }) if pinned == MEANING_DIGEST_SOURCE_SHA256
        ),
        "an edited digest source must be refused"
    );

    // The package names another Lean, and the workspace pin moves without the
    // package's.
    assert_eq!(
        check_toolchain_pin(&format!("{other}\n"), WORKSPACE_TOOLCHAIN),
        Err(Refusal::ToolchainPin {
            theory: other.to_owned(),
            workspace: pin.to_owned(),
        })
    );
    assert_eq!(
        check_toolchain_pin(THEORY_TOOLCHAIN, other),
        Err(Refusal::ToolchainPin {
            theory: theory.to_owned(),
            workspace: other.to_owned(),
        })
    );

    // The census was minted with another Lean.
    assert_eq!(
        check_census_toolchain(other, THEORY_TOOLCHAIN),
        Err(Refusal::CensusToolchain {
            census: other.to_owned(),
            theory: theory.to_owned(),
        })
    );

    // A second row for one declaration, placed before the real row with its
    // closure emptied: keyed by name, the real row would replace it and the
    // forged row would vanish unread.
    let mut doubled = census.clone();
    let rows = doubled["packages"][census_package_index(census)]["declarations"]
        .as_array_mut()
        .expect("the census package lists its declarations");
    let mut forged = rows.first().expect("a census row").clone();
    let twice = forged["declaration"]
        .as_str()
        .expect("a census row names its declaration")
        .to_owned();
    forged["axiom_closure"] = serde_json::json!([]);
    rows.insert(0, forged);
    assert_eq!(
        census_rows(&doubled).map(|_| ()),
        Err(Refusal::CensusDuplicateRows { names: vec![twice] })
    );
    eprintln!(
        "input controls: an edited digest source, a package Lean off the pin, a pin moved \
         without the package, a census of another Lean and a census row stated twice each \
         refused as stated"
    );
}

/// The selection's checks, each run again on a planted defect over the real
/// selection, which passed them.
pub(crate) fn selection_controls(
    declared: &BTreeSet<Name>,
    not_replayable: &BTreeSet<String>,
    targets: &BTreeSet<Name>,
    by_prefix: &BTreeSet<Name>,
) {
    // A name stored unsafe that no artifact declares: the readers disagree.
    let undeclared = "CICL.Controls.undeclared._unsafe_rec".to_owned();
    let mut wider_unsafe = not_replayable.clone();
    wider_unsafe.insert(undeclared.clone());
    assert_eq!(
        check_selection(declared, &wider_unsafe, targets),
        Err(Refusal::Selection {
            unsafe_not_declared: vec![undeclared],
            dropped: Vec::new(),
            stray: Vec::new(),
        })
    );

    // A declared private name the selection drops. The prefix filter never
    // held it, so this is the check that refuses it.
    let private = targets
        .iter()
        .find(|name| name.to_string().starts_with("_private."))
        .expect("a private target")
        .clone();
    let mut narrowed = targets.clone();
    narrowed.remove(&private);
    assert_eq!(
        check_selection(declared, not_replayable, &narrowed),
        Err(Refusal::Selection {
            unsafe_not_declared: Vec::new(),
            dropped: vec![private.to_string()],
            stray: Vec::new(),
        })
    );
    assert_eq!(
        check_prefix_filter_kept(by_prefix, &narrowed),
        Ok(()),
        "the prefix filter never held a private name"
    );

    // A target nothing declares, and a stored-unsafe declaration made a target.
    let ghost = Name::from_string("CICL.Controls.not_declared");
    let mut wider = targets.clone();
    wider.insert(ghost.clone());
    assert_eq!(
        check_selection(declared, not_replayable, &wider),
        Err(Refusal::Selection {
            unsafe_not_declared: Vec::new(),
            dropped: Vec::new(),
            stray: vec![ghost.to_string()],
        })
    );
    let twin = Name::from_string("CICL.Controls.twin._unsafe_rec");
    let mut twin_declared = declared.clone();
    twin_declared.insert(twin.clone());
    let mut twin_unsafe = not_replayable.clone();
    twin_unsafe.insert(twin.to_string());
    let mut twin_targets = targets.clone();
    twin_targets.insert(twin.clone());
    assert_eq!(
        check_selection(&twin_declared, &twin_unsafe, &twin_targets),
        Err(Refusal::Selection {
            unsafe_not_declared: Vec::new(),
            dropped: Vec::new(),
            stray: vec![twin.to_string()],
        })
    );

    // A constant the loader holds under the old name filter that the
    // selection lost.
    let lost = by_prefix
        .iter()
        .next()
        .expect("a constant under the prefix filter")
        .clone();
    let mut short = targets.clone();
    short.remove(&lost);
    assert_eq!(
        check_prefix_filter_kept(by_prefix, &short),
        Err(Refusal::PrefixFilterLost {
            names: vec![lost.to_string()],
        })
    );
    eprintln!(
        "selection controls: a stored-unsafe name no artifact declares, a dropped private name \
         (which the prefix filter passes), a target nothing declares, a stored-unsafe target \
         and a name lost from the prefix filter each refused as stated"
    );
}

/// Each check above, run again on one planted defect, refuses for the reason
/// it states. The positive run comes first, so no control can pass because
/// its check refuses everything.
pub(crate) fn negative_controls(
    loaded: &Environment,
    order: &[String],
    level: &BTreeSet<String>,
    inventory: &BTreeMap<String, String>,
    pins: &BTreeMap<String, String>,
    hand_table: &[&str],
) {
    // ORDER: a listed module the root stops reaching, and a module loaded but
    // never listed.
    let lost = level.iter().next_back().expect("a level module").clone();
    let mut short = level.clone();
    short.remove(&lost);
    assert_eq!(
        check_order(order, &short),
        Err(Refusal::Order {
            listed_not_loaded: vec![lost],
            loaded_not_listed: Vec::new(),
        })
    );
    let stray = "CICL.Controls.Unlisted".to_owned();
    let mut wide = level.clone();
    wide.insert(stray.clone());
    assert_eq!(
        check_order(order, &wide),
        Err(Refusal::Order {
            listed_not_loaded: Vec::new(),
            loaded_not_listed: vec![stray],
        })
    );

    // Lakefile: a module ORDER compiles that `lake build` would not.
    let mut roots = lakefile_roots();
    let dropped = roots.iter().next().expect("a lakefile root").clone();
    roots.remove(&dropped);
    assert_eq!(
        check_lakefile_roots(order, &roots),
        Err(Refusal::LakefileRoots {
            listed_not_root: vec![dropped],
            root_not_listed: Vec::new(),
        })
    );

    // Not replayable: a stored-unsafe declaration that is no compiler twin.
    let planted = "CICL.Controls.hand_written_unsafe".to_owned();
    let stored: BTreeSet<String> = ["CICL.Level.eval._unsafe_rec".to_owned(), planted.clone()]
        .into_iter()
        .collect();
    assert_eq!(
        check_not_replayable(&stored),
        Err(Refusal::NotReplayable {
            names: vec![planted],
        })
    );

    // Residency: a declared name the environment does not hold.
    let ghost = Name::from_string("CICL.Controls.never_declared");
    assert_eq!(
        check_resident("the control", loaded, [&ghost]),
        Err(Refusal::NotResident {
            stage: "the control",
            names: vec![ghost.to_string()],
        })
    );

    // Statements: a theorem with no pin, and a pin with no theorem. A changed
    // statement is planted per control theorem by `forged_statement_refused`.
    let (pinned, digest) = inventory.iter().next().expect("a pinned theorem");
    let unlisted = "CICL.Controls.unlisted_theorem".to_owned();
    let mut grown = inventory.clone();
    grown.insert(unlisted.clone(), digest.clone());
    assert_eq!(
        check_statements(&grown, pins),
        Err(Refusal::Statements {
            unlisted: vec![unlisted.clone()],
            missing: Vec::new(),
            changed: Vec::new(),
        })
    );
    let mut shrunk = inventory.clone();
    shrunk.remove(pinned);
    assert_eq!(
        check_statements(&shrunk, pins),
        Err(Refusal::Statements {
            unlisted: Vec::new(),
            missing: vec![pinned.clone()],
            changed: Vec::new(),
        })
    );

    // Hand table: an entry that is no theorem of the level modules.
    let mut table = hand_table.to_vec();
    table.push(&unlisted);
    assert_eq!(
        check_hand_table(&table, inventory),
        Err(Refusal::HandTable {
            names: vec![unlisted.clone()],
        })
    );

    // Axioms. A real theorem proved by `Classical.choice`, admitted through
    // the entry, is walked by the same closure function and refused; so is the
    // old allow-list, which pinned a name nothing reaches.
    let observed = observed_axioms();
    let choice = "Classical.choice".to_owned();
    assert!(
        !observed.contains(&choice),
        "the control assumes choice is outside the observed set"
    );
    let closure = choice_user_closure(loaded);
    assert!(
        closure.contains(&choice),
        "the closure walk must see Classical.choice in a proof that uses it: {closure:?}"
    );
    assert_eq!(
        check_closure_within("CICL.Controls.choice_user", &closure, &observed),
        Err(Refusal::OutsideObservedClosure {
            subject: "CICL.Controls.choice_user".to_owned(),
            extra: closure.difference(&observed).cloned().collect(),
        })
    );
    let mut allow_list = observed.clone();
    allow_list.insert(choice.clone());
    assert_eq!(
        check_closure_used(&observed, &allow_list),
        Err(Refusal::ObservedClosureUnused {
            unused: vec![choice],
        })
    );
    eprintln!(
        "negative controls: ORDER, lakefile roots, stored-unsafe, residency, statements, hand \
         table and axioms each refused as stated"
    );
}

/// Each census check, run again on one planted defect, refuses for the reason
/// it states. They run after the real checks passed, so `census` names exactly
/// the declared names and agrees with `lean_rule` and `kernel`.
pub(crate) fn census_controls(
    census: &BTreeMap<String, CensusRow>,
    lean_rule: &BTreeMap<String, BTreeSet<String>>,
    kernel: &BTreeMap<String, BTreeSet<String>>,
    observed: &BTreeSet<String>,
) {
    let declared: BTreeSet<String> = census.keys().cloned().collect();
    let propext = "propext".to_owned();
    let choice = "Classical.choice".to_owned();
    assert!(
        !observed.contains(&choice),
        "the controls assume choice is outside the observed set"
    );

    // Inventory: a declaration the census lost, and a row for a name no level
    // module declares.
    let (dropped, _) = census.iter().next().expect("a census row");
    let mut short = census.clone();
    short.remove(dropped);
    assert_eq!(
        check_census_inventory(&declared, &short),
        Err(Refusal::CensusInventory {
            census_only: Vec::new(),
            test_only: vec![dropped.clone()],
        })
    );
    let stray = "CICL.Controls.census_stray".to_owned();
    let mut wide = census.clone();
    wide.insert(
        stray.clone(),
        CensusRow {
            kind: "theorem".to_owned(),
            closure: BTreeSet::new(),
        },
    );
    assert_eq!(
        check_census_inventory(&declared, &wide),
        Err(Refusal::CensusInventory {
            census_only: vec![stray],
            test_only: Vec::new(),
        })
    );

    // Lower bound: a census row that lost `propext`, which the kernel's walk
    // of the admitted declaration reaches, is refused, and so is a kernel
    // closure that grew past its row.
    let (subject, _) = kernel
        .iter()
        .find(|(_, closure)| closure.contains(&propext))
        .expect("a target whose kernel closure reaches propext");
    let mut hiding = census.clone();
    hiding
        .get_mut(subject)
        .expect("the subject has a census row")
        .closure
        .remove(&propext);
    match check_kernel_within_census(kernel, &hiding) {
        Err(Refusal::KernelBeyondCensus { disagreements })
            if disagreements.len() == 1 && disagreements[0].starts_with(subject.as_str()) => {}
        other => panic!("a census row hiding propext must be refused for {subject}: {other:?}"),
    }
    let mut wider = kernel.clone();
    wider
        .get_mut(subject)
        .expect("the subject has a kernel closure")
        .insert(choice.clone());
    match check_kernel_within_census(&wider, census) {
        Err(Refusal::KernelBeyondCensus { disagreements })
            if disagreements.len() == 1 && disagreements[0].starts_with(subject.as_str()) => {}
        other => panic!("a kernel closure beyond the census must be refused: {other:?}"),
    }

    // Upper bound: a census row naming an axiom Lean's rule cannot reach from
    // the admitted declaration.
    let (subject, _) = lean_rule
        .iter()
        .find(|(_, reached)| !reached.contains(&choice))
        .expect("a target that does not reach choice");
    let mut claiming = census.clone();
    claiming
        .get_mut(subject)
        .expect("the subject has a census row")
        .closure
        .insert(choice.clone());
    match check_census_within_reach(lean_rule, &claiming) {
        Err(Refusal::CensusBeyondReach { disagreements })
            if disagreements.len() == 1 && disagreements[0].starts_with(subject.as_str()) => {}
        other => panic!("a census row beyond reach must be refused for {subject}: {other:?}"),
    }

    // Union: a census row that reaches choice moves the union off the
    // observed set.
    let mut grown = census.clone();
    grown
        .get_mut(dropped)
        .expect("the row is in the census")
        .closure
        .insert(choice.clone());
    let mut with_choice = observed.clone();
    with_choice.insert(choice);
    assert_eq!(
        check_census_union(&grown, observed),
        Err(Refusal::CensusUnion {
            census: with_choice.into_iter().collect(),
            observed: observed.iter().cloned().collect(),
        })
    );
    eprintln!(
        "census controls: inventory (lost and stray), a row hiding an axiom the kernel sees, a \
         kernel closure past its row, a row beyond reach and the union each refused as stated"
    );
}
