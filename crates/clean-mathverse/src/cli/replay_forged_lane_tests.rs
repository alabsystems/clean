// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The three mathverse `.olean` re-check lanes against `.olean`s Lean's kernel
//! never admitted (fixture family `replay_forged` in `crates/clean-olean`, whose
//! README records `leanchecker`'s verdict on each).
//!
//! Measured 2026-09-23/24 with the pre-fix binary: `per-constant-verify`
//! returned `kernel_verified 3` for `forged3_self : False := forged3_self` and
//! the two-cycle; `stamp-verified --parallel` stored those three as
//! KernelVerified; every lane accepted `isOSX = true := rfl` (a native
//! reducer for Lean's `@[extern] opaque`); and all three lanes, the sequential
//! `stamp-verified` included, stamped `False := unsafeCast True.intro`. Each
//! test drives a lane through the entry point the CLI calls and asserts a named
//! refusal for every forgery and a verdict for every honest control.
//!
//! Round 2 (2026-09-24) added three classes, each measured against the
//! round-1 release binary before its fix: Clean's prelude constants and
//! shadowing reached the re-check (`ReplayPrelude`, `ReplayPreludeUse`,
//! `ReplayRedeclare`, `ReplayForgedQuot`); stored recursors and constructors
//! were trusted (`ReplayForgedRec`, `ReplayForgedRule`, `ReplayForgedCtor`,
//! control `ReplayHonestInd`); and native reducers computed values Lean's
//! definitions do not (`ReplayForgedStr`, control `ReplayHonestStr`).
//!
//! The `.olean` loader's module-trust rules (one name, one declaration; closed
//! over its imports; no self-dependent declaration) refuse the WHOLE import
//! for `ReplayForged`, `ReplayForged3`, `ReplayCrossA`, `ReplayRedeclare`,
//! `ReplayForgedBoolDef` and `ReplayForgedIndOverAx`, and for `ReplayCrossB`
//! through its import. Pinned `leanchecker` refuses none of them at load: it
//! refuses each forged declaration in its replay, and exits 0 on
//! `ReplayCrossB`, whose import it trusts. A lane may leave those rules to its
//! own replay only for declarations it replays itself, in Lean's order,
//! refusing self-dependence and redeclarations per declaration
//! (`OleanImportPolicy::with_replay_refusals`'s precondition). The sharded
//! worker replays one module's own declarations, so it loads THOSE with rules
//! 1 and 3 left to its replay
//! (`clean_olean::load_module_with_deps_replaying_module`) and refuses each
//! forgery by name; whatever an import gets wrong still refuses the import,
//! since it only trusts its imports. `stamp-verified` keeps the rules
//! throughout: `--parallel` checks every
//! target against ONE base holding all of them, where a reference from one
//! target to a name only another declares resolves, so only the loader's rules
//! 2 and 3 refuse a cross-module forward reference or cycle there; and the
//! sequential modes load nothing but trusted imports. Every lane reports the
//! loader's refusal naming the declarations it is about
//! ([`MathverseCliError::StampImportRefused`],
//! `ShardedVerifyError::ImportRefused`). `per-constant-verify` loads through
//! its own demand walk, and trusts a module's imports as `leanchecker` does.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use clap::Parser;
use clean_kernel::env::ProofValueElision;
use clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT;
use clean_olean::test_support::compiled_fixture_dir;

use super::kv_cache::FingerprintMode;
use super::per_constant_load::{per_constant_verify, PerConstantResult};
use super::stamp_verified_dispatch::cmd_stamp_verified;
use super::{MathverseArgs, MathverseCliError, MathverseCommands};
use crate::verify::kernel_verified_manifest::KernelVerifiedManifest;

mod delta_prop;
mod proj_idx;
mod sort_def;
// Hole R112: blocks found through a forged `all`; flags the replay did not compare.
mod block_cover;
// Hole B1 (R113): a declaration placed where `lean` never reads it.
mod misplaced;
// Hole B3 (R113): a Clean payload trailer on a part Lean's own compiler wrote.
mod trailer;
// R113 review P1-P3, P7: parts that disagree, and a misplaced family in a dependency.
mod parts;
// R131: value-free stubs a later part completes, and the placement entries S5 names.
mod stubs;
// R142: a value the authoritative part states must be resident with it.
mod values;
// The refusal bookkeeping the `parts` and `stubs` tables share.
mod problems;
use problems::{assert_no_problems, refusal_problem};
// The `is_prop`-requires-a-sort rule; release-only (its fixture's closure).
#[cfg(not(debug_assertions))]
mod is_prop_sort;

fn fixtures() -> PathBuf {
    compiled_fixture_dir("replay_forged")
}

fn per_constant(module: &str, constants: &[&str]) -> PerConstantResult {
    try_per_constant(module, constants)
        .unwrap_or_else(|e| panic!("per-constant-verify {module}: {e}"))
}

/// [`per_constant`], returning the run's refusal instead of panicking.
fn try_per_constant(
    module: &str,
    constants: &[&str],
) -> Result<PerConstantResult, MathverseCliError> {
    let dir = fixtures();
    let explicit: Vec<String> = constants.iter().map(|s| (*s).to_owned()).collect();
    per_constant_verify(
        &dir.join(format!("{module}.olean")),
        &dir,
        &explicit,
        DEFAULT_HEARTBEAT_LIMIT,
        None,
        FingerprintMode::Metadata,
        false,
        false,
        explicit.is_empty(),
        ProofValueElision::None,
        64,
        None,
    )
}

fn assert_refused(lane: &str, errors: &impl Fn(&str) -> Option<String>, name: &str, needle: &str) {
    let message = errors(name).unwrap_or_else(|| panic!("{lane}: `{name}` must be refused"));
    assert!(
        message.contains(needle),
        "{lane}: `{name}` refused without `{needle}`: {message}"
    );
}

#[test]
fn test_per_constant_verify_forgeries_refused_honest_verified() {
    let r = per_constant("ReplayForged3", &[]);
    let errs = |n: &str| r.errors.get(n).cloned();
    assert_eq!((r.kernel_verified, r.failed), (0, 3), "{:?}", r.errors);
    assert_refused("pcv", &errs, "forged3_self", "refers to itself");
    assert_refused("pcv", &errs, "forged3_cycB", "dependency cycle");
    assert_refused("pcv", &errs, "forged3_cycA", "depends on `forged3_cycB`");

    let r = per_constant("ReplayForged4", &[]);
    assert_eq!((r.kernel_verified, r.failed), (0, 4), "{:?}", r.errors);
    for name in [
        "forged4_osx",
        "forged4_not_osx",
        "forged4_not_windows",
        "forged4_not_emscripten",
    ] {
        let errs = |n: &str| r.errors.get(n).cloned();
        assert_refused("pcv", &errs, name, "check_type: TypeMismatch");
    }

    let r = per_constant("ReplayForged5", &[]);
    assert_eq!((r.kernel_verified, r.failed), (0, 1), "{:?}", r.errors);
    let errs = |n: &str| r.errors.get(n).cloned();
    assert_refused("pcv", &errs, "forged5_unsafe", "UnsafeDeclaration");

    let r = per_constant("ReplayHonest", &[]);
    assert_eq!((r.kernel_verified, r.failed), (4, 0), "{:?}", r.errors);
    let r = per_constant("ReplayHonest4", &[]);
    assert_eq!((r.kernel_verified, r.failed), (1, 0), "{:?}", r.errors);
}

/// `--constant` on ONE cycle member: its module-mate is resident as context,
/// and must be replayed (and refused) before it can vouch for the target.
/// Measured 2026-09-24 before the prerequisite wiring: `kernel_verified 1`.
#[test]
fn test_per_constant_verify_single_cycle_member_is_refused() {
    let r = per_constant("ReplayForged3", &["forged3_cycA"]);
    assert_eq!((r.kernel_verified, r.failed), (0, 1), "{:?}", r.errors);
    let errs = |n: &str| r.errors.get(n).cloned();
    assert_refused("pcv --constant", &errs, "forged3_cycA", "replay order");
    let r = per_constant("ReplayHonest", &["honest_chain"]);
    assert_eq!((r.kernel_verified, r.failed), (1, 0), "{:?}", r.errors);
}

#[derive(Debug, Parser)]
struct Harness {
    #[command(subcommand)]
    command: Top,
}

#[derive(Debug, clap::Subcommand)]
enum Top {
    Mathverse(MathverseArgs),
}

/// The three `stamp-verified` modes: the merged sequential default, the
/// streaming `--single-pass`, and PARAGON's `--parallel`.
const STAMP_MODES: [Option<&str>; 3] = [None, Some("--single-pass"), Some("--parallel")];

/// Run `clean mathverse stamp-verified <module>.olean... [mode]` exactly as
/// the CLI does and read back the manifest's KernelVerified names.
fn stamp(modules: &[&str], mode: Option<&str>) -> BTreeSet<String> {
    try_stamp(modules, mode).unwrap_or_else(|e| panic!("stamp-verified {modules:?}: {e}"))
}

/// [`stamp`], returning the run's refusal instead of panicking.
fn try_stamp(modules: &[&str], mode: Option<&str>) -> Result<BTreeSet<String>, MathverseCliError> {
    let dir = fixtures();
    let out = tempfile::tempdir().expect("tempdir");
    let manifest = out.path().join("kv-manifest.json");
    let mut argv: Vec<String> = vec!["clean".into(), "mathverse".into(), "stamp-verified".into()];
    for module in modules {
        argv.push(path_str(&dir.join(format!("{module}.olean"))).to_owned());
    }
    for arg in [
        "--out-dir",
        path_str(out.path()),
        "--closure-root",
        path_str(&dir),
        "--manifest",
        path_str(&manifest),
        "--json",
    ] {
        argv.push(arg.to_owned());
    }
    if let Some(flag) = mode {
        argv.push(flag.to_owned());
    }
    let h = Harness::try_parse_from(&argv).expect("parse stamp-verified");
    let Top::Mathverse(args) = h.command;
    let MathverseCommands::StampVerified(s) = args.command else {
        panic!("expected stamp-verified");
    };
    cmd_stamp_verified(s)?;
    let bytes = std::fs::read(&manifest).expect("manifest written");
    let m: KernelVerifiedManifest = serde_json::from_slice(&bytes).expect("manifest parses");
    Ok(m.accepted_names().iter().cloned().collect())
}

fn path_str(p: &Path) -> &str {
    p.to_str().expect("utf-8 fixture path")
}

fn assert_stamps_run(modules: &[&str], expected: &[&str]) {
    let expected: BTreeSet<String> = expected.iter().map(|s| (*s).to_owned()).collect();
    for mode in STAMP_MODES {
        let lane = mode.unwrap_or("(default)");
        assert_eq!(
            stamp(modules, mode),
            expected,
            "stamp-verified {lane} on {modules:?}"
        );
    }
}

fn assert_stamps(module: &str, expected: &[&str]) {
    assert_stamps_run(&[module], expected);
}

/// [`assert_stamps_run`] for a run whose TARGETS the `.olean` loader's
/// module-trust rules refuse: `--parallel`, which loads every target into its
/// base, may refuse the run at import instead, and then the refusal must name
/// forged declarations only (`forged`), and nothing is stamped. The sequential
/// modes never load a target through the loader (they convert and replay the
/// targets; the loader reads only their imports), so they must stamp exactly
/// `expected`. The earlier refusal is accepted as upstream's
/// `replay_forged_lanes` accepts it for `verify-batch` (95ca0bdf9): PARAGON
/// does not meet `OleanImportPolicy::with_replay_refusals`'s precondition (the
/// module doc says why).
fn assert_stamps_run_or_refused_at_import(modules: &[&str], expected: &[&str], forged: &[&str]) {
    let wanted: BTreeSet<String> = expected.iter().map(|s| (*s).to_owned()).collect();
    for mode in STAMP_MODES {
        let lane = mode.unwrap_or("(default)");
        match (mode, try_stamp(modules, mode)) {
            (_, Ok(stamped)) => {
                assert_eq!(stamped, wanted, "stamp-verified {lane} on {modules:?}");
            }
            (Some("--parallel"), Err(MathverseCliError::StampImportRefused { names, .. })) => {
                assert!(
                    !names.is_empty() && names.iter().all(|n| forged.contains(&n.as_str())),
                    "stamp-verified {lane} on {modules:?}: refused at import naming {names:?}, \
                     which are not all forged declarations {forged:?}"
                );
            }
            (_, Err(e)) => panic!("stamp-verified {lane} on {modules:?}: {e}"),
        }
    }
}

/// A run that stamps both modules refuses the importer's use of the
/// importee's forgery: Lean admits a constant only after what it uses
/// (`leanchecker --fresh ReplayCrossB` refuses it). Measured 2026-09-24 with the
/// pre-fix binary: `--parallel` and `--single-pass` both stamped
/// `cross_uses_forged`.
///
/// `--parallel` may refuse the run at import instead: the loader refuses
/// `ReplayCrossA`, whose `cross_forged := cross_forged` depends on itself.
#[test]
fn test_stamp_verified_both_lanes_refuse_use_of_another_run_modules_forgery() {
    assert_stamps_run_or_refused_at_import(
        &["ReplayCrossA", "ReplayCrossB"],
        &["cross_honest", "cross_uses_honest"],
        &["cross_forged"],
    );
}

/// A run over `ReplayCrossB` ALONE: its closure holds `ReplayCrossA`, whose
/// `cross_forged := cross_forged` depends on itself, and every
/// `stamp-verified` mode keeps the loader's refusal of that import, naming it.
/// Pinned `leanchecker ReplayCrossB` exits 0 (it trusts the import), as
/// `per-constant-verify` does; a stamping lane never replays an import, and a
/// stamp over it would stand `cross_uses_forged : False` on the refused
/// `cross_forged` (see the module doc).
#[test]
fn test_stamp_verified_refuses_a_self_dependent_import_by_name() {
    for mode in STAMP_MODES {
        match try_stamp(&["ReplayCrossB"], mode) {
            Err(MathverseCliError::StampImportRefused { names, .. }) => {
                assert_eq!(names, ["cross_forged"], "{mode:?}");
            }
            other => panic!("stamp-verified {mode:?} on ReplayCrossB: {other:?}"),
        }
    }
}

/// An honest module with an `unsafe def`: Lean's replay skips the unsafe one
/// (`leanchecker` rc 0), so every lane leaves it neither verified nor failed and
/// still verifies its safe neighbour.
#[test]
fn test_lanes_skip_an_unsafe_definition_like_lean_replay() {
    let r = per_constant("ReplayHonestUnsafe", &[]);
    assert_eq!(
        (r.kernel_verified, r.failed, r.not_replayable),
        (1, 0, 1),
        "{:?}",
        r.errors
    );
    assert_stamps("ReplayHonestUnsafe", &["honest_safe"]);
    // Asked for by name, it is refused with the reason.
    let r = per_constant("ReplayHonestUnsafe", &["honest_unsafe_val"]);
    assert_eq!((r.kernel_verified, r.failed), (0, 1), "{:?}", r.errors);
    let errs = |n: &str| r.errors.get(n).cloned();
    assert_refused("pcv --constant", &errs, "honest_unsafe_val", "is unsafe");
}

/// Alone, `ReplayCrossB`'s imports are the trusted starting environment, as in
/// `leanchecker ReplayCrossB` (rc 0): the per-module lanes keep that scope.
#[test]
fn test_per_constant_verify_trusts_imports_like_leanchecker_without_fresh() {
    let r = per_constant("ReplayCrossB", &[]);
    assert_eq!((r.kernel_verified, r.failed), (2, 0), "{:?}", r.errors);
}

#[test]
fn test_stamp_verified_both_lanes_never_stamp_a_forgery() {
    let forged3 = ["forged3_self", "forged3_cycA", "forged3_cycB"];
    assert_stamps_run_or_refused_at_import(&["ReplayForged3"], &[], &forged3);
    let forged = ["forged_self", "forged_cycA", "forged_cycB", "forged_bad"];
    assert_stamps_run_or_refused_at_import(&["ReplayForged"], &[], &forged);
    assert_stamps("ReplayForged4", &[]);
    assert_stamps("ReplayForged5", &[]);
}

#[test]
fn test_stamp_verified_both_lanes_stamp_honest_controls() {
    assert_stamps(
        "ReplayHonest",
        &["honest_t", "honest_chain", "honest_one", "honest_one_eq"],
    );
    assert_stamps("ReplayHonest4", &["honest4_osx_refl"]);
}

/// The sharded worker over one fixture module, as `mathverse_shard sharded
/// --module <M>` runs it.
fn sharded(module: &str, max_failures: usize) -> crate::verify::sharded::ModuleVerifyResult {
    let mut search = vec![fixtures()];
    search.extend(clean_olean::default_search_paths());
    crate::verify::sharded::verify_module(module, &search, max_failures)
        .unwrap_or_else(|e| panic!("sharded verify {module}: {e}"))
}

/// `mathverse_shard sharded` (`verify::sharded::verify_module`) re-checks a
/// module's own constants with the module resident: the same lane shape, so the
/// same forgeries and controls. The module's own parts load with the loader's
/// module-trust rules left to its replay
/// (`clean_olean::load_module_with_deps_replaying_module`), so a module the
/// default load refuses whole (`ReplayForged`, `ReplayForged3`,
/// `ReplayCrossA`: a declaration that depends on itself) reaches the worker's
/// replay, which refuses each forged declaration by name, as pinned
/// `leanchecker` does (`(kernel) unknown constant 'forged3_self'`, `...
/// 'cross_forged'`).
#[test]
fn test_sharded_verify_module_refuses_forgeries_verifies_honest() {
    let run = |module: &str| sharded(module, 16);
    for (module, forged) in [
        ("ReplayForged3", 3),
        ("ReplayForged", 4),
        ("ReplayForged4", 4),
        ("ReplayForged5", 1),
    ] {
        let r = run(module);
        assert_eq!(r.counts.kernel_verified, 0, "{module}: {:?}", r.failures);
        assert_eq!(r.counts.failed, forged, "{module}: {:?}", r.failures);
    }
    let r = run("ReplayForged3");
    let reason = |n: &str| {
        r.failures
            .iter()
            .find(|(name, _)| name == n)
            .map(|(_, why)| why.clone())
            .unwrap_or_default()
    };
    assert!(
        reason("forged3_self").contains("refers to itself"),
        "{:?}",
        r.failures
    );
    assert!(
        reason("forged3_cycB").contains("dependency cycle"),
        "{:?}",
        r.failures
    );
    assert_eq!(run("ReplayHonest").counts.kernel_verified, 4);
    let r = run("ReplayHonestUnsafe");
    assert_eq!(
        (r.counts.kernel_verified, r.counts.failed),
        (1, 0),
        "{:?}",
        r.failures
    );
    // `ReplayCrossA`: its forgery refused by name, its honest neighbour
    // verified (`leanchecker` replays both, and stops at the first refusal).
    let r = run("ReplayCrossA");
    assert_eq!(
        r.kernel_verified_names,
        ["cross_honest"],
        "{:?}",
        r.failures
    );
    assert_eq!(r.counts.failed, 1, "{:?}", r.failures);
    assert!(
        r.failures
            .iter()
            .any(|(n, why)| n == "cross_forged" && why.contains("refers to itself")),
        "{:?}",
        r.failures
    );
}

/// `ReplayCrossB` alone: its import `ReplayCrossA` holds `cross_forged :=
/// cross_forged`, and the worker keeps the loader's refusal of that import,
/// by name. Pinned `leanchecker ReplayCrossB` exits 0 (it trusts the import,
/// as `per-constant-verify` does too); the worker does not, because it never
/// replays an import and its verdicts are merged over a corpus with no
/// cross-module pass, where `cross_uses_forged : False` would stand verified
/// beside the refused `cross_forged` (`load_module_with_deps_replaying_module`
/// keeps every module-trust rule for imports).
#[test]
fn test_sharded_verify_module_refuses_a_self_dependent_import_by_name() {
    let mut search = vec![fixtures()];
    search.extend(clean_olean::default_search_paths());
    match crate::verify::sharded::verify_module("ReplayCrossB", &search, 16) {
        Err(crate::verify::sharded::ShardedVerifyError::ImportRefused { names, .. }) => {
            assert_eq!(names, ["cross_forged"]);
        }
        Err(e) => panic!("sharded verify ReplayCrossB: {e}"),
        Ok(r) => panic!(
            "sharded verify ReplayCrossB was not refused at import: verified {:?}",
            r.kernel_verified_names
        ),
    }
}

/// A module that redeclares what its import declares, its own parts loaded
/// with the loader's rule 1 left to the replay: the loader keeps the import's
/// declaration and records the module's instead of refusing the import, and
/// the worker refuses the redeclaration as already declared, and every
/// declaration that uses it. Pinned `leanchecker`: `ReplayForgedBoolDef` rc 1 (`(kernel)
/// application type mismatch` for `forged_bool_false`, checked against the
/// imported axiom), `ReplayForgedIndOverAx` rc 1 (`(kernel) constant has
/// already been declared 'ind_ax_t'`); the controls `ReplayHonestBoolAx` and
/// `ReplayHonestIndAx` rc 0. Without the loader's stub-upgrade confinement
/// under `OleanImportPolicy::with_replay_refusals`, `def bool_ax_b := true`
/// would fill the imported `axiom bool_ax_b` and `forged_bool_false : False`
/// would check.
#[test]
fn test_sharded_verify_module_refuses_redefinitions_of_imported_axioms() {
    for (module, forged, redeclared) in [
        (
            "ReplayForgedBoolDef",
            ["bool_ax_b", "forged_bool_false"].as_slice(),
            "bool_ax_b",
        ),
        (
            "ReplayForgedIndOverAx",
            ["ind_ax_t", "forged_ind_false"].as_slice(),
            "ind_ax_t",
        ),
    ] {
        let r = sharded(module, 64);
        assert_eq!(r.counts.kernel_verified, 0, "{module}: {:?}", r.failures);
        for name in forged {
            assert!(
                r.failures.iter().any(|(n, _)| n == name),
                "{module}: `{name}` not refused; failures {:?}",
                r.failures
            );
        }
        assert!(
            r.failures
                .iter()
                .any(|(n, why)| n == redeclared && why.contains("already declared")),
            "{module}: {:?}",
            r.failures
        );
    }
    for control in ["ReplayHonestBoolAx", "ReplayHonestIndAx"] {
        let r = sharded(control, 64);
        assert_eq!(r.counts.failed, 0, "{control}: {:?}", r.failures);
    }
}

/// Every value-bearing declaration a fixture module stores (what
/// `--all-declared` selects), by name.
fn value_bearing(module: &str) -> BTreeSet<String> {
    let path = fixtures().join(format!("{module}.olean"));
    let parsed = clean_olean::parse_module_file(&path)
        .unwrap_or_else(|e| panic!("parse {}: {e}", path.display()));
    parsed
        .constants
        .iter()
        .filter(|c| {
            matches!(
                c.kind,
                clean_olean::ConstantKind::Definition
                    | clean_olean::ConstantKind::Theorem
                    | clean_olean::ConstantKind::Opaque
            )
        })
        .map(|c| c.name.clone())
        .collect()
}

/// Hole A, per constant: Clean's prelude is not in the replay environment,
/// a module's own declaration is the one checked, and a redeclaration of an
/// import's name is refused. Measured with the round-1 binary: `kernel_verified
/// 5` on `ReplayPrelude` (the three `: False` forgeries through `sorry`,
/// `trustedArith`, `trustedAy`), 2 on `ReplayPreludeUse`, and `Nat.pred`
/// verified on `ReplayRedeclare`.
#[test]
fn test_per_constant_verify_prelude_constants_and_shadowing_are_refused() {
    let r = per_constant("ReplayPrelude", &[]);
    assert_eq!((r.kernel_verified, r.failed), (1, 4), "{:?}", r.errors);
    for forged in ["prelude_sorry", "prelude_arith", "prelude_ay"] {
        let errs = |n: &str| r.errors.get(n).cloned();
        assert_refused("pcv", &errs, forged, "UnknownConst");
    }
    let errs = |n: &str| r.errors.get(n).cloned();
    assert_refused("pcv", &errs, "Nat.not_succ_lt_zero", "TypeMismatch");

    let r = per_constant("ReplayPreludeUse", &[]);
    assert_eq!((r.kernel_verified, r.failed), (1, 1), "{:?}", r.errors);
    let errs = |n: &str| r.errors.get(n).cloned();
    assert_refused("pcv", &errs, "prelude_shadow_use", "TypeMismatch");

    let r = per_constant("ReplayRedeclare", &[]);
    assert_eq!((r.kernel_verified, r.failed), (0, 2), "{:?}", r.errors);
    let errs = |n: &str| r.errors.get(n).cloned();
    assert_refused("pcv", &errs, "Nat.pred", "already declared");

    let r = per_constant("ReplayForgedQuot", &[]);
    assert_eq!((r.kernel_verified, r.failed), (0, 1), "{:?}", r.errors);
}

/// Hole A, the canonical-quotient guard of per-constant-verify's demand walk.
/// `ReplayForgedQuot` is refused one step earlier (its `Quot.ind` redeclares
/// `Init.Prelude`'s), so this pins the guard itself: a stored quotient
/// primitive the demand walk loads -- from an IMPORT of the target, where the
/// redeclaration refusal does not reach -- never replaces the kernel's
/// canonical one, since Lean replays a `quotInfo` as the kernel's own
/// `quotDecl`. No fixture carries that case: Lean's `finalizeImport` refuses to
/// import a module that restates `Quot.ind`, so the pinned toolchain cannot
/// write one.
#[test]
fn test_per_constant_verify_stored_quotient_never_replaces_the_canonical_one() {
    use clean_kernel::env::{ConstantInfo, Environment};
    use clean_kernel::expr::{BinderInfo, Expr};
    use clean_kernel::name::Name;
    let quot_ind = Name::from_string("Quot.ind");
    let mut env = Environment::for_lean_replay();
    let canonical = env
        .get_const(&quot_ind)
        .expect("the canonical quotient is seeded")
        .clone();
    // `Quot.ind : (p : Prop) -> p`, the type `ReplayForgedQuot` stores.
    let forged_ty = Expr::pi(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
    super::per_constant_load::insert_or_upgrade(
        &mut env,
        ConstantInfo::new(quot_ind.clone(), vec![], forged_ty, None, false),
    );
    let resident = env.get_const(&quot_ind).expect("still resident");
    assert_eq!(resident.level_params, canonical.level_params);
    assert_eq!(resident.type_, canonical.type_);
    assert!(env.get_quot(&quot_ind).is_some());
}

/// Hole A through PARAGON's opt-in demand-paged base
/// (`CLEAN_PARAGON_LAZY_BASE=1`, and every `CLEAN_REQUIRE_BOUNDED=1` run). Its
/// index serves one declaration per name and the loader never sees a lazily
/// served constant, so a redeclaration went unrefused there: measured
/// 2026-09-25, that base stamped `ReplayRedeclare`'s `Nat.pred`. The base is
/// now unavailable over a closure two of whose modules declare one name (other
/// than as Lean's theorem restatement), and the eager base, which refuses the
/// redeclaration, runs instead. `ReplayHonest` is the control: the base stays
/// available.
#[test]
fn test_paragon_demand_paged_base_is_unavailable_over_a_redeclaration() {
    let dir = fixtures();
    let scratch = tempfile::tempdir().expect("tempdir");
    let available = |module: &str| {
        super::parallel_verify::lazy_base_available(
            &[dir.join(format!("{module}.olean"))],
            &dir,
            &scratch.path().join(module),
        )
        .unwrap_or_else(|e| panic!("lazy base over {module}: {e}"))
    };
    assert!(!available("ReplayRedeclare"), "a redeclaration is served");
    assert!(
        available("ReplayHonest"),
        "the honest control lost the base"
    );
}

/// Hole B, per constant: the target's inductive blocks are replayed as
/// Lean's replay does. Measured with the round-1 binary: `kernel_verified 1`
/// on each of the three forgeries.
#[test]
fn test_per_constant_verify_forged_inductive_blocks_are_refused() {
    for (module, user) in [
        ("ReplayForgedRec", "forged_rec_false"),
        ("ReplayForgedRule", "forged_rule_eq"),
        ("ReplayForgedCtor", "forged_ctor_false"),
    ] {
        let r = per_constant(module, &[]);
        assert_eq!(
            (r.kernel_verified, r.failed),
            (0, 1),
            "{module}: {:?}",
            r.errors
        );
        let errs = |n: &str| r.errors.get(n).cloned();
        assert_refused("pcv", &errs, user, "replay order");
    }
    let r = per_constant("ReplayHonestInd", &[]);
    assert_eq!(r.failed, 0, "{:?}", r.errors);
    assert_eq!(r.kernel_verified, value_bearing("ReplayHonestInd").len());
}

/// Hole C, per constant: the `String` reducers whose values are not Lean's
/// are off in Lean's theory. Measured with the round-1 binary: all five
/// equations kernel-verified.
#[test]
fn test_per_constant_verify_string_reducers_that_disagree_with_lean_are_off() {
    let r = per_constant("ReplayForgedStr", &[]);
    assert_eq!((r.kernel_verified, r.failed), (0, 5), "{:?}", r.errors);
    let r = per_constant("ReplayHonestStr", &[]);
    assert_eq!((r.kernel_verified, r.failed), (2, 0), "{:?}", r.errors);
}

/// Hole A through every `stamp-verified` mode. Measured with the round-1
/// binary: every mode stamped `prelude_sorry`, `prelude_arith` and
/// `prelude_ay` (`: False`); the sequential modes stamped `prelude_shadow_use`
/// against the prelude theorem's type, and `--parallel` the redeclared
/// `Nat.pred`.
#[test]
fn test_stamp_verified_all_modes_refuse_prelude_constants_and_redeclarations() {
    assert_stamps("ReplayPrelude", &["prelude_honest"]);
    assert_stamps("ReplayPreludeUse", &["Nat.not_succ_lt_zero"]);
    assert_stamps_run_or_refused_at_import(&["ReplayRedeclare"], &[], &["Nat.pred"]);
    assert_stamps("ReplayForgedQuot", &[]);
}

/// A redeclaration of an imported AXIOM through every `stamp-verified` mode: a
/// definition (`ReplayForgedBoolDef`) and an inductive
/// (`ReplayForgedIndOverAx`), each with a proof of `False` that holds only if
/// the module's declaration replaces the import's axiom. Pinned `leanchecker`
/// refuses both (`(kernel) application type mismatch` for
/// `forged_bool_false`; `(kernel) constant has already been declared
/// 'ind_ax_t'`), and admits nothing of either module. Measured 2026-09-29 on
/// the integrated main before the fix: the default and `--single-pass` modes
/// stamped `bool_ax_b` and `forged_bool_false : False` KernelVerified (the
/// sequential replay filled the imported axiom with the module's value).
#[test]
fn test_stamp_verified_all_modes_refuse_redefinitions_of_imported_axioms() {
    for (module, redeclared) in [
        ("ReplayForgedBoolDef", "bool_ax_b"),
        ("ReplayForgedIndOverAx", "ind_ax_t"),
    ] {
        assert_stamps_run_or_refused_at_import(&[module], &[], &[redeclared]);
    }
}

/// The same two modules through `per-constant-verify`. Measured 2026-09-29 on
/// the integrated main before the fix: `kernel_verified 1` on each, for
/// `forged_bool_false : False` and `forged_ind_false : False` (the demand walk
/// made the module's `bool_ax_b` and its inductive `ind_ax_t` resident in
/// place of the import's axioms).
#[test]
fn test_per_constant_verify_refuses_redefinitions_of_imported_axioms() {
    for module in ["ReplayForgedBoolDef", "ReplayForgedIndOverAx"] {
        let r = per_constant(module, &[]);
        assert_eq!(
            r.kernel_verified, 0,
            "{module}: targets {:?}, errors {:?}",
            r.targets, r.errors
        );
    }
}

/// Hole B through every `stamp-verified` mode. Measured with the round-1
/// binary: `--parallel` stamped `forged_rec_false`, `forged_rule_eq` and
/// `forged_ctor_false`, and the sequential modes stamped `FRR.rec` with its
/// forged rule.
#[test]
fn test_stamp_verified_all_modes_refuse_forged_inductive_blocks() {
    assert_stamps("ReplayForgedRec", &[]);
    assert_stamps("ReplayForgedRule", &[]);
    assert_stamps("ReplayForgedCtor", &[]);
}

/// Hole C through every `stamp-verified` mode. Measured with the round-1
/// binary: every mode stamped all five `ReplayForgedStr` equations.
#[test]
fn test_stamp_verified_all_modes_refuse_disagreeing_string_reducers() {
    assert_stamps("ReplayForgedStr", &[]);
    assert_stamps(
        "ReplayHonestStr",
        &["honest_str_drop_refl", "honest_str_lower_refl"],
    );
}

/// The honest control for the inductive replay, through every mode: every
/// value-bearing declaration of `ReplayHonestInd` is stamped (the sequential
/// modes also stamp the family members themselves).
#[test]
fn test_stamp_verified_all_modes_stamp_honest_inductive_blocks() {
    let wanted = value_bearing("ReplayHonestInd");
    for mode in STAMP_MODES {
        let stamped = stamp(&["ReplayHonestInd"], mode);
        let missing: Vec<&String> = wanted.difference(&stamped).collect();
        assert!(
            missing.is_empty(),
            "stamp-verified {mode:?}: not stamped {missing:?}"
        );
    }
}

/// The sharded verifier on the round-2 forgeries. `ReplayRedeclare` reaches
/// the worker's replay (the default load refused the whole import for
/// `Nat.pred`): pinned `leanchecker ReplayRedeclare` refuses
/// `Nat.pred` (`(kernel) constant has already been declared 'Nat.pred'`), and
/// `redecl_pred`, which uses it, with it.
#[test]
fn test_sharded_verify_module_refuses_round_two_forgeries() {
    let run = |module: &str| sharded(module, 64);
    for (module, forged) in [
        (
            "ReplayPrelude",
            ["prelude_sorry", "prelude_arith", "prelude_ay"].as_slice(),
        ),
        ("ReplayRedeclare", ["Nat.pred", "redecl_pred"].as_slice()),
        ("ReplayForgedQuot", ["forged_quot_false"].as_slice()),
        (
            "ReplayForgedRec",
            ["forged_rec_false", "FRT.rec"].as_slice(),
        ),
        ("ReplayForgedRule", ["forged_rule_eq", "FRR.rec"].as_slice()),
        (
            "ReplayForgedCtor",
            ["forged_ctor_false", "FRC.a"].as_slice(),
        ),
        (
            "ReplayForgedStr",
            [
                "forged_str_drop",
                "forged_str_take",
                "forged_str_trim",
                "forged_str_lower",
                "forged_str_upper",
            ]
            .as_slice(),
        ),
    ] {
        let r = run(module);
        for name in forged {
            assert!(
                !r.kernel_verified_names.iter().any(|n| n == name),
                "{module}: `{name}` verified; failures {:?}",
                r.failures
            );
            assert!(
                r.failures.iter().any(|(n, _)| n == name),
                "{module}: `{name}` not refused; failures {:?}",
                r.failures
            );
        }
    }
    let r = run("ReplayRedeclare");
    assert!(
        r.failures
            .iter()
            .any(|(n, why)| n == "Nat.pred" && why.contains("already declared")),
        "{:?}",
        r.failures
    );
    let r = run("ReplayHonestInd");
    assert_eq!(r.counts.failed, 0, "{:?}", r.failures);
}

/// The private declarations of the `module`-system fixtures (`GenReplayForged.lean`'s `parted`
/// families): each is in `.olean.private` alone, never in the `.olean` a lane parses for a
/// module's own names.
const PRIV_SELF: &str = "_private.ReplayForgedPriv.0.priv_self";
const PRIV_BAD: &str = "_private.ReplayForgedPrivBad.0.priv_bad";
const PRIV_OK: &str = "_private.ReplayHonestPriv.0.priv_ok";

/// A `module`-system artifact's PRIVATE declarations are the module's own: a consumer that is
/// not itself a `module` (`leanchecker`, and every file Clean checks) reads the artifact through
/// its `.olean.private`, which alone holds them, and replays them with the rest. Pinned
/// `leanchecker` (2026-09-29): `ReplayForgedPriv` rc 1 (`(kernel) unknown constant
/// '_private.ReplayForgedPriv.0.priv_self'`), `ReplayForgedPrivBad` rc 1 (`(kernel)
/// declaration type mismatch, '_private.ReplayForgedPrivBad.0.priv_bad'`), `ReplayHonestPriv`
/// rc 0. The sharded worker's replay set was the `.olean`'s names alone, so a private
/// declaration was never replayed: with the module's own parts loaded under the loader's
/// module-trust rule 3 left to that replay, `priv_user : False := priv_self` (a private
/// `False := itself`) was verified, and `priv_bad_user` stood on the never-checked private
/// `priv_bad : False := True.intro`.
#[test]
fn test_sharded_verify_module_replays_private_part_declarations() {
    // Every module's verdict first, so one red run names each hole.
    let mut violations = Vec::new();
    for (module, forged) in [
        ("ReplayForgedPriv", [PRIV_SELF, "priv_user"]),
        ("ReplayForgedPrivBad", [PRIV_BAD, "priv_bad_user"]),
    ] {
        let r = sharded(module, 64);
        let unrefused: Vec<&str> = forged
            .into_iter()
            .filter(|name| !r.failures.iter().any(|(n, _)| n == name))
            .collect();
        if r.counts.kernel_verified != 0 || !unrefused.is_empty() {
            violations.push(format!(
                "{module}: verified {:?}, not refused {unrefused:?}; failures {:?}",
                r.kernel_verified_names, r.failures
            ));
        }
    }
    assert!(violations.is_empty(), "{violations:#?}");
    let r = sharded("ReplayForgedPriv", 64);
    assert!(
        r.failures
            .iter()
            .any(|(n, why)| n == PRIV_SELF && why.contains("refers to itself")),
        "{:?}",
        r.failures
    );
    let r = sharded("ReplayHonestPriv", 64);
    let verified: BTreeSet<&str> = r.kernel_verified_names.iter().map(String::as_str).collect();
    assert_eq!(
        verified,
        BTreeSet::from([PRIV_OK, "priv_ok_user"]),
        "{:?}",
        r.failures
    );
    assert_eq!(r.counts.failed, 0, "{:?}", r.failures);
}

/// The same `module`-system forgeries through `stamp-verified` (every mode) and
/// `per-constant-verify`: neither the private forgery nor its public user may be stamped or
/// verified (a refusal of the whole run at import naming only forged declarations is accepted
/// from `--parallel`, as for the other forgeries), and the honest control keeps its public
/// theorem verified.
#[test]
fn test_stamp_and_per_constant_lanes_refuse_private_part_forgeries() {
    for (module, forged) in [
        ("ReplayForgedPriv", [PRIV_SELF, "priv_user"]),
        ("ReplayForgedPrivBad", [PRIV_BAD, "priv_bad_user"]),
    ] {
        assert_stamps_run_or_refused_at_import(&[module], &[], &forged);
        let r = per_constant(module, &[]);
        assert_eq!(
            r.kernel_verified, 0,
            "{module}: targets {:?}, errors {:?}",
            r.targets, r.errors
        );
    }
    for mode in STAMP_MODES {
        let stamped = stamp(&["ReplayHonestPriv"], mode);
        assert!(
            stamped.contains("priv_ok_user"),
            "stamp-verified {mode:?} on ReplayHonestPriv: {stamped:?}"
        );
    }
    let r = per_constant("ReplayHonestPriv", &[]);
    assert_eq!(r.failed, 0, "{:?}", r.errors);
    assert!(r.kernel_verified >= 1, "{:?}", r.targets);
}

/// A DEFINITION over an imported OPAQUE: `ReplayForgedOpaqueDef` declares `def op_b := true`
/// over `ReplayHonestOpaqueAx`'s `opaque op_b : Bool` (with `axiom op_hb : op_b = false`), and
/// `forged_op_false : False` by `Eq.rec` over `op_hb`, well typed only if `op_b` unfolds to
/// `true`; `ReplayForgedOpaqueUse` states the same proof and lists both modules as imports.
/// Pinned `leanchecker` (2026-09-29): `ReplayHonestOpaqueAx` rc 0; `ReplayForgedOpaqueDef` rc 1,
/// `(kernel) constant has already been declared 'op_b'` (`--fresh` rc 1: `environment already
/// contains 'op_b' from ReplayHonestOpaqueAx`); `ReplayForgedOpaqueUse` rc 1, `import
/// ReplayForgedOpaqueDef failed, environment already contains 'op_b'`. A run over all three must
/// stamp nothing the honest module alone does not. Measured 2026-09-29 by the review, before the
/// fix: `--single-pass` roll-elides each verified target's opaque values before the next, so
/// `op_b` was resident value-free and not an axiom when `ReplayForgedOpaqueDef`'s definition met
/// it, the refusal of a definition over an axiom alone let the checked stub upgrade replace it
/// with `true`, and that module's `op_b` was stamped.
#[test]
fn test_all_lanes_refuse_a_definition_over_an_imported_opaque() {
    let run = [
        "ReplayHonestOpaqueAx",
        "ReplayForgedOpaqueDef",
        "ReplayForgedOpaqueUse",
    ];
    for mode in STAMP_MODES {
        let honest = stamp(&["ReplayHonestOpaqueAx"], mode);
        match (mode, try_stamp(&run, mode)) {
            (_, Ok(stamped)) => assert_eq!(
                stamped, honest,
                "stamp-verified {mode:?} over {run:?} stamped more than the honest module alone"
            ),
            (Some("--parallel"), Err(MathverseCliError::StampImportRefused { names, .. })) => {
                assert_eq!(names, ["op_b"], "stamp-verified --parallel over {run:?}");
            }
            (_, Err(e)) => panic!("stamp-verified {mode:?} over {run:?}: {e}"),
        }
    }
    for module in ["ReplayForgedOpaqueDef", "ReplayForgedOpaqueUse"] {
        let r = per_constant(module, &[]);
        assert_eq!(
            r.kernel_verified, 0,
            "{module}: targets {:?}, errors {:?}",
            r.targets, r.errors
        );
    }
    let r = sharded("ReplayForgedOpaqueDef", 64);
    assert_eq!(
        r.counts.kernel_verified, 0,
        "verified {:?}; failures {:?}",
        r.kernel_verified_names, r.failures
    );
    assert!(
        r.failures
            .iter()
            .any(|(n, why)| n == "op_b" && why.contains("already declared")),
        "{:?}",
        r.failures
    );
    let r = sharded("ReplayHonestOpaqueAx", 64);
    assert_eq!(r.counts.failed, 0, "{:?}", r.failures);
}

/// A redefinition of the KERNEL's `Quot`: `ReplayForgedQuotDef` declares `def Quot := fun {α}
/// _ => α` at `Quot`'s own type over `Init.Core`, and `quot_def_false : False` from `Quot.ind`
/// and `Quot.sound`, which checks only if `Quot r` unfolds to `Bool`. Pinned `leanchecker
/// ReplayForgedQuotDef` (2026-09-29): rc 1, `(kernel) constant has already been declared 'Quot'`
/// (`--fresh` rc 1: `environment already contains 'Quot' from Init.Prelude`). A name the kernel
/// seeded has no declaring artifact, so the `.olean` loader's rule 1 does not see the
/// redeclaration; no lane may let the definition fill the kernel's value-free `Quot`.
#[test]
fn test_all_lanes_refuse_a_redefinition_of_the_kernel_quotient() {
    for mode in STAMP_MODES {
        match try_stamp(&["ReplayForgedQuotDef"], mode) {
            Ok(stamped) => assert!(
                stamped.is_empty(),
                "stamp-verified {mode:?} on ReplayForgedQuotDef stamped {stamped:?}"
            ),
            Err(MathverseCliError::StampImportRefused { names, .. }) => {
                assert_eq!(
                    names,
                    ["Quot"],
                    "stamp-verified {mode:?} on ReplayForgedQuotDef"
                );
            }
            Err(e) => panic!("stamp-verified {mode:?} on ReplayForgedQuotDef: {e}"),
        }
    }
    let r = per_constant("ReplayForgedQuotDef", &[]);
    assert_eq!(
        r.kernel_verified, 0,
        "targets {:?}, errors {:?}",
        r.targets, r.errors
    );
    let r = sharded("ReplayForgedQuotDef", 64);
    assert_eq!(
        r.counts.kernel_verified, 0,
        "verified {:?}; failures {:?}",
        r.kernel_verified_names, r.failures
    );
    assert!(
        r.failures
            .iter()
            .any(|(n, why)| n == "Quot" && why.contains("already declared")),
        "{:?}",
        r.failures
    );
}
