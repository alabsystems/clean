// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R142 (`docs/DECISIONS.md`) through the `.olean` loader and verify-batch: a
//! declaration an artifact's AUTHORITATIVE part (`.olean.private` for a
//! `module`, `.olean` otherwise) states with a value must be resident with
//! that value after a re-check lane's load, whatever kept it out.
//!
//! R131 refused a stub completion the KERNEL refuses. Its verification found
//! the same outcome by other paths (family README, pinned `leanchecker`
//! v4.30.0-rc2):
//!
//! - `ReplayStubMv` / `ReplayStubFv`: the private value carries a metavariable
//!   or a free variable, which Clean's converter cannot read, so the checked
//!   upgrade never ran and the stub stayed trusted (S1-conv). rc 1 in both
//!   modes (`declaration has metavariables` / `free variables`).
//! - `ReplayShadowStub` (and its user): the stub's name and type are an
//!   import's axiom, so the stub dropped as a restatement and the refused
//!   value fell on the import's axiom, which R131's own-stub rows did not
//!   cover (S1-shadow). rc 1 in both modes; the user rc 0 (default) / rc 1
//!   (`--fresh`).
//! - `ReplayShadowThm`: the non-module form, a theorem over the import's
//!   axiom. rc 1 in both modes.
//! - `ReplayQuotIndThm`: a theorem restating the kernel's `Quot.ind`. No load
//!   completes a quotient primitive, so the loader drops it as a restatement
//!   of the resident axiom; only a restated THEOREM is Lean's merge. rc 1 in
//!   both modes (`already declared` / `environment already contains`).
//! - An eliding re-check load (`--closure-elide opaque-and-theorem`) dropped
//!   a completion's value before the checked upgrade, which then never ran.

use super::*;
use clean_kernel::env::ConstantKind as KernelKind;

/// Each module whose load the rule refuses, the artifact it refuses, and the
/// declaration it names.
const VALUE_NOT_RESIDENT: [(&str, &str, &str); 6] = [
    ("ReplayStubMv", "ReplayStubMv", "smv_f"),
    ("ReplayStubFv", "ReplayStubFv", "sfv_f"),
    ("ReplayShadowStub", "ReplayShadowStub", "sha_n"),
    ("ReplayShadowStubUser", "ReplayShadowStub", "sha_n"),
    ("ReplayShadowThm", "ReplayShadowThm", "sha_n"),
    ("ReplayQuotIndThm", "ReplayQuotIndThm", "Quot.ind"),
];

fn needle(artifact: &str, name: &str) -> String {
    format!("`{artifact}` states `{name}` with a value the environment does not hold")
}

#[test]
fn test_loader_refuses_a_declaration_whose_authoritative_value_is_not_resident() {
    for (module, artifact, name) in VALUE_NOT_RESIDENT {
        let error = match try_load(module) {
            Ok(_) => {
                panic!("{module}: `{name}`'s value is not resident; the import must be refused")
            }
            Err(error) => error,
        };
        assert!(
            error.contains(&needle(artifact, name)),
            "{module}: refused without naming `{name}`: {error}"
        );
    }
    // Controls: the import itself, and a module in the stub layout whose values
    // the kernel admits.
    try_load("ReplayShadowAx").expect("the honest axiom module loads");
    try_load("ReplayStubHonest").expect("the honest stub layout loads");
}

#[test]
fn test_verify_batch_in_run_refuses_a_value_the_load_did_not_make_resident() {
    let mut run = InRun::new();
    for (module, artifact, name) in [
        ("ReplayStubMv", "ReplayStubMv", "smv_f"),
        ("ReplayShadowStub", "ReplayShadowStub", "sha_n"),
    ] {
        let result = run.run(module, false);
        assert!(
            !result.load_ok,
            "{module}: the load must be refused, not checked: {result:?}"
        );
        let error = result.load_error.as_deref().unwrap_or_default();
        assert!(error.contains(&needle(artifact, name)), "{module}: {error}");
        assert_eq!((result.tc_pass, result.tc_fail), (0, 0), "{result:?}");
    }
}

/// An eliding re-check load checks a completion before it drops the value:
/// `ReplayStubRefusedDep`'s refused `srd_t` refuses the import, and the honest
/// stub layout loads with its theorems completed, their values then dropped.
#[test]
fn test_an_eliding_recheck_load_checks_a_completion_before_dropping_its_value() {
    let policy = OleanImportPolicy::default()
        .refusing_refused_completions()
        .with_proof_elision(ProofValueElision::OpaqueAndTheorem);
    let load = |module: &str| {
        let mut env = Environment::for_lean_replay();
        let mut search = vec![compiled_fixture_dir(FAMILY)];
        search.extend(default_search_paths());
        let mut visited = hashbrown::HashSet::new();
        load_module_with_deps_shared_with_policy(&mut env, module, &search, &mut visited, policy)
            .map(|_| env)
            .map_err(|e| e.to_string())
    };
    let error = match load("ReplayStubRefusedDepUser") {
        Ok(_) => panic!("an eliding re-check load still refuses a refused completion"),
        Err(error) => error,
    };
    assert!(
        error.contains("completes the value-free `srd_t` with a value the kernel refuses"),
        "{error}"
    );
    let env = load("ReplayStubHonest").expect("the honest stub layout loads");
    for name in ["sh_t", "sh_u"] {
        let resident = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("`{name}` is resident"));
        assert_eq!(
            (resident.kind, resident.value.is_none()),
            (KernelKind::Theorem, true),
            "`{name}` is completed, then its value dropped by the policy: {resident:?}"
        );
    }
}

/// The loader's own guard, that no stub upgrade fills a quotient primitive,
/// where R142's invariant does not run. A re-check load of
/// `ReplayForgedQuotDef` (`def Quot := fun {α} _ => α` at `Quot`'s own type;
/// pinned `leanchecker`: already declared 'Quot') is refused twice over: the
/// guard keeps the kernel's `Quot`, and a filled one would be another
/// declaration holding the name. The default policy, an elaborator's import,
/// checks no invariant, so there the guard alone keeps the kernel's
/// value-free quotient, and the module's definition is recorded as shadowed.
/// Before the guard, that definition passed the checked upgrade there
/// (measured 2026-09-29).
#[test]
fn test_the_default_import_keeps_the_kernel_quotient_over_a_redefinition() {
    let mut env = Environment::for_lean_replay();
    let mut search = vec![compiled_fixture_dir(FAMILY)];
    search.extend(default_search_paths());
    let mut visited = hashbrown::HashSet::new();
    let summaries = load_module_with_deps_shared_with_policy(
        &mut env,
        "ReplayForgedQuotDef",
        &search,
        &mut visited,
        OleanImportPolicy::default(),
    )
    .unwrap_or_else(|e| panic!("the default import of ReplayForgedQuotDef: {e}"));
    let quot = Name::from_string("Quot");
    let resident = env.get_const(&quot).expect("`Quot` is resident");
    assert!(
        env.get_quot(&quot).is_some() && resident.value.is_none(),
        "the kernel's value-free `Quot` stays: {resident:?}"
    );
    assert!(
        summaries.iter().any(|s| s
            .shadowed_declarations
            .iter()
            .any(|(name, _)| *name == quot)),
        "the module's `Quot` is recorded as shadowed"
    );
}
