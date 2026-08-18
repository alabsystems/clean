// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared test utilities for clean-verify.
//!
//! This module provides common helpers for tests that need larger stack sizes
//! to handle deep recursion during proof term elaboration.
//! Stack size constants are centralized in `clean_kernel::test_utils` (#2101).
//!
//! # The shared-specification cache — what it is, and why it is sound
//!
//! Building the full specification parses, elaborates and kernel-checks every
//! spec declaration; one build costs tens of minutes. ~700 `spec::*` tests each
//! call [`build_spec_with_stack`], and each call used to rebuild the whole
//! thing, so the `clean-verify` lib target cost about one full build per test —
//! measured at 3,659s for a single test running alone, and a 43,200s (12h)
//! timeout for the target as a whole.
//!
//! Each builder below now builds its specification **once per process** and
//! hands every caller a `clone()` of that value. Nothing else changes: the
//! signature still returns an owned `Specification`, so every existing caller —
//! including the ones that append declarations to it — keeps working unchanged.
//!
//! Isolation is by ownership, not by convention:
//!
//! * [`Specification`] is a plain value: a [`clean_kernel::Environment`], a
//!   `HashMap<String, SpecDefinition>`, and an `Option<String>`. Cloning
//!   deep-copies every map, so a caller that registers a declaration, mutates a
//!   `proof_status`, or reaches for `env_mut()` mutates ITS OWN copy.
//! * The only structure shared between clones is the immutable term DAG:
//!   `Expr` children are `Arc<Expr>` and `Name` components are interned `Arc`s.
//!   Neither is mutable — `clean-kernel` is `#![forbid(unsafe_code)]` and
//!   carries no `Cell`/`RefCell`/`Mutex`/atomic inside `Expr`, `Level`, `Name`
//!   or `ConstantInfo` — so no clone can observe another clone's writes through
//!   them. The one `Arc<dyn ConstantSource>` field (`Environment::lazy_source`)
//!   is `None` here: nothing in `clean-verify` installs a lazy source.
//! * A clone is also *stack-safe on the caller's thread*: `Expr::clone` copies
//!   one node and bumps `Arc`s (no recursion), and deep trees already drop
//!   iteratively (`clean_kernel::expr::drop`).
//!
//! `tests::test_spec_clone_registration_does_not_leak_to_siblings` and
//! `tests::test_shared_spec_matches_a_fresh_build` hold that story to account.
//!
//! Set `CLEAN_VERIFY_SPEC_CACHE=0` to opt every builder back onto a fresh
//! per-call build. That knob exists so the cached and uncached paths can be
//! differentially compared on one binary; it can only make a run slower, never
//! weaker.
//!
//! The cache is deliberately **in-process only**. Persisting a built
//! specification would drop `Environment`'s `#[serde(skip)]`
//! `declaration_verification` provenance and let a run inherit a kernel-checked
//! claim it never rechecked; that trade is not available here at any speedup.

use crate::spec::{SpecError, Specification};
use std::sync::OnceLock;

/// Stack size for tests requiring deep recursion (64MB).
///
/// Specification construction + cross-validation elaborates complex proof terms
/// that recurse deeply through the kernel and elaborator. 16MB (DEFAULT_STACK)
/// was insufficient after Wave 0/1 infrastructure additions increased
/// elaboration depth.
pub const TEST_STACK_SIZE: usize = clean_kernel::test_utils::LARGE_STACK;

/// Run a function on a thread with a larger stack.
///
/// Delegates to `clean_kernel::test_utils::run_with_stack` with `DEFAULT_STACK`.
///
/// # Example
/// ```no_run
/// # use clean_verify::test_utils::run_with_stack;
/// let result = run_with_stack(|| 42);
/// assert_eq!(result, 42);
/// ```
pub fn run_with_stack<F, T>(f: F) -> T
where
    F: FnOnce() -> T + Send + 'static,
    T: Send + 'static,
{
    clean_kernel::test_utils::run_with_stack(TEST_STACK_SIZE, f)
}

/// Whether the shared-specification cache is enabled (the default).
///
/// `CLEAN_VERIFY_SPEC_CACHE=0` disables it, restoring a fresh build per call.
fn spec_cache_enabled() -> bool {
    !matches!(
        std::env::var("CLEAN_VERIFY_SPEC_CACHE").as_deref(),
        Ok("0") | Ok("off") | Ok("false")
    )
}

/// One process-wide build of a specification flavour, kept for cloning.
///
/// The `Result` is stored rather than unwrapped so a build failure surfaces
/// with its own error in EVERY test that asks for the specification, exactly as
/// it did when every test built its own — instead of one real error followed by
/// a cascade of `OnceLock` poison reports.
type SpecCell = OnceLock<Result<Specification, String>>;

/// Build `build()` once per process, on a large stack, and return the stored
/// value. Panics with `panic_msg` (plus the build error) on every call if the
/// build failed, matching the pre-cache `.expect(panic_msg)` behaviour.
fn cached_spec(
    cell: &'static SpecCell,
    build: fn() -> Result<Specification, SpecError>,
    label: &'static str,
    panic_msg: &'static str,
) -> &'static Specification {
    let stored = cell.get_or_init(move || {
        run_with_stack(move || {
            let started = std::time::Instant::now();
            let built = build().map_err(|error| format!("{error:?}"));
            eprintln!(
                "[clean-verify test_utils] {label}: one process-wide build took {:.1}s",
                started.elapsed().as_secs_f64()
            );
            built
        })
    });
    match stored {
        Ok(spec) => spec,
        Err(error) => panic!("{panic_msg}: {error}"),
    }
}

static FULL_SPEC: SpecCell = OnceLock::new();
static EVAL_IR_SPEC: SpecCell = OnceLock::new();
static IMPL_SOUNDNESS_SPEC: SpecCell = OnceLock::new();
static SUBSTITUTION_SPEC: SpecCell = OnceLock::new();

/// The process-wide full specification, borrowed.
///
/// Read-only callers may borrow this instead of cloning; callers that need to
/// append declarations want [`build_spec_with_stack`], which hands back an
/// owned copy.
#[must_use]
pub fn shared_spec() -> &'static Specification {
    cached_spec(
        &FULL_SPEC,
        Specification::new,
        "full Specification::new()",
        "spec should build",
    )
}

/// Build a specification on a thread with larger stack.
///
/// Specification building involves deep recursion during proof term elaboration,
/// so it requires a larger stack than the default test thread provides.
///
/// The heavy build happens once per process (see the module docs); this hands
/// back an owned clone of it, so callers may mutate the result freely.
pub fn build_spec_with_stack() -> Specification {
    if spec_cache_enabled() {
        shared_spec().clone()
    } else {
        run_with_stack(|| Specification::new().expect("spec should build"))
    }
}

/// Build the `EvalIR` subset of the specification (crystal job C3) on a larger
/// stack: foundation types plus the trust-ir executable-semantics stage.
///
/// Used by the EvalIR witness tests and by the vacuity firewall's audit of the
/// EvalIR relations. Much cheaper than the full spec — EvalIR depends on nothing
/// but `Nat`, `Bool` and `Eq`. Built once per process; see the module docs.
#[cfg(any(test, feature = "test-utils"))]
pub fn build_eval_ir_spec_with_stack() -> Specification {
    if spec_cache_enabled() {
        cached_spec(
            &EVAL_IR_SPEC,
            Specification::new_eval_ir_spec,
            "EvalIR specification",
            "EvalIR test spec should build",
        )
        .clone()
    } else {
        crate::eval_ir::build_spec_with_stack().expect("EvalIR test spec should build")
    }
}

/// Build the implementation-soundness subset of the specification on a larger stack.
///
/// This avoids full-spec construction in focused implementation-soundness tests,
/// which keeps their dependency surface aligned with the modules under test.
/// Built once per process; see the module docs.
#[cfg(any(test, feature = "test-utils"))]
pub fn build_implementation_soundness_spec_with_stack() -> Specification {
    if spec_cache_enabled() {
        cached_spec(
            &IMPL_SOUNDNESS_SPEC,
            Specification::new_implementation_soundness_test_spec,
            "implementation-soundness specification",
            "implementation-soundness test spec should build",
        )
        .clone()
    } else {
        run_with_stack(|| {
            Specification::new_implementation_soundness_test_spec()
                .expect("implementation-soundness test spec should build")
        })
    }
}

/// Build the substitution/WHNF subset of the specification on a larger stack.
///
/// This is not a small bundle — 91 of the 158 registration stages are in it —
/// so the ~30 modules whose tests build it were paying most of a full spec
/// build each. Built once per process; see the module docs.
#[cfg(any(test, feature = "test-utils"))]
pub fn build_substitution_spec_with_stack() -> Specification {
    if spec_cache_enabled() {
        cached_spec(
            &SUBSTITUTION_SPEC,
            Specification::new_substitution_test_spec,
            "substitution specification",
            "substitution test spec should build",
        )
        .clone()
    } else {
        run_with_stack(|| {
            Specification::new_substitution_test_spec()
                .expect("substitution test spec should build")
        })
    }
}

/// Parse-check a specification declaration WITHOUT elaborating it.
///
/// `add_recursive_def` parses first and elaborates second, so a malformed
/// source dies at parse time — but only once the whole specification is being
/// built, which costs ~27 minutes. Parsing one declaration costs microseconds.
///
/// This exists because two failures in a row were parse errors, not proof
/// errors: a parenthesised `forall` in argument position (which this parser
/// rejects), and a `fun` keyword dropped by a mechanical edit. Neither is
/// visible to `cargo check`, since specification sources are Rust string
/// literals, and neither is visible to a paren-balance check — the second one
/// balances perfectly and simply is not a lambda.
///
/// Use it in a module's unit tests on every source that module generates. Those
/// run in milliseconds and turn the commonest failure class into instant
/// feedback.
pub fn parse_check(source: &str) -> Result<(), String> {
    clean_parser::parse_decl(source)
        .map(|_| ())
        .map_err(|e| format!("{e}"))
}

#[cfg(test)]
mod tests {
    use super::{build_spec_with_stack, run_with_stack, shared_spec};
    use crate::spec::{ProofStatus, Specification};
    use clean_kernel::Name;

    /// One line per definition, comparable and sortable without requiring `Ord`
    /// on the label enums.
    fn definition_fingerprints(spec: &Specification) -> Vec<String> {
        let mut rows: Vec<String> = spec
            .definitions()
            .values()
            .map(|def| {
                format!(
                    "{}|{:?}|{:?}|axiom={}|has_value={}|deps={}",
                    def.name,
                    def.category,
                    def.proof_status,
                    def.is_axiom,
                    def.value_src.is_some(),
                    def.axiom_deps.len(),
                )
            })
            .collect();
        rows.sort();
        rows
    }

    fn constant_names(spec: &Specification) -> Vec<String> {
        let mut names: Vec<String> = spec.env().constants().map(|c| c.name.to_string()).collect();
        names.sort();
        names
    }

    /// A declaration registered in one handed-out specification must not be
    /// visible in any other, nor in the shared value they were cloned from.
    ///
    /// This is the whole soundness question of the cache: if it failed, a test
    /// could pass because an earlier test registered something.
    #[test]
    fn test_spec_clone_registration_does_not_leak_to_siblings() {
        let probe = "spec_cache_isolation_probe";
        let probe_name = Name::from_string(probe);

        let mut first = build_spec_with_stack();
        let second = build_spec_with_stack();

        assert!(
            first.get_definition(probe).is_none(),
            "probe must not already exist"
        );
        first
            .add_recursive_def(
                "def spec_cache_isolation_probe (n : Nat) : Nat := n",
                "shared-spec isolation probe",
            )
            .expect("probe should register in the caller's own copy");
        assert!(
            first.get_definition(probe).is_some(),
            "probe should be visible in the copy it was registered in"
        );
        assert!(
            first.env().get_const(&probe_name).is_some(),
            "probe should be visible in the copy's own kernel environment"
        );

        assert!(
            second.get_definition(probe).is_none(),
            "probe leaked into a sibling specification"
        );
        assert!(
            second.env().get_const(&probe_name).is_none(),
            "probe leaked into a sibling specification's kernel environment"
        );
        assert!(
            shared_spec().get_definition(probe).is_none(),
            "probe leaked into the shared specification"
        );
        assert!(
            shared_spec().env().get_const(&probe_name).is_none(),
            "probe leaked into the shared specification's kernel environment"
        );

        let third = build_spec_with_stack();
        assert!(
            third.get_definition(probe).is_none(),
            "probe leaked into a specification handed out after the mutation"
        );
        assert!(
            third.env().get_const(&probe_name).is_none(),
            "probe leaked into a later specification's kernel environment"
        );
    }

    /// Mutating a definition's `proof_status` in one copy must not be visible
    /// in another: the promotion pipeline does exactly this, in many tests.
    #[test]
    fn test_spec_clone_definition_mutation_does_not_leak() {
        let mut first = build_spec_with_stack();
        let name = first
            .definitions()
            .keys()
            .min()
            .cloned()
            .expect("specification has definitions");
        let before = first
            .get_definition(&name)
            .expect("definition exists")
            .proof_status;
        let flipped = match before {
            ProofStatus::DerivedProved => ProofStatus::Axiom,
            _ => ProofStatus::DerivedProved,
        };

        first
            .definitions_mut()
            .get_mut(&name)
            .expect("definition exists")
            .proof_status = flipped;

        let second = build_spec_with_stack();
        assert_eq!(
            second
                .get_definition(&name)
                .expect("definition exists")
                .proof_status,
            before,
            "proof_status mutation leaked into a sibling specification"
        );
        assert_eq!(
            shared_spec()
                .get_definition(&name)
                .expect("definition exists")
                .proof_status,
            before,
            "proof_status mutation leaked into the shared specification"
        );
    }

    /// The cached specification must be indistinguishable from one built fresh
    /// by `Specification::new()` — the same definitions with the same honesty
    /// labels, and the same kernel environment contents.
    ///
    /// This costs one extra full build in the process that runs it, and it is
    /// the gate that keeps the cache from drifting away from the real builder.
    #[test]
    fn test_shared_spec_matches_a_fresh_build() {
        let fresh = run_with_stack(|| Specification::new().expect("spec should build"));

        assert_eq!(
            definition_fingerprints(shared_spec()),
            definition_fingerprints(&fresh),
            "cached specification definitions differ from a fresh build"
        );
        assert_eq!(
            constant_names(shared_spec()),
            constant_names(&fresh),
            "cached specification kernel environment differs from a fresh build"
        );
        assert_eq!(
            shared_spec().axiom_category_stats(),
            fresh.axiom_category_stats(),
            "cached specification axiom census differs from a fresh build"
        );
    }
}
