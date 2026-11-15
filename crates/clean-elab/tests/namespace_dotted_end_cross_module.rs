// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `end A.B` closes BOTH namespace components — the CROSS-MODULE consequence.
//!
//! ## The defect
//!
//! `NamespaceState::exit_namespace` dropped exactly one dotted component,
//! whatever its matching `enter_namespace` had pushed. `namespace Alpha.Beta`
//! pushes two, so `end Alpha.Beta` left `Alpha` open for the rest of the file
//! and every later declaration registered under a leaked prefix.
//!
//! This is measurable in the pinned SRCELAB slice, not hypothetical:
//! `Mathlib/Order/Basic.lean` registers declarations as
//! `Mathlib.Tactic.LE.LE.LT.DenselyOrdered`, which is
//! `namespace Mathlib.Tactic.GCongr` / `end` leaving `Mathlib.Tactic`, two
//! `namespace LE.le` / `end` leaving `LE.LE`, and `namespace LT.lt` / `end`
//! leaving `LT`, composed.
//!
//! ## Why it took a cross-module probe to expose
//!
//! WITHIN one file the defect self-cancels and is INVISIBLE. The leaked prefix
//! is in `current_namespace`, so a later `theorem uses := Gamma.g_inside`
//! resolves `Gamma.g_inside` by walking that same leaked prefix outward, finds
//! the equally-leaked `Alpha.Gamma.g_inside`, and elaborates. Both the wrong
//! registration and the wrong lookup cancel. The defect had therefore never
//! appeared as a single-file failure, and was deliberately not ranked as a
//! brick in `docs/plans/BRICK_QUEUE_2026-08-31-C.md`.
//!
//! Across a module boundary the two halves come apart: the importer has its
//! own file context with no leak, so it spells the name the way Lean does and
//! the name is not there. Measured through the production path
//! (`target/release/clean check`, two real `.lean` modules, real `import`):
//!
//! ```text
//!                                   Lean 4.30.0-rc2   Clean before   Clean after
//!   `Gamma.g_inside`      (correct)      PASS             FAIL           PASS
//!   `Alpha.Gamma.g_inside` (leaked)      FAIL             PASS           FAIL
//! ```
//!
//! i.e. the polarity was exactly inverted, and is now exactly Lean's. The Lean
//! transcript for the leaked spelling is
//! `error(lean.unknownIdentifier): Unknown identifier `Alpha.Gamma.g_inside``.
//!
//! ## What this test drives
//!
//! An `import` is, semantically, a shared `Environment` reached by a module
//! that has its OWN `FileContext`. So the producer fixture is elaborated into
//! an environment, and each consumer fixture is elaborated against that same
//! environment with a fresh `FileContext` — the configuration in which the
//! self-cancellation cannot save a leaked name. Every accept below is
//! kernel-checked by `elaborate_decl_and_register`.
//!
//! The mechanism itself is pinned separately and more finely by
//! `namespace::tests::test_enter_exit_namespace_are_inverse_for_mixed_shapes`
//! and its two Lean-pinned witnesses in `crates/clean-elab/src/namespace_tests.rs`.

use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

fn fixture(name: &str) -> String {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/namespace_dotted_end")
        .join(name);
    std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture must exist at {}: {e}", path.display()))
}

/// Elaborate `source` as its own MODULE against `env`: ONE `FileContext` for
/// the whole module, the shared environment. Returns each declaration's
/// outcome in source order.
///
/// The single `FileContext` is load-bearing, not tidiness. A namespace leak
/// lives in the file context's namespace state BETWEEN top-level declarations,
/// so a harness that elaborates each one against a fresh context cannot
/// observe it at all. This harness used `elaborate_decl_and_register`, which
/// takes no context and therefore builds a throwaway `FileContext` per
/// namespace block (`lib.rs`'s `Namespace` arm, `temp_fc`) — under it all
/// three dotted-`end` assertions below PASSED with `exit_namespace` reverted
/// to the pre-6557c358d one-component pop, i.e. they were vacuous. Measured by
/// mutation, not read off the source.
fn elaborate_module(env: &mut Environment, source: &str) -> Vec<Result<ElabResult, String>> {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).expect("fixture must parse");
    decls
        .iter()
        .map(|decl| {
            let processed = preprocess_decl_with_context(decl, &mut file_ctx);
            elaborate_decl_and_register_with_context(env, &processed, &mut file_ctx)
                .map_err(|e| e.to_string())
        })
        .collect()
}

fn producer_env() -> Environment {
    let mut env = Environment::with_prelude();
    for (idx, outcome) in elaborate_module(&mut env, &fixture("producer.lean"))
        .into_iter()
        .enumerate()
    {
        if let Err(e) = outcome {
            panic!("producer declaration #{idx} must elaborate, got: {e}");
        }
    }
    env
}

/// The registration half: a declaration after a dotted `end` carries NO leaked
/// prefix.
#[test]
fn declaration_after_dotted_end_registers_without_a_leaked_prefix() {
    let env = producer_env();

    for name in ["Alpha.Beta.b_inside", "Gamma.g_inside", "after_everything"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "`{name}` is the name Lean 4.30.0-rc2 gives this declaration, so it \
             must be the name Clean registers"
        );
    }

    // The negative half. Without it this test passes on an implementation that
    // registers BOTH spellings, which would leave every importing module free
    // to depend on a name Lean does not have.
    for leaked in [
        "Alpha.Gamma.g_inside",
        "Alpha.after_everything",
        "Alpha.Beta.Gamma.g_inside",
    ] {
        assert!(
            env.get_const(&Name::from_string(leaked)).is_none(),
            "`{leaked}` is a leaked-prefix name Lean 4.30.0-rc2 rejects with \
             `Unknown identifier`; Clean must not mint it"
        );
    }
}

/// The consequence half: an IMPORTING module — fresh file context, no leak of
/// its own to cancel against — reaches those declarations by their Lean names.
///
/// This is the assertion that was RED before the fix, with
/// `Unknown identifier: g_inside`.
#[test]
fn an_importing_module_resolves_the_lean_correct_names() {
    let mut env = producer_env();
    let outcomes = elaborate_module(&mut env, &fixture("consumer_correct.lean"));
    assert_eq!(
        outcomes.len(),
        3,
        "consumer fixture declares three theorems"
    );
    for (idx, outcome) in outcomes.into_iter().enumerate() {
        if let Err(e) = outcome {
            panic!(
                "consumer theorem #{idx} spells its reference the way Lean \
                 4.30.0-rc2 does, so it must elaborate; got: {e}"
            );
        }
    }
    for thm in ["uses_gamma", "uses_alpha_beta", "uses_root"] {
        assert!(
            env.get_const(&Name::from_string(thm)).is_some(),
            "`{thm}` must be registered after the consumer module elaborates"
        );
    }
}

/// The negative control: the leaked spelling must FAIL, exactly as it does on
/// the pinned Lean binary. Before the fix this one PASSED — the inverted
/// polarity — so a fix that merely made both spellings work would be caught
/// here rather than declared a success.
#[test]
fn an_importing_module_rejects_the_leaked_name() {
    let mut env = producer_env();
    let outcomes = elaborate_module(&mut env, &fixture("consumer_leaked.lean"));
    assert_eq!(outcomes.len(), 1, "control fixture declares one theorem");
    assert!(
        outcomes[0].is_err(),
        "`Alpha.Gamma.g_inside` is `Unknown identifier` on Lean 4.30.0-rc2; \
         Clean accepting it means the namespace leak is back"
    );
    assert!(
        env.get_const(&Name::from_string("uses_leaked")).is_none(),
        "a refused theorem must not be registered"
    );
}

// ===========================================================================
// The PARTIAL `end` half of the same defect: `end` pops by the END name's
// width, not by the `namespace` name's.
// ===========================================================================

/// Elaborate the partial-`end` producer, tolerating failures so the probe can
/// report which NAME was minted rather than dying on the first mismatch.
fn partial_end_env() -> Environment {
    let mut env = Environment::with_prelude();
    for (idx, outcome) in elaborate_module(&mut env, &fixture("producer_partial_end.lean"))
        .into_iter()
        .enumerate()
    {
        if let Err(e) = outcome {
            panic!("partial-end producer declaration #{idx} must elaborate, got: {e}");
        }
    }
    env
}

/// `end Pretriv` against `namespace Bundle.Pretriv` closes exactly ONE scope.
///
/// Ground truth, Lean 4.30.0-rc2 (`set_option pp.fullNames true`):
///
/// ```text
///   namespace Bundle.Pretriv / def inner / end Pretriv
///   def after_partial / end Bundle
///     => Bundle.Pretriv.inner : Nat
///        Bundle.after_partial : Nat
///   #check @after_partial
///     => error(lean.unknownIdentifier): Unknown identifier `after_partial`
/// ```
///
/// `end Alpha` against an open `Alpha.Beta` is the error case, and Lean names
/// the remedy: "you must end all the intervening scopes: `end Alpha.Beta`".
/// So the pop width is the `end` name's component count — one for `end
/// Pretriv`, two for `end Alpha.Beta` — and neither the entered width nor a
/// fixed 1 reproduces both.
#[test]
fn a_partial_end_closes_only_the_components_it_names() {
    let env = partial_end_env();

    assert!(
        env.get_const(&Name::from_string("Bundle.Pretriv.inner"))
            .is_some(),
        "`Bundle.Pretriv.inner` is the Lean 4.30.0-rc2 name of the inner \
         declaration"
    );
    assert!(
        env.get_const(&Name::from_string("Bundle.after_partial"))
            .is_some(),
        "`end Pretriv` closes ONE scope, so `Bundle` is still open and Lean \
         4.30.0-rc2 names this declaration `Bundle.after_partial`; registering \
         it anywhere else means `end` popped by the wrong width"
    );

    // The negative half: over-popping mints the bare root name, which Lean
    // rejects. Under-popping (the pre-6557c358d one-component pop applied to
    // the ENTERED name) is caught by the sibling dotted-`end` tests above.
    assert!(
        env.get_const(&Name::from_string("after_partial")).is_none(),
        "a bare `after_partial` is `Unknown identifier` on Lean 4.30.0-rc2; \
         minting it means `end Pretriv` closed both components"
    );
}

/// The cross-module consequence, in the configuration where an in-file
/// reference cannot self-cancel against the same wrong prefix.
#[test]
fn an_importing_module_resolves_a_partial_ends_outer_prefix() {
    let mut env = partial_end_env();
    let outcomes = elaborate_module(&mut env, &fixture("consumer_partial_end.lean"));
    assert_eq!(outcomes.len(), 2, "consumer fixture declares two theorems");
    for (idx, outcome) in outcomes.into_iter().enumerate() {
        if let Err(e) = outcome {
            panic!(
                "partial-end consumer theorem #{idx} spells its reference the \
                 way Lean 4.30.0-rc2 does, so it must elaborate; got: {e}"
            );
        }
    }
}

/// `end B.C` against `namespace A.B.C` closes exactly TWO components.
///
/// This is the case that separates Lean's rule — the `end` name's component
/// count — from the convenient approximation "a partial `end` closes its
/// leaf", which satisfies the `end Pretriv` fixture above exactly and is wrong
/// here: it would leave `A.B` open and register `A.B.mid`.
///
/// Ground truth, Lean 4.30.0-rc2 (`set_option pp.fullNames true`):
/// `A.B.C.deep : Nat` and `A.mid : Nat`.
#[test]
fn a_multi_component_partial_end_closes_exactly_the_components_it_names() {
    let mut env = Environment::with_prelude();
    for (idx, outcome) in elaborate_module(&mut env, &fixture("producer_suffix_end.lean"))
        .into_iter()
        .enumerate()
    {
        if let Err(e) = outcome {
            panic!("suffix-end producer declaration #{idx} must elaborate, got: {e}");
        }
    }

    for name in ["A.B.C.deep", "A.mid"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "`{name}` is the Lean 4.30.0-rc2 name for this declaration"
        );
    }
    for wrong in ["A.B.mid", "mid", "A.B.C.mid"] {
        assert!(
            env.get_const(&Name::from_string(wrong)).is_none(),
            "`{wrong}` is not a name Lean 4.30.0-rc2 mints here; `end B.C` \
             closes exactly two components, so `mid` is `A.mid`"
        );
    }

    let outcomes = elaborate_module(&mut env, &fixture("consumer_suffix_end.lean"));
    for (idx, outcome) in outcomes.into_iter().enumerate() {
        if let Err(e) = outcome {
            panic!("suffix-end consumer theorem #{idx} must elaborate; got: {e}");
        }
    }
}

/// The negative control: the over-popped spelling must FAIL, as on Lean.
#[test]
fn an_importing_module_rejects_a_partial_ends_over_popped_name() {
    let mut env = partial_end_env();
    let outcomes = elaborate_module(&mut env, &fixture("consumer_partial_end_overpopped.lean"));
    assert_eq!(outcomes.len(), 1, "control fixture declares one theorem");
    assert!(
        outcomes[0].is_err(),
        "`after_partial` is `Unknown identifier` on Lean 4.30.0-rc2; Clean \
         accepting it means `end Pretriv` over-popped to the root"
    );
}
