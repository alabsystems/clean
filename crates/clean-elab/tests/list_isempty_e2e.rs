// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `List.isEmpty` — elaboration, computation and the value-distinguishing
//! soundness twins, over the prelude registration in clean-kernel
//! `env/data.rs`.
//!
//! WHY THIS FILE EXISTS RATHER THAN A BLOCK IN `src/lean4_corpus_tests.rs`.
//! These two tests arrived on the `agents/prelude-bits-20260916` side branch
//! and were appended to the R-series corpus, which their own header said they
//! were not part of ("carries no R-number on purpose"). That file is the
//! subject of the `everyday-battery` R7 FRESHNESS PIN in
//! `data/gate_demonstrations.json`: the pin is a sha256 of the whole file, so
//! appending anything to it turns `scripts/check_gate_registry.py` red until
//! the demonstration — a tens-of-minutes `clean-elab --lib` mutation arm — is
//! re-run and re-pinned. MEASURED 2026-09-19: with the two tests appended the
//! gate reports `R7 FRESH: everyday-battery was demonstrated against
//! crates/clean-elab/src/lean4_corpus_tests.rs at sha256:671fcb0fe88c, the
//! tree has sha256:a332d227b9c7`; with them here instead, that file is
//! byte-identical to `origin/main` and the gate is green.
//!
//! Nothing about the coverage changes: every declaration, every `rfl` and
//! every refused twin below is the one the appended block asserted, rebuilt on
//! the public API the other `tests/` e2e files use. Re-pinning R7 blind is
//! what that row's own note records refusing, so the fixture moved instead.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

/// Elaborate and kernel-register every declaration in `source`.
///
/// Descends `ElabResult::Multiple` and fails on any `Failed` leaf: a
/// `namespace … end` block returns `Ok(Multiple([…]))` even when a CHILD
/// declaration failed, so an `is_ok()` check alone passes on a file whose
/// declarations silently did not elaborate.
fn register(env: &mut Environment, source: &str) -> Result<(), String> {
    fn failures(result: &ElabResult) -> Result<(), String> {
        match result {
            ElabResult::Multiple(results) => {
                for result in results {
                    failures(result)?;
                }
                Ok(())
            }
            ElabResult::Failed { name, error, .. } => Err(format!("{name}: {error}")),
            _ => Ok(()),
        }
    }
    let mut context = FileContext::new();
    for decl in parse_file(source).map_err(|error| format!("parse error: {error}"))? {
        let processed = preprocess_decl_with_context(&decl, &mut context);
        let result = elaborate_decl_and_register(env, &processed)
            .map_err(|error| format!("elaborate/kernel-check error: {error}"))?;
        failures(&result)?;
    }
    Ok(())
}

/// A `rfl` theorem that must be ACCEPTED, and whose proof must close with an
/// EMPTY axiom closure — a `sorry`-bearing or axiom-bearing accept would prove
/// the same statement while proving nothing about `List.isEmpty`.
fn accepts_axiom_free(env: &mut Environment, name: &str, statement: &str) {
    register(env, &format!("theorem {name} : {statement} := rfl"))
        .unwrap_or_else(|error| panic!("{statement} must be provable by rfl: {error}"));
    let deps = env
        .axiom_deps(&Name::from_string(name))
        .expect("registered theorem");
    assert!(
        deps.is_empty(),
        "{statement} closed over axioms {deps:?}; an axiom-bearing accept is not a computation",
    );
}

/// A `rfl` theorem that must be REFUSED, loudly, and must leave no constant
/// behind.
fn refuses(env: &mut Environment, name: &str, statement: &str) {
    let error = register(env, &format!("theorem {name} : {statement} := rfl"))
        .expect_err("the wrong computational result must be rejected");
    assert!(
        !error.contains("parse error"),
        "the negative twin must PARSE, so that it is refused for its meaning \
         rather than its syntax: {error}",
    );
    assert!(
        !error.to_lowercase().contains("sorryax"),
        "no sorry fallback: {error}",
    );
    assert!(
        env.get_const(&Name::from_string(name)).is_none(),
        "false theorem `{name}` was registered anyway",
    );
}

/// `List.isEmpty : {α} → List α → Bool`, transcribed from Lean v4.30.0-rc2
/// `src/Init/Data/List/Basic.lean` (`| [] => true | _ :: _ => false`) as a
/// `List.rec` fold with motive `fun _ => Bool`. Without it `l.isEmpty` failed
/// LOUD with UnknownIdent (measured on the owner's AySoundness/Lrat.lean).
#[test]
fn list_isempty_elaborates_and_computes() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        "def f (l : List Nat) : Bool := l.isEmpty\n\
         def g (l : List Nat) : Bool := List.isEmpty l\n",
    )
    .expect("`l.isEmpty` and `List.isEmpty l` must elaborate for a variable list");

    // Lean's own doc examples, by rfl: nil -> true, any cons -> false.
    accepts_axiom_free(&mut env, "nil_is_empty", "([] : List Nat).isEmpty = true");
    accepts_axiom_free(&mut env, "one_is_not_empty", "[7].isEmpty = false");
    accepts_axiom_free(&mut env, "three_is_not_empty", "[1, 2, 3].isEmpty = false");
}

/// UNIVERSE: the motive lands in `Bool : Type`, so the recursor is instantiated
/// at motive universe 1 whatever `u` is. A body that reused the `succ u`
/// instantiation of the neighbouring accessors is ill-typed at every `u != 0` —
/// `List Type` is `u = 1`, the smallest such witness.
#[test]
fn list_isempty_is_universe_polymorphic_in_the_element_type() {
    let mut env = Environment::with_prelude();
    register(&mut env, "def h (l : List Type) : Bool := l.isEmpty\n")
        .expect("`List.isEmpty` must elaborate at `List Type`");
    accepts_axiom_free(
        &mut env,
        "nil_type_is_empty",
        "([] : List Type).isEmpty = true",
    );
    accepts_axiom_free(
        &mut env,
        "cons_type_is_not_empty",
        "[Nat, Bool].isEmpty = false",
    );
}

/// SOUNDNESS (value-distinguishing, both recursor cases): a fold with the
/// nil/cons arms swapped answers exactly these, and each must be rejected.
#[test]
fn list_isempty_soundness_twins_stay_refused() {
    let mut env = Environment::with_prelude();
    refuses(&mut env, "bad_nil", "([] : List Nat).isEmpty = false");
    refuses(&mut env, "bad_three", "[1, 2, 3].isEmpty = true");
    refuses(&mut env, "bad_one", "[7].isEmpty = true");
}
