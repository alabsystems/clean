// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `termination_by` on the WELL-FOUNDED path must FAIL CLOSED.
//!
//! Measured state (against real `import Init`, where `invImage`,
//! `WellFoundedRelation`, `Nat.lt_wfRel` and `WellFounded.fix` all resolve
//! from Lean's own olean with their real signatures):
//!
//! A `termination_by` whose recursion is STRUCTURAL is routed by
//! `elab_termination_hints` to the structural recursion compiler and
//! elaborates today. Only a recursive definition for which no structural
//! decreasing argument can be found reaches `elab_wf_recursion`.
//!
//! That path cannot produce a correct term. Each recursive call `f arg` must
//! become `rec arg h` with `h : measure arg < measure param`, and nothing
//! synthesises `h`: `transform_rec_calls` rewrites `f ↦ rec` and drops the
//! proof argument entirely, while the obligation machinery in
//! `wf_recursion/decreasing.rs` has no production caller at all.
//!
//! Before this pin, such a `def` emitted the malformed term anyway and was
//! rejected by the KERNEL with a message naming an internal implementation
//! constant — "Level count mismatch for invImage: declared 2 level params,
//! got 1", and behind it "Unbound variable index: 0". A user who wrote
//! `termination_by` was shown a kernel error about `invImage`, a constant
//! they never mentioned, which reads as a kernel bug rather than an
//! unimplemented feature.
//!
//! Worse than the message: without the guard the ELABORATOR returns `Ok`.
//! Remove it and `wfSelf` elaborates to a `WellFounded.fix` whose recursive
//! call is `rec (Nat.pred n)` — `rec` has type `(y : α) → rel y x → C y`, so
//! the proof argument is simply missing and the term is ill-typed. Only the
//! subsequent kernel check rejects it, so every consumer that elaborates
//! WITHOUT kernel-checking (the IDE/hole surface, `elaborate_decl`) would
//! accept a bogus definition. Fail-closed must not rest on the kernel alone.
//!
//! It must instead be refused by the ELABORATOR with a diagnostic naming the
//! construct, and it must never degrade to `sorry`, an axiom, or an unchecked
//! declaration.

use clean_elab::{
    elaborate_decl, elaborate_decl_and_register, preprocess_decl_with_context, ElabError,
    FileContext,
};
use clean_kernel::name::Name;
use clean_kernel::Environment;
use clean_parser::parse_file;

/// A recursive definition with NO structural decreasing argument.
///
/// The recursive call's argument is an application (`Nat.pred n`), not a bare
/// parameter name, and the body is not a `match`, so structural detection
/// finds no decreasing position and the well-founded path is taken.
const NON_STRUCTURAL: &str = "def wfSelf (n : Nat) : Nat := wfSelf (Nat.pred n)\ntermination_by n";

/// The same annotation on a definition whose recursion IS structural.
const STRUCTURAL: &str = "def wfOk (n : Nat) : Nat :=\n  match n with\n  | 0 => 0\n  | Nat.succ m => wfOk m\ntermination_by n";

/// Parse → preprocess → elaborate, mirroring the real `clean check` pipeline.
///
/// The preprocessing pass is what attaches the recursion/termination
/// information the well-founded path dispatches on; a harness that skips it
/// never reaches that path.
fn elab_one(env: &Environment, source: &str) -> Result<clean_elab::ElabResult, ElabError> {
    let decls = parse_file(source).expect("source should parse");
    assert_eq!(decls.len(), 1, "probe must be exactly one declaration");
    let mut file_ctx = FileContext::new();
    let processed = preprocess_decl_with_context(&decls[0], &mut file_ctx);
    elaborate_decl(env, &processed)
}

fn nat_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env
}

// ---------------------------------------------------------------------------
// Fail closed, with a diagnostic that names the construct.
// ---------------------------------------------------------------------------

#[test]
fn test_non_structural_termination_by_fails_closed_naming_the_construct() {
    let env = nat_env();
    let err = elab_one(&env, NON_STRUCTURAL)
        .expect_err("non-structural `termination_by` must be refused, not compiled");

    let ElabError::Unsupported { feature } = &err else {
        panic!("must fail closed as `Unsupported`, got: {err:?}");
    };

    assert!(
        feature.contains("termination_by"),
        "diagnostic must name `termination_by`, got: {feature}"
    );
    assert!(
        feature.contains("well-founded recursion"),
        "diagnostic must name well-founded recursion, got: {feature}"
    );
    assert!(
        feature.contains("wfSelf"),
        "diagnostic must name the declaration, got: {feature}"
    );

    // DECOY that discriminates. The declaration failed before this pin too, so
    // "it errors" proves nothing on its own — what changed is WHICH layer
    // refuses it and what the message names. If the guard is removed and the
    // malformed term flows to the kernel again, the message goes back to
    // naming `invImage` / a de Bruijn index and this assertion catches it.
    assert!(
        !feature.contains("invImage")
            && !feature.contains("Level count mismatch")
            && !feature.contains("Unbound variable"),
        "must not surface an internal kernel message as the diagnostic: {feature}"
    );
}

#[test]
fn test_non_structural_termination_by_registers_nothing() {
    // Fail closed means nothing reaches the environment: no value, no axiom,
    // no unchecked declaration.
    let mut env = nat_env();
    let decls = parse_file(NON_STRUCTURAL).expect("parse");
    let mut file_ctx = FileContext::new();
    let processed = preprocess_decl_with_context(&decls[0], &mut file_ctx);

    let result = elaborate_decl_and_register(&mut env, &processed);
    assert!(
        result.is_err(),
        "a `def` the well-founded path cannot compile must not register"
    );

    // Nothing derived from the refused declaration may exist: not the constant
    // itself, and not the equation lemmas / unary packing the well-founded
    // compiler would otherwise generate alongside it.
    //
    // (`sorryAx` is part of the prelude `init_nat` installs, and registration
    // also initialises import stubs, so neither "sorryAx is present" nor a
    // raw constant-count delta discriminates anything here.)
    for derived in [
        "wfSelf",
        "wfSelf._unary",
        "wfSelf._eq_1",
        "wfSelf.eq_def",
        "wfSelf._sorry",
    ] {
        assert!(
            env.get_const(&Name::from_string(derived)).is_none(),
            "refused well-founded definition leaked `{derived}` into the environment"
        );
    }
}

// ---------------------------------------------------------------------------
// CONTROL: the guard must key on genuine recursion, not on `termination_by`.
// ---------------------------------------------------------------------------

#[test]
fn test_structural_termination_by_still_elaborates() {
    // This is the discriminating control. `wfOk` carries the very same
    // `termination_by n` annotation but recurses structurally, so it is routed
    // to the structural compiler and must keep working. A guard that fired on
    // the presence of `termination_by` — rather than on reaching the
    // well-founded path with a real recursive call — takes this red.
    let env = nat_env();
    let result = elab_one(&env, STRUCTURAL);
    assert!(
        result.is_ok(),
        "structural recursion carrying `termination_by` must still elaborate; \
         got {:?}",
        result.err()
    );
}
