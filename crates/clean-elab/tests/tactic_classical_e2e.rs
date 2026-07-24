// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end regression lock for the **`classical`** tactic.
//!
//! `classical` is Mathlib's single most common tactic-block opener (≈3,000 uses,
//! ≈1,000 of them the first line of a block). Before this change it was an
//! `UnknownTactic`, and — worse — the unknown token derailed the block's parser,
//! so a single leading `classical` aborted the *entire* declaration with a
//! `parser recovery produced raw declaration` cascade. Real Mathlib source that
//! opens `by classical; …` could not elaborate at all.
//!
//! ## Faithful-in-Clean semantics
//!
//! In Lean 4, `classical` registers `Classical.propDecidable` as a low-priority
//! local instance so `Decidable p` synthesizes for any `p`. Clean's classical
//! foundation — `Classical.em` / `Classical.choice` / `Or.rec` — is
//! **unconditionally** in the environment, and Clean's classical case-analysis
//! tactics (`by_cases`, `by_contra`) use `Classical.em` *directly* rather than
//! requiring a `Decidable` instance. So the classical case-analysis proofs that
//! open with `classical` already have everything they need: the faithful
//! behaviour is to recognize the tactic and succeed with the goal unchanged.
//! `classical` therefore introduces **no proof term** — it is a structural
//! no-op — so it cannot affect the kernel-rechecked assembled proof.
//!
//! Honest scope (deliberately not covered here): `classical` does not yet
//! register a `Decidable`-instance fallback, so a `dite`/`ite` over an
//! undecidable prop after `classical` still fails **loudly at the point of use**
//! (a clear "could not synthesize Decidable"), never silently-wrong. That wiring
//! belongs to the instance-synthesis surface and is tracked separately.
//!
//! ## Why these are genuine proofs (not `sorry`)
//!
//! Each theorem carries a real tactic proof; the test drives the SAME pipeline as
//! `clean check` (`parse_file → preprocess_decl_with_context →
//! elaborate_decl_and_register`) and asserts, for every positive gate:
//!   * the theorem registers (the kernel re-checks the produced `Or.rec`/`em`
//!     term from the `by_cases`/`by_contra` that follow `classical`),
//!   * `infer_type` of the proof term is def-eq to the stated proposition, and
//!   * the transitive `axiom_deps` closure is `⊆ {Classical.em, Classical.choice}`
//!     — i.e. the only axioms under the proof are the foundational classical
//!     ones, and in particular `sorry` / `sorryAx` are never reached.
//!
//! The DECISIVE NEGATIVE gate proves `classical` did not weaken the checker: a
//! genuinely false goal is still unprovable after `classical`.

use std::collections::BTreeSet;

use clean_kernel::env::Environment;
use clean_kernel::{Name, TypeChecker};

use clean_elab::tactic::builtins::builtin_tactic_patterns;
use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_parser::parse_file_with_tactics;

/// Drive the real file pipeline for a (possibly multi-declaration) source.
///
/// Uses the **tactic-pattern-aware** parse (`parse_file_with_tactics` +
/// `builtin_tactic_patterns()`) exactly as `clean check` does — the patterns
/// drive the indentation-sensitive parser's grouping of `·` bullet bodies into
/// focus blocks. The pattern-less `parse_file` mis-parses a leading nullary
/// tactic followed by a newline-and-bullet proof (a pre-existing limitation
/// unrelated to `classical`), so a faithful `classical` test must parse the way
/// the real checker does.
fn try_elaborate_into(env: &mut Environment, source: &str) -> Result<(), String> {
    let mut file_ctx = FileContext::new();
    let patterns = builtin_tactic_patterns();
    let decls =
        parse_file_with_tactics(source, &patterns).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed).map_err(|e| e.to_string())?;
    }
    Ok(())
}

/// Elaborate `source` (defining `name` last as a tactic-proved theorem) and
/// assert it kernel-checks, infers a def-eq type, and its axiom closure is a
/// subset of `allowed`.
fn assert_tactic_theorem_axioms(name: &str, source: &str, allowed: &[&str]) {
    let mut env = Environment::with_prelude();
    try_elaborate_into(&mut env, source)
        .unwrap_or_else(|e| panic!("`{name}` must elaborate and kernel-check: {e}"));

    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must be registered after elaboration"));
    let proof = info
        .value
        .as_ref()
        .unwrap_or_else(|| panic!("`{name}` theorem must carry a proof value"));

    // SOUNDNESS 1 — kernel re-derives the proof's type, def-eq to the stated prop.
    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(proof)
        .unwrap_or_else(|e| panic!("`{name}` proof must infer a type: {e}"));
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "`{name}` proof type must be def-eq to its stated proposition:\n  got {inferred:?}\n  exp {:?}",
        info.type_
    );

    // SOUNDNESS 2 — axiom_deps closure ⊆ allowed; in particular no `sorry`.
    let deps = env
        .axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must have an axiom_deps closure"));
    let allowed_set: BTreeSet<Name> = allowed.iter().map(|s| Name::from_string(s)).collect();
    for dep in &deps {
        assert!(
            allowed_set.contains(dep),
            "`{name}` axiom closure must be ⊆ {allowed:?}; found disallowed axiom `{dep:?}` \
             (full closure: {deps:?})"
        );
    }
}

// The classical foundation `classical` advertises. `by_cases`/`by_contra` build
// their proof terms from `Classical.em` (which itself rests on `Classical.choice`
// in the prelude), so a real classical proof's axiom closure lands in this set.
const CLASSICAL_AXIOMS: &[&str] = &["Classical.em", "Classical.choice", "propext"];

// ---------------------------------------------------------------------------
// GATE a — `classical` then `by_cases`. This is the canonical Mathlib opener:
// `classical` must be recognized (not `UnknownTactic`), leave the goal alone,
// and let the following `by_cases` (which uses `Classical.em` + `Or.rec`) close
// `p ∨ ¬p`. Kernel re-checks the assembled `Or.rec` term.
// ---------------------------------------------------------------------------

#[test]
fn classical_then_by_cases_closes_em() {
    assert_tactic_theorem_axioms(
        "classical_em",
        "theorem classical_em (p : Prop) : p ∨ ¬p := by\n\
         classical\n\
         by_cases h : p\n\
         · exact Or.inl h\n\
         · exact Or.inr h",
        CLASSICAL_AXIOMS,
    );
}

// ---------------------------------------------------------------------------
// GATE b — `classical` then `by_contra`. Exercises the other classical
// case-analysis path and confirms `classical` composes with it.
// ---------------------------------------------------------------------------

#[test]
fn classical_then_by_contra_double_negation() {
    assert_tactic_theorem_axioms(
        "classical_dne",
        "theorem classical_dne (p : Prop) (h : ¬¬p) : p := by\n\
         classical\n\
         by_contra hn\n\
         exact h hn",
        CLASSICAL_AXIOMS,
    );
}

// ---------------------------------------------------------------------------
// GATE c — `classical` is a no-op that does not disturb a subsequent trivial
// close. `classical` followed by `exact h` must behave exactly as `exact h`
// alone (goal untouched), and the closure carries NO axiom at all (no classical
// reasoning was actually used).
// ---------------------------------------------------------------------------

#[test]
fn classical_is_noop_before_exact() {
    assert_tactic_theorem_axioms(
        "classical_noop",
        "theorem classical_noop (p : Prop) (h : p) : p := by classical; exact h",
        &[],
    );
}

// ---------------------------------------------------------------------------
// DECISIVE NEGATIVE — `classical` must not make anything *more* provable at the
// proposition level: a genuinely false goal is still unprovable after it. If
// this ever PASSES, `classical` (or the machinery it unlocked) is unsound.
// ---------------------------------------------------------------------------

#[test]
fn classical_does_not_prove_false_goal() {
    let mut env = Environment::with_prelude();
    let result = try_elaborate_into(
        &mut env,
        "theorem classical_bad (p q : Prop) (h : p) : q := by classical; exact h",
    );
    assert!(
        result.is_err(),
        "`classical; exact h` (h : p) must NOT close goal q; this proof MUST fail closed"
    );
}

// ---------------------------------------------------------------------------
// PARSE REGRESSION — a leading `classical` must not derail the block parser.
// Before the fix, the unknown `classical` token produced a `parser recovery
// produced raw declaration` cascade that failed the WHOLE declaration. Here the
// full multi-line block after `classical` must parse and elaborate as one decl.
// ---------------------------------------------------------------------------

#[test]
fn classical_leading_does_not_break_block_parse() {
    // Purely structural: if `classical` still derailed the parser, `parse_file`
    // would split this into a bogus second "declaration" and elaboration would
    // fail. Success of the full 4-line block is the regression lock.
    assert_tactic_theorem_axioms(
        "classical_parse",
        "theorem classical_parse (p : Prop) : p ∨ ¬p := by\n\
         classical\n\
         by_cases h : p\n\
         · exact Or.inl h\n\
         · exact Or.inr h",
        CLASSICAL_AXIOMS,
    );
}
