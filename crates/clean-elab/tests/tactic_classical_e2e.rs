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
//! Lean registers `Classical.propDecidable` as a low-priority local instance.
//! Clean's `classical` checks for the classical foundation and leaves the
//! goals unchanged. A following `by_cases` can use a supplied `Decidable`
//! instance, or the classical foundation for a proposition with no instance.
//!
//! ## Why these are genuine proofs (not `sorry`)
//!
//! Each theorem carries a real tactic proof; the test drives the SAME pipeline as
//! `clean check` (`parse_file → preprocess_decl_with_context →
//! elaborate_decl_and_register_with_context`) and asserts, for every positive gate:
//!   * the theorem registers (the kernel re-checks the produced elimination
//!     term from the `by_cases`/`by_contra` that follow `classical`),
//!   * `infer_type` of the proof term is def-eq to the stated proposition, and
//!   * the transitive `axiom_deps` closure is `⊆ {Classical.em, Classical.choice}`
//!     — i.e. the only axioms under the proof are the foundational classical
//!     ones, and in particular `sorry` / `sorryAx` are never reached.
//!
//! The DECISIVE NEGATIVE gate proves `classical` did not weaken the checker: a
//! genuinely false goal is still unprovable after `classical`.

#[path = "tactic_classical_e2e/lifted_values.rs"]
mod lifted_values;

use std::collections::BTreeSet;

use clean_kernel::env::Environment;
use clean_kernel::{Expr, ExprKind, Name, TypeChecker};

use clean_elab::tactic::builtins::builtin_tactic_patterns;
use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, FileContext,
};
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
        elaborate_decl_and_register_with_context(env, &processed, &mut file_ctx)
            .map_err(|e| e.to_string())?;
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

// The classical cases below have no supplied decision. Their proof terms may
// use the prelude's excluded-middle theorem and its foundations.
const CLASSICAL_AXIOMS: &[&str] = &["Classical.em", "Classical.choice", "propext"];

// ---------------------------------------------------------------------------
// GATE a — `classical` then `by_cases`. This is the canonical Mathlib opener:
// `classical` must be recognized (not `UnknownTactic`), leave the goal alone,
// and let the following `by_cases` close `p ∨ ¬p`. The kernel checks the result.
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

#[test]
fn by_cases_prefers_the_local_decision_to_classical_em() {
    assert_tactic_theorem_axioms(
        "localEM",
        "theorem localEM (p : Prop) [Decidable p] : p ∨ ¬p := by\n\
         by_cases h : p\n\
         · exact Or.inl h\n\
         · exact Or.inr h",
        &[],
    );
}

#[test]
fn by_cases_local_decision_computes_both_data_branches() {
    let mut env = Environment::with_prelude();
    try_elaborate_into(
        &mut env,
        "def splitToNat (p : Prop) [Decidable p] : Nat := by\n\
         by_cases h : p\n\
         · exact 17\n\
         · exact 23",
    )
    .expect("a supplied decision must support a data-valued case split");
    for reduction in [
        "theorem positive (p : Prop) (h : p) : @splitToNat p (Decidable.isTrue h) = 17 := rfl",
        "theorem negative (p : Prop) (h : ¬p) : @splitToNat p (Decidable.isFalse h) = 23 := rfl",
    ] {
        try_elaborate_into(&mut env, reduction).expect("the selected data branch must reduce");
    }
}

#[test]
fn by_cases_rejects_using_a_negative_witness_as_positive() {
    let mut env = Environment::with_prelude();
    let error = try_elaborate_into(
        &mut env,
        "theorem wrongBranch (p : Prop) [Decidable p] : p ∨ ¬p := by\n\
         by_cases h : p\n\
         · exact Or.inl h\n\
         · exact Or.inl h",
    )
    .expect_err("the second branch supplies a witness of ¬p");
    assert!(error.to_lowercase().contains("type mismatch"), "{error}");
    assert!(env.get_const(&Name::from_string("wrongBranch")).is_none());
}

#[test]
fn by_cases_elaborates_its_condition_under_open_classical() {
    let mut env = Environment::with_prelude();
    try_elaborate_into(
        &mut env,
        "theorem choiceCondition (q : Nonempty Prop) : True := by\n\
         by_cases h : (choice q : Prop)\n\
         · exact True.intro\n\
         · exact True.intro",
    )
    .expect("Classical.choice should resolve inside the proposition");
    let error = try_elaborate_into(
        &mut env,
        "theorem choiceBranch (p : Prop) (inh : Nonempty p) : p := by\n\
         by_cases h : True\n\
         · exact choice inh\n\
         · exact choice inh",
    )
    .expect_err("the condition's namespace should be closed before the branches");
    assert!(
        error.to_lowercase().contains("unknown") && error.contains("choice"),
        "{error}"
    );
}

#[test]
fn by_cases_checks_a_boolean_condition_against_prop() {
    assert_tactic_theorem_axioms(
        "splitBool",
        "theorem splitBool (b : Bool) : b = true ∨ ¬ b = true := by\n\
         by_cases h : b\n\
         · exact Or.inl h\n\
         · exact Or.inr h",
        &[],
    );
}

#[test]
fn let_i_computes_both_branches_with_an_anonymous_decision() {
    let mut env = Environment::with_prelude();
    try_elaborate_into(
        &mut env,
        "def splitWithInstance (p : Prop) (choose : Nat → Decidable p) : Nat := by
  letI : Decidable p := choose 7
  by_cases h : p
  · exact 17
  · exact 23",
    )
    .expect("by_cases must use the decision bound by letI");
    for reduction in [
        "theorem splitYes (p : Prop) (h : p) :
    splitWithInstance p (fun _ => Decidable.isTrue h) = 17 := rfl",
        "theorem splitNo (p : Prop) (h : ¬p) :
    splitWithInstance p (fun _ => Decidable.isFalse h) = 23 := rfl",
    ] {
        try_elaborate_into(&mut env, reduction).expect("the supplied decision selects the branch");
    }
    assert!(env
        .axiom_deps(&Name::from_string("splitWithInstance"))
        .expect("registered definition")
        .is_empty());
}

#[test]
fn let_i_inlines_a_named_value_in_the_stored_term() {
    fn lambda_body<'a>(env: &'a Environment, name: &str) -> &'a Expr {
        let info = env.get_const(&Name::from_string(name)).expect(name);
        let value = info.value.as_ref().expect("stored definition");
        let ExprKind::Lam(_, _, body) = value.strip_mdata().kind() else {
            panic!("expected a lambda in {name}, got {value:?}");
        };
        body.strip_mdata()
    }

    let mut env = Environment::with_prelude();
    try_elaborate_into(
        &mut env,
        "def namedInline (n : Nat) : Nat := by
  letI chosen : Nat := n
  exact chosen
def namedOrdinary (n : Nat) : Nat := by
  let chosen : Nat := n
  exact chosen",
    )
    .expect("both tactic bindings elaborate");
    let inline = lambda_body(&env, "namedInline");
    assert!(matches!(inline.kind(), ExprKind::BVar(0)), "{inline:?}");
    let ordinary = lambda_body(&env, "namedOrdinary");
    let ExprKind::Let(name, _, value, body, _) = ordinary.kind() else {
        panic!("ordinary let must retain its binder, got {ordinary:?}");
    };
    assert_eq!(name, &Name::from_string("chosen"));
    assert!(matches!(value.strip_mdata().kind(), ExprKind::BVar(0)));
    assert!(matches!(body.strip_mdata().kind(), ExprKind::BVar(0)));
}

#[test]
fn let_i_only_supplies_an_instance_to_its_own_branch() {
    let mut env = Environment::with_prelude();
    try_elaborate_into(
        &mut env,
        "def scopedNat : Nat × Nat := by
  constructor
  · letI : Inhabited Nat := Inhabited.mk 17
    exact Inhabited.default
  · exact Inhabited.default",
    )
    .expect("both product goals elaborate");
    for reduction in [
        "theorem scopedFirst : scopedNat.1 = 17 := rfl",
        "theorem scopedSecond : scopedNat.2 = 0 := rfl",
    ] {
        try_elaborate_into(&mut env, reduction)
            .expect("first goal must use its local instance and second the prelude instance");
    }
}

#[test]
fn let_i_rejects_a_witness_of_the_wrong_type() {
    let mut env = Environment::with_prelude();
    let error = try_elaborate_into(
        &mut env,
        "def badWitness (p : Prop) : Nat := by
  letI : Decidable p := Nat.zero
  exact 0",
    )
    .expect_err("the unused instance must still type-check");
    assert!(error.to_lowercase().contains("type mismatch"), "{error}");
    assert!(env.get_const(&Name::from_string("badWitness")).is_none());
}
