// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for the `|` alternation (Or-pattern) in `rcases`/`obtain`/
//! `rintro`.
//!
//! In an rcases pattern, `pat₁ | pat₂` (the `|` ALTERNATION) means: the
//! hypothesis/field is an inductive with ≥2 constructors (canonically `Or`:
//! `p ∨ q`), so CASE-SPLIT it — produce one goal per branch, applying `pat₁` to
//! the first constructor's field (`Or.inl`'s `p`) and `pat₂` to the second
//! (`Or.inr`'s `q`). This is the most common rcases idiom (`rcases h with h | h`)
//! for splitting disjunctions.
//!
//! These tests exercise the full parse -> elaborate -> kernel-type-check path.
//! The case-split routes through the SAME kernel-checked `cases`/`Or.casesOn`
//! engine that backs `cases h with | inl .. | inr ..`, so each branch's proof
//! term is a genuine eliminator application the kernel accepts. A `|` pattern on
//! a non-splittable hypothesis, a wrong branch count, or a branch that fails to
//! close its goal must ERROR (never a panic, never a silent over-accept).

use super::common::check_and_add_decl;
use clean_kernel::{Declaration, Environment, Expr, Name};

/// Logic environment with `Or` (and its `Or.inl`/`Or.inr`/`Or.casesOn`), `And`,
/// and props `P`, `Q`, `R`.
fn setup_or_env() -> Environment {
    let mut env = Environment::new();
    env.init_true_false().expect("init_true_false");
    env.init_and().expect("init_and");
    env.init_or().expect("init_or");
    env.init_classical().expect("init_classical");

    let prop = Expr::prop();
    for name in ["P", "Q", "R"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: prop.clone(),
        })
        .expect("add prop axiom");
    }
    env
}

#[test]
fn test_rcases_or_alternation_splits_kernel_accepts() {
    // The canonical idiom: `rcases h with hp | hq` on `h : P ∨ Q ⊢ Q ∨ P`.
    // Each branch is closed by the swapped `Or` constructor.
    let mut env = setup_or_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem rcases_or_swap (h : Or P Q) : Or Q P := by\n  rcases h with hp | hq\n  · exact Or.inr hp\n  · exact Or.inl hq",
    );
    assert!(
        result.is_ok(),
        "rcases h with hp | hq then per-branch Or.inr/Or.inl should kernel-check, got: {result:?}"
    );
}

#[test]
fn test_obtain_or_alternation_splits_kernel_accepts() {
    // Same disjunction split via `obtain hp | hq := h` (no `with`-clause form).
    let mut env = setup_or_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem obtain_or_swap (h : Or P Q) : Or Q P := by\n  obtain hp | hq := h\n  · exact Or.inr hp\n  · exact Or.inl hq",
    );
    assert!(
        result.is_ok(),
        "obtain hp | hq := h then per-branch Or.inr/Or.inl should kernel-check, got: {result:?}"
    );
}

#[test]
fn test_rintro_paren_or_alternation_splits_kernel_accepts() {
    // `rintro (hp | hq)` on `P ∨ Q → Q ∨ P`: the parenthesized alternation
    // intros the hypothesis and case-splits it (Lean requires the parens for an
    // alternation under `rintro`).
    let mut env = setup_or_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem rintro_or_swap : Or P Q → Or Q P := by\n  rintro (hp | hq)\n  · exact Or.inr hp\n  · exact Or.inl hq",
    );
    assert!(
        result.is_ok(),
        "rintro (hp | hq) then per-branch Or.inr/Or.inl should kernel-check, got: {result:?}"
    );
}

#[test]
fn test_obtain_nested_and_or_alternation_kernel_accepts() {
    // Nested alternation inside an And destructure: `obtain ⟨hp, hq | hr⟩ := h`
    // on `h : P ∧ (Q ∨ R) ⊢ (P ∧ Q) ∨ (P ∧ R)`. The `And` splits to fields
    // `hp : P` and `q ∨ r`, and the `|` then case-splits the second field.
    let mut env = setup_or_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem obtain_and_or (h : And P (Or Q R)) : Or (And P Q) (And P R) := by\n  obtain ⟨hp, hq | hr⟩ := h\n  · exact Or.inl ⟨hp, hq⟩\n  · exact Or.inr ⟨hp, hr⟩",
    );
    assert!(
        result.is_ok(),
        "obtain ⟨hp, hq | hr⟩ := h then per-branch ⟨..⟩ should kernel-check, got: {result:?}"
    );
}

#[test]
fn test_cases_with_inl_inr_still_kernel_accepts() {
    // Regression guard: the pre-existing `cases h with | inl .. | inr ..` form
    // (which the Or-pattern machinery reuses) must keep working.
    let mut env = setup_or_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem cases_or_swap (h : Or P Q) : Or Q P := by\n  cases h with\n  | inl hp => exact Or.inr hp\n  | inr hq => exact Or.inl hq",
    );
    assert!(
        result.is_ok(),
        "cases h with | inl .. | inr .. must still kernel-check, got: {result:?}"
    );
}

#[test]
fn test_rcases_or_on_non_or_hypothesis_errors_not_panics() {
    // A `|` alternation on a NON-Or hypothesis `h : P ∧ Q` (one constructor)
    // has no second branch to split into. This must surface as an elaboration
    // error (not a panic) and must NOT yield a kernel-accepted proof.
    let mut env = setup_or_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem rcases_or_on_and (h : And P Q) : Q := by\n  rcases h with hp | hq\n  · exact hq",
    );
    assert!(
        result.is_err(),
        "rcases hp | hq on a 1-constructor And must error, not silently succeed: {result:?}"
    );
}

#[test]
fn test_rcases_or_unclosed_branch_errors_not_panics() {
    // A `|` split that proves only the first branch leaves the second goal
    // unsolved. The proof must NOT be accepted.
    let mut env = setup_or_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem rcases_or_unclosed (h : Or P Q) : Or Q P := by\n  rcases h with hp | hq\n  · exact Or.inr hp",
    );
    assert!(
        result.is_err(),
        "rcases hp | hq with only one branch closed must error (unsolved goal): {result:?}"
    );
}

#[test]
fn test_rcases_or_wrong_branch_closer_errors_not_panics() {
    // Each branch must close its OWN goal with a well-typed term. Using `hp`
    // (a proof of P) to close `Or.inl hp : Q ∨ P` in the wrong slot is a type
    // error the kernel rejects.
    let mut env = setup_or_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem rcases_or_wrong (h : Or P Q) : Or Q P := by\n  rcases h with hp | hq\n  · exact Or.inl hp\n  · exact Or.inr hq",
    );
    assert!(
        result.is_err(),
        "rcases branches closed with mistyped Or constructors must error: {result:?}"
    );
}

/// Like [`setup_or_env`] but adds a fourth prop `S`, for the 3-tuple
/// non-last-field or-pattern test.
fn setup_or_env_with_s() -> Environment {
    let mut env = setup_or_env();
    let prop = Expr::prop();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("S"),
        level_params: vec![],
        type_: prop.clone(),
    })
    .expect("add prop S");
    env
}

#[test]
fn test_rcases_or_in_first_field_of_tuple_kernel_accepts() {
    // Tooth 1 (regression for the non-last-field or-pattern bug): a `|`
    // alternation in the FIRST field of a `⟨…⟩` tuple must case-split that field
    // AND still bind the LATER sibling field (`hr`) in EVERY resulting branch, so
    // both branches can close with `exact hr`. Previously the later field's FVar
    // was renamed in only one branch, leaving a dangling `UnknownFVar` in the
    // other branch's proof term (kernel rejected). Now both branches kernel-check.
    let mut env = setup_or_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem rcases_or_first_field (h : And (Or P Q) R) : R := by\n  rcases h with ⟨hp | hq, hr⟩\n  · exact hr\n  · exact hr",
    );
    assert!(
        result.is_ok(),
        "rcases ⟨hp | hq, hr⟩ (or in FIRST field) must bind `hr` in both branches and kernel-check, got: {result:?}"
    );
}

#[test]
fn test_rcases_or_in_first_field_of_triple_kernel_accepts() {
    // Tooth 2: or-pattern in the first field of a 3-tuple. The trailing two
    // fields (`hr`, `hs`) are carried into BOTH `|` branches; `<;> exact hr`
    // closes every branch. Exercises the field-flattening (`⟨hp|hq, hr, hs⟩` on
    // `(P∨Q) ∧ R ∧ S` regroups the tail into a nested destructure) composed with
    // the earlier-field split — each branch is run in isolation so its nested
    // `cases` sees a single goal and numbers its fields consistently.
    let mut env = setup_or_env_with_s();
    let result = check_and_add_decl(
        &mut env,
        "theorem rcases_or_first_of_triple (h : And (Or P Q) (And R S)) : R := by\n  rcases h with ⟨hp | hq, hr, hs⟩ <;> exact hr",
    );
    assert!(
        result.is_ok(),
        "rcases ⟨hp | hq, hr, hs⟩ (or in FIRST field of a 3-tuple) must kernel-check, got: {result:?}"
    );
}

#[test]
fn test_rcases_or_two_fields_both_split_kernel_accepts() {
    // Two or-fields in one tuple: `⟨hp | hq, hr | hs⟩` on `(P∨Q) ∧ (R∨S)` splits
    // the first field into two branches, then splits the second field within each
    // — four branches total. `<;> trivial` (goal `True`) closes them all. Guards
    // that a later or-field is applied to EVERY branch a prior or-field produced.
    let mut env = setup_or_env_with_s();
    let result = check_and_add_decl(
        &mut env,
        "theorem rcases_or_two_fields (h : And (Or P Q) (Or R S)) : True := by\n  rcases h with ⟨hp | hq, hr | hs⟩ <;> trivial",
    );
    assert!(
        result.is_ok(),
        "rcases ⟨hp | hq, hr | hs⟩ (two or-fields, 4 branches) must kernel-check, got: {result:?}"
    );
}

#[test]
fn test_rcases_or_in_first_field_wrong_closer_errors_not_panics() {
    // Tooth 5 (negative): with an or-pattern in the first field, the second (`hq`)
    // branch has `hq : Q` and `hr : R` but the goal is `P` — neither hypothesis
    // proves it. Closing that branch with `exact hr` is a type error the kernel
    // rejects. Must ERROR (fail-closed), never panic, never over-accept.
    let mut env = setup_or_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem rcases_or_first_field_bad (h : And (Or P Q) R) : P := by\n  rcases h with ⟨hp | hq, hr⟩\n  · exact hp\n  · exact hr",
    );
    assert!(
        result.is_err(),
        "rcases ⟨hp | hq, hr⟩ where the `hq` branch closes `⊢ P` with `hr : R` must error, not over-accept: {result:?}"
    );
}

#[test]
fn test_or_notation_is_right_associative() {
    // `∨` is `infixr:30` in Lean 4: `P ∨ Q ∨ R` parses as `P ∨ (Q ∨ R)`, NOT
    // `(P ∨ Q) ∨ R`. Regression for the ∨-associativity parser fix (mirrors ∧).
    let mut env = setup_or_env();
    check_and_add_decl(
        &mut env,
        "theorem or_right_assoc (h : P ∨ Q ∨ R) : P ∨ (Q ∨ R) := h",
    )
    .expect("`P ∨ Q ∨ R` must be def-eq to `P ∨ (Q ∨ R)` (right-associative)");
}

#[test]
fn test_rcases_three_way_or_pattern_via_notation() {
    // Right-assoc `P ∨ Q ∨ R` ≡ `P ∨ (Q ∨ R)`; the 3-way alternation
    // `hp | hq | hr` right-nests to match, splitting into three branches.
    // Regression that the ∨-assoc fix unblocks 3-way or-patterns end-to-end.
    let mut env = setup_or_env();
    check_and_add_decl(
        &mut env,
        "theorem rcases_three_way (h : P ∨ Q ∨ R) : R ∨ Q ∨ P := by\n  rcases h with hp | hq | hr\n  · exact Or.inr (Or.inr hp)\n  · exact Or.inr (Or.inl hq)\n  · exact Or.inl hr",
    )
    .expect("3-way or-pattern on right-assoc `P ∨ Q ∨ R` must split into three branches");
}
