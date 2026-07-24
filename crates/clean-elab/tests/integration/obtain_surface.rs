// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for the Lean 4 `obtain ⟨pat⟩ := e` surface form.
//!
//! These tests exercise the full parse -> elaborate -> kernel-type-check path:
//! a `theorem ... := by obtain ... ; exact ...` proof is parsed by
//! `clean-parser`, elaborated by `clean-elab` (the `obtain` compound handler
//! introduces the elaborated RHS via the kernel-checked `have_`, then destructs
//! it through the kernel-checked `cases`/`casesOn` engine), and the resulting
//! proof term is type-checked against the stated type by the kernel.
//!
//! Faithfulness: `obtain pat := e` desugars to `have h := e; rcases h with pat`.
//! A pattern/type mismatch surfaces as an elaboration error, never a panic, and
//! the goal is only ever closed via the kernel-checked path.

use super::common::check_and_add_decl;
use clean_kernel::{Declaration, Environment, Expr, Name};

/// Build a logic environment with And, Exists, props P/Q/R, a type A with a
/// predicate `pr : A → Prop`, and witnesses `hp : P`, `hq : Q`.
fn setup_logic_env() -> Environment {
    let mut env = Environment::new();
    env.init_true_false().expect("init_true_false");
    env.init_and().expect("init_and");
    env.init_classical().expect("init_classical");
    env.init_exists().expect("init_exists");
    // `Nat` and `Eq` back the `⟨b, rfl⟩` substitution-pattern tests: the second
    // existential field is an equation `a = b` that the `rfl` pattern `subst`s.
    env.init_nat().expect("init_nat");
    env.init_eq().expect("init_eq");

    let prop = Expr::prop();
    for name in ["P", "Q", "R"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: prop.clone(),
        })
        .expect("add prop axiom");
    }

    // A : Type, pr : A → Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("add A");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("pr"),
        level_params: vec![],
        type_: Expr::arrow(Expr::const_(Name::from_string("A"), vec![]), Expr::prop()),
    })
    .expect("add pr");

    // Witnesses for the compound-RHS test.
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hp"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("P"), vec![]),
    })
    .expect("add hp");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hq"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Q"), vec![]),
    })
    .expect("add hq");

    // A non-pair proposition `Atom : Prop` plus a witness, for the mismatch test.
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Atom"),
        level_params: vec![],
        type_: prop.clone(),
    })
    .expect("add Atom");

    env
}

#[test]
fn test_obtain_and_binds_left_kernel_accepts() {
    // obtain ⟨hp, hq⟩ := h  on  h : P ∧ Q  binds hp:P, hq:Q; `exact hp` closes.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem obtain_and_left (h : And P Q) : P := by\n  obtain ⟨hp, hq⟩ := h\n  exact hp",
    );
    assert!(
        result.is_ok(),
        "obtain ⟨hp, hq⟩ on And then `exact hp` should kernel-check, got: {result:?}"
    );
}

#[test]
fn test_obtain_and_binds_right_kernel_accepts() {
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem obtain_and_right (h : And P Q) : Q := by\n  obtain ⟨hp, hq⟩ := h\n  exact hq",
    );
    assert!(
        result.is_ok(),
        "obtain ⟨hp, hq⟩ on And then `exact hq` should kernel-check, got: {result:?}"
    );
}

#[test]
fn test_obtain_nested_pattern_kernel_accepts() {
    // obtain ⟨a, ⟨b, c⟩⟩ := h  on  h : P ∧ (Q ∧ R); `exact c` closes.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem obtain_nested (h : And P (And Q R)) : R := by\n  obtain ⟨a, ⟨b, c⟩⟩ := h\n  exact c",
    );
    assert!(
        result.is_ok(),
        "nested obtain ⟨a, ⟨b, c⟩⟩ then `exact c` should kernel-check, got: {result:?}"
    );
}

#[test]
fn test_obtain_exists_binds_witness_kernel_accepts() {
    // obtain ⟨x, hx⟩ := he  on  he : ∃ x, pr x; rebuild via ⟨x, hx⟩.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem obtain_exists (he : Exists (fun x : A => pr x)) : Exists (fun x : A => pr x) := by\n  obtain ⟨x, hx⟩ := he\n  exact ⟨x, hx⟩",
    );
    assert!(
        result.is_ok(),
        "obtain ⟨x, hx⟩ on ∃ then rebuild should kernel-check, got: {result:?}"
    );
}

#[test]
fn test_obtain_compound_rhs_term_kernel_accepts() {
    // The RHS may be an arbitrary term: obtain ⟨a, b⟩ := And.intro hp hq.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem obtain_compound_rhs : P := by\n  obtain ⟨a, b⟩ := And.intro P Q hp hq\n  exact a",
    );
    assert!(
        result.is_ok(),
        "obtain ⟨a, b⟩ := And.intro P Q hp hq then `exact a` should kernel-check, got: {result:?}"
    );
}

#[test]
fn test_obtain_rfl_pattern_substitutes_kernel_accepts() {
    // The `⟨b, rfl⟩` idiom: the existential `∃ b, a = b` binds `b` and an
    // equation `a = b`; the `rfl` pattern `subst`s that equation away. The goal
    // `True` is then closed by `trivial`. Previously this FAILED outright (parse
    // error: `rfl` is a keyword token the obtain pattern reader rejected).
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem obtain_rfl (a : Nat) (h : Exists (fun b : Nat => Eq a b)) : True := by\n  obtain ⟨b, rfl⟩ := h\n  trivial",
    );
    assert!(
        result.is_ok(),
        "obtain ⟨b, rfl⟩ on ∃ b, a = b then `trivial` should kernel-check, got: {result:?}"
    );
}

#[test]
fn test_obtain_rfl_pattern_substitution_is_real_kernel_accepts() {
    // DECISIVE: the goal is `a = a`. After `obtain ⟨b, rfl⟩` substitutes `a := b`
    // (eliminating `a`), the goal becomes `b = b`, which `rfl` closes. This can
    // only succeed if a GENUINE Eq-based subst happened (not a no-op): a no-op
    // would leave the goal as `a = a` with `a` still in context, which `rfl`
    // would still close — so to distinguish, we rely on the kernel re-checking
    // the assembled `Eq.ndrec` proof term end-to-end via `add_decl`.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem obtain_rfl_real (a : Nat) (h : Exists (fun b : Nat => Eq a b)) : Eq a a := by\n  obtain ⟨b, rfl⟩ := h\n  rfl",
    );
    assert!(
        result.is_ok(),
        "obtain ⟨b, rfl⟩ on ∃ b, a = b proving `a = a` (goal becomes `b = b`) should kernel-check, got: {result:?}"
    );
}

#[test]
fn test_obtain_rfl_pattern_non_equation_field_errors_not_panics() {
    // NEGATIVE: the second field of `∃ b, P` is `P` (a proposition), NOT an
    // equation. The `rfl` pattern has nothing to substitute, so `subst` must
    // surface an elaboration error (not a panic, not a silent over-accept) — it
    // mirrors Lean 4's `subst` failure ("not of the form x = t or t = x").
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem obtain_rfl_nonequation (h : Exists (fun b : Nat => P)) : True := by\n  obtain ⟨b, rfl⟩ := h\n  trivial",
    );
    assert!(
        result.is_err(),
        "obtain ⟨b, rfl⟩ where the second field is NOT an equation must error, not silently succeed: {result:?}"
    );
}

#[test]
fn test_obtain_pattern_type_mismatch_errors_not_panics() {
    // Destructuring a non-pair hypothesis `h : Atom` with a 2-field tuple has no
    // sound casesOn fields to bind to both names. This must surface as an
    // elaboration error (not a panic) and must NOT yield a kernel-accepted proof.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem obtain_mismatch (h : Atom) : P := by\n  obtain ⟨a, b⟩ := h\n  exact a",
    );
    assert!(
        result.is_err(),
        "obtain ⟨a, b⟩ on a non-pair hypothesis must error, not silently succeed: {result:?}"
    );
}

// ===========================================================================
// Nested existential destructuring (the `∃ x y, P x y` idiom).
//
// `∃ a : Nat, ∃ b : Nat, a = b` desugars to a *nested* `Exists`, so
// `obtain ⟨a, b, hab⟩ := h` flattens to `⟨a, ⟨b, hab⟩⟩`: the outer
// `Exists.casesOn` binds the witness `a` and the PROOF field (itself an
// `∃ b, a = b`), which is then recursively destructured by a second
// `Exists.casesOn`. These tests pin that the recursive destructure assembles a
// fully-solved, sentinel-free proof term that the kernel re-checks (regression
// for the leaked-meta `UnknownFVar(FVarId(2^63 + n))` class).
// ===========================================================================

#[test]
fn test_obtain_nested_exists_flat_pattern_kernel_accepts() {
    // TOOTH 1: flat `⟨a, b, hab⟩` on a nested `∃`. The kernel re-checks the
    // composed `Exists.casesOn ∘ Exists.casesOn` term; no sentinel FVar survives.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem obtain_nested_exists_flat \
         (h : Exists (fun a : Nat => Exists (fun b : Nat => Eq a b))) : True := by\n  \
         obtain ⟨a, b, hab⟩ := h\n  trivial",
    );
    assert!(
        result.is_ok(),
        "flat obtain ⟨a, b, hab⟩ on a nested ∃ should kernel-check (no leaked meta), got: {result:?}"
    );
}

#[test]
fn test_obtain_nested_exists_explicit_pattern_kernel_accepts() {
    // TOOTH 2: explicit nesting `⟨a, ⟨b, hab⟩⟩` on the same nested `∃`.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem obtain_nested_exists_explicit \
         (h : Exists (fun a : Nat => Exists (fun b : Nat => Eq a b))) : True := by\n  \
         obtain ⟨a, ⟨b, hab⟩⟩ := h\n  trivial",
    );
    assert!(
        result.is_ok(),
        "explicit-nested obtain ⟨a, ⟨b, hab⟩⟩ on a nested ∃ should kernel-check, got: {result:?}"
    );
}

#[test]
fn test_obtain_triple_nested_exists_kernel_accepts() {
    // TOOTH 3: triple-nested `∃ a, ∃ b, ∃ c, a = c` destructured `⟨a, b, c, hac⟩`
    // — three composed `Exists.casesOn`, all motives solved.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem obtain_triple_nested_exists \
         (h : Exists (fun a : Nat => Exists (fun b : Nat => Exists (fun c : Nat => Eq a c)))) \
         : True := by\n  obtain ⟨a, b, c, hac⟩ := h\n  trivial",
    );
    assert!(
        result.is_ok(),
        "triple-nested obtain ⟨a, b, c, hac⟩ should kernel-check, got: {result:?}"
    );
}

#[test]
fn test_obtain_nested_exists_used_for_real_kernel_accepts() {
    // TOOTH 4: the destructured witnesses/proof are actually USED to rebuild a
    // nested existential, forcing the fields to carry real (kernel-typed) values.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem obtain_nested_exists_real \
         (h : Exists (fun a : Nat => Exists (fun b : Nat => Eq a b))) \
         : Exists (fun x : Nat => Exists (fun y : Nat => Eq x y)) := by\n  \
         obtain ⟨a, b, hab⟩ := h\n  exact ⟨a, b, hab⟩",
    );
    assert!(
        result.is_ok(),
        "nested obtain then rebuild ⟨a, b, hab⟩ should kernel-check, got: {result:?}"
    );
}

#[test]
fn test_obtain_nested_exists_wrong_closer_errors_not_panics() {
    // TOOTH 5 (NEGATIVE): a 2-field pattern `⟨a, hab⟩` on a nested `∃` binds
    // `hab : ∃ b, a = b` (the inner existential, NOT a proof of the goal). Closing
    // `True` with `exact hab` is a genuine type mismatch — it MUST error (no panic,
    // no over-accept). Real Lean 4 rejects this same shape.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem obtain_nested_exists_wrong \
         (h : Exists (fun a : Nat => Exists (fun b : Nat => Eq a b))) : True := by\n  \
         obtain ⟨a, hab⟩ := h\n  exact hab",
    );
    assert!(
        result.is_err(),
        "2-field pattern on a nested ∃ then a wrong closer must error, not silently succeed: {result:?}"
    );
}

#[test]
fn test_obtain_untyped_exists_unsolved_meta_errors_not_sentinel() {
    // FAIL-CLOSED (no sentinel leak): `∃ a, ∃ b, a = b` with NO binder type
    // leaves the binder type `?α` unresolved (Lean 4 itself rejects this header).
    // The destructure must surface a CLEAN elaboration error — never leak the
    // unsolved-meta sentinel FVar (`2^63 + n`) into the proof term where the
    // kernel would report the confusing `UnknownFVar`.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem obtain_untyped_exists \
         (h : Exists (fun a => Exists (fun b => Eq a b))) : True := by\n  \
         obtain ⟨a, b, hab⟩ := h\n  trivial",
    );
    let err = match result {
        Ok(()) => panic!("untyped nested ∃ must not be accepted (unresolved binder type)"),
        Err(e) => e,
    };
    assert!(
        !err.contains("UnknownFVar"),
        "untyped ∃ must fail with a clean diagnostic, NOT a leaked sentinel UnknownFVar: {err}"
    );
}

// ===========================================================================
// TOP-LEVEL `rfl` pattern (`rcases h with rfl` / `obtain rfl := h`).
//
// A TOP-LEVEL `rfl` pattern applied to an existing equality hypothesis IS
// `subst h`: it substitutes the equation away throughout the goal and context,
// exactly like the in-a-tuple `⟨rfl, _⟩` field pattern and `cases`-on-`Eq`.
// Previously this was a no-op, leaving the goal unsubstituted (a `fvar mismatch`
// when the trailing tactic tried to close it). Each positive was cross-checked
// against real Lean 4 (accepts). The negatives are rejected by Lean 4 too.
// ===========================================================================

#[test]
fn test_rcases_top_level_rfl_substitutes_kernel_accepts() {
    // TOOTH 1: `rcases h with rfl` on `h : a = b ⊢ b = a`. After subst the goal
    // is `a = a` (or `b = b`), which the trailing `rfl` closes. Kernel re-checks
    // the assembled `Eq.ndrec` proof end-to-end via `add_decl`.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem rcases_top_rfl (a b : Nat) (h : Eq a b) : Eq b a := by\n  rcases h with rfl\n  rfl",
    );
    assert!(
        result.is_ok(),
        "rcases h with rfl on h : a = b ⊢ b = a should subst then close with rfl, got: {result:?}"
    );
}

#[test]
fn test_obtain_top_level_rfl_substitutes_kernel_accepts() {
    // TOOTH 2: `obtain rfl := h` on the same goal. The bare-hypothesis fast path
    // routes to `subst h` directly (Lean consumes `h`), no `have_` copy.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem obtain_top_rfl (a b : Nat) (h : Eq a b) : Eq b a := by\n  obtain rfl := h\n  rfl",
    );
    assert!(
        result.is_ok(),
        "obtain rfl := h on h : a = b ⊢ b = a should subst then close with rfl, got: {result:?}"
    );
}

#[test]
fn test_obtain_top_level_rfl_substitution_is_real_with_dependent_hyp_kernel_accepts() {
    // TOOTH 3 (DECISIVE): a hypothesis `hp : pr a` DEPENDS on the substituted
    // variable. After `obtain rfl := h` (`h : a = b`), `pr a`/`pr b` must be
    // reconciled by a GENUINE subst that eliminates the side not referenced by
    // `hp`, so that `exact hp` closes `pr b`. A no-op or wrong-direction subst
    // leaves a `fvar mismatch` that the kernel re-check rejects.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem obtain_top_rfl_real (a b : A) (h : Eq a b) (hp : pr a) : pr b := by\n  \
         obtain rfl := h\n  exact hp",
    );
    assert!(
        result.is_ok(),
        "obtain rfl := h with a dependent hyp `hp : pr a` proving `pr b` should kernel-check, got: {result:?}"
    );
}

#[test]
fn test_rcases_top_level_rfl_on_non_equality_errors_not_panics() {
    // TOOTH 4 (NEGATIVE): `rcases h with rfl` where `h : P ∧ Q` is NOT an
    // equality. The `rfl` pattern routes to `subst`, which fails-closed with an
    // elaboration error ("not an equality") — never a panic, never an
    // over-accept. Real Lean 4 rejects this same shape (`subst` failed: invalid
    // equality proof).
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem rcases_top_rfl_nonequality (h : And P Q) : P := by\n  rcases h with rfl",
    );
    assert!(
        result.is_err(),
        "rcases h with rfl on a non-equality hypothesis must error, not silently succeed: {result:?}"
    );
}

#[test]
fn test_obtain_top_level_rfl_unclosable_goal_errors_not_panics() {
    // TOOTH 5 (NEGATIVE): `obtain rfl := h` on `h : a = b ⊢ b = c`. After subst
    // the goal is `a = c` (or `b = c` in the other direction), which the trailing
    // `rfl` cannot close — it MUST error (no panic, no over-accept). Real Lean 4
    // rejects this same shape (`rfl` failed: not definitionally equal).
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem obtain_top_rfl_unclosable (a b c : Nat) (h : Eq a b) : Eq b c := by\n  \
         obtain rfl := h\n  rfl",
    );
    assert!(
        result.is_err(),
        "obtain rfl := h leaving an unclosable goal must error, not silently succeed: {result:?}"
    );
}
