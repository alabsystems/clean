// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression coverage for the `cases` DEPENDENT-MOTIVE bug.
//!
//! `cases <var> with | …` failed exactly when the goal MENTIONS the scrutinee
//! (a dependent motive `fun n => P n`), while a non-dependent goal succeeded.
//! Three independent defects combined:
//!
//! 1. **`cases` used the strict `close_goal`** (`proof_manipulation.rs`). The
//!    casesOn minor premises are open subgoal metavariables whose stored targets
//!    are the *constructor-specialized* goals (`Eq (succ k) (succ k)`), i.e. the
//!    motive already beta-reduced and substituted at the constructor. casesOn's
//!    strict App-arg check instead expects each minor to inhabit the *unreduced*
//!    dependent application `motive (ctor …)` (a beta-redex). For a dependent
//!    motive the strict path rejected this genuinely-valid term. Fix: use
//!    `close_goal_assembled` (the lenient recursor-spine variant `induction`
//!    already uses); strict re-check is deferred to `verify_tactic_proof`.
//!
//! 2. **`exact` elaborated its term against a stale expected type**
//!    (`elab_tactic.rs`). Inside a branch, `exact Or.inr …` read the original
//!    `by`-block target (carrying the pre-`cases` scrutinee FVar), so the `Or`
//!    disjunct was matched against `n` instead of `succ k`. Fix: elaborate the
//!    `exact`/bare-term argument against the CURRENT goal target, as `refine`
//!    already does.
//!
//! 3. **A polymorphic head constant's universe level parameter was never
//!    solved** (`elab_app.rs`). `∃ m, n = m + 1` desugars to `Exists.{u_1} ?α …`
//!    with `u_1` a free `Level::Param`; ordinary unification solved `?α := Nat`
//!    but left `u_1` unconstrained, so the kernel rejected `Nat : Sort u_1` vs
//!    `Nat : Sort 1`. Fix: after assembling the application (and in the
//!    anonymous constructor), solve each `Sort (Param p)` parameter from the
//!    concrete type-argument's universe via the level union-find.
//!
//! Soundness is preserved throughout: every assembled proof is strictly
//! re-checked by `verify_tactic_proof` and kernel-rechecked by `add_decl`, so a
//! wrong motive, wrong disjunct, or wrong universe fails downstream — the WRONG
//! branch test below confirms no over-acceptance.

use crate::elaborate_decl_and_register;
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

/// Elaborate every declaration in `code`; assert all succeed and `expected_name`
/// is registered.
fn elab_all_and_assert_ok(code: &str, expected_name: &str) {
    let mut env = Environment::with_prelude();
    let decls = parse_file(code).expect("should parse");
    let mut outcomes: Vec<String> = Vec::new();
    for (i, decl) in decls.iter().enumerate() {
        if let clean_parser::SurfaceDecl::RawDecl { content, span } = decl {
            panic!("decl {i} fell through to RawDecl (parser error recovery); content={content:?}, span={span:?}");
        }
        match elaborate_decl_and_register(&mut env, decl) {
            Ok(_) => outcomes.push(format!("decl {i}: OK")),
            Err(e) => outcomes.push(format!("decl {i}: ERR = {e:?}")),
        }
    }
    assert!(
        outcomes.iter().all(|o| !o.contains("ERR")),
        "cases dependent-motive regression: elaboration errors: {outcomes:#?}"
    );
    assert!(
        env.get_const(&Name::from_string(expected_name)).is_some(),
        "{expected_name} should be registered (outcomes: {outcomes:#?})"
    );
}

/// Elaborate `code`; assert at least one declaration ERRORS (no over-accept).
fn elab_all_and_assert_err(code: &str) {
    let mut env = Environment::with_prelude();
    let decls = parse_file(code).expect("should parse");
    let any_err = decls
        .iter()
        .filter(|d| !matches!(d, clean_parser::SurfaceDecl::RawDecl { .. }))
        .any(|decl| elaborate_decl_and_register(&mut env, decl).is_err());
    assert!(
        any_err,
        "expected an elaboration error (false branch goal is unprovable), but all decls succeeded"
    );
}

/// The headline bug: dependent motive `fun n => n = n`, proved per-constructor
/// by `rfl`. Failed before the fix with a casesOn minor-premise TypeMismatch.
#[test]
fn test_cases_dependent_motive_nat_eq_refl() {
    let code = "theorem t (n : Nat) : n = n := by cases n with | zero => rfl | succ k => rfl\n";
    elab_all_and_assert_ok(code, "t");
}

/// Dependent motive over `Bool` — a different inductive, same shape.
#[test]
fn test_cases_dependent_motive_bool_eq_refl() {
    let code = "theorem t (b : Bool) : b = b := by cases b with | false => rfl | true => rfl\n";
    elab_all_and_assert_ok(code, "t");
}

/// Dependent motive + a disjunction whose right arm supplies an existential
/// WITNESS via the anonymous constructor. Exercises all three sub-fixes at once:
/// dependent motive, branch-`exact` disjunct selection, and the `Exists`
/// universe-level solve.
#[test]
fn test_cases_dependent_motive_or_with_existential_witness() {
    let code = "theorem t (n : Nat) : n = 0 \u{2228} \u{2203} m, n = m + 1 := by cases n with | zero => exact Or.inl rfl | succ k => exact Or.inr \u{27e8}k, rfl\u{27e9}\n";
    elab_all_and_assert_ok(code, "t");
}

/// The non-dependent case must KEEP working (motive does not mention the
/// scrutinee). This path was always green; guard against a regression.
#[test]
fn test_cases_non_dependent_motive_true_unchanged() {
    let code =
        "theorem t (n : Nat) : True := by cases n with | zero => trivial | succ k => trivial\n";
    elab_all_and_assert_ok(code, "t");
}

/// SOUNDNESS guard: the `succ` branch goal `Nat.succ k = 0` is FALSE, so `rfl`
/// cannot close it. The whole declaration must be REJECTED — the fix must not
/// over-accept by handing branches a wrong/weaker motive.
#[test]
fn test_cases_dependent_motive_wrong_branch_rejected() {
    let code = "theorem t (n : Nat) : n = 0 := by cases n with | zero => rfl | succ k => rfl\n";
    elab_all_and_assert_err(code);
}

/// The universe-level solve also fixes the bare existential TYPE (no proof):
/// `∃ m, n = m + 1` with an elided binder type must elaborate without leaving an
/// unsolved `Exists` universe parameter.
#[test]
fn test_existential_type_elided_binder_universe_solved() {
    let code = "axiom t (n : Nat) : n = 0 \u{2228} \u{2203} m, n = m + 1\n";
    elab_all_and_assert_ok(code, "t");
}
