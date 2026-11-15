// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rows that OVERLAP across columns — a binder in one column beside a
//! constructor in another, `| _, .top => … | .top, _ => … | .interval ..,
//! .interval .. => …` (a lattice `implies`) — through the elaborator's
//! production entry (`elaborate_decl_and_register`: elaborate, then the full
//! kernel check).
//!
//! Both surface decision-tree builders split the first column on its
//! constructor heads and, for the binder rows, added a DEFAULT arm. Here the
//! heads already name every constructor, so the default is unreachable, but
//! its rows are only the binder rows — `match y with | .top => …`, a partial
//! match — and the whole definition was refused: "Match arm 2 has type … but
//! match motive expects Bool" for the equation form
//! (`compile_pattern_matrix`), "non-exhaustive nested constructor pattern
//! `Shape.interval`" for a term-mode `match x, y` and for a recursive minor
//! (`build_column_split_surface`). Neither emits the default for a complete
//! signature now (`infer/elab_match/signature.rs`), as Lean 4.8.0's
//! `processConstructor` never does.
//!
//! Every value here is the pinned Lean 4.8.0 binary's (checked 2026-10-04):
//! it accepts each definition and `rfl` below, rejects each FALSE `rfl`, and
//! reports `missing cases: top, (interval _ _)` (or the recursive analogue)
//! for each partial cover.

use super::*;

fn register(env: &mut Environment, src: &str) -> Result<(), ElabError> {
    let decl = parse_decl_for_elab(src)?;
    crate::elaborate_decl_and_register(env, &decl).map(|_| ())
}

fn register_ok(env: &mut Environment, src: &str) {
    if let Err(err) = register(env, src) {
        panic!("should elaborate and kernel-check:\n{src}\n{err:?}");
    }
}

/// `theorem name : lhs = rhs := rfl` — accepted only when the kernel reduces
/// `lhs` to `rhs`.
fn rfl_ok(env: &mut Environment, name: &str, lhs: &str, rhs: &str) {
    register_ok(env, &format!("theorem {name} : {lhs} = {rhs} := rfl"));
}

/// Refused, and not registered.
fn refused(env: &mut Environment, name: &str, src: &str) {
    assert!(register(env, src).is_err(), "must be refused:\n{src}");
    assert!(
        env.get_const(&Name::from_string(name)).is_none(),
        "the refused `{name}` must not be registered"
    );
}

/// Markers of a refusal BECAUSE some value matches no alternative (Lean
/// 4.8.0: `missing cases`). A refusal for any other reason fails the control.
const NOT_EXHAUSTIVE: &[&str] = &["non-exhaustive", "missing"];

/// The same refusal where the equation matrix (`compile_pattern_matrix`)
/// emits the partial match as written: the lowering refuses it positionally
/// (`Type mismatch` / `Match arm … motive`), not as `missing cases` — ledger
/// class (83), wrong message, right verdict. The accepted twin with the
/// missing row restored is in the same file.
const NOT_EXHAUSTIVE_MATRIX_83: &[&str] =
    &["non-exhaustive", "missing", "Type mismatch", "Match arm"];

/// Refused for one of `reasons`, and not registered.
fn refused_because(env: &mut Environment, name: &str, src: &str, reasons: &[&str]) {
    let err = match register(env, src) {
        Ok(()) => panic!("`{name}` must be refused:\n{src}"),
        Err(err) => format!("{err}"),
    };
    assert!(
        reasons.iter().any(|reason| err.contains(reason)),
        "`{name}` must be refused for one of {reasons:?}, got: {err}"
    );
    assert!(
        env.get_const(&Name::from_string(name)).is_none(),
        "the refused `{name}` must not be registered"
    );
}

/// A FALSE `rfl` must be refused (Lean rejects it).
fn rfl_refused(env: &mut Environment, name: &str, lhs: &str, rhs: &str) {
    refused(env, name, &format!("theorem {name} : {lhs} = {rhs} := rfl"));
}

fn shape_env() -> Environment {
    let mut env = Environment::with_prelude();
    register_ok(
        &mut env,
        "inductive Shape where\n  | top\n  | interval (lo hi : Nat)",
    );
    env
}

/// The five cases every `implies` below must compute, with Lean's values.
fn assert_implies_cases(env: &mut Environment, func: &str) {
    let cases = [
        ("tt", ".top .top", "true"),
        ("ii_t", "(.interval 2 5) (.interval 0 7)", "true"),
        ("ii_f", "(.interval 0 7) (.interval 2 5)", "false"),
        ("ti", ".top (.interval 0 7)", "false"),
        ("it", "(.interval 0 7) .top", "true"),
    ];
    for (tag, args, value) in cases {
        let name = format!("{}_{tag}", func.replace('.', "_"));
        rfl_ok(env, &name, &format!("{func} {args}"), value);
    }
    // `.top, .interval` reaches the SECOND row, not the first.
    let false_name = format!("{}_false", func.replace('.', "_"));
    rfl_refused(
        env,
        &false_name,
        &format!("{func} .top (.interval 0 7)"),
        "true",
    );
}

#[test]
fn test_overlapping_rows_equation_form_elaborates_and_computes() {
    let mut env = shape_env();
    register_ok(
        &mut env,
        "def Shape.implies : Shape → Shape → Bool
  | _, .top => true
  | .top, _ => false
  | .interval a b, .interval c d => c ≤ a && b ≤ d",
    );
    assert_implies_cases(&mut env, "Shape.implies");
}

#[test]
fn test_overlapping_rows_term_match_elaborates_and_computes() {
    let mut env = shape_env();
    register_ok(
        &mut env,
        "def Shape.impliesM (x y : Shape) : Bool :=
  match x, y with
  | _, .top => true
  | .top, _ => false
  | .interval a b, .interval c d => c ≤ a && b ≤ d",
    );
    assert_implies_cases(&mut env, "Shape.impliesM");
}

/// Three constructors, the binder in the SECOND column of a middle row: the
/// complete signature is spread over rows above and below it.
#[test]
fn test_overlapping_rows_three_constructors_elaborate_and_compute() {
    let mut env = Environment::with_prelude();
    register_ok(&mut env, "inductive Tri where | a | b | c");
    let arms = "  | .a, _ => 0
  | _, .a => 1
  | .b, .b => 2
  | .b, .c => 3
  | .c, _ => 4";
    register_ok(&mut env, &format!("def Tri.f : Tri → Tri → Nat\n{arms}"));
    register_ok(
        &mut env,
        &format!("def Tri.g (x y : Tri) : Nat :=\n  match x, y with\n{arms}"),
    );
    for func in ["Tri.f", "Tri.g"] {
        let tag = func.replace('.', "_");
        for (case, args, value) in [
            ("ac", ".a .c", "0"),
            ("ba", ".b .a", "1"),
            ("ca", ".c .a", "1"),
            ("bb", ".b .b", "2"),
            ("bc", ".b .c", "3"),
            ("cb", ".c .b", "4"),
        ] {
            rfl_ok(
                &mut env,
                &format!("{tag}_{case}"),
                &format!("{func} {args}"),
                value,
            );
        }
        // `.c, .a` reaches `_, .a` before `.c, _`.
        rfl_refused(
            &mut env,
            &format!("{tag}_false"),
            &format!("{func} .c .a"),
            "4",
        );
    }
}

/// The overlap inside a recursive minor's field columns: the decision tree
/// the joint-cover rescue builds (`rec_column_split`) has the same default.
#[test]
fn test_overlapping_rows_recursive_minor_elaborates_and_computes() {
    let mut env = shape_env();
    register_ok(
        &mut env,
        "def countImp : List (Shape × Shape) → Nat
  | [] => 0
  | (_, .top) :: rest => countImp rest + 1
  | (.top, _) :: rest => countImp rest
  | (.interval _ _, .interval _ _) :: rest => countImp rest + 10",
    );
    rfl_ok(
        &mut env,
        "count_imp_val",
        "countImp [(.top, .top), (.top, .interval 0 1), (.interval 0 1, .top), \
         (.interval 0 1, .interval 2 3)]",
        "12",
    );
    rfl_refused(
        &mut env,
        "count_imp_false",
        "countImp [(.top, .interval 0 1)]",
        "1",
    );
}

/// Negative control for the complete-signature rule: without the `.top, _`
/// row, `.top, .interval _ _` matches nothing (Lean 4.8.0: `missing cases:
/// top, (interval _ _)`). Dropping the default of the complete first column
/// must not hide that hole in any of the three lowerings.
#[test]
fn test_overlapping_rows_partial_cover_is_refused() {
    let mut env = shape_env();
    refused_because(
        &mut env,
        "Shape.partialImplies",
        "def Shape.partialImplies : Shape → Shape → Bool
  | _, .top => true
  | .interval a b, .interval c d => c ≤ a && b ≤ d",
        NOT_EXHAUSTIVE_MATRIX_83,
    );
    refused_because(
        &mut env,
        "Shape.partialImpliesM",
        "def Shape.partialImpliesM (x y : Shape) : Bool :=
  match x, y with
  | _, .top => true
  | .interval a b, .interval c d => c ≤ a && b ≤ d",
        NOT_EXHAUSTIVE,
    );
    refused_because(
        &mut env,
        "countImpPartial",
        "def countImpPartial : List (Shape × Shape) → Nat
  | [] => 0
  | (_, .top) :: rest => countImpPartial rest + 1
  | (.interval _ _, .interval _ _) :: rest => countImpPartial rest + 10",
        NOT_EXHAUSTIVE,
    );
}
