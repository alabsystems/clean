// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Match compilation of covers that are exhaustive only JOINTLY, through the
//! elaborator's production entry (`elaborate_decl_and_register`: elaborate,
//! then the full kernel check).
//!
//! Each shape is from trust-ir's Lean 4.8.0 semantics package, minimized, and
//! Lean 4.8.0 accepts every definition here:
//!
//! * a recursive minor whose arms differ in a nested field sub-pattern with no
//!   catch-all (`Pred.lean` `filterSomeBounds` / `sequenceBounds`): the
//!   fallback chain had nothing to fall back to under its last arm;
//! * relative constructor heads (`.int`) that two inductives both declare
//!   (`Arith.lean` `semVectorIntBinOp`): the equation pattern matrix could not
//!   canonicalize them without the column type and dropped the definition;
//! * a three-column matrix whose constructor heads already cover a column
//!   (`Step.lean` `semVectorSelectLanes`, gap G18): the unreachable default
//!   arm was compiled into a PARTIAL match of its own.
//!
//! Every acceptance is pinned by `rfl` theorems the kernel only accepts by
//! reducing the lowered term, and each widening carries a negative control
//! Lean rejects: a FALSE `rfl`, or a cover that is genuinely partial.

use super::*;

/// Parse and register `src` (one declaration) through the production entry.
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

/// A FALSE `rfl` must be refused (Lean rejects it).
fn rfl_refused(env: &mut Environment, name: &str, lhs: &str, rhs: &str) {
    let src = format!("theorem {name} : {lhs} = {rhs} := rfl");
    assert!(
        register(env, &src).is_err(),
        "a false equation must be refused: {src}"
    );
    assert!(
        env.get_const(&Name::from_string(name)).is_none(),
        "the refused theorem `{name}` must not be registered"
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

const FILTER_SOME: &str = "def filterSome : List (Option Nat) → List Nat
  | []             => []
  | none :: rest   => filterSome rest
  | some b :: rest => b :: filterSome rest";

#[test]
fn test_rec_joint_cover_filter_some_elaborates_and_computes() {
    let mut env = Environment::with_prelude();
    register_ok(&mut env, FILTER_SOME);
    rfl_ok(&mut env, "fs_nil", "filterSome []", "[]");
    rfl_ok(
        &mut env,
        "fs_mixed",
        "filterSome [some 1, none, some 2, none]",
        "[1, 2]",
    );
    rfl_ok(&mut env, "fs_none", "filterSome [none, none]", "[]");
    rfl_refused(
        &mut env,
        "fs_false",
        "filterSome [some 1, none, some 2]",
        "[1]",
    );
}

/// A user-written `sorry` in a split arm is the program, not a minor the
/// lowering failed to build: Lean 4 accepts it with a warning. The split used
/// to discard ANY sorry-bearing minor, so the chain refused the cover as
/// non-exhaustive. It must elaborate, keep only the user's sorry, and stay
/// visible to the audit; a sorry arm must not excuse a missing case.
#[test]
fn test_rec_joint_cover_user_sorry_arm_elaborates_and_is_audited() {
    for (arm, with_sorry) in [
        ("none", "  | none :: rest   => sorry"),
        ("some", "  | some b :: rest => sorry"),
    ] {
        let mut env = Environment::with_prelude();
        let original = FILTER_SOME
            .lines()
            .find(|line| line.starts_with(&format!("  | {arm}")))
            .expect("the arm being replaced");
        register_ok(&mut env, &FILTER_SOME.replace(original, with_sorry));
        let name = Name::from_string("filterSome");
        let value = env
            .get_const(&name)
            .and_then(|info| info.value.clone())
            .expect("registered body");
        assert!(
            value.has_non_synthetic_sorry(),
            "`{arm}` arm: the user's sorry is kept"
        );
        assert!(
            !value.has_synthetic_sorry(),
            "`{arm}` arm: no compiler-minted sorry"
        );
        let closure = env.axiom_deps(&name).expect("closure");
        assert!(
            closure.contains(&Name::from_string("sorryAx")),
            "`{arm}` arm: an incomplete body must stay visible to the audit"
        );
    }
    let mut env = Environment::with_prelude();
    refused_because(
        &mut env,
        "filterSome",
        "def filterSome : List (Option Nat) → List Nat
  | []           => []
  | none :: rest => sorry",
        NOT_EXHAUSTIVE,
    );
}

#[test]
fn test_rec_joint_cover_sequence_option_elaborates_and_computes() {
    let mut env = Environment::with_prelude();
    register_ok(
        &mut env,
        "def seqOpt : List (Option Nat) → Option (List Nat)
  | []             => some []
  | none :: _      => none
  | some b :: rest => (seqOpt rest).map (fun bs => b :: bs)",
    );
    rfl_ok(&mut env, "so_all", "seqOpt [some 1, some 2]", "some [1, 2]");
    rfl_ok(&mut env, "so_hole", "seqOpt [some 1, none, some 3]", "none");
    rfl_refused(&mut env, "so_false", "seqOpt [some 1, none]", "some [1]");
}

#[test]
fn test_rec_joint_cover_explicit_match_elaborates_and_computes() {
    let mut env = Environment::with_prelude();
    register_ok(
        &mut env,
        "def sumSome (l : List (Option Nat)) : Nat :=
  match l with
  | []             => 0
  | none :: rest   => sumSome rest
  | some b :: rest => b + sumSome rest",
    );
    rfl_ok(&mut env, "ss_val", "sumSome [some 4, none, some 5]", "9");
    rfl_refused(&mut env, "ss_false", "sumSome [some 4, none, some 5]", "4");
}

/// Negative control: the same shape with a genuinely missing case
/// (`some (n+1) :: rest`) — Lean reports `missing cases` — stays refused.
#[test]
fn test_rec_joint_cover_genuinely_partial_cover_is_refused() {
    let mut env = Environment::with_prelude();
    refused_because(
        &mut env,
        "partialSome",
        "def partialSome : List (Option Nat) → Nat
  | []             => 0
  | none :: rest   => partialSome rest
  | some 0 :: rest => partialSome rest",
        NOT_EXHAUSTIVE,
    );
}

/// Two inductives both declare `int` and `bool`, so `.int`/`.bool` name no
/// single constructor without the column's type.
fn ambiguous_ctor_env() -> Environment {
    let mut env = Environment::with_prelude();
    register_ok(
        &mut env,
        "inductive KConst where
  | int : Int → KConst
  | bool : Bool → KConst",
    );
    register_ok(
        &mut env,
        "inductive Val where
  | int : Nat → Int → Val
  | bool : Bool → Val
  | unit : Val",
    );
    env
}

#[test]
fn test_rec_matrix_ambiguous_relative_heads_elaborates_and_computes() {
    let mut env = ambiguous_ctor_env();
    register_ok(
        &mut env,
        "def laneAdd (width : Nat) : List Val → List Val → Except String (List Val)
  | [], [] => .ok []
  | .int w1 l :: lhsRest, .int w2 r :: rhsRest =>
    if w1 != width || w2 != width then
      .error \"width\"
    else do
      let rest ← laneAdd width lhsRest rhsRest
      pure (.int width (l + r) :: rest)
  | [], _ :: _ => .error \"count\"
  | _ :: _, [] => .error \"count\"
  | _ :: _, _ :: _ => .error \"lane\"",
    );
    rfl_ok(
        &mut env,
        "la_ok",
        "laneAdd 8 [.int 8 1, .int 8 2] [.int 8 10, .int 8 20]",
        "Except.ok [Val.int 8 11, Val.int 8 22]",
    );
    rfl_ok(
        &mut env,
        "la_lane",
        "laneAdd 8 [.int 8 1, .bool true] [.int 8 10, .int 8 20]",
        "Except.error \"lane\"",
    );
    rfl_ok(
        &mut env,
        "la_count",
        "laneAdd 8 [] [.unit]",
        "Except.error \"count\"",
    );
    rfl_refused(
        &mut env,
        "la_false",
        "laneAdd 8 [.int 8 1, .bool true] [.int 8 10, .int 8 20]",
        "Except.error \"count\"",
    );
}

/// Negative control for the relative-head grouping: DISTINCT relative names
/// stay distinct constructors. A grouping that conflated `.int` and `.bool`
/// would send `.bool` to the `.int` arm.
#[test]
fn test_rec_matrix_ambiguous_relative_heads_stay_distinct() {
    let mut env = ambiguous_ctor_env();
    register_ok(
        &mut env,
        "def headTag : List Val → List Val → Nat
  | .int _ _ :: _, _ => 1
  | .bool _ :: _, _ => 2
  | _, _ => 3",
    );
    rfl_ok(&mut env, "ht_int", "headTag [.int 1 1] []", "1");
    rfl_ok(&mut env, "ht_bool", "headTag [.bool false] []", "2");
    rfl_ok(&mut env, "ht_unit", "headTag [.unit] []", "3");
    rfl_refused(&mut env, "ht_false", "headTag [.bool false] []", "1");
}

const ZIP3: &str = "def zip3 : List Nat → List Nat → List Nat → Except String (List Nat)
  | [], [], [] => .ok []
  | a :: as, b :: bs, c :: cs => do
    let rest ← zip3 as bs cs
    pure ((a + b + c) :: rest)
  | _ :: _, _, _ => .error \"lane count mismatch\"
  | [], _ :: _, _ => .error \"lane count mismatch\"
  | [], _, _ :: _ => .error \"lane count mismatch\"";

#[test]
fn test_matrix_complete_signature_three_columns_elaborates_and_computes() {
    let mut env = Environment::with_prelude();
    register_ok(&mut env, ZIP3);
    rfl_ok(
        &mut env,
        "z3_ok",
        "zip3 [1, 2] [10, 20] [100, 200]",
        "Except.ok [111, 222]",
    );
    rfl_ok(
        &mut env,
        "z3_short",
        "zip3 [1] [10] []",
        "Except.error \"lane count mismatch\"",
    );
    rfl_ok(
        &mut env,
        "z3_mid",
        "zip3 [] [] [5]",
        "Except.error \"lane count mismatch\"",
    );
    rfl_refused(&mut env, "z3_false", "zip3 [1] [10] [100]", "Except.ok [1]");
}

/// The same matrix with no recursion: the default arm was the defect, not
/// the recursive lowering.
#[test]
fn test_matrix_complete_signature_nonrecursive_elaborates_and_computes() {
    let mut env = Environment::with_prelude();
    register_ok(
        &mut env,
        "def shape3 : List Nat → List Nat → List Nat → Nat
  | [], [], [] => 0
  | _ :: _, _ :: _, _ :: _ => 1
  | _ :: _, _, _ => 2
  | [], _ :: _, _ => 3
  | [], _, _ :: _ => 4",
    );
    rfl_ok(&mut env, "s3_a", "shape3 [] [] []", "0");
    rfl_ok(&mut env, "s3_b", "shape3 [1] [2] [3]", "1");
    rfl_ok(&mut env, "s3_c", "shape3 [1] [] [3]", "2");
    rfl_ok(&mut env, "s3_d", "shape3 [] [2] []", "3");
    rfl_ok(&mut env, "s3_e", "shape3 [] [] [3]", "4");
    rfl_refused(&mut env, "s3_false", "shape3 [] [] [3]", "3");
}

/// Negative control for the complete-signature rule: the same matrices
/// WITHOUT the `[], _, _ :: _` row miss `[], [], _ :: _` (Lean 4.8.0: `missing
/// cases: [], [], (List.cons _ _)`). Dropping the default arm of the complete
/// first column must not hide that hole, recursive or not.
#[test]
fn test_matrix_complete_signature_missing_row_is_refused() {
    let mut env = Environment::with_prelude();
    for (name, src) in [
        (
            "shape3Partial",
            "def shape3Partial : List Nat → List Nat → List Nat → Nat
  | [], [], [] => 0
  | _ :: _, _ :: _, _ :: _ => 1
  | _ :: _, _, _ => 2
  | [], _ :: _, _ => 3",
        ),
        (
            "zip3Partial",
            "def zip3Partial : List Nat → List Nat → List Nat → Except String (List Nat)
  | [], [], [] => .ok []
  | a :: as, b :: bs, c :: cs => do
    let rest ← zip3Partial as bs cs
    pure ((a + b + c) :: rest)
  | _ :: _, _, _ => .error \"lane count mismatch\"
  | [], _ :: _, _ => .error \"lane count mismatch\"",
        ),
    ] {
        refused_because(&mut env, name, src, NOT_EXHAUSTIVE_MATRIX_83);
    }
}
