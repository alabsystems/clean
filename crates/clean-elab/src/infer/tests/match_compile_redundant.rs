// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A match alternative that no value selects is refused, as Lean 4.8.0
//! refuses it ("redundant alternative", `reportMatcherResultErrors` in
//! `src/Lean/Elab/Match.lean`), through the elaborator's production entry
//! (`elaborate_decl_and_register`).
//!
//! The surface decision trees (`compile_pattern_matrix` for equation-form
//! definitions, `build_column_split_surface` for constructor-field splits and
//! the recursive joint-cover rescue) keep the FIRST row each leaf reaches and
//! drop the rest. Once they compiled complete covers (no unreachable default,
//! a joint cover rescued), an unreachable row was accepted with its body
//! silently never run. They now record which rows a leaf selects
//! (`infer/elab_match/row_reach.rs`) and refuse a row none selects.
//!
//! Every verdict below is the pinned Lean 4.8.0 binary's (2026-10-07,
//! `scratchpad/match-compile/v17/oracle/R.lean`): each refused definition is
//! "redundant alternative" there, at the alternative the assertion names.
//! The accepted twins of these shapes (the same definitions without the
//! redundant row) are `match_compile_joint_cover.rs` and
//! `match_compile_overlap.rs`.

use super::*;

fn register(env: &mut Environment, src: &str) -> Result<(), ElabError> {
    let decl = parse_decl_for_elab(src)?;
    crate::elaborate_decl_and_register(env, &decl).map(|_| ())
}

/// Refused as a redundant alternative, naming alternative `alt` (1-based, as
/// written), and not registered.
fn refused_redundant(env: &mut Environment, name: &str, alt: usize, src: &str) {
    let err = match register(env, src) {
        Ok(()) => panic!("`{name}` has an alternative no value selects; Lean refuses it:\n{src}"),
        Err(err) => err,
    };
    let text = format!("{err}");
    assert!(
        matches!(err, ElabError::RedundantAlternative { .. })
            && text.contains(&format!("alternative {alt} of")),
        "`{name}` must be refused as redundant alternative {alt}, got: {text}"
    );
    assert!(
        env.get_const(&Name::from_string(name)).is_none(),
        "the refused `{name}` must not be registered"
    );
}

/// The recursive joint cover with a repeated row: the field tree the rescue
/// builds selects `none :: rest` at its FIRST row only.
#[test]
fn test_redundant_alternative_rec_joint_cover_repeated_row_is_refused() {
    let mut env = Environment::with_prelude();
    refused_redundant(
        &mut env,
        "redJoint",
        4,
        "def redJoint : List (Option Nat) → Nat
  | []             => 0
  | none :: rest   => redJoint rest
  | some b :: rest => b + redJoint rest
  | none :: rest   => 99 + redJoint rest",
    );
}

/// The same cover closed by a field binder row: the fallback chain compiles
/// it (its last arm is total), and the row is still reached by no value.
#[test]
fn test_redundant_alternative_rec_chain_total_last_row_is_refused() {
    let mut env = Environment::with_prelude();
    refused_redundant(
        &mut env,
        "chainRed",
        4,
        "def chainRed : List (Option Nat) → Nat
  | []             => 0
  | none :: rest   => chainRed rest
  | some b :: rest => b + chainRed rest
  | _ :: rest      => 7 + chainRed rest",
    );
}

/// The equation matrix over a complete signature: `false, _` comes after
/// `false, false` and `_, true` have taken every `false` row.
#[test]
fn test_redundant_alternative_equation_matrix_overlap_is_refused() {
    let mut env = Environment::with_prelude();
    refused_redundant(
        &mut env,
        "redOverlap",
        4,
        "def redOverlap : Bool → Bool → Nat
  | _, true => 1
  | true, _ => 2
  | false, false => 3
  | false, _ => 4",
    );
    refused_redundant(
        &mut env,
        "dupPair",
        3,
        "def dupPair : List Nat → List Nat → Nat
  | _ :: _, _ => 1
  | [], _ => 2
  | [], [] => 3",
    );
}

/// Three constructors, equation form and a term-mode `match x, y` (the field
/// split of `Prod.mk`): `.c, .b` follows `.c, _`.
#[test]
fn test_redundant_alternative_three_constructors_is_refused() {
    let mut env = Environment::with_prelude();
    let decl = parse_decl_for_elab("inductive Tri where | a | b | c").expect("parses");
    crate::elaborate_decl_and_register(&mut env, &decl).expect("Tri elaborates");
    let arms = "  | .a, _ => 0
  | _, .a => 1
  | .b, _ => 2
  | .c, _ => 3
  | .c, .b => 4";
    refused_redundant(
        &mut env,
        "triRed",
        5,
        &format!("def triRed : Tri → Tri → Nat\n{arms}"),
    );
    refused_redundant(
        &mut env,
        "triRedM",
        5,
        &format!("def triRedM (x y : Tri) : Nat :=\n  match x, y with\n{arms}"),
    );
}

/// A recursive `Nat` match whose arms are read as constructors (`n + 1`,
/// literals): an arm after full `zero`/`succ` cover. It used to be refused
/// only by accident (the source-order loop's garbled "expected valid type,
/// got Expected function type"); it is now named. `natOk`, the same arms
/// with the literal BEFORE `n + 1`, is accepted (Lean too; oracle
/// `v17/oracle/N2.lean`).
#[test]
fn test_redundant_alternative_recursive_nat_arm_is_refused() {
    let mut env = Environment::with_prelude();
    refused_redundant(
        &mut env,
        "natRed",
        3,
        "def natRed : Nat → Nat
  | n + 1 => natRed n
  | _ => 0
  | _ => 1",
    );
    refused_redundant(
        &mut env,
        "natLit",
        3,
        "def natLit : Nat → Nat
  | 0 => 0
  | n + 1 => natLit n
  | 3 => 7",
    );
    let decl = parse_decl_for_elab(
        "def natOk : Nat → Nat
  | 0 => 0
  | 3 => 7
  | n + 1 => natOk n",
    )
    .expect("parses");
    crate::elaborate_decl_and_register(&mut env, &decl)
        .unwrap_or_else(|err| panic!("every arm of `natOk` is reached: {err:?}"));
}

/// OPEN, ledger class (89): the single-column lowerings that never build a
/// field decision tree still compile a redundant alternative and drop it.
/// Lean 4.8.0 refuses both definitions ("redundant alternative" at the second
/// `some _` and at `_ => 7`); Clean accepts them. This pin fails the day the
/// class closes: then turn each into a `refused_redundant` row.
#[test]
fn test_redundant_alternative_single_column_chain_is_accepted_open_class_89() {
    let mut env = Environment::with_prelude();
    for (name, src) in [
        (
            "dupOpt",
            "def dupOpt : Option Nat → Nat
  | some _ => 1
  | some _ => 2
  | none => 3",
        ),
        (
            "redOld",
            "def redOld : List Nat → Nat
  | [] => 0
  | x :: xs => x + redOld xs
  | _ => 7",
        ),
    ] {
        if let Err(err) = register(&mut env, src) {
            panic!(
                "open class (89): `{name}` was expected to be accepted (a divergence from \
                 Lean, which refuses it). If it is now refused as a redundant alternative, \
                 close the class: {err}"
            );
        }
    }
}
