// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Existing local-binding and pattern-matching E2E controls.

use super::*;

// ===========================================================================
// Section 1: Let bindings
// ===========================================================================

#[test]
fn test_e2e_let_simple() {
    let source = r#"
def letSimple : Nat :=
  let x := 5
  x
"#;
    let result = check_source(source, &default_config()).expect("simple let binding should parse");
    // Let bindings may or may not be fully supported by the elaborator;
    // the key invariant is no crash and structured error reporting.
    assert_no_panic(&result, "let simple");
}

#[test]
fn test_e2e_let_chained() {
    let source = r#"
def letChained : Nat :=
  let x := 1
  let y := 2
  let z := 3
  Nat.add x (Nat.add y z)
"#;
    let result =
        check_source(source, &default_config()).expect("chained let bindings should parse");
    assert_no_panic(&result, "let chained");
}

#[test]
fn test_e2e_let_with_type_annotation() {
    let source = r#"
def letTyped : Nat :=
  let x : Nat := 42
  x
"#;
    let result = check_source(source, &default_config()).expect("typed let binding should parse");
    assert_no_panic(&result, "let typed");
}

#[test]
fn test_e2e_let_in_lambda() {
    let source = r#"
def letInLambda : Nat -> Nat := fun n =>
  let doubled := Nat.add n n
  doubled
"#;
    let result = check_source(source, &default_config()).expect("let in lambda should parse");
    assert_no_panic(&result, "let in lambda");
}

// ===========================================================================
// Section 2: Pattern matching
// ===========================================================================

#[test]
fn test_e2e_match_nat_zero_succ() {
    let source = r#"
def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ _ => false
"#;
    let result = check_source(source, &default_config()).expect("Nat match should parse");
    assert_no_panic(&result, "match nat zero/succ");
}

#[test]
fn test_e2e_match_bool() {
    let source = r#"
def boolToNat (b : Bool) : Nat :=
  match b with
  | true => 1
  | false => 0
"#;
    let result = check_source(source, &default_config()).expect("Bool match should parse");
    assert_no_panic(&result, "match bool");
}

#[test]
fn test_e2e_match_custom_inductive() {
    let source = r#"
inductive Traffic where
  | red : Traffic
  | yellow : Traffic
  | green : Traffic

def canGo (t : Traffic) : Bool :=
  match t with
  | Traffic.red => false
  | Traffic.yellow => false
  | Traffic.green => true
"#;
    let result =
        check_source(source, &default_config()).expect("custom inductive match should parse");
    assert_no_panic(&result, "match custom inductive");
}

#[test]
fn test_e2e_match_with_wildcard() {
    let source = r#"
inductive Suit where
  | hearts : Suit
  | diamonds : Suit
  | clubs : Suit
  | spades : Suit

def isRed (s : Suit) : Bool :=
  match s with
  | Suit.hearts => true
  | Suit.diamonds => true
  | _ => false
"#;
    let result = check_source(source, &default_config()).expect("wildcard match should parse");
    assert_no_panic(&result, "match wildcard");
}
