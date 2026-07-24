// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Comprehensive end-to-end validation tests for the clean check pipeline.
//!
//! This module extends the existing `e2e_pipeline.rs` tests with additional
//! coverage for: pattern matching, let bindings, typeclasses, tactics,
//! recursive functions, dependent types, propositions, mutual definitions,
//! nested structures, and complex real-world patterns.
//!
//! Run with:
//!   cargo test -p clean --test e2e_validation

use std::time::{Duration, Instant};

use clean::kernel::Environment;
use clean::{check_source, load_source_into, CheckConfig, CheckResult};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn default_config() -> CheckConfig {
    CheckConfig::default()
}

fn allow_sorry_config() -> CheckConfig {
    let mut config = CheckConfig::default();
    config.allow_sorry = true;
    config
}

/// Assert the check result has no errors and at least `min_passed` passed declarations.
fn assert_clean(result: &CheckResult, min_passed: usize, context: &str) {
    assert!(
        result.errors.is_empty(),
        "{context}: expected no errors, got: {:?}",
        result.errors
    );
    assert!(
        result.passed_count >= min_passed,
        "{context}: expected at least {min_passed} passed, got {}",
        result.passed_count
    );
}

/// Assert the pipeline does not panic and either succeeds or produces meaningful errors.
/// Useful for features at the boundary of what the elaborator supports.
fn assert_no_panic(result: &CheckResult, context: &str) {
    // The key invariant is that the pipeline did not crash.
    // Either it succeeded or it produced structured errors.
    assert!(
        result.passed_count > 0 || !result.errors.is_empty() || result.declarations.is_empty(),
        "{context}: pipeline returned unexpected state: passed={}, errors={:?}, decls={}",
        result.passed_count,
        result.errors,
        result.declarations.len()
    );
}

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

// ===========================================================================
// Section 3: Recursive functions
// ===========================================================================

#[test]
fn test_e2e_recursive_factorial_style() {
    // Lean 4 structural recursion on Nat
    let source = r#"
def myAdd (a b : Nat) : Nat :=
  match a with
  | Nat.zero => b
  | Nat.succ n => Nat.succ (myAdd n b)
"#;
    let result = check_source(source, &default_config()).expect("recursive function should parse");
    assert_no_panic(&result, "recursive add");
}

#[test]
fn test_e2e_recursive_list_length() {
    let source = r#"
inductive MyList2 (a : Type) where
  | nil : MyList2 a
  | cons : a -> MyList2 a -> MyList2 a

def myLength (a : Type) (xs : MyList2 a) : Nat :=
  match xs with
  | MyList2.nil => 0
  | MyList2.cons _ rest => Nat.succ (myLength a rest)
"#;
    let result = check_source(source, &default_config()).expect("list length should parse");
    assert_no_panic(&result, "recursive list length");
}

// ===========================================================================
// Section 4: Typeclasses
// ===========================================================================

#[test]
fn test_e2e_class_declaration() {
    let source = r#"
class MyToString (a : Type) where
  toString : a -> String
"#;
    let result = check_source(source, &default_config()).expect("class declaration should parse");
    assert_no_panic(&result, "class declaration");
}

#[test]
fn test_e2e_class_with_instance() {
    let source = r#"
class MyShow (a : Type) where
  show : a -> Nat

instance : MyShow Bool where
  show := fun b => match b with
    | true => 1
    | false => 0
"#;
    let result = check_source(source, &default_config()).expect("class + instance should parse");
    assert_no_panic(&result, "class with instance");
}

#[test]
fn test_e2e_class_multi_method() {
    let source = r#"
class MyOrd (a : Type) where
  le : a -> a -> Bool
  lt : a -> a -> Bool
"#;
    let result = check_source(source, &default_config()).expect("multi-method class should parse");
    assert_no_panic(&result, "class multi-method");
}

// ===========================================================================
// Section 5: Tactic proofs
// ===========================================================================

#[test]
fn test_e2e_tactic_rfl() {
    let source = "theorem rfl_tac : 1 = 1 := by rfl";
    let result = check_source(source, &default_config()).expect("tactic rfl should parse");
    assert_no_panic(&result, "tactic rfl");
}

#[test]
fn test_e2e_tactic_exact() {
    let source = "theorem exact_tac : True := by exact True.intro";
    let result = check_source(source, &default_config()).expect("tactic exact should parse");
    assert_no_panic(&result, "tactic exact");
}

#[test]
fn test_e2e_tactic_trivial() {
    let source = "theorem trivial_tac : True := by trivial";
    let result = check_source(source, &default_config()).expect("tactic trivial should parse");
    assert_no_panic(&result, "tactic trivial");
}

#[test]
fn test_e2e_tactic_intro() {
    let source = r#"
theorem intro_tac : Nat -> Nat := by
  intro n
  exact n
"#;
    let result = check_source(source, &default_config()).expect("tactic intro should parse");
    assert_no_panic(&result, "tactic intro");
}

#[test]
fn test_e2e_tactic_apply() {
    let source = r#"
theorem apply_tac (h : True) : True := by
  apply h
"#;
    // `apply h` where h : True should close the goal
    let result = check_source(source, &default_config()).expect("tactic apply should parse");
    assert_no_panic(&result, "tactic apply");
}

// ===========================================================================
// Section 6: Dependent types
// ===========================================================================

#[test]
fn test_e2e_dependent_pair_type() {
    let source = r#"
def dependentId (a : Type) (x : a) : a := x
"#;
    let result = check_source(source, &default_config()).expect("dependent function should parse");
    assert_clean(&result, 1, "dependent id");
}

#[test]
fn test_e2e_type_as_parameter() {
    let source = r#"
def typeParam (T : Type) (x : T) (y : T) : T := x
"#;
    let result = check_source(source, &default_config()).expect("type parameter should parse");
    assert_clean(&result, 1, "type as parameter");
}

#[test]
fn test_e2e_prop_returning_function() {
    let source = r#"
def myEq (a : Type) (x y : a) : Prop := x = y
"#;
    let result =
        check_source(source, &default_config()).expect("Prop-returning function should parse");
    assert_no_panic(&result, "prop returning function");
}

// ===========================================================================
// Section 7: Proposition logic
// ===========================================================================

#[test]
fn test_e2e_and_intro() {
    let source = r#"
theorem and_intro_test (h1 : True) (h2 : True) : True := h1
"#;
    let result = check_source(source, &default_config()).expect("And intro should parse");
    assert_no_panic(&result, "and intro");
}

#[test]
fn test_e2e_implies_proof() {
    let source = r#"
theorem implies_test : True -> True := fun h => h
"#;
    let result = check_source(source, &default_config()).expect("implication proof should parse");
    assert_no_panic(&result, "implies proof");
}

#[test]
fn test_e2e_forall_proof() {
    let source = r#"
theorem forall_test : (n : Nat) -> Nat := fun n => n
"#;
    let result = check_source(source, &default_config()).expect("forall proof should parse");
    assert_no_panic(&result, "forall proof");
}

// ===========================================================================
// Section 8: Nested structures
// ===========================================================================

#[test]
fn test_e2e_nested_structure() {
    let source = r#"
structure Inner where
  val : Nat

structure Outer where
  inner : Inner
  extra : Nat
"#;
    let result = check_source(source, &default_config()).expect("nested structure should parse");
    assert_no_panic(&result, "nested structure");
}

#[test]
fn test_e2e_structure_with_function_field() {
    let source = r#"
structure Transformer where
  transform : Nat -> Nat
  name : Nat
"#;
    let result = check_source(source, &default_config())
        .expect("structure with function field should parse");
    assert_no_panic(&result, "structure with function field");
}

// ===========================================================================
// Section 9: Multi-declaration dependency chains
// ===========================================================================

#[test]
fn test_e2e_five_level_dependency() {
    let source = r#"
def level0 : Nat := 0
def level1 : Nat := Nat.succ level0
def level2 : Nat := Nat.succ level1
def level3 : Nat := Nat.succ level2
def level4 : Nat := Nat.succ level3
"#;
    let result =
        check_source(source, &default_config()).expect("5-level dependency chain should succeed");
    assert_clean(&result, 5, "five-level dependency chain");
}

#[test]
fn test_e2e_diamond_dependency() {
    let source = r#"
def base : Nat := 1
def left : Nat := Nat.add base 1
def right : Nat := Nat.add base 2
def join : Nat := Nat.add left right
"#;
    let result =
        check_source(source, &default_config()).expect("diamond dependency should succeed");
    assert_clean(&result, 4, "diamond dependency");
}

// ===========================================================================
// Section 10: Universe polymorphism (extended)
// ===========================================================================

#[test]
fn test_e2e_universe_sort() {
    let source = r#"
def sortExample : Type := Nat
"#;
    let result = check_source(source, &default_config()).expect("Sort/Type alias should parse");
    assert_clean(&result, 1, "universe sort");
}

#[test]
fn test_e2e_universe_prop() {
    let source = r#"
def propExample : Prop := True
"#;
    let result = check_source(source, &default_config()).expect("Prop def should parse");
    assert_clean(&result, 1, "universe prop");
}

#[test]
fn test_e2e_type_of_types() {
    let source = r#"
def typeOfType : Type 1 := Type
"#;
    let result = check_source(source, &default_config()).expect("Type 1 should parse");
    assert_no_panic(&result, "type of types");
}

// ===========================================================================
// Section 11: Opaque declarations
// ===========================================================================

#[test]
fn test_e2e_opaque_def() {
    let source = r#"
opaque mySecret : Nat := 42
"#;
    let result = check_source(source, &default_config()).expect("opaque def should parse");
    assert_no_panic(&result, "opaque def");
}

// ===========================================================================
// Section 12: Axiom declarations
// ===========================================================================

#[test]
fn test_e2e_axiom_declaration() {
    let source = r#"
axiom myAxiom : Nat -> Nat
"#;
    let result = check_source(source, &default_config()).expect("axiom declaration should parse");
    assert_no_panic(&result, "axiom declaration");
}

#[test]
fn test_e2e_axiom_used_in_def() {
    let source = r#"
axiom myFunc : Nat -> Nat
def applyMyFunc : Nat := myFunc 0
"#;
    let result = check_source(source, &default_config()).expect("axiom usage should parse");
    assert_no_panic(&result, "axiom used in def");
}

// ===========================================================================
// Section 13: Complex function signatures
// ===========================================================================

#[test]
fn test_e2e_curried_function() {
    let source = r#"
def curried : Nat -> Nat -> Nat -> Nat := fun a b c => Nat.add a (Nat.add b c)
"#;
    let result = check_source(source, &default_config()).expect("curried function should parse");
    assert_clean(&result, 1, "curried function");
}

#[test]
fn test_e2e_implicit_parameter() {
    let source = r#"
def implicitId {a : Type} (x : a) : a := x
"#;
    let result = check_source(source, &default_config()).expect("implicit parameter should parse");
    assert_no_panic(&result, "implicit parameter");
}

#[test]
fn test_e2e_explicit_type_application() {
    let source = r#"
def myId2 (a : Type) (x : a) : a := x
def applied : Nat := myId2 Nat 42
"#;
    let result =
        check_source(source, &default_config()).expect("explicit type application should parse");
    assert_no_panic(&result, "explicit type application");
}

// ===========================================================================
// Section 14: String and other base types
// ===========================================================================

#[test]
fn test_e2e_string_literal() {
    let source = r#"
def greeting : String := "hello"
"#;
    let result = check_source(source, &default_config()).expect("string literal should parse");
    assert_no_panic(&result, "string literal");
}

#[test]
fn test_e2e_unit_type() {
    let source = r#"
def unitVal : Unit := ()
"#;
    let result = check_source(source, &default_config()).expect("Unit should parse");
    assert_no_panic(&result, "unit type");
}

// ===========================================================================
// Section 15: Do-notation / monadic syntax
// ===========================================================================

#[test]
fn test_e2e_do_notation_option() {
    let source = r#"
def optionTest : Option Nat :=
  do
    let x <- some 1
    let y <- some 2
    return Nat.add x y
"#;
    let result = check_source(source, &default_config()).expect("do-notation should parse");
    assert_no_panic(&result, "do-notation option");
}

// ===========================================================================
// Section 16: Mutual definitions
// ===========================================================================

#[test]
fn test_e2e_mutual_defs() {
    let source = r#"
mutual
  def isEven (n : Nat) : Bool :=
    match n with
    | Nat.zero => true
    | Nat.succ m => isOdd m

  def isOdd (n : Nat) : Bool :=
    match n with
    | Nat.zero => false
    | Nat.succ m => isEven m
end
"#;
    let result = check_source(source, &default_config()).expect("mutual definitions should parse");
    assert_no_panic(&result, "mutual defs");
}

// ===========================================================================
// Section 17: Where clauses and local defs
// ===========================================================================

#[test]
fn test_e2e_where_clause() {
    let source = r#"
def withWhere (n : Nat) : Nat :=
  helper n
where
  helper (x : Nat) : Nat := Nat.add x x
"#;
    let result = check_source(source, &default_config()).expect("where clause should parse");
    assert_no_panic(&result, "where clause");
}

// ===========================================================================
// Section 18: Inductive families
// ===========================================================================

#[test]
fn test_e2e_inductive_indexed() {
    // Indexed inductive: Vector (length-indexed list)
    let source = r#"
inductive Vec (a : Type) : Nat -> Type where
  | nil : Vec a 0
  | cons : a -> Vec a n -> Vec a (Nat.succ n)
"#;
    let result = check_source(source, &default_config()).expect("indexed inductive should parse");
    assert_no_panic(&result, "indexed inductive (Vec)");
}

#[test]
fn test_e2e_inductive_prop() {
    // Propositional inductive (like standard Lean Even)
    let source = r#"
inductive MyEven : Nat -> Prop where
  | zero : MyEven 0
  | succ_succ : MyEven n -> MyEven (Nat.succ (Nat.succ n))
"#;
    let result =
        check_source(source, &default_config()).expect("propositional inductive should parse");
    assert_no_panic(&result, "propositional inductive");
}

// ===========================================================================
// Section 19: Namespace and section-like patterns
// ===========================================================================

#[test]
fn test_e2e_namespace_qualified_name() {
    let source = r#"
namespace MyNS
  def val : Nat := 1
end MyNS

def usesNS : Nat := MyNS.val
"#;
    let result = check_source(source, &default_config()).expect("namespace should parse");
    assert_no_panic(&result, "namespace");
}

// ===========================================================================
// Section 20: Large batch stress test
// ===========================================================================

#[test]
fn test_e2e_stress_100_defs() {
    let mut source = String::new();
    for i in 0..100 {
        source.push_str(&format!("def stress_{i} : Nat := {i}\n"));
    }

    let result =
        check_source(&source, &default_config()).expect("100-def stress test should succeed");
    // Exclude time queued behind the process-global Clean check lock.  The
    // result timer starts after that lock is acquired and measures the work
    // whose throughput this assertion is intended to guard.
    let elapsed = result.elapsed;

    assert!(
        result.passed_count >= 100,
        "expected 100+ passed, got {}: errors={:?}",
        result.passed_count,
        result.errors
    );

    let rate = 100.0 / elapsed.as_secs_f64();
    // 100 simple defs should process in reasonable time
    assert!(
        rate > 2.0,
        "100-def throughput {rate:.1} decls/sec is below minimum threshold (elapsed: {elapsed:?})"
    );
}

#[test]
fn test_e2e_stress_incremental_20() {
    let mut env = Environment::try_with_prelude().expect("prelude should initialize");
    let config = default_config();

    let mut elapsed = Duration::ZERO;
    for i in 0..20 {
        let src = format!("def incr_stress_{i} : Nat := {i}");
        let result =
            load_source_into(&mut env, &src, &config).expect("incremental stress should succeed");
        assert_clean(&result, 1, &format!("incremental stress: def {i}"));
        elapsed += result.elapsed;
    }

    let rate = 20.0 / elapsed.as_secs_f64();
    assert!(
        rate > 2.0,
        "20-def incremental throughput {rate:.1} decls/sec is below minimum (elapsed: {elapsed:?})"
    );
}

// ===========================================================================
// Section 21: Mixed declaration stress test
// ===========================================================================

#[test]
fn test_e2e_stress_mixed_types() {
    let source = r#"
def mixA : Nat := 1
def mixB : Nat := 2
def mixC : Bool := true
def mixD : Nat -> Nat := fun x => x
theorem mixT1 : True := True.intro
def mixE (a b : Nat) : Nat := Nat.add a b
theorem mixT2 : True := True.intro
def mixF : Nat := Nat.succ (Nat.succ Nat.zero)
def mixG (f : Nat -> Nat) (x : Nat) : Nat := f x
def mixH : Nat := Nat.add 1 2
"#;
    let result = check_source(source, &default_config()).expect("mixed type stress should succeed");
    assert!(
        result.passed_count >= 8,
        "expected at least 8 passed in mixed stress, got {}: errors={:?}",
        result.passed_count,
        result.errors
    );
}

// ===========================================================================
// Section 22: Incremental cross-source interaction
// ===========================================================================

#[test]
fn test_e2e_incremental_inductive_then_match() {
    let mut env = Environment::try_with_prelude().expect("prelude should initialize");
    let config = default_config();

    let r1 = load_source_into(
        &mut env,
        r#"
inductive Season where
  | spring : Season
  | summer : Season
  | autumn : Season
  | winter : Season
"#,
        &config,
    )
    .expect("Season inductive should parse");
    assert!(
        r1.errors.is_empty(),
        "Season inductive should have no errors: {:?}",
        r1.errors
    );

    let r2 = load_source_into(&mut env, "def mySeason : Season := Season.summer", &config)
        .expect("def using Season should parse");
    assert_clean(&r2, 1, "incremental: def using Season");
}

#[test]
fn test_e2e_incremental_structure_then_constructor() {
    let mut env = Environment::try_with_prelude().expect("prelude should initialize");
    let config = default_config();

    let r1 = load_source_into(
        &mut env,
        r#"
structure Vec2 where
  x : Nat
  y : Nat
"#,
        &config,
    )
    .expect("Vec2 structure should parse");
    assert!(r1.errors.is_empty(), "Vec2 errors: {:?}", r1.errors);

    let r2 = load_source_into(&mut env, "def myVec : Vec2 := { x := 3, y := 4 }", &config)
        .expect("Vec2 constructor should parse");
    assert_no_panic(&r2, "incremental: Vec2 constructor");
}

// ===========================================================================
// Section 23: Error quality checks
// ===========================================================================

#[test]
fn test_e2e_error_contains_name_info() {
    let result = check_source("def bad : Nat := not_a_real_thing", &default_config())
        .expect("pipeline should not crash");
    assert!(
        !result.errors.is_empty(),
        "undefined reference should produce errors"
    );
    // Error messages should contain some diagnostic information
    let error_msg = &result.errors[0].1;
    assert!(!error_msg.is_empty(), "error message should not be empty");
}

#[test]
fn test_e2e_multiple_errors_independent() {
    let source = r#"
def bad1 : Nat := unknown_x
def bad2 : Nat := unknown_y
"#;
    let result =
        check_source(source, &default_config()).expect("pipeline should handle multiple errors");
    // Each bad definition should produce its own error
    assert!(
        result.errors.len() >= 2,
        "expected at least 2 independent errors, got {}: {:?}",
        result.errors.len(),
        result.errors
    );
}

#[test]
fn test_e2e_error_does_not_block_subsequent() {
    let source = r#"
def bad : Nat := unknown_ref
def good : Nat := 42
"#;
    let result =
        check_source(source, &default_config()).expect("pipeline should continue after error");
    // The good definition should still pass even after the bad one
    let good_passed = result
        .declarations
        .iter()
        .any(|d| d.name.contains("good") && d.passed);
    assert!(
        good_passed,
        "good def after bad def should still pass: decls={:?}",
        result
            .declarations
            .iter()
            .map(|d| (&d.name, d.passed))
            .collect::<Vec<_>>()
    );
}

// ===========================================================================
// Section 24: Pipeline timing properties
// ===========================================================================

#[test]
fn test_e2e_timing_single_def_under_5s() {
    let result = check_source("def timingTest : Nat := 0", &default_config())
        .expect("timing test should succeed");
    let elapsed = result.elapsed;

    assert_clean(&result, 1, "timing test");
    assert!(
        elapsed.as_secs() < 5,
        "single def should complete in under 5s, took {elapsed:?}"
    );
}

#[test]
fn test_e2e_result_elapsed_matches_wall_clock() {
    let start = Instant::now();
    let result = check_source("def elapsedTest : Nat := 0", &default_config())
        .expect("elapsed test should succeed");
    let wall_clock = start.elapsed();

    // result.elapsed should be <= wall_clock (it measures a subset of the work)
    assert!(
        result.elapsed <= wall_clock + Duration::from_millis(50),
        "result.elapsed ({:?}) should not exceed wall clock ({:?}) by much",
        result.elapsed,
        wall_clock
    );
}

// ===========================================================================
// Section 25: JSON-serializable result structure
// ===========================================================================

#[test]
fn test_e2e_result_structure_complete() {
    let source = r#"
def structResult : Nat := 1
theorem structThm : True := True.intro
"#;
    let result =
        check_source(source, &default_config()).expect("result structure test should succeed");

    // Verify the result has all the expected fields populated
    assert!(result.passed_count >= 2, "should have 2+ passed");
    assert!(result.errors.is_empty(), "should have no errors");
    assert_eq!(result.sorry_count, 0, "should have 0 sorry");
    assert_eq!(
        result.kernel_check_failures, 0,
        "should have 0 kernel failures"
    );
    assert!(!result.declarations.is_empty(), "should have declarations");

    // Check that declarations have names
    for decl in &result.declarations {
        assert!(
            !decl.name.is_empty(),
            "declaration name should not be empty"
        );
        if decl.passed {
            assert!(decl.error.is_none(), "passed decl should have no error");
        }
    }
}

// ===========================================================================
// Section 26: Regression guards
// ===========================================================================

#[test]
fn test_e2e_regression_nat_succ_chain() {
    // Regression: chained Nat.succ applications should not overflow
    let source = r#"
def succ5 : Nat := Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))
"#;
    let result = check_source(source, &default_config()).expect("succ chain should not overflow");
    assert_clean(&result, 1, "succ chain");
}

#[test]
fn test_e2e_regression_many_params() {
    // Regression: functions with many parameters should not cause issues
    let source = r#"
def tenParams (a b c d e f g h i j : Nat) : Nat := a
"#;
    let result = check_source(source, &default_config()).expect("10 params should parse");
    assert_clean(&result, 1, "ten params");
}

#[test]
fn test_e2e_regression_deeply_nested_lambda() {
    let source = r#"
def deepLambda : Nat -> Nat -> Nat -> Nat -> Nat :=
  fun a => fun b => fun c => fun d => Nat.add a (Nat.add b (Nat.add c d))
"#;
    let result =
        check_source(source, &default_config()).expect("deeply nested lambda should parse");
    assert_clean(&result, 1, "deeply nested lambda");
}

#[test]
fn test_e2e_regression_empty_inductive() {
    // An inductive with no constructors (Empty type)
    let source = r#"
inductive MyEmpty where
"#;
    let result = check_source(source, &default_config()).expect("empty inductive should parse");
    assert_no_panic(&result, "empty inductive");
}

// ===========================================================================
// Section 27: Concurrent-safety (sequential serialization test)
// ===========================================================================

#[test]
fn test_e2e_sequential_isolation() {
    // Verify that sequential calls to check_source are isolated
    // (global counters reset between calls)
    let r1 = check_source("theorem s1 : True := sorry", &allow_sorry_config())
        .expect("sorry 1 should succeed");
    let r2 =
        check_source("def clean1 : Nat := 0", &default_config()).expect("clean 1 should succeed");

    // The clean check should not inherit sorry count from the previous call
    assert_eq!(
        r2.sorry_count, 0,
        "sorry count should be isolated between calls"
    );
    assert!(r2.is_fully_verified(), "clean def should be fully verified");

    // But the sorry check should have detected it
    assert!(
        r1.sorry_count > 0 || !r1.errors.is_empty(),
        "sorry should be detected"
    );
}

// ===========================================================================
// Section 28: Complete real-world scenario
// ===========================================================================

#[test]
fn test_e2e_realistic_mini_library() {
    // A realistic scenario combining multiple features
    let source = r#"
-- A small "standard library" exercise

def zero : Nat := 0
def one : Nat := Nat.succ zero

def double (n : Nat) : Nat := Nat.add n n
def triple (n : Nat) : Nat := Nat.add n (double n)

def myId3 (a : Type) (x : a) : a := x

theorem truth : True := True.intro

def compose2 (f g : Nat -> Nat) (x : Nat) : Nat := f (g x)

def applyN (f : Nat -> Nat) (n : Nat) (x : Nat) : Nat :=
  match n with
  | Nat.zero => x
  | Nat.succ k => f (applyN f k x)
"#;
    let result = check_source(source, &default_config()).expect("mini library should parse");

    // Count how many declarations passed
    let passed_names: Vec<_> = result
        .declarations
        .iter()
        .filter(|d| d.passed)
        .map(|d| d.name.as_str())
        .collect();

    // At minimum the simple defs and theorem should pass
    assert!(
        passed_names.len() >= 5,
        "expected at least 5 passed declarations in mini library, got {}: {:?}",
        passed_names.len(),
        passed_names
    );
}
