// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `deriving Inhabited` / `deriving Nonempty` on inductives (G43, G55),
//! through the production elaborate-and-register entry over the default
//! prelude. Every Lean verdict below was measured with the pinned Lean 4.8.0
//! toolchain on 2026-10-16 (oracle only); the repro files are
//! `reports/trust-ir-semantics-probe/repros/G43-*.lean` and `G55-*.lean`.

use clean_kernel::name::Name;
use clean_kernel::Environment;

use crate::{ElabError, ElabResult};

fn run_source(source: &str) -> (Environment, Vec<Result<ElabResult, ElabError>>) {
    let mut env = Environment::with_prelude();
    let mut file = crate::FileContext::new();
    let declarations = clean_parser::parse_file(source).expect("test source parses");
    let results = declarations
        .iter()
        .map(|decl| {
            let decl = crate::preprocess_decl_with_context(decl, &mut file);
            crate::elaborate_decl_and_register_with_context(&mut env, &decl, &mut file)
        })
        .collect();
    (env, results)
}

/// Every declaration elaborated with no failed leaf.
fn assert_all_pass(results: &[Result<ElabResult, ElabError>]) {
    for (index, result) in results.iter().enumerate() {
        match result {
            Ok(ElabResult::Multiple(leaves)) => {
                for leaf in leaves {
                    assert!(
                        !matches!(leaf, ElabResult::Failed { .. }),
                        "declaration {index} has a failed leaf: {leaf:?}"
                    );
                }
            }
            Ok(_) => {}
            Err(error) => panic!("declaration {index} failed: {error}"),
        }
    }
}

/// The failed-class texts of a declared type (`infer::deriving_log`).
fn failed_classes(result: &Result<ElabResult, ElabError>) -> Vec<String> {
    let Ok(ElabResult::Multiple(leaves)) = result else {
        panic!("expected the declared type plus its failed classes, got {result:?}");
    };
    let (declared, failures) = leaves.split_first().expect("the type leads the result");
    assert!(
        matches!(declared, ElabResult::Inductive { .. }),
        "the type itself is declared and passes: {declared:?}"
    );
    failures
        .iter()
        .map(|leaf| match leaf {
            ElabResult::Failed { error, .. } => error.to_string(),
            other => panic!("expected a failed deriving leaf, got {other:?}"),
        })
        .collect()
}

fn error_text(result: &Result<ElabResult, ElabError>) -> String {
    match result {
        Err(error) => error.to_string(),
        Ok(ElabResult::Multiple(leaves)) => leaves
            .iter()
            .find_map(|leaf| match leaf {
                ElabResult::Failed { error, .. } => Some(error.to_string()),
                _ => None,
            })
            .unwrap_or_else(|| panic!("expected a refusal, got {result:?}")),
        Ok(other) => panic!("expected a refusal, got {other:?}"),
    }
}

/// G43: the first constructor whose fields are all inhabited, as Lean.
#[test]
fn test_derive_inhabited_first_inhabitable_constructor_is_leans_default() {
    let source = "inductive DecodeError where\n\
                  | unsupported (feature : String)\n\
                  | malformed (msg : String)\n\
                  deriving Inhabited\n\
                  theorem d1 : (default : DecodeError) = .unsupported \"\" := rfl\n\
                  inductive Tree where\n\
                  | node (l : Tree) (r : Tree)\n\
                  | leaf (n : Nat)\n\
                  deriving Inhabited\n\
                  theorem d2 : (default : Tree) = .leaf 0 := rfl\n\
                  inductive Box (α : Type) where\n\
                  | mk (x : α) (n : Nat)\n\
                  deriving Inhabited\n\
                  theorem d3 : (default : Box Bool) = .mk false 0 := rfl\n";
    let (_env, results) = run_source(source);
    assert_all_pass(&results);
}

/// G43 twin: Lean refuses `default = .malformed ""` (`type mismatch`).
#[test]
fn test_derive_inhabited_is_not_a_later_constructor() {
    let source = "inductive DecodeError where\n\
                  | unsupported (feature : String)\n\
                  | malformed (msg : String)\n\
                  deriving Inhabited\n\
                  theorem bad : (default : DecodeError) = .malformed \"\" := rfl\n";
    let (_env, results) = run_source(source);
    assert!(
        results[0].is_ok(),
        "the inductive and its instance: {:?}",
        results[0]
    );
    assert!(
        results[1].is_err(),
        "Lean 4.8.0 refuses `default = .malformed \"\"` by rfl, got {:?}",
        results[1]
    );
}

/// A parameter hypothesis is added only when a field needs it: Lean accepts
/// `Inhabited (Box2 Empty)` (no `[Inhabited α]`) and refuses
/// `Inhabited (Box3 Empty)` (`failed to synthesize instance`).
#[test]
fn test_derive_inhabited_parameter_hypothesis_only_when_used() {
    let ok = "inductive Box2 (α : Type) where\n\
              | mk (n : Nat)\n\
              deriving Inhabited\n\
              def b2 : Box2 Empty := default\n";
    let (_env, results) = run_source(ok);
    assert_all_pass(&results);

    let refused = "inductive Box3 (α : Type) where\n\
                   | mk (x : α)\n\
                   deriving Inhabited\n\
                   def b3 : Box3 Empty := default\n";
    let (_env, results) = run_source(refused);
    assert!(results[0].is_ok(), "Box3 derives: {:?}", results[0]);
    let text = error_text(&results[1]);
    assert!(
        text.contains("Inhabited"),
        "Lean refuses `Inhabited (Box3 Empty)`, got {text}"
    );
}

/// No constructor can be built: Lean's message, and the type stays declared.
#[test]
fn test_derive_inhabited_without_inhabitable_constructor_is_refused() {
    let source = "inductive Never where\n\
                  | loop (n : Never)\n\
                  deriving Inhabited\n\
                  def useNever (n : Never) : Never := n\n";
    let (env, results) = run_source(source);
    let failures = failed_classes(&results[0]);
    assert_eq!(
        failures,
        vec!["failed to generate 'Inhabited' instance for 'Never'".to_string()]
    );
    assert!(env.get_const(&Name::from_string("Never")).is_some());
    assert!(
        results[1].is_ok(),
        "`Never` stays declared: {:?}",
        results[1]
    );
}

/// G55: `deriving Nonempty` builds a well-typed instance (with fields too),
/// and the inductive is declared.
#[test]
fn test_derive_nonempty_constructor_with_fields() {
    let source = "inductive Color where\n\
                  | red | green\n\
                  deriving Nonempty\n\
                  inductive Payload where\n\
                  | text (s : String)\n\
                  | num (n : Nat)\n\
                  deriving Nonempty\n\
                  def colorName : Color → String\n\
                  | .red => \"red\"\n\
                  | .green => \"green\"\n\
                  example : Nonempty Payload := inferInstance\n\
                  example : Nonempty Color := inferInstance\n";
    let (_env, results) = run_source(source);
    assert_all_pass(&results);
}

/// G55 hypotheses: Lean keeps `[Nonempty α]` only where a field uses it
/// (`Nonempty (W2 Empty)` accepted, `Nonempty (W Empty)` refused).
#[test]
fn test_derive_nonempty_parameter_hypothesis_only_when_used() {
    let ok = "inductive W2 (α : Type) where\n\
              | mk (n : Nat)\n\
              deriving Nonempty\n\
              example : Nonempty (W2 Empty) := inferInstance\n";
    let (_env, results) = run_source(ok);
    assert_all_pass(&results);

    let refused = "inductive W (α : Type) where\n\
                   | mk (x : α)\n\
                   deriving Nonempty\n\
                   example : Nonempty (W Nat) := inferInstance\n\
                   example : Nonempty (W Empty) := inferInstance\n";
    let (_env, results) = run_source(refused);
    assert!(results[0].is_ok(), "W derives: {:?}", results[0]);
    assert!(results[1].is_ok(), "Nonempty (W Nat): {:?}", results[1]);
    assert!(
        error_text(&results[2]).contains("Nonempty"),
        "Lean refuses `Nonempty (W Empty)`, got {:?}",
        results[2]
    );
}

/// G55 twin: no constructor can be built; Lean refuses ("failed to
/// synthesize instance Nonempty Never") and the type stays declared.
#[test]
fn test_derive_nonempty_without_buildable_constructor_is_refused() {
    let source = "inductive Never where\n\
                  | loop (n : Never)\n\
                  deriving Nonempty\n\
                  def useNever (n : Never) : Never := n\n";
    let (env, results) = run_source(source);
    let failures = failed_classes(&results[0]);
    assert_eq!(failures.len(), 1, "{failures:?}");
    assert!(
        failures[0].contains("failed to synthesize instance Nonempty"),
        "{failures:?}"
    );
    assert!(env.get_const(&Name::from_string("Never")).is_some());
    assert!(
        results[1].is_ok(),
        "`Never` stays declared: {:?}",
        results[1]
    );
}

/// G55, the structure face: a field-less structure's `Nonempty` instance is
/// well-typed and the structure stays declared (it was un-declared by the
/// kernel's refusal of `Nonempty.intro E.mk` without its type argument).
#[test]
fn test_derive_nonempty_fieldless_structure_stays_declared() {
    let source = "structure E where\n\
                  deriving Nonempty\n\
                  def useE (e : E) : E := e\n\
                  example : Nonempty E := inferInstance\n";
    let (_env, results) = run_source(source);
    assert_all_pass(&results);
}

/// KNOWN GAP G73 (ledger (143)), pinned so it fails the day it closes: the
/// structure handlers are not Lean's. Lean 4.8.0 derives `Nonempty` for a
/// structure with fields (`structure S where n : Nat`) and `Inhabited (P
/// Empty)` for `structure P (α : Type) where x : Nat` (no `[Inhabited α]`);
/// Clean refuses both. Both are refusals, never acceptances.
#[test]
fn test_structure_witness_handlers_known_gap_g73() {
    let (env, results) = run_source("structure S where\n  n : Nat\n  deriving Nonempty\n");
    let failures = failed_classes_structure(&results[0]);
    assert!(
        failures
            .iter()
            .any(|f| f.contains("requires a closed nullary constructor")),
        "G73 closed? update the ledger and this pin: {failures:?}"
    );
    assert!(env.get_const(&Name::from_string("S")).is_some());

    let (_env, results) = run_source(
        "structure P (α : Type) where\n  x : Nat\n  deriving Inhabited\n\
         def p : P Empty := default\n",
    );
    assert!(results[0].is_ok(), "P derives: {:?}", results[0]);
    assert!(
        error_text(&results[1]).contains("Inhabited"),
        "G73 closed? update the ledger and this pin: {:?}",
        results[1]
    );
}

fn failed_classes_structure(result: &Result<ElabResult, ElabError>) -> Vec<String> {
    let Ok(ElabResult::Multiple(leaves)) = result else {
        panic!("expected the declared structure plus its failed classes, got {result:?}");
    };
    leaves
        .iter()
        .filter_map(|leaf| match leaf {
            ElabResult::Failed { error, .. } => Some(error.to_string()),
            _ => None,
        })
        .collect()
}

/// KNOWN GAP G74 (ledger (144)), pinned so it fails the day it closes:
/// pinned Lean 4.8.0 answers `Inhabited Prop` with `instInhabitedProp`
/// (`⟨True⟩`), which the builtin prelude lacks, and Clean's instance search
/// answers it with `instInhabitedBool` because the elaborator's unifier
/// equates `Bool` and `Prop`; the kernel refuses the term (fail-closed).
#[test]
fn test_inhabited_prop_known_gap_g74() {
    let (_env, results) = run_source("example : Inhabited Prop := inferInstance\n");
    let text = error_text(&results[0]);
    assert!(
        text.contains("Inhabited Bool"),
        "G74 closed or changed? update the ledger and this pin: {text}"
    );
}
