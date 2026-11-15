// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A failing `deriving` class leaves its type declared and passing, with the
//! class reported beside it as its own failed leaf (`infer::deriving_log`),
//! through the production elaborate-and-register entry over the default
//! prelude. Every Lean claim below was measured against the pinned Lean 4.8.0
//! toolchain (2026-09-30), used as an oracle only.
//!
//! The trust-ir shape: `structure FieldDef … deriving BEq, Repr` failed to
//! derive, so `StructDef`'s `fields : List FieldDef` auto-bound the bare name
//! and failed with `Unknown free variable: FVarId(2)` (G02 / G17).

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

/// The failed classes of a declared type, as the text of each one's failed
/// leaf. The declaration itself is accepted: its first leaf is the type, and
/// every later leaf is a [`ElabError::DerivingHandlerFailed`] — the error is
/// about the clause, never about the type.
fn failed_classes(result: &Result<ElabResult, ElabError>) -> Vec<String> {
    let Ok(ElabResult::Multiple(leaves)) = result else {
        panic!("expected the declared type plus its failed classes, got {result:?}");
    };
    let (declared, failures) = leaves.split_first().expect("the type leads the result");
    assert!(
        matches!(
            declared,
            ElabResult::Structure { .. } | ElabResult::Inductive { .. }
        ),
        "the type itself is declared and passes: {declared:?}"
    );
    assert!(!failures.is_empty(), "a failed class is reported");
    failures
        .iter()
        .map(|leaf| match leaf {
            ElabResult::Failed { error, .. } => {
                assert!(
                    matches!(**error, ElabError::DerivingHandlerFailed { .. }),
                    "expected a deriving failure, got {error:?}"
                );
                error.to_string()
            }
            other => panic!("expected a failed deriving leaf, got {other:?}"),
        })
        .collect()
}

fn declared(env: &Environment, name: &str) -> bool {
    env.get_const(&Name::from_string(name)).is_some()
}

fn derived_instance(env: &Environment, type_name: &str, class: &'static str) -> bool {
    let instance = crate::derive::builtin_instance_name(&Name::from_string(type_name), class);
    env.get_const(&instance).is_some()
}

#[test]
fn test_derive_failure_structure_stays_declared_and_clause_fails() {
    // Lean 4.8: `failed to synthesize instance Repr (Nat → Nat)` at the
    // clause, and `useW` elaborates — `W` is declared.
    let source = "structure W where\n  f : Nat → Nat\n  deriving Repr\n\
                  def useW (w : W) : Nat := w.f 0\n";
    let (env, results) = run_source(source);
    assert_eq!(results.len(), 2);
    let failed = failed_classes(&results[0]);
    assert_eq!(failed.len(), 1, "{failed:?}");
    assert!(
        failed[0].contains("cannot synthesize Repr for field `f`"),
        "{failed:?}"
    );
    for name in ["W", "W.mk", "W.f"] {
        assert!(declared(&env, name), "`{name}` must be declared");
    }
    assert!(
        !derived_instance(&env, "W", "Repr"),
        "the failed instance must not register"
    );
    assert!(results[1].is_ok(), "{:?}", results[1]);
    assert!(declared(&env, "useW"));
}

#[test]
fn test_derive_failure_inductive_stays_declared_and_clause_fails() {
    // Lean 4.8: `failed to synthesize instance BEq (Nat → Nat)`, and `useT`
    // elaborates.
    let source = "inductive T where\n  | mk (f : Nat → Nat)\n  | z\n  deriving BEq\n\
                  def useT : T := T.z\n";
    let (env, results) = run_source(source);
    assert_eq!(results.len(), 2);
    let failed = failed_classes(&results[0]);
    assert_eq!(failed.len(), 1, "{failed:?}");
    assert!(
        failed[0].contains("BEq"),
        "Lean refuses `deriving BEq` here: {failed:?}"
    );
    for name in ["T", "T.mk", "T.z", "T.rec"] {
        assert!(declared(&env, name), "`{name}` must be declared");
    }
    assert!(!derived_instance(&env, "T", "BEq"));
    assert!(results[1].is_ok(), "{:?}", results[1]);
}

#[test]
fn test_derive_failure_keeps_earlier_instances_and_skips_later_classes() {
    // Lean 4.8: `default handlers have not been implemented yet, class: 'Add'`
    // — a THROWN handler failure: `Repr X` (derived before it) exists, so `rx`
    // elaborates, and nothing after it is derived, so `beqX` is refused
    // (`failed to synthesize instance BEq X`).
    let source = "structure X where\n  n : Nat\n  deriving Repr, Add, BEq\n\
                  def rx (x : X) := repr x\n\
                  def beqX (x : X) : Bool := x == x\n";
    let (env, results) = run_source(source);
    assert_eq!(results.len(), 3);
    // One failed leaf: `Add` threw, so `BEq` never ran (and never failed).
    let failed = failed_classes(&results[0]);
    assert_eq!(failed.len(), 1, "{failed:?}");
    assert!(
        failed[0].contains("no available derive handler for class `Add`"),
        "{failed:?}"
    );
    assert!(declared(&env, "X"));
    assert!(derived_instance(&env, "X", "Repr"));
    assert!(!derived_instance(&env, "X", "BEq"));
    assert!(results[1].is_ok(), "{:?}", results[1]);
    assert!(results[2].is_err(), "Lean refuses `x == x`: no `BEq X`");
    assert!(!declared(&env, "beqX"));
}

#[test]
fn test_derive_unknown_class_refuses_the_declaration() {
    // Lean 4.8 resolves the classes BEFORE it declares the type: `unknown
    // constant 'NoSuchClass'`, and `useBad` fails because `Bad` does not
    // exist (`invalid field notation`).
    let source = "structure Bad where\n  x : Nat\n  deriving NoSuchClass\n\
                  def useBad (b : Bad) : Nat := b.x\n";
    let (env, results) = run_source(source);
    assert_eq!(results.len(), 2);
    let error = results[0]
        .as_ref()
        .expect_err("an unknown class refuses the whole declaration");
    let text = error.to_string();
    assert!(
        text.contains("no available derive handler for unresolved class `NoSuchClass`"),
        "{text}"
    );
    assert!(
        !matches!(error, ElabError::DerivingHandlerFailed { .. }),
        "an unknown class is resolved before the type is declared: {error:?}"
    );
    assert!(!declared(&env, "Bad"), "an unknown class declares nothing");
    assert!(results[1].is_err(), "Lean refuses `useBad`");
    assert!(!declared(&env, "useBad"));
}

#[test]
fn test_derive_known_class_twin_of_unknown_class_declares_and_passes() {
    // The positive twin of the unknown-class refusal: the same structure with
    // a class that resolves and derives declares `Good` and its instance, and
    // the same use elaborates (Lean 4.8 accepts both).
    let source = "structure Good where
  x : Nat
  deriving Repr
                  def useGood (b : Good) : Nat := b.x
";
    let (env, results) = run_source(source);
    assert_eq!(results.len(), 2);
    for (index, result) in results.iter().enumerate() {
        assert!(result.is_ok(), "declaration {index}: {result:?}");
    }
    assert!(declared(&env, "Good"));
    assert!(derived_instance(&env, "Good", "Repr"));
    assert!(declared(&env, "useGood"));
}

#[test]
fn test_derive_failure_field_type_no_longer_cascades() {
    // The 2026-09-30 census shape: the type a failed clause decorates is
    // still a type for every later declaration (Lean 4.8 accepts all three
    // later declarations; only the clause is an error). trust-ir's
    // `TrustIrEval/Decode.lean` `DecodeError … deriving Repr, Inhabited` /
    // `abbrev D := Except DecodeError` has the same dependency.
    let source = "structure FieldDef where\n  name : String\n  f : Nat → Nat\n  deriving Repr\n\
                  structure StructDef where\n  fields : List FieldDef\n\
                  def count (s : StructDef) : Nat := s.fields.length\n\
                  def wrap (x : FieldDef) : Except String FieldDef := Except.ok x\n";
    let (env, results) = run_source(source);
    assert_eq!(results.len(), 4);
    let failed = failed_classes(&results[0]);
    assert!(
        failed
            .iter()
            .any(|text| text.contains("cannot synthesize Repr for field `f`")),
        "the clause itself fails: {failed:?}"
    );
    for (index, result) in results.iter().enumerate().skip(1) {
        assert!(result.is_ok(), "declaration {index} cascaded: {result:?}");
    }
    for name in ["FieldDef", "StructDef", "count", "wrap"] {
        assert!(declared(&env, name), "`{name}` must be declared");
    }
}
