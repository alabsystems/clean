// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression coverage for issue #3517.
//!
//! #3517 — "[tMIR] Record-update elaborator loses struct type after monadic bind"
//!
//! Minimal repro (from tMIR case study):
//!
//! ```lean
//! inductive SemError where
//!   | ub : SemError
//!
//! structure Counter where
//!   value : Nat
//!
//! abbrev Sem (a : Type) := StateT Counter (Except SemError) a
//!
//! def addValue (n : Nat) : Sem Unit := do
//!   let c <- StateT.get
//!   StateT.set { c with value := c.value + n }
//! ```
//!
//! Two independent bugs combined to break the repro:
//!
//! 1. **Parser — struct-literal field values.** `struct_field_value_expr`
//!    parsed field values via `struct_field_arrow_expr` / `struct_field_app_expr`,
//!    which only supported application + arrow — no binary operators.
//!    `{ c with value := c.value + 1 }` therefore broke at `+`, the outer
//!    `def` fell into the parser's `skip-to-next-decl` recovery branch, and
//!    the whole declaration was silently turned into `SurfaceDecl::RawDecl`.
//!    The elaborator then returned `Ok(Skipped)` and the decl simply never
//!    landed in the environment. Fix: route field values through the full
//!    `self.expr()` with a new `in_struct_field` flag so `app_expr` stops at
//!    the next `ident :=` field boundary (preserves the comma-less
//!    `{ x := 1 y := 2 }` form).
//!
//! 2. **Elaborator — terminal do-action expected type.** `elab_do_elems`
//!    elaborated a terminal `[DoElem::Expr]` via bare `self.elaborate(expr)`
//!    rather than `elaborate_with_expected_type`. The outer `current_expected_type`
//!    (e.g. `Sem Unit`) therefore never drove unification of fresh implicit
//!    arguments introduced by the action (e.g. `StateT.set`'s monad
//!    parameter `{m : Type _ → Type _}`). The unresolved `?m` was then
//!    encoded as an FVar (via `MetaState::to_fvar`) and leaked into the
//!    kernel term, producing `Declaration <name> contains free variables`.
//!    `pure <arg>` was already immune because of the `try_short_circuit_do_pure`
//!    path from #3435. Fix: elaborate terminal do-actions with the current
//!    expected type so the final unification fires.

use crate::elaborate_decl_and_register;
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

fn elab_all_and_assert_ok(code: &str, expected_name: &str) -> Environment {
    let mut env = Environment::with_prelude();
    let decls = parse_file(code).expect("should parse");
    let mut outcomes: Vec<String> = Vec::new();
    for (i, decl) in decls.iter().enumerate() {
        // Guard against the parser's "skip-to-next-decl" recovery turning a
        // malformed `def` into SurfaceDecl::RawDecl — the elaborator then
        // returns Ok(Skipped) and the missing declaration is silently dropped.
        if let clean_parser::SurfaceDecl::RawDecl { content, span } = decl {
            panic!(
                "decl {i} fell through to RawDecl (parser error recovery); \
                 content={content:?}, span={span:?}"
            );
        }
        match elaborate_decl_and_register(&mut env, decl) {
            Ok(r) => outcomes.push(format!("decl {i}: OK = {}", summarize_result(&r))),
            Err(e) => outcomes.push(format!("decl {i}: ERR = {e:?}")),
        }
    }
    let any_err = outcomes.iter().any(|o| o.contains("ERR"));
    assert!(
        !any_err,
        "#3517 regression: elaboration errors: {outcomes:#?}"
    );
    assert!(
        env.get_const(&Name::from_string(expected_name)).is_some(),
        "{expected_name} should be registered (outcomes: {outcomes:#?})"
    );
    env
}

fn summarize_result(r: &crate::ElabResult) -> String {
    match r {
        crate::ElabResult::Definition { name, .. } => format!("Definition({name})"),
        crate::ElabResult::Theorem { name, .. } => format!("Theorem({name})"),
        crate::ElabResult::Axiom { name, .. } => format!("Axiom({name})"),
        crate::ElabResult::Inductive { name, .. } => format!("Inductive({name})"),
        crate::ElabResult::Structure { name, .. } => format!("Structure({name})"),
        crate::ElabResult::Skipped => "Skipped".to_string(),
        other => format!("{:?}", std::mem::discriminant(other)),
    }
}

/// Regression test for #3517: record-update after do-notation bind.
#[test]
fn test_issue_3517_record_update_after_do_bind() {
    let code = r#"
inductive SemError where
  | ub : SemError

structure Counter where
  value : Nat

abbrev Sem (a : Type) := StateT Counter (Except SemError) a

def addValue (n : Nat) : Sem Unit := do
  let c <- StateT.get
  StateT.set { c with value := c.value + n }
"#;
    elab_all_and_assert_ok(code, "addValue");
}

/// Narrow repro: record-update on a FVar-bound variable (no do-block).
/// Simulates the do-bind continuation's body by binding `c` via a lambda.
#[test]
fn test_issue_3517_record_update_on_lambda_bound_var() {
    let code = r#"
structure Counter where
  value : Nat

def bumpLam : Counter -> Nat -> Counter :=
  fun c n => { c with value := c.value + n }
"#;
    elab_all_and_assert_ok(code, "bumpLam");
}

/// Do-block with record-update but no outer parameter — isolates whether the
/// leaking FVar comes from the do-bind binder or from a def-level binder.
#[test]
fn test_issue_3517_record_update_after_do_bind_no_outer_param() {
    let code = r#"
inductive SemError where
  | ub : SemError

structure Counter where
  value : Nat

abbrev Sem (a : Type) := StateT Counter (Except SemError) a

def bumpOnce : Sem Unit := do
  let c <- StateT.get
  StateT.set { c with value := c.value + 1 }
"#;
    elab_all_and_assert_ok(code, "bumpOnce");
}

/// Isolation: `do let c <- StateT.get; StateT.set c` — same do-bind shape
/// but no struct-update. Verifies whether the FVar leak depends on
/// struct-literal elaboration or is already present for any do-bind
/// continuation with a non-pure final action.
#[test]
fn test_issue_3517_do_bind_set_identity() {
    let code = r#"
inductive SemError where
  | ub : SemError

structure Counter where
  value : Nat

abbrev Sem (a : Type) := StateT Counter (Except SemError) a

def setSame : Sem Unit := do
  let c <- StateT.get
  StateT.set c
"#;
    elab_all_and_assert_ok(code, "setSame");
}

/// Variant: multi-field structure with record-update on one field.
#[test]
fn test_issue_3517_multi_field_record_update_after_do_bind() {
    let code = r#"
inductive SemError where
  | ub : SemError

structure MState where
  counter : Nat
  tag : Nat

abbrev Sem (a : Type) := StateT MState (Except SemError) a

def bumpCounter : Sem Unit := do
  let s <- StateT.get
  StateT.set { s with counter := s.counter + 1 }
"#;
    elab_all_and_assert_ok(code, "bumpCounter");
}

/// Isolation: make sure a record update without do-notation still parses.
/// Failing this test would implicate the struct-literal elaborator itself;
/// a pass here while the primary test fails pinpoints the issue to the
/// do-block interaction.
#[test]
fn test_issue_3517_record_update_outside_do_block_parses_and_elaborates() {
    let code = r#"
structure Counter where
  value : Nat

def bump (c : Counter) : Counter := { c with value := c.value + 1 }
"#;
    elab_all_and_assert_ok(code, "bump");
}
