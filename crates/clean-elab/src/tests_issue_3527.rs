// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression coverage for issue #3527.
//!
//! #3527 — "Struct-update-with-function-valued-generic-field produces
//!           UnknownFVar(FVarId(2))".
//!
//! Before the fix, this two-line program failed with
//!   TypeMismatch { expected: "valid type", actual: "UnknownFVar(FVarId(2))" }
//!
//! ```lean
//! structure S where
//!   f : Nat → Option Nat
//!
//! def upd (s : S) : S := { s with f := fun n => some n }
//! ```
//!
//! Root cause: bare `some` was not registered as a constant (only
//! `Option.some` is in the prelude, and our elaborator has no implicit
//! `export Option (some none)` step). `elab_ident` therefore fell through to
//! auto-implicit handling and bound `some` as a fresh free variable whose
//! type was inherited from the expected type (the field type
//! `Nat → Option Nat`). The auto-implicit fvar was scoped to the enclosing
//! lambda/record-update context and went out of scope by the time the
//! resulting term was re-checked, producing `UnknownFVar(FVarId(N))`.
//!
//! Fix: extend `elab_core::elab_ident` to treat the bare Lean 4 prelude
//! exports (`some`, `none`, `inl`, `inr`) as aliases for their underlying
//! inductive-type constructors, alongside the existing monad typeclass
//! aliases (`pure`, `bind`, …) introduced in the #3435 fix.

use crate::elaborate_decl_and_register;
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

fn elaborate_all(env: &mut Environment, code: &str, label: &str) {
    let decls = parse_file(code).unwrap_or_else(|e| panic!("{label}: parse failed: {e:?}"));
    for (i, decl) in decls.iter().enumerate() {
        let result = elaborate_decl_and_register(env, decl);
        assert!(
            result.is_ok(),
            "{label}: decl {i} should elaborate, got: {result:?}"
        );
    }
}

/// Exact repro from the issue body.
#[test]
fn test_issue_3527_struct_update_option_field() {
    let mut env = Environment::with_prelude();
    let code = r#"
structure S where
  f : Nat → Option Nat

def upd (s : S) : S := { s with f := fun n => some n }
"#;
    elaborate_all(&mut env, code, "#3527 exact repro");
    assert!(
        env.get_const(&Name::from_string("upd")).is_some(),
        "upd should be registered after #3527 fix"
    );
}

/// Underlying regression is in `fun n => some n` against
/// `Nat → Option Nat` — the struct-update wrapper is incidental.
#[test]
fn test_issue_3527_lambda_option_return() {
    let mut env = Environment::with_prelude();
    let code = r#"
def f : Nat → Option Nat := fun n => some n
"#;
    elaborate_all(&mut env, code, "#3527 lambda variant");
    assert!(env.get_const(&Name::from_string("f")).is_some());
}

/// Extension: other generic return types (List) exercise the same path.
#[test]
fn test_issue_3527_struct_update_list_field() {
    let mut env = Environment::with_prelude();
    let code = r#"
structure S where
  f : Nat → List Nat

def upd (s : S) : S := { s with f := fun n => [n] }
"#;
    elaborate_all(&mut env, code, "#3527 list variant");
    assert!(env.get_const(&Name::from_string("upd")).is_some());
}

/// Nested parametric return types (`Option (Option Nat)`) also routed
/// `some` through the broken auto-implicit path.
#[test]
fn test_issue_3527_struct_update_nested_option() {
    let mut env = Environment::with_prelude();
    let code = r#"
structure S where
  f : Nat → Option (Option Nat)

def upd (s : S) : S := { s with f := fun n => some (some n) }
"#;
    elaborate_all(&mut env, code, "#3527 nested option variant");
    assert!(env.get_const(&Name::from_string("upd")).is_some());
}

/// Bare `none` (the sibling prelude export) should likewise resolve to
/// `Option.none` without going through auto-implicit.
#[test]
fn test_issue_3527_bare_none_alias() {
    let mut env = Environment::with_prelude();
    let code = r#"
def optN : Option Nat := none
"#;
    elaborate_all(&mut env, code, "#3527 bare none");
    assert!(env.get_const(&Name::from_string("optN")).is_some());
}
