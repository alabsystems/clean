// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression coverage for issue #3435.
//!
//! #3435 — "Struct field access after do-notation bind produces type mismatch."
//!
//! Before the fix, the exact repro in the issue body failed with:
//!   TypeMismatch { expected: "MState", actual: "const mismatch: Nat vs MState" }
//!
//! Root cause (confirmed via diagnostic trace 2026-04-18):
//!   - The do-block's bind was wiring the continuation's binder `s` to `MState`
//!     correctly; `try_extract_bind_inner_type` returned `MState` as intended.
//!   - The crash surfaced when elaborating `pure s.counter`. The identifier
//!     `pure` was not registered as a constant (only `Pure.pure` is in the
//!     prelude, and nothing `open`s the `Pure` namespace), so `elab_ident`
//!     fell through to the auto-implicit handler. The auto-implicit was
//!     given `current_expected_type` as its type — which was the monadic
//!     `Sem Nat` (WHNF: `MState → Except SemError (Prod Nat MState)`). That
//!     free variable, applied to `s.counter`, demanded an `MState` argument
//!     but received `Nat` — hence the reported "expected MState, actual Nat"
//!     mismatch.
//!
//! Fix (two guards, either of which is sufficient):
//!   1. `elab_app` intercepts `pure <arg>` whenever we are inside a do-block
//!      (`do_monad_info.is_some()`) and routes it through `mk_pure_app`,
//!      reusing the do-block's cached `(u, v, m)` so universes and the
//!      monad metavariable stay concrete.
//!   2. `elab_ident` treats `pure`/`bind`/`map`/`seq`/`seqLeft`/`seqRight`
//!      as aliases for their typeclass constants (`Pure.pure`, …) when
//!      the bare identifier is not otherwise resolved, matching Lean 4's
//!      implicit `open Pure`/`open Bind` semantics.

use crate::elaborate_decl_and_register;
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

/// Regression test for #3435: struct field access on a do-notation bind result.
#[test]
fn test_issue_3435_struct_field_access_after_do_bind() {
    let mut env = Environment::with_prelude();
    let code = r#"
inductive SemError where
  | ub : SemError

structure MState where
  counter : Nat
  values : List Nat

abbrev Sem (a : Type) := StateT MState (Except SemError) a

def getCounter : Sem Nat := do
  let s <- StateT.get
  pure s.counter
"#;
    let decls = parse_file(code).expect("should parse #3435 repro");
    for (i, decl) in decls.iter().enumerate() {
        let result = elaborate_decl_and_register(&mut env, decl);
        assert!(
            result.is_ok(),
            "#3435 regression: decl {} should elaborate, got: {:?}",
            i,
            result
        );
    }

    let info = env.get_const(&Name::from_string("getCounter"));
    assert!(
        info.is_some(),
        "getCounter should be registered (#3435 regression)"
    );
}

/// Minor variant: multi-field struct, multiple field accesses.
#[test]
fn test_issue_3435_multi_field_access_after_do_bind() {
    let mut env = Environment::with_prelude();
    let code = r#"
inductive SemError where
  | ub : SemError

structure MState where
  counter : Nat
  values : List Nat

abbrev Sem (a : Type) := StateT MState (Except SemError) a

def peekValues : Sem (List Nat) := do
  let s <- StateT.get
  pure s.values
"#;
    let decls = parse_file(code).expect("should parse #3435 multi-field repro");
    for (i, decl) in decls.iter().enumerate() {
        let result = elaborate_decl_and_register(&mut env, decl);
        assert!(
            result.is_ok(),
            "#3435 multi-field regression: decl {} should elaborate, got: {:?}",
            i,
            result
        );
    }

    assert!(
        env.get_const(&Name::from_string("peekValues")).is_some(),
        "peekValues should be registered"
    );
}
