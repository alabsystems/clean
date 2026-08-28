// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic-mode `let ⟨a, b⟩ := e`.
//!
//! `parse_tactic_let` opened with `expect_ident("let")`, so `⟨` was rejected
//! outright and the declaration fell into parser recovery. Measured before the
//! fix on the release binary, `clean check --prelude builtin`:
//!
//! ```text
//! ✗ parser recovery: unsupported tactic `let` … expected identifier in let,
//!   got LAngle
//! ✗ parser recovery: unsupported tactic `classical` … `classical` > `let`:
//!   … got LAngle          ← recovery names the PRECEDING tactic
//! ✗ elaboration error: ParseError("parser recovery produced raw declaration:
//!   Comma  b   p ")
//! ```
//!
//! The parser fix routes the destructuring form through `obtain`, mirroring
//! `parse_tactic_have`. These tests are the ELABORATION half: they check that
//! the desugaring actually produces usable bindings, in particular the
//! defeq-sensitive case the queue's caveat calls for — Lean's `let` pattern
//! introduces let-bound definitions where `obtain` introduces opaque
//! hypotheses, so a goal that must close by `rfl` THROUGH the bound components
//! is the case where the two routes could differ.

use clean_kernel::Environment;
use clean_parser::parse_file;

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};

fn elab_all(code: &str) -> Vec<Result<ElabResult, crate::ElabError>> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(code).expect("parse_file should succeed");
    decls
        .iter()
        .map(|decl| {
            let processed = preprocess_decl_with_context(decl, &mut file_ctx);
            elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
        })
        .collect()
}

#[track_caller]
fn assert_all_ok(code: &str, what: &str) {
    let results = elab_all(code);
    assert!(!results.is_empty(), "{what}: nothing parsed");
    for result in &results {
        assert!(
            result.is_ok(),
            "{what}: expected a kernel-registered declaration, got {result:?}"
        );
    }
}

/// The reported shape: a bare tactic-mode `let ⟨a, b⟩ := p`.
#[test]
fn test_tactic_let_pattern_elaborates() {
    assert_all_ok(
        "theorem taclet (p : Nat × Nat) : p.1 + p.2 = p.1 + p.2 := by\n  \
         let ⟨a, b⟩ := p\n  rfl\n",
        "tactic-mode let ⟨a, b⟩",
    );
}

/// The defeq-sensitive case. `show a + b = a + b` only type-checks against the
/// goal `p.1 + p.2 = p.1 + p.2` if the destructuring made the components
/// definitionally reachable — with `obtain`'s route, `p` is replaced by
/// `⟨a, b⟩` so `p.1` iota-reduces to `a`. This is the row that would expose a
/// divergence from Lean's let-binding (zeta) route if there were one.
#[test]
fn test_tactic_let_pattern_components_are_definitionally_usable() {
    assert_all_ok(
        "theorem tacletDefEq (p : Nat × Nat) : p.1 + p.2 = p.1 + p.2 := by\n  \
         let ⟨a, b⟩ := p\n  show a + b = a + b\n  rfl\n",
        "defeq-sensitive tactic-mode let ⟨a, b⟩",
    );
}

/// The `Mathlib/Logic/Basic:508` shape — a preceding tactic, which is why the
/// source-elab report MISLABELS these rows as `classical`/`ext` failures:
/// recovery names the tactic before the one that actually failed.
#[test]
fn test_tactic_let_pattern_after_another_tactic() {
    assert_all_ok(
        "theorem tacletAfter (p : Nat × Nat) : p.1 + p.2 = p.1 + p.2 := by\n  \
         classical\n  let ⟨a, b⟩ := p\n  rfl\n",
        "tactic-mode let ⟨a, b⟩ after `classical`",
    );
}

/// Control 1: the TERM-level form already worked by a different route
/// (`is_let_pattern_start` / `let_tuple_body`), which is what proved the gap
/// was one parser function rather than the pattern engine. It must stay green.
#[test]
fn test_term_level_let_pattern_control() {
    assert_all_ok(
        "def tletTerm (p : Nat × Nat) : Nat := let ⟨a, b⟩ := p; a + b\n",
        "term-level let ⟨a, b⟩ control",
    );
}

/// Control 2: the NAMED tactic-mode `let` must be untouched.
#[test]
fn test_named_tactic_let_control() {
    assert_all_ok(
        "theorem tacletNamed (p : Nat × Nat) : p.1 + p.2 = p.1 + p.2 := by\n  \
         let x := p\n  rfl\n",
        "named tactic-mode let control",
    );
}
