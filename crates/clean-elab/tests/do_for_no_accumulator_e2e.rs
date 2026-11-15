// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end pins for the NO-ACCUMULATOR `for` loop: `for x in xs do <body>`
//! inside a `do` block that has no `let mut`, no `break`/`continue` and no
//! early `return`.
//!
//! That shape is the ONLY one routed to the monadic lane
//! (`ElabCtx::elab_do_for` / `elab_do_for_compound`). `elab_do_inner` turns
//! `do_pure_state` on exactly when the block needs a control stack —
//! reassignment, `break`/`continue`, or an early `return` — so every other
//! `for` goes to the pure state-threading lane (`elab_do_pure_for`). The
//! accumulator control at the bottom of this file pins that split: it must
//! keep passing whatever happens to the monadic lane.
//!
//! Measured before the fix (2026-09-16, `target/debug/clean check`): every
//! `for` in this file that carries no accumulator failed with
//! `def f: elaboration left unresolved variables (unsolved metavariables ?[4])`
//! — `ForIn.forIn`'s telescope carries a `[Monad m]` binder that the hand-built
//! application never supplied, so the application's type came back as a
//! leftover `Pi` and `mk_bind_app` substituted an unassignable metavariable for
//! the bind's `α`. See the comment at the lowering site in
//! `crates/clean-elab/src/infer/elab_do_for.rs`.
//!
//! These tests drive the SAME pipeline as `clean check`
//! (`parse_file → preprocess_decl_with_context → elaborate_decl_and_register`),
//! and `elaborate_decl_and_register` registers into the `Environment`, so a
//! pass here is a kernel acceptance and not just an elaboration.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_parser::parse_file;

fn elaborate_file(source: &str) -> Result<Vec<ElabResult>, String> {
    let mut env = Environment::with_prelude();
    // The `clean check` path registers the IO operation axioms on top of the
    // prelude (`crates/clean-cli/src/cmd_core.rs:141`); without them
    // `IO.println` is an unknown identifier and an `IO` test here would measure
    // THAT instead of the loop.
    env.init_io_ops()
        .expect("IO operation axioms must register on a prelude environment");
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    let mut results = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        results.push(elaborate_decl_and_register(&mut env, &processed).map_err(|e| e.to_string())?);
    }
    Ok(results)
}

/// Elaborate and register, failing with the verbatim elaborator message.
fn expect_registers(source: &str) {
    if let Err(e) = elaborate_file(source) {
        panic!("must elaborate and kernel-register, got: {e}\n--- source ---\n{source}");
    }
}

/// The reproduction from `CLAUDE.md`'s compiler/runtime paragraph, verbatim:
/// a `for` over a `List` in `IO` with an effectful body and no accumulator.
#[test]
fn test_for_no_accumulator_io_effectful_body_registers() {
    expect_registers(
        "def f (xs : List String) : IO Unit := do\n  for x in xs do\n    IO.println x\n",
    );
}

/// The same loop with the collection bound inside the block rather than taken
/// as a parameter.
#[test]
fn test_for_no_accumulator_local_collection_registers() {
    expect_registers(
        "def g : IO Unit := do\n  let xs : List String := [\"a\", \"b\"]\n  for x in xs do\n    IO.println x\n",
    );
}

/// Compound position: a statement AFTER the loop, which routes through
/// `elab_do_for_compound` and its post-loop continuation rather than through
/// the terminal `elab_do_for`.
#[test]
fn test_for_no_accumulator_compound_position_registers() {
    expect_registers(
        "def h (xs : List String) : IO Unit := do\n  for x in xs do\n    IO.println x\n  IO.println \"done\"\n",
    );
}

/// A two-statement body, so the step lambda is a real `Bind.bind` chain and
/// not a single action.
#[test]
fn test_for_no_accumulator_multi_statement_body_registers() {
    expect_registers(
        "def k (xs : List String) : IO Unit := do\n  for x in xs do\n    IO.println x\n    IO.println x\n",
    );
}

/// A non-`IO` monad: the lowering must read the block's monad rather than
/// assume `IO`.
#[test]
fn test_for_no_accumulator_id_monad_registers() {
    expect_registers("def i (xs : List Nat) : Id Unit := do\n  for _x in xs do\n    pure ()\n");
}

/// CONTROL — the accumulator form, which routes to the PURE lane
/// (`elab_do_pure_for`) and was already passing before this fix. It is here so
/// that a future change to the monadic lane cannot quietly take the pure lane
/// with it.
#[test]
fn test_for_with_accumulator_still_registers() {
    expect_registers(
        "def s (xs : List Nat) : Id Nat := do\n  let mut acc := 0\n  for x in xs do\n    acc := acc + x\n  pure acc\n",
    );
}
