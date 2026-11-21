// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The eager-IO rewrite: its type classification, and — end to end through
//! the production `clean run` emit + build path — the measured programs that
//! printed a wrong answer at exit 0 before it, each now byte-identical to
//! pinned Lean v4.30.0-rc2 (`lean --run`, outputs quoted per test).

use std::path::PathBuf;
use std::process::Command;

use clean_kernel::{Environment, Expr, Name};

use super::*;
use crate::native_build::{build_native_binary_in_scratch, emit_entry_c_with_type};

fn native_base_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_io_ops().expect("init_io_ops on the prelude");
    env
}

fn io_of(ty: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("IO"), vec![]), ty)
}

fn unit() -> Expr {
    Expr::const_(Name::from_string("Unit"), vec![])
}

/// Build `main` from `source` through the production emit + link path and run
/// it with `args`, returning (stdout, exit status).
///
/// FAIL-CLOSED on a missing C compiler, with no skip path: these tests exist to
/// assert the exact bytes a program prints, and a test that returns early
/// without a compiler passes having asserted nothing
/// (`scripts/check_self_skipping_tests.py`'s EARLY_RETURN shape).
fn run_main(source: &str, args: &[&str]) -> (String, i32) {
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    let has_cc = Command::new(&cc)
        .arg("--version")
        .output()
        .is_ok_and(|o| o.status.success());
    assert!(
        has_cc,
        "a C compiler (`{cc}`) is required: these tests assert the bytes a linked program prints"
    );
    let dir = tempfile::tempdir().expect("tempdir");
    let file: PathBuf = dir.path().join("eager_io_fixture.lean");
    std::fs::write(&file, source).expect("write fixture");
    let (emitted, ty) = emit_entry_c_with_type(&file, "main", 0).expect("emit main");
    let built =
        build_native_binary_in_scratch("main", &emitted, ty.as_ref(), true).expect("link main");
    let output = Command::new(&built.binary)
        .args(args)
        .output()
        .expect("run main");
    (
        String::from_utf8_lossy(&output.stdout).into_owned(),
        output.status.code().unwrap_or(-1),
    )
}

#[test]
fn test_is_action_type_io_application_is_an_action_and_the_monad_is_not() {
    let env = native_base_env();
    assert!(is_action_type(&env, &io_of(unit())), "IO Unit is an action");
    assert!(
        !is_action_type(&env, &Expr::const_(Name::from_string("IO"), vec![])),
        "`IO` unapplied is the monad, not an action"
    );
    assert!(!is_action_type(&env, &unit()), "Unit is not an action");
    let thunk = Expr::pi(BinderInfo::Default, unit(), io_of(unit()));
    assert!(
        !is_action_type(&env, &thunk),
        "a thunk `Unit → IO Unit` is a function, not an action"
    );
    assert!(
        is_action_returning(&env, &thunk),
        "a thunk `Unit → IO Unit` returns an action"
    );
    // `Id (IO Unit)` unfolds to an action: the classification looks through
    // a definition at the head (`Id α := α`).
    let id_io = Expr::app(
        Expr::const_(Name::from_string("Id"), vec![clean_kernel::Level::zero()]),
        io_of(unit()),
    );
    assert!(
        is_action_type(&env, &id_io),
        "Id (IO Unit) δ-unfolds to IO Unit"
    );
}

/// The rewrite leaves an action-free value structurally unchanged.
#[test]
fn test_rewrite_for_eager_io_pure_value_is_unchanged() {
    let env = native_base_env();
    let pure = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::nat_lit(3),
    );
    assert_eq!(rewrite_for_eager_io(&env, &pure), pure);
}

/// Measured before the rewrite: `big` AND `small`, exit 0 (both arms of the
/// non-final `if` ran). Pinned Lean with one argument: `small`.
#[test]
fn test_native_nonfinal_if_runs_only_the_taken_arm() {
    let (out, status) = run_main(
        "def main (args : List String) : IO UInt32 := do\n  \
         if args.length > 5 then\n    IO.println \"big\"\n  \
         else\n    IO.println \"small\"\n  \
         return 0\n",
        &["a"],
    );
    assert_eq!(out, "small\n");
    assert_eq!(status, 0);
}

/// Measured before: `never\ndone`. Pinned Lean: `done`.
#[test]
fn test_native_if_false_never_runs_its_then_arm() {
    let (out, _) = run_main(
        "def main : IO Unit := do\n  \
         if false then IO.println \"never\" else pure ()\n  \
         IO.println \"done\"\n",
        &[],
    );
    assert_eq!(out, "done\n");
}

/// Measured before: `A\nB` (the named action ran once, at its `let`). Pinned
/// Lean: `B\nA\nA`.
#[test]
fn test_native_let_bound_action_runs_at_each_use() {
    let (out, _) = run_main(
        "def main : IO Unit := do\n  \
         let a := IO.println \"A\"\n  \
         IO.println \"B\"\n  a\n  a\n",
        &[],
    );
    assert_eq!(out, "B\nA\nA\n");
}

/// A non-final `match` statement: the nullary arm was an evaluated argument of
/// `l_Nat_casesOn`, so `greet 1` printed `zero` too. Pinned Lean:
/// `zero\nafter\nnonzero\nafter`.
#[test]
fn test_native_nonfinal_match_runs_only_the_matched_arm() {
    let (out, _) = run_main(
        "def greet (n : Nat) : IO Unit := do\n  \
         match n with\n  | 0 => IO.println \"zero\"\n  | _ => IO.println \"nonzero\"\n  \
         IO.println \"after\"\n\
         def main : IO Unit := do\n  greet 0\n  greet 1\n",
        &[],
    );
    assert_eq!(out, "zero\nafter\nnonzero\nafter\n");
}

/// Structural recursion over an IO motive keeps its order once its induction
/// hypothesis is a thunk: each level prints before it recurses, and the base
/// arm's own action runs once. Pinned Lean: `1\n0\nbase`.
#[test]
fn test_native_recursive_io_loop_keeps_lean_order() {
    let (out, _) = run_main(
        "def loop : Nat → IO Unit\n  \
         | 0 => IO.println \"base\"\n  \
         | n + 1 => do\n    IO.println (toString n)\n    loop n\n\
         def main : IO Unit := loop 2\n",
        &[],
    );
    assert_eq!(out, "1\n0\nbase\n");
}

/// `for a in args do IO.println a` died with SIGSEGV (its step value
/// `ForInStep.yield PUnit.unit` was built as a bare scalar and read as an
/// object). Pinned Lean with `a b`: `a\nb`, exit 3.
#[test]
fn test_native_for_in_over_io_prints_each_element() {
    let (out, status) = run_main(
        "def main (args : List String) : IO UInt32 := do\n  \
         for a in args do\n    IO.println a\n  return 3\n",
        &["a", "b"],
    );
    assert_eq!(out, "a\nb\n");
    assert_eq!(status, 3);
}

#[test]
fn test_native_for_in_uses_the_selected_closed_instance() {
    let (out, status) = run_main(
        "local instance (priority := 20000) skipAll : ForIn IO (List String) String where\n  \
         forIn _ initial _ := pure initial\n\n\
         def main (args : List String) : IO UInt32 := do\n  \
         for a in args do\n    IO.println a\n  return 3\n",
        &["a", "b"],
    );
    assert!(out.is_empty(), "{out}");
    assert_eq!(status, 3);
}

/// The two iterator dictionaries are definitionally equal. Only the compiled
/// replacement calls the overridden value, making the runtime choice visible.
#[test]
fn test_native_for_in_preserves_the_selected_dictionary_for_csimp() {
    let source = include_str!("../tests/fixtures/for_in_csimp.lean");
    assert_eq!(run_main(source, &[]), ("7\n".to_string(), 0));
    let without_rule = source.replace("@[csimp] theorem", "theorem");
    assert_eq!(run_main(&without_rule, &[]), ("0\n".to_string(), 0));
}

/// The constructor-layout face of the same fault, at exit 0: `((PUnit.unit,
/// 5)).2` printed `1` (Lean: `5`) because the producer dropped the erased
/// field while `.2` read the declared slot.
#[test]
fn test_native_erased_constructor_field_keeps_its_slot() {
    let (out, _) = run_main(
        "def p : PUnit.{1} × Nat := (PUnit.unit, 5)\n\
         def main : IO Unit := IO.println (toString p.2)\n",
        &[],
    );
    assert_eq!(out, "5\n");
}

/// Under `abbrev M := IO` an `if` between actions has type `M Unit`, so the
/// value names `M` where the audit's trigger scan looked for `IO`: nothing was
/// rewritten or audited, the `if` stayed an evaluated argument, and both arms
/// ran. Measured 2026-09-25 through `clean run`: `a\nb` at exit 0. Pinned Lean
/// v4.30.0-rc2: `a`.
#[test]
fn test_native_action_alias_branch_runs_only_the_taken_arm() {
    let (out, status) = run_main(
        "abbrev M := IO\n\
         def g (c : Bool) : M Unit :=\n  \
         (fun (x : M Unit) => x) (if c then IO.println \"a\" else IO.println \"b\")\n\
         def main : IO Unit := g true\n",
        &[],
    );
    assert_eq!(out, "a\n");
    assert_eq!(status, 0);
}
