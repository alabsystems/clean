// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Direct tests for elab_do_try.rs: try/catch/finally, let-else, repeat,
//! while, and dbg_trace elaboration paths.
//!
//! These cover the 460-line module that previously had ZERO direct test
//! coverage (#1795). Uses Environment::with_prelude() so monadic constants
//! are declared and elaboration exercises real desugaring logic.

use super::*;

/// Recursively search an `Expr` for a `Const` with the given name.
///
/// Added 2026-09-16 with the fail-closed rewrite below: several tests in this
/// file need to name a constant that must appear INSIDE the term, not just at
/// its head.
fn expr_contains_const(expr: &Expr, name: &str) -> bool {
    match expr.kind() {
        ExprKind::Const(n, _) => n.to_string() == name,
        ExprKind::App(f, a) => expr_contains_const(f, name) || expr_contains_const(a, name),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_contains_const(ty, name) || expr_contains_const(body, name)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            expr_contains_const(ty, name)
                || expr_contains_const(val, name)
                || expr_contains_const(body, name)
        }
        _ => false,
    }
}

// === try/catch elaboration ===

/// try/catch should elaborate to a MonadExcept.tryCatch application.
/// Uses the flat Lean 4 syntax to cover the parser boundary from #2969.
#[test]
fn test_elab_do_try_catch_basic() {
    // FAIL-CLOSED since 2026-09-16. Every arm of this test used to be
    // satisfiable: the `Err` arm accepted five unrelated error kinds and the
    // `Ok` arm accepted three different heads with a silent `_ => {}` fallback,
    // so nothing here could fail. MEASURED on this tree: the elaboration
    // succeeds and the head is exactly `MonadExcept.tryCatch`.
    let env = Environment::with_prelude();
    let expr = elab_with_env(&env, "do try return 42 catch e => return 0")
        .expect("try/catch with an unused catch binder must elaborate under the prelude");
    let head = expr.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(
            name.to_string(),
            "MonadExcept.tryCatch",
            "try/catch lowers through MonadExcept.tryCatch"
        ),
        other => panic!("expected Const(MonadExcept.tryCatch, _), got {other:?}"),
    }
}

/// The `catch` handler's BINDER is bound in its own body (G61, ledger (131)).
///
/// MEASURED 2026-09-16: `do try return 42 catch e => return e` failed with
/// `UnknownIdentWithSuggestions { name: "e", .. }` — `elab_do_catch_clause`
/// elaborated the handler body before pushing its binder — and under an
/// outer `e` the handler silently returned the OUTER value. Since round-5
/// lane D the handler is elaborated with its binder in scope.
#[test]
fn test_catch_handler_binder_is_bound_in_its_body() {
    let env = Environment::with_prelude();
    let expr = elab_with_env(&env, "do try return 42 catch e => return e")
        .expect("the catch binder is in scope in its handler");
    assert!(
        expr_contains_const(&expr, "MonadExcept.tryCatch"),
        "try/catch lowers through MonadExcept.tryCatch: {expr:?}"
    );
}

/// Typed catch clause should exercise the tryCatchThe path.
///
/// BROKEN FIXTURE, repaired 2026-09-16. The fixture was
/// `catch e : Nat => return e`, whose handler body USES the binder — and the
/// binder is unbound (see the refusal pin above), so this elaboration was
/// always `UnknownIdentWithSuggestions { name: "e", .. }`. The `Err` arm
/// accepted `UnknownIdent`, so the test passed while the `tryCatchThe` path it
/// is named for was never entered. With the binder unused the typed form
/// elaborates and the head is exactly `tryCatchThe` (MEASURED).
#[test]
fn test_elab_do_try_catch_typed() {
    let env = Environment::with_prelude();
    let expr = elab_with_env(&env, "do try return 42 catch e : Nat => return 0")
        .expect("a typed catch clause must elaborate under the prelude");
    let head = expr.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(
            name.to_string(),
            "tryCatchThe",
            "a TYPED catch clause must lower through tryCatchThe, not plain tryCatch"
        ),
        other => panic!("expected Const(tryCatchThe, _), got {other:?}"),
    }
}

/// try/catch/finally should exercise the tryFinally path.
#[test]
fn test_elab_do_try_catch_finally() {
    let env = Environment::with_prelude();
    // FAIL-CLOSED since 2026-09-16: the `Err` arm accepted seven unrelated
    // error substrings and the `Ok` arm only checked "not a bare Sort", so the
    // test could not fail either way. MEASURED: the elaboration succeeds with
    // head `tryFinally`, and `MonadExcept.tryCatch` appears inside it.
    let expr = elab_with_env(&env, "do try return 1 catch e => return 2 finally pure ()")
        .expect("try/catch/finally must elaborate under the prelude");
    let head = expr.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(
            name.to_string(),
            "tryFinally",
            "try/catch/finally lowers through tryFinally"
        ),
        other => panic!("expected Const(tryFinally, _), got {other:?}"),
    }
}

/// A `finally` body with an exit point is refused with Lean's message:
/// pinned Lean 4.8.0 says "`finally` currently does `return`, `break`, nor
/// `continue`" (sic) for `try return 1 catch _ => return 2 finally return 3`
/// (measured 2026-10-16).
#[test]
fn test_elab_do_finally_with_return_refused_as_lean() {
    let env = Environment::with_prelude();
    let err = elab_with_env(&env, "do try return 1 catch e => return 2 finally return 3")
        .expect_err("Lean refuses `return` in a `finally` body");
    assert!(
        err.to_string()
            .contains("`finally` currently does `return`, `break`, nor `continue`"),
        "the refusal is Lean's: {err:?}"
    );
}

// === let-else elaboration ===

/// `let x <- Id.mk 42 | return 0` then `return x` (one element per line: on one
/// line the fallback sequence would be `return 0; return x`, which Lean refuses
/// as "must be last element") exercises the variable-pattern
/// path of elab_do_let_else (the simpler path that doesn't go through ctor matching).
#[test]
fn test_elab_do_let_else_var_pattern() {
    let env = Environment::with_prelude();
    // FAIL-CLOSED since 2026-09-16. MEASURED: this elaborates with head
    // `Bind.bind`. The old `Err` arm accepted `UnknownIdent`, which is exactly
    // what a broken fixture produces, and the old `Ok` arm had a silent
    // `_ => {}` fallback for non-Const heads.
    let expr = elab_with_env(&env, "do\n  let x <- Id.mk 42 | return 0\n  return x")
        .expect("the let-else variable-pattern path must elaborate under the prelude");
    let head = expr.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(
            name.to_string(),
            "Bind.bind",
            "let-else var pattern binds through Bind.bind"
        ),
        other => panic!("expected Const(Bind.bind, _), got {other:?}"),
    }
}

// === repeat elaboration ===

/// REFUSAL PIN: `do repeat ...` desugars onto a constant the prelude does not
/// have.
///
/// MEASURED 2026-09-16 under `Environment::with_prelude()`:
/// `do repeat return ()` fails with
/// `UnknownIdentWithSuggestions { name: "Lean.Loop.mk", .. }` — the desugaring
/// emits `for _ in Lean.Loop.mk do body` and `Lean.Loop.mk` is not registered.
/// So the `Ok` arm here never ran, while the `Err` arm accepted
/// `msg.contains("Loop")`, which that very failure satisfies. The `elab_do_repeat`
/// path this test is named for has never been observed to produce a term.
///
/// Why `while` works and `repeat` does not, both in `infer/elab_do_try.rs`:
/// `elab_do_repeat` (:354) emits `Lean.Loop.mk` as a SURFACE identifier, so it
/// goes through name resolution, while `elab_do_while` (:392-:397) builds
/// `ForIn.forIn` and `Lean.Loop` with `Expr::const_` directly and never resolves
/// them.
///
/// PINNED AS A REFUSAL, not skipped: on the day `Lean.Loop` is registered,
/// `expect_err` fails loudly and the target assertion is
///
///     assert_eq!(expr.get_app_fn() head name, "ForIn.forIn");
///
/// which is what `do while ... do ...` already does today (see
/// `test_elab_do_while_basic`), so the shape is not speculative.
#[test]
fn test_elab_do_repeat_needs_lean_loop_which_the_prelude_lacks() {
    let env = Environment::with_prelude();
    let err = elab_with_env(&env, "do repeat return ()").expect_err(
        "`Lean.Loop.mk` is a MEASURED GAP in the prelude: if `repeat` now \
         elaborates, delete this pin and assert the ForIn.forIn head instead",
    );
    assert!(
        format!("{err:?}").contains("Lean.Loop"),
        "the repeat wall is the missing `Lean.Loop` collection; a different error \
         means the cause moved and this pin no longer describes it: {err:?}"
    );
}

// === while elaboration ===

/// `do while Bool.true do return ()` exercises the elab_do_while path which
/// builds an ite-guarded ForIn loop with ForInStep.yield/done.
#[test]
fn test_elab_do_while_basic() {
    let env = Environment::with_prelude();
    // FAIL-CLOSED since 2026-09-16. MEASURED: this elaborates with head
    // `ForIn.forIn`, carrying both `ForInStep.yield` and `ForInStep.done`. The
    // old arms accepted three heads, a silent non-Const fallback, and seven
    // error substrings, so no outcome could fail the test.
    let expr = elab_with_env(&env, "do while Bool.true do return ()")
        .expect("the while desugaring must elaborate under the prelude");
    let head = expr.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(
            name.to_string(),
            "ForIn.forIn",
            "while desugars to a ForIn.forIn loop"
        ),
        other => panic!("expected Const(ForIn.forIn, _), got {other:?}"),
    }
    assert!(
        expr_contains_const(&expr, "ForInStep.yield")
            && expr_contains_const(&expr, "ForInStep.done"),
        "the while body is an ite guarding ForInStep.yield / ForInStep.done"
    );
}

// === dbg_trace elaboration ===

/// `do dbg_trace "hello"; return 42` should produce a `dbgTrace "hello" (fun _ => ...)`
/// application, exercising elab_do_dbg_trace with a continuation.
#[test]
fn test_elab_do_dbg_trace_with_continuation() {
    let env = Environment::with_prelude();
    // FAIL-CLOSED since 2026-09-16. MEASURED: head `dbgTrace` with exactly 2
    // arguments. The `_ => {}` fallback in the old `Ok` arm and the
    // four-substring `Err` arm both made this test unfalsifiable.
    let expr = elab_with_env(&env, "do dbg_trace \"hello\"; return 42")
        .expect("dbg_trace with a continuation must elaborate under the prelude");
    let head = expr.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(
            name.to_string(),
            "dbgTrace",
            "dbg_trace should produce a dbgTrace head"
        ),
        other => panic!("expected Const(dbgTrace, _), got {other:?}"),
    }
    let args = expr.get_app_args();
    assert!(
        args.len() >= 2,
        "dbgTrace should have at least 2 args (msg, thunk), got {}",
        args.len()
    );
}

/// `do dbg_trace "terminal"` (terminal position, no continuation) should
/// produce `dbgTrace "terminal" (fun _ => pure ())`.
#[test]
fn test_elab_do_dbg_trace_terminal() {
    let env = Environment::with_prelude();
    // FAIL-CLOSED since 2026-09-16. MEASURED: head `dbgTrace` with 2 arguments.
    // The old `if let ExprKind::Const(..)` guard plus the disjunctive `Err` arm
    // meant no outcome could fail this test.
    let expr = elab_with_env(&env, "do dbg_trace \"terminal\"")
        .expect("terminal dbg_trace must elaborate under the prelude");
    let head = expr.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(
            name.to_string(),
            "dbgTrace",
            "terminal dbg_trace should produce a dbgTrace head"
        ),
        other => panic!("expected Const(dbgTrace, _), got {other:?}"),
    }
}
