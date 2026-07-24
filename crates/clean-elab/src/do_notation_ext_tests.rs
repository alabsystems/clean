// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended do-notation desugaring (try/catch, reassign, break/continue, etc.)

use crate::do_notation::DoElement;
use crate::do_notation_ext::{
    desugar_break, desugar_continue, desugar_dbg_trace, desugar_nested_do, desugar_reassign,
    desugar_repeat, desugar_try_catch, CatchClause,
};
use clean_parser::SurfaceExpr;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn expect_ok(result: Result<SurfaceExpr, crate::ElabError>) -> SurfaceExpr {
    result.expect("desugaring should succeed")
}

fn is_app_of(expr: &SurfaceExpr, name: &str) -> bool {
    if let SurfaceExpr::App(_, func, _) = expr {
        if let SurfaceExpr::Ident(_, ident_name) = func.as_ref() {
            return ident_name == name;
        }
    }
    false
}

fn is_ident(expr: &SurfaceExpr, name: &str) -> bool {
    matches!(expr, SurfaceExpr::Ident(_, n) if n == name)
}

fn app_args(expr: &SurfaceExpr) -> Option<&[clean_parser::SurfaceArg]> {
    if let SurfaceExpr::App(_, _, args) = expr {
        Some(args)
    } else {
        None
    }
}

fn action(name: &str) -> DoElement {
    DoElement::Action(Box::new(SurfaceExpr::ident(name)))
}

fn bind(name: &str, act: &str) -> DoElement {
    DoElement::Bind {
        name: Some(name.into()),
        action: Box::new(SurfaceExpr::ident(act)),
    }
}

fn ret(name: &str) -> DoElement {
    DoElement::Return(Box::new(SurfaceExpr::ident(name)))
}

// ---------------------------------------------------------------------------
// Tests: try/catch
// ---------------------------------------------------------------------------

#[test]
fn test_try_catch_basic_untyped() {
    // try { action1 } catch e => { action2 }
    let result = expect_ok(desugar_try_catch(
        &[action("action1")],
        &[CatchClause {
            binder: "e".into(),
            exc_type: None,
            body: vec![action("handler")],
        }],
        None,
    ));
    assert!(
        is_app_of(&result, "MonadExcept.tryCatch"),
        "should produce MonadExcept.tryCatch, got {result:?}"
    );
    let args = app_args(&result).unwrap();
    assert_eq!(args.len(), 2);
}

#[test]
fn test_try_catch_typed() {
    // try { action1 } catch e : IOError => { handler }
    let result = expect_ok(desugar_try_catch(
        &[action("action1")],
        &[CatchClause {
            binder: "e".into(),
            exc_type: Some(SurfaceExpr::ident("IOError")),
            body: vec![action("handler")],
        }],
        None,
    ));
    assert!(
        is_app_of(&result, "tryCatchThe"),
        "typed catch should produce tryCatchThe, got {result:?}"
    );
    let args = app_args(&result).unwrap();
    assert_eq!(args.len(), 3, "tryCatchThe takes ExcType, body, handler");
    assert!(
        is_ident(&args[0].expr, "IOError"),
        "first arg is exception type"
    );
}

#[test]
fn test_try_catch_with_finally() {
    // try { action1 } catch e => { handler } finally { cleanup }
    let result = expect_ok(desugar_try_catch(
        &[action("action1")],
        &[CatchClause {
            binder: "e".into(),
            exc_type: None,
            body: vec![action("handler")],
        }],
        Some(&[action("cleanup")]),
    ));
    assert!(
        is_app_of(&result, "tryFinally"),
        "should wrap in tryFinally, got {result:?}"
    );
}

#[test]
fn test_try_finally_no_catch() {
    // try { body } finally { cleanup }
    let result = expect_ok(desugar_try_catch(
        &[action("body")],
        &[],
        Some(&[action("cleanup")]),
    ));
    assert!(
        is_app_of(&result, "tryFinally"),
        "try-finally without catch should produce tryFinally"
    );
}

#[test]
fn test_try_empty_body_errors() {
    let result = desugar_try_catch(
        &[],
        &[CatchClause {
            binder: "e".into(),
            exc_type: None,
            body: vec![action("handler")],
        }],
        None,
    );
    assert!(result.is_err(), "empty try body should error");
}

#[test]
fn test_try_no_handler_errors() {
    let result = desugar_try_catch(&[action("body")], &[], None);
    assert!(result.is_err(), "try without catch or finally should error");
}

#[test]
fn test_try_multiple_catches_fold_left() {
    // try { body } catch e1 => { h1 } catch e2 : T => { h2 }
    let result = expect_ok(desugar_try_catch(
        &[action("body")],
        &[
            CatchClause {
                binder: "e1".into(),
                exc_type: None,
                body: vec![action("h1")],
            },
            CatchClause {
                binder: "e2".into(),
                exc_type: Some(SurfaceExpr::ident("T")),
                body: vec![action("h2")],
            },
        ],
        None,
    ));
    // Outer should be tryCatchThe (second catch wraps first)
    assert!(
        is_app_of(&result, "tryCatchThe"),
        "outer catch should be tryCatchThe, got {result:?}"
    );
}

#[test]
fn test_try_catch_empty_handler_defaults_to_pure_unit() {
    let result = expect_ok(desugar_try_catch(
        &[action("body")],
        &[CatchClause {
            binder: "e".into(),
            exc_type: None,
            body: vec![],
        }],
        None,
    ));
    assert!(is_app_of(&result, "MonadExcept.tryCatch"));
}

// ---------------------------------------------------------------------------
// Tests: reassignment
// ---------------------------------------------------------------------------

#[test]
fn test_reassign_produces_let() {
    // x := 42; pure x
    let result = expect_ok(desugar_reassign(
        "x",
        &SurfaceExpr::ident("new_val"),
        &[ret("x")],
    ));
    assert!(
        matches!(&result, SurfaceExpr::Let(_, binder, _, _) if binder.name == "x"),
        "should produce let x := new_val in rest, got {result:?}"
    );
}

#[test]
fn test_reassign_empty_var_errors() {
    let result = desugar_reassign("", &SurfaceExpr::ident("val"), &[ret("x")]);
    assert!(result.is_err(), "empty variable name should error");
}

#[test]
fn test_reassign_chain() {
    // x := a; x := b; pure x
    let result = expect_ok(desugar_reassign(
        "x",
        &SurfaceExpr::ident("a"),
        &[
            DoElement::LetMut {
                name: "x".into(),
                value: Box::new(SurfaceExpr::ident("b")),
            },
            ret("x"),
        ],
    ));
    // Outer: let x := a in (let x := b in pure x)
    assert!(matches!(&result, SurfaceExpr::Let(_, _, _, _)));
}

// ---------------------------------------------------------------------------
// Tests: break/continue
// ---------------------------------------------------------------------------

#[test]
fn test_break_produces_done_step() {
    let result = desugar_break();
    // Pure.pure (ForInStep.done PUnit.unit)
    assert!(
        is_app_of(&result, "Pure.pure"),
        "break should produce Pure.pure"
    );
    let inner = &app_args(&result).unwrap()[0].expr;
    assert!(
        is_app_of(inner, "ForInStep.done"),
        "inner should be ForInStep.done, got {inner:?}"
    );
}

#[test]
fn test_continue_produces_yield_step() {
    let result = desugar_continue();
    assert!(
        is_app_of(&result, "Pure.pure"),
        "continue should produce Pure.pure"
    );
    let inner = &app_args(&result).unwrap()[0].expr;
    assert!(
        is_app_of(inner, "ForInStep.yield"),
        "inner should be ForInStep.yield, got {inner:?}"
    );
}

#[test]
fn test_break_and_continue_differ() {
    let brk = desugar_break();
    let cont = desugar_continue();
    let brk_inner = &app_args(&brk).unwrap()[0].expr;
    let cont_inner = &app_args(&cont).unwrap()[0].expr;
    // break uses ForInStep.done, continue uses ForInStep.yield
    assert!(is_app_of(brk_inner, "ForInStep.done"));
    assert!(is_app_of(cont_inner, "ForInStep.yield"));
}

// ---------------------------------------------------------------------------
// Tests: dbg_trace
// ---------------------------------------------------------------------------

#[test]
fn test_dbg_trace_desugars_to_dbgtrace_app() {
    let result = expect_ok(desugar_dbg_trace(&SurfaceExpr::ident("msg"), &[ret("x")]));
    assert!(
        is_app_of(&result, "dbgTrace"),
        "should produce dbgTrace app, got {result:?}"
    );
    let args = app_args(&result).unwrap();
    assert_eq!(args.len(), 2, "dbgTrace takes msg and thunk");
    assert!(is_ident(&args[0].expr, "msg"), "first arg is the message");
    assert!(
        matches!(&args[1].expr, SurfaceExpr::Lambda(_, _, _)),
        "second arg is a lambda thunk"
    );
}

#[test]
fn test_dbg_trace_empty_rest_errors() {
    let result = desugar_dbg_trace(&SurfaceExpr::ident("msg"), &[]);
    assert!(
        result.is_err(),
        "dbg_trace with empty continuation should error"
    );
}

// ---------------------------------------------------------------------------
// Tests: repeat
// ---------------------------------------------------------------------------

#[test]
fn test_repeat_desugars_to_forin_loop_mk() {
    let result = expect_ok(desugar_repeat(&[action("body")]));
    assert!(
        is_app_of(&result, "ForIn.forIn"),
        "repeat should produce ForIn.forIn, got {result:?}"
    );
    let args = app_args(&result).unwrap();
    assert_eq!(args.len(), 3, "ForIn.forIn takes collection, init, step_fn");
    assert!(
        is_ident(&args[0].expr, "Lean.Loop.mk"),
        "first arg should be Lean.Loop.mk"
    );
}

#[test]
fn test_repeat_empty_body_errors() {
    let result = desugar_repeat(&[]);
    assert!(result.is_err(), "empty repeat body should error");
}

// ---------------------------------------------------------------------------
// Tests: nested do-blocks
// ---------------------------------------------------------------------------

#[test]
fn test_nested_do_block_desugars() {
    let inner = vec![bind("a", "action2"), ret("a")];
    let result = expect_ok(desugar_nested_do(&inner));
    assert!(
        is_app_of(&result, "Bind.bind"),
        "nested do should produce Bind.bind, got {result:?}"
    );
}

#[test]
fn test_nested_do_empty_errors() {
    let result = desugar_nested_do(&[]);
    assert!(result.is_err(), "empty nested do should error");
}

#[test]
fn test_nested_do_single_action() {
    let result = expect_ok(desugar_nested_do(&[action("x")]));
    assert!(
        is_ident(&result, "x"),
        "single action nested do should return the action"
    );
}

// ---------------------------------------------------------------------------
// Tests: desugar_do_elems_ext (full DoElem pipeline)
// ---------------------------------------------------------------------------

#[test]
fn test_ext_simple_bind_chain() {
    use crate::do_notation_ext::desugar_do_elems_ext;
    use clean_parser::{DoElem, Span, SurfaceBinder, SurfaceBinderInfo};

    let elems = vec![
        DoElem::Bind(
            Span::dummy(),
            SurfaceBinder::new("x", None, SurfaceBinderInfo::Explicit),
            Box::new(SurfaceExpr::ident("getLine")),
        ),
        DoElem::Return(Span::dummy(), Box::new(SurfaceExpr::ident("x"))),
    ];
    let result = expect_ok(desugar_do_elems_ext(&elems));
    assert!(is_app_of(&result, "Bind.bind"));
}

#[test]
fn test_ext_try_catch_direct() {
    use crate::do_notation_ext::desugar_do_elems_ext;
    use clean_parser::{DoCatchClause, DoElem, Span};

    let elems = vec![DoElem::TryCatch(
        Span::dummy(),
        vec![DoElem::Expr(
            Span::dummy(),
            Box::new(SurfaceExpr::ident("riskyOp")),
        )],
        vec![DoCatchClause {
            span: Span::dummy(),
            binder: "e".into(),
            exc_type: None,
            body: vec![DoElem::Return(
                Span::dummy(),
                Box::new(SurfaceExpr::ident("fallback")),
            )],
        }],
        None,
    )];
    let result = expect_ok(desugar_do_elems_ext(&elems));
    assert!(
        is_app_of(&result, "MonadExcept.tryCatch"),
        "ext pipeline should handle TryCatch, got {result:?}"
    );
}

#[test]
fn test_ext_break_in_compound() {
    use crate::do_notation_ext::desugar_do_elems_ext;
    use clean_parser::{DoElem, Span};

    // break; unreachable_continuation
    let elems = vec![
        DoElem::Break(Span::dummy()),
        DoElem::Expr(Span::dummy(), Box::new(SurfaceExpr::ident("unreachable"))),
    ];
    let result = expect_ok(desugar_do_elems_ext(&elems));
    // break ignores continuation
    assert!(is_app_of(&result, "Pure.pure"));
}

#[test]
fn test_ext_reassign_in_compound() {
    use crate::do_notation_ext::desugar_do_elems_ext;
    use clean_parser::{DoElem, Span};

    let elems = vec![
        DoElem::Reassign(
            Span::dummy(),
            "counter".into(),
            Box::new(SurfaceExpr::ident("new_val")),
        ),
        DoElem::Return(Span::dummy(), Box::new(SurfaceExpr::ident("counter"))),
    ];
    let result = expect_ok(desugar_do_elems_ext(&elems));
    assert!(
        matches!(&result, SurfaceExpr::Let(_, binder, _, _) if binder.name == "counter"),
        "reassign should produce let-shadowing, got {result:?}"
    );
}

#[test]
fn test_ext_dbg_trace_in_compound() {
    use crate::do_notation_ext::desugar_do_elems_ext;
    use clean_parser::{DoElem, Span};

    let elems = vec![
        DoElem::DbgTrace(Span::dummy(), Box::new(SurfaceExpr::ident("msg"))),
        DoElem::Return(Span::dummy(), Box::new(SurfaceExpr::ident("result"))),
    ];
    let result = expect_ok(desugar_do_elems_ext(&elems));
    assert!(
        is_app_of(&result, "dbgTrace"),
        "dbg_trace in compound should produce dbgTrace app, got {result:?}"
    );
}

#[test]
fn test_ext_repeat_in_compound() {
    use crate::do_notation_ext::desugar_do_elems_ext;
    use clean_parser::{DoElem, Span};

    let elems = vec![
        DoElem::Repeat(
            Span::dummy(),
            vec![DoElem::Expr(
                Span::dummy(),
                Box::new(SurfaceExpr::ident("tick")),
            )],
        ),
        DoElem::Return(Span::dummy(), Box::new(SurfaceExpr::ident("done"))),
    ];
    let result = expect_ok(desugar_do_elems_ext(&elems));
    // repeat + continuation = Bind.bind (repeat_expr) (_ => rest)
    assert!(
        is_app_of(&result, "Bind.bind"),
        "repeat in compound should be bound with continuation, got {result:?}"
    );
}

#[test]
fn test_ext_empty_errors() {
    use crate::do_notation_ext::desugar_do_elems_ext;
    let result = desugar_do_elems_ext(&[]);
    assert!(result.is_err());
}
