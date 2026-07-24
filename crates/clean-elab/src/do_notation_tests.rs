// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for do notation surface-level desugaring.

use crate::do_notation::{desugar_do_block, desugar_for_in, desugar_while, DoElement};
use clean_parser::SurfaceExpr;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Assert the result is Ok and return the inner value.
fn expect_ok(result: Result<SurfaceExpr, crate::ElabError>) -> SurfaceExpr {
    result.expect("desugar_do_block should succeed")
}

/// Check if a `SurfaceExpr` is an `App` whose function is an `Ident` with the given name.
fn is_app_of(expr: &SurfaceExpr, name: &str) -> bool {
    if let SurfaceExpr::App(_, func, _) = expr {
        if let SurfaceExpr::Ident(_, ident_name) = func.as_ref() {
            return ident_name == name;
        }
    }
    false
}

/// Check if a `SurfaceExpr` is an `Ident` with the given name.
fn is_ident(expr: &SurfaceExpr, name: &str) -> bool {
    matches!(expr, SurfaceExpr::Ident(_, n) if n == name)
}

/// Extract the args from an App node.
fn app_args(expr: &SurfaceExpr) -> Option<&[clean_parser::SurfaceArg]> {
    if let SurfaceExpr::App(_, _, args) = expr {
        Some(args)
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Tests: basic desugaring
// ---------------------------------------------------------------------------

#[test]
fn test_simple_bind_desugars_to_bind_app() {
    // do let x <- action1; pure (x)
    let elements = vec![
        DoElement::Bind {
            name: Some("x".into()),
            action: Box::new(SurfaceExpr::ident("action1")),
        },
        DoElement::Return(Box::new(SurfaceExpr::ident("x"))),
    ];

    let result = expect_ok(desugar_do_block(&elements));

    // Should be Bind.bind action1 (fun x => Pure.pure x)
    assert!(
        is_app_of(&result, "Bind.bind"),
        "expected Bind.bind app, got {result:?}"
    );
    let args = app_args(&result).expect("should have args");
    assert_eq!(args.len(), 2, "Bind.bind should have 2 args");
    assert!(
        is_ident(&args[0].expr, "action1"),
        "first arg should be action1"
    );

    // Second arg should be a Lambda
    assert!(
        matches!(&args[1].expr, SurfaceExpr::Lambda(_, binders, _) if binders[0].name == "x"),
        "second arg should be fun x => ..."
    );
}

#[test]
fn test_chain_binds_produces_nested_bind() {
    // do let x <- a; let y <- b; pure (y)
    let elements = vec![
        DoElement::Bind {
            name: Some("x".into()),
            action: Box::new(SurfaceExpr::ident("a")),
        },
        DoElement::Bind {
            name: Some("y".into()),
            action: Box::new(SurfaceExpr::ident("b")),
        },
        DoElement::Return(Box::new(SurfaceExpr::ident("y"))),
    ];

    let result = expect_ok(desugar_do_block(&elements));

    // Outer should be Bind.bind a (fun x => ...)
    assert!(is_app_of(&result, "Bind.bind"));
    let args = app_args(&result).expect("should have args");

    // The continuation body should contain another Bind.bind
    if let SurfaceExpr::Lambda(_, _, body) = &args[1].expr {
        assert!(
            is_app_of(body, "Bind.bind"),
            "inner should be Bind.bind, got {body:?}"
        );
    } else {
        panic!("expected Lambda continuation");
    }
}

#[test]
fn test_bare_action_binds_with_wildcard() {
    // do action1; action2
    let elements = vec![
        DoElement::Action(Box::new(SurfaceExpr::ident("action1"))),
        DoElement::Action(Box::new(SurfaceExpr::ident("action2"))),
    ];

    let result = expect_ok(desugar_do_block(&elements));

    // Should be Bind.bind action1 (fun _ => action2)
    assert!(is_app_of(&result, "Bind.bind"));
    let args = app_args(&result).expect("should have args");
    assert!(is_ident(&args[0].expr, "action1"));

    if let SurfaceExpr::Lambda(_, binders, body) = &args[1].expr {
        assert_eq!(binders[0].name, "_", "binder should be wildcard");
        assert!(is_ident(body, "action2"), "body should be action2");
    } else {
        panic!("expected Lambda continuation");
    }
}

#[test]
fn test_let_in_do_desugars_to_let_expr() {
    // do let x := 42; pure x
    let elements = vec![
        DoElement::Let {
            name: "x".into(),
            value: Box::new(SurfaceExpr::nat(42)),
        },
        DoElement::Return(Box::new(SurfaceExpr::ident("x"))),
    ];

    let result = expect_ok(desugar_do_block(&elements));

    // Should be let x := 42 in Pure.pure x
    assert!(
        matches!(&result, SurfaceExpr::Let(_, binder, val, body)
            if binder.name == "x"
            && matches!(val.as_ref(), SurfaceExpr::Lit(_, clean_parser::SurfaceLit::Nat(42)))
            && is_app_of(body, "Pure.pure")
        ),
        "expected let x := 42 in Pure.pure x, got {result:?}"
    );
}

#[test]
fn test_return_desugars_to_pure() {
    // do return 7
    let elements = vec![DoElement::Return(Box::new(SurfaceExpr::nat(7)))];

    let result = expect_ok(desugar_do_block(&elements));

    // Should be Pure.pure 7
    assert!(
        is_app_of(&result, "Pure.pure"),
        "expected Pure.pure, got {result:?}"
    );
    let args = app_args(&result).expect("should have args");
    assert!(
        matches!(
            &args[0].expr,
            SurfaceExpr::Lit(_, clean_parser::SurfaceLit::Nat(7))
        ),
        "pure arg should be 7"
    );
}

#[test]
fn test_if_in_do_desugars_branches() {
    // do if cond then return 1 else return 2
    let elements = vec![DoElement::If {
        cond: Box::new(SurfaceExpr::ident("cond")),
        then_branch: vec![DoElement::Return(Box::new(SurfaceExpr::nat(1)))],
        else_branch: vec![DoElement::Return(Box::new(SurfaceExpr::nat(2)))],
    }];

    let result = expect_ok(desugar_do_block(&elements));

    // Should be if cond then Pure.pure 1 else Pure.pure 2
    assert!(
        matches!(&result, SurfaceExpr::If(_, cond, then_expr, else_expr)
            if is_ident(cond, "cond")
            && is_app_of(then_expr, "Pure.pure")
            && is_app_of(else_expr, "Pure.pure")
        ),
        "expected if-then-else with pure branches, got {result:?}"
    );
}

#[test]
fn test_for_in_desugars_to_for_in_app() {
    // for x in xs do action
    let body = vec![DoElement::Action(Box::new(SurfaceExpr::ident("action")))];

    let result = expect_ok(desugar_for_in("x", &SurfaceExpr::ident("xs"), &body));

    // Should be ForIn.forIn xs PUnit.unit (fun x _ => ...)
    assert!(
        is_app_of(&result, "ForIn.forIn"),
        "expected ForIn.forIn, got {result:?}"
    );
    let args = app_args(&result).expect("should have args");
    assert_eq!(args.len(), 3, "ForIn.forIn should have 3 args");

    // First arg: collection
    assert!(is_ident(&args[0].expr, "xs"));

    // Second arg: initial accumulator (PUnit.unit)
    assert!(is_ident(&args[1].expr, "PUnit.unit"));

    // Third arg: step function (fun x _ => ...)
    assert!(
        matches!(&args[2].expr, SurfaceExpr::Lambda(_, binders, _)
            if binders.len() == 2
            && binders[0].name == "x"
            && binders[1].name == "_"
        ),
        "third arg should be fun x _ => ..."
    );
}

#[test]
fn test_nested_do_blocks() {
    // do let x <- outer; do let y <- inner; pure y
    // The inner do block is an Action containing a conceptual nested do
    // For our desugaring, we can represent this as nested bind chains
    let elements = vec![
        DoElement::Bind {
            name: Some("x".into()),
            action: Box::new(SurfaceExpr::ident("outer")),
        },
        DoElement::Bind {
            name: Some("y".into()),
            action: Box::new(SurfaceExpr::ident("inner")),
        },
        DoElement::Return(Box::new(SurfaceExpr::ident("y"))),
    ];

    let result = expect_ok(desugar_do_block(&elements));

    // Verify nested bind structure
    assert!(is_app_of(&result, "Bind.bind"));
    let outer_args = app_args(&result).expect("should have args");
    assert!(is_ident(&outer_args[0].expr, "outer"));

    // Inner continuation contains another bind
    if let SurfaceExpr::Lambda(_, _, inner_body) = &outer_args[1].expr {
        assert!(is_app_of(inner_body, "Bind.bind"));
    } else {
        panic!("expected Lambda");
    }
}

#[test]
fn test_empty_do_fails() {
    let result = desugar_do_block(&[]);
    assert!(result.is_err(), "empty do block should fail");

    let err = result.unwrap_err();
    assert!(
        matches!(err, crate::ElabError::NotImplemented(msg) if msg.contains("empty")),
        "error should mention empty"
    );
}

#[test]
fn test_do_element_variants_construction() {
    // Just verify all DoElement variants can be constructed
    let _bind = DoElement::Bind {
        name: Some("x".into()),
        action: Box::new(SurfaceExpr::ident("a")),
    };
    let _bind_anon = DoElement::Bind {
        name: None,
        action: Box::new(SurfaceExpr::ident("a")),
    };
    let _let = DoElement::Let {
        name: "x".into(),
        value: Box::new(SurfaceExpr::nat(1)),
    };
    let _let_mut = DoElement::LetMut {
        name: "x".into(),
        value: Box::new(SurfaceExpr::nat(1)),
    };
    let _action = DoElement::Action(Box::new(SurfaceExpr::ident("a")));
    let _return = DoElement::Return(Box::new(SurfaceExpr::ident("x")));
    let _if = DoElement::If {
        cond: Box::new(SurfaceExpr::ident("c")),
        then_branch: vec![],
        else_branch: vec![],
    };
    let _for_in = DoElement::ForIn {
        var: "x".into(),
        collection: Box::new(SurfaceExpr::ident("xs")),
        body: vec![],
    };
}

#[test]
fn test_let_mut_in_do_treated_as_let() {
    // do let mut x := 0; pure x
    let elements = vec![
        DoElement::LetMut {
            name: "x".into(),
            value: Box::new(SurfaceExpr::nat(0)),
        },
        DoElement::Return(Box::new(SurfaceExpr::ident("x"))),
    ];

    let result = expect_ok(desugar_do_block(&elements));

    // At surface level, LetMut desugars the same as Let
    assert!(
        matches!(&result, SurfaceExpr::Let(_, binder, _, _) if binder.name == "x"),
        "LetMut should desugar like Let at surface level, got {result:?}"
    );
}

#[test]
fn test_while_desugars_to_repeat() {
    let body = vec![DoElement::Action(Box::new(SurfaceExpr::ident("do_work")))];

    let result = expect_ok(desugar_while(&SurfaceExpr::ident("cond"), &body));

    // Should be Lean.Loop.repeat (if cond then ... else ...)
    assert!(
        is_app_of(&result, "Lean.Loop.repeat"),
        "expected Lean.Loop.repeat, got {result:?}"
    );
    let args = app_args(&result).expect("should have args");
    assert_eq!(args.len(), 1);

    // The arg should be an if expression
    assert!(
        matches!(&args[0].expr, SurfaceExpr::If(_, _, _, _)),
        "repeat body should be an if expression"
    );
}

#[test]
fn test_terminal_action_is_identity() {
    // do expr
    let elements = vec![DoElement::Action(Box::new(SurfaceExpr::ident("result")))];

    let result = expect_ok(desugar_do_block(&elements));

    // Terminal action is just the expression itself
    assert!(
        is_ident(&result, "result"),
        "terminal action should be identity"
    );
}

#[test]
fn test_if_with_empty_else_uses_pure_unit() {
    // do if cond then return 1
    // (no else branch — empty else_branch vec)
    let elements = vec![DoElement::If {
        cond: Box::new(SurfaceExpr::ident("cond")),
        then_branch: vec![DoElement::Return(Box::new(SurfaceExpr::nat(1)))],
        else_branch: vec![],
    }];

    let result = expect_ok(desugar_do_block(&elements));

    // Else branch should be Pure.pure PUnit.unit
    if let SurfaceExpr::If(_, _, _, else_expr) = &result {
        assert!(
            is_app_of(else_expr, "Pure.pure"),
            "else branch should be Pure.pure, got {else_expr:?}"
        );
    } else {
        panic!("expected If, got {result:?}");
    }
}

#[test]
fn test_for_in_body_produces_yield_step() {
    // for x in xs do action
    let body = vec![DoElement::Action(Box::new(SurfaceExpr::ident("process")))];
    let result = expect_ok(desugar_for_in("x", &SurfaceExpr::ident("xs"), &body));

    // The step function body should end with Pure.pure (ForInStep.yield ())
    let args = app_args(&result).expect("ForIn.forIn should have args");
    if let SurfaceExpr::Lambda(_, _, step_body) = &args[2].expr {
        // step_body should be Bind.bind process (fun _ => Pure.pure (ForInStep.yield PUnit.unit))
        assert!(
            is_app_of(step_body, "Bind.bind"),
            "step body should bind, got {step_body:?}"
        );
    } else {
        panic!("expected lambda step function");
    }
}

#[test]
fn test_empty_for_body_fails() {
    let result = desugar_for_in("x", &SurfaceExpr::ident("xs"), &[]);
    assert!(result.is_err(), "empty for-in body should fail");
}

#[test]
fn test_empty_while_body_fails() {
    let result = desugar_while(&SurfaceExpr::ident("cond"), &[]);
    assert!(result.is_err(), "empty while body should fail");
}

#[test]
fn test_non_terminal_return_produces_pure() {
    // do return 5; action  (return is non-terminal, rest is unreachable)
    let elements = vec![
        DoElement::Return(Box::new(SurfaceExpr::nat(5))),
        DoElement::Action(Box::new(SurfaceExpr::ident("unreachable"))),
    ];

    let result = expect_ok(desugar_do_block(&elements));

    // Non-terminal return still produces Pure.pure 5 (rest is discarded)
    assert!(
        is_app_of(&result, "Pure.pure"),
        "non-terminal return should produce Pure.pure, got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// Tests: from_parser_do_elems conversion
// ---------------------------------------------------------------------------

#[test]
fn test_from_parser_bind_converts() {
    use crate::do_notation::from_parser_do_elems;
    use clean_parser::{Span, SurfaceBinder, SurfaceBinderInfo};

    let parser_elems = vec![clean_parser::DoElem::Bind(
        Span::dummy(),
        SurfaceBinder::new("x", None, SurfaceBinderInfo::Explicit),
        Box::new(SurfaceExpr::ident("action")),
    )];

    let converted = from_parser_do_elems(&parser_elems);
    assert_eq!(converted.len(), 1);
    assert!(
        matches!(&converted[0], DoElement::Bind { name: Some(n), .. } if n == "x"),
        "should convert to Bind with name x"
    );
}

#[test]
fn test_from_parser_wildcard_bind_becomes_none() {
    use crate::do_notation::from_parser_do_elems;
    use clean_parser::{Span, SurfaceBinder, SurfaceBinderInfo};

    let parser_elems = vec![clean_parser::DoElem::Bind(
        Span::dummy(),
        SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit),
        Box::new(SurfaceExpr::ident("action")),
    )];

    let converted = from_parser_do_elems(&parser_elems);
    assert!(
        matches!(&converted[0], DoElement::Bind { name: None, .. }),
        "wildcard binder should become None"
    );
}
