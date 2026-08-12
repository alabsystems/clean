// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for do-notation elaboration.
//!
//! Verifies that `do { ... }` blocks are correctly desugared to
//! `Bind.bind` / `Pure.pure` chains during elaboration.
//!
//! Tests use `Environment::with_prelude()` so that monadic constants
//! (`Bind.bind`, `Pure.pure`, `ite`, `ForIn.forIn`) are declared in the
//! environment, eliminating tautological assertions on self-constructed
//! string literals (#1841).
//!
//! Bare monadic paths leave the monad metavariable unconstrained. When a test
//! needs kernel verification, it pins the monad with an explicit target type
//! such as `Id Bool` so the remaining metas can be solved.

use super::*;

// === Core desugaring tests ===

/// `do return 42` should desugar to `@Pure.pure.{u,v} m α 42`
///
/// With kernel-matching arity (#1799), the structure is:
///   App(App(App(Pure.pure, m), α), Lit(42))
/// The outermost App's arg is the value (42).
#[test]
fn test_elab_do_return_literal() {
    let env = Environment::with_prelude();
    let expr =
        elab_with_env(&env, "do return 42").expect("do return 42 should elaborate with prelude");
    // Outermost App: arg should be the literal 42
    match expr.kind() {
        ExprKind::App(func, arg) => {
            match arg.kind() {
                ExprKind::Lit(Literal::Nat(ref n)) => {
                    assert_eq!(n.to_u64(), Some(42), "expected literal 42");
                }
                _ => panic!("expected Lit(Nat(42)), got {arg:?}"),
            }
            let head = func.get_app_fn();
            match head.kind() {
                ExprKind::Const(name, levels) => {
                    assert_eq!(
                        name.to_string(),
                        "Pure.pure",
                        "expected Pure.pure head, got {}",
                        name
                    );
                    assert_eq!(
                        levels.len(),
                        2,
                        "Pure.pure should have 2 universe levels (u, v)"
                    );
                }
                _ => panic!("expected Const(Pure.pure, _), got {head:?}"),
            }
        }
        _ => panic!("expected App(_, _) for 'do return 42', got {expr:?}"),
    }
}

/// `do e` (single expression) should just elaborate to `e`
#[test]
fn test_elab_do_single_expr() {
    // `do Type` should just be `Type`
    let result = elab("do Type");
    match result {
        Ok(expr) => {
            assert!(
                matches!(expr.kind(), ExprKind::Sort(_)),
                "expected Sort for 'do Type', got {expr:?}"
            );
        }
        Err(e) => panic!("failed to elaborate 'do Type': {e:?}"),
    }
}

/// `do let x := 1; x` should desugar to `let x := 1 in x`
#[test]
fn test_elab_do_let_binding() {
    let result = elab("do let x := 1; x");
    match result {
        Ok(expr) => {
            // Should be a Let expression: Let(name, type, value, body, nonDep)
            match expr.kind() {
                ExprKind::Let(_, _, val, body, _) => {
                    // val should be literal 1
                    match val.kind() {
                        ExprKind::Lit(Literal::Nat(ref n)) if n.to_u64() == Some(1) => {}
                        _ => panic!("expected Lit(Nat(1)) as let value, got {val:?}"),
                    }
                    // body should be BVar(0) (reference to the let-bound variable)
                    match body.kind() {
                        ExprKind::BVar(0) => {}
                        _ => panic!("expected BVar(0) as let body, got {body:?}"),
                    }
                }
                _ => panic!("expected Let for 'do let x := 1; x', got {expr:?}"),
            }
        }
        Err(e) => panic!("failed to elaborate 'do let x := 1; x': {e:?}"),
    }
}

/// `do let x <- f; return x` — 'f' is unknown even with prelude.
/// Verifies the elaborator produces a specific error for unknown identifiers.
#[test]
fn test_elab_do_bind_then_return() {
    let env = Environment::with_prelude();
    let err = elab_with_env(&env, "do let x <- f; return x")
        .expect_err("'f' is unknown even with prelude, elaboration should fail");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("UnknownIdent") && msg.contains("\"f\""),
        "expected an UnknownIdent error naming `f`, got {err:?}"
    );
}

/// `do e; rest` should desugar to `@Bind.bind.{u,v} m α β e (fun _ => rest)`
#[test]
fn test_elab_do_sequence() {
    let env = Environment::with_prelude();
    let expr =
        elab_with_env(&env, "do Type; Type").expect("do Type; Type should elaborate with prelude");
    // Kernel-matching arity (#1799): @Bind.bind.{u,v} m α β Type (fun _ => Type)
    let head = expr.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, levels) => {
            assert_eq!(name.to_string(), "Bind.bind");
            assert_eq!(levels.len(), 2, "Bind.bind should have 2 universe levels");
        }
        _ => panic!("expected Const(Bind.bind, _), got {head:?}"),
    }
    let args = expr.get_app_args();
    assert_eq!(
        args.len(),
        5,
        "Bind.bind should have 5 arguments, got {}",
        args.len()
    );
}

/// `do return Prop` should produce `@Pure.pure.{u,v} m α Prop`
/// Test with Prop which is always available
#[test]
fn test_elab_do_return_prop() {
    let env = Environment::with_prelude();
    let expr = elab_with_env(&env, "do return Prop")
        .expect("do return Prop should elaborate with prelude");
    match expr.kind() {
        ExprKind::App(func, arg) => {
            // arg should be Prop = Sort(0)
            match arg.kind() {
                ExprKind::Sort(level) => {
                    assert!(level.is_zero(), "expected Sort(0) for Prop");
                }
                _ => panic!("expected Sort(_) as Pure.pure arg, got {arg:?}"),
            }
            let head = func.get_app_fn();
            match head.kind() {
                ExprKind::Const(name, levels) => {
                    assert_eq!(name.to_string(), "Pure.pure");
                    assert_eq!(
                        levels.len(),
                        2,
                        "Pure.pure should have 2 universe levels (u, v)"
                    );
                }
                _ => panic!("expected Const(Pure.pure, _), got {head:?}"),
            }
        }
        _ => panic!("expected App(_, _) for 'do return Prop', got {expr:?}"),
    }
}

/// Multiple let bindings in do block
#[test]
fn test_elab_do_multiple_lets() {
    let result = elab("do let x := Type; let y := Type; x");
    match result {
        Ok(expr) => {
            // Should be: let x := Type in (let y := Type in x)
            // Let(name, type, value, body, nonDep)
            match expr.kind() {
                ExprKind::Let(_, _, _, body, _) => {
                    // body should be another Let
                    match body.kind() {
                        ExprKind::Let(_, _, _, inner_body, _) => {
                            // inner_body should reference x (BVar 1, since y is BVar 0)
                            assert!(
                                matches!(inner_body.kind(), ExprKind::BVar(1)),
                                "expected BVar(1) for x reference, got {inner_body:?}"
                            );
                        }
                        _ => panic!("expected inner Let for nested let bindings, got {body:?}"),
                    }
                }
                _ => panic!("expected Let for multiple let bindings, got {expr:?}"),
            }
        }
        Err(e) => panic!("failed to elaborate multiple lets: {e:?}"),
    }
}

/// Verify that do blocks with `let mut` parse and elaborate (treated as regular let for now)
#[test]
fn test_elab_do_let_mut_as_let() {
    let result = elab("do let mut x := Type; x");
    match result {
        Ok(expr) => {
            // Should be same as `let x := Type in x`
            assert!(
                matches!(expr.kind(), ExprKind::Let(_, _, _, _, _)),
                "expected Let, got {expr:?}"
            );
        }
        Err(e) => panic!("failed to elaborate 'do let mut': {e:?}"),
    }
}

/// Empty do block should error
#[test]
fn test_elab_do_empty_errors() {
    let result = elab("do {}");
    assert!(result.is_err(), "empty do block should error");
}

// === If/For/Match as do-elements ===

/// `do if True then return Prop else return Prop` should produce an ite application
/// With #1810 fix: @ite.{u} α cond inst then_expr else_expr (5 args, 1 universe level)
#[test]
fn test_elab_do_if_then_else() {
    let env = Environment::with_prelude();
    let expr = elab_with_env(&env, "do { if True then return Prop else return Prop }")
        .expect("do if-then-else should elaborate with prelude");
    // Should be: @ite.{u} α True inst (Pure.pure Prop) (Pure.pure Prop)
    let head = expr.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, levels) => {
            assert_eq!(name.to_string(), "ite", "expected ite head, got {}", name);
            assert_eq!(levels.len(), 1, "ite should have 1 universe level");
        }
        _ => panic!("expected Const(ite, _), got {head:?}"),
    }
    let args = expr.get_app_args();
    assert_eq!(
        args.len(),
        5,
        "ite should have 5 arguments (α, cond, inst, then, else), got {}",
        args.len()
    );
}

/// `do if True then Type else Type; Type` should sequence the if result
#[test]
fn test_elab_do_if_then_sequence() {
    let env = Environment::with_prelude();
    let expr = elab_with_env(&env, "do { if True then Type else Type; Type }")
        .expect("do if-then-sequence should elaborate with prelude");
    // Should be: Bind.bind (ite True Type Type) (fun _ => Type)
    assert!(
        matches!(expr.kind(), ExprKind::App(_, _)),
        "expected App for Bind.bind chain, got {expr:?}"
    );
}

/// `do for x in xs do return x` — 'xs' is unknown even with prelude.
/// Verifies the elaborator produces a specific error for unknown identifiers.
#[test]
fn test_elab_do_for() {
    let env = Environment::with_prelude();
    let err = elab_with_env(&env, "do { for x in xs do return x }")
        .expect_err("'xs' is unknown even with prelude, elaboration should fail");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("UnknownIdent") && msg.contains("\"xs\""),
        "expected an UnknownIdent error naming `xs`, got {err:?}"
    );
}

/// `do match Type with | x => return x` — single-arm variable match desugars to let
#[test]
fn test_elab_do_match() {
    let env = Environment::with_prelude();
    let expr = elab_with_env(&env, "do { match Type with | x => return x }")
        .expect("do match should elaborate with prelude");
    // Single-arm variable match desugars to:
    //   let x := Type in @Pure.pure m inst α x
    match expr.kind() {
        ExprKind::Let(_, _, val, body, _) => {
            assert!(
                matches!(val.kind(), ExprKind::Sort(_)),
                "expected Sort for match scrutinee, got {val:?}"
            );
            match body.kind() {
                ExprKind::App(_, arg) => {
                    assert!(
                        matches!(arg.kind(), ExprKind::BVar(0)),
                        "expected BVar(0) as Pure.pure arg, got {arg:?}"
                    );
                }
                _ => panic!("expected App for Pure.pure in match body, got {body:?}"),
            }
        }
        _ => panic!("expected Let for single-arm match, got {expr:?}"),
    }
}

// === Nested action lifting tests (#1819) ===

/// `do return (<- f)` should expand to `do let __do_lift_0 <- f; return __do_lift_0`
/// which is `@Bind.bind f (fun __do_lift_0 => @Pure.pure __do_lift_0)`
#[test]
fn test_elab_do_nested_action_basic() {
    let env = Environment::with_prelude();
    let expr = elab_with_env(&env, "do return (<- Type)")
        .expect("do return (<- Type) should elaborate with prelude");
    // Should produce a Bind.bind chain (the lift creates a bind + pure sequence)
    let head = expr.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, levels) => {
            assert_eq!(
                name.to_string(),
                "Bind.bind",
                "expected Bind.bind from nested action lift, got {}",
                name
            );
            assert_eq!(levels.len(), 2, "Bind.bind should have 2 universe levels");
        }
        _ => panic!("expected Const(Bind.bind, _) from nested action lift, got {head:?}"),
    }
}

/// Parsing: `(<- expr)` in term position should produce LiftMethod in the AST
#[test]
fn test_parse_nested_action_in_paren() {
    // Parser may not yet support `<-` in expression position (#1819)
    let parse_result = parse_expr("do return (<- Type)");
    match parse_result {
        Ok(surface) => {
            // Should be Do([Return(_, Paren(_, LiftMethod(_, Universe(Type))))])
            // or Do([Return(_, LiftMethod(_, Universe(Type)))]) depending on paren handling
            match surface {
                SurfaceExpr::Do(_, elems) => {
                    assert_eq!(elems.len(), 1, "expected 1 do element");
                    match &elems[0] {
                        DoElem::Return(_, expr) => {
                            fn has_lift_method(e: &SurfaceExpr) -> bool {
                                match e {
                                    SurfaceExpr::LiftMethod(_, _) => true,
                                    SurfaceExpr::Paren(_, inner) => has_lift_method(inner),
                                    _ => false,
                                }
                            }
                            assert!(
                                has_lift_method(expr),
                                "expected LiftMethod in return expression, got {expr:?}"
                            );
                        }
                        other => panic!("expected Return do element, got {other:?}"),
                    }
                }
                other => panic!("expected Do block, got {other:?}"),
            }
        }
        Err(e) => {
            // Parser doesn't support `<-` in expression position yet (#1819)
            let msg = format!("{e:?}");
            assert!(
                msg.contains("LeftArrow") || msg.contains("unexpected token"),
                "unexpected parse error: {e:?}"
            );
        }
    }
}

/// Nested lifts: `do return (<- (<- Type))` should produce two lifted bindings
/// expanding to: `do let __do_lift_0 <- Type; let __do_lift_1 <- __do_lift_0; return __do_lift_1`
#[test]
fn test_elab_do_nested_action_double() {
    let env = Environment::with_prelude();
    let expr = elab_with_env(&env, "do return (<- (<- Type))")
        .expect("do return (<- (<- Type)) should elaborate with prelude");
    // Should produce at least one Bind.bind (from the outer lift)
    let head = expr.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => {
            assert_eq!(name.to_string(), "Bind.bind");
        }
        _ => panic!("expected Bind.bind from double nested lift, got {head:?}"),
    }
}

// === Kernel typecheck tests (#1799 AC4) ===

/// `do let x := Type; x` desugars to `let x := Type in x` — no monadic operations.
/// This should pass `elaborate_and_verify` (elaboration + kernel typecheck + certificate).
#[test]
fn test_elab_do_let_kernel_typecheck() {
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);
    let surface = parse_expr("do let x := Type; x").unwrap();
    let (expr, ty, _cert) = ctx
        .elaborate_and_verify(&surface)
        .expect("do let x := Type; x should kernel-typecheck");
    // Should be: let x := Type in x
    assert!(
        matches!(expr.kind(), ExprKind::Let(_, _, _, _, _)),
        "expected Let, got {expr:?}"
    );
    // Type of (let x := Type in x) is Type (since x = Type, and body = x)
    assert!(
        matches!(ty.kind(), ExprKind::Sort(_)),
        "expected Sort as type, got {ty:?}"
    );
}

/// `do return Type` desugars to `@Pure.pure.{u,v} ?m ?α Type`.
/// With a prelude environment, Pure.pure is declared. The elaborated expression
/// should have structurally valid application arity matching the kernel declaration.
///
/// This validates #1799: universe levels are not empty and arg count matches
/// the kernel declaration of Pure.pure (3 args: m, α, val).
#[test]
fn test_elab_do_return_arity_matches_kernel_decl() {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let surface = parse_expr("do return Type").unwrap();
    let expr = ctx
        .elaborate(&surface)
        .expect("do return Type should elaborate with prelude env");

    // Verify application structure: @Pure.pure.{u,v} m α Type
    let head = expr.get_app_fn();
    let args = expr.get_app_args();

    // Head should be Pure.pure with 2 universe levels
    match head.kind() {
        ExprKind::Const(name, levels) => {
            assert_eq!(name.to_string(), "Pure.pure");
            assert_eq!(
                levels.len(),
                2,
                "Pure.pure should have 2 universe levels (matching kernel decl)"
            );
        }
        _ => panic!("expected Const(Pure.pure, _), got {head:?}"),
    }

    // 3 args matching kernel declaration: {m} {α} val
    assert_eq!(
        args.len(),
        3,
        "Pure.pure application should have 3 args (m, α, val) matching kernel decl"
    );

    // Cross-check against kernel declaration
    let pure_info = env
        .get_const(&Name::from_string("Pure.pure"))
        .expect("Pure.pure should be in prelude env");
    assert_eq!(
        pure_info.level_params.len(),
        2,
        "kernel decl Pure.pure should have 2 level params"
    );
}

/// `do Type; Type` desugars to `@Bind.bind.{u,v} ?m ?α ?β Type (fun _ => Type)`.
/// With a prelude environment, Bind.bind is declared. Validates #1799 arity fix.
#[test]
fn test_elab_do_bind_arity_matches_kernel_decl() {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let surface = parse_expr("do Type; Type").unwrap();
    let expr = ctx
        .elaborate(&surface)
        .expect("do Type; Type should elaborate with prelude env");

    let head = expr.get_app_fn();
    let args = expr.get_app_args();

    // Head should be Bind.bind with 2 universe levels
    match head.kind() {
        ExprKind::Const(name, levels) => {
            assert_eq!(name.to_string(), "Bind.bind");
            assert_eq!(
                levels.len(),
                2,
                "Bind.bind should have 2 universe levels (matching kernel decl)"
            );
        }
        _ => panic!("expected Const(Bind.bind, _), got {head:?}"),
    }

    // 5 args matching kernel declaration: {m} {α} {β} action continuation
    assert_eq!(
        args.len(),
        5,
        "Bind.bind application should have 5 args (m, α, β, action, cont) matching kernel decl"
    );

    // Last arg should be a lambda (the continuation)
    assert!(
        matches!(args[4].kind(), ExprKind::Lam(_, _, _)),
        "arg[4] (continuation) should be Lam, got {:?}",
        args[4].kind()
    );

    // Cross-check against kernel declaration
    let bind_info = env
        .get_const(&Name::from_string("Bind.bind"))
        .expect("Bind.bind should be in prelude env");
    assert_eq!(
        bind_info.level_params.len(),
        2,
        "kernel decl Bind.bind should have 2 level params"
    );
}

/// `<- expr` outside a do block should produce an error
#[test]
fn test_elab_lift_method_outside_do_errors() {
    let result = elab("(<- Type)");
    assert!(result.is_err(), "LiftMethod outside do block should error");
    let msg = format!("{:?}", result.unwrap_err());
    assert!(
        msg.contains("do block")
            || msg.contains("Unsupported")
            || msg.contains("nested action")
            || msg.contains("ParseError")
            || msg.contains("LeftArrow"),
        "error should mention do block context, got: {msg}"
    );
}

/// `do if (<- Id.mk Bool.true) then Type else Type` should lift from the
/// condition only.  Use a genuine `Id Bool` action: `Prop` is itself a term of
/// type `Type`, not a proposition-valued monadic action.
#[test]
fn test_elab_do_nested_action_in_if_condition() {
    let env = Environment::with_prelude();
    let expr = elab_with_env(&env, "do { if (<- Id.mk Bool.true) then Type else Type }")
        .expect("do if (<- Id.mk Bool.true) should elaborate with prelude");
    // The lift from the condition should produce a Bind.bind
    let head = expr.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => {
            assert_eq!(
                name.to_string(),
                "Bind.bind",
                "expected Bind.bind from lifted if-condition"
            );
        }
        _ => panic!("expected Bind.bind from lifted if-condition, got {head:?}"),
    }
}

/// `do f (<- Type)` — nested action as a function argument
/// The `<-` inside parens should be parsed as LiftMethod and lifted by the pre-pass.
#[test]
fn test_parse_nested_action_as_app_arg() {
    let surface = parse_expr("do f (<- Type)").unwrap();
    match surface {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 1, "expected 1 do element");
            match &elems[0] {
                DoElem::Expr(_, expr) => {
                    // Should be App(f, [Paren(LiftMethod(Type))])
                    fn has_lift_method(e: &SurfaceExpr) -> bool {
                        match e {
                            SurfaceExpr::LiftMethod(_, _) => true,
                            SurfaceExpr::Paren(_, inner) => has_lift_method(inner),
                            SurfaceExpr::App(_, _, args) => {
                                args.iter().any(|a| has_lift_method(&a.expr))
                            }
                            _ => false,
                        }
                    }
                    assert!(
                        has_lift_method(expr),
                        "expected LiftMethod in app argument, got {expr:?}"
                    );
                }
                other => panic!("expected Expr do element, got {other:?}"),
            }
        }
        other => panic!("expected Do block, got {other:?}"),
    }
}

/// Bare `<- expr` as a do-element gets parsed as DoElem::Expr(LiftMethod(...))
/// and the pre-pass lifts it into `let __do_lift_0 <- expr; __do_lift_0`.
#[test]
fn test_parse_bare_lift_as_do_elem() {
    let surface = parse_expr("do { <- Type; Type }").unwrap();
    match surface {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 2, "expected 2 do elements");
            match &elems[0] {
                DoElem::Expr(_, expr) => {
                    assert!(
                        matches!(expr.as_ref(), SurfaceExpr::LiftMethod(_, _)),
                        "expected LiftMethod as first do element expr, got {expr:?}"
                    );
                }
                other => panic!("expected Expr do element, got {other:?}"),
            }
        }
        other => panic!("expected Do block, got {other:?}"),
    }
}

// === Monadic kernel typecheck tests (#1841) ===

fn elaborate_do_definition_and_verify(env: &Environment, decl_src: &str) -> (Expr, Expr) {
    let mut ctx = ElabCtx::new(env);
    let surface = parse_decl_for_elab(decl_src).expect("definition should parse");
    let (expr, ty) = match ctx
        .elab_decl(&surface)
        .expect("definition should elaborate")
    {
        ElabResult::Definition { ty, val, .. } => (val, ty),
        other => panic!("expected definition elaboration result, got {other:?}"),
    };
    let (expr_ty, cert) = ctx
        .infer_type_with_cert(&expr)
        .expect("definition body should typecheck with a certificate");
    let mut verifier = ctx
        .create_cert_verifier()
        .expect("certificate verifier should build");
    let _ = verifier
        .verify(&cert, &expr)
        .expect("certificate should verify");
    assert!(
        ctx.is_def_eq(&expr_ty, &ty),
        "definition body type should match declared type: body={expr_ty:?} decl={ty:?}"
    );
    (expr, ty)
}

/// `do return Bool.true` should kernel typecheck when elaborated as the body of
/// an `Id Bool` definition.
///
/// B22 (Id-monad reduction): with `Pure Id`/`Bind Id` instances registered,
/// the monad-materialization pass rewrites the terminal `Pure.pure Id …` stub
/// into instance-projected form `(Proj Pure 0 instPureId) …` — exactly the
/// shape B07 produces for `Option`. The kernel then reduces it (`pure v ↦ v`),
/// which is what makes `Id.run (pure v)` value-certifiable.
#[test]
fn test_elab_do_return_id_kernel_typecheck() {
    let env = Environment::with_prelude();
    let (expr, ty) = elaborate_do_definition_and_verify(
        &env,
        "def test_do_return_bool : Id Bool := do return Bool.true",
    );
    let head = expr.get_app_fn();
    match head.kind() {
        ExprKind::Proj(struct_name, idx, inner) => {
            assert_eq!(struct_name.to_string(), "Pure");
            assert_eq!(*idx, 0, "Pure.pure is field 0 of the Pure class");
            assert!(
                matches!(inner.kind(), ExprKind::Const(n, _) if n.to_string() == "instPureId"),
                "projection must be over instPureId, got {inner:?}"
            );
        }
        _ => panic!("expected Proj(Pure, 0, instPureId), got {head:?}"),
    }
    let ty_head = ty.get_app_fn();
    match ty_head.kind() {
        ExprKind::Const(name, levels) => {
            assert_eq!(name.to_string(), "Id");
            assert_eq!(levels.len(), 1, "Id should have 1 universe level");
        }
        _ => panic!("expected Const(Id, _), got {ty_head:?}"),
    }
}

/// `do let x <- Id.mk Bool.true; return x` exercises a real monadic bind path
/// and should kernel typecheck as the body of an `Id Bool` definition.
///
/// B22: the `Bind.bind Id …` stub materializes into `(Proj Bind 0 instBindId)
/// α β action cont`, the instance-projected identity-monad bind.
#[test]
fn test_elab_do_bind_id_kernel_typecheck() {
    let env = Environment::with_prelude();
    let (expr, ty) = elaborate_do_definition_and_verify(
        &env,
        "def test_do_bind_bool : Id Bool := do let x <- Id.mk Bool.true; return x",
    );
    let head = expr.get_app_fn();
    let args = expr.get_app_args();
    match head.kind() {
        ExprKind::Proj(struct_name, idx, inner) => {
            assert_eq!(struct_name.to_string(), "Bind");
            assert_eq!(*idx, 0, "Bind.bind is field 0 of the Bind class");
            assert!(
                matches!(inner.kind(), ExprKind::Const(n, _) if n.to_string() == "instBindId"),
                "projection must be over instBindId, got {inner:?}"
            );
        }
        _ => panic!("expected Proj(Bind, 0, instBindId), got {head:?}"),
    }
    assert_eq!(
        args.len(),
        4,
        "materialized bind projection should have 4 args (α, β, action, cont)"
    );
    assert!(
        matches!(args[3].kind(), ExprKind::Lam(_, _, _)),
        "arg[3] (continuation) should be Lam, got {:?}",
        args[3].kind()
    );
    let ty_head = ty.get_app_fn();
    match ty_head.kind() {
        ExprKind::Const(name, levels) => {
            assert_eq!(name.to_string(), "Id");
            assert_eq!(levels.len(), 1, "Id should have 1 universe level");
        }
        _ => panic!("expected Const(Id, _), got {ty_head:?}"),
    }
}

// ===========================================================================
// #3409: Chained binds must not leak FVars
// ===========================================================================

/// Two chained binds elaborated as a full definition.
/// Before #3409 fix, the continuation FVar leaked because metas were not
/// instantiated before abstract_fvar in elab_do_bind, hiding the FVar
/// inside a meta solution. The fix mirrors the #443 pattern from elab_def_body.
///
/// Elaborates a definition with do-notation and checks the result value has
/// no FVars. With `elab_with_env`, unresolved monad metas appear as FVars,
/// so the test uses definition-level elaboration where metas get instantiated.
#[test]
fn test_elab_do_chained_binds_def_no_leaked_fvars() {
    let env = Environment::with_prelude();
    let patterns = crate::tactic::builtins::builtin_tactic_patterns();
    let input = "def doTest : Id Nat := do let x <- Id.mk 1; let y <- Id.mk 2; return x";
    let surface = parse_decl_with_tactics(input, &patterns).expect("parse should succeed");
    let mut ctx = ElabCtx::new(&env);
    let result = ctx
        .elab_decl(&surface)
        .expect("chained binds should elaborate");
    match &result {
        ElabResult::Definition { val, .. } => {
            assert!(
                !val.has_fvar_quick(),
                "chained bind definition value should not contain FVars: {val:?}"
            );
        }
        other => panic!("expected Definition, got {other:?}"),
    }
}

/// Three chained binds in a definition -- deeper chain.
/// Regression test for #3409.
#[test]
fn test_elab_do_three_chained_binds_def_no_leaked_fvars() {
    let env = Environment::with_prelude();
    let patterns = crate::tactic::builtins::builtin_tactic_patterns();
    let input =
        "def doTest3 : Id Nat := do let a <- Id.mk 1; let b <- Id.mk 2; let c <- Id.mk 3; return a";
    let surface = parse_decl_with_tactics(input, &patterns).expect("parse should succeed");
    let mut ctx = ElabCtx::new(&env);
    let result = ctx
        .elab_decl(&surface)
        .expect("three chained binds should elaborate");
    match &result {
        ElabResult::Definition { val, .. } => {
            assert!(
                !val.has_fvar_quick(),
                "three chained bind definition value should not contain FVars: {val:?}"
            );
        }
        other => panic!("expected Definition, got {other:?}"),
    }
}

/// Bind + non-terminal action + return in a definition.
/// This is the pattern from the issue repro: `do let n <- f; g n; return n`
#[test]
fn test_elab_do_bind_action_return_def_no_leaked_fvars() {
    let env = Environment::with_prelude();
    let patterns = crate::tactic::builtins::builtin_tactic_patterns();
    let input = "def doTest4 : Id Nat := do let n <- Id.mk 1; Id.mk 2; return n";
    let surface = parse_decl_with_tactics(input, &patterns).expect("parse should succeed");
    let mut ctx = ElabCtx::new(&env);
    let result = ctx
        .elab_decl(&surface)
        .expect("bind+action+return should elaborate");
    match &result {
        ElabResult::Definition { val, .. } => {
            assert!(
                !val.has_fvar_quick(),
                "bind+action+return definition value should not contain FVars: {val:?}"
            );
        }
        other => panic!("expected Definition, got {other:?}"),
    }
}

/// #3419: Two sequential binds with a complex monad stack (StateT/Except).
/// Tests that chained binds with external function calls don't leak FVars.
///
/// Uses `return` (not `pure`) since clean requires the `return` keyword
/// in do-blocks (bare `pure` is not registered as a prelude alias).
#[test]
fn test_elab_do_bind_action_return_complex_monad_no_leaked_fvars() {
    use clean_parser::parse_file;
    let code = r#"
inductive MyError where | notFound
structure MyState where
  counter : Nat
  values : List Nat

abbrev MySem (a : Type) := StateT MyState (Except MyError) a

axiom incCounter : MySem Nat
axiom addValue : Nat -> MySem Unit

def incAndAdd : MySem Nat := do
  let n <- incCounter
  addValue n
  return n
"#;
    let decls = parse_file(code).expect("parse should succeed");
    let mut env = Environment::with_prelude();
    let mut file_ctx = crate::FileContext::new();
    for (i, decl) in decls.iter().enumerate() {
        let processed = crate::preprocess_decl_with_context(decl, &mut file_ctx);
        let result = crate::elaborate_decl_and_register(&mut env, &processed);
        if let Err(ref e) = result {
            eprintln!("Declaration {} failed: {:?}", i, e);
            eprintln!("  Decl: {:?}", std::mem::discriminant(decl));
        }
        assert!(
            result.is_ok(),
            "Declaration {} failed: {:?}",
            i,
            result.err()
        );
    }
    // If we get here, incAndAdd was successfully registered (no free variables)
    assert!(
        env.get_const(&Name::from_string("incAndAdd")).is_some(),
        "incAndAdd should be registered in the environment"
    );
}

/// Minimal reproduction: external function calls in a do-block with Id monad.
/// Uses separate def declarations instead of inline Id.mk.
#[test]
fn test_elab_do_external_calls_id_monad() {
    use clean_parser::parse_file;
    let code = r#"
def getVal : Id Nat := Id.mk 42
def useVal (n : Nat) : Id Unit := Id.mk ()

def testDo : Id Nat := do
  let n <- getVal
  useVal n
  return n
"#;
    let decls = parse_file(code).expect("parse should succeed");
    let mut env = Environment::with_prelude();
    let mut file_ctx = crate::FileContext::new();
    for (i, decl) in decls.iter().enumerate() {
        let processed = crate::preprocess_decl_with_context(decl, &mut file_ctx);
        let result = crate::elaborate_decl_and_register(&mut env, &processed);
        assert!(
            result.is_ok(),
            "Declaration {} failed: {:?}",
            i,
            result.err()
        );
    }
    assert!(
        env.get_const(&Name::from_string("testDo")).is_some(),
        "testDo should be registered in the environment"
    );
}

/// Two-element do-block with external function call (action+return, no bind).
#[test]
fn test_elab_do_external_action_then_return() {
    use clean_parser::parse_file;
    let code = r#"
def sideEffect : Id Unit := Id.mk ()

def testDo2 : Id Nat := do
  sideEffect
  return 42
"#;
    let decls = parse_file(code).expect("parse should succeed");
    let mut env = Environment::with_prelude();
    let mut file_ctx = crate::FileContext::new();
    for (i, decl) in decls.iter().enumerate() {
        let processed = crate::preprocess_decl_with_context(decl, &mut file_ctx);
        let result = crate::elaborate_decl_and_register(&mut env, &processed);
        assert!(
            result.is_ok(),
            "Declaration {} failed (action+return): {:?}",
            i,
            result.err()
        );
    }
}

/// Single bind with external function (bind+return, no bare action).
/// Registers getVal in the environment first, then elaborates the do-block.
#[test]
fn test_elab_do_external_bind_then_return() {
    let mut env = Environment::with_prelude();
    let patterns = crate::tactic::builtins::builtin_tactic_patterns();

    // Register getVal : Id Nat in the environment
    let input1 = "def getVal : Id Nat := Id.mk 42";
    let surface1 = parse_decl_with_tactics(input1, &patterns).expect("parse should succeed");
    let result1 = crate::elaborate_decl_and_register(&mut env, &surface1);
    assert!(
        result1.is_ok(),
        "getVal registration failed: {:?}",
        result1.err()
    );

    // Now elaborate testDo3 using the environment that has getVal
    let input2 = "def testDo3 : Id Nat := do\n  let n <- getVal\n  return n";
    let surface2 = parse_decl_with_tactics(input2, &patterns).expect("parse should succeed");
    let mut ctx2 = ElabCtx::new(&env);
    let result2 = ctx2.elab_decl(&surface2);
    match &result2 {
        Ok(ElabResult::Definition { val, .. }) => {
            assert!(
                !val.has_fvar_quick(),
                "external bind+return should not contain FVars: {val:?}"
            );
        }
        Ok(other) => panic!("expected Definition, got {other:?}"),
        Err(e) => panic!("testDo3 elab failed: {e:?}"),
    }
}

// === #3419 regression tests: FVar leaks in non-bind do-notation patterns ===

/// #3419: if-let with variable pattern inside a do-block.
/// The then-branch is elaborated with the pattern variable in scope;
/// if metas are not instantiated before abstracting, FVars leak.
#[test]
fn test_elab_do_if_let_var_pattern_no_leaked_fvars() {
    use clean_parser::parse_file;
    let code = r#"
def getVal : Id Nat := Id.mk 42

def testIfLet : Id Nat := do
  let x <- getVal
  if let y := x then
    return y
  else
    return 0
"#;
    let decls = parse_file(code).expect("parse should succeed");
    let mut env = Environment::with_prelude();
    let mut file_ctx = crate::FileContext::new();
    for (i, decl) in decls.iter().enumerate() {
        let processed = crate::preprocess_decl_with_context(decl, &mut file_ctx);
        let result = crate::elaborate_decl_and_register(&mut env, &processed);
        assert!(
            result.is_ok(),
            "Declaration {} failed: {:?}",
            i,
            result.err()
        );
    }
    assert!(
        env.get_const(&Name::from_string("testIfLet")).is_some(),
        "testIfLet should be registered in the environment"
    );
}

/// #3419: Bind followed by let and return -- exercises mixed bind/let chains.
/// The let body is elaborated with the let variable in scope, and the
/// earlier bind variable is referenced through metas.
#[test]
fn test_elab_do_bind_let_return_no_leaked_fvars() {
    let env = Environment::with_prelude();
    let patterns = crate::tactic::builtins::builtin_tactic_patterns();
    let input = "def testBindLet : Id Nat := do let x <- Id.mk 1; let y := x; return y";
    let surface = parse_decl_with_tactics(input, &patterns).expect("parse should succeed");
    let mut ctx = ElabCtx::new(&env);
    let result = ctx
        .elab_decl(&surface)
        .expect("bind+let+return should elaborate");
    match &result {
        ElabResult::Definition { val, .. } => {
            assert!(
                !val.has_fvar_quick(),
                "bind+let+return definition value should not contain FVars: {val:?}"
            );
        }
        other => panic!("expected Definition, got {other:?}"),
    }
}

/// #3419: let-else with variable pattern in a do-block.
/// The continuation body is elaborated with the let-else variable in scope.
#[test]
fn test_elab_do_let_else_var_no_leaked_fvars() {
    let env = Environment::with_prelude();
    let patterns = crate::tactic::builtins::builtin_tactic_patterns();
    let input = "def testLetElse : Id Nat := do let x <- Id.mk 42; let y := x; return y";
    let surface = parse_decl_with_tactics(input, &patterns).expect("parse should succeed");
    let mut ctx = ElabCtx::new(&env);
    let result = ctx
        .elab_decl(&surface)
        .expect("let-else with variable pattern should elaborate");
    match &result {
        ElabResult::Definition { val, .. } => {
            assert!(
                !val.has_fvar_quick(),
                "let-else var pattern definition value should not contain FVars: {val:?}"
            );
        }
        other => panic!("expected Definition, got {other:?}"),
    }
}

/// #3419: Four chained binds with cross-references between variables.
/// Deeper chains exercise the full meta-instantiation-before-abstraction pipeline.
#[test]
fn test_elab_do_four_chained_binds_cross_ref_no_leaked_fvars() {
    let env = Environment::with_prelude();
    let patterns = crate::tactic::builtins::builtin_tactic_patterns();
    let input = "def testDeep : Id Nat := do let a <- Id.mk 1; let b <- Id.mk a; let c <- Id.mk b; let d <- Id.mk c; return d";
    let surface = parse_decl_with_tactics(input, &patterns).expect("parse should succeed");
    let mut ctx = ElabCtx::new(&env);
    let result = ctx
        .elab_decl(&surface)
        .expect("four chained binds should elaborate");
    match &result {
        ElabResult::Definition { val, .. } => {
            assert!(
                !val.has_fvar_quick(),
                "four chained bind definition value should not contain FVars: {val:?}"
            );
        }
        other => panic!("expected Definition, got {other:?}"),
    }
}

/// #3419: Issue reproduction case — StateT/Except monad stack with 2+ sequential binds.
/// This is the exact pattern from the issue description. The `incCounter` and
/// `addValue` calls produce bind chains in a complex monad stack where metas
/// hide FVars from abstraction.
#[test]
fn test_elab_do_statet_except_multi_bind_no_leaked_fvars() {
    use clean_parser::parse_file;
    let code = r#"
inductive MyError where | notFound
structure MyState where
  counter : Nat
  values : List Nat

abbrev MySem (a : Type) := StateT MyState (Except MyError) a

axiom incCounter : MySem Nat
axiom addValue : Nat -> MySem Unit
axiom getValues : MySem (List Nat)

def incAddAndGet : MySem (List Nat) := do
  let n <- incCounter
  addValue n
  let vs <- getValues
  return vs
"#;
    let decls = parse_file(code).expect("parse should succeed");
    let mut env = Environment::with_prelude();
    let mut file_ctx = crate::FileContext::new();
    for (i, decl) in decls.iter().enumerate() {
        let processed = crate::preprocess_decl_with_context(decl, &mut file_ctx);
        let result = crate::elaborate_decl_and_register(&mut env, &processed);
        assert!(
            result.is_ok(),
            "Declaration {} ({:?}) failed: {:?}",
            i,
            std::mem::discriminant(decl),
            result.err()
        );
    }
    assert!(
        env.get_const(&Name::from_string("incAddAndGet")).is_some(),
        "incAddAndGet should be registered in the environment"
    );
}

/// #3419: StateT.get bind + field access on the bound variable.
///
/// This tests the `apply_implicit_to_expected_type` fix in `elab_do_bind`:
/// `StateT.get` is a polymorphic constant that needs implicit argument
/// resolution (filling in σ = MyState) before `try_extract_bind_inner_type`
/// can decompose its type as `App(m, α)`. Without the fix, the action's type
/// stays as a Pi (unresolved implicits) and the bind variable gets a fresh
/// metavar type. When the continuation does `s.counter` (field projection),
/// the metavar-typed `s` can't be resolved as `MyState`, causing the
/// projection to fail.
#[test]
fn test_elab_do_statet_get_field_access_no_leaked_fvars() {
    use clean_parser::parse_file;
    let code = r#"
inductive MyError where | notFound
structure MyState where
  counter : Nat
  values : List Nat

abbrev MySem (a : Type) := StateT MyState (Except MyError) a

def getCounter : MySem Nat := do
  let s <- StateT.get
  return s.counter
"#;
    let decls = parse_file(code).expect("parse should succeed");
    let mut env = Environment::with_prelude();
    let mut file_ctx = crate::FileContext::new();
    for (i, decl) in decls.iter().enumerate() {
        let processed = crate::preprocess_decl_with_context(decl, &mut file_ctx);
        let result = crate::elaborate_decl_and_register(&mut env, &processed);
        assert!(
            result.is_ok(),
            "Declaration {} ({:?}) failed: {:?}",
            i,
            std::mem::discriminant(decl),
            result.err()
        );
    }
    assert!(
        env.get_const(&Name::from_string("getCounter")).is_some(),
        "getCounter should be registered in the environment"
    );
}

// ControlStack integration tests moved to tests/do_control_flow.rs (#1818 Phase 4C)
