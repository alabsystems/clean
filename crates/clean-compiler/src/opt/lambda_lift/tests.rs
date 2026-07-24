// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::analysis::code_references_fvar;
use super::remap::{remap_fvars_in_code, remap_fvars_in_expr};
use super::*;
use crate::lcnf::Param;
use clean_kernel::expr::{ExprKind, ZFCSetExpr};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn nat_type() -> Expr {
    Expr::const_str("Nat")
}

fn bool_type() -> Expr {
    Expr::const_str("Bool")
}

fn expr_fvar(n: u64) -> Expr {
    Expr::fvar(fvar(n))
}

fn remap_pairs(pairs: &[(u64, u64)]) -> HashMap<FVarId, FVarId> {
    pairs
        .iter()
        .map(|(from, to)| (fvar(*from), fvar(*to)))
        .collect()
}

// ────────────────────────────────────────────────────────────────────────
// Free variable analysis tests
// ────────────────────────────────────────────────────────────────────────

#[test]
fn test_free_vars_return() {
    // return x
    let code = Code::ret(fvar(0));
    let bound = HashSet::new();
    let free = free_vars_in_code(&code, &bound);

    assert!(free.contains(&fvar(0)), "x should be free");
}

#[test]
fn test_free_vars_return_bound() {
    // x is bound, return x
    let code = Code::ret(fvar(0));
    let mut bound = HashSet::new();
    bound.insert(fvar(0));
    let free = free_vars_in_code(&code, &bound);

    assert!(free.is_empty(), "x is bound, should not be free");
}

#[test]
fn test_free_vars_let_binds() {
    // let y := x
    // return y
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("y"),
            nat_type(),
            LetValue::FVar {
                fvar: fvar(0),
                args: vec![],
            },
        ),
        Code::ret(fvar(1)),
    );
    let bound = HashSet::new();
    let free = free_vars_in_code(&code, &bound);

    assert!(free.contains(&fvar(0)), "x should be free");
    assert!(!free.contains(&fvar(1)), "y is bound by let");
}

#[test]
fn test_free_vars_function() {
    // fun f (x) := return x
    // return f
    let fun_decl = FunDecl::new(
        fvar(1),
        name("f"),
        vec![Param::new(fvar(10), name("x"), nat_type())],
        nat_type(),
        Code::ret(fvar(10)),
    );
    let code = Code::fun(fun_decl, Code::ret(fvar(1)));
    let bound = HashSet::new();
    let free = free_vars_in_code(&code, &bound);

    // f is bound by Fun, x is bound as param, so nothing should be free
    assert!(free.is_empty(), "No free variables expected");
}

#[test]
fn test_free_vars_function_captures() {
    // fun f (x) := return y  // y is free!
    // return f
    let fun_decl = FunDecl::new(
        fvar(1),
        name("f"),
        vec![Param::new(fvar(10), name("x"), nat_type())],
        nat_type(),
        Code::ret(fvar(20)), // y = fvar(20) is not a param
    );
    let code = Code::fun(fun_decl, Code::ret(fvar(1)));
    let bound = HashSet::new();
    let free = free_vars_in_code(&code, &bound);

    assert!(free.contains(&fvar(20)), "y should be free");
}

// ────────────────────────────────────────────────────────────────────────
// Lambda lifting tests
// ────────────────────────────────────────────────────────────────────────

#[test]
fn test_lift_non_capturing_function() {
    // def outer :=
    //   fun inner (x) := return x
    //   let y := inner 42
    //   return y
    let inner_fn = FunDecl::new(
        fvar(1),
        name("inner"),
        vec![Param::new(fvar(10), name("x"), nat_type())],
        nat_type(),
        Code::ret(fvar(10)),
    );

    let code = Code::fun(
        inner_fn,
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("y"),
                nat_type(),
                LetValue::FVar {
                    fvar: fvar(1),
                    args: vec![Arg::FVar(fvar(100))],
                },
            ),
            Code::ret(fvar(2)),
        ),
    );

    let decl = Decl::new(name("outer"), vec![], nat_type(), vec![], code, false);

    let result = lambda_lift_default(&decl);

    // Should have lifted one function
    assert_eq!(result.lifted.len(), 1, "Should lift one function");

    // The lifted function should have the inner body
    let lifted = &result.lifted[0];
    assert!(
        lifted.name.to_string().contains("inner"),
        "Lifted name should contain 'inner'"
    );
}

#[test]
fn test_lift_capturing_function_with_extra_params() {
    // def outer (z) :=
    //   fun inner (x) := return z  // captures z
    //   return inner
    // After lifting: inner gets z as extra parameter
    let inner_fn = FunDecl::new(
        fvar(1),
        name("inner"),
        vec![Param::new(fvar(10), name("x"), nat_type())],
        nat_type(),
        Code::ret(fvar(0)), // Returns z (param of outer)
    );

    let code = Code::fun(inner_fn, Code::ret(fvar(1)));

    let decl = Decl::new(
        name("outer"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("z"), nat_type())],
        code,
        false,
    );

    let result = lambda_lift_default(&decl);

    // Function captures z, should be lifted with z as extra parameter
    assert_eq!(
        result.lifted.len(),
        1,
        "Capturing function should be lifted"
    );
    let lifted = &result.lifted[0];
    // Should have 2 params: captured z (first) and original x
    assert_eq!(
        lifted.params.len(),
        2,
        "Lifted function should have capture param + original param"
    );
    assert!(
        lifted.name.to_string().contains("inner"),
        "Lifted name should contain 'inner'"
    );
}

#[test]
fn test_lift_capture_param_preserves_outer_type() {
    let outer_flag_type = bool_type();
    let inner_fn = FunDecl::new(
        fvar(1),
        name("inner"),
        vec![Param::new(fvar(10), name("x"), nat_type())],
        outer_flag_type.clone(),
        Code::ret(fvar(0)),
    );

    let decl = Decl::new(
        name("outer"),
        vec![],
        outer_flag_type.clone(),
        vec![Param::new(fvar(0), name("flag"), outer_flag_type.clone())],
        Code::fun(inner_fn, Code::ret(fvar(0))),
        false,
    );

    let result = lambda_lift_default(&decl);
    let lifted = result
        .lifted
        .first()
        .expect("capturing function should be lifted");

    assert_eq!(lifted.params.len(), 2);
    assert_eq!(
        lifted.params[0].ty, outer_flag_type,
        "capture param should keep the outer variable type"
    );
}

#[test]
fn test_lift_replaces_calls() {
    // After lifting, calls to local function should become calls to lifted version
    let inner_fn = FunDecl::new(
        fvar(1),
        name("inner"),
        vec![],
        nat_type(),
        Code::let_bind(
            LetDecl::new(fvar(10), name("c"), nat_type(), LetValue::nat(42)),
            Code::ret(fvar(10)),
        ),
    );

    let code = Code::fun(
        inner_fn,
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("result"),
                nat_type(),
                LetValue::FVar {
                    fvar: fvar(1),
                    args: vec![],
                },
            ),
            Code::ret(fvar(2)),
        ),
    );

    let decl = Decl::new(name("outer"), vec![], nat_type(), vec![], code, false);

    let result = lambda_lift_default(&decl);

    // Verify the call was replaced
    if let DeclValue::Code(body) = &result.decl.body {
        // Should be a Let now (not Fun)
        match body.as_ref() {
            Code::Let(let_decl, _) => {
                // The value should be a Const call to the lifted function
                match &let_decl.value {
                    LetValue::Const { name, .. } => {
                        assert!(
                            name.to_string().contains("inner"),
                            "Call should be to lifted function"
                        );
                    }
                    _ => panic!("Expected Const call, got {:?}", let_decl.value),
                }
            }
            _ => panic!("Expected Let, got {:?}", body),
        }
    }
}

#[test]
fn test_captured_vars_ordered_deterministically() {
    // When a function captures multiple variables, they should be ordered by FVarId
    // to ensure deterministic builds
    let inner_fn = FunDecl::new(
        fvar(1),
        name("inner"),
        vec![Param::new(fvar(10), name("x"), nat_type())],
        nat_type(),
        // Return z + y (captures both y=fvar(0) and z=fvar(2), but z has higher id)
        Code::let_bind(
            LetDecl::new(
                fvar(11),
                name("sum"),
                nat_type(),
                LetValue::Const {
                    name: name("Nat.add"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(2)), Arg::FVar(fvar(0))], // z, y
                },
            ),
            Code::ret(fvar(11)),
        ),
    );

    let code = Code::fun(inner_fn, Code::ret(fvar(1)));

    let decl = Decl::new(
        name("outer"),
        vec![],
        nat_type(),
        vec![
            Param::new(fvar(0), name("y"), nat_type()),
            Param::new(fvar(2), name("z"), nat_type()),
        ],
        code,
        false,
    );

    let result = lambda_lift_default(&decl);

    // Lifted function should have capture params sorted by FVarId: y (0) before z (2)
    assert_eq!(result.lifted.len(), 1);
    let lifted = &result.lifted[0];
    // 2 capture params + 1 original param = 3
    assert_eq!(
        lifted.params.len(),
        3,
        "Should have 2 capture params + 1 original"
    );
    // First capture param should be for y (lower FVarId)
    assert!(
        lifted.params[0].name.to_string().contains("cap"),
        "First param should be a capture param"
    );
}

#[test]
fn test_lifted_recursive_function_marked_recursive() {
    // A recursive local function should have recursive=true after lifting
    // fun f (x) := let y := f x; return y
    let inner_fn = FunDecl::new(
        fvar(1),
        name("recurse"),
        vec![Param::new(fvar(10), name("x"), nat_type())],
        nat_type(),
        Code::let_bind(
            LetDecl::new(
                fvar(11),
                name("y"),
                nat_type(),
                LetValue::FVar {
                    fvar: fvar(1), // Recursive self-reference
                    args: vec![Arg::FVar(fvar(10))],
                },
            ),
            Code::ret(fvar(11)),
        ),
    );

    let code = Code::fun(inner_fn, Code::ret(fvar(1)));
    let decl = Decl::new(name("outer"), vec![], nat_type(), vec![], code, false);

    let result = lambda_lift_default(&decl);

    assert_eq!(result.lifted.len(), 1);
    let lifted = &result.lifted[0];
    assert!(
        lifted.recursive,
        "Recursive function should have recursive=true after lifting"
    );
}

#[test]
fn test_lifted_non_recursive_function_not_marked_recursive() {
    // A non-recursive local function should have recursive=false after lifting
    let inner_fn = FunDecl::new(
        fvar(1),
        name("simple"),
        vec![Param::new(fvar(10), name("x"), nat_type())],
        nat_type(),
        Code::ret(fvar(10)), // Just returns param, no self-reference
    );

    let code = Code::fun(inner_fn, Code::ret(fvar(1)));
    let decl = Decl::new(name("outer"), vec![], nat_type(), vec![], code, false);

    let result = lambda_lift_default(&decl);

    assert_eq!(result.lifted.len(), 1);
    let lifted = &result.lifted[0];
    assert!(
        !lifted.recursive,
        "Non-recursive function should have recursive=false"
    );
}

#[test]
fn test_free_vars_recursive_function_not_free() {
    // A recursive function referencing itself should NOT report self as free
    // fun f (x) := let y := f x; return y
    let fun_decl = FunDecl::new(
        fvar(1),
        name("f"),
        vec![Param::new(fvar(10), name("x"), nat_type())],
        nat_type(),
        Code::let_bind(
            LetDecl::new(
                fvar(11),
                name("y"),
                nat_type(),
                LetValue::FVar {
                    fvar: fvar(1), // Recursive self-reference
                    args: vec![Arg::FVar(fvar(10))],
                },
            ),
            Code::ret(fvar(11)),
        ),
    );
    let code = Code::fun(fun_decl, Code::ret(fvar(1)));
    let bound = HashSet::new();
    let free = free_vars_in_code(&code, &bound);

    // The function references itself (fvar(1)), but that should NOT be free
    // since the function binds its own name
    assert!(
        !free.contains(&fvar(1)),
        "Recursive self-reference should not be free"
    );
    assert!(free.is_empty(), "No free variables expected");
}

#[test]
fn test_free_vars_type_arg_contains_fvar() {
    // fun inner (x) :=
    //   let y := SomeConst @(alpha)  // alpha is free, only in Arg::Type
    //   return y
    // Alpha (fvar(50)) is referenced only inside Arg::Type and should be detected as free.
    let alpha_fvar = fvar(50);
    let alpha_type_expr = Expr::fvar(alpha_fvar);
    let inner_fn = FunDecl::new(
        fvar(1),
        name("inner"),
        vec![Param::new(fvar(10), name("x"), nat_type())],
        nat_type(),
        Code::let_bind(
            LetDecl::new(
                fvar(11),
                name("y"),
                nat_type(),
                LetValue::Const {
                    name: name("SomeConst"),
                    levels: vec![],
                    args: vec![Arg::Type(alpha_type_expr)],
                },
            ),
            Code::ret(fvar(11)),
        ),
    );
    let code = Code::fun(inner_fn, Code::ret(fvar(1)));
    let bound = HashSet::new();
    let free = free_vars_in_code(&code, &bound);

    assert!(
        free.contains(&alpha_fvar),
        "FVar inside Arg::Type should be detected as free, but got: {:?}",
        free
    );
}

#[test]
fn test_free_vars_let_type_annotation() {
    // let y : alpha := 42
    // return y
    // Alpha (fvar(50)) is referenced only in the let-declaration type annotation.
    let alpha_fvar = fvar(50);
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("y"),
            Expr::fvar(alpha_fvar), // type references alpha
            LetValue::nat(42),
        ),
        Code::ret(fvar(1)),
    );
    let bound = HashSet::new();
    let free = free_vars_in_code(&code, &bound);

    assert!(
        free.contains(&alpha_fvar),
        "FVar in let type annotation should be detected as free, got: {:?}",
        free
    );
}

#[test]
fn test_free_vars_fun_param_type() {
    // fun f (x : alpha) := return x
    // return f
    // Alpha (fvar(50)) is referenced only in a function parameter type.
    let alpha_fvar = fvar(50);
    let fun_decl = FunDecl::new(
        fvar(1),
        name("f"),
        vec![Param::new(fvar(10), name("x"), Expr::fvar(alpha_fvar))],
        nat_type(),
        Code::ret(fvar(10)),
    );
    let code = Code::fun(fun_decl, Code::ret(fvar(1)));
    let bound = HashSet::new();
    let free = free_vars_in_code(&code, &bound);

    assert!(
        free.contains(&alpha_fvar),
        "FVar in fun param type should be detected as free, got: {:?}",
        free
    );
}

#[test]
fn test_free_vars_fun_return_type() {
    // fun f (x) : alpha := return x
    // return f
    // Alpha (fvar(50)) is referenced only in the function return type.
    let alpha_fvar = fvar(50);
    let fun_decl = FunDecl::new(
        fvar(1),
        name("f"),
        vec![Param::new(fvar(10), name("x"), nat_type())],
        Expr::fvar(alpha_fvar), // return type references alpha
        Code::ret(fvar(10)),
    );
    let code = Code::fun(fun_decl, Code::ret(fvar(1)));
    let bound = HashSet::new();
    let free = free_vars_in_code(&code, &bound);

    assert!(
        free.contains(&alpha_fvar),
        "FVar in fun return type should be detected as free, got: {:?}",
        free
    );
}

#[test]
fn test_free_vars_cases_result_type() {
    let alpha_fvar = fvar(50);
    let code = Code::cases(
        name("Nat"),
        Expr::fvar(alpha_fvar),
        fvar(1),
        vec![Alt::Default(Box::new(Code::ret(fvar(1))))],
    );
    let mut bound = HashSet::new();
    bound.insert(fvar(1));
    let free = free_vars_in_code(&code, &bound);

    assert!(
        free.contains(&alpha_fvar),
        "FVar in cases result_type should be detected as free, got: {:?}",
        free
    );
}

#[test]
fn test_code_references_fvar_cases_result_type() {
    let target = fvar(50);
    let code = Code::cases(
        name("Nat"),
        Expr::fvar(target),
        fvar(1),
        vec![Alt::Default(Box::new(Code::ret(fvar(1))))],
    );

    assert!(
        code_references_fvar(&code, target),
        "cases result_type should count as an FVar reference"
    );
}

#[test]
fn test_lift_captures_type_only_fvar() {
    // def outer (alpha) :=
    //   fun inner (x : alpha) := return x  // captures alpha via param type only
    //   return inner
    // After lifting: inner should get alpha as a capture parameter.
    let alpha_fvar = fvar(0);
    let inner_fn = FunDecl::new(
        fvar(1),
        name("inner"),
        vec![Param::new(fvar(10), name("x"), Expr::fvar(alpha_fvar))],
        nat_type(),
        Code::ret(fvar(10)),
    );

    let code = Code::fun(inner_fn, Code::ret(fvar(1)));

    let decl = Decl::new(
        name("outer"),
        vec![],
        nat_type(),
        vec![Param::new(alpha_fvar, name("alpha"), nat_type())],
        code,
        false,
    );

    let result = lambda_lift_default(&decl);

    assert_eq!(result.lifted.len(), 1);
    let lifted = &result.lifted[0];
    // Should have 2 params: captured alpha (from type) + original x
    assert_eq!(
        lifted.params.len(),
        2,
        "Lifted function should capture alpha from param type: got {:?}",
        lifted.params.iter().map(|p| &p.name).collect::<Vec<_>>()
    );
}

#[test]
fn test_lift_remaps_cases_result_type_capture() {
    let alpha_fvar = fvar(0);
    let inner_fn = FunDecl::new(
        fvar(1),
        name("inner"),
        vec![Param::new(fvar(10), name("x"), nat_type())],
        nat_type(),
        Code::cases(
            name("Nat"),
            Expr::fvar(alpha_fvar),
            fvar(10),
            vec![Alt::Default(Box::new(Code::ret(fvar(10))))],
        ),
    );

    let code = Code::fun(inner_fn, Code::ret(fvar(1)));
    let decl = Decl::new(
        name("outer"),
        vec![],
        nat_type(),
        vec![Param::new(alpha_fvar, name("alpha"), nat_type())],
        code,
        false,
    );

    let result = lambda_lift_default(&decl);

    assert_eq!(result.lifted.len(), 1);
    let lifted = &result.lifted[0];
    assert_eq!(lifted.params.len(), 2);

    match &lifted.body {
        DeclValue::Code(body) => match body.as_ref() {
            Code::Cases(cases) => match cases.result_type.kind() {
                ExprKind::FVar(fv) => {
                    assert_ne!(
                        *fv, alpha_fvar,
                        "Cases result type should be remapped away from the original capture"
                    );
                    assert_eq!(
                        *fv, lifted.params[0].fvar_id,
                        "Cases result type should reference the new capture parameter"
                    );
                }
                other => panic!("Expected FVar in cases result type, got {:?}", other),
            },
            other => panic!("Expected lifted body to remain cases code, got {:?}", other),
        },
        other => panic!(
            "Expected lifted declaration to contain code, got {:?}",
            other
        ),
    }
}

#[test]
fn test_remap_types_in_lifted_closure() {
    // def outer (alpha) :=
    //   fun inner (x : alpha) : alpha := return x
    //   return inner
    // After lifting, the remapped body's param types and return type should
    // reference the new capture FVarId, not the original alpha.
    let alpha_fvar = fvar(0);
    let inner_fn = FunDecl::new(
        fvar(1),
        name("inner"),
        vec![Param::new(fvar(10), name("x"), Expr::fvar(alpha_fvar))],
        Expr::fvar(alpha_fvar), // return type also uses alpha
        Code::ret(fvar(10)),
    );

    let code = Code::fun(inner_fn, Code::ret(fvar(1)));

    let decl = Decl::new(
        name("outer"),
        vec![],
        nat_type(),
        vec![Param::new(alpha_fvar, name("alpha"), nat_type())],
        code,
        false,
    );

    let result = lambda_lift_default(&decl);

    assert_eq!(result.lifted.len(), 1);
    let lifted = &result.lifted[0];

    // The lifted function should NOT reference the original alpha FVarId (0)
    // in its param types — it should have been remapped to the capture param.
    // The capture param is first (index 0), original param x is second (index 1).
    let x_param = &lifted.params[1]; // original "x" param
                                     // x's type was `Expr::fvar(alpha_fvar=0)` — after remap, it should be
                                     // `Expr::fvar(<new_capture_id>)`, NOT `Expr::fvar(0)`.
    match x_param.ty.kind() {
        ExprKind::FVar(fv) => {
            assert_ne!(
                *fv, alpha_fvar,
                "Param type should be remapped away from original alpha FVarId"
            );
            // It should be the capture param's FVarId
            assert_eq!(
                *fv, lifted.params[0].fvar_id,
                "Param type FVar should reference capture param"
            );
        }
        other => panic!("Expected FVar in param type, got {:?}", other),
    }
}

#[test]
fn test_remap_fvars_in_expr_rewrites_cubical_extensions() {
    let remap = remap_pairs(&[
        (1, 101),
        (2, 102),
        (3, 103),
        (4, 104),
        (5, 105),
        (6, 106),
        (7, 107),
        (8, 108),
        (9, 109),
    ]);

    let input = Expr::from_kind(ExprKind::Squash(Arc::new(Expr::from_kind(
        ExprKind::CubicalHComp {
            ty: Arc::new(expr_fvar(1)),
            phi: Arc::new(Expr::from_kind(ExprKind::CubicalPath {
                ty: Arc::new(expr_fvar(2)),
                left: Arc::new(expr_fvar(3)),
                right: Arc::new(expr_fvar(4)),
            })),
            u: Arc::new(Expr::from_kind(ExprKind::CubicalPathApp {
                path: Arc::new(Expr::from_kind(ExprKind::CubicalPathLam {
                    body: Arc::new(expr_fvar(5)),
                })),
                arg: Arc::new(expr_fvar(6)),
            })),
            base: Arc::new(Expr::from_kind(ExprKind::CubicalTransp {
                ty: Arc::new(expr_fvar(7)),
                phi: Arc::new(expr_fvar(8)),
                base: Arc::new(expr_fvar(9)),
            })),
        },
    ))));

    let expected = Expr::from_kind(ExprKind::Squash(Arc::new(Expr::from_kind(
        ExprKind::CubicalHComp {
            ty: Arc::new(expr_fvar(101)),
            phi: Arc::new(Expr::from_kind(ExprKind::CubicalPath {
                ty: Arc::new(expr_fvar(102)),
                left: Arc::new(expr_fvar(103)),
                right: Arc::new(expr_fvar(104)),
            })),
            u: Arc::new(Expr::from_kind(ExprKind::CubicalPathApp {
                path: Arc::new(Expr::from_kind(ExprKind::CubicalPathLam {
                    body: Arc::new(expr_fvar(105)),
                })),
                arg: Arc::new(expr_fvar(106)),
            })),
            base: Arc::new(Expr::from_kind(ExprKind::CubicalTransp {
                ty: Arc::new(expr_fvar(107)),
                phi: Arc::new(expr_fvar(108)),
                base: Arc::new(expr_fvar(109)),
            })),
        },
    ))));

    assert_eq!(remap_fvars_in_expr(&input, &remap), expected);
}

#[test]
fn test_remap_fvars_in_expr_rewrites_zfc_extensions() {
    let remap = remap_pairs(&[(10, 110), (11, 111), (12, 112), (13, 113), (14, 114)]);

    let input = Expr::from_kind(ExprKind::ZFCComprehension {
        domain: Arc::new(Expr::from_kind(ExprKind::ZFCMem {
            element: Arc::new(expr_fvar(10)),
            set: Arc::new(Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Replacement {
                set: Arc::new(Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Pair(
                    Arc::new(Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Infinity))),
                    Arc::new(expr_fvar(11)),
                )))),
                func: Arc::new(Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Choice(
                    Arc::new(expr_fvar(12)),
                )))),
            }))),
        })),
        pred: Arc::new(Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Separation {
            set: Arc::new(Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::PowerSet(
                Arc::new(expr_fvar(13)),
            )))),
            pred: Arc::new(Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Union(
                Arc::new(expr_fvar(14)),
            )))),
        }))),
    });

    let expected = Expr::from_kind(ExprKind::ZFCComprehension {
        domain: Arc::new(Expr::from_kind(ExprKind::ZFCMem {
            element: Arc::new(expr_fvar(110)),
            set: Arc::new(Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Replacement {
                set: Arc::new(Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Pair(
                    Arc::new(Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Infinity))),
                    Arc::new(expr_fvar(111)),
                )))),
                func: Arc::new(Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Choice(
                    Arc::new(expr_fvar(112)),
                )))),
            }))),
        })),
        pred: Arc::new(Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Separation {
            set: Arc::new(Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::PowerSet(
                Arc::new(expr_fvar(113)),
            )))),
            pred: Arc::new(Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Union(
                Arc::new(expr_fvar(114)),
            )))),
        }))),
    });

    assert_eq!(remap_fvars_in_expr(&input, &remap), expected);
}

#[test]
fn test_remap_fvars_in_code_rewrites_cases_result_type() {
    let remap = remap_pairs(&[(5, 105), (20, 120), (21, 121), (22, 122), (23, 123)]);
    let result_type = Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(expr_fvar(20)),
        left: Arc::new(expr_fvar(21)),
        right: Arc::new(expr_fvar(22)),
    });
    let input = Code::cases(
        name("Nat"),
        result_type,
        fvar(5),
        vec![Alt::Default(Box::new(Code::ret(fvar(23))))],
    );

    let remapped = remap_fvars_in_code(&input, &remap);

    match remapped {
        Code::Cases(cases) => {
            assert_eq!(cases.scrutinee, fvar(105));
            assert_eq!(
                cases.result_type,
                Expr::from_kind(ExprKind::CubicalPath {
                    ty: Arc::new(expr_fvar(120)),
                    left: Arc::new(expr_fvar(121)),
                    right: Arc::new(expr_fvar(122)),
                })
            );
            match cases.alts.as_slice() {
                [Alt::Default(body)] => assert_eq!(body.as_ref(), &Code::ret(fvar(123))),
                other => panic!("Expected one default alternative, got {:?}", other),
            }
        }
        other => panic!("Expected cases code, got {:?}", other),
    }
}
