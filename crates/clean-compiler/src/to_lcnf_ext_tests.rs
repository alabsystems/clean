// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended LCNF conversion.

use super::to_lcnf_ext::*;
use crate::lcnf::{Alt, Arg, Cases, Code, Decl, DeclValue, FunDecl, LetDecl, LetValue, Param};
use clean_kernel::{Expr, FVarId, Name};

// ─── Test Helpers ───────────────────────────────────────────────────────────

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn nat_ty() -> Expr {
    Expr::const_str("Nat")
}

fn param(id: u64, name: &str) -> Param {
    Param::new(fvar(id), Name::from_string(name), nat_ty())
}

fn let_decl(id: u64, value: LetValue) -> LetDecl {
    LetDecl::new(fvar(id), Name::anon(), nat_ty(), value)
}

fn simple_decl(name: &str, params: Vec<Param>, body: Code) -> Decl {
    Decl::new(
        Name::from_string(name),
        Vec::new(),
        nat_ty(),
        params,
        body,
        false,
    )
}

fn fun_decl(id: u64, params: Vec<Param>, body: Code) -> FunDecl {
    FunDecl::new(fvar(id), Name::from_string("f"), params, nat_ty(), body)
}

// ─── ExtConvConfig Tests ────────────────────────────────────────────────────

#[test]
fn test_config_default_enables_all_passes() {
    let config = ExtConvConfig::default();
    assert!(config.lambda_lifting);
    assert!(config.let_flattening);
    assert!(config.case_simplification);
    assert!(config.eta_reduction);
    assert!(config.beta_reduction);
    assert!(config.join_point_detection);
    assert!(config.erased_arg_elimination);
    assert!(!config.validate);
}

#[test]
fn test_config_all_disabled() {
    let config = ExtConvConfig {
        lambda_lifting: false,
        let_flattening: false,
        case_simplification: false,
        eta_reduction: false,
        beta_reduction: false,
        join_point_detection: false,
        erased_arg_elimination: false,
        validate: false,
    };
    let decl = simple_decl("id", vec![param(0, "x")], Code::ret(fvar(0)));
    let result = convert_ext(&decl, &config);
    assert_eq!(
        result.stats,
        ConvStats::default().tap(|s| s.decls_processed = 1)
    );
}

// ─── Lambda Lifting Tests ───────────────────────────────────────────────────

#[test]
fn test_lambda_lifting_single_nested_fun() {
    let inner_body = Code::ret(fvar(2));
    let inner_fun = fun_decl(1, vec![param(2, "y")], inner_body);
    let body = Code::fun(inner_fun, Code::ret(fvar(0)));
    let decl = simple_decl("test", vec![param(0, "x")], body);

    let config = ExtConvConfig {
        lambda_lifting: true,
        ..disabled_config()
    };
    let result = convert_ext(&decl, &config);

    assert_eq!(result.stats.lambdas_lifted, 1);
    assert_eq!(result.lifted_decls.len(), 1);
    assert!(result.lifted_decls[0].name.to_string().contains("lifted"));
}

#[test]
fn test_lambda_lifting_doubly_nested() {
    let inner2 = Code::ret(fvar(3));
    let fun2 = fun_decl(2, vec![param(3, "z")], inner2);
    let inner1 = Code::fun(fun2, Code::ret(fvar(2)));
    let fun1 = fun_decl(1, vec![param(2, "y")], inner1);
    let body = Code::fun(fun1, Code::ret(fvar(0)));
    let decl = simple_decl("test", vec![param(0, "x")], body);

    let config = ExtConvConfig {
        lambda_lifting: true,
        ..disabled_config()
    };
    let result = convert_ext(&decl, &config);

    assert_eq!(result.stats.lambdas_lifted, 2);
    assert_eq!(result.lifted_decls.len(), 2);
}

#[test]
fn test_lambda_lifting_preserves_params() {
    let inner_body = Code::ret(fvar(2));
    let inner_fun = fun_decl(1, vec![param(2, "y")], inner_body);
    let body = Code::fun(inner_fun, Code::ret(fvar(0)));
    let decl = simple_decl("test", vec![param(0, "x")], body);

    let config = ExtConvConfig {
        lambda_lifting: true,
        ..disabled_config()
    };
    let result = convert_ext(&decl, &config);

    let lifted = &result.lifted_decls[0];
    assert_eq!(lifted.params.len(), 1);
    assert_eq!(lifted.params[0].fvar_id, fvar(2));
}

#[test]
fn test_lambda_lifting_no_funs_noop() {
    let body = Code::ret(fvar(0));
    let decl = simple_decl("test", vec![param(0, "x")], body);

    let config = ExtConvConfig {
        lambda_lifting: true,
        ..disabled_config()
    };
    let result = convert_ext(&decl, &config);

    assert_eq!(result.stats.lambdas_lifted, 0);
    assert!(result.lifted_decls.is_empty());
}

// ─── Let Flattening Tests ───────────────────────────────────────────────────

#[test]
fn test_let_flattening_nested_lets() {
    // let x = 1; let y = 2; return y
    let inner = Code::let_bind(let_decl(2, LetValue::nat(2)), Code::ret(fvar(2)));
    let body = Code::let_bind(let_decl(1, LetValue::nat(1)), inner);
    let decl = simple_decl("test", vec![], body);

    let config = ExtConvConfig {
        let_flattening: true,
        ..disabled_config()
    };
    let result = convert_ext(&decl, &config);

    assert!(result.stats.lets_flattened > 0);
}

#[test]
fn test_let_flattening_single_let_noop() {
    let body = Code::let_bind(let_decl(1, LetValue::nat(1)), Code::ret(fvar(1)));
    let decl = simple_decl("test", vec![], body);

    let config = ExtConvConfig {
        let_flattening: true,
        ..disabled_config()
    };
    let result = convert_ext(&decl, &config);

    // Single let: depth=1, no flattening needed
    assert_eq!(result.stats.lets_flattened, 0);
}

#[test]
fn test_let_flattening_deeply_nested() {
    // 4-deep let chain
    let body = Code::let_bind(
        let_decl(1, LetValue::nat(1)),
        Code::let_bind(
            let_decl(2, LetValue::nat(2)),
            Code::let_bind(
                let_decl(3, LetValue::nat(3)),
                Code::let_bind(let_decl(4, LetValue::nat(4)), Code::ret(fvar(4))),
            ),
        ),
    );
    let decl = simple_decl("test", vec![], body);

    let config = ExtConvConfig {
        let_flattening: true,
        ..disabled_config()
    };
    let result = convert_ext(&decl, &config);

    assert!(result.stats.lets_flattened >= 3);
}

// ─── Case Simplification Tests ──────────────────────────────────────────────

#[test]
fn test_case_simplify_single_default_alt() {
    let cases = Cases::new(
        Name::from_string("Bool"),
        nat_ty(),
        fvar(0),
        vec![Alt::default(Code::ret(fvar(1)))],
    );
    let body = Code::Cases(cases);
    let decl = simple_decl("test", vec![param(0, "x"), param(1, "y")], body);

    let config = ExtConvConfig {
        case_simplification: true,
        ..disabled_config()
    };
    let result = convert_ext(&decl, &config);

    assert_eq!(result.stats.cases_simplified, 1);
    // Body should now be Return, not Cases
    if let DeclValue::Code(ref code) = result.decl.body {
        assert!(matches!(code.as_ref(), Code::Return(_)));
    }
}

#[test]
fn test_case_simplify_identical_branches() {
    let cases = Cases::new(
        Name::from_string("Bool"),
        nat_ty(),
        fvar(0),
        vec![
            Alt::ctor(Name::from_string("Bool.true"), vec![], Code::ret(fvar(1))),
            Alt::ctor(Name::from_string("Bool.false"), vec![], Code::ret(fvar(1))),
        ],
    );
    let body = Code::Cases(cases);
    let decl = simple_decl("test", vec![param(0, "x"), param(1, "y")], body);

    let config = ExtConvConfig {
        case_simplification: true,
        ..disabled_config()
    };
    let result = convert_ext(&decl, &config);

    assert_eq!(result.stats.cases_simplified, 1);
}

#[test]
fn test_case_simplify_different_branches_noop() {
    let cases = Cases::new(
        Name::from_string("Bool"),
        nat_ty(),
        fvar(0),
        vec![
            Alt::ctor(Name::from_string("Bool.true"), vec![], Code::ret(fvar(1))),
            Alt::ctor(Name::from_string("Bool.false"), vec![], Code::ret(fvar(2))),
        ],
    );
    let body = Code::Cases(cases);
    let decl = simple_decl(
        "test",
        vec![param(0, "x"), param(1, "y"), param(2, "z")],
        body,
    );

    let config = ExtConvConfig {
        case_simplification: true,
        ..disabled_config()
    };
    let result = convert_ext(&decl, &config);

    assert_eq!(result.stats.cases_simplified, 0);
}

#[test]
fn test_case_simplify_nested_cases() {
    let inner_cases = Cases::new(
        Name::from_string("Bool"),
        nat_ty(),
        fvar(1),
        vec![Alt::default(Code::ret(fvar(2)))],
    );
    let outer_body = Code::let_bind(let_decl(3, LetValue::nat(0)), Code::Cases(inner_cases));
    let outer_cases = Cases::new(
        Name::from_string("Nat"),
        nat_ty(),
        fvar(0),
        vec![Alt::default(outer_body)],
    );
    let body = Code::Cases(outer_cases);
    let decl = simple_decl(
        "test",
        vec![param(0, "x"), param(1, "y"), param(2, "z")],
        body,
    );

    let config = ExtConvConfig {
        case_simplification: true,
        ..disabled_config()
    };
    let result = convert_ext(&decl, &config);

    // Both the outer and inner single-default cases should simplify
    assert!(result.stats.cases_simplified >= 2);
}

// ─── Eta Reduction Tests ────────────────────────────────────────────────────

#[test]
fn test_eta_reduction_simple() {
    // fun f(x) := let tmp = g(x); return tmp  →  eta-reducible to g
    let f_body = Code::let_bind(
        LetDecl::new(
            fvar(10),
            Name::anon(),
            nat_ty(),
            LetValue::FVar {
                fvar: fvar(5),
                args: vec![Arg::FVar(fvar(2))],
            },
        ),
        Code::ret(fvar(10)),
    );
    let fun = fun_decl(1, vec![param(2, "x")], f_body);
    let body = Code::fun(fun, Code::ret(fvar(0)));
    let decl = simple_decl("test", vec![param(0, "x"), param(5, "g")], body);

    let config = ExtConvConfig {
        eta_reduction: true,
        ..disabled_config()
    };
    let result = convert_ext(&decl, &config);

    assert_eq!(result.stats.eta_reductions, 1);
}

#[test]
fn test_eta_reduction_non_matching_args_noop() {
    // fun f(x) := let tmp = g(y); return tmp  → NOT eta (arg mismatch)
    let f_body = Code::let_bind(
        LetDecl::new(
            fvar(10),
            Name::anon(),
            nat_ty(),
            LetValue::FVar {
                fvar: fvar(5),
                args: vec![Arg::FVar(fvar(99))], // different from param
            },
        ),
        Code::ret(fvar(10)),
    );
    let fun = fun_decl(1, vec![param(2, "x")], f_body);
    let body = Code::fun(fun, Code::ret(fvar(0)));
    let decl = simple_decl("test", vec![param(0, "x"), param(5, "g")], body);

    let config = ExtConvConfig {
        eta_reduction: true,
        ..disabled_config()
    };
    let result = convert_ext(&decl, &config);

    assert_eq!(result.stats.eta_reductions, 0);
}

#[test]
fn test_eta_reduction_multiple_params() {
    // fun f(x, y) := let tmp = g(x, y); return tmp → eta-reducible
    let f_body = Code::let_bind(
        LetDecl::new(
            fvar(10),
            Name::anon(),
            nat_ty(),
            LetValue::FVar {
                fvar: fvar(5),
                args: vec![Arg::FVar(fvar(2)), Arg::FVar(fvar(3))],
            },
        ),
        Code::ret(fvar(10)),
    );
    let fun = fun_decl(1, vec![param(2, "x"), param(3, "y")], f_body);
    let body = Code::fun(fun, Code::ret(fvar(0)));
    let decl = simple_decl("test", vec![param(0, "x"), param(5, "g")], body);

    let config = ExtConvConfig {
        eta_reduction: true,
        ..disabled_config()
    };
    let result = convert_ext(&decl, &config);

    assert_eq!(result.stats.eta_reductions, 1);
}

// ─── Beta Reduction Tests ───────────────────────────────────────────────────

#[test]
fn test_beta_reduction_trivial_thunk() {
    // fun f() := return x  → trivial thunk
    let fun = fun_decl(1, vec![], Code::ret(fvar(0)));
    let body = Code::fun(fun, Code::ret(fvar(0)));
    let decl = simple_decl("test", vec![param(0, "x")], body);

    let config = ExtConvConfig {
        beta_reduction: true,
        ..disabled_config()
    };
    let result = convert_ext(&decl, &config);

    assert_eq!(result.stats.beta_reductions, 1);
}

#[test]
fn test_beta_reduction_non_trivial_noop() {
    // fun f(x) := return x  → has params, not a trivial thunk
    let fun = fun_decl(1, vec![param(2, "x")], Code::ret(fvar(2)));
    let body = Code::fun(fun, Code::ret(fvar(0)));
    let decl = simple_decl("test", vec![param(0, "x")], body);

    let config = ExtConvConfig {
        beta_reduction: true,
        ..disabled_config()
    };
    let result = convert_ext(&decl, &config);

    assert_eq!(result.stats.beta_reductions, 0);
}

// ─── Join Point Detection Tests ─────────────────────────────────────────────

#[test]
fn test_join_point_detection_tail_call() {
    // fun f(x) := return x; jmp f(0)  → f is only used in tail position
    let fun = fun_decl(1, vec![param(2, "x")], Code::ret(fvar(2)));
    let body = Code::fun(fun, Code::jmp(fvar(1), vec![Arg::FVar(fvar(0))]));
    let decl = simple_decl("test", vec![param(0, "x")], body);

    let config = ExtConvConfig {
        join_point_detection: true,
        ..disabled_config()
    };
    let result = convert_ext(&decl, &config);

    assert_eq!(result.stats.join_points_detected, 1);
    // The Fun should have been converted to JoinPoint
    if let DeclValue::Code(ref code) = result.decl.body {
        assert!(matches!(code.as_ref(), Code::JoinPoint(_, _)));
    }
}

#[test]
fn test_join_point_detection_non_tail_noop() {
    // fun f(x) := return x; let y = f(0); return y  → f used in non-tail
    let fun = fun_decl(1, vec![param(2, "x")], Code::ret(fvar(2)));
    let body = Code::fun(
        fun,
        Code::let_bind(
            LetDecl::new(
                fvar(3),
                Name::anon(),
                nat_ty(),
                LetValue::FVar {
                    fvar: fvar(1),
                    args: vec![Arg::FVar(fvar(0))],
                },
            ),
            Code::ret(fvar(3)),
        ),
    );
    let decl = simple_decl("test", vec![param(0, "x")], body);

    let config = ExtConvConfig {
        join_point_detection: true,
        ..disabled_config()
    };
    let result = convert_ext(&decl, &config);

    assert_eq!(result.stats.join_points_detected, 0);
}

#[test]
fn test_join_point_detection_in_case_branches() {
    // fun f(x) := return x; cases { true => jmp f(0), false => jmp f(1) }
    let fun = fun_decl(1, vec![param(2, "x")], Code::ret(fvar(2)));
    let cases = Cases::new(
        Name::from_string("Bool"),
        nat_ty(),
        fvar(0),
        vec![
            Alt::ctor(
                Name::from_string("Bool.true"),
                vec![],
                Code::jmp(fvar(1), vec![Arg::FVar(fvar(0))]),
            ),
            Alt::ctor(
                Name::from_string("Bool.false"),
                vec![],
                Code::jmp(fvar(1), vec![Arg::FVar(fvar(0))]),
            ),
        ],
    );
    let body = Code::fun(fun, Code::Cases(cases));
    let decl = simple_decl("test", vec![param(0, "x")], body);

    let config = ExtConvConfig {
        join_point_detection: true,
        ..disabled_config()
    };
    let result = convert_ext(&decl, &config);

    assert_eq!(result.stats.join_points_detected, 1);
}

// ─── Erased Argument Elimination Tests ──────────────────────────────────────

#[test]
fn test_erased_arg_elimination_in_let() {
    let body = Code::let_bind(
        LetDecl::new(
            fvar(1),
            Name::anon(),
            nat_ty(),
            LetValue::Const {
                name: Name::from_string("f"),
                levels: vec![],
                args: vec![Arg::Erased, Arg::FVar(fvar(0)), Arg::Erased],
            },
        ),
        Code::ret(fvar(1)),
    );
    let decl = simple_decl("test", vec![param(0, "x")], body);

    let config = ExtConvConfig {
        erased_arg_elimination: true,
        ..disabled_config()
    };
    let result = convert_ext(&decl, &config);

    assert_eq!(result.stats.erased_args_eliminated, 2);
    // Check the args were actually removed
    if let DeclValue::Code(ref code) = result.decl.body {
        if let Code::Let(ref ld, _) = code.as_ref() {
            if let LetValue::Const { ref args, .. } = ld.value {
                assert_eq!(args.len(), 1);
                assert!(matches!(args[0], Arg::FVar(_)));
            }
        }
    }
}

#[test]
fn test_erased_arg_elimination_in_jmp() {
    let fun = fun_decl(1, vec![param(2, "x")], Code::ret(fvar(2)));
    let body = Code::fun(
        fun,
        Code::jmp(fvar(1), vec![Arg::Erased, Arg::FVar(fvar(0))]),
    );
    let decl = simple_decl("test", vec![param(0, "x")], body);

    let config = ExtConvConfig {
        erased_arg_elimination: true,
        ..disabled_config()
    };
    let result = convert_ext(&decl, &config);

    assert_eq!(result.stats.erased_args_eliminated, 1);
}

#[test]
fn test_erased_arg_elimination_no_erased_noop() {
    let body = Code::let_bind(
        LetDecl::new(
            fvar(1),
            Name::anon(),
            nat_ty(),
            LetValue::Const {
                name: Name::from_string("f"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(0))],
            },
        ),
        Code::ret(fvar(1)),
    );
    let decl = simple_decl("test", vec![param(0, "x")], body);

    let config = ExtConvConfig {
        erased_arg_elimination: true,
        ..disabled_config()
    };
    let result = convert_ext(&decl, &config);

    assert_eq!(result.stats.erased_args_eliminated, 0);
}

// ─── Statistics Tests ───────────────────────────────────────────────────────

#[test]
fn test_stats_default_is_zero() {
    let stats = ConvStats::default();
    assert_eq!(stats.lambdas_lifted, 0);
    assert_eq!(stats.lets_flattened, 0);
    assert_eq!(stats.cases_simplified, 0);
    assert_eq!(stats.eta_reductions, 0);
    assert_eq!(stats.beta_reductions, 0);
    assert_eq!(stats.join_points_detected, 0);
    assert_eq!(stats.erased_args_eliminated, 0);
    assert_eq!(stats.decls_processed, 0);
}

#[test]
fn test_stats_tracks_decls_processed() {
    let decl = simple_decl("test", vec![], Code::ret(fvar(0)));
    let config = disabled_config();
    let result = convert_ext(&decl, &config);
    assert_eq!(result.stats.decls_processed, 1);
}

#[test]
fn test_batch_aggregates_stats() {
    let d1 = simple_decl("a", vec![], Code::ret(fvar(0)));
    let d2 = simple_decl("b", vec![], Code::ret(fvar(0)));
    let d3 = simple_decl("c", vec![], Code::ret(fvar(0)));

    let config = disabled_config();
    let (results, total_stats) = convert_ext_batch(&[d1, d2, d3], &config);

    assert_eq!(results.len(), 3);
    assert_eq!(total_stats.decls_processed, 3);
}

// ─── Validation Tests ───────────────────────────────────────────────────────

#[test]
fn test_validation_valid_decl() {
    let body = Code::let_bind(let_decl(1, LetValue::nat(42)), Code::ret(fvar(1)));
    let decl = simple_decl("test", vec![], body);

    let config = ExtConvConfig {
        validate: true,
        ..disabled_config()
    };
    let result = convert_ext(&decl, &config);

    assert!(result.validation_errors.is_empty());
}

#[test]
fn test_validation_unbound_return() {
    let body = Code::ret(fvar(99)); // not bound
    let decl = simple_decl("test", vec![], body);

    let config = ExtConvConfig {
        validate: true,
        ..disabled_config()
    };
    let result = convert_ext(&decl, &config);

    assert!(!result.validation_errors.is_empty());
    assert!(result
        .validation_errors
        .iter()
        .any(|e| matches!(e, ValidationError::UnboundReturn(_))));
}

#[test]
fn test_validation_unbound_join_point() {
    let body = Code::jmp(fvar(99), vec![]);
    let decl = simple_decl("test", vec![], body);

    let config = ExtConvConfig {
        validate: true,
        ..disabled_config()
    };
    let result = convert_ext(&decl, &config);

    assert!(result
        .validation_errors
        .iter()
        .any(|e| matches!(e, ValidationError::UnboundJoinPoint(_))));
}

#[test]
fn test_validation_empty_case_alts() {
    let cases = Cases::new(
        Name::from_string("Bool"),
        nat_ty(),
        fvar(0),
        vec![], // empty alts
    );
    let decl = simple_decl("test", vec![param(0, "x")], Code::Cases(cases));

    let config = ExtConvConfig {
        validate: true,
        ..disabled_config()
    };
    let result = convert_ext(&decl, &config);

    assert!(result
        .validation_errors
        .iter()
        .any(|e| matches!(e, ValidationError::EmptyCaseAlts)));
}

#[test]
fn test_validation_param_is_bound() {
    // Return a parameter — should be valid
    let body = Code::ret(fvar(0));
    let decl = simple_decl("test", vec![param(0, "x")], body);

    let config = ExtConvConfig {
        validate: true,
        ..disabled_config()
    };
    let result = convert_ext(&decl, &config);

    assert!(result.validation_errors.is_empty());
}

// ─── Edge Case Tests ────────────────────────────────────────────────────────

#[test]
fn test_already_lcnf_passthrough() {
    // A simple return is already in LCNF — all passes should be no-ops
    let body = Code::ret(fvar(0));
    let decl = simple_decl("test", vec![param(0, "x")], body);
    let config = ExtConvConfig::default();
    let result = convert_ext(&decl, &config);

    assert_eq!(result.stats.lambdas_lifted, 0);
    assert_eq!(result.stats.cases_simplified, 0);
    assert_eq!(result.stats.eta_reductions, 0);
    assert!(result.lifted_decls.is_empty());
}

#[test]
fn test_extern_decl_skipped() {
    use crate::lcnf::ExternEntry;
    let decl = Decl::extern_decl(
        Name::from_string("ext"),
        vec![],
        nat_ty(),
        vec![],
        vec![ExternEntry {
            backend: "c".into(),
            name: "ext_impl".into(),
        }],
    );

    let config = ExtConvConfig::default();
    let result = convert_ext(&decl, &config);

    // Extern decls have no code body, so no transformations apply
    assert_eq!(result.stats.lambdas_lifted, 0);
    assert_eq!(result.stats.lets_flattened, 0);
}

#[test]
fn test_recursive_decl_handling() {
    let body = Code::ret(fvar(0));
    let decl = Decl::new(
        Name::from_string("rec"),
        vec![],
        nat_ty(),
        vec![param(0, "n")],
        body,
        true, // recursive
    );

    let config = ExtConvConfig::default();
    let result = convert_ext(&decl, &config);

    assert!(result.decl.recursive);
    assert_eq!(result.stats.decls_processed, 1);
}

#[test]
fn test_deeply_nested_code() {
    // 10-deep let chain
    let mut body = Code::ret(fvar(10));
    for i in (1..=10).rev() {
        body = Code::let_bind(let_decl(i as u64, LetValue::nat(i as u64)), body);
    }
    let decl = simple_decl("test", vec![], body);

    let config = ExtConvConfig::default();
    let result = convert_ext(&decl, &config);

    assert!(result.stats.lets_flattened >= 9);
    assert_eq!(result.stats.decls_processed, 1);
}

// ─── Combined Pass Tests ────────────────────────────────────────────────────

#[test]
fn test_all_passes_combined() {
    // Build a declaration that exercises multiple passes:
    // fun f(x) := return x; let y = g(erased, x); cases { _ => return y }
    let fun = fun_decl(1, vec![param(2, "x")], Code::ret(fvar(2)));
    let cases = Cases::new(
        Name::from_string("Unit"),
        nat_ty(),
        fvar(3),
        vec![Alt::default(Code::ret(fvar(3)))],
    );
    let inner = Code::let_bind(
        LetDecl::new(
            fvar(3),
            Name::anon(),
            nat_ty(),
            LetValue::Const {
                name: Name::from_string("g"),
                levels: vec![],
                args: vec![Arg::Erased, Arg::FVar(fvar(0))],
            },
        ),
        Code::Cases(cases),
    );
    let body = Code::fun(fun, inner);
    let decl = simple_decl("test", vec![param(0, "x")], body);

    let config = ExtConvConfig::default();
    let result = convert_ext(&decl, &config);

    // Multiple passes should have fired
    assert!(
        result.stats.lambdas_lifted > 0
            || result.stats.cases_simplified > 0
            || result.stats.erased_args_eliminated > 0
    );
    assert_eq!(result.stats.decls_processed, 1);
}

// ─── Helpers ────────────────────────────────────────────────────────────────

/// Config with all passes disabled (for isolating individual pass tests).
fn disabled_config() -> ExtConvConfig {
    ExtConvConfig {
        lambda_lifting: false,
        let_flattening: false,
        case_simplification: false,
        eta_reduction: false,
        beta_reduction: false,
        join_point_detection: false,
        erased_arg_elimination: false,
        validate: false,
    }
}

/// Extension trait for mutating ConvStats in tests.
trait ConvStatsTap {
    fn tap(self, f: impl FnOnce(&mut Self)) -> Self;
}

impl ConvStatsTap for ConvStats {
    fn tap(mut self, f: impl FnOnce(&mut Self)) -> Self {
        f(&mut self);
        self
    }
}
