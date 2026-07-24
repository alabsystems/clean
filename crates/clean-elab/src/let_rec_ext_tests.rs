// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended let-rec elaboration module.

use clean_kernel::expr::BinderInfo;
use clean_kernel::name::Name;
use clean_kernel::sorry::create_sorry_term;
use clean_kernel::{Environment, Expr, ExprKind, FVarId};

use crate::let_rec_ext::*;

// =============================================================================
// Helper constructors
// =============================================================================

fn mk_binding(name: &str, params: Vec<(String, Expr)>, body: Expr) -> LetRecBinding {
    LetRecBinding {
        name: name.to_string(),
        params,
        return_type: None,
        body,
        fvar_id: 1,
    }
}

fn mk_binding_with_fvar(
    name: &str,
    params: Vec<(String, Expr)>,
    body: Expr,
    fvar_id: u64,
) -> LetRecBinding {
    LetRecBinding {
        name: name.to_string(),
        params,
        return_type: None,
        body,
        fvar_id,
    }
}

fn mk_binding_with_ret(
    name: &str,
    params: Vec<(String, Expr)>,
    ret: Expr,
    body: Expr,
) -> LetRecBinding {
    LetRecBinding {
        name: name.to_string(),
        params,
        return_type: Some(ret),
        body,
        fvar_id: 1,
    }
}

fn nat_ty() -> Expr {
    Expr::const_str("Nat")
}

fn sorry_term(goal_ty: &Expr) -> Expr {
    let env = Environment::with_prelude();
    create_sorry_term(&env, goal_ty)
}

fn fvar(id: u64) -> Expr {
    Expr::fvar(FVarId::new(id))
}

fn contains_const_name(expr: &Expr, target: &str) -> bool {
    match expr.kind() {
        ExprKind::Const(name, _) => name.to_string() == target,
        ExprKind::App(f, a) => contains_const_name(f, target) || contains_const_name(a, target),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            contains_const_name(ty, target) || contains_const_name(body, target)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            contains_const_name(ty, target)
                || contains_const_name(val, target)
                || contains_const_name(body, target)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => {
            contains_const_name(inner, target)
        }
        _ => false,
    }
}

// =============================================================================
// Config tests
// =============================================================================

#[test]
fn test_config_default_values() {
    let config = LetRecExtConfig::default();
    assert_eq!(config.max_mutual_depth, 16);
    assert!(config.enable_wf_fallback);
    assert!(config.enable_type_inference);
    assert!(config.enable_capture_analysis);
    assert_eq!(config.max_unfolding_depth, 32);
    assert!(!config.allow_partial_functions);
}

// =============================================================================
// Single recursive function
// =============================================================================

#[test]
fn test_build_single_non_recursive() {
    let config = LetRecExtConfig::default();
    let bindings = vec![(
        "f".into(),
        vec![("n".into(), nat_ty())],
        Some(nat_ty()),
        Expr::nat_lit(42),
    )];
    let block = build_mutual_block(&bindings, &config).unwrap();
    assert_eq!(block.bindings.len(), 1);
    assert_eq!(block.bindings[0].name, "f");
    assert!(matches!(block.metrics[0], TerminationMetric::Unguarded));
}

#[test]
fn test_build_single_recursive_wf_fallback() {
    let config = LetRecExtConfig::default();
    // Body references its own fvar_id (which will be 1 for the first binding)
    let body = Expr::app(fvar(1), Expr::bvar(0));
    let bindings = vec![(
        "f".into(),
        vec![("n".into(), nat_ty())],
        Some(nat_ty()),
        body,
    )];
    let block = build_mutual_block(&bindings, &config).unwrap();
    assert!(matches!(
        block.metrics[0],
        TerminationMetric::WellFounded { .. }
    ));
}

// =============================================================================
// Mutual let-rec (2 functions)
// =============================================================================

#[test]
fn test_mutual_two_functions_dep_graph() {
    let config = LetRecExtConfig::default();
    // f calls g (fvar 2), g calls f (fvar 1)
    let f_body = Expr::app(fvar(2), Expr::nat_lit(0));
    let g_body = Expr::app(fvar(1), Expr::nat_lit(1));
    let bindings = vec![
        (
            "f".into(),
            vec![("n".into(), nat_ty())],
            Some(nat_ty()),
            f_body,
        ),
        (
            "g".into(),
            vec![("m".into(), nat_ty())],
            Some(nat_ty()),
            g_body,
        ),
    ];
    let block = build_mutual_block(&bindings, &config).unwrap();
    assert_eq!(block.bindings.len(), 2);
    // f depends on g (idx 1), g depends on f (idx 0)
    assert!(block.dep_graph[0].contains(&1));
    assert!(block.dep_graph[1].contains(&0));
}

// =============================================================================
// Mutual let-rec (3 functions)
// =============================================================================

#[test]
fn test_mutual_three_functions() {
    let config = LetRecExtConfig::default();
    let f_body = Expr::app(fvar(2), Expr::nat_lit(0));
    let g_body = Expr::app(fvar(3), Expr::nat_lit(1));
    let h_body = Expr::nat_lit(0); // non-recursive
    let bindings = vec![
        ("f".into(), vec![], Some(nat_ty()), f_body),
        ("g".into(), vec![], Some(nat_ty()), g_body),
        ("h".into(), vec![], Some(nat_ty()), h_body),
    ];
    let block = build_mutual_block(&bindings, &config).unwrap();
    assert_eq!(block.bindings.len(), 3);
    assert!(matches!(block.metrics[2], TerminationMetric::Unguarded));
}

// =============================================================================
// Termination metric detection
// =============================================================================

#[test]
fn test_termination_unguarded_no_self_ref() {
    let binding = mk_binding("f", vec![("n".into(), nat_ty())], Expr::nat_lit(0));
    let metric = detect_termination_metric(&binding, std::slice::from_ref(&binding));
    assert!(matches!(metric, TerminationMetric::Unguarded));
}

#[test]
fn test_termination_wf_recursive_no_structural() {
    let body = Expr::app(fvar(1), Expr::bvar(0));
    let binding = mk_binding_with_fvar("f", vec![("n".into(), nat_ty())], body, 1);
    let metric = detect_termination_metric(&binding, std::slice::from_ref(&binding));
    assert!(matches!(metric, TerminationMetric::WellFounded { .. }));
}

#[test]
fn test_termination_wf_has_measure_and_relation() {
    let body = Expr::app(fvar(1), Expr::bvar(0));
    let binding = mk_binding_with_fvar("f", vec![("n".into(), nat_ty())], body, 1);
    let metric = detect_termination_metric(&binding, std::slice::from_ref(&binding));
    if let TerminationMetric::WellFounded { measure, relation } = &metric {
        // DENY_SORRY integration: WF fallback placeholders must not add
        // sorry/sorryAx terms just to keep the temporary encoding total.
        assert!(contains_const_name(measure, "Nat.succ"));
        assert!(contains_const_name(measure, "Nat.zero"));
        assert!(contains_const_name(relation, "WellFounded.placeholderRel"));
        assert!(!contains_const_name(measure, "sorryAx"));
        assert!(!contains_const_name(relation, "sorryAx"));
        assert!(!contains_const_name(measure, "sorry"));
        assert!(!contains_const_name(relation, "sorry"));
    } else {
        panic!("expected WellFounded metric");
    }
}

// =============================================================================
// WF recursion encoding
// =============================================================================

#[test]
fn test_encode_wf_recursion_produces_fix_app() {
    let body = Expr::app(fvar(1), Expr::bvar(0));
    let binding = mk_binding_with_ret("f", vec![("n".into(), nat_ty())], nat_ty(), body);
    let metric = TerminationMetric::WellFounded {
        measure: Expr::app(sorry_term(&Expr::arrow(nat_ty(), nat_ty())), nat_ty()),
        relation: Expr::prop(),
    };
    let encoded = encode_wf_recursion(&binding, &metric);
    // Should be an application: WellFounded.fix applied to args
    assert!(matches!(encoded.kind(), ExprKind::App(_, _)));
}

#[test]
fn test_encode_wf_recursion_default_metric_uses_no_sorry_placeholder() {
    let binding = mk_binding_with_ret(
        "f",
        vec![("n".into(), nat_ty())],
        nat_ty(),
        Expr::app(fvar(1), Expr::nat_lit(0)),
    );
    let encoded = encode_wf_recursion(&binding, &TerminationMetric::Unguarded);
    assert!(contains_const_name(&encoded, "Nat.succ"));
    assert!(contains_const_name(&encoded, "Nat.zero"));
    assert!(!contains_const_name(&encoded, "sorryAx"));
    assert!(!contains_const_name(&encoded, "sorry"));
}

// =============================================================================
// Type inference for return types
// =============================================================================

#[test]
fn test_infer_return_type_from_nat_lit() {
    let binding = mk_binding("f", vec![], Expr::nat_lit(42));
    let inferred = infer_return_type(&binding);
    assert!(inferred.is_some());
    // Inferred type for Nat literal should be Nat
    let ty = inferred.unwrap();
    assert!(matches!(ty.kind(), ExprKind::Const(_, _)));
}

#[test]
fn test_infer_return_type_preserves_existing() {
    let binding = mk_binding_with_ret("f", vec![], nat_ty(), Expr::nat_lit(42));
    let inferred = infer_return_type(&binding);
    assert!(inferred.is_some());
}

#[test]
fn test_infer_return_type_from_sort() {
    let binding = mk_binding("f", vec![], Expr::type_());
    let inferred = infer_return_type(&binding);
    assert!(inferred.is_some());
}

#[test]
fn test_infer_return_type_from_const() {
    let binding = mk_binding("f", vec![], Expr::const_str("Bool"));
    let inferred = infer_return_type(&binding);
    assert!(inferred.is_some());
    let ty = inferred.unwrap();
    assert!(matches!(ty.kind(), ExprKind::Const(_, _)));
}

#[test]
fn test_type_inference_disabled_errors() {
    let config = LetRecExtConfig {
        enable_type_inference: false,
        ..Default::default()
    };
    let bindings = vec![(
        "f".into(),
        vec![("n".into(), nat_ty())],
        None,
        Expr::nat_lit(42),
    )];
    let result = build_mutual_block(&bindings, &config);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        LetRecExtError::TypeInferenceFailed { .. }
    ));
}

// =============================================================================
// Capture analysis
// =============================================================================

#[test]
fn test_capture_analysis_no_captures() {
    let block = MutualBlock {
        bindings: vec![LetRecBinding {
            name: "f".into(),
            params: vec![],
            return_type: Some(nat_ty()),
            body: Expr::nat_lit(0),
            fvar_id: 1,
        }],
        dep_graph: vec![vec![]],
        metrics: vec![TerminationMetric::Unguarded],
    };
    let captures = analyze_captures(&block);
    assert_eq!(captures.len(), 1);
    assert!(captures[0].captured_fvars.is_empty());
}

#[test]
fn test_capture_analysis_with_external_fvar() {
    let body = Expr::app(fvar(999), Expr::nat_lit(0));
    let block = MutualBlock {
        bindings: vec![LetRecBinding {
            name: "f".into(),
            params: vec![],
            return_type: Some(nat_ty()),
            body,
            fvar_id: 1,
        }],
        dep_graph: vec![vec![]],
        metrics: vec![TerminationMetric::Unguarded],
    };
    let captures = analyze_captures(&block);
    assert_eq!(captures.len(), 1);
    assert!(captures[0].captured_fvars.contains(&999));
}

#[test]
fn test_capture_analysis_excludes_block_fvars() {
    let body = Expr::app(fvar(2), Expr::nat_lit(0));
    let block = MutualBlock {
        bindings: vec![
            LetRecBinding {
                name: "f".into(),
                params: vec![],
                return_type: Some(nat_ty()),
                body,
                fvar_id: 1,
            },
            LetRecBinding {
                name: "g".into(),
                params: vec![],
                return_type: Some(nat_ty()),
                body: Expr::nat_lit(0),
                fvar_id: 2,
            },
        ],
        dep_graph: vec![vec![1], vec![]],
        metrics: vec![TerminationMetric::Unguarded, TerminationMetric::Unguarded],
    };
    let captures = analyze_captures(&block);
    // f references g (fvar 2), but g is in the block so shouldn't be "captured"
    assert!(captures[0].captured_fvars.is_empty());
}

// =============================================================================
// Unfolding equation generation
// =============================================================================

#[test]
fn test_unfolding_equations_single_binding() {
    let block = MutualBlock {
        bindings: vec![LetRecBinding {
            name: "f".into(),
            params: vec![("n".into(), nat_ty())],
            return_type: Some(nat_ty()),
            body: Expr::nat_lit(0),
            fvar_id: 1,
        }],
        dep_graph: vec![vec![]],
        metrics: vec![TerminationMetric::Unguarded],
    };
    let eqs = generate_unfolding_equations(&block);
    assert_eq!(eqs.len(), 1);
    assert_eq!(eqs[0].name, "f");
    // Non-recursive binding should be marked as simp
    assert!(eqs[0].is_simp);
}

#[test]
fn test_unfolding_equations_recursive_not_simp() {
    let body = Expr::app(fvar(1), Expr::bvar(0));
    let block = MutualBlock {
        bindings: vec![LetRecBinding {
            name: "f".into(),
            params: vec![("n".into(), nat_ty())],
            return_type: Some(nat_ty()),
            body,
            fvar_id: 1,
        }],
        dep_graph: vec![vec![0]],
        metrics: vec![TerminationMetric::WellFounded {
            measure: Expr::prop(),
            relation: Expr::prop(),
        }],
    };
    let eqs = generate_unfolding_equations(&block);
    assert_eq!(eqs.len(), 1);
    // Recursive binding should NOT be marked as simp
    assert!(!eqs[0].is_simp);
}

#[test]
fn test_unfolding_equations_mutual_block() {
    let f_body = Expr::app(fvar(2), Expr::nat_lit(0));
    let g_body = Expr::nat_lit(1);
    let block = MutualBlock {
        bindings: vec![
            LetRecBinding {
                name: "f".into(),
                params: vec![],
                return_type: Some(nat_ty()),
                body: f_body,
                fvar_id: 1,
            },
            LetRecBinding {
                name: "g".into(),
                params: vec![],
                return_type: Some(nat_ty()),
                body: g_body,
                fvar_id: 2,
            },
        ],
        dep_graph: vec![vec![1], vec![]],
        metrics: vec![TerminationMetric::Unguarded, TerminationMetric::Unguarded],
    };
    let eqs = generate_unfolding_equations(&block);
    assert_eq!(eqs.len(), 2);
}

// =============================================================================
// Partial function handling
// =============================================================================

#[test]
fn test_partial_function_not_allowed_by_default() {
    let config = LetRecExtConfig::default();
    // Body contains "nomatch" marker
    let body = Expr::const_str("nomatch");
    let block = MutualBlock {
        bindings: vec![LetRecBinding {
            name: "f".into(),
            params: vec![],
            return_type: Some(nat_ty()),
            body,
            fvar_id: 1,
        }],
        dep_graph: vec![vec![]],
        metrics: vec![TerminationMetric::Unguarded],
    };
    let result = check_partial_functions(&block, &config);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        LetRecExtError::PartialFunctionNotAllowed { .. }
    ));
}

#[test]
fn test_partial_function_allowed_with_config() {
    let config = LetRecExtConfig {
        allow_partial_functions: true,
        ..Default::default()
    };
    let body = Expr::const_str("panic");
    let block = MutualBlock {
        bindings: vec![LetRecBinding {
            name: "f".into(),
            params: vec![],
            return_type: Some(nat_ty()),
            body,
            fvar_id: 1,
        }],
        dep_graph: vec![vec![]],
        metrics: vec![TerminationMetric::Unguarded],
    };
    let result = check_partial_functions(&block, &config);
    assert!(result.is_ok());
    let infos = result.unwrap();
    assert_eq!(infos.len(), 1);
    assert_eq!(infos[0].name, "f");
}

#[test]
fn test_partial_function_exhaustive_ok() {
    let config = LetRecExtConfig::default();
    let block = MutualBlock {
        bindings: vec![LetRecBinding {
            name: "f".into(),
            params: vec![],
            return_type: Some(nat_ty()),
            body: Expr::nat_lit(0),
            fvar_id: 1,
        }],
        dep_graph: vec![vec![]],
        metrics: vec![TerminationMetric::Unguarded],
    };
    let result = check_partial_functions(&block, &config);
    assert!(result.is_ok());
    assert!(result.unwrap().is_empty());
}

// =============================================================================
// Nested let-rec flattening
// =============================================================================

#[test]
fn test_flatten_no_lets() {
    let expr = Expr::nat_lit(42);
    let (bindings, body) = flatten_nested_let_recs(&expr);
    assert!(bindings.is_empty());
    assert!(matches!(body.kind(), ExprKind::Lit(_)));
}

#[test]
fn test_flatten_single_let() {
    let inner = Expr::let_named(
        Name::from_string("x"),
        nat_ty(),
        Expr::nat_lit(1),
        Expr::bvar(0),
        false,
    );
    let (bindings, _body) = flatten_nested_let_recs(&inner);
    assert_eq!(bindings.len(), 1);
    assert_eq!(bindings[0].name, "x");
}

#[test]
fn test_flatten_nested_two_lets() {
    let inner2 = Expr::let_named(
        Name::from_string("y"),
        nat_ty(),
        Expr::nat_lit(2),
        Expr::bvar(0),
        false,
    );
    let inner1 = Expr::let_named(
        Name::from_string("x"),
        nat_ty(),
        Expr::nat_lit(1),
        inner2,
        false,
    );
    let (bindings, _body) = flatten_nested_let_recs(&inner1);
    assert_eq!(bindings.len(), 2);
    assert_eq!(bindings[0].name, "x");
    assert_eq!(bindings[1].name, "y");
}

#[test]
fn test_flatten_deeply_nested() {
    // Build 5 nested lets
    let mut expr = Expr::nat_lit(0);
    for i in (0..5).rev() {
        expr = Expr::let_named(
            Name::from_string(&format!("v{i}")),
            nat_ty(),
            Expr::nat_lit(i as u64),
            expr,
            false,
        );
    }
    let (bindings, _body) = flatten_nested_let_recs(&expr);
    assert_eq!(bindings.len(), 5);
    assert_eq!(bindings[0].name, "v0");
    assert_eq!(bindings[4].name, "v4");
}

// =============================================================================
// Topological sort
// =============================================================================

#[test]
fn test_topo_sort_no_deps() {
    let dep_graph = vec![vec![], vec![], vec![]];
    let order = topological_sort_bindings(&dep_graph).unwrap();
    assert_eq!(order.len(), 3);
}

#[test]
fn test_topo_sort_linear_chain() {
    // 0 -> 1 -> 2
    let dep_graph = vec![vec![], vec![0], vec![1]];
    let order = topological_sort_bindings(&dep_graph).unwrap();
    assert_eq!(order.len(), 3);
    // 0 must come before 1, 1 before 2
    let pos = |idx: usize| order.iter().position(|&x| x == idx).unwrap();
    assert!(pos(0) < pos(1));
    assert!(pos(1) < pos(2));
}

#[test]
fn test_topo_sort_cycle_detected() {
    // 0 -> 1 -> 0 (cycle)
    let dep_graph = vec![vec![1], vec![0]];
    let result = topological_sort_bindings(&dep_graph);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        LetRecExtError::CyclicDependency { .. }
    ));
}

// =============================================================================
// Dep graph computation
// =============================================================================

#[test]
fn test_dep_graph_independent() {
    let bindings = vec![
        mk_binding_with_fvar("f", vec![], Expr::nat_lit(0), 1),
        mk_binding_with_fvar("g", vec![], Expr::nat_lit(1), 2),
    ];
    let graph = compute_dep_graph(&bindings);
    assert!(graph[0].is_empty());
    assert!(graph[1].is_empty());
}

#[test]
fn test_dep_graph_f_calls_g() {
    let bindings = vec![
        mk_binding_with_fvar("f", vec![], Expr::app(fvar(2), Expr::nat_lit(0)), 1),
        mk_binding_with_fvar("g", vec![], Expr::nat_lit(1), 2),
    ];
    let graph = compute_dep_graph(&bindings);
    assert_eq!(graph[0], vec![1]);
    assert!(graph[1].is_empty());
}

// =============================================================================
// Structural recursion encoding
// =============================================================================

#[test]
fn test_encode_structural_recursion_produces_rec() {
    let binding = LetRecBinding {
        name: "f".into(),
        params: vec![("n".into(), nat_ty())],
        return_type: Some(nat_ty()),
        body: Expr::nat_lit(0),
        fvar_id: 1,
    };
    let encoded = encode_structural_recursion(&binding, 0);
    assert!(matches!(encoded.kind(), ExprKind::App(_, _)));
}

// =============================================================================
// Error variants
// =============================================================================

#[test]
fn test_mutual_recursion_too_deep_error() {
    let config = LetRecExtConfig {
        max_mutual_depth: 2,
        ..Default::default()
    };
    let bindings: Vec<_> = (0..3)
        .map(|i| {
            (
                format!("f{i}"),
                vec![],
                Some(nat_ty()),
                Expr::nat_lit(i as u64),
            )
        })
        .collect();
    let result = build_mutual_block(&bindings, &config);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        LetRecExtError::MutualRecursionTooDeep { depth: 3, max: 2 }
    ));
}

#[test]
fn test_wf_fallback_disabled_error() {
    let config = LetRecExtConfig {
        enable_wf_fallback: false,
        ..Default::default()
    };
    // Recursive body referencing fvar 1
    let body = Expr::app(fvar(1), Expr::bvar(0));
    let bindings = vec![(
        "f".into(),
        vec![("n".into(), nat_ty())],
        Some(nat_ty()),
        body,
    )];
    let result = build_mutual_block(&bindings, &config);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        LetRecExtError::TerminationCheckFailed { .. }
    ));
}

// =============================================================================
// Edge cases
// =============================================================================

#[test]
fn test_empty_body_binding() {
    let config = LetRecExtConfig::default();
    let bindings = vec![("f".into(), vec![], Some(nat_ty()), sorry_term(&nat_ty()))];
    let block = build_mutual_block(&bindings, &config).unwrap();
    assert_eq!(block.bindings.len(), 1);
    assert!(matches!(block.metrics[0], TerminationMetric::Unguarded));
}

#[test]
fn test_non_recursive_let() {
    let config = LetRecExtConfig::default();
    let body = Expr::app(Expr::const_str("Nat.add"), Expr::nat_lit(1));
    let bindings = vec![(
        "f".into(),
        vec![("n".into(), nat_ty())],
        Some(nat_ty()),
        body,
    )];
    let block = build_mutual_block(&bindings, &config).unwrap();
    assert!(matches!(block.metrics[0], TerminationMetric::Unguarded));
}

#[test]
fn test_deeply_nested_body_lambda() {
    let config = LetRecExtConfig::default();
    // Build a deeply nested lambda: λ x. λ y. λ z. 0
    let body = Expr::lam(
        BinderInfo::Default,
        nat_ty(),
        Expr::lam(
            BinderInfo::Default,
            nat_ty(),
            Expr::lam(BinderInfo::Default, nat_ty(), Expr::nat_lit(0)),
        ),
    );
    let bindings = vec![("f".into(), vec![], Some(nat_ty()), body)];
    let block = build_mutual_block(&bindings, &config).unwrap();
    assert!(matches!(block.metrics[0], TerminationMetric::Unguarded));
}

#[test]
fn test_multiple_params_binding() {
    let config = LetRecExtConfig::default();
    let bindings = vec![(
        "f".into(),
        vec![
            ("a".into(), nat_ty()),
            ("b".into(), nat_ty()),
            ("c".into(), nat_ty()),
        ],
        Some(nat_ty()),
        Expr::nat_lit(0),
    )];
    let block = build_mutual_block(&bindings, &config).unwrap();
    assert_eq!(block.bindings[0].params.len(), 3);
}

#[test]
fn test_capture_with_nested_expr() {
    // Body has fvar 999 nested inside lambda and app
    let inner = Expr::app(fvar(999), Expr::nat_lit(0));
    let body = Expr::lam(BinderInfo::Default, nat_ty(), inner);
    let block = MutualBlock {
        bindings: vec![LetRecBinding {
            name: "f".into(),
            params: vec![],
            return_type: Some(nat_ty()),
            body,
            fvar_id: 1,
        }],
        dep_graph: vec![vec![]],
        metrics: vec![TerminationMetric::Unguarded],
    };
    let captures = analyze_captures(&block);
    assert!(captures[0].captured_fvars.contains(&999));
}
