// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the extended macro command analysis module.

use crate::macro_cmd::{MacroDef, MacroPatternPart, MacroRegistry, MacroScoping};
use crate::macro_cmd_ext::*;
use clean_parser::{Span, SurfaceArg, SurfaceExpr};

// =============================================================================
// Helpers
// =============================================================================

fn ident(name: &str) -> SurfaceExpr {
    SurfaceExpr::Ident(Span::new(0, 0), name.to_owned())
}

fn hole() -> SurfaceExpr {
    SurfaceExpr::Hole(Span::new(0, 0))
}

fn simple_macro(name: &str, template: SurfaceExpr, scoping: MacroScoping) -> MacroDef {
    MacroDef {
        name: name.to_owned(),
        pattern: vec![MacroPatternPart::Expr],
        expansion_template: template,
        scoping,
    }
}

// Test scaffolding not exercised by every including build — kept per the 2026-07-30
// keep-and-annotate sweep; see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md.
#[allow(dead_code)]
fn empty_macro(name: &str, template: SurfaceExpr) -> MacroDef {
    MacroDef {
        name: name.to_owned(),
        pattern: vec![],
        expansion_template: template,
        scoping: MacroScoping::Term,
    }
}

// =============================================================================
// Expansion tracing tests
// =============================================================================

#[test]
fn test_traced_expand_simple() {
    let mut reg = MacroRegistry::empty();
    reg.register(simple_macro("neg", ident("Bool.not"), MacroScoping::Term));

    let trace = traced_expand(&reg, "neg", &[ident("x")]).expect("should expand");
    assert_eq!(trace.steps.len(), 1);
    assert_eq!(trace.steps[0].macro_name, "neg");
    assert_eq!(trace.steps[0].arg_count, 1);
    assert_eq!(trace.steps[0].depth, 0);
    assert_eq!(trace.max_depth, 0);
}

#[test]
fn test_traced_expand_unknown_macro_returns_error() {
    let reg = MacroRegistry::empty();
    let result = traced_expand(&reg, "nonexistent", &[ident("x")]);
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(matches!(err, MacroAnalysisError::ExpansionFailed { .. }));
}

#[test]
fn test_traced_expand_preserves_final_expr() {
    let reg = MacroRegistry::new(); // has check, eval, print
    let trace = traced_expand(&reg, "check", &[ident("Nat")]).expect("should expand");
    // Final expr should be an App of #check to Nat
    match &trace.final_expr {
        SurfaceExpr::App(_, func, args) => {
            match func.as_ref() {
                SurfaceExpr::Ident(_, name) => assert_eq!(name, "#check"),
                other => panic!("expected Ident func, got {other:?}"),
            }
            assert_eq!(args.len(), 1);
        }
        other => panic!("expected App, got {other:?}"),
    }
}

#[test]
fn test_traced_expand_recursive_single_step() {
    let mut reg = MacroRegistry::empty();
    reg.register(simple_macro("wrap", ident("wrapper"), MacroScoping::Term));

    let trace = traced_expand_recursive(&reg, "wrap", &[ident("x")], 5).expect("should expand");
    assert_eq!(trace.steps.len(), 1);
    assert_eq!(trace.max_depth, 0);
}

#[test]
fn test_traced_expand_recursive_follows_chain() {
    let mut reg = MacroRegistry::empty();
    // "outer" expands to App(ident("inner"), [arg])
    // We need "outer" to produce an expression whose head is "inner"
    reg.register(simple_macro("outer", ident("inner"), MacroScoping::Term));
    reg.register(simple_macro("inner", ident("base"), MacroScoping::Term));

    let trace = traced_expand_recursive(&reg, "outer", &[ident("x")], 5).expect("should expand");
    // Should have 2 steps: outer -> inner
    assert!(trace.steps.len() >= 2);
    assert_eq!(trace.steps[0].macro_name, "outer");
    assert_eq!(trace.steps[1].macro_name, "inner");
}

#[test]
fn test_traced_expand_recursive_depth_exceeded() {
    let mut reg = MacroRegistry::empty();
    // Create a chain: a -> b -> c, with max_depth=0
    reg.register(simple_macro("a", ident("b"), MacroScoping::Term));
    reg.register(simple_macro("b", ident("c"), MacroScoping::Term));
    reg.register(simple_macro("c", ident("done"), MacroScoping::Term));

    let result = traced_expand_recursive(&reg, "a", &[ident("x")], 0);
    // depth=0 should succeed for the first step but the recursive call
    // at depth=1 would exceed. The first expansion at depth 0 succeeds.
    // It tries to recurse into "b" at depth=1 which is > max_depth=0.
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        MacroAnalysisError::DepthExceeded { .. }
    ));
}

// =============================================================================
// Macro pattern classification tests
// =============================================================================

#[test]
fn test_classify_terminal_macro() {
    let reg = MacroRegistry::empty();
    let def = simple_macro("foo", ident("bar"), MacroScoping::Term);
    assert_eq!(classify_macro(&reg, &def), MacroPattern::Terminal);
}

#[test]
fn test_classify_identity_macro() {
    let reg = MacroRegistry::empty();
    let def = MacroDef {
        name: "id".to_owned(),
        pattern: vec![MacroPatternPart::Expr],
        expansion_template: hole(),
        scoping: MacroScoping::Term,
    };
    assert_eq!(classify_macro(&reg, &def), MacroPattern::Identity);
}

#[test]
fn test_classify_self_recursive_macro() {
    let reg = MacroRegistry::empty();
    let def = MacroDef {
        name: "rec".to_owned(),
        pattern: vec![MacroPatternPart::Expr],
        expansion_template: ident("rec"),
        scoping: MacroScoping::Term,
    };
    assert_eq!(classify_macro(&reg, &def), MacroPattern::SelfRecursive);
}

#[test]
fn test_classify_delegates_to_other() {
    let mut reg = MacroRegistry::empty();
    reg.register(simple_macro("target", ident("impl"), MacroScoping::Term));
    let def = simple_macro("wrapper", ident("target"), MacroScoping::Term);
    assert_eq!(classify_macro(&reg, &def), MacroPattern::DelegatesToOther);
}

#[test]
fn test_classify_all_builtins() {
    let reg = MacroRegistry::new();
    let classifications = classify_all(&reg);
    assert_eq!(classifications.len(), 3);
    // All builtins are terminal (templates are idents not referencing other macros)
    for pattern in classifications.values() {
        assert_eq!(*pattern, MacroPattern::Terminal);
    }
}

#[test]
fn test_classify_terminal_no_names() {
    let reg = MacroRegistry::empty();
    // A macro with a literal template (no idents)
    let def = MacroDef {
        name: "lit".to_owned(),
        pattern: vec![],
        expansion_template: SurfaceExpr::Lit(Span::new(0, 0), clean_parser::SurfaceLit::Nat(42)),
        scoping: MacroScoping::Term,
    };
    assert_eq!(classify_macro(&reg, &def), MacroPattern::Terminal);
}

// =============================================================================
// Hygiene validation tests
// =============================================================================

#[test]
fn test_hygiene_clean_macro_no_issues_above_info() {
    let reg = MacroRegistry::empty();
    let def = simple_macro("clean", ident("helper"), MacroScoping::Term);
    let issues = validate_hygiene(&reg, &def);
    // Should have no warnings or errors (may have info)
    let non_info: Vec<_> = issues
        .iter()
        .filter(|i| i.severity != HygieneSeverity::Info)
        .collect();
    assert!(
        non_info.is_empty(),
        "unexpected non-info issues: {non_info:?}"
    );
}

#[test]
fn test_hygiene_self_reference_warning() {
    let reg = MacroRegistry::empty();
    let def = MacroDef {
        name: "loop".to_owned(),
        pattern: vec![MacroPatternPart::Expr],
        expansion_template: ident("loop"),
        scoping: MacroScoping::Term,
    };
    let issues = validate_hygiene(&reg, &def);
    let warnings: Vec<_> = issues
        .iter()
        .filter(|i| i.severity == HygieneSeverity::Warning)
        .collect();
    assert!(!warnings.is_empty(), "expected self-reference warning");
    assert!(warnings[0].detail.contains("own name"));
}

#[test]
fn test_hygiene_common_name_info() {
    let reg = MacroRegistry::empty();
    let def = simple_macro("uses_nat", ident("Nat"), MacroScoping::Term);
    let issues = validate_hygiene(&reg, &def);
    let infos: Vec<_> = issues
        .iter()
        .filter(|i| i.severity == HygieneSeverity::Info)
        .collect();
    assert!(!infos.is_empty(), "expected info about common name");
    assert!(infos[0].detail.contains("Nat"));
}

#[test]
fn test_hygiene_unbound_holes_error() {
    let reg = MacroRegistry::empty();
    // Template has a hole but pattern has no Expr slots
    let def = MacroDef {
        name: "bad".to_owned(),
        pattern: vec![MacroPatternPart::Keyword("kw".to_owned())],
        expansion_template: hole(),
        scoping: MacroScoping::Term,
    };
    let issues = validate_hygiene(&reg, &def);
    let errors: Vec<_> = issues
        .iter()
        .filter(|i| i.severity == HygieneSeverity::Error)
        .collect();
    assert!(!errors.is_empty(), "expected error about unbound holes");
    assert!(errors[0].detail.contains("hole"));
}

#[test]
fn test_validate_all_hygiene_empty_registry() {
    let reg = MacroRegistry::empty();
    let issues = validate_all_hygiene(&reg);
    assert!(issues.is_empty());
}

#[test]
fn test_validate_all_hygiene_builtins() {
    let reg = MacroRegistry::new();
    let issues = validate_all_hygiene(&reg);
    // Builtins should be clean (no warnings/errors, maybe info)
    let non_info: Vec<_> = issues
        .iter()
        .filter(|i| i.severity != HygieneSeverity::Info)
        .collect();
    assert!(
        non_info.is_empty(),
        "builtins had non-info issues: {non_info:?}"
    );
}

// =============================================================================
// Expansion statistics tests
// =============================================================================

#[test]
fn test_stats_new_is_empty() {
    let stats = ExpansionStats::new();
    assert_eq!(stats.total_expansions(), 0);
}

#[test]
fn test_stats_record_single_expansion() {
    let mut stats = ExpansionStats::new();
    let reg = MacroRegistry::new();
    let trace = traced_expand(&reg, "check", &[ident("x")]).unwrap();
    stats.record(&trace);

    assert_eq!(stats.total_expansions(), 1);
    assert_eq!(stats.count_for("check"), 1);
    assert_eq!(stats.count_for("eval"), 0);
}

#[test]
fn test_stats_accumulate_multiple_expansions() {
    let mut stats = ExpansionStats::new();
    let reg = MacroRegistry::new();

    for _ in 0..5 {
        let trace = traced_expand(&reg, "check", &[ident("x")]).unwrap();
        stats.record(&trace);
    }
    for _ in 0..3 {
        let trace = traced_expand(&reg, "eval", &[ident("y")]).unwrap();
        stats.record(&trace);
    }

    assert_eq!(stats.total_expansions(), 8);
    assert_eq!(stats.count_for("check"), 5);
    assert_eq!(stats.count_for("eval"), 3);
}

#[test]
fn test_stats_max_depth_tracking() {
    let mut stats = ExpansionStats::new();
    let reg = MacroRegistry::new();
    let trace = traced_expand(&reg, "check", &[ident("x")]).unwrap();
    stats.record(&trace);

    assert_eq!(stats.max_depth_for("check"), 0);
    assert_eq!(stats.max_depth_for("unknown"), 0);
}

#[test]
fn test_stats_reset() {
    let mut stats = ExpansionStats::new();
    let reg = MacroRegistry::new();
    let trace = traced_expand(&reg, "check", &[ident("x")]).unwrap();
    stats.record(&trace);
    assert_eq!(stats.total_expansions(), 1);

    stats.reset();
    assert_eq!(stats.total_expansions(), 0);
    assert_eq!(stats.count_for("check"), 0);
}

// =============================================================================
// Dependency graph tests
// =============================================================================

#[test]
fn test_dep_graph_empty_registry() {
    let reg = MacroRegistry::empty();
    let graph = MacroDependencyGraph::build(&reg);
    assert!(graph.edges.is_empty());
    assert!(graph.reverse_edges.is_empty());
}

#[test]
fn test_dep_graph_independent_macros() {
    let reg = MacroRegistry::new(); // check, eval, print — all independent
    let graph = MacroDependencyGraph::build(&reg);

    assert_eq!(graph.edges.len(), 3);
    // All builtins should have zero dependencies on each other
    for deps in graph.edges.values() {
        assert!(deps.is_empty());
    }
}

#[test]
fn test_dep_graph_with_delegation() {
    let mut reg = MacroRegistry::empty();
    reg.register(simple_macro("base", ident("impl"), MacroScoping::Term));
    reg.register(simple_macro("wrapper", ident("base"), MacroScoping::Term));

    let graph = MacroDependencyGraph::build(&reg);

    let wrapper_deps = graph.dependencies_of("wrapper");
    assert!(
        wrapper_deps.contains("base"),
        "wrapper should depend on base"
    );

    let base_deps = graph.dependencies_of("base");
    assert!(base_deps.is_empty(), "base should have no deps");

    let base_dependents = graph.dependents_of("base");
    assert!(base_dependents.contains("wrapper"));
}

#[test]
fn test_dep_graph_leaves_and_roots() {
    let mut reg = MacroRegistry::empty();
    reg.register(simple_macro("base", ident("impl"), MacroScoping::Term));
    reg.register(simple_macro("wrapper", ident("base"), MacroScoping::Term));

    let graph = MacroDependencyGraph::build(&reg);

    let leaves = graph.leaves();
    assert!(leaves.contains("base"), "base should be a leaf (no deps)");

    let roots = graph.roots();
    assert!(
        roots.contains("wrapper"),
        "wrapper should be a root (no dependents)"
    );
}

#[test]
fn test_dep_graph_no_cycle_in_independent() {
    let reg = MacroRegistry::new();
    let graph = MacroDependencyGraph::build(&reg);
    assert!(graph.detect_cycle().is_none());
}

#[test]
fn test_dep_graph_no_cycle_in_chain() {
    let mut reg = MacroRegistry::empty();
    reg.register(simple_macro("a", ident("b"), MacroScoping::Term));
    reg.register(simple_macro("b", ident("c"), MacroScoping::Term));
    reg.register(simple_macro("c", ident("end"), MacroScoping::Term));

    let graph = MacroDependencyGraph::build(&reg);
    assert!(graph.detect_cycle().is_none());
}

#[test]
fn test_dep_graph_detects_cycle() {
    let mut reg = MacroRegistry::empty();
    reg.register(simple_macro("x", ident("y"), MacroScoping::Term));
    reg.register(simple_macro("y", ident("x"), MacroScoping::Term));

    let graph = MacroDependencyGraph::build(&reg);
    let cycle = graph.detect_cycle();
    assert!(cycle.is_some(), "should detect x <-> y cycle");
    let cycle = cycle.unwrap();
    assert!(cycle.contains(&"x".to_owned()));
    assert!(cycle.contains(&"y".to_owned()));
}

#[test]
fn test_dep_graph_topological_order_independent() {
    let reg = MacroRegistry::new();
    let graph = MacroDependencyGraph::build(&reg);
    let order = graph.topological_order();
    assert!(order.is_some());
    let order = order.unwrap();
    assert_eq!(order.len(), 3);
}

#[test]
fn test_dep_graph_topological_order_cycle_returns_none() {
    let mut reg = MacroRegistry::empty();
    reg.register(simple_macro("x", ident("y"), MacroScoping::Term));
    reg.register(simple_macro("y", ident("x"), MacroScoping::Term));

    let graph = MacroDependencyGraph::build(&reg);
    assert!(graph.topological_order().is_none());
}

#[test]
fn test_dep_graph_dependencies_of_unknown() {
    let reg = MacroRegistry::new();
    let graph = MacroDependencyGraph::build(&reg);
    let deps = graph.dependencies_of("nonexistent");
    assert!(deps.is_empty());
}

// =============================================================================
// Template extraction tests
// =============================================================================

#[test]
fn test_extract_template_simple_ident() {
    let def = simple_macro("neg", ident("Bool.not"), MacroScoping::Term);
    let desc = extract_template(&def);

    assert_eq!(desc.name, "neg");
    assert_eq!(desc.parameters.len(), 1);
    assert_eq!(desc.parameters[0], "expr_0");
    assert_eq!(desc.scoping, MacroScoping::Term);
    assert!(desc.structure.contains("ident"));
}

#[test]
fn test_extract_template_hole() {
    let def = MacroDef {
        name: "id".to_owned(),
        pattern: vec![MacroPatternPart::Expr],
        expansion_template: hole(),
        scoping: MacroScoping::Term,
    };
    let desc = extract_template(&def);
    assert_eq!(desc.structure, "hole");
}

#[test]
fn test_extract_template_mixed_pattern() {
    let def = MacroDef {
        name: "ite".to_owned(),
        pattern: vec![
            MacroPatternPart::Keyword("if".to_owned()),
            MacroPatternPart::Expr,
            MacroPatternPart::Keyword("then".to_owned()),
            MacroPatternPart::Expr,
        ],
        expansion_template: ident("ite"),
        scoping: MacroScoping::Term,
    };
    let desc = extract_template(&def);
    // Only Expr slots become parameters
    assert_eq!(desc.parameters.len(), 2);
    assert_eq!(desc.parameters[0], "expr_1");
    assert_eq!(desc.parameters[1], "expr_3");
}

#[test]
fn test_extract_template_with_optional_and_sepby() {
    let def = MacroDef {
        name: "args".to_owned(),
        pattern: vec![
            MacroPatternPart::Ident,
            MacroPatternPart::OptionalExpr,
            MacroPatternPart::SepByExpr(",".to_owned()),
        ],
        expansion_template: ident("apply"),
        scoping: MacroScoping::Command,
    };
    let desc = extract_template(&def);
    assert_eq!(desc.parameters.len(), 3);
    assert!(desc.parameters[0].starts_with("ident_"));
    assert!(desc.parameters[1].starts_with("opt_expr_"));
    assert!(desc.parameters[2].starts_with("list_"));
    assert_eq!(desc.scoping, MacroScoping::Command);
}

#[test]
fn test_extract_all_templates_builtin_count() {
    let reg = MacroRegistry::new();
    let templates = extract_all_templates(&reg);
    assert_eq!(templates.len(), 3);
}

// =============================================================================
// Optimization hints tests
// =============================================================================

#[test]
fn test_optimization_identity_hint() {
    let mut reg = MacroRegistry::empty();
    reg.register(MacroDef {
        name: "id".to_owned(),
        pattern: vec![MacroPatternPart::Expr],
        expansion_template: hole(),
        scoping: MacroScoping::Term,
    });

    let hints = suggest_optimizations(&reg);
    let inline_hints: Vec<_> = hints
        .iter()
        .filter(|h| h.kind == OptimizationKind::Inline)
        .collect();
    assert!(
        !inline_hints.is_empty(),
        "expected inline hint for identity macro"
    );
    assert_eq!(inline_hints[0].macro_name, "id");
}

#[test]
fn test_optimization_merge_delegate_hint() {
    let mut reg = MacroRegistry::empty();
    reg.register(simple_macro("base", ident("impl"), MacroScoping::Term));
    reg.register(simple_macro("wrapper", ident("base"), MacroScoping::Term));

    let hints = suggest_optimizations(&reg);
    let merge_hints: Vec<_> = hints
        .iter()
        .filter(|h| h.kind == OptimizationKind::MergeDelegate && h.macro_name == "wrapper")
        .collect();
    assert!(
        !merge_hints.is_empty(),
        "expected merge-delegate hint for wrapper"
    );
}

#[test]
fn test_optimization_keyword_only_simplify() {
    let mut reg = MacroRegistry::empty();
    reg.register(MacroDef {
        name: "kw_only".to_owned(),
        pattern: vec![
            MacroPatternPart::Keyword("do".to_owned()),
            MacroPatternPart::Keyword("stuff".to_owned()),
        ],
        expansion_template: ident("action"),
        scoping: MacroScoping::Command,
    });

    let hints = suggest_optimizations(&reg);
    let simplify_hints: Vec<_> = hints
        .iter()
        .filter(|h| h.kind == OptimizationKind::Simplify)
        .collect();
    assert!(
        !simplify_hints.is_empty(),
        "expected simplify hint for keyword-only"
    );
}

#[test]
fn test_optimization_no_hints_for_clean_macros() {
    let mut reg = MacroRegistry::empty();
    // A well-defined macro with no obvious optimizations
    reg.register(MacroDef {
        name: "check2".to_owned(),
        pattern: vec![MacroPatternPart::Expr, MacroPatternPart::Expr],
        expansion_template: ident("custom_check"),
        scoping: MacroScoping::Command,
    });

    let hints = suggest_optimizations(&reg);
    let relevant: Vec<_> = hints.iter().filter(|h| h.macro_name == "check2").collect();
    assert!(
        relevant.is_empty(),
        "expected no hints for clean macro, got: {relevant:?}"
    );
}

// =============================================================================
// Error display tests
// =============================================================================

#[test]
fn test_error_display_expansion_failed() {
    let err = MacroAnalysisError::ExpansionFailed {
        name: "foo".to_owned(),
        source: crate::macro_cmd::MacroError::UnknownMacro("foo".to_owned()),
    };
    let msg = err.to_string();
    assert!(msg.contains("foo"));
    assert!(msg.contains("expansion trace failed"));
}

#[test]
fn test_error_display_depth_exceeded() {
    let err = MacroAnalysisError::DepthExceeded {
        name: "deep".to_owned(),
        max_depth: 10,
    };
    let msg = err.to_string();
    assert!(msg.contains("deep"));
    assert!(msg.contains("10"));
}

#[test]
fn test_error_display_cycle_detected() {
    let err = MacroAnalysisError::CycleDetected {
        cycle: vec!["a".to_owned(), "b".to_owned(), "a".to_owned()],
    };
    let msg = err.to_string();
    assert!(msg.contains("cycle"));
}

#[test]
fn test_error_display_hygiene_violation() {
    let err = MacroAnalysisError::HygieneViolation {
        macro_name: "bad".to_owned(),
        detail: "captured variable".to_owned(),
    };
    let msg = err.to_string();
    assert!(msg.contains("bad"));
    assert!(msg.contains("captured variable"));
}

// =============================================================================
// Edge case tests
// =============================================================================

#[test]
fn test_classify_macro_empty_template_names() {
    let reg = MacroRegistry::empty();
    // Literal template — no names
    let def = MacroDef {
        name: "num".to_owned(),
        pattern: vec![],
        expansion_template: SurfaceExpr::Lit(Span::new(0, 0), clean_parser::SurfaceLit::Nat(0)),
        scoping: MacroScoping::Term,
    };
    assert_eq!(classify_macro(&reg, &def), MacroPattern::Terminal);
}

#[test]
fn test_dep_graph_self_reference_not_edge() {
    let mut reg = MacroRegistry::empty();
    // Self-referencing macro should NOT have a self-edge in the dep graph
    reg.register(MacroDef {
        name: "self_ref".to_owned(),
        pattern: vec![MacroPatternPart::Expr],
        expansion_template: ident("self_ref"),
        scoping: MacroScoping::Term,
    });

    let graph = MacroDependencyGraph::build(&reg);
    let deps = graph.dependencies_of("self_ref");
    assert!(
        !deps.contains("self_ref"),
        "self-reference should not create dep edge"
    );
}

#[test]
fn test_hygiene_multiple_common_names() {
    let reg = MacroRegistry::empty();
    let def = MacroDef {
        name: "multi".to_owned(),
        pattern: vec![MacroPatternPart::Expr],
        expansion_template: SurfaceExpr::App(
            Span::new(0, 0),
            Box::new(ident("Nat")),
            vec![SurfaceArg::positional(ident("Bool"))],
        ),
        scoping: MacroScoping::Term,
    };
    let issues = validate_hygiene(&reg, &def);
    let infos: Vec<_> = issues
        .iter()
        .filter(|i| i.severity == HygieneSeverity::Info)
        .collect();
    assert!(infos.len() >= 2, "expected info for both Nat and Bool");
}

#[test]
fn test_stats_output_size_tracked() {
    let mut stats = ExpansionStats::new();
    let reg = MacroRegistry::new();

    let trace = traced_expand(&reg, "check", &[ident("x")]).unwrap();
    stats.record(&trace);

    let size = stats.output_sizes.get("check");
    assert!(size.is_some(), "output size should be tracked");
    assert!(*size.unwrap() > 0, "output size should be positive");
}

#[test]
fn test_extract_template_app_structure() {
    let def = MacroDef {
        name: "app_macro".to_owned(),
        pattern: vec![MacroPatternPart::Expr],
        expansion_template: SurfaceExpr::App(
            Span::new(0, 0),
            Box::new(ident("f")),
            vec![SurfaceArg::positional(ident("g"))],
        ),
        scoping: MacroScoping::Term,
    };
    let desc = extract_template(&def);
    assert!(
        desc.structure.contains("app"),
        "expected app in structure description"
    );
}

#[test]
fn test_traced_expand_hole_template() {
    let mut reg = MacroRegistry::empty();
    reg.register(MacroDef {
        name: "pass".to_owned(),
        pattern: vec![MacroPatternPart::Expr],
        expansion_template: hole(),
        scoping: MacroScoping::Term,
    });

    let trace = traced_expand(&reg, "pass", &[ident("val")]).expect("should expand");
    // Hole template substitutes first arg
    match &trace.final_expr {
        SurfaceExpr::Ident(_, name) => assert_eq!(name, "val"),
        other => panic!("expected Ident, got {other:?}"),
    }
}
