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

fn ident(name: clean_parser::SurfaceName) -> SurfaceExpr {
    SurfaceExpr::Ident(Span::new(0, 0), name)
}

fn hole() -> SurfaceExpr {
    SurfaceExpr::Hole(Span::new(0, 0))
}

fn simple_macro(
    name: clean_parser::SurfaceName,
    template: SurfaceExpr,
    scoping: MacroScoping,
) -> MacroDef {
    MacroDef {
        name,
        pattern: vec![MacroPatternPart::Expr],
        expansion_template: template,
        scoping,
    }
}

// Test scaffolding not exercised by every including build — kept per the 2026-07-30
// keep-and-annotate sweep; see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md.
#[allow(dead_code)]
fn empty_macro(name: clean_parser::SurfaceName, template: SurfaceExpr) -> MacroDef {
    MacroDef {
        name,
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
    reg.register(simple_macro(
        clean_parser::SurfaceName::generated_path("neg"),
        ident(clean_parser::SurfaceName::generated_path("Bool.not")),
        MacroScoping::Term,
    ));

    let trace = traced_expand(
        &reg,
        &clean_parser::SurfaceName::generated_path("neg"),
        &[ident(clean_parser::SurfaceName::generated_path("x"))],
    )
    .expect("should expand");
    assert_eq!(trace.steps.len(), 1);
    assert_eq!(
        trace.steps[0].macro_name,
        clean_parser::SurfaceName::generated_path("neg")
    );
    assert_eq!(trace.steps[0].arg_count, 1);
    assert_eq!(trace.steps[0].depth, 0);
    assert_eq!(trace.max_depth, 0);
}

#[test]
fn test_traced_expand_unknown_macro_returns_error() {
    let reg = MacroRegistry::empty();
    let result = traced_expand(
        &reg,
        &clean_parser::SurfaceName::generated_path("nonexistent"),
        &[ident(clean_parser::SurfaceName::generated_path("x"))],
    );
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(matches!(err, MacroAnalysisError::ExpansionFailed { .. }));
}

#[test]
fn test_traced_expand_preserves_final_expr() {
    let reg = MacroRegistry::new(); // has check, eval, print
    let trace = traced_expand(
        &reg,
        &clean_parser::SurfaceName::generated_path("check"),
        &[ident(clean_parser::SurfaceName::generated_path("Nat"))],
    )
    .expect("should expand");
    // Final expr should be an App of #check to Nat
    match &trace.final_expr {
        SurfaceExpr::App(_, func, args) => {
            match func.as_ref() {
                SurfaceExpr::Ident(_, name) => {
                    assert_eq!(name, &clean_parser::SurfaceName::generated_path("#check"))
                }
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
    reg.register(simple_macro(
        clean_parser::SurfaceName::generated_path("wrap"),
        ident(clean_parser::SurfaceName::generated_path("wrapper")),
        MacroScoping::Term,
    ));

    let trace = traced_expand_recursive(
        &reg,
        &clean_parser::SurfaceName::generated_path("wrap"),
        &[ident(clean_parser::SurfaceName::generated_path("x"))],
        5,
    )
    .expect("should expand");
    assert_eq!(trace.steps.len(), 1);
    assert_eq!(trace.max_depth, 0);
}

#[test]
fn test_traced_expand_recursive_follows_chain() {
    let mut reg = MacroRegistry::empty();
    // "outer" expands to App(ident("inner"), [arg])
    // We need "outer" to produce an expression whose head is "inner"
    reg.register(simple_macro(
        clean_parser::SurfaceName::generated_path("outer"),
        ident(clean_parser::SurfaceName::generated_path("inner")),
        MacroScoping::Term,
    ));
    reg.register(simple_macro(
        clean_parser::SurfaceName::generated_path("inner"),
        ident(clean_parser::SurfaceName::generated_path("base")),
        MacroScoping::Term,
    ));

    let trace = traced_expand_recursive(
        &reg,
        &clean_parser::SurfaceName::generated_path("outer"),
        &[ident(clean_parser::SurfaceName::generated_path("x"))],
        5,
    )
    .expect("should expand");
    // Should have 2 steps: outer -> inner
    assert!(trace.steps.len() >= 2);
    assert_eq!(
        trace.steps[0].macro_name,
        clean_parser::SurfaceName::generated_path("outer")
    );
    assert_eq!(
        trace.steps[1].macro_name,
        clean_parser::SurfaceName::generated_path("inner")
    );
}

#[test]
fn test_traced_expand_recursive_depth_exceeded() {
    let mut reg = MacroRegistry::empty();
    // Create a chain: a -> b -> c, with max_depth=0
    reg.register(simple_macro(
        clean_parser::SurfaceName::generated_path("a"),
        ident(clean_parser::SurfaceName::generated_path("b")),
        MacroScoping::Term,
    ));
    reg.register(simple_macro(
        clean_parser::SurfaceName::generated_path("b"),
        ident(clean_parser::SurfaceName::generated_path("c")),
        MacroScoping::Term,
    ));
    reg.register(simple_macro(
        clean_parser::SurfaceName::generated_path("c"),
        ident(clean_parser::SurfaceName::generated_path("done")),
        MacroScoping::Term,
    ));

    let result = traced_expand_recursive(
        &reg,
        &clean_parser::SurfaceName::generated_path("a"),
        &[ident(clean_parser::SurfaceName::generated_path("x"))],
        0,
    );
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
    let def = simple_macro(
        clean_parser::SurfaceName::generated_path("foo"),
        ident(clean_parser::SurfaceName::generated_path("bar")),
        MacroScoping::Term,
    );
    assert_eq!(classify_macro(&reg, &def), MacroPattern::Terminal);
}

#[test]
fn test_classify_identity_macro() {
    let reg = MacroRegistry::empty();
    let def = MacroDef {
        name: clean_parser::SurfaceName::generated_path("id"),
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
        name: clean_parser::SurfaceName::generated_path("rec"),
        pattern: vec![MacroPatternPart::Expr],
        expansion_template: ident(clean_parser::SurfaceName::generated_path("rec")),
        scoping: MacroScoping::Term,
    };
    assert_eq!(classify_macro(&reg, &def), MacroPattern::SelfRecursive);
}

#[test]
fn test_classify_delegates_to_other() {
    let mut reg = MacroRegistry::empty();
    reg.register(simple_macro(
        clean_parser::SurfaceName::generated_path("target"),
        ident(clean_parser::SurfaceName::generated_path("impl")),
        MacroScoping::Term,
    ));
    let def = simple_macro(
        clean_parser::SurfaceName::generated_path("wrapper"),
        ident(clean_parser::SurfaceName::generated_path("target")),
        MacroScoping::Term,
    );
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
        name: clean_parser::SurfaceName::generated_path("lit"),
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
    let def = simple_macro(
        clean_parser::SurfaceName::generated_path("clean"),
        ident(clean_parser::SurfaceName::generated_path("helper")),
        MacroScoping::Term,
    );
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
        name: clean_parser::SurfaceName::generated_path("loop"),
        pattern: vec![MacroPatternPart::Expr],
        expansion_template: ident(clean_parser::SurfaceName::generated_path("loop")),
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
    let def = simple_macro(
        clean_parser::SurfaceName::generated_path("uses_nat"),
        ident(clean_parser::SurfaceName::generated_path("Nat")),
        MacroScoping::Term,
    );
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
        name: clean_parser::SurfaceName::generated_path("bad"),
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
    let trace = traced_expand(
        &reg,
        &clean_parser::SurfaceName::generated_path("check"),
        &[ident(clean_parser::SurfaceName::generated_path("x"))],
    )
    .unwrap();
    stats.record(&trace);

    assert_eq!(stats.total_expansions(), 1);
    assert_eq!(
        stats.count_for(&clean_parser::SurfaceName::generated_path("check")),
        1
    );
    assert_eq!(
        stats.count_for(&clean_parser::SurfaceName::generated_path("eval")),
        0
    );
}

#[test]
fn test_stats_accumulate_multiple_expansions() {
    let mut stats = ExpansionStats::new();
    let reg = MacroRegistry::new();

    for _ in 0..5 {
        let trace = traced_expand(
            &reg,
            &clean_parser::SurfaceName::generated_path("check"),
            &[ident(clean_parser::SurfaceName::generated_path("x"))],
        )
        .unwrap();
        stats.record(&trace);
    }
    for _ in 0..3 {
        let trace = traced_expand(
            &reg,
            &clean_parser::SurfaceName::generated_path("eval"),
            &[ident(clean_parser::SurfaceName::generated_path("y"))],
        )
        .unwrap();
        stats.record(&trace);
    }

    assert_eq!(stats.total_expansions(), 8);
    assert_eq!(
        stats.count_for(&clean_parser::SurfaceName::generated_path("check")),
        5
    );
    assert_eq!(
        stats.count_for(&clean_parser::SurfaceName::generated_path("eval")),
        3
    );
}

#[test]
fn test_stats_max_depth_tracking() {
    let mut stats = ExpansionStats::new();
    let reg = MacroRegistry::new();
    let trace = traced_expand(
        &reg,
        &clean_parser::SurfaceName::generated_path("check"),
        &[ident(clean_parser::SurfaceName::generated_path("x"))],
    )
    .unwrap();
    stats.record(&trace);

    assert_eq!(
        stats.max_depth_for(&clean_parser::SurfaceName::generated_path("check")),
        0
    );
    assert_eq!(
        stats.max_depth_for(&clean_parser::SurfaceName::generated_path("unknown")),
        0
    );
}

#[test]
fn test_stats_reset() {
    let mut stats = ExpansionStats::new();
    let reg = MacroRegistry::new();
    let trace = traced_expand(
        &reg,
        &clean_parser::SurfaceName::generated_path("check"),
        &[ident(clean_parser::SurfaceName::generated_path("x"))],
    )
    .unwrap();
    stats.record(&trace);
    assert_eq!(stats.total_expansions(), 1);

    stats.reset();
    assert_eq!(stats.total_expansions(), 0);
    assert_eq!(
        stats.count_for(&clean_parser::SurfaceName::generated_path("check")),
        0
    );
}

#[path = "macro_cmd_ext_dependency_graph_tests.rs"]
mod dependency_graph_tests;

// =============================================================================
// Template extraction tests
// =============================================================================

#[test]
fn test_extract_template_simple_ident() {
    let def = simple_macro(
        clean_parser::SurfaceName::generated_path("neg"),
        ident(clean_parser::SurfaceName::generated_path("Bool.not")),
        MacroScoping::Term,
    );
    let desc = extract_template(&def);

    assert_eq!(desc.name, clean_parser::SurfaceName::generated_path("neg"));
    assert_eq!(desc.parameters.len(), 1);
    assert_eq!(desc.parameters[0], "expr_0");
    assert_eq!(desc.scoping, MacroScoping::Term);
    assert!(desc.structure.contains("ident"));
}

#[test]
fn test_extract_template_hole() {
    let def = MacroDef {
        name: clean_parser::SurfaceName::generated_path("id"),
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
        name: clean_parser::SurfaceName::generated_path("ite"),
        pattern: vec![
            MacroPatternPart::Keyword("if".to_owned()),
            MacroPatternPart::Expr,
            MacroPatternPart::Keyword("then".to_owned()),
            MacroPatternPart::Expr,
        ],
        expansion_template: ident(clean_parser::SurfaceName::generated_path("ite")),
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
        name: clean_parser::SurfaceName::generated_path("args"),
        pattern: vec![
            MacroPatternPart::Ident,
            MacroPatternPart::OptionalExpr,
            MacroPatternPart::SepByExpr(",".to_owned()),
        ],
        expansion_template: ident(clean_parser::SurfaceName::generated_path("apply")),
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
        name: clean_parser::SurfaceName::generated_path("id"),
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
    assert_eq!(
        inline_hints[0].macro_name,
        clean_parser::SurfaceName::generated_path("id")
    );
}

#[test]
fn test_optimization_merge_delegate_hint() {
    let mut reg = MacroRegistry::empty();
    reg.register(simple_macro(
        clean_parser::SurfaceName::generated_path("base"),
        ident(clean_parser::SurfaceName::generated_path("impl")),
        MacroScoping::Term,
    ));
    reg.register(simple_macro(
        clean_parser::SurfaceName::generated_path("wrapper"),
        ident(clean_parser::SurfaceName::generated_path("base")),
        MacroScoping::Term,
    ));

    let hints = suggest_optimizations(&reg);
    let merge_hints: Vec<_> = hints
        .iter()
        .filter(|h| {
            h.kind == OptimizationKind::MergeDelegate
                && h.macro_name == clean_parser::SurfaceName::generated_path("wrapper")
        })
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
        name: clean_parser::SurfaceName::generated_path("kw_only"),
        pattern: vec![
            MacroPatternPart::Keyword("do".to_owned()),
            MacroPatternPart::Keyword("stuff".to_owned()),
        ],
        expansion_template: ident(clean_parser::SurfaceName::generated_path("action")),
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
        name: clean_parser::SurfaceName::generated_path("check2"),
        pattern: vec![MacroPatternPart::Expr, MacroPatternPart::Expr],
        expansion_template: ident(clean_parser::SurfaceName::generated_path("custom_check")),
        scoping: MacroScoping::Command,
    });

    let hints = suggest_optimizations(&reg);
    let relevant: Vec<_> = hints
        .iter()
        .filter(|h| h.macro_name == clean_parser::SurfaceName::generated_path("check2"))
        .collect();
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
        name: clean_parser::SurfaceName::generated_path("foo"),
        source: crate::macro_cmd::MacroError::UnknownMacro(
            clean_parser::SurfaceName::generated_path("foo"),
        ),
    };
    let msg = err.to_string();
    assert!(msg.contains("foo"));
    assert!(msg.contains("expansion trace failed"));
}

#[test]
fn test_error_display_depth_exceeded() {
    let err = MacroAnalysisError::DepthExceeded {
        name: clean_parser::SurfaceName::generated_path("deep"),
        max_depth: 10,
    };
    let msg = err.to_string();
    assert!(msg.contains("deep"));
    assert!(msg.contains("10"));
}

#[test]
fn test_error_display_cycle_detected() {
    let err = MacroAnalysisError::CycleDetected {
        cycle: vec![
            clean_parser::SurfaceName::generated_path("a"),
            clean_parser::SurfaceName::generated_path("b"),
            clean_parser::SurfaceName::generated_path("a"),
        ],
    };
    let msg = err.to_string();
    assert!(msg.contains("cycle"));
}

#[test]
fn test_error_display_hygiene_violation() {
    let err = MacroAnalysisError::HygieneViolation {
        macro_name: clean_parser::SurfaceName::generated_path("bad"),
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
        name: clean_parser::SurfaceName::generated_path("num"),
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
        name: clean_parser::SurfaceName::generated_path("self_ref"),
        pattern: vec![MacroPatternPart::Expr],
        expansion_template: ident(clean_parser::SurfaceName::generated_path("self_ref")),
        scoping: MacroScoping::Term,
    });

    let graph = MacroDependencyGraph::build(&reg);
    let deps = graph.dependencies_of(&clean_parser::SurfaceName::generated_path("self_ref"));
    assert!(
        !deps.contains(&clean_parser::SurfaceName::generated_path("self_ref")),
        "self-reference should not create dep edge"
    );
}

#[test]
fn test_hygiene_multiple_common_names() {
    let reg = MacroRegistry::empty();
    let def = MacroDef {
        name: clean_parser::SurfaceName::generated_path("multi"),
        pattern: vec![MacroPatternPart::Expr],
        expansion_template: SurfaceExpr::App(
            Span::new(0, 0),
            Box::new(ident(clean_parser::SurfaceName::generated_path("Nat"))),
            vec![SurfaceArg::positional(ident(
                clean_parser::SurfaceName::generated_path("Bool"),
            ))],
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

    let trace = traced_expand(
        &reg,
        &clean_parser::SurfaceName::generated_path("check"),
        &[ident(clean_parser::SurfaceName::generated_path("x"))],
    )
    .unwrap();
    stats.record(&trace);

    let size = stats
        .output_sizes
        .get(&clean_parser::SurfaceName::generated_path("check"));
    assert!(size.is_some(), "output size should be tracked");
    assert!(*size.unwrap() > 0, "output size should be positive");
}

#[test]
fn test_extract_template_app_structure() {
    let def = MacroDef {
        name: clean_parser::SurfaceName::generated_path("app_macro"),
        pattern: vec![MacroPatternPart::Expr],
        expansion_template: SurfaceExpr::App(
            Span::new(0, 0),
            Box::new(ident(clean_parser::SurfaceName::generated_path("f"))),
            vec![SurfaceArg::positional(ident(
                clean_parser::SurfaceName::generated_path("g"),
            ))],
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
        name: clean_parser::SurfaceName::generated_path("pass"),
        pattern: vec![MacroPatternPart::Expr],
        expansion_template: hole(),
        scoping: MacroScoping::Term,
    });

    let trace = traced_expand(
        &reg,
        &clean_parser::SurfaceName::generated_path("pass"),
        &[ident(clean_parser::SurfaceName::generated_path("val"))],
    )
    .expect("should expand");
    // Hole template substitutes first arg
    match &trace.final_expr {
        SurfaceExpr::Ident(_, name) => {
            assert_eq!(name, &clean_parser::SurfaceName::generated_path("val"))
        }
        other => panic!("expected Ident, got {other:?}"),
    }
}
