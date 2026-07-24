// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended emission base.
//!
//! Part of #3084 - IO/FFI/Native.

use std::collections::BTreeSet;

use clean_kernel::Name;

use crate::emit_base_ext::{
    compare_backends, compute_emission_order, compute_output_stats, detect_name_collisions,
    format_ir_type, generate_decl_comment, generate_module_header, validate_declarations, Backend,
    CollisionReport, EmitConfig, EmitTarget, IssueSeverity, OptLevel, OutputStats,
};
use crate::ir::{FnId, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, VarId};

// ── Helpers ──

fn mk_name(s: &str) -> Name {
    Name::from_string(s)
}

fn simple_decl(name: &str, params: Vec<(VarId, IRType)>, ret_ty: IRType, body: IRBody) -> IRDecl {
    IRDecl {
        name: mk_name(name),
        params,
        return_type: ret_ty,
        body,
    }
}

fn ret_var(v: u32) -> IRBody {
    IRBody::Ret(IRArg::Var(VarId(v)))
}

fn ret_erased() -> IRBody {
    IRBody::Ret(IRArg::Erased)
}

fn call_body(callee: &str, arg: u32, result: u32) -> IRBody {
    IRBody::VDecl {
        var: VarId(result),
        ty: IRType::Object,
        value: IRExpr::Apply {
            fn_id: FnId(mk_name(callee)),
            args: vec![IRArg::Var(VarId(arg))],
        },
        rest: Box::new(ret_var(result)),
    }
}

// ── OutputStats tests ──

#[test]
fn test_output_stats_default_is_zero() {
    let s = OutputStats::default();
    assert_eq!(s.lines_of_code, 0);
    assert_eq!(s.declarations_emitted, 0);
    assert_eq!(s.comment_lines, 0);
    assert_eq!(s.blank_lines, 0);
    assert_eq!(s.total_lines(), 0);
}

#[test]
fn test_output_stats_merge() {
    let mut a = OutputStats {
        lines_of_code: 10,
        declarations_emitted: 2,
        comment_lines: 3,
        blank_lines: 1,
    };
    let b = OutputStats {
        lines_of_code: 5,
        declarations_emitted: 1,
        comment_lines: 2,
        blank_lines: 4,
    };
    a.merge(&b);
    assert_eq!(a.lines_of_code, 15);
    assert_eq!(a.declarations_emitted, 3);
    assert_eq!(a.comment_lines, 5);
    assert_eq!(a.blank_lines, 5);
}

#[test]
fn test_output_stats_total_lines() {
    let s = OutputStats {
        lines_of_code: 10,
        declarations_emitted: 0,
        comment_lines: 5,
        blank_lines: 3,
    };
    assert_eq!(s.total_lines(), 18);
}

#[test]
fn test_compute_stats_empty_text() {
    let s = compute_output_stats("", 0);
    assert_eq!(s.lines_of_code, 0);
    assert_eq!(s.comment_lines, 0);
    assert_eq!(s.blank_lines, 0);
}

#[test]
fn test_compute_stats_code_only() {
    let s = compute_output_stats("int x = 0;\nreturn x;\n", 1);
    assert_eq!(s.lines_of_code, 2);
    assert_eq!(s.declarations_emitted, 1);
    assert_eq!(s.comment_lines, 0);
    assert_eq!(s.blank_lines, 0);
}

#[test]
fn test_compute_stats_comments() {
    let text = "// header\n/* block */\nint x;\n";
    let s = compute_output_stats(text, 0);
    assert_eq!(s.comment_lines, 2);
    assert_eq!(s.lines_of_code, 1);
}

#[test]
fn test_compute_stats_blank_lines() {
    let text = "int x;\n\n  \nreturn;\n";
    let s = compute_output_stats(text, 0);
    assert_eq!(s.blank_lines, 2);
    assert_eq!(s.lines_of_code, 2);
}

#[test]
fn test_compute_stats_star_continuation() {
    let text = "/* start\n * middle\n */\ncode;\n";
    let s = compute_output_stats(text, 0);
    assert_eq!(s.comment_lines, 3);
    assert_eq!(s.lines_of_code, 1);
}

#[test]
fn test_compute_stats_mixed() {
    let text = "// comment\n\nint x;\nint y;\n// another\n\n";
    let s = compute_output_stats(text, 2);
    assert_eq!(s.comment_lines, 2);
    assert_eq!(s.lines_of_code, 2);
    assert_eq!(s.blank_lines, 2);
    assert_eq!(s.declarations_emitted, 2);
    assert_eq!(s.total_lines(), 6);
}

// ── Name collision detection tests ──

#[test]
fn test_no_collisions_distinct_names() {
    let names = vec![mk_name("foo"), mk_name("bar"), mk_name("baz")];
    let report = detect_name_collisions(&names);
    assert!(report.is_clean());
    assert_eq!(report.collision_count(), 0);
}

#[test]
fn test_no_collisions_empty() {
    let report = detect_name_collisions(&[]);
    assert!(report.is_clean());
}

#[test]
fn test_no_collisions_single_name() {
    let report = detect_name_collisions(&[mk_name("x")]);
    assert!(report.is_clean());
}

#[test]
fn test_collision_identical_names() {
    let names = vec![mk_name("foo"), mk_name("foo")];
    let report = detect_name_collisions(&names);
    // Same name mangles to the same thing, but only appears once in the set.
    // Since BTreeSet deduplicates, it's actually 1 entry -> no collision.
    assert!(report.is_clean());
}

#[test]
fn test_collision_report_methods() {
    // Manually construct to test methods.
    let mut collisions = std::collections::BTreeMap::new();
    let mut group = BTreeSet::new();
    group.insert("a".to_string());
    group.insert("b".to_string());
    collisions.insert("l_x".to_string(), group);
    let report = CollisionReport { collisions };
    assert!(!report.is_clean());
    assert_eq!(report.collision_count(), 1);
}

// ── Emission ordering tests ──

#[test]
fn test_emission_order_empty() {
    let order = compute_emission_order(&[]).unwrap();
    assert!(order.is_empty());
}

#[test]
fn test_emission_order_single() {
    let decls = vec![simple_decl("f", vec![], IRType::Object, ret_erased())];
    let order = compute_emission_order(&decls).unwrap();
    assert_eq!(order, vec![0]);
}

#[test]
fn test_emission_order_independent() {
    let decls = vec![
        simple_decl("a", vec![], IRType::Object, ret_erased()),
        simple_decl("b", vec![], IRType::Object, ret_erased()),
    ];
    let order = compute_emission_order(&decls).unwrap();
    assert_eq!(order.len(), 2);
}

#[test]
fn test_emission_order_callee_before_caller() {
    let decls = vec![
        simple_decl(
            "caller",
            vec![(VarId(0), IRType::Object)],
            IRType::Object,
            call_body("callee", 0, 1),
        ),
        simple_decl(
            "callee",
            vec![(VarId(0), IRType::Object)],
            IRType::Object,
            ret_var(0),
        ),
    ];
    let order = compute_emission_order(&decls).unwrap();
    // callee (index 1) must appear before caller (index 0).
    let pos_callee = order.iter().position(|&x| x == 1).unwrap();
    let pos_caller = order.iter().position(|&x| x == 0).unwrap();
    assert!(pos_callee < pos_caller);
}

#[test]
fn test_emission_order_chain() {
    // a calls b, b calls c => c, b, a
    let decls = vec![
        simple_decl(
            "a",
            vec![(VarId(0), IRType::Object)],
            IRType::Object,
            call_body("b", 0, 1),
        ),
        simple_decl(
            "b",
            vec![(VarId(0), IRType::Object)],
            IRType::Object,
            call_body("c", 0, 1),
        ),
        simple_decl(
            "c",
            vec![(VarId(0), IRType::Object)],
            IRType::Object,
            ret_var(0),
        ),
    ];
    let order = compute_emission_order(&decls).unwrap();
    let pos = |name_idx: usize| order.iter().position(|&x| x == name_idx).unwrap();
    assert!(pos(2) < pos(1)); // c before b
    assert!(pos(1) < pos(0)); // b before a
}

#[test]
fn test_emission_order_cycle_detected() {
    // a calls b, b calls a => cycle
    let decls = vec![
        simple_decl(
            "a",
            vec![(VarId(0), IRType::Object)],
            IRType::Object,
            call_body("b", 0, 1),
        ),
        simple_decl(
            "b",
            vec![(VarId(0), IRType::Object)],
            IRType::Object,
            call_body("a", 0, 1),
        ),
    ];
    let result = compute_emission_order(&decls);
    assert!(result.is_err());
    let err = result.unwrap_err();
    let msg = format!("{}", err);
    assert!(msg.contains("dependency cycle"));
}

#[test]
fn test_emission_order_external_refs_ignored() {
    // Calling an unknown function should not cause ordering issues.
    let decls = vec![simple_decl(
        "f",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        call_body("external", 0, 1),
    )];
    let order = compute_emission_order(&decls).unwrap();
    assert_eq!(order, vec![0]);
}

// ── Backend comparison tests ──

#[test]
fn test_compare_backends_all_same() {
    let decls: BTreeSet<String> = ["f", "g"].iter().map(|s| s.to_string()).collect();
    let stats = OutputStats {
        lines_of_code: 10,
        declarations_emitted: 2,
        comment_lines: 0,
        blank_lines: 0,
    };
    let result = compare_backends(&[
        (Backend::C, decls.clone(), stats.clone()),
        (Backend::Rust, decls.clone(), stats.clone()),
    ]);
    assert!(result.missing_decls.is_empty());
    assert_eq!(result.stats.len(), 2);
}

#[test]
fn test_compare_backends_missing_decl() {
    let c_decls: BTreeSet<String> = ["f", "g"].iter().map(|s| s.to_string()).collect();
    let rust_decls: BTreeSet<String> = ["f"].iter().map(|s| s.to_string()).collect();
    let stats = OutputStats::default();
    let result = compare_backends(&[
        (Backend::C, c_decls, stats.clone()),
        (Backend::Rust, rust_decls, stats),
    ]);
    assert_eq!(result.missing_decls.len(), 1);
    assert_eq!(result.missing_decls[0].decl_name, "g");
    assert!(result.missing_decls[0].present_in.contains(&Backend::C));
    assert!(result.missing_decls[0].absent_from.contains(&Backend::Rust));
}

#[test]
fn test_compare_backends_empty() {
    let result = compare_backends(&[]);
    assert!(result.missing_decls.is_empty());
    assert!(result.stats.is_empty());
}

// ── Backend label tests ──

#[test]
fn test_backend_labels() {
    assert_eq!(Backend::C.label(), "C");
    assert_eq!(Backend::Llvm.label(), "LLVM");
    assert_eq!(Backend::Rust.label(), "Rust");
}

// ── Comment generation tests ──

#[test]
fn test_generate_decl_comment_no_params() {
    let decl = simple_decl("f", vec![], IRType::Object, ret_erased());
    let comment = generate_decl_comment(&decl, "//");
    assert!(comment.contains("// f() -> Object"));
}

#[test]
fn test_generate_decl_comment_with_params() {
    let decl = simple_decl(
        "g",
        vec![(VarId(0), IRType::UInt64), (VarId(1), IRType::Bool)],
        IRType::UInt64,
        ret_var(0),
    );
    let comment = generate_decl_comment(&decl, "//");
    assert!(comment.contains("_x0: UInt64"));
    assert!(comment.contains("_x1: Bool"));
    assert!(comment.contains("-> UInt64"));
}

#[test]
fn test_generate_decl_comment_llvm_prefix() {
    let decl = simple_decl("h", vec![], IRType::Void, ret_erased());
    let comment = generate_decl_comment(&decl, ";");
    assert!(comment.starts_with("; "));
}

#[test]
fn test_generate_module_header() {
    let header = generate_module_header("my_mod", 42, "//");
    assert!(header.contains("// Module: my_mod"));
    assert!(header.contains("// Declarations: 42"));
    assert!(header.contains("clean-compiler"));
}

// ── format_ir_type tests ──

#[test]
fn test_format_ir_type_scalars() {
    assert_eq!(format_ir_type(&IRType::Bool), "Bool");
    assert_eq!(format_ir_type(&IRType::UInt8), "UInt8");
    assert_eq!(format_ir_type(&IRType::UInt16), "UInt16");
    assert_eq!(format_ir_type(&IRType::UInt32), "UInt32");
    assert_eq!(format_ir_type(&IRType::UInt64), "UInt64");
    assert_eq!(format_ir_type(&IRType::USize), "USize");
    assert_eq!(format_ir_type(&IRType::Float32), "Float32");
    assert_eq!(format_ir_type(&IRType::Float64), "Float64");
}

#[test]
fn test_format_ir_type_objects() {
    assert_eq!(format_ir_type(&IRType::Object), "Object");
    assert_eq!(format_ir_type(&IRType::TObject), "TObject");
}

#[test]
fn test_format_ir_type_struct() {
    let ty = IRType::Struct(vec![IRType::UInt64, IRType::Object]);
    assert_eq!(format_ir_type(&ty), "Struct(UInt64, Object)");
}

#[test]
fn test_format_ir_type_union() {
    let ty = IRType::Union(vec![IRType::Bool]);
    assert_eq!(format_ir_type(&ty), "Union(Bool)");
}

#[test]
fn test_format_ir_type_special() {
    assert_eq!(format_ir_type(&IRType::Erased), "Erased");
    assert_eq!(format_ir_type(&IRType::Void), "Void");
}

// ── Validation tests ──

#[test]
fn test_validate_empty_decls() {
    let issues = validate_declarations(&[]);
    assert!(issues.is_empty());
}

#[test]
fn test_validate_clean_decls() {
    let decls = vec![simple_decl(
        "f",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        ret_var(0),
    )];
    let issues = validate_declarations(&decls);
    assert!(issues.is_empty());
}

#[test]
fn test_validate_duplicate_name() {
    let decls = vec![
        simple_decl("f", vec![], IRType::Object, ret_erased()),
        simple_decl("f", vec![], IRType::Object, ret_erased()),
    ];
    let issues = validate_declarations(&decls);
    let errors: Vec<_> = issues
        .iter()
        .filter(|i| i.severity == IssueSeverity::Error)
        .collect();
    assert!(!errors.is_empty());
    assert!(errors[0].message.contains("duplicate"));
}

#[test]
fn test_validate_unreachable_body() {
    let decls = vec![simple_decl(
        "f",
        vec![],
        IRType::Object,
        IRBody::Unreachable,
    )];
    let issues = validate_declarations(&decls);
    let infos: Vec<_> = issues
        .iter()
        .filter(|i| i.severity == IssueSeverity::Info)
        .collect();
    assert!(!infos.is_empty());
    assert!(infos[0].message.contains("unreachable"));
}

#[test]
fn test_validate_void_param() {
    let decls = vec![simple_decl(
        "f",
        vec![(VarId(0), IRType::Void)],
        IRType::Object,
        ret_erased(),
    )];
    let issues = validate_declarations(&decls);
    let warnings: Vec<_> = issues
        .iter()
        .filter(|i| i.severity == IssueSeverity::Warning)
        .collect();
    assert!(!warnings.is_empty());
    assert!(warnings[0].message.contains("Void"));
}

#[test]
fn test_validate_undefined_reference() {
    let decls = vec![simple_decl(
        "f",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        call_body("unknown_fn", 0, 1),
    )];
    let issues = validate_declarations(&decls);
    let warnings: Vec<_> = issues
        .iter()
        .filter(|i| i.severity == IssueSeverity::Warning)
        .collect();
    assert!(!warnings.is_empty());
    assert!(warnings[0].message.contains("undefined reference"));
}

#[test]
fn test_validate_known_reference_no_warning() {
    let decls = vec![
        simple_decl(
            "caller",
            vec![(VarId(0), IRType::Object)],
            IRType::Object,
            call_body("callee", 0, 1),
        ),
        simple_decl(
            "callee",
            vec![(VarId(0), IRType::Object)],
            IRType::Object,
            ret_var(0),
        ),
    ];
    let issues = validate_declarations(&decls);
    let undef: Vec<_> = issues
        .iter()
        .filter(|i| i.message.contains("undefined"))
        .collect();
    assert!(undef.is_empty());
}

#[test]
fn test_validate_multiple_issues() {
    let decls = vec![
        simple_decl(
            "f",
            vec![(VarId(0), IRType::Void)],
            IRType::Object,
            IRBody::Unreachable,
        ),
        simple_decl("f", vec![], IRType::Object, ret_erased()),
    ];
    let issues = validate_declarations(&decls);
    // Should find: duplicate name, void param, unreachable body
    assert!(issues.len() >= 3);
}

// ── IssueSeverity ordering tests ──

#[test]
fn test_severity_ordering() {
    assert!(IssueSeverity::Info < IssueSeverity::Warning);
    assert!(IssueSeverity::Warning < IssueSeverity::Error);
}

// ── EmitConfig tests ──

#[test]
fn test_emit_config_default() {
    let cfg = EmitConfig::default();
    assert!(!cfg.debug_info);
    assert_eq!(cfg.opt_level, OptLevel::O0);
    assert_eq!(cfg.target, EmitTarget::Generic);
    assert!(cfg.module_header);
    assert!(!cfg.decl_comments);
}

#[test]
fn test_emit_config_debug() {
    let cfg = EmitConfig::debug();
    assert!(cfg.debug_info);
    assert!(cfg.decl_comments);
    assert_eq!(cfg.opt_level, OptLevel::O0);
}

#[test]
fn test_emit_config_release() {
    let cfg = EmitConfig::release();
    assert!(!cfg.debug_info);
    assert_eq!(cfg.opt_level, OptLevel::O2);
}

// ── OptLevel ordering ──

#[test]
fn test_opt_level_ordering() {
    assert!(OptLevel::O0 < OptLevel::O1);
    assert!(OptLevel::O1 < OptLevel::O2);
    assert!(OptLevel::O2 < OptLevel::O3);
}

// ── EmitTarget equality ──

#[test]
fn test_emit_target_equality() {
    assert_eq!(EmitTarget::X86_64, EmitTarget::X86_64);
    assert_ne!(EmitTarget::X86_64, EmitTarget::AArch64);
    assert_ne!(EmitTarget::Wasm32, EmitTarget::Generic);
}

// ── Error Display tests ──

#[test]
fn test_error_display_name_collision() {
    let err = crate::emit_base_ext::EmitExtError::NameCollision {
        mangled: "l_foo".to_string(),
        first: "foo".to_string(),
        second: "Foo".to_string(),
    };
    let msg = format!("{}", err);
    assert!(msg.contains("name collision"));
    assert!(msg.contains("l_foo"));
}

#[test]
fn test_error_display_dependency_cycle() {
    let err = crate::emit_base_ext::EmitExtError::DependencyCycle {
        name: "f".to_string(),
    };
    assert!(format!("{}", err).contains("dependency cycle"));
}

#[test]
fn test_error_display_undefined_ref() {
    let err = crate::emit_base_ext::EmitExtError::UndefinedReference {
        name: "g".to_string(),
        in_decl: "f".to_string(),
    };
    let msg = format!("{}", err);
    assert!(msg.contains("undefined reference"));
    assert!(msg.contains("g"));
}

#[test]
fn test_error_display_backend_mismatch() {
    let err = crate::emit_base_ext::EmitExtError::BackendMismatch {
        decl: "f".to_string(),
        detail: "missing in Rust".to_string(),
    };
    assert!(format!("{}", err).contains("backend mismatch"));
}
