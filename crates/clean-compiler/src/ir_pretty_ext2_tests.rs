// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended IR pretty-printing module (ext2).
//! Part of #3083 - Extensibility.

use crate::ir::{
    CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, JoinPointId, VarId,
};
use crate::ir_pretty_ext2::{
    cfg_to_dot, decl_summaries, decl_summary, decl_to_html, format_stats_table, ir_diff,
    pretty_ext2, pretty_ext2_body, Ext2Config, Ext2Printer, OutputFormat,
};
use clean_kernel::Name;

// ── Test helpers ───────────────────────────────────────────────────

fn mk_ctor(name: &str, tag: u32) -> CtorInfo {
    CtorInfo {
        name: Name::from_string(name),
        tag,
        num_scalars: 0,
        num_objects: 0,
        field_types: vec![],
    }
}

fn mk_fn_id(name: &str) -> FnId {
    FnId(Name::from_string(name))
}

fn simple_decl() -> IRDecl {
    IRDecl {
        name: Name::from_string("Nat.zero"),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(VarId(0))),
    }
}

fn two_param_decl() -> IRDecl {
    IRDecl {
        name: Name::from_string("Nat.add"),
        params: vec![(VarId(0), IRType::Object), (VarId(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(2),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: mk_fn_id("Nat.add"),
                args: vec![IRArg::Var(VarId(0)), IRArg::Var(VarId(1))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
        },
    }
}

fn rc_body() -> IRBody {
    IRBody::Inc {
        var: VarId(0),
        n: 1,
        rest: Box::new(IRBody::Inc {
            var: VarId(1),
            n: 2,
            rest: Box::new(IRBody::Dec {
                var: VarId(0),
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
            }),
        }),
    }
}

fn case_body() -> IRBody {
    IRBody::Case {
        scrutinee: VarId(0),
        alts: vec![
            IRAlt {
                ctor: mk_ctor("Bool.true", 1),
                body: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
            },
            IRAlt {
                ctor: mk_ctor("Bool.false", 0),
                body: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
            },
        ],
        default: None,
    }
}

fn rc_decl() -> IRDecl {
    IRDecl {
        name: Name::from_string("rc_test"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::Object,
        body: rc_body(),
    }
}

// ── OutputFormat tests ─────────────────────────────────────────────

#[test]
fn test_output_format_compact() {
    let result = pretty_ext2(&simple_decl(), OutputFormat::Compact);
    assert!(result.contains("def"));
    assert!(result.contains("ret"));
    assert!(!result.contains("Object"), "compact should not show types");
}

#[test]
fn test_output_format_verbose() {
    let result = pretty_ext2(&simple_decl(), OutputFormat::Verbose);
    assert!(result.contains("def"));
    assert!(result.contains("Object"));
}

#[test]
fn test_output_format_debug() {
    let result = pretty_ext2(&simple_decl(), OutputFormat::Debug);
    assert!(result.contains("def"));
    // Debug format uses x_ prefix
    assert!(result.contains("x_0"));
}

#[test]
fn test_compact_config_no_types() {
    let cfg = Ext2Config::compact();
    assert_eq!(cfg.format, OutputFormat::Compact);
    assert!(!cfg.show_types);
}

#[test]
fn test_debug_config_shows_rc() {
    let cfg = Ext2Config::debug();
    assert_eq!(cfg.format, OutputFormat::Debug);
    assert!(cfg.show_rc_annotations);
}

#[test]
fn test_default_config() {
    let cfg = Ext2Config::default();
    assert_eq!(cfg.format, OutputFormat::Verbose);
    assert!(cfg.show_types);
    assert!(!cfg.ansi_color);
    assert!(!cfg.show_rc_annotations);
    assert_eq!(cfg.indent_width, 2);
    assert!(cfg.max_depth.is_none());
    assert!(!cfg.html_mode);
}

// ── ANSI color tests ───────────────────────────────────────────────

#[test]
fn test_ansi_color_enabled() {
    let mut p = Ext2Printer::new(Ext2Config {
        ansi_color: true,
        ..Ext2Config::default()
    });
    p.print_decl(&simple_decl());
    let result = p.into_string();
    assert!(result.contains("\x1b["), "should contain ANSI codes");
    assert!(result.contains("\x1b[0m"), "should contain ANSI reset");
}

#[test]
fn test_ansi_color_disabled() {
    let result = pretty_ext2(&simple_decl(), OutputFormat::Verbose);
    assert!(!result.contains("\x1b["), "should NOT contain ANSI codes");
}

#[test]
fn test_ansi_keywords_colored() {
    let mut p = Ext2Printer::new(Ext2Config {
        ansi_color: true,
        ..Ext2Config::default()
    });
    p.print_decl(&two_param_decl());
    let result = p.into_string();
    // Bold blue for keywords
    assert!(result.contains("\x1b[1;34m"));
}

#[test]
fn test_ansi_types_colored() {
    let mut p = Ext2Printer::new(Ext2Config {
        ansi_color: true,
        ..Ext2Config::default()
    });
    p.print_decl(&simple_decl());
    let result = p.into_string();
    // Green for types
    assert!(result.contains("\x1b[32m"));
}

// ── Type annotation tests ──────────────────────────────────────────

#[test]
fn test_type_annotation_shown() {
    let result = pretty_ext2(&two_param_decl(), OutputFormat::Verbose);
    assert!(result.contains("Object"));
}

#[test]
fn test_type_annotation_hidden_compact() {
    let result = pretty_ext2(&two_param_decl(), OutputFormat::Compact);
    assert!(!result.contains(": Object"));
}

#[test]
fn test_type_format_struct() {
    let p = Ext2Printer::new(Ext2Config::default());
    let ty = IRType::Struct(vec![IRType::UInt64, IRType::Object]);
    let result = p.format_type(&ty);
    assert!(result.contains("Struct"));
    assert!(result.contains("UInt64"));
    assert!(result.contains("Object"));
}

#[test]
fn test_type_format_union() {
    let p = Ext2Printer::new(Ext2Config::default());
    let ty = IRType::Union(vec![IRType::Bool, IRType::UInt8]);
    let result = p.format_type(&ty);
    assert!(result.contains("Union"));
    assert!(result.contains("Bool"));
    assert!(result.contains("UInt8"));
}

// ── CFG DOT visualization tests ────────────────────────────────────

#[test]
fn test_cfg_dot_basic() {
    let dot = cfg_to_dot(&simple_decl());
    assert!(dot.contains("digraph"));
    assert!(dot.contains("Nat.zero"));
    assert!(dot.contains("node [shape=box"));
    assert!(dot.contains("ret"));
}

#[test]
fn test_cfg_dot_edges() {
    let dot = cfg_to_dot(&two_param_decl());
    assert!(dot.contains("->"), "should contain edge arrows");
}

#[test]
fn test_cfg_dot_case_branches() {
    let decl = IRDecl {
        name: Name::from_string("test_case"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::Object,
        body: case_body(),
    };
    let dot = cfg_to_dot(&decl);
    assert!(dot.contains("case x0"));
    // Case node should have multiple outgoing edges
    let arrow_count = dot.matches("->").count();
    assert!(
        arrow_count >= 3,
        "case should have at least 3 edges (case->alt1, case->alt2, parent->case)"
    );
}

#[test]
fn test_cfg_dot_inc_dec() {
    let dot = cfg_to_dot(&rc_decl());
    assert!(dot.contains("inc"));
    assert!(dot.contains("dec"));
}

// ── RC annotation tests ───────────────────────────────────────────

#[test]
fn test_rc_annotations_shown() {
    let cfg = Ext2Config {
        show_rc_annotations: true,
        ..Ext2Config::default()
    };
    let result = pretty_ext2_body(&rc_body(), cfg);
    assert!(result.contains("[RC]"), "should show [RC] prefix");
}

#[test]
fn test_rc_annotations_hidden_by_default() {
    let result = pretty_ext2_body(&rc_body(), Ext2Config::default());
    assert!(!result.contains("[RC]"));
}

#[test]
fn test_rc_annotations_with_ansi() {
    let cfg = Ext2Config {
        show_rc_annotations: true,
        ansi_color: true,
        ..Ext2Config::default()
    };
    let result = pretty_ext2_body(&rc_body(), cfg);
    assert!(result.contains("[RC]"));
    // Red for RC keywords
    assert!(result.contains("\x1b[1;31m"));
}

// ── Indentation and nesting control ────────────────────────────────

#[test]
fn test_indent_width_4() {
    let cfg = Ext2Config {
        indent_width: 4,
        ..Ext2Config::default()
    };
    let mut p = Ext2Printer::new(cfg);
    p.print_decl(&two_param_decl());
    let result = p.into_string();
    // Should have 4-space indentation
    assert!(result.contains("    let"), "should have 4 spaces indent");
}

#[test]
fn test_indent_width_1() {
    let cfg = Ext2Config {
        indent_width: 1,
        ..Ext2Config::default()
    };
    let mut p = Ext2Printer::new(cfg);
    p.print_decl(&two_param_decl());
    let result = p.into_string();
    // First body line should have exactly 1 space indent
    let lines: Vec<&str> = result.lines().collect();
    assert!(lines.len() > 1);
    let body_line = lines[1];
    assert!(body_line.starts_with(' '));
    assert!(
        !body_line.starts_with("  "),
        "should not have 2 spaces at indent=1"
    );
}

#[test]
fn test_max_depth_truncation() {
    let cfg = Ext2Config {
        max_depth: Some(1),
        ..Ext2Config::default()
    };
    let result = pretty_ext2_body(&two_param_decl().body, cfg);
    // At depth 1 the nested body should be truncated
    assert!(result.contains("..."), "should truncate at max depth");
}

#[test]
fn test_max_depth_none_no_truncation() {
    let result = pretty_ext2(&two_param_decl(), OutputFormat::Verbose);
    assert!(
        !result.contains("..."),
        "should not truncate without max_depth"
    );
}

// ── Declaration summary tests ──────────────────────────────────────

#[test]
fn test_decl_summary_basic() {
    let s = decl_summary(&simple_decl());
    assert!(s.contains("Nat.zero"));
    assert!(s.contains("0 params"));
    assert!(s.contains("1 nodes"));
    assert!(s.contains("depth 1"));
    assert!(s.contains("rc 0/0"));
}

#[test]
fn test_decl_summary_with_params() {
    let s = decl_summary(&two_param_decl());
    assert!(s.contains("Nat.add"));
    assert!(s.contains("2 params"));
}

#[test]
fn test_decl_summary_rc() {
    let s = decl_summary(&rc_decl());
    assert!(s.contains("rc 2/1"), "should show 2 incs, 1 dec");
}

#[test]
fn test_decl_summaries_multiple() {
    let decls = vec![simple_decl(), two_param_decl()];
    let result = decl_summaries(&decls);
    assert!(result.contains("Nat.zero"));
    assert!(result.contains("Nat.add"));
    let line_count = result.lines().count();
    assert_eq!(line_count, 2);
}

// ── IR diff display tests ──────────────────────────────────────────

#[test]
fn test_ir_diff_identical() {
    let d = simple_decl();
    let result = ir_diff(&d, &d);
    // All lines should start with "  " (no changes)
    for line in result.lines() {
        assert!(
            line.starts_with("  "),
            "identical decls should have no diff markers, got: {line}"
        );
    }
}

#[test]
fn test_ir_diff_different() {
    let old = simple_decl();
    let new = two_param_decl();
    let result = ir_diff(&old, &new);
    assert!(
        result.contains("- ") || result.contains("+ "),
        "different decls should show diff markers"
    );
}

#[test]
fn test_ir_diff_name_change() {
    let old = simple_decl();
    let mut new = simple_decl();
    new.name = Name::from_string("Nat.one");
    let result = ir_diff(&old, &new);
    assert!(result.contains('+'), "should contain + marker for new name");
    assert!(result.contains('-'), "should contain - marker for old name");
}

// ── Statistics table tests ─────────────────────────────────────────

#[test]
fn test_stats_table_empty() {
    let result = format_stats_table(&[]);
    assert!(result.is_empty());
}

#[test]
fn test_stats_table_single_pass() {
    let result = format_stats_table(&[("dce", &[("removed", 5), ("kept", 10)])]);
    assert!(result.contains("Pass"));
    assert!(result.contains("dce"));
    assert!(result.contains("5"));
    assert!(result.contains("10"));
    assert!(result.contains("removed"));
    assert!(result.contains("kept"));
}

#[test]
fn test_stats_table_multiple_passes() {
    let result = format_stats_table(&[
        ("dce", &[("removed", 5), ("kept", 10)]),
        ("inline", &[("removed", 0), ("kept", 3)]),
    ]);
    assert!(result.contains("dce"));
    assert!(result.contains("inline"));
    let lines: Vec<&str> = result.lines().collect();
    assert_eq!(lines.len(), 4, "header + separator + 2 rows");
}

#[test]
fn test_stats_table_alignment() {
    let result = format_stats_table(&[("short", &[("x", 1)]), ("very_long_name", &[("x", 999)])]);
    let lines: Vec<&str> = result.lines().collect();
    // Header and data lines should have consistent structure
    assert!(lines.len() >= 3);
}

// ── HTML output tests ──────────────────────────────────────────────

#[test]
fn test_html_output_wraps_in_pre() {
    let result = decl_to_html(&simple_decl());
    assert!(result.starts_with("<pre class=\"ir-code\">"));
    assert!(result.ends_with("</pre>"));
}

#[test]
fn test_html_output_has_spans() {
    let result = decl_to_html(&simple_decl());
    assert!(result.contains("<span class=\"ir-kw\">"));
    assert!(result.contains("</span>"));
}

#[test]
fn test_html_output_no_ansi() {
    let result = decl_to_html(&simple_decl());
    assert!(
        !result.contains("\x1b["),
        "HTML output should not contain ANSI codes"
    );
}

#[test]
fn test_html_escapes_special_chars() {
    // Create a decl with a string literal that has special HTML chars
    let decl = IRDecl {
        name: Name::from_string("test"),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(0),
            ty: IRType::Object,
            value: IRExpr::String("<script>alert('xss')</script>".into()),
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
        },
    };
    let result = decl_to_html(&decl);
    assert!(
        !result.contains("<script>"),
        "should escape HTML special chars"
    );
}

#[test]
fn test_html_type_spans() {
    let result = decl_to_html(&two_param_decl());
    assert!(result.contains("<span class=\"ir-type\">"));
}

// ── Expression formatting tests ────────────────────────────────────

#[test]
fn test_format_ctor_expr() {
    let result = pretty_ext2(
        &IRDecl {
            name: Name::from_string("test"),
            params: vec![],
            return_type: IRType::Object,
            body: IRBody::VDecl {
                var: VarId(0),
                ty: IRType::Object,
                value: IRExpr::Ctor {
                    info: mk_ctor("Nat.zero", 0),
                    args: vec![],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
            },
        },
        OutputFormat::Verbose,
    );
    assert!(result.contains("ctor"));
    assert!(result.contains("Nat.zero"));
}

#[test]
fn test_format_ctor_debug_shows_tag() {
    let result = pretty_ext2(
        &IRDecl {
            name: Name::from_string("test"),
            params: vec![],
            return_type: IRType::Object,
            body: IRBody::VDecl {
                var: VarId(0),
                ty: IRType::Object,
                value: IRExpr::Ctor {
                    info: mk_ctor("Nat.succ", 1),
                    args: vec![IRArg::Var(VarId(1))],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
            },
        },
        OutputFormat::Debug,
    );
    assert!(result.contains("tag=1"), "debug mode should show ctor tag");
}

#[test]
fn test_format_literal_uint64() {
    let result = pretty_ext2(
        &IRDecl {
            name: Name::from_string("test"),
            params: vec![],
            return_type: IRType::UInt64,
            body: IRBody::VDecl {
                var: VarId(0),
                ty: IRType::UInt64,
                value: IRExpr::Lit(IRLiteral::UInt64(42)),
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
            },
        },
        OutputFormat::Verbose,
    );
    assert!(result.contains("42u64"));
}

#[test]
fn test_format_partial_apply() {
    let result = pretty_ext2(
        &IRDecl {
            name: Name::from_string("test"),
            params: vec![],
            return_type: IRType::Object,
            body: IRBody::VDecl {
                var: VarId(0),
                ty: IRType::Object,
                value: IRExpr::PartialApply {
                    fn_id: mk_fn_id("f"),
                    arity: 3,
                    args: vec![IRArg::Var(VarId(1))],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
            },
        },
        OutputFormat::Verbose,
    );
    assert!(result.contains("papp"));
    assert!(result.contains("f/3"));
}

#[test]
fn test_format_box_unbox() {
    let _p = Ext2Printer::new(Ext2Config::default());
    let body = IRBody::VDecl {
        var: VarId(0),
        ty: IRType::Object,
        value: IRExpr::Box {
            ty: IRType::UInt64,
            arg: IRArg::Var(VarId(1)),
        },
        rest: Box::new(IRBody::VDecl {
            var: VarId(2),
            ty: IRType::UInt64,
            value: IRExpr::Unbox {
                ty: IRType::UInt64,
                arg: IRArg::Var(VarId(0)),
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
        }),
    };
    let result = pretty_ext2_body(&body, Ext2Config::default());
    assert!(result.contains("box"));
    assert!(result.contains("unbox"));
}

// ── Body printing tests ────────────────────────────────────────────

#[test]
fn test_print_unreachable() {
    let result = pretty_ext2_body(&IRBody::Unreachable, Ext2Config::default());
    assert!(result.contains("unreachable"));
}

#[test]
fn test_print_jmp() {
    let body = IRBody::Jmp {
        jp: JoinPointId(5),
        args: vec![IRArg::Var(VarId(0))],
    };
    let result = pretty_ext2_body(&body, Ext2Config::default());
    assert!(result.contains("jmp"));
    assert!(result.contains("jp5"));
}

#[test]
fn test_print_set_operations() {
    let body = IRBody::Set {
        var: VarId(0),
        idx: 1,
        value: VarId(2),
        rest: Box::new(IRBody::SetTag {
            var: VarId(0),
            tag: 3,
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
        }),
    };
    let result = pretty_ext2_body(&body, Ext2Config::default());
    assert!(result.contains("set"));
    assert!(result.contains("setTag"));
}

#[test]
fn test_print_uset_sset() {
    let body = IRBody::USet {
        var: VarId(0),
        idx: 1,
        value: VarId(2),
        rest: Box::new(IRBody::SSet {
            var: VarId(3),
            n: 2,
            offset: 4,
            value: VarId(5),
            ty: IRType::UInt32,
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
        }),
    };
    let result = pretty_ext2_body(&body, Ext2Config::default());
    assert!(result.contains("uset"));
    assert!(result.contains("sset"));
}

#[test]
fn test_print_case_with_default() {
    let body = IRBody::Case {
        scrutinee: VarId(0),
        alts: vec![IRAlt {
            ctor: mk_ctor("Option.some", 1),
            body: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        }],
        default: Some(Box::new(IRBody::Unreachable)),
    };
    let result = pretty_ext2_body(&body, Ext2Config::default());
    assert!(result.contains("case"));
    assert!(result.contains("Option.some"));
    assert!(result.contains("_ =>"));
    assert!(result.contains("unreachable"));
}

#[test]
fn test_print_join_point_decl() {
    let body = IRBody::JDecl {
        jp: JoinPointId(0),
        params: vec![(VarId(1), IRType::Object)],
        body: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        rest: Box::new(IRBody::Jmp {
            jp: JoinPointId(0),
            args: vec![IRArg::Var(VarId(0))],
        }),
    };
    let result = pretty_ext2_body(&body, Ext2Config::default());
    assert!(result.contains("jp"));
    assert!(result.contains("jmp"));
}

#[test]
fn test_erased_arg_display() {
    let body = IRBody::Ret(IRArg::Erased);
    let result = pretty_ext2_body(&body, Ext2Config::default());
    assert!(result.contains("erased"));
}
