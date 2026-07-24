// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for enhanced IR pretty printing.
//! Part of #3084 - IO/FFI/Native.

use crate::ir::{
    CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, JoinPointId, VarId,
};
use crate::ir_pretty_ext::{
    ir_body_depth, ir_body_node_count, ir_rc_ops_count, ir_var_usage, pretty_print_ir_ext,
    pretty_print_ir_stats, pretty_print_lcnf, ExtIrPrinter, ExtPrettyConfig,
};
use crate::lcnf::{Arg, Code, Decl, ExternEntry, LetDecl, LetValue, Param};
use clean_kernel::{Expr, FVarId, Name};

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

fn simple_ir_decl() -> IRDecl {
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

fn mk_lcnf_return(id: u64) -> Code {
    Code::Return(FVarId::new(id))
}

fn mk_lcnf_let(fvar: u64, value: LetValue, body: Code) -> Code {
    Code::let_bind(
        LetDecl::new(
            FVarId::new(fvar),
            Name::from_string("_"),
            Expr::prop(),
            value,
        ),
        body,
    )
}

fn simple_lcnf_decl() -> Decl {
    Decl::new(
        Name::from_string("Nat.succ"),
        vec![],
        Expr::prop(),
        vec![Param::new(
            FVarId::new(0),
            Name::from_string("n"),
            Expr::prop(),
        )],
        mk_lcnf_let(
            1,
            LetValue::Ctor {
                name: Name::from_string("Nat.succ"),
                levels: vec![],
                args: vec![Arg::FVar(FVarId::new(0))],
            },
            mk_lcnf_return(1),
        ),
        false,
    )
}

// ── Default config tests ────────────────────────────────────────────

#[test]
fn test_ext_config_defaults() {
    let c = ExtPrettyConfig::default();
    assert_eq!(c.indent_size, 2);
    assert!(c.show_types);
    assert!(!c.highlight_rc);
    assert!(!c.color);
    assert!(!c.summary_mode);
    assert!(!c.stable_ordering);
}

// ── IR body printing ────────────────────────────────────────────────

#[test]
fn test_ext_print_ret() {
    let result = pretty_print_ir_ext(&simple_ir_decl());
    assert!(result.contains("ret"));
    assert!(result.contains("x0"));
}

#[test]
fn test_ext_print_let_with_types() {
    let result = pretty_print_ir_ext(&two_param_decl());
    assert!(result.contains("let"));
    assert!(result.contains("Nat.add"));
}

#[test]
fn test_ext_print_without_types() {
    let mut p = ExtIrPrinter::new(ExtPrettyConfig {
        show_types: false,
        ..ExtPrettyConfig::default()
    });
    p.print_ir_decl(&two_param_decl());
    let result = p.into_string();
    assert!(result.contains("def"));
    assert!(result.contains("Nat.add"));
}

#[test]
fn test_ext_print_inc_dec() {
    let decl = IRDecl {
        name: Name::from_string("rc_test"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::Object,
        body: rc_body(),
    };
    let result = pretty_print_ir_ext(&decl);
    assert!(result.contains("inc"));
    assert!(result.contains("dec"));
}

// ── RC highlighting ─────────────────────────────────────────────────

#[test]
fn test_rc_highlight_mode() {
    let mut p = ExtIrPrinter::new(ExtPrettyConfig {
        highlight_rc: true,
        ..ExtPrettyConfig::default()
    });
    p.print_ir_body(&rc_body());
    let result = p.into_string();
    assert!(result.contains("[RC]"));
}

#[test]
fn test_no_rc_highlight_by_default() {
    let mut p = ExtIrPrinter::new(ExtPrettyConfig::default());
    p.print_ir_body(&rc_body());
    let result = p.into_string();
    assert!(!result.contains("[RC]"));
}

// ── ANSI color ──────────────────────────────────────────────────────

#[test]
fn test_color_mode() {
    let mut p = ExtIrPrinter::new(ExtPrettyConfig {
        color: true,
        ..ExtPrettyConfig::default()
    });
    p.print_ir_decl(&simple_ir_decl());
    let result = p.into_string();
    assert!(result.contains("\x1b["));
    assert!(result.contains("\x1b[0m"));
}

#[test]
fn test_no_color_by_default() {
    let result = pretty_print_ir_ext(&simple_ir_decl());
    assert!(!result.contains("\x1b["));
}

// ── Case printing ───────────────────────────────────────────────────

#[test]
fn test_ext_print_case() {
    let decl = IRDecl {
        name: Name::from_string("bool_case"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::Object,
        body: case_body(),
    };
    let result = pretty_print_ir_ext(&decl);
    assert!(result.contains("case"));
    assert!(result.contains("Bool.true"));
    assert!(result.contains("Bool.false"));
}

#[test]
fn test_ext_print_case_with_default() {
    let body = IRBody::Case {
        scrutinee: VarId(0),
        alts: vec![IRAlt {
            ctor: mk_ctor("Option.some", 1),
            body: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        }],
        default: Some(Box::new(IRBody::Unreachable)),
    };
    let mut p = ExtIrPrinter::new(ExtPrettyConfig::default());
    p.print_ir_body(&body);
    let result = p.into_string();
    assert!(result.contains("_ =>"));
    assert!(result.contains("unreachable"));
}

// ── Summary mode ────────────────────────────────────────────────────

#[test]
fn test_summary_ir_decl() {
    let mut p = ExtIrPrinter::new(ExtPrettyConfig {
        summary_mode: true,
        ..ExtPrettyConfig::default()
    });
    p.print_ir_decl(&two_param_decl());
    let result = p.into_string();
    assert!(result.contains("def"));
    assert!(result.contains("Nat.add"));
    assert!(result.contains("2 params"));
    assert!(result.contains("nodes"));
}

// ── Stable ordering ─────────────────────────────────────────────────

#[test]
fn test_stable_ordering_ir_decls() {
    let decls = vec![
        IRDecl {
            name: Name::from_string("Zebra"),
            params: vec![],
            return_type: IRType::Object,
            body: IRBody::Ret(IRArg::Var(VarId(0))),
        },
        IRDecl {
            name: Name::from_string("Alpha"),
            params: vec![],
            return_type: IRType::Object,
            body: IRBody::Ret(IRArg::Var(VarId(0))),
        },
    ];
    let mut p = ExtIrPrinter::new(ExtPrettyConfig {
        stable_ordering: true,
        ..ExtPrettyConfig::default()
    });
    p.print_ir_decls(&decls);
    let result = p.into_string();
    let alpha_pos = result.find("Alpha").expect("should contain Alpha");
    let zebra_pos = result.find("Zebra").expect("should contain Zebra");
    assert!(
        alpha_pos < zebra_pos,
        "Alpha should come before Zebra in sorted output"
    );
}

// ── IR Statistics ───────────────────────────────────────────────────

#[test]
fn test_ir_body_depth_simple() {
    assert_eq!(ir_body_depth(&IRBody::Ret(IRArg::Var(VarId(0)))), 1);
}

#[test]
fn test_ir_body_depth_nested() {
    let body = IRBody::VDecl {
        var: VarId(0),
        ty: IRType::UInt64,
        value: IRExpr::Lit(IRLiteral::UInt64(1)),
        rest: Box::new(IRBody::VDecl {
            var: VarId(1),
            ty: IRType::UInt64,
            value: IRExpr::Lit(IRLiteral::UInt64(2)),
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        }),
    };
    assert_eq!(ir_body_depth(&body), 3);
}

#[test]
fn test_ir_body_depth_case() {
    assert_eq!(ir_body_depth(&case_body()), 2);
}

#[test]
fn test_ir_body_node_count_simple() {
    assert_eq!(ir_body_node_count(&IRBody::Ret(IRArg::Var(VarId(0)))), 1);
}

#[test]
fn test_ir_body_node_count_inc_dec_ret() {
    assert_eq!(ir_body_node_count(&rc_body()), 4);
}

#[test]
fn test_ir_body_node_count_case() {
    // case node (1) + 2 alt bodies (each 1) = 3
    assert_eq!(ir_body_node_count(&case_body()), 3);
}

#[test]
fn test_ir_rc_ops_count() {
    let (incs, decs) = ir_rc_ops_count(&rc_body());
    assert_eq!(incs, 2);
    assert_eq!(decs, 1);
}

#[test]
fn test_ir_rc_ops_count_no_rc() {
    let (incs, decs) = ir_rc_ops_count(&IRBody::Ret(IRArg::Var(VarId(0))));
    assert_eq!(incs, 0);
    assert_eq!(decs, 0);
}

#[test]
fn test_ir_var_usage() {
    let body = IRBody::VDecl {
        var: VarId(0),
        ty: IRType::UInt64,
        value: IRExpr::Apply {
            fn_id: mk_fn_id("f"),
            args: vec![IRArg::Var(VarId(1)), IRArg::Var(VarId(1))],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
    };
    let usage = ir_var_usage(&body);
    assert_eq!(*usage.get(&VarId(1)).unwrap_or(&0), 2);
    assert!(usage.contains_key(&VarId(0)));
}

#[test]
fn test_ir_stats_string() {
    let stats = pretty_print_ir_stats(&simple_ir_decl());
    assert!(stats.contains("Nat.zero"));
    assert!(stats.contains("nodes="));
    assert!(stats.contains("depth="));
    assert!(stats.contains("incs="));
    assert!(stats.contains("decs="));
    assert!(stats.contains("vars="));
}

// ── LCNF printing ──────────────────────────────────────────────────

#[test]
fn test_lcnf_return() {
    let mut p = ExtIrPrinter::new(ExtPrettyConfig::default());
    p.print_lcnf_code(&mk_lcnf_return(42));
    let result = p.into_string();
    assert!(result.contains("return"));
    assert!(result.contains("42"));
}

#[test]
fn test_lcnf_let_binding() {
    let code = mk_lcnf_let(1, LetValue::nat(99), mk_lcnf_return(1));
    let mut p = ExtIrPrinter::new(ExtPrettyConfig::default());
    p.print_lcnf_code(&code);
    let result = p.into_string();
    assert!(result.contains("let"));
    assert!(result.contains("99"));
}

#[test]
fn test_lcnf_decl_pretty_print() {
    let result = pretty_print_lcnf(&simple_lcnf_decl());
    assert!(result.contains("def"));
    assert!(result.contains("Nat.succ"));
}

#[test]
fn test_lcnf_extern_decl() {
    let decl = Decl::extern_decl(
        Name::from_string("IO.println"),
        vec![],
        Expr::prop(),
        vec![Param::new(
            FVarId::new(0),
            Name::from_string("s"),
            Expr::prop(),
        )],
        vec![ExternEntry {
            backend: "c".into(),
            name: "clean_io_println".into(),
        }],
    );
    let result = pretty_print_lcnf(&decl);
    assert!(result.contains("extern"));
    assert!(result.contains("c"));
    assert!(result.contains("clean_io_println"));
}

#[test]
fn test_lcnf_summary_mode() {
    let mut p = ExtIrPrinter::new(ExtPrettyConfig {
        summary_mode: true,
        ..ExtPrettyConfig::default()
    });
    p.print_lcnf_decl(&simple_lcnf_decl());
    let result = p.into_string();
    assert!(result.contains("Nat.succ"));
    assert!(result.contains("1 params"));
    assert!(result.contains("nodes"));
}

#[test]
fn test_lcnf_stable_ordering() {
    let decls = vec![
        Decl::new(
            Name::from_string("Zebra"),
            vec![],
            Expr::prop(),
            vec![],
            mk_lcnf_return(0),
            false,
        ),
        Decl::new(
            Name::from_string("Alpha"),
            vec![],
            Expr::prop(),
            vec![],
            mk_lcnf_return(0),
            false,
        ),
    ];
    let mut p = ExtIrPrinter::new(ExtPrettyConfig {
        stable_ordering: true,
        ..ExtPrettyConfig::default()
    });
    p.print_lcnf_decls(&decls);
    let result = p.into_string();
    let alpha_pos = result.find("Alpha").expect("should contain Alpha");
    let zebra_pos = result.find("Zebra").expect("should contain Zebra");
    assert!(alpha_pos < zebra_pos);
}

// ── Join point and jump ─────────────────────────────────────────────

#[test]
fn test_ext_print_join_point() {
    let body = IRBody::JDecl {
        jp: JoinPointId(0),
        params: vec![(VarId(1), IRType::Object)],
        body: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        rest: Box::new(IRBody::Jmp {
            jp: JoinPointId(0),
            args: vec![IRArg::Var(VarId(0))],
        }),
    };
    let mut p = ExtIrPrinter::new(ExtPrettyConfig::default());
    p.print_ir_body(&body);
    let result = p.into_string();
    assert!(result.contains("jp"));
    assert!(result.contains("jmp"));
}

// ── Set operations ──────────────────────────────────────────────────

#[test]
fn test_ext_print_set_ops() {
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
    let mut p = ExtIrPrinter::new(ExtPrettyConfig::default());
    p.print_ir_body(&body);
    let result = p.into_string();
    assert!(result.contains("set"));
    assert!(result.contains("set_tag"));
}

// ── Unreachable ─────────────────────────────────────────────────────

#[test]
fn test_ext_print_unreachable() {
    let mut p = ExtIrPrinter::new(ExtPrettyConfig::default());
    p.print_ir_body(&IRBody::Unreachable);
    let result = p.into_string();
    assert!(result.contains("unreachable"));
}

// ── Multiple decls ──────────────────────────────────────────────────

#[test]
fn test_print_multiple_ir_decls() {
    let decls = vec![simple_ir_decl(), two_param_decl()];
    let mut p = ExtIrPrinter::new(ExtPrettyConfig::default());
    p.print_ir_decls(&decls);
    let result = p.into_string();
    assert!(result.contains("Nat.zero"));
    assert!(result.contains("Nat.add"));
}
