// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// 3.14 here is an arbitrary test value, not an approximation of PI.
#![allow(clippy::approx_constant)]

//! Tests for IR pretty printer.
//! Part of #3084 - IO/FFI/Native.

use crate::ir::{
    CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, JoinPointId, VarId,
};
use crate::ir_pretty::{pretty_print_body, pretty_print_decl, IrPrinter, PrettyConfig};
use clean_kernel::Name;

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

// --- Config ---

#[test]
fn test_config_defaults() {
    let d = PrettyConfig::default();
    assert_eq!(d.indent_size, 2);
    assert!(d.show_types && !d.show_var_ids && d.use_unicode && !d.show_metadata);

    let c = PrettyConfig::compact();
    assert!(!c.show_types && !c.show_metadata);

    let v = PrettyConfig::verbose();
    assert!(v.show_types && v.show_var_ids && v.show_metadata);
}

// --- Terminals: ret, unreachable ---

#[test]
fn test_print_ret() {
    assert_eq!(
        pretty_print_body(&IRBody::Ret(IRArg::Var(VarId(0)))),
        "ret x0"
    );
    assert_eq!(
        pretty_print_body(&IRBody::Ret(IRArg::Erased)),
        "ret \u{25C7}"
    );
}

#[test]
fn test_print_unreachable() {
    assert_eq!(pretty_print_body(&IRBody::Unreachable), "unreachable");
}

// --- Let binding ---

#[test]
fn test_print_let_with_types() {
    let body = IRBody::VDecl {
        var: VarId(1),
        ty: IRType::UInt64,
        value: IRExpr::Lit(IRLiteral::UInt64(42)),
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
    };
    let result = pretty_print_body(&body);
    assert!(result.contains("let x1 : UInt64 := 42u64"));
    assert!(result.contains("ret x1"));
}

#[test]
fn test_print_let_compact() {
    let body = IRBody::VDecl {
        var: VarId(1),
        ty: IRType::UInt64,
        value: IRExpr::Lit(IRLiteral::UInt64(42)),
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
    };
    let mut p = IrPrinter::new(PrettyConfig::compact());
    p.print_body(&body);
    let result = p.into_string();
    assert!(result.contains("let x1 := 42u64"));
    assert!(!result.contains(": UInt64"));
}

// --- Inc/Dec ---

#[test]
fn test_print_inc_dec() {
    let body = IRBody::Inc {
        var: VarId(0),
        n: 1,
        rest: Box::new(IRBody::Dec {
            var: VarId(0),
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
        }),
    };
    let result = pretty_print_body(&body);
    assert!(result.contains("inc x0") && result.contains("dec x0") && result.contains("ret x0"));
}

#[test]
fn test_print_inc_multiple() {
    let body = IRBody::Inc {
        var: VarId(3),
        n: 5,
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(3)))),
    };
    assert!(pretty_print_body(&body).contains("inc x3 5"));
}

// --- Application ---

#[test]
fn test_print_apply() {
    let body = IRBody::VDecl {
        var: VarId(2),
        ty: IRType::Object,
        value: IRExpr::Apply {
            fn_id: mk_fn_id("Nat.add"),
            args: vec![IRArg::Var(VarId(0)), IRArg::Var(VarId(1))],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
    };
    assert!(pretty_print_body(&body).contains("Nat.add x0 x1"));
}

// --- Case analysis ---

#[test]
fn test_print_case() {
    let body = IRBody::Case {
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
    };
    let result = pretty_print_body(&body);
    assert!(result.contains("case x0 of"));
    assert!(result.contains("| Bool.true =>") && result.contains("| Bool.false =>"));
    assert!(result.contains("ret x1") && result.contains("ret x2"));
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
    let result = pretty_print_body(&body);
    assert!(result.contains("| _ =>") && result.contains("unreachable"));
}

// --- Join points and jumps ---

#[test]
fn test_print_join_point_and_jump() {
    let body = IRBody::JDecl {
        jp: JoinPointId(0),
        params: vec![(VarId(1), IRType::Object)],
        body: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        rest: Box::new(IRBody::Jmp {
            jp: JoinPointId(0),
            args: vec![IRArg::Var(VarId(0))],
        }),
    };
    let result = pretty_print_body(&body);
    assert!(
        result.contains("jp jp0") && result.contains("ret x1") && result.contains("goto jp0 x0")
    );
}

#[test]
fn test_print_jump_no_args() {
    assert_eq!(
        pretty_print_body(&IRBody::Jmp {
            jp: JoinPointId(2),
            args: vec![]
        }),
        "goto jp2"
    );
}

// --- Set operations ---

#[test]
fn test_print_set_operations() {
    let set = IRBody::Set {
        var: VarId(0),
        idx: 1,
        value: VarId(2),
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
    };
    assert!(pretty_print_body(&set).contains("x0[1] := x2"));

    let set_tag = IRBody::SetTag {
        var: VarId(0),
        tag: 3,
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
    };
    assert!(pretty_print_body(&set_tag).contains("setTag x0 3"));

    let uset = IRBody::USet {
        var: VarId(0),
        idx: 0,
        value: VarId(1),
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
    };
    assert!(pretty_print_body(&uset).contains("uset x0[0] := x1"));

    let sset = IRBody::SSet {
        var: VarId(0),
        n: 2,
        offset: 4,
        value: VarId(1),
        ty: IRType::UInt32,
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
    };
    assert!(pretty_print_body(&sset).contains("sset x0[2, 4] := x1 : UInt32"));
}

// --- Expression formatting ---

#[test]
fn test_format_ctor() {
    let p = IrPrinter::new(PrettyConfig::default());
    assert_eq!(
        p.format_expr(&IRExpr::Ctor {
            info: mk_ctor("Unit.unit", 0),
            args: vec![]
        }),
        "ctor Unit.unit"
    );
    assert_eq!(
        p.format_expr(&IRExpr::Ctor {
            info: mk_ctor("Pair.mk", 0),
            args: vec![IRArg::Var(VarId(0)), IRArg::Var(VarId(1))],
        }),
        "ctor Pair.mk x0 x1"
    );
}

#[test]
fn test_format_proj_box_unbox() {
    let p = IrPrinter::new(PrettyConfig::default());
    assert_eq!(
        p.format_expr(&IRExpr::Proj {
            idx: 0,
            ty: IRType::Object,
            arg: IRArg::Var(VarId(0))
        }),
        "proj[0] x0 : Object"
    );
    assert_eq!(
        p.format_expr(&IRExpr::Box {
            ty: IRType::UInt64,
            arg: IRArg::Var(VarId(0))
        }),
        "box[UInt64] x0"
    );
    assert_eq!(
        p.format_expr(&IRExpr::Unbox {
            ty: IRType::UInt64,
            arg: IRArg::Var(VarId(1))
        }),
        "unbox[UInt64] x1"
    );
}

#[test]
fn test_format_partial_and_closure_apply() {
    let p = IrPrinter::new(PrettyConfig::default());
    assert_eq!(
        p.format_expr(&IRExpr::PartialApply {
            fn_id: mk_fn_id("List.map"),
            arity: 3,
            args: vec![IRArg::Var(VarId(0))]
        }),
        "papp List.map x0"
    );

    let pv = IrPrinter::new(PrettyConfig::verbose());
    let result = pv.format_expr(&IRExpr::PartialApply {
        fn_id: mk_fn_id("List.map"),
        arity: 3,
        args: vec![IRArg::Var(VarId(0))],
    });
    assert!(result.contains("arity=3"));

    assert_eq!(
        p.format_expr(&IRExpr::ClosureApply {
            closure: IRArg::Var(VarId(0)),
            args: vec![IRArg::Var(VarId(1))]
        }),
        "ap x0 x1"
    );
}

#[test]
fn test_format_misc_exprs() {
    let p = IrPrinter::new(PrettyConfig::default());
    assert_eq!(p.format_expr(&IRExpr::IsShared(VarId(5))), "isShared x5");
    assert_eq!(p.format_expr(&IRExpr::Reset(VarId(0))), "reset x0");
    assert_eq!(p.format_expr(&IRExpr::Tag(IRArg::Var(VarId(0)))), "tag x0");
    assert_eq!(p.format_expr(&IRExpr::String("hello".into())), "\"hello\"");
    assert_eq!(
        p.format_expr(&IRExpr::Apply {
            fn_id: mk_fn_id("IO.getLine"),
            args: vec![]
        }),
        "IO.getLine ()"
    );
    assert_eq!(
        p.format_expr(&IRExpr::UProj {
            idx: 2,
            var: VarId(0)
        }),
        "uproj[2] x0"
    );
    assert_eq!(
        p.format_expr(&IRExpr::SProj {
            n: 1,
            offset: 8,
            var: VarId(0),
            ty: IRType::UInt64
        }),
        "sproj[1, 8] x0 : UInt64"
    );
}

#[test]
fn test_format_reset_reuse() {
    let p = IrPrinter::new(PrettyConfig::default());
    let reuse = IRExpr::Reuse {
        var: VarId(0),
        ctor: mk_ctor("Pair.mk", 0),
        args: vec![IRArg::Var(VarId(1)), IRArg::Var(VarId(2))],
    };
    assert_eq!(p.format_expr(&reuse), "reuse x0 in ctor Pair.mk x1 x2");
}

// --- Literals ---

#[test]
fn test_format_literals() {
    let p = IrPrinter::new(PrettyConfig::default());
    assert_eq!(p.format_expr(&IRExpr::Lit(IRLiteral::Bool(true))), "true");
    assert_eq!(p.format_expr(&IRExpr::Lit(IRLiteral::UInt8(255))), "255u8");
    assert_eq!(
        p.format_expr(&IRExpr::Lit(IRLiteral::Float64(3.14))),
        "3.1f64"
    );
}

// --- Declarations ---

#[test]
fn test_print_decl_simple() {
    let decl = IRDecl {
        name: Name::from_string("Nat.zero"),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(VarId(0))),
    };
    let result = pretty_print_decl(&decl);
    assert!(
        result.contains("def Nat.zero") && result.contains("Object") && result.contains("ret x0")
    );
}

#[test]
fn test_print_decl_with_params() {
    let decl = IRDecl {
        name: Name::from_string("Nat.add"),
        params: vec![(VarId(0), IRType::Object), (VarId(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(VarId(0))),
    };
    let result = pretty_print_decl(&decl);
    assert!(result.contains("def Nat.add (x0 : Object, x1 : Object)"));
    assert!(result.contains("\u{2192} Object"));
}

// --- Indentation ---

#[test]
fn test_nested_let_indentation() {
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
    let output = pretty_print_body(&body);
    let lines: Vec<&str> = output.lines().collect();
    assert_eq!(lines.len(), 3);
    assert!(
        lines[0].starts_with("let x0")
            && lines[1].starts_with("let x1")
            && lines[2].starts_with("ret")
    );
}

// --- Var ID and metadata modes ---

#[test]
fn test_var_id_verbose() {
    let mut p = IrPrinter::new(PrettyConfig::verbose());
    p.print_body(&IRBody::Ret(IRArg::Var(VarId(42))));
    assert_eq!(p.into_string(), "ret x_42");
}

#[test]
fn test_ctor_metadata_verbose() {
    let mut p = IrPrinter::new(PrettyConfig::verbose());
    let body = IRBody::Case {
        scrutinee: VarId(0),
        alts: vec![IRAlt {
            ctor: CtorInfo {
                name: Name::from_string("List.cons"),
                tag: 1,
                num_scalars: 0,
                num_objects: 2,
                field_types: vec![IRType::Object, IRType::Object],
            },
            body: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        }],
        default: None,
    };
    p.print_body(&body);
    assert!(p.into_string().contains("[tag=1, scalars=0, objects=2]"));
}

// --- Types ---

#[test]
fn test_format_types() {
    let p = IrPrinter::new(PrettyConfig::default());
    assert_eq!(
        p.format_type(&IRType::Struct(vec![IRType::UInt64, IRType::Object])),
        "Struct(UInt64, Object)"
    );
    assert_eq!(
        p.format_type(&IRType::Union(vec![IRType::Bool, IRType::UInt32])),
        "Union(Bool, UInt32)"
    );
    assert_eq!(p.format_type(&IRType::Erased), "\u{25C7}");
    assert_eq!(p.format_type(&IRType::Void), "Void");
}

// --- ASCII mode ---

#[test]
fn test_ascii_mode_decl() {
    let decl = IRDecl {
        name: Name::from_string("id"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(VarId(0))),
    };
    let mut p = IrPrinter::new(PrettyConfig {
        use_unicode: false,
        ..PrettyConfig::default()
    });
    p.print_decl(&decl);
    assert!(p.into_string().contains("-> Object"));
}
