// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended IR back-translation module.
//!
//! Part of #3083.

use super::back_translate_ext::*;
use crate::ir::*;
use clean_kernel::{Expr, ExprKind, Name};

fn nm(s: &str) -> Name {
    s.parse().expect("valid name")
}

fn mk_ctor(name: &str, tag: u32) -> CtorInfo {
    CtorInfo {
        name: nm(name),
        tag,
        num_scalars: 0,
        num_objects: 0,
        field_types: vec![],
    }
}

fn mk_fn_id(s: &str) -> FnId {
    FnId(nm(s))
}

fn simple_ret_body(arg: IRArg) -> IRBody {
    IRBody::Ret(arg)
}

fn vdecl(var: u32, ty: IRType, val: IRExpr, rest: IRBody) -> IRBody {
    IRBody::VDecl {
        var: VarId(var),
        ty,
        value: val,
        rest: Box::new(rest),
    }
}

// === NameRegistry tests ===

#[test]
fn test_registry_new_is_empty() {
    let r = NameRegistry::new();
    assert_eq!(r.var_count(), 0);
}

#[test]
fn test_registry_register_and_lookup_var() {
    let mut r = NameRegistry::new();
    r.register_var(VarId(0), nm("x"));
    assert_eq!(r.var_name(VarId(0)), nm("x"));
    assert_eq!(r.var_count(), 1);
}

#[test]
fn test_registry_var_fallback_name() {
    let r = NameRegistry::new();
    let name = r.var_name(VarId(42));
    assert_eq!(name, nm("_x42"));
}

#[test]
fn test_registry_register_and_lookup_ctor() {
    let mut r = NameRegistry::new();
    r.register_ctor(0, nm("Nat.zero"));
    assert_eq!(r.ctor_name(0), Some(&nm("Nat.zero")));
    assert_eq!(r.ctor_name(1), None);
}

#[test]
fn test_registry_register_and_lookup_fn() {
    let mut r = NameRegistry::new();
    r.register_fn("Nat.add", nm("Nat.add"));
    assert_eq!(r.fn_name("Nat.add"), Some(&nm("Nat.add")));
    assert!(r.fn_name("missing").is_none());
}

#[test]
fn test_translator_registry_mut_updates_registry() {
    let mut translator = BackTranslator::new(NameRegistry::new());
    translator
        .registry_mut()
        .register_var(VarId(7), nm("seven"));
    assert_eq!(translator.registry().var_name(VarId(7)), nm("seven"));
}

// === BackTranslateStats tests ===

#[test]
fn test_stats_default_zero() {
    let s = BackTranslateStats::default();
    assert_eq!(s.terms_reconstructed, 0);
    assert_eq!(s.names_recovered, 0);
    assert_eq!(s.partial_reconstructions, 0);
    assert_eq!(s.ctors_recovered, 0);
}

#[test]
fn test_stats_display() {
    let s = BackTranslateStats {
        terms_reconstructed: 10,
        names_recovered: 3,
        partial_reconstructions: 2,
        ctors_recovered: 5,
    };
    let d = format!("{s}");
    assert!(d.contains("reconstructed=10"));
    assert!(d.contains("names=3"));
}

// === Type reconstruction tests ===

#[test]
fn test_translate_type_bool() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let e = t.translate_type(&IRType::Bool);
    assert!(matches!(e.kind(), ExprKind::Const(n, _) if n.to_string() == "Bool"));
}

#[test]
fn test_translate_type_uint64() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let e = t.translate_type(&IRType::UInt64);
    assert!(matches!(e.kind(), ExprKind::Const(n, _) if n.to_string() == "UInt64"));
}

#[test]
fn test_translate_type_erased_is_partial() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let _ = t.translate_type(&IRType::Erased);
    assert_eq!(t.stats().partial_reconstructions, 1);
}

#[test]
fn test_translate_type_void_is_unit() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let e = t.translate_type(&IRType::Void);
    assert!(matches!(e.kind(), ExprKind::Const(n, _) if n.to_string() == "Unit"));
}

#[test]
fn test_translate_type_struct() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let e = t.translate_type(&IRType::Struct(vec![IRType::Bool, IRType::UInt8]));
    // Should be (Struct Bool UInt8)
    let pp = pretty_print(&e);
    assert!(pp.contains("Struct"));
    assert!(pp.contains("Bool"));
}

#[test]
fn test_translate_type_union() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let e = t.translate_type(&IRType::Union(vec![IRType::Object]));
    let pp = pretty_print(&e);
    assert!(pp.contains("Union"));
}

#[test]
fn test_translate_type_all_scalars() {
    let mut t = BackTranslator::new(NameRegistry::new());
    for ty in &[
        IRType::UInt8,
        IRType::UInt16,
        IRType::UInt32,
        IRType::USize,
        IRType::Float32,
        IRType::Float64,
    ] {
        let _ = t.translate_type(ty);
    }
    assert!(t.stats().terms_reconstructed >= 6);
}

// === Literal reconstruction tests ===

#[test]
fn test_translate_literal_bool_true() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let e = t.translate_literal(&IRLiteral::Bool(true));
    assert!(matches!(e.kind(), ExprKind::Const(n, _) if n.to_string() == "Bool.true"));
}

#[test]
fn test_translate_literal_bool_false() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let e = t.translate_literal(&IRLiteral::Bool(false));
    assert!(matches!(e.kind(), ExprKind::Const(n, _) if n.to_string() == "Bool.false"));
}

#[test]
fn test_translate_literal_uint64() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let e = t.translate_literal(&IRLiteral::UInt64(42));
    assert!(matches!(
        e.kind(),
        ExprKind::Lit(clean_kernel::Literal::Nat(_))
    ));
}

#[test]
fn test_translate_literal_float_is_partial() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let _ = t.translate_literal(&IRLiteral::Float64(1.25));
    assert_eq!(t.stats().partial_reconstructions, 1);
}

// === Arg reconstruction tests ===

#[test]
fn test_translate_arg_var_with_name() {
    let mut reg = NameRegistry::new();
    reg.register_var(VarId(0), nm("x"));
    let mut t = BackTranslator::new(reg);
    let e = t.translate_arg(&IRArg::Var(VarId(0)));
    assert!(matches!(e.kind(), ExprKind::Const(n, _) if n.to_string() == "x"));
    assert_eq!(t.stats().names_recovered, 1);
}

#[test]
fn test_translate_arg_var_without_name() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let e = t.translate_arg(&IRArg::Var(VarId(7)));
    assert!(matches!(e.kind(), ExprKind::Const(n, _) if n.to_string() == "_x7"));
    assert_eq!(t.stats().names_recovered, 0);
}

#[test]
fn test_translate_arg_erased() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let _ = t.translate_arg(&IRArg::Erased);
    assert_eq!(t.stats().partial_reconstructions, 1);
}

// === IRExpr reconstruction tests ===

#[test]
fn test_translate_expr_ctor_no_args() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let e = t.translate_expr(&IRExpr::Ctor {
        info: mk_ctor("Nat.zero", 0),
        args: vec![],
    });
    assert!(matches!(e.kind(), ExprKind::Const(n, _) if n.to_string() == "Nat.zero"));
}

#[test]
fn test_translate_expr_ctor_with_args() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let e = t.translate_expr(&IRExpr::Ctor {
        info: mk_ctor("Nat.succ", 1),
        args: vec![IRArg::Var(VarId(0))],
    });
    assert!(matches!(e.kind(), ExprKind::App(_, _)));
}

#[test]
fn test_translate_expr_lit() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let e = t.translate_expr(&IRExpr::Lit(IRLiteral::UInt32(99)));
    assert!(matches!(e.kind(), ExprKind::Lit(_)));
}

#[test]
fn test_translate_expr_apply() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let e = t.translate_expr(&IRExpr::Apply {
        fn_id: mk_fn_id("Nat.add"),
        args: vec![IRArg::Var(VarId(0)), IRArg::Var(VarId(1))],
    });
    assert!(matches!(e.kind(), ExprKind::App(_, _)));
}

#[test]
fn test_translate_expr_tag() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let e = t.translate_expr(&IRExpr::Tag(IRArg::Var(VarId(0))));
    let pp = pretty_print(&e);
    assert!(pp.contains("_tag"));
}

#[test]
fn test_translate_expr_box() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let e = t.translate_expr(&IRExpr::Box {
        ty: IRType::UInt64,
        arg: IRArg::Var(VarId(0)),
    });
    let pp = pretty_print(&e);
    assert!(pp.contains("_box"));
}

#[test]
fn test_translate_expr_unbox() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let e = t.translate_expr(&IRExpr::Unbox {
        ty: IRType::UInt64,
        arg: IRArg::Var(VarId(0)),
    });
    let pp = pretty_print(&e);
    assert!(pp.contains("_unbox"));
}

#[test]
fn test_translate_expr_string() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let e = t.translate_expr(&IRExpr::String("hello".to_owned()));
    assert!(matches!(
        e.kind(),
        ExprKind::Lit(clean_kernel::Literal::String(_))
    ));
}

#[test]
fn test_translate_expr_proj() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let e = t.translate_expr(&IRExpr::Proj {
        idx: 1,
        ty: IRType::Object,
        arg: IRArg::Var(VarId(0)),
    });
    assert!(matches!(e.kind(), ExprKind::Proj(_, 1, _)));
}

#[test]
fn test_translate_expr_partial_apply() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let e = t.translate_expr(&IRExpr::PartialApply {
        fn_id: mk_fn_id("f"),
        arity: 3,
        args: vec![IRArg::Var(VarId(0))],
    });
    assert!(matches!(e.kind(), ExprKind::App(_, _)));
}

#[test]
fn test_translate_expr_closure_apply() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let e = t.translate_expr(&IRExpr::ClosureApply {
        closure: IRArg::Var(VarId(0)),
        args: vec![IRArg::Var(VarId(1))],
    });
    assert!(matches!(e.kind(), ExprKind::App(_, _)));
}

#[test]
fn test_translate_expr_is_shared() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let e = t.translate_expr(&IRExpr::IsShared(VarId(0)));
    let pp = pretty_print(&e);
    assert!(pp.contains("_isShared"));
}

#[test]
fn test_translate_expr_reset() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let e = t.translate_expr(&IRExpr::Reset(VarId(0)));
    let pp = pretty_print(&e);
    assert!(pp.contains("_reset"));
}

#[test]
fn test_translate_expr_reuse() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let e = t.translate_expr(&IRExpr::Reuse {
        var: VarId(0),
        ctor: mk_ctor("Pair.mk", 0),
        args: vec![IRArg::Var(VarId(1))],
    });
    let pp = pretty_print(&e);
    assert!(pp.contains("_reuse"));
}

#[test]
fn test_translate_expr_uproj() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let e = t.translate_expr(&IRExpr::UProj {
        idx: 2,
        var: VarId(0),
    });
    let pp = pretty_print(&e);
    assert!(pp.contains("_uproj2"));
}

#[test]
fn test_translate_expr_sproj() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let e = t.translate_expr(&IRExpr::SProj {
        n: 1,
        offset: 4,
        var: VarId(0),
        ty: IRType::UInt32,
    });
    let pp = pretty_print(&e);
    assert!(pp.contains("_sproj1_4"));
}

// === IRBody reconstruction tests ===

#[test]
fn test_translate_body_ret() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let e = t.translate_body(&simple_ret_body(IRArg::Var(VarId(0))));
    assert!(matches!(e.kind(), ExprKind::Const(_, _)));
}

#[test]
fn test_translate_body_vdecl() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let body = vdecl(
        0,
        IRType::UInt64,
        IRExpr::Lit(IRLiteral::UInt64(5)),
        IRBody::Ret(IRArg::Var(VarId(0))),
    );
    let e = t.translate_body(&body);
    assert!(matches!(e.kind(), ExprKind::Let(_, _, _, _, _)));
}

#[test]
fn test_translate_body_inc_dec_skipped() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let body = IRBody::Inc {
        var: VarId(0),
        n: 1,
        rest: Box::new(IRBody::Dec {
            var: VarId(0),
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
        }),
    };
    let e = t.translate_body(&body);
    // Should skip Inc/Dec and just return the variable
    assert!(matches!(e.kind(), ExprKind::Const(_, _)));
}

#[test]
fn test_translate_body_unreachable() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let e = t.translate_body(&IRBody::Unreachable);
    assert_eq!(t.stats().partial_reconstructions, 1);
    let pp = pretty_print(&e);
    assert!(pp.contains("_unreachable"));
}

#[test]
fn test_translate_body_jmp() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let body = IRBody::Jmp {
        jp: JoinPointId(3),
        args: vec![IRArg::Var(VarId(0))],
    };
    let e = t.translate_body(&body);
    let pp = pretty_print(&e);
    assert!(pp.contains("_jp3"));
}

#[test]
fn test_translate_body_case() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let body = IRBody::Case {
        scrutinee: VarId(0),
        alts: vec![IRAlt {
            ctor: mk_ctor("Nat.zero", 0),
            body: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        }],
        default: Some(Box::new(IRBody::Ret(IRArg::Var(VarId(2))))),
    };
    let e = t.translate_body(&body);
    let pp = pretty_print(&e);
    assert!(pp.contains("_match"));
}

#[test]
fn test_translate_body_jdecl() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let body = IRBody::JDecl {
        jp: JoinPointId(0),
        params: vec![(VarId(1), IRType::Object)],
        body: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
    };
    let e = t.translate_body(&body);
    let pp = pretty_print(&e);
    assert!(pp.contains("_jp"));
}

#[test]
fn test_translate_body_set_skipped() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let body = IRBody::Set {
        var: VarId(0),
        idx: 0,
        value: VarId(1),
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
    };
    let e = t.translate_body(&body);
    assert!(matches!(e.kind(), ExprKind::Const(_, _)));
}

// === Decl reconstruction tests ===

#[test]
fn test_translate_decl_signature() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let decl = IRDecl {
        name: nm("f"),
        params: vec![(VarId(0), IRType::UInt64)],
        return_type: IRType::Bool,
        body: IRBody::Ret(IRArg::Var(VarId(0))),
    };
    let e = t.translate_decl_signature(&decl);
    assert!(matches!(e.kind(), ExprKind::Pi(_, _, _)));
}

#[test]
fn test_translate_decl_full() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let decl = IRDecl {
        name: nm("id"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(VarId(0))),
    };
    let e = t.translate_decl(&decl);
    assert!(matches!(e.kind(), ExprKind::Let(_, _, _, _, _)));
    let pp = pretty_print(&e);
    assert!(pp.contains("id"));
}

#[test]
fn test_translate_decl_auto_registers_param_names() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let decl = IRDecl {
        name: nm("g"),
        params: vec![(VarId(0), IRType::UInt8), (VarId(1), IRType::Bool)],
        return_type: IRType::Void,
        body: IRBody::Ret(IRArg::Erased),
    };
    let _ = t.translate_decl(&decl);
    assert_eq!(t.registry().var_count(), 2);
}

// === Pretty-print tests ===

#[test]
fn test_pretty_print_const() {
    let e = Expr::const_str("Nat");
    assert_eq!(pretty_print(&e), "Nat");
}

#[test]
fn test_pretty_print_app() {
    let e = Expr::app(Expr::const_str("f"), Expr::const_str("x"));
    assert_eq!(pretty_print(&e), "(f x)");
}

#[test]
fn test_pretty_print_let() {
    let e = Expr::let_named(
        nm("x"),
        Expr::const_str("Nat"),
        Expr::nat_lit(0),
        Expr::const_str("x"),
        false,
    );
    let pp = pretty_print(&e);
    assert!(pp.contains("let x"));
    assert!(pp.contains("Nat"));
}

#[test]
fn test_pretty_print_nat_lit() {
    let e = Expr::nat_lit(42);
    assert_eq!(pretty_print(&e), "42");
}

#[test]
fn test_pretty_print_string_lit() {
    let e = Expr::str_lit("hello");
    assert_eq!(pretty_print(&e), "\"hello\"");
}

// === Round-trip tests ===

#[test]
fn test_round_trip_exact_match() {
    let a = Expr::const_str("Nat");
    let b = Expr::const_str("Nat");
    assert_eq!(round_trip_compare(&a, &b), RoundTripResult::ExactMatch);
}

#[test]
fn test_round_trip_partial_on_placeholder() {
    let a = Expr::const_str("Nat");
    let b = Expr::const_str("_erased");
    assert!(matches!(
        round_trip_compare(&a, &b),
        RoundTripResult::PartialMatch { .. }
    ));
}

#[test]
fn test_round_trip_mismatch() {
    let a = Expr::const_str("Nat");
    let b = Expr::const_str("Bool");
    assert!(matches!(
        round_trip_compare(&a, &b),
        RoundTripResult::Mismatch { .. }
    ));
}

#[test]
fn test_round_trip_app_match() {
    let a = Expr::app(Expr::const_str("f"), Expr::const_str("x"));
    let b = Expr::app(Expr::const_str("f"), Expr::const_str("x"));
    assert_eq!(round_trip_compare(&a, &b), RoundTripResult::ExactMatch);
}

#[test]
fn test_round_trip_app_partial() {
    let a = Expr::app(Expr::const_str("f"), Expr::const_str("x"));
    let b = Expr::app(Expr::const_str("f"), Expr::const_str("_erased"));
    assert!(matches!(
        round_trip_compare(&a, &b),
        RoundTripResult::PartialMatch { .. }
    ));
}

#[test]
fn test_round_trip_let_match() {
    let a = Expr::let_named(
        nm("x"),
        Expr::const_str("T"),
        Expr::const_str("v"),
        Expr::const_str("b"),
        false,
    );
    let b = Expr::let_named(
        nm("x"),
        Expr::const_str("T"),
        Expr::const_str("v"),
        Expr::const_str("b"),
        false,
    );
    assert_eq!(round_trip_compare(&a, &b), RoundTripResult::ExactMatch);
}

#[test]
fn test_round_trip_let_name_diff() {
    let a = Expr::let_named(
        nm("x"),
        Expr::const_str("T"),
        Expr::const_str("v"),
        Expr::const_str("b"),
        false,
    );
    let b = Expr::let_named(
        nm("y"),
        Expr::const_str("T"),
        Expr::const_str("v"),
        Expr::const_str("b"),
        false,
    );
    assert!(matches!(
        round_trip_compare(&a, &b),
        RoundTripResult::PartialMatch { .. }
    ));
}

// === Constructor name recovery tests ===

#[test]
fn test_ctor_recovery_from_registry() {
    let mut reg = NameRegistry::new();
    reg.register_ctor(0, nm("MyType.mk"));
    let mut t = BackTranslator::new(reg);
    let e = t.translate_expr(&IRExpr::Ctor {
        info: mk_ctor("fallback", 0),
        args: vec![],
    });
    assert!(matches!(e.kind(), ExprKind::Const(n, _) if n.to_string() == "MyType.mk"));
}

#[test]
fn test_ctor_recovery_from_info() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let e = t.translate_expr(&IRExpr::Ctor {
        info: mk_ctor("Nat.succ", 1),
        args: vec![],
    });
    assert!(matches!(e.kind(), ExprKind::Const(n, _) if n.to_string() == "Nat.succ"));
    assert_eq!(t.stats().ctors_recovered, 1);
}

// === Function name recovery tests ===

#[test]
fn test_fn_recovery_from_registry() {
    let mut reg = NameRegistry::new();
    reg.register_fn("Nat.add", nm("Nat.add"));
    let mut t = BackTranslator::new(reg);
    let e = t.translate_expr(&IRExpr::Apply {
        fn_id: mk_fn_id("Nat.add"),
        args: vec![],
    });
    assert_eq!(t.stats().names_recovered, 1);
    assert!(matches!(e.kind(), ExprKind::Const(n, _) if n.to_string() == "Nat.add"));
}

// === Statistics accumulation test ===

#[test]
fn test_stats_accumulate_across_translations() {
    let mut reg = NameRegistry::new();
    reg.register_var(VarId(0), nm("x"));
    let mut t = BackTranslator::new(reg);
    let _ = t.translate_type(&IRType::Bool);
    let _ = t.translate_type(&IRType::Erased);
    let _ = t.translate_arg(&IRArg::Var(VarId(0)));
    let _ = t.translate_arg(&IRArg::Erased);
    assert!(t.stats().terms_reconstructed >= 3);
    assert_eq!(t.stats().names_recovered, 1);
    assert_eq!(t.stats().partial_reconstructions, 2);
}

// === Integration: compile → back-translate → compare ===

#[test]
fn test_integration_simple_identity() {
    let mut reg = NameRegistry::new();
    reg.register_var(VarId(0), nm("x"));
    let mut t = BackTranslator::new(reg);
    let decl = IRDecl {
        name: nm("id"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(VarId(0))),
    };
    let result = t.translate_decl(&decl);
    let pp = pretty_print(&result);
    assert!(pp.contains("id"));
    assert!(pp.contains("Object"));
    assert!(t.stats().terms_reconstructed > 0);
}

#[test]
fn test_integration_vdecl_chain() {
    let mut t = BackTranslator::new(NameRegistry::new());
    let body = vdecl(
        0,
        IRType::UInt64,
        IRExpr::Lit(IRLiteral::UInt64(1)),
        vdecl(
            1,
            IRType::UInt64,
            IRExpr::Lit(IRLiteral::UInt64(2)),
            IRBody::Ret(IRArg::Var(VarId(1))),
        ),
    );
    let e = t.translate_body(&body);
    let pp = pretty_print(&e);
    assert!(pp.contains("let"));
    // Two VDecls
    assert!(pp.matches("let").count() >= 2);
}

#[test]
fn test_integration_case_with_default() {
    let mut reg = NameRegistry::new();
    reg.register_var(VarId(0), nm("n"));
    reg.register_var(VarId(1), nm("result_zero"));
    reg.register_var(VarId(2), nm("result_default"));
    let mut t = BackTranslator::new(reg);
    let body = IRBody::Case {
        scrutinee: VarId(0),
        alts: vec![IRAlt {
            ctor: mk_ctor("Nat.zero", 0),
            body: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        }],
        default: Some(Box::new(IRBody::Ret(IRArg::Var(VarId(2))))),
    };
    let e = t.translate_body(&body);
    let pp = pretty_print(&e);
    assert!(pp.contains("_match"));
    assert!(pp.contains("n"));
}
