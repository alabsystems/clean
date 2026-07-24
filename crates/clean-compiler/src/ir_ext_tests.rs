// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for ir_ext: node statistics, def-use chains, structural comparison,
//! validation, subexpression extraction, and pretty summary.

use crate::ir::{
    CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, JoinPointId, VarId,
};
use crate::ir_ext::*;
use clean_kernel::Name;

// ── Helpers ────────────────────────────────────────────────────────────────

fn mk_name(s: &str) -> Name {
    Name::from_string(s)
}

fn simple_ret() -> IRBody {
    IRBody::Ret(IRArg::Var(VarId(0)))
}

fn mk_lit_vdecl(var: u32, rest: IRBody) -> IRBody {
    IRBody::VDecl {
        var: VarId(var),
        ty: IRType::UInt64,
        value: IRExpr::Lit(IRLiteral::UInt64(42)),
        rest: Box::new(rest),
    }
}

fn mk_inc(var: u32, rest: IRBody) -> IRBody {
    IRBody::Inc {
        var: VarId(var),
        n: 1,
        rest: Box::new(rest),
    }
}

fn mk_dec(var: u32, rest: IRBody) -> IRBody {
    IRBody::Dec {
        var: VarId(var),
        rest: Box::new(rest),
    }
}

fn mk_fn_id(s: &str) -> FnId {
    FnId(mk_name(s))
}

fn mk_apply(fn_name: &str, args: Vec<IRArg>) -> IRExpr {
    IRExpr::Apply {
        fn_id: mk_fn_id(fn_name),
        args,
    }
}

fn mk_ctor_info(name: &str, tag: u32) -> CtorInfo {
    CtorInfo {
        name: mk_name(name),
        tag,
        num_scalars: 0,
        num_objects: 0,
        field_types: vec![],
    }
}

fn mk_case(scrutinee: u32, alts: Vec<IRAlt>, default: Option<IRBody>) -> IRBody {
    IRBody::Case {
        scrutinee: VarId(scrutinee),
        alts,
        default: default.map(Box::new),
    }
}

fn mk_decl(name: &str, params: Vec<(VarId, IRType)>, body: IRBody) -> IRDecl {
    IRDecl {
        name: mk_name(name),
        params,
        return_type: IRType::Object,
        body,
    }
}

// ── NodeKindCounts tests ───────────────────────────────────────────────────

#[test]
fn test_node_kind_counts_ret_only() {
    let c = node_kind_counts(&simple_ret());
    assert_eq!(c.ret, 1);
    assert_eq!(c.total(), 1);
}

#[test]
fn test_node_kind_counts_vdecl_chain() {
    let body = mk_lit_vdecl(0, mk_lit_vdecl(1, simple_ret()));
    let c = node_kind_counts(&body);
    assert_eq!(c.vdecl, 2);
    assert_eq!(c.ret, 1);
    assert_eq!(c.total(), 3);
}

#[test]
fn test_node_kind_counts_inc_dec() {
    let body = mk_inc(0, mk_dec(0, simple_ret()));
    let c = node_kind_counts(&body);
    assert_eq!(c.inc, 1);
    assert_eq!(c.dec, 1);
    assert_eq!(c.total(), 3);
}

#[test]
fn test_node_kind_counts_case() {
    let body = mk_case(
        0,
        vec![IRAlt {
            ctor: mk_ctor_info("A", 0),
            body: Box::new(simple_ret()),
        }],
        Some(simple_ret()),
    );
    let c = node_kind_counts(&body);
    assert_eq!(c.case, 1);
    assert_eq!(c.ret, 2);
    assert_eq!(c.total(), 3);
}

#[test]
fn test_node_kind_counts_jdecl() {
    let body = IRBody::JDecl {
        jp: JoinPointId(0),
        params: vec![(VarId(10), IRType::Object)],
        body: Box::new(simple_ret()),
        rest: Box::new(simple_ret()),
    };
    let c = node_kind_counts(&body);
    assert_eq!(c.jdecl, 1);
    assert_eq!(c.ret, 2);
}

#[test]
fn test_node_kind_counts_unreachable() {
    let c = node_kind_counts(&IRBody::Unreachable);
    assert_eq!(c.unreachable, 1);
    assert_eq!(c.total(), 1);
}

#[test]
fn test_node_kind_counts_jmp() {
    let body = IRBody::Jmp {
        jp: JoinPointId(0),
        args: vec![],
    };
    let c = node_kind_counts(&body);
    assert_eq!(c.jmp, 1);
}

#[test]
fn test_node_kind_counts_set() {
    let body = IRBody::Set {
        var: VarId(0),
        idx: 0,
        value: VarId(1),
        rest: Box::new(simple_ret()),
    };
    let c = node_kind_counts(&body);
    assert_eq!(c.set, 1);
}

#[test]
fn test_node_kind_counts_set_tag() {
    let body = IRBody::SetTag {
        var: VarId(0),
        tag: 1,
        rest: Box::new(simple_ret()),
    };
    let c = node_kind_counts(&body);
    assert_eq!(c.set_tag, 1);
}

#[test]
fn test_node_kind_counts_uset() {
    let body = IRBody::USet {
        var: VarId(0),
        idx: 0,
        value: VarId(1),
        rest: Box::new(simple_ret()),
    };
    let c = node_kind_counts(&body);
    assert_eq!(c.uset, 1);
}

#[test]
fn test_node_kind_counts_sset() {
    let body = IRBody::SSet {
        var: VarId(0),
        n: 0,
        offset: 0,
        value: VarId(1),
        ty: IRType::UInt8,
        rest: Box::new(simple_ret()),
    };
    let c = node_kind_counts(&body);
    assert_eq!(c.sset, 1);
}

// ── Nesting depth tests ───────────────────────────────────────────────────

#[test]
fn test_nesting_depth_terminal() {
    assert_eq!(nesting_depth(&simple_ret()), 0);
    assert_eq!(nesting_depth(&IRBody::Unreachable), 0);
}

#[test]
fn test_nesting_depth_chain() {
    let body = mk_lit_vdecl(0, mk_lit_vdecl(1, simple_ret()));
    assert_eq!(nesting_depth(&body), 2);
}

#[test]
fn test_nesting_depth_case() {
    let body = mk_case(
        0,
        vec![IRAlt {
            ctor: mk_ctor_info("A", 0),
            body: Box::new(mk_lit_vdecl(1, simple_ret())),
        }],
        None,
    );
    // case(1) -> vdecl(2) -> ret(2)
    assert_eq!(nesting_depth(&body), 2);
}

#[test]
fn test_nesting_depth_jdecl() {
    let body = IRBody::JDecl {
        jp: JoinPointId(0),
        params: vec![],
        body: Box::new(mk_lit_vdecl(10, simple_ret())),
        rest: Box::new(simple_ret()),
    };
    assert_eq!(nesting_depth(&body), 2);
}

// ── Def-use chain tests ───────────────────────────────────────────────────

#[test]
fn test_def_use_simple() {
    let body = mk_lit_vdecl(1, IRBody::Ret(IRArg::Var(VarId(1))));
    let decl = mk_decl("f", vec![(VarId(0), IRType::Object)], body);
    let du = def_use_chain(&decl);
    assert_eq!(du.defs.get(&VarId(0)), Some(&DefSite::FuncParam));
    assert_eq!(du.defs.get(&VarId(1)), Some(&DefSite::VDecl));
    assert_eq!(du.uses.get(&VarId(1)), Some(&1));
}

#[test]
fn test_def_use_jp_param() {
    let body = IRBody::JDecl {
        jp: JoinPointId(0),
        params: vec![(VarId(5), IRType::Object)],
        body: Box::new(IRBody::Ret(IRArg::Var(VarId(5)))),
        rest: Box::new(simple_ret()),
    };
    let decl = mk_decl("f", vec![(VarId(0), IRType::Object)], body);
    let du = def_use_chain(&decl);
    assert_eq!(
        du.defs.get(&VarId(5)),
        Some(&DefSite::JDeclParam { jp: JoinPointId(0) })
    );
    assert_eq!(du.uses.get(&VarId(5)), Some(&1));
}

#[test]
fn test_dead_vars_none() {
    let body = IRBody::Ret(IRArg::Var(VarId(0)));
    let decl = mk_decl("f", vec![(VarId(0), IRType::Object)], body);
    let du = def_use_chain(&decl);
    assert!(dead_vars(&du).is_empty());
}

#[test]
fn test_dead_vars_found() {
    let body = mk_lit_vdecl(1, simple_ret()); // v1 defined but unused (ret uses v0)
    let decl = mk_decl("f", vec![(VarId(0), IRType::Object)], body);
    let du = def_use_chain(&decl);
    let d = dead_vars(&du);
    assert!(d.contains(&VarId(1)));
}

#[test]
fn test_def_use_inc_dec_counted() {
    let body = mk_inc(0, mk_dec(0, simple_ret()));
    let decl = mk_decl("f", vec![(VarId(0), IRType::Object)], body);
    let du = def_use_chain(&decl);
    // inc + dec + ret all use v0
    assert_eq!(du.uses.get(&VarId(0)), Some(&3));
}

#[test]
fn test_def_use_set_uses_both_vars() {
    let body = IRBody::Set {
        var: VarId(0),
        idx: 0,
        value: VarId(1),
        rest: Box::new(simple_ret()),
    };
    let decl = mk_decl(
        "f",
        vec![(VarId(0), IRType::Object), (VarId(1), IRType::Object)],
        body,
    );
    let du = def_use_chain(&decl);
    assert!(du.uses.get(&VarId(0)).unwrap_or(&0) >= &1);
    assert!(du.uses.get(&VarId(1)).unwrap_or(&0) >= &1);
}

// ── Structural comparison tests ───────────────────────────────────────────

#[test]
fn test_structural_equal_identical() {
    let a = mk_lit_vdecl(0, simple_ret());
    assert!(structurally_equal(&a, &a));
}

#[test]
fn test_structural_equal_renamed() {
    let a = mk_lit_vdecl(0, IRBody::Ret(IRArg::Var(VarId(0))));
    let b = mk_lit_vdecl(99, IRBody::Ret(IRArg::Var(VarId(99))));
    assert!(structurally_equal(&a, &b));
}

#[test]
fn test_structural_not_equal_diff_shape() {
    let a = mk_lit_vdecl(0, simple_ret());
    let b = simple_ret();
    assert!(!structurally_equal(&a, &b));
}

#[test]
fn test_structural_not_equal_diff_type() {
    let a = IRBody::VDecl {
        var: VarId(0),
        ty: IRType::UInt64,
        value: IRExpr::Lit(IRLiteral::UInt64(42)),
        rest: Box::new(simple_ret()),
    };
    let b = IRBody::VDecl {
        var: VarId(0),
        ty: IRType::UInt32,
        value: IRExpr::Lit(IRLiteral::UInt64(42)),
        rest: Box::new(simple_ret()),
    };
    assert!(!structurally_equal(&a, &b));
}

#[test]
fn test_structural_equal_case() {
    let mk = |v: u32| {
        mk_case(
            v,
            vec![IRAlt {
                ctor: mk_ctor_info("A", 0),
                body: Box::new(IRBody::Ret(IRArg::Var(VarId(v)))),
            }],
            None,
        )
    };
    assert!(structurally_equal(&mk(0), &mk(99)));
}

#[test]
fn test_structural_equal_unreachable() {
    assert!(structurally_equal(
        &IRBody::Unreachable,
        &IRBody::Unreachable
    ));
}

#[test]
fn test_structural_not_equal_unreachable_vs_ret() {
    assert!(!structurally_equal(&IRBody::Unreachable, &simple_ret()));
}

#[test]
fn test_structural_equal_inc() {
    // VDecl + Inc chain with renamed variables should still match.
    let a = IRBody::VDecl {
        var: VarId(0),
        ty: IRType::Object,
        value: IRExpr::Lit(IRLiteral::UInt64(1)),
        rest: Box::new(mk_inc(0, IRBody::Ret(IRArg::Var(VarId(0))))),
    };
    let b = IRBody::VDecl {
        var: VarId(5),
        ty: IRType::Object,
        value: IRExpr::Lit(IRLiteral::UInt64(1)),
        rest: Box::new(mk_inc(5, IRBody::Ret(IRArg::Var(VarId(5))))),
    };
    assert!(structurally_equal(&a, &b));
}

// ── Validation tests ──────────────────────────────────────────────────────

#[test]
fn test_validate_well_formed() {
    let body = mk_lit_vdecl(1, IRBody::Ret(IRArg::Var(VarId(1))));
    let decl = mk_decl("f", vec![(VarId(0), IRType::Object)], body);
    validate_decl(&decl).expect("should be well-formed");
}

#[test]
fn test_validate_undefined_var() {
    let body = IRBody::Ret(IRArg::Var(VarId(99)));
    let decl = mk_decl("f", vec![(VarId(0), IRType::Object)], body);
    let errs = validate_decl(&decl).unwrap_err();
    assert!(errs
        .iter()
        .any(|e| matches!(e, IrValidationError::UndefinedVar(VarId(99)))));
}

#[test]
fn test_validate_duplicate_def() {
    // Define v0 as param AND as vdecl.
    let body = mk_lit_vdecl(0, simple_ret());
    let decl = mk_decl("f", vec![(VarId(0), IRType::Object)], body);
    let errs = validate_decl(&decl).unwrap_err();
    assert!(errs
        .iter()
        .any(|e| matches!(e, IrValidationError::DuplicateDef(VarId(0)))));
}

#[test]
fn test_validate_undefined_jp() {
    let body = IRBody::Jmp {
        jp: JoinPointId(7),
        args: vec![],
    };
    let decl = mk_decl("f", vec![(VarId(0), IRType::Object)], body);
    let errs = validate_decl(&decl).unwrap_err();
    assert!(errs
        .iter()
        .any(|e| matches!(e, IrValidationError::UndefinedJoinPoint(JoinPointId(7)))));
}

#[test]
fn test_validate_jp_arity_mismatch() {
    let body = IRBody::JDecl {
        jp: JoinPointId(0),
        params: vec![(VarId(5), IRType::Object)],
        body: Box::new(simple_ret()),
        rest: Box::new(IRBody::Jmp {
            jp: JoinPointId(0),
            args: vec![],
        }), // expects 1 arg
    };
    let decl = mk_decl("f", vec![(VarId(0), IRType::Object)], body);
    let errs = validate_decl(&decl).unwrap_err();
    assert!(errs.iter().any(|e| matches!(
        e,
        IrValidationError::JoinPointArityMismatch {
            jp: JoinPointId(0),
            expected: 1,
            actual: 0
        }
    )));
}

#[test]
fn test_validate_jp_correct_arity() {
    let body = IRBody::JDecl {
        jp: JoinPointId(0),
        params: vec![(VarId(5), IRType::Object)],
        body: Box::new(simple_ret()),
        rest: Box::new(IRBody::Jmp {
            jp: JoinPointId(0),
            args: vec![IRArg::Var(VarId(0))],
        }),
    };
    let decl = mk_decl("f", vec![(VarId(0), IRType::Object)], body);
    validate_decl(&decl).expect("well-formed with correct arity");
}

#[test]
fn test_validate_erased_ret_ok() {
    let body = IRBody::Ret(IRArg::Erased);
    let decl = mk_decl("f", vec![], body);
    validate_decl(&decl).expect("erased ret should be valid");
}

#[test]
fn test_validate_duplicate_jp() {
    let body = IRBody::JDecl {
        jp: JoinPointId(0),
        params: vec![],
        body: Box::new(simple_ret()),
        rest: Box::new(IRBody::JDecl {
            jp: JoinPointId(0),
            params: vec![],
            body: Box::new(simple_ret()),
            rest: Box::new(simple_ret()),
        }),
    };
    let decl = mk_decl("f", vec![(VarId(0), IRType::Object)], body);
    let errs = validate_decl(&decl).unwrap_err();
    assert!(errs
        .iter()
        .any(|e| matches!(e, IrValidationError::DuplicateJoinPoint(JoinPointId(0)))));
}

// ── Call site extraction tests ────────────────────────────────────────────

#[test]
fn test_extract_call_sites_empty() {
    assert!(extract_call_sites(&simple_ret()).is_empty());
}

#[test]
fn test_extract_call_sites_apply() {
    let body = IRBody::VDecl {
        var: VarId(1),
        ty: IRType::Object,
        value: mk_apply("Nat.add", vec![IRArg::Var(VarId(0)), IRArg::Var(VarId(0))]),
        rest: Box::new(simple_ret()),
    };
    let sites = extract_call_sites(&body);
    assert_eq!(sites.len(), 1);
    assert_eq!(sites[0].fn_id.0.to_string(), "Nat.add");
    assert_eq!(sites[0].num_args, 2);
    assert!(!sites[0].is_partial);
}

#[test]
fn test_extract_call_sites_partial() {
    let body = IRBody::VDecl {
        var: VarId(1),
        ty: IRType::Object,
        value: IRExpr::PartialApply {
            fn_id: mk_fn_id("f"),
            arity: 3,
            args: vec![IRArg::Var(VarId(0))],
        },
        rest: Box::new(simple_ret()),
    };
    let sites = extract_call_sites(&body);
    assert_eq!(sites.len(), 1);
    assert!(sites[0].is_partial);
    assert_eq!(sites[0].num_args, 1);
}

#[test]
fn test_extract_call_sites_in_case_alt() {
    let body = mk_case(
        0,
        vec![IRAlt {
            ctor: mk_ctor_info("A", 0),
            body: Box::new(IRBody::VDecl {
                var: VarId(1),
                ty: IRType::Object,
                value: mk_apply("g", vec![]),
                rest: Box::new(simple_ret()),
            }),
        }],
        None,
    );
    let sites = extract_call_sites(&body);
    assert_eq!(sites.len(), 1);
}

// ── Case scrutinee extraction tests ───────────────────────────────────────

#[test]
fn test_extract_scrutinees_empty() {
    assert!(extract_case_scrutinees(&simple_ret()).is_empty());
}

#[test]
fn test_extract_scrutinees_nested() {
    let inner = mk_case(
        1,
        vec![IRAlt {
            ctor: mk_ctor_info("B", 0),
            body: Box::new(simple_ret()),
        }],
        None,
    );
    let outer = mk_case(
        0,
        vec![IRAlt {
            ctor: mk_ctor_info("A", 0),
            body: Box::new(inner),
        }],
        None,
    );
    let scruts = extract_case_scrutinees(&outer);
    assert_eq!(scruts, vec![VarId(0), VarId(1)]);
}

// ── Pretty summary tests ──────────────────────────────────────────────────

#[test]
fn test_decl_summary_format() {
    let body = mk_lit_vdecl(1, simple_ret());
    let decl = mk_decl("my_func", vec![(VarId(0), IRType::Object)], body);
    let s = decl_summary(&decl);
    assert_eq!(s.name, "my_func");
    assert_eq!(s.num_params, 1);
    assert_eq!(s.node_counts.vdecl, 1);
    assert_eq!(s.node_counts.ret, 1);
    let display = s.to_string();
    assert!(display.contains("my_func"));
    assert!(display.contains("1 params"));
}

#[test]
fn test_module_pretty_summary() {
    let decl1 = mk_decl("a", vec![], simple_ret());
    let decl2 = mk_decl(
        "b",
        vec![(VarId(0), IRType::UInt64)],
        mk_lit_vdecl(1, simple_ret()),
    );
    let out = module_pretty_summary(&[decl1, decl2]);
    assert!(out.contains("2 declaration(s)"));
    assert!(out.contains("fn a"));
    assert!(out.contains("fn b"));
}

#[test]
fn test_module_pretty_summary_empty() {
    let out = module_pretty_summary(&[]);
    assert!(out.contains("0 declaration(s)"));
}
