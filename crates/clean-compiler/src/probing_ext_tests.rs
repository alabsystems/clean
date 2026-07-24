// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended IR probing module.

use super::probing_ext::*;
use crate::ir::*;
use clean_kernel::Name;

fn var(n: u32) -> VarId {
    VarId(n)
}
fn arg_var(n: u32) -> IRArg {
    IRArg::Var(VarId(n))
}
fn name(s: &str) -> Name {
    Name::from_string(s)
}
fn fn_id(s: &str) -> FnId {
    FnId(name(s))
}

fn mk_ctor(tag: u32, n_objs: u32) -> CtorInfo {
    CtorInfo {
        name: name("Ctor"),
        tag,
        num_scalars: 0,
        num_objects: n_objs,
        field_types: vec![IRType::Object; n_objs as usize],
    }
}

fn mk_decl(fname: &str, params: Vec<(VarId, IRType)>, ret: IRType, body: IRBody) -> IRDecl {
    IRDecl {
        name: name(fname),
        params,
        return_type: ret,
        body,
    }
}

fn simple_ret(v: u32) -> IRBody {
    IRBody::Ret(arg_var(v))
}

fn vdecl(v: u32, ty: IRType, value: IRExpr, rest: IRBody) -> IRBody {
    IRBody::VDecl {
        var: var(v),
        ty,
        value,
        rest: Box::new(rest),
    }
}

fn inc(v: u32, n: u32, rest: IRBody) -> IRBody {
    IRBody::Inc {
        var: var(v),
        n,
        rest: Box::new(rest),
    }
}

fn dec(v: u32, rest: IRBody) -> IRBody {
    IRBody::Dec {
        var: var(v),
        rest: Box::new(rest),
    }
}

fn case(scrutinee: u32, alts: Vec<IRAlt>, default: Option<IRBody>) -> IRBody {
    IRBody::Case {
        scrutinee: var(scrutinee),
        alts,
        default: default.map(Box::new),
    }
}

fn alt(tag: u32, body: IRBody) -> IRAlt {
    IRAlt {
        ctor: mk_ctor(tag, 0),
        body: Box::new(body),
    }
}

fn apply_expr(target: &str, args: Vec<IRArg>) -> IRExpr {
    IRExpr::Apply {
        fn_id: fn_id(target),
        args,
    }
}

fn partial_apply_expr(target: &str, arity: u16, args: Vec<IRArg>) -> IRExpr {
    IRExpr::PartialApply {
        fn_id: fn_id(target),
        arity,
        args,
    }
}

// ─── find_decl ───

#[test]
fn test_find_decl_found() {
    let decls = vec![
        mk_decl("foo", vec![], IRType::Object, simple_ret(0)),
        mk_decl("bar", vec![], IRType::Object, simple_ret(0)),
    ];
    let d = find_decl(&decls, "bar");
    assert!(d.is_some());
    assert_eq!(d.unwrap().name.to_string(), "bar");
}

#[test]
fn test_find_decl_not_found() {
    let decls = vec![mk_decl("foo", vec![], IRType::Object, simple_ret(0))];
    assert!(find_decl(&decls, "baz").is_none());
}

#[test]
fn test_find_decl_empty() {
    assert!(find_decl(&[], "any").is_none());
}

// ─── body_size ───

#[test]
fn test_body_size_ret() {
    assert_eq!(body_size(&simple_ret(0)), 1);
}

#[test]
fn test_body_size_unreachable() {
    assert_eq!(body_size(&IRBody::Unreachable), 1);
}

#[test]
fn test_body_size_jmp() {
    let body = IRBody::Jmp {
        jp: JoinPointId(0),
        args: vec![],
    };
    assert_eq!(body_size(&body), 1);
}

#[test]
fn test_body_size_vdecl_chain() {
    let body = vdecl(
        1,
        IRType::Object,
        IRExpr::Lit(IRLiteral::UInt64(42)),
        vdecl(
            2,
            IRType::Object,
            IRExpr::Lit(IRLiteral::UInt64(43)),
            simple_ret(2),
        ),
    );
    assert_eq!(body_size(&body), 3);
}

#[test]
fn test_body_size_inc_dec() {
    let body = inc(0, 1, dec(0, simple_ret(0)));
    assert_eq!(body_size(&body), 3);
}

#[test]
fn test_body_size_case_no_default() {
    let body = case(0, vec![alt(0, simple_ret(0)), alt(1, simple_ret(1))], None);
    assert_eq!(body_size(&body), 3); // 1 case + 2 rets
}

#[test]
fn test_body_size_case_with_default() {
    let body = case(0, vec![alt(0, simple_ret(0))], Some(simple_ret(1)));
    assert_eq!(body_size(&body), 3); // 1 case + 1 alt ret + 1 default ret
}

#[test]
fn test_body_size_jdecl() {
    let body = IRBody::JDecl {
        jp: JoinPointId(0),
        params: vec![],
        body: Box::new(simple_ret(0)),
        rest: Box::new(simple_ret(1)),
    };
    assert_eq!(body_size(&body), 3); // 1 jdecl + 1 jp body + 1 rest
}

// ─── var_usage_counts ───

#[test]
fn test_var_usage_ret() {
    let counts = var_usage_counts(&simple_ret(5));
    assert_eq!(counts.get(&var(5)), Some(&1));
}

#[test]
fn test_var_usage_ret_erased() {
    let body = IRBody::Ret(IRArg::Erased);
    let counts = var_usage_counts(&body);
    assert!(counts.is_empty());
}

#[test]
fn test_var_usage_inc_dec() {
    let body = inc(3, 1, dec(3, simple_ret(3)));
    let counts = var_usage_counts(&body);
    assert_eq!(counts.get(&var(3)), Some(&3)); // inc + dec + ret
}

#[test]
fn test_var_usage_apply() {
    let body = vdecl(
        1,
        IRType::Object,
        apply_expr("f", vec![arg_var(0), arg_var(0)]),
        simple_ret(1),
    );
    let counts = var_usage_counts(&body);
    assert_eq!(counts.get(&var(0)), Some(&2));
    assert_eq!(counts.get(&var(1)), Some(&1));
}

#[test]
fn test_var_usage_case_scrutinee() {
    let body = case(7, vec![alt(0, simple_ret(0))], None);
    let counts = var_usage_counts(&body);
    assert_eq!(counts.get(&var(7)), Some(&1));
}

#[test]
fn test_var_usage_set() {
    let body = IRBody::Set {
        var: var(1),
        idx: 0,
        value: var(2),
        rest: Box::new(simple_ret(0)),
    };
    let counts = var_usage_counts(&body);
    assert_eq!(counts.get(&var(1)), Some(&1));
    assert_eq!(counts.get(&var(2)), Some(&1));
}

#[test]
fn test_var_usage_sproj() {
    let body = vdecl(
        1,
        IRType::UInt64,
        IRExpr::SProj {
            n: 0,
            offset: 0,
            var: var(0),
            ty: IRType::UInt64,
        },
        simple_ret(1),
    );
    let counts = var_usage_counts(&body);
    assert_eq!(counts.get(&var(0)), Some(&1));
}

#[test]
fn test_var_usage_closure_apply() {
    let body = vdecl(
        2,
        IRType::Object,
        IRExpr::ClosureApply {
            closure: arg_var(0),
            args: vec![arg_var(1)],
        },
        simple_ret(2),
    );
    let counts = var_usage_counts(&body);
    assert_eq!(counts.get(&var(0)), Some(&1));
    assert_eq!(counts.get(&var(1)), Some(&1));
}

// ─── call_graph ───

#[test]
fn test_call_graph_simple() {
    let decls = vec![
        mk_decl(
            "main",
            vec![],
            IRType::Object,
            vdecl(
                1,
                IRType::Object,
                apply_expr("helper", vec![arg_var(0)]),
                simple_ret(1),
            ),
        ),
        mk_decl("helper", vec![], IRType::Object, simple_ret(0)),
    ];
    let graph = call_graph(&decls);
    assert_eq!(graph.get("main").unwrap(), &vec!["helper".to_string()]);
    assert!(graph.get("helper").unwrap().is_empty());
}

#[test]
fn test_call_graph_multiple_callees() {
    let body = vdecl(
        1,
        IRType::Object,
        apply_expr("a", vec![]),
        vdecl(2, IRType::Object, apply_expr("b", vec![]), simple_ret(2)),
    );
    let decls = vec![mk_decl("f", vec![], IRType::Object, body)];
    let graph = call_graph(&decls);
    let callees = graph.get("f").unwrap();
    assert_eq!(callees, &vec!["a".to_string(), "b".to_string()]);
}

#[test]
fn test_call_graph_dedup() {
    let body = vdecl(
        1,
        IRType::Object,
        apply_expr("x", vec![]),
        vdecl(2, IRType::Object, apply_expr("x", vec![]), simple_ret(2)),
    );
    let decls = vec![mk_decl("f", vec![], IRType::Object, body)];
    let graph = call_graph(&decls);
    assert_eq!(graph.get("f").unwrap().len(), 1);
}

#[test]
fn test_call_graph_partial_apply() {
    let body = vdecl(
        1,
        IRType::Object,
        partial_apply_expr("target", 3, vec![arg_var(0)]),
        simple_ret(1),
    );
    let decls = vec![mk_decl("f", vec![], IRType::Object, body)];
    let graph = call_graph(&decls);
    assert_eq!(graph.get("f").unwrap(), &vec!["target".to_string()]);
}

#[test]
fn test_call_graph_empty_module() {
    assert!(call_graph(&[]).is_empty());
}

// ─── closure_captures ───

#[test]
fn test_captures_empty() {
    assert!(closure_captures(&simple_ret(0)).is_empty());
}

#[test]
fn test_captures_partial_apply() {
    let body = vdecl(
        2,
        IRType::Object,
        partial_apply_expr("f", 3, vec![arg_var(0), arg_var(1)]),
        simple_ret(2),
    );
    let caps = closure_captures(&body);
    assert_eq!(caps.len(), 1);
    assert_eq!(caps[0].fn_name, "f");
    assert_eq!(caps[0].captured_vars, vec![var(0), var(1)]);
}

#[test]
fn test_captures_erased_args_filtered() {
    let body = vdecl(
        2,
        IRType::Object,
        partial_apply_expr("g", 3, vec![IRArg::Erased, arg_var(1)]),
        simple_ret(2),
    );
    let caps = closure_captures(&body);
    assert_eq!(caps[0].captured_vars, vec![var(1)]);
}

#[test]
fn test_captures_nested_in_case() {
    let alt_body = vdecl(
        5,
        IRType::Object,
        partial_apply_expr("inner", 2, vec![arg_var(3)]),
        simple_ret(5),
    );
    let body = case(
        0,
        vec![IRAlt {
            ctor: mk_ctor(0, 0),
            body: Box::new(alt_body),
        }],
        None,
    );
    let caps = closure_captures(&body);
    assert_eq!(caps.len(), 1);
    assert_eq!(caps[0].fn_name, "inner");
}

// ─── type_occurrences ───

#[test]
fn test_type_occurrences_vdecl() {
    let body = vdecl(
        1,
        IRType::UInt64,
        IRExpr::Lit(IRLiteral::UInt64(0)),
        simple_ret(1),
    );
    let counts = type_occurrences(&body);
    assert_eq!(counts.get("UInt64"), Some(&1));
}

#[test]
fn test_type_occurrences_proj() {
    let body = vdecl(
        1,
        IRType::Object,
        IRExpr::Proj {
            idx: 0,
            ty: IRType::Bool,
            arg: arg_var(0),
        },
        simple_ret(1),
    );
    let counts = type_occurrences(&body);
    assert_eq!(counts.get("Object"), Some(&1)); // VDecl ty
    assert_eq!(counts.get("Bool"), Some(&1)); // Proj ty
}

#[test]
fn test_type_occurrences_ctor_field_types() {
    let ctor = CtorInfo {
        name: name("Pair"),
        tag: 0,
        num_scalars: 0,
        num_objects: 2,
        field_types: vec![IRType::Object, IRType::UInt32],
    };
    let body = vdecl(
        1,
        IRType::Object,
        IRExpr::Ctor {
            info: ctor,
            args: vec![arg_var(0), arg_var(0)],
        },
        simple_ret(1),
    );
    let counts = type_occurrences(&body);
    assert_eq!(counts.get("Object"), Some(&2)); // VDecl + field
    assert_eq!(counts.get("UInt32"), Some(&1)); // field
}

#[test]
fn test_type_occurrences_empty_ret() {
    let counts = type_occurrences(&simple_ret(0));
    assert!(counts.is_empty());
}

// ─── case_depth ───

#[test]
fn test_case_depth_no_case() {
    assert_eq!(case_depth(&simple_ret(0)), 0);
}

#[test]
fn test_case_depth_one_level() {
    let body = case(0, vec![alt(0, simple_ret(0))], None);
    assert_eq!(case_depth(&body), 1);
}

#[test]
fn test_case_depth_nested() {
    let inner_case = case(1, vec![alt(0, simple_ret(0))], None);
    let body = case(
        0,
        vec![IRAlt {
            ctor: mk_ctor(0, 0),
            body: Box::new(inner_case),
        }],
        None,
    );
    assert_eq!(case_depth(&body), 2);
}

#[test]
fn test_case_depth_default_branch() {
    let inner = case(1, vec![alt(0, simple_ret(0))], None);
    let body = case(0, vec![alt(0, simple_ret(0))], Some(inner));
    assert_eq!(case_depth(&body), 2);
}

#[test]
fn test_case_depth_vdecl_before_case() {
    let body = vdecl(
        1,
        IRType::Object,
        IRExpr::Lit(IRLiteral::UInt64(0)),
        case(0, vec![alt(0, simple_ret(0))], None),
    );
    assert_eq!(case_depth(&body), 1);
}

// ─── rc_op_counts ───

#[test]
fn test_rc_ops_empty() {
    assert_eq!(rc_op_counts(&simple_ret(0)), RcOpCounts::default());
}

#[test]
fn test_rc_ops_inc_dec() {
    let body = inc(0, 1, dec(0, simple_ret(0)));
    let ops = rc_op_counts(&body);
    assert_eq!(ops.inc, 1);
    assert_eq!(ops.dec, 1);
    assert_eq!(ops.reset, 0);
    assert_eq!(ops.reuse, 0);
}

#[test]
fn test_rc_ops_reset() {
    let body = vdecl(1, IRType::Object, IRExpr::Reset(var(0)), simple_ret(1));
    let ops = rc_op_counts(&body);
    assert_eq!(ops.reset, 1);
}

#[test]
fn test_rc_ops_reuse() {
    let body = vdecl(
        1,
        IRType::Object,
        IRExpr::Reuse {
            var: var(0),
            ctor: mk_ctor(0, 1),
            args: vec![arg_var(0)],
        },
        simple_ret(1),
    );
    let ops = rc_op_counts(&body);
    assert_eq!(ops.reuse, 1);
}

#[test]
fn test_rc_ops_in_case() {
    let alt_body = inc(0, 1, simple_ret(0));
    let body = case(
        0,
        vec![IRAlt {
            ctor: mk_ctor(0, 0),
            body: Box::new(alt_body),
        }],
        None,
    );
    let ops = rc_op_counts(&body);
    assert_eq!(ops.inc, 1);
}

// ─── module_summary ───

#[test]
fn test_module_summary_empty() {
    let s = module_summary(&[]);
    assert_eq!(s.num_decls, 0);
    assert_eq!(s.total_body_size, 0);
    assert_eq!(s.avg_body_size, 0.0);
}

#[test]
fn test_module_summary_single() {
    let decls = vec![mk_decl(
        "f",
        vec![(var(0), IRType::Object)],
        IRType::UInt64,
        simple_ret(0),
    )];
    let s = module_summary(&decls);
    assert_eq!(s.num_decls, 1);
    assert_eq!(s.total_body_size, 1);
    assert_eq!(s.total_params, 1);
    assert_eq!(s.avg_body_size, 1.0);
    assert!(s.type_counts.get("Object").unwrap_or(&0) > &0);
    assert!(s.type_counts.get("UInt64").unwrap_or(&0) > &0);
}

#[test]
fn test_module_summary_rc_aggregation() {
    let d1 = mk_decl("a", vec![], IRType::Object, inc(0, 1, simple_ret(0)));
    let d2 = mk_decl("b", vec![], IRType::Object, dec(0, simple_ret(0)));
    let s = module_summary(&[d1, d2]);
    assert_eq!(s.rc_ops.inc, 1);
    assert_eq!(s.rc_ops.dec, 1);
}

#[test]
fn test_module_summary_avg() {
    let d1 = mk_decl("a", vec![], IRType::Object, simple_ret(0));
    let d2 = mk_decl(
        "b",
        vec![],
        IRType::Object,
        vdecl(
            1,
            IRType::Object,
            IRExpr::Lit(IRLiteral::UInt64(0)),
            vdecl(
                2,
                IRType::Object,
                IRExpr::Lit(IRLiteral::UInt64(1)),
                simple_ret(2),
            ),
        ),
    );
    let s = module_summary(&[d1, d2]);
    assert_eq!(s.num_decls, 2);
    assert_eq!(s.total_body_size, 4); // 1 + 3
    assert_eq!(s.avg_body_size, 2.0);
}

// ─── query_callers ───

#[test]
fn test_query_callers_found() {
    let decls = vec![
        mk_decl(
            "main",
            vec![],
            IRType::Object,
            vdecl(
                1,
                IRType::Object,
                apply_expr("helper", vec![]),
                simple_ret(1),
            ),
        ),
        mk_decl("helper", vec![], IRType::Object, simple_ret(0)),
        mk_decl(
            "other",
            vec![],
            IRType::Object,
            vdecl(
                1,
                IRType::Object,
                apply_expr("helper", vec![]),
                simple_ret(1),
            ),
        ),
    ];
    let callers = query_callers(&decls, "helper");
    assert_eq!(callers, vec!["main".to_string(), "other".to_string()]);
}

#[test]
fn test_query_callers_none() {
    let decls = vec![mk_decl("f", vec![], IRType::Object, simple_ret(0))];
    assert!(query_callers(&decls, "nonexistent").is_empty());
}

#[test]
fn test_query_callers_self_call() {
    let decls = vec![mk_decl(
        "rec",
        vec![],
        IRType::Object,
        vdecl(1, IRType::Object, apply_expr("rec", vec![]), simple_ret(1)),
    )];
    assert_eq!(query_callers(&decls, "rec"), vec!["rec".to_string()]);
}

#[test]
fn test_query_callers_empty_module() {
    assert!(query_callers(&[], "any").is_empty());
}
