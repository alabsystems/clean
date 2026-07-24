// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the base local dead code elimination pass (`dce_local`).
//!
//! Pins the current behavior of `eliminate_dead_locals` (fixpoint VDecl/JDecl
//! removal with correct `removed` accounting, including `count_vdecls` when a
//! whole dead join point is dropped) and the `collect_used` /
//! `collect_used_expr` use-set walkers per variant.
//!
//! Part of #3084 - IO/FFI/Native epic.

use crate::dce_local::{collect_used, collect_used_expr, eliminate_dead_locals};
use crate::ir::{
    CtorInfo, FnId, IRAlt, IRArg, IRBody, IRExpr, IRLiteral, IRType, JoinPointId, VarId,
};
use clean_kernel::Name;
use std::collections::HashSet;

// -----------------------------------------------------------------------
// Test helpers
// -----------------------------------------------------------------------

fn var(n: u32) -> VarId {
    VarId(n)
}

fn jp(n: u32) -> JoinPointId {
    JoinPointId(n)
}

fn var_arg(n: u32) -> IRArg {
    IRArg::Var(VarId(n))
}

fn ret_var(n: u32) -> IRBody {
    IRBody::Ret(IRArg::Var(VarId(n)))
}

fn lit_u64(val: u64) -> IRExpr {
    IRExpr::Lit(IRLiteral::UInt64(val))
}

fn vdecl(v: u32, value: IRExpr, rest: IRBody) -> IRBody {
    IRBody::VDecl {
        var: var(v),
        ty: IRType::UInt64,
        value,
        rest: Box::new(rest),
    }
}

fn jdecl(j: u32, params: Vec<(VarId, IRType)>, body: IRBody, rest: IRBody) -> IRBody {
    IRBody::JDecl {
        jp: jp(j),
        params,
        body: Box::new(body),
        rest: Box::new(rest),
    }
}

fn ctor_info(tag: u32) -> CtorInfo {
    CtorInfo {
        name: Name::from_string(&format!("Ctor{}", tag)),
        tag,
        num_scalars: 0,
        num_objects: 0,
        field_types: vec![],
    }
}

fn alt(tag: u32, body: IRBody) -> IRAlt {
    IRAlt {
        ctor: ctor_info(tag),
        body: Box::new(body),
    }
}

// Convenience: collect just the used VarId set from a body.
fn used_vars(body: &IRBody) -> HashSet<VarId> {
    let mut vars = HashSet::new();
    let mut jps = HashSet::new();
    collect_used(body, &mut vars, &mut jps);
    vars
}

// Convenience: collect just the used JoinPointId set from a body.
fn used_jps(body: &IRBody) -> HashSet<JoinPointId> {
    let mut vars = HashSet::new();
    let mut jps = HashSet::new();
    collect_used(body, &mut vars, &mut jps);
    jps
}

// Convenience: collect the used VarId set from a single expression.
fn used_vars_expr(expr: &IRExpr) -> HashSet<VarId> {
    let mut vars = HashSet::new();
    collect_used_expr(expr, &mut vars);
    vars
}

// -----------------------------------------------------------------------
// eliminate_dead_locals: dead VDecl removal
// -----------------------------------------------------------------------

#[test]
fn test_eliminate_dead_vdecl_removed() {
    // let v1 = 42; ret v0  =>  ret v0  (v1 dead)
    let body = vdecl(1, lit_u64(42), ret_var(0));
    let (result, removed) = eliminate_dead_locals(&body);
    assert_eq!(removed, 1);
    assert_eq!(result, ret_var(0));
}

#[test]
fn test_eliminate_live_vdecl_preserved() {
    // let v1 = 42; ret v1  =>  unchanged (v1 live)
    let body = vdecl(1, lit_u64(42), ret_var(1));
    let (result, removed) = eliminate_dead_locals(&body);
    assert_eq!(removed, 0);
    assert_eq!(result, body);
}

#[test]
fn test_eliminate_chain_of_dead_vdecls() {
    // let v1=1; let v2=2; let v3=3; ret v0  =>  ret v0  (all dead)
    let body = vdecl(
        1,
        lit_u64(1),
        vdecl(2, lit_u64(2), vdecl(3, lit_u64(3), ret_var(0))),
    );
    let (result, removed) = eliminate_dead_locals(&body);
    assert_eq!(removed, 3);
    assert_eq!(result, ret_var(0));
}

#[test]
fn test_eliminate_mixed_live_and_dead_vdecls() {
    // let v1=42; let v2=99; ret v1  =>  let v1=42; ret v1  (v2 dead)
    let body = vdecl(1, lit_u64(42), vdecl(2, lit_u64(99), ret_var(1)));
    let (result, removed) = eliminate_dead_locals(&body);
    assert_eq!(removed, 1);
    assert_eq!(result, vdecl(1, lit_u64(42), ret_var(1)));
}

#[test]
fn test_eliminate_fixpoint_cascading_dead_vdecls() {
    // let v1 = proj v2; let v2 = 42; ret v0
    // Pass 1 removes dead v1; pass 2 then sees v2 unused and removes it.
    let body = vdecl(
        1,
        IRExpr::Proj {
            idx: 0,
            ty: IRType::UInt64,
            arg: var_arg(2),
        },
        vdecl(2, lit_u64(42), ret_var(0)),
    );
    let (result, removed) = eliminate_dead_locals(&body);
    assert_eq!(removed, 2);
    assert_eq!(result, ret_var(0));
}

// -----------------------------------------------------------------------
// eliminate_dead_locals: dead JDecl drop + count_vdecls accounting
// -----------------------------------------------------------------------

#[test]
fn test_eliminate_dead_jdecl_counts_inner_vdecls() {
    // jdecl j0 [] { let v5=1; let v6=2; ret v9 }; ret v1
    // j0 is never jumped to => dropped. The two VDecls inside its body are
    // accounted for via count_vdecls, so removed == 2.
    let jp_body = vdecl(5, lit_u64(1), vdecl(6, lit_u64(2), ret_var(9)));
    let body = jdecl(0, vec![], jp_body, ret_var(1));
    let (result, removed) = eliminate_dead_locals(&body);
    assert_eq!(removed, 2);
    assert_eq!(result, ret_var(1));
}

#[test]
fn test_eliminate_dead_jdecl_empty_body_counts_zero() {
    // jdecl j0 [] { ret v9 }; ret v1  =>  ret v1, removed == 0
    // Dropped join point body has no VDecls.
    let body = jdecl(0, vec![], ret_var(9), ret_var(1));
    let (result, removed) = eliminate_dead_locals(&body);
    assert_eq!(removed, 0);
    assert_eq!(result, ret_var(1));
}

#[test]
fn test_eliminate_live_jdecl_kept_body_cleaned() {
    // jdecl j0 [] { let v5=1; ret v2 }; jmp j0 []
    // j0 is jumped to => kept; the dead v5 inside the body is removed.
    let jp_body = vdecl(5, lit_u64(1), ret_var(2));
    let body = jdecl(
        0,
        vec![],
        jp_body,
        IRBody::Jmp {
            jp: jp(0),
            args: vec![],
        },
    );
    let (result, removed) = eliminate_dead_locals(&body);
    assert_eq!(removed, 1);
    let expected = jdecl(
        0,
        vec![],
        ret_var(2),
        IRBody::Jmp {
            jp: jp(0),
            args: vec![],
        },
    );
    assert_eq!(result, expected);
}

#[test]
fn test_eliminate_terminal_bodies_unchanged() {
    // Ret / Jmp / Unreachable have no VDecls to remove.
    for body in [
        ret_var(0),
        IRBody::Jmp {
            jp: jp(0),
            args: vec![var_arg(1)],
        },
        IRBody::Unreachable,
    ] {
        let (result, removed) = eliminate_dead_locals(&body);
        assert_eq!(removed, 0);
        assert_eq!(result, body);
    }
}

#[test]
fn test_eliminate_dead_vdecl_inside_case_alt() {
    // case v0 { Ctor0 => let v1=1; ret v2 }
    // v1 is dead inside the alt body => removed == 1, structure preserved.
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![alt(0, vdecl(1, lit_u64(1), ret_var(2)))],
        default: None,
    };
    let (result, removed) = eliminate_dead_locals(&body);
    assert_eq!(removed, 1);
    let expected = IRBody::Case {
        scrutinee: var(0),
        alts: vec![alt(0, ret_var(2))],
        default: None,
    };
    assert_eq!(result, expected);
}

// -----------------------------------------------------------------------
// collect_used: per-IRBody-variant use sets
// -----------------------------------------------------------------------

#[test]
fn test_collect_used_ret_var() {
    assert_eq!(used_vars(&ret_var(7)), HashSet::from([var(7)]));
}

#[test]
fn test_collect_used_ret_erased_empty() {
    let body = IRBody::Ret(IRArg::Erased);
    assert!(used_vars(&body).is_empty());
}

#[test]
fn test_collect_used_unreachable_empty() {
    assert!(used_vars(&IRBody::Unreachable).is_empty());
    assert!(used_jps(&IRBody::Unreachable).is_empty());
}

#[test]
fn test_collect_used_jmp_adds_jp_and_args() {
    // jmp j3 [v0, v1]  =>  vars {v0, v1}, jps {j3}
    let body = IRBody::Jmp {
        jp: jp(3),
        args: vec![var_arg(0), var_arg(1)],
    };
    assert_eq!(used_vars(&body), HashSet::from([var(0), var(1)]));
    assert_eq!(used_jps(&body), HashSet::from([jp(3)]));
}

#[test]
fn test_collect_used_inc_dec_add_var() {
    let inc = IRBody::Inc {
        var: var(4),
        n: 1,
        rest: Box::new(IRBody::Unreachable),
    };
    assert_eq!(used_vars(&inc), HashSet::from([var(4)]));

    let dec = IRBody::Dec {
        var: var(5),
        rest: Box::new(IRBody::Unreachable),
    };
    assert_eq!(used_vars(&dec), HashSet::from([var(5)]));
}

#[test]
fn test_collect_used_set_adds_var_and_value() {
    // set v0[0] := v1; unreachable  =>  {v0, v1}
    let body = IRBody::Set {
        var: var(0),
        idx: 0,
        value: var(1),
        rest: Box::new(IRBody::Unreachable),
    };
    assert_eq!(used_vars(&body), HashSet::from([var(0), var(1)]));
}

#[test]
fn test_collect_used_uset_adds_var_and_value() {
    let body = IRBody::USet {
        var: var(0),
        idx: 0,
        value: var(1),
        rest: Box::new(IRBody::Unreachable),
    };
    assert_eq!(used_vars(&body), HashSet::from([var(0), var(1)]));
}

#[test]
fn test_collect_used_sset_adds_var_and_value() {
    let body = IRBody::SSet {
        var: var(0),
        n: 0,
        offset: 0,
        value: var(1),
        ty: IRType::UInt64,
        rest: Box::new(IRBody::Unreachable),
    };
    assert_eq!(used_vars(&body), HashSet::from([var(0), var(1)]));
}

#[test]
fn test_collect_used_settag_adds_only_var() {
    // setTag v0 := 1; unreachable  =>  {v0} (no value operand)
    let body = IRBody::SetTag {
        var: var(0),
        tag: 1,
        rest: Box::new(IRBody::Unreachable),
    };
    assert_eq!(used_vars(&body), HashSet::from([var(0)]));
}

#[test]
fn test_collect_used_case_scrutinee_alts_default() {
    // case v0 { Ctor0 => ret v1 } default => ret v2  =>  {v0, v1, v2}
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![alt(0, ret_var(1))],
        default: Some(Box::new(ret_var(2))),
    };
    assert_eq!(used_vars(&body), HashSet::from([var(0), var(1), var(2)]));
}

#[test]
fn test_collect_used_vdecl_def_var_not_counted() {
    // let v1 = v0...; ret v0  =>  the *defined* v1 is never in the use set.
    let body = vdecl(1, lit_u64(0), ret_var(0));
    let vars = used_vars(&body);
    assert!(vars.contains(&var(0)));
    assert!(!vars.contains(&var(1)));
}

#[test]
fn test_collect_used_jdecl_recurses_body_and_rest() {
    // jdecl j0 [] { ret v5 }; jmp j0 [v6]  =>  vars {v5, v6}, jps {j0}
    let body = jdecl(
        0,
        vec![],
        ret_var(5),
        IRBody::Jmp {
            jp: jp(0),
            args: vec![var_arg(6)],
        },
    );
    assert_eq!(used_vars(&body), HashSet::from([var(5), var(6)]));
    assert_eq!(used_jps(&body), HashSet::from([jp(0)]));
}

// -----------------------------------------------------------------------
// collect_used_expr: per-IRExpr-variant use sets
// -----------------------------------------------------------------------

#[test]
fn test_collect_used_expr_lit_and_string_empty() {
    assert!(used_vars_expr(&lit_u64(7)).is_empty());
    assert!(used_vars_expr(&IRExpr::String("x".to_string())).is_empty());
}

#[test]
fn test_collect_used_expr_ctor_all_args() {
    let expr = IRExpr::Ctor {
        info: ctor_info(0),
        args: vec![var_arg(0), var_arg(1), IRArg::Erased],
    };
    assert_eq!(used_vars_expr(&expr), HashSet::from([var(0), var(1)]));
}

#[test]
fn test_collect_used_expr_proj_arg() {
    let expr = IRExpr::Proj {
        idx: 0,
        ty: IRType::UInt64,
        arg: var_arg(3),
    };
    assert_eq!(used_vars_expr(&expr), HashSet::from([var(3)]));
}

#[test]
fn test_collect_used_expr_apply_args() {
    let expr = IRExpr::Apply {
        fn_id: FnId(Name::from_string("f")),
        args: vec![var_arg(0), var_arg(1)],
    };
    assert_eq!(used_vars_expr(&expr), HashSet::from([var(0), var(1)]));
}

#[test]
fn test_collect_used_expr_closure_apply_closure_and_args() {
    let expr = IRExpr::ClosureApply {
        closure: var_arg(0),
        args: vec![var_arg(1), var_arg(2)],
    };
    assert_eq!(
        used_vars_expr(&expr),
        HashSet::from([var(0), var(1), var(2)])
    );
}

#[test]
fn test_collect_used_expr_reset_var() {
    let expr = IRExpr::Reset(var(4));
    assert_eq!(used_vars_expr(&expr), HashSet::from([var(4)]));
}

#[test]
fn test_collect_used_expr_reuse_var_and_args() {
    // reuse v0 Ctor(v1, v2)  =>  {v0, v1, v2}
    let expr = IRExpr::Reuse {
        var: var(0),
        ctor: ctor_info(0),
        args: vec![var_arg(1), var_arg(2)],
    };
    assert_eq!(
        used_vars_expr(&expr),
        HashSet::from([var(0), var(1), var(2)])
    );
}
