// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for LCNF extended analysis (lcnf_ext): statistics, depth, size,
//! free variables, summary, and complexity.

use crate::lcnf::{Alt, Arg, Code, Decl, ExternEntry, FunDecl, LetDecl, LetValue, Param};
use crate::lcnf_ext::*;
use clean_kernel::{Expr, FVarId, Name};

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn nat_ty() -> Expr {
    Expr::const_str("Nat")
}

/// Helper: `let _xN := 42; return _xN`
fn simple_let(id: u64) -> Code {
    Code::let_bind(
        LetDecl::new(fvar(id), name("v"), nat_ty(), LetValue::nat(42)),
        Code::ret(fvar(id)),
    )
}

// ════════════════════════════════════════════════════════════════════════════
// Statistics
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_stats_simple_return() {
    let stats = code_stats(&Code::ret(fvar(0)));
    assert_eq!(stats.returns, 1);
    assert_eq!(stats.total_nodes(), 1);
}

#[test]
fn test_stats_let_chain() {
    let code = Code::let_bind(
        LetDecl::new(fvar(0), name("a"), nat_ty(), LetValue::nat(1)),
        Code::let_bind(
            LetDecl::new(fvar(1), name("b"), nat_ty(), LetValue::nat(2)),
            Code::ret(fvar(1)),
        ),
    );
    let stats = code_stats(&code);
    assert_eq!(stats.let_bindings, 2);
    assert_eq!(stats.returns, 1);
    assert_eq!(stats.total_nodes(), 3);
}

#[test]
fn test_stats_cases() {
    let code = Code::cases(
        name("Bool"),
        nat_ty(),
        fvar(0),
        vec![
            Alt::ctor(name("Bool.true"), vec![], Code::ret(fvar(1))),
            Alt::ctor(name("Bool.false"), vec![], Code::ret(fvar(2))),
        ],
    );
    let stats = code_stats(&code);
    assert_eq!(stats.cases, 1);
    assert_eq!(stats.alts, 2);
    assert_eq!(stats.returns, 2);
}

#[test]
fn test_stats_join_point() {
    let jp = FunDecl::new(
        fvar(10),
        name("jp"),
        vec![Param::new(fvar(11), name("r"), nat_ty())],
        nat_ty(),
        Code::ret(fvar(11)),
    );
    let code = Code::join_point(jp, Code::jmp(fvar(10), vec![Arg::FVar(fvar(0))]));
    let stats = code_stats(&code);
    assert_eq!(stats.join_points, 1);
    assert_eq!(stats.jmps, 1);
    assert_eq!(stats.returns, 1);
}

#[test]
fn test_stats_fun_decl() {
    let fun = FunDecl::new(fvar(5), name("f"), vec![], nat_ty(), Code::ret(fvar(0)));
    let code = Code::fun(fun, Code::ret(fvar(5)));
    let stats = code_stats(&code);
    assert_eq!(stats.fun_decls, 1);
    assert_eq!(stats.returns, 2);
}

#[test]
fn test_stats_unreachable() {
    let stats = code_stats(&Code::Unreachable(nat_ty()));
    assert_eq!(stats.unreachables, 1);
    assert_eq!(stats.total_nodes(), 1);
}

// ════════════════════════════════════════════════════════════════════════════
// Depth and size
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_depth_terminal() {
    assert_eq!(code_depth(&Code::ret(fvar(0))), 1);
    assert_eq!(code_depth(&Code::Unreachable(nat_ty())), 1);
}

#[test]
fn test_depth_nested_lets() {
    let code = Code::let_bind(
        LetDecl::new(fvar(0), name("a"), nat_ty(), LetValue::nat(1)),
        Code::let_bind(
            LetDecl::new(fvar(1), name("b"), nat_ty(), LetValue::nat(2)),
            Code::ret(fvar(1)),
        ),
    );
    assert_eq!(code_depth(&code), 3);
}

#[test]
fn test_depth_cases_max_branch() {
    let code = Code::cases(
        name("Bool"),
        nat_ty(),
        fvar(0),
        vec![
            Alt::ctor(name("Bool.true"), vec![], Code::ret(fvar(1))),
            Alt::ctor(
                name("Bool.false"),
                vec![],
                Code::let_bind(
                    LetDecl::new(fvar(2), name("x"), nat_ty(), LetValue::nat(0)),
                    Code::ret(fvar(2)),
                ),
            ),
        ],
    );
    assert_eq!(code_depth(&code), 3);
}

#[test]
fn test_size_composite() {
    assert_eq!(code_size(&simple_let(0)), 2);
}

#[test]
fn test_size_fun_body_counted() {
    let fun = FunDecl::new(fvar(5), name("f"), vec![], nat_ty(), Code::ret(fvar(0)));
    let code = Code::fun(fun, Code::ret(fvar(5)));
    assert_eq!(code_size(&code), 3);
}

// ════════════════════════════════════════════════════════════════════════════
// Free variables
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_free_vars_return_free() {
    let fv = free_vars(&Code::ret(fvar(99)));
    assert!(fv.contains(&fvar(99)));
    assert_eq!(fv.len(), 1);
}

#[test]
fn test_free_vars_let_binds() {
    let fv = free_vars(&simple_let(0));
    assert!(fv.is_empty());
}

#[test]
fn test_free_vars_let_value_references_free() {
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("r"),
            nat_ty(),
            LetValue::Const {
                name: name("Nat.add"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(0)), Arg::FVar(fvar(0))],
            },
        ),
        Code::ret(fvar(1)),
    );
    let fv = free_vars(&code);
    assert_eq!(fv.len(), 1);
    assert!(fv.contains(&fvar(0)));
}

#[test]
fn test_free_vars_cases_scrutinee() {
    let code = Code::cases(
        name("Bool"),
        nat_ty(),
        fvar(7),
        vec![Alt::default(Code::ret(fvar(7)))],
    );
    let fv = free_vars(&code);
    assert!(fv.contains(&fvar(7)));
}

#[test]
fn test_free_vars_case_ctor_params_bound() {
    let code = Code::cases(
        name("List"),
        nat_ty(),
        fvar(0),
        vec![Alt::ctor(
            name("List.cons"),
            vec![
                Param::new(fvar(1), name("hd"), nat_ty()),
                Param::new(fvar(2), name("tl"), nat_ty()),
            ],
            Code::ret(fvar(1)),
        )],
    );
    let fv = free_vars(&code);
    assert!(fv.contains(&fvar(0)));
    assert!(!fv.contains(&fvar(1)));
    assert!(!fv.contains(&fvar(2)));
}

#[test]
fn test_free_vars_jmp_jp_free() {
    let fv = free_vars(&Code::jmp(fvar(10), vec![Arg::FVar(fvar(20))]));
    assert!(fv.contains(&fvar(10)));
    assert!(fv.contains(&fvar(20)));
}

#[test]
fn test_free_vars_proj_structure_free() {
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("p"),
            nat_ty(),
            LetValue::Proj {
                type_name: name("Prod"),
                idx: 0,
                structure: fvar(0),
            },
        ),
        Code::ret(fvar(1)),
    );
    assert!(free_vars(&code).contains(&fvar(0)));
}

#[test]
fn test_free_vars_fvar_call() {
    let code = Code::let_bind(
        LetDecl::new(
            fvar(2),
            name("r"),
            nat_ty(),
            LetValue::FVar {
                fvar: fvar(0),
                args: vec![Arg::FVar(fvar(1))],
            },
        ),
        Code::ret(fvar(2)),
    );
    let fv = free_vars(&code);
    assert!(fv.contains(&fvar(0)));
    assert!(fv.contains(&fvar(1)));
}

#[test]
fn test_free_vars_erased_and_type_args_not_counted() {
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("r"),
            nat_ty(),
            LetValue::Const {
                name: name("f"),
                levels: vec![],
                args: vec![Arg::Erased, Arg::Type(nat_ty()), Arg::Index(0)],
            },
        ),
        Code::ret(fvar(1)),
    );
    assert!(free_vars(&code).is_empty());
}

#[test]
fn test_free_vars_reuse_slot_and_args() {
    let code = Code::let_bind(
        LetDecl::new(
            fvar(5),
            name("v"),
            nat_ty(),
            LetValue::Reuse {
                slot: fvar(0),
                ctor_name: name("List.cons"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(1))],
            },
        ),
        Code::ret(fvar(5)),
    );
    let fv = free_vars(&code);
    assert!(fv.contains(&fvar(0)));
    assert!(fv.contains(&fvar(1)));
    assert!(!fv.contains(&fvar(5)));
}

// ════════════════════════════════════════════════════════════════════════════
// Pretty summary
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_code_summary_simple() {
    let s = code_summary(&Code::ret(fvar(0)));
    assert!(s.starts_with("Return("), "got: {s}");
    assert!(s.contains("depth=1"), "got: {s}");
    assert!(s.contains("size=1"), "got: {s}");
}

#[test]
fn test_code_summary_let() {
    let s = code_summary(&simple_let(0));
    assert!(s.starts_with("Let("), "got: {s}");
    assert!(s.contains("lets=1"), "got: {s}");
    assert!(s.contains("free_vars=0"), "got: {s}");
}

#[test]
fn test_decl_summary_code() {
    let decl = Decl::new(
        name("foo"),
        vec![],
        nat_ty(),
        vec![Param::new(fvar(0), name("x"), nat_ty())],
        Code::ret(fvar(0)),
        false,
    );
    let s = decl_summary(&decl);
    assert!(s.contains("foo"), "got: {s}");
    assert!(s.contains("params=1"), "got: {s}");
    assert!(s.contains("recursive=false"), "got: {s}");
}

#[test]
fn test_decl_summary_extern() {
    let decl = Decl::extern_decl(
        name("io_print"),
        vec![],
        nat_ty(),
        vec![],
        vec![ExternEntry {
            backend: "c".into(),
            name: "lean_io_print".into(),
        }],
    );
    let s = decl_summary(&decl);
    assert!(s.contains("extern"), "got: {s}");
    assert!(s.contains("backends=[c]"), "got: {s}");
}

// ════════════════════════════════════════════════════════════════════════════
// Complexity
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_complexity_return() {
    let cx = complexity(&Code::ret(fvar(0)));
    assert_eq!(cx.max_let_depth, 0);
    assert_eq!(cx.max_case_depth, 0);
    assert_eq!(cx.call_sites, 0);
}

#[test]
fn test_complexity_let_chain() {
    let code = Code::let_bind(
        LetDecl::new(fvar(0), name("a"), nat_ty(), LetValue::nat(1)),
        Code::let_bind(
            LetDecl::new(fvar(1), name("b"), nat_ty(), LetValue::nat(2)),
            Code::let_bind(
                LetDecl::new(fvar(2), name("c"), nat_ty(), LetValue::nat(3)),
                Code::ret(fvar(2)),
            ),
        ),
    );
    assert_eq!(complexity(&code).max_let_depth, 3);
}

#[test]
fn test_complexity_nested_cases() {
    let inner_cases = Code::cases(
        name("Bool"),
        nat_ty(),
        fvar(1),
        vec![Alt::default(Code::ret(fvar(1)))],
    );
    let code = Code::cases(
        name("Bool"),
        nat_ty(),
        fvar(0),
        vec![
            Alt::ctor(name("Bool.true"), vec![], inner_cases),
            Alt::ctor(name("Bool.false"), vec![], Code::ret(fvar(2))),
        ],
    );
    let cx = complexity(&code);
    assert_eq!(cx.max_case_depth, 2);
    assert_eq!(cx.total_case_alts, 3);
}

#[test]
fn test_complexity_call_sites() {
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("r"),
            nat_ty(),
            LetValue::Const {
                name: name("f"),
                levels: vec![],
                args: vec![],
            },
        ),
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("s"),
                nat_ty(),
                LetValue::FVar {
                    fvar: fvar(1),
                    args: vec![],
                },
            ),
            Code::ret(fvar(2)),
        ),
    );
    assert_eq!(complexity(&code).call_sites, 2);
}

#[test]
fn test_complexity_join_point_count() {
    let jp = FunDecl::new(
        fvar(10),
        name("jp"),
        vec![Param::new(fvar(11), name("r"), nat_ty())],
        nat_ty(),
        Code::ret(fvar(11)),
    );
    let code = Code::join_point(jp, Code::jmp(fvar(10), vec![Arg::FVar(fvar(0))]));
    let cx = complexity(&code);
    assert_eq!(cx.join_point_count, 1);
    assert_eq!(cx.call_sites, 1);
}

#[test]
fn test_complexity_ctor_not_call() {
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("v"),
            nat_ty(),
            LetValue::Ctor {
                name: name("Nat.succ"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(0))],
            },
        ),
        Code::ret(fvar(1)),
    );
    assert_eq!(complexity(&code).call_sites, 0);
}
