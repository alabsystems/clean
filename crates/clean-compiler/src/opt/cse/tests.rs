// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::lcnf::Param;
use clean_kernel::{Expr, ExprKind, Name};

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

#[test]
fn test_cse_duplicate_literal() {
    // let _1 := 42
    // let _2 := 42  // duplicate!
    // let _3 := Nat.add _1 _2
    // return _3
    let code = Code::Let(
        LetDecl::new(
            fvar(1),
            name("_1"),
            Expr::const_str("Nat"),
            LetValue::nat(42),
        ),
        Box::new(Code::Let(
            LetDecl::new(
                fvar(2),
                name("_2"),
                Expr::const_str("Nat"),
                LetValue::nat(42),
            ),
            Box::new(Code::Let(
                LetDecl::new(
                    fvar(3),
                    name("_3"),
                    Expr::const_str("Nat"),
                    LetValue::Const {
                        name: name("Nat.add"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(2))],
                    },
                ),
                Box::new(Code::Return(fvar(3))),
            )),
        )),
    );

    let decl = Decl::new(
        name("test"),
        vec![],
        Expr::const_str("Nat"),
        vec![],
        code,
        false,
    );

    let result = eliminate_common_subexpressions(&decl);

    // _2 should be eliminated (or rewritten to use _1)
    let s = result.to_string();
    // The add should use _1 twice
    assert!(
        s.contains("Nat.add _x1 _x1"),
        "Should use _x1 twice, got:\n{s}"
    );
}

#[test]
fn test_cse_in_code_duplicate_literal() {
    // let _1 := 42
    // let _2 := 42  // duplicate!
    // let _3 := Nat.add _1 _2
    // return _3
    let code = Code::Let(
        LetDecl::new(
            fvar(1),
            name("_1"),
            Expr::const_str("Nat"),
            LetValue::nat(42),
        ),
        Box::new(Code::Let(
            LetDecl::new(
                fvar(2),
                name("_2"),
                Expr::const_str("Nat"),
                LetValue::nat(42),
            ),
            Box::new(Code::Let(
                LetDecl::new(
                    fvar(3),
                    name("_3"),
                    Expr::const_str("Nat"),
                    LetValue::Const {
                        name: name("Nat.add"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(2))],
                    },
                ),
                Box::new(Code::Return(fvar(3))),
            )),
        )),
    );

    let result = eliminate_common_subexpressions_in_code(&code);

    let s = result.to_string();
    assert!(
        s.contains("Nat.add _x1 _x1"),
        "Should use _x1 twice, got:\n{s}"
    );
}

#[test]
fn test_cse_duplicate_call() {
    // let _1 := Nat.succ _0
    // let _2 := Nat.succ _0  // duplicate!
    // let _3 := Nat.add _1 _2
    // return _3
    let code = Code::Let(
        LetDecl::new(
            fvar(1),
            name("_1"),
            Expr::const_str("Nat"),
            LetValue::Const {
                name: name("Nat.succ"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(0))],
            },
        ),
        Box::new(Code::Let(
            LetDecl::new(
                fvar(2),
                name("_2"),
                Expr::const_str("Nat"),
                LetValue::Const {
                    name: name("Nat.succ"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0))],
                },
            ),
            Box::new(Code::Let(
                LetDecl::new(
                    fvar(3),
                    name("_3"),
                    Expr::const_str("Nat"),
                    LetValue::Const {
                        name: name("Nat.add"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(2))],
                    },
                ),
                Box::new(Code::Return(fvar(3))),
            )),
        )),
    );

    let decl = Decl::new(
        name("test"),
        vec![],
        Expr::const_str("Nat"),
        vec![Param::new(fvar(0), name("n"), Expr::const_str("Nat"))],
        code,
        false,
    );

    let result = eliminate_common_subexpressions(&decl);

    // _2 should be eliminated
    let s = result.to_string();
    // The add should use _1 twice
    assert!(
        s.contains("Nat.add _x1 _x1"),
        "Should use _x1 twice, got:\n{s}"
    );
}

#[test]
fn test_cse_no_false_positive() {
    // let _1 := Nat.succ _0
    // let _2 := Nat.succ _1  // different!
    // return _2
    let code = Code::Let(
        LetDecl::new(
            fvar(1),
            name("_1"),
            Expr::const_str("Nat"),
            LetValue::Const {
                name: name("Nat.succ"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(0))],
            },
        ),
        Box::new(Code::Let(
            LetDecl::new(
                fvar(2),
                name("_2"),
                Expr::const_str("Nat"),
                LetValue::Const {
                    name: name("Nat.succ"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(1))],
                },
            ),
            Box::new(Code::Return(fvar(2))),
        )),
    );

    let decl = Decl::new(
        name("test"),
        vec![],
        Expr::const_str("Nat"),
        vec![Param::new(fvar(0), name("n"), Expr::const_str("Nat"))],
        code,
        false,
    );

    let result = eliminate_common_subexpressions(&decl);

    // Both lets should be preserved
    let s = result.to_string();
    assert!(
        s.contains("_x1 := Nat.succ _x0"),
        "First succ should remain"
    );
    assert!(
        s.contains("_x2 := Nat.succ _x1"),
        "Second succ should remain"
    );
}

#[test]
fn test_cse_no_subst_leak_across_fun() {
    let fun_body = Code::Let(
        LetDecl::new(
            fvar(1),
            name("_1"),
            Expr::const_str("Nat"),
            LetValue::nat(42),
        ),
        Box::new(Code::Let(
            LetDecl::new(
                fvar(2),
                name("_2"),
                Expr::const_str("Nat"),
                LetValue::nat(42),
            ),
            Box::new(Code::Return(fvar(2))),
        )),
    );

    let code = Code::Fun(
        FunDecl::new(
            fvar(10),
            name("f"),
            vec![],
            Expr::const_str("Nat"),
            fun_body,
        ),
        Box::new(Code::Let(
            LetDecl::new(
                fvar(2),
                name("_outer"),
                Expr::const_str("Nat"),
                LetValue::nat(7),
            ),
            Box::new(Code::Return(fvar(2))),
        )),
    );

    let result = eliminate_common_subexpressions_in_code(&code);

    match result {
        Code::Fun(_, body) => match *body {
            Code::Let(decl, body) => {
                assert_eq!(decl.fvar_id, fvar(2));
                assert!(matches!(*body, Code::Return(ret_fvar) if ret_fvar == fvar(2)));
            }
            other => panic!("Expected outer let, got {:?}", other),
        },
        other => panic!("Expected fun wrapper, got {:?}", other),
    }
}

#[test]
fn test_cse_no_subst_leak_across_case_alts() {
    let alt1 = Alt::ctor(
        name("Nat.zero"),
        vec![],
        Code::Let(
            LetDecl::new(
                fvar(3),
                name("_alt1"),
                Expr::const_str("Nat"),
                LetValue::nat(42),
            ),
            Box::new(Code::ret(fvar(3))),
        ),
    );
    let alt2 = Alt::ctor(
        name("Nat.succ"),
        vec![Param::new(fvar(3), name("_param"), Expr::const_str("Nat"))],
        Code::ret(fvar(3)),
    );

    let code = Code::Let(
        LetDecl::new(
            fvar(1),
            name("_1"),
            Expr::const_str("Nat"),
            LetValue::nat(42),
        ),
        Box::new(Code::Let(
            LetDecl::new(
                fvar(2),
                name("_2"),
                Expr::const_str("Nat"),
                LetValue::nat(0),
            ),
            Box::new(Code::Cases(Cases::new(
                name("Nat"),
                Expr::const_str("Nat"),
                fvar(2),
                vec![alt1, alt2],
            ))),
        )),
    );

    let result = eliminate_common_subexpressions_in_code(&code);

    let cases = match result {
        Code::Let(_, body) => match *body {
            Code::Let(_, body) => match *body {
                Code::Cases(cases) => cases,
                other => panic!("Expected cases node, got {:?}", other),
            },
            other => panic!("Expected second let wrapper, got {:?}", other),
        },
        other => panic!("Expected outer let wrapper, got {:?}", other),
    };

    match cases.alts.as_slice() {
        [Alt::Ctor {
            body: alt1_body, ..
        }, Alt::Ctor {
            body: alt2_body, ..
        }] => {
            assert!(
                matches!(alt1_body.as_ref(), Code::Return(ret) if *ret == fvar(1)),
                "first alt should CSE duplicate literal to outer _1, got {:?}",
                alt1_body
            );
            assert!(
                matches!(alt2_body.as_ref(), Code::Return(ret) if *ret == fvar(3)),
                "second alt must keep its own branch param; leaked substitution would rewrite it, got {:?}",
                alt2_body
            );
        }
        other => panic!("Expected two ctor alts, got {:?}", other),
    }
}

/// Build input code for the type/type-arg substitution test.
fn make_type_subst_test_code() -> Code {
    let alt_body = Code::Let(
        LetDecl::new(
            fvar(3),
            name("_3"),
            Expr::fvar(fvar(2)),
            LetValue::FVar {
                fvar: fvar(2),
                args: vec![],
            },
        ),
        Box::new(Code::Let(
            LetDecl::new(
                fvar(4),
                name("_4"),
                Expr::fvar(fvar(2)),
                LetValue::Const {
                    name: name("Foo"),
                    levels: vec![],
                    args: vec![Arg::Type(Expr::fvar(fvar(2)))],
                },
            ),
            Box::new(Code::Unreachable(Expr::fvar(fvar(2)))),
        )),
    );

    Code::Let(
        LetDecl::new(
            fvar(1),
            name("_1"),
            Expr::const_str("Nat"),
            LetValue::nat(42),
        ),
        Box::new(Code::Let(
            LetDecl::new(
                fvar(2),
                name("_2"),
                Expr::const_str("Nat"),
                LetValue::nat(42),
            ),
            Box::new(Code::Cases(Cases::new(
                name("Nat"),
                Expr::fvar(fvar(2)),
                fvar(2),
                vec![Alt::Default(Box::new(alt_body))],
            ))),
        )),
    )
}

/// Assert an expression is an FVar pointing to the expected id.
fn assert_fvar_eq(expr: &Expr, expected: FVarId, context: &str) {
    match expr.kind() {
        ExprKind::FVar(id) => assert_eq!(*id, expected, "{context}"),
        other => panic!("{context}: expected FVar, got {other:?}"),
    }
}

#[test]
fn test_cse_substitutes_in_types_and_type_args() {
    let result = eliminate_common_subexpressions_in_code(&make_type_subst_test_code());

    // Extract the cases node and verify scrutinee/result_type were substituted
    let alt_body = match result {
        Code::Let(_, body) => match *body {
            Code::Cases(cases) => {
                assert_eq!(cases.scrutinee, fvar(1));
                assert_fvar_eq(&cases.result_type, fvar(1), "cases result_type");
                match cases.alts.as_slice() {
                    [Alt::Default(body)] => body.as_ref().clone(),
                    other => panic!("Expected default alt, got {:?}", other),
                }
            }
            other => panic!("Expected cases, got {:?}", other),
        },
        other => panic!("Expected let wrapper, got {:?}", other),
    };

    // Verify substitution propagated into alt body types and type args
    verify_alt_body_substitutions(alt_body);
}

/// Verify that all FVar(2) references in the alt body were substituted to FVar(1).
fn verify_alt_body_substitutions(alt_body: Code) {
    match alt_body {
        Code::Let(decl_3, body) => {
            assert_fvar_eq(&decl_3.ty, fvar(1), "_3 type");
            match *body {
                Code::Let(decl_4, body) => {
                    assert_fvar_eq(&decl_4.ty, fvar(1), "_4 type");
                    match decl_4.value {
                        LetValue::Const { args, .. } => match args.as_slice() {
                            [Arg::Type(expr)] => assert_fvar_eq(expr, fvar(1), "type arg"),
                            other => panic!("Expected type arg, got {:?}", other),
                        },
                        other => panic!("Expected const value, got {:?}", other),
                    }
                    match *body {
                        Code::Unreachable(ref expr) => {
                            assert_fvar_eq(expr, fvar(1), "unreachable type")
                        }
                        ref other => panic!("Expected unreachable, got {:?}", other),
                    }
                }
                other => panic!("Expected _4 let, got {:?}", other),
            }
        }
        other => panic!("Expected _3 let, got {:?}", other),
    }
}

// Part of #975: Universe level handling tests
// ===========================================================================

#[test]
fn test_cse_same_levels_should_cse() {
    // let _1 := List.nil.{1} ()
    // let _2 := List.nil.{1} ()  // same level, should CSE
    // return _2
    use clean_kernel::Level;

    let level_1 = Level::succ(Level::zero());
    let code = Code::Let(
        LetDecl::new(
            fvar(1),
            name("_1"),
            Expr::const_str("List"),
            LetValue::Const {
                name: name("List.nil"),
                levels: vec![level_1.clone()],
                args: vec![],
            },
        ),
        Box::new(Code::Let(
            LetDecl::new(
                fvar(2),
                name("_2"),
                Expr::const_str("List"),
                LetValue::Const {
                    name: name("List.nil"),
                    levels: vec![level_1],
                    args: vec![],
                },
            ),
            Box::new(Code::Return(fvar(2))),
        )),
    );

    let decl = Decl::new(
        name("test"),
        vec![],
        Expr::const_str("List"),
        vec![],
        code,
        false,
    );

    let result = eliminate_common_subexpressions(&decl);
    let s = result.to_string();
    // _2 should be rewritten to use _1
    assert!(
        s.contains("return _x1") || !s.contains("_x2 := List.nil"),
        "Should CSE same universe levels, got:\n{s}"
    );
}

#[test]
fn test_cse_different_levels_no_cse() {
    // let _1 := List.nil.{1} ()
    // let _2 := List.nil.{2} ()  // different level, should NOT CSE
    // return _2
    use clean_kernel::Level;

    let level_1 = Level::succ(Level::zero());
    let level_2 = Level::succ(level_1.clone());
    let code = Code::Let(
        LetDecl::new(
            fvar(1),
            name("_1"),
            Expr::const_str("List"),
            LetValue::Const {
                name: name("List.nil"),
                levels: vec![level_1],
                args: vec![],
            },
        ),
        Box::new(Code::Let(
            LetDecl::new(
                fvar(2),
                name("_2"),
                Expr::const_str("List"),
                LetValue::Const {
                    name: name("List.nil"),
                    levels: vec![level_2],
                    args: vec![],
                },
            ),
            Box::new(Code::Return(fvar(2))),
        )),
    );

    let decl = Decl::new(
        name("test"),
        vec![],
        Expr::const_str("List"),
        vec![],
        code,
        false,
    );

    let result = eliminate_common_subexpressions(&decl);
    let s = result.to_string();
    // Both bindings should remain - different levels
    assert!(
        s.contains("_x1 := List.nil") && s.contains("_x2 := List.nil"),
        "Should NOT CSE different universe levels, got:\n{s}"
    );
}

#[test]
fn test_cse_param_levels_same_name_should_cse() {
    // let _1 := List.nil.{u} ()
    // let _2 := List.nil.{u} ()  // same param, should CSE
    // return _2
    use clean_kernel::Level;

    let level_u = Level::Param(name("u"));
    let code = Code::Let(
        LetDecl::new(
            fvar(1),
            name("_1"),
            Expr::const_str("List"),
            LetValue::Const {
                name: name("List.nil"),
                levels: vec![level_u.clone()],
                args: vec![],
            },
        ),
        Box::new(Code::Let(
            LetDecl::new(
                fvar(2),
                name("_2"),
                Expr::const_str("List"),
                LetValue::Const {
                    name: name("List.nil"),
                    levels: vec![level_u],
                    args: vec![],
                },
            ),
            Box::new(Code::Return(fvar(2))),
        )),
    );

    let decl = Decl::new(
        name("test"),
        vec![name("u")],
        Expr::const_str("List"),
        vec![],
        code,
        false,
    );

    let result = eliminate_common_subexpressions(&decl);
    let s = result.to_string();
    // _2 should be rewritten to use _1
    assert!(
        s.contains("return _x1") || !s.contains("_x2 := List.nil"),
        "Should CSE same param levels, got:\n{s}"
    );
}

#[test]
fn test_cse_param_levels_different_names_no_cse() {
    // let _1 := List.nil.{u} ()
    // let _2 := List.nil.{v} ()  // different param, should NOT CSE
    // return _2
    use clean_kernel::Level;

    let level_u = Level::Param(name("u"));
    let level_v = Level::Param(name("v"));
    let code = Code::Let(
        LetDecl::new(
            fvar(1),
            name("_1"),
            Expr::const_str("List"),
            LetValue::Const {
                name: name("List.nil"),
                levels: vec![level_u],
                args: vec![],
            },
        ),
        Box::new(Code::Let(
            LetDecl::new(
                fvar(2),
                name("_2"),
                Expr::const_str("List"),
                LetValue::Const {
                    name: name("List.nil"),
                    levels: vec![level_v],
                    args: vec![],
                },
            ),
            Box::new(Code::Return(fvar(2))),
        )),
    );

    let decl = Decl::new(
        name("test"),
        vec![name("u"), name("v")],
        Expr::const_str("List"),
        vec![],
        code,
        false,
    );

    let result = eliminate_common_subexpressions(&decl);
    let s = result.to_string();
    // Both bindings should remain - different param names
    assert!(
        s.contains("_x1 := List.nil") && s.contains("_x2 := List.nil"),
        "Should NOT CSE different param levels, got:\n{s}"
    );
}

/// Performance proof: apply_subst_to_expr is O(S * M) per invocation where
/// S = substitution count, M = expression tree size.
///
/// For a function with N let-bindings where every other one is CSE-eliminated,
/// S grows to ~N/2. Called at each binding, total cost is sum(S_i * M) which
/// is O(N^2 * M) for the full function. This test documents the quadratic
/// growth pattern.
///
/// Fix: Build a single HashMap of all canonical substitutions and perform one
/// combined tree traversal per invocation, reducing cost to O(M) per call.
#[test]
fn test_cse_apply_subst_scaling() {
    use std::time::Instant;

    // Build a function with N sequential let-bindings, all duplicating _1.
    // CSE will eliminate bindings 2..N, growing ctx.subst to N-1 entries.
    // apply_subst_to_expr is called for each binding's type with the
    // accumulated substitutions, causing O(N^2) total subst_fvar calls.
    fn make_cse_chain(n: u64) -> Decl {
        // Build from the inside out: ret -> let_N -> ... -> let_1
        let mut body = Code::Return(fvar(1));
        for i in (2..=n).rev() {
            body = Code::Let(
                LetDecl::new(
                    fvar(i),
                    name(&format!("_{i}")),
                    Expr::const_str("Nat"),
                    LetValue::nat(42), // All duplicate _1's value
                ),
                Box::new(body),
            );
        }
        // Outermost: let _1 := 42
        body = Code::Let(
            LetDecl::new(
                fvar(1),
                name("_1"),
                Expr::const_str("Nat"),
                LetValue::nat(42),
            ),
            Box::new(body),
        );
        Decl::new(
            name("test_scaling"),
            vec![],
            Expr::const_str("Nat"),
            vec![],
            body,
            false,
        )
    }

    let sizes = [100u64, 400, 1600];
    let mut times = Vec::new();
    for &n in &sizes {
        let decl = make_cse_chain(n);
        let start = Instant::now();
        let _ = eliminate_common_subexpressions(&decl);
        let elapsed = start.elapsed();
        times.push(elapsed.as_nanos() as f64);
    }

    // Document the scaling ratio. For O(N^2), 16x input should give ~256x time.
    // For O(N), 16x input should give ~16x time.
    let ratio_16x = times[2] / times[0];
    // We expect superlinear scaling due to the O(S * M) per-call pattern.
    // This test documents the behavior -- it does not assert linear scaling.
    assert!(times[2] > 0.0, "CSE should complete on 1600 bindings");

    // Document: if ratio > 100, the quadratic pattern is clearly observable.
    // Note: this is a documentation test, not a regression gate. The assertion
    // is lenient to avoid flaky failures while still capturing the data.
    eprintln!(
        "CSE apply_subst scaling: n=100: {:.0}ns, n=400: {:.0}ns, n=1600: {:.0}ns, ratio(16x): {:.1}x",
        times[0], times[1], times[2], ratio_16x
    );
}

/// Performance proof: case alternative CSE restore is near-linear in branch count.
///
/// Before #1931 this path cloned the entire `available` and `subst` HashMaps
/// for every alternative, producing O(alts * map_size) behavior on large
/// match trees. The checkpoint/restore trail keeps per-alt restore work
/// proportional to mutations in that alt instead.
#[test]
fn test_cse_cases_scope_restore_scaling() {
    use std::hint::black_box;
    use std::time::Instant;

    fn make_cases_scaling_decl(n: u64) -> Decl {
        let alts = (0..n)
            .map(|i| Alt::ctor(name(&format!("Nat.alt{i}")), vec![], Code::ret(fvar(1))))
            .collect();
        let mut body = Code::Cases(Cases::new(
            name("Nat"),
            Expr::const_str("Nat"),
            fvar(1),
            alts,
        ));

        for i in (1..=n).rev() {
            body = Code::Let(
                LetDecl::new(
                    fvar(i),
                    name(&format!("_{i}")),
                    Expr::const_str("Nat"),
                    LetValue::nat(i),
                ),
                Box::new(body),
            );
        }

        Decl::new(
            name("test_cases_scope_restore_scaling"),
            vec![],
            Expr::const_str("Nat"),
            vec![],
            body,
            false,
        )
    }

    let sizes = [16u64, 64, 256];
    let mut times = Vec::new();
    for &n in &sizes {
        let decl = make_cases_scaling_decl(n);
        let start = Instant::now();
        black_box(eliminate_common_subexpressions(&decl));
        times.push(start.elapsed().as_nanos() as f64);
    }

    let ratio_16x = times[2] / times[0];
    assert!(
        ratio_16x < 100.0,
        "case-alt scope restore scaling regressed: n=16 {:.0}ns, n=64 {:.0}ns, n=256 {:.0}ns, ratio(16x)={ratio_16x:.1}x",
        times[0],
        times[1],
        times[2],
    );
}
