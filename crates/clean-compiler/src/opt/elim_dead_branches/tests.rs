// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the ElimDeadBranches pass.

use super::*;
use crate::lcnf::{Cases, LetDecl, Param};
use clean_kernel::Expr;

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

// ── Value lattice tests ────────────────────────────────────────────

#[test]
fn test_value_merge_bot_neutral() {
    let v = Value::Ctor(name("Bool.true"));
    assert_eq!(Value::Bot.merge(v.clone()), v);
    assert_eq!(v.merge(Value::Bot), Value::Ctor(name("Bool.true")));
}

#[test]
fn test_value_merge_top_annihilator() {
    assert_eq!(Value::Top.merge(Value::Ctor(name("X"))), Value::Top);
    assert_eq!(Value::Ctor(name("X")).merge(Value::Top), Value::Top);
}

#[test]
fn test_value_merge_same_ctor() {
    let a = Value::Ctor(name("Bool.true"));
    let b = Value::Ctor(name("Bool.true"));
    assert_eq!(a.merge(b), Value::Ctor(name("Bool.true")));
}

#[test]
fn test_value_merge_different_ctors() {
    let a = Value::Ctor(name("Bool.true"));
    let b = Value::Ctor(name("Bool.false"));
    let merged = a.merge(b);
    match &merged {
        Value::Choice(names) => {
            assert!(names.contains(&name("Bool.true")));
            assert!(names.contains(&name("Bool.false")));
        }
        _ => panic!("expected Choice, got {:?}", merged),
    }
}

#[test]
fn test_value_contains_ctor() {
    assert!(Value::Top.contains_ctor(&name("X")));
    assert!(Value::Bot.contains_ctor(&name("X")));
    assert!(Value::Ctor(name("X")).contains_ctor(&name("X")));
    assert!(!Value::Ctor(name("X")).contains_ctor(&name("Y")));
    let choice = Value::Choice(vec![name("A"), name("B")]);
    assert!(choice.contains_ctor(&name("A")));
    assert!(!choice.contains_ctor(&name("C")));
}

// ── End-to-end pass tests ──────────────────────────────────────────

#[test]
fn test_elim_dead_branch_known_ctor() {
    // let _0 := Bool.true
    // cases _0 of
    // | Bool.true => return _1
    // | Bool.false => return _2
    //
    // Expected: let _0 := Bool.true; return _1
    let code = Code::Let(
        LetDecl::new(
            fvar(0),
            name("_0"),
            Expr::const_str("Bool"),
            LetValue::Ctor {
                name: name("Bool.true"),
                levels: vec![],
                args: vec![],
            },
        ),
        Box::new(Code::Cases(Cases {
            type_name: name("Bool"),
            result_type: Expr::const_str("Nat"),
            scrutinee: fvar(0),
            alts: vec![
                Alt::Ctor {
                    ctor_name: name("Bool.true"),
                    params: vec![],
                    body: Box::new(Code::Return(fvar(1))),
                },
                Alt::Ctor {
                    ctor_name: name("Bool.false"),
                    params: vec![],
                    body: Box::new(Code::Return(fvar(2))),
                },
            ],
        })),
    );

    let result = elim_dead_branches_in_code(&code);
    // The cases should be eliminated, leaving just the true branch.
    match &result {
        Code::Let(decl, body) => {
            assert_eq!(decl.fvar_id, fvar(0));
            match body.as_ref() {
                Code::Return(fv) => assert_eq!(*fv, fvar(1)),
                other => panic!("expected Return(_1), got {:?}", other),
            }
        }
        other => panic!("expected Let, got {:?}", other),
    }
}

#[test]
fn test_elim_dead_branch_unknown_scrutinee_keeps_all() {
    // cases _0 of
    // | Bool.true => return _1
    // | Bool.false => return _2
    //
    // _0 is unknown (Top), so both branches are kept.
    let code = Code::Cases(Cases {
        type_name: name("Bool"),
        result_type: Expr::const_str("Nat"),
        scrutinee: fvar(0),
        alts: vec![
            Alt::Ctor {
                ctor_name: name("Bool.true"),
                params: vec![],
                body: Box::new(Code::Return(fvar(1))),
            },
            Alt::Ctor {
                ctor_name: name("Bool.false"),
                params: vec![],
                body: Box::new(Code::Return(fvar(2))),
            },
        ],
    });

    let result = elim_dead_branches_in_code(&code);
    match &result {
        Code::Cases(cases) => {
            assert_eq!(cases.alts.len(), 2);
        }
        other => panic!("expected Cases, got {:?}", other),
    }
}

#[test]
fn test_elim_dead_branch_nat_zero_literal() {
    // let _0 := 0   (Nat literal)
    // cases _0 of
    // | Nat.zero => return _1
    // | Nat.succ _p => return _2
    //
    // Expected: eliminates Nat.succ branch.
    let code = Code::Let(
        LetDecl::new(
            fvar(0),
            name("_0"),
            Expr::const_str("Nat"),
            LetValue::nat(0),
        ),
        Box::new(Code::Cases(Cases {
            type_name: name("Nat"),
            result_type: Expr::const_str("Nat"),
            scrutinee: fvar(0),
            alts: vec![
                Alt::Ctor {
                    ctor_name: name("Nat.zero"),
                    params: vec![],
                    body: Box::new(Code::Return(fvar(1))),
                },
                Alt::Ctor {
                    ctor_name: name("Nat.succ"),
                    params: vec![Param::new(fvar(10), name("_p"), Expr::const_str("Nat"))],
                    body: Box::new(Code::Return(fvar(2))),
                },
            ],
        })),
    );

    let result = elim_dead_branches_in_code(&code);
    match &result {
        Code::Let(_, body) => match body.as_ref() {
            Code::Return(fv) => assert_eq!(*fv, fvar(1)),
            other => panic!("expected Return(_1), got {:?}", other),
        },
        other => panic!("expected Let, got {:?}", other),
    }
}

#[test]
fn test_elim_dead_branch_nat_succ_literal() {
    // let _0 := 42   (nonzero Nat literal)
    // cases _0 of
    // | Nat.zero => return _1
    // | Nat.succ _p => return _2
    //
    // Expected: eliminates Nat.zero branch.
    let code = Code::Let(
        LetDecl::new(
            fvar(0),
            name("_0"),
            Expr::const_str("Nat"),
            LetValue::nat(42),
        ),
        Box::new(Code::Cases(Cases {
            type_name: name("Nat"),
            result_type: Expr::const_str("Nat"),
            scrutinee: fvar(0),
            alts: vec![
                Alt::Ctor {
                    ctor_name: name("Nat.zero"),
                    params: vec![],
                    body: Box::new(Code::Return(fvar(1))),
                },
                Alt::Ctor {
                    ctor_name: name("Nat.succ"),
                    params: vec![Param::new(fvar(10), name("_p"), Expr::const_str("Nat"))],
                    body: Box::new(Code::Return(fvar(2))),
                },
            ],
        })),
    );

    let result = elim_dead_branches_in_code(&code);
    match &result {
        Code::Let(_, body) => match body.as_ref() {
            Code::Return(fv) => assert_eq!(*fv, fvar(2)),
            other => panic!("expected Return(_2), got {:?}", other),
        },
        other => panic!("expected Let, got {:?}", other),
    }
}

#[test]
fn test_elim_preserves_default_branch() {
    // let _0 := Bool.true
    // cases _0 of
    // | Bool.true => return _1
    // | _ => return _2
    //
    // Default branch is always kept, but since Bool.true is known
    // and the ctor branch matches, we have 2 reachable alternatives.
    let code = Code::Let(
        LetDecl::new(
            fvar(0),
            name("_0"),
            Expr::const_str("Bool"),
            LetValue::Ctor {
                name: name("Bool.true"),
                levels: vec![],
                args: vec![],
            },
        ),
        Box::new(Code::Cases(Cases {
            type_name: name("Bool"),
            result_type: Expr::const_str("Nat"),
            scrutinee: fvar(0),
            alts: vec![
                Alt::Ctor {
                    ctor_name: name("Bool.true"),
                    params: vec![],
                    body: Box::new(Code::Return(fvar(1))),
                },
                Alt::Default(Box::new(Code::Return(fvar(2)))),
            ],
        })),
    );

    let result = elim_dead_branches_in_code(&code);
    // Both branches kept (default always survives).
    match &result {
        Code::Let(_, body) => match body.as_ref() {
            Code::Cases(cases) => {
                assert_eq!(cases.alts.len(), 2);
            }
            other => panic!("expected Cases, got {:?}", other),
        },
        other => panic!("expected Let, got {:?}", other),
    }
}

/// Build the nested-cases test input:
/// let _0 := Bool.true; let _3 := Bool.false;
/// cases _0 { true => cases _3 { true => ret _1, false => ret _4 }, false => ret _2 }
fn make_nested_cases_code() -> Code {
    let inner_cases = Code::Cases(Cases {
        type_name: name("Bool"),
        result_type: Expr::const_str("Nat"),
        scrutinee: fvar(3),
        alts: vec![
            Alt::Ctor {
                ctor_name: name("Bool.true"),
                params: vec![],
                body: Box::new(Code::Return(fvar(1))),
            },
            Alt::Ctor {
                ctor_name: name("Bool.false"),
                params: vec![],
                body: Box::new(Code::Return(fvar(4))),
            },
        ],
    });
    Code::Let(
        LetDecl::new(
            fvar(0),
            name("_0"),
            Expr::const_str("Bool"),
            LetValue::Ctor {
                name: name("Bool.true"),
                levels: vec![],
                args: vec![],
            },
        ),
        Box::new(Code::Let(
            LetDecl::new(
                fvar(3),
                name("_3"),
                Expr::const_str("Bool"),
                LetValue::Ctor {
                    name: name("Bool.false"),
                    levels: vec![],
                    args: vec![],
                },
            ),
            Box::new(Code::Cases(Cases {
                type_name: name("Bool"),
                result_type: Expr::const_str("Nat"),
                scrutinee: fvar(0),
                alts: vec![
                    Alt::Ctor {
                        ctor_name: name("Bool.true"),
                        params: vec![],
                        body: Box::new(inner_cases),
                    },
                    Alt::Ctor {
                        ctor_name: name("Bool.false"),
                        params: vec![],
                        body: Box::new(Code::Return(fvar(2))),
                    },
                ],
            })),
        )),
    )
}

#[test]
fn test_elim_dead_branch_nested_cases() {
    let code = make_nested_cases_code();
    let result = elim_dead_branches_in_code(&code);

    // Outer cases eliminated (only true branch), inner eliminated (only false branch)
    // Final: let _0 := ...; let _3 := ...; return _4
    match &result {
        Code::Let(d0, rest) => {
            assert_eq!(d0.fvar_id, fvar(0));
            match rest.as_ref() {
                Code::Let(d3, inner) => {
                    assert_eq!(d3.fvar_id, fvar(3));
                    match inner.as_ref() {
                        Code::Return(fv) => assert_eq!(*fv, fvar(4)),
                        other => panic!("expected Return(_4), got {:?}", other),
                    }
                }
                other => panic!("expected inner Let, got {:?}", other),
            }
        }
        other => panic!("expected Let, got {:?}", other),
    }
}

#[test]
fn test_elim_dead_branch_fvar_propagation() {
    // let _0 := Bool.true
    // let _1 := _0          (FVar alias, no args)
    // cases _1 of
    // | Bool.true => return _2
    // | Bool.false => return _3
    //
    // _1 should inherit _0's value via FVar propagation.
    let code = Code::Let(
        LetDecl::new(
            fvar(0),
            name("_0"),
            Expr::const_str("Bool"),
            LetValue::Ctor {
                name: name("Bool.true"),
                levels: vec![],
                args: vec![],
            },
        ),
        Box::new(Code::Let(
            LetDecl::new(
                fvar(1),
                name("_1"),
                Expr::const_str("Bool"),
                LetValue::FVar {
                    fvar: fvar(0),
                    args: vec![],
                },
            ),
            Box::new(Code::Cases(Cases {
                type_name: name("Bool"),
                result_type: Expr::const_str("Nat"),
                scrutinee: fvar(1),
                alts: vec![
                    Alt::Ctor {
                        ctor_name: name("Bool.true"),
                        params: vec![],
                        body: Box::new(Code::Return(fvar(2))),
                    },
                    Alt::Ctor {
                        ctor_name: name("Bool.false"),
                        params: vec![],
                        body: Box::new(Code::Return(fvar(3))),
                    },
                ],
            })),
        )),
    );

    let result = elim_dead_branches_in_code(&code);
    // Should eliminate Bool.false, inline Bool.true body.
    match &result {
        Code::Let(_, rest) => match rest.as_ref() {
            Code::Let(_, inner) => match inner.as_ref() {
                Code::Return(fv) => assert_eq!(*fv, fvar(2)),
                other => panic!("expected Return(_2), got {:?}", other),
            },
            other => panic!("expected inner Let, got {:?}", other),
        },
        other => panic!("expected Let, got {:?}", other),
    }
}

#[test]
fn test_elim_dead_branch_decl_api() {
    // Test the Decl-level API.
    let code = Code::Let(
        LetDecl::new(
            fvar(0),
            name("_0"),
            Expr::const_str("Bool"),
            LetValue::Ctor {
                name: name("Bool.true"),
                levels: vec![],
                args: vec![],
            },
        ),
        Box::new(Code::Cases(Cases {
            type_name: name("Bool"),
            result_type: Expr::const_str("Nat"),
            scrutinee: fvar(0),
            alts: vec![
                Alt::Ctor {
                    ctor_name: name("Bool.true"),
                    params: vec![],
                    body: Box::new(Code::Return(fvar(1))),
                },
                Alt::Ctor {
                    ctor_name: name("Bool.false"),
                    params: vec![],
                    body: Box::new(Code::Return(fvar(2))),
                },
            ],
        })),
    );

    let decl = Decl::new(
        name("test"),
        vec![],
        Expr::const_str("Nat"),
        vec![],
        code,
        false,
    );

    let result = elim_dead_branches(&decl);
    match &result.body {
        DeclValue::Code(code) => match code.as_ref() {
            Code::Let(_, body) => match body.as_ref() {
                Code::Return(fv) => assert_eq!(*fv, fvar(1)),
                other => panic!("expected Return, got {:?}", other),
            },
            other => panic!("expected Let, got {:?}", other),
        },
        DeclValue::Extern(_) => panic!("expected Code body"),
    }
}

#[test]
fn test_elim_dead_branch_extern_passthrough() {
    // Extern declarations pass through unchanged.
    let decl = Decl::extern_decl(
        name("ext_fn"),
        vec![],
        Expr::const_str("Nat"),
        vec![],
        vec![],
    );
    let result = elim_dead_branches(&decl);
    assert!(result.is_extern());
}
