// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::ir::{IRAlt, IRLiteral};

fn var(n: u32) -> VarId {
    VarId(n)
}
fn jp(n: u32) -> JoinPointId {
    JoinPointId(n)
}
fn name(s: &str) -> Name {
    Name::from_string(s)
}
fn ctor(tag: u32) -> CtorInfo {
    CtorInfo {
        name: name(&format!("C{}", tag)),
        tag,
        num_scalars: 0,
        num_objects: 0,
        field_types: vec![],
    }
}
fn mk_decl(n: &str, params: Vec<(VarId, IRType)>, ret: IRType, body: IRBody) -> IRDecl {
    IRDecl {
        name: name(n),
        params,
        return_type: ret,
        body,
    }
}

// ── Passthrough tests ───────────────────────────────────────────────

#[test]
fn test_lower_simple_ret() {
    let decl = mk_decl(
        "id",
        vec![(var(0), IRType::Object)],
        IRType::Object,
        IRBody::Ret(IRArg::Var(var(0))),
    );
    assert!(matches!(lower_decl(&decl).body, LoweredBody::Ret(_)));
}

#[test]
fn test_lower_no_join_points() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: IRExpr::Lit(IRLiteral::UInt64(42)),
        rest: Box::new(IRBody::Inc {
            var: var(0),
            n: 1,
            rest: Box::new(IRBody::Dec {
                var: var(0),
                rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
            }),
        }),
    };
    let l = lower_decl(&mk_decl(
        "no_jp",
        vec![(var(0), IRType::Object)],
        IRType::UInt64,
        body,
    ));
    // VDecl → Inc → Dec → Ret preserved
    match &l.body {
        LoweredBody::VDecl { rest, .. } => match rest.as_ref() {
            LoweredBody::Inc { rest, .. } => match rest.as_ref() {
                LoweredBody::Dec { rest, .. } => {
                    assert!(matches!(rest.as_ref(), LoweredBody::Ret(_)));
                }
                other => panic!("Expected Dec, got {:?}", other),
            },
            other => panic!("Expected Inc, got {:?}", other),
        },
        other => panic!("Expected VDecl, got {:?}", other),
    }
}

#[test]
fn test_lower_set_preserved() {
    let body = IRBody::Set {
        var: var(0),
        idx: 1,
        value: var(1),
        rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
    };
    let l = lower_decl(&mk_decl(
        "set",
        vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        IRType::Object,
        body,
    ));
    match &l.body {
        LoweredBody::Set {
            var: v,
            idx,
            value,
            rest,
        } => {
            assert_eq!((*v, *idx, *value), (var(0), 1, var(1)));
            assert!(matches!(rest.as_ref(), LoweredBody::Ret(_)));
        }
        other => panic!("Expected Set, got {:?}", other),
    }
}

#[test]
fn test_lower_decls_batch() {
    let decls = vec![
        mk_decl(
            "f1",
            vec![(var(0), IRType::Object)],
            IRType::Object,
            IRBody::Ret(IRArg::Var(var(0))),
        ),
        mk_decl("f2", vec![], IRType::Void, IRBody::Unreachable),
    ];
    let lowered = lower_decls(&decls);
    assert_eq!(lowered.len(), 2);
    assert!(matches!(lowered[0].body, LoweredBody::Ret(_)));
    assert!(matches!(lowered[1].body, LoweredBody::Unreachable));
}

// ── JDecl/Jmp lowering tests ────────────────────────────────────────

#[test]
fn test_lower_jdecl_simple() {
    // JDecl jp0 (v1: Obj): body=Ret(v1), rest=Jmp(jp0, [v0])
    let body = IRBody::JDecl {
        jp: jp(0),
        params: vec![(var(1), IRType::Object)],
        body: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
        rest: Box::new(IRBody::Jmp {
            jp: jp(0),
            args: vec![IRArg::Var(var(0))],
        }),
    };
    let l = lower_decl(&mk_decl(
        "jp",
        vec![(var(0), IRType::Object)],
        IRType::Object,
        body,
    ));

    match &l.body {
        LoweredBody::JoinPoint {
            jp,
            params,
            init,
            body,
        } => {
            assert_eq!((jp.0, params.len(), params[0].0), (0, 1, var(1)));
            match init.as_ref() {
                LoweredBody::JumpBreak { jp, assignments } => {
                    assert_eq!((jp.0, assignments.len(), assignments[0].0), (0, 1, var(1)));
                }
                other => panic!("Expected JumpBreak, got {:?}", other),
            }
            assert!(matches!(body.as_ref(), LoweredBody::Ret(_)));
        }
        other => panic!("Expected JoinPoint, got {:?}", other),
    }
}

#[test]
fn test_lower_jdecl_with_case() {
    // Case dispatch with JP for common exit: both alts jump to jp0.
    let body = IRBody::JDecl {
        jp: jp(0),
        params: vec![(var(3), IRType::Object)],
        body: Box::new(IRBody::Ret(IRArg::Var(var(3)))),
        rest: Box::new(IRBody::Case {
            scrutinee: var(0),
            alts: vec![
                IRAlt {
                    ctor: ctor(0),
                    body: Box::new(IRBody::Jmp {
                        jp: jp(0),
                        args: vec![IRArg::Var(var(0))],
                    }),
                },
                IRAlt {
                    ctor: ctor(1),
                    body: Box::new(IRBody::VDecl {
                        var: var(2),
                        ty: IRType::Object,
                        value: IRExpr::Proj {
                            idx: 0,
                            ty: IRType::Object,
                            arg: IRArg::Var(var(0)),
                        },
                        rest: Box::new(IRBody::Jmp {
                            jp: jp(0),
                            args: vec![IRArg::Var(var(2))],
                        }),
                    }),
                },
            ],
            default: None,
        }),
    };
    let l = lower_decl(&mk_decl(
        "case_jp",
        vec![(var(0), IRType::Object)],
        IRType::Object,
        body,
    ));

    match &l.body {
        LoweredBody::JoinPoint { init, body, .. } => {
            match init.as_ref() {
                LoweredBody::Case { alts, .. } => {
                    assert_eq!(alts.len(), 2);
                    assert!(matches!(
                        alts[0].body.as_ref(),
                        LoweredBody::JumpBreak { .. }
                    ));
                    match alts[1].body.as_ref() {
                        LoweredBody::VDecl { rest, .. } => {
                            assert!(matches!(rest.as_ref(), LoweredBody::JumpBreak { .. }));
                        }
                        other => panic!("Expected VDecl, got {:?}", other),
                    }
                }
                other => panic!("Expected Case, got {:?}", other),
            }
            assert!(matches!(body.as_ref(), LoweredBody::Ret(_)));
        }
        other => panic!("Expected JoinPoint, got {:?}", other),
    }
}

#[test]
fn test_lower_recursive_jp() {
    // JP body re-enters itself: Jmp in body → JumpContinue.
    let body = IRBody::JDecl {
        jp: jp(0),
        params: vec![(var(1), IRType::UInt64)],
        body: Box::new(IRBody::Case {
            scrutinee: var(1),
            alts: vec![IRAlt {
                ctor: ctor(0),
                body: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
            }],
            default: Some(Box::new(IRBody::VDecl {
                var: var(2),
                ty: IRType::UInt64,
                value: IRExpr::Lit(IRLiteral::UInt64(1)),
                rest: Box::new(IRBody::Jmp {
                    jp: jp(0),
                    args: vec![IRArg::Var(var(2))],
                }),
            })),
        }),
        rest: Box::new(IRBody::Jmp {
            jp: jp(0),
            args: vec![IRArg::Var(var(0))],
        }),
    };
    let l = lower_decl(&mk_decl(
        "rec",
        vec![(var(0), IRType::UInt64)],
        IRType::UInt64,
        body,
    ));

    match &l.body {
        LoweredBody::JoinPoint { init, body, .. } => {
            // init: JumpBreak (initial entry from rest)
            assert!(matches!(init.as_ref(), LoweredBody::JumpBreak { jp, .. } if jp.0 == 0));
            // body: Case with JumpContinue in default (re-entry)
            match body.as_ref() {
                LoweredBody::Case { alts, default, .. } => {
                    assert!(matches!(alts[0].body.as_ref(), LoweredBody::Ret(_)));
                    match default.as_ref().expect("default").as_ref() {
                        LoweredBody::VDecl { rest, .. } => {
                            assert!(matches!(
                                rest.as_ref(),
                                LoweredBody::JumpContinue { jp, .. } if jp.0 == 0
                            ));
                        }
                        other => panic!("Expected VDecl, got {:?}", other),
                    }
                }
                other => panic!("Expected Case, got {:?}", other),
            }
        }
        other => panic!("Expected JoinPoint, got {:?}", other),
    }
}

#[test]
fn test_lower_nested_jdecl() {
    // jp1 nested inside jp0's rest. jp1's body jumps to jp0.
    let body = IRBody::JDecl {
        jp: jp(0),
        params: vec![(var(2), IRType::Object)],
        body: Box::new(IRBody::Ret(IRArg::Var(var(2)))),
        rest: Box::new(IRBody::JDecl {
            jp: jp(1),
            params: vec![(var(3), IRType::Object)],
            body: Box::new(IRBody::Jmp {
                jp: jp(0),
                args: vec![IRArg::Var(var(3))],
            }),
            rest: Box::new(IRBody::Jmp {
                jp: jp(1),
                args: vec![IRArg::Var(var(0))],
            }),
        }),
    };
    let l = lower_decl(&mk_decl(
        "nested",
        vec![(var(0), IRType::Object)],
        IRType::Object,
        body,
    ));

    match &l.body {
        LoweredBody::JoinPoint {
            jp: jp0,
            init,
            body,
            ..
        } => {
            assert_eq!(jp0.0, 0);
            // init: nested JoinPoint for jp1
            match init.as_ref() {
                LoweredBody::JoinPoint {
                    jp: jp1,
                    init: j1i,
                    body: j1b,
                    ..
                } => {
                    assert_eq!(jp1.0, 1);
                    assert!(matches!(j1i.as_ref(), LoweredBody::JumpBreak { jp, .. } if jp.0 == 1));
                    // jp1 body jumps to jp0 — still in jp0's init → JumpBreak
                    assert!(matches!(j1b.as_ref(), LoweredBody::JumpBreak { jp, .. } if jp.0 == 0));
                }
                other => panic!("Expected JoinPoint for jp1, got {:?}", other),
            }
            assert!(matches!(body.as_ref(), LoweredBody::Ret(_)));
        }
        other => panic!("Expected JoinPoint for jp0, got {:?}", other),
    }
}

// ── is_terminating tests ────────────────────────────────────────────

#[test]
fn test_is_terminating_ret() {
    assert!(LoweredBody::Ret(IRArg::Erased).is_terminating());
}

#[test]
fn test_is_terminating_unreachable() {
    assert!(LoweredBody::Unreachable.is_terminating());
}

#[test]
fn test_is_terminating_jump_break() {
    assert!(LoweredBody::JumpBreak {
        jp: jp(0),
        assignments: vec![],
    }
    .is_terminating());
}

#[test]
fn test_is_terminating_case_no_default_all_ret() {
    // Exhaustive case (no default) where all alts return — must be terminating.
    let case = LoweredBody::Case {
        scrutinee: var(0),
        alts: vec![
            LoweredAlt {
                ctor: ctor(0),
                body: Box::new(LoweredBody::Ret(IRArg::Var(var(0)))),
            },
            LoweredAlt {
                ctor: ctor(1),
                body: Box::new(LoweredBody::Ret(IRArg::Var(var(0)))),
            },
        ],
        default: None,
    };
    assert!(
        case.is_terminating(),
        "exhaustive case with all-terminating alts and no default must be terminating"
    );
}

#[test]
fn test_is_terminating_case_with_default_all_ret() {
    let case = LoweredBody::Case {
        scrutinee: var(0),
        alts: vec![LoweredAlt {
            ctor: ctor(0),
            body: Box::new(LoweredBody::Ret(IRArg::Var(var(0)))),
        }],
        default: Some(Box::new(LoweredBody::Ret(IRArg::Erased))),
    };
    assert!(case.is_terminating());
}

#[test]
fn test_is_terminating_case_with_nonterminating_default() {
    // Case where default falls through — NOT terminating.
    let case = LoweredBody::Case {
        scrutinee: var(0),
        alts: vec![LoweredAlt {
            ctor: ctor(0),
            body: Box::new(LoweredBody::Ret(IRArg::Var(var(0)))),
        }],
        default: Some(Box::new(LoweredBody::VDecl {
            var: var(1),
            ty: IRType::UInt64,
            value: IRExpr::Lit(IRLiteral::UInt64(0)),
            rest: Box::new(LoweredBody::JoinPoint {
                jp: jp(0),
                params: vec![],
                init: Box::new(LoweredBody::Ret(IRArg::Erased)),
                body: Box::new(LoweredBody::Ret(IRArg::Erased)),
            }),
        })),
    };
    assert!(!case.is_terminating());
}

#[test]
fn test_is_terminating_case_no_default_mixed_alts() {
    // Exhaustive case but one alt doesn't terminate — NOT terminating.
    let case = LoweredBody::Case {
        scrutinee: var(0),
        alts: vec![
            LoweredAlt {
                ctor: ctor(0),
                body: Box::new(LoweredBody::Ret(IRArg::Var(var(0)))),
            },
            LoweredAlt {
                ctor: ctor(1),
                body: Box::new(LoweredBody::JoinPoint {
                    jp: jp(0),
                    params: vec![],
                    init: Box::new(LoweredBody::Ret(IRArg::Erased)),
                    body: Box::new(LoweredBody::Ret(IRArg::Erased)),
                }),
            },
        ],
        default: None,
    };
    assert!(!case.is_terminating());
}

#[test]
fn test_is_terminating_join_point() {
    let jp_body = LoweredBody::JoinPoint {
        jp: jp(0),
        params: vec![],
        init: Box::new(LoweredBody::Ret(IRArg::Erased)),
        body: Box::new(LoweredBody::Ret(IRArg::Erased)),
    };
    assert!(!jp_body.is_terminating(), "JoinPoint always returns false");
}

// ── Edge cases ──────────────────────────────────────────────────────

#[test]
fn test_lower_multiple_params() {
    let body = IRBody::JDecl {
        jp: jp(0),
        params: vec![(var(2), IRType::UInt64), (var(3), IRType::Object)],
        body: Box::new(IRBody::Ret(IRArg::Var(var(2)))),
        rest: Box::new(IRBody::Jmp {
            jp: jp(0),
            args: vec![IRArg::Var(var(0)), IRArg::Var(var(1))],
        }),
    };
    let l = lower_decl(&mk_decl(
        "mp",
        vec![(var(0), IRType::UInt64), (var(1), IRType::Object)],
        IRType::UInt64,
        body,
    ));
    match &l.body {
        LoweredBody::JoinPoint { params, init, .. } => {
            assert_eq!(params.len(), 2);
            match init.as_ref() {
                LoweredBody::JumpBreak { assignments, .. } => {
                    assert_eq!(assignments.len(), 2);
                    assert_eq!((assignments[0].0, assignments[1].0), (var(2), var(3)));
                }
                other => panic!("Expected JumpBreak, got {:?}", other),
            }
        }
        other => panic!("Expected JoinPoint, got {:?}", other),
    }
}

#[test]
fn test_lower_erased_args() {
    let body = IRBody::JDecl {
        jp: jp(0),
        params: vec![(var(1), IRType::Object)],
        body: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
        rest: Box::new(IRBody::Jmp {
            jp: jp(0),
            args: vec![IRArg::Erased],
        }),
    };
    let l = lower_decl(&mk_decl("erased", vec![], IRType::Object, body));
    match &l.body {
        LoweredBody::JoinPoint { init, .. } => match init.as_ref() {
            LoweredBody::JumpBreak { assignments, .. } => {
                assert!(matches!(assignments[0].1, IRArg::Erased));
            }
            other => panic!("Expected JumpBreak, got {:?}", other),
        },
        other => panic!("Expected JoinPoint, got {:?}", other),
    }
}

#[test]
fn test_lower_zero_param_jp() {
    let body = IRBody::JDecl {
        jp: jp(0),
        params: vec![],
        body: Box::new(IRBody::Ret(IRArg::Erased)),
        rest: Box::new(IRBody::Jmp {
            jp: jp(0),
            args: vec![],
        }),
    };
    let l = lower_decl(&mk_decl("zp", vec![], IRType::Object, body));
    match &l.body {
        LoweredBody::JoinPoint { params, init, .. } => {
            assert!(params.is_empty());
            match init.as_ref() {
                LoweredBody::JumpBreak { assignments, .. } => assert!(assignments.is_empty()),
                other => panic!("Expected JumpBreak, got {:?}", other),
            }
        }
        other => panic!("Expected JoinPoint, got {:?}", other),
    }
}
