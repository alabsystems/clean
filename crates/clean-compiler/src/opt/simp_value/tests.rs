// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::lcnf::{Code, LetDecl, LetValue, Param};
use clean_kernel::{Expr, FVarId, Name};

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn nat_type() -> Expr {
    Expr::const_str("Nat")
}

fn prod_type() -> Expr {
    Expr::const_str("Prod")
}

#[test]
fn test_proj_after_ctor() {
    // let _1 := Prod.mk _x _y
    // let _2 := Prod.fst _1  (projection index 0)
    // return _2
    // Should simplify _2 to _x
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("_1"),
            prod_type(),
            LetValue::Ctor {
                name: name("Prod.mk"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(10)), Arg::FVar(fvar(11))],
            },
        ),
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_2"),
                nat_type(),
                LetValue::Proj {
                    type_name: name("Prod"),
                    idx: 0,
                    structure: fvar(1),
                },
            ),
            Code::ret(fvar(2)),
        ),
    );

    let simplified = simplify_values_in_code(&code);

    // Check that _2's value is now _x (fvar 10)
    if let Code::Let(_, body) = simplified {
        if let Code::Let(decl2, _) = *body {
            match &decl2.value {
                LetValue::FVar { fvar: f, args } if args.is_empty() => {
                    assert_eq!(*f, fvar(10));
                    return;
                }
                _ => {}
            }
        }
    }
    panic!("Expected simplified projection");
}

#[test]
fn test_proj_second_field() {
    // let _1 := Prod.mk _x _y
    // let _2 := Prod.snd _1  (projection index 1)
    // return _2
    // Should simplify _2 to _y
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("_1"),
            prod_type(),
            LetValue::Ctor {
                name: name("Prod.mk"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(10)), Arg::FVar(fvar(11))],
            },
        ),
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_2"),
                nat_type(),
                LetValue::Proj {
                    type_name: name("Prod"),
                    idx: 1,
                    structure: fvar(1),
                },
            ),
            Code::ret(fvar(2)),
        ),
    );

    let simplified = simplify_values_in_code(&code);

    // Check that _2's value is now _y (fvar 11)
    if let Code::Let(_, body) = simplified {
        if let Code::Let(decl2, _) = *body {
            match &decl2.value {
                LetValue::FVar { fvar: f, args } if args.is_empty() => {
                    assert_eq!(*f, fvar(11));
                    return;
                }
                _ => {}
            }
        }
    }
    panic!("Expected simplified projection");
}

#[test]
fn test_copy_propagation() {
    // let _1 := _x
    // let _2 := Nat.add _1 _y
    // return _2
    // Should propagate _x in place of _1
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("_1"),
            nat_type(),
            LetValue::FVar {
                fvar: fvar(10),
                args: vec![],
            },
        ),
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_2"),
                nat_type(),
                LetValue::Const {
                    name: name("Nat.add"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(11))],
                },
            ),
            Code::ret(fvar(2)),
        ),
    );

    let simplified = simplify_values_in_code(&code);

    // Check that _2's value uses _x (fvar 10) instead of _1
    if let Code::Let(_, body) = simplified {
        if let Code::Let(decl2, _) = *body {
            if let LetValue::Const { args, .. } = &decl2.value {
                assert_eq!(args[0], Arg::FVar(fvar(10)));
                return;
            }
        }
    }
    panic!("Expected propagated argument");
}

#[test]
fn test_alias_chain() {
    // let _1 := _x
    // let _2 := _1
    // let _3 := Nat.add _2 _y
    // Should propagate _x through the alias chain
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("_1"),
            nat_type(),
            LetValue::FVar {
                fvar: fvar(10),
                args: vec![],
            },
        ),
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_2"),
                nat_type(),
                LetValue::FVar {
                    fvar: fvar(1),
                    args: vec![],
                },
            ),
            Code::let_bind(
                LetDecl::new(
                    fvar(3),
                    name("_3"),
                    nat_type(),
                    LetValue::Const {
                        name: name("Nat.add"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(2)), Arg::FVar(fvar(11))],
                    },
                ),
                Code::ret(fvar(3)),
            ),
        ),
    );

    let simplified = simplify_values_in_code(&code);

    if let Code::Let(_, body) = simplified {
        if let Code::Let(_, body) = *body {
            if let Code::Let(decl3, _) = *body {
                if let LetValue::Const { args, .. } = &decl3.value {
                    assert_eq!(args[0], Arg::FVar(fvar(10)));
                    return;
                }
            }
        }
    }

    panic!("Expected propagated alias chain");
}

#[test]
fn test_no_simplify_unknown_ctor() {
    // If we don't know the constructor, can't simplify projection
    // let _2 := Prod.fst _param  // _param is unknown
    // return _2
    let code = Code::let_bind(
        LetDecl::new(
            fvar(2),
            name("_2"),
            nat_type(),
            LetValue::Proj {
                type_name: name("Prod"),
                idx: 0,
                structure: fvar(1), // unknown
            },
        ),
        Code::ret(fvar(2)),
    );

    let simplified = simplify_values_in_code(&code);

    // Check that projection is unchanged
    if let Code::Let(decl, _) = simplified {
        if let LetValue::Proj { idx, structure, .. } = &decl.value {
            assert_eq!(*idx, 0);
            assert_eq!(*structure, fvar(1));
            return;
        }
    }
    panic!("Expected unchanged projection");
}

#[test]
fn test_simp_in_cases() {
    // In a case branch, the scrutinee has known constructor form
    // cases _1 of
    // | Prod.mk _a _b =>
    //     let _2 := Prod.fst _1
    //     return _2
    // Should simplify _2 to _a
    let code = Code::cases(
        name("Prod"),
        nat_type(),
        fvar(1),
        vec![Alt::Ctor {
            ctor_name: name("Prod.mk"),
            params: vec![
                Param::new(fvar(10), name("_a"), nat_type()),
                Param::new(fvar(11), name("_b"), nat_type()),
            ],
            body: Box::new(Code::let_bind(
                LetDecl::new(
                    fvar(2),
                    name("_2"),
                    nat_type(),
                    LetValue::Proj {
                        type_name: name("Prod"),
                        idx: 0,
                        structure: fvar(1),
                    },
                ),
                Code::ret(fvar(2)),
            )),
        }],
    );

    let simplified = simplify_values_in_code(&code);

    // Check that in the branch, _2's value is _a (fvar 10)
    if let Code::Cases(cases) = simplified {
        if let Alt::Ctor { body, .. } = &cases.alts[0] {
            if let Code::Let(decl, _) = body.as_ref() {
                match &decl.value {
                    LetValue::FVar { fvar: f, args } if args.is_empty() => {
                        assert_eq!(*f, fvar(10));
                        return;
                    }
                    _ => {}
                }
            }
        }
    }
    panic!("Expected simplified projection in case branch");
}

#[test]
fn test_simplify_decl() {
    // Test simplify_values on a full Decl
    let decl = Decl::new(
        name("proj_test"),
        vec![],
        nat_type(),
        vec![
            Param::new(fvar(100), name("x"), nat_type()),
            Param::new(fvar(101), name("y"), nat_type()),
        ],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("pair"),
                prod_type(),
                LetValue::Ctor {
                    name: name("Prod.mk"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(100)), Arg::FVar(fvar(101))],
                },
            ),
            Code::let_bind(
                LetDecl::new(
                    fvar(2),
                    name("result"),
                    nat_type(),
                    LetValue::Proj {
                        type_name: name("Prod"),
                        idx: 0,
                        structure: fvar(1),
                    },
                ),
                Code::ret(fvar(2)),
            ),
        ),
        false,
    );

    let simplified = simplify_values(&decl);

    // Verify the projection is simplified
    if let DeclValue::Code(code) = &simplified.body {
        if let Code::Let(_, body) = code.as_ref() {
            if let Code::Let(decl2, _) = body.as_ref() {
                if let LetValue::FVar { fvar: f, args } = &decl2.value {
                    if args.is_empty() {
                        assert_eq!(*f, fvar(100)); // x
                        return;
                    }
                }
            }
        }
    }
    panic!("Expected simplified decl");
}
