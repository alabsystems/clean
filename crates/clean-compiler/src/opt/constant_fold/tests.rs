// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::lcnf::{Alt, Code, LetDecl, LetValue};
use clean_kernel::{Expr, FVarId, Name};
use std::sync::Arc;

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn nat_type() -> Expr {
    Expr::const_str("Nat")
}

#[test]
fn test_fold_nat_add() {
    // let _1 := 2
    // let _2 := 3
    // let _3 := Nat.add _1 _2
    // return _3
    let code = Code::let_bind(
        LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(2)),
        Code::let_bind(
            LetDecl::new(fvar(2), name("_2"), nat_type(), LetValue::nat(3)),
            Code::let_bind(
                LetDecl::new(
                    fvar(3),
                    name("_3"),
                    nat_type(),
                    LetValue::Const {
                        name: name("Nat.add"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(2))],
                    },
                ),
                Code::ret(fvar(3)),
            ),
        ),
    );

    let folded = fold_constants_in_code(&code);

    // Check that _3 now has value 5
    if let Code::Let(_, body) = folded {
        if let Code::Let(_, body) = *body {
            if let Code::Let(decl3, _) = *body {
                assert_eq!(decl3.value, LetValue::nat(5));
                return;
            }
        }
    }
    panic!("Expected folded result");
}

#[test]
fn test_fold_nat_mul() {
    // let _1 := 6
    // let _2 := 7
    // let _3 := Nat.mul _1 _2
    // return _3
    let code = Code::let_bind(
        LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(6)),
        Code::let_bind(
            LetDecl::new(fvar(2), name("_2"), nat_type(), LetValue::nat(7)),
            Code::let_bind(
                LetDecl::new(
                    fvar(3),
                    name("_3"),
                    nat_type(),
                    LetValue::Const {
                        name: name("Nat.mul"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(2))],
                    },
                ),
                Code::ret(fvar(3)),
            ),
        ),
    );

    let folded = fold_constants_in_code(&code);

    // Check that _3 now has value 42
    if let Code::Let(_, body) = folded {
        if let Code::Let(_, body) = *body {
            if let Code::Let(decl3, _) = *body {
                assert_eq!(decl3.value, LetValue::nat(42));
                return;
            }
        }
    }
    panic!("Expected folded result");
}

#[test]
fn test_fold_nat_sub_saturating() {
    // Nat.sub 3 10 should produce 0 (saturating subtraction)
    let code = Code::let_bind(
        LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(3)),
        Code::let_bind(
            LetDecl::new(fvar(2), name("_2"), nat_type(), LetValue::nat(10)),
            Code::let_bind(
                LetDecl::new(
                    fvar(3),
                    name("_3"),
                    nat_type(),
                    LetValue::Const {
                        name: name("Nat.sub"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(2))],
                    },
                ),
                Code::ret(fvar(3)),
            ),
        ),
    );

    let folded = fold_constants_in_code(&code);

    // Check that _3 now has value 0
    if let Code::Let(_, body) = folded {
        if let Code::Let(_, body) = *body {
            if let Code::Let(decl3, _) = *body {
                assert_eq!(decl3.value, LetValue::nat(0));
                return;
            }
        }
    }
    panic!("Expected folded result");
}

#[test]
fn test_fold_nat_div_by_zero() {
    // Nat.div 10 0 should NOT fold (div by zero)
    let code = Code::let_bind(
        LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(10)),
        Code::let_bind(
            LetDecl::new(fvar(2), name("_2"), nat_type(), LetValue::nat(0)),
            Code::let_bind(
                LetDecl::new(
                    fvar(3),
                    name("_3"),
                    nat_type(),
                    LetValue::Const {
                        name: name("Nat.div"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(2))],
                    },
                ),
                Code::ret(fvar(3)),
            ),
        ),
    );

    let folded = fold_constants_in_code(&code);

    // Check that _3 is still Nat.div (not folded)
    if let Code::Let(_, body) = folded {
        if let Code::Let(_, body) = *body {
            if let Code::Let(decl3, _) = *body {
                if let LetValue::Const { name, .. } = &decl3.value {
                    assert_eq!(name.to_string(), "Nat.div");
                    return;
                }
            }
        }
    }
    panic!("Expected non-folded div by zero");
}

#[test]
fn test_fold_nat_beq() {
    // Nat.beq 5 5 should produce Bool.true
    let code = Code::let_bind(
        LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(5)),
        Code::let_bind(
            LetDecl::new(fvar(2), name("_2"), nat_type(), LetValue::nat(5)),
            Code::let_bind(
                LetDecl::new(
                    fvar(3),
                    name("_3"),
                    Expr::const_str("Bool"),
                    LetValue::Const {
                        name: name("Nat.beq"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(2))],
                    },
                ),
                Code::ret(fvar(3)),
            ),
        ),
    );

    let folded = fold_constants_in_code(&code);

    // Check that _3 is now Bool.true
    if let Code::Let(_, body) = folded {
        if let Code::Let(_, body) = *body {
            if let Code::Let(decl3, _) = *body {
                if let LetValue::Ctor { name, .. } = &decl3.value {
                    assert_eq!(name.to_string(), "Bool.true");
                    return;
                }
            }
        }
    }
    panic!("Expected Bool.true constructor");
}

#[test]
fn test_no_fold_dynamic() {
    // When one arg is not a constant, don't fold
    // let _1 := <param>
    // let _2 := 3
    // let _3 := Nat.add _1 _2
    // return _3
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("_1"),
            nat_type(),
            LetValue::FVar {
                fvar: fvar(0), // parameter
                args: vec![],
            },
        ),
        Code::let_bind(
            LetDecl::new(fvar(2), name("_2"), nat_type(), LetValue::nat(3)),
            Code::let_bind(
                LetDecl::new(
                    fvar(3),
                    name("_3"),
                    nat_type(),
                    LetValue::Const {
                        name: name("Nat.add"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(2))],
                    },
                ),
                Code::ret(fvar(3)),
            ),
        ),
    );

    let folded = fold_constants_in_code(&code);

    // Check that _3 is still Nat.add (not folded)
    if let Code::Let(_, body) = folded {
        if let Code::Let(_, body) = *body {
            if let Code::Let(decl3, _) = *body {
                if let LetValue::Const { name, .. } = &decl3.value {
                    assert_eq!(name.to_string(), "Nat.add");
                    return;
                }
            }
        }
    }
    panic!("Expected non-folded add with dynamic arg");
}

#[test]
fn test_fold_string_append() {
    // String.append "hello" "world" -> "helloworld"
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("_1"),
            Expr::const_str("String"),
            LetValue::Lit(Literal::String(Arc::from("hello"))),
        ),
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_2"),
                Expr::const_str("String"),
                LetValue::Lit(Literal::String(Arc::from("world"))),
            ),
            Code::let_bind(
                LetDecl::new(
                    fvar(3),
                    name("_3"),
                    Expr::const_str("String"),
                    LetValue::Const {
                        name: name("String.append"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(2))],
                    },
                ),
                Code::ret(fvar(3)),
            ),
        ),
    );

    let folded = fold_constants_in_code(&code);

    // Check that _3 now has value "helloworld"
    if let Code::Let(_, body) = folded {
        if let Code::Let(_, body) = *body {
            if let Code::Let(decl3, _) = *body {
                if let LetValue::Lit(Literal::String(s)) = &decl3.value {
                    assert_eq!(&**s, "helloworld");
                    return;
                }
            }
        }
    }
    panic!("Expected folded string");
}

#[test]
fn test_fold_decl() {
    // Test fold_constants on a full Decl
    let decl = Decl::new(
        name("const_sum"),
        vec![],
        nat_type(),
        vec![],
        Code::let_bind(
            LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(10)),
            Code::let_bind(
                LetDecl::new(fvar(2), name("_2"), nat_type(), LetValue::nat(20)),
                Code::let_bind(
                    LetDecl::new(
                        fvar(3),
                        name("_3"),
                        nat_type(),
                        LetValue::Const {
                            name: name("Nat.add"),
                            levels: vec![],
                            args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(2))],
                        },
                    ),
                    Code::ret(fvar(3)),
                ),
            ),
        ),
        false,
    );

    let folded = fold_constants(&decl);

    // Verify the result through the body
    if let DeclValue::Code(code) = &folded.body {
        if let Code::Let(_, body) = code.as_ref() {
            if let Code::Let(_, body) = body.as_ref() {
                if let Code::Let(decl3, _) = body.as_ref() {
                    assert_eq!(decl3.value, LetValue::nat(30));
                    return;
                }
            }
        }
    }
    panic!("Expected folded decl");
}

#[test]
fn test_fold_cases_isolated_context() {
    // Ensure constant context doesn't leak across case branches.
    let alt1 = Alt::Ctor {
        ctor_name: name("Nat.succ"),
        params: vec![],
        body: Box::new(Code::let_bind(
            LetDecl::new(fvar(2), name("_2"), nat_type(), LetValue::nat(4)),
            Code::let_bind(
                LetDecl::new(
                    fvar(3),
                    name("_3"),
                    nat_type(),
                    LetValue::Const {
                        name: name("Nat.add"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(2)), Arg::FVar(fvar(2))],
                    },
                ),
                Code::ret(fvar(3)),
            ),
        )),
    };

    let alt2 = Alt::Default(Box::new(Code::let_bind(
        LetDecl::new(
            fvar(2),
            name("_2"),
            nat_type(),
            LetValue::Const {
                name: name("Nat.add"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(10)), Arg::FVar(fvar(11))],
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
                    args: vec![Arg::FVar(fvar(2)), Arg::FVar(fvar(2))],
                },
            ),
            Code::ret(fvar(3)),
        ),
    )));

    let code = Code::cases(name("Nat"), nat_type(), fvar(1), vec![alt1, alt2]);
    let folded = fold_constants_in_code(&code);

    if let Code::Cases(cases) = folded {
        if let Alt::Ctor { body, .. } = &cases.alts[0] {
            if let Code::Let(_, body) = body.as_ref() {
                if let Code::Let(decl3, _) = body.as_ref() {
                    assert_eq!(decl3.value, LetValue::nat(8));
                }
            }
        }

        if let Alt::Default(body) = &cases.alts[1] {
            if let Code::Let(_, body) = body.as_ref() {
                if let Code::Let(decl3, _) = body.as_ref() {
                    if let LetValue::Const { name, .. } = &decl3.value {
                        assert_eq!(name.to_string(), "Nat.add");
                        return;
                    }
                }
            }
        }
    }

    panic!("Expected isolated folding across cases");
}

#[test]
fn test_fold_nat_add_overflow_skips_fold() {
    // Nat.add u64::MAX 1 should NOT fold (would overflow u64)
    let code = Code::let_bind(
        LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(u64::MAX)),
        Code::let_bind(
            LetDecl::new(fvar(2), name("_2"), nat_type(), LetValue::nat(1)),
            Code::let_bind(
                LetDecl::new(
                    fvar(3),
                    name("_3"),
                    nat_type(),
                    LetValue::Const {
                        name: name("Nat.add"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(2))],
                    },
                ),
                Code::ret(fvar(3)),
            ),
        ),
    );

    let folded = fold_constants_in_code(&code);

    // Should remain as Nat.add (not folded to 0)
    if let Code::Let(_, body) = folded {
        if let Code::Let(_, body) = *body {
            if let Code::Let(decl3, _) = *body {
                if let LetValue::Const { name, .. } = &decl3.value {
                    assert_eq!(name.to_string(), "Nat.add");
                    return;
                }
            }
        }
    }
    panic!("Expected non-folded add on overflow");
}

#[test]
fn test_fold_nat_mul_overflow_skips_fold() {
    // Nat.mul u64::MAX 2 should NOT fold (would overflow u64)
    let code = Code::let_bind(
        LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(u64::MAX)),
        Code::let_bind(
            LetDecl::new(fvar(2), name("_2"), nat_type(), LetValue::nat(2)),
            Code::let_bind(
                LetDecl::new(
                    fvar(3),
                    name("_3"),
                    nat_type(),
                    LetValue::Const {
                        name: name("Nat.mul"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(2))],
                    },
                ),
                Code::ret(fvar(3)),
            ),
        ),
    );

    let folded = fold_constants_in_code(&code);

    // Should remain as Nat.mul (not folded to u64::MAX - 1)
    if let Code::Let(_, body) = folded {
        if let Code::Let(_, body) = *body {
            if let Code::Let(decl3, _) = *body {
                if let LetValue::Const { name, .. } = &decl3.value {
                    assert_eq!(name.to_string(), "Nat.mul");
                    return;
                }
            }
        }
    }
    panic!("Expected non-folded mul on overflow");
}

#[test]
fn test_fold_string_length_unicode() {
    // String.length "日本語" should return 3 (chars), not 9 (bytes)
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("_1"),
            Expr::const_str("String"),
            LetValue::Lit(Literal::String(Arc::from("日本語"))),
        ),
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_2"),
                nat_type(),
                LetValue::Const {
                    name: name("String.length"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(1))],
                },
            ),
            Code::ret(fvar(2)),
        ),
    );

    let folded = fold_constants_in_code(&code);

    if let Code::Let(_, body) = folded {
        if let Code::Let(decl2, _) = *body {
            assert_eq!(decl2.value, LetValue::nat(3));
            return;
        }
    }
    panic!("Expected String.length to count chars, not bytes");
}

#[test]
fn test_fold_string_length_emoji() {
    // String.length "🎉" should return 1 (one codepoint), not 4 (bytes)
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("_1"),
            Expr::const_str("String"),
            LetValue::Lit(Literal::String(Arc::from("🎉"))),
        ),
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_2"),
                nat_type(),
                LetValue::Const {
                    name: name("String.length"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(1))],
                },
            ),
            Code::ret(fvar(2)),
        ),
    );

    let folded = fold_constants_in_code(&code);

    if let Code::Let(_, body) = folded {
        if let Code::Let(decl2, _) = *body {
            assert_eq!(decl2.value, LetValue::nat(1));
            return;
        }
    }
    panic!("Expected String.length to count chars, not bytes");
}
