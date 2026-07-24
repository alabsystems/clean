// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Bug 15 (join-point-based code sharing: resetjp + reusejp).
//! Part of #2059.

use super::*;

fn count_ops(code: &Code, op_name: &str) -> usize {
    match code {
        Code::Let(decl, body) => {
            let is_match = matches!(
                &decl.value,
                LetValue::Const { name, .. } if name.to_string() == op_name
            );
            (if is_match { 1 } else { 0 }) + count_ops(body, op_name)
        }
        Code::Fun(fun_decl, body) | Code::JoinPoint(fun_decl, body) => {
            count_ops(&fun_decl.body, op_name) + count_ops(body, op_name)
        }
        Code::Cases(cases) => cases
            .alts
            .iter()
            .map(|alt| match alt {
                Alt::Ctor { body, .. } => count_ops(body, op_name),
                Alt::Default(body) => count_ops(body, op_name),
            })
            .sum(),
        Code::Jmp { .. } | Code::Return(_) | Code::Unreachable(_) => 0,
    }
}

fn masked_proj_decl() -> LetDecl {
    LetDecl::new(
        fvar(10),
        name("p"),
        nat_type(),
        LetValue::Proj {
            type_name: name("T"),
            idx: 0,
            structure: fvar(1),
        },
    )
}

fn reset_decl() -> LetDecl {
    LetDecl::new(
        fvar(2),
        name("w"),
        nat_type(),
        LetValue::Const {
            name: name("_reset"),
            levels: vec![],
            args: vec![Arg::FVar(fvar(1))],
        },
    )
}

fn masked_inc_decl() -> LetDecl {
    LetDecl::new(
        fvar(11),
        name("_"),
        Expr::const_str("Unit"),
        LetValue::Const {
            name: name("_inc"),
            levels: vec![],
            args: vec![Arg::FVar(fvar(10))],
        },
    )
}

fn reuse_decl() -> LetDecl {
    LetDecl::new(
        fvar(3),
        name("y"),
        nat_type(),
        LetValue::Const {
            name: name("_reuse"),
            levels: vec![],
            args: vec![Arg::FVar(fvar(2)), Arg::FVar(fvar(10))],
        },
    )
}

fn masked_inc_reset_reuse_code() -> Code {
    Code::let_bind(
        masked_proj_decl(),
        Code::let_bind(
            reset_decl(),
            Code::let_bind(
                masked_inc_decl(),
                Code::let_bind(reuse_decl(), Code::ret(fvar(3))),
            ),
        ),
    )
}

#[test]
fn test_expand_creates_resetjp() {
    // The full expansion should produce a resetjp join point.
    //
    // Input:
    //   let w := reset x
    //   let y := reuse w arg
    //   return y
    let code = Code::let_bind(
        LetDecl::new(
            fvar(2),
            name("w"),
            nat_type(),
            LetValue::Const {
                name: name("_reset"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(1))],
            },
        ),
        Code::let_bind(
            LetDecl::new(
                fvar(3),
                name("y"),
                nat_type(),
                LetValue::Const {
                    name: name("_reuse"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(2)), Arg::FVar(fvar(10))],
                },
            ),
            Code::ret(fvar(3)),
        ),
    );

    let result = expand_reset_reuse_in_code(&code);
    let s = format!("{result:?}");

    // Should contain a JoinPoint (resetjp)
    assert!(
        s.contains("JoinPoint"),
        "Expansion should create a JoinPoint (resetjp): {s}"
    );
    // Should contain a Jmp (to resetjp or reusejp)
    assert!(
        s.contains("Jmp"),
        "Expansion should contain Jmp instructions: {s}"
    );
    // Should still have isShared check
    assert!(s.contains("_isShared"), "Should still check isShared: {s}");
}

#[test]
fn test_expand_resetjp_token_preserves_input_type() {
    let code = Code::let_bind(
        reset_decl(),
        Code::let_bind(reuse_decl(), Code::ret(fvar(3))),
    );
    let decl = Decl::new(
        name("wrap"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(1), name("x"), nat_type())],
        code,
        false,
    );

    let result = expand_reset_reuse(&decl);
    let DeclValue::Code(body) = result.body else {
        panic!("expected expanded declaration to keep a code body");
    };
    let Code::JoinPoint(resetjp, _) = body.as_ref() else {
        panic!("expected expanded reset/reuse to produce a resetjp join point");
    };

    assert_eq!(
        resetjp.params.len(),
        2,
        "resetjp should have token + isShared params"
    );
    assert_eq!(
        resetjp.params[0].ty,
        nat_type(),
        "resetjp token should preserve the reset object's runtime type"
    );
    assert_eq!(resetjp.params[1].ty, Expr::const_str("Bool"));
}

#[test]
fn test_expand_creates_reusejp() {
    // The expansion should produce a reusejp for the reuse site.
    //
    // Input:
    //   let w := reset x
    //   let y := reuse w arg0 arg1
    //   return y
    let code = Code::let_bind(
        LetDecl::new(
            fvar(2),
            name("w"),
            nat_type(),
            LetValue::Const {
                name: name("_reset"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(1))],
            },
        ),
        Code::let_bind(
            LetDecl::new(
                fvar(3),
                name("y"),
                nat_type(),
                LetValue::Const {
                    name: name("_reuse"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(2)), Arg::FVar(fvar(10)), Arg::FVar(fvar(11))],
                },
            ),
            Code::ret(fvar(3)),
        ),
    );

    let result = expand_reset_reuse_in_code(&code);
    let s = format!("{result:?}");

    // The fast path should have _set operations (inside reusejp dispatch)
    assert!(s.contains("_set"), "Reuse fast path should have _set: {s}");
    // The slow path should have Ctor allocation
    assert!(s.contains("Ctor"), "Reuse slow path should have Ctor: {s}");
    // The continuation (return y) should appear once in the shared JP body
    assert!(
        s.contains("Return"),
        "Shared continuation should contain Return: {s}"
    );
}

#[test]
fn test_expand_jp_dec_becomes_del() {
    // Within the resetjp body, dec of the token should become del.
    //
    // Input:
    //   let w := reset x
    //   let _ := dec w
    //   return fvar(99)
    let code = Code::let_bind(
        LetDecl::new(
            fvar(2),
            name("w"),
            nat_type(),
            LetValue::Const {
                name: name("_reset"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(1))],
            },
        ),
        Code::let_bind(
            LetDecl::new(
                fvar(5),
                name("_"),
                Expr::const_str("Unit"),
                LetValue::Const {
                    name: name("_dec"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(2))],
                },
            ),
            Code::ret(fvar(99)),
        ),
    );

    let result = expand_reset_reuse_in_code(&code);
    let s = format!("{result:?}");

    // The body should contain _del (converted from _dec)
    assert!(
        s.contains("_del"),
        "Dec of reset var should become del in JP body: {s}"
    );
}

#[test]
fn test_expand_jp_slow_path_incs_masked_projections() {
    // When projections of obj_fvar exist, the slow path should inc them
    // (because the parent object is being dec'd).
    //
    // Input:
    //   let p := proj[0] x
    //   let w := reset x
    //   let y := reuse w p
    //   return y
    let code = Code::let_bind(
        LetDecl::new(
            fvar(5),
            name("p"),
            nat_type(),
            LetValue::Proj {
                type_name: name("T"),
                idx: 0,
                structure: fvar(1),
            },
        ),
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("w"),
                nat_type(),
                LetValue::Const {
                    name: name("_reset"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(1))],
                },
            ),
            Code::let_bind(
                LetDecl::new(
                    fvar(3),
                    name("y"),
                    nat_type(),
                    LetValue::Const {
                        name: name("_reuse"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(2)), Arg::FVar(fvar(5))],
                    },
                ),
                Code::ret(fvar(3)),
            ),
        ),
    );

    let result = expand_reset_reuse_in_code(&code);
    let s = format!("{result:?}");

    // The slow path should inc the projected variable
    assert!(
        s.contains("_inc"),
        "Slow path should inc masked projection vars: {s}"
    );
    // The slow path should dec the original object
    assert!(
        s.contains("_dec"),
        "Slow path should dec original object: {s}"
    );
}

#[test]
fn test_expand_jp_body_shared_not_duplicated() {
    // The body after the reuse should appear exactly once (in the reusejp),
    // not duplicated for fast/slow paths. We verify by checking that
    // a unique marker in the body appears exactly once.
    //
    // Input:
    //   let w := reset x
    //   let y := reuse w arg
    //   let marker := f(y)      <-- unique marker
    //   return marker
    let code = Code::let_bind(
        LetDecl::new(
            fvar(2),
            name("w"),
            nat_type(),
            LetValue::Const {
                name: name("_reset"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(1))],
            },
        ),
        Code::let_bind(
            LetDecl::new(
                fvar(3),
                name("y"),
                nat_type(),
                LetValue::Const {
                    name: name("_reuse"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(2)), Arg::FVar(fvar(10))],
                },
            ),
            Code::let_bind(
                LetDecl::new(
                    fvar(4),
                    name("marker"),
                    nat_type(),
                    LetValue::Const {
                        name: name("unique_fn"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(3))],
                    },
                ),
                Code::ret(fvar(4)),
            ),
        ),
    );

    let result = expand_reset_reuse_in_code(&code);
    let s = format!("{result:?}");

    // "unique_fn" should appear exactly once (in the shared JP body)
    let count = s.matches("unique_fn").count();
    assert_eq!(
        count, 1,
        "Body should be shared (unique_fn appears {count} times, expected 1): {s}"
    );
}

#[test]
fn test_expand_jp_erases_masked_inc_from_shared_body() {
    // Bug 16 parity: an _inc of a projected field between reset and reuse
    // must not stay in the shared JP body. Only the slow path should keep
    // the projection alive, via its prefixed _inc.
    let code = masked_inc_reset_reuse_code();

    let result = expand_reset_reuse_in_code(&code);
    let inc_count = count_ops(&result, "_inc");

    assert_eq!(
        inc_count, 1,
        "Only the slow path should contain one masked projection _inc: {result:?}"
    );
}

#[test]
fn test_expand_jp_skips_self_sets_on_fast_path() {
    // Bug 17 parity on the production JP path: projected field 0 reused back
    // into slot 0 should not emit a redundant _set, while field 1 should still
    // be updated normally.
    let code = Code::let_bind(
        masked_proj_decl(),
        Code::let_bind(
            reset_decl(),
            Code::let_bind(
                LetDecl::new(fvar(20), name("fresh"), nat_type(), LetValue::nat(7)),
                Code::let_bind(
                    LetDecl::new(
                        fvar(3),
                        name("result"),
                        nat_type(),
                        LetValue::Reuse {
                            slot: fvar(2),
                            ctor_name: name("Pair.mk"),
                            levels: vec![],
                            args: vec![Arg::FVar(fvar(10)), Arg::FVar(fvar(20))],
                        },
                    ),
                    Code::ret(fvar(3)),
                ),
            ),
        ),
    );

    let result = expand_reset_reuse_in_code(&code);

    assert_eq!(
        count_ops(&result, "_set"),
        1,
        "JP fast path should elide the self-set and keep only the real field update: {result:?}"
    );
}

#[test]
fn test_expand_jp_emits_set_tag_for_native_reuse() {
    // Bug 18 parity on the production JP path: native Reuse carries ctor_name,
    // so the fast path must emit `_setTag` before reusing the object.
    let code = Code::let_bind(
        reset_decl(),
        Code::let_bind(
            LetDecl::new(
                fvar(3),
                name("result"),
                nat_type(),
                LetValue::Reuse {
                    slot: fvar(2),
                    ctor_name: name("Color.blue"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(10))],
                },
            ),
            Code::ret(fvar(3)),
        ),
    );

    let result = expand_reset_reuse_in_code(&code);
    let rendered = format!("{result:?}");

    assert_eq!(
        count_ops(&result, "_setTag"),
        1,
        "JP fast path should emit exactly one _setTag for native reuse: {rendered}"
    );
    assert!(
        rendered.contains("Color") && rendered.contains("blue"),
        "JP _setTag should carry the target ctor name: {rendered}"
    );
}
