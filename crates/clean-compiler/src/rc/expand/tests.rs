// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::cleanup::TypeMap;
use super::mask::ProjSources;
use super::rewrite::{find_reuse_sites, make_fast_path_with_types, make_slow_path};
use super::*;
use crate::rc::FVarIdAllocator;

#[path = "proptest_expand.rs"]
mod proptest_expand;

#[path = "tests_mask.rs"]
mod tests_mask;

#[path = "tests_cleanup.rs"]
mod tests_cleanup;

#[path = "tests_jp.rs"]
mod tests_jp;

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn nat_type() -> Expr {
    Expr::const_str("Nat")
}

fn make_fast_path(
    reset_var: FVarId,
    obj_fvar: FVarId,
    body: &Code,
    alloc: &mut FVarIdAllocator,
) -> Code {
    let type_map = TypeMap::new();
    let proj_sources = ProjSources::new();
    make_fast_path_with_types(reset_var, obj_fvar, body, alloc, &type_map, &proj_sources)
}

#[test]
fn test_is_reset_op() {
    let reset = LetValue::Const {
        name: name("_reset"),
        levels: vec![],
        args: vec![Arg::FVar(fvar(1))],
    };
    assert!(is_reset_op(&reset));

    let not_reset = LetValue::Const {
        name: name("f"),
        levels: vec![],
        args: vec![],
    };
    assert!(!is_reset_op(&not_reset));
}

#[test]
fn test_is_reuse_op() {
    let reuse = LetValue::Const {
        name: name("_reuse"),
        levels: vec![],
        args: vec![Arg::FVar(fvar(1))],
    };
    assert!(is_reuse_op(&reuse));
}

#[test]
fn test_no_expand_without_reset() {
    // Code without reset should pass through unchanged
    let code = Code::let_bind(
        LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(42)),
        Code::ret(fvar(1)),
    );

    let result = expand_reset_reuse_in_code(&code);

    // Should be equivalent (just different structure)
    match result {
        Code::Let(decl, body) => {
            assert_eq!(decl.fvar_id, fvar(1));
            assert!(matches!(*body, Code::Return(_)));
        }
        _ => panic!("Expected Let"),
    }
}

#[test]
fn test_expand_reset_creates_case() {
    // let w := reset x
    // let y := reuse w arg  -- consumed: w is reused
    // return y
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
                    // reuse w with one argument
                    args: vec![Arg::FVar(fvar(2)), Arg::FVar(fvar(10))],
                },
            ),
            Code::ret(fvar(3)),
        ),
    );

    let result = expand_reset_reuse_in_code(&code);

    // Should have a case analysis for isShared
    let s = format!("{result:?}");
    assert!(s.contains("_isShared"), "Should check isShared: {s}");
    // Debug format separates "Bool" and "false"/"true" in Name inner structure
    assert!(
        (s.contains("\"Bool\"") && s.contains("\"false\""))
            || (s.contains("\"Bool\"") && s.contains("\"true\"")),
        "Should have branches: {s}"
    );
}

#[test]
fn test_find_reuse_sites_empty() {
    let code = Code::ret(fvar(1));
    let sites = find_reuse_sites(&code, fvar(0));
    assert!(sites.is_empty());
}

#[test]
fn test_make_fast_path_binds_reset_var() {
    // Fast path: reset_var is bound to obj_fvar (memory reuse)
    let body = Code::ret(fvar(2));
    let mut alloc = FVarIdAllocator::for_expand_reset();
    let fast = make_fast_path(fvar(2), fvar(1), &body, &mut alloc);

    // Should have a let binding for the reset_var
    let s = format!("{fast:?}");
    assert!(
        s.contains("_reuse_slot"),
        "Fast path should bind reset var: {s}"
    );
}

#[test]
fn test_make_slow_path_decrements_original() {
    // Slow path: should decrement the original object
    let body = Code::ret(fvar(2));
    let mut alloc = FVarIdAllocator::for_expand_reset();
    let slow = make_slow_path(fvar(1), &body, &mut alloc);

    // Should have a dec operation for the original object
    let s = format!("{slow:?}");
    assert!(
        s.contains("_dec"),
        "Slow path should decrement original: {s}"
    );
}

#[test]
fn test_make_fast_path_rewrites_reuse_to_set() {
    // let x := reuse w arg1 arg2
    // return x
    let reuse_code = Code::let_bind(
        LetDecl::new(
            fvar(3),
            name("x"),
            nat_type(),
            LetValue::Const {
                name: name("_reuse"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(2)), Arg::FVar(fvar(10)), Arg::FVar(fvar(11))],
            },
        ),
        Code::ret(fvar(3)),
    );

    let mut alloc = FVarIdAllocator::for_expand_reset();
    let fast = make_fast_path(fvar(2), fvar(1), &reuse_code, &mut alloc);

    // Should have _set operations for each field
    let s = format!("{fast:?}");
    assert!(
        s.contains("_set"),
        "Fast path should use set operations: {s}"
    );
}

#[test]
fn test_make_slow_path_rewrites_reuse_to_ctor() {
    // let x := reuse w arg1 arg2
    // return x
    let reuse_code = Code::let_bind(
        LetDecl::new(
            fvar(3),
            name("x"),
            nat_type(),
            LetValue::Const {
                name: name("_reuse"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(2)), Arg::FVar(fvar(10)), Arg::FVar(fvar(11))],
            },
        ),
        Code::ret(fvar(3)),
    );

    let mut alloc = FVarIdAllocator::for_expand_reset();
    let slow = make_slow_path(fvar(1), &reuse_code, &mut alloc);

    // Should convert reuse to ctor
    let s = format!("{slow:?}");
    assert!(s.contains("Ctor"), "Slow path should use constructor: {s}");
    assert!(
        !s.contains("_reuse"),
        "Slow path should not have _reuse: {s}"
    );
}

#[test]
fn test_field_index_encoding() {
    // Verify that field indices use Arg::Index (Part of #1105)
    let reuse_code = Code::let_bind(
        LetDecl::new(
            fvar(3),
            name("x"),
            nat_type(),
            LetValue::Const {
                name: name("_reuse"),
                levels: vec![],
                // 3 fields: indices should be 0, 1, 2
                args: vec![
                    Arg::FVar(fvar(2)),   // reset_var
                    Arg::FVar(fvar(100)), // field 0
                    Arg::FVar(fvar(101)), // field 1
                    Arg::FVar(fvar(102)), // field 2
                ],
            },
        ),
        Code::ret(fvar(3)),
    );

    let mut alloc = FVarIdAllocator::for_expand_reset();
    let fast = make_fast_path(fvar(2), fvar(1), &reuse_code, &mut alloc);
    let s = format!("{fast:?}");

    // Field indices should appear as Index(0), Index(1), Index(2)
    // This replaced the FVarId encoding hack (Part of #1105)
    assert!(
        s.contains("Index(0)") || s.contains("Index(1)") || s.contains("Index(2)"),
        "Field indices should be encoded as Arg::Index: {s}"
    );
}

#[test]
fn test_find_reuse_sites_with_reuse() {
    // let x := reuse reset_var arg1
    // return x
    let code = Code::let_bind(
        LetDecl::new(
            fvar(3),
            name("x"),
            nat_type(),
            LetValue::Const {
                name: name("_reuse"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(2)), Arg::FVar(fvar(10))],
            },
        ),
        Code::ret(fvar(3)),
    );

    let sites = find_reuse_sites(&code, fvar(2));
    assert_eq!(sites.len(), 1, "Should find one reuse site");
    assert_eq!(sites[0].result_fvar, fvar(3));
    assert_eq!(sites[0].args.len(), 1); // arg1 without reset_var
}

// Part of #1103: Consumed analysis tests (Lean4 parity)

#[test]
fn test_consumed_with_reuse() {
    // x is consumed via reuse
    let code = Code::let_bind(
        LetDecl::new(
            fvar(2),
            name("y"),
            nat_type(),
            LetValue::Const {
                name: name("_reuse"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(10))],
            },
        ),
        Code::ret(fvar(2)),
    );
    assert!(consumed(fvar(1), &code), "x should be consumed via reuse");
}

#[test]
fn test_consumed_with_dec() {
    // x is consumed via dec
    let code = Code::let_bind(
        LetDecl::new(
            fvar(2),
            name("_"),
            Expr::const_str("Unit"),
            LetValue::Const {
                name: name("_dec"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(1))],
            },
        ),
        Code::ret(fvar(2)),
    );
    assert!(consumed(fvar(1), &code), "x should be consumed via dec");
}

#[test]
fn test_consumed_not_consumed() {
    // x NOT consumed (no dec or reuse)
    let code = Code::ret(fvar(1));
    assert!(!consumed(fvar(1), &code), "x should not be consumed");
}

#[test]
fn test_consumed_cases_all_branches() {
    // x consumed in ALL branches (dec in A, reuse in B)
    let code = Code::Cases(Cases {
        scrutinee: fvar(5),
        type_name: name("T"),
        result_type: Expr::const_str("Unit"),
        alts: vec![
            Alt::Ctor {
                ctor_name: name("A"),
                params: vec![],
                body: Box::new(Code::let_bind(
                    LetDecl::new(
                        fvar(10),
                        name("_"),
                        Expr::const_str("Unit"),
                        LetValue::Const {
                            name: name("_dec"),
                            levels: vec![],
                            args: vec![Arg::FVar(fvar(1))],
                        },
                    ),
                    Code::ret(fvar(10)),
                )),
            },
            Alt::Ctor {
                ctor_name: name("B"),
                params: vec![],
                body: Box::new(Code::let_bind(
                    LetDecl::new(
                        fvar(11),
                        name("z"),
                        nat_type(),
                        LetValue::Const {
                            name: name("_reuse"),
                            levels: vec![],
                            args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(20))],
                        },
                    ),
                    Code::ret(fvar(11)),
                )),
            },
        ],
    });
    assert!(consumed(fvar(1), &code), "x consumed in all branches");
}

#[test]
fn test_consumed_cases_not_all_branches() {
    // x NOT consumed (must be ALL branches)
    let code = Code::Cases(Cases {
        scrutinee: fvar(5),
        type_name: name("T"),
        result_type: Expr::const_str("Unit"),
        alts: vec![
            Alt::Ctor {
                ctor_name: name("A"),
                params: vec![],
                body: Box::new(Code::let_bind(
                    LetDecl::new(
                        fvar(10),
                        name("_"),
                        Expr::const_str("Unit"),
                        LetValue::Const {
                            name: name("_dec"),
                            levels: vec![],
                            args: vec![Arg::FVar(fvar(1))],
                        },
                    ),
                    Code::ret(fvar(10)),
                )),
            },
            Alt::Ctor {
                ctor_name: name("B"),
                params: vec![],
                body: Box::new(Code::ret(fvar(99))),
            },
        ],
    });
    assert!(!consumed(fvar(1), &code), "x not consumed in all branches");
}

#[test]
fn test_reset_not_expanded_if_not_consumed() {
    // Reset should be skipped when result not consumed
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
        Code::ret(fvar(2)),
    );

    let result = expand_reset_reuse_in_code(&code);
    let s = format!("{result:?}");
    assert!(
        !s.contains("_isShared"),
        "Reset should be skipped when not consumed: {s}"
    );
}

// Part of #1104: Native LetValue::Reuse tests

#[test]
fn test_find_reuse_sites_with_native_reuse() {
    // Native Reuse variant with embedded ctor_name
    let code = Code::let_bind(
        LetDecl::new(
            fvar(3),
            name("x"),
            nat_type(),
            LetValue::Reuse {
                slot: fvar(2),
                ctor_name: name("Pair.mk"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(10)), Arg::FVar(fvar(11))],
            },
        ),
        Code::ret(fvar(3)),
    );

    let sites = find_reuse_sites(&code, fvar(2));
    assert_eq!(sites.len(), 1, "Should find one reuse site");
    assert_eq!(sites[0].result_fvar, fvar(3));
    assert_eq!(
        sites[0].ctor_name.to_string(),
        "Pair.mk",
        "Should extract ctor_name from native Reuse"
    );
    assert_eq!(sites[0].args.len(), 2);
}

#[test]
fn test_consumed_with_native_reuse() {
    // x is consumed via native Reuse
    let code = Code::let_bind(
        LetDecl::new(
            fvar(2),
            name("y"),
            nat_type(),
            LetValue::Reuse {
                slot: fvar(1),
                ctor_name: name("Pair.mk"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(10))],
            },
        ),
        Code::ret(fvar(2)),
    );
    assert!(
        consumed(fvar(1), &code),
        "x should be consumed via native Reuse"
    );
}

#[test]
fn test_slow_path_uses_native_ctor_name() {
    // Verify slow path extracts ctor_name from native Reuse (Part of #1104)
    let reuse_code = Code::let_bind(
        LetDecl::new(
            fvar(3),
            name("x"),
            nat_type(),
            LetValue::Reuse {
                slot: fvar(2),
                ctor_name: name("Pair.mk"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(10)), Arg::FVar(fvar(11))],
            },
        ),
        Code::ret(fvar(3)),
    );

    let mut alloc = FVarIdAllocator::for_expand_reset();
    let slow = make_slow_path(fvar(1), &reuse_code, &mut alloc);

    let s = format!("{slow:?}");
    // Should have Ctor with Pair.mk name (Debug format shows "Pair", "mk")
    assert!(s.contains("Ctor"), "Slow path should use constructor: {s}");
    assert!(
        s.contains("\"Pair\"") && s.contains("\"mk\""),
        "Slow path should use Pair.mk ctor name: {s}"
    );
}

#[test]
fn test_fast_path_with_native_reuse() {
    // Verify fast path generates set operations for native Reuse (Part of #1104)
    let reuse_code = Code::let_bind(
        LetDecl::new(
            fvar(3),
            name("x"),
            nat_type(),
            LetValue::Reuse {
                slot: fvar(2),
                ctor_name: name("Pair.mk"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(10)), Arg::FVar(fvar(11))],
            },
        ),
        Code::ret(fvar(3)),
    );

    let mut alloc = FVarIdAllocator::for_expand_reset();
    let fast = make_fast_path(fvar(2), fvar(1), &reuse_code, &mut alloc);

    let s = format!("{fast:?}");
    // Fast path should have _set operations, not Ctor
    assert!(
        s.contains("_set"),
        "Fast path should use _set operations: {s}"
    );
    // Should NOT have a Ctor construction in fast path
    assert!(
        !s.contains("LetValue::Ctor"),
        "Fast path should not allocate new constructor: {s}"
    );
}

// Part of #2059: Bug 21 - consumed() must check JP bodies

#[test]
fn test_consumed_via_jp_body() {
    // x is consumed via reuse inside a JP body.
    // consumed() must check JP body, not just the continuation.
    let jp_body = Code::let_bind(
        LetDecl::new(
            fvar(10),
            name("y"),
            nat_type(),
            LetValue::Const {
                name: name("_reuse"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(20))],
            },
        ),
        Code::ret(fvar(10)),
    );

    let code = Code::JoinPoint(
        FunDecl {
            fvar_id: fvar(50),
            name: name("jp"),
            params: vec![],
            ty: nat_type(),
            body: Box::new(jp_body),
        },
        Box::new(Code::ret(fvar(99))),
    );

    assert!(
        consumed(fvar(1), &code),
        "x should be consumed via reuse in JP body"
    );
}

#[test]
fn test_consumed_not_in_jp_continuation_only() {
    // x is NOT consumed in continuation, NOT consumed in JP body → false
    let jp_body = Code::ret(fvar(10));
    let code = Code::JoinPoint(
        FunDecl {
            fvar_id: fvar(50),
            name: name("jp"),
            params: vec![],
            ty: nat_type(),
            body: Box::new(jp_body),
        },
        Box::new(Code::ret(fvar(99))),
    );

    assert!(
        !consumed(fvar(1), &code),
        "x should not be consumed when absent from both JP body and continuation"
    );
}

// Part of #2059: Bug 18 - setTag for cross-constructor reuse

#[test]
fn test_fast_path_emits_set_tag_for_native_reuse() {
    // When using native Reuse with ctor_name, fast path must emit _setTag
    // to update the constructor tag for cross-ctor reuse.
    let reuse_code = Code::let_bind(
        LetDecl::new(
            fvar(3),
            name("x"),
            nat_type(),
            LetValue::Reuse {
                slot: fvar(2),
                ctor_name: name("Color.blue"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(10))],
            },
        ),
        Code::ret(fvar(3)),
    );

    let mut alloc = FVarIdAllocator::for_expand_reset();
    let fast = make_fast_path(fvar(2), fvar(1), &reuse_code, &mut alloc);

    let s = format!("{fast:?}");
    assert!(
        s.contains("_setTag"),
        "Fast path should emit _setTag for native Reuse: {s}"
    );
    // Should reference the ctor name
    assert!(
        s.contains("Color") && s.contains("blue"),
        "setTag should reference ctor name Color.blue: {s}"
    );
}

#[test]
fn test_fast_path_no_set_tag_for_legacy_reuse() {
    // Legacy reuse (LetValue::Const { name: "_reuse" }) has no ctor_name,
    // so setTag is not emitted (legacy path doesn't carry cross-ctor info).
    let reuse_code = Code::let_bind(
        LetDecl::new(
            fvar(3),
            name("x"),
            nat_type(),
            LetValue::Const {
                name: name("_reuse"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(2)), Arg::FVar(fvar(10))],
            },
        ),
        Code::ret(fvar(3)),
    );

    let mut alloc = FVarIdAllocator::for_expand_reset();
    let fast = make_fast_path(fvar(2), fvar(1), &reuse_code, &mut alloc);

    let s = format!("{fast:?}");
    assert!(
        !s.contains("_setTag"),
        "Fast path should NOT emit _setTag for legacy reuse: {s}"
    );
}

// Part of #2059: Bug 19 - dec-to-del conversion on fast path

#[test]
fn test_fast_path_converts_dec_to_del() {
    // On the fast path, _dec of the reset_var should become _del
    // because refcount is known to be 1.
    //
    // Input:
    //   let _ := _dec(reset_var)
    //   return fvar(99)
    let code_with_dec = Code::let_bind(
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
    );

    let mut alloc = FVarIdAllocator::for_expand_reset();
    let fast = make_fast_path(fvar(2), fvar(1), &code_with_dec, &mut alloc);

    let s = format!("{fast:?}");
    assert!(
        s.contains("_del"),
        "Fast path should convert _dec to _del: {s}"
    );
}

#[test]
fn test_fast_path_keeps_dec_for_other_vars() {
    // _dec of a variable other than the reset_var should NOT be converted.
    let code_with_dec = Code::let_bind(
        LetDecl::new(
            fvar(5),
            name("_"),
            Expr::const_str("Unit"),
            LetValue::Const {
                name: name("_dec"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(77))], // not the reset_var
            },
        ),
        Code::ret(fvar(99)),
    );

    let mut alloc = FVarIdAllocator::for_expand_reset();
    let fast = make_fast_path(fvar(2), fvar(1), &code_with_dec, &mut alloc);

    let s = format!("{fast:?}");
    assert!(
        s.contains("_dec"),
        "Fast path should keep _dec for non-reset vars: {s}"
    );
}
