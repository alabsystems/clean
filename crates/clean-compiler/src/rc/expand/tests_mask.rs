// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Bug 16 (eraseProjIncFor) and Bug 17 (partitionSelfSets).
//! Part of #2059.

use super::*;
use crate::rc::FVarIdAllocator;

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn nat_type() -> Expr {
    Expr::const_str("Nat")
}

/// Count occurrences of a pseudo-op by name in the Code tree.
fn count_ops(code: &Code, op_name: &str) -> usize {
    match code {
        Code::Let(decl, body) => {
            let is_match = matches!(
                &decl.value,
                LetValue::Const { name, .. } if name.to_string() == op_name
            );
            (if is_match { 1 } else { 0 }) + count_ops(body, op_name)
        }
        Code::Fun(f, body) => count_ops(&f.body, op_name) + count_ops(body, op_name),
        Code::JoinPoint(j, body) => count_ops(&j.body, op_name) + count_ops(body, op_name),
        Code::Cases(cases) => cases
            .alts
            .iter()
            .map(|alt| match alt {
                Alt::Ctor { body, .. } => count_ops(body, op_name),
                Alt::Default(body) => count_ops(body, op_name),
            })
            .sum(),
        _ => 0,
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Test helpers for building LCNF patterns
// ═══════════════════════════════════════════════════════════════════════════

/// Build a `let fvar_id := proj structure idx` declaration.
fn proj_decl(fvar_id: FVarId, n: &str, idx: u32, structure: FVarId) -> LetDecl {
    LetDecl::new(
        fvar_id,
        name(n),
        nat_type(),
        LetValue::Proj {
            type_name: name("T"),
            idx,
            structure,
        },
    )
}

/// Build a `let fvar_id := _inc(target)` declaration.
fn inc_decl(fvar_id: FVarId, target: FVarId) -> LetDecl {
    LetDecl::new(
        fvar_id,
        name("_"),
        Expr::const_str("Unit"),
        LetValue::Const {
            name: name("_inc"),
            levels: vec![],
            args: vec![Arg::FVar(target)],
        },
    )
}

/// Build a native Reuse declaration.
fn reuse_decl(fvar_id: FVarId, slot: FVarId, ctor: &str, args: Vec<Arg>) -> LetDecl {
    LetDecl::new(
        fvar_id,
        name("result"),
        nat_type(),
        LetValue::Reuse {
            slot,
            ctor_name: name(ctor),
            levels: vec![],
            args,
        },
    )
}

// ═══════════════════════════════════════════════════════════════════════════
// Bug 16: eraseProjIncFor — erase redundant _inc on fast path
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_fast_path_erases_proj_inc() {
    // _inc of a variable projected from obj_fvar should be erased.
    //   let z := proj obj 0
    //   let _ := inc z            ← erased
    //   let result := reuse w Ctor.mk z new_val
    //   return result
    let code = Code::let_bind(
        proj_decl(fvar(10), "z", 0, fvar(1)),
        Code::let_bind(
            inc_decl(fvar(11), fvar(10)),
            Code::let_bind(
                reuse_decl(
                    fvar(3),
                    fvar(2),
                    "Ctor.mk",
                    vec![Arg::FVar(fvar(10)), Arg::FVar(fvar(20))],
                ),
                Code::ret(fvar(3)),
            ),
        ),
    );

    let mut alloc = FVarIdAllocator::for_expand_reset();
    let fast = make_fast_path(fvar(2), fvar(1), &code, &mut alloc);

    assert_eq!(
        count_ops(&fast, "_inc"),
        0,
        "Should erase _inc for projected fields"
    );
    let s = format!("{fast:?}");
    assert!(s.contains("Proj"), "Projection should remain: {s}");
}

#[test]
fn test_fast_path_keeps_inc_for_non_proj() {
    // _inc of a variable NOT projected from obj_fvar should be kept.
    let code = Code::let_bind(
        inc_decl(fvar(11), fvar(77)),
        Code::let_bind(
            reuse_decl(fvar(3), fvar(2), "Ctor.mk", vec![Arg::FVar(fvar(20))]),
            Code::ret(fvar(3)),
        ),
    );

    let mut alloc = FVarIdAllocator::for_expand_reset();
    let fast = make_fast_path(fvar(2), fvar(1), &code, &mut alloc);

    assert_eq!(
        count_ops(&fast, "_inc"),
        1,
        "Should keep _inc for non-projected vars"
    );
}

#[test]
fn test_fast_path_erases_multiple_proj_incs() {
    // Multiple projections from obj, each with an inc — all incs erased.
    let code = Code::let_bind(
        proj_decl(fvar(10), "z0", 0, fvar(1)),
        Code::let_bind(
            inc_decl(fvar(11), fvar(10)),
            Code::let_bind(
                proj_decl(fvar(12), "z1", 1, fvar(1)),
                Code::let_bind(
                    inc_decl(fvar(13), fvar(12)),
                    Code::let_bind(
                        reuse_decl(
                            fvar(3),
                            fvar(2),
                            "Ctor.mk",
                            vec![Arg::FVar(fvar(10)), Arg::FVar(fvar(12))],
                        ),
                        Code::ret(fvar(3)),
                    ),
                ),
            ),
        ),
    );

    let mut alloc = FVarIdAllocator::for_expand_reset();
    let fast = make_fast_path(fvar(2), fvar(1), &code, &mut alloc);

    assert_eq!(
        count_ops(&fast, "_inc"),
        0,
        "Should erase all _inc ops for projected fields"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// Bug 17: partitionSelfSets — skip self-set stores on fast path
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_fast_path_skips_self_sets() {
    // z projected from idx 0, written back to idx 0 → self-set, skipped.
    // new_val at idx 1 → real set, kept.
    let code = Code::let_bind(
        proj_decl(fvar(10), "z", 0, fvar(1)),
        Code::let_bind(
            reuse_decl(
                fvar(3),
                fvar(2),
                "Ctor.mk",
                vec![Arg::FVar(fvar(10)), Arg::FVar(fvar(20))],
            ),
            Code::ret(fvar(3)),
        ),
    );

    let mut alloc = FVarIdAllocator::for_expand_reset();
    let fast = make_fast_path(fvar(2), fvar(1), &code, &mut alloc);

    assert_eq!(
        count_ops(&fast, "_set"),
        1,
        "Only 1 _set (field 1), field 0 is self-set"
    );
}

#[test]
fn test_fast_path_keeps_non_self_sets() {
    // z projected from idx 0, written to idx 1 → NOT self-set.
    let code = Code::let_bind(
        proj_decl(fvar(10), "z", 0, fvar(1)),
        Code::let_bind(
            reuse_decl(
                fvar(3),
                fvar(2),
                "Ctor.mk",
                vec![Arg::FVar(fvar(20)), Arg::FVar(fvar(10))],
            ),
            Code::ret(fvar(3)),
        ),
    );

    let mut alloc = FVarIdAllocator::for_expand_reset();
    let fast = make_fast_path(fvar(2), fvar(1), &code, &mut alloc);

    assert_eq!(
        count_ops(&fast, "_set"),
        2,
        "Both _set ops kept (z at wrong index)"
    );
}

#[test]
fn test_fast_path_all_self_sets_elided() {
    // Both fields are self-sets — all _set operations elided.
    let code = Code::let_bind(
        proj_decl(fvar(10), "z0", 0, fvar(1)),
        Code::let_bind(
            proj_decl(fvar(12), "z1", 1, fvar(1)),
            Code::let_bind(
                reuse_decl(
                    fvar(3),
                    fvar(2),
                    "Ctor.mk",
                    vec![Arg::FVar(fvar(10)), Arg::FVar(fvar(12))],
                ),
                Code::ret(fvar(3)),
            ),
        ),
    );

    let mut alloc = FVarIdAllocator::for_expand_reset();
    let fast = make_fast_path(fvar(2), fvar(1), &code, &mut alloc);

    assert_eq!(count_ops(&fast, "_set"), 0, "All self-sets elided");
}

// ═══════════════════════════════════════════════════════════════════════════
// Combined Bug 16 + Bug 17
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_fast_path_combined_bug16_and_bug17() {
    // proj + inc (Bug 16) + self-set (Bug 17) together.
    //   let z0 := proj obj 0     → mask entry
    //   let _ := inc z0          → erased (Bug 16)
    //   let z1 := proj obj 1     → mask entry
    //   let _ := inc z1          → erased (Bug 16)
    //   let result := reuse w Ctor.mk z0 new_val
    //   return result
    // z0 at idx 0 = self-set (Bug 17). new_val at idx 1 = real set.
    let code = Code::let_bind(
        proj_decl(fvar(10), "z0", 0, fvar(1)),
        Code::let_bind(
            inc_decl(fvar(11), fvar(10)),
            Code::let_bind(
                proj_decl(fvar(12), "z1", 1, fvar(1)),
                Code::let_bind(
                    inc_decl(fvar(13), fvar(12)),
                    Code::let_bind(
                        reuse_decl(
                            fvar(3),
                            fvar(2),
                            "Ctor.mk",
                            vec![Arg::FVar(fvar(10)), Arg::FVar(fvar(20))],
                        ),
                        Code::ret(fvar(3)),
                    ),
                ),
            ),
        ),
    );

    let mut alloc = FVarIdAllocator::for_expand_reset();
    let fast = make_fast_path(fvar(2), fvar(1), &code, &mut alloc);

    assert_eq!(count_ops(&fast, "_inc"), 0, "Bug 16: all _inc erased");
    assert_eq!(
        count_ops(&fast, "_set"),
        1,
        "Bug 17: only 1 _set (field 0 is self-set)"
    );
}
