// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for reset/reuse optimization (R/D/S transforms).
//!
//! Part of #963 - Compiler IR infrastructure.

use super::d_transform::{
    classify_use, d_go, d_transform, is_fvar_live_in, value_stores_var, DCtx, UseClassification,
};
use super::s_transform::{get_ctor_family, is_compatible_ctor, s_transform};
use super::*;
use crate::lcnf::{LetDecl, Param};
use crate::rc::borrow::{BorrowMap, FnBorrow, Ownership};
use clean_kernel::Name;

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn nat_type() -> clean_kernel::Expr {
    clean_kernel::Expr::const_str("Nat")
}

#[test]
fn test_no_reuse_without_case() {
    let code = Code::ret(fvar(0));
    let result = reset_reuse_in_code(&code);
    assert!(matches!(result, Code::Return(_)));
}

#[test]
fn test_value_stores_var() {
    let value = LetValue::Ctor {
        name: name("Pair.mk"),
        levels: vec![],
        args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(2))],
    };
    assert!(value_stores_var(&value, fvar(1)));
    assert!(value_stores_var(&value, fvar(2)));
    assert!(!value_stores_var(&value, fvar(3)));
}

#[test]
fn test_classify_use_proj_is_other() {
    let bm = BorrowMap::new();
    let proj = LetValue::Proj {
        type_name: name("Pair"),
        idx: 0,
        structure: fvar(5),
    };
    assert_eq!(classify_use(&proj, fvar(5), &bm), UseClassification::Other);
    assert_eq!(classify_use(&proj, fvar(6), &bm), UseClassification::None);
}

#[test]
fn test_classify_use_owned_arg() {
    let bm = BorrowMap::new();
    let call = LetValue::Const {
        name: name("f"),
        levels: vec![],
        args: vec![Arg::FVar(fvar(7))],
    };
    // No borrow info for "f" → defaults to OwnedArg
    assert_eq!(
        classify_use(&call, fvar(7), &bm),
        UseClassification::OwnedArg
    );
    assert_eq!(classify_use(&call, fvar(8), &bm), UseClassification::None);
}

#[test]
fn test_classify_use_ctor_is_other() {
    let bm = BorrowMap::new();
    let ctor = LetValue::Ctor {
        name: name("Pair.mk"),
        levels: vec![],
        args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(2))],
    };
    assert_eq!(classify_use(&ctor, fvar(1), &bm), UseClassification::Other);
    assert_eq!(classify_use(&ctor, fvar(3), &bm), UseClassification::None);
}

#[test]
fn test_is_compatible_ctor() {
    // Same name: always compatible
    assert!(is_compatible_ctor(
        &name("List.cons"),
        &name("List.cons"),
        false,
        None,
    ));
    // Different name, same family, cross_family=false: incompatible
    assert!(!is_compatible_ctor(
        &name("List.cons"),
        &name("List.nil"),
        false,
        None,
    ));
    // Different name, same family, cross_family=true, no env: conservative false
    // (Part of #2082: name-prefix fallback was unsound — List.cons/nil have
    // different layouts but the same family name.)
    assert!(!is_compatible_ctor(
        &name("List.cons"),
        &name("List.nil"),
        true,
        None,
    ));
}

#[test]
fn test_is_compatible_ctor_with_env_unknown_ctors_conservative() {
    // When env is provided but constructors are not found, the check must
    // be conservative (return false) rather than falling back to the unsound
    // family name heuristic.
    let env = Environment::default();

    // Unknown constructors in env → conservative false (not unsound family fallback)
    assert!(
        !is_compatible_ctor(&name("Foo.a"), &name("Foo.b"), true, Some(&env),),
        "Unknown ctors with env should be conservative (false), not fallback to family name"
    );
    // Different families → also incompatible
    assert!(!is_compatible_ctor(
        &name("Foo.a"),
        &name("Bar.a"),
        true,
        Some(&env),
    ));
}

#[test]
fn test_get_ctor_family() {
    assert_eq!(get_ctor_family(&name("List.cons")), "List");
    assert_eq!(get_ctor_family(&name("Nat.succ")), "Nat");
    assert_eq!(get_ctor_family(&name("simple")), "simple");
}

#[test]
fn test_d_terminal_liveness_check() {
    let bm = BorrowMap::new();
    let ctor_name = name("List.cons");
    let ctx = DCtx {
        x: fvar(0),
        n: 2,
        source_ctor: &ctor_name,
        cross_family: false,
        borrow_map: &bm,
        env: None,
    };
    let code = Code::ret(fvar(0));
    let mut already_found = HashSet::new();
    let mut alloc = FVarIdAllocator::for_reset_reuse();

    let result = d_transform(&ctx, &code, &mut already_found, &mut alloc);
    assert!(matches!(result, Code::Return(f) if f == fvar(0)));

    let code2 = Code::ret(fvar(99));
    let result2 = d_transform(&ctx, &code2, &mut already_found, &mut alloc);
    assert!(matches!(result2, Code::Return(f) if f == fvar(99)));
}

#[test]
fn test_scalar_ctor_excluded() {
    let body = Code::let_bind(
        LetDecl::new(
            fvar(10),
            name("_1"),
            nat_type(),
            LetValue::Ctor {
                name: name("Bool.true"),
                levels: vec![],
                args: vec![],
            },
        ),
        Code::ret(fvar(10)),
    );
    let cases = Code::Cases(Cases {
        type_name: name("Bool"),
        result_type: nat_type(),
        scrutinee: fvar(0),
        alts: vec![Alt::Ctor {
            ctor_name: name("Bool.true"),
            params: vec![],
            body: Box::new(body),
        }],
    });
    let result = reset_reuse_in_code(&cases);
    let s = format!("{result:?}");
    assert!(
        !s.contains("_reset") && !s.contains("Reuse"),
        "Scalar ctor should NOT have reset/reuse: {s}"
    );
}

#[test]
fn test_cross_family_collects_existing_resets() {
    let reset_code = Code::let_bind(
        LetDecl::new(
            fvar(100),
            name("w"),
            nat_type(),
            LetValue::Const {
                name: name("_reset"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(0))],
            },
        ),
        Code::ret(fvar(100)),
    );
    let collected = collect_resets(&reset_code);
    assert!(collected.contains(&fvar(0)));
    assert!(!collected.contains(&fvar(100)));
}

#[test]
fn test_s_recurses_into_case_alternatives() {
    let inner_body = Code::let_bind(
        LetDecl::new(
            fvar(11),
            name("_1"),
            nat_type(),
            LetValue::Ctor {
                name: name("Pair.mk"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(3)), Arg::FVar(fvar(4))],
            },
        ),
        Code::ret(fvar(11)),
    );
    let cases_code = Code::Cases(Cases {
        type_name: name("Pair"),
        result_type: nat_type(),
        scrutinee: fvar(5),
        alts: vec![Alt::Ctor {
            ctor_name: name("Pair.mk"),
            params: vec![
                Param::new(fvar(3), name("a"), nat_type()),
                Param::new(fvar(4), name("b"), nat_type()),
            ],
            body: Box::new(inner_body),
        }],
    });
    let w = fvar(200);
    let result = s_transform(w, 2, &name("Pair.mk"), &cases_code, false, None);
    assert!(result.is_some(), "S should find reuse in case alternative");
    let s = format!("{:?}", result.unwrap());
    assert!(s.contains("Reuse"), "Should substitute with Reuse: {s}");
}

#[test]
fn test_d_recurses_into_jp_body() {
    let bm = BorrowMap::new();
    let jp_body = Code::let_bind(
        LetDecl::new(
            fvar(11),
            name("_1"),
            nat_type(),
            LetValue::Ctor {
                name: name("Pair.mk"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(3)), Arg::FVar(fvar(4))],
            },
        ),
        Code::ret(fvar(11)),
    );
    let jp_decl = FunDecl::new(fvar(50), name("j"), vec![], nat_type(), jp_body);
    let code = Code::JoinPoint(jp_decl, Box::new(Code::ret(fvar(99))));
    let ctor_name = name("Pair.mk");
    let ctx = DCtx {
        x: fvar(0),
        n: 2,
        source_ctor: &ctor_name,
        cross_family: false,
        borrow_map: &bm,
        env: None,
    };
    let mut already_found = HashSet::new();
    let mut alloc = FVarIdAllocator::for_reset_reuse();
    let result = d_transform(&ctx, &code, &mut already_found, &mut alloc);
    let s = format!("{result:?}");
    assert!(s.contains("JoinPoint"), "Should preserve JP structure: {s}");
}

#[test]
fn test_d_cases_found_propagation() {
    let bm = BorrowMap::new();
    let case_body = Code::ret(fvar(0));
    let cases = Code::Cases(Cases {
        type_name: name("Pair"),
        result_type: nat_type(),
        scrutinee: fvar(5),
        alts: vec![Alt::Ctor {
            ctor_name: name("Pair.mk"),
            params: vec![
                Param::new(fvar(3), name("a"), nat_type()),
                Param::new(fvar(4), name("b"), nat_type()),
            ],
            body: Box::new(case_body),
        }],
    });
    let ctor_name = name("Pair.mk");
    let ctx = DCtx {
        x: fvar(0),
        n: 2,
        source_ctor: &ctor_name,
        cross_family: false,
        borrow_map: &bm,
        env: None,
    };
    let mut already_found = HashSet::new();
    let mut alloc = FVarIdAllocator::for_reset_reuse();
    let (_, alive) = d_go(&ctx, &cases, &mut already_found, &mut alloc);
    assert!(alive, "x is live in case branch — should report alive");
}

#[test]
fn test_reset_reuse_with_case() {
    let body = Code::let_bind(
        LetDecl::new(
            fvar(10),
            name("_1"),
            nat_type(),
            LetValue::Const {
                name: name("f"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(1))],
            },
        ),
        Code::let_bind(
            LetDecl::new(
                fvar(11),
                name("_2"),
                nat_type(),
                LetValue::Ctor {
                    name: name("List.cons"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(10)), Arg::FVar(fvar(2))],
                },
            ),
            Code::ret(fvar(11)),
        ),
    );
    let cases = Code::Cases(Cases {
        type_name: name("List"),
        result_type: nat_type(),
        scrutinee: fvar(0),
        alts: vec![Alt::Ctor {
            ctor_name: name("List.cons"),
            params: vec![
                Param::new(fvar(1), name("h"), nat_type()),
                Param::new(fvar(2), name("t"), nat_type()),
            ],
            body: Box::new(body),
        }],
    });
    let result = reset_reuse_in_code(&cases);
    let s = format!("{result:?}");
    assert!(
        s.contains("_reset") || s.contains("Reuse"),
        "Should insert reset/reuse: {s}"
    );
}

#[test]
fn test_reuse_preserves_ctor_name() {
    let body = Code::let_bind(
        LetDecl::new(
            fvar(11),
            name("_1"),
            nat_type(),
            LetValue::Ctor {
                name: name("Pair.mk"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(10)), Arg::FVar(fvar(2))],
            },
        ),
        Code::ret(fvar(11)),
    );
    let cases = Code::Cases(Cases {
        type_name: name("Pair"),
        result_type: nat_type(),
        scrutinee: fvar(0),
        alts: vec![Alt::Ctor {
            ctor_name: name("Pair.mk"),
            params: vec![
                Param::new(fvar(1), name("a"), nat_type()),
                Param::new(fvar(2), name("b"), nat_type()),
            ],
            body: Box::new(body),
        }],
    });
    let result = reset_reuse_in_code(&cases);
    let s = format!("{result:?}");
    assert!(
        s.contains("Reuse { slot:"),
        "Should produce Reuse variant: {s}"
    );
    assert!(
        s.contains("ctor_name:") && s.contains("\"Pair\"") && s.contains("\"mk\""),
        "Should have ctor_name containing 'Pair' and 'mk': {s}"
    );
}

#[test]
fn test_is_fvar_live_in() {
    let code = Code::ret(fvar(0));
    assert!(is_fvar_live_in(&code, fvar(0)));
    assert!(!is_fvar_live_in(&code, fvar(1)));

    let code2 = Code::let_bind(
        LetDecl::new(
            fvar(10),
            name("_1"),
            nat_type(),
            LetValue::Const {
                name: name("f"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(5))],
            },
        ),
        Code::ret(fvar(10)),
    );
    assert!(is_fvar_live_in(&code2, fvar(5)));
    assert!(!is_fvar_live_in(&code2, fvar(99)));
}

// Bug 22 test: classify_use with borrow info downgrades OwnedArg to Other
// when the parameter at that position is borrowed.
// (Lean 4: ResetReuse.lean:147-167)
#[test]
fn test_classify_use_borrowed_arg_is_other() {
    // Create borrow map where "g" has params: [Owned, Borrowed]
    let mut bm = BorrowMap::new();
    bm.insert(
        name("g"),
        FnBorrow {
            params: vec![Ownership::Owned, Ownership::Borrowed],
        },
    );

    // Call: let _ := g(x, y) where x=fvar(1), y=fvar(2)
    let call = LetValue::Const {
        name: name("g"),
        levels: vec![],
        args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(2))],
    };

    // fvar(1) is at position 0 (Owned) → OwnedArg
    assert_eq!(
        classify_use(&call, fvar(1), &bm),
        UseClassification::OwnedArg,
        "owned param position should classify as OwnedArg"
    );

    // fvar(2) is at position 1 (Borrowed) → Other (not consumed)
    assert_eq!(
        classify_use(&call, fvar(2), &bm),
        UseClassification::Other,
        "borrowed param position should classify as Other, not OwnedArg"
    );

    // fvar(99) not in args → None
    assert_eq!(classify_use(&call, fvar(99), &bm), UseClassification::None,);
}

// Bug 22 test: when same variable appears at both owned and borrowed positions,
// accumulation follows Lean 4 logic: OwnedArg + borrowed → Other.
#[test]
fn test_classify_use_duplicate_arg_borrow_downgrade() {
    let mut bm = BorrowMap::new();
    // "h" has params: [Owned, Borrowed]
    bm.insert(
        name("h"),
        FnBorrow {
            params: vec![Ownership::Owned, Ownership::Borrowed],
        },
    );

    // Call: let _ := h(x, x) where x=fvar(5) appears at both positions
    let call = LetValue::Const {
        name: name("h"),
        levels: vec![],
        args: vec![Arg::FVar(fvar(5)), Arg::FVar(fvar(5))],
    };

    // fvar(5) at pos 0 → OwnedArg; then at pos 1 (borrowed) → downgrades to Other
    assert_eq!(
        classify_use(&call, fvar(5), &bm),
        UseClassification::Other,
        "OwnedArg + borrowed position should downgrade to Other"
    );
}

/// Build: let result_id := call_name(arg_id); let ctor_id := List.cons(result_id, tail_id); ret ctor_id
fn make_call_then_cons(
    call_name: &str,
    arg_id: u64,
    tail_id: u64,
    result_id: u64,
    ctor_id: u64,
) -> Code {
    Code::let_bind(
        LetDecl::new(
            fvar(result_id),
            name("_tmp"),
            nat_type(),
            LetValue::Const {
                name: name(call_name),
                levels: vec![],
                args: vec![Arg::FVar(fvar(arg_id))],
            },
        ),
        Code::let_bind(
            LetDecl::new(
                fvar(ctor_id),
                name("_out"),
                nat_type(),
                LetValue::Ctor {
                    name: name("List.cons"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(result_id)), Arg::FVar(fvar(tail_id))],
                },
            ),
            Code::ret(fvar(ctor_id)),
        ),
    )
}

// Bug 23 test: already_found from one case branch must not leak into siblings.
#[test]
fn test_already_found_does_not_leak_across_branches() {
    let branch1_body = make_call_then_cons("f", 1, 2, 10, 11);
    let branch2_body = make_call_then_cons("g", 3, 4, 20, 21);

    let inner_cases = Code::Cases(Cases {
        type_name: name("List"),
        result_type: nat_type(),
        scrutinee: fvar(50),
        alts: vec![Alt::Ctor {
            ctor_name: name("List.cons"),
            params: vec![
                Param::new(fvar(3), name("h2"), nat_type()),
                Param::new(fvar(4), name("t2"), nat_type()),
            ],
            body: Box::new(branch2_body),
        }],
    });

    let outer_cases = Code::Cases(Cases {
        type_name: name("List"),
        result_type: nat_type(),
        scrutinee: fvar(0),
        alts: vec![
            Alt::Ctor {
                ctor_name: name("List.cons"),
                params: vec![
                    Param::new(fvar(1), name("h"), nat_type()),
                    Param::new(fvar(2), name("t"), nat_type()),
                ],
                body: Box::new(branch1_body),
            },
            Alt::Ctor {
                ctor_name: name("List.cons"),
                params: vec![
                    Param::new(fvar(51), name("h3"), nat_type()),
                    Param::new(fvar(52), name("t3"), nat_type()),
                ],
                body: Box::new(inner_cases),
            },
        ],
    });

    let result = reset_reuse_in_code(&outer_cases);
    let s = format!("{result:?}");
    let reuse_count = s.matches("Reuse").count();
    assert!(
        reuse_count >= 2,
        "Both branches should have reuse (found {reuse_count}): {s}"
    );
}

// Part of #2081: cross-family mode with mismatched layouts must NOT reuse
// when arity differs between source and target constructors.
#[test]
fn test_cross_family_mismatched_arity_no_reuse() {
    // Build a case on List.cons (2 params) where the branch constructs List.nil (0 args).
    // The arity check (args.len() == n) blocks this, and with env the layout check
    // would also block it. Verifies the full pipeline rejects this.
    let nil_body = Code::let_bind(
        LetDecl::new(
            fvar(10),
            name("_nil"),
            nat_type(),
            LetValue::Ctor {
                name: name("List.nil"),
                levels: vec![],
                args: vec![], // 0 args — mismatched with source ctor's 2 params
            },
        ),
        Code::ret(fvar(10)),
    );

    let cases = Code::Cases(Cases {
        type_name: name("List"),
        result_type: nat_type(),
        scrutinee: fvar(0),
        alts: vec![Alt::Ctor {
            ctor_name: name("List.cons"),
            params: vec![
                Param::new(fvar(1), name("h"), nat_type()),
                Param::new(fvar(2), name("t"), nat_type()),
            ],
            body: Box::new(nil_body),
        }],
    });

    // Run with cross_family=true via full pipeline
    let bm = BorrowMap::new();
    let config = ResetReuseConfig { cross_family: true };
    let decl = Decl {
        name: name("test_fn"),
        level_params: vec![],
        ty: nat_type(),
        params: vec![Param::new(fvar(0), name("xs"), nat_type())],
        body: DeclValue::Code(Box::new(cases)),
        recursive: false,
    };
    let result = reset_reuse_with_config(&decl, &config, &bm, None);
    let s = format!("{:?}", result.body);
    assert!(
        !s.contains("Reuse"),
        "List.nil (0 args) must not reuse List.cons (2 params) slot: {s}"
    );
}

// Part of #2081: layout-based cross-family compatibility using real Environment.
// Uses prelude constructors: List.nil (0 fields) and List.cons (2 fields) have
// different layouts, so must not be compatible. Prod.mk (2 obj fields) could be
// compatible with List.cons (2 obj fields) since both have 2 object fields and
// no scalars.
#[test]
fn test_is_compatible_ctor_with_env_layout_comparison() {
    let env = Environment::with_prelude();

    // List.nil has 0 fields, List.cons has 2 fields → different layouts
    // With env, the layout check should reject this even though they share family
    assert!(
        !is_compatible_ctor(&name("List.cons"), &name("List.nil"), true, Some(&env),),
        "List.cons (2 obj fields) and List.nil (0 fields) have different layouts"
    );

    // Same constructor: always compatible
    assert!(is_compatible_ctor(
        &name("List.cons"),
        &name("List.cons"),
        true,
        Some(&env),
    ));

    // Without env, cross-family reuse is conservatively rejected (Part of #2082)
    assert!(
        !is_compatible_ctor(&name("List.cons"), &name("List.nil"), true, None),
        "Without env, cross-family reuse is conservatively rejected"
    );

    // cross_family=false: different names always incompatible
    assert!(!is_compatible_ctor(
        &name("List.cons"),
        &name("List.nil"),
        false,
        Some(&env),
    ));
}

// Part of #2081: constructors from different families with same layout should
// be compatible in cross-family mode when env provides layout info.
#[test]
fn test_cross_family_same_layout_compatible_with_env() {
    let env = Environment::with_prelude();

    // Prod.mk has 2 object fields, List.cons has 2 object fields
    // Both have num_objects=2, scalar_size=0 → layout compatible
    // Note: if prelude types have different layouts, this test documents the behavior.
    let prod_compat = is_compatible_ctor(&name("List.cons"), &name("Prod.mk"), true, Some(&env));

    // Verify the layouts are actually what we expect by checking both exist
    let cons_exists = env.get_constructor(&name("List.cons")).is_some();
    let prod_exists = env.get_constructor(&name("Prod.mk")).is_some();
    if cons_exists && prod_exists {
        // Both constructors found — the result of is_compatible_ctor tells us
        // whether they have the same layout. Document the actual behavior.
        assert!(
            prod_compat,
            "List.cons and Prod.mk should have compatible layouts (both 2 obj fields)"
        );
    }
}
