// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Bug 20 (unread field cleanup on the fast path).
//! Part of #2059.

use super::super::cleanup::TypeMap;
use super::super::mask::ProjSources;
use super::super::rewrite::make_fast_path_with_types;
use super::*;
use crate::rc::pseudo_op;
use std::collections::HashMap;

fn pair_type() -> Expr {
    Expr::const_str("Pair")
}

fn mixed_type() -> Expr {
    Expr::const_str("Mixed")
}

fn char_mixed_type() -> Expr {
    Expr::const_str("CharMixed")
}

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

fn dec_projected_field_indices(code: &Code) -> Vec<u32> {
    fn collect(code: &Code, projections: &mut HashMap<FVarId, u32>, indices: &mut Vec<u32>) {
        match code {
            Code::Let(decl, body) => {
                if let LetValue::Proj { idx, .. } = &decl.value {
                    projections.insert(decl.fvar_id, *idx);
                }

                if let LetValue::Const { name, args, .. } = &decl.value {
                    if name.to_string() == pseudo_op::DEC {
                        if let [Arg::FVar(target)] = args.as_slice() {
                            if let Some(idx) = projections.get(target) {
                                indices.push(*idx);
                            }
                        }
                    }
                }

                collect(body, projections, indices);
            }
            Code::Fun(fun_decl, body) | Code::JoinPoint(fun_decl, body) => {
                collect(&fun_decl.body, projections, indices);
                collect(body, projections, indices);
            }
            Code::Cases(cases) => {
                for alt in &cases.alts {
                    match alt {
                        Alt::Ctor { body, .. } => collect(body, projections, indices),
                        Alt::Default(body) => collect(body, projections, indices),
                    }
                }
            }
            Code::Jmp { .. } | Code::Return(_) | Code::Unreachable(_) => {}
        }
    }

    let mut projections = HashMap::new();
    let mut indices = Vec::new();
    collect(code, &mut projections, &mut indices);
    indices
}

fn first_cases_after_lets(code: &Code) -> &Cases {
    match code {
        Code::Let(_, body) => first_cases_after_lets(body),
        Code::Cases(cases) => cases,
        _ => panic!("expected leading lets followed by a case split"),
    }
}

fn branch_cleanup_code() -> Code {
    Code::Cases(Cases {
        type_name: name("Bool"),
        result_type: pair_type(),
        scrutinee: fvar(99),
        alts: vec![
            Alt::Ctor {
                ctor_name: name("Bool.true"),
                params: vec![],
                body: Box::new(Code::let_bind(
                    LetDecl::new(
                        fvar(10),
                        name("left"),
                        nat_type(),
                        LetValue::Proj {
                            type_name: name("Pair"),
                            idx: 0,
                            structure: fvar(1),
                        },
                    ),
                    Code::let_bind(
                        LetDecl::new(
                            fvar(3),
                            name("result_true"),
                            pair_type(),
                            LetValue::Reuse {
                                slot: fvar(2),
                                ctor_name: name("Pair.mk"),
                                levels: vec![],
                                args: vec![Arg::FVar(fvar(10)), Arg::FVar(fvar(20))],
                            },
                        ),
                        Code::ret(fvar(3)),
                    ),
                )),
            },
            Alt::Ctor {
                ctor_name: name("Bool.false"),
                params: vec![],
                body: Box::new(Code::let_bind(
                    LetDecl::new(
                        fvar(4),
                        name("result_false"),
                        pair_type(),
                        LetValue::Reuse {
                            slot: fvar(2),
                            ctor_name: name("Pair.mk"),
                            levels: vec![],
                            args: vec![Arg::FVar(fvar(30)), Arg::FVar(fvar(31))],
                        },
                    ),
                    Code::ret(fvar(4)),
                )),
            },
        ],
    })
}

#[test]
fn test_fast_path_decrements_unread_object_fields_only() {
    let code = Code::let_bind(
        LetDecl::new(
            fvar(10),
            name("left"),
            nat_type(),
            LetValue::Proj {
                type_name: name("Pair"),
                idx: 0,
                structure: fvar(1),
            },
        ),
        Code::let_bind(
            LetDecl::new(fvar(20), name("new_right"), nat_type(), LetValue::nat(7)),
            Code::let_bind(
                LetDecl::new(
                    fvar(3),
                    name("result"),
                    pair_type(),
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
    );

    let mut type_map = TypeMap::new();
    type_map.insert(fvar(1), pair_type());

    let mut alloc = FVarIdAllocator::for_expand_reset();
    let proj_sources = ProjSources::new();
    let fast = make_fast_path_with_types(
        fvar(2),
        fvar(1),
        &code,
        &mut alloc,
        &type_map,
        &proj_sources,
    );

    assert_eq!(
        count_ops(&fast, "_dec"),
        1,
        "Only the unread object field should be released on the fast path"
    );
}

#[test]
fn test_fast_path_skips_scalar_unread_fields() {
    let code = Code::let_bind(
        LetDecl::new(
            fvar(10),
            name("u64_val"),
            Expr::const_str("UInt64"),
            LetValue::Const {
                name: name("u64"),
                levels: vec![],
                args: vec![],
            },
        ),
        Code::let_bind(
            LetDecl::new(fvar(20), name("new_obj"), nat_type(), LetValue::nat(1)),
            Code::let_bind(
                LetDecl::new(
                    fvar(3),
                    name("result"),
                    mixed_type(),
                    LetValue::Reuse {
                        slot: fvar(2),
                        ctor_name: name("Mixed.mk"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(10)), Arg::FVar(fvar(20))],
                    },
                ),
                Code::ret(fvar(3)),
            ),
        ),
    );

    let mut type_map = TypeMap::new();
    type_map.insert(fvar(1), mixed_type());

    let mut alloc = FVarIdAllocator::for_expand_reset();
    let proj_sources = ProjSources::new();
    let fast = make_fast_path_with_types(
        fvar(2),
        fvar(1),
        &code,
        &mut alloc,
        &type_map,
        &proj_sources,
    );

    assert_eq!(
        count_ops(&fast, "_dec"),
        1,
        "Only unread object-typed fields should be released"
    );
}

#[test]
fn test_fast_path_skips_char_unread_fields() {
    let code = Code::let_bind(
        LetDecl::new(
            fvar(10),
            name("char_val"),
            Expr::const_str("Char"),
            LetValue::Const {
                name: name("char_val"),
                levels: vec![],
                args: vec![],
            },
        ),
        Code::let_bind(
            LetDecl::new(fvar(20), name("new_obj"), nat_type(), LetValue::nat(1)),
            Code::let_bind(
                LetDecl::new(
                    fvar(3),
                    name("result"),
                    char_mixed_type(),
                    LetValue::Reuse {
                        slot: fvar(2),
                        ctor_name: name("CharMixed.mk"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(10)), Arg::FVar(fvar(20))],
                    },
                ),
                Code::ret(fvar(3)),
            ),
        ),
    );

    let mut type_map = TypeMap::new();
    type_map.insert(fvar(1), char_mixed_type());

    let mut alloc = FVarIdAllocator::for_expand_reset();
    let proj_sources = ProjSources::new();
    let fast = make_fast_path_with_types(
        fvar(2),
        fvar(1),
        &code,
        &mut alloc,
        &type_map,
        &proj_sources,
    );

    assert_eq!(
        count_ops(&fast, "_dec"),
        1,
        "Unread Char fields are scalar and must not receive fast-path cleanup decs"
    );
    assert_eq!(
        dec_projected_field_indices(&fast),
        vec![1],
        "Fast-path cleanup must only release the unread object slot, not the unread Char slot"
    );
}

#[test]
fn test_fast_path_skips_cleanup_for_projected_fields() {
    let code = Code::let_bind(
        LetDecl::new(
            fvar(10),
            name("left"),
            nat_type(),
            LetValue::Proj {
                type_name: name("Pair"),
                idx: 0,
                structure: fvar(1),
            },
        ),
        Code::let_bind(
            LetDecl::new(
                fvar(11),
                name("right"),
                nat_type(),
                LetValue::Proj {
                    type_name: name("Pair"),
                    idx: 1,
                    structure: fvar(1),
                },
            ),
            Code::let_bind(
                LetDecl::new(
                    fvar(3),
                    name("result"),
                    pair_type(),
                    LetValue::Reuse {
                        slot: fvar(2),
                        ctor_name: name("Pair.mk"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(10)), Arg::FVar(fvar(11))],
                    },
                ),
                Code::ret(fvar(3)),
            ),
        ),
    );

    let mut type_map = TypeMap::new();
    type_map.insert(fvar(1), pair_type());

    let mut alloc = FVarIdAllocator::for_expand_reset();
    let proj_sources = ProjSources::new();
    let fast = make_fast_path_with_types(
        fvar(2),
        fvar(1),
        &code,
        &mut alloc,
        &type_map,
        &proj_sources,
    );

    assert_eq!(
        count_ops(&fast, "_dec"),
        0,
        "Projected fields should stay alive without extra fast-path cleanup"
    );
}

#[test]
fn test_expand_reset_reuse_preserves_pre_reset_projected_fields() {
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("orig"),
            pair_type(),
            LetValue::FVar {
                fvar: fvar(100),
                args: vec![],
            },
        ),
        Code::let_bind(
            LetDecl::new(
                fvar(10),
                name("left"),
                nat_type(),
                LetValue::Proj {
                    type_name: name("Pair"),
                    idx: 0,
                    structure: fvar(1),
                },
            ),
            Code::let_bind(
                LetDecl::new(
                    fvar(2),
                    name("slot"),
                    Expr::const_str("_"),
                    LetValue::Const {
                        name: name("_reset"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(1))],
                    },
                ),
                Code::let_bind(
                    LetDecl::new(fvar(20), name("new_right"), nat_type(), LetValue::nat(7)),
                    Code::let_bind(
                        LetDecl::new(
                            fvar(3),
                            name("result"),
                            pair_type(),
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
        ),
    );

    let expanded = expand_reset_reuse_in_code(&code);

    assert_eq!(
        count_ops(&expanded, "_set"),
        1,
        "Expanded fast path should still recognize pre-reset projections as self-sets"
    );
    assert_eq!(
        count_ops(&expanded, "_dec"),
        2,
        "Expanded code should only dec the slow-path object plus one unread fast-path field"
    );
}

#[test]
fn test_fast_path_cleans_unread_fields_per_branch() {
    let mut type_map = TypeMap::new();
    type_map.insert(fvar(1), pair_type());
    type_map.insert(fvar(20), nat_type());
    type_map.insert(fvar(30), nat_type());
    type_map.insert(fvar(31), nat_type());

    let mut alloc = FVarIdAllocator::for_expand_reset();
    let proj_sources = ProjSources::new();
    let fast = make_fast_path_with_types(
        fvar(2),
        fvar(1),
        &branch_cleanup_code(),
        &mut alloc,
        &type_map,
        &proj_sources,
    );

    let cases = first_cases_after_lets(&fast);
    let true_branch = match &cases.alts[0] {
        Alt::Ctor { body, .. } => body,
        Alt::Default(_) => panic!("expected ctor alt"),
    };
    let false_branch = match &cases.alts[1] {
        Alt::Ctor { body, .. } => body,
        Alt::Default(_) => panic!("expected ctor alt"),
    };

    assert_eq!(count_ops(true_branch, "_dec"), 1);
    assert_eq!(count_ops(false_branch, "_dec"), 2);
}
