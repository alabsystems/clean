// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the extended IR checker (phase 2).

use super::ir_checker_ext2::*;
use crate::ir::{
    CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, JoinPointId, VarId,
};
use clean_kernel::Name;

fn var(n: u32) -> VarId {
    VarId(n)
}
fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn mk_ctor(tag: u32, fields: Vec<IRType>) -> CtorInfo {
    let num_objects = fields.iter().filter(|t| t.is_object()).count() as u32;
    let num_scalars = fields.iter().filter(|t| t.is_scalar()).count() as u32;
    CtorInfo {
        name: name("C"),
        tag,
        num_scalars,
        num_objects,
        field_types: fields,
    }
}

fn mk_ctor0(tag: u32) -> CtorInfo {
    mk_ctor(tag, vec![])
}

fn identity_decl() -> IRDecl {
    IRDecl {
        name: name("id"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(var(0))),
    }
}

// ── C1: Operand type consistency ─────────────────────────────────

#[test]
fn test_c1_inc_on_object_ok() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Inc {
            var: var(0),
            n: 1,
            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert_eq!(r.errors_in(Ext2CheckCategory::OperandType), 0);
}

#[test]
fn test_c1_inc_on_scalar_error() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::UInt64)],
        return_type: IRType::UInt64,
        body: IRBody::Inc {
            var: var(0),
            n: 1,
            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert!(
        r.errors_in(Ext2CheckCategory::OperandType) > 0,
        "inc on scalar should error"
    );
}

#[test]
fn test_c1_dec_on_scalar_error() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Bool)],
        return_type: IRType::Bool,
        body: IRBody::Dec {
            var: var(0),
            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert!(r.errors_in(Ext2CheckCategory::OperandType) > 0);
}

#[test]
fn test_c1_set_on_non_object_error() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::UInt64), (var(1), IRType::Object)],
        return_type: IRType::UInt64,
        body: IRBody::Set {
            var: var(0),
            idx: 0,
            value: var(1),
            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert!(r.errors_in(Ext2CheckCategory::OperandType) > 0);
}

#[test]
fn test_c1_sset_non_scalar_type_error() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::UInt64)],
        return_type: IRType::Object,
        body: IRBody::SSet {
            var: var(0),
            n: 0,
            offset: 0,
            value: var(1),
            ty: IRType::Object,
            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert!(
        r.errors_in(Ext2CheckCategory::OperandType) > 0,
        "SSet with Object type should error"
    );
}

#[test]
fn test_c1_sset_scalar_type_ok() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::UInt32)],
        return_type: IRType::Object,
        body: IRBody::SSet {
            var: var(0),
            n: 0,
            offset: 0,
            value: var(1),
            ty: IRType::UInt32,
            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        },
    };
    let r = check_ir_ext2(&[decl]);
    // No operand type errors (sset on Object target with scalar type is correct)
    let ops: Vec<_> = r
        .diagnostics
        .iter()
        .filter(|e| e.cat == Ext2CheckCategory::OperandType)
        .collect();
    assert!(ops.is_empty(), "correct SSet should not error: {:?}", ops);
}

// ── C2: Per-path RC balance ──────────────────────────────────────

#[test]
fn test_c2_balanced_paths_ok() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Case {
            scrutinee: var(0),
            alts: vec![
                IRAlt {
                    ctor: mk_ctor0(0),
                    body: Box::new(IRBody::Inc {
                        var: var(0),
                        n: 1,
                        rest: Box::new(IRBody::Dec {
                            var: var(0),
                            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
                        }),
                    }),
                },
                IRAlt {
                    ctor: mk_ctor0(1),
                    body: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
                },
            ],
            default: None,
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert_eq!(r.errors_in(Ext2CheckCategory::RcPath), 0);
}

#[test]
fn test_c2_imbalanced_path_error() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Case {
            scrutinee: var(0),
            alts: vec![
                IRAlt {
                    ctor: mk_ctor0(0),
                    body: Box::new(IRBody::Dec {
                        var: var(0),
                        rest: Box::new(IRBody::Dec {
                            var: var(0),
                            rest: Box::new(IRBody::Dec {
                                var: var(0),
                                rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
                            }),
                        }),
                    }),
                },
                IRAlt {
                    ctor: mk_ctor0(1),
                    body: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
                },
            ],
            default: None,
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert!(
        r.errors_in(Ext2CheckCategory::RcPath) > 0,
        "triple-dec path should warn"
    );
}

// ── C3: Control flow well-formedness ─────────────────────────────

#[test]
fn test_c3_simple_ret_terminates() {
    let r = check_ir_ext2(&[identity_decl()]);
    assert_eq!(r.errors_in(Ext2CheckCategory::ControlFlow), 0);
}

#[test]
fn test_c3_unreachable_terminates() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![],
        return_type: IRType::Void,
        body: IRBody::Unreachable,
    };
    let r = check_ir_ext2(&[decl]);
    assert_eq!(r.errors_in(Ext2CheckCategory::ControlFlow), 0);
}

#[test]
fn test_c3_jmp_terminates() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::JDecl {
            jp: JoinPointId(0),
            params: vec![(var(1), IRType::Object)],
            body: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
            rest: Box::new(IRBody::Jmp {
                jp: JoinPointId(0),
                args: vec![IRArg::Var(var(0))],
            }),
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert_eq!(r.errors_in(Ext2CheckCategory::ControlFlow), 0);
}

#[test]
fn test_c3_case_all_terminate() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Case {
            scrutinee: var(0),
            alts: vec![
                IRAlt {
                    ctor: mk_ctor0(0),
                    body: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
                },
                IRAlt {
                    ctor: mk_ctor0(1),
                    body: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
                },
            ],
            default: Some(Box::new(IRBody::Ret(IRArg::Var(var(0))))),
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert_eq!(r.errors_in(Ext2CheckCategory::ControlFlow), 0);
}

// ── C4: Join point validation ────────────────────────────────────

#[test]
fn test_c4_jp_in_scope_ok() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::JDecl {
            jp: JoinPointId(0),
            params: vec![(var(1), IRType::Object)],
            body: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
            rest: Box::new(IRBody::Jmp {
                jp: JoinPointId(0),
                args: vec![IRArg::Var(var(0))],
            }),
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert_eq!(r.errors_in(Ext2CheckCategory::JoinPoint), 0);
}

#[test]
fn test_c4_jp_undeclared_error() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Jmp {
            jp: JoinPointId(99),
            args: vec![IRArg::Var(var(0))],
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert!(
        r.errors_in(Ext2CheckCategory::JoinPoint) > 0,
        "undeclared jp should error"
    );
    assert!(r.diagnostics.iter().any(|e| e.msg.contains("jp99")));
}

#[test]
fn test_c4_jp_wrong_arity_error() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::JDecl {
            jp: JoinPointId(0),
            params: vec![(var(1), IRType::Object), (var(2), IRType::Object)],
            body: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
            rest: Box::new(IRBody::Jmp {
                jp: JoinPointId(0),
                args: vec![IRArg::Var(var(0))], // Only 1 arg, expects 2
            }),
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert!(
        r.errors_in(Ext2CheckCategory::JoinPoint) > 0,
        "wrong jp arity should error"
    );
}

// ── C5: Constructor arity ────────────────────────────────────────

#[test]
fn test_c5_ctor_correct_arity_ok() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: IRExpr::Ctor {
                info: mk_ctor(0, vec![IRType::Object]),
                args: vec![IRArg::Var(var(0))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert_eq!(r.errors_in(Ext2CheckCategory::CtorArity), 0);
}

#[test]
fn test_c5_ctor_wrong_arity_error() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: IRExpr::Ctor {
                info: mk_ctor(0, vec![IRType::Object, IRType::Object]),
                args: vec![IRArg::Var(var(0))], // 1 arg, 2 fields
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert!(r.errors_in(Ext2CheckCategory::CtorArity) > 0);
}

#[test]
fn test_c5_reuse_wrong_arity_error() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: IRExpr::Reuse {
                var: var(0),
                ctor: mk_ctor(0, vec![IRType::Object, IRType::Object, IRType::Object]),
                args: vec![IRArg::Var(var(0))], // 1 arg, 3 fields
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert!(r.errors_in(Ext2CheckCategory::CtorArity) > 0);
}

// ── C6: Closure arity ────────────────────────────────────────────

#[test]
fn test_c6_partial_apply_correct_ok() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: IRExpr::PartialApply {
                fn_id: FnId(name("target")),
                arity: 3,
                args: vec![IRArg::Var(var(0))], // 1 < 3
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert_eq!(r.errors_in(Ext2CheckCategory::ClosureArity), 0);
}

#[test]
fn test_c6_partial_apply_too_many_args_error() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: IRExpr::PartialApply {
                fn_id: FnId(name("target")),
                arity: 1,
                args: vec![IRArg::Var(var(0))], // 1 >= 1
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert!(r.errors_in(Ext2CheckCategory::ClosureArity) > 0);
}

#[test]
fn test_c6_closure_apply_with_args_ok() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(2),
            ty: IRType::Object,
            value: IRExpr::ClosureApply {
                closure: IRArg::Var(var(0)),
                args: vec![IRArg::Var(var(1))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(2)))),
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert_eq!(r.errors_in(Ext2CheckCategory::ClosureArity), 0);
}

#[test]
fn test_c6_closure_apply_zero_args_error() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: IRExpr::ClosureApply {
                closure: IRArg::Var(var(0)),
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert!(r.errors_in(Ext2CheckCategory::ClosureArity) > 0);
}

// ── C7: Scoped type tracking ─────────────────────────────────────

#[test]
fn test_c7_consistent_type_ok() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::UInt64)],
        return_type: IRType::UInt64,
        body: IRBody::VDecl {
            var: var(1),
            ty: IRType::UInt64,
            value: IRExpr::Lit(IRLiteral::UInt64(42)),
            rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert_eq!(r.errors_in(Ext2CheckCategory::ScopedType), 0);
}

#[test]
fn test_c7_type_redeclaration_mismatch_error() {
    // var(0) declared as UInt64 in params, then re-declared as Object in VDecl
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::UInt64)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(0),
            ty: IRType::Object,
            value: IRExpr::String("hello".into()),
            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert!(
        r.errors_in(Ext2CheckCategory::ScopedType) > 0,
        "type mismatch on redecl"
    );
}

// ── C8: Type erasure validation ──────────────────────────────────

#[test]
fn test_c8_box_erased_error() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(0),
            ty: IRType::Object,
            value: IRExpr::Box {
                ty: IRType::UInt64,
                arg: IRArg::Erased,
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert!(
        r.errors_in(Ext2CheckCategory::Erasure) > 0,
        "Box(Erased) should error"
    );
}

#[test]
fn test_c8_set_erased_value_error() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Erased)],
        return_type: IRType::Object,
        body: IRBody::Set {
            var: var(0),
            idx: 0,
            value: var(1),
            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert!(
        r.errors_in(Ext2CheckCategory::Erasure) > 0,
        "Set with Erased value should error"
    );
}

#[test]
fn test_c8_case_erased_scrutinee_error() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Erased)],
        return_type: IRType::Erased,
        body: IRBody::Case {
            scrutinee: var(0),
            alts: vec![IRAlt {
                ctor: mk_ctor0(0),
                body: Box::new(IRBody::Ret(IRArg::Erased)),
            }],
            default: None,
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert!(
        r.errors_in(Ext2CheckCategory::Erasure) > 0,
        "erased scrutinee should error"
    );
}

#[test]
fn test_c8_set_non_erased_ok() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Set {
            var: var(0),
            idx: 0,
            value: var(1),
            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert_eq!(r.errors_in(Ext2CheckCategory::Erasure), 0);
}

#[test]
fn test_c8_uset_erased_value_error() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Erased)],
        return_type: IRType::Object,
        body: IRBody::USet {
            var: var(0),
            idx: 0,
            value: var(1),
            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert!(
        r.errors_in(Ext2CheckCategory::Erasure) > 0,
        "USet with Erased value should error"
    );
}

#[test]
fn test_c8_sset_erased_value_error() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Erased)],
        return_type: IRType::Object,
        body: IRBody::SSet {
            var: var(0),
            n: 0,
            offset: 0,
            value: var(1),
            ty: IRType::UInt32,
            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert!(
        r.errors_in(Ext2CheckCategory::Erasure) > 0,
        "SSet with Erased value should error"
    );
}

// ── C9: Exhaustiveness ───────────────────────────────────────────

#[test]
fn test_c9_complete_coverage_ok() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Case {
            scrutinee: var(0),
            alts: vec![
                IRAlt {
                    ctor: mk_ctor0(0),
                    body: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
                },
                IRAlt {
                    ctor: mk_ctor0(1),
                    body: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
                },
            ],
            default: None,
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert_eq!(r.errors_in(Ext2CheckCategory::Exhaustiveness), 0);
}

#[test]
fn test_c9_gap_in_tags_error() {
    // tags 0 and 2 but not 1 — max_tag=2 requires 3 alts
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Case {
            scrutinee: var(0),
            alts: vec![
                IRAlt {
                    ctor: mk_ctor0(0),
                    body: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
                },
                IRAlt {
                    ctor: mk_ctor0(2),
                    body: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
                },
            ],
            default: None,
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert!(
        r.errors_in(Ext2CheckCategory::Exhaustiveness) > 0,
        "missing tag 1 should warn"
    );
}

#[test]
fn test_c9_gap_with_default_ok() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Case {
            scrutinee: var(0),
            alts: vec![
                IRAlt {
                    ctor: mk_ctor0(0),
                    body: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
                },
                IRAlt {
                    ctor: mk_ctor0(2),
                    body: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
                },
            ],
            default: Some(Box::new(IRBody::Ret(IRArg::Var(var(0))))),
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert_eq!(
        r.errors_in(Ext2CheckCategory::Exhaustiveness),
        0,
        "default covers gap"
    );
}

#[test]
fn test_c9_single_alt_tag0_ok() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Case {
            scrutinee: var(0),
            alts: vec![IRAlt {
                ctor: mk_ctor0(0),
                body: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
            }],
            default: None,
        },
    };
    let r = check_ir_ext2(&[decl]);
    // tag 0, 1 alt, max_tag+1 = 1 => ok
    assert_eq!(r.errors_in(Ext2CheckCategory::Exhaustiveness), 0);
}

// ── C10: Statistics ──────────────────────────────────────────────

#[test]
fn test_c10_stats_populated() {
    let decl = identity_decl();
    let r = check_ir_ext2(&[decl]);
    assert!(r.total_checks() > 0, "should have performed some checks");
}

#[test]
fn test_c10_empty_program() {
    let r = check_ir_ext2(&[]);
    assert_eq!(r.total_checks(), 0);
    assert!(!r.has_errors());
}

#[test]
fn test_c10_error_count_matches() {
    // Create a decl with known errors: inc on scalar + ctor arity mismatch
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::UInt64)],
        return_type: IRType::Object,
        body: IRBody::Inc {
            var: var(0),
            n: 1,
            rest: Box::new(IRBody::VDecl {
                var: var(1),
                ty: IRType::Object,
                value: IRExpr::Ctor {
                    info: mk_ctor(0, vec![IRType::Object, IRType::Object]),
                    args: vec![IRArg::Var(var(0))],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
            }),
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert!(
        r.error_count() >= 2,
        "at least operand type + ctor arity errors"
    );
    assert!(r.errors_in(Ext2CheckCategory::OperandType) > 0);
    assert!(r.errors_in(Ext2CheckCategory::CtorArity) > 0);
}

// ── Integration / edge cases ─────────────────────────────────────

#[test]
fn test_erased_return_ok() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![],
        return_type: IRType::Erased,
        body: IRBody::Ret(IRArg::Erased),
    };
    let r = check_ir_ext2(&[decl]);
    assert!(!r.has_errors());
}

#[test]
fn test_nested_case_checked() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Case {
            scrutinee: var(0),
            alts: vec![IRAlt {
                ctor: mk_ctor0(0),
                body: Box::new(IRBody::Case {
                    scrutinee: var(0),
                    alts: vec![
                        IRAlt {
                            ctor: mk_ctor0(0),
                            body: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
                        },
                        IRAlt {
                            ctor: mk_ctor0(2),
                            body: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
                        },
                    ],
                    default: None,
                }),
            }],
            default: Some(Box::new(IRBody::Ret(IRArg::Var(var(0))))),
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert!(
        r.errors_in(Ext2CheckCategory::Exhaustiveness) > 0,
        "nested case gap"
    );
}

#[test]
fn test_multiple_decls_checked() {
    let decls = vec![
        identity_decl(),
        IRDecl {
            name: name("g"),
            params: vec![(var(0), IRType::Bool)],
            return_type: IRType::Bool,
            body: IRBody::Dec {
                var: var(0),
                rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
            },
        },
    ];
    let r = check_ir_ext2(&decls);
    assert!(
        r.errors_in(Ext2CheckCategory::OperandType) > 0,
        "dec on Bool in second decl"
    );
}

#[test]
fn test_inc_on_erased_no_error() {
    // Erased is allowed for inc/dec (it's a valid no-op at runtime)
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Erased)],
        return_type: IRType::Erased,
        body: IRBody::Inc {
            var: var(0),
            n: 1,
            rest: Box::new(IRBody::Ret(IRArg::Erased)),
        },
    };
    let r = check_ir_ext2(&[decl]);
    assert_eq!(r.errors_in(Ext2CheckCategory::OperandType), 0);
}

#[test]
fn test_result_methods() {
    let r = check_ir_ext2(&[identity_decl()]);
    assert!(!r.has_errors());
    assert_eq!(r.error_count(), 0);
    assert!(r.total_checks() > 0);
}
