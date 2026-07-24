// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the L5IR validity checker.

use super::*;
use crate::ir::{CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRType, JoinPointId, VarId};
use clean_kernel::Name;

fn var(n: u32) -> VarId {
    VarId(n)
}

fn jp(n: u32) -> JoinPointId {
    JoinPointId(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

#[test]
fn test_valid_simple() {
    // let x := 42; ret x
    let decl = IRDecl {
        name: name("test"),
        params: vec![(var(0), IRType::UInt64)],
        return_type: IRType::UInt64,
        body: IRBody::Ret(IRArg::Var(var(0))),
    };

    check_decl(&decl, &[]).expect("simple ret-param decl should be valid");
}

#[test]
fn test_undefined_variable() {
    // ret x (x never defined)
    let body = IRBody::Ret(IRArg::Var(var(0)));
    let decl = IRDecl {
        name: name("test"),
        params: vec![], // No params!
        return_type: IRType::Object,
        body,
    };

    let result = check_decl(&decl, &[]);
    assert!(matches!(result, Err(IRError::UndefinedVariable(VarId(0)))));
}

#[test]
fn test_undefined_join_point() {
    // jmp jp0 (jp0 never declared)
    let decl = IRDecl {
        name: name("test"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Jmp {
            jp: jp(0),
            args: vec![],
        },
    };

    let result = check_decl(&decl, &[]);
    assert!(matches!(
        result,
        Err(IRError::UndefinedJoinPoint(JoinPointId(0)))
    ));
}

#[test]
fn test_jp_arity_mismatch() {
    // jdecl jp0 (x : obj) { ret x }; jmp jp0  -- missing arg
    let decl = IRDecl {
        name: name("test"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::JDecl {
            jp: jp(0),
            params: vec![(var(1), IRType::Object)],
            body: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
            rest: Box::new(IRBody::Jmp {
                jp: jp(0),
                args: vec![], // Missing argument!
            }),
        },
    };

    let result = check_decl(&decl, &[]);
    assert!(matches!(
        result,
        Err(IRError::JoinPointArityMismatch {
            jp: JoinPointId(0),
            expected: 1,
            actual: 0
        })
    ));
}

#[test]
fn test_inc_requires_object() {
    // let x : i32 := 42; inc x; ret x  -- x is scalar
    let decl = IRDecl {
        name: name("test"),
        params: vec![],
        return_type: IRType::UInt64,
        body: IRBody::VDecl {
            var: var(0),
            ty: IRType::UInt64,
            value: IRExpr::Lit(crate::ir::IRLiteral::UInt64(42)),
            rest: Box::new(IRBody::Inc {
                var: var(0),
                n: 1,
                rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
            }),
        },
    };

    let result = check_decl(&decl, &[]);
    assert!(matches!(
        result,
        Err(IRError::TypeMismatch {
            context: "inc requires object type",
            ..
        })
    ));
}

#[test]
fn test_valid_join_point() {
    // jdecl jp0 (x : obj) { ret x }; jmp jp0 y
    let decl = IRDecl {
        name: name("test"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::JDecl {
            jp: jp(0),
            params: vec![(var(1), IRType::Object)],
            body: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
            rest: Box::new(IRBody::Jmp {
                jp: jp(0),
                args: vec![IRArg::Var(var(0))],
            }),
        },
    };

    let result = check_decl(&decl, &[]);
    assert!(result.is_ok(), "Expected Ok, got {:?}", result);
}

#[test]
fn test_ctor_tag_too_large() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(0),
            ty: IRType::Object,
            value: IRExpr::Ctor {
                info: CtorInfo {
                    name: name("Bad.ctor"),
                    tag: 100000, // > MAX_CTOR_TAG
                    num_scalars: 0,
                    num_objects: 0,
                    field_types: vec![],
                },
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        },
    };

    let result = check_decl(&decl, &[]);
    assert!(matches!(result, Err(IRError::CtorTagTooLarge { .. })));
}

#[test]
fn test_valid_inc_dec_object() {
    // Object type is allowed for inc/dec
    let decl = IRDecl {
        name: name("test"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Inc {
            var: var(0),
            n: 1,
            rest: Box::new(IRBody::Dec {
                var: var(0),
                rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
            }),
        },
    };

    check_decl(&decl, &[]).expect("inc+dec on object type should be valid");
}

#[test]
fn test_duplicate_definition() {
    // Defining the same variable twice
    let decl = IRDecl {
        name: name("test"),
        params: vec![],
        return_type: IRType::UInt64,
        body: IRBody::VDecl {
            var: var(0),
            ty: IRType::UInt64,
            value: IRExpr::Lit(crate::ir::IRLiteral::UInt64(1)),
            rest: Box::new(IRBody::VDecl {
                var: var(0), // Duplicate!
                ty: IRType::UInt64,
                value: IRExpr::Lit(crate::ir::IRLiteral::UInt64(2)),
                rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
            }),
        },
    };

    let result = check_decl(&decl, &[]);
    assert!(matches!(result, Err(IRError::DuplicateDefinition(0))));
}

#[test]
fn test_duplicate_join_point() {
    // Defining the same join point twice
    let decl = IRDecl {
        name: name("test"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::JDecl {
            jp: jp(0),
            params: vec![],
            body: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
            rest: Box::new(IRBody::JDecl {
                jp: jp(0), // Duplicate!
                params: vec![],
                body: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
                rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
            }),
        },
    };

    let result = check_decl(&decl, &[]);
    assert!(matches!(result, Err(IRError::DuplicateDefinition(0))));
}

#[test]
fn test_check_decls() {
    let decls = vec![
        IRDecl {
            name: name("foo"),
            params: vec![(var(0), IRType::Object)],
            return_type: IRType::Object,
            body: IRBody::Ret(IRArg::Var(var(0))),
        },
        IRDecl {
            name: name("bar"),
            params: vec![(var(0), IRType::Object)],
            return_type: IRType::Object,
            body: IRBody::VDecl {
                var: var(1),
                ty: IRType::Object,
                value: IRExpr::Apply {
                    fn_id: FnId(name("foo")),
                    args: vec![IRArg::Var(var(0))],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
            },
        },
    ];

    check_decls(&decls).expect("foo+bar cross-call decls should be valid");
}

#[test]
fn test_function_arity_mismatch() {
    let decls = vec![
        IRDecl {
            name: name("add"),
            params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
            return_type: IRType::Object,
            body: IRBody::Ret(IRArg::Var(var(0))),
        },
        IRDecl {
            name: name("test"),
            params: vec![(var(0), IRType::Object)],
            return_type: IRType::Object,
            body: IRBody::VDecl {
                var: var(1),
                ty: IRType::Object,
                value: IRExpr::Apply {
                    fn_id: FnId(name("add")),
                    args: vec![IRArg::Var(var(0))], // Missing one arg!
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
            },
        },
    ];

    let result = check_decls(&decls);
    assert!(matches!(
        result,
        Err(IRError::ArityMismatch {
            expected: 2,
            actual: 1,
            ..
        })
    ));
}

#[test]
fn test_partial_apply_arity_less_than_captured() {
    // PartialApply with arity=1 but 2 captured args -> error
    let decls = vec![
        IRDecl {
            name: name("add"),
            params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
            return_type: IRType::Object,
            body: IRBody::Ret(IRArg::Var(var(0))),
        },
        IRDecl {
            name: name("test"),
            params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
            return_type: IRType::Object,
            body: IRBody::VDecl {
                var: var(2),
                ty: IRType::Object,
                value: IRExpr::PartialApply {
                    fn_id: FnId(name("add")),
                    arity: 1, // Wrong: less than captured count
                    args: vec![IRArg::Var(var(0)), IRArg::Var(var(1))],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(var(2)))),
            },
        },
    ];

    let result = check_decls(&decls);
    assert!(
        matches!(
            result,
            Err(IRError::PartialApplyArityTooSmall {
                arity: 1,
                num_captured: 2,
                ..
            })
        ),
        "Expected PartialApplyArityTooSmall, got {:?}",
        result
    );
}

#[test]
fn test_partial_apply_arity_mismatch_with_decl() {
    // PartialApply with arity=5 but function only has 2 params -> error
    let decls = vec![
        IRDecl {
            name: name("add"),
            params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
            return_type: IRType::Object,
            body: IRBody::Ret(IRArg::Var(var(0))),
        },
        IRDecl {
            name: name("test"),
            params: vec![(var(0), IRType::Object)],
            return_type: IRType::Object,
            body: IRBody::VDecl {
                var: var(2),
                ty: IRType::Object,
                value: IRExpr::PartialApply {
                    fn_id: FnId(name("add")),
                    arity: 5, // Wrong: doesn't match add's 2 params
                    args: vec![IRArg::Var(var(0))],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(var(2)))),
            },
        },
    ];

    let result = check_decls(&decls);
    assert!(
        matches!(
            result,
            Err(IRError::PartialApplyArityMismatch {
                arity: 5,
                expected: 2,
                ..
            })
        ),
        "Expected PartialApplyArityMismatch, got {:?}",
        result
    );
}

#[test]
fn test_valid_partial_apply() {
    // PartialApply with correct arity=2, 1 captured arg -> valid
    let decls = vec![
        IRDecl {
            name: name("add"),
            params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
            return_type: IRType::Object,
            body: IRBody::Ret(IRArg::Var(var(0))),
        },
        IRDecl {
            name: name("test"),
            params: vec![(var(0), IRType::Object)],
            return_type: IRType::Object,
            body: IRBody::VDecl {
                var: var(2),
                ty: IRType::Object,
                value: IRExpr::PartialApply {
                    fn_id: FnId(name("add")),
                    arity: 2,
                    args: vec![IRArg::Var(var(0))],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(var(2)))),
            },
        },
    ];

    check_decls(&decls).expect("valid partial apply should pass");
}

#[test]
fn test_inc_dec_struct_type_valid() {
    // Struct types are object types -- inc/dec should be valid
    let decl = IRDecl {
        name: name("test"),
        params: vec![(var(0), IRType::Struct(vec![IRType::UInt64, IRType::Object]))],
        return_type: IRType::Struct(vec![IRType::UInt64, IRType::Object]),
        body: IRBody::Inc {
            var: var(0),
            n: 1,
            rest: Box::new(IRBody::Dec {
                var: var(0),
                rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
            }),
        },
    };

    check_decl(&decl, &[]).expect("inc+dec on Struct type should be valid");
}

#[test]
fn test_proj_union_type_valid() {
    // Projection on Union type should be accepted (runtime-validated)
    let decl = IRDecl {
        name: name("test"),
        params: vec![(var(0), IRType::Union(vec![IRType::Object, IRType::UInt64]))],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: IRExpr::Proj {
                idx: 0,
                ty: IRType::Object,
                arg: IRArg::Var(var(0)),
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
        },
    };

    check_decl(&decl, &[]).expect("projection on Union type should be valid");
}

// Part of #1963 - Duplicate tags in Case alternatives
#[test]
fn test_duplicate_case_tag() {
    // Case with two alternatives having the same tag -> error
    let decl = IRDecl {
        name: name("test"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Case {
            scrutinee: var(0),
            alts: vec![
                IRAlt {
                    ctor: CtorInfo {
                        name: name("A.mk"),
                        tag: 0,
                        num_scalars: 0,
                        num_objects: 0,
                        field_types: vec![],
                    },
                    body: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
                },
                IRAlt {
                    ctor: CtorInfo {
                        name: name("B.mk"),
                        tag: 0, // Duplicate tag!
                        num_scalars: 0,
                        num_objects: 0,
                        field_types: vec![],
                    },
                    body: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
                },
            ],
            default: None,
        },
    };

    let result = check_decl(&decl, &[]);
    assert!(
        matches!(result, Err(IRError::DuplicateCaseTag { tag: 0 })),
        "Expected DuplicateCaseTag, got {:?}",
        result
    );
}

// Part of #1963 - Distinct tags in Case alternatives pass
#[test]
fn test_distinct_case_tags_valid() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Case {
            scrutinee: var(0),
            alts: vec![
                IRAlt {
                    ctor: CtorInfo {
                        name: name("Nat.zero"),
                        tag: 0,
                        num_scalars: 0,
                        num_objects: 0,
                        field_types: vec![],
                    },
                    body: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
                },
                IRAlt {
                    ctor: CtorInfo {
                        name: name("Nat.succ"),
                        tag: 1,
                        num_scalars: 0,
                        num_objects: 1,
                        field_types: vec![IRType::Object],
                    },
                    body: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
                },
            ],
            default: None,
        },
    };

    check_decl(&decl, &[]).expect("distinct tags should pass");
}

// Part of #1963 - Field count mismatch caught by checker
#[test]
fn test_ctor_field_count_mismatch() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(0),
            ty: IRType::Object,
            value: IRExpr::Ctor {
                info: CtorInfo {
                    name: name("Bad.mk"),
                    tag: 0,
                    num_scalars: 1,
                    num_objects: 2,
                    // field_types has 2 entries but num_scalars + num_objects = 3
                    field_types: vec![IRType::UInt64, IRType::Object],
                },
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        },
    };

    let result = check_decl(&decl, &[]);
    assert!(
        matches!(result, Err(IRError::CtorFieldCountMismatch { .. })),
        "Expected CtorFieldCountMismatch, got {:?}",
        result
    );
}

// Part of #1963 - Consistent field counts pass
// C3 checks args.len() == num_objects (not total fields). Scalar fields
// are written via SSet, not passed as Ctor args. Self-audit W2-727 F1.
#[test]
fn test_ctor_field_count_consistent() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![(var(2), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(0),
            ty: IRType::Object,
            value: IRExpr::Ctor {
                info: CtorInfo {
                    name: name("Pair.mk"),
                    tag: 0,
                    num_scalars: 1,
                    num_objects: 1,
                    field_types: vec![IRType::UInt64, IRType::Object],
                },
                args: vec![IRArg::Var(var(2))], // Only object arg
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        },
    };

    check_decl(&decl, &[]).expect("object-only args should pass C3");
}

// Part of #1953 - Rule C3: Ctor arg count must match field count
#[test]
fn test_ctor_arg_count_mismatch() {
    // Ctor with num_objects=2 but only 1 arg -> error
    let decl = IRDecl {
        name: name("test"),
        params: vec![(var(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(0),
            ty: IRType::Object,
            value: IRExpr::Ctor {
                info: CtorInfo {
                    name: name("Pair.mk"),
                    tag: 0,
                    num_scalars: 0,
                    num_objects: 2,
                    field_types: vec![],
                },
                args: vec![IRArg::Var(var(1))], // Only 1 arg for 2-field ctor
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        },
    };

    let result = check_decl(&decl, &[]);
    assert!(
        matches!(
            result,
            Err(IRError::CtorArgCountMismatch {
                expected: 2,
                num_args: 1,
                ..
            })
        ),
        "Expected CtorArgCountMismatch, got {:?}",
        result
    );
}

// Part of #1953 - Rule T3: Reuse slot must be object type
#[test]
fn test_reuse_slot_requires_object_type() {
    // Reuse with scalar-typed slot -> error
    let decl = IRDecl {
        name: name("test"),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(0),
            ty: IRType::UInt64, // Scalar type -- invalid for Reuse slot
            value: IRExpr::Lit(crate::ir::IRLiteral::UInt64(42)),
            rest: Box::new(IRBody::VDecl {
                var: var(1),
                ty: IRType::Object,
                value: IRExpr::Reuse {
                    var: var(0), // Scalar-typed variable as reuse slot!
                    ctor: CtorInfo {
                        name: name("Unit.unit"),
                        tag: 0,
                        num_scalars: 0,
                        num_objects: 0,
                        field_types: vec![],
                    },
                    args: vec![],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
            }),
        },
    };

    let result = check_decl(&decl, &[]);
    assert!(
        matches!(
            result,
            Err(IRError::TypeMismatch {
                context: "reuse slot",
                ..
            })
        ),
        "Expected TypeMismatch for reuse slot, got {:?}",
        result
    );
}

// Part of #1953 - Rule T3: Reset source must be object type
#[test]
fn test_reset_source_requires_object_type() {
    // Reset on scalar-typed var -> error
    let decl = IRDecl {
        name: name("test"),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(0),
            ty: IRType::UInt64, // Scalar type -- invalid for Reset
            value: IRExpr::Lit(crate::ir::IRLiteral::UInt64(42)),
            rest: Box::new(IRBody::VDecl {
                var: var(1),
                ty: IRType::Object,
                value: IRExpr::Reset(var(0)), // Scalar-typed variable!
                rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
            }),
        },
    };

    let result = check_decl(&decl, &[]);
    assert!(
        matches!(
            result,
            Err(IRError::TypeMismatch {
                context: "reset source",
                ..
            })
        ),
        "Expected TypeMismatch for reset source, got {:?}",
        result
    );
}

// Part of #1953 - Valid Reuse with object-typed slot passes
#[test]
fn test_reuse_valid_object_slot() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: IRExpr::Reset(var(0)),
            rest: Box::new(IRBody::VDecl {
                var: var(2),
                ty: IRType::Object,
                value: IRExpr::Reuse {
                    var: var(1),
                    ctor: CtorInfo {
                        name: name("Nat.succ"),
                        tag: 1,
                        num_scalars: 0,
                        num_objects: 1,
                        field_types: vec![IRType::Object],
                    },
                    args: vec![IRArg::Var(var(0))],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(var(2)))),
            }),
        },
    };

    check_decl(&decl, &[]).expect("valid reuse with object slot should pass");
}

// Part of #1953 - Rule C3: Reuse arg count mismatch
#[test]
fn test_reuse_arg_count_mismatch() {
    // Reuse with num_objects=2 but 3 args -> error
    let decl = IRDecl {
        name: name("test"),
        params: vec![
            (var(0), IRType::Object),
            (var(1), IRType::Object),
            (var(2), IRType::Object),
            (var(3), IRType::Object),
        ],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(10),
            ty: IRType::Object,
            value: IRExpr::Reset(var(0)),
            rest: Box::new(IRBody::VDecl {
                var: var(11),
                ty: IRType::Object,
                value: IRExpr::Reuse {
                    var: var(10),
                    ctor: CtorInfo {
                        name: name("Pair.mk"),
                        tag: 0,
                        num_scalars: 0,
                        num_objects: 2,
                        field_types: vec![],
                    },
                    args: vec![
                        IRArg::Var(var(1)),
                        IRArg::Var(var(2)),
                        IRArg::Var(var(3)), // Extra arg!
                    ],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(var(11)))),
            }),
        },
    };

    let result = check_decl(&decl, &[]);
    assert!(
        matches!(
            result,
            Err(IRError::CtorArgCountMismatch {
                expected: 2,
                num_args: 3,
                ..
            })
        ),
        "Expected CtorArgCountMismatch for Reuse, got {:?}",
        result
    );
}

#[test]
fn test_apply_unknown_function_succeeds_as_external() {
    // Apply to a function not in the declaration list should succeed
    // silently — the checker treats it as an external function call.
    // This documents the O(1) get_decl refactor preserves the find-first
    // fallthrough semantics (Part of #1956).
    let decl = IRDecl {
        name: name("caller"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: FnId(name("unknown_external")),
                args: vec![IRArg::Var(var(0))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
        },
    };

    check_decl(&decl, &[]).expect("call to unknown function should succeed (external tolerance)");
}

// ═══ Rule F1 refinement: saturated-call + clean_apply_N over-application ═══
// (parity with `emit_trust_ir::emit_apply_user` / `emit_c::emit_apply`).

fn ptr_returning_callee() -> IRDecl {
    IRDecl {
        name: name("callee_ptr"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(var(0))),
    }
}

fn caller_with_args(n_args: usize, callee: &str) -> IRDecl {
    let params: Vec<(VarId, IRType)> = (0..n_args as u32)
        .map(|i| (var(i), IRType::Object))
        .collect();
    let args: Vec<IRArg> = (0..n_args as u32).map(|i| IRArg::Var(var(i))).collect();
    IRDecl {
        name: name("caller"),
        params,
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(n_args as u32),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: FnId(name(callee)),
                args,
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(n_args as u32)))),
        },
    }
}

#[test]
fn test_over_applied_apply_on_ptr_returning_callee_is_valid() {
    // The full application spine (3 args for a 1-param callee) is legal IR:
    // the extras apply to the result closure via clean_apply_N.
    let callee = ptr_returning_callee();
    let caller = caller_with_args(3, "callee_ptr");
    let all = vec![callee, caller.clone()];
    check_decl(&caller, &all).expect("over-application onto a Ptr-returning callee is valid IR");
}

#[test]
fn test_over_applied_apply_on_scalar_returning_callee_refused() {
    // A scalar-returning callee has nothing to apply the extras to.
    let callee = IRDecl {
        name: name("callee_scalar"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::UInt64,
        body: IRBody::Ret(IRArg::Var(var(0))),
    };
    let caller = caller_with_args(3, "callee_scalar");
    let all = vec![callee, caller.clone()];
    assert!(matches!(
        check_decl(&caller, &all),
        Err(IRError::ArityMismatch {
            expected: 1,
            actual: 3,
            ..
        })
    ));
}

#[test]
fn test_under_applied_apply_still_refused() {
    let callee = IRDecl {
        name: name("callee_two"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(var(0))),
    };
    let caller = caller_with_args(1, "callee_two");
    let all = vec![callee, caller.clone()];
    assert!(matches!(
        check_decl(&caller, &all),
        Err(IRError::ArityMismatch {
            expected: 2,
            actual: 1,
            ..
        })
    ));
}

// ═══ C2 carrier projections out of an unboxed scalar carrier ═══

fn carrier_decl(body: IRBody) -> IRDecl {
    IRDecl {
        name: name("carrier"),
        params: vec![(var(0), IRType::UInt32)],
        return_type: IRType::Object,
        body,
    }
}

#[test]
fn test_sproj_same_width_out_of_scalar_carrier_is_valid() {
    let decl = IRDecl {
        return_type: IRType::UInt32,
        ..carrier_decl(IRBody::VDecl {
            var: var(1),
            ty: IRType::UInt32,
            value: IRExpr::SProj {
                n: 0,
                offset: 0,
                var: var(0),
                ty: IRType::UInt32,
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
        })
    };
    check_decl(&decl, &[]).expect("same-width sproj out of a scalar carrier is the identity");
}

#[test]
fn test_sproj_width_change_out_of_scalar_carrier_refused() {
    let decl = carrier_decl(IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt8,
        value: IRExpr::SProj {
            n: 0,
            offset: 0,
            var: var(0),
            ty: IRType::UInt8,
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
    });
    assert!(matches!(
        check_decl(&decl, &[]),
        Err(IRError::TypeMismatch {
            context: "sproj source",
            ..
        })
    ));
}

#[test]
fn test_proj_to_object_out_of_scalar_carrier_is_valid_rebox() {
    // `UInt8.toBitVec`-class: object-typed projection re-boxes the carrier.
    let decl = carrier_decl(IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::Proj {
            idx: 0,
            ty: IRType::Object,
            arg: IRArg::Var(var(0)),
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
    });
    check_decl(&decl, &[]).expect("object-typed projection out of a scalar carrier re-boxes");
}

#[test]
fn test_proj_width_change_out_of_scalar_carrier_refused() {
    let decl = carrier_decl(IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: IRExpr::Proj {
            idx: 0,
            ty: IRType::UInt64,
            arg: IRArg::Var(var(0)),
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
    });
    assert!(matches!(
        check_decl(&decl, &[]),
        Err(IRError::TypeMismatch {
            context: "projection target",
            ..
        })
    ));
}

#[test]
fn test_uproj_out_of_u64_class_carrier_is_valid() {
    let decl = IRDecl {
        name: name("carrier64"),
        params: vec![(var(0), IRType::USize)],
        return_type: IRType::USize,
        body: IRBody::VDecl {
            var: var(1),
            ty: IRType::USize,
            value: IRExpr::UProj {
                idx: 0,
                var: var(0),
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
        },
    };
    check_decl(&decl, &[]).expect("uproj out of a UInt64/USize-class carrier is the identity");
}

#[test]
fn test_uproj_out_of_narrow_carrier_refused() {
    let decl = carrier_decl(IRBody::VDecl {
        var: var(1),
        ty: IRType::USize,
        value: IRExpr::UProj {
            idx: 0,
            var: var(0),
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
    });
    assert!(matches!(
        check_decl(&decl, &[]),
        Err(IRError::TypeMismatch {
            context: "uproj source",
            ..
        })
    ));
}
