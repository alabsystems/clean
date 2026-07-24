// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the extended IR checker.

use super::ir_checker_ext::*;
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

fn mk_ctor(tag: u32) -> CtorInfo {
    CtorInfo {
        name: name("Test.mk"),
        tag,
        num_scalars: 0,
        num_objects: 0,
        field_types: vec![],
    }
}

fn identity_decl(fn_name: &str) -> IRDecl {
    IRDecl {
        name: name(fn_name),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(var(0))),
    }
}

// ── E1: Type consistency ───────────────────────────────────────────

#[test]
fn test_type_consistency_uint64_literal_correct() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![],
        return_type: IRType::UInt64,
        body: IRBody::VDecl {
            var: var(0),
            ty: IRType::UInt64,
            value: IRExpr::Lit(IRLiteral::UInt64(42)),
            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        },
    };
    let result = check_decls_ext_default(&[decl]);
    assert!(
        !result.has_errors(),
        "correct literal should not produce errors"
    );
}

#[test]
fn test_type_consistency_literal_type_mismatch() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![],
        return_type: IRType::Bool,
        body: IRBody::VDecl {
            var: var(0),
            ty: IRType::Bool,
            value: IRExpr::Lit(IRLiteral::UInt64(42)),
            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        },
    };
    let result = check_decls_ext_default(&[decl]);
    assert!(
        result.has_errors(),
        "UInt64 literal in Bool binding should error"
    );
    assert!(result
        .diagnostics
        .iter()
        .any(|d| d.message.contains("literal")));
}

#[test]
fn test_type_consistency_bool_literal_correct() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![],
        return_type: IRType::Bool,
        body: IRBody::VDecl {
            var: var(0),
            ty: IRType::Bool,
            value: IRExpr::Lit(IRLiteral::Bool(true)),
            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        },
    };
    let result = check_decls_ext_default(&[decl]);
    assert!(!result.has_errors());
}

#[test]
fn test_type_consistency_box_scalar_correct() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(0),
            ty: IRType::UInt64,
            value: IRExpr::Lit(IRLiteral::UInt64(1)),
            rest: Box::new(IRBody::VDecl {
                var: var(1),
                ty: IRType::Object,
                value: IRExpr::Box {
                    ty: IRType::UInt64,
                    arg: IRArg::Var(var(0)),
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
            }),
        },
    };
    let result = check_decls_ext_default(&[decl]);
    assert!(!result.has_errors());
}

#[test]
fn test_type_consistency_box_object_error() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: IRExpr::Box {
                ty: IRType::Object, // Object cannot be boxed
                arg: IRArg::Var(var(0)),
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
        },
    };
    let result = check_decls_ext_default(&[decl]);
    assert!(result.has_errors(), "boxing Object should error");
}

#[test]
fn test_type_consistency_ctor_non_object_binding() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![],
        return_type: IRType::UInt64,
        body: IRBody::VDecl {
            var: var(0),
            ty: IRType::UInt64, // Ctor bound to scalar type
            value: IRExpr::Ctor {
                info: mk_ctor(0),
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        },
    };
    let result = check_decls_ext_default(&[decl]);
    assert!(result.has_errors());
}

#[test]
fn test_type_consistency_string_object_binding() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(0),
            ty: IRType::Object,
            value: IRExpr::String("hello".to_string()),
            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        },
    };
    let result = check_decls_ext_default(&[decl]);
    assert!(!result.has_errors());
}

#[test]
fn test_type_consistency_string_scalar_binding_error() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![],
        return_type: IRType::UInt64,
        body: IRBody::VDecl {
            var: var(0),
            ty: IRType::UInt64, // String bound to scalar
            value: IRExpr::String("hello".to_string()),
            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        },
    };
    let result = check_decls_ext_default(&[decl]);
    assert!(result.has_errors());
}

// ── E2: Variable scope ─────────────────────────────────────────────

#[test]
fn test_scope_variable_in_scope() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![(var(0), IRType::UInt64)],
        return_type: IRType::UInt64,
        body: IRBody::Ret(IRArg::Var(var(0))),
    };
    let result = check_decls_ext_default(&[decl]);
    assert!(!result.has_errors());
}

#[test]
fn test_scope_variable_out_of_scope() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![],
        return_type: IRType::UInt64,
        body: IRBody::Ret(IRArg::Var(var(99))), // Not defined
    };
    let result = check_decls_ext_default(&[decl]);
    assert!(result.has_errors());
    assert!(result.diagnostics.iter().any(|d| d.message.contains("x99")));
}

#[test]
fn test_scope_vdecl_introduces_binding() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![],
        return_type: IRType::UInt64,
        body: IRBody::VDecl {
            var: var(0),
            ty: IRType::UInt64,
            value: IRExpr::Lit(IRLiteral::UInt64(1)),
            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        },
    };
    let result = check_decls_ext_default(&[decl]);
    assert!(!result.has_errors());
}

#[test]
fn test_scope_inc_out_of_scope() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Inc {
            var: var(5), // Not in scope
            n: 1,
            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        },
    };
    let result = check_decls_ext_default(&[decl]);
    assert!(result.has_errors());
    assert!(result.diagnostics.iter().any(|d| d.message.contains("x5")));
}

#[test]
fn test_scope_case_scrutinee_in_scope() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Case {
            scrutinee: var(0),
            alts: vec![IRAlt {
                ctor: mk_ctor(0),
                body: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
            }],
            default: None,
        },
    };
    let result = check_decls_ext_default(&[decl]);
    assert!(!result.has_errors());
}

// ── E3: Function signature validation ──────────────────────────────

#[test]
fn test_signature_apply_correct_arity() {
    let decls = vec![
        IRDecl {
            name: name("callee"),
            params: vec![(var(0), IRType::Object)],
            return_type: IRType::Object,
            body: IRBody::Ret(IRArg::Var(var(0))),
        },
        IRDecl {
            name: name("caller"),
            params: vec![(var(0), IRType::Object)],
            return_type: IRType::Object,
            body: IRBody::VDecl {
                var: var(1),
                ty: IRType::Object,
                value: IRExpr::Apply {
                    fn_id: FnId(name("callee")),
                    args: vec![IRArg::Var(var(0))],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
            },
        },
    ];
    let result = check_decls_ext_default(&decls);
    assert!(
        !result.has_errors(),
        "correct arity should pass: {:?}",
        result.diagnostics
    );
}

#[test]
fn test_signature_apply_wrong_arity() {
    let decls = vec![
        IRDecl {
            name: name("callee"),
            params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
            return_type: IRType::Object,
            body: IRBody::Ret(IRArg::Var(var(0))),
        },
        IRDecl {
            name: name("caller"),
            params: vec![(var(0), IRType::Object)],
            return_type: IRType::Object,
            body: IRBody::VDecl {
                var: var(1),
                ty: IRType::Object,
                value: IRExpr::Apply {
                    fn_id: FnId(name("callee")),
                    args: vec![IRArg::Var(var(0))], // Missing second arg
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
            },
        },
    ];
    let result = check_decls_ext_default(&decls);
    assert!(result.has_errors());
    assert!(result
        .diagnostics
        .iter()
        .any(|d| d.message.contains("callee")));
}

#[test]
fn test_signature_partial_apply_arity_mismatch() {
    let decls = vec![
        IRDecl {
            name: name("target"),
            params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
            return_type: IRType::Object,
            body: IRBody::Ret(IRArg::Var(var(0))),
        },
        IRDecl {
            name: name("caller"),
            params: vec![(var(0), IRType::Object)],
            return_type: IRType::Object,
            body: IRBody::VDecl {
                var: var(1),
                ty: IRType::Object,
                value: IRExpr::PartialApply {
                    fn_id: FnId(name("target")),
                    arity: 5, // Wrong arity
                    args: vec![IRArg::Var(var(0))],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
            },
        },
    ];
    let result = check_decls_ext_default(&decls);
    assert!(result.has_errors());
}

// ── E4: Control flow validation ────────────────────────────────────

#[test]
fn test_control_flow_simple_ret_terminates() {
    let decl = identity_decl("test");
    let result = check_decls_ext_default(&[decl]);
    assert!(!result.has_errors());
}

#[test]
fn test_control_flow_case_all_paths_terminate() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Case {
            scrutinee: var(0),
            alts: vec![
                IRAlt {
                    ctor: mk_ctor(0),
                    body: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
                },
                IRAlt {
                    ctor: mk_ctor(1),
                    body: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
                },
            ],
            default: Some(Box::new(IRBody::Ret(IRArg::Var(var(0))))),
        },
    };
    let result = check_decls_ext_default(&[decl]);
    assert!(!result.has_errors());
}

#[test]
fn test_control_flow_unreachable_terminates() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![],
        return_type: IRType::Void,
        body: IRBody::Unreachable,
    };
    let result = check_decls_ext_default(&[decl]);
    assert!(!result.has_errors());
}

// ── E5: RC balance checking ────────────────────────────────────────

#[test]
fn test_rc_balanced_inc_dec() {
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
    let result = check_decls_ext_default(&[decl]);
    assert!(
        !result.has_warnings(),
        "balanced inc/dec should not warn: {:?}",
        result.diagnostics
    );
}

#[test]
fn test_rc_excessive_dec_warns() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Dec {
            var: var(0),
            rest: Box::new(IRBody::Dec {
                var: var(0),
                rest: Box::new(IRBody::Dec {
                    var: var(0),
                    rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
                }),
            }),
        },
    };
    let result = check_decls_ext_default(&[decl]);
    assert!(result.has_warnings(), "triple dec without inc should warn");
    assert!(result
        .diagnostics
        .iter()
        .any(|d| d.message.contains("RC balance")));
}

#[test]
fn test_rc_inc_only_no_warning() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Inc {
            var: var(0),
            n: 3,
            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        },
    };
    let result = check_decls_ext_default(&[decl]);
    // Positive balance is fine (RC will be decremented by callers)
    assert!(!result.has_warnings());
}

// ── E6: Closure environment validation ─────────────────────────────

#[test]
fn test_closure_env_captured_var_in_scope() {
    let decls = vec![
        IRDecl {
            name: name("target"),
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
                value: IRExpr::PartialApply {
                    fn_id: FnId(name("target")),
                    arity: 2,
                    args: vec![IRArg::Var(var(0))],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
            },
        },
    ];
    let result = check_decls_ext_default(&decls);
    // Should not error because var(0) is a param
    let closure_errors: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.location.context == "closure_env")
        .collect();
    assert!(closure_errors.is_empty(), "captured var is in scope");
}

#[test]
fn test_closure_env_captured_var_out_of_scope() {
    let decls = vec![
        IRDecl {
            name: name("target"),
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
                value: IRExpr::PartialApply {
                    fn_id: FnId(name("target")),
                    arity: 2,
                    args: vec![IRArg::Var(var(99))], // Not in scope
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
            },
        },
    ];
    let result = check_decls_ext_default(&decls);
    assert!(result.has_errors());
    assert!(
        result.diagnostics.iter().any(|d| d.message.contains("x99")),
        "should report out-of-scope captured var"
    );
}

// ── E7: Dead code detection ────────────────────────────────────────

#[test]
fn test_dead_code_uncalled_function() {
    let decls = vec![
        identity_decl("main"),
        identity_decl("helper"), // Never called
    ];
    let result = check_decls_ext_default(&decls);
    let dead_code: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.location.context == "dead_code")
        .collect();
    assert_eq!(dead_code.len(), 1, "one uncalled function");
    assert!(dead_code[0].message.contains("helper"));
    assert_eq!(dead_code[0].severity, Severity::Info);
}

#[test]
fn test_dead_code_called_function_not_flagged() {
    let decls = vec![
        identity_decl("callee"),
        IRDecl {
            name: name("main"),
            params: vec![(var(0), IRType::Object)],
            return_type: IRType::Object,
            body: IRBody::VDecl {
                var: var(1),
                ty: IRType::Object,
                value: IRExpr::Apply {
                    fn_id: FnId(name("callee")),
                    args: vec![IRArg::Var(var(0))],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
            },
        },
    ];
    let result = check_decls_ext_default(&decls);
    let dead_code: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.location.context == "dead_code")
        .collect();
    assert!(
        dead_code.is_empty(),
        "called function should not be flagged"
    );
}

#[test]
fn test_dead_code_empty_program() {
    let result = check_decls_ext_default(&[]);
    assert!(!result.has_errors());
    assert!(result.diagnostics.is_empty());
}

// ── E8: Case completeness ──────────────────────────────────────────

#[test]
fn test_case_empty_no_default_error() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Case {
            scrutinee: var(0),
            alts: vec![],
            default: None,
        },
    };
    let result = check_decls_ext_default(&[decl]);
    assert!(result.has_errors());
    assert!(result
        .diagnostics
        .iter()
        .any(|d| d.message.contains("no alternatives")));
}

#[test]
fn test_case_duplicate_tags_error() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Case {
            scrutinee: var(0),
            alts: vec![
                IRAlt {
                    ctor: mk_ctor(0),
                    body: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
                },
                IRAlt {
                    ctor: mk_ctor(0), // Duplicate tag
                    body: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
                },
            ],
            default: None,
        },
    };
    let result = check_decls_ext_default(&[decl]);
    assert!(result.has_errors());
    assert!(result
        .diagnostics
        .iter()
        .any(|d| d.message.contains("duplicate")));
}

#[test]
fn test_case_distinct_tags_ok() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Case {
            scrutinee: var(0),
            alts: vec![
                IRAlt {
                    ctor: mk_ctor(0),
                    body: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
                },
                IRAlt {
                    ctor: mk_ctor(1),
                    body: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
                },
            ],
            default: None,
        },
    };
    let result = check_decls_ext_default(&[decl]);
    let case_errors: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error && d.location.context == "case")
        .collect();
    assert!(case_errors.is_empty());
}

// ── Diagnostic severity and config ─────────────────────────────────

#[test]
fn test_severity_levels_ordering() {
    assert!(Severity::Info < Severity::Warning);
    assert!(Severity::Warning < Severity::Error);
}

#[test]
fn test_config_disable_scope_check() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![],
        return_type: IRType::UInt64,
        body: IRBody::Ret(IRArg::Var(var(99))), // Out of scope
    };
    let config = ExtCheckerConfig {
        check_scopes: false,
        ..ExtCheckerConfig::default()
    };
    let result = check_decls_ext(&[decl], &config);
    // Scope check disabled, so no scope error
    let scope_errors: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.message.contains("out of scope"))
        .collect();
    assert!(scope_errors.is_empty(), "scope check should be disabled");
}

#[test]
fn test_config_disable_dead_code() {
    let decls = vec![identity_decl("main"), identity_decl("unused")];
    let config = ExtCheckerConfig {
        check_dead_code: false,
        ..ExtCheckerConfig::default()
    };
    let result = check_decls_ext(&decls, &config);
    let dead: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.location.context == "dead_code")
        .collect();
    assert!(dead.is_empty(), "dead code check should be disabled");
}

// ── Edge cases ─────────────────────────────────────────────────────

#[test]
fn test_single_function_program() {
    let decl = identity_decl("main");
    let result = check_decls_ext_default(&[decl]);
    assert!(!result.has_errors());
    assert!(result.diagnostics.is_empty());
}

#[test]
fn test_recursive_function_not_dead() {
    let decl = IRDecl {
        name: name("rec"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: FnId(name("rec")),
                args: vec![IRArg::Var(var(0))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
        },
    };
    let result = check_decls_ext_default(&[decl]);
    let dead: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.location.context == "dead_code")
        .collect();
    assert!(
        dead.is_empty(),
        "self-recursive function should not be dead"
    );
}

#[test]
fn test_result_count_method() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![],
        return_type: IRType::UInt64,
        body: IRBody::Ret(IRArg::Var(var(99))),
    };
    let result = check_decls_ext_default(&[decl]);
    assert!(result.count(Severity::Error) > 0);
    assert_eq!(result.count(Severity::Info), 0);
}

#[test]
fn test_erased_arg_in_scope() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![],
        return_type: IRType::Erased,
        body: IRBody::Ret(IRArg::Erased),
    };
    let result = check_decls_ext_default(&[decl]);
    assert!(!result.has_errors());
}

#[test]
fn test_jdecl_scope_isolation() {
    // Variables declared in a join point body should not leak to the rest.
    let decl = IRDecl {
        name: name("test"),
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
    let result = check_decls_ext_default(&[decl]);
    assert!(
        !result.has_errors(),
        "jdecl with proper scoping should pass"
    );
}

#[test]
fn test_unbox_scalar_type_correct() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::UInt64,
        body: IRBody::VDecl {
            var: var(1),
            ty: IRType::UInt64,
            value: IRExpr::Unbox {
                ty: IRType::UInt64,
                arg: IRArg::Var(var(0)),
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
        },
    };
    let result = check_decls_ext_default(&[decl]);
    assert!(!result.has_errors());
}

#[test]
fn test_unbox_object_type_error() {
    let decl = IRDecl {
        name: name("test"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: IRExpr::Unbox {
                ty: IRType::Object, // Cannot unbox to object
                arg: IRArg::Var(var(0)),
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
        },
    };
    let result = check_decls_ext_default(&[decl]);
    assert!(result.has_errors());
}
