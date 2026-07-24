// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended borrow inference: escape analysis, alias tracking,
//! and ownership computation.

use super::*;
use crate::ir::{CtorInfo, FnId, IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
use clean_kernel::Name;

fn var(n: u32) -> VarId {
    VarId(n)
}
fn arg_var(n: u32) -> IRArg {
    IRArg::Var(VarId(n))
}
fn name(s: &str) -> Name {
    Name::from_string(s)
}
fn fn_id(s: &str) -> FnId {
    FnId(Name::from_string(s))
}

fn mk_ctor(tag: u32) -> CtorInfo {
    CtorInfo {
        name: name("Ctor"),
        tag,
        num_scalars: 0,
        num_objects: 1,
        field_types: vec![IRType::Object],
    }
}

// ═══════════════════════════════════════════════════════════════════════
// Config tests
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_config_defaults() {
    let config = BorrowInferExtConfig::default();
    assert_eq!(config.max_iterations, 20);
    assert!(config.enable_escape_analysis);
    assert!(config.enable_alias_tracking);
    assert!(config.pessimistic_extern);
}

#[test]
fn test_ownership_default_is_unknown() {
    assert_eq!(Ownership::default(), Ownership::Unknown);
}

// ═══════════════════════════════════════════════════════════════════════
// Escape analysis: ReturnedDirectly
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_escape_returned_directly() {
    let body = IRBody::Ret(arg_var(0));
    let escapes = analyze_escapes(&body, &[var(0)]);
    assert_eq!(escapes.len(), 1);
    assert_eq!(escapes[0], (var(0), EscapeReason::ReturnedDirectly));
}

#[test]
fn test_escape_returned_erased_no_escape() {
    let escapes = analyze_escapes(&IRBody::Ret(IRArg::Erased), &[var(0)]);
    assert!(escapes.is_empty());
}

// ═══════════════════════════════════════════════════════════════════════
// Escape analysis: StoredInCtor
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_escape_stored_in_ctor() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::Ctor {
            info: mk_ctor(0),
            args: vec![arg_var(0)],
        },
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let escapes = analyze_escapes(&body, &[var(0)]);
    assert!(escapes
        .iter()
        .any(|(v, r)| *v == var(0) && *r == EscapeReason::StoredInCtor));
}

#[test]
fn test_escape_stored_in_reuse() {
    let body = IRBody::VDecl {
        var: var(2),
        ty: IRType::Object,
        value: IRExpr::Reuse {
            var: var(0),
            ctor: mk_ctor(0),
            args: vec![arg_var(1)],
        },
        rest: Box::new(IRBody::Ret(arg_var(2))),
    };
    let escapes = analyze_escapes(&body, &[var(0), var(1)]);
    assert!(escapes
        .iter()
        .any(|(v, r)| *v == var(1) && *r == EscapeReason::StoredInCtor));
}

// ═══════════════════════════════════════════════════════════════════════
// Escape analysis: CapturedInClosure
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_escape_captured_in_closure() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::PartialApply {
            fn_id: fn_id("g"),
            arity: 2,
            args: vec![arg_var(0)],
        },
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let escapes = analyze_escapes(&body, &[var(0)]);
    assert!(escapes
        .iter()
        .any(|(v, r)| *v == var(0) && *r == EscapeReason::CapturedInClosure));
}

// ═══════════════════════════════════════════════════════════════════════
// Escape analysis: PassedToExtern (closure apply)
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_escape_closure_apply_extern() {
    let body = IRBody::VDecl {
        var: var(2),
        ty: IRType::Object,
        value: IRExpr::ClosureApply {
            closure: arg_var(0),
            args: vec![arg_var(1)],
        },
        rest: Box::new(IRBody::Ret(arg_var(2))),
    };
    let escapes = analyze_escapes(&body, &[var(0), var(1)]);
    assert!(escapes
        .iter()
        .any(|(v, r)| *v == var(0) && *r == EscapeReason::PassedToExtern));
    assert!(escapes
        .iter()
        .any(|(v, r)| *v == var(1) && *r == EscapeReason::PassedToExtern));
}

// ═══════════════════════════════════════════════════════════════════════
// Escape analysis: PassedOwned
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_escape_passed_to_apply() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::Apply {
            fn_id: fn_id("g"),
            args: vec![arg_var(0)],
        },
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let escapes = analyze_escapes(&body, &[var(0)]);
    assert!(escapes
        .iter()
        .any(|(v, r)| *v == var(0) && *r == EscapeReason::PassedOwned));
}

#[test]
fn test_escape_reset_param() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::Reset(var(0)),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let escapes = analyze_escapes(&body, &[var(0)]);
    assert!(escapes
        .iter()
        .any(|(v, r)| *v == var(0) && *r == EscapeReason::PassedOwned));
}

#[test]
fn test_escape_set_mutates() {
    let body = IRBody::Set {
        var: var(0),
        idx: 0,
        value: var(1),
        rest: Box::new(IRBody::Ret(arg_var(0))),
    };
    let escapes = analyze_escapes(&body, &[var(0), var(1)]);
    assert!(escapes
        .iter()
        .any(|(v, r)| *v == var(0) && *r == EscapeReason::PassedOwned));
    assert!(escapes
        .iter()
        .any(|(v, r)| *v == var(1) && *r == EscapeReason::StoredInCtor));
}

#[test]
fn test_escape_box_stores() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::Box {
            ty: IRType::UInt64,
            arg: arg_var(0),
        },
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let escapes = analyze_escapes(&body, &[var(0)]);
    assert!(escapes
        .iter()
        .any(|(v, r)| *v == var(0) && *r == EscapeReason::StoredInCtor));
}

// ═══════════════════════════════════════════════════════════════════════
// Escape analysis: no escape for read-only operations
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_no_escape_tag_read() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt32,
        value: IRExpr::Tag(arg_var(0)),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    assert!(analyze_escapes(&body, &[var(0)]).is_empty());
}

#[test]
fn test_no_escape_is_shared() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt8,
        value: IRExpr::IsShared(var(0)),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    assert!(analyze_escapes(&body, &[var(0)]).is_empty());
}

#[test]
fn test_no_escape_unbox() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: IRExpr::Unbox {
            ty: IRType::UInt64,
            arg: arg_var(0),
        },
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    assert!(analyze_escapes(&body, &[var(0)]).is_empty());
}

#[test]
fn test_inc_dec_no_escape() {
    let body = IRBody::Inc {
        var: var(0),
        n: 1,
        rest: Box::new(IRBody::Dec {
            var: var(0),
            rest: Box::new(IRBody::Ret(IRArg::Erased)),
        }),
    };
    assert!(analyze_escapes(&body, &[var(0)]).is_empty());
}

// ═══════════════════════════════════════════════════════════════════════
// Alias tracking
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_alias_through_proj() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::Proj {
            idx: 0,
            ty: IRType::Object,
            arg: arg_var(0),
        },
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    assert!(track_aliases(&body).get(&var(0)).unwrap().contains(&var(1)));
}

#[test]
fn test_alias_through_uproj() {
    let body = IRBody::VDecl {
        var: var(2),
        ty: IRType::USize,
        value: IRExpr::UProj {
            idx: 0,
            var: var(0),
        },
        rest: Box::new(IRBody::Ret(arg_var(2))),
    };
    assert!(track_aliases(&body).get(&var(0)).unwrap().contains(&var(2)));
}

#[test]
fn test_alias_through_sproj() {
    let body = IRBody::VDecl {
        var: var(3),
        ty: IRType::UInt8,
        value: IRExpr::SProj {
            n: 0,
            offset: 0,
            var: var(0),
            ty: IRType::UInt8,
        },
        rest: Box::new(IRBody::Ret(arg_var(3))),
    };
    assert!(track_aliases(&body).get(&var(0)).unwrap().contains(&var(3)));
}

#[test]
fn test_no_alias_for_ctor() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::Ctor {
            info: mk_ctor(0),
            args: vec![arg_var(0)],
        },
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    assert!(track_aliases(&body).is_empty());
}

#[test]
fn test_alias_chain() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::Proj {
            idx: 0,
            ty: IRType::Object,
            arg: arg_var(0),
        },
        rest: Box::new(IRBody::VDecl {
            var: var(2),
            ty: IRType::Object,
            value: IRExpr::Proj {
                idx: 0,
                ty: IRType::Object,
                arg: arg_var(1),
            },
            rest: Box::new(IRBody::Ret(arg_var(2))),
        }),
    };
    let aliases = track_aliases(&body);
    assert!(aliases.get(&var(0)).unwrap().contains(&var(1)));
    assert!(aliases.get(&var(1)).unwrap().contains(&var(2)));
}

// ═══════════════════════════════════════════════════════════════════════
// Ownership computation
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_compute_ownership_from_escape() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(arg_var(0)),
    };
    let escapes = vec![(var(0), EscapeReason::ReturnedDirectly)];
    let ownership = compute_param_ownership(&decl, &escapes, &HashMap::new());
    assert_eq!(ownership[0], (var(0), Ownership::Owned));
    assert_eq!(ownership[1], (var(1), Ownership::Unknown));
}

#[test]
fn test_compute_ownership_scalar_always_owned() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::UInt64)],
        return_type: IRType::UInt64,
        body: IRBody::Ret(arg_var(0)),
    };
    let ownership = compute_param_ownership(&decl, &[], &HashMap::new());
    assert_eq!(ownership[0], (var(0), Ownership::Owned));
}

#[test]
fn test_compute_ownership_alias_propagation() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(arg_var(1)),
    };
    let escapes = vec![(var(1), EscapeReason::StoredInCtor)];
    let mut aliases = HashMap::new();
    aliases.insert(var(0), vec![var(1)]);
    let ownership = compute_param_ownership(&decl, &escapes, &aliases);
    assert_eq!(ownership[0], (var(0), Ownership::Owned));
}
