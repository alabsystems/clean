// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for type class outParam detection, resolution, and propagation.

use super::*;
use crate::instances::{InstanceTable, DEFAULT_PRIORITY};
use clean_kernel::expr::{BinderData, BinderInfo, Expr, ExprKind, FVarId};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::Environment;

// -- Helpers --

fn n(s: &str) -> Name {
    Name::from_string(s)
}
fn c(s: &str) -> Expr {
    Expr::const_(n(s), vec![])
}

/// HAdd with 3 params: α, β, γ(outParam=2). Instances: Nat+Nat, Int+Int.
fn make_hadd_table() -> InstanceTable {
    let mut t = InstanceTable::new();
    t.register_class_full(n("HAdd"), 3, vec![2], vec![]);

    let hadd_type = |a: &str| Expr::app(Expr::app(Expr::app(c("HAdd"), c(a)), c(a)), c(a));
    t.add_instance(
        n("instHAddNat"),
        n("HAdd"),
        c("instHAddNat"),
        hadd_type("Nat"),
        DEFAULT_PRIORITY,
    );
    t.add_instance(
        n("instHAddInt"),
        n("HAdd"),
        c("instHAddInt"),
        hadd_type("Int"),
        DEFAULT_PRIORITY,
    );
    t
}

/// Add with 1 param, no outParams. Instance: Add Nat.
fn make_add_table() -> InstanceTable {
    let mut t = InstanceTable::new();
    t.register_class(n("Add"), 1, vec![]);
    t.add_instance(
        n("instAddNat"),
        n("Add"),
        c("instAddNat"),
        Expr::app(c("Add"), c("Nat")),
        DEFAULT_PRIORITY,
    );
    t
}

/// OfNat with 2 params: α(semiOut=0), n. Instance: OfNat Nat zero.
fn make_semi_table() -> InstanceTable {
    let mut t = InstanceTable::new();
    t.register_class_full(n("OfNat"), 2, vec![], vec![0]);
    t.add_instance(
        n("instOfNatNatZero"),
        n("OfNat"),
        c("instOfNatNatZero"),
        Expr::app(Expr::app(c("OfNat"), c("Nat")), c("zero")),
        DEFAULT_PRIORITY,
    );
    t
}

// -- OutParam detection --

#[test]
fn test_detect_out_params_hadd() {
    let env = Environment::new();
    let r = OutParamResolver::with_defaults(&env);
    let out = r.detect_out_params(&n("HAdd"), &make_hadd_table());
    assert_eq!(out.len(), 1);
    assert_eq!(out[0].index, 2);
    assert!(!out[0].is_semi);
}

#[test]
fn test_detect_out_params_none() {
    let env = Environment::new();
    let r = OutParamResolver::with_defaults(&env);
    assert!(r.detect_out_params(&n("Add"), &make_add_table()).is_empty());
}

#[test]
fn test_detect_out_params_unregistered() {
    let env = Environment::new();
    let r = OutParamResolver::with_defaults(&env);
    assert!(r
        .detect_out_params(&n("Unknown"), &InstanceTable::new())
        .is_empty());
}

#[test]
fn test_detect_semi_out_params() {
    let env = Environment::new();
    let r = OutParamResolver::with_defaults(&env);
    let out = r.detect_out_params(&n("OfNat"), &make_semi_table());
    assert_eq!(out.len(), 1);
    assert_eq!(out[0].index, 0);
    assert!(out[0].is_semi);
}

#[test]
fn test_detect_semi_disabled() {
    let env = Environment::new();
    let cfg = OutParamConfig {
        semi_outparam_enabled: false,
        ..Default::default()
    };
    let r = OutParamResolver::new(&env, cfg);
    assert!(r
        .detect_out_params(&n("OfNat"), &make_semi_table())
        .is_empty());
}

// -- Type-level detection (outParam/semiOutParam wrapper) --

#[test]
fn test_is_out_param_type_positive() {
    assert!(is_out_param_type(&Expr::app(c("outParam"), c("Type"))));
}

#[test]
fn test_is_out_param_type_lean_prefixed() {
    assert!(is_out_param_type(&Expr::app(c("Lean.outParam"), c("Type"))));
}

#[test]
fn test_is_out_param_type_negative() {
    assert!(!is_out_param_type(&c("Nat")));
}

#[test]
fn test_is_semi_out_param_type() {
    assert!(is_semi_out_param_type(&Expr::app(
        c("semiOutParam"),
        c("Type")
    )));
}

#[test]
fn test_unwrap_out_param_wrapped() {
    let ty = Expr::app(c("outParam"), c("Type"));
    let inner = unwrap_out_param(&ty).expect("should unwrap outParam");
    assert!(matches!(inner.kind(), ExprKind::Const(name, _) if name.to_string() == "Type"));
}

#[test]
fn test_unwrap_out_param_not_wrapped() {
    assert!(unwrap_out_param(&c("Nat")).is_none());
}

#[test]
fn test_unwrap_semi_out_param() {
    assert!(unwrap_out_param(&Expr::app(c("semiOutParam"), c("Type"))).is_some());
}

// -- OutParam resolution --

#[test]
fn test_resolve_hadd_nat() {
    let env = Environment::new();
    let r = OutParamResolver::with_defaults(&env);
    let t = make_hadd_table();
    let goal = vec![c("Nat"), c("Nat"), Expr::fvar(FVarId::new(0))];

    match r.resolve_out_params(&n("HAdd"), &goal, &t, 0) {
        OutParamResult::Resolved(sols) => {
            assert_eq!(sols.len(), 1);
            assert_eq!(sols[0].0, 2);
            assert!(matches!(sols[0].1.kind(), ExprKind::Const(name, _) if *name == n("Nat")));
        }
        other => panic!("Expected Resolved, got {other:?}"),
    }
}

#[test]
fn test_resolve_hadd_int() {
    let env = Environment::new();
    let r = OutParamResolver::with_defaults(&env);
    let t = make_hadd_table();
    let goal = vec![c("Int"), c("Int"), Expr::fvar(FVarId::new(0))];

    match r.resolve_out_params(&n("HAdd"), &goal, &t, 0) {
        OutParamResult::Resolved(sols) => {
            assert_eq!(sols.len(), 1);
            assert_eq!(sols[0].0, 2);
            assert!(matches!(sols[0].1.kind(), ExprKind::Const(name, _) if *name == n("Int")));
        }
        other => panic!("Expected Resolved, got {other:?}"),
    }
}

#[test]
fn test_resolve_no_match() {
    let env = Environment::new();
    let r = OutParamResolver::with_defaults(&env);
    let t = make_hadd_table();
    let goal = vec![c("Bool"), c("Bool"), Expr::fvar(FVarId::new(0))];

    assert!(matches!(
        r.resolve_out_params(&n("HAdd"), &goal, &t, 0),
        OutParamResult::Failed(OutParamError::NoMatchingInstance(_))
    ));
}

#[test]
fn test_resolve_no_outparams_class() {
    let env = Environment::new();
    let r = OutParamResolver::with_defaults(&env);
    let t = make_add_table();

    match r.resolve_out_params(&n("Add"), &[c("Nat")], &t, 0) {
        OutParamResult::Resolved(sols) => assert!(sols.is_empty()),
        other => panic!("Expected Resolved(empty), got {other:?}"),
    }
}

#[test]
fn test_resolve_depth_exceeded() {
    let env = Environment::new();
    let cfg = OutParamConfig {
        max_depth: 2,
        ..Default::default()
    };
    let r = OutParamResolver::new(&env, cfg);
    let t = make_hadd_table();
    let goal = vec![c("Nat"), c("Nat"), Expr::fvar(FVarId::new(0))];

    assert!(matches!(
        r.resolve_out_params(&n("HAdd"), &goal, &t, 3),
        OutParamResult::Failed(OutParamError::MaxDepthExceeded(2))
    ));
}

// -- Ambiguity --

#[test]
fn test_resolve_ambiguous_outparam() {
    let mut t = InstanceTable::new();
    t.register_class_full(n("HMul"), 3, vec![2], vec![]);

    let mk = |out: &str| Expr::app(Expr::app(Expr::app(c("HMul"), c("Nat")), c("Nat")), c(out));
    t.add_instance(
        n("inst1"),
        n("HMul"),
        c("inst1"),
        mk("Nat"),
        DEFAULT_PRIORITY,
    );
    t.add_instance(
        n("inst2"),
        n("HMul"),
        c("inst2"),
        mk("Int"),
        DEFAULT_PRIORITY,
    );

    let env = Environment::new();
    let r = OutParamResolver::with_defaults(&env);
    let goal = vec![c("Nat"), c("Nat"), Expr::fvar(FVarId::new(0))];

    match r.resolve_out_params(&n("HMul"), &goal, &t, 0) {
        OutParamResult::Ambiguous(names) => assert_eq!(names.len(), 2),
        other => panic!("Expected Ambiguous, got {other:?}"),
    }
}

#[test]
fn test_resolve_multiple_agreeing() {
    let mut t = InstanceTable::new();
    t.register_class_full(n("HMul"), 3, vec![2], vec![]);

    let mk = || {
        Expr::app(
            Expr::app(Expr::app(c("HMul"), c("Nat")), c("Nat")),
            c("Nat"),
        )
    };
    t.add_instance(n("inst1"), n("HMul"), c("inst1"), mk(), DEFAULT_PRIORITY);
    t.add_instance(n("inst2"), n("HMul"), c("inst2"), mk(), 50);

    let env = Environment::new();
    let r = OutParamResolver::with_defaults(&env);
    let goal = vec![c("Nat"), c("Nat"), Expr::fvar(FVarId::new(0))];

    match r.resolve_out_params(&n("HMul"), &goal, &t, 0) {
        OutParamResult::Resolved(sols) => {
            assert_eq!(sols.len(), 1);
            assert_eq!(sols[0].0, 2);
        }
        other => panic!("Expected Resolved, got {other:?}"),
    }
}

// -- Propagation --

#[test]
fn test_propagate_basic() {
    let env = Environment::new();
    let r = OutParamResolver::with_defaults(&env);
    let goal = vec![c("Nat"), c("Nat"), Expr::fvar(FVarId::new(0))];
    let sols = vec![(2, c("Nat"))];

    let result = r.propagate_solutions(&goal, &sols);
    assert_eq!(result.len(), 3);
    assert!(matches!(result[2].kind(), ExprKind::Const(name, _) if *name == n("Nat")));
}

#[test]
fn test_propagate_empty() {
    let env = Environment::new();
    let r = OutParamResolver::with_defaults(&env);
    let result = r.propagate_solutions(&[c("Nat")], &[]);
    assert_eq!(result.len(), 1);
}

#[test]
fn test_propagate_out_of_bounds() {
    let env = Environment::new();
    let r = OutParamResolver::with_defaults(&env);
    let result = r.propagate_solutions(&[c("Nat")], &[(5, c("Int"))]);
    assert_eq!(result.len(), 1); // out-of-bounds ignored
}

// -- count_out_params / has_unresolved_out_params --

#[test]
fn test_count_out_params_values() {
    assert_eq!(count_out_params(&n("HAdd"), &make_hadd_table()), 1);
    assert_eq!(count_out_params(&n("Add"), &make_add_table()), 0);
    assert_eq!(count_out_params(&n("X"), &InstanceTable::new()), 0);
}

#[test]
fn test_has_unresolved_fvar() {
    let t = make_hadd_table();
    let goal = vec![c("Nat"), c("Nat"), Expr::fvar(FVarId::new(42))];
    assert!(has_unresolved_out_params(&n("HAdd"), &goal, &t));
}

#[test]
fn test_has_unresolved_all_concrete() {
    let t = make_hadd_table();
    let goal = vec![c("Nat"), c("Nat"), c("Nat")];
    assert!(!has_unresolved_out_params(&n("HAdd"), &goal, &t));
}

#[test]
fn test_has_unresolved_no_class() {
    assert!(!has_unresolved_out_params(
        &n("X"),
        &[],
        &InstanceTable::new()
    ));
}

// -- Binder helpers --

#[test]
fn test_is_inst_implicit_binder() {
    assert!(is_inst_implicit_binder(&BinderData::from(
        BinderInfo::InstImplicit
    )));
    assert!(!is_inst_implicit_binder(&BinderData::from(
        BinderInfo::Default
    )));
    assert!(!is_inst_implicit_binder(&BinderData::from(
        BinderInfo::Implicit
    )));
}

// -- Type expression scanning --

#[test]
fn test_detect_from_type_outparam() {
    let env = Environment::new();
    let r = OutParamResolver::with_defaults(&env);

    // Π α → Π β → Π (outParam Type) → Sort 0
    let ty = Expr::pi(
        BinderInfo::Default,
        Expr::sort(Level::succ(Level::zero())),
        Expr::pi(
            BinderInfo::Default,
            Expr::sort(Level::succ(Level::zero())),
            Expr::pi(
                BinderInfo::Default,
                Expr::app(c("outParam"), Expr::sort(Level::succ(Level::zero()))),
                Expr::sort(Level::zero()),
            ),
        ),
    );

    let out = r.detect_out_params_from_type(&ty);
    assert_eq!(out.len(), 1);
    assert_eq!(out[0].index, 2);
    assert!(!out[0].is_semi);
}

#[test]
fn test_detect_from_type_no_outparam() {
    let env = Environment::new();
    let r = OutParamResolver::with_defaults(&env);
    let ty = Expr::pi(
        BinderInfo::Default,
        Expr::sort(Level::succ(Level::zero())),
        Expr::sort(Level::zero()),
    );
    assert!(r.detect_out_params_from_type(&ty).is_empty());
}

#[test]
fn test_detect_from_type_semi() {
    let env = Environment::new();
    let r = OutParamResolver::with_defaults(&env);
    let ty = Expr::pi(
        BinderInfo::Default,
        Expr::sort(Level::succ(Level::zero())),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(c("semiOutParam"), Expr::sort(Level::succ(Level::zero()))),
            Expr::sort(Level::zero()),
        ),
    );

    let out = r.detect_out_params_from_type(&ty);
    assert_eq!(out.len(), 1);
    assert_eq!(out[0].index, 1);
    assert!(out[0].is_semi);
}

// -- Default instance / config --

#[test]
fn test_select_default_instance_none() {
    let env = Environment::new();
    let r = OutParamResolver::with_defaults(&env);
    assert!(r.select_default_instance(&n("HAdd")).is_none());
}

#[test]
fn test_config_defaults() {
    let cfg = OutParamConfig::default();
    assert_eq!(cfg.max_depth, 32);
    assert!(cfg.allow_default_instances);
    assert!(cfg.semi_outparam_enabled);
}

// -- Error display --

#[test]
fn test_error_display() {
    assert!(format!("{}", OutParamError::UnregisteredClass(n("Foo"))).contains("Foo"));
    assert!(format!("{}", OutParamError::MaxDepthExceeded(32)).contains("32"));
    let e = OutParamError::UnificationFailed {
        instance: n("inst"),
        index: 2,
    };
    let msg = format!("{e}");
    assert!(msg.contains("inst") && msg.contains("2"));
}
