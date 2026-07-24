// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Translation guardrail tests: expression cache, FVar registration, sort inference.

use super::*;

/// Regression test for #452: Cache should use structural equality, not pointer identity.
///
/// This test verifies that cloned Exprs hit the cache even though they have
/// different memory addresses. Before the fix, pointer-based caching could
/// cause cache misses for structurally identical expressions.
#[test]
fn test_expr_cache_structural_equality() {
    let mut backend = AyBackend::new(AyLogic::QfLia);

    // Register FVar before translation (#2129: unregistered FVars are rejected)
    let fvar_id = FVarId::new(42);
    backend.register_fvar_int(fvar_id);

    // Create an expression and translate it
    let expr1 = Expr::fvar(fvar_id);
    let term1 = backend.translate_expr(&expr1).unwrap();

    // Clone the expression - different memory address, same structure
    let expr2 = expr1.clone();

    // Translate the cloned expression - should hit cache
    let term2 = backend.translate_expr(&expr2).unwrap();

    // Both translations should return the same Term
    assert_eq!(
        term1, term2,
        "Cloned Exprs should produce identical Terms via cache"
    );
}

/// Test that unregistered FVars are rejected (#2129 AC1)
#[test]
fn test_unregistered_fvar_rejected() {
    let mut backend = AyBackend::new(AyLogic::QfLia);
    let fvar_id = FVarId::new(99);
    let expr = Expr::fvar(fvar_id);
    let result = backend.translate_expr(&expr);
    assert!(result.is_err(), "Unregistered FVar should be rejected");
}

/// Test that registered FVars use the correct sort (#2129 AC1)
#[test]
fn test_registered_fvar_uses_correct_sort() {
    let mut backend = AyBackend::new(AyLogic::QfLia);
    let fvar_id = FVarId::new(100);
    backend.register_fvar_int(fvar_id);
    let expr = Expr::fvar(fvar_id);
    let term = backend
        .translate_expr(&expr)
        .expect("Registered FVar should translate successfully");
    // Verify the term is usable as an integer by building a satisfiable constraint
    let zero = backend.int_const(0);
    let constraint = backend.gt(term, zero);
    backend.assert_term(constraint);
    assert_eq!(
        backend.check_sat(),
        AySolveResult::Sat,
        "Registered int FVar should be usable in arithmetic constraints"
    );
}

/// Regression (#2255): translate_fvar must preserve the registered sort.
///
/// The stale self-audit fix in db9ff1359 switched `registered_fvars` to a map,
/// but the actual translation bug was that `translate_fvar` still passed
/// `Sort::Int` into `get_or_declare`. An `Int`-only test would miss that bug.
#[test]
fn test_registered_bool_fvar_preserves_registered_sort() {
    let mut backend = AyBackend::new(AyLogic::QfUf);
    let fvar_id = FVarId::new(101);
    backend.register_fvar_bool(fvar_id);

    let term = backend
        .translate_expr(&Expr::fvar(fvar_id))
        .expect("Registered bool FVar should translate successfully");

    assert_eq!(
        backend.solver.term_sort(term.into_inner()),
        Sort::Bool,
        "translate_fvar must keep the registered Bool sort instead of defaulting to Int"
    );
}

/// Regression (#2260): unknown Lean types should register as uninterpreted sorts.
#[test]
fn test_register_fvar_from_unknown_lean_type_uses_uninterpreted_sort() {
    use clean_kernel::name::Name;

    let mut backend = AyBackend::new(AyLogic::QfUf);
    let fvar_id = FVarId::new(102);
    let opaque_ty = Expr::const_(Name::from_string("MyOpaqueType"), vec![]);
    backend
        .register_fvar_from_lean_type(fvar_id, &opaque_ty)
        .expect("opaque type should register as uninterpreted");

    let term = backend
        .translate_expr(&Expr::fvar(fvar_id))
        .expect("FVar registered from an unknown Lean type should translate");

    assert_eq!(
        backend.solver.term_sort(term.into_inner()),
        Sort::Uninterpreted("MyOpaqueType".to_string()),
        "register_fvar_from_lean_type should preserve unknown Lean types as uninterpreted sorts"
    );
}

/// Test that unknown expression kinds are rejected (#2129 AC2)
#[test]
fn test_unknown_expr_kind_rejected() {
    let mut backend = AyBackend::new(AyLogic::QfLia);
    // BVar is unsupported in SMT translation
    let expr = Expr::bvar(0);
    let result = backend.translate_expr(&expr);
    assert!(result.is_err(), "BVar should be rejected");
}

/// Test that unknown constants are rejected (#2129 AC2)
#[test]
fn test_unknown_constant_rejected() {
    use clean_kernel::Name;
    let mut backend = AyBackend::new(AyLogic::QfLia);
    let expr = Expr::const_(Name::from_string("UnknownThing"), vec![]);
    let result = backend.translate_expr(&expr);
    assert!(result.is_err(), "Unknown constant should be rejected");
}

/// Test that known boolean constants still work (#2129 AC2)
#[test]
fn test_known_constants_still_work() {
    use clean_kernel::Name;
    let mut backend = AyBackend::new(AyLogic::QfLia);

    let true_expr = Expr::const_(Name::from_string("True"), vec![]);
    let true_term = backend
        .translate_expr(&true_expr)
        .expect("True should translate");

    let false_expr = Expr::const_(Name::from_string("False"), vec![]);
    let false_term = backend
        .translate_expr(&false_expr)
        .expect("False should translate");

    // True and False must translate to distinct boolean terms
    assert_ne!(
        true_term, false_term,
        "True and False should translate to different Ay terms"
    );
}

/// Regression (#2261): MData-wrapped Lean types should be recognized by infer_sort_from_lean_type.
///
/// Without MData stripping, `MData(_, Const("Nat"))` falls to `Sort::Uninterpreted`
/// instead of `Sort::Int`, causing sort mismatches in SMT formulas.
#[test]
fn test_infer_sort_mdata_wrapped_types() {
    use clean_kernel::name::Name;
    use clean_kernel::{Expr, MDataValue};

    let metadata = vec![(Name::from_string("simp"), MDataValue::Bool(true))];

    // Bare Nat → Sort::Int
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    assert_eq!(infer_sort_from_lean_type(&nat).unwrap(), Sort::Int);

    // MData-wrapped Nat → should also be Sort::Int
    let mdata_nat = Expr::mdata(metadata.clone(), nat);
    assert_eq!(
        infer_sort_from_lean_type(&mdata_nat).unwrap(),
        Sort::Int,
        "MData-wrapped Nat should infer as Sort::Int"
    );

    // MData-wrapped Bool → Sort::Bool
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let mdata_bool = Expr::mdata(metadata, bool_ty);
    assert_eq!(
        infer_sort_from_lean_type(&mdata_bool).unwrap(),
        Sort::Bool,
        "MData-wrapped Bool should infer as Sort::Bool"
    );
}

// -- Rat → Sort::Real mapping (#3367) --

/// `infer_sort_from_lean_type` maps Lean `Rat` to SMT `Sort::Real`.
///
/// SMT-LIB's Real sort models the rationals (dense ordered field without
/// completeness), so Lean's `Rat` is a sound mapping. This unblocks SMT proof
/// automation for gamma-crown axioms involving rational arithmetic.
#[test]
fn test_infer_sort_rat_maps_to_real() {
    use clean_kernel::name::Name;

    let rat_ty = Expr::const_(Name::from_string("Rat"), vec![]);
    let sort = infer_sort_from_lean_type(&rat_ty).expect("Rat should be a recognized type");
    assert_eq!(sort, Sort::Real, "Lean Rat must map to SMT Sort::Real");
}

/// `infer_sort_from_lean_type` maps App-wrapped `Rat` to `Sort::Real`.
#[test]
fn test_infer_sort_rat_app_maps_to_real() {
    use clean_kernel::name::Name;

    // Simulate an App-wrapped Rat type (e.g. from a type application)
    let rat_head = Expr::const_(Name::from_string("Rat"), vec![]);
    let dummy_arg = Expr::const_(Name::from_string("Unit"), vec![]);
    let app_rat = Expr::app(rat_head, dummy_arg);
    let sort = infer_sort_from_lean_type(&app_rat).expect("App Rat should be a recognized type");
    assert_eq!(
        sort,
        Sort::Real,
        "App-wrapped Lean Rat must map to SMT Sort::Real"
    );
}

/// `register_fvar_from_lean_type` accepts Rat and registers as Real sort.
#[test]
fn test_register_fvar_rat_type_uses_real_sort() {
    use clean_kernel::name::Name;

    let mut backend = AyBackend::new(AyLogic::QfLra);
    let fvar_id = FVarId::new(300);
    let rat_ty = Expr::const_(Name::from_string("Rat"), vec![]);
    backend
        .register_fvar_from_lean_type(fvar_id, &rat_ty)
        .expect("Rat type should register successfully");

    let term = backend
        .translate_expr(&Expr::fvar(fvar_id))
        .expect("FVar registered from Rat should translate");

    assert_eq!(
        backend.solver.term_sort(term.into_inner()),
        Sort::Real,
        "FVar registered from Lean Rat must have SMT Sort::Real"
    );
}

// -- Domain-mismatch rejection regressions (#2849) --

/// `infer_sort_from_lean_type` must reject UInt*, USize, and Float (#2849 AC1-AC2, #2852).
#[test]
fn test_infer_sort_rejects_unsound_domain_types() {
    use clean_kernel::name::Name;

    for name in ["UInt8", "UInt16", "UInt32", "UInt64", "USize", "Float"] {
        let ty = Expr::const_(Name::from_string(name), vec![]);
        let result = infer_sort_from_lean_type(&ty);
        assert!(
            result.is_err(),
            "{name} must be rejected by infer_sort_from_lean_type, not widened"
        );
    }
}

/// `reject_unsound_domain_ty` must reject UInt*, USize, and Float from Expr (#2852).
#[test]
fn test_reject_unsound_domain_ty_rejects_unsound_types() {
    use super::super::reject_unsound_domain_ty;
    use clean_kernel::name::Name;

    for name in ["UInt8", "UInt16", "UInt32", "UInt64", "USize", "Float"] {
        let ty = Expr::const_(Name::from_string(name), vec![]);
        let result = reject_unsound_domain_ty(&ty);
        assert!(
            result.is_err(),
            "reject_unsound_domain_ty must reject {name}"
        );
        let err_msg = result.unwrap_err().to_string();
        assert!(
            err_msg.contains(name),
            "error message should mention the type name {name}, got: {err_msg}"
        );
    }

    // Safe types must pass
    for name in ["Nat", "Int", "Real", "Rat", "Bool"] {
        let ty = Expr::const_(Name::from_string(name), vec![]);
        let result = reject_unsound_domain_ty(&ty);
        assert!(
            result.is_ok(),
            "reject_unsound_domain_ty must accept {name}"
        );
    }
}

/// `reject_unsound_domain_ty` must handle MData-wrapped unsound types (#2852).
#[test]
fn test_reject_unsound_domain_ty_strips_mdata() {
    use super::super::reject_unsound_domain_ty;
    use clean_kernel::name::Name;

    let inner = Expr::const_(Name::from_string("UInt32"), vec![]);
    let mdata = Expr::mdata(vec![], inner);
    let result = reject_unsound_domain_ty(&mdata);
    assert!(
        result.is_err(),
        "reject_unsound_domain_ty must reject MData-wrapped UInt32"
    );
}

/// `register_fvar_from_lean_type` must reject UInt*, USize, and Float (#2849 AC3, #2852).
#[test]
fn test_register_fvar_rejects_unsound_domain_types() {
    use clean_kernel::name::Name;

    for name in ["UInt8", "UInt16", "UInt32", "UInt64", "USize", "Float"] {
        let mut backend = AyBackend::new(AyLogic::QfLia);
        let fvar_id = FVarId::new(200);
        let ty = Expr::const_(Name::from_string(name), vec![]);
        let result = backend.register_fvar_from_lean_type(fvar_id, &ty);
        assert!(
            result.is_err(),
            "register_fvar_from_lean_type must reject {name}"
        );
    }
}
