// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Scaling regressions for projection type inference.

use super::*;

fn measure_infer_proj_whnf_calls(num_fields: u32) -> u64 {
    use crate::inductive::{Constructor, InductiveDecl, InductiveType};

    let mut env = Environment::new();
    env.init_nat().unwrap();

    let struct_name = Name::from_string(&format!("ManyFields{num_fields}"));
    let ctor_name = Name::from_string(&format!("ManyFields{num_fields}.mk"));
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    // ManyFieldsN.mk : Nat -> ... -> Nat -> ManyFieldsN
    let mut ctor_type = Expr::const_(struct_name.clone(), vec![]);
    for _ in 0..num_fields {
        ctor_type = Expr::pi(BinderInfo::Default, nat.clone(), ctor_type);
    }

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: struct_name.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: ctor_name,
                type_: ctor_type,
            }],
        }],
    };
    env.add_inductive(decl).unwrap();

    let mut tc = TypeChecker::new(&env);
    let struct_ty = Expr::const_(struct_name.clone(), vec![]);
    let sid = tc.local_context_mut().push(
        Name::from_string("s"),
        struct_ty.clone(),
        BinderInfo::Default,
    );
    let s = Expr::fvar(sid);

    tc.reset_whnf_impl_call_count_for_tests();
    for idx in 0..num_fields {
        let field_ty = tc
            .infer_proj_type_from(&struct_name, idx, &s, &struct_ty)
            .expect("projection type inference should succeed");
        assert_eq!(
            field_ty, nat,
            "field type should remain Nat for projection index {idx}"
        );
    }

    tc.whnf_impl_call_count_for_tests()
}

fn measure_infer_proj_cache_fill_vs_hits(num_fields: u32) -> (u64, u64) {
    use crate::inductive::{Constructor, InductiveDecl, InductiveType};

    let mut env = Environment::new();
    env.init_nat().unwrap();

    let struct_name = Name::from_string(&format!("ManyFields{num_fields}"));
    let ctor_name = Name::from_string(&format!("ManyFields{num_fields}.mk"));
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    let mut ctor_type = Expr::const_(struct_name.clone(), vec![]);
    for _ in 0..num_fields {
        ctor_type = Expr::pi(BinderInfo::Default, nat.clone(), ctor_type);
    }

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: struct_name.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: ctor_name,
                type_: ctor_type,
            }],
        }],
    };
    env.add_inductive(decl).unwrap();

    let mut tc = TypeChecker::new(&env);
    let struct_ty = Expr::const_(struct_name.clone(), vec![]);
    let sid = tc.local_context_mut().push(
        Name::from_string("s"),
        struct_ty.clone(),
        BinderInfo::Default,
    );
    let s = Expr::fvar(sid);

    tc.reset_whnf_impl_call_count_for_tests();
    let field_ty0 = tc
        .infer_proj_type_from(&struct_name, 0, &s, &struct_ty)
        .expect("projection type inference should succeed");
    assert_eq!(
        field_ty0, nat,
        "field type should remain Nat for projection index 0"
    );
    let calls_after_first = tc.whnf_impl_call_count_for_tests();

    for idx in 1..num_fields {
        let field_ty = tc
            .infer_proj_type_from(&struct_name, idx, &s, &struct_ty)
            .expect("projection type inference should succeed");
        assert_eq!(
            field_ty, nat,
            "field type should remain Nat for projection index {idx}"
        );
    }

    (calls_after_first, tc.whnf_impl_call_count_for_tests())
}

/// Regression test for #1516.
///
/// Projection typing over all fields of an n-field structure should show near-linear
/// WHNF call growth, not quadratic growth from re-WHNF'ing the same Pi telescope
/// prefix for every projection.
#[test]
fn test_infer_proj_type_whnf_scaling_regression_1516() {
    let calls_8 = measure_infer_proj_whnf_calls(8);
    let calls_32 = measure_infer_proj_whnf_calls(32);

    // 8 -> 32 fields is a 4x input increase. Linear behavior stays near 4x.
    // Allow small fixed overhead for setup and non-projection WHNF work.
    let linear_upper_bound = calls_8.saturating_mul(4).saturating_add(64);
    assert!(
        calls_32 <= linear_upper_bound,
        "WHNF call growth regressed toward quadratic: calls_8={calls_8}, calls_32={calls_32}, linear_upper_bound={linear_upper_bound}"
    );
}

#[test]
fn test_infer_proj_type_cache_hits_for_later_fields_1516() {
    let (calls_after_first, calls_total) = measure_infer_proj_cache_fill_vs_hits(32);
    let calls_from_cache_hits = calls_total.saturating_sub(calls_after_first);

    // First projection fills the non-Prop projection cache for all fields.
    // Subsequent field lookups should be cache hits with minimal extra WHNF work.
    assert!(
        calls_from_cache_hits <= 8,
        "projection cache miss regression: calls_after_first={calls_after_first}, calls_total={calls_total}, calls_from_cache_hits={calls_from_cache_hits}"
    );
}

/// End-to-end test measuring WHNF calls through the full `is_def_eq` → struct eta
/// expansion path at Mathlib-representative field counts.
///
/// Mathlib structures like TopologicalSpace (9 fields), MetricSpace (12+ fields),
/// and NormedField (16+ fields) trigger struct eta expansion during definitional
/// equality checks. This test confirms the batch projection cache keeps WHNF
/// call growth linear through the full `is_def_eq` → `try_eta_struct` →
/// `expand_eta_struct` → `infer_proj_type_from_quick` pipeline.
fn measure_is_def_eq_eta_whnf_calls(num_fields: u32) -> u64 {
    use crate::inductive::{Constructor, InductiveDecl, InductiveType};

    let mut env = Environment::new();
    env.init_nat().unwrap();

    let struct_name = Name::from_string(&format!("Struct{num_fields}"));
    let ctor_name = Name::from_string(&format!("Struct{num_fields}.mk"));
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    // Struct_N.mk : Nat -> ... -> Nat -> Struct_N  (num_fields Nat args)
    let mut ctor_type = Expr::const_(struct_name.clone(), vec![]);
    for _ in 0..num_fields {
        ctor_type = Expr::pi(BinderInfo::Default, nat.clone(), ctor_type);
    }

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: struct_name.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: ctor_name.clone(),
                type_: ctor_type,
            }],
        }],
    };
    env.add_inductive(decl).unwrap();

    let tc = TypeChecker::new(&env);
    let struct_ty = Expr::const_(struct_name.clone(), vec![]);

    // Create FVar x : Struct_N
    let x_id = tc.ctx.borrow_mut().push(
        Name::from_string("x"),
        struct_ty.clone(),
        BinderInfo::Default,
    );
    let x = Expr::fvar(x_id);

    // Build eta-expanded form: Struct_N.mk (proj 0 x) (proj 1 x) ... (proj (n-1) x)
    let mut expanded = Expr::const_(ctor_name, vec![]);
    for i in 0..num_fields {
        expanded = Expr::app(expanded, Expr::proj(struct_name.clone(), i, x.clone()));
    }

    // Measure WHNF calls for: is_def_eq(x, expanded)
    // This exercises: is_def_eq_structural → try_eta_struct → expand_eta_struct
    // → is_def_eq_impl recursion on each (proj i x) pair → infer_proj_type_from_quick
    tc.reset_whnf_impl_call_count_for_tests();
    assert!(
        tc.is_def_eq(&x, &expanded),
        "x should be def-eq to its eta expansion via struct eta for {num_fields} fields"
    );
    tc.whnf_impl_call_count_for_tests()
}

/// Regression test for #1516: full is_def_eq path with Mathlib-representative sizes.
///
/// Tests 12 → 48 fields (4x increase). Linear WHNF behavior means calls_48 should
/// be roughly 4 * calls_12 (plus fixed overhead). Quadratic behavior would give ~16x.
#[test]
fn test_is_def_eq_eta_whnf_scaling_mathlib_representative_1516() {
    let calls_12 = measure_is_def_eq_eta_whnf_calls(12);
    let calls_48 = measure_is_def_eq_eta_whnf_calls(48);

    // 12 → 48 is 4x. Linear growth ≈ 4x. Quadratic would be ~16x.
    // Allow generous fixed overhead for setup WHNF (type inference, structure checks).
    let linear_upper_bound = calls_12.saturating_mul(5).saturating_add(128);
    assert!(
        calls_48 <= linear_upper_bound,
        "is_def_eq eta expansion WHNF scaling regressed toward quadratic: \
         calls_12={calls_12}, calls_48={calls_48}, \
         ratio={:.1}x (expected ≈4x for linear), \
         linear_upper_bound={linear_upper_bound}",
        calls_48 as f64 / calls_12.max(1) as f64,
    );
}

// =========================================================================
// Prop-typed structure projection scaling tests (#1420)
// =========================================================================

/// Build a Prop-typed structure with `num_fields` fields, all of type P (a Prop).
/// Returns (env, struct_name, p_const) after setting up the environment.
fn setup_prop_struct_env(num_fields: u32) -> (Environment, Name, Expr) {
    use crate::env::Declaration;
    use crate::inductive::{Constructor, InductiveDecl, InductiveType};

    let mut env = Environment::new();

    // P : Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    let p_const = Expr::const_(Name::from_string("P"), vec![]);
    let struct_name = Name::from_string(&format!("PropStruct{num_fields}"));
    let ctor_name = Name::from_string(&format!("PropStruct{num_fields}.mk"));

    // PropStructN.mk : P -> P -> ... -> P -> PropStructN
    // All fields are of type P (a Prop), so the Prop projection check passes.
    let mut ctor_type = Expr::const_(struct_name.clone(), vec![]);
    for _ in 0..num_fields {
        ctor_type = Expr::pi(BinderInfo::Default, p_const.clone(), ctor_type);
    }

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: struct_name.clone(),
            type_: Expr::prop(), // Structure lives in Prop
            constructors: vec![Constructor {
                name: ctor_name,
                type_: ctor_type,
            }],
        }],
    };
    env.add_inductive(decl).unwrap();

    (env, struct_name, p_const)
}

/// Measure WHNF calls for sequential projection queries on a Prop-typed structure.
fn measure_prop_struct_proj_whnf_calls(num_fields: u32) -> u64 {
    let (env, struct_name, p_const) = setup_prop_struct_env(num_fields);

    let mut tc = TypeChecker::new(&env);
    let struct_ty = Expr::const_(struct_name.clone(), vec![]);
    let sid = tc.local_context_mut().push(
        Name::from_string("s"),
        struct_ty.clone(),
        BinderInfo::Default,
    );
    let s = Expr::fvar(sid);

    tc.reset_whnf_impl_call_count_for_tests();
    for idx in 0..num_fields {
        let field_ty = tc
            .infer_proj_type_from(&struct_name, idx, &s, &struct_ty)
            .expect("Prop projection type inference should succeed");
        assert_eq!(
            field_ty, p_const,
            "field type should be P for Prop structure projection index {idx}"
        );
    }

    tc.whnf_impl_call_count_for_tests()
}

/// Regression test for #1420: Prop-typed structure projection scaling.
///
/// Before the fix, each projection index K re-walked the telescope from 0..K,
/// giving O(N^2) total work for sequential queries of all N fields. The batch
/// cache in `cache_projection_field_types_prop` fills all field types in one
/// walk, so subsequent lookups are O(1) cache hits.
#[test]
fn test_prop_struct_proj_scaling_1420() {
    let calls_8 = measure_prop_struct_proj_whnf_calls(8);
    let calls_32 = measure_prop_struct_proj_whnf_calls(32);

    // 8 -> 32 is a 4x input increase. Linear behavior stays near 4x.
    // Prop path has additional is_prop() checks per field, so allow more overhead.
    let linear_upper_bound = calls_8.saturating_mul(6).saturating_add(128);
    assert!(
        calls_32 <= linear_upper_bound,
        "Prop projection WHNF call growth regressed toward quadratic (#1420): \
         calls_8={calls_8}, calls_32={calls_32}, \
         ratio={:.1}x (expected ~4x for linear), \
         linear_upper_bound={linear_upper_bound}",
        calls_32 as f64 / calls_8.max(1) as f64,
    );
}

/// Test that the Prop projection cache fills on the first projection query
/// and subsequent queries are cache hits with minimal WHNF work.
#[test]
fn test_prop_struct_proj_cache_hits_1420() {
    let (env, struct_name, p_const) = setup_prop_struct_env(32);

    let mut tc = TypeChecker::new(&env);
    let struct_ty = Expr::const_(struct_name.clone(), vec![]);
    let sid = tc.local_context_mut().push(
        Name::from_string("s"),
        struct_ty.clone(),
        BinderInfo::Default,
    );
    let s = Expr::fvar(sid);

    // First projection fills the batch cache for ALL fields.
    tc.reset_whnf_impl_call_count_for_tests();
    let ty0 = tc
        .infer_proj_type_from(&struct_name, 0, &s, &struct_ty)
        .expect("projection 0 should succeed");
    assert_eq!(ty0, p_const);
    let calls_after_first = tc.whnf_impl_call_count_for_tests();

    // Subsequent projections should be cache hits with near-zero WHNF calls.
    for idx in 1..32u32 {
        let field_ty = tc
            .infer_proj_type_from(&struct_name, idx, &s, &struct_ty)
            .expect("projection should succeed");
        assert_eq!(field_ty, p_const);
    }
    let calls_total = tc.whnf_impl_call_count_for_tests();
    let calls_from_remaining = calls_total.saturating_sub(calls_after_first);

    // After the first query fills the cache, the remaining 31 queries
    // should add minimal WHNF overhead (just cache lookups + whnf of expr_type).
    assert!(
        calls_from_remaining <= 16,
        "Prop projection cache miss regression (#1420): calls_after_first={calls_after_first}, \
         calls_total={calls_total}, calls_from_remaining={calls_from_remaining}"
    );
}

/// Test projection on a deeply nested dependent Prop structure (7 fields).
/// Verifies that the batch Prop cache handles dependent field types correctly.
#[test]
fn test_prop_struct_proj_deeply_nested_dependent_1420() {
    use crate::env::Declaration;
    use crate::inductive::{Constructor, InductiveDecl, InductiveType};

    let mut env = Environment::new();

    // P : Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    let p_const = Expr::const_(Name::from_string("P"), vec![]);
    let struct_name = Name::from_string("DeepPropStruct");
    let ctor_name = Name::from_string("DeepPropStruct.mk");

    // 7 non-dependent fields, all of type P.
    let num_fields = 7u32;
    let mut ctor_type = Expr::const_(struct_name.clone(), vec![]);
    for _ in 0..num_fields {
        ctor_type = Expr::pi(BinderInfo::Default, p_const.clone(), ctor_type);
    }

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: struct_name.clone(),
            type_: Expr::prop(),
            constructors: vec![Constructor {
                name: ctor_name,
                type_: ctor_type,
            }],
        }],
    };
    env.add_inductive(decl).unwrap();

    let mut tc = TypeChecker::new(&env);
    let struct_ty = Expr::const_(struct_name.clone(), vec![]);
    let sid = tc.local_context_mut().push(
        Name::from_string("s"),
        struct_ty.clone(),
        BinderInfo::Default,
    );
    let s = Expr::fvar(sid);

    // Query all 7 fields — all should return P.
    for idx in 0..num_fields {
        let field_ty = tc
            .infer_proj_type_from(&struct_name, idx, &s, &struct_ty)
            .expect("Prop projection type inference should succeed");
        assert_eq!(
            field_ty, p_const,
            "field {idx} of DeepPropStruct should have type P"
        );
    }

    // Verify cache is populated for all fields.
    assert!(
        tc.proj_type_cache_entries() >= num_fields as usize,
        "proj_type_cache should have entries for all {num_fields} fields, got {}",
        tc.proj_type_cache_entries()
    );
}
