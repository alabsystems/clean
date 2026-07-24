// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Property-based tests for explicit_boxing invariants (#1080).

use super::*;
use crate::ir::{eqv_types, IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
use clean_kernel::Name;
use proptest::prelude::*;
use std::collections::HashSet;

use super::config::CLOSURE_MAX_ARGS;

fn make_test_decl(
    name: &str,
    params: Vec<(VarId, IRType)>,
    return_type: IRType,
    body: IRBody,
) -> IRDecl {
    IRDecl {
        name: Name::from_string(name),
        params,
        return_type,
        body,
    }
}

/// Generate arbitrary IRType (simplified for testing)
fn arb_ir_type() -> impl Strategy<Value = IRType> {
    prop_oneof![
        Just(IRType::Bool),
        Just(IRType::UInt8),
        Just(IRType::UInt16),
        Just(IRType::UInt32),
        Just(IRType::UInt64),
        Just(IRType::USize),
        Just(IRType::Float32),
        Just(IRType::Float64),
        Just(IRType::Object),
        Just(IRType::TObject),
        Just(IRType::Void), // Include Void for requires_boxed_version coverage
    ]
}

/// Generate a parameter list with given size
fn arb_params(max_params: usize) -> impl Strategy<Value = Vec<(VarId, IRType)>> {
    prop::collection::vec(arb_ir_type(), 0..=max_params).prop_map(|types| {
        types
            .into_iter()
            .enumerate()
            .map(|(i, ty)| (VarId(i as u32), ty))
            .collect()
    })
}

/// Generate a simple IRDecl with Ret body
fn arb_simple_decl() -> impl Strategy<Value = IRDecl> {
    // Generate params first, then derive return type from first param
    // to ensure type-correct IR (returned value matches return type).
    arb_params(CLOSURE_MAX_ARGS + 2).prop_flat_map(|params| {
        // If we have params, return type should match first param type
        // (since we return Var(params[0])).
        // If no params, use any return type with Erased body.
        let return_type_strat = if params.is_empty() {
            arb_ir_type().boxed()
        } else {
            Just(params[0].1.clone()).boxed()
        };

        return_type_strat.prop_map(move |return_type| {
            let body = if params.is_empty() {
                IRBody::Ret(IRArg::Erased)
            } else {
                IRBody::Ret(IRArg::Var(params[0].0))
            };
            make_test_decl("test", params.clone(), return_type, body)
        })
    })
}

/// Generate multiple declarations with unique names
fn arb_decls(max_decls: usize) -> impl Strategy<Value = Vec<IRDecl>> {
    prop::collection::vec(arb_simple_decl(), 1..=max_decls).prop_map(|decls| {
        // Ensure unique names by adding index suffix
        decls
            .into_iter()
            .enumerate()
            .map(|(i, mut d)| {
                d.name = Name::from_string(&format!("fn_{}", i));
                d
            })
            .collect()
    })
}

// Property 1: Output contains at least as many decls as input
proptest! {
    #[test]
    #[allow(deprecated)]
    fn prop_output_count_geq_input(decls in arb_decls(5)) {
        let input_count = decls.len();
        let output = explicit_boxing(decls);
        prop_assert!(output.len() >= input_count,
            "Output count {} < input count {}", output.len(), input_count);
    }
}

// Property 2: All output declaration names are unique
proptest! {
    #[test]
    #[allow(deprecated)]
    fn prop_unique_decl_names(decls in arb_decls(5)) {
        let output = explicit_boxing(decls);
        let mut names = HashSet::new();
        for decl in &output {
            let name_str = decl.name.to_string();
            prop_assert!(names.insert(name_str.clone()),
                "Duplicate declaration name: {}", name_str);
        }
    }
}

// Property 3: Count of boxed versions matches count of decls needing them
proptest! {
    #[test]
    #[allow(deprecated)]
    fn prop_boxed_version_consistency(decls in arb_decls(5)) {
        let needs_boxed_count = decls.iter()
            .filter(|d| requires_boxed_version(d))
            .count();

        let output = explicit_boxing(decls.clone());

        // Count boxed versions in output (exclude boxed_const aux decls)
        let boxed_count = output.iter()
            .filter(|d| {
                let n = d.name.to_string();
                n.contains("boxed") && !n.contains("boxed_const")
            })
            .count();

        // Each decl needing boxed version should produce exactly one
        prop_assert_eq!(boxed_count, needs_boxed_count,
            "Expected {} boxed versions, got {}",
            needs_boxed_count, boxed_count);
    }
}

// Property 4: Boxed version return types are never scalar
proptest! {
    #[test]
    #[allow(deprecated)]
    fn prop_boxed_return_not_scalar(decls in arb_decls(5)) {
        let output = explicit_boxing(decls);
        for decl in &output {
            let name = decl.name.to_string();
            if name.contains("boxed") {
                prop_assert!(!decl.return_type.is_scalar(),
                    "Boxed version {} has scalar return type {:?}",
                    name, decl.return_type);
            }
        }
    }
}

// Property 5: Boxed version params are all Object type
proptest! {
    #[test]
    #[allow(deprecated)]
    fn prop_boxed_params_are_object(decls in arb_decls(5)) {
        let output = explicit_boxing(decls);
        for decl in &output {
            let name = decl.name.to_string();
            if name.contains("boxed") && !name.contains("boxed_const") {
                for (_, ty) in &decl.params {
                    // mk_boxed_version creates params as IRType::Object specifically
                    prop_assert_eq!(ty.clone(), IRType::Object,
                        "Boxed version {} has non-Object param type {:?}",
                        name, ty);
                }
            }
        }
    }
}

// Property 6: requires_boxed_version is consistent with param/return analysis
proptest! {
    #[test]
    fn prop_requires_boxed_version_correctness(
        params in arb_params(CLOSURE_MAX_ARGS + 2),
        return_type in arb_ir_type()
    ) {
        let decl = make_test_decl("test_fn", params.clone(), return_type.clone(),
            IRBody::Ret(IRArg::Erased));

        let result = requires_boxed_version(&decl);

        // Compute expected result
        let has_scalar_param = params.iter().any(|(_, ty)| ty.is_scalar() || ty.is_void());
        let has_scalar_return = return_type.is_scalar();
        let too_many_params = params.len() > CLOSURE_MAX_ARGS;
        let no_params = params.is_empty();

        let expected = !no_params && (has_scalar_param || has_scalar_return || too_many_params);

        prop_assert_eq!(result, expected,
            "requires_boxed_version mismatch: got {}, expected {} for params {:?}, return {:?}",
            result, expected, params, return_type);
    }
}

// Property 7: mk_boxed_version preserves param count
proptest! {
    #[test]
    fn prop_boxed_version_param_count(
        params in arb_params(CLOSURE_MAX_ARGS).prop_filter("need params", |p| !p.is_empty()),
        return_type in arb_ir_type()
    ) {
        let decl = make_test_decl("test_fn", params.clone(), return_type,
            IRBody::Ret(IRArg::Var(VarId(0))));

        let boxed = mk_boxed_version(&decl);

        prop_assert_eq!(boxed.params.len(), decl.params.len(),
            "Boxed version param count mismatch");
    }
}

// Property 8: eqv_types is reflexive
proptest! {
    #[test]
    fn prop_eqv_types_reflexive(ty in arb_ir_type()) {
        prop_assert!(eqv_types(&ty, &ty),
            "eqv_types not reflexive for {:?}", ty);
    }
}

// Property 9: eqv_types is symmetric
proptest! {
    #[test]
    fn prop_eqv_types_symmetric(ty1 in arb_ir_type(), ty2 in arb_ir_type()) {
        let fwd = eqv_types(&ty1, &ty2);
        let bwd = eqv_types(&ty2, &ty1);
        prop_assert_eq!(fwd, bwd,
            "eqv_types not symmetric: ({:?}, {:?}) = {}, ({:?}, {:?}) = {}",
            ty1, ty2, fwd, ty2, ty1, bwd);
    }
}

// Property 10: Scalar and non-scalar types are never equivalent
proptest! {
    #[test]
    fn prop_eqv_types_scalar_object_disjoint(
        scalar in arb_ir_type().prop_filter("scalar", |t| t.is_scalar()),
        non_scalar in arb_ir_type().prop_filter("non-scalar", |t| !t.is_scalar())
    ) {
        prop_assert!(!eqv_types(&scalar, &non_scalar),
            "Scalar {:?} should not be eqv to non-scalar {:?}",
            scalar, non_scalar);
    }
}

// Property 11: boxed() is idempotent for non-scalars
proptest! {
    #[test]
    fn prop_boxed_idempotent_non_scalar(
        ty in arb_ir_type().prop_filter("non-scalar", |t| !t.is_scalar())
    ) {
        let boxed = ty.boxed();
        prop_assert_eq!(boxed, ty.clone(),
            "boxed() should be identity for non-scalar {:?}", ty);
    }
}

// Property 12: boxed() produces Object for scalars
proptest! {
    #[test]
    fn prop_boxed_scalar_produces_object(
        ty in arb_ir_type().prop_filter("scalar", |t| t.is_scalar())
    ) {
        prop_assert_eq!(ty.boxed(), IRType::Object,
            "boxed() should produce Object for scalar {:?}", ty);
    }
}

// Property 13: mk_cast produces Box for scalar-to-object with correct ty
proptest! {
    #[test]
    fn prop_mk_cast_scalar_to_object(
        scalar in arb_ir_type().prop_filter("scalar", |t| t.is_scalar())
    ) {
        let cast = mk_cast(VarId(0), &scalar, &IRType::Object);
        match cast {
            IRExpr::Box { ty, arg } => {
                prop_assert_eq!(ty, scalar.clone(),
                    "Box ty should be source scalar type");
                prop_assert_eq!(arg, IRArg::Var(VarId(0)));
            }
            ref other => prop_assert!(false,
                "Expected Box for scalar {:?} to Object, got {:?}", scalar, other),
        }
    }
}

// Property 14: mk_cast produces Unbox for object-to-scalar with correct ty
proptest! {
    #[test]
    fn prop_mk_cast_object_to_scalar(
        scalar in arb_ir_type().prop_filter("scalar", |t| t.is_scalar())
    ) {
        let cast = mk_cast(VarId(0), &IRType::Object, &scalar);
        match cast {
            IRExpr::Unbox { ty, arg } => {
                prop_assert_eq!(ty, scalar.clone(),
                    "Unbox ty should match target scalar type");
                prop_assert_eq!(arg, IRArg::Var(VarId(0)));
            }
            ref other => prop_assert!(false,
                "Expected Unbox for Object to scalar {:?}, got {:?}", scalar, other),
        }
    }
}

// Property 15: Variable numbering in boxed version body is valid
proptest! {
    #[test]
    fn prop_boxed_version_var_numbering(
        params in arb_params(CLOSURE_MAX_ARGS).prop_filter("need params", |p| !p.is_empty()),
        return_type in arb_ir_type()
    ) {
        let decl = make_test_decl("test_fn", params.clone(), return_type,
            IRBody::Ret(IRArg::Var(VarId(0))));

        let boxed = mk_boxed_version(&decl);

        // Collect all variable IDs declared in body (comprehensive traversal)
        fn collect_declared_vars(body: &IRBody, vars: &mut HashSet<u32>) {
            match body {
                IRBody::VDecl { var, rest, .. } => {
                    vars.insert(var.0);
                    collect_declared_vars(rest, vars);
                }
                IRBody::JDecl { params: jp_params, body: jp_body, rest, .. } => {
                    for (v, _) in jp_params { vars.insert(v.0); }
                    collect_declared_vars(jp_body, vars);
                    collect_declared_vars(rest, vars);
                }
                IRBody::Case { alts, default, .. } => {
                    for alt in alts { collect_declared_vars(&alt.body, vars); }
                    if let Some(d) = default { collect_declared_vars(d, vars); }
                }
                IRBody::Inc { rest, .. } | IRBody::Dec { rest, .. } | IRBody::Set { rest, .. }
                | IRBody::SetTag { rest, .. } | IRBody::USet { rest, .. } | IRBody::SSet { rest, .. } => {
                    collect_declared_vars(rest, vars);
                }
                IRBody::Ret(_) | IRBody::Jmp { .. } | IRBody::Unreachable => {}
            }
        }

        let mut declared_vars = HashSet::new();
        collect_declared_vars(&boxed.body, &mut declared_vars);

        // Param vars are 0..params.len()
        let param_count = params.len() as u32;

        // All declared vars should be >= param_count (no conflicts with params)
        for &v in &declared_vars {
            prop_assert!(v >= param_count,
                "Variable {} in body collides with params (params end at {})", v, param_count);
            prop_assert!(v < 1000,
                "Suspiciously large var ID {} in boxed body", v);
        }
    }
}

// Property 16: eqv_types is transitive (for equivalence relation)
proptest! {
    #[test]
    fn prop_eqv_types_transitive(
        ty1 in arb_ir_type(),
        ty2 in arb_ir_type(),
        ty3 in arb_ir_type()
    ) {
        // If ty1 ~ ty2 and ty2 ~ ty3, then ty1 ~ ty3
        if eqv_types(&ty1, &ty2) && eqv_types(&ty2, &ty3) {
            prop_assert!(eqv_types(&ty1, &ty3),
                "eqv_types not transitive: {:?} ~ {:?} and {:?} ~ {:?} but not {:?} ~ {:?}",
                ty1, ty2, ty2, ty3, ty1, ty3);
        }
    }
}

// Property 17: Generated decls have type-correct bodies (regression guard)
proptest! {
    #[test]
    fn prop_generated_decl_type_correct(decl in arb_simple_decl()) {
        match &decl.body {
            IRBody::Ret(IRArg::Var(var)) => {
                let var_type = decl.params.iter()
                    .find(|(v, _)| *v == *var)
                    .map(|(_, t)| t.clone())
                    .expect("Returned var should be in params");
                prop_assert!(eqv_types(&var_type, &decl.return_type),
                    "Return type {:?} doesn't match returned var type {:?}",
                    decl.return_type, var_type);
            }
            IRBody::Ret(IRArg::Erased) => {}
            _ => prop_assert!(false, "arb_simple_decl should only generate Ret bodies"),
        }
    }
}

// Property 18: build_unbox_chain at CLOSURE_MAX_ARGS boundary (#1064)
proptest! {
    #[test]
    fn prop_build_unbox_chain_at_max_args(
        return_type in arb_ir_type()
    ) {
        let params: Vec<_> = (0..=CLOSURE_MAX_ARGS as u32)
            .map(|i| (VarId(i), if i % 2 == 0 { IRType::UInt64 } else { IRType::Object }))
            .collect();

        let decl = make_test_decl("edge_test", params.clone(), return_type.clone(),
            IRBody::Ret(IRArg::Var(VarId(0))));

        prop_assert!(requires_boxed_version(&decl),
            "Decl with {} params should require boxed version", params.len());

        let boxed = mk_boxed_version(&decl);

        prop_assert!(!boxed.name.to_string().is_empty(),
            "Boxed version should have valid name");

        fn count_unbox_ops(body: &IRBody) -> usize {
            match body {
                IRBody::VDecl { value: IRExpr::Unbox { .. }, rest, .. } => 1 + count_unbox_ops(rest),
                IRBody::VDecl { rest, .. } => count_unbox_ops(rest),
                _ => 0,
            }
        }

        let scalar_count = params.iter().filter(|(_, ty)| ty.is_scalar()).count();
        let unbox_count = count_unbox_ops(&boxed.body);
        prop_assert_eq!(unbox_count, scalar_count,
            "Expected {} unbox ops for {} scalar params, got {}",
            scalar_count, scalar_count, unbox_count);
    }
}

// Property 19: build_unbox_chain variable sequencing (#1064)
proptest! {
    #[test]
    fn prop_build_unbox_chain_var_sequence(
        params in arb_params(CLOSURE_MAX_ARGS).prop_filter("need scalars", |p| {
            !p.is_empty() && p.iter().any(|(_, ty)| ty.is_scalar())
        }),
        return_type in arb_ir_type()
    ) {
        let decl = make_test_decl("seq_test", params.clone(), return_type,
            IRBody::Ret(IRArg::Var(VarId(0))));

        let boxed = mk_boxed_version(&decl);

        fn collect_vars_ordered(body: &IRBody, vars: &mut Vec<u32>) {
            if let IRBody::VDecl { var, rest, .. } = body {
                vars.push(var.0);
                collect_vars_ordered(rest, vars);
            }
        }

        let mut body_vars = Vec::new();
        collect_vars_ordered(&boxed.body, &mut body_vars);

        let start = params.len() as u32;
        for (i, &v) in body_vars.iter().enumerate() {
            prop_assert_eq!(v, start + i as u32,
                "Variable at position {} should be {}, got {}",
                i, start + i as u32, v);
        }
    }
}
