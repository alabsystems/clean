// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the explicit boxing pass.

#[allow(deprecated)] // Tests for legacy explicit_boxing API
use super::*;
use crate::ir::{CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, VarId};
use clean_kernel::Name;

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

#[test]
fn test_mk_cast_box() {
    let cast = mk_cast(VarId(0), &IRType::UInt64, &IRType::Object);
    match cast {
        IRExpr::Box { ty, arg } => {
            assert_eq!(
                ty,
                IRType::UInt64,
                "Box ty should be the source scalar type"
            );
            assert_eq!(arg, IRArg::Var(VarId(0)));
        }
        other => panic!("Expected Box, got {:?}", other),
    }
}
#[test]
fn test_mk_cast_unbox() {
    let cast = mk_cast(VarId(0), &IRType::Object, &IRType::UInt64);
    match cast {
        IRExpr::Unbox { ty, arg } => {
            assert_eq!(
                ty,
                IRType::UInt64,
                "Unbox ty should match target scalar type"
            );
            assert_eq!(arg, IRArg::Var(VarId(0)));
        }
        other => panic!("Expected Unbox, got {:?}", other),
    }
}
#[test]
fn test_requires_boxed_version_scalar_return() {
    let decl = make_test_decl(
        "foo",
        vec![(VarId(0), IRType::Object)],
        IRType::UInt64,
        IRBody::Ret(IRArg::Var(VarId(0))),
    );
    assert!(requires_boxed_version(&decl));
}
#[test]
fn test_requires_boxed_version_scalar_param() {
    let decl = make_test_decl(
        "foo",
        vec![(VarId(0), IRType::UInt64)],
        IRType::Object,
        IRBody::Ret(IRArg::Var(VarId(0))),
    );
    assert!(requires_boxed_version(&decl));
}
#[test]
fn test_requires_boxed_version_all_objects() {
    let decl = make_test_decl(
        "foo",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        IRBody::Ret(IRArg::Var(VarId(0))),
    );
    assert!(!requires_boxed_version(&decl));
}
#[test]
fn test_requires_boxed_version_no_params() {
    let decl = make_test_decl("foo", vec![], IRType::UInt64, IRBody::Ret(IRArg::Erased));
    assert!(!requires_boxed_version(&decl));
}
#[test]
fn test_requires_boxed_version_many_params() {
    let params: Vec<_> = (0..=config::CLOSURE_MAX_ARGS as u32)
        .map(|i| (VarId(i), IRType::Object))
        .collect();
    let decl = make_test_decl(
        "foo",
        params,
        IRType::Object,
        IRBody::Ret(IRArg::Var(VarId(0))),
    );
    assert!(requires_boxed_version(&decl));
}
#[test]
fn test_mk_boxed_version_scalar_return() {
    let decl = make_test_decl(
        "foo",
        vec![(VarId(0), IRType::Object)],
        IRType::UInt64,
        IRBody::Ret(IRArg::Var(VarId(0))),
    );
    let boxed = mk_boxed_version(&decl);
    assert_eq!(boxed.return_type, IRType::Object);
}
#[test]
fn test_mk_boxed_version_scalar_param() {
    let decl = make_test_decl(
        "bar",
        vec![(VarId(0), IRType::UInt64)],
        IRType::Object,
        IRBody::Ret(IRArg::Var(VarId(0))),
    );
    let boxed = mk_boxed_version(&decl);
    assert_eq!(boxed.params[0].1, IRType::Object);
    match &boxed.body {
        IRBody::VDecl { value, .. } => assert!(matches!(value, IRExpr::Unbox { .. })),
        _ => panic!("Expected VDecl with Unbox"),
    }
}
#[test]
#[allow(deprecated)]
fn test_explicit_boxing_passthrough() {
    let decl = make_test_decl(
        "id",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        IRBody::Ret(IRArg::Var(VarId(0))),
    );
    let result = explicit_boxing(vec![decl]);
    assert_eq!(result.len(), 1);
}
#[test]
#[allow(deprecated)]
fn test_explicit_boxing_generates_boxed_version() {
    let decl = make_test_decl(
        "square",
        vec![(VarId(0), IRType::UInt64)],
        IRType::UInt64,
        IRBody::Ret(IRArg::Var(VarId(0))),
    );
    let result = explicit_boxing(vec![decl]);
    assert_eq!(result.len(), 2);
    assert!(result[1].name.to_string().contains("boxed"));
}
#[test]
fn test_visit_body_ret_cast() {
    let decl = make_test_decl(
        "test",
        vec![(VarId(0), IRType::UInt64)],
        IRType::Object,
        IRBody::Ret(IRArg::Var(VarId(0))),
    );
    let decls = vec![decl.clone()];
    let mut ctx = BoxingContext::new_default(&decl, &decls);
    ctx.set_var_type(VarId(0), IRType::UInt64);
    let transformed = visit_body(&decl.body, &mut ctx);
    match transformed {
        IRBody::VDecl { value, .. } => assert!(matches!(value, IRExpr::Box { .. })),
        _ => panic!("Expected VDecl with Box"),
    }
}

// Tests for Issue 1: expensive_constant_boxing
#[test]
fn test_expensive_constant_boxing_skips_cheap_types() {
    let decl = make_test_decl("test", vec![], IRType::Object, IRBody::Ret(IRArg::Erased));
    let decls = vec![decl.clone()];
    let mut ctx = BoxingContext::new_default(&decl, &decls);
    ctx.set_var_type(VarId(0), IRType::UInt8);
    ctx.set_var_value(VarId(0), IRExpr::Lit(IRLiteral::UInt8(42)));
    // UInt8 is cheap, should return None
    assert!(
        BoxingContext::expensive_constant_boxing(VarId(0), &IRType::UInt8, &mut ctx).is_none(),
        "cheap type UInt8 should not trigger expensive constant boxing"
    );
    assert!(ctx.take_aux_decls().is_empty());
}

#[test]
fn test_expensive_constant_boxing_creates_aux_decl() {
    let decl = make_test_decl("test", vec![], IRType::Object, IRBody::Ret(IRArg::Erased));
    let decls = vec![decl.clone()];
    let mut ctx = BoxingContext::new_default(&decl, &decls);
    ctx.set_var_type(VarId(0), IRType::UInt64);
    ctx.set_var_value(VarId(0), IRExpr::Lit(IRLiteral::UInt64(0xFFFFFFFFFFFFFFFF)));
    // UInt64 literal is expensive, should create aux decl
    let result = BoxingContext::expensive_constant_boxing(VarId(0), &IRType::UInt64, &mut ctx);
    assert!(
        matches!(result, Some(IRExpr::Apply { .. })),
        "expensive UInt64 literal should produce Apply aux decl, got {:?}",
        result
    );
    let aux_decls = ctx.take_aux_decls();
    assert_eq!(aux_decls.len(), 1);
    assert!(aux_decls[0].name.to_string().contains("boxed_const"));
    // #2174: Boxing produces heap-allocated Object, not tagged TObject
    assert_eq!(
        aux_decls[0].return_type,
        IRType::Object,
        "aux decl return type should be Object (heap-allocated), not TObject (tagged)"
    );
}

// Tests for Issue 2: partial application uses boxed version
#[test]
fn test_requires_boxed_version_for_pap() {
    use crate::ir::FnId;

    let scalar_fn = make_test_decl(
        "add",
        vec![(VarId(0), IRType::UInt64)],
        IRType::UInt64,
        IRBody::Ret(IRArg::Var(VarId(0))),
    );
    let object_fn = make_test_decl(
        "id",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        IRBody::Ret(IRArg::Var(VarId(0))),
    );
    let decls = vec![scalar_fn.clone(), object_fn.clone()];
    let ctx = BoxingContext::new_default(&scalar_fn, &decls);
    assert!(ctx.requires_boxed_version_for_pap(&FnId(Name::from_string("add")),));
    assert!(!ctx.requires_boxed_version_for_pap(&FnId(Name::from_string("id")),));
}

// Tests for Issue 3: case scrutinee type based on constructors

#[test]
fn test_expected_case_scrutinee_type_scalar_ctors() {
    // Bool-like constructors: no object fields, at most one scalar
    let true_ctor = CtorInfo {
        name: Name::from_string("true"),
        tag: 1,
        num_scalars: 0,
        num_objects: 0,
        field_types: vec![],
    };
    let false_ctor = CtorInfo {
        name: Name::from_string("false"),
        tag: 0,
        num_scalars: 0,
        num_objects: 0,
        field_types: vec![],
    };
    let alts = vec![
        IRAlt {
            ctor: true_ctor,
            body: Box::new(IRBody::Ret(IRArg::Erased)),
        },
        IRAlt {
            ctor: false_ctor,
            body: Box::new(IRBody::Ret(IRArg::Erased)),
        },
    ];
    // All scalar ctors, no default -> scrutinee should be USize (tag only)
    assert_eq!(
        BoxingContext::expected_case_scrutinee_type(&alts, false),
        IRType::USize
    );
    // All scalar ctors BUT with default -> must be Object (default may need full object)
    assert_eq!(
        BoxingContext::expected_case_scrutinee_type(&alts, true),
        IRType::Object
    );
}

#[test]
fn test_expected_case_scrutinee_type_object_ctors() {
    // Option-like constructors: Some has object field
    let none_ctor = CtorInfo {
        name: Name::from_string("none"),
        tag: 0,
        num_scalars: 0,
        num_objects: 0,
        field_types: vec![],
    };
    let some_ctor = CtorInfo {
        name: Name::from_string("some"),
        tag: 1,
        num_scalars: 0,
        num_objects: 1,
        field_types: vec![IRType::Object],
    };
    let alts = vec![
        IRAlt {
            ctor: none_ctor,
            body: Box::new(IRBody::Ret(IRArg::Erased)),
        },
        IRAlt {
            ctor: some_ctor,
            body: Box::new(IRBody::Ret(IRArg::Erased)),
        },
    ];
    // Has object field -> scrutinee must be Object (regardless of default)
    assert_eq!(
        BoxingContext::expected_case_scrutinee_type(&alts, false),
        IRType::Object
    );
    assert_eq!(
        BoxingContext::expected_case_scrutinee_type(&alts, true),
        IRType::Object
    );
}

// ========================================================================
// Scaling test for get_decl HashMap optimization (#1109)
// ========================================================================
#[test]
fn test_get_decl_scaling() {
    use crate::ir::FnId;
    use std::time::Instant;

    // Part of #1109: Verify get_decl is O(1) via HashMap, not O(n) linear search.
    // We create contexts with different numbers of declarations and measure
    // lookup time. With O(1) HashMap, time should be nearly constant.

    let sizes = [100usize, 400, 1600];
    let mut times = Vec::new();

    for &n in &sizes {
        // Create n declarations
        let decls: Vec<IRDecl> = (0..n)
            .map(|i| {
                make_test_decl(
                    &format!("fn_{}", i),
                    vec![(VarId(0), IRType::Object)],
                    IRType::Object,
                    IRBody::Ret(IRArg::Var(VarId(0))),
                )
            })
            .collect();

        // Use the last decl for context (arbitrary choice)
        let ctx = BoxingContext::new_default(&decls[0], &decls);

        // Target: lookup the middle declaration
        let target = FnId(Name::from_string(&format!("fn_{}", n / 2)));

        // Warm up
        let _ = ctx.get_decl(&target);

        // Time many lookups for stable measurement
        let iterations = 10_000;
        let start = Instant::now();
        for _ in 0..iterations {
            let _ = ctx.get_decl(&target);
        }
        let elapsed = start.elapsed();
        times.push(elapsed.as_nanos());
    }

    // With O(1) HashMap lookup, time should be roughly constant regardless of n.
    // With O(n) linear search, 16x more declarations would give ~16x slower lookup.
    // We use a generous bound: 16x input should NOT cause >4x time increase.
    let ratio = times[2] as f64 / times[0] as f64;
    assert!(
        ratio < 4.0,
        "get_decl shows poor scaling: 16x declarations gave {:.1}x time (expected < 4x for O(1))",
        ratio
    );
}

// ========================================================================
// Tests for new API functions (#1055)
// ========================================================================

#[test]
fn test_boxing_config_default() {
    let config = BoxingConfig::default();
    // Default enables all optimizations (same as new())
    assert!(config.optimize_expensive_constants);
    assert!(config.generate_boxed_versions);
}

#[test]
fn test_boxing_config_new() {
    let config = BoxingConfig::new();
    // new() enables all optimizations
    assert!(config.optimize_expensive_constants);
    assert!(config.generate_boxed_versions);
}

#[test]
fn test_boxing_config_minimal() {
    let config = BoxingConfig::minimal();
    // minimal() disables all optimizations
    assert!(!config.optimize_expensive_constants);
    assert!(!config.generate_boxed_versions);
}

#[test]
fn test_explicit_boxing_decl_single() {
    // Single-decl API should produce same output as batch for one decl
    let decl = make_test_decl(
        "id",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        IRBody::Ret(IRArg::Var(VarId(0))),
    );
    let all_decls = vec![decl.clone()];
    let config = BoxingConfig::new();

    let result = explicit_boxing_decl(&decl, &all_decls, &config);
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].name.to_string(), "id");
}

#[test]
fn test_explicit_boxing_decl_generates_boxed() {
    // Single-decl with scalar param should generate boxed version
    let decl = make_test_decl(
        "scalar_fn",
        vec![(VarId(0), IRType::UInt64)],
        IRType::UInt64,
        IRBody::Ret(IRArg::Var(VarId(0))),
    );
    let all_decls = vec![decl.clone()];
    let config = BoxingConfig::new();

    let result = explicit_boxing_decl(&decl, &all_decls, &config);
    assert_eq!(result.len(), 2);
    assert!(result[1].name.to_string().contains("boxed"));
}

#[test]
fn test_explicit_boxing_decl_respects_config() {
    // With generate_boxed_versions=false, should not generate boxed wrapper
    let decl = make_test_decl(
        "scalar_fn",
        vec![(VarId(0), IRType::UInt64)],
        IRType::UInt64,
        IRBody::Ret(IRArg::Var(VarId(0))),
    );
    let all_decls = vec![decl.clone()];
    let config = BoxingConfig::minimal();

    let result = explicit_boxing_decl(&decl, &all_decls, &config);
    assert_eq!(result.len(), 1); // No boxed version
}

#[test]
fn test_explicit_boxing_with_config_reference_api() {
    // Test that the reference-based API works correctly
    let decl = make_test_decl(
        "id",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        IRBody::Ret(IRArg::Var(VarId(0))),
    );
    let decls = [decl]; // Array, not Vec - proves we can use slices
    let config = BoxingConfig::new();

    let result = explicit_boxing_with_config(&decls, &config);
    assert_eq!(result.len(), 1);
}

#[test]
fn test_explicit_boxing_with_config_multiple_decls() {
    // Multiple decls with mixed types
    let object_decl = make_test_decl(
        "obj_fn",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        IRBody::Ret(IRArg::Var(VarId(0))),
    );
    let scalar_decl = make_test_decl(
        "scalar_fn",
        vec![(VarId(0), IRType::UInt64)],
        IRType::UInt64,
        IRBody::Ret(IRArg::Var(VarId(0))),
    );
    let decls = vec![object_decl, scalar_decl];
    let config = BoxingConfig::new();

    let result = explicit_boxing_with_config(&decls, &config);
    // Should have 2 original + 1 boxed (for scalar_fn)
    assert_eq!(result.len(), 3);
}

#[test]
#[allow(deprecated)]
fn test_explicit_boxing_legacy_api_equivalence() {
    // Legacy API should produce same results as with_config + BoxingConfig::new()
    let decl = make_test_decl(
        "fn",
        vec![(VarId(0), IRType::UInt64)],
        IRType::UInt64,
        IRBody::Ret(IRArg::Var(VarId(0))),
    );
    let decls = vec![decl.clone()];

    let legacy_result = explicit_boxing(decls.clone());
    let config_result = explicit_boxing_with_config(&decls, &BoxingConfig::new());

    assert_eq!(legacy_result.len(), config_result.len());
    for (l, c) in legacy_result.iter().zip(config_result.iter()) {
        assert_eq!(l.name, c.name);
    }
}

#[path = "proptest_boxing.rs"]
mod proptest_boxing;

// Part of #1936: verify ClosureApply boxing boxes closure and args to Object.
#[test]
fn test_closure_apply_boxing_all_object() {
    // ClosureApply with scalar closure and args should box everything to Object.
    let decl = make_test_decl(
        "caller",
        vec![
            (VarId(0), IRType::Object), // closure (already Object)
            (VarId(1), IRType::UInt64), // scalar arg needs boxing
        ],
        IRType::Object,
        IRBody::VDecl {
            var: VarId(2),
            ty: IRType::Object,
            value: IRExpr::ClosureApply {
                closure: IRArg::Var(VarId(0)),
                args: vec![IRArg::Var(VarId(1))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
        },
    );
    let decls = vec![decl.clone()];
    let mut ctx = BoxingContext::new_default(&decl, &decls);
    ctx.set_var_type(VarId(0), IRType::Object);
    ctx.set_var_type(VarId(1), IRType::UInt64);

    let transformed = visit_body(&decl.body, &mut ctx);

    // The scalar arg (UInt64) should have been boxed.
    // We expect: VDecl fresh_var = Box(VarId(1)); VDecl VarId(2) = ClosureApply(VarId(0), fresh_var); Ret
    match &transformed {
        IRBody::VDecl {
            var: box_var,
            ty,
            value: IRExpr::Box { ty: box_ty, .. },
            rest,
        } => {
            assert_eq!(*ty, IRType::Object, "Boxing target should be Object");
            assert!(box_ty.is_scalar(), "Box source should be scalar type");
            // Rest should be the ClosureApply
            match rest.as_ref() {
                IRBody::VDecl {
                    value: IRExpr::ClosureApply { closure, args },
                    ..
                } => {
                    // Closure should still be VarId(0) (was already Object, no boxing needed)
                    assert_eq!(*closure, IRArg::Var(VarId(0)));
                    // The arg should be the boxed fresh variable
                    assert_eq!(args.len(), 1);
                    assert_eq!(args[0], IRArg::Var(*box_var));
                }
                other => panic!("Expected ClosureApply VDecl, got {:?}", other),
            }
        }
        other => panic!("Expected Box VDecl for scalar arg, got {:?}", other),
    }
}

// Regression: #2174 — try_correct_vdecl_type must return Object for Box,
// not TObject. Boxing produces a heap-allocated lean_object*, not a tagged pointer.
#[test]
fn test_try_correct_vdecl_type_box_returns_object() {
    use super::visit::try_correct_vdecl_type;

    let decl = make_test_decl("test", vec![], IRType::Object, IRBody::Ret(IRArg::Erased));
    let decls = [decl.clone()];
    let ctx = BoxingContext::new_default(&decl, &decls);
    let box_expr = IRExpr::Box {
        ty: IRType::UInt64,
        arg: IRArg::Var(VarId(0)),
    };
    let result = try_correct_vdecl_type(&IRType::USize, &box_expr, &ctx);
    assert_eq!(
        result,
        IRType::Object,
        "Box expression should produce Object (heap-allocated), not TObject (tagged)"
    );
}

// Regression: #1930 third silent default path — boxing.rs get_var_type
// warning for unknown VarId. Tests for to_ir.rs paths exist but this
// path was untested.
#[test]
fn test_get_var_type_unknown_varid_returns_object_with_warning() {
    let decl = make_test_decl(
        "test_fn",
        vec![(VarId(0), IRType::UInt64)],
        IRType::Object,
        IRBody::Ret(IRArg::Var(VarId(0))),
    );
    let decls = [decl.clone()];
    let ctx = BoxingContext::new_default(&decl, &decls);

    // Query an unknown VarId (not in params)
    let result = ctx.get_var_type(VarId(999));
    assert_eq!(
        result,
        IRType::Object,
        "Unknown VarId should default to Object"
    );

    let warnings = ctx.warnings.borrow();
    assert_eq!(warnings.len(), 1, "Should record exactly one warning");
    assert!(
        warnings[0].contains("unknown VarId"),
        "Warning should mention unknown VarId, got: {}",
        warnings[0]
    );
}

#[test]
fn test_cast_var_if_needed_scalar_mismatch_warns() {
    let decl = make_test_decl(
        "test_fn",
        vec![(VarId(0), IRType::UInt64)],
        IRType::Object,
        IRBody::Ret(IRArg::Var(VarId(0))),
    );
    let decls = [decl.clone()];
    let mut ctx = BoxingContext::new_default(&decl, &decls);

    let body = cast_var_if_needed(VarId(0), &IRType::Float64, &mut ctx, |var| {
        IRBody::Ret(IRArg::Var(var))
    });

    match body {
        IRBody::Ret(IRArg::Var(var)) => {
            assert_eq!(var, VarId(0), "scalar mismatch should remain a passthrough");
        }
        other => panic!("Expected passthrough Ret body, got {:?}", other),
    }

    let warnings = ctx.warnings.borrow();
    assert_eq!(warnings.len(), 1, "Should record exactly one warning");
    assert!(
        warnings[0].contains("unsupported scalar-scalar cast from UInt64 to Float64"),
        "Warning should mention the scalar mismatch, got: {}",
        warnings[0]
    );
}

#[test]
fn test_cast_args_scalar_mismatch_warns() {
    let decl = make_test_decl(
        "test_fn",
        vec![(VarId(0), IRType::UInt64)],
        IRType::Object,
        IRBody::Ret(IRArg::Var(VarId(0))),
    );
    let decls = [decl.clone()];
    let mut ctx = BoxingContext::new_default(&decl, &decls);

    let (args, prefix) = cast_args(&[IRArg::Var(VarId(0))], &[IRType::Float64], &mut ctx);

    assert_eq!(
        args,
        vec![IRArg::Var(VarId(0))],
        "scalar mismatch should keep the original argument"
    );
    assert!(
        prefix.is_empty(),
        "scalar mismatch should not synthesize a cast prefix"
    );

    let warnings = ctx.warnings.borrow();
    assert_eq!(warnings.len(), 1, "Should record exactly one warning");
    assert!(
        warnings[0].contains("unsupported scalar-scalar cast from UInt64 to Float64"),
        "Warning should mention the scalar mismatch, got: {}",
        warnings[0]
    );
}

// ========================================================================
// Zone test recovery (#2224): PartialApply arity preservation
// ========================================================================

#[test]
fn test_boxing_partial_apply_preserves_arity() {
    // Create a function with scalar params that requires a boxed version,
    // then create a PartialApply referencing it. After boxing, the fn_id
    // should be replaced with the boxed version but arity must be preserved.
    let target_fn = make_test_decl(
        "Nat.add",
        vec![(VarId(0), IRType::UInt64), (VarId(1), IRType::UInt64)],
        IRType::UInt64,
        IRBody::Ret(IRArg::Var(VarId(0))),
    );
    let caller = make_test_decl(
        "make_adder",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        IRBody::VDecl {
            var: VarId(1),
            ty: IRType::Object,
            value: IRExpr::PartialApply {
                fn_id: FnId(Name::from_string("Nat.add")),
                arity: 2,
                args: vec![IRArg::Var(VarId(0))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        },
    );
    let decls = vec![target_fn, caller];
    let result = explicit_boxing_with_config(&decls, &BoxingConfig::new());

    let transformed = result
        .iter()
        .find(|d| d.name.to_string() == "make_adder")
        .expect("make_adder should be in output");

    fn find_partial_apply(body: &IRBody) -> Option<(String, u16, usize)> {
        match body {
            IRBody::VDecl { value, rest, .. } => {
                if let IRExpr::PartialApply { fn_id, arity, args } = value {
                    Some((fn_id.0.to_string(), *arity, args.len()))
                } else {
                    find_partial_apply(rest)
                }
            }
            _ => None,
        }
    }

    let (fn_name, arity, num_args) = find_partial_apply(&transformed.body)
        .expect("transformed body should contain PartialApply");

    assert!(
        fn_name.contains("_boxed"),
        "fn_id should be boxed version, got: {}",
        fn_name
    );
    assert_eq!(arity, 2, "arity should be preserved through boxing");
    assert_eq!(num_args, 1, "captured arg count should be unchanged");
}

// ========================================================================
// Zone test recovery (#2224): ClosureApply boxing tests
// ========================================================================

#[test]
fn test_boxing_closure_apply_boxes_scalar_args() {
    let caller = make_test_decl(
        "call_closure",
        vec![(VarId(0), IRType::Object), (VarId(1), IRType::UInt64)],
        IRType::Object,
        IRBody::VDecl {
            var: VarId(2),
            ty: IRType::Object,
            value: IRExpr::ClosureApply {
                closure: IRArg::Var(VarId(0)),
                args: vec![IRArg::Var(VarId(1))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
        },
    );
    let decls = vec![caller];
    let result = explicit_boxing_with_config(&decls, &BoxingConfig::new());

    let transformed = result
        .iter()
        .find(|d| d.name.to_string() == "call_closure")
        .expect("call_closure should be in output");

    fn has_box_cast(body: &IRBody) -> bool {
        match body {
            IRBody::VDecl { value, rest, .. } => {
                matches!(value, IRExpr::Box { .. }) || has_box_cast(rest)
            }
            _ => false,
        }
    }

    assert!(
        has_box_cast(&transformed.body),
        "ClosureApply with scalar arg should insert Box cast"
    );

    fn has_closure_apply(body: &IRBody) -> bool {
        match body {
            IRBody::VDecl { value, rest, .. } => {
                matches!(value, IRExpr::ClosureApply { .. }) || has_closure_apply(rest)
            }
            _ => false,
        }
    }

    assert!(
        has_closure_apply(&transformed.body),
        "ClosureApply should be preserved after boxing"
    );
}

#[test]
fn test_boxing_closure_apply_all_object_args() {
    let caller = make_test_decl(
        "call_closure",
        vec![(VarId(0), IRType::Object), (VarId(1), IRType::Object)],
        IRType::Object,
        IRBody::VDecl {
            var: VarId(2),
            ty: IRType::Object,
            value: IRExpr::ClosureApply {
                closure: IRArg::Var(VarId(0)),
                args: vec![IRArg::Var(VarId(1))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
        },
    );
    let decls = vec![caller];
    let result = explicit_boxing_with_config(&decls, &BoxingConfig::new());

    let transformed = result
        .iter()
        .find(|d| d.name.to_string() == "call_closure")
        .expect("call_closure should be in output");

    fn count_box_casts(body: &IRBody) -> usize {
        match body {
            IRBody::VDecl { value, rest, .. } => {
                let here = usize::from(matches!(value, IRExpr::Box { .. }));
                here + count_box_casts(rest)
            }
            _ => 0,
        }
    }

    assert_eq!(
        count_box_casts(&transformed.body),
        0,
        "all-Object ClosureApply should not insert Box casts"
    );
}

#[test]
fn test_boxing_closure_apply_zero_args() {
    let caller = make_test_decl(
        "force_thunk",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        IRBody::VDecl {
            var: VarId(1),
            ty: IRType::Object,
            value: IRExpr::ClosureApply {
                closure: IRArg::Var(VarId(0)),
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        },
    );
    let decls = vec![caller];
    let result = explicit_boxing_with_config(&decls, &BoxingConfig::new());

    let transformed = result
        .iter()
        .find(|d| d.name.to_string() == "force_thunk")
        .expect("force_thunk should be in output");

    fn count_box_casts(body: &IRBody) -> usize {
        match body {
            IRBody::VDecl { value, rest, .. } => {
                let here = usize::from(matches!(value, IRExpr::Box { .. }));
                here + count_box_casts(rest)
            }
            _ => 0,
        }
    }

    assert_eq!(
        count_box_casts(&transformed.body),
        0,
        "zero-arg ClosureApply should not insert Box casts"
    );
}

#[test]
fn test_boxing_closure_apply_boxes_specific_scalar_arg() {
    // Mixed types: Object + UInt64 + Object. Only the UInt64 arg should be boxed.
    let caller = make_test_decl(
        "call_mixed",
        vec![
            (VarId(0), IRType::Object),
            (VarId(1), IRType::UInt64),
            (VarId(2), IRType::Object),
        ],
        IRType::Object,
        IRBody::VDecl {
            var: VarId(3),
            ty: IRType::Object,
            value: IRExpr::ClosureApply {
                closure: IRArg::Var(VarId(0)),
                args: vec![IRArg::Var(VarId(1)), IRArg::Var(VarId(2))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(3)))),
        },
    );
    let decls = vec![caller];
    let result = explicit_boxing_with_config(&decls, &BoxingConfig::new());

    let transformed = result
        .iter()
        .find(|d| d.name.to_string() == "call_mixed")
        .expect("call_mixed should be in output");

    fn count_box_casts(body: &IRBody) -> usize {
        match body {
            IRBody::VDecl { value, rest, .. } => {
                let here = usize::from(matches!(value, IRExpr::Box { .. }));
                here + count_box_casts(rest)
            }
            _ => 0,
        }
    }

    assert_eq!(
        count_box_casts(&transformed.body),
        1,
        "mixed-type ClosureApply should insert exactly 1 Box cast (for UInt64 arg)"
    );

    fn closure_apply_arg_count(body: &IRBody) -> Option<usize> {
        match body {
            IRBody::VDecl { value, rest, .. } => {
                if let IRExpr::ClosureApply { args, .. } = value {
                    Some(args.len())
                } else {
                    closure_apply_arg_count(rest)
                }
            }
            _ => None,
        }
    }

    assert_eq!(
        closure_apply_arg_count(&transformed.body),
        Some(2),
        "ClosureApply should preserve arg count after boxing"
    );
}

// Passthrough variant coverage for the boxing pass.
//
// `visit_body` dispatches VDecl/JDecl/Case/Ret/Jmp and routes every other
// `IRBody` variant through `visit_body_passthrough`, which must preserve the
// node and recurse only into `rest`. These tests drive the in-place mutation
// and ref-count variants through the real `explicit_boxing_with_config` entry
// and pin that they survive the pass without panicking. With the exhaustive
// (no catch-all `_`) match, a future `IRBody` variant becomes a compile error
// in the passthrough helper rather than a runtime `unreachable!()` crash.

#[test]
fn test_boxing_passthrough_inc_dec_preserves_body() {
    // inc x0 2; dec x0; unreachable
    let body = IRBody::Inc {
        var: VarId(0),
        n: 2,
        rest: Box::new(IRBody::Dec {
            var: VarId(0),
            rest: Box::new(IRBody::Unreachable),
        }),
    };
    let decl = make_test_decl("f", vec![(VarId(0), IRType::Object)], IRType::Object, body);
    let result = explicit_boxing_with_config(&[decl], &BoxingConfig::minimal());
    assert_eq!(result.len(), 1);
    assert!(
        matches!(
            &result[0].body,
            IRBody::Inc { n: 2, rest, .. }
                if matches!(rest.as_ref(), IRBody::Dec { rest, .. }
                    if matches!(rest.as_ref(), IRBody::Unreachable))
        ),
        "inc/dec/unreachable must pass through boxing unchanged, got: {:?}",
        result[0].body
    );
}

#[test]
fn test_boxing_passthrough_set_settag_preserves_body() {
    // x0[1] := x1; setTag x0 4; unreachable
    let body = IRBody::Set {
        var: VarId(0),
        idx: 1,
        value: VarId(1),
        rest: Box::new(IRBody::SetTag {
            var: VarId(0),
            tag: 4,
            rest: Box::new(IRBody::Unreachable),
        }),
    };
    let decl = make_test_decl(
        "f",
        vec![(VarId(0), IRType::Object), (VarId(1), IRType::Object)],
        IRType::Object,
        body,
    );
    let result = explicit_boxing_with_config(&[decl], &BoxingConfig::minimal());
    assert!(
        matches!(
            &result[0].body,
            IRBody::Set { idx: 1, rest, .. }
                if matches!(rest.as_ref(), IRBody::SetTag { tag: 4, .. })
        ),
        "set/setTag must pass through boxing unchanged, got: {:?}",
        result[0].body
    );
}

#[test]
fn test_boxing_passthrough_uset_sset_preserves_body() {
    // uset x0 0 := x1; sset x0 1 8 := x2 : UInt64; unreachable
    let body = IRBody::USet {
        var: VarId(0),
        idx: 0,
        value: VarId(1),
        rest: Box::new(IRBody::SSet {
            var: VarId(0),
            n: 1,
            offset: 8,
            value: VarId(2),
            ty: IRType::UInt64,
            rest: Box::new(IRBody::Unreachable),
        }),
    };
    let decl = make_test_decl(
        "f",
        vec![
            (VarId(0), IRType::Object),
            (VarId(1), IRType::USize),
            (VarId(2), IRType::UInt64),
        ],
        IRType::Object,
        body,
    );
    let result = explicit_boxing_with_config(&[decl], &BoxingConfig::minimal());
    assert!(
        matches!(
            &result[0].body,
            IRBody::USet { idx: 0, rest, .. }
                if matches!(rest.as_ref(), IRBody::SSet { n: 1, offset: 8, .. })
        ),
        "uset/sset must pass through boxing unchanged, got: {:?}",
        result[0].body
    );
}

// ── Regression: fresh boxing VarIds must not collide with body locals ──
//
// The boxing pass seeds its fresh-VarId counter from the declaration. The bug
// (`duplicate definition: index 1`) was that the counter was seeded only from
// `decl.params`, ignoring VarIds already defined in the body. When a scalar
// body local then had to be boxed before a call, `mk_fresh_var` handed back a
// VarId already bound by a body `VDecl`, so the pass emitted two `VDecl`s with
// the same VarId — which the IR checker's V2 rule correctly rejects as
// `DuplicateDefinition`. The fix seeds the counter from the max VarId across
// both params and body. These tests pin that invariant directly on the pass.

/// Collect every VarId *introduced* (params + every `VDecl`/`JDecl`-param)
/// in a boxed declaration, so duplicates can be detected.
fn collect_defined_var_ids(decl: &IRDecl) -> Vec<u32> {
    fn walk(body: &IRBody, out: &mut Vec<u32>) {
        match body {
            IRBody::VDecl { var, rest, .. } => {
                out.push(var.0);
                walk(rest, out);
            }
            IRBody::JDecl {
                params, body, rest, ..
            } => {
                out.extend(params.iter().map(|(v, _)| v.0));
                walk(body, out);
                walk(rest, out);
            }
            IRBody::Case { alts, default, .. } => {
                for a in alts {
                    walk(&a.body, out);
                }
                if let Some(d) = default {
                    walk(d, out);
                }
            }
            IRBody::Inc { rest, .. }
            | IRBody::Dec { rest, .. }
            | IRBody::Set { rest, .. }
            | IRBody::SetTag { rest, .. }
            | IRBody::USet { rest, .. }
            | IRBody::SSet { rest, .. } => walk(rest, out),
            IRBody::Ret(_) | IRBody::Jmp { .. } | IRBody::Unreachable => {}
        }
    }
    let mut out: Vec<u32> = decl.params.iter().map(|(v, _)| v.0).collect();
    walk(&decl.body, &mut out);
    out
}

#[test]
fn test_boxing_fresh_var_does_not_collide_with_body_local() {
    // Callee `g` takes one Object parameter, forcing the caller's scalar
    // argument to be boxed at the call site.
    let g = make_test_decl(
        "g",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        IRBody::Ret(IRArg::Var(VarId(0))),
    );

    // Caller `f (x0 : Object)`:
    //   VDecl x1 : USize  = Lit(USize(1))      <- body local beyond the params
    //   VDecl x2 : Object = g(x1)              <- x1 (scalar) must be boxed
    //   Ret x2
    // With the bug, boxing's fresh var is x1 (== an existing body local),
    // producing a second `VDecl x1`. With the fix it is x3.
    let f_body = IRBody::VDecl {
        var: VarId(1),
        ty: IRType::USize,
        value: IRExpr::Lit(IRLiteral::USize(1)),
        rest: Box::new(IRBody::VDecl {
            var: VarId(2),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: FnId(Name::from_string("g")),
                args: vec![IRArg::Var(VarId(1))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
        }),
    };
    let f = make_test_decl(
        "f",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        f_body,
    );

    let boxed = explicit_boxing_with_config(&[g, f], &BoxingConfig::minimal());
    let boxed_f = boxed
        .iter()
        .find(|d| d.name == Name::from_string("f"))
        .expect("boxed output must still contain `f`");

    let defined = collect_defined_var_ids(boxed_f);
    let mut sorted = defined.clone();
    sorted.sort_unstable();
    sorted.dedup();
    assert_eq!(
        sorted.len(),
        defined.len(),
        "boxing must not introduce duplicate VarId definitions; got {defined:?} in {:?}",
        boxed_f.body
    );

    // The pass must actually have boxed the scalar arg (otherwise the test
    // would vacuously pass). A fresh Object VDecl beyond x0..x2 proves it.
    assert!(
        defined.iter().any(|&v| v >= 3),
        "expected a fresh boxing VarId (>= 3) to be introduced, got {defined:?}"
    );

    // And the IR checker must not flag a DuplicateDefinition on the boxed decls.
    // Other checker results (Ok, or a *different* error from an unrelated
    // pre-existing defect) are out of scope for this numbering regression.
    if let Err(crate::ir_checker::IRError::DuplicateDefinition(v)) =
        crate::ir_checker::check_decls(&boxed)
    {
        panic!("boxing produced a duplicate definition of VarId({v}): {boxed:?}")
    }
}

// Regression for the V5 "inc requires object type" bug (Phase 5 emit bug #2).
//
// The RC pass (rc::insert) runs at L5CNF, BEFORE final IRTypes are assigned, and
// conservatively emits inc/dec on a `Nat` literal (treated as a possibly-boxed
// BigNum). to_ir + boxing later lower that literal to a pure scalar (USize). The
// boxing pass is the first stage that knows the final IRType, so it drops the
// stale RC op on the now-scalar var — but ONLY on provably-scalar vars, never
// objects (which would be a use-after-free / leak). The object inc must survive.
#[test]
fn test_boxing_drops_inc_dec_on_scalar_var() {
    // let x1 : USize = lit 1 in   (scalar)
    // inc x1;                     (stale RC op on a scalar — must be dropped)
    // dec x1;                     (stale RC op on a scalar — must be dropped)
    // inc x0;                     (genuine object — must survive)
    // ret x0
    let body = IRBody::VDecl {
        var: VarId(1),
        ty: IRType::USize,
        value: IRExpr::Lit(IRLiteral::USize(1)),
        rest: Box::new(IRBody::Inc {
            var: VarId(1),
            n: 1,
            rest: Box::new(IRBody::Dec {
                var: VarId(1),
                rest: Box::new(IRBody::Inc {
                    var: VarId(0),
                    n: 1,
                    rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
                }),
            }),
        }),
    };
    let decl = make_test_decl("f", vec![(VarId(0), IRType::Object)], IRType::Object, body);
    let result = explicit_boxing_with_config(&[decl], &BoxingConfig::minimal());
    assert_eq!(result.len(), 1);

    // Walk the body: the scalar Inc/Dec on VarId(1) must be gone, the object
    // Inc on VarId(0) must remain. No Inc/Dec may target the scalar VarId(1).
    fn assert_no_rc_on_scalar(body: &IRBody) {
        match body {
            IRBody::Inc { var, rest, .. } => {
                assert_ne!(*var, VarId(1), "scalar Inc must have been dropped");
                assert_no_rc_on_scalar(rest);
            }
            IRBody::Dec { var, rest } => {
                assert_ne!(*var, VarId(1), "scalar Dec must have been dropped");
                assert_no_rc_on_scalar(rest);
            }
            IRBody::VDecl { rest, .. } => assert_no_rc_on_scalar(rest),
            _ => {}
        }
    }
    assert_no_rc_on_scalar(&result[0].body);

    // The object Inc on VarId(0) must still be present somewhere in the body.
    fn has_object_inc(body: &IRBody) -> bool {
        match body {
            IRBody::Inc { var, rest, .. } => *var == VarId(0) || has_object_inc(rest),
            IRBody::Dec { rest, .. } | IRBody::VDecl { rest, .. } => has_object_inc(rest),
            _ => false,
        }
    }
    assert!(
        has_object_inc(&result[0].body),
        "object Inc on VarId(0) must survive boxing, got: {:?}",
        result[0].body
    );
}
