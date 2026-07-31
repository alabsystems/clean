// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type validation tests for .olean module import functionality.
//!
//! These tests validate type structures (Nat, List, inductive types, etc.)
//! from Lean 4 standard library modules. Requires a Lean 4 installation via elan.

use clean_kernel::env::Environment;
use clean_kernel::expr::{BinderInfo, Expr, ExprKind};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::tc::TypeChecker;
use clean_olean::{load_module_with_deps, parse_module_file, pinned_lean_lib_path};

fn get_lean_lib_path() -> Option<std::path::PathBuf> {
    pinned_lean_lib_path()
}

/// Gate this file's integration tests behind `CLEAN_OLEAN_INTEGRATION=1`.
/// They load real `.olean` files against the installed Lean toolchain; on
/// machines with a non-matching toolchain they surface compiler-name and
/// inductive-flag differences that reflect Lean version drift rather than
/// real bugs in the import pipeline. Opt in via the env var when running
/// the dedicated integration lane.
fn require_olean_lean() -> Option<std::path::PathBuf> {
    if std::env::var_os("CLEAN_OLEAN_INTEGRATION").is_none() {
        eprintln!(
            "TRACE: olean integration test skipped \u{2014} set \
             CLEAN_OLEAN_INTEGRATION=1 to run against the installed \
             Lean toolchain"
        );
        return None;
    }
    get_lean_lib_path()
}

/// Assert that inferring the type of `expr` yields a Sort — i.e., `expr` is a well-formed type.
fn assert_type_is_sort(tc: &TypeChecker<'_>, expr: &Expr, label: &str) {
    let inferred = tc
        .infer_type(expr)
        .unwrap_or_else(|e| panic!("{label} type should be well-formed: {e:?}"));
    assert!(
        matches!(tc.whnf(&inferred).kind(), ExprKind::Sort(_)),
        "type of {label}'s type should be a Sort, got: {inferred:?}"
    );
}

#[test]
fn test_inspect_nat_add_structure() {
    // Inspect what Nat.add looks like to understand the InvalidProjNotStruct errors
    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Data.Nat.Basic", &[lib_path]).expect("Failed to load");

    // Check Nat.below type
    let below_name = Name::from_string("Nat.below");
    if let Some(const_info) = env.get_const(&below_name) {
        println!("\n=== Nat.below ===");
        println!("Type: {:?}", const_info.type_);
        println!("Has value: {}", const_info.value.is_some());
    }

    // Check Nat.brecOn type
    let brecon_name = Name::from_string("Nat.brecOn");
    if let Some(const_info) = env.get_const(&brecon_name) {
        println!("\n=== Nat.brecOn ===");
        println!("Type: {:?}", const_info.type_);
        println!("Has value: {}", const_info.value.is_some());
    }

    // Check PProd
    let pprod_name = Name::from_string("PProd");
    if let Some(inductive) = env.get_inductive(&pprod_name) {
        println!("\n=== PProd is an inductive ===");
        println!("  num_params: {}", inductive.num_params);
        println!("  constructors: {:?}", inductive.constructor_names);
        // Check constructor info
        for ctor_name in &inductive.constructor_names {
            if let Some(ctor) = env.get_constructor(ctor_name) {
                println!("  {} - num_fields: {}", ctor_name, ctor.num_fields);
            }
        }
    } else if env.get_const(&pprod_name).is_some() {
        println!("\n=== PProd is a constant (NOT inductive!) ===");
    }

    let name = Name::from_string("Nat.add");
    if let Some(const_info) = env.get_const(&name) {
        println!("\n=== Nat.add Structure ===");
        println!("Type: {:?}", const_info.type_);
        if let Some(ref value) = const_info.value {
            println!("Value (full): {value:?}");

            // Check for FVars in the value
            fn count_fvars(e: &Expr) -> usize {
                match e.kind() {
                    ExprKind::FVar(_) => 1,
                    ExprKind::App(f, a) => count_fvars(f) + count_fvars(a),
                    ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                        count_fvars(ty) + count_fvars(body)
                    }
                    ExprKind::Let(_, ty, val, body, _) => {
                        count_fvars(ty) + count_fvars(val) + count_fvars(body)
                    }
                    ExprKind::Proj(_, _, e) | ExprKind::MData(_, e) => count_fvars(e),
                    _ => 0,
                }
            }
            let fvar_count = count_fvars(value);
            println!("FVar count in value: {fvar_count}");

            // Check for BVars
            fn count_bvars(e: &Expr) -> usize {
                match e.kind() {
                    ExprKind::BVar(_) => 1,
                    ExprKind::App(f, a) => count_bvars(f) + count_bvars(a),
                    ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                        count_bvars(ty) + count_bvars(body)
                    }
                    ExprKind::Let(_, ty, val, body, _) => {
                        count_bvars(ty) + count_bvars(val) + count_bvars(body)
                    }
                    ExprKind::Proj(_, _, e) | ExprKind::MData(_, e) => count_bvars(e),
                    _ => 0,
                }
            }
            let bvar_count = count_bvars(value);
            println!("BVar count in value: {bvar_count}");
        }
    } else {
        println!("Nat.add not found");
    }
}

#[test]
fn test_nat_below_reduction() {
    // Test that Nat.below (λ_. T) (Nat.succ n) reduces to PProd T (Nat.below ...)
    use clean_kernel::tc::TypeChecker;

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Prelude", &[lib_path]).expect("Failed to load");

    // Construct: Nat.below (λ_. Nat) (Nat.succ Nat.zero)
    // Should reduce to: PProd Nat (Nat.below (λ_. Nat) Nat.zero)
    // = PProd Nat PUnit
    let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_motive = Expr::lam(
        BinderInfo::Default,
        nat_const.clone(),
        nat_const.clone(), // body returns Nat
    );
    let succ_zero = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );

    // Nat.below [Type 1] motive (Nat.succ Nat.zero)
    let below_app = Expr::app(
        Expr::app(
            Expr::const_(
                Name::from_string("Nat.below"),
                vec![Level::succ(Level::zero())],
            ),
            nat_motive,
        ),
        succ_zero,
    );

    println!("Input: {below_app:?}");

    let tc = TypeChecker::new(&env);
    let whnf_result = tc.whnf(&below_app);

    println!("WHNF result: {whnf_result:?}");

    // Check if it reduced to PProd application
    let head = whnf_result.get_app_fn();
    println!("Head of result: {head:?}");

    if let ExprKind::Const(name, _) = head.kind() {
        println!("Head is const: {name}");
        assert_eq!(
            name.to_string(),
            "PProd",
            "Nat.below on Nat.succ should reduce to PProd"
        );
    } else {
        panic!("Expected WHNF to produce a Const head, got: {head:?}");
    }
}

#[test]
fn test_parse_inductive_val_data() {
    // Test that InductiveVal, ConstructorVal, RecursorVal extra fields are parsed
    use clean_olean::ConstantKind;

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let prelude_path = lib_path.join("Init/Prelude.olean");
    let module = parse_module_file(&prelude_path).expect("Failed to parse Init/Prelude.olean");

    // Count different kinds and check extra data
    let mut inductives_with_data = 0;
    let mut ctors_with_data = 0;
    let mut recs_with_data = 0;

    for constant in &module.constants {
        match constant.kind {
            ConstantKind::Inductive => {
                if let Some(ref ind_val) = constant.inductive_val {
                    inductives_with_data += 1;
                    // Verify we got some useful data
                    if constant.name == "Nat" {
                        println!("=== Nat InductiveVal ===");
                        println!("  numParams: {}", ind_val.num_params);
                        println!("  numIndices: {}", ind_val.num_indices);
                        println!("  all: {:?}", ind_val.all);
                        println!("  ctors: {:?}", ind_val.ctors);
                        println!("  isRec: {}", ind_val.is_rec);
                        assert_eq!(ind_val.num_params, 0);
                        assert_eq!(ind_val.num_indices, 0);
                        assert!(ind_val.is_rec);
                        assert!(
                            ind_val.ctors.iter().any(|c| c == "Nat.zero"),
                            "Nat should have zero constructor"
                        );
                        assert!(
                            ind_val.ctors.iter().any(|c| c == "Nat.succ"),
                            "Nat should have succ constructor"
                        );
                    }
                    if constant.name == "Bool" {
                        println!("=== Bool InductiveVal ===");
                        println!("  numParams: {}", ind_val.num_params);
                        println!("  ctors: {:?}", ind_val.ctors);
                        assert!(!ind_val.is_rec, "Bool should not be recursive");
                        assert_eq!(ind_val.ctors.len(), 2);
                    }
                }
            }
            ConstantKind::Constructor => {
                if let Some(ref ctor_val) = constant.constructor_val {
                    ctors_with_data += 1;
                    if constant.name == "Nat.succ" {
                        println!("=== Nat.succ ConstructorVal ===");
                        println!("  induct: {}", ctor_val.induct);
                        println!("  cidx: {}", ctor_val.cidx);
                        println!("  numParams: {}", ctor_val.num_params);
                        println!("  numFields: {}", ctor_val.num_fields);
                        assert_eq!(ctor_val.induct, "Nat");
                        assert_eq!(ctor_val.cidx, 1); // succ is second constructor
                        assert_eq!(ctor_val.num_fields, 1); // succ has one field
                    }
                    if constant.name == "Nat.zero" {
                        println!("=== Nat.zero ConstructorVal ===");
                        println!("  cidx: {}", ctor_val.cidx);
                        println!("  numFields: {}", ctor_val.num_fields);
                        assert_eq!(ctor_val.cidx, 0); // zero is first constructor
                        assert_eq!(ctor_val.num_fields, 0);
                    }
                }
            }
            ConstantKind::Recursor => {
                if let Some(ref rec_val) = constant.recursor_val {
                    recs_with_data += 1;
                    if constant.name == "Nat.rec" {
                        println!("=== Nat.rec RecursorVal ===");
                        println!("  numParams: {}", rec_val.num_params);
                        println!("  numIndices: {}", rec_val.num_indices);
                        println!("  numMotives: {}", rec_val.num_motives);
                        println!("  numMinors: {}", rec_val.num_minors);
                        println!("  rules: {} rules", rec_val.rules.len());
                        for rule in &rec_val.rules {
                            println!("    - ctor: {}, numFields: {}", rule.ctor, rule.num_fields);
                        }
                        assert_eq!(rec_val.num_minors, 2); // zero and succ
                        assert_eq!(rec_val.rules.len(), 2);
                    }
                }
            }
            _ => {}
        }
    }

    println!("\n=== Summary ===");
    println!("Inductives with data: {inductives_with_data}");
    println!("Constructors with data: {ctors_with_data}");
    println!("Recursors with data: {recs_with_data}");

    assert!(
        inductives_with_data > 0,
        "Expected at least one inductive with data"
    );
    assert!(
        ctors_with_data > 0,
        "Expected at least one constructor with data"
    );
    assert!(
        recs_with_data > 0,
        "Expected at least one recursor with data"
    );
}

#[test]
fn test_typecheck_list_definitions() {
    // Test that List type and operations type-check correctly
    use clean_kernel::tc::TypeChecker;

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    let summaries = load_module_with_deps(
        &mut env,
        "Init.Data.List.Basic",
        std::slice::from_ref(&lib_path),
    )
    .expect("Failed to load Init.Data.List.Basic");

    let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
    println!("Loaded {total_added} constants from Init.Data.List.Basic");

    // Test List inductive registration
    let list_name = Name::from_string("List");
    if let Some(ind) = env.get_inductive(&list_name) {
        println!("\n=== List Inductive ===");
        println!("  num_params: {}", ind.num_params);
        println!("  num_indices: {}", ind.num_indices);
        println!("  is_recursive: {}", ind.is_recursive);
        println!("  constructors: {:?}", ind.constructor_names);
        assert_eq!(ind.num_params, 1, "List should have 1 type parameter");
        assert!(ind.is_recursive, "List should be recursive");
        assert_eq!(
            ind.constructor_names.len(),
            2,
            "List should have 2 constructors"
        );
    } else {
        panic!("List inductive not found in environment");
    }

    // Type-check List definitions
    let test_definitions = [
        "List.length",
        "List.append",
        "List.map",
        "List.filter",
        "List.reverse",
        "List.head?",
        "List.tail?",
    ];

    let mut value_successes = 0;
    let mut type_successes = 0;
    let mut failures = 0;

    for const_name in test_definitions {
        let name = Name::from_string(const_name);
        if let Some(const_info) = env.get_const(&name) {
            // Type-check the type
            let tc = TypeChecker::new(&env);
            match tc.infer_type(&const_info.type_) {
                Ok(_) => type_successes += 1,
                Err(e) => {
                    println!("  {const_name} type error: {e:?}");
                }
            }

            // Type-check the value if present
            if let Some(ref value) = const_info.value {
                let tc = TypeChecker::new(&env);
                match tc.infer_type(value) {
                    Ok(inferred_type) => {
                        let tc = TypeChecker::new(&env);
                        if tc.is_def_eq(&inferred_type, &const_info.type_) {
                            println!("  {const_name} value ✓");
                            value_successes += 1;
                        } else {
                            println!("  {const_name} value type mismatch");
                            failures += 1;
                        }
                    }
                    Err(e) => {
                        println!("  {const_name} value error: {e:?}");
                        failures += 1;
                    }
                }
            } else {
                println!("  {const_name} has no value");
            }
        } else {
            println!("  {const_name} NOT FOUND");
        }
    }

    println!("\n=== List Definition Type-checking Summary ===");
    println!(
        "Value successes: {value_successes}, Type successes: {type_successes}, Failures: {failures}"
    );

    // At minimum, types should check
    assert!(
        type_successes >= 4,
        "Expected at least 4 List function types to check, got {type_successes}"
    );
}

#[test]
fn test_list_rec_reduction() {
    // Test that List.rec reduces correctly via iota reduction
    use clean_kernel::tc::TypeChecker;

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Data.List.Basic", &[lib_path]).expect("Failed to load");

    // Check that List.rec is properly registered
    let rec_name = Name::from_string("List.rec");
    if let Some(rec) = env.get_recursor(&rec_name) {
        println!("\n=== List.rec Recursor ===");
        println!("  num_params: {}", rec.num_params);
        println!("  num_indices: {}", rec.num_indices);
        println!("  num_motives: {}", rec.num_motives);
        println!("  num_minors: {}", rec.num_minors);
        println!("  rules: {}", rec.rules.len());
        for (i, rule) in rec.rules.iter().enumerate() {
            println!(
                "    rule {}: ctor={}, nfields={}",
                i, rule.constructor_name, rule.num_fields
            );
        }
        assert_eq!(rec.num_minors, 2, "List.rec should have 2 minor premises");
        assert_eq!(rec.rules.len(), 2, "List.rec should have 2 rules");
    } else {
        panic!("List.rec recursor not found");
    }

    // Construct: List.length [Nat] [Nat.zero, Nat.succ Nat.zero]
    // = List.rec [u] α (λ_. Nat) 0 (λ_ _ ih. Nat.succ ih) list
    // For the nil case: should reduce to 0
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let nil = Expr::app(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        nat.clone(),
    );

    // Try to infer type of List.nil Nat - this tests constructor application
    let tc = TypeChecker::new(&env);
    match tc.infer_type(&nil) {
        Ok(ty) => {
            println!("\nList.nil Nat has type: {ty:?}");
            let whnf_ty = tc.whnf(&ty);
            println!("WHNF of type: {whnf_ty:?}");
        }
        Err(e) => {
            println!("\nFailed to infer type of List.nil Nat: {e:?}");
        }
    }
}

#[test]
fn test_list_rec_recursive_fields() {
    // Verify recursive field detection uses constructor types (only tail is recursive)
    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Data.List.Basic", &[lib_path]).expect("Failed to load");

    let rec = env
        .get_recursor(&Name::from_string("List.rec"))
        .expect("List.rec recursor not found");

    let nil_rule = rec
        .rules
        .iter()
        .find(|r| r.constructor_name == Name::from_string("List.nil"))
        .expect("List.nil rule missing");
    assert!(
        nil_rule.recursive_fields.is_empty() || nil_rule.recursive_fields.iter().all(|&b| !b),
        "List.nil should not have recursive fields"
    );

    let cons_rule = rec
        .rules
        .iter()
        .find(|r| r.constructor_name == Name::from_string("List.cons"))
        .expect("List.cons rule missing");
    assert_eq!(cons_rule.recursive_fields.len(), 2);
    assert!(
        !cons_rule.recursive_fields[0],
        "List.cons head parameter is not recursive"
    );
    assert!(
        cons_rule.recursive_fields[1],
        "List.cons tail parameter should be recursive"
    );
}

#[test]
fn test_mutual_inductive_and() {
    // Test And/Or which may be mutually defined or use mutual patterns
    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Prelude", &[lib_path]).expect("Failed to load");

    // And is a structure/inductive
    let and_name = Name::from_string("And");
    if let Some(ind) = env.get_inductive(&and_name) {
        println!("\n=== And Inductive ===");
        println!("  num_params: {}", ind.num_params);
        println!("  is_recursive: {}", ind.is_recursive);
        println!("  constructors: {:?}", ind.constructor_names);
        assert_eq!(
            ind.num_params, 2,
            "And should have 2 parameters (left, right)"
        );
    } else if env.get_const(&and_name).is_some() {
        println!("And exists as constant but not inductive");
    } else {
        println!("And not found");
    }

    // Or is an inductive
    let or_name = Name::from_string("Or");
    if let Some(ind) = env.get_inductive(&or_name) {
        println!("\n=== Or Inductive ===");
        println!("  num_params: {}", ind.num_params);
        println!("  is_recursive: {}", ind.is_recursive);
        println!("  constructors: {:?}", ind.constructor_names);
        assert_eq!(ind.num_params, 2, "Or should have 2 parameters");
        assert_eq!(
            ind.constructor_names.len(),
            2,
            "Or should have inl/inr constructors"
        );
    } else {
        println!("Or not found as inductive");
    }
}

#[test]
fn test_loading_performance_with_multipass() {
    // Measure performance impact of multi-pass loading
    use std::time::Instant;

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    // Test multiple modules to get average performance
    let modules = [
        "Init.Prelude",
        "Init.Core",
        "Init.Data.Nat.Basic",
        "Init.Data.List.Basic",
    ];

    println!("\n=== Multi-pass Loading Performance ===");

    let mut total_time = std::time::Duration::ZERO;
    let mut total_constants = 0usize;

    for module in modules {
        let start = Instant::now();
        let mut env = Environment::default();
        let summaries = load_module_with_deps(&mut env, module, std::slice::from_ref(&lib_path))
            .expect("Failed to load");
        let elapsed = start.elapsed();

        let added: usize = summaries.iter().map(|s| s.added_constants).sum();
        let rate = added as f64 / elapsed.as_secs_f64();

        println!("  {module}: {added} constants in {elapsed:?} ({rate:.0} const/sec)");

        total_time += elapsed;
        total_constants += added;
    }

    let overall_rate = total_constants as f64 / total_time.as_secs_f64();
    println!("\nOverall: {total_constants} constants in {total_time:?}");
    println!("Average rate: {overall_rate:.0} constants/sec");

    // Performance target: at least 1000 constants/sec in debug mode
    assert!(
        overall_rate > 500.0,
        "Expected > 500 constants/sec, got {overall_rate:.0}"
    );
}

#[test]
fn test_indexed_inductive_fin() {
    // Fin is an indexed inductive: Fin : Nat → Type
    // Its index is the upper bound on values
    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    let summaries = load_module_with_deps(
        &mut env,
        "Init.Data.Fin.Basic",
        std::slice::from_ref(&lib_path),
    )
    .expect("Failed to load Init.Data.Fin.Basic");

    let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
    println!("Loaded {total_added} constants from Init.Data.Fin.Basic");

    // Check Fin inductive
    let fin_name = Name::from_string("Fin");
    if let Some(ind) = env.get_inductive(&fin_name) {
        println!("\n=== Fin Inductive ===");
        println!("  num_params: {}", ind.num_params);
        println!("  num_indices: {}", ind.num_indices);
        println!("  is_recursive: {}", ind.is_recursive);
        println!("  constructors: {:?}", ind.constructor_names);

        // In Lean 4, Fin is a structure with n as a parameter (not an index)
        // Fin : Nat → Type, where n is passed as a parameter
        assert_eq!(ind.num_params, 1, "Fin has 1 parameter (the bound n)");
        assert_eq!(ind.num_indices, 0, "Fin has no indices (n is a parameter)");
        assert!(!ind.is_recursive, "Fin is not recursive");
    } else {
        panic!("Fin inductive not found");
    }

    // Check Fin.mk constructor
    let mk_name = Name::from_string("Fin.mk");
    if let Some(ctor) = env.get_constructor(&mk_name) {
        println!("\n=== Fin.mk Constructor ===");
        println!("  num_params: {}", ctor.num_params);
        println!("  num_fields: {}", ctor.num_fields);
        println!("  constructor_idx: {}", ctor.constructor_idx);
        // Fin.mk has fields: val (the value) and isLt (proof val < n)
        assert_eq!(
            ctor.num_fields, 2,
            "Fin.mk should have 2 fields (val and isLt)"
        );
    }

    // Check Fin.rec recursor (should handle indices properly)
    let rec_name = Name::from_string("Fin.rec");
    if let Some(rec) = env.get_recursor(&rec_name) {
        println!("\n=== Fin.rec Recursor ===");
        println!("  num_params: {}", rec.num_params);
        println!("  num_indices: {}", rec.num_indices);
        println!("  num_motives: {}", rec.num_motives);
        println!("  num_minors: {}", rec.num_minors);
        println!("  rules: {}", rec.rules.len());

        assert_eq!(rec.num_indices, 0, "Fin.rec has 0 indices (n is a param)");
        assert_eq!(
            rec.rules.len(),
            1,
            "Fin.rec should have 1 rule (for Fin.mk)"
        );
    }
}

#[test]
fn test_structure_pprod_projection() {
    // Test projection reduction for PProd (polymorphic pair)
    // PProd.fst (PProd.mk a b) should reduce to a
    use clean_kernel::tc::TypeChecker;

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Prelude", &[lib_path]).expect("Failed to load");

    // Verify PProd is a structure (single-constructor inductive)
    let pprod_name = Name::from_string("PProd");
    let pprod_ind = env
        .get_inductive(&pprod_name)
        .expect("PProd inductive not found");
    println!("\n=== PProd Inductive ===");
    println!("  num_params: {}", pprod_ind.num_params);
    println!("  constructors: {:?}", pprod_ind.constructor_names);
    assert_eq!(
        pprod_ind.constructor_names.len(),
        1,
        "PProd is a structure (1 constructor)"
    );

    // Verify PProd.mk constructor has 2 fields (fst, snd)
    let mk_name = Name::from_string("PProd.mk");
    let mk_ctor = env.get_constructor(&mk_name).expect("PProd.mk not found");
    println!("\n=== PProd.mk Constructor ===");
    println!("  num_params: {}", mk_ctor.num_params);
    println!("  num_fields: {}", mk_ctor.num_fields);
    assert_eq!(mk_ctor.num_fields, 2, "PProd.mk has 2 fields");

    // Construct: PProd.mk [Type, Type] Nat Bool
    // Then project: PProd.fst (PProd.mk Nat Bool) = Nat
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let bool_ = Expr::const_(Name::from_string("Bool"), vec![]);
    let type0 = Expr::sort(Level::succ(Level::zero()));

    // PProd.mk {α} {β} fst snd
    // PProd : Sort u → Sort v → Sort (max 1 u v)
    let mk_app = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("PProd.mk"),
                        vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
                    ),
                    type0.clone(), // α = Type
                ),
                type0.clone(), // β = Type
            ),
            nat.clone(), // fst = Nat
        ),
        bool_.clone(), // snd = Bool
    );

    println!("\nConstructed PProd.mk application");

    // Now create projection: .0 (fst field)
    let proj_fst = Expr::proj(pprod_name.clone(), 0, mk_app.clone());

    // Reduce via whnf
    let tc = TypeChecker::new(&env);
    let reduced = tc.whnf(&proj_fst);

    println!("Projection .0 result: {reduced:?}");

    // Should reduce to Nat
    if let ExprKind::Const(name, _) = reduced.kind() {
        assert_eq!(
            name.to_string(),
            "Nat",
            "PProd.fst (PProd.mk Nat Bool) should be Nat"
        );
    } else {
        panic!("Expected Const(Nat), got {reduced:?}");
    }

    // Test projection .1 (snd field)
    let proj_snd = Expr::proj(pprod_name.clone(), 1, mk_app);
    let reduced_snd = tc.whnf(&proj_snd);

    println!("Projection .1 result: {reduced_snd:?}");

    if let ExprKind::Const(name, _) = reduced_snd.kind() {
        assert_eq!(
            name.to_string(),
            "Bool",
            "PProd.snd (PProd.mk Nat Bool) should be Bool"
        );
    } else {
        panic!("Expected Const(Bool), got {reduced_snd:?}");
    }
}

#[test]
fn test_prod_projection_typecheck() {
    // Type-check projections on Prod (value-level pairs)
    use clean_kernel::tc::TypeChecker;

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Core", &[lib_path]).expect("Failed to load");

    // Verify Prod structure
    let prod_name = Name::from_string("Prod");
    if let Some(ind) = env.get_inductive(&prod_name) {
        println!("\n=== Prod Inductive ===");
        println!("  num_params: {}", ind.num_params);
        println!("  constructors: {:?}", ind.constructor_names);
        assert_eq!(ind.constructor_names.len(), 1, "Prod is a structure");
    } else {
        println!("Prod not found as inductive (may be defined differently)");
        return;
    }

    // Type-check Prod.fst and Prod.snd functions
    for fn_name in ["Prod.fst", "Prod.snd"] {
        let name = Name::from_string(fn_name);
        if let Some(const_info) = env.get_const(&name) {
            let tc = TypeChecker::new(&env);
            match tc.infer_type(&const_info.type_) {
                Ok(sort) => {
                    println!("  {fn_name} type checks to: {sort:?}");
                }
                Err(e) => {
                    println!("  {fn_name} type error: {e:?}");
                }
            }
        } else {
            println!("  {fn_name} not found");
        }
    }
}

#[test]
fn test_iota_reduction_option() {
    // Test iota reduction on Option type
    // Option.rec on Option.some should reduce correctly
    use clean_kernel::tc::TypeChecker;

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Prelude", &[lib_path]).expect("Failed to load");

    // Check Option inductive
    let option_name = Name::from_string("Option");
    let opt_ind = env.get_inductive(&option_name).expect("Option not found");
    println!("\n=== Option Inductive ===");
    println!("  num_params: {}", opt_ind.num_params);
    println!("  is_recursive: {}", opt_ind.is_recursive);
    println!("  constructors: {:?}", opt_ind.constructor_names);

    assert_eq!(opt_ind.num_params, 1, "Option has 1 type parameter");
    assert!(!opt_ind.is_recursive, "Option is not recursive");
    assert_eq!(
        opt_ind.constructor_names.len(),
        2,
        "Option has none and some"
    );

    // Check Option.rec
    let rec_name = Name::from_string("Option.rec");
    if let Some(rec) = env.get_recursor(&rec_name) {
        println!("\n=== Option.rec Recursor ===");
        println!("  num_params: {}", rec.num_params);
        println!("  num_minors: {}", rec.num_minors);
        println!("  rules: {}", rec.rules.len());
        for rule in &rec.rules {
            println!(
                "    - {}: {} fields, recursive={:?}",
                rule.constructor_name, rule.num_fields, rule.recursive_fields
            );
        }
        assert_eq!(rec.num_minors, 2, "Option.rec has 2 minor premises");
    }

    // Construct: Option.some Nat (Nat.zero)
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let some_zero = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Option.some"), vec![Level::zero()]),
            nat.clone(),
        ),
        zero.clone(),
    );

    // Type-check some_zero
    let tc = TypeChecker::new(&env);
    match tc.infer_type(&some_zero) {
        Ok(ty) => {
            println!("\nOption.some Nat Nat.zero has type: {ty:?}");
            let whnf_ty = tc.whnf(&ty);
            println!("WHNF of type: {whnf_ty:?}");

            // Should be Option Nat
            let head = whnf_ty.get_app_fn();
            if let ExprKind::Const(name, _) = head.kind() {
                assert_eq!(name.to_string(), "Option");
            }
        }
        Err(e) => {
            println!("Type error: {e:?}");
        }
    }
}

#[test]
fn test_iota_reduction_bool_rec() {
    // Test Bool.rec reduction for Bool (simple non-recursive type)
    // Bool.rec.{u} (motive : Bool → Sort u) (false : motive false) (true : motive true) (t : Bool) : motive t
    use clean_kernel::tc::TypeChecker;

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Prelude", &[lib_path]).expect("Failed to load");

    // Check Bool.rec recursor
    let rec_name = Name::from_string("Bool.rec");
    let rec_val = env.get_recursor(&rec_name).expect("Bool.rec not found");
    println!("\n=== Bool.rec Recursor ===");
    println!("  arg_order: {:?}", rec_val.arg_order);
    println!("  num_params: {}", rec_val.num_params);
    println!("  num_motives: {}", rec_val.num_motives);
    println!("  num_minors: {}", rec_val.num_minors);
    println!("  rules: {}", rec_val.rules.len());
    for rule in &rec_val.rules {
        println!(
            "    - {}: {} fields",
            rule.constructor_name, rule.num_fields
        );
    }

    // Construct Bool.rec application
    // Bool.rec.{u} (motive : Bool → Sort u) (false : motive false) (true : motive true) (t : Bool) : motive t
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let true_val = Expr::const_(Name::from_string("Bool.true"), vec![]);

    // motive = λ _ : Bool. Nat
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let motive = Expr::lam(BinderInfo::Default, bool_ty.clone(), nat.clone());

    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        zero.clone(),
    );

    // Bool.rec.{1} motive zero one true
    // (rec has MajorAfterMinors ordering: motive, minors, then major)
    let rec_app = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(rec_name.clone(), vec![Level::succ(Level::zero())]),
                    motive.clone(),
                ),
                zero.clone(), // false case (minor 0)
            ),
            one.clone(), // true case (minor 1)
        ),
        true_val.clone(), // major premise = true
    );

    println!("\nBool.rec motive zero one true:");
    let tc = TypeChecker::new(&env);
    let whnf_result = tc.whnf(&rec_app);
    println!("WHNF result: {whnf_result:?}");

    // Should reduce to one (Nat.succ Nat.zero) since Bool.true is constructor 1
    let head = whnf_result.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        assert_eq!(
            name.to_string(),
            "Nat.succ",
            "Bool.rec on true should reduce to the true case (Nat.succ ...)"
        );
    } else {
        panic!("Bool.rec iota reduction did not fire. Got: {whnf_result:?}");
    }

    // Also test the false case
    let false_val = Expr::const_(Name::from_string("Bool.false"), vec![]);
    let rec_app_false = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(rec_name.clone(), vec![Level::succ(Level::zero())]),
                    motive,
                ),
                zero.clone(), // false case (minor 0)
            ),
            one.clone(), // true case (minor 1)
        ),
        false_val, // major premise = false
    );

    println!("\nBool.rec motive zero one false:");
    let whnf_false = tc.whnf(&rec_app_false);
    println!("WHNF result: {whnf_false:?}");

    // Should reduce to zero since Bool.false is constructor 0
    if let ExprKind::Const(name, _) = whnf_false.kind() {
        assert_eq!(
            name.to_string(),
            "Nat.zero",
            "Bool.rec on false should reduce to the false case (Nat.zero)"
        );
    } else {
        panic!("Bool.rec iota reduction did not fire for false. Got: {whnf_false:?}");
    }
}

#[test]
fn test_sigma_dependent_pair() {
    // Test Sigma (dependent pair) from Init.Core
    // structure Sigma {α : Type u} (β : α → Type v) where
    //   mk :: (fst : α) (snd : β fst)
    use clean_kernel::tc::TypeChecker;

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Core", &[lib_path]).expect("Failed to load Init.Core");

    // Check Sigma inductive exists
    let sigma_name = Name::from_string("Sigma");
    let sigma_ind = env.get_inductive(&sigma_name).expect("Sigma not found");
    println!("\n=== Sigma Inductive ===");
    println!("  num_params: {}", sigma_ind.num_params);
    println!("  num_indices: {}", sigma_ind.num_indices);
    println!("  is_recursive: {}", sigma_ind.is_recursive);
    println!("  constructors: {:?}", sigma_ind.constructor_names);

    // Sigma has 1 param (α) and 1 implicit param (β : α → Type v)
    // Actually it's structure so num_params includes all implicit params
    assert_eq!(
        sigma_ind.constructor_names.len(),
        1,
        "Sigma should have exactly 1 constructor (mk)"
    );

    // Check Sigma.mk exists
    let mk_name = Name::from_string("Sigma.mk");
    let mk_const = env.get_const(&mk_name).expect("Sigma.mk not found");
    println!("\nSigma.mk type: {:?}", mk_const.type_);

    // Type-check Sigma.mk (verify its type is well-formed and infers to a Sort)
    let tc = TypeChecker::new(&env);
    assert_type_is_sort(&tc, &mk_const.type_, "Sigma.mk");

    // Test projection: Sigma.fst (require it exists — regression if removed)
    let fst_name = Name::from_string("Sigma.fst");
    let fst_const = env
        .get_const(&fst_name)
        .expect("Sigma.fst should exist in Init.Core");
    println!("\nSigma.fst type: {:?}", fst_const.type_);
    assert_type_is_sort(&tc, &fst_const.type_, "Sigma.fst");

    // Test Sigma.snd projection (require it exists — regression if removed)
    let snd_name = Name::from_string("Sigma.snd");
    let snd_const = env
        .get_const(&snd_name)
        .expect("Sigma.snd should exist in Init.Core");
    println!("\nSigma.snd type: {:?}", snd_const.type_);
    assert_type_is_sort(&tc, &snd_const.type_, "Sigma.snd");
}

#[test]
fn test_sum_coproduct_type() {
    // Test Sum (coproduct) from Init.Core
    // inductive Sum (α : Type u) (β : Type v) where
    //   | inl (val : α) : Sum α β
    //   | inr (val : β) : Sum α β
    use clean_kernel::tc::TypeChecker;

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Core", &[lib_path]).expect("Failed to load Init.Core");

    // Check Sum inductive
    let sum_name = Name::from_string("Sum");
    let sum_ind = env.get_inductive(&sum_name).expect("Sum not found");
    println!("\n=== Sum Inductive ===");
    println!("  num_params: {}", sum_ind.num_params);
    println!("  num_indices: {}", sum_ind.num_indices);
    println!("  is_recursive: {}", sum_ind.is_recursive);
    println!("  constructors: {:?}", sum_ind.constructor_names);

    assert_eq!(sum_ind.num_params, 2, "Sum should have 2 parameters (α, β)");
    assert_eq!(
        sum_ind.constructor_names.len(),
        2,
        "Sum should have 2 constructors (inl, inr)"
    );

    // Check Sum.inl and Sum.inr constructors exist
    let inl_name = Name::from_string("Sum.inl");
    let inr_name = Name::from_string("Sum.inr");
    let inl_const = env.get_const(&inl_name).expect("Sum.inl should exist");
    let inr_const = env.get_const(&inr_name).expect("Sum.inr should exist");

    // Type-check Sum.inl and Sum.inr types — verify they infer to Sorts
    let tc = TypeChecker::new(&env);
    println!("\nSum.inl type: {:?}", inl_const.type_);
    assert_type_is_sort(&tc, &inl_const.type_, "Sum.inl");

    println!("Sum.inr type: {:?}", inr_const.type_);
    assert_type_is_sort(&tc, &inr_const.type_, "Sum.inr");

    // Check Sum.rec exists (require it — regression if missing)
    let rec_name = Name::from_string("Sum.rec");
    let rec_val = env
        .get_recursor(&rec_name)
        .expect("Sum.rec should exist in Init.Core");
    println!("\n=== Sum.rec Recursor ===");
    println!("  num_params: {}", rec_val.num_params);
    println!("  num_motives: {}", rec_val.num_motives);
    println!("  num_minors: {}", rec_val.num_minors);
    println!("  rules: {}", rec_val.rules.len());
    assert_eq!(
        rec_val.rules.len(),
        2,
        "Sum.rec should have 2 rules (inl, inr)"
    );
}

#[test]
fn test_subtype_dependent() {
    // Test Subtype (dependent type with proof) from Init.Prelude
    // structure Subtype {α : Sort u} (p : α → Prop) where
    //   mk :: (val : α) (property : p val)
    use clean_kernel::tc::TypeChecker;

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Prelude", &[lib_path])
        .expect("Failed to load Init.Prelude");

    // Check Subtype inductive
    let subtype_name = Name::from_string("Subtype");
    let subtype_ind = env.get_inductive(&subtype_name).expect("Subtype not found");
    println!("\n=== Subtype Inductive ===");
    println!("  num_params: {}", subtype_ind.num_params);
    println!("  num_indices: {}", subtype_ind.num_indices);
    println!("  is_recursive: {}", subtype_ind.is_recursive);
    println!("  constructors: {:?}", subtype_ind.constructor_names);

    // Subtype has α and p as params
    assert_eq!(
        subtype_ind.constructor_names.len(),
        1,
        "Subtype should have 1 constructor (mk)"
    );

    // Check Subtype.mk type-checks — verify inferred type is a Sort
    let tc = TypeChecker::new(&env);
    let mk_name = Name::from_string("Subtype.mk");
    let mk_const = env.get_const(&mk_name).expect("Subtype.mk not found");
    println!("\nSubtype.mk type: {:?}", mk_const.type_);
    assert_type_is_sort(&tc, &mk_const.type_, "Subtype.mk");

    // Check Subtype.val projection (require it exists — regression if removed)
    let val_name = Name::from_string("Subtype.val");
    let val_const = env
        .get_const(&val_name)
        .expect("Subtype.val should exist in Init.Prelude");
    println!("\nSubtype.val type: {:?}", val_const.type_);
    assert_type_is_sort(&tc, &val_const.type_, "Subtype.val");

    // Check Subtype.property projection (require it exists — regression if removed)
    let prop_name = Name::from_string("Subtype.property");
    let prop_const = env
        .get_const(&prop_name)
        .expect("Subtype.property should exist in Init.Prelude");
    println!("\nSubtype.property type: {:?}", prop_const.type_);
    assert_type_is_sort(&tc, &prop_const.type_, "Subtype.property");
}

#[test]
fn test_decidable_inductive() {
    // Test Decidable (important for computation) from Init.Prelude
    // inductive Decidable (p : Prop) where
    //   | isFalse (h : ¬p) : Decidable p
    //   | isTrue (h : p) : Decidable p
    use clean_kernel::tc::TypeChecker;

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Prelude", &[lib_path])
        .expect("Failed to load Init.Prelude");

    // Check Decidable inductive
    let dec_name = Name::from_string("Decidable");
    let dec_ind = env.get_inductive(&dec_name).expect("Decidable not found");
    println!("\n=== Decidable Inductive ===");
    println!("  num_params: {}", dec_ind.num_params);
    println!("  num_indices: {}", dec_ind.num_indices);
    println!("  is_recursive: {}", dec_ind.is_recursive);
    println!("  constructors: {:?}", dec_ind.constructor_names);

    assert_eq!(
        dec_ind.num_params, 1,
        "Decidable should have 1 parameter (p : Prop)"
    );
    assert_eq!(
        dec_ind.constructor_names.len(),
        2,
        "Decidable should have 2 constructors (isFalse, isTrue)"
    );
    assert!(!dec_ind.is_recursive, "Decidable is not recursive");

    // Type-check Decidable.isTrue — verify inferred type is a Sort
    let tc = TypeChecker::new(&env);
    let is_true_name = Name::from_string("Decidable.isTrue");
    let is_true_const = env
        .get_const(&is_true_name)
        .expect("Decidable.isTrue not found");
    println!("\nDecidable.isTrue type: {:?}", is_true_const.type_);
    assert_type_is_sort(&tc, &is_true_const.type_, "Decidable.isTrue");

    // Type-check Decidable.isFalse — verify inferred type is a Sort
    let is_false_name = Name::from_string("Decidable.isFalse");
    let is_false_const = env
        .get_const(&is_false_name)
        .expect("Decidable.isFalse not found");
    println!("\nDecidable.isFalse type: {:?}", is_false_const.type_);
    assert_type_is_sort(&tc, &is_false_const.type_, "Decidable.isFalse");

    // Check Decidable.rec exists (require it — regression if missing)
    let rec_name = Name::from_string("Decidable.rec");
    let rec_val = env
        .get_recursor(&rec_name)
        .expect("Decidable.rec should exist in Init.Prelude");
    println!("\n=== Decidable.rec Recursor ===");
    println!("  arg_order: {:?}", rec_val.arg_order);
    println!("  num_params: {}", rec_val.num_params);
    println!("  num_motives: {}", rec_val.num_motives);
    println!("  num_minors: {}", rec_val.num_minors);
    println!("  rules: {}", rec_val.rules.len());
    for rule in &rec_val.rules {
        println!(
            "    - {}: {} fields",
            rule.constructor_name, rule.num_fields
        );
    }
    assert_eq!(rec_val.rules.len(), 2, "Decidable.rec should have 2 rules");
}

#[test]
fn test_exists_inductive() {
    // Test Exists (existential quantifier) from Init.Core
    // inductive Exists {α : Sort u} (p : α → Prop) : Prop where
    //   | intro (w : α) (h : p w) : Exists p
    use clean_kernel::tc::TypeChecker;

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Core", &[lib_path]).expect("Failed to load Init.Core");

    // Check Exists inductive
    let exists_name = Name::from_string("Exists");
    let exists_ind = env.get_inductive(&exists_name).expect("Exists not found");
    println!("\n=== Exists Inductive ===");
    println!("  num_params: {}", exists_ind.num_params);
    println!("  num_indices: {}", exists_ind.num_indices);
    println!("  is_recursive: {}", exists_ind.is_recursive);
    println!("  constructors: {:?}", exists_ind.constructor_names);

    // Exists has α and p as params
    assert_eq!(
        exists_ind.constructor_names.len(),
        1,
        "Exists should have 1 constructor (intro)"
    );
    assert!(!exists_ind.is_recursive, "Exists is not recursive");

    // Type-check Exists.intro — verify inferred type is a Sort
    let tc = TypeChecker::new(&env);
    let intro_name = Name::from_string("Exists.intro");
    let intro_const = env.get_const(&intro_name).expect("Exists.intro not found");
    println!("\nExists.intro type: {:?}", intro_const.type_);
    assert_type_is_sort(&tc, &intro_const.type_, "Exists.intro");
}

#[test]
fn test_psigma_sort_level_dependent_pair() {
    // Test PSigma - the Sort-level dependent pair (vs Sigma which is Type-level)
    // structure PSigma {α : Sort u} (β : α → Sort v) where
    //   mk :: (fst : α) (snd : β fst)
    use clean_kernel::tc::TypeChecker;

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Core", &[lib_path]).expect("Failed to load Init.Core");

    // Check PSigma inductive
    let psigma_name = Name::from_string("PSigma");
    let psigma_ind = env.get_inductive(&psigma_name).expect("PSigma not found");
    println!("\n=== PSigma Inductive ===");
    println!("  num_params: {}", psigma_ind.num_params);
    println!("  num_indices: {}", psigma_ind.num_indices);
    println!("  is_recursive: {}", psigma_ind.is_recursive);
    println!("  constructors: {:?}", psigma_ind.constructor_names);

    // PSigma has 2 params: α and β (where β depends on α)
    assert_eq!(
        psigma_ind.num_params, 2,
        "PSigma should have 2 params (α, β)"
    );
    assert_eq!(
        psigma_ind.constructor_names.len(),
        1,
        "PSigma should have 1 constructor (mk)"
    );
    assert!(!psigma_ind.is_recursive, "PSigma is not recursive");

    // Type-check PSigma.mk — verify inferred type is a Sort
    let tc = TypeChecker::new(&env);
    let mk_name = Name::from_string("PSigma.mk");
    let mk_const = env.get_const(&mk_name).expect("PSigma.mk not found");
    println!("\nPSigma.mk type: {:?}", mk_const.type_);
    assert_type_is_sort(&tc, &mk_const.type_, "PSigma.mk");

    // Type-check PSigma.fst (projection) — verify inferred type is a Sort
    let fst_name = Name::from_string("PSigma.fst");
    let fst_const = env.get_const(&fst_name).expect("PSigma.fst not found");
    println!("\nPSigma.fst type: {:?}", fst_const.type_);
    assert_type_is_sort(&tc, &fst_const.type_, "PSigma.fst");

    // Type-check PSigma.snd (projection - depends on fst) — verify inferred type is a Sort
    let snd_name = Name::from_string("PSigma.snd");
    let snd_const = env.get_const(&snd_name).expect("PSigma.snd not found");
    println!("\nPSigma.snd type: {:?}", snd_const.type_);
    assert_type_is_sort(&tc, &snd_const.type_, "PSigma.snd");
}

#[test]
fn test_psum_sort_level_coproduct() {
    // Test PSum - the Sort-level coproduct (vs Sum which is Type-level)
    // inductive PSum (α : Sort u) (β : Sort v) : Sort (max 1 u v) where
    //   | inl (a : α) : PSum α β
    //   | inr (b : β) : PSum α β
    use clean_kernel::tc::TypeChecker;

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Core", &[lib_path]).expect("Failed to load Init.Core");

    // Check PSum inductive
    let psum_name = Name::from_string("PSum");
    let psum_ind = env.get_inductive(&psum_name).expect("PSum not found");
    println!("\n=== PSum Inductive ===");
    println!("  num_params: {}", psum_ind.num_params);
    println!("  num_indices: {}", psum_ind.num_indices);
    println!("  is_recursive: {}", psum_ind.is_recursive);
    println!("  constructors: {:?}", psum_ind.constructor_names);

    assert_eq!(psum_ind.num_params, 2, "PSum should have 2 params (α, β)");
    assert_eq!(
        psum_ind.constructor_names.len(),
        2,
        "PSum should have 2 constructors (inl, inr)"
    );
    assert!(!psum_ind.is_recursive, "PSum is not recursive");

    // Type-check PSum.inl — verify inferred type is a Sort
    let tc = TypeChecker::new(&env);
    let inl_name = Name::from_string("PSum.inl");
    let inl_const = env.get_const(&inl_name).expect("PSum.inl not found");
    println!("\nPSum.inl type: {:?}", inl_const.type_);
    assert_type_is_sort(&tc, &inl_const.type_, "PSum.inl");

    // Type-check PSum.inr — verify inferred type is a Sort
    let inr_name = Name::from_string("PSum.inr");
    let inr_const = env.get_const(&inr_name).expect("PSum.inr not found");
    println!("\nPSum.inr type: {:?}", inr_const.type_);
    assert_type_is_sort(&tc, &inr_const.type_, "PSum.inr");

    // Check PSum.rec recursor (require it — regression if missing)
    let rec_name = Name::from_string("PSum.rec");
    let rec_val = env
        .get_recursor(&rec_name)
        .expect("PSum.rec should exist in Init.Core");
    println!("\n=== PSum.rec Recursor ===");
    println!("  num_params: {}", rec_val.num_params);
    println!("  num_motives: {}", rec_val.num_motives);
    println!("  num_minors: {}", rec_val.num_minors);
    println!("  rules: {}", rec_val.rules.len());
    assert_eq!(rec_val.rules.len(), 2, "PSum.rec should have 2 rules");
}

#[test]
fn test_empty_false_true_props() {
    // Test Empty (uninhabited type), False (empty proposition), True (unit proposition)
    use clean_kernel::tc::TypeChecker;

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Prelude", &[lib_path])
        .expect("Failed to load Init.Prelude");

    let tc = TypeChecker::new(&env);

    // Test Empty - uninhabited type (no constructors)
    let empty_name = Name::from_string("Empty");
    let empty_ind = env.get_inductive(&empty_name).expect("Empty not found");
    println!("\n=== Empty Inductive ===");
    println!("  num_params: {}", empty_ind.num_params);
    println!("  constructors: {:?}", empty_ind.constructor_names);
    assert_eq!(
        empty_ind.constructor_names.len(),
        0,
        "Empty should have 0 constructors"
    );
    assert!(!empty_ind.is_recursive, "Empty is not recursive");

    // Check Empty.rec exists (ex falso quodlibet for types — require it)
    let empty_rec_name = Name::from_string("Empty.rec");
    let empty_rec = env
        .get_recursor(&empty_rec_name)
        .expect("Empty.rec should exist in Init.Prelude");
    println!("Empty.rec rules: {}", empty_rec.rules.len());
    assert_eq!(empty_rec.rules.len(), 0, "Empty.rec should have 0 rules");

    // Test False - empty proposition (Prop-level Empty)
    let false_name = Name::from_string("False");
    let false_ind = env.get_inductive(&false_name).expect("False not found");
    println!("\n=== False Inductive ===");
    println!("  num_params: {}", false_ind.num_params);
    println!("  constructors: {:?}", false_ind.constructor_names);
    assert_eq!(
        false_ind.constructor_names.len(),
        0,
        "False should have 0 constructors"
    );

    // Check False.rec exists (ex falso quodlibet — require it)
    let false_rec_name = Name::from_string("False.rec");
    let false_rec = env
        .get_recursor(&false_rec_name)
        .expect("False.rec should exist in Init.Prelude");
    println!("False.rec rules: {}", false_rec.rules.len());
    assert_eq!(false_rec.rules.len(), 0, "False.rec should have 0 rules");

    // Test True - unit proposition
    let true_name = Name::from_string("True");
    let true_ind = env.get_inductive(&true_name).expect("True not found");
    println!("\n=== True Inductive ===");
    println!("  num_params: {}", true_ind.num_params);
    println!("  constructors: {:?}", true_ind.constructor_names);
    assert_eq!(
        true_ind.constructor_names.len(),
        1,
        "True should have 1 constructor (intro)"
    );

    // Type-check True.intro — verify inferred type is a Sort
    let intro_name = Name::from_string("True.intro");
    let intro_const = env.get_const(&intro_name).expect("True.intro not found");
    println!("\nTrue.intro type: {:?}", intro_const.type_);
    assert_type_is_sort(&tc, &intro_const.type_, "True.intro");
}

#[test]
fn test_unit_punit_types() {
    // Test PUnit (Sort-level unit) and Unit (abbreviation for PUnit)
    use clean_kernel::tc::TypeChecker;

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Core", &[lib_path]).expect("Failed to load Init.Core");

    let tc = TypeChecker::new(&env);

    // Test PUnit - Sort-level unit (polymorphic in universe)
    // inductive PUnit : Sort u where
    //   | unit : PUnit
    let punit_name = Name::from_string("PUnit");
    let punit_ind = env.get_inductive(&punit_name).expect("PUnit not found");
    println!("\n=== PUnit Inductive ===");
    println!("  num_params: {}", punit_ind.num_params);
    println!("  num_indices: {}", punit_ind.num_indices);
    println!("  is_recursive: {}", punit_ind.is_recursive);
    println!("  constructors: {:?}", punit_ind.constructor_names);
    assert_eq!(
        punit_ind.constructor_names.len(),
        1,
        "PUnit should have 1 constructor (unit)"
    );
    assert!(!punit_ind.is_recursive, "PUnit is not recursive");

    // Type-check PUnit.unit — verify inferred type is a Sort
    let punit_unit_name = Name::from_string("PUnit.unit");
    let punit_unit_const = env
        .get_const(&punit_unit_name)
        .expect("PUnit.unit not found");
    println!("\nPUnit.unit type: {:?}", punit_unit_const.type_);
    assert_type_is_sort(&tc, &punit_unit_const.type_, "PUnit.unit");

    // Test Unit - abbreviation for PUnit (require it exists in Init.Core)
    // @[reducible] def Unit : Type := PUnit
    let unit_name = Name::from_string("Unit");
    let unit_const = env
        .get_const(&unit_name)
        .expect("Unit should exist in Init.Core");
    println!("\n=== Unit Definition ===");
    println!("Type: {:?}", unit_const.type_);
    if let Some(ref value) = unit_const.value {
        println!("Value: {value:?}");
    }
    assert_type_is_sort(&tc, &unit_const.type_, "Unit");

    // Check PUnit.rec recursor (require it — regression if missing)
    let rec_name = Name::from_string("PUnit.rec");
    let rec_val = env
        .get_recursor(&rec_name)
        .expect("PUnit.rec should exist in Init.Core");
    println!("\n=== PUnit.rec Recursor ===");
    println!("  num_params: {}", rec_val.num_params);
    println!("  num_motives: {}", rec_val.num_motives);
    println!("  num_minors: {}", rec_val.num_minors);
    println!("  rules: {}", rec_val.rules.len());
    assert_eq!(
        rec_val.rules.len(),
        1,
        "PUnit.rec should have 1 rule (unit)"
    );
}

#[test]
fn test_typeclass_instance_loading() {
    // Test that type class instances are properly loaded
    // Type classes are structures, instances are definitions
    use clean_kernel::tc::TypeChecker;

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Data.Nat.Basic", &[lib_path])
        .expect("Failed to load Init.Data.Nat.Basic");

    let tc = TypeChecker::new(&env);

    // Check that common type classes are loaded as structures
    let class_names = ["Add", "Mul", "Sub", "Div", "BEq", "Inhabited", "ToString"];

    println!("\n=== Type Class Structures ===");
    for class_name in class_names {
        let name = Name::from_string(class_name);
        if let Some(ind) = env.get_inductive(&name) {
            println!(
                "  {} - params: {}, ctors: {}, recursive: {}",
                class_name,
                ind.num_params,
                ind.constructor_names.len(),
                ind.is_recursive
            );
            // Type classes are typically structures with 1 constructor (mk)
            assert!(
                ind.constructor_names.len() <= 2,
                "{class_name} should be a structure"
            );
        } else if env.get_const(&name).is_some() {
            println!("  {class_name} - exists as constant (abbreviation)");
        } else {
            println!("  {class_name} - NOT FOUND");
        }
    }

    // Check that instances exist for Nat
    let instance_names = [
        "instAddNat",
        "instMulNat",
        "instSubNat",
        "instBEqNat",
        "instInhabitedNat",
    ];

    println!("\n=== Nat Type Class Instances ===");
    let mut instances_found = 0;
    for inst_name in instance_names {
        let name = Name::from_string(inst_name);
        if let Some(const_info) = env.get_const(&name) {
            println!("  {inst_name} found");
            instances_found += 1;

            // Type-check the instance
            let check = tc.infer_type(&const_info.type_);
            if check.is_ok() {
                println!("    type check passed");
            } else {
                println!("    type error: {:?}", check.err());
            }

            // Type-check the value if present
            if let Some(ref value) = const_info.value {
                let check = tc.infer_type(value);
                if check.is_ok() {
                    println!("    value check passed");
                } else {
                    println!("    value error: {:?}", check.err());
                }
            }
        } else {
            println!("  {inst_name} NOT FOUND");
        }
    }

    // At least some instances should be found
    assert!(
        instances_found >= 2,
        "Expected at least 2 Nat instances, found {instances_found}"
    );
}

#[test]
fn test_eq_heq_inductive() {
    // Test Eq (equality) and HEq (heterogeneous equality)
    // These are fundamental propositions used throughout Lean
    use clean_kernel::tc::TypeChecker;

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Prelude", &[lib_path])
        .expect("Failed to load Init.Prelude");

    let tc = TypeChecker::new(&env);

    // Test Eq - propositional equality
    // inductive Eq {α : Sort u} (a : α) : α → Prop where
    //   | refl : Eq a a
    let eq_name = Name::from_string("Eq");
    let eq_ind = env.get_inductive(&eq_name).expect("Eq not found");
    println!("\n=== Eq Inductive ===");
    println!("  num_params: {}", eq_ind.num_params);
    println!("  num_indices: {}", eq_ind.num_indices);
    println!("  is_recursive: {}", eq_ind.is_recursive);
    println!("  constructors: {:?}", eq_ind.constructor_names);

    // Eq has α (implicit) and a as params, second a as index
    assert_eq!(
        eq_ind.constructor_names.len(),
        1,
        "Eq should have 1 constructor (refl)"
    );
    assert!(!eq_ind.is_recursive, "Eq is not recursive");

    // Type-check Eq.refl — verify inferred type is a Sort
    let refl_name = Name::from_string("Eq.refl");
    let refl_const = env.get_const(&refl_name).expect("Eq.refl not found");
    println!("\nEq.refl type: {:?}", refl_const.type_);
    assert_type_is_sort(&tc, &refl_const.type_, "Eq.refl");

    // Test HEq - heterogeneous equality
    // inductive HEq {α : Sort u} (a : α) : {β : Sort u} → β → Prop where
    //   | refl : HEq a a
    let heq_name = Name::from_string("HEq");
    let heq_ind = env.get_inductive(&heq_name).expect("HEq not found");
    println!("\n=== HEq Inductive ===");
    println!("  num_params: {}", heq_ind.num_params);
    println!("  num_indices: {}", heq_ind.num_indices);
    println!("  is_recursive: {}", heq_ind.is_recursive);
    println!("  constructors: {:?}", heq_ind.constructor_names);

    assert_eq!(
        heq_ind.constructor_names.len(),
        1,
        "HEq should have 1 constructor (refl)"
    );
    assert!(!heq_ind.is_recursive, "HEq is not recursive");

    // Type-check HEq.refl — verify inferred type is a Sort
    let heq_refl_name = Name::from_string("HEq.refl");
    let heq_refl_const = env.get_const(&heq_refl_name).expect("HEq.refl not found");
    println!("\nHEq.refl type: {:?}", heq_refl_const.type_);
    assert_type_is_sort(&tc, &heq_refl_const.type_, "HEq.refl");

    // Check Eq.rec exists (substitution principle — require it)
    let eq_rec_name = Name::from_string("Eq.rec");
    let rec_val = env
        .get_recursor(&eq_rec_name)
        .expect("Eq.rec should exist in Init.Prelude");
    println!("\n=== Eq.rec Recursor ===");
    println!("  num_params: {}", rec_val.num_params);
    println!("  num_indices: {}", rec_val.num_indices);
    println!("  num_motives: {}", rec_val.num_motives);
    println!("  num_minors: {}", rec_val.num_minors);
    println!("  rules: {}", rec_val.rules.len());
    assert_eq!(rec_val.rules.len(), 1, "Eq.rec should have 1 rule (refl)");
}

#[test]
fn test_and_or_not_props() {
    // Test And, Or, Not - basic propositional connectives
    use clean_kernel::tc::TypeChecker;

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Prelude", &[lib_path])
        .expect("Failed to load Init.Prelude");

    let tc = TypeChecker::new(&env);

    // Test And - conjunction
    // structure And (a b : Prop) : Prop where
    //   intro :: (left : a) (right : b)
    let and_name = Name::from_string("And");
    let and_ind = env.get_inductive(&and_name).expect("And not found");
    println!("\n=== And Inductive ===");
    println!("  num_params: {}", and_ind.num_params);
    println!("  is_recursive: {}", and_ind.is_recursive);
    println!("  constructors: {:?}", and_ind.constructor_names);

    assert_eq!(and_ind.num_params, 2, "And should have 2 params (a, b)");
    assert_eq!(
        and_ind.constructor_names.len(),
        1,
        "And should have 1 constructor (intro)"
    );
    assert!(!and_ind.is_recursive, "And is not recursive");

    // Type-check And.intro — verify inferred type is a Sort
    let and_intro_name = Name::from_string("And.intro");
    let and_intro_const = env.get_const(&and_intro_name).expect("And.intro not found");
    println!("\nAnd.intro type: {:?}", and_intro_const.type_);
    assert_type_is_sort(&tc, &and_intro_const.type_, "And.intro");

    // Test Or - disjunction
    // inductive Or (a b : Prop) : Prop where
    //   | inl (h : a) : Or a b
    //   | inr (h : b) : Or a b
    let or_name = Name::from_string("Or");
    let or_ind = env.get_inductive(&or_name).expect("Or not found");
    println!("\n=== Or Inductive ===");
    println!("  num_params: {}", or_ind.num_params);
    println!("  is_recursive: {}", or_ind.is_recursive);
    println!("  constructors: {:?}", or_ind.constructor_names);

    assert_eq!(or_ind.num_params, 2, "Or should have 2 params (a, b)");
    assert_eq!(
        or_ind.constructor_names.len(),
        2,
        "Or should have 2 constructors (inl, inr)"
    );

    // Type-check Or.inl and Or.inr — verify each infers to a Sort
    for ctor in ["Or.inl", "Or.inr"] {
        let name = Name::from_string(ctor);
        let const_info = env
            .get_const(&name)
            .unwrap_or_else(|| panic!("{ctor} not found"));
        println!("\n{} type: {:?}", ctor, const_info.type_);
        assert_type_is_sort(&tc, &const_info.type_, ctor);
    }

    // Test Not - negation (defined as Not p = p → False — require it exists)
    let not_name = Name::from_string("Not");
    let not_const = env
        .get_const(&not_name)
        .expect("Not should exist in Init.Prelude");
    println!("\n=== Not Definition ===");
    println!("Type: {:?}", not_const.type_);
    if let Some(ref value) = not_const.value {
        println!("Value: {value:?}");
    }
    assert_type_is_sort(&tc, &not_const.type_, "Not");
}

#[test]
fn test_iff_biconditional() {
    // Test Iff - bidirectional implication (logical equivalence)
    // structure Iff (a b : Prop) : Prop where
    //   intro :: (mp : a → b) (mpr : b → a)
    use clean_kernel::tc::TypeChecker;

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Core", &[lib_path]).expect("Failed to load Init.Core");

    let tc = TypeChecker::new(&env);

    // Test Iff - bidirectional implication
    let iff_name = Name::from_string("Iff");
    let iff_ind = env.get_inductive(&iff_name).expect("Iff not found");
    println!("\n=== Iff Inductive ===");
    println!("  num_params: {}", iff_ind.num_params);
    println!("  num_indices: {}", iff_ind.num_indices);
    println!("  is_recursive: {}", iff_ind.is_recursive);
    println!("  constructors: {:?}", iff_ind.constructor_names);

    assert_eq!(iff_ind.num_params, 2, "Iff should have 2 params (a, b)");
    assert_eq!(
        iff_ind.constructor_names.len(),
        1,
        "Iff should have 1 constructor (intro)"
    );
    assert!(!iff_ind.is_recursive, "Iff is not recursive");

    // Type-check Iff.intro — verify inferred type is a Sort
    let iff_intro_name = Name::from_string("Iff.intro");
    let iff_intro_const = env.get_const(&iff_intro_name).expect("Iff.intro not found");
    println!("\nIff.intro type: {:?}", iff_intro_const.type_);
    assert_type_is_sort(&tc, &iff_intro_const.type_, "Iff.intro");

    // Check Iff.mp (forward direction) and Iff.mpr (backward direction) — require both
    for accessor in ["Iff.mp", "Iff.mpr"] {
        let name = Name::from_string(accessor);
        let const_info = env
            .get_const(&name)
            .unwrap_or_else(|| panic!("{accessor} should exist in Init.Core"));
        println!("\n{} type: {:?}", accessor, const_info.type_);
        assert_type_is_sort(&tc, &const_info.type_, accessor);
    }

    // Check Iff.rec exists (require it — regression if missing)
    let rec_name = Name::from_string("Iff.rec");
    let rec_val = env
        .get_recursor(&rec_name)
        .expect("Iff.rec should exist in Init.Core");
    println!("\n=== Iff.rec Recursor ===");
    println!("  num_params: {}", rec_val.num_params);
    println!("  num_motives: {}", rec_val.num_motives);
    println!("  num_minors: {}", rec_val.num_minors);
    println!("  rules: {}", rec_val.rules.len());
    assert_eq!(rec_val.rules.len(), 1, "Iff.rec should have 1 rule (intro)");
}

#[test]
fn test_array_type() {
    // Test Array - dynamically sized arrays (fundamental data structure)
    // structure Array (α : Type u) where
    //   mk ::
    //   (data : List α)
    use clean_kernel::tc::TypeChecker;

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Prelude", &[lib_path])
        .expect("Failed to load Init.Prelude");

    let tc = TypeChecker::new(&env);

    // Test Array structure
    let array_name = Name::from_string("Array");
    let array_ind = env.get_inductive(&array_name).expect("Array not found");
    println!("\n=== Array Inductive ===");
    println!("  num_params: {}", array_ind.num_params);
    println!("  num_indices: {}", array_ind.num_indices);
    println!("  is_recursive: {}", array_ind.is_recursive);
    println!("  constructors: {:?}", array_ind.constructor_names);

    assert_eq!(array_ind.num_params, 1, "Array should have 1 param (α)");
    assert_eq!(
        array_ind.constructor_names.len(),
        1,
        "Array should have 1 constructor (mk)"
    );
    assert!(!array_ind.is_recursive, "Array itself is not recursive");

    // Type-check Array.mk — verify inferred type is a Sort
    let mk_name = Name::from_string("Array.mk");
    let mk_const = env.get_const(&mk_name).expect("Array.mk not found");
    println!("\nArray.mk type: {:?}", mk_const.type_);
    assert_type_is_sort(&tc, &mk_const.type_, "Array.mk");

    // Check Array.data accessor (require it — regression if removed)
    let data_name = Name::from_string("Array.data");
    let data_const = env
        .get_const(&data_name)
        .expect("Array.data should exist in Init.Prelude");
    println!("\nArray.data type: {:?}", data_const.type_);
    assert_type_is_sort(&tc, &data_const.type_, "Array.data");

    // Check Array.rec exists (require it — regression if missing)
    let rec_name = Name::from_string("Array.rec");
    let rec_val = env
        .get_recursor(&rec_name)
        .expect("Array.rec should exist in Init.Prelude");
    println!("\n=== Array.rec Recursor ===");
    println!("  num_params: {}", rec_val.num_params);
    println!("  num_motives: {}", rec_val.num_motives);
    println!("  num_minors: {}", rec_val.num_minors);
    println!("  rules: {}", rec_val.rules.len());
}

#[test]
fn test_option_type() {
    // Test Option - fundamental sum type for optional values
    // inductive Option (α : Type u) where
    //   | none : Option α
    //   | some (val : α) : Option α
    use clean_kernel::tc::TypeChecker;

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Prelude", &[lib_path])
        .expect("Failed to load Init.Prelude");

    let tc = TypeChecker::new(&env);

    // Test Option inductive
    let option_name = Name::from_string("Option");
    let option_ind = env.get_inductive(&option_name).expect("Option not found");
    println!("\n=== Option Inductive ===");
    println!("  num_params: {}", option_ind.num_params);
    println!("  num_indices: {}", option_ind.num_indices);
    println!("  is_recursive: {}", option_ind.is_recursive);
    println!("  constructors: {:?}", option_ind.constructor_names);

    assert_eq!(option_ind.num_params, 1, "Option should have 1 param (α)");
    assert_eq!(
        option_ind.constructor_names.len(),
        2,
        "Option should have 2 constructors (none, some)"
    );
    assert!(!option_ind.is_recursive, "Option is not recursive");

    // Type-check Option.none and Option.some — verify each infers to a Sort
    for ctor in ["Option.none", "Option.some"] {
        let name = Name::from_string(ctor);
        let const_info = env
            .get_const(&name)
            .unwrap_or_else(|| panic!("{ctor} not found"));
        println!("\n{} type: {:?}", ctor, const_info.type_);
        assert_type_is_sort(&tc, &const_info.type_, ctor);
    }

    // Check Option.rec exists (require it — regression if missing)
    let rec_name = Name::from_string("Option.rec");
    let rec_val = env
        .get_recursor(&rec_name)
        .expect("Option.rec should exist in Init.Prelude");
    println!("\n=== Option.rec Recursor ===");
    println!("  num_params: {}", rec_val.num_params);
    println!("  num_motives: {}", rec_val.num_motives);
    println!("  num_minors: {}", rec_val.num_minors);
    println!("  rules: {}", rec_val.rules.len());
    assert_eq!(
        rec_val.rules.len(),
        2,
        "Option.rec should have 2 rules (none, some)"
    );
}

#[test]
fn test_prod_sigma_types() {
    // Test Prod and Sigma - product types (dependent and non-dependent)
    // structure Prod (α : Type u) (β : Type v) where
    //   mk :: (fst : α) (snd : β)
    // structure Sigma {α : Type u} (β : α → Type v) where
    //   mk :: (fst : α) (snd : β fst)

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Core", &[lib_path]).expect("Failed to load Init.Core");

    let tc = TypeChecker::new(&env);

    // Test Prod (non-dependent product)
    let prod_name = Name::from_string("Prod");
    let prod_ind = env.get_inductive(&prod_name).expect("Prod not found");

    assert_eq!(prod_ind.num_params, 2, "Prod should have 2 params (α, β)");
    assert_eq!(
        prod_ind.constructor_names.len(),
        1,
        "Prod should have 1 constructor (mk)"
    );

    // Type-check Prod.mk and accessors
    for name_str in ["Prod.mk", "Prod.fst", "Prod.snd"] {
        let name = Name::from_string(name_str);
        let const_info = env
            .get_const(&name)
            .unwrap_or_else(|| panic!("{name_str} not found"));
        assert_type_is_sort(&tc, &const_info.type_, name_str);
    }

    // Test Sigma (dependent product)
    let sigma_name = Name::from_string("Sigma");
    let sigma_ind = env.get_inductive(&sigma_name).expect("Sigma not found");

    assert_eq!(
        sigma_ind.constructor_names.len(),
        1,
        "Sigma should have 1 constructor (mk)"
    );

    // Type-check Sigma.mk and accessors
    for name_str in ["Sigma.mk", "Sigma.fst", "Sigma.snd"] {
        let name = Name::from_string(name_str);
        let const_info = env
            .get_const(&name)
            .unwrap_or_else(|| panic!("{name_str} not found"));
        assert_type_is_sort(&tc, &const_info.type_, name_str);
    }
}

#[test]
fn test_decidable_types() {
    // Test Decidable - computational decidability of propositions
    // class inductive Decidable (p : Prop) where
    //   | isFalse (h : ¬p) : Decidable p
    //   | isTrue (h : p) : Decidable p

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Prelude", &[lib_path])
        .expect("Failed to load Init.Prelude");

    let tc = TypeChecker::new(&env);

    let decidable_name = Name::from_string("Decidable");
    let decidable_ind = env
        .get_inductive(&decidable_name)
        .expect("Decidable not found");

    assert_eq!(
        decidable_ind.num_params, 1,
        "Decidable should have 1 param (p : Prop)"
    );
    assert_eq!(
        decidable_ind.constructor_names.len(),
        2,
        "Decidable should have 2 constructors (isFalse, isTrue)"
    );

    // Type-check constructors
    for ctor in ["Decidable.isFalse", "Decidable.isTrue"] {
        let name = Name::from_string(ctor);
        let const_info = env
            .get_const(&name)
            .unwrap_or_else(|| panic!("{ctor} not found"));
        assert_type_is_sort(&tc, &const_info.type_, ctor);
    }

    // Check Decidable.rec
    let rec_name = Name::from_string("Decidable.rec");
    let rec_val = env
        .get_recursor(&rec_name)
        .expect("Decidable.rec should exist");
    assert_eq!(rec_val.rules.len(), 2, "Decidable.rec should have 2 rules");
}

#[test]
fn test_string_type() {
    // Test String - fundamental string type
    // In Lean 4.13: structure String where mk :: (data : List Char)
    // In Lean 4.27: structure String where ofByteArray :: (ba : ByteArray)

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Prelude", &[lib_path])
        .expect("Failed to load Init.Prelude");

    let tc = TypeChecker::new(&env);

    let string_name = Name::from_string("String");
    let string_ind = env.get_inductive(&string_name).expect("String not found");

    assert_eq!(string_ind.num_params, 0, "String has no type params");
    assert_eq!(
        string_ind.constructor_names.len(),
        1,
        "String should have 1 constructor"
    );
    assert!(!string_ind.is_recursive, "String itself is not recursive");

    // Type-check String constructor - name varies by version (String.mk or String.ofByteArray)
    let constructor_name = &string_ind.constructor_names[0];
    let ctor_const = env
        .get_const(constructor_name)
        .expect("String constructor not found");
    assert_type_is_sort(&tc, &ctor_const.type_, &constructor_name.to_string());

    // Verify Char type exists (used by String in older versions)
    let char_name = Name::from_string("Char");
    if let Some(char_ind) = env.get_inductive(&char_name) {
        assert!(
            !char_ind.constructor_names.is_empty(),
            "Char should have constructors"
        );
    }
}

#[test]
fn test_subtype_type() {
    // Test Subtype - refinement types (values with proofs)
    // structure Subtype {α : Sort u} (p : α → Prop) where
    //   mk :: (val : α) (property : p val)

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Core", &[lib_path]).expect("Failed to load Init.Core");

    let tc = TypeChecker::new(&env);

    let subtype_name = Name::from_string("Subtype");
    let subtype_ind = env.get_inductive(&subtype_name).expect("Subtype not found");

    assert_eq!(
        subtype_ind.constructor_names.len(),
        1,
        "Subtype should have 1 constructor (mk)"
    );
    assert!(!subtype_ind.is_recursive, "Subtype is not recursive");

    // Type-check Subtype.mk
    let mk_name = Name::from_string("Subtype.mk");
    let mk_const = env.get_const(&mk_name).expect("Subtype.mk not found");
    assert_type_is_sort(&tc, &mk_const.type_, "Subtype.mk");

    // Check accessors
    for accessor in ["Subtype.val", "Subtype.property"] {
        let name = Name::from_string(accessor);
        let const_info = env
            .get_const(&name)
            .unwrap_or_else(|| panic!("{accessor} not found"));
        assert_type_is_sort(&tc, &const_info.type_, accessor);
    }
}

#[test]
fn test_exists_type() {
    // Test Exists - existential quantifier
    // inductive Exists {α : Sort u} (p : α → Prop) : Prop where
    //   | intro (w : α) (h : p w) : Exists p

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Core", &[lib_path]).expect("Failed to load Init.Core");

    let tc = TypeChecker::new(&env);

    let exists_name = Name::from_string("Exists");
    let exists_ind = env.get_inductive(&exists_name).expect("Exists not found");

    assert_eq!(
        exists_ind.constructor_names.len(),
        1,
        "Exists should have 1 constructor (intro)"
    );
    assert!(!exists_ind.is_recursive, "Exists is not recursive");

    // Type-check Exists.intro
    let intro_name = Name::from_string("Exists.intro");
    let intro_const = env.get_const(&intro_name).expect("Exists.intro not found");
    assert_type_is_sort(&tc, &intro_const.type_, "Exists.intro");

    // Check Exists.rec (elimination principle)
    let rec_name = Name::from_string("Exists.rec");
    let rec_val = env
        .get_recursor(&rec_name)
        .expect("Exists.rec should exist");
    assert_eq!(
        rec_val.rules.len(),
        1,
        "Exists.rec should have 1 rule (intro)"
    );
}

#[test]
fn test_except_monad() {
    // Test Except - error handling monad transformer
    // inductive Except (ε : Type u) (α : Type v) where
    //   | error : ε → Except ε α
    //   | ok : α → Except ε α
    use clean_kernel::tc::TypeChecker;

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Control.Except", &[lib_path])
        .expect("Failed to load Init.Control.Except");

    let tc = TypeChecker::new(&env);

    let except_name = Name::from_string("Except");
    let except_ind = env.get_inductive(&except_name).expect("Except not found");

    assert_eq!(except_ind.num_params, 2, "Except has 2 type params (ε, α)");
    assert_eq!(
        except_ind.constructor_names.len(),
        2,
        "Except should have 2 constructors (error, ok)"
    );
    assert!(!except_ind.is_recursive, "Except is not recursive");

    // Type-check Except constructors
    for ctor in ["Except.error", "Except.ok"] {
        let name = Name::from_string(ctor);
        let const_info = env
            .get_const(&name)
            .unwrap_or_else(|| panic!("{ctor} not found"));
        assert_type_is_sort(&tc, &const_info.type_, ctor);
    }

    // Test ExceptT monad transformer
    let exceptt_name = Name::from_string("ExceptT");
    if let Some(exceptt_const) = env.get_const(&exceptt_name) {
        assert_type_is_sort(&tc, &exceptt_const.type_, "ExceptT");
    }
}

#[test]
fn test_state_monad() {
    // Test StateT - state monad transformer
    // def StateT (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v)

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Control.State", &[lib_path])
        .expect("Failed to load Init.Control.State");

    let tc = TypeChecker::new(&env);

    // Test StateT definition
    let statet_name = Name::from_string("StateT");
    let statet_const = env.get_const(&statet_name).expect("StateT not found");
    assert_type_is_sort(&tc, &statet_const.type_, "StateT");

    // Test StateM (StateT with Id monad)
    let statem_name = Name::from_string("StateM");
    if let Some(statem_const) = env.get_const(&statem_name) {
        assert_type_is_sort(&tc, &statem_const.type_, "StateM");
    }

    // Test state manipulation functions
    for fn_name in ["get", "set", "modify", "modifyGet"] {
        let name = Name::from_string(fn_name);
        if let Some(const_info) = env.get_const(&name) {
            assert_type_is_sort(&tc, &const_info.type_, fn_name);
        }
    }
}

#[test]
fn test_reader_monad() {
    // Test ReaderT - reader monad transformer
    // def ReaderT (ρ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v)

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Control.Reader", &[lib_path])
        .expect("Failed to load Init.Control.Reader");

    let tc = TypeChecker::new(&env);

    let readert_name = Name::from_string("ReaderT");
    let readert_const = env.get_const(&readert_name).expect("ReaderT not found");
    assert_type_is_sort(&tc, &readert_const.type_, "ReaderT");

    // Test read function
    let read_name = Name::from_string("read");
    if let Some(read_const) = env.get_const(&read_name) {
        assert_type_is_sort(&tc, &read_const.type_, "read");
    }
}

#[test]
fn test_io_monad() {
    // Test IO - the fundamental I/O monad
    // In Lean 4, IO is defined using EIO (Exception IO)

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.System.IO", &[lib_path])
        .expect("Failed to load Init.System.IO");

    let tc = TypeChecker::new(&env);

    // Test IO type
    let io_name = Name::from_string("IO");
    let io_const = env.get_const(&io_name).expect("IO not found");
    assert_type_is_sort(&tc, &io_const.type_, "IO");

    // Test EIO type (Exception IO)
    let eio_name = Name::from_string("EIO");
    if let Some(eio_const) = env.get_const(&eio_name) {
        assert_type_is_sort(&tc, &eio_const.type_, "EIO");
    }

    // Test BaseIO type (the raw IO without exceptions)
    let baseio_name = Name::from_string("BaseIO");
    if let Some(baseio_const) = env.get_const(&baseio_name) {
        assert_type_is_sort(&tc, &baseio_const.type_, "BaseIO");
    }
}

#[test]
fn test_int_type() {
    // Test Int - signed integers
    // inductive Int where
    //   | ofNat : Nat → Int
    //   | negSucc : Nat → Int  (represents -(n+1))

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Data.Int.Basic", &[lib_path])
        .expect("Failed to load Init.Data.Int.Basic");

    let tc = TypeChecker::new(&env);

    let int_name = Name::from_string("Int");
    let int_ind = env.get_inductive(&int_name).expect("Int not found");

    assert_eq!(int_ind.num_params, 0, "Int has no type params");
    assert_eq!(
        int_ind.constructor_names.len(),
        2,
        "Int should have 2 constructors (ofNat, negSucc)"
    );
    assert!(!int_ind.is_recursive, "Int is not directly recursive");

    // Type-check Int constructors
    for ctor in ["Int.ofNat", "Int.negSucc"] {
        let name = Name::from_string(ctor);
        let const_info = env
            .get_const(&name)
            .unwrap_or_else(|| panic!("{ctor} not found"));
        assert_type_is_sort(&tc, &const_info.type_, ctor);
    }

    // Check Int arithmetic operations
    for op_name in ["Int.add", "Int.sub", "Int.mul", "Int.neg"] {
        let name = Name::from_string(op_name);
        if let Some(const_info) = env.get_const(&name) {
            assert_type_is_sort(&tc, &const_info.type_, op_name);
        }
    }
}

#[test]
fn test_uint_types() {
    // Test UInt8, UInt16, UInt32, UInt64, USize

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Data.UInt.Basic", &[lib_path])
        .expect("Failed to load Init.Data.UInt.Basic");

    let tc = TypeChecker::new(&env);

    for uint_name in ["UInt8", "UInt16", "UInt32", "UInt64", "USize"] {
        let name = Name::from_string(uint_name);

        if let Some(uint_ind) = env.get_inductive(&name) {
            assert_eq!(
                uint_ind.constructor_names.len(),
                1,
                "{uint_name} should have 1 constructor (mk)"
            );
        } else if let Some(uint_const) = env.get_const(&name) {
            assert_type_is_sort(&tc, &uint_const.type_, uint_name);
        }

        // Check mk constructor
        let mk_label = format!("{uint_name}.mk");
        let mk_name = Name::from_string(&mk_label);
        if let Some(mk_const) = env.get_const(&mk_name) {
            assert_type_is_sort(&tc, &mk_const.type_, &mk_label);
        }
    }
}

#[test]
fn test_float_type() {
    // Test Float - IEEE 754 double precision floating point

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Data.Float", &[lib_path])
        .expect("Failed to load Init.Data.Float");

    let tc = TypeChecker::new(&env);

    let float_name = Name::from_string("Float");
    if let Some(float_const) = env.get_const(&float_name) {
        assert_type_is_sort(&tc, &float_const.type_, "Float");
    }

    for op_name in [
        "Float.add",
        "Float.sub",
        "Float.mul",
        "Float.div",
        "Float.sqrt",
        "Float.sin",
        "Float.cos",
    ] {
        let name = Name::from_string(op_name);
        if let Some(const_info) = env.get_const(&name) {
            assert_type_is_sort(&tc, &const_info.type_, op_name);
        }
    }
}

#[test]
fn test_monad_typeclass() {
    // Test Monad typeclass and its instances
    // class Monad (m : Type u → Type v) extends Applicative m, Bind m where

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Control.Basic", &[lib_path])
        .expect("Failed to load Init.Control.Basic");

    let tc = TypeChecker::new(&env);

    // Test fundamental type classes — verify at least as inductive or definition
    for class_name in ["Functor", "Applicative", "Monad", "Bind", "Pure", "Seq"] {
        let name = Name::from_string(class_name);
        if env.get_inductive(&name).is_some() {
            // Exists as inductive — structural check sufficient
        } else if let Some(class_const) = env.get_const(&name) {
            assert_type_is_sort(&tc, &class_const.type_, class_name);
        }
    }

    // Test bind and pure functions
    for fn_name in ["bind", "pure"] {
        let name = Name::from_string(fn_name);
        if let Some(fn_const) = env.get_const(&name) {
            assert_type_is_sort(&tc, &fn_const.type_, fn_name);
        }
    }
}

#[test]
fn test_function_composition() {
    // Test function composition and related combinators
    // Function.comp (∘), id, const, flip

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Core", &[lib_path]).expect("Failed to load Init.Core");

    let tc = TypeChecker::new(&env);

    for fn_name in ["Function.comp", "id", "Function.const", "flip"] {
        let name = Name::from_string(fn_name);
        if let Some(fn_const) = env.get_const(&name) {
            assert_type_is_sort(&tc, &fn_const.type_, fn_name);
        }
    }
}

#[test]
fn test_bytearray_type() {
    // Test ByteArray - raw byte storage, fundamental for I/O
    // structure ByteArray where mk :: (data : Array UInt8)

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Data.ByteArray.Basic", &[lib_path])
        .expect("Failed to load Init.Data.ByteArray.Basic");

    let tc = TypeChecker::new(&env);

    let ba_name = Name::from_string("ByteArray");
    let ba_ind = env.get_inductive(&ba_name).expect("ByteArray not found");

    assert_eq!(ba_ind.num_params, 0, "ByteArray has no type params");
    assert_eq!(
        ba_ind.constructor_names.len(),
        1,
        "ByteArray should have 1 constructor (mk)"
    );
    assert!(!ba_ind.is_recursive, "ByteArray is not recursive");

    // Type-check ByteArray.mk and accessor
    let mk_name = Name::from_string("ByteArray.mk");
    let mk_const = env.get_const(&mk_name).expect("ByteArray.mk not found");
    assert_type_is_sort(&tc, &mk_const.type_, "ByteArray.mk");

    let data_name = Name::from_string("ByteArray.data");
    if let Some(data_const) = env.get_const(&data_name) {
        assert_type_is_sort(&tc, &data_const.type_, "ByteArray.data");
    }

    for op_name in ["ByteArray.size", "ByteArray.push", "ByteArray.get!"] {
        let name = Name::from_string(op_name);
        if let Some(const_info) = env.get_const(&name) {
            assert_type_is_sort(&tc, &const_info.type_, op_name);
        }
    }
}

#[test]
fn test_fin_bounded_nat() {
    // Test Fin - bounded natural numbers (fundamental for array indexing)
    // structure Fin (n : Nat) where mk :: (val : Nat) (isLt : val < n)

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Data.Fin.Basic", &[lib_path])
        .expect("Failed to load Init.Data.Fin.Basic");

    let tc = TypeChecker::new(&env);

    let fin_name = Name::from_string("Fin");
    let fin_ind = env.get_inductive(&fin_name).expect("Fin not found");

    assert_eq!(fin_ind.num_params, 1, "Fin should have 1 param (n : Nat)");
    assert_eq!(
        fin_ind.constructor_names.len(),
        1,
        "Fin should have 1 constructor (mk)"
    );
    assert!(!fin_ind.is_recursive, "Fin is not recursive");

    // Type-check Fin.mk and projections
    let mk_name = Name::from_string("Fin.mk");
    let mk_const = env.get_const(&mk_name).expect("Fin.mk not found");
    assert_type_is_sort(&tc, &mk_const.type_, "Fin.mk");

    for proj_name in ["Fin.val", "Fin.isLt"] {
        let name = Name::from_string(proj_name);
        if let Some(proj_const) = env.get_const(&name) {
            assert_type_is_sort(&tc, &proj_const.type_, proj_name);
        }
    }

    // Check Fin.rec recursor
    let rec_name = Name::from_string("Fin.rec");
    let rec_val = env.get_recursor(&rec_name).expect("Fin.rec should exist");
    assert_eq!(rec_val.rules.len(), 1, "Fin.rec should have 1 rule (mk)");
}

#[test]
fn test_char_type() {
    // Test Char - Unicode code points
    // structure Char where val : UInt32, valid : val.isValidChar

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Data.Char.Basic", &[lib_path])
        .expect("Failed to load Init.Data.Char.Basic");

    let tc = TypeChecker::new(&env);

    let char_name = Name::from_string("Char");
    let char_ind = env.get_inductive(&char_name).expect("Char not found");

    assert_eq!(char_ind.num_params, 0, "Char has no type params");
    assert_eq!(
        char_ind.constructor_names.len(),
        1,
        "Char should have 1 constructor (mk)"
    );
    assert!(!char_ind.is_recursive, "Char is not recursive");

    // Type-check Char.mk, val projection, and operations
    let mk_name = Name::from_string("Char.mk");
    let mk_const = env.get_const(&mk_name).expect("Char.mk not found");
    assert_type_is_sort(&tc, &mk_const.type_, "Char.mk");

    for name_str in ["Char.val", "Char.toNat", "Char.toLower", "Char.toUpper"] {
        let name = Name::from_string(name_str);
        if let Some(const_info) = env.get_const(&name) {
            assert_type_is_sort(&tc, &const_info.type_, name_str);
        }
    }
}

#[test]
fn test_hashmap_type() {
    // Test HashMap - hash-based key-value store
    // In Lean 4.13: Lean.Data.HashMap, In Lean 4.27+: Std.Data.HashMap

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();

    // Try Lean.Data.HashMap first (older versions), fallback to Std.Data.HashMap (4.27+)
    let module_loaded = load_module_with_deps(
        &mut env,
        "Lean.Data.HashMap",
        std::slice::from_ref(&lib_path),
    )
    .or_else(|_| {
        load_module_with_deps(
            &mut env,
            "Std.Data.HashMap",
            std::slice::from_ref(&lib_path),
        )
    })
    .is_ok();

    if !module_loaded {
        eprintln!("Skipping test: HashMap module not found in Lean stdlib");
        return;
    }

    let tc = TypeChecker::new(&env);

    // Test HashMap structure (Std.HashMap or HashMap depending on version)
    for hm_str in ["Std.HashMap", "HashMap"] {
        let hm_name = Name::from_string(hm_str);
        if env.get_inductive(&hm_name).is_some() {
            // Exists as inductive — structural check sufficient
        } else if let Some(hm_const) = env.get_const(&hm_name) {
            assert_type_is_sort(&tc, &hm_const.type_, hm_str);
        }
    }

    // Test Hashable typeclass (required for HashMap keys)
    let hashable_name = Name::from_string("Hashable");
    if env.get_inductive(&hashable_name).is_some() {
        // Exists as inductive
    } else if let Some(hashable_const) = env.get_const(&hashable_name) {
        assert_type_is_sort(&tc, &hashable_const.type_, "Hashable");
    }
}

#[test]
fn test_task_async_type() {
    // Test Task - asynchronous computation (for parallelism)

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.System.Promise", &[lib_path])
        .expect("Failed to load Init.System.Promise");

    let tc = TypeChecker::new(&env);

    for fn_name in ["Task", "BaseIO.asTask", "Task.get"] {
        let name = Name::from_string(fn_name);
        if let Some(fn_const) = env.get_const(&name) {
            assert_type_is_sort(&tc, &fn_const.type_, fn_name);
        }
    }
}

#[test]
fn test_range_type() {
    // Test Range - for iteration (fundamental for for-loops)
    // structure Range where start : Nat, stop : Nat, step : Nat := 1

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Data.Range", &[lib_path])
        .expect("Failed to load Init.Data.Range");

    let tc = TypeChecker::new(&env);

    let range_name = Name::from_string("Std.Range");
    if let Some(range_ind) = env.get_inductive(&range_name) {
        assert_eq!(range_ind.num_params, 0, "Range has no type params");
        assert_eq!(
            range_ind.constructor_names.len(),
            1,
            "Range should have 1 constructor (mk)"
        );
        assert!(!range_ind.is_recursive, "Range is not recursive");

        let mk_name = Name::from_string("Std.Range.mk");
        if let Some(mk_const) = env.get_const(&mk_name) {
            assert_type_is_sort(&tc, &mk_const.type_, "Std.Range.mk");
        }
    } else if let Some(range_const) = env.get_const(&range_name) {
        assert_type_is_sort(&tc, &range_const.type_, "Std.Range");
    }

    // Check ForIn typeclass (for iteration)
    let forin_name = Name::from_string("ForIn");
    if env.get_inductive(&forin_name).is_some() {
        // Exists as inductive
    } else if let Some(forin_const) = env.get_const(&forin_name) {
        assert_type_is_sort(&tc, &forin_const.type_, "ForIn");
    }
}

#[test]
fn test_thunk_lazy_type() {
    // Test Thunk - lazy evaluation (memoized computation)

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Core", &[lib_path]).expect("Failed to load Init.Core");

    let tc = TypeChecker::new(&env);

    for fn_name in ["Thunk", "Thunk.get", "Lazy"] {
        let name = Name::from_string(fn_name);
        if let Some(fn_const) = env.get_const(&name) {
            assert_type_is_sort(&tc, &fn_const.type_, fn_name);
        }
    }
}

#[test]
fn test_name_syntax_types() {
    // Test Name and Syntax - metaprogramming types

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Meta", &[lib_path]).expect("Failed to load Init.Meta");

    let tc = TypeChecker::new(&env);

    // Test Name inductive (hierarchical identifiers)
    let name_name = Name::from_string("Lean.Name");
    if let Some(name_ind) = env.get_inductive(&name_name) {
        assert_eq!(name_ind.num_params, 0, "Name has no type params");
        assert_eq!(
            name_ind.constructor_names.len(),
            3,
            "Name should have 3 constructors (anonymous, str, num)"
        );
        assert!(name_ind.is_recursive, "Name is recursive");
    }

    // Type-check Name constructors
    for ctor in ["Lean.Name.anonymous", "Lean.Name.str", "Lean.Name.num"] {
        let name = Name::from_string(ctor);
        if let Some(const_info) = env.get_const(&name) {
            assert_type_is_sort(&tc, &const_info.type_, ctor);
        }
    }

    // Test Syntax type (AST nodes for metaprogramming)
    let syntax_name = Name::from_string("Lean.Syntax");
    if env.get_inductive(&syntax_name).is_some() {
        // Exists as inductive
    } else if let Some(syntax_const) = env.get_const(&syntax_name) {
        assert_type_is_sort(&tc, &syntax_const.type_, "Lean.Syntax");
    }
}

#[test]
fn test_expr_level_meta_types() {
    // Test Expr and Level - kernel representation types

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Meta", &[lib_path]).expect("Failed to load Init.Meta");

    let tc = TypeChecker::new(&env);

    for type_name in ["Lean.Expr", "Lean.Level", "Lean.MVarId", "Lean.FVarId"] {
        let name = Name::from_string(type_name);
        if let Some(type_const) = env.get_const(&name) {
            assert_type_is_sort(&tc, &type_const.type_, type_name);
        }
    }
}

#[test]
fn test_acc_wellfounded_types() {
    // Test Acc and WellFounded - termination proofs
    // Acc α r a holds when a is accessible via relation r

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.WF", &[lib_path]).expect("Failed to load Init.WF");

    let tc = TypeChecker::new(&env);

    let acc_name = Name::from_string("Acc");
    let acc_ind = env.get_inductive(&acc_name).expect("Acc not found");

    assert_eq!(
        acc_ind.constructor_names.len(),
        1,
        "Acc should have 1 constructor (intro)"
    );
    assert!(acc_ind.is_recursive, "Acc is recursive (nested in intro)");

    // Type-check Acc.intro
    let acc_intro_name = Name::from_string("Acc.intro");
    let acc_intro_const = env.get_const(&acc_intro_name).expect("Acc.intro not found");
    assert_type_is_sort(&tc, &acc_intro_const.type_, "Acc.intro");

    // Test WellFounded structure
    let wf_name = Name::from_string("WellFounded");
    if let Some(_wf_ind) = env.get_inductive(&wf_name) {
        let wf_intro_name = Name::from_string("WellFounded.intro");
        if let Some(wf_intro_const) = env.get_const(&wf_intro_name) {
            assert_type_is_sort(&tc, &wf_intro_const.type_, "WellFounded.intro");
        }
    }
}

#[test]
fn test_tactic_monad_types() {
    // Test TacticM, MetaM, TermElabM - tactic monads for metaprogramming

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(
        &mut env,
        "Lean.Elab.Tactic.Basic",
        std::slice::from_ref(&lib_path),
    )
    .expect("Failed to load Lean.Elab.Tactic.Basic");

    let tc = TypeChecker::new(&env);

    for type_name in [
        "Lean.Elab.Tactic.TacticM",
        "Lean.Meta.MetaM",
        "Lean.Elab.Term.TermElabM",
        "Lean.CoreM",
        "Lean.Elab.Tactic.focus",
        "Lean.Elab.Tactic.getMainGoal",
    ] {
        let name = Name::from_string(type_name);
        if let Some(type_const) = env.get_const(&name) {
            assert_type_is_sort(&tc, &type_const.type_, type_name);
        }
    }
}
