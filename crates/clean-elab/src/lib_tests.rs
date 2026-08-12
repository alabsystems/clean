// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::register::{kernel_check_failure_count, reset_kernel_check_counter};
use clean_kernel::sorry::with_sorry_location_key;
use clean_kernel::{Environment, ExprKind, Name};
use clean_parser::{parse_expr, DeclModifiers};

#[test]
fn test_register_aesop_rule() {
    use clean_parser::{AesopAttr, AesopBuilder, AesopPhase};

    let mut env = Environment::new();

    // Register a safe apply rule
    let attr = AesopAttr {
        phase: AesopPhase::Safe,
        builder: AesopBuilder::Apply,
        builder_args: vec![],
        priority: None,
        rule_sets: vec![],
        index_mode: clean_parser::AesopIndexMode::default(),
    };
    register_aesop_rule(&mut env, Name::from_string("my_safe_rule"), &attr);

    // Register an unsafe rule with priority
    let attr2 = AesopAttr {
        phase: AesopPhase::Unsafe,
        builder: AesopBuilder::Apply,
        builder_args: vec![],
        priority: Some(30),
        rule_sets: vec![],
        index_mode: clean_parser::AesopIndexMode::default(),
    };
    register_aesop_rule(&mut env, Name::from_string("my_unsafe_rule"), &attr2);

    // Register a norm simp rule
    let attr3 = AesopAttr {
        phase: AesopPhase::Norm,
        builder: AesopBuilder::Simp,
        builder_args: vec![],
        priority: None,
        rule_sets: vec![],
        index_mode: clean_parser::AesopIndexMode::default(),
    };
    register_aesop_rule(&mut env, Name::from_string("my_simp_rule"), &attr3);

    // Verify rules are registered
    assert_eq!(env.get_aesop_safe_rules().len(), 1);
    assert_eq!(env.get_aesop_unsafe_rules().len(), 1);
    assert_eq!(env.get_aesop_norm_rules().len(), 1);

    // Check safe rule
    let safe_rules = env.get_aesop_safe_rules();
    assert_eq!(safe_rules[0].name.to_string(), "my_safe_rule");

    // Check unsafe rule priority
    let unsafe_rules = env.get_aesop_unsafe_rules();
    assert_eq!(unsafe_rules[0].priority, 30);
}

#[test]
fn test_register_aesop_rule_to_named_set() {
    use clean_parser::{AesopAttr, AesopBuilder, AesopPhase};

    let mut env = Environment::new();

    // Register a rule to the Measurable rule set
    let attr = AesopAttr {
        phase: AesopPhase::Safe,
        builder: AesopBuilder::Apply,
        builder_args: vec![],
        priority: None,
        rule_sets: vec!["Measurable".to_string()],
        index_mode: clean_parser::AesopIndexMode::default(),
    };
    register_aesop_rule(&mut env, Name::from_string("measurable_id"), &attr);

    // Default rule set should be empty
    assert_eq!(env.get_aesop_safe_rules().len(), 0);

    // Measurable rule set should have the rule
    let measurable = env
        .get_named_rule_set(&Name::from_string("Measurable"))
        .expect("Measurable rule set should exist");
    assert_eq!(measurable.safe_rules.len(), 1);
    assert_eq!(measurable.safe_rules[0].name.to_string(), "measurable_id");
}

#[test]
fn test_register_aesop_rule_to_multiple_sets() {
    use clean_parser::{AesopAttr, AesopBuilder, AesopPhase};

    let mut env = Environment::new();

    // Register a rule to multiple rule sets
    let attr = AesopAttr {
        phase: AesopPhase::Safe,
        builder: AesopBuilder::Apply,
        builder_args: vec![],
        priority: None,
        rule_sets: vec!["Measurable".to_string(), "Continuous".to_string()],
        index_mode: clean_parser::AesopIndexMode::default(),
    };
    register_aesop_rule(
        &mut env,
        Name::from_string("measurable_continuous_fn"),
        &attr,
    );

    // Both rule sets should have the rule
    let measurable = env
        .get_named_rule_set(&Name::from_string("Measurable"))
        .expect("Measurable rule set should exist");
    assert_eq!(measurable.safe_rules.len(), 1);

    let continuous = env
        .get_named_rule_set(&Name::from_string("Continuous"))
        .expect("Continuous rule set should exist");
    assert_eq!(continuous.safe_rules.len(), 1);
}

#[test]
fn test_get_combined_rule_sets() {
    use clean_parser::{AesopAttr, AesopBuilder, AesopPhase};

    let mut env = Environment::new();

    // Add rules to different rule sets
    let attr1 = AesopAttr {
        phase: AesopPhase::Safe,
        builder: AesopBuilder::Apply,
        builder_args: vec![],
        priority: None,
        rule_sets: vec!["Measurable".to_string()],
        index_mode: clean_parser::AesopIndexMode::default(),
    };
    register_aesop_rule(&mut env, Name::from_string("measurable_rule"), &attr1);

    let attr2 = AesopAttr {
        phase: AesopPhase::Safe,
        builder: AesopBuilder::Apply,
        builder_args: vec![],
        priority: None,
        rule_sets: vec!["Continuous".to_string()],
        index_mode: clean_parser::AesopIndexMode::default(),
    };
    register_aesop_rule(&mut env, Name::from_string("continuous_rule"), &attr2);

    // Get combined rules
    let combined = env.get_combined_rule_sets(&[
        Name::from_string("Measurable"),
        Name::from_string("Continuous"),
    ]);

    assert_eq!(combined.safe_rules.len(), 2);
}

#[test]
fn test_elaborate_type() {
    let env = Environment::new();
    let surface = parse_expr("Type").unwrap();
    let result = elaborate(&env, &surface).unwrap();
    assert!(matches!(result.kind(), ExprKind::Sort(_)));
}

#[test]
fn test_elaborate_identity() {
    let env = Environment::new();
    let surface = parse_expr("fun (A : Type) (x : A) => x").unwrap();
    let result = elaborate(&env, &surface).unwrap();
    assert!(matches!(result.kind(), ExprKind::Lam(_, _, _)));
}

#[test]
fn test_elaborate_arrow() {
    let env = Environment::new();
    let surface = parse_expr("Type -> Type").unwrap();
    let result = elaborate(&env, &surface).unwrap();
    assert!(matches!(result.kind(), ExprKind::Pi(_, _, _)));
}

#[test]
fn test_elaborate_decl_and_register_aesop() {
    use clean_parser::parse_decl;

    let mut env = Environment::new();
    env.init_true_false().unwrap();

    // Parse a theorem with @[aesop safe apply] attribute
    // Theorem type must be Prop (#1276 fix: TheoremTypeNotProp)
    let decl = parse_decl("@[aesop safe apply] theorem my_intro : True := True.intro").unwrap();

    // Elaborate and register - this should wire the aesop rule
    let result = elaborate_decl_and_register(&mut env, &decl).unwrap();

    // Check elaboration result
    assert!(matches!(result, ElabResult::Theorem { .. }));

    // Verify the aesop rule was registered
    let safe_rules = env.get_aesop_safe_rules();
    assert_eq!(safe_rules.len(), 1, "Expected 1 safe rule to be registered");
    assert_eq!(safe_rules[0].name.to_string(), "my_intro");
}

#[test]
fn test_elaborate_decl_and_register_multiple_attrs() {
    use clean_parser::parse_decl;

    let mut env = Environment::new();

    // Parse and register a safe rule
    // Use `Prop` as value of type `Type` (Prop : Type is well-typed)
    let decl1 = parse_decl("@[aesop safe apply] def helper1 : Type := Prop").unwrap();
    elaborate_decl_and_register(&mut env, &decl1).unwrap();

    // Parse and register an unsafe rule with priority
    let decl2 = parse_decl("@[aesop unsafe 50 apply] def helper2 : Type := Prop").unwrap();
    elaborate_decl_and_register(&mut env, &decl2).unwrap();

    // Parse and register a norm simp rule
    let decl3 = parse_decl("@[aesop norm simp] axiom helper3 : Type").unwrap();
    elaborate_decl_and_register(&mut env, &decl3).unwrap();

    // Verify all rules were registered
    assert_eq!(env.get_aesop_safe_rules().len(), 1);
    assert_eq!(env.get_aesop_unsafe_rules().len(), 1);
    assert_eq!(env.get_aesop_norm_rules().len(), 1);

    // Verify unsafe rule has correct priority
    let unsafe_rules = env.get_aesop_unsafe_rules();
    assert_eq!(unsafe_rules[0].priority, 50);
}

#[test]
fn test_elaborate_decl_without_aesop_attr() {
    use clean_parser::parse_decl;

    let mut env = Environment::new();
    env.init_true_false().unwrap();

    // Parse a theorem without aesop attribute
    // Theorem type must be Prop (#1276 fix: TheoremTypeNotProp)
    let decl = parse_decl("theorem plain_thm : True := True.intro").unwrap();
    elaborate_decl_and_register(&mut env, &decl).unwrap();

    // Verify no aesop rules were registered
    assert_eq!(env.get_aesop_safe_rules().len(), 0);
    assert_eq!(env.get_aesop_unsafe_rules().len(), 0);
    assert_eq!(env.get_aesop_norm_rules().len(), 0);
}

#[test]
fn test_elaborate_decl_and_register_export_skipped() {
    use clean_parser::parse_decl;

    // B13: `export` of a name that does not exist is now a LOUD error (Lean
    // `elabExport` resolves each ident), so this administrative-result pin
    // uses the prelude env where `Nat.add` genuinely exists.
    let mut env = Environment::with_prelude();
    let decl = parse_decl("export Nat (add)").unwrap();
    let result = elaborate_decl_and_register(&mut env, &decl).unwrap();

    assert!(matches!(result, ElabResult::Skipped));
}

#[test]
fn test_elaborate_decl_and_register_deriving_instance_skipped() {
    use clean_parser::parse_decl;

    let mut env = Environment::new();
    let decl = parse_decl("deriving instance Repr for Nat").unwrap();
    let result = elaborate_decl_and_register(&mut env, &decl).unwrap();

    assert!(matches!(result, ElabResult::Skipped));
}

#[test]
fn test_elaborate_decl_and_register_open_skipped() {
    use clean_parser::parse_decl;

    let mut env = Environment::new();
    let decl = parse_decl("open Nat").unwrap();
    let result = elaborate_decl_and_register(&mut env, &decl).unwrap();

    assert!(matches!(result, ElabResult::Skipped));
}

#[test]
fn test_elaborate_decl_export_skipped() {
    use clean_parser::parse_decl;

    // B13: unknown export names are loud errors now; pin the Skipped result
    // shape against the prelude env where `Nat.add` exists.
    let env = Environment::with_prelude();
    let decl = parse_decl("export Nat (add)").unwrap();
    let result = elaborate_decl(&env, &decl).unwrap();

    assert!(matches!(result, ElabResult::Skipped));
}

#[test]
fn test_elaborate_decl_deriving_instance_skipped() {
    use clean_parser::parse_decl;

    let env = Environment::new();
    let decl = parse_decl("deriving instance Repr for Nat").unwrap();
    let result = elaborate_decl(&env, &decl).unwrap();

    assert!(matches!(result, ElabResult::Skipped));
}

#[test]
fn test_process_imports_euclidean_geometry() {
    let mut env = Environment::new();

    // Process Euclidean geometry imports
    let paths = vec![vec!["Mathlib", "Geometry", "Euclidean", "Basic"]
        .into_iter()
        .map(String::from)
        .collect()];
    process_imports(&mut env, &paths).unwrap();

    // Verify EuclideanSpace and related types are now available
    assert!(
        env.get_const(&Name::from_string("EuclideanSpace"))
            .is_some(),
        "EuclideanSpace should be defined after import"
    );
    assert!(
        env.get_const(&Name::from_string("InnerProductSpace"))
            .is_some(),
        "InnerProductSpace should be defined after import"
    );
    assert!(
        env.get_const(&Name::from_string("EuclideanGeometry.Sphere"))
            .is_some(),
        "EuclideanGeometry.Sphere should be defined after import"
    );
}

#[test]
fn test_process_imports_real_basic() {
    let mut env = Environment::new();

    // Process Real import
    let paths = vec![vec!["Mathlib", "Data", "Real", "Basic"]
        .into_iter()
        .map(String::from)
        .collect()];
    process_imports(&mut env, &paths).unwrap();

    // Verify Real is now available
    assert!(
        env.get_const(&Name::from_string("Real")).is_some(),
        "Real should be defined after import"
    );

    // Verify OfNat typeclass and instances are initialized (#110)
    assert!(
        env.get_const(&Name::from_string("OfNat")).is_some(),
        "OfNat typeclass should be defined after Real import"
    );
    assert!(
        env.get_const(&Name::from_string("OfNat.ofNat")).is_some(),
        "OfNat.ofNat projection should be defined"
    );
    assert!(
        env.get_const(&Name::from_string("instOfNatNat")).is_some(),
        "instOfNatNat should be defined after Real import"
    );
    assert!(
        env.get_const(&Name::from_string("instOfNatReal")).is_some(),
        "instOfNatReal should be defined after Real import"
    );
}

#[test]
fn test_process_imports_mathlib_zmod_basic_surface_type() {
    prelude_providers::reset_mathlib_init();
    let mut env = Environment::new();
    let paths = vec![vec!["Mathlib", "Data", "ZMod", "Basic"]
        .into_iter()
        .map(String::from)
        .collect()];

    process_imports(&mut env, &paths).unwrap();

    let zmod = env
        .get_const(&Name::from_string("ZMod"))
        .expect("Mathlib.Data.ZMod.Basic should provide the ZMod type constructor");
    assert!(
        matches!(zmod.kind, clean_kernel::ConstantKind::Axiom),
        "surface ZMod stub should be marked as an axiom, got {:?}",
        zmod.kind
    );
    assert!(
        env.get_const(&Name::from_string("ZMod.val")).is_none(),
        "surface ZMod stub must not pretend to provide ZMod operations"
    );
}

#[test]
fn test_process_imports_unknown_ignored() {
    let mut env = Environment::new();

    // Unknown imports should be silently ignored
    let paths = vec![vec!["Some", "Unknown", "Module"]
        .into_iter()
        .map(String::from)
        .collect()];
    let result = process_imports(&mut env, &paths);
    assert!(result.is_ok(), "Unknown imports should not cause errors");
}

#[test]
fn test_process_imports_lean_elab_tactic_succeeds_via_shim() {
    // Plan decision 1 (Clean-native meta shim): the old metaprogramming wall that
    // hard-rejected `import Lean.Elab.Tactic` has been removed. The import must now
    // SUCCEED via the Clean-native opaque meta shim — never fail closed.
    //
    // Exercise the shim path DIRECTLY (`process_imports_clean_native`), not the
    // toolchain-sensitive `process_imports`. The latter prefers real `.olean`
    // artifacts whenever a toolchain is discoverable on the machine, and
    // `Lean.Elab.Tactic` transitively pulls in its ENTIRE ~16k-module closure
    // (`FRONTEND_OLEAN_IMPORT_MODULE_LIMIT = 16_384`). Loading that is
    // pathologically slow, so the test's outcome flaked on the environment: fast
    // in CI (no toolchain → shim), effectively hanging for minutes on dev machines
    // with an installed toolchain (the real-olean path — which, being an olean
    // *success*, never even reached the shim this test is named for). The shim
    // provides the same opaque meta types the assertions below require, in O(1).
    let mut env = Environment::new();
    let paths = vec![vec!["Lean", "Elab", "Tactic"]
        .into_iter()
        .map(String::from)
        .collect()];
    imports::process_imports_clean_native(&mut env, &paths)
        .expect("Lean.Elab.Tactic must import via the Clean-native meta shim");

    // Whichever path served the import, the core Lean meta types must resolve so
    // meta-referencing declarations elaborate.
    assert!(
        env.get_const(&clean_kernel::Name::from_string("Lean.Syntax"))
            .is_some(),
        "meta shim (or real olean) must make `Lean.Syntax` resolvable",
    );
    assert!(
        env.get_const(&clean_kernel::Name::from_string("Lean.Elab.Tactic.TacticM"))
            .is_some(),
        "meta shim (or real olean) must make `Lean.Elab.Tactic.TacticM` resolvable",
    );
}

#[test]
fn test_elaborate_with_import_routing() {
    use clean_parser::parse_file;

    let mut env = Environment::new();

    // Parse a file with imports (like MATP-BENCH Q1)
    let code = r#"
import Mathlib.Geometry.Euclidean.Basic
abbrev PPoint := EuclideanSpace
"#;
    let decls = parse_file(code).unwrap();

    // Process all declarations
    for decl in &decls {
        elaborate_decl_and_register(&mut env, decl).unwrap();
    }

    // After processing imports, EuclideanSpace should be available
    assert!(
        env.get_const(&Name::from_string("EuclideanSpace"))
            .is_some(),
        "EuclideanSpace should be available after import"
    );
}

#[test]
fn test_abbrev_reduces_in_type_elaboration() {
    use clean_parser::parse_file;

    let mut env = Environment::with_prelude();
    let code = r#"
abbrev MyType := Nat
def myVal : MyType := 0
"#;
    let decls = parse_file(code).unwrap();
    for (i, decl) in decls.iter().enumerate() {
        let result = elaborate_decl_and_register(&mut env, decl);
        assert!(
            result.is_ok(),
            "simple abbrev decl {} should elaborate: {:?}",
            i,
            result
        );
    }
    assert!(
        env.get_const(&Name::from_string("myVal")).is_some(),
        "myVal should be registered"
    );

    let mut env = Environment::with_prelude();
    let code = r#"
abbrev MyAlias (a : Type) := a
def myId : MyAlias Nat := (0 : Nat)
"#;
    let decls = parse_file(code).unwrap();
    for (i, decl) in decls.iter().enumerate() {
        let result = elaborate_decl_and_register(&mut env, decl);
        assert!(
            result.is_ok(),
            "parameterized abbrev decl {} should elaborate: {:?}",
            i,
            result
        );
    }
    assert!(
        env.get_const(&Name::from_string("myId")).is_some(),
        "myId should be registered"
    );
}

// ========================================================================
// FileContext and variable scope tests
// ========================================================================

#[test]
fn test_file_context_basic() {
    use clean_parser::{Span, SurfaceBinder, SurfaceBinderInfo, SurfaceExpr};

    let mut ctx = FileContext::new();
    assert!(!ctx.has_variables());
    assert!(ctx.current_variables().is_empty());

    // Add a variable
    let binder = SurfaceBinder {
        span: Span::dummy(),
        name: "P".to_string(),
        ty: Some(Box::new(SurfaceExpr::type_())),
        default: None,
        info: SurfaceBinderInfo::Implicit,
    };
    ctx.add_variables(&[binder]);

    assert!(ctx.has_variables());
    assert_eq!(ctx.current_variables().len(), 1);
    assert_eq!(ctx.current_variables()[0].name, "P");
}

#[test]
fn test_file_context_section_scope() {
    use clean_parser::{Span, SurfaceBinder, SurfaceBinderInfo, SurfaceExpr};

    let mut ctx = FileContext::new();

    // Add variable outside section
    let binder1 = SurfaceBinder {
        span: Span::dummy(),
        name: "A".to_string(),
        ty: Some(Box::new(SurfaceExpr::type_())),
        default: None,
        info: SurfaceBinderInfo::Implicit,
    };
    ctx.add_variables(&[binder1]);

    // Enter section
    ctx.enter_section();

    // Add variable inside section
    let binder2 = SurfaceBinder {
        span: Span::dummy(),
        name: "B".to_string(),
        ty: Some(Box::new(SurfaceExpr::type_())),
        default: None,
        info: SurfaceBinderInfo::Implicit,
    };
    ctx.add_variables(&[binder2]);

    assert_eq!(ctx.current_variables().len(), 2);

    // Exit section - B should be gone
    ctx.exit_section();

    assert_eq!(ctx.current_variables().len(), 1);
    assert_eq!(ctx.current_variables()[0].name, "A");
}

#[test]
fn test_preprocess_decl_with_variable() {
    use clean_parser::{parse_file, SurfaceDecl};

    let code = r#"
variable {P : Type}
theorem uses_P (x : P) : P := x
"#;
    let decls = parse_file(code).unwrap();
    let mut file_ctx = FileContext::new();

    // First decl is variable
    let processed1 = preprocess_decl_with_context(&decls[0], &mut file_ctx);
    assert!(matches!(processed1, SurfaceDecl::Variable { .. }));

    // Second decl is theorem - should have P prepended
    let processed2 = preprocess_decl_with_context(&decls[1], &mut file_ctx);
    match processed2 {
        SurfaceDecl::Theorem { binders, .. } => {
            // Should have 2 binders: P (from variable) and x (from theorem)
            assert_eq!(binders.len(), 2, "Expected 2 binders after preprocessing");
            assert_eq!(
                binders[0].name, "P",
                "First binder should be P from variable"
            );
            assert_eq!(
                binders[1].name, "x",
                "Second binder should be x from theorem"
            );
        }
        _ => panic!("Expected Theorem"),
    }
}

#[test]
fn test_preprocess_decl_multiple_variables() {
    use clean_parser::{parse_file, SurfaceDecl};

    let code = r#"
variable {P : Type}
variable [Add P]
def add_P (x y : P) : P := sorry
"#;
    let decls = parse_file(code).unwrap();
    let mut file_ctx = FileContext::new();

    // Process first two variable declarations
    let _ = preprocess_decl_with_context(&decls[0], &mut file_ctx);
    let _ = preprocess_decl_with_context(&decls[1], &mut file_ctx);

    assert_eq!(
        file_ctx.current_variables().len(),
        2,
        "Should have 2 accumulated variables"
    );

    // Process def - should have both variables prepended
    let processed = preprocess_decl_with_context(&decls[2], &mut file_ctx);
    match processed {
        SurfaceDecl::Def { binders, .. } => {
            // Should have 4 binders: P, Add P, x, y
            assert!(
                binders.len() >= 4,
                "Expected at least 4 binders: {binders:?}"
            );
            assert_eq!(binders[0].name, "P");
        }
        _ => panic!("Expected Def"),
    }
}

#[test]
fn test_variable_scope_propagation_elaboration() {
    use clean_parser::parse_file;

    let code = r#"
variable {P : Type}
def uses_P (x : P) : P := x
"#;
    let decls = parse_file(code).unwrap();
    let mut env = Environment::new();
    let mut file_ctx = FileContext::new();

    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed);
        assert!(result.is_ok(), "Elaboration should succeed: {:?}", result);
    }

    // Verify the definition was added to the environment
    assert!(
        env.get_const(&Name::from_string("uses_P")).is_some(),
        "uses_P should be in environment"
    );
}

#[test]
fn test_q6_typeclass_universe_unification_elaboration() {
    use clean_parser::parse_file;

    let code = r#"
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Data.Real.Basic
open EuclideanGeometry Real
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
def q6_typeclass_ok (A : P) : P := A
"#;
    let decls = parse_file(code).unwrap();
    let mut env = Environment::new();
    let mut file_ctx = FileContext::new();

    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed);
        assert!(
            result.is_ok(),
            "Elaboration should succeed (Fixes #121): {:?}",
            result
        );
    }

    assert!(
        env.get_const(&Name::from_string("q6_typeclass_ok"))
            .is_some(),
        "q6_typeclass_ok should be in environment"
    );
}

/// Test that later declarations can reference earlier declarations in the same file.
///
/// This is a discriminating test for #163 - the declaration ordering bug.
/// It must FAIL before the fix and PASS after the fix.
///
/// The issue: When elaborating a file with multiple declarations, each declaration
/// is elaborated with a fresh ElabCtx that takes an immutable reference to the
/// environment. The declaration is only registered to the environment AFTER
/// elaboration completes. This means later declarations can't see earlier ones.
///
/// Expected behavior: `bar` should be able to reference `foo` since `foo` is
/// defined earlier in the same file.
#[test]
fn test_issue163_declaration_ordering() {
    use clean_parser::parse_file;

    // Code where bar references foo (defined earlier)
    let code = r#"
def foo : Nat := 42
def bar : Nat := foo
"#;
    let decls = parse_file(code).unwrap();
    assert_eq!(decls.len(), 2, "Should parse 2 declarations");

    let mut env = Environment::with_prelude(); // Need prelude for Nat
    let mut file_ctx = FileContext::new();

    // Try to elaborate both declarations
    for (i, decl) in decls.iter().enumerate() {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed);
        assert!(
            result.is_ok(),
            "Elaboration of decl {} should succeed (Fixes #163): {:?}",
            i,
            result
        );
    }

    // Verify both declarations were registered
    let foo_const = env.get_const(&Name::from_string("foo"));
    let bar_const = env.get_const(&Name::from_string("bar"));
    assert!(
        foo_const.is_some(),
        "foo should be registered in environment"
    );
    assert!(
        bar_const.is_some(),
        "bar should be registered in environment"
    );
}

/// Test #163 with type-checking (like the CLI does)
/// This is the actual bug path - elaboration succeeds but type-checking fails.
#[test]
fn test_issue163_with_type_checking() {
    use clean_kernel::TypeChecker;
    use clean_parser::parse_file;

    // Code where bar references foo (defined earlier)
    let code = r#"
def foo : Nat := 42
def bar : Nat := foo
"#;
    let decls = parse_file(code).unwrap();
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();

    for (i, decl) in decls.iter().enumerate() {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed);
        assert!(
            result.is_ok(),
            "Elaboration of decl {} should succeed (Fixes #163): {:?}",
            i,
            result
        );

        // Now type-check like the CLI does
        if let Ok(ElabResult::Definition { name, ty, val, .. }) = &result {
            let tc = TypeChecker::new(&env);
            let tc_result = tc.infer_type(ty).and_then(|_| tc.infer_type(val));
            assert!(
                tc_result.is_ok(),
                "Type checking of {} should succeed (Fixes #163): {:?}\n  ty: {:?}\n  val: {:?}",
                name,
                tc_result,
                ty,
                val
            );
        }
    }
}

/// Additional test for #163: mutual recursion (forward reference)
/// This tests a more complex case where declarations can reference each other.
#[test]
fn test_issue163_sequential_dependencies() {
    use clean_parser::parse_file;

    // A chain of dependencies: c depends on b, b depends on a
    let code = r#"
def a : Nat := 1
def b : Nat := a + 1
def c : Nat := b + 1
"#;
    let decls = parse_file(code).unwrap();
    assert_eq!(decls.len(), 3, "Should parse 3 declarations");

    let mut env = Environment::with_prelude(); // Need prelude for `+`
    let mut file_ctx = FileContext::new();

    for (i, decl) in decls.iter().enumerate() {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed);
        assert!(
            result.is_ok(),
            "Elaboration of decl {} should succeed (Fixes #163): {:?}",
            i,
            result
        );
    }

    // Verify all declarations were registered
    assert!(
        env.get_const(&Name::from_string("a")).is_some(),
        "a should be registered"
    );
    assert!(
        env.get_const(&Name::from_string("b")).is_some(),
        "b should be registered"
    );
    assert!(
        env.get_const(&Name::from_string("c")).is_some(),
        "c should be registered"
    );
}

/// Discriminating test for #168: Universe level unification
///
/// The issue: When two universe-polymorphic constants share the same declared universe
/// (like `Type u`), clean creates independent fresh level params (u_0, u_1) that don't
/// resolve to the same canonical level, causing kernel type checking to fail.
///
/// Reproduction case from #168:
/// ```lean
/// universe u
/// axiom MyType : Type u
/// axiom myFn : {T : Type u} → T → T
/// def test (x : MyType) : MyType := myFn x
/// ```
///
/// Expected: myFn's `T` unifies with MyType's universe, both resolve to same level.
/// Bug: Kernel sees `Sort(Succ(Param("u_2")))` vs `Sort(Succ(Param("u_0")))` and fails.
#[test]
fn test_issue168_universe_level_unification() {
    use clean_kernel::TypeChecker;
    use clean_parser::parse_file;

    // Simplified reproduction: P at Type 0, angle takes {Q : Type u}
    // When we apply angle to P-typed arguments, the fresh u should unify to 0.
    let code = r#"
axiom P : Type
axiom angle : {Q : Type} → Q → Q → Q → P
def test_angle (A B C : P) : P := angle A B C
"#;
    let decls = parse_file(code).unwrap();
    assert!(decls.len() >= 3, "Should parse axioms and def");

    let mut env = Environment::new();
    let mut file_ctx = FileContext::new();

    for (i, decl) in decls.iter().enumerate() {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed);
        assert!(
            result.is_ok(),
            "Elaboration of decl {} should succeed (Fixes #168): {:?}",
            i,
            result
        );

        // Type-check like the CLI does - this is where #168 fails
        if let Ok(ref elab_result) = result {
            let (name, ty, val) = match elab_result {
                ElabResult::Definition { name, ty, val, .. } => (name, ty, val),
                ElabResult::Theorem {
                    name, ty, proof, ..
                } => (name, ty, proof),
                _ => continue, // Skip axioms, etc.
            };
            let tc = TypeChecker::new(&env);
            let tc_result = tc.infer_type(ty).and_then(|_| tc.infer_type(val));
            assert!(
                tc_result.is_ok(),
                "Type checking of {} should succeed (Fixes #168): {:?}\n  ty: {:?}\n  val: {:?}",
                name,
                tc_result,
                ty,
                val
            );
        }
    }

    // Verify the definition was registered
    assert!(
        env.get_const(&Name::from_string("test_angle")).is_some(),
        "test_angle should be registered in environment"
    );
}

/// Test #168 variant: param-to-param unification without concrete level
///
/// This tests the case where both universe params remain polymorphic but must
/// resolve to the same canonical param.
#[test]
fn test_issue168_param_to_param_canonical() {
    use clean_kernel::TypeChecker;
    use clean_parser::parse_file;

    // Universe-polymorphic: MyType at Type u, myFn takes {T : Type u}
    // u_0 (from myFn) and u_1 (from MyType) must unify to same canonical param
    let code = r#"
universe u
axiom MyType : Type u
axiom myFn : {T : Type u} → T → T
def test (x : MyType) : MyType := myFn x
"#;
    let decls = parse_file(code).unwrap();
    let mut env = Environment::new();
    let mut file_ctx = FileContext::new();

    for (i, decl) in decls.iter().enumerate() {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed);
        assert!(
            result.is_ok(),
            "Elaboration of decl {} should succeed (Fixes #168 param-to-param): {:?}",
            i,
            result
        );

        // Type-check - this is where param-to-param #168 fails
        if let Ok(ElabResult::Definition { name, ty, val, .. }) = &result {
            let tc = TypeChecker::new(&env);
            let tc_result = tc.infer_type(ty).and_then(|_| tc.infer_type(val));
            assert!(
                tc_result.is_ok(),
                "Type checking of {} should succeed (Fixes #168 param-to-param): {:?}\n  ty: {:?}\n  val: {:?}",
                name,
                tc_result,
                ty,
                val
            );
        }
    }

    assert!(
        env.get_const(&Name::from_string("test")).is_some(),
        "test should be registered in environment"
    );
}

// =========================================================================
// Kernel check tests (#2207): kernel type checking is unconditional and
// fail-closed — ill-typed declarations are always rejected and never
// structurally registered.
// =========================================================================

/// Verify that the kernel check rejects ill-typed declarations (#2207).
#[test]
#[serial_test::serial]
fn test_kernel_check_rejects_ill_typed() {
    use clean_kernel::{Expr, Name};

    reset_kernel_check_counter();

    let mut env = Environment::with_prelude();

    // Nat.zero : Nat, but we claim type is Nat (a type, not a prop) —
    // the kernel will reject this theorem.
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_zero_proof = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    let result = ElabResult::Theorem {
        name: Name::from_string("test_enforce_ill_typed"),
        universe_params: vec![],
        ty: nat_ty,
        proof: nat_zero_proof,
        modifiers: DeclModifiers::default(),
    };

    let before = kernel_check_failure_count();
    let reg = register_elab_result(&mut env, &result);
    let after = kernel_check_failure_count();

    match reg {
        Err(ElabError::KernelCheckFailed { name, detail }) => {
            assert_eq!(name.to_string(), "test_enforce_ill_typed");
            assert!(
                detail.contains("type must be Prop"),
                "expected theorem sort rejection detail, got: {detail}"
            );
        }
        other => panic!(
            "kernel check should return KernelCheckFailed for ill-typed theorem, got: {other:?}"
        ),
    }
    assert_eq!(
        after,
        before + 1,
        "failure counter should increment on kernel rejection"
    );
    assert!(
        env.get_const(&Name::from_string("test_enforce_ill_typed"))
            .is_none(),
        "ill-typed declaration should NOT be in environment (fail-closed)"
    );
}

/// Verify the unconditional kernel check still rejects ill-typed declarations
/// (fail-closed) — there is no off-switch.
#[test]
#[serial_test::serial]
fn test_kernel_check_always_enforces_type_check() {
    use clean_kernel::{Expr, Name};

    reset_kernel_check_counter();

    let mut env = Environment::with_prelude();

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_zero_proof = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    let result = ElabResult::Theorem {
        name: Name::from_string("test_disabled_strict_still_enforced"),
        universe_params: vec![],
        ty: nat_ty,
        proof: nat_zero_proof,
        modifiers: DeclModifiers::default(),
    };

    let before = kernel_check_failure_count();
    let reg = register_elab_result(&mut env, &result);
    let after = kernel_check_failure_count();

    match reg {
        Err(ElabError::KernelCheckFailed { name, detail }) => {
            assert_eq!(name.to_string(), "test_disabled_strict_still_enforced");
            assert!(
                detail.contains("type must be Prop"),
                "expected theorem sort rejection detail, got: {detail}"
            );
        }
        other => panic!(
            "kernel check must always reject ill-typed theorems (fail-closed), got: {other:?}"
        ),
    }
    assert_eq!(
        after,
        before + 1,
        "failure counter should increment before kernel rejection"
    );
    assert!(
        env.get_const(&Name::from_string("test_disabled_strict_still_enforced"))
            .is_none(),
        "ill-typed declaration must never become launch evidence (fail-closed)"
    );
}

/// Verify that the kernel check maps definition type-check failures to KernelCheckFailed.
#[test]
#[serial_test::serial]
fn test_kernel_check_definition_type_mismatch_returns_kernel_check_failed() {
    use clean_kernel::{Expr, Name};

    reset_kernel_check_counter();

    let mut env = Environment::with_prelude();

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let true_intro = Expr::const_(Name::from_string("True.intro"), vec![]);

    let result = ElabResult::Definition {
        name: Name::from_string("test_enforce_bad_definition"),
        universe_params: vec![],
        ty: nat_ty,
        val: true_intro,
        modifiers: DeclModifiers::default(),
    };

    let before = kernel_check_failure_count();
    let reg = register_elab_result(&mut env, &result);
    let after = kernel_check_failure_count();

    match reg {
        Err(ElabError::KernelCheckFailed { name, detail }) => {
            assert_eq!(name.to_string(), "test_enforce_bad_definition");
            assert!(
                !detail.is_empty(),
                "type-check failures should preserve kernel detail"
            );
        }
        other => panic!(
            "kernel check should return KernelCheckFailed for bad definitions, got: {other:?}"
        ),
    }
    assert_eq!(
        after,
        before + 1,
        "failure counter should increment for definition type-check failures"
    );
    assert!(
        env.get_const(&Name::from_string("test_enforce_bad_definition"))
            .is_none(),
        "ill-typed definition should NOT be in environment (fail-closed)"
    );
}

/// Verify that the kernel check still accepts valid declarations (#2207).
#[test]
#[serial_test::serial]
fn test_kernel_check_accepts_valid() {
    use clean_kernel::{Expr, Name};

    reset_kernel_check_counter();

    let mut env = Environment::with_prelude();

    let true_ty = Expr::const_(Name::from_string("True"), vec![]);
    let true_proof = Expr::const_(Name::from_string("True.intro"), vec![]);

    let result = ElabResult::Theorem {
        name: Name::from_string("test_enforce_valid"),
        universe_params: vec![],
        ty: true_ty,
        proof: true_proof,
        modifiers: DeclModifiers::default(),
    };

    let before = kernel_check_failure_count();
    let reg = register_elab_result(&mut env, &result);
    let after = kernel_check_failure_count();

    assert!(
        reg.is_ok(),
        "kernel check should accept valid theorem: {reg:?}"
    );
    assert_eq!(
        before, after,
        "failure counter should not increment for valid theorem"
    );
}

/// Verify the kernel check records and rejects ill-typed declarations without
/// structural insertion (fail-closed).
#[test]
#[serial_test::serial]
fn test_kernel_check_rejects_ill_typed_without_structural_insert() {
    use clean_kernel::{Expr, Name};

    reset_kernel_check_counter();

    let mut env = Environment::with_prelude();

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_zero_proof = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    let result = ElabResult::Theorem {
        name: Name::from_string("test_observe_ill_typed"),
        universe_params: vec![],
        ty: nat_ty,
        proof: nat_zero_proof,
        modifiers: DeclModifiers::default(),
    };

    let before = kernel_check_failure_count();
    let reg = register_elab_result(&mut env, &result);
    let after = kernel_check_failure_count();

    match reg {
        Err(ElabError::KernelCheckFailed { name, detail }) => {
            assert_eq!(name.to_string(), "test_observe_ill_typed");
            assert!(
                detail.contains("type must be Prop"),
                "expected theorem sort rejection detail, got: {detail}"
            );
        }
        other => panic!(
            "kernel check should record and reject ill-typed theorem without structural insertion, got: {other:?}"
        ),
    }
    assert_eq!(
        after,
        before + 1,
        "failure counter should increment on kernel rejection"
    );
    assert!(
        env.get_const(&Name::from_string("test_observe_ill_typed"))
            .is_none(),
        "declaration should not be registered after kernel rejection (fail-closed)"
    );
}

/// Verify the kernel check records and rejects definition type-check failures.
#[test]
#[serial_test::serial]
fn test_kernel_check_definition_type_mismatch_rejects_without_structural_insert() {
    use clean_kernel::{Expr, Name};

    reset_kernel_check_counter();

    let mut env = Environment::with_prelude();

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let true_intro = Expr::const_(Name::from_string("True.intro"), vec![]);

    let result = ElabResult::Definition {
        name: Name::from_string("test_observe_bad_definition"),
        universe_params: vec![],
        ty: nat_ty,
        val: true_intro,
        modifiers: DeclModifiers::default(),
    };

    let before = kernel_check_failure_count();
    let reg = register_elab_result(&mut env, &result);
    let after = kernel_check_failure_count();

    match reg {
        Err(ElabError::KernelCheckFailed { name, detail }) => {
            assert_eq!(name.to_string(), "test_observe_bad_definition");
            assert!(
                !detail.is_empty(),
                "type-check failures should preserve kernel detail"
            );
        }
        other => panic!(
            "kernel check should reject bad definitions without structural insertion, got: {other:?}"
        ),
    }
    assert_eq!(
        after,
        before + 1,
        "kernel check should record the type-check failure"
    );
    assert!(
        env.get_const(&Name::from_string("test_observe_bad_definition"))
            .is_none(),
        "bad definition should not be structurally registered (fail-closed)"
    );
}

/// Verify the kernel check records and rejects axiom type-check failures.
#[test]
#[serial_test::serial]
fn test_kernel_check_axiom_invalid_type_records_and_rejects() {
    use clean_kernel::{Expr, Name};

    reset_kernel_check_counter();

    let mut env = Environment::with_prelude();
    let result = ElabResult::Axiom {
        name: Name::from_string("test_observe_bad_axiom"),
        universe_params: vec![],
        ty: Expr::const_(Name::from_string("True.intro"), vec![]),
        modifiers: DeclModifiers::default(),
    };

    let before = kernel_check_failure_count();
    let reg = register_elab_result(&mut env, &result);
    let after = kernel_check_failure_count();

    match reg {
        Err(ElabError::KernelCheckFailed { name, detail }) => {
            assert_eq!(name.to_string(), "test_observe_bad_axiom");
            assert!(
                detail.contains("Expected sort") || detail.contains("type must be Prop"),
                "invalid axiom types should fail with a sort/type rejection, got: {detail}"
            );
        }
        other => panic!("kernel check should reject invalid axiom types, got: {other:?}"),
    }
    assert_eq!(
        after,
        before + 1,
        "kernel check should count invalid axiom type-check failures"
    );
    assert!(
        env.get_const(&Name::from_string("test_observe_bad_axiom"))
            .is_none(),
        "invalid axiom should not be registered (fail-closed)"
    );
}

/// Verify the kernel check records and rejects body-less opaque axiom-lane failures.
#[test]
#[serial_test::serial]
fn test_kernel_check_opaque_without_value_invalid_type_records_and_rejects() {
    use clean_kernel::{Expr, Name};

    reset_kernel_check_counter();

    let mut env = Environment::with_prelude();
    let result = ElabResult::Opaque {
        name: Name::from_string("test_observe_bad_opaque_no_value"),
        universe_params: vec![],
        ty: Expr::const_(Name::from_string("True.intro"), vec![]),
        val: None,
        modifiers: DeclModifiers::default(),
    };

    let before = kernel_check_failure_count();
    let reg = register_elab_result(&mut env, &result);
    let after = kernel_check_failure_count();

    match reg {
        Err(ElabError::KernelCheckFailed { name, detail }) => {
            assert_eq!(name.to_string(), "test_observe_bad_opaque_no_value");
            assert!(
                detail.contains("Expected sort") || detail.contains("type must be Prop"),
                "invalid body-less opaque types should fail with a sort/type rejection, got: {detail}"
            );
        }
        other => {
            panic!("kernel check should reject invalid body-less opaque types, got: {other:?}")
        }
    }
    assert_eq!(
        after,
        before + 1,
        "kernel check should count body-less opaque axiom-lane type-check failures"
    );
    assert!(
        env.get_const(&Name::from_string("test_observe_bad_opaque_no_value"))
            .is_none(),
        "invalid body-less opaque should not be registered (fail-closed)"
    );
}

#[test]
fn test_register_axiom_duplicate_name_returns_kernel_registration_failed() {
    use clean_kernel::{Expr, Name};

    let mut env = Environment::with_prelude();
    let result = ElabResult::Axiom {
        name: Name::from_string("duplicate_axiom"),
        universe_params: vec![],
        ty: Expr::const_(Name::from_string("True"), vec![]),
        modifiers: DeclModifiers::default(),
    };

    register_elab_result(&mut env, &result).expect("first axiom registration should succeed");
    let reg = register_elab_result(&mut env, &result);

    match reg {
        Err(ElabError::KernelRegistrationFailed { operation, detail }) => {
            assert_eq!(operation, "add_decl Axiom");
            assert!(
                detail.contains("Duplicate declaration"),
                "expected duplicate registration detail, got: {detail}"
            );
            assert!(
                detail.contains("duplicate_axiom"),
                "duplicate detail should name the axiom, got: {detail}"
            );
        }
        other => panic!(
            "duplicate axiom registration should return KernelRegistrationFailed, got: {other:?}"
        ),
    }
}

#[test]
#[serial_test::serial]
fn test_register_axiom_invalid_type_returns_kernel_check_failed() {
    use clean_kernel::{Expr, Name};

    let mut env = Environment::with_prelude();
    let result = ElabResult::Axiom {
        name: Name::from_string("invalid_axiom"),
        universe_params: vec![],
        ty: Expr::const_(Name::from_string("True.intro"), vec![]),
        modifiers: DeclModifiers::default(),
    };

    let reg = register_elab_result(&mut env, &result);

    match reg {
        Err(ElabError::KernelCheckFailed { name, detail }) => {
            assert_eq!(name.to_string(), "invalid_axiom");
            assert!(
                detail.contains("Expected sort") || detail.contains("type must be Prop"),
                "invalid axiom types should fail with a sort/type rejection, got: {detail}"
            );
        }
        other => panic!("invalid axiom type should return KernelCheckFailed, got: {other:?}"),
    }
}

// #2552: registering opaque with body emits Declaration::Opaque (ConstantKind::Opaque)
#[test]
fn test_register_opaque_with_value_uses_opaque_kind() {
    use clean_kernel::{Expr, Name};

    let mut env = Environment::with_prelude();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let result = ElabResult::Opaque {
        name: Name::from_string("my_opaque_with_val"),
        universe_params: vec![],
        ty: nat,
        val: Some(nat_zero),
        modifiers: DeclModifiers::default(),
    };

    register_elab_result(&mut env, &result).expect("well-typed opaque should register");

    let info = env
        .get_const(&Name::from_string("my_opaque_with_val"))
        .expect("opaque should be in environment");
    assert!(
        matches!(info.kind, clean_kernel::ConstantKind::Opaque),
        "body-bearing opaque should register as ConstantKind::Opaque, got: {:?}",
        info.kind
    );
}

// #2552: registering opaque without body falls back to axiom lane
#[test]
fn test_register_opaque_without_value_uses_axiom_kind() {
    use clean_kernel::{Expr, Name};

    let mut env = Environment::with_prelude();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let result = ElabResult::Opaque {
        name: Name::from_string("my_opaque_no_val"),
        universe_params: vec![],
        ty: nat,
        val: None,
        modifiers: DeclModifiers::default(),
    };

    register_elab_result(&mut env, &result).expect("body-less opaque should register");

    let info = env
        .get_const(&Name::from_string("my_opaque_no_val"))
        .expect("body-less opaque should be in environment");
    assert!(
        matches!(info.kind, clean_kernel::ConstantKind::Axiom),
        "body-less opaque should register as ConstantKind::Axiom, got: {:?}",
        info.kind
    );
}

// #2552: elaborating `opaque x : T := v` preserves the body in ElabResult::Opaque
#[test]
fn test_elaborate_opaque_with_value_preserves_body() {
    let mut env = Environment::with_prelude();
    let decl =
        clean_parser::parse_decl("opaque secretImpl : Nat := Nat.zero").expect("should parse");
    let result = elaborate_decl(&env, &decl).expect("should elaborate");

    match &result {
        ElabResult::Opaque { val: Some(_), .. } => {}
        other => panic!(
            "opaque with body should elaborate to ElabResult::Opaque with Some(val), got: {other:?}"
        ),
    }

    // Registration should succeed
    register_elab_result(&mut env, &result).expect("should register");
}

// #2552: elaborating `opaque x : T` (no body) preserves as ElabResult::Opaque with val=None
#[test]
fn test_elaborate_opaque_without_value_has_none_body() {
    let env = Environment::with_prelude();
    let decl = clean_parser::parse_decl("opaque myConst : Nat").expect("should parse");
    let result = elaborate_decl(&env, &decl).expect("should elaborate");

    match &result {
        ElabResult::Opaque { val: None, .. } => {}
        other => panic!(
            "opaque without body should elaborate to ElabResult::Opaque with val=None, got: {other:?}"
        ),
    }
}

// =========================================================================
// Registration warning tests (#2640)
// =========================================================================

/// #2640: explicit `sorry` in a theorem produces an ExplicitSorry warning.
#[test]
fn test_registration_warning_explicit_sorry() {
    use crate::registration_warning::RegistrationWarningKind;

    with_sorry_location_key("fixture:sorry:registration_warning:explicit", || {
        let mut env = Environment::with_prelude();
        env.init_true_false()
            .expect("True/False init should succeed");

        let decl = clean_parser::parse_decl("theorem explicit_sorry : True := sorry")
            .expect("should parse");
        let registered =
            elaborate_decl_and_register_with_warning(&mut env, &decl).expect("should elaborate");

        let warning = registered
            .warning
            .expect("explicit sorry should produce a warning");
        assert_eq!(warning.decl_name.to_string(), "explicit_sorry");
        assert_eq!(
            warning.kind,
            RegistrationWarningKind::ExplicitSorry,
            "explicit sorry should be classified as ExplicitSorry"
        );
        assert!(warning.summary.has_explicit_sorry);
        assert!(!warning.summary.has_synthetic_sorry);
        assert_eq!(warning.summary.trusted_axiom_count(), 0);
        let stored_summary = env
            .get_const(&Name::from_string("explicit_sorry"))
            .expect("declaration should be registered")
            .trust_summary();
        assert_eq!(warning.summary, stored_summary);
    });
}

/// #2667: synthetic sorry still reports the Lean 4-compatible warning lane.
#[test]
fn test_registration_warning_synthetic_sorry() {
    use crate::registration_warning::RegistrationWarningKind;
    use clean_parser::{Span, SurfaceDecl, SurfaceExpr, TerminationHints};

    with_sorry_location_key("fixture:sorry:registration_warning:synthetic", || {
        let mut env = Environment::with_prelude();
        env.init_true_false()
            .expect("True/False init should succeed");

        let decl = SurfaceDecl::Theorem {
            span: Span::dummy(),
            name: "synthetic_sorry".to_string(),
            universe_params: vec![],
            binders: vec![],
            ty: Box::new(parse_expr("True").expect("should parse theorem type")),
            proof: Box::new(SurfaceExpr::SyntheticSorry(Span::dummy())),
            attrs: vec![],
            termination: TerminationHints::default(),
            modifiers: DeclModifiers::default(),
            where_decls: vec![],
        };
        let registered =
            elaborate_decl_and_register_with_warning(&mut env, &decl).expect("should elaborate");

        let warning = registered
            .warning
            .expect("synthetic sorry theorem should produce a warning");
        assert_eq!(warning.decl_name.to_string(), "synthetic_sorry");
        assert_eq!(warning.kind, RegistrationWarningKind::SyntheticSorry);
        assert!(!warning.summary.has_explicit_sorry);
        assert!(warning.summary.has_synthetic_sorry);
        assert_eq!(warning.summary.trusted_axiom_count(), 0);
        let stored_summary = env
            .get_const(&Name::from_string("synthetic_sorry"))
            .expect("declaration should be registered")
            .trust_summary();
        assert_eq!(warning.summary, stored_summary);
    });
}

/// #2640: a clean declaration (no sorry) produces no warning.
#[test]
fn test_registration_warning_no_sorry() {
    let mut env = Environment::with_prelude();
    env.init_true_false()
        .expect("True/False init should succeed");

    let decl =
        clean_parser::parse_decl("theorem clean_thm : True := True.intro").expect("should parse");
    let registered =
        elaborate_decl_and_register_with_warning(&mut env, &decl).expect("should elaborate");

    assert!(
        registered.warning.is_none(),
        "clean theorem should produce no warning"
    );
}

/// #2667: `trustedArith` declarations now produce registration warnings.
#[test]
fn test_registration_warning_trusted_arith() {
    use crate::registration_warning::RegistrationWarningKind;

    let mut env = Environment::with_prelude();
    env.init_true_false()
        .expect("True/False init should succeed");

    let decl = clean_parser::parse_decl("theorem trusted_arith_decl : True := trustedArith")
        .expect("should parse");
    let registered =
        elaborate_decl_and_register_with_warning(&mut env, &decl).expect("should elaborate");

    let warning = registered
        .warning
        .expect("trustedArith theorem should produce a warning");
    assert_eq!(warning.decl_name.to_string(), "trusted_arith_decl");
    assert_eq!(warning.kind, RegistrationWarningKind::TrustedArith);
    assert!(!warning.summary.has_sorry());
    assert_eq!(warning.summary.trusted_arith_count, 1);
    assert_eq!(warning.summary.trusted_ay_count, 0);
    let stored_summary = env
        .get_const(&Name::from_string("trusted_arith_decl"))
        .expect("declaration should be registered")
        .trust_summary();
    assert_eq!(warning.summary, stored_summary);
}

/// #2667: `trustedAy` declarations now produce registration warnings.
#[test]
fn test_registration_warning_trusted_ay() {
    use crate::registration_warning::RegistrationWarningKind;

    let mut env = Environment::with_prelude();
    env.init_true_false()
        .expect("True/False init should succeed");

    let decl = clean_parser::parse_decl("theorem trusted_ay_decl : True := trustedAy")
        .expect("should parse");
    let registered =
        elaborate_decl_and_register_with_warning(&mut env, &decl).expect("should elaborate");

    let warning = registered
        .warning
        .expect("trustedAy theorem should produce a warning");
    assert_eq!(warning.decl_name.to_string(), "trusted_ay_decl");
    assert_eq!(warning.kind, RegistrationWarningKind::TrustedAy);
    assert!(!warning.summary.has_sorry());
    assert_eq!(warning.summary.trusted_arith_count, 0);
    assert_eq!(warning.summary.trusted_ay_count, 1);
    let stored_summary = env
        .get_const(&Name::from_string("trusted_ay_decl"))
        .expect("declaration should be registered")
        .trust_summary();
    assert_eq!(warning.summary, stored_summary);
}

/// #2640: Skipped declarations produce no warning.
#[test]
fn test_registration_warning_skipped_no_warning() {
    // B13: unknown export names are loud errors now; use the prelude env so
    // `export Nat (add)` succeeds and the no-warning pin stays meaningful.
    let mut env = Environment::with_prelude();
    let decl = clean_parser::parse_decl("export Nat (add)").expect("should parse");
    let registered =
        elaborate_decl_and_register_with_warning(&mut env, &decl).expect("should elaborate");

    assert!(matches!(registered.result, ElabResult::Skipped));
    assert!(
        registered.warning.is_none(),
        "skipped declarations should produce no warning"
    );
}

/// #3396: StateT universe over-generalization bug.
///
/// When an abbrev like `MySem` wraps `StateT MyState (Except MyError)` with
/// all-concrete types, the elaborator should specialize universe params to
/// concrete levels. Without the fix, definitions using such abbrevs fail with:
///   "Type mismatch: expected Sort(Succ(Param(u_9))), got Sort(Succ(Zero))"
/// because unsolved universe params leak into the registered definition.
#[test]
fn test_state_t_universe() {
    use clean_parser::parse_file;

    let mut env = Environment::with_prelude();
    let code = r#"
inductive MyError where
  | notFound : MyError

structure MyState where
  count : Nat

abbrev MySem (a : Type) := StateT MyState (Except MyError) a

def getState : MySem MyState := StateT.get
"#;
    let decls = parse_file(code).unwrap();
    for (i, decl) in decls.iter().enumerate() {
        let result = elaborate_decl_and_register(&mut env, decl);
        assert!(
            result.is_ok(),
            "StateT universe decl {} should elaborate: {:?}",
            i,
            result
        );
    }

    // Verify MySem has zero universe params (all levels specialized to concrete)
    let mysem_info = env.get_const(&Name::from_string("MySem"));
    assert!(
        mysem_info.is_some(),
        "MySem should be registered in the environment"
    );
    assert!(
        mysem_info.unwrap().level_params.is_empty(),
        "MySem should have zero universe params (all concrete), but has: {:?}",
        mysem_info.unwrap().level_params
    );

    // Verify getState has zero universe params (all levels specialized to concrete)
    let get_state_info = env.get_const(&Name::from_string("getState"));
    assert!(
        get_state_info.is_some(),
        "getState should be registered in the environment"
    );
    assert!(
        get_state_info.unwrap().level_params.is_empty(),
        "getState should have zero universe params (all concrete), but has: {:?}",
        get_state_info.unwrap().level_params
    );
}

/// Regression test for #3418: StateT.set returns `m PUnit` which must unify with
/// `MySem Unit` when Unit is an abbreviation for PUnit.{1}.
///
/// Before the fix, Unit was an independent inductive type, so `PUnit.{1}` and
/// `Unit` were not definitionally equal. The kernel reported:
///   "Type mismatch: expected Pi(MState, Sem Unit),
///    got Pi(MState, StateT MState (Except SemError) PUnit.{Succ(Zero)})"
///
/// The fix makes `Unit := PUnit.{1}` (a reducible definition), so the kernel
/// can unfold Unit during WHNF and establish definitional equality.
#[test]
fn test_state_t_set_punit_unit_equality() {
    use clean_parser::parse_file;

    let mut env = Environment::with_prelude();
    let code = r#"
inductive MyError where
  | notFound : MyError

structure MyState where
  counter : Nat

abbrev MySem (a : Type) := StateT MyState (Except MyError) a

def MySem.setState (s : MyState) : MySem Unit := StateT.set s
"#;
    let decls = parse_file(code).unwrap();
    for (i, decl) in decls.iter().enumerate() {
        let result = elaborate_decl_and_register(&mut env, decl);
        assert!(
            result.is_ok(),
            "#3418 regression: StateT.set decl {} should elaborate: {:?}",
            i,
            result
        );
    }

    // Verify MySem.setState was registered
    let set_state_info = env.get_const(&Name::from_string("MySem.setState"));
    assert!(
        set_state_info.is_some(),
        "MySem.setState should be registered in the environment"
    );
    assert!(
        set_state_info.unwrap().level_params.is_empty(),
        "MySem.setState should have zero universe params (all concrete), but has: {:?}",
        set_state_info.unwrap().level_params
    );
}

/// Regression test for #3418: StateT.modify returns `m PUnit` which must unify with
/// `MySem Unit` when Unit is an abbreviation for PUnit.{1}.
///
/// This extends the StateT.set test to also cover StateT.modify, which has the
/// same PUnit return type pattern: `(σ → σ) → StateT σ m PUnit`.
#[test]
fn test_state_t_modify_punit_unit_equality() {
    use clean_parser::parse_file;

    let mut env = Environment::with_prelude();
    let code = r#"
inductive MyError where
  | notFound : MyError

structure MyState where
  counter : Nat

abbrev MySem (a : Type) := StateT MyState (Except MyError) a

def MySem.setState (s : MyState) : MySem Unit := StateT.set s

def MySem.modifyState (f : MyState → MyState) : MySem Unit := StateT.modify f
"#;
    let decls = parse_file(code).unwrap();
    for (i, decl) in decls.iter().enumerate() {
        let result = elaborate_decl_and_register(&mut env, decl);
        assert!(
            result.is_ok(),
            "#3418 regression: StateT.modify decl {} should elaborate: {:?}",
            i,
            result
        );
    }

    // Verify both MySem.setState and MySem.modifyState were registered
    for name in &["MySem.setState", "MySem.modifyState"] {
        let info = env.get_const(&Name::from_string(name));
        assert!(
            info.is_some(),
            "{name} should be registered in the environment"
        );
        assert!(
            info.unwrap().level_params.is_empty(),
            "{name} should have zero universe params (all concrete), but has: {:?}",
            info.unwrap().level_params
        );
    }
}

#[test]
fn test_nested_subterm_hole_records_ascribed_expected_type() {
    use clean_parser::parse_decl;

    let env = {
        let mut e = Environment::new();
        e.init_nat().expect("Nat should initialize");
        e
    };

    // A NESTED (sub-term) hole: the `_` is ascribed to `Nat`, so the hole's
    // expected type is the sub-term goal `Nat`, distinct from the whole
    // declaration type. Elaboration of an unsolved `_` succeeds (it becomes a
    // metavariable); only kernel registration would reject the free variable,
    // so we exercise the elaborator core directly and snapshot its hole
    // contexts — exactly what the IDE surface reads to show a hole's goal.
    let src = "def f : Nat := Nat.succ (_ : Nat)";
    let decl = parse_decl(src).expect("decl should parse");

    let mut ctx = ElabCtx::new(&env);
    ctx.elab_decl(&decl).expect("declaration should elaborate");
    let holes = ctx.collect_hole_contexts();

    assert_eq!(
        holes.len(),
        1,
        "exactly one user-written `_` hole should be recorded, got {holes:?}"
    );
    let hole = &holes[0];

    // The hole span must point at the `_` token, not the whole declaration.
    let underscore = src.find('_').expect("source contains the hole token");
    assert_eq!(
        hole.span.start, underscore,
        "hole span should start at the `_` token (sub-term, not whole decl)"
    );
    assert!(
        hole.span.start < hole.span.end && hole.span.end <= src.len(),
        "hole span should be a narrow, valid sub-range of the declaration"
    );

    // The expected type recovered at the hole resolves to `Nat` (the ascription
    // target), demonstrating the sub-term goal was captured and instantiated.
    let rendered = format!("{:?}", hole.expected_type);
    assert!(
        rendered.contains("Nat"),
        "hole expected type should resolve to Nat, got {rendered}"
    );
}

#[test]
fn test_no_hole_decl_records_no_hole_context() {
    use clean_parser::parse_decl;

    let env = {
        let mut e = Environment::new();
        e.init_nat().expect("Nat should initialize");
        e
    };

    // A declaration with no user-written `_` holes records no hole contexts.
    let decl = parse_decl("def g : Nat := Nat.succ Nat.zero").expect("decl should parse");

    let mut ctx = ElabCtx::new(&env);
    ctx.elab_decl(&decl).expect("declaration should elaborate");
    let holes = ctx.collect_hole_contexts();

    assert!(
        holes.is_empty(),
        "a hole-free declaration must record no hole contexts, got {holes:?}"
    );
}

#[test]
fn test_body_hole_records_declaration_type() {
    use clean_parser::parse_decl;

    let env = {
        let mut e = Environment::new();
        e.init_nat().expect("Nat should initialize");
        e
    };

    // A body-level `_` hole: its expected type is the declaration's own type.
    let decl = parse_decl("def h : Nat := _").expect("decl should parse");

    let mut ctx = ElabCtx::new(&env);
    ctx.elab_decl(&decl).expect("declaration should elaborate");
    let holes = ctx.collect_hole_contexts();

    assert_eq!(
        holes.len(),
        1,
        "a body `_` hole should record exactly one hole context, got {holes:?}"
    );
    let rendered = format!("{:?}", holes[0].expected_type);
    assert!(
        rendered.contains("Nat"),
        "body hole expected type should resolve to Nat, got {rendered}"
    );
}

/// Regression: a `namespace` block whose middle inner declaration fails to
/// kernel-check must NOT abort the whole block and drop its good siblings (the
/// namespace-ABORT bug). The block should still return `Ok(Multiple(..))` with
/// the two successful inner decls registered/counted and the failing one
/// recorded as an explicit `ElabResult::Failed` leaf — so the checker reports
/// "2 passed, 1 failed", matching the same three decls written without a
/// namespace.
#[test]
fn test_namespace_collects_inner_failures_without_dropping_siblings() {
    use clean_parser::parse_file;

    reset_kernel_check_counter();

    let mut env = Environment::new();
    env.init_nat().expect("Nat should initialize");

    // `T.b`'s value is a `String`, not a `Nat`: it fails the kernel check while
    // `T.a` and `T.c` are well-typed.
    let decls = parse_file(
        "namespace T\n def a : Nat := 1\n def b : Nat := \"x\"\n def c : Nat := 3\n end T\n",
    )
    .expect("namespace block should parse");
    assert_eq!(decls.len(), 1, "should parse as a single namespace decl");

    let registered = elaborate_decl_and_register_with_warning(&mut env, &decls[0])
        .expect("namespace block must NOT abort on an inner failure");

    // Flatten to leaves exactly as `clean check` does.
    let mut leaves: Vec<&ElabResult> = Vec::new();
    registered.result.leaf_decls(&mut leaves);
    assert_eq!(
        leaves.len(),
        3,
        "all three inner decls must be counted as leaves, got {leaves:?}"
    );

    let failed: Vec<&&ElabResult> = leaves
        .iter()
        .filter(|l| matches!(l, ElabResult::Failed { .. }))
        .collect();
    let passed = leaves.len() - failed.len();
    assert_eq!(passed, 2, "T.a and T.c must be counted as passes");
    assert_eq!(failed.len(), 1, "exactly T.b must be recorded as Failed");

    // The failure must be COUNTED (not swallowed — asserted above as the single
    // `ElabResult::Failed` leaf) and the good siblings must still be registered.
    // B18: `def b : Nat := "x"` (String vs Nat) is now caught by the elaborator's
    // def-body `ensureHasType` (`reject_body_type_mismatch`) — a LOUD elaboration
    // error — so the ill-typed term is NEVER shipped to `add_decl` and the
    // kernel-check tally stays 0. The failure is not deferred to the kernel, yet
    // the block still does not abort and the failing leaf is still recorded.
    assert_eq!(
        kernel_check_failure_count(),
        0,
        "B18: the type mismatch is caught at elaboration, never reaching the kernel"
    );
    assert!(
        env.get_const(&Name::from_string("T.a")).is_some(),
        "successful sibling T.a must be registered despite the sibling failure"
    );
    assert!(
        env.get_const(&Name::from_string("T.c")).is_some(),
        "successful sibling T.c must be registered despite the sibling failure"
    );
    assert!(
        env.get_const(&Name::from_string("T.b")).is_none(),
        "the failing inner decl T.b must NOT be registered into the kernel"
    );
}

/// Track IJ: an empty-list literal `[]` as a tuple component must infer its
/// element type *and universe* from the expected `Prod` component type, instead
/// of leaking a polymorphic `List ?α` / `Sort (Succ (Succ ?u))` metavar to the
/// kernel re-check.
///
/// `(x, []) : A × List B` desugars to `Prod.mk x []` (= `Prod.mk x List.nil`).
/// `List.nil` has no operand to pin its element type, and `Prod.mk`'s second
/// argument type is the still-open implicit `?β`. The pre-arg expected-result
/// unification must pin `?β := List B` so `List.nil`'s element type/universe
/// resolve, otherwise the kernel re-check fails with a free universe variable.
/// A non-empty list `[a]` is unaffected — `List.cons a List.nil` pins the
/// element type from its head — so this regression is specific to the empty
/// literal. Mirrors the `bodyInstsWithResultDests` head row in the real
/// `TrustIr/Semantics/Eval.lean`.
#[test]
#[serial_test::serial]
fn test_empty_list_in_tuple_component_infers_element_type_and_universe() {
    use clean_parser::parse_decl;

    reset_kernel_check_counter();

    let mut env = Environment::with_prelude();

    // Empty list as the *second* tuple component.
    let decl_snd = parse_decl("def ij_tup_empty_snd : (Nat × List Nat) := (Nat.zero, [])").unwrap();
    // Empty list as the *first* tuple component.
    let decl_fst = parse_decl("def ij_tup_empty_fst : (List Nat × Nat) := ([], Nat.zero)").unwrap();

    let before = kernel_check_failure_count();
    let reg_snd = elaborate_decl_and_register(&mut env, &decl_snd);
    let reg_fst = elaborate_decl_and_register(&mut env, &decl_fst);
    let after = kernel_check_failure_count();

    assert!(
        reg_snd.is_ok(),
        "(Nat.zero, []) : Nat × List Nat must kernel-check: {reg_snd:?}"
    );
    assert!(
        reg_fst.is_ok(),
        "([], Nat.zero) : List Nat × Nat must kernel-check: {reg_fst:?}"
    );
    assert_eq!(
        before, after,
        "empty-list-in-tuple must not produce a kernel re-check failure (leaked universe metavar)"
    );
    assert!(
        env.get_const(&Name::from_string("ij_tup_empty_snd"))
            .is_some(),
        "the empty-list tuple definition must be registered"
    );
    assert!(
        env.get_const(&Name::from_string("ij_tup_empty_fst"))
            .is_some(),
        "the empty-list-first tuple definition must be registered"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// SOUNDNESS regressions: silent declaration drops (#open-in-body-drop,
// #section-drops-all-but-last). Found by TY's adversarial trust-base audit:
// both vectors let a declaration vanish with no error, no `Failed` leaf, and
// no registration — downstream (`elaborate_decl_and_register` library callers)
// counted the file green while the theorem was never kernel-checked.
// ═══════════════════════════════════════════════════════════════════════════

/// `open scoped X in theorem …` must ELABORATE (and so kernel-check + register)
/// the body. The scoped early-return used to fire before the body check,
/// silently dropping the theorem.
#[test]
fn test_open_scoped_in_body_is_elaborated_and_registered() {
    use clean_parser::parse_file;

    let mut env = Environment::with_prelude();
    let decls = parse_file(
        "open scoped Nat in theorem open_in_kept (n : Nat) : @Eq Nat n n := @Eq.refl Nat n",
    )
    .expect("parse");
    for d in &decls {
        elaborate_decl_and_register(&mut env, d).expect("open-in body must elaborate");
    }
    assert!(
        env.get_const(&Name::from_string("open_in_kept")).is_some(),
        "the `in`-body theorem must be registered (it used to be silently dropped)"
    );
}

/// …and because the body is now genuinely elaborated, a FALSE body must fail
/// LOUDLY (kernel rejection), not vanish.
#[test]
fn test_open_scoped_in_false_body_fails_loudly() {
    use clean_parser::parse_file;

    let mut env = Environment::with_prelude();
    let decls = parse_file(
        "open scoped Nat in theorem open_in_bogus (n : Nat) : @Eq Nat n (Nat.succ n) := @Eq.refl Nat n",
    )
    .expect("parse");
    let result: Result<Vec<_>, _> = decls
        .iter()
        .map(|d| elaborate_decl_and_register(&mut env, d))
        .collect();
    assert!(
        result.is_err(),
        "a false `in`-body theorem must be REJECTED (it used to be silently skipped)"
    );
    assert!(
        env.get_const(&Name::from_string("open_in_bogus")).is_none(),
        "the false theorem must not be registered"
    );
}

/// A `section` must surface (and so register) EVERY inner declaration, not just
/// the last one. `elab_section` used to keep only `last_result`.
#[test]
fn test_section_registers_every_declaration() {
    use clean_parser::parse_file;

    let mut env = Environment::with_prelude();
    let decls = parse_file(
        "section\n\
         theorem section_first (n : Nat) : @Eq Nat n n := @Eq.refl Nat n\n\
         theorem section_last (n : Nat) : @Eq Nat n n := @Eq.refl Nat n\n\
         end",
    )
    .expect("parse");
    for d in &decls {
        elaborate_decl_and_register(&mut env, d).expect("section must elaborate");
    }
    assert!(
        env.get_const(&Name::from_string("section_first")).is_some(),
        "the FIRST section declaration must be registered (it used to be silently dropped)"
    );
    assert!(
        env.get_const(&Name::from_string("section_last")).is_some(),
        "the last section declaration must (still) be registered"
    );
}
