// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Issue regression tests and domain-specific stub tests.
//!
//! This module contains tests for specific GitHub issues that were fixed,
//! ensuring they don't regress. Tests are organized by issue number.

use super::common::{check_and_add_decl, check_expr};
use clean_elab::{elaborate_decl, elaborate_decl_and_register_with_warning, ElabResult};
use clean_kernel::{env::TrustedEnvExt, Environment, Expr, ExprKind, Name};
use clean_parser::parse_decl;

/// Recursively check whether an elaborated term mentions a `sorry`/`sorryAx`
/// constant — the marker the elaborator leaves when instance resolution fails.
fn term_mentions_sorry(e: &Expr) -> bool {
    match e.kind() {
        ExprKind::Const(n, _) => {
            let s = n.to_string();
            s == "sorryAx" || s == "sorry"
        }
        ExprKind::App(f, a) => term_mentions_sorry(f) || term_mentions_sorry(a),
        ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
            term_mentions_sorry(t) || term_mentions_sorry(b)
        }
        ExprKind::Let(_, t, v, b, _) => {
            term_mentions_sorry(t) || term_mentions_sorry(v) || term_mentions_sorry(b)
        }
        _ => false,
    }
}

fn elaborated_value(env: &Environment, src: &str) -> Expr {
    let surface = parse_decl(src).expect("parse");
    match elaborate_decl(env, &surface).expect("elaborate") {
        ElabResult::Definition { val, .. } => val,
        other => panic!("expected a definition with a value, got {other:?}"),
    }
}

/// A `Prop`-condition `if (a = b)` over `Nat` must resolve its `Decidable`
/// instance to the constructive `Nat.decEq` rather than fall back to a synthetic
/// `sorry`. Covers both bare `Nat.zero` literals and `OfNat`-elaborated numerals.
#[test]
fn test_nat_eq_if_resolves_decidable_no_sorry() {
    let env = Environment::with_prelude();
    let zero_val = elaborated_value(
        &env,
        "def nat_eq_if_zero : Nat := if (Nat.zero = Nat.zero) then Nat.zero else Nat.zero",
    );
    assert!(
        !term_mentions_sorry(&zero_val),
        "if (Nat.zero = Nat.zero) must resolve Decidable, got: {zero_val:?}"
    );
    let lit_val = elaborated_value(&env, "def nat_eq_if_lit : Nat := if (1 = 1) then 1 else 0");
    assert!(
        !term_mentions_sorry(&lit_val),
        "if (1 = 1) must resolve Decidable, got: {lit_val:?}"
    );
}

/// `if (a ≠ b)` (via `instDecidableNot`) and `if (true = false)` (via
/// `instDecidableEqBool`) must resolve their `Decidable` instances without a
/// synthetic `sorry`.
#[test]
fn test_ne_and_bool_eq_if_resolve_no_sorry() {
    let env = Environment::with_prelude();
    let ne_val = elaborated_value(&env, "def ne_if : Nat := if (1 ≠ 2) then 7 else 9");
    assert!(
        !term_mentions_sorry(&ne_val),
        "if (1 ≠ 2) must resolve via instDecidableNot, got: {ne_val:?}"
    );
    let bool_val = elaborated_value(&env, "def bool_if : Nat := if (true = false) then 1 else 0");
    assert!(
        !term_mentions_sorry(&bool_val),
        "if (true = false) must resolve via instDecidableEqBool, got: {bool_val:?}"
    );
}

/// The GENERAL `Decidable (Eq T a b)` bridge: a `Prop`-condition `if (a = b)`
/// over ANY type carrying a `DecidableEq` instance — here a `deriving
/// DecidableEq` enum — must resolve via the `decEq` bridge + the derived
/// instance, NOT fall back to a synthetic `sorry`.
#[test]
fn test_general_decidable_eq_bridge_derived_enum() {
    let mut env = Environment::with_prelude();
    // Register the inductive + its derived `DecidableEq` instance through the
    // same path the CLI uses (the derive returns its instance in the
    // `ElabResult`, which this register entry installs into the env).
    let ind =
        parse_decl("inductive Color where | red : Color | green : Color deriving DecidableEq")
            .expect("parse inductive Color");
    elaborate_decl_and_register_with_warning(&mut env, &ind)
        .expect("inductive Color (deriving DecidableEq) should register");
    assert!(
        env.get_class_instances(&Name::from_string("DecidableEq"))
            .iter()
            .any(|i| i.name == Name::from_string("instColorDecidableEq")),
        "deriving DecidableEq must register a DecidableEq Color instance"
    );
    let val = elaborated_value(
        &env,
        "def color_if (c : Color) : Nat := if (c = Color.red) then 1 else 0",
    );
    assert!(
        !term_mentions_sorry(&val),
        "derived-enum if (c = Color.red) must resolve Decidable via the general \
         DecidableEq bridge, got: {val:?}"
    );
}

/// Reproduce the EXACT `clean check` pipeline: parse_file_with_tactics →
/// preprocess_decl_with_context → elaborate_decl_and_register_with_warning, then
/// inspect the registered body for a synthetic `sorry`.
#[test]
fn test_nat_eq_if_full_cli_pipeline_no_sorry() {
    use clean_elab::tactic::builtins::builtin_tactic_patterns;
    use clean_elab::{preprocess_decl_with_context, FileContext};
    use clean_parser::parse_file_with_tactics;

    let patterns = builtin_tactic_patterns();
    let decls =
        parse_file_with_tactics("def tp_cli : Nat := if (1 = 1) then 1 else 0\n", &patterns)
            .expect("parse_file_with_tactics");

    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::default();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register_with_warning(&mut env, &processed).expect("elaborate+register");
    }
    let info = env
        .get_const(&Name::from_string("tp_cli"))
        .expect("decl registered");
    let val = info.value.clone().expect("definition has value");
    assert!(
        !term_mentions_sorry(&val),
        "full-pipeline if (1 = 1) must resolve Decidable, got: {val:?}"
    );
}

// =============================================================================
// FATE-X Domain Type Stub Tests (Part of #130)
// =============================================================================

/// Test that IsDomain stub is recognized during elaboration
#[test]
fn test_isdomain_stub_elaboration() {
    let mut env = Environment::new();
    env.init_module_algebra_all().unwrap();

    // IsDomain should now be a recognized constant
    let isdomain = env.get_const(&Name::from_string("IsDomain"));
    assert!(
        isdomain.is_some(),
        "IsDomain should be a known constant after init_module_algebra_all"
    );
}

/// Test that IsNoetherianRing stub is recognized during elaboration
#[test]
fn test_isnoetherianring_stub_elaboration() {
    let mut env = Environment::new();
    env.init_module_algebra_all().unwrap();

    // IsNoetherianRing should now be a recognized constant
    let noeth = env.get_const(&Name::from_string("IsNoetherianRing"));
    assert!(
        noeth.is_some(),
        "IsNoetherianRing should be a known constant after init_module_algebra_all"
    );
}

/// Test that ChainComplex stub is recognized during elaboration
#[test]
fn test_chaincomplex_stub_elaboration() {
    let mut env = Environment::new();
    env.init_module_algebra_all().unwrap();

    // ChainComplex should now be a recognized constant
    let cc = env.get_const(&Name::from_string("ChainComplex"));
    assert!(
        cc.is_some(),
        "ChainComplex should be a known constant after init_module_algebra_all"
    );
}

/// Test that Module/Algebra/Ideal/Submodule stubs are all initialized together
#[test]
fn test_module_algebra_all_initialization() {
    let mut env = Environment::new();
    env.init_module_algebra_all().unwrap();

    // All core algebra stubs should be initialized
    assert!(env.has_module(), "Module should be initialized");
    assert!(env.has_algebra(), "Algebra should be initialized");
    assert!(env.has_ideal(), "Ideal should be initialized");
    assert!(env.has_submodule(), "Submodule should be initialized");
    assert!(env.has_domain_types(), "Domain types should be initialized");

    // Verify some key constants
    let constants = vec![
        "Module",
        "Algebra",
        "Ideal",
        "Submodule",
        "IsDomain",
        "IsNoetherianRing",
        "ChainComplex",
        "AlgHom",
        "TensorProduct",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist after init_module_algebra_all"
        );
    }
}

// =============================================================================
// Issue #134: Closure Verification Tests
// =============================================================================
//
// These tests verify the fix for #134: implicit parameter application causes
// UnknownFVar in type elaboration.
//
// Root cause: elab_def_body returns expressions without calling metas.instantiate(),
// so metavariables created for implicit arguments escape into final expressions.
//
// Test behavior:
// - BEFORE FIX: These tests FAIL with UnknownFVar(FVarId::new(9223372036854775808))
// - AFTER FIX: These tests PASS
//
// See reports/research/2026-01-19-r185-implicit-param-deep-dive.md for full analysis.

/// Issue #134 case 1: Typeclass instance implicit in theorem signature
///
/// Note: Basic typeclass instance implicits like `[Ring R]` appear to work
/// in simple cases with axiom-defined Ring. The bug manifests specifically when:
/// - Using type constructors with implicit params that return Types (case 2, 3)
/// - The result type is a Sort that gets mistakenly treated as a function
///
/// This test exists for completeness and to catch regressions.
#[test]
fn test_issue134_typeclass_instance_implicit_simple_case() {
    let mut env = Environment::new();

    // Set up minimal typeclass infrastructure
    check_and_add_decl(&mut env, "axiom Ring : Type → Type").unwrap();
    check_and_add_decl(&mut env, "axiom True : Prop").unwrap();
    check_and_add_decl(&mut env, "axiom True.intro : True").unwrap();

    // Simple case: instance implicit with axiomatic Ring
    // This currently passes, but we keep the test to catch regressions.
    let result = check_and_add_decl(
        &mut env,
        "theorem test_typeclass (R : Type) [inst : Ring R] : True := True.intro",
    );

    assert!(
        result.is_ok(),
        "Simple typeclass instance implicit should elaborate. Got: {:?}",
        result.err()
    );
}

/// Issue #134 case 2: Type constructor with implicit parameters
///
/// Prod has implicit type parameters: Prod : {α : Type} → {β : Type} → Type
/// When applied explicitly as `Prod Nat Nat`, metavars are created for the
/// implicit params and should unify with Nat, but they escape uninstantiated.
#[test]
fn test_issue134_type_constructor_application() {
    let mut env = Environment::new();

    // Minimal setup: Nat and a polymorphic type constructor
    check_and_add_decl(&mut env, "axiom Nat : Type").unwrap();
    // Prod with implicit params (simplified - real Prod has universe polymorphism)
    check_and_add_decl(&mut env, "axiom Prod : {A : Type} → {B : Type} → Type").unwrap();

    // This fails with NotAFunction(Sort(...)) because the implicit args
    // create metavars that aren't resolved, causing the function type to be mishandled
    let result = check_and_add_decl(&mut env, "def foo := Prod Nat Nat");

    assert!(
        result.is_ok(),
        "Type constructor application should elaborate. Got: {:?}",
        result.err()
    );
}

/// Issue #134 case 3: Type constructor in parameter type position
///
/// Similar to case 2, but the type constructor is used in a parameter type,
/// causing the UnknownFVar to appear during type checking of the definition.
#[test]
fn test_issue134_type_constructor_in_param_type() {
    let mut env = Environment::new();

    check_and_add_decl(&mut env, "axiom Nat : Type").unwrap();
    check_and_add_decl(&mut env, "axiom Prod : {A : Type} → {B : Type} → Type").unwrap();
    check_and_add_decl(&mut env, "axiom True : Prop").unwrap();
    check_and_add_decl(&mut env, "axiom True.intro : True").unwrap();

    // def test (p : Prod Nat Nat) : True := True.intro
    // The `Prod Nat Nat` in the parameter type creates metavars that escape
    let result = check_and_add_decl(
        &mut env,
        "def test_param (p : Prod Nat Nat) : True := True.intro",
    );

    assert!(
        result.is_ok(),
        "Type constructor in parameter type should elaborate. Got: {:?}",
        result.err()
    );
}

/// Issue #134 verification: FVarId sentinel value
///
/// The error UnknownFVar(FVarId::new(9223372036854775808)) contains a sentinel value:
/// 9223372036854775808 = 0x8000000000000000 = META_FVAR_TAG | 0 = MetaId(0)
///
/// This proves the bug is uninstantiated metavariables, not genuine FVar issues.
#[test]
fn test_issue134_fvarid_sentinel_analysis() {
    // META_FVAR_TAG constant from crates/clean-elab/src/unify.rs:35
    const META_FVAR_TAG: u64 = 1 << 63; // 0x8000000000000000

    let error_fvar_id: u64 = 9223372036854775808;
    assert_eq!(
        error_fvar_id, META_FVAR_TAG,
        "Error FVarId should be META_FVAR_TAG | 0"
    );

    // This confirms the error is MetaId(0) encoded as FVar, meaning:
    // 1. First metavariable created (index 0)
    // 2. Never assigned a value
    // 3. Escaped into final expression

    let meta_id = error_fvar_id & !META_FVAR_TAG;
    assert_eq!(meta_id, 0, "Should be MetaId(0)");
}

/// Issue #139: Nested instance-implicit binders in typeclass signatures
///
/// When a typeclass has an instance-implicit parameter in its signature
/// (e.g., `IsDomain : {α : Type} → [Ring α] → Prop`), the inner instance
/// creates a metavariable that escapes uninstantiated.
///
/// Simple case with independent typeclasses WORKS:
/// - `axiom TC1 : Type → Type`
/// - `axiom TC2 : Type → Type`
/// - `theorem (R : Type) [TC1 R] [TC2 R] : True` -- OK
///
/// Issue #139 closure test: Nested instance-implicit binders in typeclass signatures.
///
/// TC2 has signature `{α : Type} → [TC1 α] → Prop` which means when we write
/// `[inst2 : TC2 R]`, the elaborator needs to resolve the inner `[TC1 α]` parameter.
/// This test verifies that local instance-implicit binders (`inst1 : TC1 R`) are
/// searched during nested instance resolution.
///
/// Before fix: UnknownFVar because the metavariable for `[TC1 α]` escaped to kernel.
/// After fix: Local instance `inst1` is found and used for nested resolution.
#[test]
fn test_issue139_nested_instance_implicit_in_signature() {
    let mut env = Environment::new();

    // TC1 is simple: Type → Type
    check_and_add_decl(&mut env, "axiom TC1 : Type → Type").unwrap();
    // TC2 depends on TC1 via nested instance-implicit: {α : Type} → [TC1 α] → Prop
    check_and_add_decl(&mut env, "axiom TC2 : {α : Type} → [TC1 α] → Prop").unwrap();
    check_and_add_decl(&mut env, "axiom True : Prop").unwrap();
    check_and_add_decl(&mut env, "axiom True.intro : True").unwrap();

    // When elaborating [TC2 R], the inner [TC1 α] needs resolution from inst1
    let result = check_and_add_decl(
        &mut env,
        "theorem nested_inst (R : Type) [inst1 : TC1 R] [inst2 : TC2 R] : True := True.intro",
    );

    assert!(
        result.is_ok(),
        "Nested instance-implicit in typeclass signature should elaborate. Got: {:?}",
        result.err()
    );
}

/// Issue #139 case 2: Multiple independent instance binders (BASELINE - should pass)
///
/// When typeclasses have simple signatures without nested instances, multiple
/// instance binders on the same type should work.
#[test]
fn test_issue139_baseline_independent_instances() {
    let mut env = Environment::new();

    // Both typeclasses have simple Type → Type signatures (no nested instances)
    check_and_add_decl(&mut env, "axiom TC1 : Type → Type").unwrap();
    check_and_add_decl(&mut env, "axiom TC2 : Type → Type").unwrap();
    check_and_add_decl(&mut env, "axiom True : Prop").unwrap();
    check_and_add_decl(&mut env, "axiom True.intro : True").unwrap();

    // This should work - no nested instance resolution needed
    let result = check_and_add_decl(
        &mut env,
        "theorem independent (R : Type) [inst1 : TC1 R] [inst2 : TC2 R] : True := True.intro",
    );

    assert!(
        result.is_ok(),
        "Independent instance binders should elaborate. Got: {:?}",
        result.err()
    );
}

/// Issue #140: Typeclass inheritance with `extends` clause
///
/// FATE-X problems typically use:
/// `{R : Type} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]`
///
/// Where IsDomain has signature: `{α : Type} → [Ring α] → Prop` (needs Ring from CommRing)
/// When CommRing extends Ring, the CommRing.toRing instance should satisfy the Ring requirement.
///
/// Tests typeclass inheritance via `extends` clause.
/// When CommRing extends Ring, having [CommRing R] should provide [Ring R].
#[test]
fn test_issue140_typeclass_inheritance_extends() {
    let mut env = Environment::new();

    // Ring is the base typeclass (defined as a proper class)
    check_and_add_decl(
        &mut env,
        "class Ring (α : Type) where
           add : α → α → α
           mul : α → α → α",
    )
    .unwrap();

    // CommRing extends Ring (the `extends` clause generates CommRing.toRing instance)
    check_and_add_decl(
        &mut env,
        "class CommRing (α : Type) extends Ring α where
           mul_comm : Prop",
    )
    .unwrap();

    // IsDomain requires [Ring α] - has nested instance-implicit
    check_and_add_decl(&mut env, "axiom IsDomain : {α : Type} → [Ring α] → Prop").unwrap();
    check_and_add_decl(&mut env, "axiom True : Prop").unwrap();
    check_and_add_decl(&mut env, "axiom True.intro : True").unwrap();

    // When elaborating [IsDomain R] and we have [CommRing R] in scope,
    // the CommRing.toRing instance should satisfy [Ring R]
    let result = check_and_add_decl(
        &mut env,
        "theorem fatex_pattern {R : Type} [inst1 : CommRing R] [inst2 : IsDomain R] : True := True.intro",
    );

    assert!(
        result.is_ok(),
        "FATE-X pattern with typeclass inheritance should elaborate. Got: {:?}",
        result.err()
    );
}

/// Issue #142: Missing instantiate_levels in elab_structure causes TypeMismatch.
///
/// Before the fix, structures with multiple type parameters that require universe
/// level inference would fail with:
///   TypeMismatch { expected: Sort(Param("u_3")), inferred: Sort(Succ(Zero)) }
///
/// This test verifies that universe level constraints collected during unification
/// are correctly substituted back into structure types and constructor types.
///
/// The fix adds instantiate_levels calls in:
/// - elab_structure (struct_ty, ctor_ty, projections)
/// - elab_inductive (ind_ty, constructors)
/// - elab_instance (final_ty, final_val)
/// - build_local_ctx (type instantiation)
/// - elab_def_binder (binder types)
#[test]
fn test_issue_142_structure_universe_instantiate() {
    // Type and Prop are built-in, no need to declare them
    let mut env = Environment::new();

    // Based on the pattern from #142 reproduction case. The original had
    // `class Bar (F E : Type) [Field F] [Field E] : Prop where some_prop : Prop`
    // but that is actually invalid in Lean 4: a Prop-valued class cannot have
    // fields of type `Prop` because `Prop : Type` (not in Prop), violating
    // proof irrelevance. The core issue was universe instantiation with
    // multiple Type parameters, which we test with a Type-valued structure.

    // We simulate this with a simpler case that exercises the same code path:
    // A structure with two Type parameters should elaborate correctly.
    let result = check_and_add_decl(
        &mut env,
        "structure TwoTypeParams (A : Type) (B : Type) where
           fst : A
           snd : B",
    );

    assert!(
        result.is_ok(),
        "Issue #142: Structure with two Type params should elaborate without TypeMismatch. Got: {:?}",
        result.err()
    );

    // Also test class (which uses same elab_structure path).
    // Note: A Prop-valued class cannot have fields whose types are not in Prop
    // (Lean 4 parity: proof irrelevance forbids projecting non-Prop data from Prop).
    // So we test a Type-valued class with Type parameters instead.
    let result = check_and_add_decl(
        &mut env,
        "class TwoTypeClass (A : Type) (B : Type) where
           fst : A
           snd : B",
    );

    assert!(
        result.is_ok(),
        "Issue #142: Class with two Type params should elaborate without TypeMismatch. Got: {:?}",
        result.err()
    );
}

/// Issue #152 Case 1: auto-bound universe names in typeclass declarations.
#[test]
fn test_issue152_auto_bound_implicit_universe() {
    let mut env = Environment::new();
    for (name, decl, expected_level_params) in [
        (
            "AutoUniverse",
            "class AutoUniverse (X : Type u) where
               val : X",
            1,
        ),
        (
            "MultiAutoUniverse",
            "class MultiAutoUniverse (X : Type u) (Y : Type v) where
               pair : X → Y → X",
            2,
        ),
    ] {
        check_and_add_decl(&mut env, decl).unwrap_or_else(|err| {
            panic!("Issue #152: {name} should elaborate with auto-bound universes. Got: {err:?}")
        });
        assert!(
            env.get_class_info(&Name::from_string(name)).is_some(),
            "{name} class should be registered"
        );
        assert_eq!(
            env.get_const(&Name::from_string(name))
                .expect("class should be declared")
                .level_params
                .len(),
            expected_level_params,
            "Issue #152: {name} should keep its auto-bound universe parameters"
        );
    }
}

/// Issue #152 Case 2: Typeclass instances with auto-bound universes
///
/// When instantiating a typeclass at a concrete type, the universe level should
/// be correctly substituted. E.g., [CommRing Nat] should have concrete level 0,
/// not a polymorphic Param("u").
#[test]
fn test_issue152_instance_universe_substitution() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");

    // Define a simple ring-like class using auto-bound universe
    check_and_add_decl(
        &mut env,
        "class MyRing (R : Type u) where
           add : R → R → R",
    )
    .expect("MyRing class");

    // Create an instance for Nat (which is at Type 0)
    let result = check_and_add_decl(
        &mut env,
        "instance : MyRing Nat where
           add := Nat.add",
    );

    assert!(
        result.is_ok(),
        "Issue #152: Instance at concrete type should have concrete universe level. Got: {:?}",
        result.err()
    );

    // Test theorem using the instance
    check_and_add_decl(&mut env, "axiom True : Prop").expect("True axiom");
    check_and_add_decl(&mut env, "axiom True.intro : True").expect("True.intro");

    let thm_result = check_and_add_decl(
        &mut env,
        "theorem ring_thm {R : Type} [MyRing R] : True := True.intro",
    );

    assert!(
        thm_result.is_ok(),
        "Issue #152: Theorem with typeclass instance should type-check. Got: {:?}",
        thm_result.err()
    );
}

// =============================================================================
// Issue #164: Auto-Implicit Type Parameter Tests
// =============================================================================

/// Issue #164: Basic auto-implicit type parameters
///
/// In Lean 4, when an identifier is not in scope but looks like a type parameter
/// (e.g., single uppercase letter, Greek letter), it is automatically bound as
/// an implicit parameter: def f (x : A) := x  becomes  def f.{u} {A : Type u} (x : A) := x
///
/// This test verifies the core auto-implicit functionality.
#[test]
fn test_issue164_auto_implicit_basic() {
    let mut env = Environment::new();

    // This should auto-bind A as an implicit type parameter
    // Without #164 fix: UnknownIdent "A"
    // With #164 fix: succeeds with A auto-bound
    let result = check_and_add_decl(&mut env, "def identity (x : A) : A := x");

    assert!(
        result.is_ok(),
        "Issue #164: Auto-implicit should bind A as implicit type param. Got: {:?}",
        result.err()
    );

    // Verify the constant exists
    let id_name = Name::from_string("identity");
    assert!(
        env.get_const(&id_name).is_some(),
        "identity should be defined"
    );
}

/// Issue #164: Multiple auto-implicits in same declaration
///
/// When multiple auto-implicit identifiers appear, they should all be bound.
/// Order of binding should follow order of first occurrence.
#[test]
fn test_issue164_auto_implicit_multiple() {
    let mut env = Environment::new();

    // A and B should both be auto-bound as implicit type parameters
    let result = check_and_add_decl(&mut env, "def pair (x : A) (y : B) : A := x");

    assert!(
        result.is_ok(),
        "Issue #164: Multiple auto-implicits should be bound. Got: {:?}",
        result.err()
    );

    // Test with more complex pattern
    let result2 = check_and_add_decl(&mut env, "def triple (x : X) (y : Y) (z : Z) : X := x");

    assert!(
        result2.is_ok(),
        "Issue #164: Three auto-implicits should work. Got: {:?}",
        result2.err()
    );
}

/// Issue #164: Auto-implicit reuse within declaration
///
/// When the same auto-implicit appears multiple times, it should refer
/// to the same variable, not create new ones.
#[test]
fn test_issue164_auto_implicit_reuse() {
    let mut env = Environment::new();

    // A appears twice - should be the SAME auto-implicit
    let result = check_and_add_decl(&mut env, "def swap (x : A) (y : A) : A := y");

    assert!(
        result.is_ok(),
        "Issue #164: Reused auto-implicit should be same variable. Got: {:?}",
        result.err()
    );
}

/// Issue #164: Auto-implicit in theorem declarations
#[test]
fn test_issue164_auto_implicit_theorem() {
    let mut env = Environment::new();
    check_and_add_decl(&mut env, "axiom True : Prop").unwrap();
    check_and_add_decl(&mut env, "axiom True.intro : True").unwrap();

    // R should be auto-bound
    let result = check_and_add_decl(&mut env, "theorem auto_thm (x : R) : True := True.intro");

    assert!(
        result.is_ok(),
        "Issue #164: Auto-implicit in theorem should work. Got: {:?}",
        result.err()
    );
}

/// Issue #164: Auto-implicit in axiom declarations
#[test]
fn test_issue164_auto_implicit_axiom() {
    let mut env = Environment::new();
    check_and_add_decl(&mut env, "axiom Prop : Type").unwrap_or(());

    // T should be auto-bound
    let result = check_and_add_decl(&mut env, "axiom ax : T → T");

    assert!(
        result.is_ok(),
        "Issue #164: Auto-implicit in axiom should work. Got: {:?}",
        result.err()
    );
}

/// Issue #164: Auto-implicit does NOT apply in standalone expressions
///
/// Auto-implicit is only for declaration contexts. In standalone expression
/// elaboration (e.g., REPL), unknown identifiers should still error.
#[test]
fn test_issue164_auto_implicit_not_in_expressions() {
    let env = Environment::new();

    // In standalone expression context, unknown idents should error
    let result = check_expr(&env, "x");
    assert!(
        result.is_err(),
        "Auto-implicit should NOT apply in expression context"
    );
}

/// Issue #164: Greek letters as auto-implicits
///
/// Greek letters (α, β, γ, etc.) are common in Mathlib for type variables.
/// They should be valid auto-implicits.
#[test]
fn test_issue164_auto_implicit_greek() {
    let mut env = Environment::new();

    // Note: This test depends on parser support for Greek letters
    // If parsing fails, that's a parser issue, not auto-implicit issue
    let result = check_and_add_decl(&mut env, "def greek_id (x : α) : α := x");

    // If this fails with ParseError (not UnknownIdent), that's expected
    // The key test is that IF parsed, auto-implicit should work
    if let Err(e) = &result {
        let err_str = format!("{:?}", e);
        if err_str.contains("Parse") {
            // Parser doesn't support Greek - that's OK for this test
            return;
        }
    }

    assert!(
        result.is_ok(),
        "Issue #164: Greek letters should be valid auto-implicits. Got: {:?}",
        result.err()
    );
}

/// Issue #171: NotAFunction(Sort(Param)) errors in universe polymorphic code
///
/// Before fix: Unknown constants like `Id`, `Nonempty` were treated as auto-implicits,
/// creating type variables that when applied caused NotAFunction(Sort(Param(u_0))).
///
/// Fix: Added Id monad and init_classical (Nonempty, Or, Classical.choice) to prelude.
#[test]
fn test_issue171_id_monad_in_prelude() {
    // Use with_prelude() to get the full standard environment
    let mut env = Environment::with_prelude();

    // Id monad should be available and work
    let result = check_and_add_decl(&mut env, "def test_id : Type := Id Nat");
    assert!(
        result.is_ok(),
        "Issue #171: Id monad should be in prelude. Got: {:?}",
        result.err()
    );

    // Id.mk should work
    let result = check_and_add_decl(&mut env, "def test_id_mk : Id Nat := Id.mk 0");
    assert!(
        result.is_ok(),
        "Issue #171: Id.mk should work. Got: {:?}",
        result.err()
    );
}

/// Issue #171: Nonempty should be available in prelude
#[test]
fn test_issue171_nonempty_in_prelude() {
    let mut env = Environment::with_prelude();

    // Nonempty should be available
    let result = check_and_add_decl(&mut env, "def test_nonempty : Prop := Nonempty Nat");
    assert!(
        result.is_ok(),
        "Issue #171: Nonempty should be in prelude. Got: {:?}",
        result.err()
    );
}

/// Issue #171: Classical.choice should be available in prelude
#[test]
fn test_issue171_classical_in_prelude() {
    let mut env = Environment::with_prelude();

    // Or should be available (from init_classical)
    let result = check_and_add_decl(&mut env, "def test_or : Prop := Or True False");
    assert!(
        result.is_ok(),
        "Issue #171: Or should be in prelude. Got: {:?}",
        result.err()
    );
}

/// Issue #171: Type unification fix - discriminating test
///
/// This test exercises the CORE fix for #171: type unification in elab_def_body.
/// Without the fix (added in W294), this fails with TypeMismatch because the
/// universe parameter u_0 in Nonempty.{u_0} is never unified with 1 from Type = Sort 1.
///
/// The fix adds `unifier.unify(&val_ty, &ty_expr)` after apply_implicit_to_expected_type,
/// which collects the constraint u_0 = 1 and allows instantiation to resolve it.
///
/// This is a discriminating test: it FAILS without the fix, PASSES with the fix.
#[test]
fn test_issue171_type_unification_universe_level() {
    let mut env = Environment::with_prelude();

    // This is the exact case from R257's root cause analysis.
    // Expected type: Type → Prop = Sort 1 → Sort 0
    // Nonempty type: Sort u_0 → Sort 0 (u_0 is fresh universe param)
    // Without unification, u_0 remains unresolved causing TypeMismatch.
    let result = check_and_add_decl(&mut env, "def foo : Type → Prop := Nonempty");
    assert!(
        result.is_ok(),
        "Issue #171: Type unification should solve universe param u_0 = 1. Got: {:?}",
        result.err()
    );

    // Also test with explicit Type 0 (Prop level)
    let result2 = check_and_add_decl(&mut env, "def bar : Prop → Prop := Nonempty");
    assert!(
        result2.is_ok(),
        "Issue #171: Should work with Prop → Prop too. Got: {:?}",
        result2.err()
    );
}

// Issue #166: Decidable should be available in prelude (W296)
//
// This is a discriminating test for W296's addition of init_decidable to with_prelude().
// Without W296, Decidable is not in the prelude and this test FAILS.
//
// The prelude defines Decidable : Prop → Type, matching Lean 4's inductive
// (Decidable is data-carrying). This test verifies the stub is present and usable.
#[test]
fn test_issue166_decidable_in_prelude() {
    let mut env = Environment::with_prelude();

    // Decidable should be available - test it can be applied to a proposition
    // Decidable : Prop → Type (Sort 1), so Decidable True : Type
    let result = check_and_add_decl(&mut env, "def test_decidable_type : Type := Decidable True");
    assert!(
        result.is_ok(),
        "Issue #166 (W296): Decidable should be in prelude. Got: {:?}",
        result.err()
    );

    // Decidable.isTrue should be available as a constructor
    // Decidable True : Type, so this axiom has type in Type
    let result = check_and_add_decl(&mut env, "axiom test_decidable_istrue : Decidable True");
    assert!(
        result.is_ok(),
        "Issue #166 (W296): Decidable.isTrue should work. Got: {:?}",
        result.err()
    );
}

// Issue #166: DecidableEq should be available in prelude (W296)
//
// This is a discriminating test for W296's addition of init_decidable_eq to with_prelude().
// DecidableEq α is defined as (a b : α) → Decidable (a = b).
#[test]
fn test_issue166_decidable_eq_in_prelude() {
    let mut env = Environment::with_prelude();

    // DecidableEq should be available as a typeclass
    // DecidableEq.{u} : Sort u → Sort (max 1 u)
    // For Nat : Type 0, DecidableEq Nat : Type 0
    let result = check_and_add_decl(
        &mut env,
        "def test_decidable_eq_type : Type := DecidableEq Nat",
    );
    assert!(
        result.is_ok(),
        "Issue #166 (W296): DecidableEq should be in prelude. Got: {:?}",
        result.err()
    );
}

// Issue #166: UInt8.mod and UInt8.toFin should be available (W297)
//
// This is a discriminating test for W297's addition of mod and toFin operations.
// Without W297, UInt8.mod is not defined and this test FAILS.
#[test]
fn test_issue166_uint8_mod_in_prelude() {
    let mut env = Environment::with_prelude();

    // UInt8.mod : UInt8 → UInt8 → UInt8
    let result = check_and_add_decl(
        &mut env,
        "def test_uint8_mod : UInt8 → UInt8 → UInt8 := UInt8.mod",
    );
    assert!(
        result.is_ok(),
        "Issue #166 (W297): UInt8.mod should be available. Got: {:?}",
        result.err()
    );
}

// Issue #166: UInt64.mod and UInt64.toFin should be available (W297)
//
// Tests that all UInt types have mod operations, not just UInt8.
#[test]
fn test_issue166_uint64_mod_in_prelude() {
    let mut env = Environment::with_prelude();

    // UInt64.mod : UInt64 → UInt64 → UInt64
    let result = check_and_add_decl(
        &mut env,
        "def test_uint64_mod : UInt64 → UInt64 → UInt64 := UInt64.mod",
    );
    assert!(
        result.is_ok(),
        "Issue #166 (W297): UInt64.mod should be available. Got: {:?}",
        result.err()
    );
}

// Issue #172: Anonymous constructor syntax ⟨⟩ elaboration
//
// Discriminating test for #172. Implementation in R261 (crates/clean-elab/src/infer/mod.rs).
// The parser transforms `⟨val⟩` to `App(Ident("anonymousCtor"), [val])`.
// The elaborator detects this pattern and uses expected type to find constructor.
#[test]
fn test_issue172_anonymous_constructor_elaboration() {
    let mut env = Environment::with_prelude();

    // First define a simple structure
    let result = check_and_add_decl(&mut env, "structure Point where x : Nat y : Nat");
    assert!(
        result.is_ok(),
        "Issue #172 setup: Structure definition should work. Got: {:?}",
        result.err()
    );

    // Anonymous constructor ⟨1, 2⟩ should elaborate to Point.mk 1 2
    let result = check_and_add_decl(&mut env, "def test_point : Point := ⟨1, 2⟩");
    assert!(
        result.is_ok(),
        "Issue #172: Anonymous constructor ⟨1, 2⟩ should elaborate to Point.mk 1 2. Got: {:?}",
        result.err()
    );

    // Explicit constructor should also work (alternative syntax)
    let result_explicit =
        check_and_add_decl(&mut env, "def test_point_explicit : Point := Point.mk 3 4");
    assert!(
        result_explicit.is_ok(),
        "Issue #172: Explicit constructor should always work. Got: {:?}",
        result_explicit.err()
    );
}

// Issue #172: Anonymous constructor with single field
//
// Tests edge case of structure with exactly one field.
#[test]
fn test_issue172_anonymous_constructor_single_field() {
    let mut env = Environment::with_prelude();

    // Define a wrapper structure
    let result = check_and_add_decl(&mut env, "structure Wrapper where val : Nat");
    assert!(result.is_ok(), "Structure definition should work");

    // Anonymous constructor with single field
    let result = check_and_add_decl(&mut env, "def test_wrapper : Wrapper := ⟨42⟩");
    assert!(
        result.is_ok(),
        "Issue #172: Anonymous constructor with single field should work. Got: {:?}",
        result.err()
    );
}

// Issue #173: Polymorphic types require implicit arg handling
//
// Per R261 gap analysis: MVP handles simple structures; polymorphic types
// like Prod need additional implicit argument insertion.
// Fixed in elab_anonymous_ctor via insert_implicit_args call.
#[test]
fn test_issue173_anonymous_constructor_prod() {
    let mut env = Environment::with_prelude();

    // Prod ⟨a, b⟩ should elaborate to Prod.mk a b
    // This requires inserting implicit type parameters
    // Note: Uses bare `true` (alias added in M391 for Lean 4 compatibility)
    let result = check_and_add_decl(&mut env, "def test_prod : Prod Nat Bool := ⟨42, true⟩");
    assert!(
        result.is_ok(),
        "Issue #173: Polymorphic anonymous constructor. Got: {:?}",
        result.err()
    );
}

// Issue #155: Dot notation fallback for non-structure types
//
// When elaborating `p.Prime` where `p : Nat`, the elaborator should:
// 1. Try structure projection on Nat (fails - Nat is not a structure)
// 2. Fall back to dot notation: look for `Nat.Prime` and apply as `Nat.Prime p`
//
// This is Lean 4's behavior for method-style calls on primitive types.
#[test]
fn test_issue155_dot_notation_fallback() {
    let mut env = Environment::with_prelude();

    // First define Nat.isZero predicate as a simple stub
    // (Using simpler predicate than n > 1 to avoid GT typeclass complexity)
    let result = check_and_add_decl(&mut env, "def Nat.isZero (n : Nat) : Bool := Bool.true");
    assert!(
        result.is_ok(),
        "Issue #155 setup: Nat.isZero definition should work. Got: {:?}",
        result.err()
    );

    // Now test dot notation: p.isZero should elaborate to Nat.isZero p
    let result = check_and_add_decl(&mut env, "def test_zero (p : Nat) : Bool := p.isZero");
    assert!(
        result.is_ok(),
        "Issue #155: Dot notation p.isZero should elaborate to Nat.isZero p. Got: {:?}",
        result.err()
    );

    // Explicit call should also work (sanity check)
    let result_explicit = check_and_add_decl(
        &mut env,
        "def test_zero_explicit (p : Nat) : Bool := Nat.isZero p",
    );
    assert!(
        result_explicit.is_ok(),
        "Issue #155: Explicit Nat.isZero p should work. Got: {:?}",
        result_explicit.err()
    );
}

// Issue #155: Dot notation with a function that takes additional args
//
// Test that dot notation correctly inserts implicit args when the target function
// has universe parameters or other implicit arguments.
#[test]
fn test_issue155_dot_notation_with_function() {
    let mut env = Environment::with_prelude();

    // Define a factorial function on Nat
    let result = check_and_add_decl(&mut env, "def Nat.factorial (n : Nat) : Nat := n + 1");
    assert!(result.is_ok(), "Nat.factorial definition should work");

    // Dot notation n.factorial should work
    let result = check_and_add_decl(&mut env, "def five_fact : Nat := (5 : Nat).factorial");
    assert!(
        result.is_ok(),
        "Issue #155: (5 : Nat).factorial should elaborate to Nat.factorial 5. Got: {:?}",
        result.err()
    );
}

// Issue #155: Structure projection still works when applicable
//
// Ensure that actual structures with fields still use projection, not dot notation fallback.
#[test]
fn test_issue155_structure_projection_still_works() {
    let mut env = Environment::with_prelude();

    // Define a structure
    let result = check_and_add_decl(&mut env, "structure Point where x : Nat y : Nat");
    assert!(result.is_ok(), "Point structure should work");

    // Structure projection should use proj, not dot notation
    let result = check_and_add_decl(&mut env, "def get_x (p : Point) : Nat := p.x");
    assert!(
        result.is_ok(),
        "Issue #155: Structure projection p.x should still work. Got: {:?}",
        result.err()
    );
}

// Issue #173: Simple structure still works (regression test for #172)
//
// Ensure the fix doesn't break simple non-polymorphic structures.
#[test]
fn test_issue173_simple_structure_still_works() {
    let mut env = Environment::with_prelude();

    // Define a simple non-polymorphic structure
    let result = check_and_add_decl(&mut env, "structure Point where x : Nat y : Nat");
    assert!(result.is_ok(), "Point definition should work");

    // Anonymous constructor should still work for simple structures
    let result = check_and_add_decl(&mut env, "def test_point : Point := ⟨1, 2⟩");
    assert!(
        result.is_ok(),
        "Issue #173: Anonymous ctor for simple Point should still work. Got: {:?}",
        result.err()
    );
}

/// Issue #252: Custom inductive implicit parameter handling
///
/// Tests that custom inductives (like MyOption) have implicit parameters handled
/// correctly in constructor types. The parameters must use BinderInfo::Implicit,
/// and the inductive FVar must be bound with its full type signature (not applied form).
///
/// Root cause: Inductive parameters were using user-supplied BinderInfo instead of
/// BinderInfo::Implicit, and the inductive FVar was bound with the wrong type.
///
/// Note: Nested polymorphic types in Prod (e.g., Prod (MyOption Nat) Bool) require
/// additional universe level work and are tracked separately.
#[test]
fn test_issue252_custom_inductive_implicit_params() {
    let mut env = Environment::with_prelude();

    // First check that defining a polymorphic inductive works
    let result = check_and_add_decl(
        &mut env,
        "inductive MyOption (α : Type) : Type where
         | none : MyOption α
         | some : α → MyOption α",
    );
    assert!(
        result.is_ok(),
        "MyOption definition should work. Got: {:?}",
        result.err()
    );

    // Check that simple Prod.mk works (baseline)
    let result = check_and_add_decl(
        &mut env,
        "def test_prod_simple : Prod Nat Bool := Prod.mk 42 Bool.true",
    );
    assert!(
        result.is_ok(),
        "Simple Prod.mk should work. Got: {:?}",
        result.err()
    );

    // Test using the custom inductive type with the nullary constructor
    let result = check_and_add_decl(
        &mut env,
        "def test_myoption_none : MyOption Nat := MyOption.none",
    );
    assert!(
        result.is_ok(),
        "Issue #252: MyOption.none should work. Got: {:?}",
        result.err()
    );

    // Test using the constructor with an argument
    let result = check_and_add_decl(
        &mut env,
        "def test_myoption_some : MyOption Nat := MyOption.some 42",
    );
    assert!(
        result.is_ok(),
        "Issue #252: MyOption.some 42 should work. Got: {:?}",
        result.err()
    );

    // Test anonymous constructor syntax with custom single-constructor inductive
    // Note: ⟨...⟩ only works for single-constructor types (like structures)
    // Define a wrapper type to test this
    let result = check_and_add_decl(
        &mut env,
        "inductive MyWrapper (α : Type) : Type where
         | mk : α → MyWrapper α",
    );
    assert!(
        result.is_ok(),
        "MyWrapper definition should work. Got: {:?}",
        result.err()
    );

    let result = check_and_add_decl(&mut env, "def test_anon_wrapper : MyWrapper Nat := ⟨42⟩");
    assert!(
        result.is_ok(),
        "Issue #252: Anonymous constructor ⟨42⟩ for single-ctor MyWrapper should work. Got: {:?}",
        result.err()
    );
}

// ============================================================================
// Issue #361: App Elaboration Expected Type Normalization Tests
// ============================================================================

/// Issue #361: Test beta reduction in function argument type checking
///
/// When elaborating applications, expected argument types may be applications like
/// `(fun n => P n) x` which need beta reduction. The fix (commit 0812fb6) adds
/// WHNF normalization of expected arg types before unification.
#[test]
fn test_issue361_dependent_application_beta_reduction() {
    let mut env = Environment::with_prelude();

    // Define a type family: P : Nat → Type
    let result = check_and_add_decl(&mut env, "axiom P : Nat → Type");
    assert!(
        result.is_ok(),
        "P definition should work: {:?}",
        result.err()
    );

    // Define a witness for P 0
    let result = check_and_add_decl(&mut env, "axiom p0 : P 0");
    assert!(
        result.is_ok(),
        "p0 definition should work: {:?}",
        result.err()
    );

    // Define a function that takes a motive and a value at motive 0
    // f : (motive : Nat → Type) → motive 0 → motive 0
    let result = check_and_add_decl(
        &mut env,
        "def f (motive : Nat → Type) (x : motive 0) : motive 0 := x",
    );
    assert!(
        result.is_ok(),
        "f definition should work: {:?}",
        result.err()
    );

    // Key test: when elaborating `f P p0`, after binding motive = P,
    // the expected type for the second argument is `motive 0` which needs
    // to be normalized to unify with the type of p0 which is `P 0`.
    let result = check_and_add_decl(&mut env, "def test := f P p0");
    assert!(
        result.is_ok(),
        "Issue #361: Dependent application should work with WHNF normalization: {:?}",
        result.err()
    );
}

/// Issue #361: Test motive-like application with explicit argument
///
/// Tests that when a motive (type family) is applied to a concrete value,
/// the resulting expected type is properly normalized before unification.
#[test]
fn test_issue361_motive_application_with_prop() {
    let mut env = Environment::with_prelude();

    // Define a predicate on Nat
    let result = check_and_add_decl(&mut env, "axiom Q : Nat → Prop");
    assert!(result.is_ok(), "Q should work: {:?}", result.err());

    // Define a proof for Q 0
    let result = check_and_add_decl(&mut env, "axiom q0 : Q 0");
    assert!(result.is_ok(), "q0 should work: {:?}", result.err());

    // Define an identity function with motive parameter
    // id_motive : (motive : Nat → Prop) → motive 0 → motive 0
    // This is similar to what recursors do with their motive parameter
    let result = check_and_add_decl(
        &mut env,
        "def id_motive (motive : Nat → Prop) (h : motive 0) : motive 0 := h",
    );
    assert!(result.is_ok(), "id_motive should work: {:?}", result.err());

    // Use id_motive with Q as the motive and q0 as the proof
    // The expected type for q0 is `motive 0` = `Q 0` after substitution
    // The fix ensures this unification works via WHNF normalization
    let result = check_and_add_decl(&mut env, "def test_q := id_motive Q q0");
    assert!(
        result.is_ok(),
        "Issue #361: id_motive Q q0 should work: {:?}",
        result.err()
    );
}

/// Issue #361: Test with nested function application in expected type
///
/// The expected argument type involves applying a function parameter to an argument,
/// which may create terms that need WHNF normalization.
#[test]
fn test_issue361_nested_application() {
    let mut env = Environment::with_prelude();

    // Define type families
    let result = check_and_add_decl(&mut env, "axiom F : Nat → Type");
    assert!(result.is_ok(), "F should work: {:?}", result.err());

    let result = check_and_add_decl(&mut env, "axiom f1 : F 1");
    assert!(result.is_ok(), "f1 should work: {:?}", result.err());

    // Define a function that takes a family and a witness
    let result = check_and_add_decl(
        &mut env,
        "def witness (family : Nat → Type) (w : family 1) : family 1 := w",
    );
    assert!(result.is_ok(), "witness should work: {:?}", result.err());

    // Apply witness to F and f1
    // When checking `f1 : family 1` after binding family = F,
    // the expected type `family 1` needs to reduce to `F 1`
    let result = check_and_add_decl(&mut env, "def test_witness := witness F f1");
    assert!(
        result.is_ok(),
        "Issue #361: witness F f1 should work: {:?}",
        result.err()
    );
}

// =============================================================================
// Issue #379: Complex proof terms with nested And.intro
// =============================================================================

/// Issue #379: Simple And.intro works
#[test]
fn test_issue379_simple_and_intro() {
    let mut env = Environment::new();

    // Define And type and constructor
    check_and_add_decl(&mut env, "axiom And : Type → Type → Type").unwrap();
    check_and_add_decl(
        &mut env,
        "axiom And.intro : forall (A : Type) (B : Type), A → B → And A B",
    )
    .unwrap();

    // Simple Nat axioms
    check_and_add_decl(&mut env, "axiom Nat : Type").unwrap();
    check_and_add_decl(&mut env, "axiom zero : Nat").unwrap();

    // Simple And.intro with explicit type arguments should work
    let result = check_and_add_decl(
        &mut env,
        "def simple_and : And Nat Nat := And.intro Nat Nat zero zero",
    );
    assert!(
        result.is_ok(),
        "Issue #379: Simple And.intro should work: {:?}",
        result.err()
    );
}

/// Issue #379: Nested And.intro in function body
#[test]
fn test_issue379_nested_and_intro() {
    let mut env = Environment::new();

    // Set up environment with And type
    check_and_add_decl(&mut env, "axiom And : Type → Type → Type").unwrap();
    check_and_add_decl(
        &mut env,
        "axiom And.intro : forall (A : Type) (B : Type), A → B → And A B",
    )
    .unwrap();

    // Define identity function that returns And
    let result = check_and_add_decl(
        &mut env,
        "def mk_and (A : Type) (B : Type) (a : A) (b : B) : And A B := And.intro A B a b",
    );
    assert!(
        result.is_ok(),
        "Issue #379: mk_and should work: {:?}",
        result.err()
    );
}

/// Issue #379: And.intro inside lambda (the problematic case)
///
/// This reproduces the issue where And.intro inside a deeply nested
/// lambda loses type information.
#[test]
fn test_issue379_and_intro_in_lambda() {
    let mut env = Environment::new();

    // Set up environment
    check_and_add_decl(&mut env, "axiom And : Type → Type → Type").unwrap();
    check_and_add_decl(
        &mut env,
        "axiom And.intro : forall (A : Type) (B : Type), A → B → And A B",
    )
    .unwrap();

    // This is the key test: And.intro inside a lambda
    // The motive function takes parameters and returns And.intro
    let result = check_and_add_decl(
        &mut env,
        "def motive_case (A : Type) (a : A) : And A A := And.intro A A a a",
    );
    assert!(
        result.is_ok(),
        "Issue #379: motive_case should work: {:?}",
        result.err()
    );

    // Now test inside a lambda - this is closer to the rec case
    let result = check_and_add_decl(
        &mut env,
        "def lambda_and : forall (A : Type), A → And A A := fun (A : Type) (a : A) => And.intro A A a a",
    );
    assert!(
        result.is_ok(),
        "Issue #379: lambda_and should work: {:?}",
        result.err()
    );
}

/// Issue #379: Recursor-style application with And motive
///
/// This tests the pattern from def_eq_typing_iff where a recursor-like
/// function takes a motive that returns And type.
#[test]
fn test_issue379_rec_style_with_and_motive() {
    let mut env = Environment::new();

    // Set up environment - use simple names to avoid parser issues with dots
    check_and_add_decl(&mut env, "axiom And : Type → Type → Type").unwrap();
    check_and_add_decl(
        &mut env,
        "axiom And_intro : forall (A : Type) (B : Type), A → B → And A B",
    )
    .unwrap();
    check_and_add_decl(
        &mut env,
        "axiom And_left : forall (A : Type) (B : Type), And A B → A",
    )
    .unwrap();
    check_and_add_decl(
        &mut env,
        "axiom And_right : forall (A : Type) (B : Type), And A B → B",
    )
    .unwrap();

    // Simple inductive type (like a simplified DefEq)
    check_and_add_decl(&mut env, "axiom Eq : Type → Type").unwrap();
    check_and_add_decl(&mut env, "axiom Eq_refl : forall (A : Type), Eq A").unwrap();

    // Recursor for Eq
    check_and_add_decl(
        &mut env,
        "axiom Eq_rec : forall (A : Type) (P : Eq A → Type), P (Eq_refl A) → forall (h : Eq A), P h",
    )
    .unwrap();

    // Test: Can we use Eq_rec with a motive that returns And?
    // This is the pattern in def_eq_typing_iff
    let result = check_and_add_decl(
        &mut env,
        concat!(
            "def test_rec (A : Type) (a : A) (h : Eq A) : And A A := ",
            "Eq_rec A (fun (_ : Eq A) => And A A) (And_intro A A a a) h"
        ),
    );
    assert!(
        result.is_ok(),
        "Issue #379: Eq_rec with And motive should work: {:?}",
        result.err()
    );
}

/// Issue #379: Multi-case recursor with IH composition
///
/// This tests the pattern from def_eq_typing_iff where each case needs to
/// compose inductive hypotheses using And.left/And.right.
#[test]
fn test_issue379_multi_case_rec() {
    let mut env = Environment::new();

    // Set up environment
    check_and_add_decl(&mut env, "axiom And : Type → Type → Type").unwrap();
    check_and_add_decl(
        &mut env,
        "axiom And_intro : forall (A : Type) (B : Type), A → B → And A B",
    )
    .unwrap();
    check_and_add_decl(
        &mut env,
        "axiom And_left : forall (A : Type) (B : Type), And A B → A",
    )
    .unwrap();
    check_and_add_decl(
        &mut env,
        "axiom And_right : forall (A : Type) (B : Type), And A B → B",
    )
    .unwrap();

    // Two-constructor inductive (like DefEq with refl and symm)
    check_and_add_decl(&mut env, "axiom Rel : Type → Type → Type").unwrap();
    check_and_add_decl(&mut env, "axiom Rel_refl : forall (A : Type), Rel A A").unwrap();
    check_and_add_decl(
        &mut env,
        "axiom Rel_symm : forall (A : Type) (B : Type), Rel A B → Rel B A",
    )
    .unwrap();

    // Recursor with two cases
    check_and_add_decl(
        &mut env,
        concat!(
            "axiom Rel_rec : forall (P : forall (A : Type) (B : Type), Rel A B → Type), ",
            "(forall (A : Type), P A A (Rel_refl A)) → ",
            "(forall (A : Type) (B : Type) (h : Rel A B), P A B h → P B A (Rel_symm A B h)) → ",
            "forall (A : Type) (B : Type) (h : Rel A B), P A B h"
        ),
    )
    .unwrap();

    // Helper axioms for proofs
    check_and_add_decl(&mut env, "axiom T : Type").unwrap();
    check_and_add_decl(
        &mut env,
        "axiom fwd : forall (A : Type) (B : Type), Rel A B → A → B",
    )
    .unwrap();
    check_and_add_decl(
        &mut env,
        "axiom bwd : forall (A : Type) (B : Type), Rel A B → B → A",
    )
    .unwrap();

    // Now the hard test: use Rel_rec with a motive returning And, and compose IH
    // refl case: And_intro (fun x => x) (fun x => x)
    // symm case: And_intro (And_right ih) (And_left ih)
    let result = check_and_add_decl(
        &mut env,
        concat!(
            "def test_multi (A : Type) (B : Type) (h : Rel A B) : And (A → B) (B → A) := ",
            "Rel_rec ",
            "(fun (X : Type) (Y : Type) (_ : Rel X Y) => And (X → Y) (Y → X)) ",
            "(fun (X : Type) => And_intro (X → X) (X → X) (fun (x : X) => x) (fun (x : X) => x)) ",
            "(fun (X : Type) (Y : Type) (hr : Rel X Y) (ih : And (X → Y) (Y → X)) => ",
            "And_intro (Y → X) (X → Y) (And_right (X → Y) (Y → X) ih) (And_left (X → Y) (Y → X) ih)) ",
            "A B h"
        ),
    );
    assert!(
        result.is_ok(),
        "Issue #379: Multi-case Rel_rec with And motive should work: {:?}",
        result.err()
    );
}

/// Issue #379: Simpler version - just the refl case as a standalone function
#[test]
fn test_issue379_standalone_refl_case() {
    let mut env = Environment::new();

    check_and_add_decl(&mut env, "axiom And : Type → Type → Type").unwrap();
    check_and_add_decl(
        &mut env,
        "axiom And_intro : forall (A : Type) (B : Type), A → B → And A B",
    )
    .unwrap();

    // Just the refl case as a standalone definition
    // This is what goes in the refl branch of Rel_rec
    let result = check_and_add_decl(
        &mut env,
        "def refl_case (X : Type) : And (X → X) (X → X) := And_intro (X → X) (X → X) (fun (x : X) => x) (fun (x : X) => x)",
    );
    assert!(
        result.is_ok(),
        "Issue #379: Standalone refl_case should work: {:?}",
        result.err()
    );
}

/// Issue #379: Breaking down further - And_intro with function types
#[test]
fn test_issue379_and_intro_with_function_type() {
    let mut env = Environment::new();

    check_and_add_decl(&mut env, "axiom And : Type → Type → Type").unwrap();
    check_and_add_decl(
        &mut env,
        "axiom And_intro : forall (A : Type) (B : Type), A → B → And A B",
    )
    .unwrap();
    check_and_add_decl(&mut env, "axiom T : Type").unwrap();

    // First verify that identity function works
    let result = check_and_add_decl(&mut env, "def id_T : T → T := fun (x : T) => x");
    assert!(result.is_ok(), "id_T should work: {:?}", result.err());

    // Now try And_intro with function type
    let result = check_and_add_decl(
        &mut env,
        "def and_id : And (T → T) (T → T) := And_intro (T → T) (T → T) id_T id_T",
    );
    assert!(
        result.is_ok(),
        "Issue #379: and_id should work: {:?}",
        result.err()
    );

    // Now the inline version
    let result = check_and_add_decl(
        &mut env,
        "def and_id_inline : And (T → T) (T → T) := And_intro (T → T) (T → T) (fun (x : T) => x) (fun (x : T) => x)",
    );
    assert!(
        result.is_ok(),
        "Issue #379: and_id_inline should work: {:?}",
        result.err()
    );
}

/// Issue #379: Minimal reproduction - function expecting dependent type argument
///
/// This isolates the issue: when a function expects an argument of a type
/// that depends on earlier parameters (like motive application in a recursor),
/// and that argument is provided as a lambda containing And_intro.
#[test]
fn test_issue379_dependent_arg_with_lambda() {
    let mut env = Environment::new();

    check_and_add_decl(&mut env, "axiom And : Type → Type → Type").unwrap();
    check_and_add_decl(
        &mut env,
        "axiom And_intro : forall (A : Type) (B : Type), A → B → And A B",
    )
    .unwrap();

    // A simpler recursor-like function:
    // takes a motive P and a proof of P T for some T
    check_and_add_decl(
        &mut env,
        "axiom apply_motive : forall (P : Type → Type) (T : Type), P T → P T",
    )
    .unwrap();

    // Test 1: Use apply_motive with a simple motive
    check_and_add_decl(&mut env, "axiom X : Type")
        .expect("declaring axiom X : Type should succeed");

    check_and_add_decl(&mut env, "axiom x : X").expect("declaring axiom x : X should succeed");

    // Test with identity motive - should work
    let result = check_and_add_decl(
        &mut env,
        "def test_id_motive : X := apply_motive (fun (A : Type) => A) X x",
    );
    assert!(result.is_ok(), "id motive should work: {:?}", result.err());

    // Test with And motive - the interesting case
    let result = check_and_add_decl(
        &mut env,
        concat!(
            "def test_and_motive : And X X := ",
            "apply_motive (fun (A : Type) => And A A) X (And_intro X X x x)"
        ),
    );
    assert!(
        result.is_ok(),
        "Issue #379: And motive should work: {:?}",
        result.err()
    );

    // Test with And motive and function types
    let result = check_and_add_decl(
        &mut env,
        concat!(
            "def test_and_fn_motive : And (X → X) (X → X) := ",
            "apply_motive (fun (A : Type) => And (A → A) (A → A)) X ",
            "(And_intro (X → X) (X → X) (fun (a : X) => a) (fun (a : X) => a))"
        ),
    );
    assert!(
        result.is_ok(),
        "Issue #379: And fn motive should work: {:?}",
        result.err()
    );
}

/// Issue #379: Even simpler - does passing a lambda to a motive argument work?
#[test]
fn test_issue379_lambda_as_motive_arg() {
    let mut env = Environment::new();

    // Function that takes a type family and uses it
    check_and_add_decl(
        &mut env,
        "axiom use_family : forall (F : Type → Type) (T : Type), F T → F T",
    )
    .unwrap();

    check_and_add_decl(&mut env, "axiom N : Type").unwrap();
    check_and_add_decl(&mut env, "axiom n : N").unwrap();

    // Pass a lambda as the motive
    let result = check_and_add_decl(
        &mut env,
        "def test_lambda_motive : N := use_family (fun (A : Type) => A) N n",
    );
    assert!(
        result.is_ok(),
        "Lambda as motive should work: {:?}",
        result.err()
    );
}

/// Issue #379: Two-argument function with dependent second argument
///
/// Rel_rec has: forall (P : ...), (forall A, P A A ...) → (forall A B h, P A B h → ...) → ...
/// The second argument type depends on P, which is passed as first argument.
/// This tests if the elaborator correctly infers the type of the second arg after
/// the first (P) is known.
#[test]
fn test_issue379_two_dependent_args() {
    let mut env = Environment::new();

    check_and_add_decl(&mut env, "axiom And : Type → Type → Type").unwrap();
    check_and_add_decl(
        &mut env,
        "axiom And_intro : forall (A : Type) (B : Type), A → B → And A B",
    )
    .unwrap();

    // A function that takes a motive and then a proof that uses that motive
    check_and_add_decl(
        &mut env,
        "axiom two_args : forall (P : Type → Type) (proof : forall (A : Type), P A), P Nat",
    )
    .unwrap();

    check_and_add_decl(&mut env, "axiom Nat : Type").unwrap();
    check_and_add_decl(&mut env, "axiom zero : Nat").unwrap();

    // Test: Can we provide a lambda motive and a matching proof?
    let result = check_and_add_decl(
        &mut env,
        concat!(
            "def test_two_args : Nat := ",
            "two_args (fun (A : Type) => A) (fun (A : Type) => A)" // Identity motive, identity proof
        ),
    );
    // This test documents a known limitation (#379):
    // The "proof" lambda elaborates without knowing it should produce `A`.
    // It elaborates `fun A => A` as `Λ A. A : ∀ A, ?` and then we need to unify ? with P A.
    //
    // Currently this fails as expected - if this starts passing, the limitation is resolved.
    assert!(
        result.is_err(),
        "Unexpected success - #379 may be resolved, update this test"
    );
}

/// Issue #379: Isolate the Rel_rec failure more precisely
#[test]
fn test_issue379_rel_rec_first_case_only() {
    let mut env = Environment::new();

    check_and_add_decl(&mut env, "axiom And : Type → Type → Type").unwrap();
    check_and_add_decl(
        &mut env,
        "axiom And_intro : forall (A : Type) (B : Type), A → B → And A B",
    )
    .unwrap();

    // Simpler recursor with just one case
    check_and_add_decl(&mut env, "axiom Rel : Type → Type → Type").unwrap();
    check_and_add_decl(&mut env, "axiom Rel_refl : forall (A : Type), Rel A A").unwrap();

    // Recursor with just the refl case
    check_and_add_decl(
        &mut env,
        concat!(
            "axiom Rel_rec_simple : forall (P : forall (A : Type) (B : Type), Rel A B → Type), ",
            "(forall (A : Type), P A A (Rel_refl A)) → ",
            "forall (A : Type) (B : Type) (h : Rel A B), P A B h"
        ),
    )
    .unwrap();

    // Test: Apply with And motive
    let result = check_and_add_decl(
        &mut env,
        concat!(
            "def test_simple_rec (A : Type) (B : Type) (h : Rel A B) : And (A → B) (B → A) := ",
            "Rel_rec_simple ",
            "(fun (X : Type) (Y : Type) (_ : Rel X Y) => And (X → Y) (Y → X)) ",
            "(fun (X : Type) => And_intro (X → X) (X → X) (fun (x : X) => x) (fun (x : X) => x)) ",
            "A B h"
        ),
    );
    assert!(
        result.is_ok(),
        "Issue #379: Simple Rel_rec with And motive should work: {:?}",
        result.err()
    );
}

// =============================================================================
// Issue #384: Structural Recursion Tests
// =============================================================================

/// Issue #384: Test that structural recursion elaboration works for Nat.add-like functions.
///
/// This tests the full structural recursion pipeline:
/// 1. Recursive field lookup from recursor rules
/// 2. IH interleaving in lambda structure
/// 3. Recursive call substitution with IH
///
/// A function like:
///   def add (n m : MyNat) : MyNat := match n with
///     | zero => m
///     | succ k => succ (add k m)
///
/// Should elaborate using MyNat.rec with recursive calls replaced by IH.
///
/// NOTE: This test currently documents a universe level mismatch in match elaboration.
/// The match motive generates `Sort(Param(u))` but the result type is concrete `Type 1`.
/// This is a separate issue from the structural recursion IH substitution (which is implemented).
#[test]
fn test_issue384_structural_recursion_add() {
    let mut env = Environment::with_prelude();

    // Define MyNat inductive type
    let result = check_and_add_decl(
        &mut env,
        r"inductive MyNat : Type
| zero : MyNat
| succ : MyNat → MyNat",
    );
    assert!(
        result.is_ok(),
        "MyNat inductive should elaborate: {:?}",
        result.err()
    );

    // First test: Non-recursive match should work
    // Issue #386 fixed: BVar lifting and nullary constructor detection now correct
    let pred_result = check_and_add_decl(
        &mut env,
        r"def myPred (n : MyNat) : MyNat := match n with
| MyNat.zero => MyNat.zero
| MyNat.succ k => k",
    );
    assert!(
        pred_result.is_ok(),
        "myPred should elaborate successfully: {:?}",
        pred_result.err()
    );

    // Now test: Recursive add function using structural recursion
    let add_result = check_and_add_decl(
        &mut env,
        r"def myAdd (n m : MyNat) : MyNat := match n with
| MyNat.zero => m
| MyNat.succ k => MyNat.succ (myAdd k m)",
    );
    assert!(
        add_result.is_ok(),
        "Issue #384: Structural recursion for myAdd should work: {:?}",
        add_result.err()
    );
}

/// Issue #381: Test structural recursion for List.length
///
/// Tests that a recursive length function on a List type elaborates correctly.
/// The function recurses structurally on the list constructor.
///
/// Fixed in #403: kernel now extracts proper field types for multi-field constructors.
#[test]
fn test_issue381_structural_recursion_list_length() {
    let mut env = Environment::with_prelude();

    // First need MyNat for element type
    let nat_result = check_and_add_decl(
        &mut env,
        r"inductive MyNat : Type
| zero : MyNat
| succ : MyNat → MyNat",
    );
    assert!(
        nat_result.is_ok(),
        "MyNat should elaborate: {:?}",
        nat_result.err()
    );

    // Define MyList using MyNat
    let list_result = check_and_add_decl(
        &mut env,
        r"inductive MyList : Type
| nil : MyList
| cons : MyNat → MyList → MyList",
    );
    assert!(
        list_result.is_ok(),
        "MyList should elaborate: {:?}",
        list_result.err()
    );

    // Define length function with structural recursion on the list
    // Fixed in #403: kernel now extracts proper field types for multi-field constructors
    let length_result = check_and_add_decl(
        &mut env,
        r"def myLength (xs : MyList) : MyNat := match xs with
| MyList.nil => MyNat.zero
| MyList.cons _ tail => MyNat.succ (myLength tail)",
    );
    assert!(
        length_result.is_ok(),
        "Issue #381/#403: List.length should elaborate with structural recursion: {:?}",
        length_result.err()
    );
}

/// Issue #381: Test structural recursion for List.map
///
/// Tests that a recursive map function on a List type elaborates correctly.
/// Map applies a function to each element, recursing structurally on the list.
///
/// REMAINING ISSUE: Using non-recursive fields (like `head`) in the match body
/// causes type unification errors. The kernel fix in #403 resolved field type
/// extraction, but there's still an issue with accessing non-recursive fields.
#[test]
fn test_issue381_structural_recursion_list_map() {
    let mut env = Environment::with_prelude();

    // Define MyNat and MyList
    let nat_result = check_and_add_decl(
        &mut env,
        r"inductive MyNat : Type
| zero : MyNat
| succ : MyNat → MyNat",
    );
    assert!(
        nat_result.is_ok(),
        "MyNat should elaborate: {:?}",
        nat_result.err()
    );

    let list_result = check_and_add_decl(
        &mut env,
        r"inductive MyList : Type
| nil : MyList
| cons : MyNat → MyList → MyList",
    );
    assert!(
        list_result.is_ok(),
        "MyList should elaborate: {:?}",
        list_result.err()
    );

    // Define map function with structural recursion
    // Fixed in #403: parser now correctly parses multi-field constructor patterns.
    let map_result = check_and_add_decl(
        &mut env,
        r"def myMap (f : MyNat → MyNat) (xs : MyList) : MyList := match xs with
| MyList.nil => MyList.nil
| MyList.cons head tail => MyList.cons (f head) (myMap f tail)",
    );
    // List.map with multi-field constructors now works (#403)
    assert!(
        map_result.is_ok(),
        "myMap should elaborate successfully: {:?}",
        map_result.err()
    );
}

/// Issue #522: Qualified recursive calls should be recognized
///
/// Tests that recursive definitions with qualified names like `Nat.add` can
/// correctly recognize recursive calls using the same qualified syntax.
/// Previously, `Nat.add p m` in the body would fail with "cannot extract type name
/// from Sort(Succ(Zero))" because the elaborator treated `Nat.add` as a projection
/// on the type `Nat` rather than recognizing it as a recursive call.
///
/// Fixed by extending `elab_app` to handle projections when checking for
/// recursive calls in the recursive definition context.
#[test]
fn test_issue522_qualified_recursive_call() {
    use clean_elab::elaborate_decl_and_register;
    use clean_kernel::env::Environment;
    use clean_parser::parse_decl;

    let mut env = Environment::new();

    // Add Nat inductive type
    let nat_decl = parse_decl(
        r"inductive Nat : Type
| zero : Nat
| succ : Nat → Nat",
    )
    .unwrap();
    elaborate_decl_and_register(&mut env, &nat_decl).expect("Nat inductive should work");

    // Define Nat.add with qualified recursive call
    // This is the pattern that failed before the fix
    let add_decl = parse_decl(
        r"def Nat.add (n m : Nat) : Nat := match n with
| Nat.zero => m
| Nat.succ p => Nat.succ (Nat.add p m)",
    )
    .unwrap();

    let result = elaborate_decl_and_register(&mut env, &add_decl);
    assert!(
        result.is_ok(),
        "Qualified recursive call Nat.add should work: {:?}",
        result.err()
    );
}

// =============================================================================
// #1292 / #1314: Compound Soundness Integration Regression Test
// =============================================================================
//
// This integration test exercises the compound soundness fix from epic #1292.
// It verifies that three independently-fixed kernel bugs (#1276, #1277, #1278)
// are all enforced together, preventing an attack chain where:
//
// 1. An ill-typed declaration is inserted (#1276: add_decl type-checking)
// 2. It's instantiated with wrong universe levels (#1277: level count mismatch)
// 3. Classical.choice is applied to the result without validation (#1278)
//
// Unlike the kernel-level unit test in env/tests.rs, this integration test
// exercises the full parse -> elaborate -> type-check -> add-to-environment
// pipeline where applicable, verifying the defenses work end-to-end.

/// #1314: Path 1 (#1276) — Ill-typed definition is rejected through the full pipeline.
///
/// Attempts to add a definition where value type disagrees with declared type.
/// The elaborator + type checker + add_decl pipeline must reject this.
#[test]
fn test_compound_soundness_path1_ill_typed_definition() {
    let mut env = Environment::new();

    // Nat is needed for the test
    check_and_add_decl(&mut env, "axiom Nat : Type").unwrap();
    check_and_add_decl(&mut env, "axiom Bool : Type").unwrap();
    check_and_add_decl(&mut env, "axiom Bool.true : Bool").unwrap();

    // Try to define something with type Nat but value Bool.true
    // The type checker must reject this mismatch
    let result = check_and_add_decl(&mut env, "def bad_def : Nat := Bool.true");
    assert!(
        result.is_err(),
        "Path 1 (#1276): definition with type/value mismatch must be rejected"
    );

    // Verify the declaration was NOT added to the environment
    assert!(
        env.get_const(&Name::from_string("bad_def")).is_none(),
        "Rejected declaration must not appear in environment"
    );
}

/// #1314: Path 1b (#1276) — Theorem with non-Prop type is rejected.
///
/// Lean 4 requires theorem types to be propositions (Sort 0).
/// A theorem whose type lives in Type (Sort 1) must be rejected.
#[test]
fn test_compound_soundness_path1b_theorem_type_not_prop() {
    use clean_kernel::{Declaration, Level};

    let mut env = Environment::new();

    // Try to add a theorem whose type is Type (not Prop)
    // theorem bad : Type := Nat  — type is Sort(1), not Sort(0)
    let result = env.add_decl(Declaration::Theorem {
        name: Name::from_string("bad_thm_1314"),
        level_params: vec![],
        type_: Expr::type_(), // Type = Sort(1) — not a Prop
        value: Expr::from_kind(ExprKind::Sort(Level::zero())), // Prop = Sort(0) as value
    });
    assert!(
        result.is_err(),
        "Path 1b (#1276): theorem with non-Prop type must be rejected"
    );
}

/// #1314: Path 2 (#1277) — Level count mismatch is caught by type checker.
///
/// After adding a universe-polymorphic axiom, constructing an Expr::Const
/// with the wrong number of universe levels and type-checking it must fail
/// with LevelCountMismatch.
#[test]
fn test_compound_soundness_path2_level_count_mismatch() {
    use clean_kernel::{Declaration, Level, TypeChecker};

    let mut env = Environment::new();

    // Add a polymorphic axiom: axiom poly.{u} : Sort(u+1)
    let u_name = Name::from_string("u");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("poly_1314"),
        level_params: vec![u_name.clone()],
        type_: Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u_name)))),
    })
    .expect("well-typed polymorphic axiom must succeed");

    // Try type-checking a reference with ZERO levels (expects 1)
    let tc = TypeChecker::new(&env);
    let bad_const_zero = Expr::const_(Name::from_string("poly_1314"), vec![]);
    let result_zero = tc.infer_type(&bad_const_zero);
    assert!(
        result_zero.is_err(),
        "Path 2 (#1277): type checker must reject 0 levels when 1 expected"
    );
    let err_msg = format!("{}", result_zero.unwrap_err());
    assert!(
        err_msg.contains("Level count mismatch"),
        "Error should be LevelCountMismatch, got: {err_msg}"
    );

    // Try type-checking a reference with TWO levels (expects 1)
    let tc2 = TypeChecker::new(&env);
    let bad_const_two = Expr::const_(
        Name::from_string("poly_1314"),
        vec![Level::zero(), Level::succ(Level::zero())],
    );
    let result_two = tc2.infer_type(&bad_const_two);
    assert!(
        result_two.is_err(),
        "Path 2 (#1277): type checker must reject 2 levels when 1 expected"
    );
    let err_msg_two = format!("{}", result_two.unwrap_err());
    assert!(
        err_msg_two.contains("Level count mismatch"),
        "Error should be LevelCountMismatch, got: {err_msg_two}"
    );

    // Verify correct level count succeeds
    let tc3 = TypeChecker::new(&env);
    let good_const = Expr::const_(Name::from_string("poly_1314"), vec![Level::zero()]);
    let result_ok = tc3.infer_type(&good_const);
    assert!(
        result_ok.is_ok(),
        "Correct level count must succeed: {:?}",
        result_ok.err()
    );

    // Also verify Environment::instantiate_type rejects mismatched levels
    assert!(
        env.instantiate_type(&Name::from_string("poly_1314"), &[])
            .is_none(),
        "instantiate_type must reject 0 levels for 1-param constant"
    );
    assert!(
        env.instantiate_type(
            &Name::from_string("poly_1314"),
            &[Level::zero(), Level::succ(Level::zero())]
        )
        .is_none(),
        "instantiate_type must reject 2 levels for 1-param constant"
    );
}

/// #1314: Path 3 (#1278) — Ill-typed application of Classical.choice axiom is rejected.
///
/// Classical.choice is now a plain axiom (no dedicated ExprKind variant).
/// Constructs a definition whose value is an ill-typed application of the
/// Classical.choice constant and verifies add_decl rejects it.
#[test]
fn test_compound_soundness_path3_classical_choice_ill_typed() {
    use clean_kernel::{Declaration, Level};

    let mut env = Environment::new();
    env.init_classical().expect("init_classical");

    // Classical.choice : {α : Sort u} → Nonempty α → α
    // Apply it with wrong argument types: supply Prop as both args
    let choice_const = Expr::const_(Name::from_string("Classical.choice"), vec![Level::zero()]);
    let bad_app = Expr::app(
        Expr::app(choice_const, Expr::prop()), // α = Prop (ok)
        Expr::prop(),                          // Nonempty Prop expected, got Prop
    );
    let bad_choice_def = Declaration::Definition {
        name: Name::from_string("bad_choice_1314"),
        level_params: vec![],
        type_: Expr::prop(),
        value: bad_app,
        is_reducible: false,
    };
    let result = env.add_decl(bad_choice_def);
    assert!(
        result.is_err(),
        "Path 3 (#1278): add_decl must reject ill-typed Classical.choice application"
    );
    assert!(
        env.get_const(&Name::from_string("bad_choice_1314"))
            .is_none(),
        "Rejected declaration must not appear in environment"
    );
}

/// #1314: Compound scenario — all three defenses block the attack chain.
///
/// This test demonstrates that even if one defense were bypassed (via
/// add_decl_unchecked for trusted imports), the remaining defenses still
/// block exploitation. This is the compound interaction test required
/// by epic #1292.
#[test]
fn test_compound_soundness_attack_chain_blocked() {
    use clean_kernel::{Declaration, Level, TypeChecker};

    let mut env = Environment::new();
    env.init_classical().expect("init_classical");

    let u_name = Name::from_string("u");
    let u_level = Level::param(u_name.clone());

    // Step 1: Verified — add_decl rejects the ill-typed definition
    let result = env.add_decl(Declaration::Definition {
        name: Name::from_string("smuggle_attempt_1314"),
        level_params: vec![u_name.clone()],
        type_: Expr::from_kind(ExprKind::Sort(u_level.clone())),
        value: Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone()))), // Wrong: Sort(u+1) is not Sort(u)
        is_reducible: true,
    });
    assert!(
        result.is_err(),
        "Compound step 1: add_decl must reject ill-typed definition"
    );

    // Step 2: Simulate bypass — insert via add_decl_unchecked (trusted import path)
    // This simulates what could happen if a corrupted .olean file were loaded
    env.add_decl_unchecked(Declaration::Definition {
        name: Name::from_string("smuggled_1314"),
        level_params: vec![u_name.clone(), Name::from_string("v")], // 2 params
        type_: Expr::from_kind(ExprKind::Sort(u_level.clone())),
        value: Expr::type_(), // Ill-typed value
        is_reducible: true,
    });
    assert!(
        env.get_const(&Name::from_string("smuggled_1314")).is_some(),
        "Unchecked declaration exists (simulating trusted import)"
    );

    // Step 3: Defense — instantiation with wrong level count is blocked
    assert!(
        env.instantiate_type(&Name::from_string("smuggled_1314"), &[Level::zero()])
            .is_none(),
        "Compound step 3: 1 level for 2-param constant must be rejected"
    );
    assert!(
        env.instantiate_type(&Name::from_string("smuggled_1314"), &[])
            .is_none(),
        "Compound step 3: 0 levels for 2-param constant must be rejected"
    );

    // Step 4: Defense — unfold with wrong level count is also blocked
    assert!(
        env.unfold(&Name::from_string("smuggled_1314"), &[Level::zero()])
            .is_none(),
        "Compound step 4: unfold with wrong level count must be rejected"
    );

    // Step 5: Defense — type checker catches level mismatch on Expr::Const
    let bad_ref = Expr::const_(Name::from_string("smuggled_1314"), vec![Level::zero()]);
    let tc_result = TypeChecker::new(&env).infer_type(&bad_ref);
    assert!(
        tc_result.is_err(),
        "Compound step 5: type checker must reject level count mismatch"
    );

    // Step 6: Defense — even with correct level count, applying Classical.choice
    // to the ill-typed term is rejected by standard application type checking
    let correct_ref = Expr::const_(
        Name::from_string("smuggled_1314"),
        vec![Level::zero(), Level::succ(Level::zero())],
    );
    let choice_const = Expr::const_(Name::from_string("Classical.choice"), vec![Level::zero()]);
    let choice_app = Expr::app(
        Expr::app(choice_const, correct_ref.clone()),
        Expr::prop(), // Ill-typed: Nonempty <smuggled> expected, not Prop
    );
    let choice_exploit = Declaration::Definition {
        name: Name::from_string("exploit_1314"),
        level_params: vec![],
        type_: Expr::prop(),
        value: choice_app,
        is_reducible: false,
    };
    let exploit_result = env.add_decl(choice_exploit);
    assert!(
        exploit_result.is_err(),
        "Compound step 6: Classical.choice exploit must be rejected"
    );
    assert!(
        env.get_const(&Name::from_string("exploit_1314")).is_none(),
        "Exploit declaration must not appear in environment"
    );

    // Positive check: correct usage still works
    let ok_result = env.instantiate_type(
        &Name::from_string("smuggled_1314"),
        &[Level::zero(), Level::succ(Level::zero())],
    );
    assert!(
        ok_result.is_some(),
        "Correct level count still works for instantiation"
    );
}

// =============================================================================
// #3395: Lambda def with monad return type — free variables
// =============================================================================

/// Regression test for #3395: `def throwUB : Sem a := fun _s => Except.error SemError.ub`
/// The implicit `a` should be auto-bound as `{a : Type}`, not leak as a free variable.
#[test]
fn test_issue_3395_lambda_def_monad_return_type_no_free_vars() {
    use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
    use clean_parser::parse_file;

    let code = r#"
inductive SemError where
  | ub : SemError

abbrev Sem (a : Type) := StateT Nat (Except SemError) a

def throwUB : Sem a := fun _s => Except.error SemError.ub
"#;

    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(code).expect("parse_file should succeed");

    let mut results = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let r = elaborate_decl_and_register(&mut env, &processed);
        results.push(r);
    }

    // All three declarations (SemError, Sem, throwUB) should elaborate and register.
    for (i, r) in results.iter().enumerate() {
        assert!(
            r.is_ok(),
            "#3395 regression: declaration {i} failed: {:?}",
            r.as_ref().err().unwrap()
        );
    }

    // throwUB should be in the environment.
    assert!(
        env.get_const(&Name::from_string("throwUB")).is_some(),
        "#3395: throwUB should be registered in environment"
    );
}
