// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! True end-to-end pipeline tests: kernel Expr -> to_lcnf -> to_mono ->
//! optimize -> RC -> IR -> boxing -> join_point_lower -> emit_{c,rust}.
//!
//! Existing pipeline tests (pipeline_e2e.rs, pipeline_rust_e2e.rs) start from
//! hand-built LCNF declarations. These tests start from kernel Expr via
//! `constant_to_decl`, exercising the to_lcnf stage that was previously only
//! tested in isolation.
//!
//! Part of #1940 — No end-to-end compilation pipeline test.

use clean_compiler::boxing::explicit_boxing_with_config;
use clean_compiler::constant_to_decl;
use clean_compiler::emit_c::{emit_c_with_config, CEmitConfig};
use clean_compiler::emit_rust::{emit_rust_with_config, RustEmitConfig};
use clean_compiler::lcnf::Decl;
use clean_compiler::rc;
use clean_compiler::to_ir::to_ir;
use clean_compiler::to_mono::to_mono;
use clean_compiler::{BoxingConfig, OptConfig, RCConfig};
use clean_kernel::env::{ConstantInfo, TrustedEnvExt};
use clean_kernel::{BinderInfo, Environment, Expr, ExprKind, Name};

// ============================================================================
// Helpers
// ============================================================================

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn nat_type() -> Expr {
    Expr::const_str("Nat")
}

/// Build a ConstantInfo representing `def <name> : <ret_type> := <value>` and
/// register it in the environment. These fixtures use already-stripped return
/// types when their focus is the downstream pipeline. The full-function-type
/// tests below exercise `constant_to_decl` stripping runtime lambda binders
/// itself.
fn add_definition(env: &mut Environment, def_name: &str, ret_type: Expr, value: Expr) -> Name {
    let n = name(def_name);
    env.extend_constants_unchecked(
        [ConstantInfo::new(
            n.clone(),
            vec![],
            ret_type,
            Some(value),
            false,
        )]
        .into_iter(),
    );
    n
}

/// Convert a kernel constant to an LCNF declaration via `constant_to_decl`.
fn lower_to_lcnf(env: &Environment, def_name: &Name) -> Decl {
    let info = env
        .get_const(def_name)
        .unwrap_or_else(|| panic!("constant {def_name} not found in env"));
    constant_to_decl(env, info)
        .expect("constant_to_decl should succeed")
        .expect("definition should produce a Decl (not an axiom)")
}

/// Run full pipeline: LCNF -> mono -> optimize -> RC -> IR -> boxing -> emit_c.
fn full_pipeline_c(decls: &[Decl]) -> String {
    let env = Environment::default();
    let mono: Vec<Decl> = decls.iter().map(|d| to_mono(d, &env)).collect();
    let opt_config = OptConfig::default();
    let opt: Vec<Decl> = mono
        .iter()
        .map(|d| clean_compiler::optimize(d, &opt_config))
        .collect();
    let rc_decls = rc::transform(&opt, &RCConfig::default());
    let ir_decls = to_ir(&rc_decls).expect("IR lowering should succeed");
    let boxed = explicit_boxing_with_config(&ir_decls, &BoxingConfig::default());
    emit_c_with_config(
        &boxed,
        CEmitConfig {
            check_ir: true,
            ..Default::default()
        },
    )
    .expect("emit_c should succeed")
}

/// Run full pipeline: LCNF -> mono -> optimize -> RC -> IR -> boxing ->
/// join_point_lower (internal) -> emit_rust.
fn full_pipeline_rust(decls: &[Decl]) -> String {
    let env = Environment::default();
    let mono: Vec<Decl> = decls.iter().map(|d| to_mono(d, &env)).collect();
    let opt_config = OptConfig::default();
    let opt: Vec<Decl> = mono
        .iter()
        .map(|d| clean_compiler::optimize(d, &opt_config))
        .collect();
    let rc_decls = rc::transform(&opt, &RCConfig::default());
    let ir_decls = to_ir(&rc_decls).expect("IR lowering should succeed");
    let boxed = explicit_boxing_with_config(&ir_decls, &BoxingConfig::default());
    // emit_rust internally runs join_point_lower::lower_decls
    emit_rust_with_config(
        &boxed,
        RustEmitConfig {
            check_ir: true,
            ..Default::default()
        },
    )
    .expect("emit_rust should succeed")
}

// ============================================================================
// Test 1: Identity function — kernel Expr through all 7 pipeline stages
// ============================================================================

// Part of #1940: kernel Expr identity function -> to_lcnf -> full pipeline -> emit
//
// Represents: def my_id (x : Nat) : Nat := x
// Kernel Expr: lam (x : Nat), BVar(0)
//
// Pipeline stages exercised:
//   to_lcnf (constant_to_decl) -> to_mono -> optimize -> RC -> to_ir
//   -> boxing -> emit_c / emit_rust (with join_point_lower)
#[test]
fn test_e2e_identity_from_kernel_expr() {
    let mut env = Environment::default();

    // Value: fun (x : Nat) => x
    let value = Expr::lam(BinderInfo::Default, nat_type(), Expr::bvar(0));

    // Return type is Nat (after stripping the one lambda parameter)
    let def_name = add_definition(&mut env, "my_id", nat_type(), value);
    let lcnf_decl = lower_to_lcnf(&env, &def_name);

    // -- Verify to_lcnf output --
    assert_eq!(lcnf_decl.params.len(), 1, "identity takes one parameter");
    assert!(!lcnf_decl.recursive, "identity is not recursive");
    assert!(
        matches!(lcnf_decl.params[0].ty.kind(), ExprKind::Const(n, _) if n.to_string() == "Nat"),
        "parameter should have Nat type, got: {:?}",
        lcnf_decl.params[0].ty
    );

    // -- Verify C backend output --
    let c_code = full_pipeline_c(std::slice::from_ref(&lcnf_decl));
    assert!(
        c_code.contains("l_my__id("),
        "C output should contain the mangled function name: {c_code}"
    );
    assert!(
        c_code.contains("clean_obj*"),
        "C output should have clean_obj* parameter type: {c_code}"
    );
    // Should NOT contain any todo!/unimplemented! markers
    assert!(
        !c_code.contains("todo!") && !c_code.contains("unimplemented!"),
        "C output should not contain incomplete markers: {c_code}"
    );

    // -- Verify Rust backend output (exercises join_point_lower internally) --
    let rust_code = full_pipeline_rust(&[lcnf_decl]);
    assert!(
        rust_code.contains("l_my__id("),
        "Rust output should contain the mangled function name: {rust_code}"
    );
    assert!(
        rust_code.contains("*mut CleanObj"),
        "Rust output should use *mut CleanObj type: {rust_code}"
    );
}

// ============================================================================
// Test 1b: Full function type — to_lcnf strips runtime binders before emit
// ============================================================================

// Part of #3708: compile bridge fixtures use kernel ConstantInfo entries with
// full function types such as `Nat -> Nat`. `constant_to_decl` must strip one
// Pi/arrow per runtime lambda before downstream C/Rust emission sees the result
// type.
#[test]
fn test_e2e_identity_from_full_function_type() {
    let mut env = Environment::default();

    // Represents: def my_id_full_type (x : Nat) : Nat := x
    let value = Expr::lam(BinderInfo::Default, nat_type(), Expr::bvar(0));
    let fn_type = Expr::arrow(nat_type(), nat_type());
    let def_name = add_definition(&mut env, "my_id_full_type", fn_type, value);
    let lcnf_decl = lower_to_lcnf(&env, &def_name);

    assert_eq!(lcnf_decl.params.len(), 1, "identity takes one parameter");
    assert_eq!(
        lcnf_decl.ty,
        nat_type(),
        "constant_to_decl should strip the parameter binder from the result type"
    );

    let c_code = full_pipeline_c(std::slice::from_ref(&lcnf_decl));
    assert!(
        c_code.contains("l_my__id__full__type("),
        "C output should contain the mangled function name: {c_code}"
    );
    assert!(
        c_code.contains("clean_obj*"),
        "C output should have clean_obj* parameter type: {c_code}"
    );

    let rust_code = full_pipeline_rust(&[lcnf_decl]);
    assert!(
        rust_code.contains("l_my__id__full__type("),
        "Rust output should contain the mangled function name: {rust_code}"
    );
    assert!(
        rust_code.contains("*mut CleanObj"),
        "Rust output should use *mut CleanObj type: {rust_code}"
    );
}

// Part of #3708: cover multiple runtime binders so the compile bridge cannot
// regress back to stripping only the first function arrow.
#[test]
fn test_e2e_two_arg_function_from_full_function_type() {
    let mut env = Environment::default();

    // Represents: def keep_left_full_type (x : Nat) (y : Nat) : Nat := x
    let body = Expr::bvar(1);
    let inner_lam = Expr::lam(BinderInfo::Default, nat_type(), body);
    let value = Expr::lam(BinderInfo::Default, nat_type(), inner_lam);
    let fn_type = Expr::arrow(nat_type(), Expr::arrow(nat_type(), nat_type()));
    let def_name = add_definition(&mut env, "keep_left_full_type", fn_type, value);
    let lcnf_decl = lower_to_lcnf(&env, &def_name);

    assert_eq!(lcnf_decl.params.len(), 2, "function takes two parameters");
    assert_eq!(
        lcnf_decl.ty,
        nat_type(),
        "constant_to_decl should strip both parameter binders from the result type"
    );

    let c_code = full_pipeline_c(std::slice::from_ref(&lcnf_decl));
    assert!(
        c_code.contains("l_keep__left__full__type("),
        "C output should contain the mangled function name: {c_code}"
    );
    assert!(
        c_code.contains("clean_obj*"),
        "C output should have clean_obj* parameter type: {c_code}"
    );

    let rust_code = full_pipeline_rust(&[lcnf_decl]);
    assert!(
        rust_code.contains("l_keep__left__full__type("),
        "Rust output should contain the mangled function name: {rust_code}"
    );
    assert!(
        rust_code.contains("*mut CleanObj"),
        "Rust output should use *mut CleanObj type: {rust_code}"
    );
}

// ============================================================================
// Test 2: Constant literal — kernel Expr through all 7 pipeline stages
// ============================================================================

// Part of #1940: kernel Expr literal -> to_lcnf -> full pipeline -> emit
//
// Represents: def answer : Nat := 42
// Kernel Expr: Lit(Nat(42))
//
// Exercises literal lowering in to_lcnf and literal emission in both backends.
#[test]
fn test_e2e_literal_from_kernel_expr() {
    let mut env = Environment::default();
    let value = Expr::from_kind(ExprKind::Lit(clean_kernel::Literal::Nat(
        clean_kernel::BigNat::from_u64(42),
    )));

    let def_name = add_definition(&mut env, "answer", nat_type(), value);
    let lcnf_decl = lower_to_lcnf(&env, &def_name);

    // -- Verify to_lcnf output --
    assert_eq!(lcnf_decl.params.len(), 0, "constant takes no parameters");
    assert!(!lcnf_decl.recursive, "constant is not recursive");

    // -- Verify C backend output --
    let c_code = full_pipeline_c(std::slice::from_ref(&lcnf_decl));
    assert!(
        c_code.contains("l_answer("),
        "C output should contain function name: {c_code}"
    );
    assert!(
        c_code.contains("42"),
        "C output should contain the literal 42: {c_code}"
    );

    // -- Verify Rust backend output --
    let rust_code = full_pipeline_rust(&[lcnf_decl]);
    assert!(
        rust_code.contains("l_answer("),
        "Rust output should contain function name: {rust_code}"
    );
    assert!(
        rust_code.contains("42"),
        "Rust output should contain the literal 42: {rust_code}"
    );
}

// ============================================================================
// Test 3: Closure application — kernel Expr through all 7 pipeline stages
// ============================================================================

// Part of #1940: kernel Expr with application -> to_lcnf -> full pipeline -> emit
//
// Represents: def apply_fn (f : Nat) (x : Nat) : Nat := f x
// Kernel Expr: lam (f : Nat), lam (x : Nat), App(BVar(1), BVar(0))
//
// Note: the binder type for f is Nat (not Nat -> Nat) because the IR type
// lowering stage only supports Const/BVar/FVar types. In monomorphized form,
// all non-scalar parameters become Object regardless of their source type.
// This matches the convention used by hand-built LCNF tests in
// pipeline_e2e.rs and pipeline_rust_e2e.rs.
//
// Exercises: to_lcnf application flattening, FVar closure dispatch, and
// clean_apply_1 emission in both backends.
#[test]
fn test_e2e_application_from_kernel_expr() {
    let mut env = Environment::default();

    // Value: fun (f : Nat) (x : Nat) => f x
    // (Nat as binder type for f — see note above)
    let body = Expr::app(Expr::bvar(1), Expr::bvar(0));
    let inner_lam = Expr::lam(BinderInfo::Default, nat_type(), body);
    let value = Expr::lam(BinderInfo::Default, nat_type(), inner_lam);

    // Return type is Nat (after stripping two lambda parameters)
    let def_name = add_definition(&mut env, "apply_fn", nat_type(), value);
    let lcnf_decl = lower_to_lcnf(&env, &def_name);

    // -- Verify to_lcnf output --
    assert_eq!(
        lcnf_decl.params.len(),
        2,
        "apply_fn takes two parameters (f, x)"
    );
    assert!(!lcnf_decl.recursive, "apply_fn is not recursive");

    // -- Verify C backend output: should emit a closure application --
    let c_code = full_pipeline_c(std::slice::from_ref(&lcnf_decl));
    assert!(
        c_code.contains("l_apply__fn("),
        "C output should contain the mangled function name: {c_code}"
    );
    assert!(
        c_code.contains("clean_apply_1(") || c_code.contains("clean_closure_apply("),
        "C output should emit closure application: {c_code}"
    );

    // -- Verify Rust backend output: should emit a closure application --
    let rust_code = full_pipeline_rust(&[lcnf_decl]);
    assert!(
        rust_code.contains("l_apply__fn("),
        "Rust output should contain the mangled function name: {rust_code}"
    );
    assert!(
        rust_code.contains("clean_apply_1(") || rust_code.contains("clean_closure_apply("),
        "Rust output should emit closure application: {rust_code}"
    );
    // Verify RC operations are present (multi-use of f and x)
    assert!(
        rust_code.contains("clean_inc(") || rust_code.contains("clean_dec("),
        "Rust output should contain RC operations for multi-use args: {rust_code}"
    );
}
