// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Adopted local-type metas must enter the new goal's immutable scope.

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabError, FileContext,
};
use clean_kernel::env::{DeclarationVerification, DomainAxiomClosure};
use clean_kernel::{BinderInfo, ConstantKind, Environment, Expr, ExprKind, Name, TypeChecker};
use clean_parser::parse_file;

fn constant(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn elaborate(source: &str) -> (Environment, Result<(), ElabError>) {
    let mut env = Environment::with_prelude();
    let mut context = FileContext::new();
    let declarations = parse_file(source).expect("the authored source parses");
    assert_eq!(declarations.len(), 1);
    let processed = preprocess_decl_with_context(&declarations[0], &mut context);
    let result =
        elaborate_decl_and_register_with_context(&mut env, &processed, &mut context).map(|_| ());
    (env, result)
}

fn checked_identity(source: &str, name: &str, parameter: &str) -> Environment {
    let (env, result) = elaborate(source);
    result.unwrap_or_else(|error| panic!("{name}: {error:?}"));
    let name = Name::from_string(name);
    let info = env
        .get_const(&name)
        .expect("the authored definition registers");
    assert_eq!(info.kind, ConstantKind::Definition);
    assert!(info.level_params.is_empty());
    assert_eq!(
        info.type_,
        Expr::pi(
            BinderInfo::Default,
            constant(parameter),
            constant(parameter)
        )
    );
    assert_eq!(
        env.declaration_verification(&name),
        Some(DeclarationVerification::FullKernelCheck)
    );
    let body = info.value.as_ref().expect("an actual stored body");
    for term in [&info.type_, body] {
        assert!(!term.has_fvar_quick());
        assert!(!term.has_expr_mvar_quick());
        assert!(!term.has_level_mvar_quick());
        assert!(!term.has_loose_bvars());
    }
    let checker = TypeChecker::new(&env);
    let sort = checker
        .infer_type_full(&info.type_)
        .expect("full type inference");
    assert!(matches!(checker.whnf(&sort).kind(), ExprKind::Sort(_)));
    checker
        .check_type(body, &info.type_)
        .expect("full stored body check");
    assert!(!checker.heartbeat_spent());
    assert!(env.axiom_deps(&name).expect("axiom closure").is_empty());
    assert!(env
        .foundational_axiom_deps(&name)
        .expect("foundational closure")
        .is_empty());
    assert!(DomainAxiomClosure::new()
        .assumptions_of_name(&env, &name)
        .is_empty());
    drop(checker);
    env
}

fn check_data(source: &str, name: &str) {
    let env = checked_identity(source, name, "Nat");
    let checker = TypeChecker::new(&env);
    for value in [0, 7, 11] {
        let application = Expr::app(constant(name), Expr::nat_lit(value));
        checker
            .check_type(&application, &constant("Nat"))
            .expect("full closed data application check");
        assert_eq!(checker.whnf(&application), Expr::nat_lit(value));
        assert!(!checker.heartbeat_spent());
    }
}

fn check_prop(source: &str, name: &str) {
    let env = checked_identity(source, name, "True");
    let checker = TypeChecker::new(&env);
    let application = Expr::app(constant(name), constant("True.intro"));
    checker
        .check_type(&application, &constant("True"))
        .expect("full closed proposition application check");
    assert_eq!(checker.whnf(&application), constant("True.intro"));
    assert!(!checker.heartbeat_spent());
}

#[test]
fn adopted_local_type_meta_data_exact_registers_checked_identity() {
    check_data(
        "def local_meta_data := fun (x : (_ : Type)) => (show Nat from by exact x)\n",
        "local_meta_data",
    );
}

#[test]
fn adopted_local_type_meta_prop_exact_registers_checked_identity() {
    check_prop(
        "def local_meta_prop := fun (h : (_ : Prop)) => (show True from by exact h)\n",
        "local_meta_prop",
    );
}

#[test]
fn adopted_local_type_meta_data_term_control() {
    check_data(
        "def local_meta_data_term := fun (x : (_ : Type)) => (show Nat from x)\n",
        "local_meta_data_term",
    );
}

#[test]
fn adopted_local_type_meta_prop_term_control() {
    check_prop(
        "def local_meta_prop_term := fun (h : (_ : Prop)) => (show True from h)\n",
        "local_meta_prop_term",
    );
}

#[test]
fn adopted_local_type_meta_wrong_data_stays_refused() {
    let (env, result) =
        elaborate("def local_meta_bad_data := fun (x : Bool) => (show Nat from by exact x)\n");
    assert!(result.is_err(), "a fixed Bool local cannot become Nat");
    assert!(env
        .get_const(&Name::from_string("local_meta_bad_data"))
        .is_none());
}

#[test]
fn adopted_local_type_meta_wrong_prop_stays_refused() {
    let (env, result) =
        elaborate("def local_meta_bad_prop := fun (h : False) => (show True from by exact h)\n");
    assert!(result.is_err(), "a fixed False local cannot become True");
    assert!(env
        .get_const(&Name::from_string("local_meta_bad_prop"))
        .is_none());
}

#[test]
fn adopted_local_type_meta_data_assumption_registers_checked_identity() {
    check_data(
        "def local_meta_data_assumption := fun (x : (_ : Type)) => (show Nat from by assumption)\n",
        "local_meta_data_assumption",
    );
}

#[test]
fn adopted_local_type_meta_prop_assumption_registers_checked_identity() {
    check_prop(
        "def local_meta_prop_assumption := fun (h : (_ : Prop)) => (show True from by assumption)\n",
        "local_meta_prop_assumption",
    );
}

#[test]
fn adopted_unconstrained_local_data_exact_registers_checked_identity() {
    check_data(
        "def local_meta_unconstrained_data_exact := fun (x : _) => (show Nat from by exact x)\n",
        "local_meta_unconstrained_data_exact",
    );
}

#[test]
fn adopted_unconstrained_local_prop_exact_registers_checked_identity() {
    check_prop(
        "def local_meta_unconstrained_prop_exact := fun (h : _) => (show True from by exact h)\n",
        "local_meta_unconstrained_prop_exact",
    );
}

#[test]
fn adopted_unconstrained_local_data_assumption_registers_checked_identity() {
    check_data(
        "def local_meta_unconstrained_data_assumption := fun (x : _) => (show Nat from by assumption)\n",
        "local_meta_unconstrained_data_assumption",
    );
}

#[test]
fn adopted_unconstrained_local_prop_assumption_registers_checked_identity() {
    check_prop(
        "def local_meta_unconstrained_prop_assumption := fun (h : _) => (show True from by assumption)\n",
        "local_meta_unconstrained_prop_assumption",
    );
}

#[test]
fn adopted_local_type_meta_exact_keeps_declared_universe_rigid() {
    let (env, result) = elaborate(
        "def local_meta_rigid_exact.{u} := fun (x : (_ : Type u)) => (show Nat from by exact x)\n",
    );
    assert!(
        result.is_err(),
        "an arbitrary declared universe cannot be specialized to Nat's universe"
    );
    assert!(env
        .get_const(&Name::from_string("local_meta_rigid_exact"))
        .is_none());
}

#[test]
fn adopted_local_type_meta_assumption_keeps_declared_universe_rigid() {
    let (env, result) = elaborate(
        "def local_meta_rigid_assumption.{u} := fun (x : (_ : Type u)) => (show Nat from by assumption)\n",
    );
    assert!(
        result.is_err(),
        "assumption cannot specialize an arbitrary declared universe"
    );
    assert!(env
        .get_const(&Name::from_string("local_meta_rigid_assumption"))
        .is_none());
}
