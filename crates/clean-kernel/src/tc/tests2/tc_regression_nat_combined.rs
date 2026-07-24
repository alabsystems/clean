// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TC regression tests: Nat reduction, reduceBool/reduceNat, combined patterns,
//! heartbeat-sensitive expressions, sort/level handling, and type inference.
//!
//! These tests cover patterns from .olean loading (#3134): native Nat
//! operations, Lean.reduceBool/reduceNat, deep nesting, typeclass projections,
//! and the UInt32.size == Nat.pow(2,32) def-eq that was the key failure.

use super::support::make_nat_env;
use super::*;
use crate::env::{ConstantInfo, Reducibility};
use crate::expr::Literal;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};

fn add_reducible(env: &mut Environment, name: &str, ty: Expr, value: Expr) {
    let mut info = ConstantInfo::new(Name::from_string(name), vec![], ty, Some(value), true);
    info.reducibility = Reducibility::Reducible;
    env.extend_constants_unchecked(std::iter::once(info));
}

fn cst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn cst_u(name: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(Name::from_string(name), levels)
}

fn nat_succ(n: Expr) -> Expr {
    Expr::app(cst("Nat.succ"), n)
}

fn binop(op_name: &str, a: Expr, b: Expr) -> Expr {
    Expr::app(Expr::app(cst(op_name), a), b)
}

// ============================================================================
// Nat native reduction
// ============================================================================

#[test]
fn test_regression_nat_add_reduces() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    assert_eq!(
        tc.whnf(&binop("Nat.add", Expr::nat_lit(100), Expr::nat_lit(200))),
        Expr::nat_lit(300),
        "Nat.add 100 200 should reduce to 300"
    );
}

#[test]
fn test_regression_nat_mul_reduces() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    assert_eq!(
        tc.whnf(&binop("Nat.mul", Expr::nat_lit(7), Expr::nat_lit(6))),
        Expr::nat_lit(42),
        "Nat.mul 7 6 should reduce to 42"
    );
}

/// Regression: Nat.pow 2 32 = 4294967296 (UInt32.size). Critical for .olean loading.
#[test]
fn test_regression_nat_pow_reduces() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    assert_eq!(
        tc.whnf(&binop("Nat.pow", Expr::nat_lit(2), Expr::nat_lit(32))),
        Expr::nat_lit(4_294_967_296),
        "Nat.pow 2 32 should reduce to 4294967296"
    );
}

/// Regression: Nat.pow 2 64 must reduce for UInt64.size.
#[test]
fn test_regression_nat_pow_2_64_reduces() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let result = tc.whnf(&binop("Nat.pow", Expr::nat_lit(2), Expr::nat_lit(64)));
    // 2^64 exceeds u64::MAX, so it's a BigNat
    assert!(
        matches!(result.kind(), ExprKind::Lit(Literal::Nat(n)) if n.to_u64().is_none()),
        "Nat.pow 2 64 should reduce to a BigNat (exceeds u64), got: {:?}",
        result
    );
}

#[test]
fn test_regression_nat_beq_equal() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let result = tc.whnf(&binop("Nat.beq", Expr::nat_lit(42), Expr::nat_lit(42)));
    assert!(
        matches!(result.kind(), ExprKind::Const(name, _) if name.to_string() == "Bool.true"),
        "Nat.beq 42 42 should reduce to Bool.true, got: {:?}",
        result
    );
}

#[test]
fn test_regression_nat_beq_not_equal() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let result = tc.whnf(&binop("Nat.beq", Expr::nat_lit(1), Expr::nat_lit(2)));
    assert!(
        matches!(result.kind(), ExprKind::Const(name, _) if name.to_string() == "Bool.false"),
        "Nat.beq 1 2 should reduce to Bool.false, got: {:?}",
        result
    );
}

#[test]
fn test_regression_nat_ble_reduces() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let r1 = tc.whnf(&binop("Nat.ble", Expr::nat_lit(3), Expr::nat_lit(5)));
    assert!(
        matches!(r1.kind(), ExprKind::Const(name, _) if name.to_string() == "Bool.true"),
        "Nat.ble 3 5 should reduce to Bool.true, got: {:?}",
        r1
    );

    let r2 = tc.whnf(&binop("Nat.ble", Expr::nat_lit(10), Expr::nat_lit(5)));
    assert!(
        matches!(r2.kind(), ExprKind::Const(name, _) if name.to_string() == "Bool.false"),
        "Nat.ble 10 5 should reduce to Bool.false, got: {:?}",
        r2
    );
}

// ============================================================================
// reduceBool / reduceNat patterns
// ============================================================================

/// Regression: Lean.reduceBool native reducer (#3134).
#[test]
fn test_regression_reduce_bool_chain() {
    let mut env = Environment::new();
    env.init_native_reducers();
    add_reducible(&mut env, "myBool", cst("Bool"), cst("Bool.true"));

    let tc = TypeChecker::new(&env);
    let expr = Expr::app(cst("Lean.reduceBool"), cst("myBool"));
    let result = tc
        .reduce_native_for_test(&expr)
        .expect("Lean.reduceBool(myBool) should reduce");
    assert!(
        matches!(result.kind(), ExprKind::Const(name, _) if name.to_string() == "Bool.true"),
        "Lean.reduceBool(myBool) should yield Bool.true, got: {:?}",
        result
    );
}

/// Regression: Lean.reduceNat native reducer.
#[test]
fn test_regression_reduce_nat_chain() {
    let mut env = Environment::new();
    env.init_native_reducers();
    add_reducible(&mut env, "myNat", cst("Nat"), Expr::nat_lit(30));

    let tc = TypeChecker::new(&env);
    let expr = Expr::app(cst("Lean.reduceNat"), cst("myNat"));
    let result = tc
        .reduce_native_for_test(&expr)
        .expect("Lean.reduceNat(myNat) should reduce");
    assert!(
        matches!(result.kind(), ExprKind::Lit(Literal::Nat(n)) if n.to_u64() == Some(30)),
        "Lean.reduceNat(myNat) should yield 30, got: {:?}",
        result
    );
}

// ============================================================================
// Deep nested applications (heartbeat-sensitive patterns)
// ============================================================================

/// Regression: 100 nested lets must reduce without stack overflow.
#[test]
fn test_regression_deep_nested_lets_reduce() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let depth = 100;
    let mut body = Expr::bvar(0);
    for _ in 0..depth {
        body = Expr::let_named(Name::anon(), Expr::type_(), Expr::prop(), body, false);
    }

    assert_eq!(
        tc.whnf(&body),
        Expr::prop(),
        "100 nested lets should reduce"
    );
}

/// Regression: 50 chained id applications must be linear, not exponential.
#[test]
fn test_regression_chained_applications_linear() {
    let mut env = Environment::new();
    add_reducible(
        &mut env,
        "id_prop",
        Expr::arrow(Expr::prop(), Expr::prop()),
        Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
    );

    let tc = TypeChecker::new(&env);
    let mut expr = Expr::prop();
    for _ in 0..50 {
        expr = Expr::app(cst("id_prop"), expr);
    }
    assert_eq!(
        tc.whnf(&expr),
        Expr::prop(),
        "50 id_prop layers should reduce"
    );
}

// ============================================================================
// Def-eq through let bindings and beta
// ============================================================================

#[test]
fn test_regression_defeq_let_binding() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let let_expr = Expr::let_named(
        Name::anon(),
        Expr::type_(),
        Expr::prop(),
        Expr::bvar(0),
        false,
    );
    assert!(
        tc.is_def_eq(&let_expr, &Expr::prop()),
        "let x := Prop in x == Prop"
    );
}

#[test]
fn test_regression_defeq_let_beta_composition() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let id = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
    let expr = Expr::let_named(
        Name::anon(),
        Expr::arrow(Expr::type_(), Expr::type_()),
        id,
        Expr::app(Expr::bvar(0), Expr::prop()),
        false,
    );
    assert!(
        tc.is_def_eq(&expr, &Expr::prop()),
        "let f := id in f Prop == Prop"
    );
}

// ============================================================================
// Typeclass projection chains (simulated)
// ============================================================================

/// Regression: projection through delta-unfolded instance (typeclass pattern).
#[test]
fn test_regression_typeclass_projection_chain() {
    let mut env = Environment::new();

    let monoid = Name::from_string("TMonoid");
    let monoid_type = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_());
    let mk_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::pi(
                BinderInfo::Default,
                Expr::arrow(Expr::bvar(1), Expr::arrow(Expr::bvar(2), Expr::bvar(3))),
                Expr::app(cst_u("TMonoid", vec![]), Expr::bvar(2)),
            ),
        ),
    );

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: monoid.clone(),
            type_: monoid_type,
            constructors: vec![Constructor {
                name: Name::from_string("TMonoid.mk"),
                type_: mk_type,
            }],
        }],
    };
    env.add_inductive(decl)
        .expect("invariant: TMonoid registers");
    env.init_nat().expect("invariant: Nat initializes");

    let inst_val = Expr::app(
        Expr::app(Expr::app(cst("TMonoid.mk"), cst("Nat")), Expr::nat_lit(0)),
        cst("Nat.add"),
    );
    let inst_ty = Expr::app(cst("TMonoid"), cst("Nat"));
    add_reducible(&mut env, "instNatMonoid", inst_ty, inst_val);

    let tc = TypeChecker::new(&env);

    let proj_zero = Expr::proj(monoid.clone(), 0, cst("instNatMonoid"));
    assert_eq!(tc.whnf(&proj_zero), Expr::nat_lit(0), "Project zero field");

    let proj_op = Expr::proj(monoid, 1, cst("instNatMonoid"));
    assert!(
        tc.is_def_eq(&tc.whnf(&proj_op), &cst("Nat.add")),
        "Project op field should yield Nat.add"
    );
}

// ============================================================================
// Nat.succ boundary and literal normalization
// ============================================================================

#[test]
fn test_regression_nat_succ_literal_normalization() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    assert!(tc.is_def_eq(&nat_succ(Expr::nat_lit(0)), &Expr::nat_lit(1)));
    assert!(tc.is_def_eq(&nat_succ(nat_succ(Expr::nat_lit(0))), &Expr::nat_lit(2)));
    assert!(tc.is_def_eq(
        &nat_succ(Expr::nat_lit(4_294_967_295)),
        &Expr::nat_lit(4_294_967_296)
    ));
}

#[test]
fn test_regression_nat_zero_edge_cases() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    assert!(tc.is_def_eq(
        &binop("Nat.add", Expr::nat_lit(0), Expr::nat_lit(0)),
        &Expr::nat_lit(0)
    ));
    assert!(tc.is_def_eq(
        &binop("Nat.mul", Expr::nat_lit(0), Expr::nat_lit(100)),
        &Expr::nat_lit(0)
    ));
    assert!(tc.is_def_eq(
        &binop("Nat.sub", Expr::nat_lit(0), Expr::nat_lit(5)),
        &Expr::nat_lit(0)
    ));
    assert!(tc.is_def_eq(
        &binop("Nat.pow", Expr::nat_lit(0), Expr::nat_lit(0)),
        &Expr::nat_lit(1)
    ));
    assert!(tc.is_def_eq(
        &binop("Nat.pow", Expr::nat_lit(1), Expr::nat_lit(1_000_000)),
        &Expr::nat_lit(1)
    ));
}

// ============================================================================
// Combined patterns (real .olean-like expressions)
// ============================================================================

/// Regression: UInt32.size == Nat.pow(2,32). The key #3134 failure.
#[test]
fn test_regression_uint32_size_defeq_pow() {
    let mut env = Environment::new();
    add_reducible(
        &mut env,
        "UInt32_size",
        cst("Nat"),
        Expr::nat_lit(4_294_967_296),
    );

    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(
            &cst("UInt32_size"),
            &binop("Nat.pow", Expr::nat_lit(2), Expr::nat_lit(32))
        ),
        "UInt32_size (= 4294967296) should be def-eq to Nat.pow 2 32"
    );
}

#[test]
fn test_regression_nat_add_through_delta() {
    let mut env = Environment::new();
    add_reducible(&mut env, "x_nat", cst("Nat"), Expr::nat_lit(10));
    add_reducible(&mut env, "y_nat", cst("Nat"), Expr::nat_lit(20));

    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(
            &binop("Nat.add", cst("x_nat"), cst("y_nat")),
            &Expr::nat_lit(30)
        ),
        "Nat.add x_nat y_nat (10 + 20) should be def-eq to 30"
    );
}

#[test]
fn test_regression_nested_nat_ops_defeq() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    // (3 + 4) * (10 - 3) = 7 * 7 = 49
    let product = binop(
        "Nat.mul",
        binop("Nat.add", Expr::nat_lit(3), Expr::nat_lit(4)),
        binop("Nat.sub", Expr::nat_lit(10), Expr::nat_lit(3)),
    );
    assert!(
        tc.is_def_eq(&product, &Expr::nat_lit(49)),
        "(3+4)*(10-3) == 49"
    );
}

// ============================================================================
// Sort/Level handling
// ============================================================================

#[test]
fn test_regression_sort_prop_defeq() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let sort0 = Expr::from_kind(ExprKind::Sort(Level::zero()));
    assert!(tc.is_def_eq(&sort0, &Expr::prop()), "Sort 0 == Prop");
}

#[test]
fn test_regression_sort_type_not_prop() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let sort1 = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
    assert!(tc.is_def_eq(&sort1, &Expr::type_()), "Sort 1 == Type");
    assert!(!tc.is_def_eq(&sort1, &Expr::prop()), "Sort 1 != Prop");
}

// ============================================================================
// Type inference
// ============================================================================

#[test]
fn test_regression_infer_type_id_app() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);
    let nat = cst("Nat");
    let id_nat = Expr::lam(BinderInfo::Default, nat.clone(), Expr::bvar(0));
    let applied = Expr::app(id_nat, Expr::nat_lit(42));

    let ty = tc.infer_type(&applied).expect("Should type-check");
    assert!(tc.is_def_eq(&ty, &nat), "Type of id_Nat 42 should be Nat");
}

#[test]
fn test_regression_infer_type_pi() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);
    let nat_arrow_nat = Expr::arrow(cst("Nat"), cst("Nat"));
    let ty = tc.infer_type(&nat_arrow_nat).expect("Should type-check");
    assert!(
        matches!(ty.kind(), ExprKind::Sort(level) if *level == Level::succ(Level::zero())),
        "Nat -> Nat should have type Type (Sort 1), got: {ty:?}"
    );
}
