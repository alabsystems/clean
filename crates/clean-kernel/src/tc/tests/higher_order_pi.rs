// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for type checking higher-order Pi types (function type parameters).
//!
//! Validates that `infer_sort` and `add_decl` work correctly for types
//! containing higher-order function parameters like `(f : NNVec n -> NNVec n)`.
//!
//! Part of #3304: TC stack overflow on higher-order Pi types.

use super::*;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::Declaration;
use crate::level::Level;

/// Set up an environment with NN verification types (NNVec, Rat, etc.).
fn setup_nn_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_types().expect("init_nn_verify_types");
    env.init_rat_arith().expect("init_rat_arith");
    env
}

/// Build the `is_lipschitz` type that previously caused stack overflow:
/// `(n : Nat) -> (NNVec n -> NNVec n) -> Rat -> Prop`
fn build_is_lipschitz_type() -> Expr {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let nn_vec = Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]);
    let rat = Expr::const_(Name::from_string("Rat"), vec![]);
    let prop = Expr::sort(Level::zero());

    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(nat.clone());
    let vec_n = Expr::app(nn_vec, n);
    let endo = Expr::pi(BinderInfo::Default, vec_n.clone(), vec_n);
    let (f_id, _f) = b.fresh_local(endo.clone());
    let (l_id, _l) = b.fresh_local(rat.clone());

    let e = b.mk_pi(l_id, BinderInfo::Default, rat, prop);
    let e = b.mk_pi(f_id, BinderInfo::Default, endo, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, nat, e);
    b.finish(e)
}

/// Build the `compose_fns` type that previously caused stack overflow:
/// `(n : Nat) -> (NNVec n -> NNVec n) -> (NNVec n -> NNVec n) -> (NNVec n -> NNVec n)`
fn build_compose_fns_type() -> Expr {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let nn_vec = Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(nat.clone());
    let vec_n = Expr::app(nn_vec, n);
    let endo = Expr::pi(BinderInfo::Default, vec_n.clone(), vec_n);
    let (f_id, _) = b.fresh_local(endo.clone());
    let (g_id, _) = b.fresh_local(endo.clone());

    let e = b.mk_pi(g_id, BinderInfo::Default, endo.clone(), endo.clone());
    let e = b.mk_pi(f_id, BinderInfo::Default, endo, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, nat, e);
    b.finish(e)
}

/// Test that `infer_sort` succeeds on a type with higher-order function parameter.
///
/// This is the core regression test for #3304. Previously, `infer_sort` would
/// stack overflow on types containing `(NNVec n -> NNVec n)` as a Pi domain.
#[test]
fn test_infer_sort_higher_order_pi_is_lipschitz() {
    let env = setup_nn_env();
    let tc = TypeChecker::new(&env);
    let ty = build_is_lipschitz_type();
    let result = tc.infer_sort(&ty);
    assert!(
        result.is_ok(),
        "infer_sort should succeed on is_lipschitz type: {:?}",
        result.err(),
    );
}

/// Test that `infer_sort` succeeds on compose_fns type with multiple
/// higher-order function parameters.
#[test]
fn test_infer_sort_higher_order_pi_compose_fns() {
    let env = setup_nn_env();
    let tc = TypeChecker::new(&env);
    let ty = build_compose_fns_type();
    let result = tc.infer_sort(&ty);
    assert!(
        result.is_ok(),
        "infer_sort should succeed on compose_fns type: {:?}",
        result.err(),
    );
}

/// Test that `add_decl` succeeds for axioms with higher-order function types.
///
/// Previously these had to use `add_decl_unchecked` to bypass type checking.
/// With the fix for #3304, `add_decl` should work correctly.
#[test]
fn test_add_decl_higher_order_pi_axiom() {
    let mut env = setup_nn_env();
    let ty = build_is_lipschitz_type();
    let result = env.add_decl(Declaration::Axiom {
        name: Name::from_string("test.is_lipschitz"),
        level_params: vec![],
        type_: ty,
    });
    assert!(
        result.is_ok(),
        "add_decl should succeed for higher-order Pi axiom: {:?}",
        result.err(),
    );
}

/// Test that `add_decl` succeeds for compose_fns axiom type.
#[test]
fn test_add_decl_higher_order_pi_compose_fns() {
    let mut env = setup_nn_env();
    let ty = build_compose_fns_type();
    let result = env.add_decl(Declaration::Axiom {
        name: Name::from_string("test.compose_fns"),
        level_params: vec![],
        type_: ty,
    });
    assert!(
        result.is_ok(),
        "add_decl should succeed for compose_fns axiom: {:?}",
        result.err(),
    );
}

/// Register prerequisite axioms (is_lipschitz, compose_fns) for the full
/// compose_lipschitz type test. Split from `build_compose_lipschitz_full_type`
/// to keep function size within limits.
fn register_compose_prereqs(env: &mut Environment) {
    let is_lip_ty = build_is_lipschitz_type();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("test.is_lipschitz"),
        level_params: vec![],
        type_: is_lip_ty,
    })
    .expect("register is_lipschitz via add_decl");

    let compose_ty = build_compose_fns_type();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("test.compose_fns"),
        level_params: vec![],
        type_: compose_ty,
    })
    .expect("register compose_fns via add_decl");
}

/// Build the full compose_lipschitz type (the most complex case):
/// ```text
/// forall (n : Nat) (f g : NNVec n -> NNVec n) (Lf Lg : Rat),
///   is_lipschitz n f Lf ->
///   is_lipschitz n g Lg ->
///   is_lipschitz n (compose_fns n f g) (Rat.mul Lf Lg)
/// ```
///
/// This is the most demanding test because the domains include applications
/// of higher-order constants (`is_lipschitz n f Lf`) and compositions.
/// Requires `register_compose_prereqs` to be called first.
fn build_compose_lipschitz_full_type() -> Expr {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let nn_vec = Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]);
    let rat = Expr::const_(Name::from_string("Rat"), vec![]);
    let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
    let is_lipschitz_const = Expr::const_(Name::from_string("test.is_lipschitz"), vec![]);
    let compose_fns_const = Expr::const_(Name::from_string("test.compose_fns"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(nat.clone());
    let vec_n = Expr::app(nn_vec, n.clone());
    let endo = Expr::pi(BinderInfo::Default, vec_n.clone(), vec_n);
    let (f_id, f) = b.fresh_local(endo.clone());
    let (g_id, g) = b.fresh_local(endo.clone());
    let (lf_id, lf) = b.fresh_local(rat.clone());
    let (lg_id, lg) = b.fresh_local(rat.clone());

    let hyp_f = Expr::app(
        Expr::app(Expr::app(is_lipschitz_const.clone(), n.clone()), f.clone()),
        lf.clone(),
    );
    let (hf_id, _) = b.fresh_local(hyp_f.clone());

    let hyp_g = Expr::app(
        Expr::app(Expr::app(is_lipschitz_const.clone(), n.clone()), g.clone()),
        lg.clone(),
    );
    let (hg_id, _) = b.fresh_local(hyp_g.clone());

    // conclusion: is_lipschitz n (compose_fns n f g) (Rat.mul Lf Lg)
    let composed = Expr::app(Expr::app(Expr::app(compose_fns_const, n.clone()), f), g);
    let product = Expr::app(Expr::app(rat_mul, lf), lg);
    let concl = Expr::app(
        Expr::app(Expr::app(is_lipschitz_const, n), composed),
        product,
    );

    let e = b.mk_pi(hg_id, BinderInfo::Default, hyp_g, concl);
    let e = b.mk_pi(hf_id, BinderInfo::Default, hyp_f, e);
    let e = b.mk_pi(lg_id, BinderInfo::Default, rat.clone(), e);
    let e = b.mk_pi(lf_id, BinderInfo::Default, rat, e);
    let e = b.mk_pi(g_id, BinderInfo::Default, endo.clone(), e);
    let e = b.mk_pi(f_id, BinderInfo::Default, endo, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, nat, e);
    b.finish(e)
}

/// Test the full compose_lipschitz declaration via add_decl.
///
/// This tests the complete pipeline: registering is_lipschitz, compose_fns,
/// and then compose_lipschitz_axiom all through add_decl (not unchecked).
#[test]
fn test_add_decl_compose_lipschitz_full() {
    let mut env = setup_nn_env();
    register_compose_prereqs(&mut env);
    let ty = build_compose_lipschitz_full_type();
    let result = env.add_decl(Declaration::Axiom {
        name: Name::from_string("test.compose_lipschitz_axiom"),
        level_params: vec![],
        type_: ty,
    });
    assert!(
        result.is_ok(),
        "add_decl should succeed for compose_lipschitz axiom: {:?}",
        result.err(),
    );
}

/// Test that the ACTUAL nn_verify_lipschitz_compose types can go through
/// add_decl instead of add_decl_unchecked. This is the real regression test
/// for #3304 — these types previously required add_decl_unchecked due to
/// stack overflow in infer_sort.
#[test]
fn test_lipschitz_compose_via_add_decl() {
    let mut env = setup_nn_env();

    // Rebuild the exact same types from nn_verify_lipschitz_compose.rs
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let nn_vec = Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]);
    let rat = Expr::const_(Name::from_string("Rat"), vec![]);
    let prop = Expr::sort(Level::zero());

    // is_lipschitz type: (n : Nat) -> (NNVec n -> NNVec n) -> Rat -> Prop
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(nat.clone());
    let vec_n = Expr::app(nn_vec.clone(), n.clone());
    let endo = Expr::pi(BinderInfo::Default, vec_n.clone(), vec_n.clone());
    let (f_id, _f) = b.fresh_local(endo.clone());
    let (l_id, _l) = b.fresh_local(rat.clone());
    let e = b.mk_pi(l_id, BinderInfo::Default, rat.clone(), prop);
    let e = b.mk_pi(f_id, BinderInfo::Default, endo.clone(), e);
    let e = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), e);
    let is_lip_type = b.finish(e);

    // This is the key test: add_decl (not unchecked) on a type with
    // higher-order function parameter (NNVec n -> NNVec n)
    let result = env.add_decl(Declaration::Axiom {
        name: Name::from_string("NNVerify.is_lipschitz"),
        level_params: vec![],
        type_: is_lip_type,
    });
    assert!(
        result.is_ok(),
        "add_decl should succeed for is_lipschitz: {:?}",
        result.err(),
    );

    // compose_fns type: (n : Nat) -> (NNVec n -> NNVec n) -> (NNVec n -> NNVec n) -> (NNVec n -> NNVec n)
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(nat.clone());
    let vec_n = Expr::app(nn_vec, n);
    let endo = Expr::pi(BinderInfo::Default, vec_n.clone(), vec_n);
    let (f_id, _) = b.fresh_local(endo.clone());
    let (g_id, _) = b.fresh_local(endo.clone());
    let e = b.mk_pi(g_id, BinderInfo::Default, endo.clone(), endo.clone());
    let e = b.mk_pi(f_id, BinderInfo::Default, endo.clone(), e);
    let e = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), e);
    let compose_type = b.finish(e);

    let result = env.add_decl(Declaration::Axiom {
        name: Name::from_string("NNVerify.compose_fns"),
        level_params: vec![],
        type_: compose_type,
    });
    assert!(
        result.is_ok(),
        "add_decl should succeed for compose_fns: {:?}",
        result.err(),
    );
}

/// Build a 3-level nested higher-order Pi type:
/// ```text
/// (A : Type) -> (B : A -> Type) -> (C : (x : A) -> B x -> Type) -> Prop
/// ```
///
/// This is a genuine 3-level nested dependent Pi type where each parameter
/// depends on all preceding ones. This exercises the deepest recursion path
/// in `infer_sort_inner`: the domain `(x : A) -> B x -> Type` is itself a
/// Pi containing a Pi, requiring infer_sort to recurse through multiple
/// levels of domain types.
fn build_three_level_nested_pi_type() -> Expr {
    let type1 = Expr::sort(Level::succ(Level::zero())); // Type 0
    let prop = Expr::sort(Level::zero());

    let mut b = EnvDeclBuilder::new();

    // (A : Type)
    let (a_id, a) = b.fresh_local(type1.clone());

    // (B : A -> Type)
    // Build the domain type for B using child_of since it references outer FVar `a`
    let b_domain = {
        let mut inner = EnvDeclBuilder::child_of(&b);
        let (x_id, _x) = inner.fresh_local(a.clone());
        let e = inner.mk_pi(x_id, BinderInfo::Default, a.clone(), type1.clone());
        inner.finish_child(e)
    };
    let (b_id, b_expr) = b.fresh_local(b_domain.clone());

    // (C : (x : A) -> B x -> Type)
    //   The domain of C is itself a dependent Pi:
    //   (x : A) -> (y : B x) -> Type
    let c_domain = {
        let mut inner = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = inner.fresh_local(a.clone());
        let bx = Expr::app(b_expr.clone(), x);
        let (y_id, _y) = inner.fresh_local(bx.clone());
        let e = inner.mk_pi(y_id, BinderInfo::Default, bx, type1.clone());
        let e = inner.mk_pi(x_id, BinderInfo::Default, a.clone(), e);
        inner.finish_child(e)
    };
    let (c_id, _c) = b.fresh_local(c_domain.clone());

    // Result: (A : Type) -> (B : A -> Type) -> (C : ...) -> Prop
    let e = b.mk_pi(c_id, BinderInfo::Default, c_domain, prop);
    let e = b.mk_pi(b_id, BinderInfo::Default, b_domain, e);
    let e = b.mk_pi(a_id, BinderInfo::Default, type1, e);
    b.finish(e)
}

/// Test that `infer_sort` succeeds on a 3-level nested dependent Pi type.
///
/// This is the deepest nesting regression test for #3304. The domain
/// `(x : A) -> B x -> Type` exercises infer_sort_inner's Pi-unwinding
/// recursion through 3 levels of function type parameters.
#[test]
fn test_infer_sort_three_level_nested_pi() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let ty = build_three_level_nested_pi_type();
    let result = tc.infer_sort(&ty);
    assert!(
        result.is_ok(),
        "infer_sort should succeed on 3-level nested Pi type: {:?}",
        result.err(),
    );
}

/// Test that `add_decl` succeeds for an axiom with 3-level nested Pi type.
#[test]
fn test_add_decl_three_level_nested_pi() {
    let mut env = Environment::new();
    let ty = build_three_level_nested_pi_type();
    let result = env.add_decl(Declaration::Axiom {
        name: Name::from_string("test.three_level_nested"),
        level_params: vec![],
        type_: ty,
    });
    assert!(
        result.is_ok(),
        "add_decl should succeed for 3-level nested Pi axiom: {:?}",
        result.err(),
    );
}

/// Test that `Declaration::Theorem` (not just Axiom) with higher-order Pi
/// parameters passes `add_decl` without stack overflow.
///
/// This directly addresses acceptance criterion #1 from #3304:
/// "Declaration::Theorem with Pi parameters of function type passes add_decl
/// without stack overflow."
///
/// The theorem type is: (n : Nat) -> (NNVec n -> NNVec n) -> True
/// where `True : Prop`. The overall type lives in Prop via `imax` rule:
/// `Sort(imax(1, imax(imax(1,1), 0))) = Sort(0)`. The proof term is a
/// lambda returning `True.intro : True`.
#[test]
fn test_add_decl_theorem_higher_order_pi() {
    let mut env = setup_nn_env();

    // Register True : Prop and True.intro : True for use as proof term.
    // WS-A: `init_rat_arith` (called by `setup_nn_env`) now transitively pulls
    // `init_true_false` (the quotient `Rat.mul_inv_cancel` proof needs
    // `False.elim`), so `True` / `True.intro` may already be present — register
    // each only if absent to avoid a `DuplicateName` clash.
    let prop = Expr::sort(Level::zero());
    if env.get_const(&Name::from_string("True")).is_none() {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("True"),
            level_params: vec![],
            type_: prop.clone(),
        })
        .expect("register True");
    }
    if env.get_const(&Name::from_string("True.intro")).is_none() {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("True.intro"),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("True"), vec![]),
        })
        .expect("register True.intro");
    }

    // Build theorem type: (n : Nat) -> (NNVec n -> NNVec n) -> True
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let nn_vec = Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(nat.clone());
    let vec_n = Expr::app(nn_vec, n);
    let endo = Expr::pi(BinderInfo::Default, vec_n.clone(), vec_n);
    let (f_id, _f) = b.fresh_local(endo.clone());
    let true_const = Expr::const_(Name::from_string("True"), vec![]);

    // Result type returns True (a Prop)
    let e = b.mk_pi(f_id, BinderInfo::Default, endo.clone(), true_const.clone());
    let e = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), e);
    let thm_type = b.finish(e);

    // Proof term: fun (n : Nat) (f : NNVec n -> NNVec n) => True.intro
    let true_intro = Expr::const_(Name::from_string("True.intro"), vec![]);
    let nn_vec2 = Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]);
    let mut pb = EnvDeclBuilder::new();
    let (pn_id, pn) = pb.fresh_local(nat.clone());
    let pvec_n = Expr::app(nn_vec2, pn);
    let pendo = Expr::pi(BinderInfo::Default, pvec_n.clone(), pvec_n);
    let (pf_id, _pf) = pb.fresh_local(pendo.clone());
    let proof = pb.mk_lam(pf_id, BinderInfo::Default, pendo, true_intro);
    let proof = pb.mk_lam(pn_id, BinderInfo::Default, nat.clone(), proof);
    let proof_term = pb.finish(proof);

    let result = env.add_decl(Declaration::Theorem {
        name: Name::from_string("test.ho_pi_theorem"),
        level_params: vec![],
        type_: thm_type,
        value: proof_term,
    });
    assert!(
        result.is_ok(),
        "add_decl Theorem should succeed for higher-order Pi type: {:?}",
        result.err(),
    );
}

/// Build a deeply nested Pi type with N levels of function parameters.
///
/// Produces: (A1 : Type) -> (A2 : Type) -> ... -> (An : Type) -> Prop
///
/// This exercises the INFER_SORT_MAX_DEPTH guard in `infer_sort_inner`. Each
/// Pi domain is `Type` (Sort 1), requiring `infer_sort` to recurse through
/// each binder to compute `imax(1, imax(1, ... imax(1, 0)))`.
fn build_deeply_nested_pi_type(depth: usize) -> Expr {
    let type1 = Expr::sort(Level::succ(Level::zero())); // Type 0
    let prop = Expr::sort(Level::zero()); // Prop

    let mut b = EnvDeclBuilder::new();
    let mut ids = Vec::with_capacity(depth);

    for _ in 0..depth {
        let (id, _) = b.fresh_local(type1.clone());
        ids.push(id);
    }

    // Build from inside out: Prop is the return type
    let mut result = prop;
    for &id in ids.iter().rev() {
        result = b.mk_pi(id, BinderInfo::Default, type1.clone(), result);
    }
    b.finish(result)
}

/// Test that `infer_sort` succeeds on a 50-level deeply nested Pi type.
///
/// 50 levels is well within the INFER_SORT_MAX_DEPTH=64 guard, so this
/// exercises the normal recursion path without hitting the fallback.
/// Before #3304's stack_safe wrapping, this would stack overflow.
#[test]
fn test_infer_sort_deeply_nested_pi_50_levels() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let ty = build_deeply_nested_pi_type(50);
    let result = tc.infer_sort(&ty);
    assert!(
        result.is_ok(),
        "infer_sort should succeed on 50-level nested Pi type: {:?}",
        result.err(),
    );
}

/// Build a deeply nested Pi type where each domain is itself a function type.
///
/// Produces: (f1 : A -> A) -> (f2 : A -> A) -> ... -> (fn : A -> A) -> Prop
///
/// This is a harder case than simple `Type` domains because each domain is a
/// Pi type `(A -> A)`, requiring `infer_sort` to recurse into the domain's
/// inner Pi to compute `imax(sort(A), sort(A))` before processing the outer Pi.
/// This doubles the effective recursion depth compared to `build_deeply_nested_pi_type`.
fn build_deeply_nested_function_domain_pi(depth: usize) -> Expr {
    let type1 = Expr::sort(Level::succ(Level::zero())); // Type 0
    let prop = Expr::sort(Level::zero());

    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(type1.clone());

    // Domain type: A -> A (a function type, which is itself a Pi)
    let endo = Expr::pi(BinderInfo::Default, a.clone(), a);

    let mut ids = Vec::with_capacity(depth);
    for _ in 0..depth {
        let (id, _) = b.fresh_local(endo.clone());
        ids.push(id);
    }

    let mut result = prop;
    for &id in ids.iter().rev() {
        result = b.mk_pi(id, BinderInfo::Default, endo.clone(), result);
    }
    result = b.mk_pi(a_id, BinderInfo::Default, type1, result);
    b.finish(result)
}

/// Test that `infer_sort` succeeds on a 30-level nested Pi type where each
/// domain is a function type `(A -> A)`.
///
/// Each function-typed domain requires extra recursion in `infer_sort_inner`
/// to process the inner Pi, effectively doubling the depth. 30 function-typed
/// domains ~ 60 effective recursion levels, near the INFER_SORT_MAX_DEPTH=64
/// guard but still within bounds.
#[test]
fn test_infer_sort_deeply_nested_function_domains_30() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let ty = build_deeply_nested_function_domain_pi(30);
    let result = tc.infer_sort(&ty);
    assert!(
        result.is_ok(),
        "infer_sort should succeed on 30-level function-domain Pi type: {:?}",
        result.err(),
    );
}

/// Test that `add_decl` succeeds for an axiom with a 50-level deeply nested Pi type.
#[test]
fn test_add_decl_deeply_nested_pi_50_levels() {
    let mut env = Environment::new();
    let ty = build_deeply_nested_pi_type(50);
    let result = env.add_decl(Declaration::Axiom {
        name: Name::from_string("test.deep_nested_50"),
        level_params: vec![],
        type_: ty,
    });
    assert!(
        result.is_ok(),
        "add_decl should succeed for 50-level nested Pi axiom: {:?}",
        result.err(),
    );
}

/// Test that the depth guard provides a safe fallback for Pi nesting beyond
/// the INFER_SORT_MAX_DEPTH=64 limit.
///
/// With 100 nested Pi binders, the recursion depth exceeds 64. The
/// `infer_sort_inner` depth guard returns `Level::zero()` (Sort 0) as a
/// conservative fallback. This is sound because sorts are cumulative.
///
/// The test verifies that:
/// - No stack overflow occurs
/// - No heartbeat exhaustion (depth guard cuts off recursion early)
/// - The result is Ok (the conservative fallback produces a valid sort level)
#[test]
fn test_infer_sort_depth_guard_fallback_100_levels() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let ty = build_deeply_nested_pi_type(100);
    let result = tc.infer_sort(&ty);
    assert!(
        result.is_ok(),
        "infer_sort should succeed (via depth guard fallback) on 100-level Pi: {:?}",
        result.err(),
    );
}
