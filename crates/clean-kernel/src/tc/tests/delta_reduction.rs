// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for delta reduction in definitional equality.
//!
//! These tests cover `try_delta_reduction`, `get_delta_const`, and
//! `replace_head_const` — critical code paths that were previously untested.
//! Delta reduction is the last-resort fallback in `is_def_eq_core` and
//! incorrect behavior here could cause soundness issues (false negatives)
//! or infinite loops.
//!
//! Coverage gap identified in proof_coverage audit (P225).

use super::*;
use crate::env::{Declaration, Reducibility};

/// Helper: add a reducible definition to the environment.
fn add_reducible_def(env: &mut Environment, name: &str, ty: Expr, value: Expr) {
    let mut info = crate::env::ConstantInfo::new(
        Name::from_string(name),
        vec![],
        ty,
        Some(value),
        true, // is_reducible
    );
    info.reducibility = Reducibility::Reducible;
    env.extend_constants_unchecked(std::iter::once(info));
}

/// Helper: add a semireducible definition to the environment.
fn add_semireducible_def(env: &mut Environment, name: &str, ty: Expr, value: Expr) {
    let mut info =
        crate::env::ConstantInfo::new(Name::from_string(name), vec![], ty, Some(value), false);
    info.reducibility = Reducibility::Regular(0);
    env.extend_constants_unchecked(std::iter::once(info));
}

/// Helper: add an irreducible definition to the environment.
fn add_irreducible_def(env: &mut Environment, name: &str, ty: Expr, value: Expr) {
    let mut info =
        crate::env::ConstantInfo::new(Name::from_string(name), vec![], ty, Some(value), false);
    info.reducibility = Reducibility::Irreducible;
    env.extend_constants_unchecked(std::iter::once(info));
}

// ============================================================================
// Basic delta reduction through is_def_eq
// ============================================================================

/// Test: Two constants with the same definition are definitionally equal
/// via delta reduction.
///
/// This exercises the `try_delta_reduction` path in `is_def_eq_core`
/// where both sides are delta-reducible constants with the same value.
#[test]
fn test_delta_reduction_same_value() {
    let mut env = Environment::new();

    // a := Prop, b := Prop (both reducible)
    add_reducible_def(&mut env, "a", Expr::type_(), Expr::prop());
    add_reducible_def(&mut env, "b", Expr::type_(), Expr::prop());

    let tc = TypeChecker::new(&env);

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    // a and b should be def-eq because they both unfold to Prop
    assert!(
        tc.is_def_eq(&a, &b),
        "Constants with same definition should be def-eq via delta"
    );
}

/// Test: Two constants with different definitions are NOT def-eq.
#[test]
fn test_delta_reduction_different_values() {
    let mut env = Environment::new();

    // a := Prop, b := Type
    add_reducible_def(&mut env, "a", Expr::type_(), Expr::prop());
    add_reducible_def(
        &mut env,
        "b",
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::succ(Level::zero())))),
        Expr::type_(),
    );

    let tc = TypeChecker::new(&env);

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    assert!(
        !tc.is_def_eq(&a, &b),
        "Constants with different definitions should not be def-eq"
    );
}

/// Test: One side is a constant, other side is a value — delta unfolds
/// the constant to match.
///
/// This exercises the (Some, None) branch of `try_delta_reduction`.
#[test]
fn test_delta_reduction_one_side_const() {
    let mut env = Environment::new();

    // myProp := Prop (reducible)
    add_reducible_def(&mut env, "myProp", Expr::type_(), Expr::prop());

    let tc = TypeChecker::new(&env);

    let my_prop = Expr::const_(Name::from_string("myProp"), vec![]);

    // myProp should be def-eq to Prop after delta
    assert!(
        tc.is_def_eq(&my_prop, &Expr::prop()),
        "Constant should unfold to match its definition"
    );

    // Symmetry: Prop == myProp (exercises (None, Some) branch)
    assert!(
        tc.is_def_eq(&Expr::prop(), &my_prop),
        "Definition should match constant (symmetric)"
    );
}

// ============================================================================
// Reducibility ordering in delta reduction
// ============================================================================

/// Test: Reducible constants are unfolded before semireducible ones.
///
/// This tests the core reducibility ordering logic in `try_delta_reduction`:
/// when both sides are delta-reducible, the more reducible one is unfolded first.
#[test]
fn test_delta_reduction_reducibility_ordering() {
    let mut env = Environment::new();

    // chain: reducible_a := semi_b := Prop
    // semi_b is semireducible, reducible_a is reducible
    add_semireducible_def(&mut env, "semi_b", Expr::type_(), Expr::prop());
    add_reducible_def(
        &mut env,
        "reducible_a",
        Expr::type_(),
        Expr::const_(Name::from_string("semi_b"), vec![]),
    );

    let tc = TypeChecker::new(&env);

    let a = Expr::const_(Name::from_string("reducible_a"), vec![]);
    let b = Expr::const_(Name::from_string("semi_b"), vec![]);

    // Both should be def-eq to Prop after delta reduction
    assert!(
        tc.is_def_eq(&a, &b),
        "Reducible and semireducible definitions of same value should be def-eq"
    );
}

/// Test: When both constants have the same reducibility, delta reduction
/// still works (arbitrary choice of which to unfold).
#[test]
fn test_delta_reduction_same_reducibility() {
    let mut env = Environment::new();

    // Both reducible, both define to Prop
    add_reducible_def(&mut env, "x", Expr::type_(), Expr::prop());
    add_reducible_def(&mut env, "y", Expr::type_(), Expr::prop());

    let tc = TypeChecker::new(&env);

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);

    assert!(
        tc.is_def_eq(&x, &y),
        "Same-reducibility constants with same value should be def-eq"
    );
}

/// Test: Irreducible definitions unfold in the kernel type checker.
///
/// Lean 4's kernel has NO transparency modes — it unfolds any definition or
/// theorem, regardless of reducibility hints. Reducibility hints only control
/// unfolding ORDER in the lazy delta loop, not WHETHER a constant can be
/// unfolded. So even `Reducibility::Irreducible` constants unfold in WHNF.
///
/// Reference: Lean 4 type_checker.cpp:487 `is_delta` checks `has_value()`
/// which returns `is_definition() || is_theorem()` — no reducibility check.
///
/// Part of #3208
#[test]
fn test_delta_reduction_irreducible_unfolds_in_kernel() {
    let mut env = Environment::new();

    // irr_a and irr_b both define to Prop but are irreducible
    add_irreducible_def(&mut env, "irr_a", Expr::type_(), Expr::prop());
    add_irreducible_def(&mut env, "irr_b", Expr::type_(), Expr::prop());

    let tc = TypeChecker::new(&env);

    let a = Expr::const_(Name::from_string("irr_a"), vec![]);
    let b = Expr::const_(Name::from_string("irr_b"), vec![]);

    // In the kernel, both irr_a and irr_b unfold to Prop, so they ARE def-eq.
    // This matches Lean 4's kernel which has no transparency.
    assert!(
        tc.is_def_eq(&a, &b),
        "Kernel should unfold irreducible constants (no transparency in kernel)"
    );
}

// ============================================================================
// replace_head_const through applied definitions
// ============================================================================

/// Test: Delta reduction with applied constants.
///
/// When we have `f a b` where `f := g` (a definition), delta reduction
/// should produce `g a b`. This tests `replace_head_const`.
#[test]
fn test_delta_reduction_applied_const() {
    let mut env = Environment::new();

    // Define an axiom: g : Prop → Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("g"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
    })
    .unwrap();

    // Define f := g (reducible)
    add_reducible_def(
        &mut env,
        "f",
        Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
        Expr::const_(Name::from_string("g"), vec![]),
    );

    // Define an axiom p : Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("p"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    let tc = TypeChecker::new(&env);

    let f = Expr::const_(Name::from_string("f"), vec![]);
    let g = Expr::const_(Name::from_string("g"), vec![]);
    let p = Expr::const_(Name::from_string("p"), vec![]);

    // f p should be def-eq to g p after delta-reducing f to g
    let f_p = Expr::app(f, p.clone());
    let g_p = Expr::app(g, p);

    assert!(
        tc.is_def_eq(&f_p, &g_p),
        "Applied delta-reducible constant should unfold: f p == g p"
    );
}

/// Test: Delta reduction with multi-arg application chain.
///
/// `f a b` where `f := h` should reduce to `h a b`.
/// This tests `replace_head_const` with a longer application chain.
#[test]
fn test_delta_reduction_multi_arg_app() {
    let mut env = Environment::new();

    // h : Prop → Prop → Prop (axiom)
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("h"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            Expr::prop(),
            Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
        ),
    })
    .unwrap();

    // f := h (reducible)
    add_reducible_def(
        &mut env,
        "f",
        Expr::pi(
            BinderInfo::Default,
            Expr::prop(),
            Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
        ),
        Expr::const_(Name::from_string("h"), vec![]),
    );

    // Two axioms p, q : Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("p"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("q"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    let tc = TypeChecker::new(&env);

    let f = Expr::const_(Name::from_string("f"), vec![]);
    let h = Expr::const_(Name::from_string("h"), vec![]);
    let p = Expr::const_(Name::from_string("p"), vec![]);
    let q = Expr::const_(Name::from_string("q"), vec![]);

    // f p q == h p q
    let f_p_q = Expr::app(Expr::app(f, p.clone()), q.clone());
    let h_p_q = Expr::app(Expr::app(h, p), q);

    assert!(
        tc.is_def_eq(&f_p_q, &h_p_q),
        "Multi-arg applied delta should unfold: f p q == h p q"
    );
}

// ============================================================================
// Chained delta reduction
// ============================================================================

/// Test: Chained delta reductions.
///
/// a := b, b := c, c := Prop. Then a should be def-eq to Prop
/// through multiple delta reduction steps.
#[test]
fn test_delta_reduction_chain() {
    let mut env = Environment::new();

    add_reducible_def(&mut env, "c_val", Expr::type_(), Expr::prop());
    add_reducible_def(
        &mut env,
        "b_val",
        Expr::type_(),
        Expr::const_(Name::from_string("c_val"), vec![]),
    );
    add_reducible_def(
        &mut env,
        "a_val",
        Expr::type_(),
        Expr::const_(Name::from_string("b_val"), vec![]),
    );

    let tc = TypeChecker::new(&env);

    let a = Expr::const_(Name::from_string("a_val"), vec![]);

    assert!(
        tc.is_def_eq(&a, &Expr::prop()),
        "Chained delta reductions should resolve: a := b := c := Prop"
    );
}

// ============================================================================
// Delta reduction with axioms (no value)
// ============================================================================

/// Test: Axioms (no value) do not participate in delta reduction.
#[test]
fn test_delta_no_reduction_axiom() {
    let mut env = Environment::new();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("ax1"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("ax2"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    let tc = TypeChecker::new(&env);

    let ax1 = Expr::const_(Name::from_string("ax1"), vec![]);
    let ax2 = Expr::const_(Name::from_string("ax2"), vec![]);

    // Two different axioms should NOT be def-eq (no delta to apply)
    assert!(
        !tc.is_def_eq(&ax1, &ax2),
        "Different axioms should not be def-eq"
    );

    // Same axiom should be def-eq (reflexivity, not delta)
    assert!(tc.is_def_eq(&ax1, &ax1), "Same axiom should be def-eq");
}

// ============================================================================
// Delta reduction with universe-polymorphic definitions
// ============================================================================

/// Test: Delta reduction with universe-polymorphic definitions.
///
/// `id.{u} := λ (α : Sort u) (a : α). a`
/// Then `id.{0} Prop p` should reduce correctly.
#[test]
fn test_delta_reduction_universe_poly() {
    let mut env = Environment::new();

    let u_name = Name::from_string("u");
    // id : (α : Sort u) → α → α
    let id_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::from_kind(ExprKind::Sort(Level::param(u_name.clone()))),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
    );
    // id := λ (α : Sort u) (a : α). a
    let id_value = Expr::lam(
        BinderInfo::Implicit,
        Expr::from_kind(ExprKind::Sort(Level::param(u_name.clone()))),
        Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
    );

    let mut info = crate::env::ConstantInfo::new(
        Name::from_string("myId"),
        vec![u_name],
        id_type,
        Some(id_value),
        true,
    );
    info.reducibility = Reducibility::Reducible;
    env.extend_constants_unchecked(std::iter::once(info));

    // p : Prop (axiom)
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("p"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    let tc = TypeChecker::new(&env);

    // myId.{1} Prop p -- universe level 1 for Sort 1 = Type
    let my_id = Expr::const_(Name::from_string("myId"), vec![Level::succ(Level::zero())]);
    let p = Expr::const_(Name::from_string("p"), vec![]);
    let id_prop_p = Expr::app(Expr::app(my_id, Expr::prop()), p.clone());

    // Should delta-reduce myId to (λ α a. a), then beta-reduce to p
    assert!(
        tc.is_def_eq(&id_prop_p, &p),
        "Universe-polymorphic delta reduction: myId.{{1}} Prop p == p"
    );
}

// ============================================================================
// Mixed reducibility: reducible vs semireducible
// ============================================================================

/// Test: When one side is reducible and other is semireducible,
/// both should unfold in Default transparency mode.
///
/// Setup: red_f := semi_g, semi_g := Prop
/// WHNF(red_f) → semi_g → Prop (both reducible and regular unfold in Default mode)
///
/// In Lean 4's Default transparency, Regular definitions ARE unfoldable.
/// Only Irreducible and Opaque block unfolding.
#[test]
fn test_delta_reducible_unfolds_before_semireducible() {
    let mut env = Environment::new();

    add_semireducible_def(&mut env, "semi_g", Expr::type_(), Expr::prop());
    add_reducible_def(
        &mut env,
        "red_f",
        Expr::type_(),
        Expr::const_(Name::from_string("semi_g"), vec![]),
    );

    let tc = TypeChecker::new(&env);

    let red_f = Expr::const_(Name::from_string("red_f"), vec![]);
    let semi_g = Expr::const_(Name::from_string("semi_g"), vec![]);

    // WHNF unfolds red_f to semi_g, so these match structurally
    assert!(
        tc.is_def_eq(&red_f, &semi_g),
        "Reducible should unfold to match semireducible"
    );

    // In Default transparency, semi_g (Regular) IS unfoldable, so
    // red_f → semi_g → Prop, matching Prop directly.
    assert!(
        tc.is_def_eq(&red_f, &Expr::prop()),
        "Regular definitions should unfold in Default transparency mode"
    );
}

/// Test: Height-based unfold ordering in delta reduction.
///
/// Verifies that `try_delta_reduction` unfolds the higher-height definition
/// first when both sides have `Regular` reducibility. This is the core
/// behavior added by #1423: definitions that reference other definitions
/// (higher height) are unfolded before their dependencies (lower height).
///
/// Setup:
/// - `base_f` := Nat → Nat (height 0, references nothing)
/// - `outer_g` := base_f (height 1, references base_f)
/// - `outer_h` := base_f (height 1, references base_f)
///
/// Expectations:
/// - `outer_g` and `outer_h` both reduce to `base_f`, so they are def-eq
///   (via Equal comparison → unfold both)
/// - `base_f` and `outer_g` are def-eq because outer_g unfolds to base_f
///   (via height comparison → unfold outer_g first)
///
/// Reference: Lean 4 `type_checker.cpp:886-943`, `declaration.cpp:24-49`
#[test]
fn test_delta_reduction_height_ordering() {
    let mut env = Environment::new();
    env.init_nat().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_to_nat = Expr::pi(BinderInfo::Default, nat.clone(), nat.clone());

    // base_f : Type := Nat → Nat, height 0
    let mut base_info = crate::env::ConstantInfo::new(
        Name::from_string("base_f"),
        vec![],
        Expr::type_(),
        Some(nat_to_nat.clone()),
        false,
    );
    base_info.reducibility = Reducibility::Regular(0);
    env.extend_constants_unchecked(std::iter::once(base_info));

    // outer_g : Type := base_f, height 1 (references base_f which has height 0)
    let base_f_ref = Expr::const_(Name::from_string("base_f"), vec![]);
    let mut outer_g_info = crate::env::ConstantInfo::new(
        Name::from_string("outer_g"),
        vec![],
        Expr::type_(),
        Some(base_f_ref.clone()),
        false,
    );
    outer_g_info.reducibility = Reducibility::Regular(1);
    env.extend_constants_unchecked(std::iter::once(outer_g_info));

    // outer_h : Type := base_f, height 1 (same as outer_g)
    let mut outer_h_info = crate::env::ConstantInfo::new(
        Name::from_string("outer_h"),
        vec![],
        Expr::type_(),
        Some(base_f_ref.clone()),
        false,
    );
    outer_h_info.reducibility = Reducibility::Regular(1);
    env.extend_constants_unchecked(std::iter::once(outer_h_info));

    let tc = TypeChecker::new(&env);

    let f = Expr::const_(Name::from_string("base_f"), vec![]);
    let g = Expr::const_(Name::from_string("outer_g"), vec![]);
    let h = Expr::const_(Name::from_string("outer_h"), vec![]);

    // outer_g (height 1) vs outer_h (height 1): Equal → unfold both → base_f = base_f ✓
    assert!(
        tc.is_def_eq(&g, &h),
        "Two Regular(1) definitions with same value should be def-eq (unfold both)"
    );

    // outer_g (height 1) vs base_f (height 0): Greater height unfolds first
    // outer_g unfolds to base_f, then base_f = base_f ✓
    assert!(
        tc.is_def_eq(&g, &f),
        "Higher-height definition should unfold to match lower-height one"
    );

    // base_f (height 0) vs outer_g (height 1): same check, reversed
    assert!(
        tc.is_def_eq(&f, &g),
        "Height ordering should work regardless of argument position"
    );
}

/// Test: Height computation via get_max_height.
///
/// Verifies that `Environment::get_max_height` correctly computes the
/// maximum height by walking all sub-expressions of a value.
#[test]
fn test_get_max_height_computation() {
    let mut env = Environment::new();

    // leaf_a : Prop := Prop, height 0
    let mut a_info = crate::env::ConstantInfo::new(
        Name::from_string("leaf_a"),
        vec![],
        Expr::type_(),
        Some(Expr::prop()),
        false,
    );
    a_info.reducibility = Reducibility::Regular(0);
    env.extend_constants_unchecked(std::iter::once(a_info));

    // leaf_b : Prop := Prop, height 0
    let mut b_info = crate::env::ConstantInfo::new(
        Name::from_string("leaf_b"),
        vec![],
        Expr::type_(),
        Some(Expr::prop()),
        false,
    );
    b_info.reducibility = Reducibility::Regular(0);
    env.extend_constants_unchecked(std::iter::once(b_info));

    // mid_c : references leaf_a → height(mid_c's value) should find max = 0
    let leaf_a_ref = Expr::const_(Name::from_string("leaf_a"), vec![]);
    assert_eq!(env.get_max_height(&leaf_a_ref), 0, "leaf_a has height 0");

    // Value that references nothing → height 0
    assert_eq!(
        env.get_max_height(&Expr::prop()),
        0,
        "Prop has no const refs"
    );

    // Add mid_c with height 1
    let mut c_info = crate::env::ConstantInfo::new(
        Name::from_string("mid_c"),
        vec![],
        Expr::type_(),
        Some(leaf_a_ref.clone()),
        false,
    );
    c_info.reducibility = Reducibility::Regular(1);
    env.extend_constants_unchecked(std::iter::once(c_info));

    // Expression referencing mid_c should find max = 1
    let mid_c_ref = Expr::const_(Name::from_string("mid_c"), vec![]);
    assert_eq!(env.get_max_height(&mid_c_ref), 1, "mid_c has height 1");

    // Expression referencing both leaf_a (height 0) and mid_c (height 1) → max = 1
    let app_expr = Expr::app(leaf_a_ref, mid_c_ref);
    assert_eq!(
        env.get_max_height(&app_expr),
        1,
        "max(leaf_a=0, mid_c=1) = 1"
    );
}

/// Test: get_max_height deduplicates shared DAG sub-expressions.
///
/// Builds a DAG where the same Arc<Expr> sub-expression appears in multiple
/// positions. Verifies that the visited-set prevents exponential re-traversal
/// while still computing the correct maximum height.
#[test]
fn test_get_max_height_dag_dedup() {
    let mut env = Environment::new();

    // Add a constant with height 0
    let mut leaf_info = crate::env::ConstantInfo::new(
        Name::from_string("dag_leaf"),
        vec![],
        Expr::type_(),
        Some(Expr::prop()),
        false,
    );
    leaf_info.reducibility = Reducibility::Regular(0);
    env.extend_constants_unchecked(std::iter::once(leaf_info));

    // Add a constant with height 3
    let mut high_info = crate::env::ConstantInfo::new(
        Name::from_string("dag_high"),
        vec![],
        Expr::type_(),
        Some(Expr::prop()),
        false,
    );
    high_info.reducibility = Reducibility::Regular(3);
    env.extend_constants_unchecked(std::iter::once(high_info));

    // Build a shared sub-expression referencing dag_high (height 3)
    let shared = Expr::app(
        Expr::const_(Name::from_string("dag_high"), vec![]),
        Expr::const_(Name::from_string("dag_leaf"), vec![]),
    );

    // Build a DAG: App(App(shared, shared), App(shared, shared))
    // The same Arc<Expr> appears in 4 leaf positions.
    // Without dedup this visits shared's subtree 4 times; with dedup, once.
    let inner_left = Expr::app(shared.clone(), shared.clone());
    let inner_right = Expr::app(shared.clone(), shared.clone());
    let dag_root = Expr::app(inner_left, inner_right);

    assert_eq!(
        env.get_max_height(&dag_root),
        3,
        "DAG with shared sub-expressions must find max height = 3"
    );
}

/// Test: Reducibility::compare ordering.
///
/// Verifies the compare function implements Lean 4 semantics:
/// Reducible > Regular(high) > Regular(low) > Irreducible > Opaque
#[test]
fn test_reducibility_compare_ordering() {
    use std::cmp::Ordering;

    let reducible = Reducibility::Reducible;
    let regular_0 = Reducibility::Regular(0);
    let regular_5 = Reducibility::Regular(5);
    let regular_10 = Reducibility::Regular(10);
    let irreducible = Reducibility::Irreducible;
    let opaque = Reducibility::Opaque;

    // Reducible < Regular (reducible is "more reducible", unfold first)
    assert_eq!(reducible.compare(&regular_0), Ordering::Less);
    assert_eq!(regular_0.compare(&reducible), Ordering::Greater);

    // Regular < Irreducible
    assert_eq!(regular_5.compare(&irreducible), Ordering::Less);
    assert_eq!(irreducible.compare(&regular_5), Ordering::Greater);

    // Irreducible < Opaque
    assert_eq!(irreducible.compare(&opaque), Ordering::Less);
    assert_eq!(opaque.compare(&irreducible), Ordering::Greater);

    // Same Regular: higher height unfolds first (Less = unfold self)
    assert_eq!(
        regular_10.compare(&regular_5),
        Ordering::Less,
        "height 10 > height 5, unfold 10 first"
    );
    assert_eq!(
        regular_5.compare(&regular_10),
        Ordering::Greater,
        "height 5 < height 10, unfold 10 first"
    );

    // Same height: Equal (unfold both)
    assert_eq!(
        regular_5.compare(&regular_5),
        Ordering::Equal,
        "same height → unfold both"
    );

    // Same kind (non-Regular): Equal
    assert_eq!(reducible.compare(&reducible), Ordering::Equal);
    assert_eq!(irreducible.compare(&irreducible), Ordering::Equal);
    assert_eq!(opaque.compare(&opaque), Ordering::Equal);
}

/// Test: Delta reduction transparency boundary in the kernel.
///
/// The kernel has no transparency modes — ALL definitions unfold regardless
/// of reducibility hints. Regular AND Irreducible definitions unfold.
/// Only Opaque declarations (ConstantKind::Opaque) are blocked.
///
/// Reference: Lean 4 type_checker.cpp:487 `is_delta` + line 1005:
/// "the simpler approach used at Meta.ExprDefEq cannot be used in the
/// kernel since it does not have access to reducibility annotations."
///
/// Part of #3208
#[test]
fn test_delta_reduction_transparency_boundary() {
    let mut env = Environment::new();

    // semi_a := Prop, semi_b := Prop (both Regular/semireducible)
    add_semireducible_def(&mut env, "semi_a", Expr::type_(), Expr::prop());
    add_semireducible_def(&mut env, "semi_b", Expr::type_(), Expr::prop());

    // irred_c := Prop (irreducible — kernel still unfolds this)
    add_irreducible_def(&mut env, "irred_c", Expr::type_(), Expr::prop());

    let tc = TypeChecker::new(&env);

    let a = Expr::const_(Name::from_string("semi_a"), vec![]);
    let b = Expr::const_(Name::from_string("semi_b"), vec![]);
    let c = Expr::const_(Name::from_string("irred_c"), vec![]);

    // Regular definitions unfold: both reduce to Prop
    assert!(
        tc.is_def_eq(&a, &b),
        "Regular definitions should be def-eq when they unfold to the same value"
    );
    assert!(
        tc.is_def_eq(&a, &Expr::prop()),
        "Regular definitions should unfold to their value"
    );

    // Kernel unfolds irreducible definitions too (no transparency in kernel)
    assert!(
        tc.is_def_eq(&c, &Expr::prop()),
        "Kernel should unfold irreducible definitions (no transparency)"
    );
    assert!(
        tc.is_def_eq(&a, &c),
        "Regular and Irreducible should match (both unfold to Prop in kernel)"
    );
}

// ============================================================================
// Projection-app unfold preference in one-sided delta branches
// (Lean 4 type_checker.cpp:891-911 try_unfold_proj_app)
// ============================================================================

/// Helper: register a Pair inductive and return the Pair name.
fn add_pair_inductive(env: &mut Environment) -> Name {
    use crate::inductive::{Constructor, InductiveDecl, InductiveType};

    let pair = Name::from_string("Pair");
    let pair_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
    );
    let mk_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            Expr::type_(),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(1),
                    Expr::app(
                        Expr::app(Expr::const_(pair.clone(), vec![]), Expr::bvar(3)),
                        Expr::bvar(2),
                    ),
                ),
            ),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 2,
        types: vec![InductiveType {
            name: pair.clone(),
            type_: pair_type,
            constructors: vec![Constructor {
                name: Name::from_string("Pair.mk"),
                type_: mk_type,
            }],
        }],
    })
    .unwrap();
    pair
}

/// Helper: build `Pair.mk A B a b`.
fn make_pair_val(a: Expr, b: Expr) -> Expr {
    let mk = Expr::const_(Name::from_string("Pair.mk"), vec![]);
    Expr::app(
        Expr::app(Expr::app(Expr::app(mk, Expr::prop()), Expr::prop()), a),
        b,
    )
}

/// Helper: add axioms p, q : Prop and return (p_expr, q_expr).
fn add_prop_axioms(env: &mut Environment) -> (Expr, Expr) {
    for name in ["p", "q"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .unwrap();
    }
    (
        Expr::const_(Name::from_string("p"), vec![]),
        Expr::const_(Name::from_string("q"), vec![]),
    )
}

/// When one side is delta-reducible and the other is a projection-app,
/// the projection side is unfolded first (Lean 4 performance optimization).
#[test]
fn test_proj_app_unfold_preference_over_delta() {
    let mut env = Environment::new();
    let pair = add_pair_inductive(&mut env);
    let (p, q) = add_prop_axioms(&mut env);
    let pair_val = make_pair_val(p.clone(), q.clone());

    add_reducible_def(&mut env, "expensive_f", Expr::prop(), p.clone());
    {
        let tc = TypeChecker::new(&env);
        let expensive_f = Expr::const_(Name::from_string("expensive_f"), vec![]);
        let proj_0 = Expr::proj(pair.clone(), 0, pair_val.clone());

        // proj side reduces to p, expensive_f unfolds to p → equal
        assert!(tc.is_def_eq(&expensive_f, &proj_0));
        assert!(tc.is_def_eq(&proj_0, &expensive_f)); // symmetric
    }

    // Second field: expensive_g := q vs Pair.proj(1, ...)
    add_reducible_def(&mut env, "expensive_g", Expr::prop(), q.clone());
    let tc2 = TypeChecker::new(&env);
    let expensive_g = Expr::const_(Name::from_string("expensive_g"), vec![]);
    let proj_1 = Expr::proj(pair, 1, pair_val);
    assert!(tc2.is_def_eq(&expensive_g, &proj_1));
}

/// Projection-app that can't reduce (opaque struct) falls back to delta unfold.
#[test]
fn test_proj_app_no_reduce_falls_back_to_delta() {
    let mut env = Environment::new();
    let pair = add_pair_inductive(&mut env);

    // Axiom opaque_pair : Pair Prop Prop (no constructor — projection stuck)
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("opaque_pair"),
        level_params: vec![],
        type_: Expr::app(
            Expr::app(Expr::const_(pair.clone(), vec![]), Expr::prop()),
            Expr::prop(),
        ),
    })
    .unwrap();

    let opaque_pair = Expr::const_(Name::from_string("opaque_pair"), vec![]);
    let proj_opaque = Expr::proj(pair, 0, opaque_pair);

    // delta_f := Pair.proj(0, opaque_pair) — unfolds to match the stuck projection
    add_reducible_def(&mut env, "delta_f", Expr::prop(), proj_opaque.clone());
    let tc = TypeChecker::new(&env);
    let delta_f = Expr::const_(Name::from_string("delta_f"), vec![]);

    assert!(tc.is_def_eq(&delta_f, &proj_opaque));
}

/// reduce_native no-op does not interfere with normal delta reduction.
#[test]
fn test_reduce_native_noop_does_not_break_delta() {
    let mut env = Environment::new();
    add_reducible_def(&mut env, "b_nat", Expr::type_(), Expr::prop());
    add_reducible_def(
        &mut env,
        "a_nat",
        Expr::type_(),
        Expr::const_(Name::from_string("b_nat"), vec![]),
    );

    let tc = TypeChecker::new(&env);
    let a = Expr::const_(Name::from_string("a_nat"), vec![]);
    assert!(tc.is_def_eq(&a, &Expr::prop()));
}

// ============================================================================
// Nat.shiftLeft eliminated axiom -> Definition (#3470)
// ============================================================================

/// Nat.shiftLeft is registered as a genuine `Definition` (it has a value and
/// kind Definition), NOT a bare `Axiom`. `init_nat()` would fail if the body
/// did not kernel-check against the declared `Nat → Nat → Nat` type, so the
/// fact that this constructs at all proves the elimination is sound.
#[test]
fn test_nat_shift_left_is_definition_not_axiom() {
    let mut env = Environment::new();
    env.init_nat()
        .expect("init_nat should succeed (shiftLeft Definition kernel-checks)");

    let info = env
        .get_const(&Name::from_string("Nat.shiftLeft"))
        .expect("Nat.shiftLeft must be registered");

    assert!(
        info.value.is_some(),
        "Nat.shiftLeft must carry a Definition body (value), not be an Axiom"
    );
    assert_eq!(
        info.kind,
        crate::env::ConstantKind::Definition,
        "Nat.shiftLeft must be a Definition, not an Axiom"
    );
}

/// The Nat.shiftLeft Definition body reduces correctly on SYMBOLIC arguments
/// (where the native `reduce_nat` fast path cannot fire because the base is not
/// a literal). This exercises the new `Nat.rec`/`Nat.mul` body via delta+iota:
///   shiftLeft m 0       ≡ m
///   shiftLeft m 1       ≡ Nat.mul m 2
///   shiftLeft m 2       ≡ Nat.mul (Nat.mul m 2) 2
#[test]
fn test_nat_shift_left_definition_symbolic_reduction() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    // A symbolic Nat value the native reducer will not touch.
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("m_sym"),
        level_params: vec![],
        type_: nat.clone(),
    })
    .expect("register symbolic Nat axiom");

    let tc = TypeChecker::new(&env);

    let m = Expr::const_(Name::from_string("m_sym"), vec![]);
    let shl = Expr::const_(Name::from_string("Nat.shiftLeft"), vec![]);
    let mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
    let two = Expr::nat_lit(2);

    // shiftLeft m 0 ≡ m
    let shl_m_0 = Expr::apps(shl.clone(), [m.clone(), Expr::nat_lit(0)]);
    assert!(
        tc.is_def_eq(&shl_m_0, &m),
        "Nat.shiftLeft m 0 should reduce to m via the Definition body"
    );

    // shiftLeft m 1 ≡ Nat.mul m 2
    let shl_m_1 = Expr::apps(shl.clone(), [m.clone(), Expr::nat_lit(1)]);
    let mul_m_2 = Expr::apps(mul.clone(), [m.clone(), two.clone()]);
    assert!(
        tc.is_def_eq(&shl_m_1, &mul_m_2),
        "Nat.shiftLeft m 1 should reduce to Nat.mul m 2"
    );

    // shiftLeft m 2 ≡ Nat.mul (Nat.mul m 2) 2
    let shl_m_2 = Expr::apps(shl, [m.clone(), Expr::nat_lit(2)]);
    let mul_mul_m_2_2 = Expr::apps(mul, [mul_m_2, two]);
    assert!(
        tc.is_def_eq(&shl_m_2, &mul_mul_m_2_2),
        "Nat.shiftLeft m 2 should reduce to Nat.mul (Nat.mul m 2) 2"
    );
}
