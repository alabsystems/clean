// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Scaling tests for type checker operations.
//!
//! These tests are scaling regression guards that verify infer_type, WHNF, and
//! related operations do not exceed O(n) time complexity.
//!
//! Threshold rationale (see #1871): for input sizes differing by 4x, an O(n)
//! algorithm gives ratio ≈ 4, O(n²) gives ratio = 16. The threshold of 16.0
//! rejects O(n²) behavior while allowing 4x headroom for constant overhead and
//! measurement noise on small inputs.
//!
//! # Serial Execution
//!
//! These tests use wall-clock timing and take a shared test lock to prevent
//! resource contention from causing false failures. See #1045 for details.
//!
//! # Timeout Handling
//!
//! Scaling tests use `run_with_timeout` to fail fast (30s) rather than hitting the
//! cargo wrapper's 10-minute timeout. See #1045. Non-scaling correctness tests
//! (like `test_whnf_quot_reduction_fires`) don't need timeout handling.

use std::time::{Duration, Instant};

/// Samples taken per measurement; the fastest is kept.
///
/// One sample is not enough: the public-release gate runs these tests as five
/// concurrent shard processes (`run_public_release_libraries.sh`, `--jobs 5`),
/// and `serial_test_guard()` is a process-local Mutex, so it provides no
/// exclusion there. A single sample can then be inflated by an unrelated
/// process and fail a threshold the algorithm actually meets — observed
/// 2026-07-29 on `test_infer_type_scaling_nested_lambda`, which reported 48.8x
/// under load and 2.1x/linear when re-run alone.
const SCALING_SAMPLES: usize = 3;

/// Time `f` `samples` times and return the fastest run with its last value.
///
/// Contention can only ever ADD time, so the minimum is the sample least
/// contaminated by scheduling noise. The threshold is unchanged, so a genuine
/// complexity regression still fails: it would be slow in every sample.
fn min_nanos<T>(samples: usize, mut f: impl FnMut() -> T) -> (u128, T) {
    let mut best = u128::MAX;
    let mut value = None;
    for _ in 0..samples.max(1) {
        let start = Instant::now();
        let produced = f();
        best = best.min(start.elapsed().as_nanos());
        value = Some(produced);
    }
    (best, value.expect("at least one sample"))
}

use super::helpers::{
    build_nested_beta_redex, build_nested_lambda, build_nested_lets, build_nested_pi,
    run_with_timeout, SCALING_TEST_TIMEOUT,
};
use super::*;

/// Build a wide application chain: (((f a₀) a₁) ... aₙ)
/// where f : Type → Type → ... → Type
fn build_wide_app_with_env(width: usize) -> (Environment, Expr) {
    use crate::env::Declaration;

    let mut env = Environment::new();

    // Build the type: Type → Type → ... → Type
    let mut f_type = Expr::type_();
    for _ in 0..width {
        f_type = Expr::pi(BinderInfo::Default, Expr::type_(), f_type);
    }

    // Add f as an axiom
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("f"),
        level_params: vec![],
        type_: f_type,
    })
    .unwrap();

    // Build the application: f Prop Prop ... Prop
    let mut app = Expr::const_(Name::from_string("f"), vec![]);
    for _ in 0..width {
        app = Expr::app(app, Expr::prop());
    }

    (env, app)
}

#[test]
fn test_infer_type_scaling_nested_lambda() {
    let _serial = crate::test_utils::serial_test_guard();
    run_with_timeout(
        SCALING_TEST_TIMEOUT,
        "test_infer_type_scaling_nested_lambda",
        || {
            // Verify infer_type scales linearly with nested lambda depth.
            // Using small sizes to avoid stack overflow in debug mode.
            // Note: infer_type is more recursive than expr operations (type of lambda
            // recurses into body after inferring domain type).
            let env = Environment::new();
            let sizes = [5usize, 10, 20];
            let mut times = Vec::new();

            for &n in &sizes {
                let expr = build_nested_lambda(n);
                let (nanos, ty) = min_nanos(SCALING_SAMPLES, || {
                    let tc = TypeChecker::new(&env);
                    tc.infer_type(&expr).unwrap()
                });
                times.push(nanos);

                // Verify the result is a Pi type (lambda of Type→Type has Pi type)
                assert!(
                    matches!(&ty.kind, ExprKind::Pi(..)),
                    "infer_type of nested lambda should return Pi type, got {:?}",
                    ty.kind
                );
            }

            // For O(n), 4x input should give ~4x time. O(n²) gives 16x.
            // Threshold 16.0 rejects O(n²); see #1871.
            // Use max(1) to avoid division by zero on fast hardware (#1785).
            let ratio = times[2] as f64 / times[0].max(1) as f64;
            assert!(
                ratio < 16.0,
                "infer_type (nested lambda) scaling regression: \
                 4x input gave {ratio:.1}x time (threshold: 16x, O(n²) = 16x). \
                 sizes: {sizes:?}, times: {times:?}"
            );
        },
    );
}

#[test]
fn test_infer_type_scaling_nested_pi() {
    let _serial = crate::test_utils::serial_test_guard();
    run_with_timeout(
        SCALING_TEST_TIMEOUT,
        "test_infer_type_scaling_nested_pi",
        || {
            // Verify infer_type scales linearly with nested Pi type depth.
            // Using small sizes to avoid stack overflow in debug mode.
            let env = Environment::new();
            let sizes = [5usize, 10, 20];
            let mut times = Vec::new();

            for &n in &sizes {
                let expr = build_nested_pi(n);
                let (nanos, ty) = min_nanos(SCALING_SAMPLES, || {
                    let tc = TypeChecker::new(&env);
                    tc.infer_type(&expr).unwrap()
                });
                times.push(nanos);

                // Nested Pi type has Sort type
                assert!(
                    matches!(&ty.kind, ExprKind::Sort(..)),
                    "infer_type of nested Pi should return Sort, got {:?}",
                    ty.kind
                );
            }

            let ratio = times[2] as f64 / times[0].max(1) as f64;
            assert!(
                ratio < 16.0,
                "infer_type (nested pi) scaling regression: \
                 4x input gave {ratio:.1}x time (threshold: 16x, O(n²) = 16x). \
                 sizes: {sizes:?}, times: {times:?}"
            );
        },
    );
}

#[test]
fn test_infer_type_scaling_wide_app() {
    let _serial = crate::test_utils::serial_test_guard();
    run_with_timeout(
        SCALING_TEST_TIMEOUT,
        "test_infer_type_scaling_wide_app",
        || {
            // Verify infer_type scales linearly with wide application chains.
            // Using smaller sizes to avoid stack overflow.
            let sizes = [5usize, 10, 20];
            let mut times = Vec::new();

            for &n in &sizes {
                let (env, expr) = build_wide_app_with_env(n);
                let (nanos, ty) = min_nanos(SCALING_SAMPLES, || {
                    let tc = TypeChecker::new(&env);
                    tc.infer_type(&expr).unwrap()
                });
                times.push(nanos);

                // Wide application f Prop Prop ... Prop with f : Type→...→Type
                // should reduce to Type when fully applied
                assert!(
                    matches!(&ty.kind, ExprKind::Sort(..)),
                    "infer_type of fully-applied wide app should return Sort, got {:?}",
                    ty.kind
                );
            }

            let ratio = times[2] as f64 / times[0].max(1) as f64;
            assert!(
                ratio < 16.0,
                "infer_type (wide app) scaling regression: \
                 4x input gave {ratio:.1}x time (threshold: 16x, O(n²) = 16x). \
                 sizes: {sizes:?}, times: {times:?}"
            );
        },
    );
}

#[test]
fn test_infer_type_with_cert_scaling() {
    let _serial = crate::test_utils::serial_test_guard();
    run_with_timeout(
        SCALING_TEST_TIMEOUT,
        "test_infer_type_with_cert_scaling",
        || {
            // Verify infer_type_with_cert scales linearly.
            // This tests the certified path which produces proof certificates.
            // Using small sizes to avoid stack overflow in debug mode.
            let env = Environment::new();
            let sizes = [5usize, 10, 20];
            let mut times = Vec::new();

            for &n in &sizes {
                let expr = build_nested_lambda(n);

                let (nanos, (ty, _cert)) = min_nanos(SCALING_SAMPLES, || {
                    let tc = TypeChecker::new(&env);
                    tc.infer_type_with_cert(&expr).unwrap()
                });

                // Certified path should agree with non-certified: nested lambda has Pi type
                assert!(
                    matches!(&ty.kind, ExprKind::Pi(..)),
                    "infer_type_with_cert of nested lambda should return Pi type, got {:?}",
                    ty.kind
                );
                times.push(nanos);
            }

            let ratio = times[2] as f64 / times[0].max(1) as f64;
            assert!(
                ratio < 16.0,
                "infer_type_with_cert scaling regression: \
                 4x input gave {ratio:.1}x time (threshold: 16x, O(n²) = 16x). \
                 sizes: {sizes:?}, times: {times:?}"
            );
        },
    );
}

// ============================================================================
// WHNF Scaling Tests
// ============================================================================

/// Build a stuck application chain: (f a₁ a₂ ... aₙ) where f is not a lambda.
/// These test the O(1) early exit optimization in try_iota_reduction (#949).
fn build_stuck_app_chain(width: usize) -> (Environment, Expr) {
    use crate::env::Declaration;

    let mut env = Environment::new();

    // Add f as an opaque axiom (cannot reduce further)
    // f : Type → Type → ... → Type
    let mut f_type = Expr::type_();
    for _ in 0..width {
        f_type = Expr::pi(BinderInfo::Default, Expr::type_(), f_type);
    }

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("f"),
        level_params: vec![],
        type_: f_type,
    })
    .unwrap();

    // Build the stuck application: f Prop Prop ... Prop
    let mut app = Expr::const_(Name::from_string("f"), vec![]);
    for _ in 0..width {
        app = Expr::app(app, Expr::prop());
    }

    (env, app)
}

/// Fast steady-state reductions can quantize to 0ns after integer averaging.
/// The scaling assertions clamp a 0ns baseline to 1ns so coarse timer
/// resolution still enforces the regression guard instead of skipping it.
fn measure_whnf_avg_nanos(tc: &TypeChecker<'_>, expr: &Expr) -> u128 {
    use std::hint::black_box;

    // Warm up caches so we're measuring the steady-state path.
    let _ = tc.whnf(expr);

    let mut iters: u32 = 0;
    let start = Instant::now();
    while iters < 20_000 && start.elapsed() < Duration::from_millis(2) {
        let _ = black_box(tc.whnf(black_box(expr)));
        iters += 1;
    }

    if iters == 0 {
        return 0;
    }

    start.elapsed().as_nanos() / iters as u128
}

/// Build a chain of reducible definitions: cₙ := cₙ₋₁ := ... := c₀ := Prop
/// Each cᵢ has type Type (Sort 1) since Prop : Type.
fn build_delta_chain(width: usize) -> (Environment, Expr) {
    use crate::env::Declaration;

    assert!(width > 0, "delta chain width must be > 0");

    let mut env = Environment::new();

    for i in 0..width {
        let name = Name::from_string(&format!("c{i}"));
        let value = if i == 0 {
            Expr::prop()
        } else {
            Expr::const_(Name::from_string(&format!("c{}", i - 1)), vec![])
        };

        // Prop : Type, so all cᵢ have type Type (Sort 1)
        env.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            value,
            is_reducible: true,
        })
        .unwrap();
    }

    let expr = Expr::const_(Name::from_string(&format!("c{}", width - 1)), vec![]);
    (env, expr)
}

#[test]
fn test_whnf_scaling_stuck_app_chain() {
    let _serial = crate::test_utils::serial_test_guard();
    run_with_timeout(
        SCALING_TEST_TIMEOUT,
        "test_whnf_scaling_stuck_app_chain",
        || {
            // Scaling behavior of WHNF on stuck application chains.
            //
            // For stuck app chain `(f a₁ a₂ ... aₙ)` where f is an axiom (not a lambda):
            // - WHNF on App recursively calls WHNF on the function
            // - This creates n recursive WHNF calls: whnf(f aₙ) → whnf(f aₙ₋₁) → ... → whnf(f)
            // - Each sub-expression is tried against iota/quot reduction
            //
            // With identity caching (#1584): each sub-expression is cached after first
            // visit (including stuck results where result == input), so subsequent
            // references hit the cache. Expected complexity: O(n) or O(n log n).
            let sizes = [3usize, 6, 12];
            let mut times = Vec::new();

            for &n in &sizes {
                let (env, expr) = build_stuck_app_chain(n);
                let tc = TypeChecker::new(&env);

                let start = Instant::now();
                let result = tc.whnf(&expr);
                let elapsed = start.elapsed();
                times.push(elapsed.as_nanos());

                // Stuck app chain (axiom head) cannot reduce — whnf returns the same App
                assert!(
                    matches!(&result.kind, ExprKind::App(..)),
                    "whnf of stuck app chain should return App (no reduction), got {:?}",
                    result.kind
                );
            }

            // With identity caching, stuck app chains should be O(n) to O(n log n).
            // For O(n): 4x input gives ~4x time. Threshold 16x rejects O(n²); see #1871.
            let ratio = times[2] as f64 / times[0].max(1) as f64;
            assert!(
                ratio < 16.0,
                "whnf (stuck app chain) scaling regression: \
                 4x input gave {ratio:.1}x time (threshold: 16x, O(n²) = 16x). \
                 sizes: {sizes:?}, times: {times:?}"
            );
        },
    );
}

#[test]
fn test_whnf_scaling_beta_reduction() {
    let _serial = crate::test_utils::serial_test_guard();
    run_with_timeout(
        SCALING_TEST_TIMEOUT,
        "test_whnf_scaling_beta_reduction",
        || {
            // Verify WHNF beta reduction scales linearly with redex depth.
            let env = Environment::new();
            let sizes = [5usize, 10, 20];
            let mut times = Vec::new();

            for &n in &sizes {
                let expr = build_nested_beta_redex(n);
                let tc = TypeChecker::new(&env);

                let start = Instant::now();
                let result = tc.whnf(&expr);
                let elapsed = start.elapsed();
                times.push(elapsed.as_nanos());

                // Beta reduction of ((λ.λ...λ.bvar(0)) Prop ... Prop) should fully
                // reduce to Prop (Sort(zero)). Each Prop arg substitutes for a bvar,
                // and bvar(0) in the innermost lambda receives the final Prop.
                assert_eq!(
                    result,
                    Expr::prop(),
                    "whnf of nested beta redex (depth={n}) should reduce to Prop, got {:?}",
                    result
                );
            }

            let ratio = times[2] as f64 / times[0].max(1) as f64;
            assert!(
                ratio < 16.0,
                "whnf (beta reduction) scaling regression: \
                 4x input gave {ratio:.1}x time (threshold: 16x, O(n²) = 16x). \
                 sizes: {sizes:?}, times: {times:?}"
            );
        },
    );
}

#[test]
fn test_whnf_scaling_let_reduction() {
    let _serial = crate::test_utils::serial_test_guard();
    run_with_timeout(
        SCALING_TEST_TIMEOUT,
        "test_whnf_scaling_let_reduction",
        || {
            // Verify WHNF let reduction scales linearly with nesting depth.
            let env = Environment::new();
            let sizes = [5usize, 10, 20];
            let mut times = Vec::new();

            for &n in &sizes {
                let expr = build_nested_lets(n);
                let tc = TypeChecker::new(&env);

                let result = tc.whnf(&expr);
                // Full-suite runs can introduce enough scheduler noise that a
                // single let-reduction sample trips the O(n^2) ratchet even
                // though the isolated steady-state path is linear. Measure the
                // warmed average, matching the other fast WHNF scaling guards.
                let avg_nanos = measure_whnf_avg_nanos(&tc, &expr);
                times.push(avg_nanos);

                // Nested let := Prop in ... bvar(0) should fully reduce to Prop.
                // bvar(0) refers to the innermost let, which binds Prop.
                assert_eq!(
                    result,
                    Expr::prop(),
                    "whnf of nested lets (depth={n}) should reduce to Prop, got {:?}",
                    result
                );
            }

            let ratio = times[2] as f64 / times[0].max(1) as f64;
            assert!(
                ratio < 16.0,
                "whnf (let reduction) scaling regression: \
                 4x input gave {ratio:.1}x time (threshold: 16x, O(n²) = 16x). \
                 sizes: {sizes:?}, times: {times:?}"
            );
        },
    );
}

#[test]
fn test_whnf_scaling_delta_chain() {
    let _serial = crate::test_utils::serial_test_guard();
    run_with_timeout(
        SCALING_TEST_TIMEOUT,
        "test_whnf_scaling_delta_chain",
        || {
            // Verify WHNF delta reduction scales linearly with definitional depth.
            let sizes = [5usize, 10, 20];
            let mut times = Vec::new();

            for &n in &sizes {
                let (env, expr) = build_delta_chain(n);
                let tc = TypeChecker::new(&env);

                let avg_nanos = measure_whnf_avg_nanos(&tc, &expr);
                times.push(avg_nanos);
            }

            // Use max(1) to avoid division by zero on fast hardware (#2958).
            // When both times[0] and times[2] are 0 (sub-nanosecond), ratio = 0 → passes.
            // When only times[0] is 0, ratio is checked against threshold normally.
            let ratio = times[2] as f64 / times[0].max(1) as f64;
            assert!(
                ratio < 16.0,
                "whnf (delta chain) scaling regression: \
                 4x input gave {ratio:.1}x time (threshold: 16x, O(n²) = 16x). \
                 sizes: {sizes:?}, times: {times:?}"
            );
        },
    );
}

// ============================================================================
// Iota Reduction Scaling Tests
// ============================================================================

/// Build a Nat value as nested succ applications: succ (succ (... (succ zero)...))
/// REQUIRES: `env.init_nat()` was called before this function.
fn build_nat_value(n: usize) -> Expr {
    let mut e = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    for _ in 0..n {
        e = Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), e);
    }
    e
}

/// Build a Nat.rec application that reduces via iota reduction.
/// Nat.rec motive zero_case succ_case n
fn build_nat_rec_app(n: usize, env: &mut Environment) -> Expr {
    // Ensure Nat is initialized
    env.init_nat().unwrap_or(());

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    // motive : Nat → Type
    let motive = Expr::lam(BinderInfo::Default, nat.clone(), Expr::type_());

    // zero_case : motive zero (= Type)
    let zero_case = Expr::prop();

    // succ_case : (n : Nat) → motive n → motive (succ n)
    // We just return Type for simplicity
    let succ_case = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(BinderInfo::Default, Expr::type_(), Expr::type_()),
    );

    // The major premise: a Nat value
    let nat_val = build_nat_value(n);

    // Nat.rec : {motive : Nat → Sort u} → motive zero → ((n : Nat) → motive n → motive (succ n)) → (t : Nat) → motive t
    let nat_rec = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );

    // Apply: Nat.rec motive zero_case succ_case nat_val
    Expr::app(
        Expr::app(Expr::app(Expr::app(nat_rec, motive), zero_case), succ_case),
        nat_val,
    )
}

#[test]
fn test_whnf_scaling_iota_reduction() {
    let _serial = crate::test_utils::serial_test_guard();
    run_with_timeout(
        SCALING_TEST_TIMEOUT,
        "test_whnf_scaling_iota_reduction",
        || {
            // Verify iota reduction (Nat.rec) scales linearly with the Nat value size.
            // This tests the actual iota reduction path when the recursor fires.
            let sizes = [2usize, 4, 8];
            let mut times = Vec::new();

            for &n in &sizes {
                let mut env = Environment::new();
                let expr = build_nat_rec_app(n, &mut env);
                let tc = TypeChecker::new(&env);

                let avg_nanos = measure_whnf_avg_nanos(&tc, &expr);
                times.push(avg_nanos);
            }

            // Nat.rec has O(n) complexity for n succs (one reduction per succ).
            // Threshold 16x rejects O(n²); see #1871.
            // Use max(1) to avoid division by zero on fast hardware (#2958).
            let ratio = times[2] as f64 / times[0].max(1) as f64;
            assert!(
                ratio < 16.0,
                "whnf (iota reduction) scaling regression: \
                 4x input gave {ratio:.1}x time (threshold: 16x, O(n²) = 16x). \
                 sizes: {sizes:?}, times: {times:?}"
            );
        },
    );
}

// ============================================================================
// Quot Reduction Scaling Tests
// ============================================================================

/// Build an expression that triggers quot reduction: Quot.lift f h (Quot.mk r a)
/// This tests the successful reduction path (Quot.lift applied to Quot.mk).
fn build_quot_lift_app(env: &mut Environment) -> Expr {
    env.init_quot();
    env.init_eq().unwrap_or(());

    // We need a simple quotient setup:
    // α = Prop, r = (λ _ _, True), β = Prop
    // f = (λ _, True), h = proof that f respects r (doesn't matter, won't be checked)
    // q = Quot.mk r True

    let prop = Expr::prop();
    let true_const = Expr::const_(Name::from_string("True"), vec![]);

    // r : Prop → Prop → Prop
    // Just use (λ _ _, True) - any equivalence relation works
    let r = Expr::lam(
        BinderInfo::Default,
        prop.clone(),
        Expr::lam(BinderInfo::Default, prop.clone(), true_const.clone()),
    );

    // f : Prop → Prop
    // Just identity-ish: (λ _, True)
    let f = Expr::lam(BinderInfo::Default, prop.clone(), true_const.clone());

    // h : proof that f respects r
    // Type: ∀ a b : Prop, r a b → f a = f b
    // We use True.intro as a placeholder (won't actually be checked during WHNF)
    let h = Expr::const_(Name::from_string("True.intro"), vec![]);

    // Build Quot.mk.{1} Prop r True : Quot Prop r
    let quot_mk = Expr::const_(
        Name::from_string("Quot.mk"),
        vec![Level::succ(Level::zero())],
    );
    let q = Expr::app(
        Expr::app(Expr::app(quot_mk, prop.clone()), r.clone()),
        true_const.clone(),
    );

    // Build Quot.lift.{1,1} Prop r Prop f h q
    let quot_lift = Expr::const_(
        Name::from_string("Quot.lift"),
        vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
    );

    // Quot.lift {α} {r} {β} f h q
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(Expr::app(quot_lift, prop.clone()), r), prop),
                f,
            ),
            h,
        ),
        q,
    )
}

/// Build a nested Quot.lift application chain.
/// This tests that quot reduction with nested applications scales linearly.
fn build_nested_quot_lift(depth: usize, env: &mut Environment) -> Expr {
    env.init_quot();
    env.init_true_false().unwrap_or(());

    let prop = Expr::prop();
    let true_const = Expr::const_(Name::from_string("True"), vec![]);

    // r : Prop → Prop → Prop
    let r = Expr::lam(
        BinderInfo::Default,
        prop.clone(),
        Expr::lam(BinderInfo::Default, prop.clone(), true_const.clone()),
    );

    // f : Prop → Prop
    let f = Expr::lam(
        BinderInfo::Default,
        prop.clone(),
        Expr::from_kind(ExprKind::BVar(0)),
    );

    // h : proof placeholder
    let h = Expr::const_(Name::from_string("True.intro"), vec![]);

    // Start with Quot.mk r True
    let quot_mk = Expr::const_(
        Name::from_string("Quot.mk"),
        vec![Level::succ(Level::zero())],
    );
    let mut q = Expr::app(
        Expr::app(Expr::app(quot_mk.clone(), prop.clone()), r.clone()),
        true_const.clone(),
    );

    // Wrap in depth layers of Quot.lift
    let quot_lift = Expr::const_(
        Name::from_string("Quot.lift"),
        vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
    );

    for _ in 0..depth {
        // Wrap f to return a Quot instead of just Prop
        let f_quot = Expr::lam(
            BinderInfo::Default,
            prop.clone(),
            Expr::app(
                Expr::app(Expr::app(quot_mk.clone(), prop.clone()), r.clone()),
                Expr::from_kind(ExprKind::BVar(0)),
            ),
        );

        // Quot.lift {Prop} {r} {Quot Prop r} f_quot h q
        let quot_type = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Quot"), vec![Level::succ(Level::zero())]),
                prop.clone(),
            ),
            r.clone(),
        );

        q = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::app(quot_lift.clone(), prop.clone()), r.clone()),
                        quot_type,
                    ),
                    f_quot,
                ),
                h.clone(),
            ),
            q,
        );
    }

    // Final lift to extract the value
    q = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(quot_lift.clone(), prop.clone()), r.clone()),
                    prop.clone(),
                ),
                f.clone(),
            ),
            h.clone(),
        ),
        q,
    );

    q
}

#[test]
fn test_whnf_scaling_quot_reduction() {
    let _serial = crate::test_utils::serial_test_guard();
    run_with_timeout(
        SCALING_TEST_TIMEOUT,
        "test_whnf_scaling_quot_reduction",
        || {
            // Verify quot reduction scales linearly with nesting depth.
            // NOTE: The early exit optimization (O(1) head check before arg collection)
            // is already tested by test_whnf_scaling_stuck_app_chain - any stuck
            // application goes through both try_iota_reduction and try_quot_reduction.
            let sizes = [1usize, 2, 4];
            let mut times = Vec::new();

            for &n in &sizes {
                let mut env = Environment::new();
                let expr = build_nested_quot_lift(n, &mut env);
                let tc = TypeChecker::new(&env);

                let avg_nanos = measure_whnf_avg_nanos(&tc, &expr);
                times.push(avg_nanos);
            }

            // Quot reduction should scale linearly with depth.
            // Threshold 16x rejects O(n²); see #1871.
            // Use max(1) to avoid division by zero on fast hardware (#2958).
            let ratio = times[2] as f64 / times[0].max(1) as f64;
            assert!(
                ratio < 16.0,
                "whnf (quot reduction) scaling regression: \
                 4x input gave {ratio:.1}x time (threshold: 16x, O(n²) = 16x). \
                 sizes: {sizes:?}, times: {times:?}"
            );
        },
    );
}

#[test]
fn test_whnf_quot_reduction_fires() {
    // Verify that quot reduction actually fires when Quot.lift is applied to Quot.mk.
    // This is a correctness test, not a scaling test - no timeout needed.
    let mut env = Environment::new();
    env.init_quot();
    env.init_true_false().unwrap();

    let expr = build_quot_lift_app(&mut env);
    let tc = TypeChecker::new(&env);

    let result = tc.whnf(&expr);

    // The result should be True (f applied to the unwrapped value)
    assert_eq!(
        result,
        Expr::const_(Name::from_string("True"), vec![]),
        "Quot.lift f h (Quot.mk r a) should reduce to f a. Got: {result:?}"
    );
}

/// Depth-sweep benchmark for #1325: verifies infer_type on nested lambdas
/// does not exhibit quadratic scaling at depths 2,4,8,16,32,64.
///
/// The original bug showed 3.8x slowdown vs Lean 4 at depth 16, caused by
/// missing O(1) metadata guards in substitution. The fix (ExprMeta packed u64,
/// ExprFolderOpt with should_descend guards) should bring doubling ratios to
/// approximately 2x (linear) rather than 4x (quadratic).
#[test]
fn test_infer_type_nested_lambda_depth_sweep() {
    let _serial = crate::test_utils::serial_test_guard();
    run_with_timeout(
        SCALING_TEST_TIMEOUT,
        "test_infer_type_nested_lambda_depth_sweep",
        || {
            let env = Environment::new();
            let depths = [2usize, 4, 8, 16, 32, 64];
            let mut times_ns = Vec::new();

            for &d in &depths {
                let expr = build_nested_lambda(d);
                let mut best_ns = u128::MAX;
                for _ in 0..3 {
                    let tc = TypeChecker::new(&env);
                    let start = Instant::now();
                    let ty = tc.infer_type(&expr).unwrap();
                    let elapsed_ns = start.elapsed().as_nanos();
                    best_ns = best_ns.min(elapsed_ns);

                    assert!(
                        matches!(&ty.kind, ExprKind::Pi(..)),
                        "depth {d}: infer_type should return Pi type, got {:?}",
                        ty.kind
                    );
                }
                times_ns.push(best_ns);
            }

            // Print timing table for benchmark evidence (captured in test output).
            // We keep the best of a few samples to reduce scheduler noise on the
            // shared worktree while still catching asymptotic regressions.
            eprintln!("\n--- #1325 depth-sweep benchmark ---");
            eprintln!("| Depth | Time (ns) | Doubling ratio |");
            eprintln!("|-------|-----------|----------------|");
            for (i, &d) in depths.iter().enumerate() {
                let ratio = if i > 0 {
                    times_ns[i] as f64 / times_ns[i - 1].max(1) as f64
                } else {
                    f64::NAN
                };
                eprintln!("| {d:5} | {t:>9} | {ratio:>14.2} |", t = times_ns[i]);
            }

            // Acceptance: depth 64 vs depth 2 — for O(n), 32x input gives ~32x time.
            // For O(n²), 32x input gives ~1024x time. Threshold 200x rejects O(n²)
            // while allowing generous constant overhead for small inputs.
            let ratio_64_2 = times_ns[5] as f64 / times_ns[0].max(1) as f64;
            eprintln!("Overall ratio (64/2): {ratio_64_2:.1}x");
            assert!(
                ratio_64_2 < 200.0,
                "#1325 scaling regression: depth 64 vs 2 gave {ratio_64_2:.1}x \
                 (threshold: 200x). O(n²) would give ~1024x. \
                 depths: {depths:?}, times: {times_ns:?}"
            );
        },
    );
}
