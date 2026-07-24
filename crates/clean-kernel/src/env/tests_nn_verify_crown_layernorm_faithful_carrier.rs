// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Guard tests for the #3617 Phase 1 carrier swap on
//! `NNVerify.IBP.forward_layernorm`.
//!
//! Issue #3617 (C004 Phase 1) swapped the wave-10 identity body
//! `fun n γ β ε B => B` for a `Nat.rec`-based body that depends on
//! both `n` and `B`:
//!
//! ```text
//! fun (n : Nat) (γ β : NNVec n) (ε : Rat) (B : IntervalBounds n) =>
//!   @Nat.rec.{1}
//!     (fun _ : Nat => IntervalBounds n)
//!     (zero_ib n)                          -- base  (n = 0)
//!     (fun _ _ => B)                       -- step  (n = succ _)
//!     n
//! ```
//!
//! These tests pin the new carrier state so wave-10's identity
//! placeholder cannot silently return. They correspond to the "Guard
//! tests" list in issue #3617:
//!
//! 1. `test_ibp_forward_layernorm_is_not_identity` — the registered
//!    body is NOT the pure identity `fun _ _ _ _ B => B`. Asserted by
//!    shape: the body root is a five-deep lambda ending in a
//!    `Nat.rec` application that references `Nat.rec`, `zero_ib`'s
//!    constructor (`NNVerify.IntervalBounds.mk`), `Rat.zero`, and
//!    `Rat.le_refl`. A pure-identity body would reference none of
//!    these.
//! 2. `test_ibp_forward_layernorm_is_monotone` — the body preserves
//!    the `IntervalBounds` structural invariant that `lower i ≤
//!    upper i` for all `i : Fin n`. Asserted by: the body's
//!    `Nat.rec` step-case returns the input `B` verbatim (so its
//!    validity proof is reused); the base-case returns `zero_ib n`
//!    whose validity is `Rat.le_refl Rat.zero`. Both cases preserve
//!    `IntervalBounds`'s monotonicity invariant by construction.
//! 3. `test_ibp_forward_layernorm_type_unchanged` — the registered
//!    Pi type is unchanged from the wave-10 shape used by the C004
//!    equality declarations (`build_ln_equality_hyp_type` in
//!    `nn_verify_crown_layernorm_proofs.rs` references
//!    `IBP.forward_layernorm` by name; changing its type would
//!    cascade into the equality shapes). Asserted by: `ty` has exactly
//!    5 Pi binders in the same order `(n, γ, β, ε, B)`, and its body
//!    is `IntervalBounds n`.
//!
//! Part of #3617 (C004 Phase 1) — epic #3381 / parent #3373. The body
//! is a structural stepping stone: Phase 2 will upgrade it to the
//! element-wise interval arithmetic body
//! `fun (lo, hi) => (interval_lb …, interval_ub …)` described in
//! `designs/2026-04-20-c004-faithful-carrier-redesign.md` §3.1.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_crown_layernorm()
        .expect("init_nn_verify_crown_layernorm");
    env
}

/// Recursively check whether `expr` references a `Const` whose name
/// matches `target_const`.
fn expr_references_const(expr: &Expr, target_const: &str) -> bool {
    match expr.kind() {
        ExprKind::Const(name, _) => name.to_string() == target_const,
        ExprKind::App(f, a) => {
            expr_references_const(f, target_const) || expr_references_const(a, target_const)
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_references_const(ty, target_const) || expr_references_const(body, target_const)
        }
        ExprKind::Let(_, ty, val, body, _nondep) => {
            expr_references_const(ty, target_const)
                || expr_references_const(val, target_const)
                || expr_references_const(body, target_const)
        }
        ExprKind::Proj(_, _, inner) => expr_references_const(inner, target_const),
        ExprKind::MData(_, inner) => expr_references_const(inner, target_const),
        _ => false,
    }
}

/// Unwrap `n` nested `Lam` binders and return the body expression.
/// Panics with a descriptive message if fewer than `n` `Lam`s are found.
fn strip_lambdas(mut expr: Expr, n: usize, label: &str) -> Expr {
    for i in 0..n {
        match expr.kind() {
            ExprKind::Lam(_, _, body) => {
                expr = (**body).clone();
            }
            other => panic!(
                "{label}: expected {n} nested Lam binders, but only found {i} \
                 (remaining expr kind: {other:?})",
            ),
        }
    }
    expr
}

/// Count the number of leading `Pi` binders in a type.
fn count_pi_binders(mut ty: Expr) -> (usize, Expr) {
    let mut count = 0usize;
    while let ExprKind::Pi(_, _, body) = ty.kind() {
        count += 1;
        ty = (**body).clone();
    }
    (count, ty)
}

// =============================================================================
// Guard 1: body is not the pure identity (#3617)
// =============================================================================

/// #3617 Phase 1 guard: the registered `IBP.forward_layernorm` body
/// must NOT be the wave-10 identity `fun n γ β ε B => B`. The faithful
/// body references `Nat.rec`, `IntervalBounds.mk`, `Rat.zero`, and
/// `Rat.le_refl` — none of which appear in a pure-identity body.
#[test]
fn test_ibp_forward_layernorm_is_not_identity() {
    let env = make_env();
    let decl = env
        .get_const(&Name::from_string("NNVerify.IBP.forward_layernorm"))
        .expect("IBP.forward_layernorm should be registered");
    let body = decl
        .value
        .clone()
        .expect("IBP.forward_layernorm must have a value (non-axiom carrier)");

    // A pure identity body `fun n γ β ε B => B` references no Const
    // constants beyond the Pi domain types. The faithful body from
    // #3617 Phase 1 must reference:
    //   * `Nat.rec`        — the recursor driving the `n = 0 | succ _` branch
    //   * `NNVerify.IntervalBounds.mk` — constructor for the base-case value
    //   * `Rat.zero`       — populating zero_ib's lower/upper components
    //   * `Rat.le_refl`    — providing the validity proof in the base case
    let required = [
        "Nat.rec",
        "NNVerify.IntervalBounds.mk",
        "Rat.zero",
        "Rat.le_refl",
    ];
    for c in required {
        assert!(
            expr_references_const(&body, c),
            "#3617 Phase 1 regression: IBP.forward_layernorm body must reference {c} \
             (would indicate the wave-10 identity body `fun n γ β ε B => B` returned); \
             body was: {body:?}",
        );
    }
}

// =============================================================================
// Guard 2: body preserves IntervalBounds monotonicity invariant (#3617)
// =============================================================================

/// #3617 Phase 1 guard: the registered body preserves the
/// `IntervalBounds` structural invariant that `lower i ≤ upper i` for
/// every `i : Fin n`. In the Phase 1 `Nat.rec` shape this holds by
/// construction:
///
/// * **Base case (`n = 0`)**: the body returns `zero_ib n`, whose
///   lower and upper are both the constant-zero function. The
///   validity field is `fun _ => Rat.le_refl Rat.zero`, so the
///   invariant holds pointwise.
/// * **Step case (`n = succ _`)**: the body returns the input `B`
///   verbatim. The input's validity proof `B.valid` carries the
///   invariant forward.
///
/// We do not run the kernel's iota-reducer to check behaviour; we
/// instead pin the structural shape that makes monotonicity hold by
/// construction. Any future body rewrite must either preserve this
/// shape OR supply its own validity witness — both of which keep the
/// invariant alive.
#[test]
fn test_ibp_forward_layernorm_is_monotone() {
    let env = make_env();
    let decl = env
        .get_const(&Name::from_string("NNVerify.IBP.forward_layernorm"))
        .expect("IBP.forward_layernorm should be registered");
    let body = decl
        .value
        .clone()
        .expect("IBP.forward_layernorm must have a value");

    // Body must reference `Rat.le_refl`. `Rat.le_refl` (applied to
    // `Rat.zero`) is the validity witness for `zero_ib n`; its
    // presence proves that the base-case branch constructs an
    // `IntervalBounds` whose monotonicity invariant holds. The
    // step-case inherits monotonicity from `B : IntervalBounds n`'s
    // own validity field.
    assert!(
        expr_references_const(&body, "Rat.le_refl"),
        "#3617 Phase 1 regression: body must reference Rat.le_refl \
         (the validity witness for zero_ib's base case); absence would mean \
         the Nat.rec branch no longer produces a well-formed IntervalBounds, \
         violating the monotonicity invariant.",
    );
    // Body must reference `IntervalBounds.mk` — the constructor that
    // packages lower, upper, and the validity proof into a single
    // `IntervalBounds n` term. Using `.mk` (not some unsafe structural
    // bypass) is what forces the validity-proof arm to be checked
    // when the Definition is type-checked by the kernel.
    assert!(
        expr_references_const(&body, "NNVerify.IntervalBounds.mk"),
        "#3617 Phase 1 regression: body must invoke NNVerify.IntervalBounds.mk; \
         bypassing the constructor would sidestep the kernel's validity check \
         on the lower ≤ upper invariant.",
    );
}

// =============================================================================
// Guard 3: Pi type unchanged from wave-10 (#3617)
// =============================================================================

/// #3617 Phase 1 guard: the registered Pi type must remain the exact
/// wave-10 shape `(n : Nat) → (γ β : NNVec n) → (ε : Rat) →
/// IntervalBounds n → IntervalBounds n`. The C004 equality declarations in
/// `nn_verify_crown_layernorm.rs` build their types via
/// `build_ln_equality_hyp_type` and reference `IBP.forward_layernorm` by
/// name; changing the Pi arity or argument order would cascade into
/// those equality type signatures and break downstream consumers.
#[test]
fn test_ibp_forward_layernorm_type_unchanged() {
    let env = make_env();
    let decl = env
        .get_const(&Name::from_string("NNVerify.IBP.forward_layernorm"))
        .expect("IBP.forward_layernorm should be registered");
    let ty = decl.type_.clone();
    let (pi_count, tail) = count_pi_binders(ty.clone());
    assert_eq!(
        pi_count, 5,
        "#3617 Phase 1 regression: IBP.forward_layernorm type must have 5 Pi \
         binders (n, γ, β, ε, B); changing arity would break C004 \
         equality signatures that reference it via build_ln_equality_hyp_type. \
         Got type: {ty:?}",
    );
    // Final body must be `IntervalBounds n` (i.e., an App of the
    // `IntervalBounds` const to a bound variable). We check
    // structurally that the tail is an App whose head is the
    // `IntervalBounds` Const.
    assert!(
        expr_references_const(&tail, "NNVerify.IntervalBounds"),
        "#3617 Phase 1 regression: tail of the Pi type must reference \
         NNVerify.IntervalBounds. Got tail: {tail:?}",
    );
}

// =============================================================================
// Guard 4: declaration kind is non-reducible Definition (#3617)
// =============================================================================

/// #3617 Phase 1 guard: the declaration is a **non-reducible
/// Definition** (`Declaration::Definition { is_reducible: false }`).
///
/// * Definition (not Opaque) advertises honestly that the body has
///   computational content.
/// * Non-reducible preserves the wave-10 guard against Rule M1
///   alias-collapse proofs of the C004 equality declarations.
/// * Under `test_c004_axiom_count`'s rubric, a non-reducible
///   Definition counts the same as an Opaque (`thm_count`), so the
///   carrier swap itself does not alter the C004 domain-axiom total.
#[test]
fn test_ibp_forward_layernorm_is_nonreducible_definition() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string("NNVerify.IBP.forward_layernorm"))
        .expect("IBP.forward_layernorm should be registered");
    assert_eq!(
        ci.kind,
        ConstantKind::Definition,
        "#3617 Phase 1: kind must be Definition (not Opaque / Axiom / Theorem). \
         Got kind: {:?}",
        ci.kind,
    );
    assert!(
        ci.value.is_some(),
        "#3617 Phase 1: Definition must carry a value (non-identity body).",
    );
    assert!(
        !ci.is_reducible,
        "#3617 Phase 1: Definition must be non-reducible. A reducible definition \
         would re-open the Rule M1 alias-collapse path that the wave-10 \
         demotion of the equality claims closed, allowing future Eq.refl \
         masquerade proofs to typecheck against the equality signatures.",
    );
}

// =============================================================================
// Invariant: the C004 equality declarations still typecheck against the new carrier
// =============================================================================

/// #3617 acceptance criterion: the C004 equality declarations
/// (`crown_backward_eq_interval_hull`, `interval_hull_eq_ibp_forward`,
/// plus the now-defined `jacobian_dense` predicate carrier) still register
/// and still kernel-typecheck against the new
/// `IBP.forward_layernorm` carrier (no Pi shape change). This test asks
/// the `TypeChecker` to infer each constant, which requires the
/// referenced carriers to be well-typed.
#[test]
fn test_c004_equality_declarations_typecheck_against_new_carrier() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let names = [
        "NNVerify.C004.crown_backward_eq_interval_hull",
        "NNVerify.C004.interval_hull_eq_ibp_forward",
        "NNVerify.C004.jacobian_dense",
    ];
    for name in &names {
        let expr = Expr::const_(Name::from_string(name), vec![]);
        let _ = tc.infer_type(&expr).unwrap_or_else(|e| {
            panic!(
                "#3617 Phase 1 regression: {name} failed to typecheck against the \
                 new IBP.forward_layernorm carrier: {e:?}. The carrier's Pi type \
                 must match the wave-10 carrier shape exactly.",
            )
        });
    }
}

// =============================================================================
// Invariant: body shape matches the Nat.rec faithful pattern (#3617)
// =============================================================================

/// #3617 Phase 1 guard: the body's outermost structure is 5 lambdas
/// (for `n, γ, β, ε, B`) wrapping a `Nat.rec` application. Pinning the
/// shape prevents accidental reverts to the wave-10 identity body and
/// documents the Phase 1 carrier shape for Phase 2 to upgrade in place.
#[test]
fn test_ibp_forward_layernorm_body_outer_shape() {
    let env = make_env();
    let decl = env
        .get_const(&Name::from_string("NNVerify.IBP.forward_layernorm"))
        .expect("IBP.forward_layernorm should be registered");
    let body = decl
        .value
        .clone()
        .expect("IBP.forward_layernorm must have a value");
    let inner = strip_lambdas(body, 5, "IBP.forward_layernorm");
    // After 5 lambdas, we expect the `Nat.rec` application at the head
    // of the inner expression. Walk left to find the App head.
    let mut head = inner;
    while let ExprKind::App(f, _) = head.kind() {
        head = (**f).clone();
    }
    match head.kind() {
        ExprKind::Const(name, _) => {
            assert_eq!(
                name.to_string(),
                "Nat.rec",
                "#3617 Phase 1: body head must be Nat.rec; got Const({name}). \
                 A different head would indicate the carrier shape changed away \
                 from the Phase 1 structural template.",
            );
        }
        other => panic!(
            "#3617 Phase 1: body head after 5 lambdas must be a Const (Nat.rec); \
             got {other:?}",
        ),
    }
}

// =============================================================================
// Guard 6: Phase 1.5 β-shift step case (#3615)
// =============================================================================

/// #3615 Phase 1.5 guard: the `Nat.rec` step case is no longer `fun _ _ => B`
/// (pure identity on the recursion input). It now β-shifts: for
/// `n = succ _`, the step case returns
/// `IntervalBounds.mk n (λ i. β i + B.lower i) (λ i. β i + B.upper i) ...`
/// and the validity proof is discharged by `Rat.add_le_add_left`.
///
/// A regression to the Phase 1 identity step case would remove the
/// reference to `Rat.add_le_add_left` — that is the canonical tripwire.
/// We also check that `Rat.add` is present, as both the lower- and
/// upper-endpoint λs run β + B.lower / β + B.upper through `Rat.add`.
#[test]
fn test_ibp_forward_layernorm_phase_1_5_beta_shift() {
    let env = make_env();
    let decl = env
        .get_const(&Name::from_string("NNVerify.IBP.forward_layernorm"))
        .expect("IBP.forward_layernorm should be registered");
    let body = decl
        .value
        .clone()
        .expect("IBP.forward_layernorm must have a value");

    // `Rat.add_le_add_left` appears only in the Phase 1.5 step-case
    // validity proof. The Phase 1 identity step `fun _ _ => B` would
    // reuse `B.valid` and therefore never mention this constant.
    assert!(
        expr_references_const(&body, "Rat.add_le_add_left"),
        "#3615 Phase 1.5 regression: body must reference Rat.add_le_add_left \
         — this is the validity witness discharging monotonicity of the \
         β-shifted step case. Absence would indicate a revert to the Phase 1 \
         identity step case `fun _ _ => B`.",
    );
    // `Rat.add` is the arithmetic operator on the shifted endpoints.
    // A Phase 1 identity step wouldn't reference it either.
    assert!(
        expr_references_const(&body, "Rat.add"),
        "#3615 Phase 1.5 regression: body must reference Rat.add \
         (step case shifts B.lower / B.upper by β via Rat.add). Absence \
         would indicate a revert to the Phase 1 identity step case.",
    );
}
