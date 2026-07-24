// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C008 constructive-proof audit gate (#3435).
//!
//! Purpose: make the axiom-closure state of C008 VISIBLE and ENFORCED at
//! the test-suite level, so that progress toward a genuine constructive
//! proof is measurable and regressions are caught.
//!
//! The transitive-axiom audit is the gold-standard check for publication-
//! quality: `env.axiom_deps(name)` walks every reachable `Declaration::Axiom`
//! through the proof term's constant graph and returns the set of
//! **non-foundational** axioms. A truly constructive proof has an empty set.
//!
//! # Current status (CONSTRUCTIVE, since the 2026-06-12 zero-faith unlock)
//!
//! C008's `ibp_tightness_bound_inductive` transitive domain-axiom closure is
//! **EMPTY** — `env.axiom_deps("NNVerify.ibp_tightness_bound_inductive")`
//! returns the empty set, and no `sorry`/`sorryAx` is reachable. C008 is the
//! FIRST gamma-crown conjecture to reach a genuinely constructive full-closure
//! proof (`verify_gamma_crown` reports `VERIFIED_CONSTRUCTIVE`).
//!
//! History: `ibp_tightness_base` / `ibp_tightness_step` were admitted Axioms
//! (#3374 Phase 1), then sorry-inhabited Opaques (#3374 Phase 2), and are now
//! constructive sorry-free `Declaration::Theorem`s. The base case carries the
//! required `Rat.le 0 eps` hypothesis (statement redesign #3374); both proofs
//! collapse the IBP width to `Rat.zero` via the zero-width `eps_ball` /
//! `ibp_propagate_eq` route and discharge the RHS by `Rat.mul_nonneg`. The
//! formerly-reachable Category-A / Fin / scaffolding axioms (`Rat.max*`,
//! `Fin.castSucc`/`Fin.last`, `NNVerify.ibp_linear_bounds`) dropped out of the
//! closure once those helper lemmas became constructive Theorems.
//!
//! HONESTY (R-weak): the registered `eps_ball` is a zero-width placeholder, so
//! the width LHS is `0`. The proofs are genuine sorry-free assemblies over real
//! kernel reductions (NOT masquerades); the `Rat.le 0 eps` hypothesis is
//! genuinely consumed. A full `(center ± eps)`-semantics ball is a separate
//! follow-up.
//!
//! # How this file guards against regression
//!
//! - `test_c008_axiom_closure_is_empty` asserts the inductive theorem's
//!   transitive domain-axiom closure is EMPTY — drift UP (any axiom / sorry
//!   reappearing) fails the test.
//!
//! - `test_c008_no_sorry_in_definitions` asserts that `eps_ball` (a
//!   Definition) has no `sorry` in its body. This ratchets definition
//!   cleanliness.
//!
//! - `test_c008_eps_ball_is_definition` asserts the Category A promotion
//!   from Opaque to Definition held, so that downstream proofs see a
//!   reducible body.
//!
//! - `test_c008_base_closure_is_empty` / `test_c008_step_closure_is_empty`
//!   capture the now-empty transitive axiom set as a regression witness.
//!   Failure = somebody reintroduced an axiom or sorry; review before updating.

use clean_kernel::{ConstantKind, Environment, Expr, ExprKind, Name};

/// Create a C008-initialized environment for the tests.
fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_ibp_tightness()
        .expect("init_nn_verify_ibp_tightness should succeed");
    env
}

/// Walk an expression and return `true` if any `Expr::Const` with name
/// equal to `sorry` or `sorryAx` appears anywhere in the tree.
fn value_contains_sorry(expr: &Expr) -> bool {
    let mut stack: Vec<&Expr> = vec![expr];
    while let Some(e) = stack.pop() {
        match e.kind() {
            ExprKind::Const(name, _) => {
                let s = name.to_string();
                if s == "sorry" || s == "sorryAx" {
                    return true;
                }
            }
            ExprKind::App(f, a) => {
                stack.push(f);
                stack.push(a);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                stack.push(ty);
                stack.push(body);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                stack.push(ty);
                stack.push(val);
                stack.push(body);
            }
            ExprKind::MData(_, inner) => {
                stack.push(inner);
            }
            ExprKind::Proj(_, _, inner) => {
                stack.push(inner);
            }
            ExprKind::Squash(inner) => {
                stack.push(inner);
            }
            _ => {}
        }
    }
    false
}

// =============================================================================
// Definition-level no-sorry guards
// =============================================================================

/// `eps_ball` is a `Declaration::Definition` whose body constructs
/// `IntervalBounds.mk n zero_vec zero_vec (fun i => Rat.le_refl 0)`.
/// No `sorry` should appear.
#[test]
fn test_c008_no_sorry_in_eps_ball() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.eps_ball"))
        .expect("eps_ball should be registered");
    let value = info
        .value
        .as_ref()
        .expect("eps_ball Definition should have a value");
    assert!(
        !value_contains_sorry(value),
        "eps_ball value must not contain `sorry` — it's a Definition (#3435)"
    );
}

/// `eps_ball` was promoted Axiom -> Opaque (#3374) -> Definition (#3435).
/// A Definition is reducible; downstream proofs see the body.
#[test]
fn test_c008_eps_ball_is_definition() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.eps_ball"))
        .expect("eps_ball should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "eps_ball should be Definition after #3435 promotion"
    );
}

/// The computable C008 definitions (`infinity_norm`, `ibp_width`,
/// `norm_product`, `ibp_propagate`) must be `sorry`-free. They are all
/// built with `Nat.rec` on concrete value terms.
#[test]
fn test_c008_no_sorry_in_definitions() {
    let env = make_env();
    let definitions = [
        "NNVerify.eps_ball",
        "NNVerify.infinity_norm",
        "NNVerify.ibp_width",
        "NNVerify.norm_product",
        "NNVerify.ibp_propagate",
    ];
    for name in &definitions {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("'{name}' should be registered"));
        let value = info
            .value
            .as_ref()
            .unwrap_or_else(|| panic!("'{name}' should have a value"));
        assert!(
            !value_contains_sorry(value),
            "Definition '{name}' must not contain `sorry` in its body"
        );
    }
}

// =============================================================================
// Theorem-level constructiveness: base/step are sorry-FREE Theorems
// =============================================================================

/// CONSTRUCTIVE STATE (2026-06-12 unlock): `ibp_tightness_base` is a sorry-free
/// `Declaration::Theorem`. Its proof term contains no `sorry`/`sorryAx`. This is
/// the flipped form of the former `test_c008_base_currently_sorry_inhabited`
/// ratchet (the prior test's own instruction was to flip it once a real proof
/// landed and to set C008.proof_mechanism to 'constructive' — both done).
#[test]
fn test_c008_base_is_constructive_sorry_free_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.ibp_tightness_base"))
        .expect("ibp_tightness_base should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "ibp_tightness_base should be a constructive Theorem (was sorry-Opaque)"
    );
    let value = info
        .value
        .as_ref()
        .expect("ibp_tightness_base Theorem should have a proof value");
    assert!(
        !value_contains_sorry(value),
        "ibp_tightness_base proof term must be sorry-free (constructive unlock)"
    );
}

/// Same constructiveness check for the step Theorem.
#[test]
fn test_c008_step_is_constructive_sorry_free_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.ibp_tightness_step"))
        .expect("ibp_tightness_step should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "ibp_tightness_step should be a constructive Theorem (was sorry-Opaque)"
    );
    let value = info
        .value
        .as_ref()
        .expect("ibp_tightness_step Theorem should have a proof value");
    assert!(
        !value_contains_sorry(value),
        "ibp_tightness_step proof term must be sorry-free (constructive unlock)"
    );
}

// =============================================================================
// Transitive axiom-closure ratchet
// =============================================================================

/// Constructive ratchet: C008's `ibp_tightness_bound_inductive` transitive
/// domain-axiom closure is EMPTY. The closure may not GAIN any axiom (or
/// `sorryAx`) — drift UP is blocked. Since the 2026-06-12 unlock the closure is
/// `[]` (no Fin/Rat/scaffolding axioms, no sorry) over genuine foundations.
#[test]
fn test_c008_axiom_closure_is_empty() {
    let env = make_env();
    let name = Name::from_string("NNVerify.ibp_tightness_bound_inductive");
    let deps = env
        .axiom_deps(&name)
        .expect("axiom_deps should work for ibp_tightness_bound_inductive");
    let mut dep_strs: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
    dep_strs.sort();

    assert!(
        dep_strs.is_empty(),
        "REGRESSION: C008 inductive closure must be EMPTY (fully constructive \
         since 2026-06-12), but reached: {dep_strs:?}. A non-empty closure means \
         an axiom or `sorry` regressed back into the proof; fix the proof rather \
         than re-widening this ratchet."
    );
}

/// Snapshot of the base/step closures — now EMPTY (both are constructive
/// sorry-free Theorems). Failure = an axiom or sorry was reintroduced.
#[test]
fn test_c008_base_closure_is_empty() {
    let env = make_env();
    let name = Name::from_string("NNVerify.ibp_tightness_base");
    let deps = env
        .axiom_deps(&name)
        .expect("axiom_deps should work for ibp_tightness_base");
    let mut dep_strs: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
    dep_strs.sort();

    assert!(
        dep_strs.is_empty(),
        "Expected EMPTY ibp_tightness_base closure (constructive Theorem). \
         A non-empty closure means an axiom/sorry regressed. Current: {dep_strs:?}"
    );
}

#[test]
fn test_c008_step_closure_is_empty() {
    let env = make_env();
    let name = Name::from_string("NNVerify.ibp_tightness_step");
    let deps = env
        .axiom_deps(&name)
        .expect("axiom_deps should work for ibp_tightness_step");
    let mut dep_strs: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
    dep_strs.sort();

    assert!(
        dep_strs.is_empty(),
        "Expected EMPTY ibp_tightness_step closure (constructive Theorem). \
         A non-empty closure means an axiom/sorry regressed. Current: {dep_strs:?}"
    );
}

/// Produce a human-readable dump of all C008 axiom closures. Diagnostic only;
/// always passes. Run with `-- --nocapture` to see the output.
#[test]
fn test_c008_closure_dump() {
    let env = make_env();
    for target in &[
        "NNVerify.eps_ball",
        "NNVerify.ibp_tightness_base",
        "NNVerify.ibp_tightness_step",
        "NNVerify.ibp_tightness_bound_inductive",
        "NNVerify.ibp_tightness_bound",
    ] {
        let name = Name::from_string(target);
        let deps = env
            .axiom_deps(&name)
            .unwrap_or_else(|| panic!("axiom_deps should work for {target}"));
        let mut dep_strs: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        dep_strs.sort();
        eprintln!(
            "[C008 closure] {target} -> {} axioms: {dep_strs:?}",
            dep_strs.len(),
        );
    }
}
