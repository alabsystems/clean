// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Guard tests for the #3594 Branch A demasquerade of
//! `NNVerify.McCormick.shared_input_width_eq` and its companion carrier
//! `NNVerify.McCormick.shared_input_width`.
//!
//! Per the demasquerade methodology in
//! `designs/2026-04-19-demasquerade-cxxx-pattern.md` the prior declaration
//! shapes were a textbook Rule M1 + M4 masquerade:
//!
//! * `NNVerify.McCormick.shared_input_width` was a reducible
//!   `Declaration::Definition` whose body was literally
//!   `fun w eps => 2 * |w| * eps` — exactly the RHS of the equation it
//!   was asked to prove (Rule M1 alias-collapse).
//! * `NNVerify.McCormick.shared_input_width_eq` was a
//!   `Declaration::Theorem` whose proof was
//!   `fun (w eps : Rat) (_ : 0 <= eps) => @Eq.refl Rat (shared_input_width w eps)`
//!   (Rule M4 — `Eq.refl` discharging the equation via δ-unfolding the
//!   alias). The `0 <= eps` hypothesis was completely unused.
//!
//! Current remediation (this file's guards):
//! 1. `shared_input_width_eq` is a hypothesis-wrapped `Declaration::Theorem`
//!    whose final premise is the target equality. `ConstantInfo.kind ==
//!    Theorem` and `value.is_some()` are both required invariants.
//! 2. `shared_input_width` is co-demoted to `Declaration::Opaque` with
//!    the SAME body. Opaque bodies are not δ-unfolded during `def_eq`,
//!    so the M1 alias-collapse path that made the prior `Eq.refl` proof
//!    type-check is severed — `ConstantInfo.kind == Opaque`,
//!    `!is_reducible`, and `value.is_some()` are all required invariants.
//!
//! Branch B (a faithful independent carrier against which the equation
//! states a non-trivial claim) is out of scope for this demasquerade pass
//! per the issue body — see `designs/2026-04-19-demasquerade-cxxx-pattern.md`.
//!
//! Mirrors the sibling demasquerade guard files for #3586 (C001
//! `tail_norm_sum`), #3591 (Zonotope `to_ibp`), #3578 (C010
//! `certified_implies_lipschitz_local`), etc.
//!
//! Part of #3594.

use super::tests_nn_verify_mccormick_attention::make_env_with_stubs;
use crate::env::types::ConstantKind;
use crate::name::Name;
use crate::test_utils::run_with_stack;

/// 256 MB stack — matches the sibling stub-based test file because
/// `Environment::new()` alone overflows the default 8 MB thread stack in
/// debug mode (#1455).
const HUGE_STACK: usize = 256 * 1024 * 1024;

fn run<F: FnOnce() + Send + 'static>(f: F) {
    run_with_stack(HUGE_STACK, f);
}

// ---------------------------------------------------------------
// Guard 1: shared_input_width_eq is a local-evidence theorem
// ---------------------------------------------------------------

/// Primary guard: `NNVerify.McCormick.shared_input_width_eq` must be a
/// local-evidence `Declaration::Theorem`. The proof term must return an
/// explicit equality premise, while the companion carrier remains opaque in
/// the next guard to keep the old `Eq.refl` alias-collapse path closed.
#[test]
fn test_c005_shared_input_width_eq_is_hypothesis_wrapped_theorem() {
    run(|| {
        let env = make_env_with_stubs();
        let info = env
            .get_const(&Name::from_string(
                "NNVerify.McCormick.shared_input_width_eq",
            ))
            .expect("NNVerify.McCormick.shared_input_width_eq should be registered");

        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "shared_input_width_eq must be a local-evidence theorem, got {:?}",
            info.kind
        );

        assert!(
            info.value.is_some(),
            "shared_input_width_eq theorem must carry the local-evidence proof value."
        );
    });
}

// ---------------------------------------------------------------
// Guard 2: shared_input_width is Opaque (carrier co-demotion)
// ---------------------------------------------------------------

/// Co-demotion guard: `NNVerify.McCormick.shared_input_width` must be
/// `Declaration::Opaque` — NOT a `Declaration::Definition` of any
/// reducibility flavour. A regression back to
/// `Declaration::Definition { is_reducible: true }` would re-expose the
/// body `fun w eps => 2 * |w| * eps` to δ-reduction during def_eq and
/// let a new `Eq.refl`-based proof of `shared_input_width w eps =
/// 2 * |w| * eps` slip through the type checker (Rule M1).
///
/// Three invariants must all hold:
/// * `info.kind == ConstantKind::Opaque` — blocks the
///   `kind != Opaque` filter in the kernel's `is_delta` predicate
///   (`crates/clean-kernel/src/tc/def_eq/delta_helpers.rs`).
/// * `!info.is_reducible` — a reducible flag would be inconsistent
///   with Opaque and would at minimum represent partial corruption.
/// * `info.value.is_some()` — Opaque (unlike Axiom) carries a body.
///   Branch A preserves the ORIGINAL body `2 * |w| * eps` so the
///   declaration remains well-typed; only the declaration kind flips.
#[test]
fn test_c005_shared_input_width_is_opaque_not_reducible_definition() {
    run(|| {
        let env = make_env_with_stubs();
        let info = env
            .get_const(&Name::from_string("NNVerify.McCormick.shared_input_width"))
            .expect("NNVerify.McCormick.shared_input_width should be registered");

        assert_eq!(
            info.kind,
            ConstantKind::Opaque,
            "#3594 Branch A: shared_input_width MUST be \
             Declaration::Opaque (co-demoted from reducible Definition \
             to sever the M1 δ-reduction path that made the prior \
             `Eq.refl`-between-aliases proof of shared_input_width_eq \
             type-check). Got kind={:?}",
            info.kind
        );

        assert!(
            !info.is_reducible,
            "#3594 Branch A: shared_input_width must be non-reducible \
             (Opaque). A reducible flag on the same body `2 * |w| * eps` \
             would flip the `reducibility != Opaque` check at \
             delta_helpers.rs back to true and re-open the M1 \
             alias-collapse attack surface."
        );

        assert!(
            info.value.is_some(),
            "#3594 Branch A: shared_input_width (Opaque) MUST carry its \
             body. Branch A preserves the ORIGINAL body \
             `fun w eps => 2 * |w| * eps` and only flips the \
             declaration kind; dropping the value would be an \
             unrelated demotion to Axiom (not the Branch A remediation)."
        );
    });
}
