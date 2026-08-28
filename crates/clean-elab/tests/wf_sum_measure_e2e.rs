// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **WF phase 3 — a SUM measure over SEVERAL parameters.** parse → elaborate →
//! kernel-check → register → COMPUTE, for the class phase 2 refused.
//!
//! The motivating program is the two-branch **subtractive** Euclid. It
//! decreases in NEITHER parameter — `gcdSub (a-b) b` shrinks `a`,
//! `gcdSub a (b-a)` shrinks `b` — only in `a + b`, so it needs a measure that
//! mentions both. Phase 2 refused that as "lexicographic / packed"; the
//! kernel never did (`clean-kernel/tests/wf_sum_measure_kernel_probe.rs`), and
//! `wf_recursion::sum_measure` now lowers it.
//!
//! HONESTY RULES, as in the R3/R5 batteries: every ADMIT is paired with a
//! refused MUTATION at the same layer, and every refusal asserts its reason.
//!
//! # The fixture that must be REFUSED, and why it is here
//!
//! A subtractive Euclid needs **two** zero guards. With only `b = 0` guarded,
//!
//! ```lean
//! def gcdSubBad (a b : Nat) : Nat :=
//!   if h : b = 0 then a
//!   else if a ≥ b then gcdSubBad (a - b) b else gcdSubBad a (b - a)
//! ```
//!
//! is **non-terminating**: at `a = 0, b > 0` the else-branch is
//! `gcdSubBad 0 (b - 0)` = `gcdSubBad 0 b`, an infinite loop — and
//! `gcdSubBad 12 18` reaches exactly that state (`12 18 → 12 6 → 6 6 → 0 6 →
//! 0 6 → …`). Its sum measure genuinely does not decrease, so it MUST be
//! refused, and it is: at the DECREASE, not at a syntactic gate. That is the
//! adversarial control this widening most needed, and it is pinned below.

use clean_elab::{
    elaborate_decl, elaborate_decl_and_register, preprocess_decl_with_context, ElabError,
    ElabResult, FileContext,
};
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, ExprKind};
use clean_parser::parse_file;

/// Subtractive Euclid, correctly guarded. Two parameters, a measure mentioning
/// BOTH, and two recursive calls that shrink different arguments.
const GCD_SUB: &str = "def gcdSub (a b : Nat) : Nat := \
     if ha : a = 0 then b \
     else if hb : b = 0 then a \
     else if hge : a >= b then gcdSub (a - b) b else gcdSub a (b - a)\n\
     termination_by a + b";

/// The same program with the `a = 0` guard MISSING — non-terminating.
const GCD_SUB_UNGUARDED: &str = "def gcdSubBad (a b : Nat) : Nat := \
     if h : b = 0 then a \
     else if hge : a >= b then gcdSubBad (a - b) b else gcdSubBad a (b - a)\n\
     termination_by a + b";

fn elab_one(env: &Environment, source: &str) -> Result<ElabResult, ElabError> {
    let decls = parse_file(source).expect("source should parse");
    assert_eq!(decls.len(), 1, "fixture must be exactly one declaration");
    let mut file_ctx = FileContext::new();
    let processed = preprocess_decl_with_context(&decls[0], &mut file_ctx);
    elaborate_decl(env, &processed)
}

fn register_one(env: &mut Environment, source: &str) -> Result<ElabResult, ElabError> {
    let decls = parse_file(source).expect("source should parse");
    assert_eq!(decls.len(), 1, "fixture must be exactly one declaration");
    let mut file_ctx = FileContext::new();
    let processed = preprocess_decl_with_context(&decls[0], &mut file_ctx);
    elaborate_decl_and_register(env, &processed)
}

/// Is the definition value a `WellFounded.fix` application (under any leading
/// parameter lambdas)? Structural — a `Debug`-string match cannot answer this.
fn head_is_wf_fix(value: &Expr) -> bool {
    let mut cursor = value.clone();
    loop {
        match cursor.kind() {
            ExprKind::Lam(_, _, body) => cursor = Expr::clone(body),
            ExprKind::MData(_, inner) => cursor = Expr::clone(inner),
            _ => break,
        }
    }
    matches!(
        cursor.get_app_fn().kind(),
        ExprKind::Const(name, _) if *name == Name::from_string("WellFounded.fix")
    )
}

/// Assert `name` registered as a kernel-checked, sorry-free `WellFounded.fix`
/// definition whose transitive axiom closure is foundational-only.
fn assert_wf_definition_registered(env: &Environment, name: &str) {
    let constant = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should be registered after kernel check"));
    let value = constant
        .value
        .as_ref()
        .unwrap_or_else(|| panic!("{name} should keep its definition value"));
    assert!(!value.has_sorry(), "{name} must be sorry-free");
    assert!(
        head_is_wf_fix(value),
        "{name} must be lowered through WellFounded.fix"
    );
    let foundational = ["propext", "Quot.sound", "Classical.choice"];
    let closure = env
        .axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should have an axiom closure"));
    let offending: Vec<String> = closure
        .iter()
        .map(ToString::to_string)
        .filter(|ax| !foundational.contains(&ax.as_str()))
        .collect();
    assert!(
        offending.is_empty(),
        "{name} must have a foundational-only axiom closure, got extra {offending:?}"
    );
}

fn env_with_gcd_sub() -> Environment {
    let mut env = Environment::with_prelude();
    register_one(&mut env, GCD_SUB)
        .expect("phase 3: subtractive `gcdSub` must elaborate and kernel-verify");
    env
}

// ═════════════ the acceptance: subtractive gcd elaborates ═════════════

#[test]
fn test_subtractive_gcd_elaborates_kernel_verifies_and_is_axiom_free() {
    let env = env_with_gcd_sub();
    assert_wf_definition_registered(&env, "gcdSub");
}

/// **THE TARGET: `gcdSub 12 18 = 6`.** Closed, so the `WellFounded.fix`
/// application must actually grind through `Acc.rec` and `Nat.accNatLt` on a
/// measure that mentions BOTH parameters. This is the computation claim, not a
/// typing claim.
#[test]
fn test_subtractive_gcd_12_18_computes_to_6() {
    let mut env = env_with_gcd_sub();
    register_one(&mut env, "theorem gcdSub_12_18 : gcdSub 12 18 = 6 := rfl")
        .expect("`gcdSub 12 18` must COMPUTE to 6 by kernel reduction");

    // MUTATION CONTROL: the computation is a decision, not a rubber stamp.
    assert!(
        register_one(
            &mut env,
            "theorem gcdSub_12_18_bad : gcdSub 12 18 = 5 := rfl"
        )
        .is_err(),
        "`gcdSub 12 18 = 5` must be REFUSED — otherwise the evidence above is vacuous"
    );
    assert!(
        env.get_const(&Name::from_string("gcdSub_12_18_bad"))
            .is_none(),
        "a refused theorem must register nothing"
    );
}

/// More closed values, both argument orders, and the boundary cases the two
/// zero guards exist for. Each is `rfl`, so each is a kernel reduction.
#[test]
fn test_subtractive_gcd_closed_values_and_identities() {
    let mut env = env_with_gcd_sub();
    for (index, source) in [
        "theorem gs0 : gcdSub 18 12 = 6 := rfl",
        "theorem gs1 : gcdSub 7 13 = 1 := rfl",
        "theorem gs2 : gcdSub 0 5 = 5 := rfl",
        "theorem gs3 : gcdSub 5 0 = 5 := rfl",
        "theorem gs4 : gcdSub 0 0 = 0 := rfl",
        "theorem gs5 : gcdSub 48 18 = 6 := rfl",
        "theorem gs6 : gcdSub 270 192 = 6 := rfl",
    ]
    .into_iter()
    .enumerate()
    {
        register_one(&mut env, source)
            .unwrap_or_else(|e| panic!("closed value #{index} (`{source}`) must compute: {e}"));
    }

    // MUTATION CONTROL at the same layer.
    assert!(
        register_one(&mut env, "theorem gs_bad : gcdSub 270 192 = 7 := rfl").is_err(),
        "a wrong closed value must be refused"
    );
}

/// It agrees with the phase-2 modulo `gcd` on closed inputs — two lowerings,
/// one function.
#[test]
fn test_subtractive_and_modulo_gcd_agree() {
    let mut env = env_with_gcd_sub();
    register_one(
        &mut env,
        "def gcdMod (a b : Nat) : Nat := if h : 0 < b then gcdMod b (a % b) else a\n\
         termination_by b",
    )
    .expect("the phase-2 one-parameter lowering must still work");
    for source in [
        "theorem agree0 : gcdSub 270 192 = gcdMod 270 192 := rfl",
        "theorem agree1 : gcdSub 48 18 = gcdMod 48 18 := rfl",
    ] {
        register_one(&mut env, source).unwrap_or_else(|e| panic!("`{source}`: {e}"));
    }
}

// ══════════ the adversarial controls: a sum that does NOT decrease ══════════

/// **THE CONTROL THAT MATTERS.** The unguarded subtractive Euclid is a
/// non-terminating program whose sum measure does not decrease. It must be
/// REFUSED — and refused at the DECREASE, with the fail-closed diagnostic,
/// never registered.
#[test]
fn test_the_unguarded_subtractive_gcd_is_refused_at_the_decrease() {
    let mut env = Environment::with_prelude();
    let err = elab_one(&env, GCD_SUB_UNGUARDED).expect_err(
        "`gcdSubBad 0 b` loops forever, so its `a + b` measure does NOT \
         decrease and the definition must be refused",
    );
    let ElabError::Unsupported { feature } = &err else {
        panic!("must fail closed as `Unsupported`, got: {err:?}");
    };
    assert!(
        feature.contains("termination_by"),
        "diagnostic must name the construct the user wrote, got: {feature}"
    );
    assert!(
        feature.contains("no decreasing proof was found"),
        "the refusal must be at the DECREASE, not at a shape gate, got: {feature}"
    );
    assert!(
        feature.contains("Fail closed"),
        "the diagnostic must state the fail-closed contract, got: {feature}"
    );

    assert!(
        register_one(&mut env, GCD_SUB_UNGUARDED).is_err(),
        "and registering it must fail too"
    );
    assert!(
        env.get_const(&Name::from_string("gcdSubBad")).is_none(),
        "a refused definition must register nothing — no sorry, no axiom, no \
         unchecked declaration"
    );
}

/// A second non-decreasing sum, from a different direction: the R3 `lex`
/// fixture. `lex (a-1) (b+0)` under only `0 < a + b` does not shrink `a + b`
/// when `a` is already `0`. Refused, at the decrease.
#[test]
fn test_a_non_decreasing_sum_measure_is_refused() {
    let env = Environment::with_prelude();
    let err = elab_one(
        &env,
        "def lex (a b : Nat) : Nat := if h : 0 < a + b then lex (a - 1) (b + 0) else 0\n\
         termination_by a + b",
    )
    .expect_err("`0 < a + b` does not bound `a` away from zero, so the sum need not shrink");
    let ElabError::Unsupported { feature } = &err else {
        panic!("must fail closed as `Unsupported`, got: {err:?}");
    };
    assert!(
        feature.contains("no decreasing proof was found"),
        "must be refused at the decrease, got: {feature}"
    );
}

/// **THE BOUNDARY THIS DID NOT MOVE.** A multi-parameter measure that is NOT a
/// sum stays refused — and the diagnostic now names the sum form as a way
/// forward, spelled for THIS declaration (v7/D3).
#[test]
fn test_a_non_sum_multi_parameter_measure_is_still_refused_with_the_fix() {
    let env = Environment::with_prelude();
    let err = elab_one(
        &env,
        "def lexSub (a b : Nat) : Nat := if h : 0 < a + b then lexSub (a - 1) (b + 0) else 0\n\
         termination_by b - a",
    )
    .expect_err("a lexicographic/packed measure is not lowered");
    let ElabError::Unsupported { feature } = &err else {
        panic!("must fail closed as `Unsupported`, got: {err:?}");
    };
    assert!(
        feature.contains("termination_by"),
        "diagnostic must name the construct, got: {feature}"
    );
    assert!(
        feature.contains("is not a SUM"),
        "diagnostic must name the boundary it refuses at, got: {feature}"
    );
    assert!(
        feature.contains("`a`") && feature.contains("`b`"),
        "diagnostic must name WHICH parameters the measure mentions, got: {feature}"
    );
    assert!(
        feature.contains("termination_by a + b"),
        "v7/D3: the refusal must carry the fix SPELLED for this declaration, got: {feature}"
    );
    assert!(
        feature.contains("Ways forward"),
        "v7/D3: a refusal must carry options, got: {feature}"
    );
}

/// A measure mentioning NO parameter keeps its own, better-worded refusal —
/// the sum widening did not swallow it.
#[test]
fn test_measure_naming_no_parameter_still_has_its_own_refusal() {
    let env = Environment::with_prelude();
    let err = elab_one(
        &env,
        "def nomeasure (a b : Nat) : Nat := if h : 0 < b then nomeasure (a + 0) (b - 1) else 0\n\
         termination_by 5",
    )
    .expect_err("a constant measure decreases nowhere");
    let ElabError::Unsupported { feature } = &err else {
        panic!("must fail closed as `Unsupported`, got: {err:?}");
    };
    assert!(
        feature.contains("mentions none of the parameters"),
        "diagnostic must name the actual defect, got: {feature}"
    );
}

// ═══════════════ the widening's own shapes ═══════════════

/// A sum measure over THREE parameters. `a + b + c` is `(a + b) + c`, so the
/// congruence tier has to peel two levels — `c` fixed, then `b` fixed — before
/// it reaches the `a - 1 < a` that `Nat.sub_lt` owns.
#[test]
fn test_a_three_parameter_sum_measure() {
    let mut env = Environment::with_prelude();
    register_one(
        &mut env,
        "def tri (a b c : Nat) : Nat := \
         if h : 0 < a then tri (a - 1) b c else b + c\n\
         termination_by a + b + c",
    )
    .expect("a three-way sum measure must lower");
    assert_wf_definition_registered(&env, "tri");
    register_one(&mut env, "theorem tri3 : tri 1 2 3 = 5 := rfl").expect("tri 1 2 3 = 2 + 3 = 5");
    assert!(
        register_one(&mut env, "theorem tri3_bad : tri 1 2 3 = 6 := rfl").is_err(),
        "mutation control"
    );
}

/// **A MEASURED RESIDUAL, stated rather than hidden.** A recursion where one
/// parameter GROWS and another shrinks by MORE — so the sum still decreases —
/// is not lowered today.
///
/// `halve (a + 1) (b - 2)` under `1 < b` owes `(a+1) + (b-2) < a + b`, which
/// is true for `b ≥ 2`. Neither summand is fixed, so tier 4's congruence rules
/// do not apply (and `a + 1 < a` is false, so its both-strict rule cannot fire
/// either); it is a genuinely linear-arithmetic obligation. Tier 5's `omega`
/// is where it should land, and `omega` cannot do it — measured on this branch
/// at pin `0b3b94e5b`, `omega` fails on the whole `Nat`-truncated-subtraction
/// family, including goals as small as
///
/// ```text
/// theorem o2 (b : Nat) (h : 0 < b) : b - 1 < b := by omega
///   -> ArithmeticFailed { tactic: "mathverse",
///        reason: "certified arithmetic contradiction has no kernel proof
///                 (close_goal rejected arithmetic proof: type mismatch …)" }
/// ```
///
/// — i.e. `omega` decides the goal and then reconstructs a proof of the
/// HYPOTHESIS instead. That is a pre-existing tactic defect, not something
/// this widening introduced, and it fails CLOSED. Two ways to close this
/// residual, in the order they are worth doing: fix `omega`'s Nat-subtraction
/// proof reconstruction (which lifts every tier-5 goal at once), or add a
/// `Nat.add_lt_add_of_le_of_lt`-class congruence rule.
///
/// If this test ever starts passing the residual is closed — delete it and
/// move the fixture up into the acceptance set above.
#[test]
fn test_a_growing_parameter_with_a_larger_shrink_is_a_measured_residual() {
    let env = Environment::with_prelude();
    let err = elab_one(
        &env,
        "def halve (a b : Nat) : Nat := \
         if h : 1 < b then halve (a + 1) (b - 2) else a\n\
         termination_by a + b",
    )
    .expect_err(
        "MEASURED RESIDUAL: the sum DOES decrease here, but no tier can prove \
         it — see this test's docs before treating a pass as a regression",
    );
    let ElabError::Unsupported { feature } = &err else {
        panic!("must fail closed as `Unsupported`, got: {err:?}");
    };
    assert!(
        feature.contains("no decreasing proof was found"),
        "the residual is a DISCHARGE gap, not a shape gap, got: {feature}"
    );
}

/// **The SIMULTANEITY of the obligation, at the elaborator level.** A call
/// that SWAPS its arguments leaves `a + b` unchanged, so the sum cannot
/// decrease and the definition must be refused. A sequential substitution
/// would build the obligation `a + a < a + b` instead — a different claim,
/// which `omega` could discharge from `a < b` and which would admit a
/// non-terminating program.
#[test]
fn test_a_swapping_recursive_call_cannot_decrease_a_sum() {
    let env = Environment::with_prelude();
    let err = elab_one(
        &env,
        "def swapper (a b : Nat) : Nat := if h : a < b then swapper b a else a\n\
         termination_by a + b",
    )
    .expect_err("swapping the arguments leaves `a + b` fixed, so nothing decreases");
    let ElabError::Unsupported { feature } = &err else {
        panic!("must fail closed as `Unsupported`, got: {err:?}");
    };
    assert!(
        feature.contains("no decreasing proof was found"),
        "must be refused at the decrease, got: {feature}"
    );
}

// ═══════════ the phase-2 path is untouched ═══════════

/// The one-parameter lowering still produces its own term shape, including for
/// a WIDER signature. Guards the phase-3 dispatch against capturing phase 2.
#[test]
fn test_one_parameter_measures_still_take_the_phase_two_path() {
    let mut env = Environment::with_prelude();
    for source in [
        "def gcdM (a b : Nat) : Nat := if h : 0 < b then gcdM b (a % b) else a\n\
         termination_by b",
        "def addDown (a b : Nat) : Nat := if h : 0 < b then a + addDown a (b - 1) else 0\n\
         termination_by b",
        "def firstDown (a b : Nat) : Nat := if h : 0 < a then b + firstDown (a - 1) b else 0\n\
         termination_by a",
        // A one-parameter measure that is nonetheless `+`-headed: the SHAPE
        // gate must not fire, because only ONE parameter is mentioned.
        "def plusZero (a b : Nat) : Nat := if h : 0 < b then plusZero a (b - 1) else a\n\
         termination_by b + 0",
    ] {
        register_one(&mut env, source).unwrap_or_else(|e| panic!("`{source}`: {e}"));
    }
    for name in ["gcdM", "addDown", "firstDown", "plusZero"] {
        assert_wf_definition_registered(&env, name);
    }
    for source in [
        "theorem p0 : gcdM 12 18 = 6 := rfl",
        "theorem p1 : addDown 3 4 = 12 := rfl",
        "theorem p2 : firstDown 3 5 = 15 := rfl",
        "theorem p3 : plusZero 7 3 = 7 := rfl",
    ] {
        register_one(&mut env, source).unwrap_or_else(|e| panic!("`{source}`: {e}"));
    }
}
