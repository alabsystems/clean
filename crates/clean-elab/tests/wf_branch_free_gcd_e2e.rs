// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **WF phase 4 — the BRANCH-FREE `gcd`, two arguments and no fuel.** parse →
//! elaborate → kernel-check → register → COMPUTE, for the class phase 3
//! refused.
//!
//! The design's §1 demo asks for `def gcd (a b : Nat)`. Phase 2 delivered the
//! modulo form (`gcd b (a % b)`, `termination_by b`) and phase 3 the two-branch
//! subtractive form (`termination_by a + b`). Both still lean on the
//! obligation's shape: the modulo one is `Nat.mod_lt`, the subtractive one is a
//! congruence of one summand over `Nat.sub_lt`. Neither can express the
//! BRANCH-FREE step,
//!
//! ```lean
//! def gcdB (a b : Nat) : Nat :=
//!   if h : 0 < b then gcdB ((a - b) + (b - a)) (a - (a - b)) else a
//! termination_by a + 2 * b
//! ```
//!
//! — **one** guard, **one** self-call — because its obligation
//! `((a-b)+(b-a)) + 2*(a-(a-b)) < a + 2*b` is true only through the *truncation*
//! of Nat subtraction: `(a-b)+(b-a)` is `|a - b|` and `a-(a-b)` is `min a b`,
//! so the left side is `a + b`, and the decrease is by exactly `b`. Every
//! pre-phase-4 tier treats `a - b` as an opaque atom and cannot see any of that;
//! measured at pin `7422b63a0`, `gcdB` was refused at the decrease.
//!
//! `infer::wf_recursion::sub_elim` closes it with three tiers that are general
//! rather than shaped to this program — sum positivity, a strict linear
//! residual, and truncated-subtraction elimination by a case split on
//! `Nat.le_total` — all of them named, axiom-free prelude theorems, and all of
//! them re-checked against the actual goal before acceptance. The term shapes
//! were kernel-probed first in
//! `clean-kernel/tests/wf_sub_case_split_kernel_probe.rs`.
//!
//! HONESTY RULES, as in the R3/R5/phase-3 batteries: every ADMIT is paired with
//! a refused MUTATION at the same layer, and every refusal asserts its reason.
//!
//! # The fixtures that must be REFUSED, and why they are here
//!
//! * **`gcdBWeak`** — the SAME program with `termination_by a + b`. One
//!   character different, and genuinely wrong: at `a = 0, b = 5` the step maps
//!   `(0,5) ↦ (5,0)`, so `a + b` is `5` before and `5` after. The tier must
//!   refuse it, and it must refuse it in the `a ≤ b` branch, where the
//!   residual's positivity side-condition `0 < a` is not in scope. This is the
//!   nearly-identical non-decreasing sibling the widening most needed.
//! * **`gcdBUnguarded`** — the branch-free step with NO guard at all, which
//!   never terminates.
//! * **`swapper`** (pinned in `wf_sum_measure_e2e`, re-asserted here) — a
//!   recursion whose measure is unchanged. Its linear residual is exactly ZERO,
//!   which the residual tier refuses; a tier that accepted a zero residual
//!   would admit an infinite loop.

use clean_elab::{
    elaborate_decl, elaborate_decl_and_register, preprocess_decl_with_context, ElabError,
    ElabResult, FileContext,
};
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, ExprKind};
use clean_parser::parse_file;

/// The branch-free Euclid: one guard, one self-call, no fuel, two arguments.
const GCD_B: &str = "def gcdB (a b : Nat) : Nat := \
     if h : 0 < b then gcdB ((a - b) + (b - a)) (a - (a - b)) else a\n\
     termination_by a + 2 * b";

/// The same step map under a measure that does NOT decrease.
const GCD_B_WEAK: &str = "def gcdBWeak (a b : Nat) : Nat := \
     if h : 0 < b then gcdBWeak ((a - b) + (b - a)) (a - (a - b)) else a\n\
     termination_by a + b";

/// The same step map with no guard: `gcdBBad 0 0` loops forever.
const GCD_B_UNGUARDED: &str = "def gcdBBad (a b : Nat) : Nat := \
     gcdBBad ((a - b) + (b - a)) (a - (a - b))\n\
     termination_by a + 2 * b";

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

/// Does `wanted` occur anywhere in the term? A fold over the constants, not a
/// string match on `Debug`.
fn mentions_const(value: &Expr, wanted: &str) -> bool {
    let wanted = Name::from_string(wanted);
    let mut stack = vec![value.clone()];
    while let Some(e) = stack.pop() {
        match e.kind() {
            ExprKind::Const(name, _) if *name == wanted => return true,
            ExprKind::App(f, a) => {
                stack.push(Expr::clone(f));
                stack.push(Expr::clone(a));
            }
            ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                stack.push(Expr::clone(t));
                stack.push(Expr::clone(b));
            }
            ExprKind::Let(_, t, v, b, _) => {
                stack.push(Expr::clone(t));
                stack.push(Expr::clone(v));
                stack.push(Expr::clone(b));
            }
            ExprKind::MData(_, inner) | ExprKind::Proj(_, _, inner) => {
                stack.push(Expr::clone(inner))
            }
            _ => {}
        }
    }
    false
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

fn env_with_gcd_b() -> Environment {
    let mut env = Environment::with_prelude();
    register_one(&mut env, GCD_B)
        .expect("phase 4: the branch-free `gcdB` must elaborate and kernel-verify");
    env
}

// ═══════════ the acceptance: the branch-free gcd elaborates ═══════════

#[test]
fn test_branch_free_gcd_elaborates_kernel_verifies_and_is_axiom_free() {
    let env = env_with_gcd_b();
    assert_wf_definition_registered(&env, "gcdB");
}

/// The termination argument must be READABLE in the emitted term: a case split
/// on `Nat.le_total`, the substitution's `Nat.ulpRound.sub_add_cancel`, the
/// truncation rewrites, and the residual's `Nat.add_lt_add_left`. If any of
/// these stops appearing, the decrease is being discharged by something other
/// than the audited lane and this test should be re-read before it is updated.
#[test]
fn test_the_decrease_is_named_prelude_theorems_not_a_tactic_artifact() {
    let env = env_with_gcd_b();
    let value = env
        .get_const(&Name::from_string("gcdB"))
        .and_then(|c| c.value.clone())
        .expect("gcdB keeps its value");
    for name in [
        // the case split
        "Nat.le_total",
        "Or.rec",
        // the substitution `b := a + (b - a)`
        "Nat.ulpRound.sub_add_cancel",
        "Nat.add_comm",
        // the truncation rewrites
        "Nat.ulpRound.sub_eq_zero_of_le",
        "Nat.ulpRound.add_sub_cancel_left",
        "Nat.ulpRound.add_sub_self_right",
        "Nat.sub_zero",
        "Nat.zero_add",
        "Nat.le_add_right",
        // the strict residual, and the transports that carry it
        "Nat.add_lt_add_left",
        "congrArg",
        "Eq.mp",
        "Eq.mpr",
    ] {
        assert!(
            mentions_const(&value, name),
            "the decreasing proof must name `{name}`"
        );
    }
    assert!(
        !value.has_sorry(),
        "and it must carry no sorry anywhere in the term"
    );
}

/// **THE TARGET: `gcdB 12 18 = 6`.** Closed, so the `WellFounded.fix`
/// application must actually grind through `Acc.rec` and `Nat.accNatLt` on the
/// `a + 2*b` measure. This is the computation claim, not a typing claim.
#[test]
fn test_branch_free_gcd_12_18_computes_to_6() {
    let mut env = env_with_gcd_b();
    register_one(&mut env, "theorem gcdB_12_18 : gcdB 12 18 = 6 := rfl")
        .expect("`gcdB 12 18` must COMPUTE to 6 by kernel reduction");

    // MUTATION CONTROL: the computation is a decision, not a rubber stamp.
    assert!(
        register_one(&mut env, "theorem gcdB_12_18_bad : gcdB 12 18 = 5 := rfl").is_err(),
        "`gcdB 12 18 = 5` must be REFUSED — otherwise the evidence above is vacuous"
    );
    assert!(
        env.get_const(&Name::from_string("gcdB_12_18_bad"))
            .is_none(),
        "a refused theorem must register nothing"
    );
}

/// The closed values the task names, both argument orders, and the boundary
/// cases the single guard exists for. Each is `rfl`, so each is a kernel
/// reduction.
#[test]
fn test_branch_free_gcd_closed_values_and_identities() {
    let mut env = env_with_gcd_b();
    for (index, source) in [
        "theorem gb0 : gcdB 270 192 = 6 := rfl",
        "theorem gb1 : gcdB 7 13 = 1 := rfl",
        "theorem gb2 : gcdB 0 5 = 5 := rfl",
        "theorem gb3 : gcdB 5 0 = 5 := rfl",
        "theorem gb4 : gcdB 18 12 = 6 := rfl",
        "theorem gb5 : gcdB 48 18 = 6 := rfl",
        "theorem gb6 : gcdB 0 0 = 0 := rfl",
    ]
    .into_iter()
    .enumerate()
    {
        register_one(&mut env, source)
            .unwrap_or_else(|e| panic!("closed value #{index} (`{source}`) must compute: {e}"));
    }

    // MUTATION CONTROL at the same layer.
    assert!(
        register_one(&mut env, "theorem gb_bad : gcdB 270 192 = 7 := rfl").is_err(),
        "a wrong closed value must be refused"
    );
    assert!(
        register_one(&mut env, "theorem gb_bad2 : gcdB 7 13 = 7 := rfl").is_err(),
        "a wrong closed value must be refused"
    );
}

/// It agrees with the phase-2 modulo `gcd` and the phase-3 subtractive `gcdSub`
/// on closed inputs — three lowerings, one function.
#[test]
fn test_branch_free_modulo_and_subtractive_gcd_agree() {
    let mut env = env_with_gcd_b();
    register_one(
        &mut env,
        "def gcdMod (a b : Nat) : Nat := if h : 0 < b then gcdMod b (a % b) else a\n\
         termination_by b",
    )
    .expect("the phase-2 one-parameter lowering must still work");
    register_one(
        &mut env,
        "def gcdSub (a b : Nat) : Nat := \
         if ha : a = 0 then b \
         else if hb : b = 0 then a \
         else if hge : a >= b then gcdSub (a - b) b else gcdSub a (b - a)\n\
         termination_by a + b",
    )
    .expect("the phase-3 sum lowering must still work");
    for source in [
        "theorem agree0 : gcdB 270 192 = gcdMod 270 192 := rfl",
        "theorem agree1 : gcdB 48 18 = gcdSub 48 18 := rfl",
        "theorem agree2 : gcdB 7 13 = gcdMod 7 13 := rfl",
    ] {
        register_one(&mut env, source).unwrap_or_else(|e| panic!("`{source}`: {e}"));
    }
}

// ══════════ the adversarial controls: what must stay REFUSED ══════════

/// **THE CONTROL THAT MATTERS.** The SAME program under `termination_by a + b`.
/// The step map sends `(0, 5) ↦ (5, 0)`, so `a + b` is `5` on both sides and
/// the measure does not decrease. It must be REFUSED — at the DECREASE, with
/// the fail-closed diagnostic, and nothing registered.
///
/// This is the fixture that shows the widening is not "accept anything with a
/// subtraction in it": it differs from the accepted `gcdB` by one coefficient.
#[test]
fn test_the_same_program_under_a_non_decreasing_measure_is_refused() {
    let mut env = Environment::with_prelude();
    let err = elab_one(&env, GCD_B_WEAK).expect_err(
        "`a + b` is unchanged by the branch-free step at `a = 0`, so the \
         measure does NOT decrease and the definition must be refused",
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
        register_one(&mut env, GCD_B_WEAK).is_err(),
        "and registering it must fail too"
    );
    assert!(
        env.get_const(&Name::from_string("gcdBWeak")).is_none(),
        "a refused definition must register nothing — no sorry, no axiom, no \
         unchecked declaration"
    );
}

/// The unguarded branch-free step never terminates (`gcdBBad 0 0` maps to
/// itself). Refused.
#[test]
fn test_the_unguarded_branch_free_step_is_refused() {
    let mut env = Environment::with_prelude();
    assert!(
        elab_one(&env, GCD_B_UNGUARDED).is_err(),
        "an unguarded self-call must be refused"
    );
    assert!(
        register_one(&mut env, GCD_B_UNGUARDED).is_err(),
        "and registering it must fail too"
    );
    assert!(
        env.get_const(&Name::from_string("gcdBBad")).is_none(),
        "a refused definition must register nothing"
    );
}

/// **THE ZERO-RESIDUAL CONTROL.** A recursion that leaves the measure exactly
/// unchanged has linear residual `0`. The residual tier must refuse it: a tier
/// that accepted `0 < 0` — or that treated "no negative coefficient" as enough
/// — would admit a non-terminating program.
#[test]
fn test_a_measure_preserving_recursion_is_refused_at_the_residual() {
    let env = Environment::with_prelude();
    for (source, why) in [
        (
            "def swapper (a b : Nat) : Nat := if h : a < b then swapper b a else a\n\
             termination_by a + b",
            "swapping the arguments leaves `a + b` fixed",
        ),
        (
            "def shuffle (a b : Nat) : Nat := \
             if h : 0 < b then shuffle (a + (b - b)) b else a\n\
             termination_by a + b",
            "`b - b` is zero, so nothing moves",
        ),
    ] {
        let err = elab_one(&env, source).expect_err(why);
        let ElabError::Unsupported { feature } = &err else {
            panic!("must fail closed as `Unsupported` ({why}), got: {err:?}");
        };
        assert!(
            feature.contains("no decreasing proof was found"),
            "must be refused at the decrease ({why}), got: {feature}"
        );
    }
}

/// A recursion whose measure GROWS, spelled with the same truncated-subtraction
/// vocabulary, must be refused — the residual is negative, not merely zero.
#[test]
fn test_a_growing_measure_is_refused() {
    let env = Environment::with_prelude();
    let err = elab_one(
        &env,
        "def grow (a b : Nat) : Nat := \
         if h : 0 < b then grow ((a - b) + (b - a) + b) (a - (a - b)) else a\n\
         termination_by a + 2 * b",
    )
    .expect_err("adding `b` back to the first argument destroys the decrease");
    let ElabError::Unsupported { feature } = &err else {
        panic!("must fail closed as `Unsupported`, got: {err:?}");
    };
    assert!(
        feature.contains("no decreasing proof was found"),
        "must be refused at the decrease, got: {feature}"
    );
}

// ═══════════ the boundaries phase 4 did NOT move ═══════════

/// The phase-3 residual is still a residual. `halve (a + 1) (b - 2)` under
/// `1 < b` genuinely decreases `a + b`, and the new tiers still do not reach it:
/// the split pair must be two distinct free variables, and `b - 2` has a
/// LITERAL subtrahend, so the case-split tier declines by design (the
/// `Nat.sub_lt` tier owns that shape).
///
/// If this ever starts passing, the split gate was widened — re-measure the
/// recursion corpus before treating it as a win.
#[test]
fn test_a_literal_subtrahend_still_declines_the_split() {
    let env = Environment::with_prelude();
    let err = elab_one(
        &env,
        "def halve (a b : Nat) : Nat := \
         if h : 1 < b then halve (a + 1) (b - 2) else a\n\
         termination_by a + b",
    )
    .expect_err(
        "MEASURED RESIDUAL: the sum DOES decrease here, but the split gate \
         requires two free variables and `2` is a literal",
    );
    let ElabError::Unsupported { feature } = &err else {
        panic!("must fail closed as `Unsupported`, got: {err:?}");
    };
    assert!(
        feature.contains("no decreasing proof was found"),
        "the residual is a DISCHARGE gap, not a shape gap, got: {feature}"
    );
}

/// The phase-2 and phase-3 lowerings are untouched: the new tiers sit after the
/// tactic tier, so every obligation an earlier tier already discharged still
/// reaches that tier first.
#[test]
fn test_the_earlier_lowerings_still_elaborate_and_compute() {
    let mut env = Environment::with_prelude();
    for source in [
        "def gcdM (a b : Nat) : Nat := if h : 0 < b then gcdM b (a % b) else a\n\
         termination_by b",
        "def addDown (a b : Nat) : Nat := if h : 0 < b then a + addDown a (b - 1) else 0\n\
         termination_by b",
        "def firstDown (a b : Nat) : Nat := if h : 0 < a then b + firstDown (a - 1) b else 0\n\
         termination_by a",
        "def tri (a b c : Nat) : Nat := if h : 0 < a then tri (a - 1) b c else b + c\n\
         termination_by a + b + c",
    ] {
        register_one(&mut env, source).unwrap_or_else(|e| panic!("`{source}`: {e}"));
    }
    for name in ["gcdM", "addDown", "firstDown", "tri"] {
        assert_wf_definition_registered(&env, name);
    }
    for source in [
        "theorem q0 : gcdM 12 18 = 6 := rfl",
        "theorem q1 : addDown 3 4 = 12 := rfl",
        "theorem q2 : firstDown 3 5 = 15 := rfl",
        "theorem q3 : tri 1 2 3 = 5 := rfl",
    ] {
        register_one(&mut env, source).unwrap_or_else(|e| panic!("`{source}`: {e}"));
    }
}

/// The `gcdM` decrease is still `Nat.mod_lt` — a tier-3 term, not a phase-4
/// one. This is the term-stability pin for the "strictly additive" claim.
#[test]
fn test_an_earlier_tier_keeps_its_own_proof_term() {
    let mut env = Environment::with_prelude();
    register_one(
        &mut env,
        "def gcdM (a b : Nat) : Nat := if h : 0 < b then gcdM b (a % b) else a\n\
         termination_by b",
    )
    .expect("phase-2 gcd must elaborate");
    let value = env
        .get_const(&Name::from_string("gcdM"))
        .and_then(|c| c.value.clone())
        .expect("gcdM keeps its value");
    assert!(
        mentions_const(&value, "Nat.mod_lt"),
        "the decrease must still be `Nat.mod_lt`"
    );
    assert!(
        !mentions_const(&value, "Nat.le_total"),
        "and it must NOT have been re-routed through the phase-4 case split"
    );
}
