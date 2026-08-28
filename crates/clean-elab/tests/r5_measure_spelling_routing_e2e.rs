// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **R5 E2E — the R3 routing rule applies to the MEASURE, not to one spelling
//! of it.**
//!
//! R3 established the rule that decides whether `gcd` reaches the well-founded
//! lowering at all: an explicit `termination_by <measure>` is a DECLARATION,
//! `detect_recursion_with_params` is a HEURISTIC, and when they name different
//! parameters the declaration wins. R3 implemented it by matching a bare
//! `SurfaceExpr::Ident` and nothing else.
//!
//! # What that missed, measured at pin `99e2128ef` BEFORE this change
//!
//! | measure | verdict THEN | verdict NOW |
//! |---|---|---|
//! | `termination_by b` | ADMITTED | unchanged |
//! | `termination_by (b)` | **`RecursionOutsideFragment`** | **ADMITTED** |
//! | `termination_by b + 0` | `RecursionOutsideFragment` | reaches the DECREASE |
//! | `termination_by b.toNat` (UInt64) | `RecursionOutsideFragment` | reaches the DECREASE |
//!
//! Every one of those is the same `gcd`, differing only in how the measure is
//! written. A single pair of parentheses moved the verdict, which is the
//! signature of a routing bug rather than a fragment boundary: the measure was
//! never consulted, routing stayed structural, and the self-call died at
//! unknown-identifier resolution — R3's own bug, one spelling over.
//!
//! `wf_recursion::measure_params` closes it by asking which parameters the
//! measure MENTIONS, which is the same "exactly one parameter" rule the
//! lowering's phase 2b already applies to the ELABORATED measure. Routing and
//! lowering now agree instead of drifting.
//!
//! # What this does NOT claim
//!
//! Two rows above still end in a refusal, and this file asserts that they do.
//! Lifting a ROUTING gate does not discharge a DECREASE: `b + 0` needs the
//! cascade to see through `+ 0` (the obligation is `(a % b) + 0 < b + 0`, and
//! the cascade is syntactic), and the UInt64 analogue needs carrier lemmas
//! that are measurably ABSENT from the prelude — there is no `UInt64.mod_lt`,
//! no `UInt64.toNat_mod`, no `UInt64.pos_of_ne_zero`. What changed for those
//! two is the DIAGNOSTIC: the compiler now names `termination_by`, the
//! cascade it tried, and the ways forward (Trust ruling v7/D3) instead of
//! reporting that the recursion is outside the fragment, which was false.
//!
//! HONESTY RULES (as in the R3/R4 batteries): every ADMIT is paired with a
//! refused MUTATION at the same layer, and every refusal asserts its reason.

use clean_elab::{
    elaborate_decl, elaborate_decl_and_register, preprocess_decl_with_context, ElabError,
    ElabResult, FileContext,
};
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, ExprKind};
use clean_parser::parse_file;

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
/// parameter lambdas)? Structural — a `Debug`-string match cannot answer this,
/// because `Name`'s derived `Debug` renders segments as a list.
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

/// Did the definition die at the ROUTER (unknown-identifier resolution), i.e.
/// never reach the well-founded lowering at all?
fn is_routing_refusal(err: &ElabError) -> bool {
    matches!(err, ElabError::RecursionOutsideFragment { .. })
}

/// Did the definition REACH the well-founded lowering and get refused there,
/// with the fail-closed diagnostic that names `termination_by`?
fn is_wf_lowering_refusal(err: &ElabError) -> bool {
    matches!(err, ElabError::Unsupported { feature } if feature.contains("termination_by"))
}

// ═══════════ the capability: a parenthesized measure now elaborates ═══════════

/// `gcd` with `termination_by (b)`. Character-for-character the R3 fixture
/// except for one pair of parentheses, which used to decide the verdict.
const GCD_PAREN: &str = "def gcd (a b : Nat) : Nat := \
     if h : b = 0 then a else gcd b (a % b)\n\
     termination_by (b)";

#[test]
fn parenthesized_measure_elaborates_kernel_verifies_and_computes() {
    let mut env = Environment::with_prelude();
    register_one(&mut env, GCD_PAREN).expect(
        "R5: `termination_by (b)` must route exactly like `termination_by b` — \
         a pair of parentheses is not a fragment boundary",
    );
    assert_wf_definition_registered(&env, "gcd");

    // COMPUTATION, not just typing: the fix must grind through `Acc.rec`.
    register_one(&mut env, "theorem gcd_12_18 : gcd 12 18 = 6 := rfl")
        .expect("`gcd 12 18` must COMPUTE to 6 by kernel reduction");

    // MUTATION CONTROL at the same layer — otherwise the line above is a
    // rubber stamp rather than a decision.
    assert!(
        register_one(&mut env, "theorem gcd_bad : gcd 12 18 = 5 := rfl").is_err(),
        "`gcd 12 18 = 5` must be REFUSED"
    );
    assert!(
        env.get_const(&Name::from_string("gcd_bad")).is_none(),
        "a refused theorem must register nothing"
    );
}

#[test]
fn the_bare_measure_control_is_unaffected() {
    // R3's spelling, which always worked. If this ever fails, the R5 change
    // broke the case it was supposed to leave alone.
    const GCD_BARE: &str = "def gcd (a b : Nat) : Nat := \
         if h : b = 0 then a else gcd b (a % b)\n\
         termination_by b";
    let mut env = Environment::with_prelude();
    register_one(&mut env, GCD_BARE).expect("the bare-identifier measure must still elaborate");
    assert_wf_definition_registered(&env, "gcd");
}

// ═════════ the diagnostic: a compound measure reaches the DECREASE ═════════

/// **RE-PIN, 2026-08-25 — the row MOVED, exactly as R5 said it should.**
///
/// R5 measured that `termination_by b + 0` reached the well-founded lowering
/// (its point) but was then refused at the DECREASE, because the obligation is
/// `(a % b) + 0 < b + 0` and the cascade was syntactic. Its RE-PIN RULE said:
/// *"If the cascade later normalizes `+ 0` … this definition becomes ADMITTED
/// and this assertion must MOVE rather than be worked around."*
///
/// WF phase 3's tier-4 sum congruence does exactly that — not by normalizing,
/// but by peeling the fixed summand: `Nat.add_lt_add_right (a % b) b ⟨…⟩ 0`
/// over the `Nat.mod_lt` the one-parameter cascade already owned. So the row
/// has moved from "refused at the decrease" to ADMITTED, and it is pinned here
/// with its computation and a mutation control.
#[test]
fn a_compound_measure_now_reaches_all_the_way_through_the_decrease() {
    // `b + 0` is `App(HAdd.hAdd, [b, 0])`. It mentions exactly one parameter,
    // so routing sends it to the well-founded lowering (R5), and tier 4 now
    // discharges the `+ 0` obligation it lands on (phase 3).
    const GCD_PLUS_ZERO: &str = "def gcd (a b : Nat) : Nat := \
         if h : b = 0 then a else gcd b (a % b)\n\
         termination_by b + 0";
    let mut env = Environment::with_prelude();
    register_one(&mut env, GCD_PLUS_ZERO).expect(
        "phase 3: the `(a % b) + 0 < b + 0` obligation is discharged by the \
         sum-congruence tier",
    );
    assert_wf_definition_registered(&env, "gcd");

    // COMPUTATION, not just typing.
    register_one(&mut env, "theorem gcd_pz : gcd 12 18 = 6 := rfl")
        .expect("`gcd 12 18` must COMPUTE to 6 by kernel reduction");
    assert!(
        register_one(&mut env, "theorem gcd_pz_bad : gcd 12 18 = 5 := rfl").is_err(),
        "mutation control"
    );

    // The R5 property this test was born to guard is unchanged and still
    // asserted: a compound measure is not a ROUTING refusal.
    let bad = elab_one(
        &Environment::with_prelude(),
        "def gcdNo (a b : Nat) : Nat := \
         if h : b = 0 then a else gcdNo b (a % b)\n\
         termination_by b + 1",
    );
    if let Err(err) = bad {
        assert!(
            !is_routing_refusal(&err),
            "a compound measure must never come back as a ROUTING refusal, got: {err}"
        );
        assert!(
            is_wf_lowering_refusal(&err),
            "any refusal must come from the well-founded lowering, got: {err}"
        );
    }
}

#[test]
fn the_uint64_analogue_reaches_the_decrease_and_is_refused_there() {
    // The task's UInt64 analogue. `b.toNat` is `Proj(Ident(b), Named toNat)`
    // and IS `Nat`-valued, so the measure gate accepts it; routing used to
    // refuse it one layer earlier.
    const GCD_U64: &str = "def gcdU (a b : UInt64) : UInt64 := \
         if h : b = 0 then a else gcdU b (a % b)\n\
         termination_by b.toNat";
    let env = Environment::with_prelude();
    let err = elab_one(&env, GCD_U64)
        .expect_err("the UInt64 analogue is NOT claimed: its carrier lemmas are absent");

    assert!(
        !is_routing_refusal(&err),
        "BEFORE R5 this was `RecursionOutsideFragment`. Got: {err}"
    );
    assert!(
        is_wf_lowering_refusal(&err),
        "the refusal must now come from the well-founded lowering, got: {err}"
    );

    // WHY it is refused, asserted rather than asserted-about: the decrease
    // `(a % b).toNat < b.toNat` has no lemma to land on. These are the
    // constants a UInt64 lane would need, and they are measurably absent.
    for absent in ["UInt64.mod_lt", "UInt64.toNat_mod", "UInt64.pos_of_ne_zero"] {
        assert!(
            env.get_const(&Name::from_string(absent)).is_none(),
            "{absent} is expected ABSENT — if it has landed, the UInt64 lane \
             is newly tractable and this test should be upgraded to an ADMIT"
        );
    }
}

// ═══════════════════════ the adversarial controls ═══════════════════════

#[test]
fn a_non_decreasing_recursion_is_refused_at_every_measure_spelling() {
    // `bad b a` shrinks NOTHING. Reaching the well-founded lowering must not
    // mean being admitted by it — this is the fail-closed claim, and it is the
    // reason lifting a routing gate is safe.
    for (label, source) in [
        (
            "bare",
            "def bad (a b : Nat) : Nat := if h : b = 0 then a else bad b a\ntermination_by b",
        ),
        (
            "parenthesized",
            "def bad (a b : Nat) : Nat := if h : b = 0 then a else bad b a\ntermination_by (b)",
        ),
        (
            "compound",
            "def bad (a b : Nat) : Nat := if h : b = 0 then a else bad b a\ntermination_by b + 0",
        ),
    ] {
        let mut env = Environment::with_prelude();
        let result = register_one(&mut env, source);
        assert!(
            result.is_err(),
            "ADVERSARIAL ({label}): a non-decreasing two-parameter recursion \
             must be REFUSED"
        );
        assert!(
            env.get_const(&Name::from_string("bad")).is_none(),
            "ADVERSARIAL ({label}): a refused definition must register nothing \
             — no sorry, no axiom, no unchecked declaration"
        );
    }
}

#[test]
fn a_two_parameter_measure_leaves_routing_untouched() {
    // `b - a` mentions BOTH parameters, so there is no sole parameter to
    // claim and routing must stay exactly where it was. A lexicographic /
    // packed measure is not lowered, and R5 does not pretend otherwise.
    const TWO: &str = "def f (a b : Nat) : Nat := \
         if h : b = 0 then a else f b (a % b)\n\
         termination_by b - a";
    let env = Environment::with_prelude();
    let err = elab_one(&env, TWO).expect_err("a two-parameter measure must be refused");
    assert!(
        is_routing_refusal(&err),
        "routing must be UNTOUCHED for a measure with no sole parameter, got: {err}"
    );
}

#[test]
fn a_binder_bearing_measure_leaves_routing_untouched() {
    // THE SHADOWING GUARD, end to end. `(fun b => b) b`'s inner `b` is a
    // different variable; the walker declines to answer rather than guess, so
    // routing is left exactly as it was.
    const SHADOW: &str = "def f (a b : Nat) : Nat := \
         if h : b = 0 then a else f b (a % b)\n\
         termination_by (fun b => b) b";
    let env = Environment::with_prelude();
    let err = elab_one(&env, SHADOW)
        .expect_err("a binder-bearing measure must not be resolved by the walker");
    assert!(
        is_routing_refusal(&err),
        "a measure the walker cannot analyse must leave routing untouched, got: {err}"
    );
}

// ═════════ the anti-regression: structural recursion stays structural ═════════

#[test]
fn a_structural_definition_with_an_agreeing_compound_measure_stays_structural() {
    // The risk R5 had to avoid: widening the measure analysis must not drag
    // structurally-recursive definitions onto the well-founded path. Here the
    // measure names the SAME parameter the detector picked, so `dec_arg`
    // survives and the definition still lowers through the recursor.
    const ADD_N: &str = "def addN (n m : Nat) : Nat := \
         match n with | Nat.zero => m | Nat.succ k => Nat.succ (addN k m)\n\
         termination_by n + 0";
    let mut env = Environment::with_prelude();
    register_one(&mut env, ADD_N)
        .expect("a structural definition with an agreeing measure must still elaborate");

    let value = env
        .get_const(&Name::from_string("addN"))
        .and_then(|c| c.value.clone())
        .expect("addN keeps its value");
    assert!(
        !head_is_wf_fix(&value),
        "addN must still lower STRUCTURALLY — R5 must not reroute a definition \
         whose measure agrees with the detected decreasing argument"
    );

    // And it still computes, so "structural" is not a claim about shape alone.
    register_one(&mut env, "theorem addN_2_3 : addN 2 3 = 5 := rfl")
        .expect("the structural lowering must still compute");
}
