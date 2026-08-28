// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **R3 — `gcd` elaborates.** The two-language design's §1 demo, end to end:
//! parse → elaborate → kernel-check → register → COMPUTE.
//!
//! What made it possible (see `r3_gcd_multiparam_probes.rs` for the
//! before-measurements):
//!
//! * **A wider SIGNATURE with a one-parameter measure.** `gcd` has two
//!   parameters; `termination_by b` names one. The lowering fixes on that one
//!   and threads the other through the MOTIVE (`C x = Nat → Nat`), so a
//!   recursive call may change every argument — `gcd b (a % b)` changes both —
//!   while the obligation stays the single-parameter `Nat.lt (a % b) b`.
//!   NOT general multi-parameter termination: a measure naming two parameters
//!   is still refused, and this file pins that refusal.
//! * **Routing.** An explicit `termination_by <parameter>` outranks the
//!   structural auto-detector when the two name different parameters. Before
//!   this, `gcd` never reached the well-founded lowering at all: the detector
//!   read `gcd b (a % b)`'s first argument (`b`, spelled differently from the
//!   first parameter `a`) as "parameter 0 decreases", routed to the structural
//!   path, and the self-call died as `RecursionOutsideFragment`.
//! * **The decrease.** `a % b < b` under `h : 0 < b` is `Nat.mod_lt a b h` —
//!   an AXIOM-FREE prelude `Theorem` that was already there
//!   (`clean-kernel/src/env/data_types_nat_div_mod_lemmas.rs`). Nothing was
//!   added to the kernel or the prelude for R3; the cascade gained a tier that
//!   reaches an existing proof.
//!
//! HONESTY RULES (as in the probe batteries): every ADMIT is paired with a
//! refused MUTATION at the same layer, and every refusal asserts its reason.

use clean_elab::{
    elaborate_decl, elaborate_decl_and_register, preprocess_decl_with_context, ElabError,
    ElabResult, FileContext,
};
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, ExprKind};
use clean_parser::parse_file;

/// `gcd`, in the spelling whose `else`-branch hypothesis bounds `b` away from
/// zero. Two parameters, a one-parameter measure, and a recursive call that
/// changes BOTH arguments.
const GCD: &str = "def gcd (a b : Nat) : Nat := \
     if h : 0 < b then gcd b (a % b) else a\n\
     termination_by b";

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

/// Does `Nat.mod_lt` occur anywhere in the term? (Same `Debug` caveat, so it
/// is answered by a fold over the constants, not by a string match.)
fn mentions_const(value: &Expr, wanted: &str) -> bool {
    let wanted = Name::from_string(wanted);
    let mut found = false;
    let mut stack = vec![value.clone()];
    while let Some(e) = stack.pop() {
        match e.kind() {
            ExprKind::Const(name, _) if *name == wanted => {
                found = true;
                break;
            }
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
                stack.push(Expr::clone(inner));
            }
            _ => {}
        }
    }
    found
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
        "{name} must be lowered through WellFounded.fix, got {value:?}"
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

/// An environment with `gcd` registered.
fn env_with_gcd() -> Environment {
    let mut env = Environment::with_prelude();
    register_one(&mut env, GCD).expect("R3: `gcd` must elaborate and kernel-verify");
    env
}

// ═══════════════════ R3's acceptance: gcd elaborates ═══════════════════

#[test]
fn test_gcd_elaborates_kernel_verifies_and_is_axiom_free() {
    let env = env_with_gcd();
    assert_wf_definition_registered(&env, "gcd");

    // The decrease must be the NAMED prelude theorem, not a tactic artifact:
    // the emitted term carries `Nat.mod_lt` at the recursive call site, so the
    // termination argument is readable in the term the kernel checked.
    let value = env
        .get_const(&Name::from_string("gcd"))
        .and_then(|c| c.value.clone())
        .expect("gcd keeps its value");
    assert!(
        mentions_const(&value, "Nat.mod_lt"),
        "the decreasing proof must be `Nat.mod_lt`"
    );
}

/// **R3's acceptance and the design's original demo: `gcd 12 18 = 6`.**
///
/// `gcd 12 18 → gcd 18 12 → gcd 12 6 → gcd 6 0 → 6`. Closed, so the
/// `WellFounded.fix` application must actually grind through `Acc.rec` and
/// the measure relation's accessibility witness — this is the computation
/// claim, not a typing claim.
#[test]
fn test_gcd_12_18_computes_to_6() {
    let mut env = env_with_gcd();
    register_one(&mut env, "theorem gcd_12_18 : gcd 12 18 = 6 := rfl")
        .expect("R3 ACCEPTANCE: `gcd 12 18` must COMPUTE to 6 by kernel reduction");

    // MUTATION CONTROL: the computation is a decision, not a rubber stamp.
    let wrong = register_one(&mut env, "theorem gcd_12_18_bad : gcd 12 18 = 5 := rfl");
    assert!(
        wrong.is_err(),
        "`gcd 12 18 = 5` must be REFUSED — otherwise the computation evidence \
         above is vacuous"
    );
    assert!(
        env.get_const(&Name::from_string("gcd_12_18_bad")).is_none(),
        "a refused theorem must register nothing"
    );
}

/// More closed values, both argument orders, plus the identities a gcd must
/// satisfy. Each is `rfl`, so each is a kernel reduction.
#[test]
fn test_gcd_closed_values_and_identities() {
    let mut env = env_with_gcd();
    for (index, source) in [
        "theorem gcd_c0 : gcd 18 12 = 6 := rfl",
        "theorem gcd_c1 : gcd 7 13 = 1 := rfl",
        "theorem gcd_c2 : gcd 0 5 = 5 := rfl",
        "theorem gcd_c3 : gcd 5 0 = 5 := rfl",
        "theorem gcd_c4 : gcd 48 18 = 6 := rfl",
        "theorem gcd_c5 : gcd 270 192 = 6 := rfl",
    ]
    .into_iter()
    .enumerate()
    {
        register_one(&mut env, source)
            .unwrap_or_else(|e| panic!("closed value #{index} (`{source}`) must compute: {e}"));
    }

    // MUTATION CONTROL at the same layer.
    assert!(
        register_one(&mut env, "theorem gcd_c_bad : gcd 270 192 = 7 := rfl").is_err(),
        "a wrong closed value must be refused"
    );
}

/// The defining equations behave — at an OPEN first argument.
///
/// The base equation `gcd a 0 = a` holds by `rfl` for every `a`: the fix
/// unfolds one layer at `b = 0`, `Nat.decLt 0 0` reduces to `isFalse`, and the
/// `dite` takes the else branch. This is the equation lemma a caller actually
/// reasons with, and it is DEFINITIONAL here rather than needing an
/// `.eq_def` machinery.
#[test]
fn test_gcd_base_equation_holds_at_an_open_argument() {
    let mut env = env_with_gcd();
    register_one(&mut env, "theorem gcd_base (a : Nat) : gcd a 0 = a := rfl").expect(
        "the base equation `gcd a 0 = a` must be rfl-definitional at an OPEN \
         `a` — the recursion parameter is what must be concrete, not the \
         threaded one",
    );

    // MUTATION CONTROLS: the open equation is not a rubber stamp.
    assert!(
        register_one(
            &mut env,
            "theorem gcd_base_bad (a : Nat) : gcd a 0 = 0 := rfl"
        )
        .is_err(),
        "`gcd a 0 = 0` must be refused"
    );
    assert!(
        register_one(
            &mut env,
            "theorem gcd_swap_bad (a : Nat) : gcd 0 a = a := rfl"
        )
        .is_err(),
        "`gcd 0 a = a` must be refused: `a` is the RECURSION parameter there, \
         so the fix does not unfold to a normal form at an open `a`"
    );
}

// ═════════ the widened lowering, and the boundary it did NOT move ═════════

/// A wider signature whose non-measure parameter is threaded through
/// UNCHANGED — the simplest shape the widening admits.
#[test]
fn test_wider_signature_with_a_carried_parameter() {
    let mut env = Environment::with_prelude();
    register_one(
        &mut env,
        "def addDown (a b : Nat) : Nat := if h : 0 < b then a + addDown a (b - 1) else 0\n\
         termination_by b",
    )
    .expect("a two-parameter WF definition carrying `a` unchanged must elaborate");
    assert_wf_definition_registered(&env, "addDown");
    register_one(&mut env, "theorem addDown_3_4 : addDown 3 4 = 12 := rfl")
        .expect("addDown 3 4 = 3+3+3+3 = 12");
    assert!(
        register_one(&mut env, "theorem addDown_bad : addDown 3 4 = 11 := rfl").is_err(),
        "mutation control"
    );
}

/// The recursion parameter need not be LAST: `termination_by a` on `(a b)`
/// puts the first parameter at the front of the fix telescope and threads the
/// second one through the motive.
#[test]
fn test_recursion_parameter_may_be_the_first_of_several() {
    let mut env = Environment::with_prelude();
    register_one(
        &mut env,
        "def firstDown (a b : Nat) : Nat := if h : 0 < a then b + firstDown (a - 1) b else 0\n\
         termination_by a",
    )
    .expect("the measure may name the FIRST parameter; the others still thread");
    assert_wf_definition_registered(&env, "firstDown");
    register_one(
        &mut env,
        "theorem firstDown_3_5 : firstDown 3 5 = 15 := rfl",
    )
    .expect("firstDown 3 5 = 5+5+5 = 15");
    assert!(
        register_one(
            &mut env,
            "theorem firstDown_bad : firstDown 3 5 = 14 := rfl"
        )
        .is_err(),
        "mutation control"
    );
}

/// **The boundary R3 did not move, and where phase 3 later moved it.**
///
/// R3 refused every measure mentioning two parameters, at a SHAPE gate, and
/// this test pinned that. Phase 3 (2026-08-25, `wf_recursion::sum_measure`)
/// lowers the SUM case, so the shape gate now applies only to non-sum
/// multi-parameter measures — that half is pinned in
/// `wf_sum_measure_e2e::test_a_non_sum_multi_parameter_measure_is_still_refused_with_the_fix`
/// and re-asserted below on a `b - a` measure.
///
/// `lex` itself is UNCHANGED in outcome and is the more interesting half: its
/// sum measure genuinely does not decrease (`0 < a + b` does not bound `a`
/// away from zero, and `(a-1) + (b+0) = a + b` at `a = 0`), so it is still
/// refused — now at the DECREASE, which is the honest place. A widening that
/// had made this fixture pass would have been a false verify.
#[test]
fn test_two_parameter_measure_boundary() {
    let env = Environment::with_prelude();

    // A non-sum multi-parameter measure: still refused at the SHAPE gate.
    let err = elab_one(
        &env,
        "def lexNonSum (a b : Nat) : Nat := \
         if h : 0 < a + b then lexNonSum (a - 1) (b + 0) else 0\n\
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
        feature.contains("Ways forward"),
        "v7/D3: a refusal must carry the fix, with options; got: {feature}"
    );

    // A SUM measure that does not decrease: refused at the DECREASE.
    let err = elab_one(
        &env,
        "def lex (a b : Nat) : Nat := if h : 0 < a + b then lex (a - 1) (b + 0) else 0\n\
         termination_by a + b",
    )
    .expect_err("`0 < a + b` does not make `a + b` shrink");
    let ElabError::Unsupported { feature } = &err else {
        panic!("must fail closed as `Unsupported`, got: {err:?}");
    };
    assert!(
        feature.contains("no decreasing proof was found"),
        "a non-decreasing sum must be refused at the decrease, got: {feature}"
    );
}

/// A measure mentioning NO parameter cannot decrease. Refused up front, with
/// the fix, rather than as an undischargeable obligation deep in the cascade.
#[test]
fn test_measure_naming_no_parameter_is_refused_up_front() {
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

/// **The residual R3 recorded, and how far R5/R6 closed it.**
///
/// R3's routing rule fired only for a measure spelled as a bare parameter
/// NAME, so any other spelling left routing structural and the definition died
/// `RecursionOutsideFragment` — the wrong refusal. R5 closed that for
/// one-parameter measures (`b + 0`, `b.toNat`); **R6 (2026-08-25) closes it
/// for a SUM over several parameters**, because those are now lowered.
///
/// `lexShadowed` is exactly the shape R3 pinned: the self-call passes a bare
/// `b` at position 1, which the structural detector reads as a decrease. It
/// now reaches the well-founded lowering and is refused THERE — its sum still
/// does not decrease (`0 < a + b` does not bound `a` away from zero), so the
/// outcome is unchanged and only the diagnostic improved, which is the whole
/// point of v7/D3.
///
/// The seam has NOT closed for a non-sum multi-parameter measure: that is the
/// second half of this test, and it is where the next increment starts.
#[test]
fn test_the_router_now_yields_to_a_sum_measure_but_not_to_a_non_sum_one() {
    let env = Environment::with_prelude();

    // R6: a SUM measure beats the structural auto-detector.
    let err = elab_one(
        &env,
        "def lexShadowed (a b : Nat) : Nat := \
         if h : 0 < a + b then lexShadowed (a - 1) b else 0\n\
         termination_by a + b",
    )
    .expect_err("still refused — the question is only WHICH refusal");
    let ElabError::Unsupported { feature } = &err else {
        panic!(
            "R6: a sum measure must now reach the well-founded lowering, not \
             the structural fragment refusal. Got: {err:?}"
        );
    };
    assert!(
        feature.contains("no decreasing proof was found"),
        "and it must be refused at the decrease, got: {feature}"
    );

    // MEASURED RESIDUAL: a NON-sum multi-parameter measure still does not
    // override the detector, so this shape keeps the fragment refusal. If this
    // ever becomes `Unsupported`, the router was widened again — re-measure
    // the structural corpus.
    let err = elab_one(
        &env,
        "def lexShadowedNonSum (a b : Nat) : Nat := \
         if h : 0 < a + b then lexShadowedNonSum (a - 1) b else 0\n\
         termination_by b - a",
    )
    .expect_err("still refused — the question is only WHICH refusal");
    assert!(
        matches!(err, ElabError::RecursionOutsideFragment { .. }),
        "MEASURED RESIDUAL: a non-sum measure does not override the structural \
         auto-detector. Got: {err:?}"
    );
}

/// A partially-applied self-call has no `rec` spelling: `rec argᵢ proof` is
/// typed at the MOTIVE, which re-binds every other parameter, so all of them
/// must be supplied. Refused loudly, with the count.
#[test]
fn test_partially_applied_self_call_is_refused_with_the_counts() {
    let env = Environment::with_prelude();
    let err = elab_one(
        &env,
        "def partialApp (a b : Nat) : Nat := \
         if h : 0 < b then (partialApp (b - 1)) a else 0\n\
         termination_by b",
    )
    .expect_err("a partially-applied self-call is not lowered");
    let ElabError::Unsupported { feature } = &err else {
        panic!("must fail closed as `Unsupported`, got: {err:?}");
    };
    assert!(
        feature.contains("termination_by"),
        "diagnostic must name the construct, got: {feature}"
    );
}

// ═══════════════ the routing rule, and its blast radius ═══════════════

/// **The routing regression control.** When the explicit measure names the
/// SAME parameter the structural detector picked, routing is untouched: a
/// structurally-recursive definition carrying `termination_by n` still lowers
/// structurally (through the recursor, NOT through `WellFounded.fix`). The
/// new rule fires only on disagreement.
#[test]
fn test_structural_recursion_with_agreeing_termination_by_stays_structural() {
    let mut env = Environment::with_prelude();
    register_one(
        &mut env,
        "def wfOk (n : Nat) : Nat :=\n  match n with\n  | 0 => 0\n  | Nat.succ m => wfOk m\n\
         termination_by n",
    )
    .expect("structural recursion carrying `termination_by n` must still elaborate");
    let value = env
        .get_const(&Name::from_string("wfOk"))
        .and_then(|c| c.value.clone())
        .expect("wfOk keeps its value");
    assert!(
        !head_is_wf_fix(&value),
        "the agreeing case must NOT be re-routed to the well-founded lowering \
         — it lowers through the recursor as before; got {value:?}"
    );
    assert!(
        !mentions_const(&value, "WellFounded.fix")
            && !mentions_const(&value, "Nat.accNatLt")
            && mentions_const(&value, "Nat.rec"),
        "and it must still be a plain recursor application with no \
         accessibility machinery anywhere in it; got {value:?}"
    );
}

/// The other half of the routing rule: the auto-detector's answer for `gcd`
/// (parameter 0, `a`) is a HEURISTIC artifact — `b` is not structurally
/// smaller than `a`. Naming a different parameter in `termination_by` is what
/// overrides it, and dropping the annotation restores the old refusal.
#[test]
fn test_without_the_annotation_gcd_is_still_outside_the_fragment() {
    let env = Environment::with_prelude();
    let err = elab_one(
        &env,
        "def gcdNoHint (a b : Nat) : Nat := if h : 0 < b then gcdNoHint b (a % b) else a",
    )
    .expect_err("with no `termination_by`, nothing names the recursion parameter");
    assert!(
        matches!(err, ElabError::RecursionOutsideFragment { params: 2, .. }),
        "the refusal must still be the recursion-fragment diagnostic, got: {err:?}"
    );
}
