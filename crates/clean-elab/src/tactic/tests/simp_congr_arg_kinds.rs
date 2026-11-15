// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! simp's congruence ARGUMENT KINDS — Lean's `FunInfo.hasFwdDeps`.
//!
//! `simp_children` descended an application by a binary `App(f, arg)` split
//! and simplified both halves unconditionally, so a position that a LATER
//! argument's type mentions was rewritten like any other and every sibling
//! that mentions it went stale. Lean's `congrArgs`
//! (`Meta/Tactic/Simp/Types.lean`) asks `getFunInfoNArgs` for the head's
//! parameter info and rewrites an argument with a proof only when
//! `!info.hasFwdDeps`; the kinds are named in `Meta/CongrTheorems.lean`
//! (`fixed`, `fixedNoParam`, `subsingletonInst`).
//!
//! The Pi arm had the same defect one constructor over: it rebuilt
//! `Expr::pi(bi, rewritten_domain, body)` with the BODY VERBATIM, so
//! `(h : A) → B h` became `(h : True) → B h` with `B : A → Prop`.
//! `mk_pi_domain_congr` refuses to prove that (`contains_bvar(body, 0)`), so
//! the ill-typed term travelled on as a claimed DEFINITIONAL change and killed
//! the whole declaration at the kernel re-check instead of simp reporting no
//! progress. Lean's `simpForall` rewrites such a domain only through
//! `forall_prop_domain_congr`, which transports the body's bound-proof
//! occurrences.
//!
//! Both replicas below are prelude-only and both close under pinned Lean
//! v4.30.0-rc2's own spelling of the same shape.

use clean_kernel::Environment;
use clean_parser::parse_file;

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};

fn elab_all(code: &str) -> Vec<Result<ElabResult, crate::ElabError>> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(code).expect("parse_file should succeed");
    decls
        .iter()
        .map(|decl| {
            let processed = preprocess_decl_with_context(decl, &mut file_ctx);
            elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
        })
        .collect()
}

#[track_caller]
fn assert_last_closed(code: &str, what: &str) {
    let results = elab_all(code);
    let last = results.last().expect("nothing parsed");
    assert!(
        matches!(last, Ok(ElabResult::Theorem { .. })),
        "{what}: expected a kernel-registered theorem, got {last:?}"
    );
}

/// The other direction: the last declaration must NOT register a theorem.
/// Used for the soundness-direction controls — a FALSE proposition of a shape
/// this file unfreezes must still be refused, not closed.
#[track_caller]
fn assert_last_not_closed(code: &str, what: &str) {
    let results = elab_all(code);
    let last = results.last().expect("nothing parsed");
    assert!(
        !matches!(last, Ok(ElabResult::Theorem { .. })),
        "{what}: expected a REFUSAL, but a theorem was registered: {last:?}"
    );
}

// ---------------------------------------------------------------------------
// A dependent ARGUMENT position (`@Exists P (fun h : P => …)`'s shape)
// ---------------------------------------------------------------------------

/// `D : (R : Prop) → (R → Prop) → Prop → Prop` is the minimal head with a
/// forward-dependent position: argument 1's TYPE mentions argument 0, so
/// rewriting `R` while the second argument keeps its `P` domain is exactly the
/// `@Exists True (fun h : P => …)` face.
///
/// `hq` rewrites the INDEPENDENT third position, so simp still makes progress
/// and the declaration's fate turns only on whether position 0 moved.
const DEP_ARG: &str = "\
axiom P : Prop
axiom Q0 : Prop
axiom R0 : Prop
axiom hp : P
axiom hq : Q0 = R0
axiom D : (R : Prop) → (R → Prop) → Prop → Prop
axiom f : P → Prop
axiom hd : D P f R0
";

/// With `hp : P` in the set, position 0 of `D P f Q0` would rewrite to `True`
/// while `f : P → Prop` stays — an ill-typed term simp used to keep, with the
/// congruence proof dropped, as a claimed definitional change.
#[test]
fn test_simp_does_not_rewrite_an_argument_a_later_argument_depends_on() {
    assert_last_closed(
        &format!("{DEP_ARG}theorem t : D P f Q0 := by\n  simp only [hp, hq]\n  exact hd\n"),
        "forward-dependent argument position",
    );
}

/// Control: the independent position DOES still rewrite, so the freeze is not
/// simply switching the App arm off.
#[test]
fn test_simp_still_rewrites_an_independent_argument_position() {
    assert_last_closed(
        &format!("{DEP_ARG}theorem t : D P f Q0 := by\n  simp only [hq]\n  exact hd\n"),
        "independent argument position",
    );
}

// ---------------------------------------------------------------------------
// A dependent Pi DOMAIN
// ---------------------------------------------------------------------------

/// `R0 → ∀ (h : P), B h`. The OUTER arrow is non-dependent, so its domain is
/// rewritten (`R0` → `S0`) as it always was; the INNER `∀ (h : P), B h` has a
/// body that mentions its binder, so its domain must not move — `∀ (h : True),
/// B h` is ill-typed and is what used to reach the kernel.
const DEP_PI: &str = "\
axiom P : Prop
axiom R0 : Prop
axiom S0 : Prop
axiom hp : P
axiom hrs : R0 = S0
axiom B : P → Prop
axiom hall : S0 → ∀ (h : P), B h
";

#[test]
fn test_simp_does_not_rewrite_a_pi_domain_its_body_depends_on() {
    assert_last_closed(
        &format!(
            "{DEP_PI}theorem t : R0 → ∀ (h : P), B h := by\n  simp only [hrs, hp]\n  exact hall\n"
        ),
        "dependent Pi domain",
    );
}

/// Control: a NON-dependent domain still rewrites, which is the half of the Pi
/// arm that was always correct.
#[test]
fn test_simp_still_rewrites_a_non_dependent_pi_domain() {
    assert_last_closed(
        &format!(
            "{DEP_PI}theorem t : R0 → ∀ (h : P), B h := by\n  simp only [hrs]\n  exact hall\n"
        ),
        "non-dependent Pi domain",
    );
}

// ---------------------------------------------------------------------------
// A position the DECLARED result type mentions, under a CONSTANT motive
// ---------------------------------------------------------------------------

/// The `mp_eq` shape of `proofs/trust-soundness/chc_tarski_unbounded.lean`
/// (the ouroboros gate), prelude-only. `simp only [bimpliesC, bnotC, borC]`
/// DELTA-unfolds the three definitions, so `bnotC P` becomes
/// `Bool.casesOn (fun _ => Bool) P true false` with `P` still a variable. On
/// the declared telescope of `Bool.casesOn` the major `t` is mentioned by the
/// result type `motive t`, so the freeze read off declared binder types left
/// `P` untouched: `hp : P = true` never fired and `h` stalled at
/// `Bool.rec (fun _ => Bool) Q true (Bool.casesOn (fun _ => Bool) P true
/// false) = true`, one iota short of `Q = true`. With the supplied motive
/// `fun _ => Bool`, `motive t` beta-reduces to `Bool` and nothing depends on
/// the major, which is exactly why `congrArg (Bool.casesOn motive) hp` is
/// well-typed.
const CONST_MOTIVE: &str = "\
def bnotC (a : Bool) : Bool := match a with | true => false | false => true
def borC (a : Bool) (b : Bool) : Bool := match a with | true => true | false => b
def bimpliesC (a : Bool) (b : Bool) : Bool := borC (bnotC a) b
";

#[test]
fn test_simp_rewrites_a_cases_on_major_whose_supplied_motive_is_constant() {
    assert_last_closed(
        &format!(
            "{CONST_MOTIVE}theorem t (P Q : Bool) (h : bimpliesC P Q = true) (hp : P = true) : \
             Q = true := by\n  simp only [hp, bimpliesC, bnotC, borC] at h\n  exact h\n"
        ),
        "casesOn major under a constant motive",
    );
}

/// Control: a result type that GENUINELY depends on the position keeps it
/// frozen. `mkT : (b : Bool) → T b`, so `mkT P` cannot become `mkT true` by
/// `congrArg` — `mkT` is not an `α → β`. `hq` rewrites the independent
/// conjunct, so simp makes progress and the declaration's fate turns only on
/// whether `mkT P` moved.
const DEP_RESULT: &str = "\
axiom Q0 : Prop
axiom R0 : Prop
axiom hq : Q0 = R0
axiom T : Bool → Type
axiom mkT : (b : Bool) → T b
axiom PT : {b : Bool} → T b → Prop
";

/// Soundness-direction control for the constant-motive unfreeze: the FALSE
/// twin of the `mp_eq` shape. With `hp : P = false`, `bimpliesC P Q` is
/// `borC (bnotC false) Q` = `borC true Q` = `true`, so the rewritten `h` says
/// `true = true` and carries no information about `Q`. Un-freezing the major
/// premise makes simp reach further into this term than it used to; it must
/// not reach a proof of `Q = true`.
///
/// This is a CONTROL, not a regression pin — it holds both with and without
/// the instantiated-telescope check. Its job is to pin the DIRECTION of that
/// change (strictly more complete, never more permissive) at the one shape
/// where the freeze was relaxed, rather than leaving it to the kernel
/// re-check to catch after the fact.
#[test]
fn test_a_false_theorem_of_the_constant_motive_shape_is_still_refused() {
    assert_last_not_closed(
        &format!(
            "{CONST_MOTIVE}theorem t (P Q : Bool) (h : bimpliesC P Q = true) (hp : P = false) : \
             Q = true := by\n  simp only [hp, bimpliesC, bnotC, borC] at h\n  exact h\n"
        ),
        "false twin of the casesOn constant-motive shape",
    );
}

#[test]
fn test_simp_still_freezes_a_position_the_supplied_result_type_depends_on() {
    assert_last_closed(
        &format!(
            "{DEP_RESULT}theorem t (P : Bool) (hp : P = true) (h : PT (mkT P) ∧ Q0) : \
             PT (mkT P) ∧ R0 := by\n  simp only [hp, hq] at h\n  exact h\n"
        ),
        "dependent result type",
    );
}
