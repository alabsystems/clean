// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The scheduled, fail-closed caller of the differential fidelity gate.
//!
//! # READ THIS FIRST: what this gate does NOT establish
//!
//! **This is a Rust-versus-Rust differential check. It says NOTHING about the
//! reflected `KExpr` model, and wiring it does not close, advance, or partially
//! close Layer 2 of `docs/SELF_VERIFICATION_PROGRAM.md`.** The comparand,
//! [`BootstrapChecker`], is a SECOND HAND-WRITTEN RUST CHECKER
//! (`crates/clean-verify/src/bootstrap_checker.rs`) with **zero** references to
//! `KExpr`, `Specification`, or any reflected object — measured 2026-08-28,
//! `grep -c KExpr crates/clean-verify/src/bootstrap_checker.rs` → `0`, the same
//! measurement `docs/SELF_VERIFICATION_CERTIFICATE.md` records. The model↔checker
//! gap is exactly as open after this file as before it.
//!
//! The word "micro-checker" is overloaded in this tree and has already caused
//! one false claim to circulate: `fidelity_gate.rs`'s own comments call
//! `BootstrapChecker` "the micro-checker", it is NOT the reflected model, and it
//! is also NOT the independent checker in `crates/clean-kernel/src/micro/`.
//! Three distinct objects, one word.
//!
//! # The scope, in numbers this file pins mechanically
//!
//! * **63** closed corpus terms (`deterministic_core_corpus`), pinned by
//!   `corpus_scope_is_pinned_at_sixty_three_closed_terms` below.
//! * a **6-of-25-constructor** fragment, `{Sort, BVar, Pi, Lam, App, Let}`,
//!   with **no environment** — `Const`, `Lit`, `Proj`, `FVar`, `SProp`,
//!   `Squash`, `Cubical*` and `ZFC*` are all out, and are COUNTED as excluded
//!   with a reason rather than silently skipped.
//! * a **pinned-empty** known-divergence allowlist, so every disagreement is
//!   new and every new disagreement fails.
//!
//! Six of twenty-five constructors, closed terms only, no environment: that is
//! a small corner of the kernel's inference surface, and a green run here is
//! evidence about that corner and nothing wider.
//!
//! # What was disconnected, and what connecting it buys
//!
//! `docs/SELF_VERIFICATION_PROGRAM.md` (Layer 2, item 1) and
//! `docs/SELF_VERIFICATION_CERTIFICATE.md` both recorded: "nothing runs the
//! gate — `scripts/local_gate.sh` invokes `clean-verify` zero times and
//! `audit_fidelity()` has no caller outside its own test." Re-measured
//! 2026-08-28 and still true: the two `clean-verify` mentions in
//! `scripts/local_gate.sh` are comments, and `audit_fidelity` appeared nowhere
//! in the tree outside `fidelity_gate.rs`'s own `#[cfg(test)]` module and the
//! `pub use` in `lib.rs`.
//!
//! This file is that missing caller: a target `scripts/verify_runner.py`
//! enumerates and schedules on its own (`clean-verify::test::fidelity_gate_lane`),
//! with its own recorded verdict and its own input digest, registered in
//! `data/gate_registry.json`. What that buys is only this: the gate now has a
//! scheduled runner and a named row, so it can go red somewhere a human looks.
//! It buys no new claim about the kernel and no new claim about the model.
//!
//! It is deliberately NOT in `scripts/local_gate.sh` or the pre-push hook: it
//! needs a `clean-verify` build, which is the same cost class that put
//! `gate::masquerade` in the suite rather than in a leg.
//!
//! [`BootstrapChecker`]: clean_verify::BootstrapChecker

use clean_kernel::{BinderInfo, Expr, Level, Name};
use clean_verify::fidelity_gate::{audit_whnf_fidelity, KNOWN_DIVERGENCES};
use clean_verify::{
    audit_fidelity, deterministic_core_corpus, in_supported_fragment, run_gate, BootstrapChecker,
    FidelityMetric, NewDivergenceReport,
};

/// The audit lane itself: the real corpus must agree, and must do so
/// non-vacuously.
///
/// This is the `#[must_use]`-shaped entry point `fidelity_gate.rs` documents as
/// "intended entry point for a `clean audit` fidelity lane" and which, until
/// this file, nothing outside its own test module called.
#[test]
fn audit_fidelity_lane_is_green_and_non_vacuous() {
    let metric = audit_fidelity();
    eprintln!("{}", metric.report());

    assert!(
        metric.passed(),
        "NEW (non-allowlisted) model↔kernel divergences: {:?}",
        metric.new_divergences
    );
    // Non-vacuity: a gate that checked nothing would also "pass".
    assert!(
        metric.terms_supported > 20,
        "the corpus stopped exercising the gate: terms_supported={}",
        metric.terms_supported
    );
    assert_eq!(
        metric.terms_excluded_unsupported, 0,
        "the deterministic corpus is in-fragment by construction"
    );
    assert_eq!(
        metric.coverage_count(),
        6,
        "all six fragment constructors must be exercised"
    );
    // The fail-closed accounting identity: nothing may be dropped on the floor.
    assert_eq!(
        metric.terms_supported,
        metric.terms_agreed + metric.terms_known_divergent,
        "supported terms must be fully accounted for"
    );
    assert!(
        KNOWN_DIVERGENCES.is_empty(),
        "the allowlist is pinned empty; a new entry needs review, not a test edit"
    );
}

/// The STEP-fidelity half: the real kernel's `whnf` must agree structurally
/// with the independent reducer over the same corpus.
#[test]
fn audit_whnf_fidelity_lane_is_green_and_non_vacuous() {
    let agreed = audit_whnf_fidelity().expect("whnf step-fidelity divergence");
    assert_eq!(
        agreed,
        deterministic_core_corpus().len(),
        "every corpus term must have been compared, not skipped"
    );
    assert!(agreed > 20, "the whnf lane must not be vacuous");
}

/// DIRECTION 2 of the two-way proof: the verdict is not hardcoded true.
///
/// A metric carrying one new divergence must FAIL, and the same metric with it
/// removed must pass — so `passed()` is reading the evidence rather than
/// returning a constant. Paired with the arm above (which must stay GREEN on
/// the real corpus), this is the inline self-test this row is demonstrated by:
/// a gate that stops saying no is not a fixed gate, it is a deleted one.
#[test]
fn verdict_is_falsifiable_not_hardcoded() {
    let mut metric = audit_fidelity();
    assert!(metric.passed(), "the real corpus must start green");

    metric.new_divergences.push(NewDivergenceReport {
        key: 0xDEAD_BEEF,
        detail: "planted divergence (test only)".to_string(),
    });
    assert!(
        !metric.passed(),
        "one new divergence must make the gate FAIL — the verdict is hardcoded"
    );
    let report = metric.report();
    assert!(
        report.contains("deadbeef") && report.contains("VERDICT: FAIL"),
        "the failing report must name the divergence it failed on and say FAIL:\n{report}"
    );

    metric.new_divergences.clear();
    assert!(metric.passed(), "and removing it must restore the pass");
}

/// The differential really runs BOTH sides: the agreed answer is the REDUCT,
/// which is not the input.
///
/// Without this, "the two checkers agreed" would be satisfied by a comparison
/// that never reduced anything.
#[test]
fn the_comparison_reads_real_kernel_output() {
    let checker = BootstrapChecker::new();

    // (λ (x : Type 0). x) Prop  —  β-reduces to Prop on both sides.
    let redex = Expr::app(
        Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0)),
        Expr::prop(),
    );
    let agreed = checker
        .recheck_kernel_whnf(&redex)
        .expect("beta redex must whnf-agree");
    assert_eq!(agreed, Expr::prop(), "the agreed whnf is the REDUCT");
    assert_ne!(agreed, redex, "the reduction genuinely fired");

    // And the inference side returns a type, not a rubber stamp.
    let inferred = checker
        .recheck_kernel_inference(&Expr::prop())
        .expect("Prop must infer on both sides");
    assert_eq!(inferred, Expr::type_(), "Prop : Type 0");
}

/// Out-of-fragment terms are COUNTED with a reason, never silently skipped.
///
/// This is the difference between "the gate passed" and "the gate declined to
/// look": an exclusion that vanished would inflate agreement for free.
#[test]
fn out_of_fragment_terms_are_counted_with_a_reason() {
    let unsupported = vec![
        Expr::const_(Name::anon(), Vec::<Level>::new()),
        Expr::nat_lit(7),
    ];
    let metric = run_gate(&unsupported);

    assert_eq!(metric.terms_supported, 0);
    assert_eq!(metric.terms_excluded_unsupported, 2);
    assert_eq!(metric.exclusion_histogram.get("Const"), Some(&1));
    assert_eq!(metric.exclusion_histogram.get("Lit"), Some(&1));
    assert_eq!(
        metric.terms_total,
        metric.terms_supported + metric.terms_excluded_unsupported
    );

    // …and the fragment predicate agrees, term by term.
    assert_eq!(in_supported_fragment(&unsupported[0], 0), Err("Const"));
    assert_eq!(in_supported_fragment(&unsupported[1], 0), Err("Lit"));
}

/// SCOPE RATCHET. The published scope of this gate — "63 closed terms in a
/// six-of-twenty-five-constructor, environment-less fragment" — is quoted in
/// `docs/SELF_VERIFICATION_CERTIFICATE.md` and in this file's header. Pin it,
/// so widening the corpus cannot silently make those sentences wrong.
///
/// If this fails because the corpus grew: that is good news, and the fix is to
/// update the number HERE and in the certificate, in the same commit.
#[test]
fn corpus_scope_is_pinned_at_sixty_three_closed_terms() {
    let corpus = deterministic_core_corpus();
    assert_eq!(
        corpus.len(),
        63,
        "the certificate and this file's header both quote 63; update all three together"
    );
    for term in &corpus {
        assert_eq!(
            in_supported_fragment(term, 0),
            Ok(()),
            "every corpus term must be closed and in-fragment: {term:?}"
        );
    }
}

/// An empty run is not a pass. A `FidelityMetric` that observed nothing has an
/// empty divergence list and would report `passed()` — so the lane's own
/// non-vacuity assertions above are load-bearing, and this arm says why in one
/// place rather than leaving it implicit.
#[test]
fn an_empty_metric_passes_which_is_why_non_vacuity_is_asserted() {
    let empty: FidelityMetric = run_gate(&[]);
    assert_eq!(empty.terms_total, 0);
    assert!(
        empty.passed(),
        "documented, not endorsed: `passed()` is 'no new divergences', so a run \
         that checked nothing passes. Every lane above therefore asserts a \
         non-zero, fully-accounted corpus."
    );
}
