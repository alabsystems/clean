// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for the axiom refutation gate
//! (`clean_verify::axiom_refutation_gate`).
//!
//! THE NON-NEGOTIABLE DELIVERABLE is the regression test
//! [`gate_refutes_both_retired_false_micro_whnf_statements`]: it reconstructs the
//! two FALSE axioms that were retired by hand in commit `11e047bd` —
//!
//! - `micro_whnf_beta`:
//!   `forall ty body arg, Eq MicroExpr (micro_whnf (app (lam ty body) arg))
//!    (micro_whnf (micro_instantiate body arg))`
//! - `micro_whnf_idempotent`:
//!   `forall e, Eq MicroExpr (micro_whnf (micro_whnf e)) (micro_whnf e)`
//!
//! — and DEMONSTRATES the gate REFUTES them via a real kernel evaluation (NOT a
//! hardcoded assert). The witnesses are exactly the "contractum is itself a
//! redex" shapes from the retirement diagnosis: a one-step `micro_whnf` leaves
//! an inner redex un-reduced, so it differs from the (recursively-`whnf`-ed or
//! fully-substituted) right-hand side.
//!
//! If the gate could not refute these, it would not work — these tests are the
//! proof that the engine genuinely reduces terms via the kernel and compares.

use std::collections::BTreeSet;

use clean_verify::axiom_ratchet::live_env_axioms;
use clean_verify::axiom_refutation_gate::{refute_statement, run_gate, ExclusionReason};
use clean_verify::spec::ProofStatus;
use clean_verify::test_utils::run_with_stack;
use clean_verify::Specification;

/// The two FALSE statements that were retired in `11e047bd`, reconstructed
/// verbatim (the universally-quantified equations between computable terms).
const OLD_FALSE_MICRO_WHNF_BETA: &str =
    "forall (ty : MicroExpr) (body : MicroExpr) (arg : MicroExpr), \
     Eq MicroExpr (micro_whnf (MicroExpr.app (MicroExpr.lam ty body) arg)) \
     (micro_whnf (micro_instantiate body arg))";

const OLD_FALSE_MICRO_WHNF_IDEMPOTENT: &str =
    "forall (e : MicroExpr), Eq MicroExpr (micro_whnf (micro_whnf e)) (micro_whnf e)";

/// THE non-negotiable regression: the gate genuinely refutes BOTH retired FALSE
/// `micro_whnf` statements, with a concrete witness on which the two sides are
/// NOT definitionally equal.
#[test]
fn gate_refutes_both_retired_false_micro_whnf_statements() {
    run_with_stack(|| {
        let spec = Specification::new().expect("spec builds");

        // ── micro_whnf_beta (FALSE form) ─────────────────────────────────
        let beta = refute_statement(
            &spec,
            "micro_whnf_beta_OLD_FALSE",
            OLD_FALSE_MICRO_WHNF_BETA,
        )
        .expect("statement elaborates");
        let beta_refutation = beta
            .expect("micro_whnf_beta (false form) must be IN-SCOPE (a computable equation)")
            .expect(
                "micro_whnf_beta (false form) MUST be refuted — the gate found no \
                 counterexample, so it does not work",
            );
        eprintln!(
            "REFUTED micro_whnf_beta(FALSE) on witness [{}]:\n  lhs(whnf) = {}\n  rhs(whnf) = {}",
            beta_refutation.witness.join("; "),
            beta_refutation.lhs_whnf,
            beta_refutation.rhs_whnf,
        );
        assert_ne!(
            beta_refutation.lhs_whnf, beta_refutation.rhs_whnf,
            "the refuting witness must make the two reduced sides genuinely differ"
        );

        // ── micro_whnf_idempotent (FALSE form) ───────────────────────────
        let idem = refute_statement(
            &spec,
            "micro_whnf_idempotent_OLD_FALSE",
            OLD_FALSE_MICRO_WHNF_IDEMPOTENT,
        )
        .expect("statement elaborates");
        let idem_refutation = idem
            .expect("micro_whnf_idempotent (false form) must be IN-SCOPE (a computable equation)")
            .expect(
                "micro_whnf_idempotent (false form) MUST be refuted — the gate found no \
                 counterexample, so it does not work",
            );
        eprintln!(
            "REFUTED micro_whnf_idempotent(FALSE) on witness [{}]:\n  lhs(whnf) = {}\n  rhs(whnf) = {}",
            idem_refutation.witness.join("; "),
            idem_refutation.lhs_whnf,
            idem_refutation.rhs_whnf,
        );
        assert_ne!(
            idem_refutation.lhs_whnf, idem_refutation.rhs_whnf,
            "the refuting witness must make the two reduced sides genuinely differ"
        );
    });
}

/// The TRUE single-step replacements (the forms that ACTUALLY landed at
/// `11e047bd`) must NOT be refuted — the gate must not produce false positives.
///
/// - `micro_whnf (app (lam ty body) arg) = micro_instantiate body arg`
///   (ONE beta step, no re-normalization) — genuinely true.
/// - `micro_whnf (micro_whnf (lam ty body)) = micro_whnf (lam ty body)`
///   (idempotence restricted to a weak-head-normal value) — genuinely true.
#[test]
fn gate_does_not_refute_the_true_single_step_replacements() {
    run_with_stack(|| {
        let spec = Specification::new().expect("spec builds");

        let true_beta = refute_statement(
            &spec,
            "micro_whnf_beta_TRUE",
            "forall (ty : MicroExpr) (body : MicroExpr) (arg : MicroExpr), \
             Eq MicroExpr (micro_whnf (MicroExpr.app (MicroExpr.lam ty body) arg)) \
             (micro_instantiate body arg)",
        )
        .expect("elaborates");
        match true_beta {
            Ok(None) => {}
            Ok(Some(r)) => panic!("TRUE single-step beta wrongly refuted: {r:?}"),
            Err(reason) => panic!("TRUE single-step beta wrongly excluded: {reason:?}"),
        }

        let true_idem = refute_statement(
            &spec,
            "micro_whnf_idempotent_TRUE",
            "forall (ty : MicroExpr) (body : MicroExpr), \
             Eq MicroExpr (micro_whnf (micro_whnf (MicroExpr.lam ty body))) \
             (micro_whnf (MicroExpr.lam ty body))",
        )
        .expect("elaborates");
        match true_idem {
            Ok(None) => {}
            Ok(Some(r)) => panic!("TRUE restricted idempotence wrongly refuted: {r:?}"),
            Err(reason) => panic!("TRUE restricted idempotence wrongly excluded: {reason:?}"),
        }
    });
}

/// The live gate over the current (post-`11e047bd`) spec PASSES: NONE of the
/// currently-admitted computable axioms is refuted. (If this ever fails, it is a
/// REAL FINDING — a live false axiom — not a flake; the message says so.)
///
/// It also asserts the coverage boundary is fully accounted-for and printed.
#[test]
fn live_spec_gate_passes_and_accounts_for_every_axiom() {
    run_with_stack(|| {
        let spec = Specification::new().expect("spec builds");
        let report = run_gate(&spec);
        eprintln!("{}", report.report());

        assert!(
            report.passed(),
            "a currently-LIVE computable axiom was REFUTED — REAL soundness finding, \
             not a flake: {:?}",
            report.refutations
        );

        // Every admitted axiom is accounted for: evaluated XOR excluded-with-reason.
        assert_eq!(
            report.total_axioms,
            report.evaluated.len() + report.excluded.len(),
            "coverage boundary must be exhaustive (no silent skips)"
        );
        assert!(report.total_axioms > 0, "the spec must admit some axioms");

        // The two retired FALSE micro_whnf axioms are gone (drained to
        // DerivedProved): they must NOT appear as live admitted axioms.
        assert!(
            !report.evaluated.contains(&"micro_whnf_beta".to_string())
                && !report.excluded.contains_key("micro_whnf_beta"),
            "micro_whnf_beta must no longer be an admitted axiom (it was retired)"
        );
        assert!(
            !report
                .evaluated
                .contains(&"micro_whnf_idempotent".to_string())
                && !report.excluded.contains_key("micro_whnf_idempotent"),
            "micro_whnf_idempotent must no longer be an admitted axiom (it was retired)"
        );
    });
}

/// Brick 5 of the micro-band drain PROVED `kernel_to_micro_instantiate` (it was
/// a `HelperAxiom`; it is now a `DerivedProved` theorem via the KExpr.rec/Nat.rec
/// commutation suite `kernel_to_micro_{lift_bvar_commute, lift_commute,
/// instantiate_bvar_geq_commute, instantiate_bvar_commute, instantiate_at_commute}`),
/// so it LEAVES the admitted-axiom population. This test pins BOTH facts:
///   (1) the spec definition is `DerivedProved`, `is_axiom:false`, carries a proof
///       term, and is ABSENT from the live `ConstantKind::Axiom` census; and
///   (2) the equation it proves is STILL evaluated on the KExpr battery and
///       SURVIVES refutation — a truth cross-check that the proof and the gate's
///       independent reduction agree (a refutation here would be a real finding).
#[test]
fn kernel_to_micro_instantiate_is_proved_and_survives() {
    run_with_stack(|| {
        let spec = Specification::new().expect("spec builds");

        // (1) It is no longer an admitted axiom — it is a proved theorem.
        let def = spec
            .get_definition("kernel_to_micro_instantiate")
            .expect("kernel_to_micro_instantiate should be a tracked SpecDefinition");
        assert!(
            !def.is_axiom,
            "kernel_to_micro_instantiate must no longer be an axiom (Brick 5 proved it)"
        );
        assert_eq!(def.proof_status, ProofStatus::DerivedProved);
        assert!(
            def.value_src.is_some(),
            "kernel_to_micro_instantiate must carry a proof term"
        );
        let live: BTreeSet<String> = live_env_axioms(&spec)
            .iter()
            .map(|a| a.name.clone())
            .collect();
        assert!(
            !live.contains("kernel_to_micro_instantiate"),
            "kernel_to_micro_instantiate must leave the ConstantKind::Axiom census after the flip"
        );

        // (2) Truth cross-check: the proved equation still SURVIVES the battery.
        let outcome = refute_statement(
            &spec,
            "kernel_to_micro_instantiate",
            "forall (b : KExpr) (a : KExpr), \
             Eq MicroExpr (kernel_to_micro (instantiate b a)) \
             (micro_instantiate (kernel_to_micro b) (kernel_to_micro a))",
        )
        .expect("statement elaborates");
        match outcome {
            // In-scope and survived — the expected, correct outcome.
            Ok(None) => {}
            // A refutation here would mean the proof and the battery DISAGREE.
            Ok(Some(r)) => panic!(
                "kernel_to_micro_instantiate REFUTED after being PROVED — the proof and the \
                 battery DISAGREE (a real finding). witness=[{}] lhs={} rhs={}",
                r.witness.join("; "),
                r.lhs_whnf,
                r.rhs_whnf
            ),
            // The equation must remain IN-SCOPE on the KExpr battery.
            Err(reason) => panic!(
                "kernel_to_micro_instantiate equation must be IN-SCOPE on the KExpr \
                 battery: {reason:?}"
            ),
        }
    });
}

/// A TRUE KExpr-quantified unfolding identity (`kapp_fn (app f a) = kapp_fn f`,
/// the proven `kapp_fn_app` lemma) is EVALUATED on the KExpr battery and SURVIVES
/// — confirming the KExpr battery really builds closed terms, really reduces, and
/// does not produce a false positive on a genuinely-true KExpr equation.
#[test]
fn kexpr_quantified_true_unfolding_survives() {
    run_with_stack(|| {
        let spec = Specification::new().expect("spec builds");
        let outcome = refute_statement(
            &spec,
            "kapp_fn_app_probe",
            "forall (f : KExpr) (a : KExpr), \
             Eq KExpr (kapp_fn (KExpr.app f a)) (kapp_fn f)",
        )
        .expect("statement elaborates");
        match outcome {
            Ok(None) => { /* in-scope, survived — correct */ }
            Ok(Some(r)) => panic!("TRUE KExpr equation wrongly refuted: {r:?}"),
            Err(reason) => panic!(
                "TRUE KExpr equation wrongly excluded — KExpr battery missing/empty: {reason:?}"
            ),
        }
    });
}

/// The KExpr battery genuinely BITES: an arg-swapped (de-Bruijn-wrong) KExpr
/// substitution identity is REFUTED by a concrete witness. This proves the new
/// battery is not a stub — a future arg-swapped KExpr equation can no longer hide
/// behind `UngeneratableBinder("KExpr")`.
///
/// `instantiate` substitutes `val` for BVar(0); the FALSE form below claims
/// `instantiate (app f a') val = app (instantiate a' val) (instantiate f val)`
/// (the two app operands swapped), which fails whenever `f` and `a'` differ after
/// substitution.
#[test]
fn arg_swapped_kexpr_instantiate_is_refuted() {
    run_with_stack(|| {
        let spec = Specification::new().expect("spec builds");
        let outcome = refute_statement(
            &spec,
            "kexpr_instantiate_app_argswap_FALSE",
            "forall (f : KExpr) (a : KExpr) (val : KExpr), \
             Eq KExpr (instantiate (KExpr.app f a) val) \
             (KExpr.app (instantiate a val) (instantiate f val))",
        )
        .expect("statement elaborates");
        let refutation = outcome
            .expect("arg-swapped KExpr instantiate must be IN-SCOPE (a computable equation)")
            .expect(
                "arg-swapped KExpr instantiate MUST be refuted — if not, the KExpr battery \
                 does not genuinely reduce/compare KExpr terms",
            );
        eprintln!(
            "REFUTED kexpr_instantiate_app_argswap(FALSE) on witness [{}]:\n  lhs={}\n  rhs={}",
            refutation.witness.join("; "),
            refutation.lhs_whnf,
            refutation.rhs_whnf,
        );
        assert_ne!(
            refutation.lhs_whnf, refutation.rhs_whnf,
            "the refuting witness must make the two reduced sides genuinely differ"
        );
    });
}

/// After the micro-band drain (Brick 3) `micro_def_eq` has a COMPUTABLE body, so
/// the reflexivity probe (`micro_def_eq e e = true`) is no longer excluded as
/// `NonComputable`: it is now IN-SCOPE and, being genuinely reflexive, is NOT
/// refuted. This pins that the classifier tracks the drain (a formerly-abstract
/// `-> Bool` token became evaluatable) AND that the gate raises no false positive
/// on a true equation.
#[test]
fn micro_def_eq_refl_probe_is_in_scope_and_not_refuted() {
    run_with_stack(|| {
        let spec = Specification::new().expect("spec builds");
        let outcome = refute_statement(
            &spec,
            "micro_def_eq_refl_probe",
            "forall (e : MicroExpr), Eq Bool (micro_def_eq e e) Bool.true",
        )
        .expect("elaborates");
        match outcome {
            Ok(None) => {}
            Ok(Some(r)) => {
                panic!("micro_def_eq reflexivity is TRUE and must not be refuted, got {r:?}")
            }
            Err(reason) => panic!(
                "micro_def_eq now has a computable body; the reflexivity probe must be \
                 IN-SCOPE (evaluatable), not excluded, got {reason:?}"
            ),
        }
    });
}

/// REGRESSION for the REFUTE-AND-DELETE of the `kernel_to_micro_def_eq` bridge
/// (Brick 3 of the micro-band drain). That axiom claimed
///
///   forall a b, is_def_eq a b -> micro_def_eq (k2m a) (k2m b) = true,
///
/// which became FALSE the moment `micro_def_eq` got its weak-head-normalising
/// body: a `DefEq.beta` redex sitting UNDER a lambda binder is invisible to the
/// weak-head `micro_whnf`, whereas kernel `is_def_eq` (a full congruence) still
/// identifies the two terms. The spec now carries the machine-checked
/// counterexample as two DerivedProved defs — a concrete `is_def_eq a b` witness
/// AND `micro_def_eq (k2m a) (k2m b) = false` (by `Eq.refl`, so it only
/// kernel-checks because the reduction genuinely yields `false`).
///
/// This test fails closed if the false axiom is ever re-registered (it must NOT
/// be a live kernel-env axiom) or if either refutation witness disappears.
#[test]
fn kernel_to_micro_def_eq_bridge_is_refuted_and_deleted() {
    run_with_stack(|| {
        let spec = Specification::new().expect("spec builds");

        // (1) The false bridge must be GONE from the live env axiom census. (The
        //     name ratchet is subset-only, so a re-admission would NOT be caught
        //     there — this explicit guard is the real tripwire.)
        let live: BTreeSet<String> = live_env_axioms(&spec).into_iter().map(|a| a.name).collect();
        assert!(
            !live.contains("kernel_to_micro_def_eq"),
            "kernel_to_micro_def_eq is a REFUTED-AND-DELETED false axiom; it must never be \
             re-admitted as a live kernel-env axiom"
        );

        // (2) Both machine-checked refutation witnesses must be present and
        //     DerivedProved — they only kernel-check because micro_def_eq
        //     genuinely reduces to `false` on a bona-fide is_def_eq pair.
        for name in [
            "kernel_to_micro_def_eq_refuting_defeq",
            "kernel_to_micro_def_eq_refuted_false",
        ] {
            let def = spec
                .get_definition(name)
                .unwrap_or_else(|| panic!("refutation witness {name} must exist"));
            assert!(
                !def.is_axiom,
                "{name} must be a proved definition, not an axiom"
            );
            assert_eq!(
                def.proof_status,
                ProofStatus::DerivedProved,
                "{name} must be DerivedProved (kernel-checked refutation evidence)"
            );
        }
    });
}
