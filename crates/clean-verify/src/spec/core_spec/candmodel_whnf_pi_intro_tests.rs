// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Scratch elaboration for the `pi_intro` quantifier-order refutation.

use super::*;
use crate::test_utils::{build_spec_with_stack, parse_check, run_with_stack};

/// `pi_intro` at `RedWStep`. SCRATCH.
///
/// Two dependency vecs only — the gate is at its ceiling and each registration
/// costs real memory, which is why `piintro_acc_to_sort` is a local copy rather
/// than a third vec.
///
/// MEASURED 2026-09-19: all seven arms elaborate, zero failures. So `pi_intro`
/// is REFUTED at `RedWStep` — assuming the field yields `C` for arbitrary `C`.
///
/// Read the scope with it. (1) CONDITIONALITY IS NOW DISCHARGED: all three
/// carriers are proved (`no_iota_reduces_lam_app`, `no_delta_reduces_lam_app`,
/// `no_beta_reduces_omega_lam`) and `redw_pi_intro_refuted_at_redwstep_uncond`
/// carries the refutation with no hypothesis but the law itself — the same step
/// `pi_elim_blind_refuted_uncond` made for its own.
/// (2) It does NOT contradict `redw_pi_intro_per_index`, which passes: that
/// lemma assumes the pointwise property at EVERY index, which is strictly
/// STRONGER than the field's premise and implies it. "Holds given the stronger
/// premise" and "false given the field's" are consistent, and the gap between
/// them is precisely the quantifier-order residual.
#[test]
fn candmodel_whnf_pi_intro_elaborates() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        // `beta_subst_congr_sources` is PARTLY WIRED: the built spec already
        // carries some of its constants (measured — `beta_reduces_psubst_congr`
        // is one), so a blind registration dies on `Duplicate declaration`.
        // Skip exactly that error and no other: an already-present constant is
        // the dependency being satisfied, while any OTHER failure still means
        // this probe is not standing on what it thinks it is.
        let mut reused = 0usize;
        for (name, src) in Specification::beta_subst_congr_sources() {
            match spec.add_recursive_def(&src, "beta/subst congruence probe") {
                Ok(()) => {}
                Err(e) if e.to_string().contains("Duplicate declaration") => reused += 1,
                Err(e) => panic!("dependency {name} must register first: {e}"),
            }
        }
        eprintln!("DEPS: {reused} beta/subst constant(s) already wired, reused");
        for (name, src) in Specification::candmodel_whnf_indexed_sources() {
            spec.add_recursive_def(&src, "CandModel whnf-indexed candidate")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        let mut passed: Vec<String> = Vec::new();
        let mut failures: Vec<String> = Vec::new();
        for (name, src) in Specification::candmodel_whnf_pi_intro_refutation_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
            eprintln!("REGISTERING {name}");
            let t0 = std::time::Instant::now();
            match spec.add_recursive_def(&src, "CandModel whnf pi_intro refutation") {
                Ok(()) => {
                    eprintln!("  ok   {name} {:.1}s", t0.elapsed().as_secs_f64());
                    passed.push(name);
                }
                Err(e) => {
                    eprintln!("  FAIL {name} {:.1}s: {e}", t0.elapsed().as_secs_f64());
                    failures.push(format!("{name}: {e}"));
                }
            }
        }
        eprintln!("PIINTRO-VERDICT: {} passed {:?}", passed.len(), passed);
        eprintln!(
            "PIINTRO-FAILURES ({}): {}",
            failures.len(),
            failures.join(" | ")
        );
        // MEASURED 2026-09-19: all SEVEN, zero failures. Pin every one — the
        // refutation is the RESULT and the six beneath it are the reasons it
        // holds, so a regression should name itself rather than leave the
        // headline standing on a changed foundation.
        assert!(
            failures.is_empty(),
            "whnf pi_intro refutation failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
        for req in [
            // the KExpr.rec projection standing in for absent `lam` injectivity
            "lamBody",
            "piintro_acc_to_sort",
            // lift-by-zero is the identity — the fact this tree did not have
            "lift_bvar_zero",
            "lift_zero_id",
            "omega_instantiate_body",
            // the accessibility induction, beta case LIVE (no `Neutral` to kill it)
            "omega_app_acc_of_candidate",
            // the three carriers, DISCHARGED 2026-09-19
            "no_iota_reduces_lam_app",
            "no_delta_reduces_lam_app",
            "no_beta_reduces_omega_lam",
            // the result, and the same result with every carrier discharged
            "redw_pi_intro_refuted_at_redwstep",
            "redw_pi_intro_refuted_at_redwstep_uncond",
        ] {
            assert!(
                passed.iter().any(|p| p == req),
                "{req} is missing from the pass list — the generator stopped \
                 emitting it, which is a silent way for this test to assert \
                 nothing. Passed: {passed:?}"
            );
        }
    });
}
