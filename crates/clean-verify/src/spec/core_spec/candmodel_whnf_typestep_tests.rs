// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Scratch elaboration for `redTypeStep` at the whnf-indexed candidate — the
//! starvation census that refutes it at a FIXED index, and the companion asking
//! whether `RedWStep` absorbs that disagreement.
//!
//! Split out of `candmodel_necessary_tests.rs`, which these two tests pushed
//! over the 1000-line paragon ratchet. Read `candmodel_whnf_typestep.rs` for
//! the terms and the scope; the headline refutation is narrower than it sounds.

use super::*;
use crate::test_utils::{build_spec_with_stack, parse_check, run_with_stack};

/// **`redTypeStep` AT THE WHNF-INDEXED CANDIDATE — the starvation census.**
///
/// A MIXED report is the intended output. Each census pair states both
/// readings of one term's clause at index one and exactly one can elaborate;
/// the three refutation arms are self-selecting and at most one pair of terms
/// can straddle the starvation boundary at a given fuel.
///
/// What is asserted is therefore not the answer — which this run is measuring —
/// but the two invariants that make the answer meaningful:
///
/// 1. the CONTROL elaborates, so the census machinery reaches the `pi` arm at
///    all (it restates `redw_pi_clause_reached`, which is green);
/// 2. each census pair is DETERMINATE — exactly one of `_blind` / `_pi`
///    elaborates. Both would mean `whnf_acc e` and the `AndType` are
///    convertible, which would make every `RedW` result at a `pi` vacuous;
///    neither would mean the clause is some third thing and the reading of
///    `RedW` used throughout `candmodel_whnf_probe.rs` is wrong.
///
/// MEASURED 2026-09-19: `redTypeStep` is REFUTED at the fixed index. Every
/// redex starves at fuel one and the already-whnf `pi` does not, so the clause
/// flips KIND across one beta step. The `r1` arm elaborates and `r2`/`r3` do
/// not — all three outcomes are now pinned above. Read
/// `candmodel_whnf_typestep.rs` for the scope, which is narrower than the
/// headline: this refutes the law at `RedW n`, NOT at the index-quantified
/// `RedWStep`.
#[test]
fn candmodel_whnf_typestep_census_elaborates() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        for (name, src) in Specification::candmodel_whnf_indexed_sources() {
            spec.add_recursive_def(&src, "CandModel whnf-indexed candidate")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        let mut passed: Vec<String> = Vec::new();
        let mut failed: Vec<String> = Vec::new();
        for (name, src) in Specification::candmodel_whnf_typestep_census_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
            eprintln!("REGISTERING {name}");
            let t0 = std::time::Instant::now();
            match spec.add_recursive_def(&src, "CandModel whnf redTypeStep census") {
                Ok(()) => {
                    eprintln!("  ok   {name} {:.1}s", t0.elapsed().as_secs_f64());
                    passed.push(name);
                }
                Err(e) => {
                    eprintln!("  FAIL {name} {:.1}s: {e}", t0.elapsed().as_secs_f64());
                    failed.push(name);
                }
            }
        }
        let ok = |n: &str| passed.iter().any(|p| p == n);
        for tag in ["r1", "r2", "r3"] {
            let b = ok(&format!("redw_tsc_{tag}_blind"));
            let p = ok(&format!("redw_tsc_{tag}_pi"));
            eprintln!("CENSUS {tag}: blind={b} pi={p}");
            assert!(
                b != p,
                "{tag}: the clause at index one must be EXACTLY ONE of the blind \
                 reading and the pi reading, measured blind={b} pi={p}. Both means \
                 the two are convertible and every RedW pi result is vacuous; \
                 neither means RedW's clause is not what candmodel_whnf_probe.rs \
                 reads it as."
            );
        }
        let refuted: Vec<&String> = passed
            .iter()
            .filter(|n| n.starts_with("redw_typestep_refuted_at_index_one_"))
            .collect();
        eprintln!(
            "REDTYPESTEP-VERDICT: {} refutation arm(s) elaborated: {:?}",
            refuted.len(),
            refuted
        );
        eprintln!("REDTYPESTEP-CENSUS-FAILED: {failed:?}");
        assert!(
            ok("redw_tsc_control_pi_at_index_one"),
            "CONTROL failed: the census never reaches the pi arm, so nothing here \
             is a statement about fuel. Failures: {failed:?}"
        );
        // MEASURED 2026-09-19 and pinned. Every redex starves at fuel one --
        // even the one-step R1 -- while the already-whnf `pi` computes. That is
        // the whole mechanism, so pin the shape rather than just the verdict:
        // if wh3 ever gets cheap enough to reduce R1 at fuel one, `r1_blind`
        // flips and this fails loudly instead of silently refuting nothing.
        for tag in ["r1", "r2", "r3"] {
            assert!(
                ok(&format!("redw_tsc_{tag}_blind")),
                "{tag} no longer STARVES at fuel one. The refutation below depends \
                 on the redex starving where its contractum does not, so re-derive \
                 it before trusting any redTypeStep claim at RedW."
            );
        }
        // Exactly ONE pair can straddle the starvation boundary: the redex whose
        // contractum is the already-whnf `pi`. r2/r3 have blind contracta and
        // must NOT refute -- they are the controls that make r1 mean something.
        assert_eq!(
            refuted,
            vec!["redw_typestep_refuted_at_index_one_r1"],
            "expected exactly the r1 arm to refute. r2/r3 have BLIND contracta, so \
             an arm landing there would mean the clause is not what the census \
             reads it as; and r1 failing would mean redTypeStep is no longer \
             refuted at a fixed index."
        );
    });
}

/// **Does `RedWStep` ABSORB the starvation the fixed index cannot?** SCRATCH.
///
/// The companion to `candmodel_whnf_typestep_census_elaborates`, on the SAME
/// pair of types that refutes `redTypeStep` at index one. If both directions
/// elaborate, the law fails at every fixed index and holds at the quantified
/// family for identical terms — which is the sharpest available statement that
/// the index is load-bearing, and the reason the refutation must not be cited
/// against the candidate.
///
/// MEASURED 2026-09-19: all five arms elaborate, first try — BOTH directions
/// of the `AndType` the field demands. So `redTypeStep` fails at every fixed
/// index and holds at the quantified family, for identical terms.
///
/// The three arms beneath the two law arms are the REASONS it works, and are
/// pinned with them: `redw_sort_to_acc` / `redw_acc_to_sort` say `sort 0` is
/// index-free (so the clause's `ih` cannot matter here), and
/// `redw_r1_reaches_pi_at_succ_succ` says the fuel loop unfolds twice at a
/// VARIABLE index (so no general fuel lemma is needed).
///
/// **This is one PAIR, not the law.** `redTypeStep` quantifies every `T`/`T2`,
/// and both reasons above are special to this pair — see the module doc.
#[test]
fn candmodel_whnf_typestep_quantified_elaborates() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        for (name, src) in Specification::candmodel_whnf_indexed_sources() {
            spec.add_recursive_def(&src, "CandModel whnf-indexed candidate")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        let mut passed: Vec<String> = Vec::new();
        let mut failures: Vec<String> = Vec::new();
        for (name, src) in Specification::candmodel_whnf_typestep_quantified_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
            eprintln!("REGISTERING {name}");
            let t0 = std::time::Instant::now();
            match spec.add_recursive_def(&src, "CandModel whnf redTypeStep quantified") {
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
        eprintln!("QUANTIFIED-VERDICT: {} passed {:?}", passed.len(), passed);
        eprintln!(
            "QUANTIFIED-FAILURES ({}): {}",
            failures.len(),
            failures.join(" | ")
        );
        // MEASURED 2026-09-19: all five, first try. Pin every one — the pair of
        // law arms is the RESULT, and the three beneath them are the reasons it
        // works, so a regression in any of them should name itself rather than
        // leave the headline standing on a changed foundation.
        //
        // `redw_r1_reaches_pi_at_succ_succ` is the one to watch: it says the
        // fuel loop unfolds TWICE at a VARIABLE index, which is what lets the
        // absorption argument avoid a general fuel lemma entirely.
        assert!(
            failures.is_empty(),
            "whnf-indexed quantified redTypeStep failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
        for req in [
            "redw_sort_to_acc",
            "redw_acc_to_sort",
            "redw_r1_reaches_pi_at_succ_succ",
            "redw_typestep_fwd_at_redwstep_for_the_refuting_pair",
            "redw_typestep_bwd_at_redwstep_for_the_refuting_pair",
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
