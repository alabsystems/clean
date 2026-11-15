// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Scratch elaboration for the derivation-indexed pi-set.

use super::*;
use crate::test_utils::{
    build_eval_ir_spec_with_stack, build_spec_with_stack, build_substitution_spec_with_stack,
    parse_check, run_with_stack,
};

/// `PiSetDep` — well-formedness, and the weakening it introduces. SCRATCH.
///
/// Two independent questions, deliberately in one run:
///
/// 1. does the spelling elaborate at all (`VD d` is `Type 1`, the body is
///    `Type`, so the `forall` over a derivation is where a universe refusal
///    would appear);
/// 2. is `PiSetDep` genuinely WEAKER than `PiSet` — if
///    `piSetDep_is_weaker_than_piSet` elaborates, the two are ordered, and
///    ordered the wrong way for a candidate, since cr1 is a USE of membership.
///
/// A green run is NOT a claim that this is the right candidate notion. It is a
/// measurement that the spelling is well-formed and that its objection is real.
#[test]
fn candmodel_dep_pi_elaborates() {
    run_with_stack(|| {
        let mut spec = build_substitution_spec_with_stack();
        let mut passed: Vec<String> = Vec::new();
        let mut failures: Vec<String> = Vec::new();
        for (name, src) in Specification::candmodel_dep_pi_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
            eprintln!("REGISTERING {name}");
            let t0 = std::time::Instant::now();
            match spec.add_recursive_def(&src, "dependent pi-set probe") {
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
        eprintln!("DEPPI-VERDICT: {} passed {:?}", passed.len(), passed);
        eprintln!(
            "DEPPI-FAILURES ({}): {}",
            failures.len(),
            failures.join(" | ")
        );
        // `PiSetDep` itself is the subject: if it does not elaborate, the
        // weakening question is moot and the route needs a different spelling.
        // cr3 and the refinement diagnostic it depends on, reported as a PAIR:
        // cr3 red with the diagnostic green means the fault is inside cr3; both
        // red means the inversion needs the discriminator route instead.
        eprintln!(
            "DEPPI-REFINES-OUTER: {}",
            if passed.iter().any(|p| p == "match_refines_outer_var_probe") {
                "YES"
            } else {
                "NO"
            }
        );
        eprintln!(
            "DEPPI-CR1: {}",
            if passed.iter().any(|p| p == "piSetDep_cr1") {
                "PROVED"
            } else {
                "not proved"
            }
        );
        // MEASURED 2026-09-19: five arms, zero failures. Pinned — but read what
        // each one IS. `xvalStepInvariant` is a `def` of a PROP: registering it
        // means the STATEMENT is well-formed and named, NOT that it is proved.
        // cr3 stays blocked on proving it.
        // PINNED REFUSALS. These two are EXPECTED to fail today, and the test
        // fails loudly if either starts passing — the idiom CLAUDE.md requires
        // for a measured gap, so that closing it cannot go unnoticed.
        //
        // `match_refines_outer_var_probe` — MEASURED 2026-09-19: this
        // elaborator refutes an impossible match arm by index clash, but does
        // NOT refine a variable bound outside the match. `hn : Neutral t` stays
        // stuck as `KExpr.rec (..) t` instead of computing to `Empty`.
        //
        // (`piSetDep_cr3` was pinned here too and is GONE from this vector: it
        // is now proved on `beta_app_inv` in the app-inversion test, which is
        // where the inversion it needs is registered.)
        const PINNED_REFUSALS: [&str; 1] = ["match_refines_outer_var_probe"];
        let expected_pass: Vec<&String> = passed
            .iter()
            .filter(|p| !PINNED_REFUSALS.contains(&p.as_str()))
            .collect();
        let unexpected: Vec<&String> = failures
            .iter()
            .filter(|f| !PINNED_REFUSALS.iter().any(|p| f.starts_with(p)))
            .collect();
        assert!(
            unexpected.is_empty(),
            "constants that should elaborate did not: {unexpected:?}"
        );
        assert_eq!(
            expected_pass.len(),
            11,
            "the eleven measured constants must all still elaborate, got {expected_pass:?}"
        );
        // The eighth is `spinePropagate` (2026-09-20), R30 route 2's arity-general
        // spine step: any predicate closed under application to a `whnf_acc`
        // argument propagates along a spine. It is counted here rather than in a
        // separate battery because it is measured against the SAME substitution
        // spec and its failure would mean the same thing -- a constant this route
        // rests on stopped elaborating.
        for pinned in PINNED_REFUSALS {
            assert!(
                !passed.iter().any(|p| p == pinned),
                "{pinned} now ELABORATES — the pinned gap has closed. Re-measure it, \
                 update the module doc and the design note, and remove it from \
                 PINNED_REFUSALS."
            );
        }
        for req in [
            "PiSetDep",
            "piSetDep_cr1",
            "piSetDep_cr2",
            // a STATEMENT, not a proof
            "xvalStepInvariant",
            "piSetDep_is_weaker_than_piSet",
        ] {
            assert!(
                passed.iter().any(|p| p == req),
                "{req} is missing from the pass list — the generator stopped \
                 emitting it, which is a silent way for this test to assert \
                 nothing. Passed: {passed:?}"
            );
        }
        assert!(
            passed.iter().any(|p| p == "PiSetDep"),
            "PiSetDep does not elaborate — the derivation-indexed spelling is \
             not well-formed here, so the objection about weakening is moot and \
             the route needs a different tie between the value and the term. \
             Failures: {failures:?}"
        );
    });
}

/// Does the elaborator refute an impossible constructor by INDEX CLASH?
///
/// Its own test, with its own spec, because the dep-pi probe beside it already
/// peaks at 91% of this box's gate budget and the cost scales with how many
/// dependency vecs ONE test registers.
///
/// Read the two arms together or not at all:
///
/// * control FAILS  -> the pattern spelling is wrong; measures nothing.
/// * control passes, probe FAILS -> no index refutation; cr3's inversion needs
///   eleven hand-written head discriminators.
/// * both pass -> the elaborator discharges the eleven impossible arms itself,
///   and cr3's inversion is four cases.
#[test]
fn candmodel_beta_match_index_refutation() {
    run_with_stack(|| {
        let mut spec = build_substitution_spec_with_stack();
        let mut passed: Vec<String> = Vec::new();
        let mut failures: Vec<String> = Vec::new();
        for (name, src) in Specification::candmodel_beta_match_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
            eprintln!("REGISTERING {name}");
            let t0 = std::time::Instant::now();
            match spec.add_recursive_def(&src, "beta match index-refutation probe") {
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
        let control = passed.iter().any(|p| p == "beta_match_control");
        let probe = passed
            .iter()
            .any(|p| p == "beta_app_index_refutation_probe");
        eprintln!("BETAMATCH-VERDICT: {} passed {:?}", passed.len(), passed);
        eprintln!(
            "BETAMATCH-FAILURES ({}): {}",
            failures.len(),
            failures.join(" | ")
        );
        eprintln!(
            "BETAMATCH-ANSWER: {}",
            match (control, probe) {
                (false, _) => "INVALID - control failed, spelling is wrong, measures nothing",
                (true, true) => "INDEX REFUTATION WORKS - cr3 inversion is four cases",
                (true, false) => "NO INDEX REFUTATION - cr3 inversion needs eleven discriminators",
            }
        );
    });
}

/// THE APP-INVERSION — fifteen arms, adapted from a template already in tree.
///
/// Its own test and its own spec: the dep-pi probe beside it carries two PINNED
/// REFUSALS, and a failure here would otherwise read as one of those pins.
///
/// What this measures is whether the R2 template survives generalising its
/// target from a fixture to variables. Everything it leans on — `lam_ne_app`,
/// `pi_ne_app`, `let_ne_app`, `proj_ne_app`, `app_inj_fst`, `app_inj_snd` —
/// is pre-existing and proved, so a failure here is about the adaptation, not
/// about the parts.
#[test]
fn candmodel_app_inversion_infrastructure() {
    run_with_stack(|| {
        let mut spec = build_substitution_spec_with_stack();
        let mut passed: Vec<String> = Vec::new();
        let mut failures: Vec<String> = Vec::new();
        for (name, src) in Specification::candmodel_app_inversion_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
            eprintln!("REGISTERING {name}");
            let t0 = std::time::Instant::now();
            match spec.add_recursive_def(&src, "app inversion") {
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
        eprintln!("APPINV-VERDICT: {} passed {:?}", passed.len(), passed);
        eprintln!(
            "APPINV-FAILURES ({}): {}",
            failures.len(),
            failures.join(" | ")
        );
        eprintln!(
            "APPINV-ANSWER: {}",
            if passed.iter().any(|p| p == "beta_app_inv") {
                "INVERSION HOLDS - cr3 has its four cases"
            } else {
                "inversion does not elaborate - read the arm named in FAILURES"
            }
        );
        eprintln!(
            "APPINV-CR3: {}",
            if passed.iter().any(|p| p == "piSetDep_cr3") {
                "PROVED"
            } else {
                "not proved"
            }
        );
        // Settles the question cr3 ROUTED AROUND rather than answered: is
        // `Neutral` Opaque? Read the two together — the second cannot pass if
        // the first fails, and if both pass then cr3 holds at the telescope's
        // own premise rather than at a hand-picked substitute for it.
        eprintln!(
            "APPINV-NEUTRAL-UNFOLDS: {}",
            if passed.iter().any(|p| p == "neutral_lam_is_empty") {
                "YES - Neutral computes to Empty at a lam"
            } else {
                "NO - Neutral is Opaque, hnlam was necessary"
            }
        );
        // THE question this whole lane is now on: does step-indexing dissolve
        // the `m_pi` self-reference the way `RedN` dissolved `pi_elim`'s?
        eprintln!(
            "APPINV-STEPINDEXED-XVAL: {}",
            if passed.iter().any(|p| p == "xvalN") {
                "ELABORATES - the dependent m_pi is expressible"
            } else {
                "does not elaborate - step-indexing does not dissolve it as written"
            }
        );
        eprintln!(
            "APPINV-XVALN-STEP0: {}",
            if passed.iter().any(|p| p == "xvalN_step_zero") {
                "base case free by Eq.refl - xvalN 0 reduces to junkD as intended"
            } else {
                "base case FAILS - xvalN 0 is not reducing as intended"
            }
        );
        eprintln!(
            "APPINV-PI-INHABITED-DEGENERATE: {}",
            if passed
                .iter()
                .any(|p| p == "xvalInf_pi_inhabited_empty_domain")
            {
                "inhabited at an EMPTY-DOMAIN pi - not empty at every pi"
            } else {
                "degenerate pi inhabitation does not elaborate"
            }
        );
        eprintln!(
            "APPINV-LIMIT-CR1: {}",
            if passed.iter().any(|p| p == "xvalInf_cr1_ty") {
                "cr1 holds at the limit BY PROJECTION at index 0"
            } else {
                "cr1 at the limit does not elaborate"
            }
        );
        eprintln!(
            "APPINV-LIMIT-INHABITED: {}",
            if passed.iter().any(|p| p == "xvalInf_sort_inhabited") {
                "INHABITED at a sort - the limit is not vacuous there"
            } else {
                "not shown inhabited - the limit may be empty"
            }
        );
        eprintln!(
            "APPINV-LIMIT: {}",
            if passed.iter().any(|p| p == "interD") {
                "interD elaborates - the limit is expressible"
            } else {
                "interD does not elaborate"
            }
        );
        eprintln!(
            "APPINV-CR3-AT-NEUTRAL: {}",
            if passed.iter().any(|p| p == "piSetDep_cr3_neutral") {
                "PROVED at the telescope's own premise"
            } else {
                "not proved - cr3 stands only at hnlam"
            }
        );
    });
}

/// PARSE ONLY — microseconds, no spec build. Mirrors r29's
/// `test_candmodel_r29_sources_parse`.
///
/// Why this exists: the elaborating tests below call `parse_check` INSIDE the
/// loop, i.e. AFTER `build_substitution_spec_with_stack()`. So a paren or arity typo costs
/// the entire spec build before it is reported — measured repeatedly at ~19
/// minutes, and three runs in one session died that way on spelling rather
/// than on mathematics. Running the parser first makes that class ~free.
///
/// A green here claims NOTHING about elaboration. It claims the strings are
/// syntactically well formed, which is exactly the class that was costing runs.
#[test]
fn candmodel_dep_pi_sources_parse() {
    let mut checked = 0usize;
    for (name, src) in Specification::candmodel_dep_pi_sources()
        .into_iter()
        .chain(Specification::candmodel_beta_match_sources())
        .chain(Specification::candmodel_app_inversion_sources())
    {
        parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
        checked += 1;
    }
    assert!(
        checked >= 12,
        "expected every probe source to be parsed, only saw {checked} — a vector was dropped"
    );
    eprintln!("PARSE-ONLY: {checked} sources parse");
}

/// The `ir_wrap` fix, demonstrated against the EVAL_IR spec.
///
/// Its own test because it needs a different SPEC: `ir_wrap` and `Nat.mod` are
/// EvalIR substrate and the substitution bundle does not carry them. A first
/// attempt ran these in the substitution test and both failed with
/// `Unknown identifier` — a missing constant, NOT a failure to fold. The
/// verdict lines there asserted "the proposed fix does not help", which the
/// error could not support; they are deleted rather than reworded.
///
/// Read the two rows together:
/// * `nat_mod_folds_u64_max_natively` — `Nat.mod` carries a native reducer, so
///   1.8e19 mod 2^32 should fold in ONE step;
/// * `ir_wrap_folds_at_a_small_value` — `ir_wrap` at a value it can reach, to
///   show it is CORRECT and cheap small. The gap is SCALE, not meaning.
///
/// The obvious control — `ir_wrap 32 u64::MAX` — is deliberately absent: it
/// would not fail, it would run ~4.29e9 reduction steps and take the test with
/// it.
#[test]
fn candmodel_ir_wrap_fix_demonstration() {
    run_with_stack(|| {
        let mut spec = build_eval_ir_spec_with_stack();
        let mut passed: Vec<String> = Vec::new();
        let mut failures: Vec<String> = Vec::new();
        for (name, src) in Specification::candmodel_ir_wrap_fix_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
            let t0 = std::time::Instant::now();
            match spec.add_recursive_def(&src, "ir_wrap fix demonstration") {
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
        eprintln!("IRWRAPFIX-VERDICT: {} passed {:?}", passed.len(), passed);
        eprintln!(
            "IRWRAPFIX-FAILURES ({}): {}",
            failures.len(),
            failures.join(" | ")
        );
        // `nat_add_algebra_is_reachable` is a PINNED REFUSAL: it is EXPECTED to
        // fail with `Unknown identifier: add_assoc`, recording that the EvalIR
        // test spec carries no Nat algebra. It is excluded from the
        // INVALID detection below so it cannot mask a real missing-constant
        // failure in another row — and asserted to keep failing, so the day the
        // bundle composition changes, this says so.
        // PINNED REFUSALS. Each is a MEASUREMENT of what this spec does not
        // give, and each must keep failing — the day one starts passing, the
        // plan built on it is stale and this test says so.
        //
        //   nat_add_algebra_is_reachable : the EvalIR spec carries no Nat algebra
        //   nat_add_zero_left_is_refl    : `Nat.add` recurses on its SECOND arg,
        //   nat_add_succ_left_is_refl    : so LEFT-side equations are not free
        //   free_var_hard_error_value_position : an undeclared identifier in
        //                                  VALUE position is a hard error
        //   free_var_same_name_two_types : the undeclared name is bound ONCE,
        //                                  so it cannot be a Nat and a Bool
        //   free_var_fail_open_type_position / _binder_used_in_value : these
        //     PASSED until 2026-09-20 and their passing WAS the defect. The spec
        //     environment now sets `relaxedAutoImplicit = false`
        //     (`core_spec::Specification::new_empty`), so an undeclared
        //     identifier is a hard error in TYPE position exactly as it always
        //     was in VALUE position. They are pinned as refusals so that
        //     REMOVING that option makes them pass and this test says so.
        const PINNED: [&str; 7] = [
            "nat_add_algebra_is_reachable",
            "nat_add_zero_left_is_refl",
            "nat_add_succ_left_is_refl",
            "free_var_hard_error_value_position",
            "free_var_same_name_two_types",
            "free_var_fail_open_type_position",
            "free_var_binder_used_in_value",
        ];
        // THE FAIL-OPEN. These rows are expected to PASS, and their passing is
        // the defect: an undeclared identifier in a TYPE position is silently
        // auto-bound as a free variable, so the declaration is true of an
        // arbitrary thing rather than of what it names. Measured here rather
        // than cited, because docs/CRYSTAL_STATUS.md names this hole and
        // declines to close it -- and a hole nobody measures is one nobody
        // notices closing OR widening.
        // THE FAIL-OPEN IS CLOSED, and the four rows above now measure the
        // CLOSURE instead of the hole. What they established while it was open
        // is worth keeping: the undeclared name was bound ONCE per declaration
        // with a type inferred from first use -- `free_var_same_name_two_types`
        // failed with "const mismatch: Nat vs Bool" -- and NOT minted fresh per
        // occurrence, which would have been strictly worse. And the domain was
        // genuinely elaborated, not skipped for being unused.
        for pinned in PINNED {
            assert!(
                !passed.iter().any(|p| p == pinned),
                "{pinned} now ELABORATES — a fact this plan rests on has changed. \
                 Re-read part (1) of designs/2026-09-20-restoring-division-agrees-\
                 with-repeated-subtraction.md before trusting it."
            );
        }
        // AND EVERYTHING ELSE MUST PASS. Without this the test reported three
        // failures and still returned ok — it observed without enforcing, which
        // is the shape of a test that reports `ok` forever.
        let unexpected: Vec<&String> = failures
            .iter()
            .filter(|f| !PINNED.iter().any(|p| f.starts_with(p)))
            .collect();
        assert!(
            unexpected.is_empty(),
            "rows that must elaborate did not: {unexpected:?}"
        );
        let unknown = failures
            .iter()
            .filter(|f| !PINNED.iter().any(|p| f.starts_with(p)))
            .any(|f| f.contains("Unknown identifier"));
        eprintln!(
            "IRWRAPFIX-ANSWER: {}",
            if unknown {
                "INVALID - a constant is missing from this spec; this measures nothing"
            } else if passed
                .iter()
                .any(|p| p == "divpow2_residue_folds_at_u64_max")
            {
                "ir_dm_rem (ir_nat_divpow2 n 32) FOLDS at u64::MAX - the fix works, \
                 with NO accelerated constant"
            } else {
                "divpow2 did NOT fold - identifiers resolved, so this is a real answer"
            }
        );
    });
}

/// R30 ROUTE 2 — the dead-prefix chain, measured against the FULL spec.
///
/// Separate from `candmodel_dep_pi_elaborates` because the arity lemmas live in
/// stages that are `in_substitution: false` AND `in_impl_soundness: false`
/// (`add_defeq_fuel`, `add_mutual_schema`, `add_snschema`), so only the full
/// spec can host `deadHead_beta_pres` and `whnfAcc_deadApp`. The four
/// prerequisites are re-measured here rather than assumed from the sibling run.
///
/// A green run is NOT a claim that `CandModel` is inhabited. It measures one
/// thing: that an under-applied recursor spine is `whnf_acc` — dead by ARITY,
/// which is the case no existing lemma covered, `whnfAcc_inertApp` being dead
/// by NAME.
#[test]
fn candmodel_dead_prefix_elaborates() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        let mut passed: Vec<String> = Vec::new();
        let mut failures: Vec<String> = Vec::new();
        for (name, src) in Specification::candmodel_dead_prefix_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
            eprintln!("REGISTERING {name}");
            let t0 = std::time::Instant::now();
            match spec.add_recursive_def(&src, "dead-prefix chain probe") {
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
        eprintln!("DEADPREFIX-VERDICT: {} passed {:?}", passed.len(), passed);
        eprintln!(
            "DEADPREFIX-FAILURES ({}): {}",
            failures.len(),
            failures.join(" | ")
        );
        // The capstone is the subject. Reported, not asserted, on this first
        // run: an assertion here would turn a measurement into a pin before
        // anything has been measured.
        eprintln!(
            "DEADPREFIX-CAPSTONE: {}",
            if passed.iter().any(|p| p == "whnfAcc_deadApp") {
                "whnfAcc_deadApp ELABORATES"
            } else {
                "whnfAcc_deadApp DOES NOT ELABORATE"
            }
        );
        // PIN. Every name in the array below measured GREEN against the full
        // spec 2026-09-20 -- the original six at the app-level commit
        // (deadHead_beta_pres 1.6s, whnfAcc_deadApp 0.7s, zero failures), then
        // the spine block and its witnesses. READ THE ARRAY for the count: a
        // typed count here went stale twice as rows were added. The
        // capstone is the one that did not exist before: `whnfAcc_inertApp`
        // hypothesises the head has NO recmeta (dead by NAME), and an
        // under-applied recursor HAS one — it is short of its major premise
        // (dead by ARITY). A regression here is a real regression, so it fails
        // loudly rather than degrading to a report.
        let expected = [
            "spinePropagate",
            "iota_step_no_reduct_absurd",
            "deadApp_step_inv",
            "iota_reduct_none_of_no_major",
            "deadHead_beta_pres",
            "whnfAcc_deadApp",
            // The spine form and its witness, measured GREEN 2026-09-20.
            // `whnfAcc_deadSpine` is the statement the chain exists for: a
            // recursor applied to a WHOLE SPINE shorter than its major index is
            // `whnf_acc`. `deadPrefix_witness_is_applied` is a CLOSED applied
            // instance at a real reflected recursor, so the capstone is not
            // vacuous by witness rather than by argument.
            "apply_spine_length_ge",
            "whnfAcc_deadSpine",
            "probe_kcre92_defval_is_none",
            "deadPrefix_witness_is_applied",
            "deadPrefix_spine_witness_is_applied",
        ];
        let missing: Vec<&str> = expected
            .iter()
            .copied()
            .filter(|want| !passed.iter().any(|p| p == want))
            .collect();
        assert!(
            missing.is_empty(),
            "dead-prefix chain regressed: {missing:?}\nfailures: {}",
            failures.join(" | ")
        );
    });
}
