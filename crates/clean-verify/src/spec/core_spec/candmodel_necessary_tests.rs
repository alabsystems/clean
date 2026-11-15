// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Scratch elaboration for the `CandModel` necessary condition.

use super::*;
use crate::test_utils::{build_spec_with_stack, parse_check, run_with_stack};

#[test]
fn candmodel_necessary_sources_parse() {
    for (name, src) in Specification::candmodel_necessary_sources() {
        parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
    }
}

/// ITERATION TOOL. Once the stage is wired the spec already carries these, so
/// the guard returns early and the SPEC BUILD is the confirmation. The guard
/// names a constant from the set this test registers — naming a wired one from
/// a different set is how a test starts passing without reaching its assertion.
#[test]
fn candmodel_necessary_elaborates() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        // WIRED-STATE BRANCH, and deliberately not an early `return`.
        // A bare return is a SELF-SKIP: this test would report ok forever if the
        // stage were removed from `bundles.rs`, which is the one regression the
        // wiring is supposed to protect. So assert the invariant instead -- when
        // the spec carries them, it must carry ALL of them.
        let wired = Specification::candmodel_necessary_sources()
            .iter()
            .any(|(n, _)| {
                spec.env()
                    .get_const(&clean_kernel::Name::from_string(n))
                    .is_some()
            });
        if wired {
            for (name, _) in Specification::candmodel_necessary_sources() {
                assert!(
                    spec.env()
                        .get_const(&clean_kernel::Name::from_string(&name))
                        .is_some(),
                    "{name} is missing while its siblings are wired -- the stage is \
                     registering only part of its table"
                );
            }
        } else {
            let mut failures: Vec<String> = Vec::new();
            for (name, src) in Specification::candmodel_necessary_sources() {
                eprintln!("REGISTERING {name}");
                let t0 = std::time::Instant::now();
                match spec.add_recursive_def(&src, "CandModel necessary condition") {
                    Ok(()) => eprintln!("  ok   {name} {:.1}s", t0.elapsed().as_secs_f64()),
                    Err(e) => {
                        eprintln!("  FAIL {name} {:.1}s", t0.elapsed().as_secs_f64());
                        failures.push(format!("{name}: {e}"));
                    }
                }
            }
            assert!(
                failures.is_empty(),
                "CandModel necessary-condition failures ({}):\n{}",
                failures.len(),
                failures.join("\n")
            );
        }
    });
}

// RUNG 2's scratch test is DELETED, not disabled, and the deletion is the point.
// `candmodel_rung2_probe_sources` existed so rung 2 could be elaborated without
// being registered -- scratch proves the terms, wiring proves the order. Both
// are now in `candmodel_necessary_sources`, so `candmodel_necessary_elaborates`
// above covers them and the spec build itself is the gate. Keeping the scratch
// test would not merely be redundant: it would try to `add_recursive_def` a
// constant the built spec already carries.

/// THE EMPTY-ENVIRONMENT PROBE, SCRATCH. Shares the cached spec with the test
/// above (`build_spec_with_stack` returns `shared_spec().clone()`), so it costs
/// a clone and three elaborations rather than a second spec build.
///
/// What a green run establishes is narrow and stated so it cannot be inflated:
/// that an empty `KDeclEnv` makes `kdecl_type_at` compute to `none`, and that
/// `redConst`'s premise is therefore refutable there. That is the one obligation
/// carried by the reduction in `designs/2026-09-18-is-candmodel-uninhabited.md`
/// §3j — NOT a model, and not a claim that `pi_elim` is any easier at the empty
/// environment, which it is not.
#[test]
fn candmodel_empty_env_probe_elaborates() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        let mut failures: Vec<String> = Vec::new();
        for (name, src) in Specification::candmodel_empty_env_probe_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
            eprintln!("REGISTERING {name}");
            let t0 = std::time::Instant::now();
            match spec.add_recursive_def(&src, "CandModel empty-environment probe") {
                Ok(()) => eprintln!("  ok   {name} {:.1}s", t0.elapsed().as_secs_f64()),
                Err(e) => {
                    eprintln!("  FAIL {name} {:.1}s", t0.elapsed().as_secs_f64());
                    failures.push(format!("{name}: {e}"));
                }
            }
        }
        assert!(
            failures.is_empty(),
            "empty-environment probe failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    });
}

/// THE STEP-INDEXED PROBE, SCRATCH. Shares the cached spec with the tests above.
///
/// What a green run would establish, stated so it cannot be inflated: that
/// `pi_elim` — the ONE law §3g proves must manufacture strong normalization, and
/// the one `pi_elim_blind_refuted_uncond` proves FALSE at the type-blind family —
/// holds at a family that is actually DEFINABLE, by dropping a step index instead
/// of recursing into `instantiate B a`.
///
/// It would NOT establish a model. `pi_intro` is the classical break point for
/// step-indexing and is deliberately not attempted here; `redstep_cr1` and
/// `redstep_pi_elim` are the two laws this probe claims and the only two.
#[test]
fn candmodel_stepindex_probe_elaborates() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        let mut failures: Vec<String> = Vec::new();
        for (name, src) in Specification::candmodel_stepindex_probe_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
            eprintln!("REGISTERING {name}");
            let t0 = std::time::Instant::now();
            match spec.add_recursive_def(&src, "CandModel step-indexed probe") {
                Ok(()) => eprintln!("  ok   {name} {:.1}s", t0.elapsed().as_secs_f64()),
                Err(e) => {
                    eprintln!("  FAIL {name} {:.1}s", t0.elapsed().as_secs_f64());
                    failures.push(format!("{name}: {e}"));
                }
            }
        }
        assert!(
            failures.is_empty(),
            "step-indexed probe failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    });
}

/// WHAT `pi_intro` COSTS at the step-indexed family, SCRATCH. Shares the cached
/// spec with the tests above.
///
/// A green run does NOT say `pi_intro` holds at `RedStep`. It says the
/// strengthened form holds — with `whnf_acc f` supplied outright and the
/// pointwise premise given PER INDEX — which locates the gap precisely at the
/// place the real field quantifies its premise.
#[test]
fn candmodel_stepindex_pi_intro_cost_elaborates() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        // DEPENDENCIES FIRST. `build_spec_with_stack` hands back a fresh
        // `shared_spec().clone()`, so nothing another test registered is
        // present: without this the sources below fail with `Unknown
        // identifier: RedN`, which is a wiring fault and not a result about
        // the laws. Measured 2026-09-18 -- the control arm is what caught it.
        for (name, src) in Specification::candmodel_stepindex_probe_sources() {
            spec.add_recursive_def(&src, "CandModel step-indexed probe")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        let mut failures: Vec<String> = Vec::new();
        for (name, src) in Specification::candmodel_stepindex_pi_intro_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
            eprintln!("REGISTERING {name}");
            let t0 = std::time::Instant::now();
            match spec.add_recursive_def(&src, "CandModel step-index pi_intro cost") {
                Ok(()) => eprintln!("  ok   {name} {:.1}s", t0.elapsed().as_secs_f64()),
                Err(e) => {
                    eprintln!("  FAIL {name} {:.1}s", t0.elapsed().as_secs_f64());
                    failures.push(format!("{name}: {e}"));
                }
            }
        }
        assert!(
            failures.is_empty(),
            "step-index pi_intro cost failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    });
}

/// `cr2` AT THE STEP-INDEXED FAMILY, SCRATCH.
///
/// Registers `candmodel_stepindex_probe_sources` first — both because the term
/// below needs `RedN`, and because those four registrations act as the control:
/// if they fail, the harness is broken and nothing here is a statement about
/// `cr2`. That is the fault the first `pi_intro` run hit.
#[test]
fn candmodel_stepindex_cr2_elaborates() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        for (name, src) in Specification::candmodel_stepindex_probe_sources() {
            spec.add_recursive_def(&src, "CandModel step-indexed probe")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        let mut failures: Vec<String> = Vec::new();
        for (name, src) in Specification::candmodel_stepindex_cr2_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
            eprintln!("REGISTERING {name}");
            let t0 = std::time::Instant::now();
            match spec.add_recursive_def(&src, "CandModel step-index cr2") {
                Ok(()) => eprintln!("  ok   {name} {:.1}s", t0.elapsed().as_secs_f64()),
                Err(e) => {
                    eprintln!("  FAIL {name} {:.1}s", t0.elapsed().as_secs_f64());
                    failures.push(format!("{name}: {e}"));
                }
            }
        }
        assert!(
            failures.is_empty(),
            "step-index cr2 failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    });
}

/// `redTypeStep` REFUTED at the step-indexed family, SCRATCH.
///
/// Registers the step-indexed vec first, which is both a dependency (`RedN`,
/// `RedStep`) and the control: if those four fail, nothing here is a statement
/// about `redTypeStep`.
///
/// A green run means the REFUTATION elaborated — that assuming the field yields
/// `C` for arbitrary `C`. It is not a green for the law.
#[test]
fn candmodel_stepindex_typestep_refuted_elaborates() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        for (name, src) in Specification::candmodel_stepindex_probe_sources() {
            spec.add_recursive_def(&src, "CandModel step-indexed probe")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        let mut failures: Vec<String> = Vec::new();
        for (name, src) in Specification::candmodel_stepindex_typestep_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
            eprintln!("REGISTERING {name}");
            let t0 = std::time::Instant::now();
            match spec.add_recursive_def(&src, "CandModel step-index redTypeStep refutation") {
                Ok(()) => eprintln!("  ok   {name} {:.1}s", t0.elapsed().as_secs_f64()),
                Err(e) => {
                    eprintln!("  FAIL {name} {:.1}s", t0.elapsed().as_secs_f64());
                    failures.push(format!("{name}: {e}"));
                }
            }
        }
        assert!(
            failures.is_empty(),
            "step-index redTypeStep refutation failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    });
}

/// THE STEP INDEX IS LOAD-BEARING, SCRATCH.
///
/// Two constants at the same `(T, e)`: index 0 inhabited, index 1 empty. A green
/// run means both elaborated — the second is an ABSURDITY term, so its success
/// means `RedN 1` at that pair is refutable, not that it holds.
#[test]
fn candmodel_stepindex_loadbearing_elaborates() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        for (name, src) in Specification::candmodel_stepindex_probe_sources() {
            spec.add_recursive_def(&src, "CandModel step-indexed probe")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        let mut failures: Vec<String> = Vec::new();
        for (name, src) in Specification::candmodel_stepindex_loadbearing_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
            eprintln!("REGISTERING {name}");
            let t0 = std::time::Instant::now();
            match spec.add_recursive_def(&src, "CandModel step-index load-bearing") {
                Ok(()) => eprintln!("  ok   {name} {:.1}s", t0.elapsed().as_secs_f64()),
                Err(e) => {
                    eprintln!("  FAIL {name} {:.1}s", t0.elapsed().as_secs_f64());
                    failures.push(format!("{name}: {e}"));
                }
            }
        }
        assert!(
            failures.is_empty(),
            "step-index load-bearing failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    });
}

/// THE WHNF-INDEXED CANDIDATE, SCRATCH — §3k step 1.
///
/// Needs no dependency vec: `RedW` is self-contained, resting on
/// `whnf_fuel_red_wh3`, `the_red_env` and `AndType`, all of which the wired
/// bundles register.
///
/// A green run says the DEFINITION is well formed and `cr1` falls out at index
/// 0. It says nothing about `redTypeStep`, which §3k predicts holds only under a
/// fuel side condition, and nothing about `pi_elim`, which is the next thing to
/// try here.
#[test]
fn candmodel_whnf_indexed_elaborates() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        let mut failures: Vec<String> = Vec::new();
        for (name, src) in Specification::candmodel_whnf_indexed_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
            eprintln!("REGISTERING {name}");
            let t0 = std::time::Instant::now();
            match spec.add_recursive_def(&src, "CandModel whnf-indexed candidate") {
                Ok(()) => eprintln!("  ok   {name} {:.1}s", t0.elapsed().as_secs_f64()),
                Err(e) => {
                    eprintln!("  FAIL {name} {:.1}s", t0.elapsed().as_secs_f64());
                    failures.push(format!("{name}: {e}"));
                }
            }
        }
        assert!(
            failures.is_empty(),
            "whnf-indexed candidate failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    });
}

/// `pi_elim` AT THE WHNF-INDEXED CANDIDATE, SCRATCH.
///
/// Registers `candmodel_whnf_indexed_sources` first — dependency and control.
/// The question is whether `whnf_fuel_red_wh3` computes a `pi` to `some (pi ..)`
/// so the clause is selected; if it does not, the indirection that bought this
/// candidate its shot at `redTypeStep` costs it `pi_elim` instead.
#[test]
fn candmodel_whnf_pi_elim_elaborates() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        for (name, src) in Specification::candmodel_whnf_indexed_sources() {
            spec.add_recursive_def(&src, "CandModel whnf-indexed candidate")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        let mut failures: Vec<String> = Vec::new();
        for (name, src) in Specification::candmodel_whnf_pi_elim_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
            eprintln!("REGISTERING {name}");
            let t0 = std::time::Instant::now();
            match spec.add_recursive_def(&src, "CandModel whnf-indexed pi_elim") {
                Ok(()) => eprintln!("  ok   {name} {:.1}s", t0.elapsed().as_secs_f64()),
                Err(e) => {
                    eprintln!("  FAIL {name} {:.1}s", t0.elapsed().as_secs_f64());
                    failures.push(format!("{name}: {e}"));
                }
            }
        }
        assert!(
            failures.is_empty(),
            "whnf-indexed pi_elim failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    });
}

/// `redTypeStep` AT THE WHNF-INDEXED CANDIDATE, UNDER ITS FUEL SIDE CONDITION.
/// SCRATCH.
///
/// A green run does NOT say the field holds. It says the law degenerates to a
/// transport once the two types' whnfs agree at the fuel in hand — moving it
/// from the PROVED FALSE row (where `redstep_redTypeStep_refuted` puts it at the
/// head-indexed family) to the conditional row.
#[test]
fn candmodel_whnf_typestep_elaborates() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        for (name, src) in Specification::candmodel_whnf_indexed_sources() {
            spec.add_recursive_def(&src, "CandModel whnf-indexed candidate")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        let mut failures: Vec<String> = Vec::new();
        for (name, src) in Specification::candmodel_whnf_typestep_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
            eprintln!("REGISTERING {name}");
            let t0 = std::time::Instant::now();
            match spec.add_recursive_def(&src, "CandModel whnf-indexed redTypeStep") {
                Ok(()) => eprintln!("  ok   {name} {:.1}s", t0.elapsed().as_secs_f64()),
                Err(e) => {
                    eprintln!("  FAIL {name} {:.1}s", t0.elapsed().as_secs_f64());
                    failures.push(format!("{name}: {e}"));
                }
            }
        }
        assert!(
            failures.is_empty(),
            "whnf-indexed redTypeStep failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    });
}

/// `pi_intro`'s RESIDUAL AT THE WHNF-INDEXED CANDIDATE, SCRATCH.
///
/// A green run does NOT say `pi_intro` holds. It says the SAME two extra
/// premises that sufficed at `RedStep` suffice here — which is evidence the
/// residual belongs to the FIELD rather than to either family.
#[test]
fn candmodel_whnf_pi_intro_elaborates() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        for (name, src) in Specification::candmodel_whnf_indexed_sources() {
            spec.add_recursive_def(&src, "CandModel whnf-indexed candidate")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        let mut failures: Vec<String> = Vec::new();
        for (name, src) in Specification::candmodel_whnf_pi_intro_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
            eprintln!("REGISTERING {name}");
            let t0 = std::time::Instant::now();
            match spec.add_recursive_def(&src, "CandModel whnf-indexed pi_intro residual") {
                Ok(()) => eprintln!("  ok   {name} {:.1}s", t0.elapsed().as_secs_f64()),
                Err(e) => {
                    eprintln!("  FAIL {name} {:.1}s", t0.elapsed().as_secs_f64());
                    failures.push(format!("{name}: {e}"));
                }
            }
        }
        assert!(
            failures.is_empty(),
            "whnf-indexed pi_intro residual failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    });
}

/// `RedW` NON-VACUITY, plus `red_sort`. SCRATCH.
///
/// `redw_pi_clause_reached` is the one that matters: it says the `some (pi ..)`
/// arm is genuinely selected, so `RedW` is not the type-blind family behind an
/// indirection. Without it every other `RedW` result could be a statement about
/// `whnf_acc`.
#[test]
fn candmodel_whnf_nonvacuity_elaborates() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        for (name, src) in Specification::candmodel_whnf_indexed_sources() {
            spec.add_recursive_def(&src, "CandModel whnf-indexed candidate")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        let mut failures: Vec<String> = Vec::new();
        for (name, src) in Specification::candmodel_whnf_nonvacuity_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
            eprintln!("REGISTERING {name}");
            let t0 = std::time::Instant::now();
            match spec.add_recursive_def(&src, "CandModel whnf-indexed non-vacuity") {
                Ok(()) => eprintln!("  ok   {name} {:.1}s", t0.elapsed().as_secs_f64()),
                Err(e) => {
                    eprintln!("  FAIL {name} {:.1}s", t0.elapsed().as_secs_f64());
                    failures.push(format!("{name}: {e}"));
                }
            }
        }
        assert!(
            failures.is_empty(),
            "whnf-indexed non-vacuity failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    });
}

/// `cr2` AT THE WHNF-INDEXED CANDIDATE, SCRATCH — retried after the refactor.
///
/// The first attempt failed with `ExpectedSort((fun _o => Type) fvar)`, an
/// ELABORATOR limitation rather than a statement about `cr2`: the motive named
/// the successor clause as a type at a bound scrutinee, and inline that clause's
/// own type is a beta-redex not reduced in a sort position. `RedWInner` and
/// `RedWClause` now give both levels a name with a declared `Type` result.
#[test]
fn candmodel_whnf_cr2_elaborates() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        for (name, src) in Specification::candmodel_whnf_indexed_sources() {
            spec.add_recursive_def(&src, "CandModel whnf-indexed candidate")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        let mut failures: Vec<String> = Vec::new();
        for (name, src) in Specification::candmodel_whnf_cr2_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
            eprintln!("REGISTERING {name}");
            let t0 = std::time::Instant::now();
            match spec.add_recursive_def(&src, "CandModel whnf-indexed cr2") {
                Ok(()) => eprintln!("  ok   {name} {:.1}s", t0.elapsed().as_secs_f64()),
                Err(e) => {
                    eprintln!("  FAIL {name} {:.1}s", t0.elapsed().as_secs_f64());
                    failures.push(format!("{name}: {e}"));
                }
            }
        }
        assert!(
            failures.is_empty(),
            "whnf-indexed cr2 failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    });
}

/// `redConst` AT THE WHNF CANDIDATE, AT THE EMPTY ENVIRONMENT. SCRATCH.
///
/// Needs BOTH dependency vecs: the empty-environment probe for
/// `kdecl_empty` and the refutation, and the whnf candidate for `RedWStep`.
/// A green run says the two threads compose — the reduction hands this
/// candidate `redConst` for free, as it would any candidate.
#[test]
fn candmodel_whnf_redconst_elaborates() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        for (name, src) in Specification::candmodel_empty_env_probe_sources() {
            spec.add_recursive_def(&src, "CandModel empty-environment probe")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        for (name, src) in Specification::candmodel_whnf_indexed_sources() {
            spec.add_recursive_def(&src, "CandModel whnf-indexed candidate")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        let mut failures: Vec<String> = Vec::new();
        for (name, src) in Specification::candmodel_whnf_redconst_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
            eprintln!("REGISTERING {name}");
            let t0 = std::time::Instant::now();
            match spec.add_recursive_def(&src, "CandModel whnf redConst at empty env") {
                Ok(()) => eprintln!("  ok   {name} {:.1}s", t0.elapsed().as_secs_f64()),
                Err(e) => {
                    eprintln!("  FAIL {name} {:.1}s", t0.elapsed().as_secs_f64());
                    failures.push(format!("{name}: {e}"));
                }
            }
        }
        assert!(
            failures.is_empty(),
            "whnf redConst-at-empty failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    });
}

/// TESTING THE FORWARD/BACKWARD PREDICTION: `cr3` at a non-`pi` type. SCRATCH.
///
/// The design note predicts the seven backward laws hold wherever the clause
/// degenerates to `whnf_acc`. A green run is that prediction surviving its first
/// test at the hardest of the seven. It is ONE TYPE, not the general law.
#[test]
fn candmodel_whnf_cr3_at_sort_elaborates() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        for (name, src) in Specification::candmodel_whnf_indexed_sources() {
            spec.add_recursive_def(&src, "CandModel whnf-indexed candidate")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        let mut failures: Vec<String> = Vec::new();
        for (name, src) in Specification::candmodel_whnf_cr3_at_sort_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
            eprintln!("REGISTERING {name}");
            let t0 = std::time::Instant::now();
            match spec.add_recursive_def(&src, "CandModel whnf cr3 at a non-pi type") {
                Ok(()) => eprintln!("  ok   {name} {:.1}s", t0.elapsed().as_secs_f64()),
                Err(e) => {
                    eprintln!("  FAIL {name} {:.1}s", t0.elapsed().as_secs_f64());
                    failures.push(format!("{name}: {e}"));
                }
            }
        }
        assert!(
            failures.is_empty(),
            "whnf cr3-at-non-pi failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    });
}

/// THE FORWARD/BACKWARD PREDICTION, SECOND TEST: `redAbstraction` at a non-`pi`
/// type. SCRATCH.
///
/// A different KIND of backward law from `cr3` — one names a contractum and
/// rebuilds a specific redex, the other quantifies over successors. Needs the
/// `redabstraction_probe` vec as a dependency, for `redabstraction_blind`.
#[test]
fn candmodel_whnf_redabstraction_elaborates() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        for (name, src) in Specification::redabstraction_probe_sources() {
            spec.add_recursive_def(&src, "redAbstraction blind probe")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        for (name, src) in Specification::candmodel_whnf_indexed_sources() {
            spec.add_recursive_def(&src, "CandModel whnf-indexed candidate")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        let mut failures: Vec<String> = Vec::new();
        for (name, src) in Specification::candmodel_whnf_redabstraction_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
            eprintln!("REGISTERING {name}");
            let t0 = std::time::Instant::now();
            match spec.add_recursive_def(&src, "CandModel whnf redAbstraction at non-pi") {
                Ok(()) => eprintln!("  ok   {name} {:.1}s", t0.elapsed().as_secs_f64()),
                Err(e) => {
                    eprintln!("  FAIL {name} {:.1}s", t0.elapsed().as_secs_f64());
                    failures.push(format!("{name}: {e}"));
                }
            }
        }
        assert!(
            failures.is_empty(),
            "whnf redAbstraction-at-non-pi failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    });
}

/// LOCATING THE STALL: `cr3` at a `pi` type needs the pointwise half and nothing
/// else. SCRATCH.
///
/// A green run does NOT say `cr3` holds at a `pi`. It says the `whnf_acc` half
/// comes free from `cr3`'s own successors hypothesis, so the residual is ONE
/// obligation — produce the pointwise half — rather than a pile.
#[test]
fn candmodel_whnf_cr3_pi_stall_elaborates() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        for (name, src) in Specification::candmodel_whnf_indexed_sources() {
            spec.add_recursive_def(&src, "CandModel whnf-indexed candidate")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        let mut failures: Vec<String> = Vec::new();
        for (name, src) in Specification::candmodel_whnf_cr3_pi_stall_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
            eprintln!("REGISTERING {name}");
            let t0 = std::time::Instant::now();
            match spec.add_recursive_def(&src, "CandModel whnf cr3 pi-arm stall") {
                Ok(()) => eprintln!("  ok   {name} {:.1}s", t0.elapsed().as_secs_f64()),
                Err(e) => {
                    eprintln!("  FAIL {name} {:.1}s", t0.elapsed().as_secs_f64());
                    failures.push(format!("{name}: {e}"));
                }
            }
        }
        assert!(
            failures.is_empty(),
            "whnf cr3 pi-stall failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    });
}

/// `cr1` AT A FIXED INDEX. SCRATCH — a building block, not a result.
///
/// `redw_cr1` reads `whnf_acc` off `RedWStep`, which quantifies every index. Any
/// argument INSIDE the recursion has only `RedW k T x`, and needs `whnf_acc x`
/// from it to start an accessibility induction — which is what the `pi` arm's
/// pointwise half requires.
#[test]
fn candmodel_whnf_cr1_at_index_elaborates() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        for (name, src) in Specification::candmodel_whnf_indexed_sources() {
            spec.add_recursive_def(&src, "CandModel whnf-indexed candidate")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        let mut failures: Vec<String> = Vec::new();
        for (name, src) in Specification::candmodel_whnf_cr1_at_index_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
            eprintln!("REGISTERING {name}");
            let t0 = std::time::Instant::now();
            match spec.add_recursive_def(&src, "CandModel whnf cr1 at a fixed index") {
                Ok(()) => eprintln!("  ok   {name} {:.1}s", t0.elapsed().as_secs_f64()),
                Err(e) => {
                    eprintln!("  FAIL {name} {:.1}s", t0.elapsed().as_secs_f64());
                    failures.push(format!("{name}: {e}"));
                }
            }
        }
        assert!(
            failures.is_empty(),
            "whnf cr1-at-index failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    });
}

/// THE POINTWISE HALF at a non-dependent codomain. SCRATCH.
///
/// The `pi` arm's whole residual, for the case where the codomain does not
/// mention its binder. A green run says the route the design note records is
/// correct and that DEPENDENCE is the only thing left in it — `hcr3` is the
/// outer induction hypothesis, assumed, which is what makes this a probe of the
/// `pi` arm rather than of the whole law.
#[test]
fn candmodel_whnf_pointwise_elaborates() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        for (name, src) in Specification::candmodel_whnf_indexed_sources() {
            spec.add_recursive_def(&src, "CandModel whnf-indexed candidate")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        for (name, src) in Specification::candmodel_whnf_cr1_at_index_sources() {
            spec.add_recursive_def(&src, "cr1 at a fixed index")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        for (name, src) in Specification::candmodel_whnf_cr2_sources() {
            spec.add_recursive_def(&src, "cr2 at a fixed index")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        let mut failures: Vec<String> = Vec::new();
        for (name, src) in Specification::candmodel_whnf_pointwise_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
            eprintln!("REGISTERING {name}");
            let t0 = std::time::Instant::now();
            match spec.add_recursive_def(&src, "CandModel whnf pointwise half") {
                Ok(()) => eprintln!("  ok   {name} {:.1}s", t0.elapsed().as_secs_f64()),
                Err(e) => {
                    eprintln!("  FAIL {name} {:.1}s", t0.elapsed().as_secs_f64());
                    failures.push(format!("{name}: {e}"));
                }
            }
        }
        assert!(
            failures.is_empty(),
            "whnf pointwise-half failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    });
}

/// `cr3` AT A NON-DEPENDENT PI TYPE. SCRATCH — `hcr3` discharged.
///
/// The previous probe proved the `pi` arm's pointwise half MODULO `cr3` at index
/// `k`. This writes the outer induction that supplies it, so nothing about `cr3`
/// is assumed — only the ι/δ carriers. It is the fragment where the obstruction
/// is ABSENT, proved rather than assumed.
#[test]
fn candmodel_whnf_cr3_nondependent_elaborates() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        for (name, src) in Specification::candmodel_whnf_indexed_sources() {
            spec.add_recursive_def(&src, "CandModel whnf-indexed candidate")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        for (name, src) in Specification::candmodel_whnf_cr1_at_index_sources() {
            spec.add_recursive_def(&src, "cr1 at a fixed index")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        for (name, src) in Specification::candmodel_whnf_cr2_sources() {
            spec.add_recursive_def(&src, "cr2 at a fixed index")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        for (name, src) in Specification::candmodel_whnf_pointwise_sources() {
            spec.add_recursive_def(&src, "the pointwise half")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        let mut failures: Vec<String> = Vec::new();
        for (name, src) in Specification::candmodel_whnf_cr3_nondependent_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
            eprintln!("REGISTERING {name}");
            let t0 = std::time::Instant::now();
            match spec.add_recursive_def(&src, "CandModel whnf cr3 at a non-dependent pi") {
                Ok(()) => eprintln!("  ok   {name} {:.1}s", t0.elapsed().as_secs_f64()),
                Err(e) => {
                    eprintln!("  FAIL {name} {:.1}s", t0.elapsed().as_secs_f64());
                    failures.push(format!("{name}: {e}"));
                }
            }
        }
        assert!(
            failures.is_empty(),
            "whnf cr3-nondependent failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    });
}

/// `cr3` PROPAGATES UP a non-dependent pi. SCRATCH — the general form.
///
/// The fixed-`sort 0` version hides that `cr3` at the codomain was ever needed.
/// This takes the codomain and its `cr3` as parameters, so the result reads as a
/// PROPAGATION: if `cr3` holds at `bb` and `bb` does not mention its binder, it
/// holds at `pi ty bb`. Non-dependence is an explicit premise, used exactly where
/// the clause (`instantiate bb x`) and the lemma (`bb`) disagree.
#[test]
fn candmodel_whnf_cr3_propagates_elaborates() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        for (name, src) in Specification::candmodel_whnf_indexed_sources() {
            spec.add_recursive_def(&src, "CandModel whnf-indexed candidate")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        for (name, src) in Specification::candmodel_whnf_cr1_at_index_sources() {
            spec.add_recursive_def(&src, "cr1 at a fixed index")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        for (name, src) in Specification::candmodel_whnf_cr2_sources() {
            spec.add_recursive_def(&src, "cr2 at a fixed index")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        for (name, src) in Specification::candmodel_whnf_pointwise_sources() {
            spec.add_recursive_def(&src, "the pointwise half")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        let mut failures: Vec<String> = Vec::new();
        for (name, src) in Specification::candmodel_whnf_cr3_propagates_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
            eprintln!("REGISTERING {name}");
            let t0 = std::time::Instant::now();
            match spec.add_recursive_def(&src, "CandModel whnf cr3 propagation") {
                Ok(()) => eprintln!("  ok   {name} {:.1}s", t0.elapsed().as_secs_f64()),
                Err(e) => {
                    eprintln!("  FAIL {name} {:.1}s", t0.elapsed().as_secs_f64());
                    failures.push(format!("{name}: {e}"));
                }
            }
        }
        assert!(
            failures.is_empty(),
            "whnf cr3-propagation failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    });
}
