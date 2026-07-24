// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::bridge::ay_backend::{AyLogic, AyProofBackend, AyProofResult};
use crate::theories::arithmetic::ArithmeticTheory;
use crate::theories::equality::EqualityTheory;
use std::hint::black_box;
use std::time::Instant;

const WARMUP_RUNS: usize = 25;
const MEASURE_RUNS: usize = 200;

#[derive(Clone, Copy, Debug)]
struct TimingSummary {
    min_ns: u128,
    median_ns: u128,
    mean_ns: u128,
    p95_ns: u128,
    max_ns: u128,
}

impl TimingSummary {
    fn from_samples(mut samples: Vec<u128>) -> Self {
        assert!(
            !samples.is_empty(),
            "measurement harness requires at least one timing sample"
        );
        samples.sort_unstable();
        let len = samples.len();
        let mean_ns = samples.iter().sum::<u128>() / len as u128;
        let median_ns = samples[len / 2];
        let p95_ns = samples[len.saturating_mul(95).div_ceil(100).saturating_sub(1)];
        Self {
            min_ns: samples[0],
            median_ns,
            mean_ns,
            p95_ns,
            max_ns: samples[len - 1],
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct MeasurementRow {
    case: &'static str,
    lane: &'static str,
    summary: TimingSummary,
}

fn measure_lane<F>(mut run: F) -> TimingSummary
where
    F: FnMut(),
{
    for _ in 0..WARMUP_RUNS {
        run();
    }

    let mut samples = Vec::with_capacity(MEASURE_RUNS);
    for _ in 0..MEASURE_RUNS {
        let start = Instant::now();
        run();
        samples.push(start.elapsed().as_nanos());
    }

    TimingSummary::from_samples(samples)
}

fn assert_ay_unsat(result: AyProofResult, expect_proof: bool, case: &str) {
    match result {
        AyProofResult::Unsat { proof, .. } => {
            if expect_proof {
                assert!(
                    proof.as_ref().is_some_and(|text| !text.trim().is_empty()),
                    "{case}: proof-enabled lane must return a non-empty proof"
                );
            } else {
                assert!(
                    proof.is_none(),
                    "{case}: no-proof lane must not return a proof artifact"
                );
            }
        }
        other => panic!("{case}: expected UNSAT from ay backend, got {other:?}"),
    }
}

fn native_bool_unsat() {
    let mut smt = SmtSolver::new();
    smt.add_clause(vec![TheoryLiteral::Bool(7)]);
    smt.add_clause(vec![TheoryLiteral::NegBool(7)]);
    let result = black_box(smt.solve());
    assert!(
        matches!(result, SmtResult::Unsat(_)),
        "native QF_BOOL fixture must be UNSAT"
    );
}

fn native_qf_uf_unsat() {
    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let c = smt.const_term("c");
    let _ = smt.assert_eq(a, b);
    let _ = smt.assert_eq(b, c);
    let _ = smt.assert_neq(a, c);

    let result = black_box(smt.solve());
    assert!(
        matches!(result, SmtResult::Unsat(_)),
        "native QF_UF fixture must be UNSAT"
    );
}

fn native_qf_lia_unsat() {
    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(ArithmeticTheory::new()));

    let x = smt.const_term("x");
    let zero = smt.int_term(0i64);
    smt.add_clause(vec![TheoryLiteral::Lt(x, zero)]);
    smt.add_clause(vec![TheoryLiteral::Lt(zero, x)]);

    let result = black_box(smt.solve());
    assert!(
        matches!(result, SmtResult::Unsat(_)),
        "native QF_LIA fixture must be UNSAT"
    );
}

fn ay_bool_unsat(expect_proof: bool) {
    let mut backend = if expect_proof {
        AyProofBackend::new_with_proofs(AyLogic::QfUf)
    } else {
        AyProofBackend::new_default(AyLogic::QfUf)
    };

    let p = backend.fresh_bool("p");
    backend.assert_formula(&p);
    backend.assert_formula(&format!("(not {p})"));

    let result = black_box(
        backend
            .check_sat()
            .expect("QF_BOOL fixture should solve without ay backend errors"),
    );
    assert_ay_unsat(result, expect_proof, "QF_BOOL");
}

fn ay_qf_uf_unsat(expect_proof: bool) {
    let mut backend = if expect_proof {
        AyProofBackend::new_with_proofs(AyLogic::QfUf)
    } else {
        AyProofBackend::new_default(AyLogic::QfUf)
    };

    backend.add_raw_declaration("(declare-sort U 0)");
    backend.add_raw_declaration("(declare-fun a () U)");
    backend.add_raw_declaration("(declare-fun b () U)");
    backend.add_raw_declaration("(declare-fun c () U)");
    backend.assert_formula("(= a b)");
    backend.assert_formula("(= b c)");
    backend.assert_formula("(not (= a c))");

    let result = black_box(
        backend
            .check_sat()
            .expect("QF_UF fixture should solve without ay backend errors"),
    );
    assert_ay_unsat(result, expect_proof, "QF_UF");
}

fn ay_qf_lia_unsat(expect_proof: bool) {
    let mut backend = if expect_proof {
        AyProofBackend::new_with_proofs(AyLogic::QfLia)
    } else {
        AyProofBackend::new_default(AyLogic::QfLia)
    };

    let x = backend.fresh_int("x");
    backend.assert_formula(&format!("(< {x} 0)"));
    backend.assert_formula(&format!("(< 0 {x})"));

    let result = black_box(
        backend
            .check_sat()
            .expect("QF_LIA fixture should solve without ay backend errors"),
    );
    assert_ay_unsat(result, expect_proof, "QF_LIA");
}

fn collect_measurements() -> Vec<MeasurementRow> {
    vec![
        MeasurementRow {
            case: "QF_BOOL",
            lane: "native",
            summary: measure_lane(native_bool_unsat),
        },
        MeasurementRow {
            case: "QF_BOOL",
            lane: "ay_no_proof",
            summary: measure_lane(|| ay_bool_unsat(false)),
        },
        MeasurementRow {
            case: "QF_BOOL",
            lane: "ay_proof_enabled",
            summary: measure_lane(|| ay_bool_unsat(true)),
        },
        MeasurementRow {
            case: "QF_UF",
            lane: "native",
            summary: measure_lane(native_qf_uf_unsat),
        },
        MeasurementRow {
            case: "QF_UF",
            lane: "ay_no_proof",
            summary: measure_lane(|| ay_qf_uf_unsat(false)),
        },
        MeasurementRow {
            case: "QF_UF",
            lane: "ay_proof_enabled",
            summary: measure_lane(|| ay_qf_uf_unsat(true)),
        },
        MeasurementRow {
            case: "QF_LIA",
            lane: "native",
            summary: measure_lane(native_qf_lia_unsat),
        },
        MeasurementRow {
            case: "QF_LIA",
            lane: "ay_no_proof",
            summary: measure_lane(|| ay_qf_lia_unsat(false)),
        },
        MeasurementRow {
            case: "QF_LIA",
            lane: "ay_proof_enabled",
            summary: measure_lane(|| ay_qf_lia_unsat(true)),
        },
    ]
}

#[test]
fn test_fast_path_measurement_snapshot_prints_native_vs_ay_latency() {
    crate::test_env::in_isolated_test_process(|| {
        let rows = collect_measurements();

        println!(
            "fast_path_measurement,warmups={WARMUP_RUNS},samples={MEASURE_RUNS},scope=solve_only"
        );
        println!("case,lane,min_ns,median_ns,mean_ns,p95_ns,max_ns");
        for row in rows {
            println!(
                "{},{},{},{},{},{},{}",
                row.case,
                row.lane,
                row.summary.min_ns,
                row.summary.median_ns,
                row.summary.mean_ns,
                row.summary.p95_ns,
                row.summary.max_ns,
            );
        }
    });
}
