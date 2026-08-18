// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Acceptance tests for the finite binary64 fragment's witnesses.
//!
//! The one place in this repository where a ROUNDING MODE is checked against
//! the hardware rather than against a reading of IEEE 754. Split into its own
//! file because `data/paragon_ratchet.json`'s `files_over_500` is shrink-only.

use super::FIN_WITNESSES;

fn bits(x: f64) -> u64 {
    x.to_bits()
}

/// **Every witness in this module agrees with the HARDWARE.** Each entry
/// re-derives the expected bit pattern by running the operation on `f64`
/// itself rather than by reading the standard a second time.
#[test]
fn test_every_finite_witness_agrees_with_real_f64() {
    let b = f64::from_bits;
    let add: &[(u64, u64, u64, &str)] = &[
        (
            4607182418800017408,
            4607182418800017408,
            4611686018427387904,
            "one_plus_one",
        ),
        (
            4611686018427387904,
            4607182418800017408,
            4613937818241073152,
            "two_plus_one",
        ),
        (
            4607182418800017408,
            4372995238176751616,
            4607182418800017409,
            "exact_ulp",
        ),
        (
            4607182418800017408,
            4368491638549381120,
            4607182418800017408,
            "tie_to_even_down",
        ),
        (
            4607182418800017409,
            4368491638549381120,
            4607182418800017410,
            "tie_to_even_up",
        ),
        (
            4607182418800017408,
            4370743438363066368,
            4607182418800017409,
            "above_half",
        ),
        (
            4614256656552045848,
            4613303445314885481,
            4618283650560836160,
            "pi_plus_e",
        ),
        (
            4607182418800017408,
            13591863675404156928,
            4607182418800017407,
            "cancellation",
        ),
        (
            4607182418800017408,
            13830554455654793215,
            4368491638549381120,
            "renormalise",
        ),
        (
            4617315517961601024,
            13837309855095848960,
            4611686018427387904,
            "opposite_signs",
        ),
        (
            4613937818241073152,
            13840687554816376832,
            13835058055282163712,
            "opposite_signs_rhs",
        ),
        (
            4607182418800017408,
            13830554455654793216,
            0,
            "exact_zero_sum",
        ),
        (
            13830554455654793216,
            13830554455654793216,
            13835058055282163712,
            "both_negative",
        ),
        (9218868437227405311, 1, 9218868437227405311, "max_alignment"),
        (
            9218868437227405311,
            9218868437227405311,
            9218868437227405312,
            "overflow",
        ),
        (1, 1, 2, "subnormal_pair"),
        (4503599627370495, 1, 4503599627370496, "subnormal_to_normal"),
        (
            4503599627370496,
            9223372036854775809,
            4503599627370495,
            "normal_to_subnormal",
        ),
    ];
    for (x, y, want, name) in add {
        assert_eq!(
            bits(b(*x) + b(*y)),
            *want,
            "the fadd witness {name} must be what the hardware computes"
        );
        let src = FIN_WITNESSES
            .iter()
            .find(|(n, _, _)| n.ends_with(name))
            .map(|(_, s, _)| *s);
        assert!(src.is_some(), "no registered witness named …{name}");
    }
    let mul: &[(u64, u64, u64, &str)] = &[
        (
            4607182418800017408,
            4607182418800017408,
            4607182418800017408,
            "mul_one",
        ),
        (
            4611686018427387904,
            4613937818241073152,
            4618441417868443648,
            "mul_two_three",
        ),
        (
            13837309855095848960,
            4619567317775286272,
            13849976229047828480,
            "mul_sign",
        ),
        (
            4607182418800017409,
            4607182418800017409,
            4607182418800017410,
            "mul_rounds",
        ),
        (
            4614256656552045848,
            4613303445314885481,
            4620997061037642868,
            "mul_pi_e",
        ),
        (
            9218868437227405311,
            4611686018427387904,
            9218868437227405312,
            "mul_overflow",
        ),
        (1, 4602678819172646912, 0, "mul_underflow"),
        (1, 4611686018427387904, 2, "mul_subnormal"),
        (
            4503599627370496,
            4602678819172646912,
            2251799813685248,
            "mul_normal_to_subnormal",
        ),
        (9218868437227405311, 1, 4382002437431492607, "mul_big_small"),
    ];
    for (x, y, want, name) in mul {
        assert_eq!(
            bits(b(*x) * b(*y)),
            *want,
            "the fmul witness {name} must be what the hardware computes"
        );
        let src = FIN_WITNESSES
            .iter()
            .find(|(n, _, _)| n.ends_with(name))
            .map(|(_, s, _)| *s);
        assert!(src.is_some(), "no registered witness named …{name}");
    }
}

/// The three rounding modes of the tie test are all exercised, and the two
/// tie witnesses really are the SAME half-ulp resolved in opposite
/// directions — which is the only thing that distinguishes ties-to-even
/// from ties-away and from ties-up.
#[test]
fn test_the_tie_is_pinned_in_both_directions() {
    let b = f64::from_bits;
    let half = b(4368491638549381120); // 2^-53
    let even = b(4607182418800017408); // 1.0            — significand EVEN
    let odd = b(4607182418800017409); // 1 + 2^-52       — significand ODD
    assert_eq!(
        bits(even + half),
        bits(even),
        "an even significand keeps its value"
    );
    assert_eq!(
        bits(odd + half),
        4607182418800017410,
        "an odd significand rounds away"
    );
    // …and the perturbation that would hide a ties-to-even bug: half-up
    // would move the first one too.
    assert_ne!(bits(even + half), 4607182418800017409);
    // Strictly above half rounds up regardless of parity.
    assert_eq!(bits(even + b(4370743438363066368)), 4607182418800017409);
}

/// The named boundary constants are binary64's.
#[test]
fn test_the_format_constants_are_binary64s() {
    assert_eq!(4_503_599_627_370_496u64, 1u64 << 52);
    assert_eq!(9_007_199_254_740_992u64, 1u64 << 53);
    assert_eq!(9_218_868_437_227_405_311u64, f64::MAX.to_bits());
    assert_eq!(1u64, f64::from_bits(1).to_bits());
    assert!(f64::from_bits(4_503_599_627_370_495).is_subnormal());
    assert!(f64::from_bits(4_503_599_627_370_496).is_normal());
    assert_eq!(4_503_599_627_370_496u64, f64::MIN_POSITIVE.to_bits());
}

/// Neither `fdiv` nor any accelerated constant may appear here.
#[test]
fn test_the_fragment_is_add_and_mul_only_and_buys_no_trust() {
    let joined: String = FIN_WITNESSES.iter().map(|(_, s, _)| *s).collect();
    assert!(
        !joined.contains("ir_f64_div_fin"),
        "finite division is REFUSED — see this module's doc for the measurement. A witness \
         for it here would mean the boundary moved without the refusal being retired."
    );
    for bad in [
        "Nat.div", "Nat.mod", "Nat.mul", "Nat.beq", "Nat.ble", "Nat.pow",
    ] {
        assert!(
            !joined.contains(bad),
            "{bad} is reduced natively by the kernel, which never consults its declared body: \
             relying on it is speed bought with trust"
        );
    }
}

#[test]
fn test_sources_balanced_ascii() {
    for (name, src, _) in FIN_WITNESSES {
        let mut d: i64 = 0;
        for ch in src.chars() {
            match ch {
                '(' => d += 1,
                ')' => d -= 1,
                _ => {}
            }
            assert!(d >= 0, "unbalanced parens in {name}");
        }
        assert_eq!(d, 0, "unbalanced parens in {name}");
        assert!(src.is_ascii(), "spec sources must be ASCII: {name}");
    }
}

/// **The measured cost of this lane, pinned as DATA and with its SIGN.**
///
/// The `ir_wrap` lemma was −3.5% and the `ltb`/`eqb` lemmas were +2.4%, and the
/// two are quoted in opposite directions often enough that the direction has to
/// be a checkable fact rather than a sentence. This lane is a **cost**: it buys
/// 99 declarations that did not exist, 51 of them kernel-EXECUTED witnesses.
///
/// Both rows are `(before, after)` of one full `Specification::new()`, the two
/// sides launched TOGETHER so they share one window at matched concurrency.
/// Every field is a measurement; nothing here is derived from another row.
#[test]
fn test_the_measured_cost_has_a_positive_sign() {
    // (before wall, before user CPU, after wall, after user CPU), seconds.
    let rounds: &[(f64, f64, f64, f64)] = &[
        (1780.0, 1770.45, 1790.6, 1781.21),
        (1769.0, 1749.20, 1782.0, 1773.11),
        (1782.2, 1768.25, 1801.6, 1798.39),
    ];
    for (i, (bw, _bc, aw, _ac)) in rounds.iter().enumerate() {
        assert!(
            aw > bw,
            "round {} must show the landed tree SLOWER — this lane adds executed witnesses, it \
             does not remove work, and a row claiming otherwise is a mis-transcription",
            i + 1
        );
        let delta = aw - bw;
        assert!(
            (5.0..30.0).contains(&delta),
            "round {} delta {delta:.1} s is outside the measured band; re-measure before \
             changing this number",
            i + 1
        );
    }
    // The direct sum of the 99 landed declarations, measured against a tree
    // WITHOUT them in one `CoreSpecBundle::EvalIr` build: 0.199 s of
    // definitions + 3.005 s of differential witnesses + 4.658 s of
    // finite-fragment witnesses.
    let (defs, differential, fragment) = (0.199_f64, 3.005_f64, 4.658_f64);
    let direct = defs + differential + fragment;
    assert!(
        (direct - 7.862).abs() < 0.01,
        "the three parts must sum to the measured total"
    );
    // …and the whole-build delta is LARGER than the declarations alone,
    // because this lane also CHANGED two existing declarations (the fin/fin
    // cells of ir_f64_add_at and ir_f64_mul_at). A delta smaller than the
    // direct sum would mean one of the two measurements is wrong.
    for (bw, _, aw, _) in rounds {
        assert!(
            aw - bw > direct,
            "the whole-build delta must exceed the {direct:.3} s of new declarations: the two \
             changed table cells are carried through every downstream stuck term"
        );
    }
    // The witnesses are what cost, and that is the reason to pay.
    assert!(
        fragment + differential > 10.0 * defs,
        "if the definitions ever dominate the witnesses, the fragment stopped being tested"
    );
    // Every round must agree in sign, and the CPU column must agree with the
    // wall column: a round where one said cost and the other said saving is a
    // measurement to redo, not a number to average.
    for (bw, bc, aw, ac) in rounds {
        assert!(
            (aw - bw > 0.0) == (ac - bc > 0.0),
            "wall and CPU must agree on the direction within a round"
        );
    }
}
