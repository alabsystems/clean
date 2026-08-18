// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `EvalIR` — **the kernel-EXECUTED witnesses for
//! [`super::eval_ir_float_fin`], and the one place they are checked against
//! the HARDWARE.**
//!
//! Completeness of the classified 4x4 tables is enforced by ELABORATION, but
//! nothing about a ROUNDING MODE is: a table that rounds half-up type-checks
//! exactly as well as one that rounds half-to-even, and computes a different
//! function. So every rule the fragment encodes has a witness the kernel had to
//! COMPUTE, and `test_every_finite_witness_agrees_with_real_f64` re-derives
//! each expected bit pattern by running the operation on `f64` itself rather
//! than by reading IEEE 754 a second time.
//!
//! The two tie witnesses are the pair that carries the mode: the SAME exact
//! half-ulp, resolved in opposite directions because the truncated significand
//! is even in one and odd in the other. A model that rounds half-up agrees with
//! every other witness in this file.
//!
//! Split from its module only because `data/paragon_ratchet.json`'s
//! `files_over_500` is shrink-only.
//!
//! `DerivedProved`, empty axiom closures.

/// Every finite-fragment witness: `(name, source, description)`.
///
/// The bit patterns, once:
/// ```text
/// 1.0                  = 0x3FF0000000000000 = 4607182418800017408
/// 1.0 + 2^-52          = 0x3FF0000000000001 = 4607182418800017409
/// 2^-52                = 0x3CB0000000000000 = 4372995238176751616
/// 2^-53                = 0x3CA0000000000000 = 4368491638549381120
/// 1.5 * 2^-53          = 0x3CB8000000000000 = 4370743438363066368
/// 2.0                  = 0x4000000000000000 = 4611686018427387904
/// 3.0                  = 0x4008000000000000 = 4613937818241073152
/// max normal           = 0x7FEFFFFFFFFFFFFF = 9218868437227405311
/// min subnormal        = 0x0000000000000001 = 1
/// largest subnormal    = 0x000FFFFFFFFFFFFF = 4503599627370495
/// min normal (2^-1022) = 0x0010000000000000 = 4503599627370496
/// ```
pub(super) const FIN_WITNESSES: &[(&str, &str, &str)] = &[
    (
        "ir_f64_w_fin_one_plus_one",
        "def ir_f64_w_fin_one_plus_one : Eq Nat (ir_f64_add_fin 4607182418800017408 4607182418800017408) 4611686018427387904 := Eq.refl Nat 4611686018427387904",
        "1.0 + 1.0 = 2.0 — THE WITNESS THE EIGHTH CHAIN REGISTERED AS A REFUSAL. It was refused \
         because rounding a 53-bit significand through ir_nat_div is a 2^52 loop, i.e. about \
         39,700 years; the restoring division makes it 0.089 s. A CARRY out of the significand: \
         2^53 rounds to 2^52 with the exponent bumped. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_f64_w_fin_two_plus_one",
        "def ir_f64_w_fin_two_plus_one : Eq Nat (ir_f64_add_fin 4611686018427387904 4607182418800017408) 4613937818241073152 := Eq.refl Nat 4613937818241073152",
        "2.0 + 1.0 = 3.0. Unequal scales, so one operand is aligned before the add. DerivedProved, \
         zero axiom_deps.",
    ),
    (
        "ir_f64_w_fin_exact_ulp",
        "def ir_f64_w_fin_exact_ulp : Eq Nat (ir_f64_add_fin 4607182418800017408 4372995238176751616) 4607182418800017409 := Eq.refl Nat 4607182418800017409",
        "1.0 + 2^-52 = 0x3FF0000000000001, EXACTLY — one ulp, no rounding, at an alignment \
         distance of 52. The control for the two tie witnesses below: same shape, one place \
         further apart, and the answer stops being exact. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_f64_w_fin_tie_to_even_down",
        "def ir_f64_w_fin_tie_to_even_down : Eq Nat (ir_f64_add_fin 4607182418800017408 4368491638549381120) 4607182418800017408 := Eq.refl Nat 4607182418800017408",
        "*** THE TIE, RESOLVED DOWN. *** 1.0 + 2^-53 is EXACTLY halfway between 1.0 and the next \
         representable number. roundTiesToEven takes the neighbour with the even significand, \
         which is 1.0 — so the answer is that the addition changed nothing. A model that rounded \
         half away from zero, or half up, would return 0x3FF0000000000001 here and would agree \
         with this one everywhere else in this file. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_f64_w_fin_tie_to_even_up",
        "def ir_f64_w_fin_tie_to_even_up : Eq Nat (ir_f64_add_fin 4607182418800017409 4368491638549381120) 4607182418800017410 := Eq.refl Nat 4607182418800017410",
        "*** THE TIE, RESOLVED UP — the same exact half-ulp, the other direction. *** The left \
         operand is 0x3FF0000000000001, whose significand is ODD, so ties-to-even rounds AWAY \
         from it. Paired with the witness above this pins the rule to the parity of the \
         truncated significand and not to a direction: same tie, opposite answers. DerivedProved, \
         zero axiom_deps.",
    ),
    (
        "ir_f64_w_fin_above_half",
        "def ir_f64_w_fin_above_half : Eq Nat (ir_f64_add_fin 4607182418800017408 4370743438363066368) 4607182418800017409 := Eq.refl Nat 4607182418800017409",
        "1.0 + 1.5*2^-53 is strictly ABOVE half an ulp, so it rounds up whatever the parity. The \
         third of the three arms of ir_f64_rup. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_f64_w_fin_pi_plus_e",
        "def ir_f64_w_fin_pi_plus_e : Eq Nat (ir_f64_add_fin 4614256656552045848 4613303445314885481) 4618283650560836160 := Eq.refl Nat 4618283650560836160",
        "pi + e, a pair with nothing special about it, against the hardware's answer. \
         DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_f64_w_fin_cancellation",
        "def ir_f64_w_fin_cancellation : Eq Nat (ir_f64_add_fin 4607182418800017408 13591863675404156928) 4607182418800017407 := Eq.refl Nat 4607182418800017407",
        "1.0 - 2^-53 = 0x3FEFFFFFFFFFFFFF. CANCELLATION: the difference has fewer bits than \
         either operand, so the result crosses into the next lower binade. DerivedProved, zero \
         axiom_deps.",
    ),
    (
        "ir_f64_w_fin_renormalise",
        "def ir_f64_w_fin_renormalise : Eq Nat (ir_f64_add_fin 4607182418800017408 13830554455654793215) 4368491638549381120 := Eq.refl Nat 4368491638549381120",
        "*** CATASTROPHIC CANCELLATION -> A RENORMALISING LEFT SHIFT. *** 1.0 - (1 - 2^-53) is \
         2^-53: the exact difference is the single integer 1, 52 bits short of a significand, and \
         the tail shifts it back up. This is the only witness that exercises ir_f64_lsh at its \
         maximum, and it is the one the scope document's set did not contain — every case it \
         labelled `renormalise` in fact had a zero left shift. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_f64_w_fin_opposite_signs",
        "def ir_f64_w_fin_opposite_signs : Eq Nat (ir_f64_add_fin 4617315517961601024 13837309855095848960) 4611686018427387904 := Eq.refl Nat 4611686018427387904",
        "5.0 + (-3.0) = 2.0. Opposite signs with the LEFT operand larger, so the result takes its \
         sign; the companion below takes the right operand's. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_f64_w_fin_opposite_signs_rhs",
        "def ir_f64_w_fin_opposite_signs_rhs : Eq Nat (ir_f64_add_fin 4613937818241073152 13840687554816376832) 13835058055282163712 := Eq.refl Nat 13835058055282163712",
        "3.0 + (-5.0) = -2.0. The same two magnitudes the other way round, so the sign now comes \
         from the RIGHT operand — which is what ir_f64_osign's magnitude comparison is for, and \
         what a model that always took the first operand's sign would get wrong. DerivedProved, \
         zero axiom_deps.",
    ),
    (
        "ir_f64_w_fin_exact_zero_sum",
        "def ir_f64_w_fin_exact_zero_sum : Eq Nat (ir_f64_add_fin 4607182418800017408 13830554455654793216) Nat.zero := Eq.refl Nat Nat.zero",
        "1.0 + (-1.0) = +0.0 THROUGH THE FINITE PIPELINE, not through the classified rule. \
         ir_f64_add_at still dispatches ir_f64_opposite first — that rule is exact and two \
         comparisons cheaper — so this input never reaches here in the machine; the witness is \
         registered anyway, because a redundant path that nobody checks is a path that can \
         silently disagree. \n\nIt is also the input the scope document could not account for: \
         `f2_magout3 0 1022` was killed at over 2 min 30 s and recorded as an unexplained cost \
         cliff. The cliff was the non-strict doubling, not the zero significand — see \
         super::eval_ir_bits — and this costs 0.037 s. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_f64_w_fin_both_negative",
        "def ir_f64_w_fin_both_negative : Eq Nat (ir_f64_add_fin 13830554455654793216 13830554455654793216) 13835058055282163712 := Eq.refl Nat 13835058055282163712",
        "(-1.0) + (-1.0) = -2.0: agreeing signs, so the sum keeps them. DerivedProved, zero \
         axiom_deps.",
    ),
    (
        "ir_f64_w_fin_max_alignment",
        "def ir_f64_w_fin_max_alignment : Eq Nat (ir_f64_add_fin 9218868437227405311 1) 9218868437227405311 := Eq.refl Nat 9218868437227405311",
        "*** THE COST ARGUMENT THAT REFUSED THIS FRAGMENT, EXECUTED. *** max normal + min \
         subnormal: an alignment distance of 2045, an EXACT 2098-bit integer sum, correctly \
         rounded back to 53 bits — and the answer is that the smallest number in the format \
         changes nothing about the largest. 1.5 s, once, in the kernel. The refusal said this \
         walks values of magnitude 2^53; it walks 2098 bits. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_f64_w_fin_overflow",
        "def ir_f64_w_fin_overflow : Eq Nat (ir_f64_add_fin 9218868437227405311 9218868437227405311) 9218868437227405312 := Eq.refl Nat 9218868437227405312",
        "OVERFLOW: max normal + max normal is +inf. Not a fault and not a refusal — IEEE 754 §7.4 \
         makes an overflow under roundTiesToEven the infinity of the result's sign, so the \
         classified fragment's infinity and this one are the SAME bit pattern arrived at two \
         different ways. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_f64_w_fin_subnormal_pair",
        "def ir_f64_w_fin_subnormal_pair : Eq Nat (ir_f64_add_fin 1 1) 2 := Eq.refl Nat 2",
        "The two smallest positive numbers in the format add exactly. Both operands are \
         subnormal, so both have no hidden bit — the arm of ir_f64_sig that a normals-only model \
         never reaches. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_f64_w_fin_subnormal_to_normal",
        "def ir_f64_w_fin_subnormal_to_normal : Eq Nat (ir_f64_add_fin 4503599627370495 1) 4503599627370496 := Eq.refl Nat 4503599627370496",
        "*** THE SUBNORMAL / NORMAL SEAM, UPWARD. *** The largest subnormal plus the smallest \
         subnormal is the smallest NORMAL, and the carry across that seam is what gradual \
         underflow means. It needs no special case here because a subnormal and an `ebits = 1` \
         normal share the scale zero. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_f64_w_fin_normal_to_subnormal",
        "def ir_f64_w_fin_normal_to_subnormal : Eq Nat (ir_f64_add_fin 4503599627370496 9223372036854775809) 4503599627370495 := Eq.refl Nat 4503599627370495",
        "*** THE SAME SEAM, DOWNWARD. *** 2^-1022 minus the smallest subnormal is the largest \
         subnormal. Paired with the witness above, the two say the seam is crossed exactly in \
         both directions. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_f64_w_fin_mul_one",
        "def ir_f64_w_fin_mul_one : Eq Nat (ir_f64_mul_fin 4607182418800017408 4607182418800017408) 4607182418800017408 := Eq.refl Nat 4607182418800017408",
        "1.0 * 1.0 = 1.0. The identity, computed rather than special-cased: a 106-bit product of \
         two hidden bits, then 53 bits dropped. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_f64_w_fin_mul_two_three",
        "def ir_f64_w_fin_mul_two_three : Eq Nat (ir_f64_mul_fin 4611686018427387904 4613937818241073152) 4618441417868443648 := Eq.refl Nat 4618441417868443648",
        "2.0 * 3.0 = 6.0. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_f64_w_fin_mul_sign",
        "def ir_f64_w_fin_mul_sign : Eq Nat (ir_f64_mul_fin 13837309855095848960 4619567317775286272) 13849976229047828480 := Eq.refl Nat 13849976229047828480",
        "(-3.0) * 7.0 = -21.0. The product's sign is the XOR of the operands', which is exact on \
         every pair including the ones the magnitude pipeline never sees. DerivedProved, zero \
         axiom_deps.",
    ),
    (
        "ir_f64_w_fin_mul_rounds",
        "def ir_f64_w_fin_mul_rounds : Eq Nat (ir_f64_mul_fin 4607182418800017409 4607182418800017409) 4607182418800017410 := Eq.refl Nat 4607182418800017410",
        "(1 + 2^-52)^2 — a product that does NOT fit in 53 bits and has to round. The exact \
         answer is 1 + 2^-51 + 2^-104; the representable neighbours are 1 + 2^-51 and \
         1 + 2^-51 + 2^-52, and the residue is far below half, so it rounds down to \
         0x3FF0000000000002. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_f64_w_fin_mul_pi_e",
        "def ir_f64_w_fin_mul_pi_e : Eq Nat (ir_f64_mul_fin 4614256656552045848 4613303445314885481) 4620997061037642868 := Eq.refl Nat 4620997061037642868",
        "pi * e, against the hardware. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_f64_w_fin_mul_overflow",
        "def ir_f64_w_fin_mul_overflow : Eq Nat (ir_f64_mul_fin 9218868437227405311 4611686018427387904) 9218868437227405312 := Eq.refl Nat 9218868437227405312",
        "max normal * 2.0 = +inf. OVERFLOW out of a multiplication. DerivedProved, zero \
         axiom_deps.",
    ),
    (
        "ir_f64_w_fin_mul_underflow",
        "def ir_f64_w_fin_mul_underflow : Eq Nat (ir_f64_mul_fin 1 4602678819172646912) Nat.zero := Eq.refl Nat Nat.zero",
        "*** UNDERFLOW TO ZERO, AND THE ROW THAT NEEDS THE NEGATIVE SCALE. *** The smallest \
         subnormal times 0.5 is exactly half the smallest representable number, which is a TIE \
         between +0 and the smallest subnormal — and ties-to-even takes the even one, which is \
         zero. The exact value sits below 2^-1074, so ir_f64_mbn is positive and ir_f64_rsh's \
         max is what drags the result onto the subnormal grid. A tail that only ever subtracted \
         `bitlen - 53` would answer the smallest subnormal here. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_f64_w_fin_mul_subnormal",
        "def ir_f64_w_fin_mul_subnormal : Eq Nat (ir_f64_mul_fin 1 4611686018427387904) 2 := Eq.refl Nat 2",
        "The smallest subnormal times 2.0 is the next subnormal — a product that stays below the \
         normal floor and is still EXACT there. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_f64_w_fin_mul_normal_to_subnormal",
        "def ir_f64_w_fin_mul_normal_to_subnormal : Eq Nat (ir_f64_mul_fin 4503599627370496 4602678819172646912) 2251799813685248 := Eq.refl Nat 2251799813685248",
        "2^-1022 * 0.5 = 2^-1023, which is SUBNORMAL: a product of two normals that lands below \
         the normal floor, so the significand loses its hidden bit and a place with it. \
         Gradual underflow, executed. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_f64_w_fin_mul_big_small",
        "def ir_f64_w_fin_mul_big_small : Eq Nat (ir_f64_mul_fin 9218868437227405311 1) 4382002437431492607 := Eq.refl Nat 4382002437431492607",
        "max normal * min subnormal. The two extreme magnitudes of the format multiplied \
         together, landing back in the middle. DerivedProved, zero axiom_deps.",
    ),
];

#[cfg(test)]
#[path = "eval_ir_float_fin_witnesses_tests.rs"]
mod tests;
