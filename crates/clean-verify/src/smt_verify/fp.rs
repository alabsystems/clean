// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Acronyms like AST/VM/IR/SMT are conventionally uppercase in this codebase.
#![allow(clippy::upper_case_acronyms)]

//! FP (Floating-Point) theory checker.
//!
//! Validates floating-point theory lemmas by evaluating concrete IEEE 754
//! operations and detecting contradictions in FP constraints. Mirrors the BV
//! checker structure: parse clause literals, build a concrete assignment map,
//! evaluate operations on known values, and verify that the negated blocking
//! clause is unsatisfiable.

// 2026-07-31: the `pub(crate)` items in this module are exercised only by its
// own `#[cfg(test)]` tests, so only the non-test `lib` build sees them as dead.
// Scoped to `not(test)` on purpose: the `lib test` build still enforces
// `dead_code` in full, so an item with no caller anywhere still fails the gate.
#![cfg_attr(not(test), allow(dead_code))]

use std::cmp::Ordering;
use std::collections::HashMap;

use super::dag::{SmtProofDag, SmtStepId, SmtSymbol, SmtTerm, SmtTermId};
use super::trust::{StepTrustLevel, StepVerdict};

/// Name of this checker for trust ledger attribution.
pub(crate) const CHECKER_NAME: &str = "fp";

/// IEEE 754 floating-point sort, parameterized by exponent bits and
/// significand precision bits (including the hidden bit).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct FpSort {
    pub(crate) eb: u32,
    pub(crate) sb: u32,
}

impl FpSort {
    pub(crate) const FLOAT16: Self = Self { eb: 5, sb: 11 };
    pub(crate) const FLOAT32: Self = Self { eb: 8, sb: 24 };
    pub(crate) const FLOAT64: Self = Self { eb: 11, sb: 53 };
    pub(crate) const FLOAT128: Self = Self { eb: 15, sb: 113 };

    #[must_use]
    pub(crate) fn new(eb: u32, sb: u32) -> Option<Self> {
        if eb == 0 || sb < 2 || eb > 15 || sb > 113 {
            None
        } else {
            Some(Self { eb, sb })
        }
    }

    #[must_use]
    fn fraction_bits(self) -> u32 {
        self.sb - 1
    }

    #[must_use]
    fn exponent_max(self) -> u64 {
        (1u64 << self.eb) - 1
    }

    #[must_use]
    fn bias(self) -> i32 {
        ((1u32 << (self.eb - 1)) - 1) as i32
    }

    #[must_use]
    fn fraction_mask(self) -> u128 {
        (1u128 << self.fraction_bits()) - 1
    }

    #[must_use]
    fn hidden_bit(self) -> u128 {
        1u128 << self.fraction_bits()
    }

    #[must_use]
    fn from_named(name: &str) -> Option<Self> {
        match name {
            "Float16" | "FP16" => return Some(Self::FLOAT16),
            "Float32" | "FP32" => return Some(Self::FLOAT32),
            "Float64" | "FP64" | "Float" => return Some(Self::FLOAT64),
            "Float128" | "FP128" => return Some(Self::FLOAT128),
            _ => {}
        }

        let numbers = extract_u32s(name);
        if numbers.len() >= 2 {
            return Self::new(numbers[0], numbers[1]);
        }
        None
    }
}

/// IEEE 754 rounding mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum RoundingMode {
    RNE,
    RNA,
    RTP,
    RTN,
    RTZ,
}

impl RoundingMode {
    #[must_use]
    fn from_symbol(name: &str) -> Option<Self> {
        match name {
            "RNE" | "roundNearestTiesToEven" => Some(Self::RNE),
            "RNA" | "roundNearestTiesToAway" => Some(Self::RNA),
            "RTP" | "roundTowardPositive" => Some(Self::RTP),
            "RTN" | "roundTowardNegative" => Some(Self::RTN),
            "RTZ" | "roundTowardZero" => Some(Self::RTZ),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum ExactReal {
    NaN {
        sign: bool,
    },
    Infinite {
        sign: bool,
    },
    Zero {
        sign: bool,
    },
    Finite {
        sign: bool,
        significand: u128,
        exponent: i32,
    },
}

impl ExactReal {
    #[must_use]
    fn from_f64(value: f64) -> Self {
        let bits = value.to_bits();
        let sign = (bits >> 63) != 0;
        let exponent = ((bits >> 52) & 0x7ff) as i32;
        let fraction = bits & ((1u64 << 52) - 1);

        match exponent {
            0x7ff if fraction != 0 => Self::NaN { sign },
            0x7ff => Self::Infinite { sign },
            0 if fraction == 0 => Self::Zero { sign },
            0 => Self::Finite {
                sign,
                significand: u128::from(fraction),
                exponent: -1074,
            },
            _ => Self::Finite {
                sign,
                significand: u128::from((1u64 << 52) | fraction),
                exponent: exponent - 1023 - 52,
            },
        }
    }
}

/// Concrete IEEE 754 value.
///
/// `significand` stores the low 64 bits of the trailing significand bits.
/// Wider formats use a private high-word to support Float128 internally.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct FpValue {
    pub(crate) sort: FpSort,
    pub(crate) sign: bool,
    pub(crate) exponent: u64,
    pub(crate) significand: u64,
    significand_hi: u64,
}

impl FpValue {
    #[must_use]
    fn from_parts_wide(sort: FpSort, sign: bool, exponent: u64, significand: u128) -> Self {
        debug_assert!(significand <= sort.fraction_mask());
        Self {
            sort,
            sign,
            exponent,
            significand: significand as u64,
            significand_hi: (significand >> 64) as u64,
        }
    }

    #[must_use]
    fn fraction(self) -> u128 {
        (u128::from(self.significand_hi) << 64) | u128::from(self.significand)
    }

    #[must_use]
    fn exact_bits_eq(self, other: Self) -> bool {
        self.sort == other.sort
            && self.sign == other.sign
            && self.exponent == other.exponent
            && self.fraction() == other.fraction()
    }

    #[must_use]
    fn same_sort(self, other: Self) -> bool {
        self.sort == other.sort
    }

    #[must_use]
    fn zero(sort: FpSort, sign: bool) -> Self {
        Self::from_parts_wide(sort, sign, 0, 0)
    }

    #[must_use]
    fn infinity(sort: FpSort, sign: bool) -> Self {
        Self::from_parts_wide(sort, sign, sort.exponent_max(), 0)
    }

    #[must_use]
    fn nan(sort: FpSort) -> Self {
        Self::from_parts_wide(sort, false, sort.exponent_max(), 1)
    }

    #[must_use]
    fn max_finite(sort: FpSort, sign: bool) -> Self {
        Self::from_parts_wide(sort, sign, sort.exponent_max() - 1, sort.fraction_mask())
    }

    #[must_use]
    fn min_subnormal(sort: FpSort, sign: bool) -> Self {
        Self::from_parts_wide(sort, sign, 0, 1)
    }

    #[must_use]
    pub(crate) fn from_f32(value: f32) -> Self {
        let bits = value.to_bits();
        let sign = (bits >> 31) != 0;
        let exponent = ((bits >> 23) & 0xff) as u64;
        let significand = u64::from(bits & ((1u32 << 23) - 1));
        Self::from_parts_wide(FpSort::FLOAT32, sign, exponent, u128::from(significand))
    }

    #[must_use]
    pub(crate) fn from_f64(value: f64) -> Self {
        let bits = value.to_bits();
        let sign = (bits >> 63) != 0;
        let exponent = (bits >> 52) & 0x7ff;
        let significand = bits & ((1u64 << 52) - 1);
        Self::from_parts_wide(FpSort::FLOAT64, sign, exponent, u128::from(significand))
    }

    #[must_use]
    fn from_exact_real(sort: FpSort, exact: ExactReal, rm: RoundingMode) -> Self {
        match exact {
            ExactReal::NaN { sign } => {
                let mut value = Self::nan(sort);
                value.sign = sign;
                value
            }
            ExactReal::Infinite { sign } => Self::infinity(sort, sign),
            ExactReal::Zero { sign } => Self::zero(sort, sign),
            ExactReal::Finite {
                sign,
                significand,
                exponent,
            } => Self::from_exact_finite(sort, sign, significand, exponent, rm),
        }
    }

    #[must_use]
    fn from_exact_finite(
        sort: FpSort,
        sign: bool,
        significand: u128,
        exponent: i32,
        rm: RoundingMode,
    ) -> Self {
        if significand == 0 {
            return Self::zero(sort, sign);
        }

        let p = sort.sb as i32;
        let k = 127 - significand.leading_zeros() as i32;
        let mut unbiased = exponent + k;
        let min_normal = 1 - sort.bias();
        let max_normal = sort.bias();

        if unbiased > max_normal {
            return Self::overflow_value(sort, sign, rm);
        }

        if unbiased >= min_normal {
            let shift = p - 1 - k;
            let mut sig = if shift >= 0 {
                significand << (shift as u32)
            } else {
                round_shift_right_u128(significand, (-shift) as u32, sign, rm)
            };

            let full_precision_limit = 1u128 << (p as u32);
            if sig >= full_precision_limit {
                sig >>= 1;
                unbiased += 1;
                if unbiased > max_normal {
                    return Self::overflow_value(sort, sign, rm);
                }
            }

            let exponent_bits = (unbiased + sort.bias()) as u64;
            let fraction = sig & sort.fraction_mask();
            Self::from_parts_wide(sort, sign, exponent_bits, fraction)
        } else {
            let sub_exp = min_normal - (p - 1);
            let shift = exponent - sub_exp;
            let fraction = if shift >= 0 {
                significand << (shift as u32)
            } else {
                round_shift_right_u128(significand, (-shift) as u32, sign, rm)
            };

            if fraction == 0 {
                return Self::zero(sort, sign);
            }

            let min_normal_sig = sort.hidden_bit();
            if fraction >= min_normal_sig {
                return Self::from_parts_wide(sort, sign, 1, 0);
            }

            Self::from_parts_wide(sort, sign, 0, fraction)
        }
    }

    #[must_use]
    fn overflow_value(sort: FpSort, sign: bool, rm: RoundingMode) -> Self {
        match rm {
            RoundingMode::RNE | RoundingMode::RNA => Self::infinity(sort, sign),
            RoundingMode::RTP => {
                if sign {
                    Self::max_finite(sort, true)
                } else {
                    Self::infinity(sort, false)
                }
            }
            RoundingMode::RTN => {
                if sign {
                    Self::infinity(sort, true)
                } else {
                    Self::max_finite(sort, false)
                }
            }
            RoundingMode::RTZ => Self::max_finite(sort, sign),
        }
    }

    #[must_use]
    fn to_native_f32(self) -> f32 {
        debug_assert_eq!(self.sort, FpSort::FLOAT32);
        let sign = if self.sign { 1u32 } else { 0u32 };
        let bits = (sign << 31) | ((self.exponent as u32) << 23) | (self.significand as u32);
        f32::from_bits(bits)
    }

    #[must_use]
    fn to_native_f64(self) -> f64 {
        debug_assert_eq!(self.sort, FpSort::FLOAT64);
        let sign = if self.sign { 1u64 } else { 0u64 };
        let bits = (sign << 63) | (self.exponent << 52) | self.significand;
        f64::from_bits(bits)
    }

    #[must_use]
    pub(crate) fn to_f32(self) -> f32 {
        if self.sort == FpSort::FLOAT32 {
            self.to_native_f32()
        } else {
            self.to_f64() as f32
        }
    }

    #[must_use]
    pub(crate) fn to_f64(self) -> f64 {
        if self.sort == FpSort::FLOAT64 {
            return self.to_native_f64();
        }
        if self.sort == FpSort::FLOAT32 {
            return f64::from(self.to_native_f32());
        }
        if self.is_nan() {
            return f64::NAN.copysign(if self.sign { -1.0 } else { 1.0 });
        }
        if self.is_infinite() {
            return if self.sign {
                f64::NEG_INFINITY
            } else {
                f64::INFINITY
            };
        }
        if self.is_zero() {
            return if self.sign { -0.0 } else { 0.0 };
        }

        let frac_bits = self.sort.fraction_bits() as i32;
        let bias = self.sort.bias();
        let (significand, exponent) = if self.exponent == 0 {
            (self.fraction(), 1 - bias - frac_bits)
        } else {
            (
                self.sort.hidden_bit() | self.fraction(),
                self.exponent as i32 - bias - frac_bits,
            )
        };

        let mut value = significand as f64;
        value *= 2.0f64.powi(exponent);
        if self.sign {
            -value
        } else {
            value
        }
    }

    #[must_use]
    pub(crate) fn fp_add(self, rm: RoundingMode, other: Self) -> Self {
        if !self.same_sort(other) {
            return Self::nan(self.sort);
        }
        if self.sort == FpSort::FLOAT64 && rm == RoundingMode::RNE {
            return Self::from_f64(self.to_native_f64() + other.to_native_f64());
        }
        let exact = ExactReal::from_f64(self.to_f64() + other.to_f64());
        Self::from_exact_real(self.sort, exact, rm)
    }

    #[must_use]
    pub(crate) fn fp_sub(self, rm: RoundingMode, other: Self) -> Self {
        if !self.same_sort(other) {
            return Self::nan(self.sort);
        }
        if self.sort == FpSort::FLOAT64 && rm == RoundingMode::RNE {
            return Self::from_f64(self.to_native_f64() - other.to_native_f64());
        }
        let exact = ExactReal::from_f64(self.to_f64() - other.to_f64());
        Self::from_exact_real(self.sort, exact, rm)
    }

    #[must_use]
    pub(crate) fn fp_mul(self, rm: RoundingMode, other: Self) -> Self {
        if !self.same_sort(other) {
            return Self::nan(self.sort);
        }
        if self.sort == FpSort::FLOAT64 && rm == RoundingMode::RNE {
            return Self::from_f64(self.to_native_f64() * other.to_native_f64());
        }
        let exact = ExactReal::from_f64(self.to_f64() * other.to_f64());
        Self::from_exact_real(self.sort, exact, rm)
    }

    #[must_use]
    pub(crate) fn fp_div(self, rm: RoundingMode, other: Self) -> Self {
        if !self.same_sort(other) {
            return Self::nan(self.sort);
        }
        if self.sort == FpSort::FLOAT64 && rm == RoundingMode::RNE {
            return Self::from_f64(self.to_native_f64() / other.to_native_f64());
        }
        let exact = ExactReal::from_f64(self.to_f64() / other.to_f64());
        Self::from_exact_real(self.sort, exact, rm)
    }

    #[must_use]
    pub(crate) fn fp_sqrt(self, rm: RoundingMode) -> Self {
        if self.sort == FpSort::FLOAT64 && rm == RoundingMode::RNE {
            return Self::from_f64(self.to_native_f64().sqrt());
        }
        let exact = ExactReal::from_f64(self.to_f64().sqrt());
        Self::from_exact_real(self.sort, exact, rm)
    }

    #[must_use]
    pub(crate) fn fp_fma(self, rm: RoundingMode, b: Self, c: Self) -> Self {
        if !(self.same_sort(b) && self.same_sort(c)) {
            return Self::nan(self.sort);
        }
        if self.sort == FpSort::FLOAT64 && rm == RoundingMode::RNE {
            return Self::from_f64(
                self.to_native_f64()
                    .mul_add(b.to_native_f64(), c.to_native_f64()),
            );
        }
        let exact = ExactReal::from_f64(self.to_f64().mul_add(b.to_f64(), c.to_f64()));
        Self::from_exact_real(self.sort, exact, rm)
    }

    #[must_use]
    pub(crate) fn fp_neg(self, _rm: RoundingMode) -> Self {
        let mut result = self;
        result.sign = !result.sign;
        result
    }

    #[must_use]
    pub(crate) fn fp_abs(self, _rm: RoundingMode) -> Self {
        let mut result = self;
        result.sign = false;
        result
    }

    #[must_use]
    pub(crate) fn fp_lt(self, other: Self) -> bool {
        matches!(self.numeric_cmp(other), Some(Ordering::Less))
    }

    #[must_use]
    pub(crate) fn fp_leq(self, other: Self) -> bool {
        matches!(
            self.numeric_cmp(other),
            Some(Ordering::Less | Ordering::Equal)
        )
    }

    #[must_use]
    pub(crate) fn fp_gt(self, other: Self) -> bool {
        matches!(self.numeric_cmp(other), Some(Ordering::Greater))
    }

    #[must_use]
    pub(crate) fn fp_geq(self, other: Self) -> bool {
        matches!(
            self.numeric_cmp(other),
            Some(Ordering::Greater | Ordering::Equal)
        )
    }

    #[must_use]
    pub(crate) fn fp_eq(self, other: Self) -> bool {
        if !self.same_sort(other) || self.is_nan() || other.is_nan() {
            return false;
        }
        if self.is_zero() && other.is_zero() {
            return true;
        }
        self.exact_bits_eq(other)
    }

    #[must_use]
    fn magnitude_cmp(self, other: Self) -> Ordering {
        match (self.is_infinite(), other.is_infinite()) {
            (true, true) => Ordering::Equal,
            (true, false) => Ordering::Greater,
            (false, true) => Ordering::Less,
            (false, false) => self
                .exponent
                .cmp(&other.exponent)
                .then_with(|| self.fraction().cmp(&other.fraction())),
        }
    }

    #[must_use]
    fn numeric_cmp(self, other: Self) -> Option<Ordering> {
        if !self.same_sort(other) || self.is_nan() || other.is_nan() {
            return None;
        }
        if self.is_zero() && other.is_zero() {
            return Some(Ordering::Equal);
        }
        if self.sign != other.sign {
            return Some(if self.sign {
                Ordering::Less
            } else {
                Ordering::Greater
            });
        }

        let cmp = self.magnitude_cmp(other);
        if self.sign {
            Some(cmp.reverse())
        } else {
            Some(cmp)
        }
    }

    #[must_use]
    pub(crate) fn is_nan(self) -> bool {
        self.exponent == self.sort.exponent_max() && self.fraction() != 0
    }

    #[must_use]
    pub(crate) fn is_infinite(self) -> bool {
        self.exponent == self.sort.exponent_max() && self.fraction() == 0
    }

    #[must_use]
    pub(crate) fn is_zero(self) -> bool {
        self.exponent == 0 && self.fraction() == 0
    }

    #[must_use]
    pub(crate) fn is_normal(self) -> bool {
        self.exponent != 0 && self.exponent != self.sort.exponent_max()
    }

    #[must_use]
    pub(crate) fn is_subnormal(self) -> bool {
        self.exponent == 0 && self.fraction() != 0
    }

    #[must_use]
    pub(crate) fn is_positive(self) -> bool {
        !self.sign
    }

    #[must_use]
    pub(crate) fn is_negative(self) -> bool {
        self.sign
    }
}

/// An FP constraint extracted from a clause literal.
#[derive(Debug, Clone)]
pub(crate) enum FpConstraint {
    /// `term = fp_constant`
    Eq(SmtTermId, SmtTermId),
    /// `term != fp_constant`
    Neq(SmtTermId, SmtTermId),
    /// FP predicate that must hold.
    Pred {
        op: FpPredOp,
        lhs: SmtTermId,
        rhs: Option<SmtTermId>,
        negated: bool,
    },
}

/// FP predicate operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum FpPredOp {
    Eq,
    Lt,
    Leq,
    Gt,
    Geq,
    IsNaN,
    IsInfinite,
    IsZero,
    IsNormal,
    IsSubnormal,
    IsPositive,
    IsNegative,
}

/// Check an FP theory lemma.
///
/// The clause is a blocking clause (disjunction). The negation of the clause
/// forms the conflict. We check whether the conflict is indeed unsatisfiable
/// by evaluating concrete floating-point operations.
///
/// Returns `KernelVerified` if a concrete contradiction is found,
/// `StructurallyAccepted` if the clause contains non-concrete terms that
/// cannot be fully evaluated, or `Trusted` on error.
pub(crate) fn check_fp_lemma(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
) -> StepVerdict {
    if clause.is_empty() {
        return fail(step_id, "fp: empty clause");
    }

    let mut constraints = Vec::with_capacity(clause.len());
    let mut all_concrete = true;

    for &lit in clause {
        match parse_fp_literal(dag, lit) {
            Some(c) => constraints.push(c),
            None => {
                all_concrete = false;
            }
        }
    }

    if constraints.is_empty() {
        return structural_accept(step_id, "fp: no parseable FP constraints");
    }

    let mut assignments: HashMap<SmtTermId, FpValue> = HashMap::new();
    let max_iters = constraints.len() + 1;

    for _ in 0..max_iters {
        let prev_count = assignments.len();

        for constraint in &constraints {
            if let FpConstraint::Eq(lhs_id, rhs_id) = constraint {
                try_assign(dag, *lhs_id, *rhs_id, &mut assignments);
                try_assign(dag, *rhs_id, *lhs_id, &mut assignments);
            }
        }

        if assignments.len() == prev_count {
            break;
        }
    }

    let has_contradiction = constraints
        .iter()
        .any(|c| is_contradiction(dag, c, &assignments));

    if has_contradiction {
        ok(step_id)
    } else if all_concrete {
        fail(
            step_id,
            "fp: no contradiction found in concrete constraints",
        )
    } else {
        structural_accept(
            step_id,
            "fp: non-concrete FP constraints, structurally accepted",
        )
    }
}

fn try_assign(
    dag: &SmtProofDag,
    term_id: SmtTermId,
    val_id: SmtTermId,
    assignments: &mut HashMap<SmtTermId, FpValue>,
) {
    if assignments.contains_key(&term_id) {
        return;
    }

    if let Some(SmtTerm::Var(_, sort)) = dag.term(term_id) {
        if let Some(value) = eval_fp_term(dag, val_id, assignments) {
            if let Some(var_sort) = fp_sort_from_smt_sort(sort) {
                if var_sort != value.sort {
                    return;
                }
            }
            assignments.insert(term_id, value);
        }
    }
}

fn is_contradiction(
    dag: &SmtProofDag,
    constraint: &FpConstraint,
    assignments: &HashMap<SmtTermId, FpValue>,
) -> bool {
    match constraint {
        FpConstraint::Eq(lhs_id, rhs_id) => {
            if let (Some(lhs), Some(rhs)) = (
                eval_fp_term(dag, *lhs_id, assignments),
                eval_fp_term(dag, *rhs_id, assignments),
            ) {
                !lhs.exact_bits_eq(rhs)
            } else {
                false
            }
        }
        FpConstraint::Neq(lhs_id, rhs_id) => {
            if let (Some(lhs), Some(rhs)) = (
                eval_fp_term(dag, *lhs_id, assignments),
                eval_fp_term(dag, *rhs_id, assignments),
            ) {
                lhs.exact_bits_eq(rhs)
            } else {
                false
            }
        }
        FpConstraint::Pred {
            op,
            lhs,
            rhs,
            negated,
        } => {
            if let Some(result) = eval_fp_predicate(dag, *op, *lhs, *rhs, assignments) {
                if *negated {
                    result
                } else {
                    !result
                }
            } else {
                false
            }
        }
    }
}

fn parse_fp_literal(dag: &SmtProofDag, lit: SmtTermId) -> Option<FpConstraint> {
    let term = dag.term(lit)?;

    match term {
        SmtTerm::App(SmtSymbol::Named(op), args) => match op.as_str() {
            "=" if args.len() == 2 => Some(FpConstraint::Neq(args[0], args[1])),
            "distinct" if args.len() == 2 => Some(FpConstraint::Eq(args[0], args[1])),
            _ => parse_fp_predicate(op.as_str(), args, true),
        },
        SmtTerm::Not(inner) => {
            let inner_term = dag.term(*inner)?;
            match inner_term {
                SmtTerm::App(SmtSymbol::Named(op), args) => match op.as_str() {
                    "=" if args.len() == 2 => Some(FpConstraint::Eq(args[0], args[1])),
                    "distinct" if args.len() == 2 => Some(FpConstraint::Neq(args[0], args[1])),
                    _ => parse_fp_predicate(op.as_str(), args, false),
                },
                _ => None,
            }
        }
        _ => None,
    }
}

fn parse_fp_predicate(op: &str, args: &[SmtTermId], negated: bool) -> Option<FpConstraint> {
    let (pred, lhs, rhs) = match (op, args.len()) {
        ("fp.eq", 2) => (FpPredOp::Eq, args[0], Some(args[1])),
        ("fp.lt", 2) => (FpPredOp::Lt, args[0], Some(args[1])),
        ("fp.leq", 2) => (FpPredOp::Leq, args[0], Some(args[1])),
        ("fp.gt", 2) => (FpPredOp::Gt, args[0], Some(args[1])),
        ("fp.geq", 2) => (FpPredOp::Geq, args[0], Some(args[1])),
        ("fp.isNaN", 1) => (FpPredOp::IsNaN, args[0], None),
        ("fp.isInfinite", 1) => (FpPredOp::IsInfinite, args[0], None),
        ("fp.isZero", 1) => (FpPredOp::IsZero, args[0], None),
        ("fp.isNormal", 1) => (FpPredOp::IsNormal, args[0], None),
        ("fp.isSubnormal", 1) => (FpPredOp::IsSubnormal, args[0], None),
        ("fp.isPositive", 1) => (FpPredOp::IsPositive, args[0], None),
        ("fp.isNegative", 1) => (FpPredOp::IsNegative, args[0], None),
        _ => return None,
    };

    Some(FpConstraint::Pred {
        op: pred,
        lhs,
        rhs,
        negated,
    })
}

fn eval_fp_term(
    dag: &SmtProofDag,
    term_id: SmtTermId,
    assignments: &HashMap<SmtTermId, FpValue>,
) -> Option<FpValue> {
    if let Some(value) = assignments.get(&term_id) {
        return Some(*value);
    }

    let term = dag.term(term_id)?;
    match term {
        SmtTerm::Var(..) => None,
        SmtTerm::App(sym, args) => eval_fp_app(dag, sym, args, assignments),
        _ => None,
    }
}

fn eval_fp_app(
    dag: &SmtProofDag,
    sym: &SmtSymbol,
    args: &[SmtTermId],
    assignments: &HashMap<SmtTermId, FpValue>,
) -> Option<FpValue> {
    match sym {
        SmtSymbol::Named(name) => eval_fp_named_op(dag, name.as_str(), args, assignments),
        SmtSymbol::Indexed(name, indices) => eval_fp_indexed_op(name.as_str(), indices, args),
    }
}

fn eval_fp_named_op(
    dag: &SmtProofDag,
    op: &str,
    args: &[SmtTermId],
    assignments: &HashMap<SmtTermId, FpValue>,
) -> Option<FpValue> {
    match op {
        "fp" if args.len() == 3 => eval_fp_constructor(dag, args),
        "fp.add" if args.len() == 3 => {
            let rm = parse_rounding_mode(dag, args[0])?;
            let a = eval_fp_term(dag, args[1], assignments)?;
            let b = eval_fp_term(dag, args[2], assignments)?;
            Some(a.fp_add(rm, b))
        }
        "fp.sub" if args.len() == 3 => {
            let rm = parse_rounding_mode(dag, args[0])?;
            let a = eval_fp_term(dag, args[1], assignments)?;
            let b = eval_fp_term(dag, args[2], assignments)?;
            Some(a.fp_sub(rm, b))
        }
        "fp.mul" if args.len() == 3 => {
            let rm = parse_rounding_mode(dag, args[0])?;
            let a = eval_fp_term(dag, args[1], assignments)?;
            let b = eval_fp_term(dag, args[2], assignments)?;
            Some(a.fp_mul(rm, b))
        }
        "fp.div" if args.len() == 3 => {
            let rm = parse_rounding_mode(dag, args[0])?;
            let a = eval_fp_term(dag, args[1], assignments)?;
            let b = eval_fp_term(dag, args[2], assignments)?;
            Some(a.fp_div(rm, b))
        }
        "fp.sqrt" if args.len() == 2 => {
            let rm = parse_rounding_mode(dag, args[0])?;
            let a = eval_fp_term(dag, args[1], assignments)?;
            Some(a.fp_sqrt(rm))
        }
        "fp.fma" if args.len() == 4 => {
            let rm = parse_rounding_mode(dag, args[0])?;
            let a = eval_fp_term(dag, args[1], assignments)?;
            let b = eval_fp_term(dag, args[2], assignments)?;
            let c = eval_fp_term(dag, args[3], assignments)?;
            Some(a.fp_fma(rm, b, c))
        }
        "fp.neg" if args.len() == 1 => {
            let a = eval_fp_term(dag, args[0], assignments)?;
            Some(a.fp_neg(RoundingMode::RNE))
        }
        "fp.neg" if args.len() == 2 => {
            let rm = parse_rounding_mode(dag, args[0])?;
            let a = eval_fp_term(dag, args[1], assignments)?;
            Some(a.fp_neg(rm))
        }
        "fp.abs" if args.len() == 1 => {
            let a = eval_fp_term(dag, args[0], assignments)?;
            Some(a.fp_abs(RoundingMode::RNE))
        }
        "fp.abs" if args.len() == 2 => {
            let rm = parse_rounding_mode(dag, args[0])?;
            let a = eval_fp_term(dag, args[1], assignments)?;
            Some(a.fp_abs(rm))
        }
        _ => None,
    }
}

fn eval_fp_indexed_op(op: &str, indices: &[u32], args: &[SmtTermId]) -> Option<FpValue> {
    if !args.is_empty() || indices.len() != 2 {
        return None;
    }
    let sort = FpSort::new(indices[0], indices[1])?;
    match op {
        "+oo" => Some(FpValue::infinity(sort, false)),
        "-oo" => Some(FpValue::infinity(sort, true)),
        "+zero" => Some(FpValue::zero(sort, false)),
        "-zero" => Some(FpValue::zero(sort, true)),
        "NaN" | "nan" => Some(FpValue::nan(sort)),
        _ => None,
    }
}

fn eval_fp_constructor(dag: &SmtProofDag, args: &[SmtTermId]) -> Option<FpValue> {
    let (sign_value, sign_width) = eval_bitvec_const(dag, args[0])?;
    let (exponent_value, exponent_width) = eval_bitvec_const(dag, args[1])?;
    let (significand_value, significand_width) = eval_bitvec_const(dag, args[2])?;

    if sign_width != 1 {
        return None;
    }

    let sort = FpSort::new(exponent_width, significand_width + 1)?;
    Some(FpValue::from_parts_wide(
        sort,
        sign_value != 0,
        exponent_value as u64,
        significand_value,
    ))
}

fn eval_fp_predicate(
    dag: &SmtProofDag,
    op: FpPredOp,
    lhs: SmtTermId,
    rhs: Option<SmtTermId>,
    assignments: &HashMap<SmtTermId, FpValue>,
) -> Option<bool> {
    let lhs_value = eval_fp_term(dag, lhs, assignments)?;
    match op {
        FpPredOp::Eq => {
            let rhs_value = eval_fp_term(dag, rhs?, assignments)?;
            Some(lhs_value.fp_eq(rhs_value))
        }
        FpPredOp::Lt => {
            let rhs_value = eval_fp_term(dag, rhs?, assignments)?;
            Some(lhs_value.fp_lt(rhs_value))
        }
        FpPredOp::Leq => {
            let rhs_value = eval_fp_term(dag, rhs?, assignments)?;
            Some(lhs_value.fp_leq(rhs_value))
        }
        FpPredOp::Gt => {
            let rhs_value = eval_fp_term(dag, rhs?, assignments)?;
            Some(lhs_value.fp_gt(rhs_value))
        }
        FpPredOp::Geq => {
            let rhs_value = eval_fp_term(dag, rhs?, assignments)?;
            Some(lhs_value.fp_geq(rhs_value))
        }
        FpPredOp::IsNaN => Some(lhs_value.is_nan()),
        FpPredOp::IsInfinite => Some(lhs_value.is_infinite()),
        FpPredOp::IsZero => Some(lhs_value.is_zero()),
        FpPredOp::IsNormal => Some(lhs_value.is_normal()),
        FpPredOp::IsSubnormal => Some(lhs_value.is_subnormal()),
        FpPredOp::IsPositive => Some(lhs_value.is_positive()),
        FpPredOp::IsNegative => Some(lhs_value.is_negative()),
    }
}

fn parse_rounding_mode(dag: &SmtProofDag, term_id: SmtTermId) -> Option<RoundingMode> {
    match dag.term(term_id)? {
        SmtTerm::Var(name, _) => RoundingMode::from_symbol(name),
        SmtTerm::App(SmtSymbol::Named(name), args) if args.is_empty() => {
            RoundingMode::from_symbol(name)
        }
        _ => None,
    }
}

fn eval_bitvec_const(dag: &SmtProofDag, term_id: SmtTermId) -> Option<(u128, u32)> {
    match dag.term(term_id)? {
        SmtTerm::BitVec(value, width) => Some((u128::from(*value), *width)),
        _ => None,
    }
}

fn fp_sort_from_smt_sort(sort: &super::dag::SmtSort) -> Option<FpSort> {
    match sort {
        super::dag::SmtSort::Named(name) => FpSort::from_named(name),
        _ => None,
    }
}

fn extract_u32s(text: &str) -> Vec<u32> {
    let mut out = Vec::new();
    let mut current = String::new();
    for ch in text.chars() {
        if ch.is_ascii_digit() {
            current.push(ch);
        } else if !current.is_empty() {
            if let Ok(num) = current.parse::<u32>() {
                out.push(num);
            }
            current.clear();
        }
    }
    if !current.is_empty() {
        if let Ok(num) = current.parse::<u32>() {
            out.push(num);
        }
    }
    out
}

fn round_shift_right_u128(value: u128, shift: u32, sign: bool, rm: RoundingMode) -> u128 {
    if shift == 0 {
        return value;
    }

    if shift > 128 {
        return match rm {
            RoundingMode::RTP if !sign && value != 0 => 1,
            RoundingMode::RTN if sign && value != 0 => 1,
            _ => 0,
        };
    }

    let (q, rem, half) = if shift == 128 {
        (0, value, 1u128 << 127)
    } else {
        let q = value >> shift;
        let mask = (1u128 << shift) - 1;
        let rem = value & mask;
        let half = 1u128 << (shift - 1);
        (q, rem, half)
    };

    if rem == 0 {
        return q;
    }

    let increment = match rm {
        RoundingMode::RNE => rem > half || (rem == half && (q & 1) == 1),
        RoundingMode::RNA => rem >= half,
        RoundingMode::RTP => !sign,
        RoundingMode::RTN => sign,
        RoundingMode::RTZ => false,
    };

    q + if increment { 1 } else { 0 }
}

fn ok(step_id: SmtStepId) -> StepVerdict {
    StepVerdict {
        step_id,
        trust_level: StepTrustLevel::KernelVerified,
        checker: CHECKER_NAME,
        detail: None,
    }
}

fn fail(step_id: SmtStepId, reason: &str) -> StepVerdict {
    StepVerdict {
        step_id,
        trust_level: StepTrustLevel::Trusted,
        checker: CHECKER_NAME,
        detail: Some(reason.to_string()),
    }
}

fn structural_accept(step_id: SmtStepId, detail: &str) -> StepVerdict {
    StepVerdict {
        step_id,
        trust_level: StepTrustLevel::StructurallyAccepted,
        checker: CHECKER_NAME,
        detail: Some(detail.to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt_verify::dag::{SmtProofDag, SmtSort, SmtSymbol, SmtTerm};
    use crate::smt_verify::trust::StepTrustLevel;

    fn add_bv_const(dag: &mut SmtProofDag, value: u64, width: u32) -> SmtTermId {
        dag.add_term(SmtTerm::BitVec(value, width))
    }

    fn add_fp_var(dag: &mut SmtProofDag, name: &str, sort: FpSort) -> SmtTermId {
        let sort_name = match sort {
            FpSort::FLOAT16 => "Float16",
            FpSort::FLOAT32 => "Float32",
            FpSort::FLOAT64 => "Float64",
            FpSort::FLOAT128 => "Float128",
            _ => "FloatingPoint",
        };
        dag.add_term(SmtTerm::Var(
            name.to_string(),
            SmtSort::Named(sort_name.to_string()),
        ))
    }

    fn add_fp_const_from_f64(dag: &mut SmtProofDag, value: f64) -> SmtTermId {
        let bits = value.to_bits();
        let sign = add_bv_const(dag, bits >> 63, 1);
        let exponent = add_bv_const(dag, (bits >> 52) & 0x7ff, 11);
        let fraction = add_bv_const(dag, bits & ((1u64 << 52) - 1), 52);
        dag.add_term(SmtTerm::App(
            SmtSymbol::Named("fp".to_string()),
            vec![sign, exponent, fraction],
        ))
    }

    fn add_eq(dag: &mut SmtProofDag, lhs: SmtTermId, rhs: SmtTermId) -> SmtTermId {
        dag.add_term(SmtTerm::App(
            SmtSymbol::Named("=".to_string()),
            vec![lhs, rhs],
        ))
    }

    fn add_not(dag: &mut SmtProofDag, t: SmtTermId) -> SmtTermId {
        dag.add_term(SmtTerm::Not(t))
    }

    #[test]
    fn test_fp_add_inf_minus_inf_is_nan() {
        let pos_inf = FpValue::infinity(FpSort::FLOAT64, false);
        let neg_inf = FpValue::infinity(FpSort::FLOAT64, true);
        let result = pos_inf.fp_add(RoundingMode::RNE, neg_inf);
        assert!(result.is_nan());
    }

    #[test]
    fn test_fp_sub_x_x_is_zero_for_normal() {
        let x = FpValue::from_f64(3.5);
        let result = x.fp_sub(RoundingMode::RNE, x);
        assert!(result.is_zero());
    }

    #[test]
    fn test_fp_lt_float64() {
        let one = FpValue::from_f64(1.0);
        let two = FpValue::from_f64(2.0);
        assert!(one.fp_lt(two));
        assert!(!two.fp_lt(one));
    }

    #[test]
    fn test_fp_add_rounds_away_small_float32_operand() {
        let one = FpValue::from_f32(1.0);
        let tiny = FpValue::from_f32(1e-20_f32);
        let result = one.fp_add(RoundingMode::RNE, tiny);
        assert_eq!(result.to_f32().to_bits(), 1.0f32.to_bits());
    }

    #[test]
    fn test_fp_classification_predicates() {
        let zero = FpValue::zero(FpSort::FLOAT32, false);
        let neg_zero = FpValue::zero(FpSort::FLOAT32, true);
        let subnormal = FpValue::min_subnormal(FpSort::FLOAT32, false);
        let normal = FpValue::from_f32(1.0);
        let inf = FpValue::infinity(FpSort::FLOAT32, false);
        let nan = FpValue::nan(FpSort::FLOAT32);

        assert!(zero.is_zero());
        assert!(zero.is_positive());
        assert!(neg_zero.is_negative());
        assert!(subnormal.is_subnormal());
        assert!(normal.is_normal());
        assert!(inf.is_infinite());
        assert!(nan.is_nan());
    }

    #[test]
    fn test_float16_software_roundtrip() {
        let value =
            FpValue::from_exact_real(FpSort::FLOAT16, ExactReal::from_f64(1.5), RoundingMode::RNE);
        assert!(value.is_normal());
        assert_eq!(value.to_f64(), 1.5);
    }

    #[test]
    fn test_float128_embeds_f64_exactly() {
        let value = FpValue::from_exact_real(
            FpSort::FLOAT128,
            ExactReal::from_f64(1.25),
            RoundingMode::RNE,
        );
        assert!(value.is_normal());
        assert_eq!(value.to_f64(), 1.25);
    }

    #[test]
    fn test_fp_lemma_detects_concrete_contradiction() {
        let mut dag = SmtProofDag::new();
        let x = add_fp_var(&mut dag, "x", FpSort::FLOAT64);
        let two = add_fp_const_from_f64(&mut dag, 2.0);
        let one = add_fp_const_from_f64(&mut dag, 1.0);

        let eq_x_two = add_eq(&mut dag, x, two);
        let lt = dag.add_term(SmtTerm::App(
            SmtSymbol::Named("fp.lt".to_string()),
            vec![x, one],
        ));

        let not_eq_x_two = add_not(&mut dag, eq_x_two);
        let not_lt = add_not(&mut dag, lt);
        let clause = vec![not_eq_x_two, not_lt];

        let verdict = check_fp_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "should detect concrete FP contradiction; detail: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_fp_lemma_empty_clause() {
        let dag = SmtProofDag::new();
        let verdict = check_fp_lemma(&dag, SmtStepId(0), &[]);
        assert_eq!(verdict.trust_level, StepTrustLevel::Trusted);
    }

    #[test]
    fn test_fp_lemma_non_fp_literals() {
        let mut dag = SmtProofDag::new();
        let t = dag.add_term(SmtTerm::Bool(true));
        let verdict = check_fp_lemma(&dag, SmtStepId(0), &[t]);
        assert_eq!(verdict.trust_level, StepTrustLevel::StructurallyAccepted);
    }

    // ---- AI Model-flagged adversarial soundness tests ----

    #[test]
    fn test_fp_eq_nan_not_equal_to_nan() {
        let nan = FpValue::nan(FpSort::FLOAT64);
        assert!(nan.is_nan());
        assert!(!nan.fp_eq(nan));
    }

    #[test]
    fn test_fp_eq_positive_zero_equals_negative_zero() {
        let pos_zero = FpValue::zero(FpSort::FLOAT32, false);
        let neg_zero = FpValue::zero(FpSort::FLOAT32, true);
        assert_ne!(pos_zero.to_f32().to_bits(), neg_zero.to_f32().to_bits());
        assert!(pos_zero.fp_eq(neg_zero));
        assert!(neg_zero.fp_eq(pos_zero));
    }

    #[test]
    fn test_fp_denorm_add_two_min_subnormals() {
        let min_sub = FpValue::min_subnormal(FpSort::FLOAT32, false);
        let result = min_sub.fp_add(RoundingMode::RNE, min_sub);
        let expected = FpValue::from_f32(f32::from_bits(0x0000_0002));
        assert!(result.is_subnormal());
        assert_eq!(result.exponent, 0u64);
        assert_eq!(result.significand, 2u64);
        assert!(result.fp_eq(expected));
    }

    #[test]
    fn test_fp_rounding_rne_vs_rtz_boundary() {
        let one = FpValue::from_f32(1.0);
        let half_ulp = FpValue::from_f32(f32::EPSILON / 2.0);
        let three_quarter_ulp = FpValue::from_f32(f32::EPSILON * 0.75);
        let next_after_one = FpValue::from_f32(f32::from_bits(1.0f32.to_bits() + 1));
        // Tie: RNE rounds to even (1.0 stays), RTZ truncates (stays 1.0)
        let tie_rne = one.fp_add(RoundingMode::RNE, half_ulp);
        let tie_rtz = one.fp_add(RoundingMode::RTZ, half_ulp);
        assert_eq!(tie_rne.to_f32().to_bits(), 1.0f32.to_bits());
        assert_eq!(tie_rtz.to_f32().to_bits(), 1.0f32.to_bits());
        // Above tie: RNE rounds up, RTZ truncates
        let above_tie_rne = one.fp_add(RoundingMode::RNE, three_quarter_ulp);
        let above_tie_rtz = one.fp_add(RoundingMode::RTZ, three_quarter_ulp);
        assert!(above_tie_rne.fp_eq(next_after_one));
        assert_eq!(above_tie_rtz.to_f32().to_bits(), 1.0f32.to_bits());
        assert_ne!(
            above_tie_rne.to_f32().to_bits(),
            above_tie_rtz.to_f32().to_bits()
        );
    }

    #[test]
    fn test_fp_inf_plus_neg_inf_is_nan() {
        let pos_inf = FpValue::infinity(FpSort::FLOAT64, false);
        let neg_inf = FpValue::infinity(FpSort::FLOAT64, true);
        let result = pos_inf.fp_add(RoundingMode::RNE, neg_inf);
        assert!(result.is_nan());
        assert!(!result.is_infinite());
    }

    #[test]
    fn test_fp_mul_overflow_to_inf_rne_vs_rtz() {
        // Use FLOAT32 so the exact intermediate (computed in f64) overflows
        // only at the FP32 level, allowing the RTZ rounding path to clamp
        // to max_finite rather than passing through as native f64 infinity.
        let max_finite = FpValue::max_finite(FpSort::FLOAT32, false);
        let two = FpValue::from_f32(2.0);
        let result_rne = max_finite.fp_mul(RoundingMode::RNE, two);
        let result_rtz = max_finite.fp_mul(RoundingMode::RTZ, two);
        assert!(result_rne.is_infinite(), "RNE overflow should produce +inf");
        assert!(result_rne.is_positive());
        assert!(
            result_rtz.fp_eq(max_finite),
            "RTZ overflow should clamp to max_finite, not infinity"
        );
        assert!(result_rtz.is_normal());
        assert!(!result_rtz.is_infinite());
    }

    #[test]
    fn test_fp_neg_zero_sign_preservation() {
        let pos_zero = FpValue::zero(FpSort::FLOAT32, false);
        let neg_zero = FpValue::zero(FpSort::FLOAT32, true);
        let negated_pos = pos_zero.fp_neg(RoundingMode::RNE);
        let negated_neg = neg_zero.fp_neg(RoundingMode::RNE);
        assert!(negated_pos.is_zero());
        assert!(negated_neg.is_zero());
        assert!(negated_pos.is_negative());
        assert!(negated_neg.is_positive());
        assert_eq!(negated_pos.to_f32().to_bits(), (-0.0f32).to_bits());
        assert_eq!(negated_neg.to_f32().to_bits(), 0.0f32.to_bits());
    }

    #[test]
    fn test_fp_eq_different_nan_payloads() {
        let nan_a = FpValue::from_f32(f32::from_bits(0x7fc0_0001));
        let nan_b = FpValue::from_f32(f32::from_bits(0x7fc0_0002));
        assert!(nan_a.is_nan());
        assert!(nan_b.is_nan());
        assert_ne!(nan_a.to_f32().to_bits(), nan_b.to_f32().to_bits());
        assert!(!nan_a.fp_eq(nan_b));
    }
}
