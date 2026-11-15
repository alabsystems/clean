// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Fixed opt-in proof-package reuse, not program or proof-verdict caching.
//!
//! Only a complete successful checked owner can enter one of four fixed cells.
//! Each call returns an independent owned clone; immutable expression DAGs are shared,
//! but declarations, registration metadata and options remain caller-owned.
//! Default EvalIrVocabulary profiles, evaluator definitions and checker limits
//! are unchanged. An explicit live construction override takes the fresh path
//! before inspecting any package cell, including a previously warm cell.

use super::{build_on_stack, build_owned, construction_override, EvalIrVocabulary, VocabularyCell};
use crate::spec::{SpecError, Specification};

#[cfg(test)]
#[path = "eval_ir_package_reuse_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "eval_ir_output_bounds_reuse_tests.rs"]
mod output_bounds_tests;

#[cfg(test)]
#[path = "eval_ir_canonical_arithmetic_reuse_tests.rs"]
mod canonical_arithmetic_tests;

/// Private fixed profiles selected only by the existing public owned builders.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Package {
    PositiveDivisionByteV1,
    U64ShiftByThreeByteV1,
    U64ShiftByThreeOutputBoundsByteV1,
    CanonicalArithmeticByteV1,
}

static POSITIVE_DIVISION_BYTE_V1: VocabularyCell = VocabularyCell::new();
static U64_SHIFT_BY_THREE_BYTE_V1: VocabularyCell = VocabularyCell::new();
static U64_SHIFT_BY_THREE_OUTPUT_BOUNDS_BYTE_V1: VocabularyCell = VocabularyCell::new();
static CANONICAL_ARITHMETIC_BYTE_V1: VocabularyCell = VocabularyCell::new();

#[cfg(test)]
static POSITIVE_FRESH_ATTEMPTS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
static SHIFT_FRESH_ATTEMPTS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
static OUTPUT_BOUNDS_FRESH_ATTEMPTS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
static CANONICAL_ARITHMETIC_FRESH_ATTEMPTS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);

impl Package {
    fn cell(self) -> &'static VocabularyCell {
        match self {
            Self::PositiveDivisionByteV1 => &POSITIVE_DIVISION_BYTE_V1,
            Self::U64ShiftByThreeByteV1 => &U64_SHIFT_BY_THREE_BYTE_V1,
            Self::U64ShiftByThreeOutputBoundsByteV1 => &U64_SHIFT_BY_THREE_OUTPUT_BOUNDS_BYTE_V1,
            Self::CanonicalArithmeticByteV1 => &CANONICAL_ARITHMETIC_BYTE_V1,
        }
    }

    #[cfg(test)]
    fn attempts(self) -> &'static std::sync::atomic::AtomicUsize {
        match self {
            Self::PositiveDivisionByteV1 => &POSITIVE_FRESH_ATTEMPTS,
            Self::U64ShiftByThreeByteV1 => &SHIFT_FRESH_ATTEMPTS,
            Self::U64ShiftByThreeOutputBoundsByteV1 => &OUTPUT_BOUNDS_FRESH_ATTEMPTS,
            Self::CanonicalArithmeticByteV1 => &CANONICAL_ARITHMETIC_FRESH_ATTEMPTS,
        }
    }
}

/// The same original checked extension path on the maintained construction
/// stack. Keep this path independent of package cells: live construction
/// overrides and the differential tests must replay the original installers.
fn build_fresh(package: Package) -> Result<Specification, SpecError> {
    #[cfg(test)]
    package
        .attempts()
        .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    match package {
        Package::PositiveDivisionByteV1 => build_on_stack(
            "clean-byte-positive-division-v1",
            "positive-division ByteV1",
            || build_owned(EvalIrVocabulary::ByteV1)?.into_positive_division_v1(),
        ),
        Package::U64ShiftByThreeByteV1 => build_on_stack(
            "clean-byte-u64-shift-by-three-v1",
            "full64 shift-by-three ByteV1",
            || {
                build_owned(EvalIrVocabulary::ByteV1)?
                    .into_positive_division_v1()?
                    .into_u64_shift_by_three_v1()
            },
        ),
        Package::U64ShiftByThreeOutputBoundsByteV1 => build_on_stack(
            "clean-byte-u64-shift-by-three-bounds-v1",
            "bounded full64 shift-by-three ByteV1",
            || {
                build_owned(EvalIrVocabulary::ByteV1)?
                    .into_positive_division_v1()?
                    .into_u64_shift_by_three_v1()?
                    .into_u64_shift_by_three_output_bounds_v1()
            },
        ),
        Package::CanonicalArithmeticByteV1 => build_on_stack(
            "clean-byte-canonical-arithmetic-v1",
            "canonical arithmetic ByteV1",
            || build_owned(EvalIrVocabulary::ByteV1)?.into_canonical_arithmetic_byte_v1(),
        ),
    }
}

/// Reuse only a complete immutable parent, then check the child's own extension.
/// These two fixed edges are acyclic: bounds -> shift -> positive -> ByteV1.
/// Each parent request returns an owned clone, so extension cannot mutate it.
fn build_from_checked_parent(package: Package) -> Result<Specification, SpecError> {
    type Extension = fn(Specification) -> Result<Specification, SpecError>;
    let (parent, thread_name, label, extend): (Package, &'static str, &'static str, Extension) =
        match package {
            Package::U64ShiftByThreeByteV1 => (
                Package::PositiveDivisionByteV1,
                "clean-byte-u64-shift-by-three-v1",
                "full64 shift-by-three ByteV1",
                Specification::into_u64_shift_by_three_v1,
            ),
            Package::U64ShiftByThreeOutputBoundsByteV1 => (
                Package::U64ShiftByThreeByteV1,
                "clean-byte-u64-shift-by-three-bounds-v1",
                "bounded full64 shift-by-three ByteV1",
                Specification::into_u64_shift_by_three_output_bounds_v1,
            ),
            Package::PositiveDivisionByteV1 | Package::CanonicalArithmeticByteV1 => {
                return build_fresh(package);
            }
        };
    #[cfg(test)]
    package
        .attempts()
        .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let owned = build_owned_package(parent)?;
    build_on_stack(thread_name, label, move || extend(owned))
}

/// Return no borrowed package or reusable admission capability. Initialization
/// errors leave the existing VocabularyCell empty and retryable; worker panic
/// conversion and poisoned-lock refusal are exactly that cell's policy.
pub(super) fn build_owned_package(package: Package) -> Result<Specification, SpecError> {
    if construction_override() {
        return build_fresh(package);
    }
    package
        .cell()
        .get_or_try_init(|| build_from_checked_parent(package))
        .cloned()
}
