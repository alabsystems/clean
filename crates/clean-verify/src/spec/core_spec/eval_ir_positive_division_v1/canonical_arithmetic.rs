// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! One disposable ByteV1 owner for the existing canonical arithmetic library.
//! Sources and root contracts remain owned by their original packages. No
//! evaluator, caller-specific theorem, checker option or default is changed.

use super::{
    canonical_division, integer_normalization, laws, output_bounds, preflight,
    register_rows_and_check, shifts, unsigned_compare, with_prerequisite, word_add, word_and_loop,
    word_and_scalar, word_lshr_canonical, word_shl_canonical, word_xor, word_xor_loop,
    word_xor_scalar, AGREEMENT_ROOTS, SHIFT_ROOTS,
};
use crate::spec::{SpecError, Specification};

#[cfg(test)]
mod tests;

// ByteV1 already installs and strictly checks PRODUCT. Keep it among the
// audited roots below, while adding each new declaration exactly once.
fn rows() -> impl Iterator<Item = (&'static str, &'static str)> + Clone {
    with_prerequisite(laws())
        .chain(shifts::LAWS.iter().copied())
        .chain(output_bounds::LAWS.iter().copied())
        .chain(word_add::LAWS.iter().copied())
        .chain(unsigned_compare::LAWS.iter().copied())
        .chain(word_xor::LAWS.iter().copied())
        .chain(word_xor_loop::LAWS.iter().copied())
        .chain(word_xor_scalar::LAWS.iter().copied())
        .chain(word_and_loop::LAWS.iter().copied())
        .chain(word_and_scalar::LAWS.iter().copied())
        .chain(canonical_division::LAWS.iter().copied())
        .chain(word_lshr_canonical::LAWS.iter().copied())
        .chain(word_shl_canonical::LAWS.iter().copied())
}

fn roots() -> impl Iterator<Item = &'static str> {
    AGREEMENT_ROOTS
        .iter()
        .chain(SHIFT_ROOTS.iter())
        .chain(output_bounds::ROOTS.iter())
        .chain(word_add::ROOTS.iter())
        .chain(unsigned_compare::ROOTS.iter())
        .chain(word_xor::ROOTS.iter())
        .chain(word_xor_loop::ROOTS.iter())
        .chain(word_xor_scalar::ROOTS.iter())
        .chain(word_and_loop::ROOTS.iter())
        .chain(word_and_scalar::ROOTS.iter())
        .chain(std::iter::once(&integer_normalization::PRODUCT_ROOT))
        .chain(canonical_division::ROOTS.iter())
        .chain(word_lshr_canonical::ROOTS.iter())
        .chain(word_shl_canonical::ROOTS.iter())
        .copied()
}

fn extend_owned(
    mut owner: Specification,
    declarations: impl Iterator<Item = (&'static str, &'static str)> + Clone,
) -> Result<Specification, SpecError> {
    preflight(&owner, declarations.clone())?;
    let roots = roots().collect::<Vec<_>>();
    register_rows_and_check(&mut owner, declarations, &roots)?;
    Ok(owner)
}

impl Specification {
    /// Compose positive division, full64 shift-by-three/output bounds,
    /// width-indexed canonical Add/output bounds, unsigned comparisons and the
    /// actual bit-basis/loop bridges and input-only typed canonical XOR/AND laws.
    /// The original sources are installed once and every original root is
    /// checked with the shared stored-declaration and complete-closure audit.
    /// An error discards this unreturned owner; no transaction clone is needed.
    pub(crate) fn into_canonical_arithmetic_byte_v1(self) -> Result<Self, SpecError> {
        extend_owned(self, rows())
    }
}
