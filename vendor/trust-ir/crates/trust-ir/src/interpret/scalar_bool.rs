// Copyright 2026 Andrew Yates. Apache-2.0.
//! Scalar operations shared by the actual interpreter's Boolean opcode paths.

/// The runtime conjunction used for both `And` and `BAnd` at Boolean type.
/// This is implementation code; its source/body/compiler correspondence must
/// be established by the original-model proof path, not asserted here.
pub(crate) fn conjunction(lhs: bool, rhs: bool) -> bool {
    lhs & rhs
}
