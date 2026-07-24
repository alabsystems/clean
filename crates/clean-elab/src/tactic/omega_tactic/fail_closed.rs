// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{TacticError, TacticResult};

pub(super) fn certified_arithmetic_contradiction_without_kernel_proof(
    reason: impl Into<String>,
) -> TacticResult {
    Err(TacticError::ArithmeticFailed {
        tactic: "mathverse".into(),
        reason: format!(
            "certified arithmetic contradiction has no kernel proof ({})",
            reason.into()
        ),
    })
}

#[cfg(test)]
pub(crate) fn test_only_certified_arithmetic_contradiction_without_kernel_proof(
    reason: &str,
) -> TacticResult {
    certified_arithmetic_contradiction_without_kernel_proof(reason)
}
