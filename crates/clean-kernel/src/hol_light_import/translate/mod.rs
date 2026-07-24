// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Internal translation entrypoints.

mod context;
mod proof;
mod proof_helpers;
mod term;

pub(crate) fn translate_proof_object(
    object: &super::HolProofObject,
) -> Result<super::TranslatedProofObject, super::HolLightImportError> {
    proof::translate_proof_object(object)
}
