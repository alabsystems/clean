// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! JSON parser for HOL Light proof objects.

use super::{HolLightImportError, HolProofObject};

/// Parse one HOL Light proof object from JSON.
pub fn parse_proof_object(input: &str) -> Result<HolProofObject, HolLightImportError> {
    Ok(serde_json::from_str(input)?)
}
