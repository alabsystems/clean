// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Typed errors for semantic-AST to VIR lowering.

use thiserror::Error;

#[derive(Debug, Error)]
#[non_exhaustive]
pub enum VirLoweringError {
    #[error("unsupported {context}: {detail}")]
    Unsupported {
        context: &'static str,
        detail: String,
    },

    #[error("unknown local `{name}`")]
    UnknownLocal { name: String },

    #[error("missing type for {context}")]
    MissingType { context: String },
}
