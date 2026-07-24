// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Universal Proof IR (UPIR) for cross-system proof import.

mod lean;
mod syntax;
#[cfg(test)]
mod tests;
mod validate;

pub use lean::LeanTranslationError;
pub use syntax::{
    BinderStyle, MatchStyle, SourceLoc, SourceSystem, UpirBinder, UpirExpr, UpirForeignExpr,
    UpirLevel, UpirLiteral, UpirMatchArm, UpirName, UpirPattern, UpirProjection, UpirProof,
    UpirSort,
};
pub use validate::UpirValidationError;
