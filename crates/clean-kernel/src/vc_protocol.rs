// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Verification condition input/output protocol types.

use crate::expr::Expr;
use serde::{Deserialize, Serialize};

/// A single verification condition hypothesis.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct VcHypothesis {
    /// Hypothesis binder name.
    pub name: String,
    /// Hypothesis type.
    pub type_: Expr,
}

/// A single verification condition obligation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct VcObligation {
    /// Stable obligation name.
    pub name: String,
    /// Goal type to prove.
    pub goal_type: Expr,
    /// Local hypotheses available for the obligation.
    pub hypotheses: Vec<VcHypothesis>,
    /// Source file path, when available.
    pub source_file: Option<String>,
    /// 1-based source line, when available.
    pub source_line: Option<u32>,
}

/// Result of attempting to discharge a verification condition.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum VcResult {
    /// Obligation was proved, returning the proof term.
    Proved(Expr),
    /// Obligation was refuted with an explanation.
    Refuted(String),
    /// Backend timed out before producing a result.
    Timeout,
    /// Backend cannot handle the obligation.
    Unsupported(String),
}

/// A batch of verification conditions.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct VcBatch {
    /// Obligations to send to the backend.
    pub obligations: Vec<VcObligation>,
}

/// Batch verification results keyed by obligation name.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct VcBatchResult {
    /// Results for each obligation.
    pub results: Vec<(String, VcResult)>,
}
