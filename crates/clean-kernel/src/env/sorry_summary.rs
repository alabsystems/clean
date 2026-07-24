// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Declaration trust and sorry provenance summaries for registered declarations.

use crate::expr::Expr;
use serde::{Deserialize, Serialize};

use super::types::ConstantInfo;

/// Summary of trust-bearing terms within a declaration.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct DeclarationTrustSummary {
    /// Whether the declaration contains an explicit/non-synthetic sorry.
    pub has_explicit_sorry: bool,
    /// Whether the declaration contains a synthetic sorry.
    pub has_synthetic_sorry: bool,
    /// Number of embedded `trustedArith` references.
    pub trusted_arith_count: usize,
    /// Number of embedded `trustedAy` references.
    pub trusted_ay_count: usize,
}

impl DeclarationTrustSummary {
    /// Whether the declaration contains any sorry-bearing term.
    pub fn has_sorry(&self) -> bool {
        self.has_explicit_sorry || self.has_synthetic_sorry
    }

    /// Total embedded trusted-axiom references in the declaration.
    pub fn trusted_axiom_count(&self) -> usize {
        self.trusted_arith_count + self.trusted_ay_count
    }

    /// Whether the declaration is free of sorry and trusted-axiom debt.
    pub fn is_fully_verified(&self) -> bool {
        !self.has_sorry() && self.trusted_axiom_count() == 0
    }

    /// Merge another summary into `self`.
    pub fn merge(&mut self, other: Self) {
        self.has_explicit_sorry |= other.has_explicit_sorry;
        self.has_synthetic_sorry |= other.has_synthetic_sorry;
        self.trusted_arith_count += other.trusted_arith_count;
        self.trusted_ay_count += other.trusted_ay_count;
    }

    /// Compute declaration trust data for a single expression.
    pub fn from_expr(expr: &Expr) -> Self {
        let (has_explicit_sorry, has_synthetic_sorry, trusted_arith_count, trusted_ay_count) =
            expr.trust_scan();
        Self {
            has_explicit_sorry,
            has_synthetic_sorry,
            trusted_arith_count,
            trusted_ay_count,
        }
    }

    /// Project the broader summary onto the legacy sorry-only surface.
    pub fn sorry_summary(&self) -> SorrySummary {
        SorrySummary {
            has_sorry: self.has_sorry(),
            has_explicit_sorry: self.has_explicit_sorry,
            has_synthetic_sorry: self.has_synthetic_sorry,
        }
    }
}

/// Summary of sorry usage within a declaration.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SorrySummary {
    /// Whether the declaration contains any sorry-bearing term.
    pub has_sorry: bool,
    /// Whether the declaration contains an explicit/non-synthetic sorry.
    pub has_explicit_sorry: bool,
    /// Whether the declaration contains a synthetic sorry.
    pub has_synthetic_sorry: bool,
}

impl SorrySummary {
    /// Merge another summary into `self`.
    pub fn merge(&mut self, other: Self) {
        self.has_sorry |= other.has_sorry;
        self.has_explicit_sorry |= other.has_explicit_sorry;
        self.has_synthetic_sorry |= other.has_synthetic_sorry;
    }

    /// Compute sorry usage for a single expression.
    ///
    /// Uses the broader trust scan and projects it onto the compatibility
    /// sorry-only surface.
    pub fn from_expr(expr: &Expr) -> Self {
        DeclarationTrustSummary::from_expr(expr).sorry_summary()
    }
}

impl ConstantInfo {
    /// Compute the declaration's trust summary from its stored type and body.
    pub fn trust_summary(&self) -> DeclarationTrustSummary {
        let mut summary = DeclarationTrustSummary::from_expr(&self.type_);
        if let Some(value) = &self.value {
            summary.merge(DeclarationTrustSummary::from_expr(value));
        }
        summary
    }

    /// Compute the declaration's sorry provenance summary as a compatibility projection.
    pub fn sorry_summary(&self) -> SorrySummary {
        self.trust_summary().sorry_summary()
    }
}
