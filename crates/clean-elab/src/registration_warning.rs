// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Registration-time trust warnings for elaborated declarations.
//!
//! This module provides the report types and selection policy for surfacing
//! declaration-level trust provenance at registration time. The selection
//! policy preserves Lean 4's `warnIfUsesSorry` priority for explicit vs
//! synthetic `sorry`, and extends it to `trustedArith` / `trustedAy`.
//!
//! The kernel remains the source of truth for declaration trust provenance via
//! `ConstantInfo::trust_summary()`. This module only defines the reporting
//! boundary above the kernel.

use clean_kernel::env::DeclarationTrustSummary;
use clean_kernel::Name;

use crate::infer::{ElabResult, HoleContext};

/// The primary trust-bearing term found in a registered declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RegistrationWarningKind {
    /// The declaration contains an explicit `sorry` (user-written).
    ExplicitSorry,
    /// The declaration contains a synthetic/internal sorry (recovery-inserted).
    SyntheticSorry,
    /// The declaration contains `trustedArith` debt but no sorry.
    TrustedArith,
    /// The declaration contains `trustedAy` debt but no sorry or `trustedArith`.
    TrustedAy,
}

/// A warning produced after registering a declaration that carries trust debt.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegistrationWarning {
    /// The name of the declaration that triggered the warning.
    pub decl_name: Name,
    /// Primary classification of the declaration's trust debt.
    pub kind: RegistrationWarningKind,
    /// Full declaration-level trust summary for richer consumers.
    pub summary: DeclarationTrustSummary,
}

/// The result of `elaborate_decl_and_register_with_warning`, bundling the
/// elaboration result with an optional registration trust warning.
pub struct RegisteredElabResult {
    /// The underlying elaboration result.
    pub result: ElabResult,
    /// A registration warning, if the declaration carries trust debt.
    pub warning: Option<RegistrationWarning>,
    /// Expected-type contexts for the user-written holes (`_`) the declaration
    /// contained, snapshotted after elaboration.
    ///
    /// Empty for declarations with no holes. IDE-surface only: consumed by the
    /// LSP `$/lean/plainTermGoal` request to report the hole-local expected type
    /// rather than the whole declaration's type.
    pub hole_contexts: Vec<HoleContext>,
}

impl RegistrationWarning {
    /// Construct a warning from a declaration name and its trust summary.
    ///
    /// Selection policy:
    /// 1. Synthetic sorry wins over explicit and trusted debt
    /// 2. Explicit sorry wins over trusted debt when synthetic is absent
    /// 3. `trustedArith` wins over `trustedAy` when no sorry is present
    /// 4. Returns `None` when the declaration is fully verified
    pub(crate) fn from_summary(name: Name, summary: DeclarationTrustSummary) -> Option<Self> {
        if summary.is_fully_verified() {
            return None;
        }
        let kind = if summary.has_synthetic_sorry {
            RegistrationWarningKind::SyntheticSorry
        } else if summary.has_explicit_sorry {
            RegistrationWarningKind::ExplicitSorry
        } else if summary.trusted_arith_count > 0 {
            RegistrationWarningKind::TrustedArith
        } else {
            RegistrationWarningKind::TrustedAy
        };
        Some(Self {
            decl_name: name,
            kind,
            summary,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_from_summary_clean_returns_none() {
        let summary = DeclarationTrustSummary {
            has_explicit_sorry: false,
            has_synthetic_sorry: false,
            trusted_arith_count: 0,
            trusted_ay_count: 0,
        };
        assert!(RegistrationWarning::from_summary(Name::from_string("x"), summary).is_none());
    }

    #[test]
    fn test_from_summary_explicit_only() {
        let summary = DeclarationTrustSummary {
            has_explicit_sorry: true,
            has_synthetic_sorry: false,
            trusted_arith_count: 0,
            trusted_ay_count: 0,
        };
        let w = RegistrationWarning::from_summary(Name::from_string("t"), summary)
            .expect("should produce warning");
        assert_eq!(w.kind, RegistrationWarningKind::ExplicitSorry);
        assert_eq!(w.decl_name.to_string(), "t");
        assert_eq!(w.summary, summary);
    }

    #[test]
    fn test_from_summary_synthetic_only() {
        let summary = DeclarationTrustSummary {
            has_explicit_sorry: false,
            has_synthetic_sorry: true,
            trusted_arith_count: 0,
            trusted_ay_count: 0,
        };
        let w = RegistrationWarning::from_summary(Name::from_string("s"), summary)
            .expect("should produce warning");
        assert_eq!(w.kind, RegistrationWarningKind::SyntheticSorry);
    }

    #[test]
    fn test_from_summary_synthetic_wins_over_other_debt() {
        let summary = DeclarationTrustSummary {
            has_explicit_sorry: true,
            has_synthetic_sorry: true,
            trusted_arith_count: 2,
            trusted_ay_count: 3,
        };
        let w = RegistrationWarning::from_summary(Name::from_string("both"), summary)
            .expect("should produce warning");
        assert_eq!(
            w.kind,
            RegistrationWarningKind::SyntheticSorry,
            "synthetic sorry should win over all other trust debt"
        );
    }

    #[test]
    fn test_from_summary_trusted_arith_wins_over_trusted_ay() {
        let summary = DeclarationTrustSummary {
            has_explicit_sorry: false,
            has_synthetic_sorry: false,
            trusted_arith_count: 1,
            trusted_ay_count: 4,
        };
        let w = RegistrationWarning::from_summary(Name::from_string("arith"), summary)
            .expect("should produce warning");
        assert_eq!(w.kind, RegistrationWarningKind::TrustedArith);
    }

    #[test]
    fn test_from_summary_trusted_ay_only() {
        let summary = DeclarationTrustSummary {
            has_explicit_sorry: false,
            has_synthetic_sorry: false,
            trusted_arith_count: 0,
            trusted_ay_count: 1,
        };
        let w = RegistrationWarning::from_summary(Name::from_string("ay"), summary)
            .expect("should produce warning");
        assert_eq!(w.kind, RegistrationWarningKind::TrustedAy);
    }
}
