// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The two-valued trusted verdict types (design §4.3 "no fail-open").
//!
//! There is deliberately **no** `Unknown` / `Trusted` / `Unverified-but-assume`
//! inhabitant. Resource exhaustion is `Rejected`, never a third state. The
//! success inhabitant carries a [`ConstId`] of a real, kernel-checked theorem,
//! so a consumer that wants a theorem must obtain a `ConstId` — none can be
//! fabricated from a `Rejected`.

use crate::name::Name;

/// A handle to a declaration in the environment whose statement the kernel has
/// checked. The success inhabitants of [`Verdict`] / [`CertVerdict`] carry one
/// of these; it cannot be constructed from a rejection.
///
/// At M0 this is a thin newtype over a [`Name`] (the environment surface is a
/// placeholder; the full env is later phases). Field-private so it can only be
/// minted by the kernel.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ConstId(Name);

impl ConstId {
    /// Mint a `ConstId`. `pub(crate)` so only the kernel can produce one — a
    /// `ConstId` therefore witnesses that the kernel vouched for the name.
    #[must_use]
    pub(crate) fn new(name: Name) -> Self {
        ConstId(name)
    }

    /// The underlying name.
    #[must_use]
    pub fn name(&self) -> &Name {
        &self.0
    }
}

/// Why the kernel rejected. Carries no data a consumer could read as a proof.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum Reason {
    /// The submitted term failed validation (ill-formed boundary IR).
    #[error("validation failed: {0}")]
    Validation(String),
    /// A soundness-relevant check could not complete within the pinned budget.
    /// Per design §4.3 / §5.1, exhaustion is *reject*, never a third state.
    #[error("out of budget (deterministic, genesis-pinned)")]
    OutOfBudget,
    /// A type-checking / def-eq decision came out negative.
    #[error("not definitionally / not type-correct: {0}")]
    NotChecked(String),
    /// A certificate's pinned problem hash, multipliers, or shape failed the
    /// fail-closed cert boundary (design §6).
    #[error("certificate rejected: {0}")]
    Cert(String),
}

/// The trusted check verdict. **Two-valued.**
#[derive(Clone, Debug, PartialEq, Eq)]
#[must_use = "a Verdict must be inspected; ignoring it discards the soundness decision"]
pub enum Verdict {
    /// The judgment holds; the kernel checked it.
    Checked,
    /// The judgment does not hold, or could not be established within budget.
    Rejected(Reason),
}

/// The trusted certificate verdict. **Two-valued.** The success inhabitant
/// names the kernel-checked theorem that was refuted/established (design §6.1).
#[derive(Clone, Debug, PartialEq, Eq)]
#[must_use = "a CertVerdict must be inspected; ignoring it discards the soundness decision"]
pub enum CertVerdict {
    /// The certificate's claim was discharged by a real, kernel-checked theorem.
    Refuted {
        /// The theorem the kernel checked.
        theorem: ConstId,
    },
    /// The certificate was rejected (bad shape, failed pin, out of budget, ...).
    Rejected(Reason),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_constid_carries_the_kernel_vouched_name() {
        // `ConstId::new` is pub(crate): only the kernel mints these, so a
        // ConstId witnesses a kernel decision. A consumer outside the crate can
        // read the name but cannot fabricate one (compile-time guarantee).
        let id = ConstId::new(crate::name::Name::from_dotted("And.intro"));
        assert_eq!(id.name(), &crate::name::Name::from_dotted("And.intro"));
    }

    #[test]
    fn test_verdict_is_two_valued() {
        // Exhaustive match: exactly two inhabitants, no Unknown/Trusted.
        let checked = Verdict::Checked;
        let rejected = Verdict::Rejected(Reason::OutOfBudget);
        for v in [checked, rejected] {
            match v {
                Verdict::Checked | Verdict::Rejected(_) => {}
            }
        }
    }

    #[test]
    fn test_cert_verdict_success_names_a_theorem() {
        let id = ConstId::new(crate::name::Name::from_dotted("T"));
        let v = CertVerdict::Refuted {
            theorem: id.clone(),
        };
        match v {
            CertVerdict::Refuted { theorem } => assert_eq!(theorem, id),
            CertVerdict::Rejected(_) => panic!("expected Refuted"),
        }
    }

    #[test]
    fn test_out_of_budget_is_rejection_not_a_third_state() {
        // Design §4.3/§5.1: exhaustion is Rejected, never a third verdict.
        assert!(matches!(
            Verdict::Rejected(Reason::OutOfBudget),
            Verdict::Rejected(Reason::OutOfBudget)
        ));
    }
}
