// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The kernel-attestation bridge: the ONLY producer of a `KernelVerified`
//! attestation.
//!
//! [`attest`] is the single seam between the trust core
//! (`graduate::recheck::recheck_and_classify`) and the signer. It:
//!
//! 1. computes the de Bruijn statement/proof digests
//!    (`graduate::record::expr_canonical_digest`) from the declaration BEFORE
//!    the decl is consumed by the kernel re-check;
//! 2. runs `recheck_and_classify` — the one honest path to a kernel verdict —
//!    in the caller's fresh environment;
//! 3. emits a [`KernelAttestation`] carrying exactly the facts the kernel
//!    produced.
//!
//! There is no public constructor that sets `foundational = true` without a
//! verdict. The signer takes a [`KernelAttestation`]; it therefore CANNOT mint
//! a `KernelVerified` for a declaration the kernel did not re-verify, nor for a
//! non-foundational closure. The signature attests provenance, never truth —
//! the digests keep the claim independently re-verifiable by any consumer.

use clean_kernel::{Declaration, Environment};

use crate::graduate::recheck::{recheck_and_classify, RecheckError};
use crate::graduate::record::expr_canonical_digest;

/// Facts a fresh kernel produced for one declaration — the ONLY input a signer
/// is permitted to attest. Constructed by [`attest`] from a `RecheckVerdict`.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct KernelAttestation {
    /// Declaration name.
    pub name: String,
    /// `blake3:<hex>` de Bruijn digest of the declaration TYPE (the claim).
    pub statement_digest: String,
    /// `blake3:<hex>` de Bruijn digest of the declaration VALUE (the proof).
    pub proof_digest: String,
    /// `true` iff the kernel re-checked the value AND the transitive axiom
    /// closure is foundational-only (`RecheckVerdict::is_foundational`).
    pub foundational: bool,
    /// Transitive non-foundational axioms, sorted. Empty iff `foundational`.
    pub domain_axioms: Vec<String>,
    /// `env!("CARGO_PKG_VERSION")` of the attesting Clean.
    pub clean_version: String,
    /// The attesting Clean commit (caller-supplied; recorded, not trusted).
    pub clean_commit: String,
}

/// Why an attestation could not be produced. Fail-closed: a digest failure or a
/// kernel rejection is an error, never a silent unattested pass.
#[derive(Clone, Debug, thiserror::Error)]
#[non_exhaustive]
pub enum AttestError {
    /// The de Bruijn digest of the type or value could not be computed.
    #[error("canonical digest failed: {0}")]
    Digest(String),

    /// The kernel re-check rejected the declaration (the trust core's verdict).
    #[error(transparent)]
    Recheck(#[from] RecheckError),

    /// The declaration kind cannot be attested (only value-bearing
    /// declarations — theorems and definitions — have a proof digest).
    #[error("cannot attest a declaration without a proof value: {0}")]
    NoValue(String),
}

/// Re-verify `decl` in `env` and produce a [`KernelAttestation`]. The
/// declaration is consumed by the kernel re-check (it is registered in `env` on
/// success, matching `recheck_and_classify`'s contract).
///
/// `foundational` in the result is exactly `RecheckVerdict::is_foundational()`
/// — the bridge does NOT re-derive or relax it.
pub fn attest(
    env: &mut Environment,
    decl: Declaration,
    clean_commit: impl Into<String>,
) -> Result<KernelAttestation, AttestError> {
    let name = decl_name(&decl);
    let (type_, value) = decl_type_and_value(&decl)?;
    let statement_digest =
        expr_canonical_digest(type_).map_err(|e| AttestError::Digest(e.to_string()))?;
    let proof_digest =
        expr_canonical_digest(value).map_err(|e| AttestError::Digest(e.to_string()))?;

    // The one honest path to a kernel verdict. Consumes `decl`.
    let verdict = recheck_and_classify(env, decl)?;

    Ok(KernelAttestation {
        name,
        statement_digest,
        proof_digest,
        foundational: verdict.is_foundational(),
        domain_axioms: verdict.domain_axioms,
        clean_version: env!("CARGO_PKG_VERSION").to_string(),
        clean_commit: clean_commit.into(),
    })
}

/// The declaration's name as a `String`.
fn decl_name(decl: &Declaration) -> String {
    match decl {
        Declaration::Axiom { name, .. }
        | Declaration::Definition { name, .. }
        | Declaration::Theorem { name, .. }
        | Declaration::Opaque { name, .. } => name.to_string(),
    }
}

/// Borrow the type and value of a value-bearing declaration (theorem /
/// definition / opaque). Axioms have no value and cannot be attested.
fn decl_type_and_value(
    decl: &Declaration,
) -> Result<(&clean_kernel::Expr, &clean_kernel::Expr), AttestError> {
    match decl {
        Declaration::Theorem { type_, value, .. }
        | Declaration::Definition { type_, value, .. }
        | Declaration::Opaque { type_, value, .. } => Ok((type_, value)),
        Declaration::Axiom { name, .. } => Err(AttestError::NoValue(name.to_string())),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{BinderInfo, Expr, Name};

    /// `fun (p : Prop) (h : p) => h : ∀ (p : Prop), p → p` — foundational-only.
    fn imp_self() -> Declaration {
        Declaration::Theorem {
            name: Name::from_string("Attest.imp_self"),
            level_params: vec![],
            type_: Expr::pi(
                BinderInfo::Default,
                Expr::prop(),
                Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
            ),
            value: Expr::lam(
                BinderInfo::Default,
                Expr::prop(),
                Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
            ),
        }
    }

    #[test]
    fn test_attest_foundational_theorem_is_foundational() {
        let mut env = Environment::new();
        let att = attest(&mut env, imp_self(), "test-commit").expect("foundational attests");
        assert!(att.foundational);
        assert!(att.domain_axioms.is_empty());
        assert!(att.statement_digest.starts_with("blake3:"));
        assert!(att.proof_digest.starts_with("blake3:"));
        assert_eq!(att.name, "Attest.imp_self");
    }

    #[test]
    fn test_attest_axiom_citing_theorem_is_not_foundational() {
        let mut env = Environment::new();
        let axiom_type = Expr::pi(
            BinderInfo::Default,
            Expr::prop(),
            Expr::pi(
                BinderInfo::Default,
                Expr::prop(),
                Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(2)),
            ),
        );
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("Attest.bad_axiom"),
            level_params: vec![],
            type_: axiom_type.clone(),
        })
        .expect("axiom kernel-checks");
        let dependent = Declaration::Theorem {
            name: Name::from_string("Attest.bad_dependent"),
            level_params: vec![],
            type_: axiom_type,
            value: Expr::const_str("Attest.bad_axiom"),
        };
        let att = attest(&mut env, dependent, "test-commit").expect("attests as non-foundational");
        assert!(!att.foundational);
        assert_eq!(att.domain_axioms, vec!["Attest.bad_axiom".to_string()]);
    }

    #[test]
    fn test_attest_kernel_rejection_fails_closed() {
        let mut env = Environment::new();
        attest(&mut env, imp_self(), "c").expect("first attest");
        // Duplicate name → kernel rejection → attest error (never a silent pass).
        let err = attest(&mut env, imp_self(), "c").expect_err("duplicate must fail closed");
        assert!(matches!(err, AttestError::Recheck(_)));
    }

    #[test]
    fn test_attest_axiom_has_no_value() {
        let mut env = Environment::new();
        let err = attest(
            &mut env,
            Declaration::Axiom {
                name: Name::from_string("Attest.an_axiom"),
                level_params: vec![],
                type_: Expr::pi(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
            },
            "c",
        )
        .expect_err("an axiom has no proof value to attest");
        assert!(matches!(err, AttestError::NoValue(_)));
    }
}
