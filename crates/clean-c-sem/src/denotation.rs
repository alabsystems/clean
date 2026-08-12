// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Deterministic local denotation hashes for translation validation.
//!
//! This module is intentionally small and backend-free. It records the local
//! source and target denotation strings for one translation step, hashes them
//! with explicit field delimiters, and validates a claimed hash against the
//! recomputed local hash.
//!
//! # Fail-closed contract
//!
//! [`validate_denotation_hash`] only ever returns `Ok(())` when the claim
//! names the same phase *and* carries exactly the hash recomputed from the
//! locally observed step. Every other outcome rejects:
//!
//! - a claim for a different phase rejects ([`DenotationValidationError::PhaseMismatch`]);
//! - a claim whose digest differs rejects ([`DenotationValidationError::HashMismatch`]);
//! - a step that carries no observable denotation for some field is
//!   *unverifiable*, not vacuously true, and rejects
//!   ([`DenotationValidationError::UnverifiableStep`]).
//!
//! The last case matters for false-control probes: hashing an empty
//! denotation would otherwise let a step that recorded nothing agree with a
//! claim that also recorded nothing, reporting agreement where no evidence
//! was ever compared.
//!
//! # Hash stability
//!
//! The digest is a pure function of [`DENOTATION_HASH_VERSION`] and the five
//! step fields. Fields are length-prefixed before being absorbed, so field
//! boundaries cannot be shifted: `("ab", "c")` and `("a", "bc")` hash apart.
//! The version tag must change whenever the framing or the mixing function
//! changes, so digests recorded by an older build cannot silently validate
//! against a newer one.

use std::fmt;

/// Version tag mixed into every denotation hash.
pub const DENOTATION_HASH_VERSION: &str = "clean-c-sem.translation-denotation.v1";

const FNV_OFFSET_0: u64 = 0xcbf2_9ce4_8422_2325;
const FNV_OFFSET_1: u64 = 0x8422_2325_cbf2_9ce4;
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

const HEX_DIGITS: [u8; 16] = *b"0123456789abcdef";

/// A deterministic 128-bit denotation hash.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DenotationHash([u8; 16]);

impl DenotationHash {
    /// Return the raw hash bytes.
    #[must_use]
    pub fn as_bytes(&self) -> &[u8; 16] {
        &self.0
    }

    /// Return the lowercase hexadecimal encoding.
    ///
    /// The encoding is infallible and always 32 characters wide.
    #[must_use]
    pub fn to_hex(&self) -> String {
        let mut out = String::with_capacity(32);
        for byte in self.0 {
            out.push(char::from(HEX_DIGITS[usize::from(byte >> 4)]));
            out.push(char::from(HEX_DIGITS[usize::from(byte & 0x0f)]));
        }
        out
    }
}

impl fmt::Display for DenotationHash {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_hex())
    }
}

/// One local translation step whose source and target denote the same program.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TranslationDenotationStep<'a> {
    phase: &'a str,
    source_kind: &'a str,
    source_denotation: &'a str,
    target_kind: &'a str,
    target_denotation: &'a str,
}

impl<'a> TranslationDenotationStep<'a> {
    /// Construct a denotation record for one translation step.
    #[must_use]
    pub fn new(
        phase: &'a str,
        source_kind: &'a str,
        source_denotation: &'a str,
        target_kind: &'a str,
        target_denotation: &'a str,
    ) -> Self {
        Self {
            phase,
            source_kind,
            source_denotation,
            target_kind,
            target_denotation,
        }
    }

    /// Translation phase name.
    #[must_use]
    pub fn phase(&self) -> &'a str {
        self.phase
    }

    /// Syntactic category of the source side (for example `"LLVM2"`).
    #[must_use]
    pub fn source_kind(&self) -> &'a str {
        self.source_kind
    }

    /// Denotation recorded for the source side.
    #[must_use]
    pub fn source_denotation(&self) -> &'a str {
        self.source_denotation
    }

    /// Syntactic category of the target side (for example `"CleanExpr"`).
    #[must_use]
    pub fn target_kind(&self) -> &'a str {
        self.target_kind
    }

    /// Denotation recorded for the target side.
    #[must_use]
    pub fn target_denotation(&self) -> &'a str {
        self.target_denotation
    }

    /// Deterministically hash this step.
    #[must_use]
    pub fn hash(&self) -> DenotationHash {
        let mut state = StableDenotationHasher::new();
        state.feed_field(DENOTATION_HASH_VERSION);
        state.feed_field(self.phase);
        state.feed_field(self.source_kind);
        state.feed_field(self.source_denotation);
        state.feed_field(self.target_kind);
        state.feed_field(self.target_denotation);
        state.finish()
    }

    /// Name of the first field that carries no observable content, if any.
    ///
    /// SOUNDNESS: a blank field means the recorder never observed that side of
    /// the step. Hashing it anyway would produce a digest two empty records
    /// agree on, so callers must treat a blank field as *unverifiable* rather
    /// than as evidence of equivalence.
    fn blank_field(&self) -> Option<&'static str> {
        const FIELDS: [&str; 5] = [
            "phase",
            "source_kind",
            "source_denotation",
            "target_kind",
            "target_denotation",
        ];

        let values = [
            self.phase,
            self.source_kind,
            self.source_denotation,
            self.target_kind,
            self.target_denotation,
        ];

        FIELDS
            .iter()
            .zip(values)
            .find(|(_, value)| value.trim().is_empty())
            .map(|(name, _)| *name)
    }
}

/// A denotation hash claim supplied by another validator or translation pass.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DenotationHashClaim<'a> {
    phase: &'a str,
    hash: DenotationHash,
}

impl<'a> DenotationHashClaim<'a> {
    /// Construct a claimed hash for a phase.
    #[must_use]
    pub fn new(phase: &'a str, hash: DenotationHash) -> Self {
        Self { phase, hash }
    }

    /// Claimed phase.
    #[must_use]
    pub fn phase(&self) -> &'a str {
        self.phase
    }

    /// Claimed hash.
    #[must_use]
    pub fn hash(&self) -> DenotationHash {
        self.hash
    }
}

/// Failure from validating a claimed denotation hash.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum DenotationValidationError {
    /// The claim names a different translation phase.
    #[error("denotation phase mismatch: actual {actual}, claimed {claimed}")]
    PhaseMismatch {
        /// Phase of the locally recomputed step.
        actual: String,
        /// Phase named by the claim.
        claimed: String,
    },

    /// The claim names the same phase but carries a different hash.
    #[error("denotation hash mismatch for {phase}: actual {actual}, claimed {claimed}")]
    HashMismatch {
        /// Phase being validated.
        phase: String,
        /// Locally recomputed hash.
        actual: DenotationHash,
        /// Claimed hash.
        claimed: DenotationHash,
    },

    /// The local step carries no observable denotation for some field, so no
    /// claim about it can be checked.
    #[error("denotation step is unverifiable: field {field} is blank")]
    UnverifiableStep {
        /// Name of the blank field.
        field: &'static str,
    },
}

/// Recompute and validate a claimed denotation hash for a translation step.
///
/// Returns `Ok(())` only when the claim names the step's phase and reproduces
/// the locally recomputed hash exactly; see the module docs for the
/// fail-closed contract.
pub fn validate_denotation_hash(
    actual_step: &TranslationDenotationStep<'_>,
    claim: &DenotationHashClaim<'_>,
) -> Result<(), DenotationValidationError> {
    // SOUNDNESS: checked before any comparison, so a step that recorded
    // nothing can never validate against a claim — including a claim that
    // faithfully hashed the same empty record.
    if let Some(field) = actual_step.blank_field() {
        return Err(DenotationValidationError::UnverifiableStep { field });
    }

    if actual_step.phase != claim.phase {
        return Err(DenotationValidationError::PhaseMismatch {
            actual: actual_step.phase.to_string(),
            claimed: claim.phase.to_string(),
        });
    }

    let actual = actual_step.hash();
    if actual != claim.hash {
        return Err(DenotationValidationError::HashMismatch {
            phase: actual_step.phase.to_string(),
            actual,
            claimed: claim.hash,
        });
    }

    Ok(())
}

struct StableDenotationHasher {
    lo: u64,
    hi: u64,
}

impl StableDenotationHasher {
    fn new() -> Self {
        Self {
            lo: FNV_OFFSET_0,
            hi: FNV_OFFSET_1,
        }
    }

    fn feed_field(&mut self, field: &str) {
        self.feed_bytes(&(field.len() as u64).to_le_bytes());
        self.feed_bytes(field.as_bytes());
    }

    fn feed_bytes(&mut self, bytes: &[u8]) {
        for byte in bytes {
            self.lo ^= u64::from(*byte);
            self.lo = self.lo.wrapping_mul(FNV_PRIME);

            self.hi ^= u64::from(byte.reverse_bits());
            self.hi = self.hi.rotate_left(5).wrapping_mul(FNV_PRIME);
        }
    }

    fn finish(self) -> DenotationHash {
        let hi = self.hi ^ self.lo.rotate_left(17);
        let lo = self.lo ^ self.hi.rotate_right(11);
        let mut bytes = [0u8; 16];
        bytes[..8].copy_from_slice(&hi.to_be_bytes());
        bytes[8..].copy_from_slice(&lo.to_be_bytes());
        DenotationHash(bytes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_step() -> TranslationDenotationStep<'static> {
        TranslationDenotationStep::new(
            "llvm2-to-clean",
            "LLVM2",
            "%0 = add i32 1, 2",
            "CleanExpr",
            "CExpr.add (CValue.int 1) (CValue.int 2)",
        )
    }

    #[test]
    fn denotation_hash_is_deterministic() {
        let step = TranslationDenotationStep::new(
            "c-expr-to-clean",
            "CExpr",
            "IntLit(1)",
            "CleanExpr",
            "CValue.int 1",
        );

        assert_eq!(step.hash(), step.hash());
        assert_eq!(step.hash().to_hex().len(), 32);
    }

    #[test]
    fn denotation_validator_rejects_swapped_hash() {
        let actual = TranslationDenotationStep::new(
            "llvm2-to-clean",
            "LLVM2",
            "%0 = add i32 1, 2",
            "CleanExpr",
            "CExpr.add (CValue.int 1) (CValue.int 2)",
        );
        let swapped = TranslationDenotationStep::new(
            "llvm2-to-clean",
            "LLVM2",
            "%0 = sub i32 1, 2",
            "CleanExpr",
            "CExpr.sub (CValue.int 1) (CValue.int 2)",
        );

        let claim = DenotationHashClaim::new(actual.phase(), swapped.hash());
        let err = validate_denotation_hash(&actual, &claim).unwrap_err();

        assert!(matches!(
            err,
            DenotationValidationError::HashMismatch { .. }
        ));
    }

    #[test]
    fn denotation_validator_accepts_matching_claim() {
        let step = sample_step();
        let claim = DenotationHashClaim::new(step.phase(), step.hash());

        assert_eq!(validate_denotation_hash(&step, &claim), Ok(()));
    }

    #[test]
    fn denotation_validator_rejects_phase_mismatch() {
        let step = sample_step();
        // Same digest, different phase name: the claim is about another step.
        let claim = DenotationHashClaim::new("c-expr-to-clean", step.hash());

        let err = validate_denotation_hash(&step, &claim).unwrap_err();
        assert_eq!(
            err,
            DenotationValidationError::PhaseMismatch {
                actual: "llvm2-to-clean".to_string(),
                claimed: "c-expr-to-clean".to_string(),
            }
        );
    }

    #[test]
    fn blank_fields_are_unverifiable_not_vacuously_valid() {
        // A step that recorded no target denotation must reject even against
        // a claim that faithfully hashed that same empty record.
        let blank = TranslationDenotationStep::new(
            "llvm2-to-clean",
            "LLVM2",
            "%0 = add i32 1, 2",
            "CleanExpr",
            "   ",
        );
        let claim = DenotationHashClaim::new(blank.phase(), blank.hash());

        let err = validate_denotation_hash(&blank, &claim).unwrap_err();
        assert_eq!(
            err,
            DenotationValidationError::UnverifiableStep {
                field: "target_denotation"
            }
        );
    }

    #[test]
    fn every_blank_field_is_reported_by_name() {
        let cases: [(TranslationDenotationStep<'_>, &str); 5] = [
            (
                TranslationDenotationStep::new("", "LLVM2", "src", "CleanExpr", "tgt"),
                "phase",
            ),
            (
                TranslationDenotationStep::new("p", "", "src", "CleanExpr", "tgt"),
                "source_kind",
            ),
            (
                TranslationDenotationStep::new("p", "LLVM2", "", "CleanExpr", "tgt"),
                "source_denotation",
            ),
            (
                TranslationDenotationStep::new("p", "LLVM2", "src", "", "tgt"),
                "target_kind",
            ),
            (
                TranslationDenotationStep::new("p", "LLVM2", "src", "CleanExpr", ""),
                "target_denotation",
            ),
        ];

        for (step, field) in cases {
            let claim = DenotationHashClaim::new(step.phase(), step.hash());
            assert_eq!(
                validate_denotation_hash(&step, &claim),
                Err(DenotationValidationError::UnverifiableStep { field }),
                "blank {field} must be unverifiable"
            );
        }
    }

    #[test]
    fn field_boundaries_cannot_be_shifted() {
        // Length prefixes must keep concatenation-equal splits apart,
        // otherwise a rename could be smuggled across a field boundary.
        let left = TranslationDenotationStep::new("phase", "ab", "c", "CleanExpr", "tgt");
        let right = TranslationDenotationStep::new("phase", "a", "bc", "CleanExpr", "tgt");

        assert_ne!(left.hash(), right.hash());

        let claim = DenotationHashClaim::new(left.phase(), right.hash());
        assert!(matches!(
            validate_denotation_hash(&left, &claim),
            Err(DenotationValidationError::HashMismatch { .. })
        ));
    }

    #[test]
    fn each_field_is_hash_relevant() {
        let base = sample_step();
        let variants = [
            TranslationDenotationStep::new(
                "llvm2-to-clean-x",
                base.source_kind(),
                base.source_denotation(),
                base.target_kind(),
                base.target_denotation(),
            ),
            TranslationDenotationStep::new(
                base.phase(),
                "LLVM2x",
                base.source_denotation(),
                base.target_kind(),
                base.target_denotation(),
            ),
            TranslationDenotationStep::new(
                base.phase(),
                base.source_kind(),
                "%0 = add i32 1, 3",
                base.target_kind(),
                base.target_denotation(),
            ),
            TranslationDenotationStep::new(
                base.phase(),
                base.source_kind(),
                base.source_denotation(),
                "CleanExprX",
                base.target_denotation(),
            ),
            TranslationDenotationStep::new(
                base.phase(),
                base.source_kind(),
                base.source_denotation(),
                base.target_kind(),
                "CExpr.add (CValue.int 1) (CValue.int 3)",
            ),
        ];

        for variant in variants {
            assert_ne!(
                base.hash(),
                variant.hash(),
                "perturbing a field must change the digest: {variant:?}"
            );
        }
    }

    #[test]
    fn swapping_source_and_target_changes_the_hash() {
        let forward = TranslationDenotationStep::new("p", "A", "a-den", "B", "b-den");
        let backward = TranslationDenotationStep::new("p", "B", "b-den", "A", "a-den");

        assert_ne!(forward.hash(), backward.hash());
    }

    #[test]
    fn hex_encoding_round_trips_the_raw_bytes() {
        let step = sample_step();
        let hash = step.hash();
        let hex = hash.to_hex();

        assert_eq!(hex.len(), 32);
        assert!(hex
            .chars()
            .all(|c| c.is_ascii_hexdigit() && !c.is_uppercase()));
        assert_eq!(hex, hash.to_string());

        let expected: String = hash
            .as_bytes()
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect();
        assert_eq!(hex, expected);
    }

    #[test]
    fn version_tag_is_pinned() {
        // Digests recorded by an older build must not validate against a
        // reframed hasher; the tag is the only thing that separates them.
        assert_eq!(
            DENOTATION_HASH_VERSION,
            "clean-c-sem.translation-denotation.v1"
        );

        let step = sample_step();
        assert_eq!(step.hash().to_hex(), sample_step().hash().to_hex());
    }

    #[test]
    fn claim_accessors_report_what_was_claimed() {
        let step = sample_step();
        let claim = DenotationHashClaim::new("llvm2-to-clean", step.hash());

        assert_eq!(claim.phase(), "llvm2-to-clean");
        assert_eq!(claim.hash(), step.hash());
    }

    #[test]
    fn errors_render_with_context() {
        let step = sample_step();
        let claim = DenotationHashClaim::new("other-phase", step.hash());
        let rendered = validate_denotation_hash(&step, &claim)
            .unwrap_err()
            .to_string();
        assert!(
            rendered.contains("llvm2-to-clean") && rendered.contains("other-phase"),
            "phase mismatch must name both phases: {rendered}"
        );

        let mismatch = DenotationValidationError::HashMismatch {
            phase: "p".to_string(),
            actual: step.hash(),
            claimed: sample_step().hash(),
        };
        assert!(mismatch.to_string().contains(&step.hash().to_hex()));
    }
}
