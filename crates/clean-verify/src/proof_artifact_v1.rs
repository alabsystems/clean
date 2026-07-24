// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `proof-artifact-v1` schema and exact-rational parser.
//!
//! This module is deliberately only a schema/parser boundary. Replay of
//! gamma-crown, ay, or other certificate payloads belongs in their existing
//! checkers after the envelope has been parsed and validated here.

use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::fmt;

use num_bigint::{BigInt, Sign};
use serde::de::{self, IgnoredAny, MapAccess, SeqAccess, Visitor};
use serde::ser::SerializeStruct;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use serde_json::Value;
use thiserror::Error;

/// Canonical schema version for proof artifacts parsed by this module.
pub const PROOF_ARTIFACT_V1_VERSION: &str = "proof-artifact-v1";

const SUPPORTED_VERSION_ALIASES: &[&str] = &[PROOF_ARTIFACT_V1_VERSION, "1", "1.0"];

/// A portable proof-artifact envelope with exact verifier constants.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProofArtifactV1 {
    /// Schema version. Canonical spelling is [`PROOF_ARTIFACT_V1_VERSION`].
    pub version: String,
    /// Repository and commit that produced the artifact.
    pub producer: Producer,
    /// Source system that generated the certificate, e.g. `gamma-crown` or `ay`.
    #[serde(alias = "system")]
    pub source_system: String,
    /// Hash of the verification problem.
    pub problem_hash: String,
    /// Hash of the model or benchmark instance.
    pub model_hash: String,
    /// Hash of the proof/certificate payload.
    pub proof_hash: String,
    /// Optional certification evidence. Absence means a legacy artifact that
    /// makes no kernel-certification claim.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub certification: Option<CertificationEvidence>,
    /// Producer-defined artifact kind, such as `gamma_crown_entailment`.
    pub artifact_kind: String,
    /// Verifier constants, encoded as exact rationals rather than JSON numbers.
    #[serde(alias = "constants")]
    pub verifier_constants: Vec<VerifierConstant>,
    /// Certificate payload envelope.
    #[serde(alias = "certificate_payload")]
    pub certificate: CertificatePayloadEnvelope,
    /// Optional metadata that is not trusted by the parser.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub metadata: BTreeMap<String, String>,
}

impl ProofArtifactV1 {
    /// Parse and validate an artifact from JSON.
    pub fn from_json(json: &str) -> Result<Self, ProofArtifactV1Error> {
        let artifact: Self = serde_json::from_str(json).map_err(ProofArtifactV1Error::from)?;
        artifact.validate()?;
        Ok(artifact)
    }

    /// Serialize the artifact as compact JSON after validating it.
    pub fn to_json(&self) -> Result<String, ProofArtifactV1Error> {
        self.validate()?;
        serde_json::to_string(self).map_err(ProofArtifactV1Error::from)
    }

    /// Serialize the artifact as pretty JSON after validating it.
    pub fn to_json_pretty(&self) -> Result<String, ProofArtifactV1Error> {
        self.validate()?;
        serde_json::to_string_pretty(self).map_err(ProofArtifactV1Error::from)
    }

    /// Validate semantic invariants not fully expressible in serde.
    pub fn validate(&self) -> Result<(), ProofArtifactV1Error> {
        require_non_empty("version", &self.version)?;
        if !SUPPORTED_VERSION_ALIASES.contains(&self.version.as_str()) {
            return Err(ProofArtifactV1Error::UnsupportedVersion {
                found: self.version.clone(),
                expected: PROOF_ARTIFACT_V1_VERSION,
            });
        }

        self.producer.validate()?;
        require_non_empty("source_system", &self.source_system)?;
        require_non_empty("problem_hash", &self.problem_hash)?;
        require_non_empty("model_hash", &self.model_hash)?;
        require_non_empty("proof_hash", &self.proof_hash)?;
        if let Some(certification) = &self.certification {
            certification.validate()?;
        }
        require_non_empty("artifact_kind", &self.artifact_kind)?;
        self.certificate.validate()?;

        for constant in &self.verifier_constants {
            constant.validate()?;
        }

        Ok(())
    }
}

/// Certification evidence associated with the proof payload.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CertificationEvidence {
    /// Whether this artifact is only replayable by an external checker or has
    /// been certified by a clean kernel checker.
    pub evidence_kind: CertificationEvidenceKind,
    /// Kernel theorem name for kernel-certified artifacts.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub kernel_theorem: Option<String>,
    /// Hash of the kernel proof term for kernel-certified artifacts.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub proof_term_hash: Option<String>,
    /// Checker identity/version that certified the kernel theorem.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub checker: Option<String>,
}

impl CertificationEvidence {
    fn validate(&self) -> Result<(), ProofArtifactV1Error> {
        validate_optional_non_empty("certification.kernel_theorem", &self.kernel_theorem)?;
        validate_optional_non_empty("certification.proof_term_hash", &self.proof_term_hash)?;
        validate_optional_non_empty("certification.checker", &self.checker)?;

        if self.evidence_kind == CertificationEvidenceKind::KernelCertified {
            require_present_non_empty("certification.kernel_theorem", &self.kernel_theorem)?;
            require_present_non_empty("certification.proof_term_hash", &self.proof_term_hash)?;
            require_present_non_empty("certification.checker", &self.checker)?;
        }

        Ok(())
    }
}

/// Certification strength claimed by the artifact metadata.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CertificationEvidenceKind {
    /// Payload can be replayed by a checker, but no clean kernel proof is
    /// claimed by this metadata.
    ReplayOnly,
    /// Payload has corresponding clean kernel certification evidence.
    KernelCertified,
}

/// Producer provenance for a proof artifact.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Producer {
    /// Repository name or URL.
    pub repo: String,
    /// Source commit that emitted the artifact.
    pub commit: String,
    /// Optional producer binary/tool name.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    /// Optional producer binary/tool version.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub version: Option<String>,
}

impl Producer {
    fn validate(&self) -> Result<(), ProofArtifactV1Error> {
        require_non_empty("producer.repo", &self.repo)?;
        require_non_empty("producer.commit", &self.commit)?;
        if let Some(name) = &self.name {
            require_non_empty("producer.name", name)?;
        }
        if let Some(version) = &self.version {
            require_non_empty("producer.version", version)?;
        }
        Ok(())
    }
}

/// One exact verifier constant used by a certificate.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerifierConstant {
    /// Stable name used by the certificate payload.
    pub name: String,
    /// Optional role such as `constraint_rhs`, `farkas_weight`, or `bound`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub role: Option<String>,
    /// Exact rational value. JSON numbers are intentionally rejected.
    pub value: ExactRational,
    /// Optional conservative interval for constants that originated from floats.
    #[serde(default, alias = "bounds", skip_serializing_if = "Option::is_none")]
    pub conservative_bounds: Option<ConservativeBounds>,
}

impl VerifierConstant {
    fn validate(&self) -> Result<(), ProofArtifactV1Error> {
        require_non_empty("verifier_constants[].name", &self.name)?;
        if let Some(role) = &self.role {
            require_non_empty("verifier_constants[].role", role)?;
        }
        if let Some(bounds) = &self.conservative_bounds {
            bounds.validate(&self.name)?;
        }
        Ok(())
    }
}

/// Conservative rational interval attached to a verifier constant.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ConservativeBounds {
    /// Lower exact rational bound.
    pub lower: ExactRational,
    /// Upper exact rational bound.
    pub upper: ExactRational,
    /// Optional reason or rounding mode used to produce the interval.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
}

impl ConservativeBounds {
    fn validate(&self, constant_name: &str) -> Result<(), ProofArtifactV1Error> {
        if let Some(reason) = &self.reason {
            require_non_empty("verifier_constants[].conservative_bounds.reason", reason)?;
        }
        if self.lower > self.upper {
            return Err(ProofArtifactV1Error::InvalidConservativeBounds {
                constant: constant_name.to_string(),
                lower: self.lower.to_string(),
                upper: self.upper.to_string(),
            });
        }
        Ok(())
    }
}

/// Certificate payload envelope. The parser validates the envelope shape but
/// treats `payload` as opaque bytes/JSON for downstream checkers.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CertificatePayloadEnvelope {
    /// Payload format identifier, e.g. `gamma-crown-linear-entailment-v1`.
    pub format: String,
    /// How `payload` is encoded.
    pub encoding: CertificatePayloadEncoding,
    /// Opaque certificate payload.
    pub payload: Value,
    /// Optional hash of the encoded payload.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub payload_hash: Option<String>,
}

impl CertificatePayloadEnvelope {
    fn validate(&self) -> Result<(), ProofArtifactV1Error> {
        require_non_empty("certificate.format", &self.format)?;
        if let Some(payload_hash) = &self.payload_hash {
            require_non_empty("certificate.payload_hash", payload_hash)?;
        }
        match self.encoding {
            CertificatePayloadEncoding::Json => {
                if self.payload.is_null() {
                    return Err(ProofArtifactV1Error::InvalidPayloadEncoding {
                        encoding: self.encoding.as_str().to_string(),
                        expected: "non-null JSON",
                    });
                }
            }
            CertificatePayloadEncoding::Base64
            | CertificatePayloadEncoding::Hex
            | CertificatePayloadEncoding::Text => {
                if !self.payload.is_string() {
                    return Err(ProofArtifactV1Error::InvalidPayloadEncoding {
                        encoding: self.encoding.as_str().to_string(),
                        expected: "a string payload",
                    });
                }
            }
        }
        Ok(())
    }
}

/// Supported certificate payload encodings.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CertificatePayloadEncoding {
    /// `payload` is embedded JSON.
    Json,
    /// `payload` is base64 text.
    Base64,
    /// `payload` is lowercase or uppercase hexadecimal text.
    Hex,
    /// `payload` is plain UTF-8 text.
    Text,
}

impl CertificatePayloadEncoding {
    fn as_str(self) -> &'static str {
        match self {
            Self::Json => "json",
            Self::Base64 => "base64",
            Self::Hex => "hex",
            Self::Text => "text",
        }
    }
}

/// Exact rational in normalized form with positive denominator.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct ExactRational {
    numerator: String,
    denominator: String,
}

impl ExactRational {
    /// Build and normalize an exact rational from signed decimal integers.
    pub fn new(numerator: &str, denominator: &str) -> Result<Self, ProofArtifactV1Error> {
        let mut num = parse_integer_component("numerator", numerator)?;
        let mut den = parse_integer_component("denominator", denominator)?;

        if den == BigInt::from(0) {
            return Err(ProofArtifactV1Error::ZeroDenominator);
        }
        if den.sign() == Sign::Minus {
            num = -num;
            den = -den;
        }

        let gcd = gcd_bigint(abs_bigint(&num), den.clone());
        if gcd != BigInt::from(1) {
            num /= &gcd;
            den /= &gcd;
        }

        Ok(Self {
            numerator: num.to_string(),
            denominator: den.to_string(),
        })
    }

    /// Parse an exact rational from `n`, `n/d`, or finite decimal string form.
    ///
    /// Scientific notation and JSON numeric values are intentionally excluded:
    /// producers must commit to exact decimal digits or provide conservative
    /// rational bounds.
    pub fn parse(input: &str) -> Result<Self, ProofArtifactV1Error> {
        if input.is_empty() || input.trim() != input {
            return Err(ProofArtifactV1Error::InvalidRational {
                value: input.to_string(),
                reason: "must be non-empty and contain no surrounding whitespace",
            });
        }

        if input.contains('/') {
            let mut parts = input.split('/');
            let numerator = parts.next().unwrap_or_default();
            let denominator = parts.next().unwrap_or_default();
            if parts.next().is_some() || numerator.is_empty() || denominator.is_empty() {
                return Err(ProofArtifactV1Error::InvalidRational {
                    value: input.to_string(),
                    reason: "expected exactly one numerator/denominator separator",
                });
            }
            return Self::new(numerator, denominator);
        }

        if input.contains('.') {
            return parse_finite_decimal(input);
        }

        Self::new(input, "1")
    }

    /// Normalized numerator as a signed decimal integer.
    #[must_use]
    pub fn numerator(&self) -> &str {
        &self.numerator
    }

    /// Normalized positive denominator as a decimal integer.
    #[must_use]
    pub fn denominator(&self) -> &str {
        &self.denominator
    }

    fn to_bigints(&self) -> (BigInt, BigInt) {
        let num = parse_integer_component("numerator", &self.numerator)
            .expect("ExactRational stores a valid numerator");
        let den = parse_integer_component("denominator", &self.denominator)
            .expect("ExactRational stores a valid denominator");
        (num, den)
    }
}

impl fmt::Display for ExactRational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.denominator == "1" {
            write!(f, "{}", self.numerator)
        } else {
            write!(f, "{}/{}", self.numerator, self.denominator)
        }
    }
}

impl Ord for ExactRational {
    fn cmp(&self, other: &Self) -> Ordering {
        let (lhs_num, lhs_den) = self.to_bigints();
        let (rhs_num, rhs_den) = other.to_bigints();
        (lhs_num * &rhs_den).cmp(&(rhs_num * &lhs_den))
    }
}

impl PartialOrd for ExactRational {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Serialize for ExactRational {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut state = serializer.serialize_struct("ExactRational", 2)?;
        state.serialize_field("num", &self.numerator)?;
        state.serialize_field("den", &self.denominator)?;
        state.end()
    }
}

impl<'de> Deserialize<'de> for ExactRational {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_any(ExactRationalVisitor)
    }
}

struct ExactRationalVisitor;

impl<'de> Visitor<'de> for ExactRationalVisitor {
    type Value = ExactRational;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(
            "an exact rational string, [\"num\", \"den\"], or {\"num\":\"...\",\"den\":\"...\"}",
        )
    }

    fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        ExactRational::parse(value).map_err(E::custom)
    }

    fn visit_string<E>(self, value: String) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        self.visit_str(&value)
    }

    fn visit_i64<E>(self, value: i64) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        ExactRational::new(&value.to_string(), "1").map_err(E::custom)
    }

    fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        ExactRational::new(&value.to_string(), "1").map_err(E::custom)
    }

    fn visit_f64<E>(self, _value: f64) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Err(rounded_float_only_error::<E>())
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let numerator: IntegerComponent = seq
            .next_element()?
            .ok_or_else(|| de::Error::invalid_length(0, &self))?;
        let denominator: IntegerComponent = seq
            .next_element()?
            .ok_or_else(|| de::Error::invalid_length(1, &self))?;
        if seq.next_element::<IgnoredAny>()?.is_some() {
            return Err(de::Error::invalid_length(3, &self));
        }
        ExactRational::new(&numerator.0, &denominator.0).map_err(de::Error::custom)
    }

    fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
    where
        A: MapAccess<'de>,
    {
        let mut numerator = None;
        let mut denominator = None;
        while let Some(key) = map.next_key::<String>()? {
            match key.as_str() {
                "num" | "numerator" => {
                    if numerator.is_some() {
                        return Err(de::Error::duplicate_field("num"));
                    }
                    numerator = Some(map.next_value::<IntegerComponent>()?);
                }
                "den" | "denominator" => {
                    if denominator.is_some() {
                        return Err(de::Error::duplicate_field("den"));
                    }
                    denominator = Some(map.next_value::<IntegerComponent>()?);
                }
                other => {
                    return Err(de::Error::unknown_field(
                        other,
                        &["num", "den", "numerator", "denominator"],
                    ));
                }
            }
        }

        let numerator = numerator.ok_or_else(|| de::Error::missing_field("num"))?;
        let denominator = denominator.ok_or_else(|| de::Error::missing_field("den"))?;
        ExactRational::new(&numerator.0, &denominator.0).map_err(de::Error::custom)
    }
}

struct IntegerComponent(String);

impl<'de> Deserialize<'de> for IntegerComponent {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_any(IntegerComponentVisitor)
    }
}

struct IntegerComponentVisitor;

impl<'de> Visitor<'de> for IntegerComponentVisitor {
    type Value = IntegerComponent;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("a signed decimal integer string or JSON integer")
    }

    fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        parse_integer_component("integer component", value)
            .map(|_| IntegerComponent(value.to_string()))
            .map_err(E::custom)
    }

    fn visit_string<E>(self, value: String) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        self.visit_str(&value)
    }

    fn visit_i64<E>(self, value: i64) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(IntegerComponent(value.to_string()))
    }

    fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(IntegerComponent(value.to_string()))
    }

    fn visit_f64<E>(self, _value: f64) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Err(rounded_float_only_error::<E>())
    }
}

/// Errors produced by `proof-artifact-v1` parsing and validation.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ProofArtifactV1Error {
    /// Unsupported artifact schema version.
    #[error("unsupported proof artifact version '{found}', expected '{expected}'")]
    UnsupportedVersion {
        /// Found version.
        found: String,
        /// Expected canonical version.
        expected: &'static str,
    },
    /// Required string field was empty.
    #[error("field '{field}' must not be empty")]
    EmptyField {
        /// Field path.
        field: &'static str,
    },
    /// Exact rational denominator was zero.
    #[error("exact rational denominator must be non-zero")]
    ZeroDenominator,
    /// Integer component was malformed.
    #[error("invalid decimal integer for {field}: '{value}'")]
    InvalidInteger {
        /// Component name.
        field: &'static str,
        /// Bad value.
        value: String,
    },
    /// Exact rational literal was malformed.
    #[error("invalid exact rational '{value}': {reason}")]
    InvalidRational {
        /// Bad literal.
        value: String,
        /// Reason.
        reason: &'static str,
    },
    /// Conservative bounds were inverted.
    #[error("conservative bounds for constant '{constant}' are inverted: {lower} > {upper}")]
    InvalidConservativeBounds {
        /// Constant name.
        constant: String,
        /// Lower bound.
        lower: String,
        /// Upper bound.
        upper: String,
    },
    /// Certificate payload did not match its declared encoding.
    #[error("certificate payload for encoding '{encoding}' must be {expected}")]
    InvalidPayloadEncoding {
        /// Encoding name.
        encoding: String,
        /// Expected payload shape.
        expected: &'static str,
    },
    /// Serde-level syntax or shape error.
    #[error("failed to parse proof artifact JSON: {message}")]
    Serde {
        /// Serde error text.
        message: String,
    },
}

impl From<serde_json::Error> for ProofArtifactV1Error {
    fn from(error: serde_json::Error) -> Self {
        Self::Serde {
            message: error.to_string(),
        }
    }
}

fn rounded_float_only_error<E>() -> E
where
    E: de::Error,
{
    E::custom(
        "rounded float-only verifier constants are rejected; encode exact rationals as strings, \
         [\"num\", \"den\"], or {\"num\":\"...\",\"den\":\"...\"}",
    )
}

fn require_non_empty(field: &'static str, value: &str) -> Result<(), ProofArtifactV1Error> {
    if value.is_empty() {
        Err(ProofArtifactV1Error::EmptyField { field })
    } else {
        Ok(())
    }
}

fn validate_optional_non_empty(
    field: &'static str,
    value: &Option<String>,
) -> Result<(), ProofArtifactV1Error> {
    if let Some(value) = value {
        require_non_empty(field, value)?;
    }
    Ok(())
}

fn require_present_non_empty(
    field: &'static str,
    value: &Option<String>,
) -> Result<(), ProofArtifactV1Error> {
    require_non_empty(field, value.as_deref().unwrap_or_default())
}

fn parse_integer_component(
    field: &'static str,
    value: &str,
) -> Result<BigInt, ProofArtifactV1Error> {
    if value.is_empty() || value.trim() != value {
        return Err(ProofArtifactV1Error::InvalidInteger {
            field,
            value: value.to_string(),
        });
    }

    let digits = value
        .strip_prefix('-')
        .or_else(|| value.strip_prefix('+'))
        .unwrap_or(value);
    if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err(ProofArtifactV1Error::InvalidInteger {
            field,
            value: value.to_string(),
        });
    }

    BigInt::parse_bytes(value.as_bytes(), 10).ok_or_else(|| ProofArtifactV1Error::InvalidInteger {
        field,
        value: value.to_string(),
    })
}

fn parse_finite_decimal(input: &str) -> Result<ExactRational, ProofArtifactV1Error> {
    let dot_count = input.bytes().filter(|byte| *byte == b'.').count();
    if dot_count != 1 {
        return Err(ProofArtifactV1Error::InvalidRational {
            value: input.to_string(),
            reason: "expected exactly one decimal point",
        });
    }

    let (sign, unsigned) = match input.as_bytes().first() {
        Some(b'-') => ("-", &input[1..]),
        Some(b'+') => ("", &input[1..]),
        _ => ("", input),
    };
    let (whole, fractional) =
        unsigned
            .split_once('.')
            .ok_or_else(|| ProofArtifactV1Error::InvalidRational {
                value: input.to_string(),
                reason: "expected a finite decimal literal",
            })?;

    if whole.is_empty() || fractional.is_empty() {
        return Err(ProofArtifactV1Error::InvalidRational {
            value: input.to_string(),
            reason: "decimal literals must contain digits on both sides of the decimal point",
        });
    }
    if !whole.bytes().all(|byte| byte.is_ascii_digit())
        || !fractional.bytes().all(|byte| byte.is_ascii_digit())
    {
        return Err(ProofArtifactV1Error::InvalidRational {
            value: input.to_string(),
            reason: "decimal literals may contain only base-10 digits",
        });
    }

    let mut denominator = BigInt::from(1);
    for _ in 0..fractional.len() {
        denominator *= 10;
    }

    let numerator = format!("{sign}{whole}{fractional}");
    ExactRational::new(&numerator, &denominator.to_string())
}

fn gcd_bigint(mut a: BigInt, mut b: BigInt) -> BigInt {
    while b != BigInt::from(0) {
        let remainder = &a % &b;
        a = b;
        b = remainder;
    }
    a
}

fn abs_bigint(value: &BigInt) -> BigInt {
    if value.sign() == Sign::Minus {
        -value
    } else {
        value.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::{Path, PathBuf};

    fn fixture_json(value: &str) -> String {
        format!(
            r#"{{
  "version": "proof-artifact-v1",
  "producer": {{
    "repo": "alabsystems/gamma-crown",
    "commit": "0123456789abcdef"
  }},
  "source_system": "gamma-crown",
  "problem_hash": "blake3:problem",
  "model_hash": "blake3:model",
  "proof_hash": "blake3:proof",
  "certification": {{
    "evidence_kind": "replay_only"
  }},
  "artifact_kind": "gamma_crown_entailment",
  "verifier_constants": [
    {{
      "name": "rhs_block_3_356",
      "role": "constraint_rhs",
      "value": {value},
      "conservative_bounds": {{
        "lower": "-236774565/1000000000",
        "upper": "-236774563/1000000000",
        "reason": "outward decimal rounding"
      }}
    }},
    {{
      "name": "farkas_weight_0",
      "value": [6, -8]
    }},
    {{
      "name": "decimal_literal",
      "value": "0.1250"
    }}
  ],
  "certificate": {{
    "format": "gamma-crown-linear-entailment-v1",
    "encoding": "json",
    "payload": {{
      "type": "linear_entailment",
      "constraints": []
    }},
    "payload_hash": "blake3:payload"
  }}
}}"#
        )
    }

    fn workspace_root() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("crate dir should have workspace parent")
            .parent()
            .expect("workspace root should exist")
            .to_path_buf()
    }

    fn external_certificate_fixture_path(name: &str) -> PathBuf {
        workspace_root()
            .join("tests/fixtures/external_certificates")
            .join(name)
    }

    fn proof_artifact_fixture_path(name: &str) -> PathBuf {
        workspace_root()
            .join("tests/fixtures/external_certificates/proof_artifact_v1")
            .join(name)
    }

    fn load_json_fixture(path: &Path) -> Value {
        let json = std::fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("fixture {} should be readable: {e}", path.display()));
        serde_json::from_str(&json)
            .unwrap_or_else(|e| panic!("fixture {} should parse as JSON: {e}", path.display()))
    }

    fn load_artifact_fixture(name: &str) -> ProofArtifactV1 {
        let path = proof_artifact_fixture_path(name);
        let json = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("fixture {} should be readable: {e}", path.display()));
        ProofArtifactV1::from_json(&json)
            .unwrap_or_else(|e| panic!("fixture {} should parse as artifact: {e}", path.display()))
    }

    #[test]
    fn fixture_artifact_roundtrips_and_normalizes_exact_rationals() {
        let artifact =
            ProofArtifactV1::from_json(&fixture_json(r#"{"num":"-473549128","den":"2000000000"}"#))
                .expect("fixture should parse");

        assert_eq!(artifact.version, PROOF_ARTIFACT_V1_VERSION);
        assert_eq!(artifact.producer.repo, "alabsystems/gamma-crown");
        assert_eq!(artifact.model_hash, "blake3:model");
        assert_eq!(artifact.proof_hash, "blake3:proof");
        assert_eq!(
            artifact
                .certification
                .as_ref()
                .map(|certification| certification.evidence_kind),
            Some(CertificationEvidenceKind::ReplayOnly)
        );
        assert_eq!(
            artifact.verifier_constants[0].value.numerator(),
            "-59193641"
        );
        assert_eq!(
            artifact.verifier_constants[0].value.denominator(),
            "250000000"
        );
        assert_eq!(artifact.verifier_constants[1].value.numerator(), "-3");
        assert_eq!(artifact.verifier_constants[1].value.denominator(), "4");
        assert_eq!(artifact.verifier_constants[2].value.numerator(), "1");
        assert_eq!(artifact.verifier_constants[2].value.denominator(), "8");

        let encoded = artifact.to_json().expect("validated artifact serializes");
        assert!(encoded.contains(r#""verifier_constants""#));
        assert!(encoded.contains(r#""num":"-59193641""#));
        assert!(encoded.contains(r#""den":"250000000""#));
    }

    #[test]
    fn rational_parser_normalizes_signs_gcd_and_decimals() {
        let cases = [
            ("-10/-20", "1", "2"),
            ("0012/00018", "2", "3"),
            ("-0.2500", "-1", "4"),
            ("0", "0", "1"),
            ("42", "42", "1"),
        ];

        for (input, expected_num, expected_den) in cases {
            let rational = ExactRational::parse(input).expect("rational should parse");
            assert_eq!(rational.numerator(), expected_num, "{input}");
            assert_eq!(rational.denominator(), expected_den, "{input}");
        }
    }

    #[test]
    fn rational_parser_rejects_zero_denominator_and_float_notation() {
        assert_eq!(
            ExactRational::parse("1/0").expect_err("zero denominator rejected"),
            ProofArtifactV1Error::ZeroDenominator
        );
        assert!(matches!(
            ExactRational::parse("1e-3"),
            Err(ProofArtifactV1Error::InvalidInteger { .. })
        ));
        assert!(serde_json::from_str::<ExactRational>("1.0").is_err());
        assert!(matches!(
            ExactRational::parse("1."),
            Err(ProofArtifactV1Error::InvalidRational { .. })
        ));
    }

    #[test]
    fn rounded_float_only_verifier_constant_is_rejected() {
        let error = ProofArtifactV1::from_json(&fixture_json("-0.236774564"))
            .expect_err("JSON float constants must be rejected");

        assert!(error.to_string().contains("rounded float-only"), "{error}");
    }

    #[test]
    fn conservative_bounds_must_be_ordered() {
        let mut artifact =
            ProofArtifactV1::from_json(&fixture_json(r#""-0.236774564""#)).expect("parse");
        let bounds = artifact.verifier_constants[0]
            .conservative_bounds
            .as_mut()
            .expect("bounds present");
        bounds.lower = ExactRational::parse("2").expect("lower");
        bounds.upper = ExactRational::parse("1").expect("upper");

        assert!(matches!(
            artifact.validate(),
            Err(ProofArtifactV1Error::InvalidConservativeBounds { .. })
        ));
    }

    #[test]
    fn missing_mandatory_model_hash_is_rejected() {
        let json = fixture_json(r#""-0.236774564""#).replace(
            r#"  "model_hash": "blake3:model",
"#,
            "",
        );

        let error = ProofArtifactV1::from_json(&json).expect_err("missing model_hash rejected");
        assert!(error.to_string().contains("model_hash"), "{error}");
    }

    #[test]
    fn non_json_payload_encodings_require_string_payloads() {
        let json = fixture_json(r#""-0.236774564""#)
            .replace(r#""encoding": "json""#, r#""encoding": "base64""#);

        assert!(matches!(
            ProofArtifactV1::from_json(&json),
            Err(ProofArtifactV1Error::InvalidPayloadEncoding { .. })
        ));
    }

    #[test]
    fn certification_metadata_is_optional_for_legacy_artifacts() {
        let json = fixture_json(r#""-0.236774564""#).replace(
            r#"  "certification": {
    "evidence_kind": "replay_only"
  },
"#,
            "",
        );

        let artifact = ProofArtifactV1::from_json(&json).expect("legacy artifact should parse");
        assert_eq!(artifact.certification, None);
    }

    #[test]
    fn kernel_certified_metadata_requires_kernel_evidence() {
        let json = fixture_json(r#""-0.236774564""#).replace(
            r#""certification": {
    "evidence_kind": "replay_only"
  }"#,
            r#""certification": {
    "evidence_kind": "kernel_certified"
  }"#,
        );

        assert_eq!(
            ProofArtifactV1::from_json(&json).expect_err("missing kernel evidence rejected"),
            ProofArtifactV1Error::EmptyField {
                field: "certification.kernel_theorem"
            }
        );
    }

    #[test]
    fn kernel_certified_metadata_accepts_nonempty_kernel_evidence() {
        let json = fixture_json(r#""-0.236774564""#).replace(
            r#""certification": {
    "evidence_kind": "replay_only"
  }"#,
            r#""certification": {
    "evidence_kind": "kernel_certified",
    "kernel_theorem": "clean.Certificates.GammaCrown.valid",
    "proof_term_hash": "blake3:proof-term",
    "checker": "clean-kernel-checker:fixture"
  }"#,
        );

        let artifact = ProofArtifactV1::from_json(&json).expect("kernel evidence should parse");
        let certification = artifact.certification.expect("certification present");
        assert_eq!(
            certification.evidence_kind,
            CertificationEvidenceKind::KernelCertified
        );
        assert_eq!(
            certification.kernel_theorem.as_deref(),
            Some("clean.Certificates.GammaCrown.valid")
        );
    }

    #[test]
    fn certification_kernel_fields_are_nonempty_when_present() {
        let json = fixture_json(r#""-0.236774564""#).replace(
            r#""certification": {
    "evidence_kind": "replay_only"
  }"#,
            r#""certification": {
    "evidence_kind": "replay_only",
    "kernel_theorem": ""
  }"#,
        );

        assert_eq!(
            ProofArtifactV1::from_json(&json).expect_err("empty kernel theorem rejected"),
            ProofArtifactV1Error::EmptyField {
                field: "certification.kernel_theorem"
            }
        );
    }

    #[test]
    fn checked_in_gamma_crown_entailment_wrapper_preserves_payload_and_constants() {
        let artifact = load_artifact_fixture("gamma_crown_entailment_valid.json");
        let raw_payload = load_json_fixture(&external_certificate_fixture_path(
            "gamma_crown_entailment_valid.json",
        ));

        assert_eq!(
            artifact.certificate.encoding,
            CertificatePayloadEncoding::Json
        );
        assert_eq!(
            artifact
                .certification
                .as_ref()
                .map(|certification| certification.evidence_kind),
            Some(CertificationEvidenceKind::ReplayOnly)
        );
        assert_eq!(artifact.certificate.payload, raw_payload);

        let constants: Vec<_> = artifact
            .verifier_constants
            .iter()
            .map(|constant| {
                (
                    constant.name.as_str(),
                    constant.role.as_deref(),
                    constant.value.numerator(),
                    constant.value.denominator(),
                )
            })
            .collect();
        assert_eq!(
            constants,
            vec![
                ("premise_0_constant", Some("constraint_rhs"), "5", "1"),
                ("multiplier_0", Some("farkas_weight"), "1", "1"),
                ("conclusion_constant", Some("constraint_rhs"), "6", "1"),
            ]
        );
    }

    #[test]
    fn checked_in_gamma_crown_farkas_wrapper_preserves_payload_and_constants() {
        let artifact = load_artifact_fixture("gamma_crown_farkas_valid.json");
        let raw_payload = load_json_fixture(&external_certificate_fixture_path(
            "gamma_crown_farkas_valid.json",
        ));

        assert_eq!(
            artifact.certificate.encoding,
            CertificatePayloadEncoding::Json
        );
        assert_eq!(
            artifact
                .certification
                .as_ref()
                .map(|certification| certification.evidence_kind),
            Some(CertificationEvidenceKind::ReplayOnly)
        );
        assert_eq!(artifact.certificate.payload, raw_payload);

        let constants: Vec<_> = artifact
            .verifier_constants
            .iter()
            .map(|constant| {
                (
                    constant.name.as_str(),
                    constant.role.as_deref(),
                    constant.value.numerator(),
                    constant.value.denominator(),
                )
            })
            .collect();
        assert_eq!(
            constants,
            vec![
                ("constraint_0_constant", Some("constraint_rhs"), "5", "1"),
                ("constraint_1_constant", Some("constraint_rhs"), "-6", "1"),
                ("multiplier_0", Some("farkas_weight"), "1", "1"),
                ("multiplier_1", Some("farkas_weight"), "1", "1"),
            ]
        );
    }

    #[test]
    fn checked_in_ay_alethe_wrapper_preserves_payload_and_has_no_constants() {
        let artifact = load_artifact_fixture("ay_alethe_envelope.json");
        let raw_payload = load_json_fixture(&external_certificate_fixture_path(
            "ay_alethe_envelope.json",
        ));

        assert_eq!(
            artifact.certificate.encoding,
            CertificatePayloadEncoding::Json
        );
        assert_eq!(
            artifact
                .certification
                .as_ref()
                .map(|certification| certification.evidence_kind),
            Some(CertificationEvidenceKind::ReplayOnly)
        );
        assert_eq!(artifact.certificate.payload, raw_payload);
        assert!(artifact.verifier_constants.is_empty());
    }
}
