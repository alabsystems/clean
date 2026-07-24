// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Certificate types and verification logic.

use super::error::ExternalCertError;
use super::rational::ExternalRational;
use serde::de::Error as _;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::collections::BTreeMap;
use std::ops::Neg;

// ============================================================================//
// Certificate Types
// ============================================================================//

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum ConstraintKind {
    Le,
    Lt,
    Eq,
    Ge,
    Gt,
}

#[derive(Debug, Clone)]
pub struct ExternalLinearConstraint {
    pub kind: ConstraintKind,
    pub coefficients: BTreeMap<String, ExternalRational>,
    pub constant: ExternalRational,
}

impl Serialize for ExternalLinearConstraint {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        #[derive(Serialize)]
        struct LinearConstraintOut<'a> {
            #[serde(rename = "type")]
            kind: &'static str,
            #[serde(rename = "kind")]
            kind_symbol: ConstraintKind,
            coefficients: &'a BTreeMap<String, ExternalRational>,
            constant: ExternalRational,
        }

        let out = LinearConstraintOut {
            kind: "linear_constraint",
            kind_symbol: self.kind,
            coefficients: &self.coefficients,
            constant: self.constant,
        };
        out.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for ExternalLinearConstraint {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        struct LinearConstraintIn {
            #[serde(rename = "type")]
            kind: Option<String>,
            #[serde(rename = "kind")]
            kind_symbol: ConstraintKind,
            coefficients: BTreeMap<String, ExternalRational>,
            constant: ExternalRational,
        }

        let input = LinearConstraintIn::deserialize(deserializer)?;
        if let Some(kind) = input.kind {
            if kind != "linear_constraint" {
                return Err(D::Error::custom("invalid constraint type"));
            }
        }
        Ok(ExternalLinearConstraint {
            kind: input.kind_symbol,
            coefficients: input.coefficients,
            constant: input.constant,
        })
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExternalFarkasCert {
    pub version: String,
    pub constraints: Vec<ExternalLinearConstraint>,
    pub multipliers: Vec<ExternalRational>,
    pub conclusion: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExternalEntailmentCert {
    pub version: String,
    pub premises: Vec<ExternalLinearConstraint>,
    pub multipliers: Vec<ExternalRational>,
    pub conclusion: ExternalLinearConstraint,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum ExternalCertificate {
    #[serde(rename = "farkas_certificate")]
    Farkas(ExternalFarkasCert),
    #[serde(rename = "entailment_certificate")]
    Entailment(ExternalEntailmentCert),
    #[serde(rename = "alethe_certificate")]
    Alethe(super::alethe::ExternalAletheCert),
}

// ============================================================================//
// Verification
// ============================================================================//

#[derive(Debug, Clone)]
pub(super) struct NormalizedConstraint {
    pub(super) coeffs: BTreeMap<String, ExternalRational>,
    pub(super) constant: ExternalRational,
    pub(super) strict: bool,
}

impl NormalizedConstraint {
    pub(super) fn zero() -> Self {
        NormalizedConstraint {
            coeffs: BTreeMap::new(),
            constant: ExternalRational::ZERO,
            strict: false,
        }
    }

    pub(super) fn scale(&self, factor: ExternalRational) -> Result<Self, ExternalCertError> {
        if factor.is_zero() {
            return Ok(NormalizedConstraint::zero());
        }
        let mut coeffs = BTreeMap::new();
        for (var, coeff) in &self.coeffs {
            let scaled = coeff.mul(factor)?;
            if !scaled.is_zero() {
                coeffs.insert(var.clone(), scaled);
            }
        }
        Ok(NormalizedConstraint {
            coeffs,
            constant: self.constant.mul(factor)?,
            strict: self.strict,
        })
    }

    pub(super) fn add(self, other: Self) -> Result<Self, ExternalCertError> {
        let mut coeffs = self.coeffs;
        for (var, coeff) in other.coeffs {
            let entry = coeffs.remove(&var);
            let next = match entry {
                Some(existing) => existing.add(coeff)?,
                None => coeff,
            };
            if !next.is_zero() {
                coeffs.insert(var, next);
            }
        }
        Ok(NormalizedConstraint {
            coeffs,
            constant: self.constant.add(other.constant)?,
            strict: self.strict || other.strict,
        })
    }
}

/// Normalize a linear constraint into one or more `<= b` form constraints.
///
/// For inequality constraints (Le, Lt, Ge, Gt), returns a single normalized
/// constraint. For equality constraints (Eq), decomposes `A*x = b` into two
/// constraints: `A*x <= b` AND `-A*x <= -b` (the Le and Ge directions).
///
/// This decomposition is sound because `A*x = b` iff `A*x <= b` AND `A*x >= b`.
pub(super) fn normalize_constraint(
    constraint: &ExternalLinearConstraint,
) -> Result<Vec<NormalizedConstraint>, ExternalCertError> {
    let mut coeffs = BTreeMap::new();
    for (var, coeff) in &constraint.coefficients {
        if !coeff.is_zero() {
            coeffs.insert(var.clone(), *coeff);
        }
    }

    match constraint.kind {
        ConstraintKind::Le => Ok(vec![NormalizedConstraint {
            coeffs,
            constant: constraint.constant,
            strict: false,
        }]),
        ConstraintKind::Lt => Ok(vec![NormalizedConstraint {
            coeffs,
            constant: constraint.constant,
            strict: true,
        }]),
        ConstraintKind::Ge => Ok(vec![NormalizedConstraint {
            coeffs: coeffs
                .into_iter()
                .map(|(var, coeff)| (var, coeff.neg()))
                .collect(),
            constant: constraint.constant.neg(),
            strict: false,
        }]),
        ConstraintKind::Gt => Ok(vec![NormalizedConstraint {
            coeffs: coeffs
                .into_iter()
                .map(|(var, coeff)| (var, coeff.neg()))
                .collect(),
            constant: constraint.constant.neg(),
            strict: true,
        }]),
        ConstraintKind::Eq => {
            // Decompose A*x = b into A*x <= b AND -A*x <= -b
            let le_part = NormalizedConstraint {
                coeffs: coeffs.clone(),
                constant: constraint.constant,
                strict: false,
            };
            let ge_part = NormalizedConstraint {
                coeffs: coeffs
                    .into_iter()
                    .map(|(var, coeff)| (var, coeff.neg()))
                    .collect(),
                constant: constraint.constant.neg(),
                strict: false,
            };
            Ok(vec![le_part, ge_part])
        }
    }
}

pub(super) fn ensure_version(version: &str) -> Result<(), ExternalCertError> {
    if version != "1.0" {
        return Err(ExternalCertError::invalid_schema(format!(
            "unsupported certificate version: {}",
            version
        )));
    }
    Ok(())
}

/// Verify a Farkas certificate proves a system of linear constraints is infeasible.
///
/// # REQUIRES
/// - `cert.version == "1.0"`
/// - `cert.constraints.len() == cert.multipliers.len()`
/// - All multipliers are non-negative (i.e., `>= 0`)
/// - `cert.conclusion == "contradiction"`
///
/// # ENSURES
/// - On success, the linear combination of constraints yields a contradiction:
///   - If strict (`sum < 0` form): requires `constant <= 0` to contradict `0 < 0`
///   - If non-strict (`sum <= 0` form): requires `constant < 0` to contradict `constant <= 0`
/// - All variable coefficients must cancel out (empty coeffs map)
/// - Returns the final constant term (for debugging/auditing)
///
/// # Errors
/// - `InvalidSchema`: version mismatch, conclusion not "contradiction"
/// - `LengthMismatch`: constraints/multipliers array length mismatch
/// - `MultiplierNegative`: negative multiplier detected
/// - `NoContradiction`: the combined constraint doesn't prove infeasibility
pub fn verify_farkas_certificate(
    cert: &ExternalFarkasCert,
) -> Result<ExternalRational, ExternalCertError> {
    ensure_version(&cert.version)?;
    if cert.conclusion != "contradiction" {
        return Err(ExternalCertError::invalid_schema(
            "farkas certificate conclusion must be 'contradiction'".to_string(),
        ));
    }
    if cert.constraints.len() != cert.multipliers.len() {
        return Err(ExternalCertError::length_mismatch(format!(
            "constraints ({}) and multipliers ({}) length mismatch",
            cert.constraints.len(),
            cert.multipliers.len()
        )));
    }

    let mut combined = NormalizedConstraint::zero();
    for (idx, (constraint, multiplier)) in cert
        .constraints
        .iter()
        .zip(cert.multipliers.iter())
        .enumerate()
    {
        if multiplier.is_negative() {
            return Err(ExternalCertError::multiplier_negative(format!(
                "multipliers[{}] = {} is negative",
                idx, multiplier
            )));
        }
        if multiplier.is_zero() {
            continue;
        }
        for normalized in normalize_constraint(constraint)? {
            let scaled = normalized.scale(*multiplier)?;
            combined = combined.add(scaled)?;
        }
    }

    if !combined.coeffs.is_empty() {
        return Err(ExternalCertError::no_contradiction(
            "combined constraint still has variable coefficients".to_string(),
        ));
    }

    if combined.strict {
        if combined.constant.is_positive() {
            return Err(ExternalCertError::no_contradiction(
                "strict contradiction not achieved".to_string(),
            ));
        }
    } else if !combined.constant.is_negative() {
        return Err(ExternalCertError::no_contradiction(
            "non-strict contradiction not achieved".to_string(),
        ));
    }

    Ok(combined.constant)
}

/// Verify an entailment certificate proves a conclusion follows from premises.
///
/// # REQUIRES
/// - `cert.version == "1.0"`
/// - `cert.premises.len() == cert.multipliers.len()`
/// - All multipliers are non-negative (i.e., `>= 0`)
///
/// # ENSURES
/// - On success, the linear combination of premises implies the conclusion:
///   - The derived coefficient map equals the conclusion's coefficient map
///   - The derived bound implies the claimed bound (considering strictness)
/// - Returns `(derived_bound, claimed_bound)` for auditing
///
/// # Errors
/// - `InvalidSchema`: version mismatch
/// - `LengthMismatch`: premises/multipliers array length mismatch
/// - `MultiplierNegative`: negative multiplier detected
/// - `EntailmentFailed`: derived constraint does not imply conclusion
pub fn verify_entailment_certificate(
    cert: &ExternalEntailmentCert,
) -> Result<(ExternalRational, ExternalRational), ExternalCertError> {
    ensure_version(&cert.version)?;
    if cert.premises.len() != cert.multipliers.len() {
        return Err(ExternalCertError::length_mismatch(format!(
            "premises ({}) and multipliers ({}) length mismatch",
            cert.premises.len(),
            cert.multipliers.len()
        )));
    }

    let mut combined = NormalizedConstraint::zero();
    for (idx, (premise, multiplier)) in cert
        .premises
        .iter()
        .zip(cert.multipliers.iter())
        .enumerate()
    {
        if multiplier.is_negative() {
            return Err(ExternalCertError::multiplier_negative(format!(
                "multipliers[{}] = {} is negative",
                idx, multiplier
            )));
        }
        if multiplier.is_zero() {
            continue;
        }
        for normalized in normalize_constraint(premise)? {
            let scaled = normalized.scale(*multiplier)?;
            combined = combined.add(scaled)?;
        }
    }

    let conclusion_parts = normalize_constraint(&cert.conclusion)?;
    // Entailment conclusion must normalize to exactly one constraint.
    // Equality conclusions are not meaningful for entailment (would require
    // proving both directions simultaneously), so reject multi-part conclusions.
    if conclusion_parts.len() != 1 {
        return Err(ExternalCertError::unsupported_constraint_kind(
            "equality constraints cannot be used as entailment conclusions".to_string(),
        ));
    }
    let conclusion = &conclusion_parts[0];
    if combined.coeffs != conclusion.coeffs {
        return Err(ExternalCertError::entailment_failed(
            "derived coefficients do not match conclusion".to_string(),
        ));
    }

    let derived = combined.constant;
    let claimed = conclusion.constant;
    let ok = if combined.strict && !conclusion.strict {
        derived <= claimed
    } else if !combined.strict && conclusion.strict {
        derived < claimed
    } else {
        derived <= claimed
    };

    if !ok {
        return Err(ExternalCertError::entailment_failed(format!(
            "derived bound {} does not imply claimed bound {}",
            derived, claimed
        )));
    }

    Ok((derived, claimed))
}
