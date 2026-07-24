// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Portable cross-project proof certificates.
//!
//! This format is intentionally small: it records the theorem name, hashes of
//! the theorem type and proof term, prover metadata, and dependency hashes.
//! That makes it easy to share proof identities between clean, ay, and
//! gamma-crown without embedding Lean-specific proof certificate internals.

use std::fmt::Write as _;

use crate::env::Environment;
use crate::expr::Expr;
use crate::name::Name;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const HASH_ALGORITHM: &str = "sha256";

/// Provenance for the system that emitted the cross-project certificate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProverSystem {
    Clean,
    Ay,
    GammaCrown,
    Other(String),
}

/// Producer metadata attached to a portable certificate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProverInfo {
    pub system: ProverSystem,
    pub name: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub version: Option<String>,
}

impl ProverInfo {
    pub fn new(system: ProverSystem, name: impl Into<String>, version: Option<String>) -> Self {
        Self {
            system,
            name: name.into(),
            version,
        }
    }
}

/// Hashed dependency entry for a theorem referenced by a shared proof.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CrossProjectDependency {
    pub theorem_name: String,
    pub theorem_type_hash: String,
    pub proof_hash: String,
}

impl CrossProjectDependency {
    pub fn new(
        theorem_name: impl Into<String>,
        theorem_type_hash: impl Into<String>,
        proof_hash: impl Into<String>,
    ) -> Self {
        Self {
            theorem_name: theorem_name.into(),
            theorem_type_hash: theorem_type_hash.into(),
            proof_hash: proof_hash.into(),
        }
    }

    /// Build a dependency record by hashing an existing theorem in `env`.
    pub fn from_environment(
        env: &Environment,
        theorem_name: impl Into<String>,
    ) -> Result<Self, CrossProjectVerifyError> {
        let theorem_name = theorem_name.into();
        let (theorem_type_hash, proof_hash) = declaration_hashes(env, &theorem_name, "dependency")?;
        Ok(Self::new(theorem_name, theorem_type_hash, proof_hash))
    }
}

/// Portable theorem identity shared across proof-producing systems.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use = "cross-project certificates should be verified or stored"]
pub struct CrossProjectCert {
    pub theorem_name: String,
    pub theorem_type_hash: String,
    pub proof_hash: String,
    pub prover: ProverInfo,
    #[serde(default)]
    pub dependencies: Vec<CrossProjectDependency>,
}

impl CrossProjectCert {
    /// Hash algorithm used for theorem and proof digests.
    pub const HASH_ALGORITHM: &'static str = HASH_ALGORITHM;

    pub fn new(
        theorem_name: impl Into<String>,
        theorem_type_hash: impl Into<String>,
        proof_hash: impl Into<String>,
        prover: ProverInfo,
        dependencies: Vec<CrossProjectDependency>,
    ) -> Self {
        Self {
            theorem_name: theorem_name.into(),
            theorem_type_hash: theorem_type_hash.into(),
            proof_hash: proof_hash.into(),
            prover,
            dependencies,
        }
    }

    /// Build a certificate by hashing the theorem currently registered in `env`.
    pub fn from_environment(
        env: &Environment,
        theorem_name: impl Into<String>,
        prover: ProverInfo,
        dependencies: Vec<CrossProjectDependency>,
    ) -> Result<Self, CrossProjectVerifyError> {
        let theorem_name = theorem_name.into();
        let (theorem_type_hash, proof_hash) = declaration_hashes(env, &theorem_name, "theorem")?;
        Ok(Self::new(
            theorem_name,
            theorem_type_hash,
            proof_hash,
            prover,
            dependencies,
        ))
    }

    /// Serialize the portable certificate as JSON using `serde_json`.
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }

    /// Deserialize the portable certificate from JSON using `serde_json`.
    pub fn from_json(json: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(json)
    }

    /// Serialize the portable certificate as bincode.
    pub fn to_bincode(&self) -> Result<Vec<u8>, bincode::error::EncodeError> {
        bincode::serde::encode_to_vec(self, bincode::config::standard())
    }

    /// Deserialize the portable certificate from bincode.
    pub fn from_bincode(bytes: &[u8]) -> Result<Self, bincode::error::DecodeError> {
        bincode::serde::decode_from_slice(bytes, bincode::config::standard()).map(|(__v, _)| __v)
    }

    /// Verify that the certificate matches the theorem and dependencies in `env`.
    pub fn verify(&self, env: &Environment) -> Result<(), CrossProjectVerifyError> {
        let (actual_type_hash, actual_proof_hash) =
            declaration_hashes(env, &self.theorem_name, "theorem")?;
        ensure_hash_match(
            "theorem",
            &self.theorem_name,
            "type",
            &self.theorem_type_hash,
            &actual_type_hash,
        )?;
        ensure_hash_match(
            "theorem",
            &self.theorem_name,
            "proof",
            &self.proof_hash,
            &actual_proof_hash,
        )?;

        for dependency in &self.dependencies {
            let (actual_type_hash, actual_proof_hash) =
                declaration_hashes(env, &dependency.theorem_name, "dependency")?;
            ensure_hash_match(
                "dependency",
                &dependency.theorem_name,
                "type",
                &dependency.theorem_type_hash,
                &actual_type_hash,
            )?;
            ensure_hash_match(
                "dependency",
                &dependency.theorem_name,
                "proof",
                &dependency.proof_hash,
                &actual_proof_hash,
            )?;
        }

        Ok(())
    }
}

/// Verification failures for portable certificates.
#[derive(Debug, thiserror::Error)]
pub enum CrossProjectVerifyError {
    #[error("{role} {name} not found in environment")]
    MissingDeclaration { role: &'static str, name: String },
    #[error("{role} {name} has no proof term in environment")]
    MissingProof { role: &'static str, name: String },
    #[error("{role} {name} {field} hash mismatch: expected {expected}, actual {actual}")]
    HashMismatch {
        role: &'static str,
        name: String,
        field: &'static str,
        expected: String,
        actual: String,
    },
    #[error("failed to serialize {field} for {role} {name}: {source}")]
    HashSerialization {
        role: &'static str,
        name: String,
        field: &'static str,
        #[source]
        source: bincode::error::EncodeError,
    },
}

fn declaration_hashes(
    env: &Environment,
    theorem_name: &str,
    role: &'static str,
) -> Result<(String, String), CrossProjectVerifyError> {
    let name = Name::from_string(theorem_name);
    let decl = env
        .get_const(&name)
        .ok_or_else(|| CrossProjectVerifyError::MissingDeclaration {
            role,
            name: theorem_name.to_string(),
        })?;
    let theorem_type_hash = hash_expr(&decl.type_, theorem_name, role, "type")?;
    let proof = decl
        .value
        .as_ref()
        .ok_or_else(|| CrossProjectVerifyError::MissingProof {
            role,
            name: theorem_name.to_string(),
        })?;
    let proof_hash = hash_expr(proof, theorem_name, role, "proof")?;
    Ok((theorem_type_hash, proof_hash))
}

fn hash_expr(
    expr: &Expr,
    theorem_name: &str,
    role: &'static str,
    field: &'static str,
) -> Result<String, CrossProjectVerifyError> {
    let bytes =
        bincode::serde::encode_to_vec(expr, bincode::config::standard()).map_err(|source| {
            CrossProjectVerifyError::HashSerialization {
                role,
                name: theorem_name.to_string(),
                field,
                source,
            }
        })?;
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    let digest = hasher.finalize();
    Ok(encode_hex(digest.as_ref()))
}

fn ensure_hash_match(
    role: &'static str,
    theorem_name: &str,
    field: &'static str,
    expected: &str,
    actual: &str,
) -> Result<(), CrossProjectVerifyError> {
    if expected == actual {
        return Ok(());
    }
    Err(CrossProjectVerifyError::HashMismatch {
        role,
        name: theorem_name.to_string(),
        field,
        expected: expected.to_string(),
        actual: actual.to_string(),
    })
}

/// Map a single nibble (0..=15) to its lowercase hex digit. Total + panic-free:
/// `n & 0x0f` is `0..=15`, every value has an explicit arm, and the catch-all keeps
/// the `match` exhaustive over `u8` without any indexing or fallible arithmetic.
#[inline]
fn hex_digit(n: u8) -> char {
    match n & 0x0f {
        0 => '0',
        1 => '1',
        2 => '2',
        3 => '3',
        4 => '4',
        5 => '5',
        6 => '6',
        7 => '7',
        8 => '8',
        9 => '9',
        10 => 'a',
        11 => 'b',
        12 => 'c',
        13 => 'd',
        14 => 'e',
        _ => 'f',
    }
}

// Panic-free, lowercase, fixed-width hex (identical output to `write!("{:02x}")`),
// written so the verifier DISCHARGES it (no `#[trust::skip]`): `String::new()` is a
// total `const fn` (unlike `with_capacity`, which has a capacity-overflow panic path)
// and `push` only aborts on OOM (not a panic); the nibbles go through `hex_digit`'s
// total `match`, so there is no index, shift-overflow, or capacity panic path left.
fn encode_hex(bytes: &[u8]) -> String {
    let mut output = String::new();
    for &byte in bytes {
        output.push(hex_digit(byte >> 4));
        output.push(hex_digit(byte & 0x0f));
    }
    output
}
