// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nova-style Folding Schemes for clean Proof Compression
//!
//! This crate implements Nova-style folding schemes for incrementally
//! composing and compressing clean proof certificates.
//!
//! # Overview
//!
//! Nova-style folding enables composing proofs incrementally without
//! proof size blowup. Instead of proving `F(x₁) ∧ F(x₂)` separately,
//! instances are "folded":
//!
//! - Two instances `(u₁, w₁)` and `(u₂, w₂)` fold into one `(u, w)`
//! - Verifier work is constant per fold step
//! - Final verification is single instance check
//!
//! # Architecture
//!
//! The crate is organized into:
//!
//! - [`r1cs`]: R1CS constraint system representation
//! - [`relaxed`]: Relaxed R1CS for folding (Az ∘ Bz = u·Cz + E)
//! - [`transcript`]: Fiat-Shamir transcript for challenges
//! - [`folding`]: Core folding operation
//! - [`ivc`]: Incrementally Verifiable Computation proofs
//! - [`commit`]: Polynomial commitment schemes (KZG/IPA) for proof
//!   certificates (absorbed from the former `clean-commit` crate)
//!
//! # Example
//!
//! ```text
//! use clean_fold::{IvcProof, start_ivc, extend_ivc, verify_ivc};
//! use clean_kernel::cert::ProofCert;
//!
//! // Start IVC from initial certificate
//! let mut ivc = start_ivc(&cert1, &env)?;
//!
//! // Extend with additional certificates
//! extend_ivc(&mut ivc, &cert2, &env)?;
//! extend_ivc(&mut ivc, &cert3, &env)?;
//!
//! // Verify the accumulated proof
//! assert!(verify_ivc(&ivc)?);
//! ```

pub mod cert_encoding;
pub mod cli;
pub mod commit;
pub mod error;
pub mod folding;
pub mod ivc;
pub mod r1cs;
pub mod relaxed;
pub mod transcript;

pub use cert_encoding::{encode_cert_to_r1cs, verify_encoded, EncodedR1CS};
pub use error::{FoldError, IvcError};
pub use folding::fold;
pub use ivc::{
    extend_ivc, extend_ivc_with_cert, start_ivc, start_ivc_from_cert, verify_ivc, IvcProof,
};
pub use r1cs::{R1CSBuilder, R1CSInstance, R1CSShape, R1CSWitness};
pub use relaxed::{RelaxedR1CSInstance, RelaxedR1CSWitness};
pub use transcript::Transcript;

use ark_bls12_381::Fr;

/// Field element type used throughout the crate
pub type Scalar = Fr;
