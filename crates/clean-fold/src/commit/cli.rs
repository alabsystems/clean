// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CLI surface for `clean commit` subcommands.
//!
//! Part of Epic #3436 Phase 2. The [`CommitCommands`] clap [`Subcommand`]
//! lives here so the owning crate (`clean-fold`, which absorbed the former
//! `clean-commit` crate in rearch stage 9) owns its CLI verbs. The
//! [`FEATURES`] array exports one [`FeatureDescriptor`] per verb for the
//! top-level `clean features` / `clean help` registry.
//!
//! Design: `designs/2026-04-18-unified-cli-feature-index.md`.

use std::path::PathBuf;

use clap::Subcommand;
use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};

/// Subcommands for `clean commit` (polynomial commitment schemes).
#[derive(Subcommand)]
pub enum CommitCommands {
    /// Create a KZG commitment to a proof certificate.
    Kzg {
        /// Input proof certificate file
        #[arg(short, long)]
        cert: PathBuf,
        /// Output commitment file
        #[arg(short, long)]
        output: PathBuf,
        /// Maximum polynomial degree (power of 2)
        #[arg(short, long, default_value = "16")]
        max_degree: u32,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
    },
    /// Create an IPA commitment to a proof certificate.
    Ipa {
        /// Input proof certificate file
        #[arg(short, long)]
        cert: PathBuf,
        /// Output commitment file
        #[arg(short, long)]
        output: PathBuf,
        /// Maximum polynomial degree (power of 2)
        #[arg(short, long, default_value = "16")]
        max_degree: u32,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
    },
    /// Verify a polynomial commitment.
    Verify {
        /// Commitment file to verify
        commitment: PathBuf,
        /// Original certificate file (for re-computing commitment)
        #[arg(short, long)]
        cert: PathBuf,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
    },
}

const DESIGN_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "Unified CLI feature index",
    target: "designs/2026-04-18-unified-cli-feature-index.md",
};

const CRATE_REF: Reference = Reference {
    kind: RefKind::Crate,
    label: "clean-fold",
    target: "clean-fold",
};

/// Descriptors for every `clean commit ...` verb.
pub const FEATURES: &[FeatureDescriptor] = &[
    FeatureDescriptor {
        path: &["commit", "kzg"],
        summary: "Commit to a proof certificate with KZG",
        description: "Creates a Kate-Zaverucha-Goldberg polynomial commitment \
that binds to a proof certificate's content. KZG produces constant-size \
commitments and pairing-checked verification, at the cost of a trusted setup.",
        category: Category::Proof,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean commit kzg --cert proof.cert.json --output proof.kzg",
            what: "commit a certificate using KZG",
        }],
        see_also: &["commit ipa", "commit verify", "fold start"],
        references: &[DESIGN_REF, CRATE_REF],
        domain_root: Some("commit"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["commit", "ipa"],
        summary: "Commit to a proof certificate with IPA",
        description: "Creates an Inner Product Argument commitment to a proof \
certificate. IPA requires no trusted setup (it is transparent) but verifies \
in logarithmic time rather than KZG's constant time.",
        category: Category::Proof,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean commit ipa --cert proof.cert.json --output proof.ipa",
            what: "commit a certificate using IPA",
        }],
        see_also: &["commit kzg", "commit verify"],
        references: &[DESIGN_REF, CRATE_REF],
        domain_root: Some("commit"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["commit", "verify"],
        summary: "Verify a polynomial commitment against a certificate",
        description: "Re-derives the commitment for the original certificate \
and compares it to the stored commitment, confirming that the artifact on \
disk is a correct commitment to that certificate.",
        category: Category::Proof,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean commit verify proof.kzg --cert proof.cert.json",
            what: "verify a commitment against its certificate",
        }],
        see_also: &["commit kzg", "commit ipa", "cert verify"],
        references: &[DESIGN_REF, CRATE_REF],
        domain_root: Some("commit"),
        alternative_forms: &[],
        feature_gate: None,
    },
];
