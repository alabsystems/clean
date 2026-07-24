// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CLI surface for `clean fold` subcommands.
//!
//! Part of Epic #3436 Phase 2. The [`FoldCommands`] clap [`Subcommand`] lives
//! here so the owning crate (`clean-fold`) also owns its CLI verbs. The
//! [`FEATURES`] array exports one [`FeatureDescriptor`] per verb for the
//! top-level `clean features` / `clean help` registry.
//!
//! Design: `designs/2026-04-18-unified-cli-feature-index.md`.

use std::path::PathBuf;

use clap::Subcommand;
use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};

/// Subcommands for `clean fold` (Nova-style folding for proof compression).
#[derive(Subcommand)]
pub enum FoldCommands {
    /// Start a new IVC proof from a proof certificate.
    Start {
        /// Input proof certificate file (JSON format)
        #[arg(short, long)]
        cert: PathBuf,
        /// Output IVC proof file
        #[arg(short, long)]
        output: PathBuf,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
    },
    /// Extend an IVC proof with another certificate.
    Extend {
        /// Existing IVC proof file
        #[arg(short, long)]
        ivc: PathBuf,
        /// Certificate to fold in
        #[arg(short, long)]
        cert: PathBuf,
        /// Output IVC proof file (defaults to updating in place)
        #[arg(short, long)]
        output: Option<PathBuf>,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
    },
    /// Verify an IVC proof.
    Verify {
        /// IVC proof file to verify
        ivc: PathBuf,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
    },
    /// Compress an IVC proof.
    Compress {
        /// IVC proof file to compress
        #[arg(short, long)]
        ivc: PathBuf,
        /// Output compressed proof file
        #[arg(short, long)]
        output: PathBuf,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
    },
    /// Show information about an IVC proof.
    Info {
        /// IVC proof file
        ivc: PathBuf,
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

/// Descriptors for every `clean fold ...` verb.
pub const FEATURES: &[FeatureDescriptor] = &[
    FeatureDescriptor {
        path: &["fold", "start"],
        summary: "Start a new IVC proof from a proof certificate",
        description: "Initializes a Nova-style IVC proof by encoding the input \
certificate as a Relaxed R1CS instance. The output file holds the running \
instance that subsequent `fold extend` calls accumulate into.",
        category: Category::Proof,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean fold start --cert proof.cert.json --output proof.ivc.json",
            what: "seed an IVC proof from one certificate",
        }],
        see_also: &["fold extend", "fold verify", "commit kzg"],
        references: &[DESIGN_REF, CRATE_REF],
        domain_root: Some("fold"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["fold", "extend"],
        summary: "Fold a new certificate into an existing IVC proof",
        description: "Runs one Nova fold step: the running IVC instance is \
combined with the fresh certificate instance to produce a new running \
instance whose verifier cost stays constant regardless of the number of \
folded steps.",
        category: Category::Proof,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean fold extend --ivc proof.ivc.json --cert step2.cert.json",
            what: "fold a second certificate into an existing IVC proof",
        }],
        see_also: &["fold start", "fold compress", "fold verify"],
        references: &[DESIGN_REF, CRATE_REF],
        domain_root: Some("fold"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["fold", "verify"],
        summary: "Verify the running instance of an IVC proof",
        description: "Checks that the accumulated Relaxed R1CS instance and \
witness pair satisfies the folding invariant. A single verification call \
discharges every folded step at once.",
        category: Category::Proof,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean fold verify proof.ivc.json",
            what: "verify an accumulated IVC proof",
        }],
        see_also: &["fold info", "cert verify"],
        references: &[DESIGN_REF, CRATE_REF],
        domain_root: Some("fold"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["fold", "compress"],
        summary: "Compress an IVC proof into a smaller artifact",
        description: "Applies the SNARK-style final compression step on an \
IVC proof so the on-disk artifact shrinks without losing soundness. Use \
this before archiving or transmitting long proof chains.",
        category: Category::Proof,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean fold compress --ivc proof.ivc.json --output proof.ivc.z",
            what: "compress an IVC proof artifact",
        }],
        see_also: &["fold verify", "commit kzg"],
        references: &[DESIGN_REF, CRATE_REF],
        domain_root: Some("fold"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["fold", "info"],
        summary: "Print metadata about an IVC proof file",
        description: "Prints the step count, R1CS shape (constraints, \
variables, IO), and other diagnostic fields carried by a serialized IVC \
proof without performing verification.",
        category: Category::Proof,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean fold info proof.ivc.json",
            what: "inspect an IVC proof's shape and step count",
        }],
        see_also: &["fold verify"],
        references: &[DESIGN_REF, CRATE_REF],
        domain_root: Some("fold"),
        alternative_forms: &[],
        feature_gate: None,
    },
];
