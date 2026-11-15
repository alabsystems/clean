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
    /// Fold a certificate into a fresh IVC proof, written to the `--ivc` path.
    Extend {
        /// Write the resulting IVC proof here. NOT read: this verb folds
        /// `--cert` into a FRESH proof, replacing any chain already at this path
        #[arg(short, long)]
        ivc: PathBuf,
        /// Certificate to fold in
        #[arg(short, long)]
        cert: PathBuf,
        /// Output IVC proof file (defaults to overwriting `--ivc`)
        #[arg(short, long)]
        output: Option<PathBuf>,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
    },
    /// Check a serialized IVC proof's structure (NOT the folding relation).
    Verify {
        /// IVC proof file to check
        ivc: PathBuf,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
    },
    /// Rewrite an IVC proof as a smaller summary (the result is NOT a proof).
    Compress {
        /// IVC proof file to summarize
        #[arg(short, long)]
        ivc: PathBuf,
        /// Output summary file (`fold verify` cannot read this back)
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
certificate as a Relaxed R1CS instance. The output file records the running \
instance's metadata; it does not carry the shape or matrices, which is why no \
later verb can resume from it.",
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
        summary: "Fold a certificate into a fresh IVC proof",
        description: "Runs one Nova fold step and writes the result to --ivc \
(or --output). It does NOT load the IVC at --ivc: the running instance is \
started fresh from --cert and that same certificate is folded in, so a chain \
already at that path is replaced, not extended. Carrying a chain forward \
needs the full IVC state to round-trip through the serialized form, which it \
does not yet.",
        category: Category::Proof,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean fold extend --ivc proof.ivc.json --cert step2.cert.json",
            what: "fold a certificate in, overwriting proof.ivc.json",
        }],
        see_also: &["fold start", "fold compress", "fold verify"],
        references: &[DESIGN_REF, CRATE_REF],
        domain_root: Some("fold"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["fold", "verify"],
        summary: "Check the structure of a serialized IVC proof",
        description: "Checks that the artifact parses and records a nonzero \
step count, a nonzero constraint count and a non-empty witness vector. It \
does NOT check the Relaxed R1CS relation (Az o Bz = u*Cz + E) — the shape and \
matrices are never deserialized — so a pass is a statement about the file's \
structure, not a verification of the folded steps.",
        category: Category::Proof,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean fold verify proof.ivc.json",
            what: "check an accumulated IVC proof's structure",
        }],
        see_also: &["fold info", "cert verify"],
        references: &[DESIGN_REF, CRATE_REF],
        domain_root: Some("fold"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["fold", "compress"],
        summary: "Rewrite an IVC proof as a smaller summary artifact",
        description: "Keeps the step count, constraint count and instance \
fields verbatim and REPLACES the witness and error vectors with a 64-bit \
digest. This is not SNARK compression: the witness cannot be recovered, the \
result is not a proof, and `fold verify` cannot read it back.",
        category: Category::Proof,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean fold compress --ivc proof.ivc.json --output proof.ivc.z",
            what: "write a digest-only summary of an IVC proof",
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
