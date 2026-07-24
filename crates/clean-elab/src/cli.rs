// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CLI argument structs and feature descriptors owned by `clean-elab`.
//!
//! Phase 2 of Epic #3436. The elaborator owns the `eval` subcommand
//! because evaluating a single expression drives parser → elaborator →
//! kernel in that order, and the elaborator is the crate that ties the
//! first two together. The descriptor and clap struct live here; the
//! handler implementation currently lives in
//! `clean-cli::cmd_core::eval_expr` and consumes the fields of
//! [`EvalArgs`] unchanged.
//!
//! Design: `designs/2026-04-18-unified-cli-feature-index.md`.

use clap::Args;
use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};

/// Arguments accepted by `clean eval`.
#[derive(Debug, Clone, Args)]
pub struct EvalArgs {
    /// Expression to evaluate.
    pub expr: String,
    /// Show verbose output.
    #[arg(short, long)]
    pub verbose: bool,
}

/// Feature descriptors surfaced by the elaborator crate.
///
/// Registered into the top-level CLI by
/// `clean-cli/src/registry.rs::all_features()`.
pub const FEATURES: &[FeatureDescriptor] = &[FeatureDescriptor {
    path: &["eval"],
    summary: "Elaborate a single expression and report its inferred type",
    description: "\
Parse the expression argument, run the elaborator against an empty \
environment, and use the kernel type-checker to infer the expression's \
type. The command prints both the input expression and the inferred type; \
pass `--verbose` to also see the parsed surface AST, elaborated kernel \
term, and timing information.\n\n\
`eval` is a lightweight probe. For checking entire source files with their \
declarations and imports use `clean check`; for an interactive session use \
`clean repl`.",
    category: Category::Verification,
    stability: Stability::V1,
    examples: &[
        Example {
            cmd: "clean eval \"fun x => x\"",
            what: "infer the type of the identity lambda",
        },
        Example {
            cmd: "clean eval --verbose \"Nat.succ Nat.zero\"",
            what: "show parse, elaboration, and inference steps for `Nat.succ 0`",
        },
    ],
    see_also: &["check", "repl"],
    references: &[
        Reference {
            kind: RefKind::Design,
            label: "Unified CLI feature index",
            target: "designs/2026-04-18-unified-cli-feature-index.md",
        },
        Reference {
            kind: RefKind::Issue,
            label: "Epic #3436",
            target: "3436",
        },
        Reference {
            kind: RefKind::Issue,
            label: "Phase 2 migration #3478",
            target: "3478",
        },
        Reference {
            kind: RefKind::Crate,
            label: "clean-elab",
            target: "clean-elab",
        },
    ],
    domain_root: Some("eval"),
    alternative_forms: &[],
    feature_gate: None,
}];

#[cfg(test)]
mod tests {
    use super::*;
    use clean_features::{ensure_has_example, ensure_unique_paths};

    #[test]
    fn features_are_lint_clean() {
        let descriptors: Vec<&FeatureDescriptor> = FEATURES.iter().collect();
        ensure_unique_paths(&descriptors).expect("elab descriptor paths are unique");
        for descriptor in FEATURES {
            ensure_has_example(descriptor).expect("every elab descriptor has ≥1 example");
        }
    }

    #[test]
    fn eval_has_expected_path() {
        assert_eq!(FEATURES.len(), 1);
        assert_eq!(FEATURES[0].path, &["eval"]);
    }
}
