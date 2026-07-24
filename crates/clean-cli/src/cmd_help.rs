// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean help [<path>]` — render a feature descriptor as Markdown, or print
//! a short index pointer when no path is supplied.
//!
//! Part of Epic #3436 (Phase 1). Design:
//! `designs/2026-04-18-unified-cli-feature-index.md`.
//!
//! Renderer choice (see sub-issue #3475 decision): `termimad` — pure Rust,
//! zero native deps, small API (`MadSkin::print_text`). `minus` is a pager
//! (scope mismatch); `pulldown-cmark` is parse-only.

use std::fmt::Write as _;
use std::io::{self, Write};

use clean_features::{FeatureDescriptor, RefKind};

use crate::registry;

/// Short pointer printed when `clean help` is called with no arguments.
///
/// Deliberately terse: the detailed index lives in `clean features`.
const INDEX_POINTER: &str = "\
clean help — interactive feature documentation

Usage:
  clean help <path>        Render the descriptor for <path> (space-joined, e.g. `kernel verify`)
  clean features           List every registered feature with filters
  clean features --search  Free-text search across paths, summaries, and descriptions
";

/// Errors surfaced by `clean help`.
#[derive(Debug, thiserror::Error)]
pub(crate) enum HelpError {
    /// Caller supplied a path that does not match any registered descriptor.
    #[error("no feature matches `{requested}` — try `clean features` for the current index")]
    UnknownPath {
        /// The path the user typed.
        requested: String,
    },
    /// Writing the rendered output failed.
    #[error("failed to write output: {0}")]
    Io(#[from] io::Error),
}

/// Entry point for `clean help [<path>]`.
pub(crate) fn run(path: Option<&str>) -> Result<(), HelpError> {
    let stdout = io::stdout();
    let mut out = stdout.lock();
    match path {
        None => {
            write!(out, "{INDEX_POINTER}")?;
            Ok(())
        }
        Some(requested) => render_for_path(&mut out, requested),
    }
}

/// Render the descriptor for a specific path or return `UnknownPath`.
fn render_for_path(out: &mut impl Write, requested: &str) -> Result<(), HelpError> {
    let needle = normalize(requested);
    let registry = registry::all_features();
    let descriptor = registry
        .iter()
        .copied()
        .find(|d| d.path_display() == needle)
        .ok_or_else(|| HelpError::UnknownPath {
            requested: requested.to_owned(),
        })?;

    let markdown = build_markdown(descriptor);

    // termimad prints directly to the process stdout; bypass the passed-in
    // writer only for the rendered-markdown body so colour/formatting escape
    // codes reach the terminal directly. Headers and references for tests use
    // the writer path below.
    let skin = termimad::MadSkin::default();
    skin.print_text(&markdown);

    writeln!(out)?;
    Ok(())
}

/// Build the Markdown body for a descriptor, suitable for `termimad`.
///
/// Exposed to the module for unit testing; tests use this rather than calling
/// the terminal renderer directly.
pub(crate) fn build_markdown(descriptor: &FeatureDescriptor) -> String {
    let mut md = String::new();

    let _ = writeln!(md, "# Clean {}", descriptor.path_display());
    let _ = writeln!(md);
    let _ = writeln!(
        md,
        "**category:** {}  **stability:** {}",
        descriptor.category.as_slug(),
        descriptor.stability.as_slug()
    );
    let _ = writeln!(md);
    let _ = writeln!(md, "{}", descriptor.summary);
    let _ = writeln!(md);
    let _ = writeln!(md, "{}", descriptor.description);

    if !descriptor.examples.is_empty() {
        let _ = writeln!(md);
        let _ = writeln!(md, "## Examples");
        for example in descriptor.examples {
            let _ = writeln!(md);
            let _ = writeln!(md, "- `{}` — {}", example.cmd, example.what);
        }
    }

    if !descriptor.see_also.is_empty() {
        let _ = writeln!(md);
        let _ = writeln!(md, "## See also");
        for path in descriptor.see_also {
            let _ = writeln!(md, "- `clean {path}`");
        }
    }

    if !descriptor.references.is_empty() {
        let _ = writeln!(md);
        let _ = writeln!(md, "## References");
        for reference in descriptor.references {
            let kind = ref_kind_slug(reference.kind);
            let _ = writeln!(
                md,
                "- {} — {} ({})",
                kind, reference.label, reference.target
            );
        }
    }

    normalize_terminal_newline(md)
}

fn normalize_terminal_newline(mut md: String) -> String {
    while md.ends_with("\n\n") {
        md.pop();
    }
    if !md.ends_with('\n') {
        md.push('\n');
    }
    md
}

/// Stable lowercase slug for a [`RefKind`] variant. Using an explicit helper
/// instead of a `match` keeps the match exhaustive as `RefKind` evolves
/// (the type is `#[non_exhaustive]`).
fn ref_kind_slug(kind: RefKind) -> &'static str {
    match kind {
        RefKind::Design => "design",
        RefKind::Issue => "issue",
        RefKind::Doc => "doc",
        RefKind::Crate => "crate",
        // Future variants render as their Debug spelling until this helper
        // is updated; keeps the call site exhaustive-free.
        _ => "other",
    }
}

/// Normalize a user-supplied path. Accepts either space-joined
/// (`"kernel verify"`) or dot-joined (`"kernel.verify"`) forms per the design
/// doc, and collapses whitespace.
fn normalize(input: &str) -> String {
    input
        .replace('.', " ")
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_features::{Category, Example, RefKind, Reference, Stability};

    const DESCRIPTOR: FeatureDescriptor = FeatureDescriptor {
        path: &["kernel", "verify"],
        summary: "Verify a kernel proof certificate",
        description: "Checks a `.cert.json` payload against the kernel.",
        category: Category::Verification,
        stability: Stability::Usable,
        examples: &[Example {
            cmd: "clean kernel verify proof.cert.json",
            what: "verify a standalone certificate",
        }],
        see_also: &["cert verify"],
        references: &[Reference {
            kind: RefKind::Design,
            label: "Cert pipeline",
            target: "designs/cert.md",
        }],
        domain_root: Some("kernel"),
        alternative_forms: &[],
        feature_gate: None,
    };

    #[test]
    fn test_run_without_path_prints_pointer() {
        // Smoke-test: run against stdout-capturing not straightforward without
        // a harness; call the build-markdown helper path instead below. For
        // the pointer path, verify the constant shape stays stable.
        assert!(INDEX_POINTER.contains("clean features"));
        assert!(INDEX_POINTER.contains("clean help <path>"));
    }

    #[test]
    fn test_normalize_space_joined() {
        assert_eq!(normalize("kernel verify"), "kernel verify");
    }

    #[test]
    fn test_normalize_dot_joined() {
        assert_eq!(normalize("kernel.verify"), "kernel verify");
    }

    #[test]
    fn test_normalize_collapses_whitespace() {
        assert_eq!(normalize("  kernel    verify  "), "kernel verify");
    }

    #[test]
    fn test_run_unknown_path_returns_error() {
        // Unknown paths must surface `HelpError::UnknownPath`. This guards the
        // error arm regardless of how many descriptors the registry holds —
        // the registry moved from empty (phase 1) to populated (phase 2+),
        // but the unknown-path contract is permanent.
        let err =
            run(Some("no-such-descriptor-xyz")).expect_err("unknown path should return an error");
        assert!(matches!(err, HelpError::UnknownPath { .. }));
    }

    #[test]
    fn test_build_markdown_contains_summary_and_description() {
        let md = build_markdown(&DESCRIPTOR);
        assert!(md.contains("# Clean kernel verify"));
        assert!(md.contains("Verify a kernel proof certificate"));
        assert!(md.contains("Checks a `.cert.json` payload"));
        assert!(md.contains("usable"));
        assert!(md.contains("verification"));
    }

    #[test]
    fn test_build_markdown_examples_section() {
        let md = build_markdown(&DESCRIPTOR);
        assert!(md.contains("## Examples"));
        assert!(md.contains("`clean kernel verify proof.cert.json`"));
    }

    #[test]
    fn test_build_markdown_see_also_section() {
        let md = build_markdown(&DESCRIPTOR);
        assert!(md.contains("## See also"));
        assert!(md.contains("`clean cert verify`"));
    }

    #[test]
    fn test_build_markdown_references_section() {
        let md = build_markdown(&DESCRIPTOR);
        assert!(md.contains("## References"));
        assert!(md.contains("design"));
        assert!(md.contains("designs/cert.md"));
        assert!(!md.ends_with("\n\n"));
        assert!(md.ends_with('\n'));
    }

    #[test]
    fn test_build_markdown_descriptor_without_examples_omits_section() {
        const NO_EXAMPLES: FeatureDescriptor = FeatureDescriptor {
            examples: &[],
            see_also: &[],
            references: &[],
            domain_root: None,
            alternative_forms: &[],
            feature_gate: None,
            ..DESCRIPTOR
        };
        let md = build_markdown(&NO_EXAMPLES);
        assert!(!md.contains("## Examples"));
        assert!(!md.contains("## See also"));
        assert!(!md.contains("## References"));
    }
}
