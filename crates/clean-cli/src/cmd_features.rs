// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean features` — flat feature index for the unified CLI.
//!
//! Part of Epic #3436 (Phase 1). Design:
//! `designs/2026-04-18-unified-cli-feature-index.md`.
//!
//! The descriptor registry (`crate::registry::all_features`) is empty in Phase
//! 1; this module renders whatever is registered today, filterable by
//! category, stability, or free-text search, with an optional JSON output for
//! tooling.

use std::io::{self, Write};
use std::str::FromStr;

use clean_features::{Category, FeatureDescriptor, Stability};

use crate::registry;

/// Hint printed when the registry is empty so first-time users know the
/// command is wired up but domain crates have not yet registered descriptors.
const EMPTY_HINT: &str = "no features registered yet — domain crates register \
into the index in Phase 2+; run `clean help` for more.";

/// Errors surfaced by `clean features`.
///
/// Kept as a local `thiserror` enum so the library entrypoint can convert
/// into `anyhow::Error` at the boundary without leaking error types up.
#[derive(Debug, thiserror::Error)]
pub(crate) enum FeaturesError {
    /// The caller supplied an unknown `--category` slug.
    #[error("unknown category `{slug}`: valid slugs are {valid}")]
    UnknownCategory {
        /// The unrecognized slug the caller supplied.
        slug: String,
        /// The comma-joined list of accepted slugs.
        valid: String,
    },
    /// The caller supplied an unknown `--stability` slug.
    #[error("unknown stability `{slug}`: valid slugs are {valid}")]
    UnknownStability {
        /// The unrecognized slug the caller supplied.
        slug: String,
        /// The comma-joined list of accepted slugs.
        valid: String,
    },
    /// Serializing descriptors to JSON failed.
    #[error("failed to serialize features as JSON: {0}")]
    Json(#[from] serde_json::Error),
    /// Writing the rendered output failed.
    #[error("failed to write output: {0}")]
    Io(#[from] io::Error),
}

fn category_slugs() -> String {
    Category::all()
        .iter()
        .map(|c| c.as_slug())
        .collect::<Vec<_>>()
        .join(", ")
}

fn stability_slugs() -> String {
    Stability::all()
        .iter()
        .map(|s| s.as_slug())
        .collect::<Vec<_>>()
        .join(", ")
}

/// Entry point for `clean features`.
///
/// The boolean `json` selects between human-readable output and a JSON array
/// suitable for tooling. Filters are applied in a fixed order: category, then
/// stability, then free-text search.
pub(crate) fn run(
    category: Option<&str>,
    stability: Option<&str>,
    search: Option<&str>,
    json: bool,
) -> Result<(), FeaturesError> {
    let category = match category {
        Some(slug) => {
            Some(
                Category::from_str(slug).map_err(|_| FeaturesError::UnknownCategory {
                    slug: slug.to_owned(),
                    valid: category_slugs(),
                })?,
            )
        }
        None => None,
    };
    let stability = match stability {
        Some(slug) => {
            Some(
                Stability::from_str(slug).map_err(|_| FeaturesError::UnknownStability {
                    slug: slug.to_owned(),
                    valid: stability_slugs(),
                })?,
            )
        }
        None => None,
    };

    let descriptors = filter_descriptors(registry::all_features(), category, stability, search);

    let stdout = io::stdout();
    let mut out = stdout.lock();
    if json {
        let json_text = serde_json::to_string_pretty(&descriptors)?;
        writeln!(out, "{json_text}")?;
    } else {
        render_human(&mut out, &descriptors)?;
    }

    Ok(())
}

/// Filter descriptors according to the provided predicates.
///
/// Exposed to the crate so unit tests can drive it without spawning a subprocess.
pub(crate) fn filter_descriptors(
    descriptors: Vec<&'static FeatureDescriptor>,
    category: Option<Category>,
    stability: Option<Stability>,
    search: Option<&str>,
) -> Vec<&'static FeatureDescriptor> {
    descriptors
        .into_iter()
        .filter(|d| category.is_none_or(|c| d.category == c))
        .filter(|d| stability.is_none_or(|s| d.stability == s))
        .filter(|d| search.is_none_or(|q| d.matches_search(q)))
        .collect()
}

/// Render the human-readable index grouped by category then stability.
fn render_human(
    out: &mut impl Write,
    descriptors: &[&'static FeatureDescriptor],
) -> io::Result<()> {
    if descriptors.is_empty() {
        writeln!(out, "{EMPTY_HINT}")?;
        return Ok(());
    }

    for &category in Category::all() {
        let in_cat: Vec<_> = descriptors
            .iter()
            .copied()
            .filter(|d| d.category == category)
            .collect();
        if in_cat.is_empty() {
            continue;
        }

        writeln!(out, "# {}", category.as_slug())?;
        for &stability in Stability::all() {
            let in_stab: Vec<_> = in_cat
                .iter()
                .copied()
                .filter(|d| d.stability == stability)
                .collect();
            if in_stab.is_empty() {
                continue;
            }
            writeln!(out, "  ## {}", stability.as_slug())?;
            for d in in_stab {
                writeln!(out, "    {:<32}  {}", d.path_display(), d.summary)?;
            }
        }
        writeln!(out)?;
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_features::{Example, RefKind, Reference};

    const CHECK: FeatureDescriptor = FeatureDescriptor {
        path: &["check"],
        summary: "Type-check a file",
        description: "Runs the kernel.",
        category: Category::Verification,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean check foo.lean",
            what: "one file",
        }],
        see_also: &[],
        references: &[Reference {
            kind: RefKind::Design,
            label: "design",
            target: "designs/x.md",
        }],
        domain_root: Some("check"),
        alternative_forms: &[],
        feature_gate: None,
    };

    const BUILD_DEV: FeatureDescriptor = FeatureDescriptor {
        path: &["bench", "run"],
        summary: "Run benchmark suite",
        description: "Benchmark description.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[Example {
            cmd: "clean bench run",
            what: "run bench",
        }],
        see_also: &[],
        references: &[],
        domain_root: Some("bench"),
        alternative_forms: &[],
        feature_gate: None,
    };

    #[test]
    fn test_filter_descriptors_no_filters_returns_all() {
        let out = filter_descriptors(vec![&CHECK, &BUILD_DEV], None, None, None);
        assert_eq!(out.len(), 2);
    }

    #[test]
    fn test_filter_descriptors_by_category() {
        let out = filter_descriptors(
            vec![&CHECK, &BUILD_DEV],
            Some(Category::Verification),
            None,
            None,
        );
        assert_eq!(out.len(), 1);
        assert_eq!(out[0].path, &["check"]);
    }

    #[test]
    fn test_filter_descriptors_by_stability() {
        let out = filter_descriptors(
            vec![&CHECK, &BUILD_DEV],
            None,
            Some(Stability::Experimental),
            None,
        );
        assert_eq!(out.len(), 1);
        assert_eq!(out[0].path, &["bench", "run"]);
    }

    #[test]
    fn test_filter_descriptors_by_search_case_insensitive() {
        let out = filter_descriptors(vec![&CHECK, &BUILD_DEV], None, None, Some("BENCHMARK"));
        assert_eq!(out.len(), 1);
        assert_eq!(out[0].path, &["bench", "run"]);
    }

    #[test]
    fn test_filter_descriptors_empty_input_stays_empty() {
        let out = filter_descriptors(Vec::new(), None, None, None);
        assert!(out.is_empty());
    }

    #[test]
    fn test_render_human_empty_prints_hint() {
        let mut buf: Vec<u8> = Vec::new();
        render_human(&mut buf, &[]).expect("render empty");
        let text = String::from_utf8(buf).expect("utf8");
        assert!(text.contains("no features registered yet"));
    }

    #[test]
    fn test_render_human_groups_by_category_then_stability() {
        let mut buf: Vec<u8> = Vec::new();
        render_human(&mut buf, &[&CHECK, &BUILD_DEV]).expect("render");
        let text = String::from_utf8(buf).expect("utf8");

        let verification_idx = text.find("# verification").expect("verification header");
        let dev_idx = text.find("# dev").expect("dev header");
        assert!(
            verification_idx < dev_idx,
            "categories appear in declared order"
        );

        assert!(text.contains("check"), "check path present");
        assert!(text.contains("bench run"), "bench run path present");
        assert!(text.contains("v1"));
        assert!(text.contains("experimental"));
    }

    #[test]
    fn test_run_unknown_category_is_typed_error() {
        let err = run(Some("nonesuch"), None, None, false).expect_err("should fail");
        assert!(matches!(err, FeaturesError::UnknownCategory { .. }));
    }

    #[test]
    fn test_run_unknown_stability_is_typed_error() {
        let err = run(None, Some("bogus"), None, false).expect_err("should fail");
        assert!(matches!(err, FeaturesError::UnknownStability { .. }));
    }
}
