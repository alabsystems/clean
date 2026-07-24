// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

//! Feature descriptor types for the unified `clean` CLI index.
//!
//! Descriptors in this crate are compile-time-static data consumed by the
//! top-level `clean` binary to render `clean features`, `clean help <path>`,
//! `clean explore`, and generated docs such as `docs/CLI.md`.
//!
//! The reference data model lives in
//! `designs/2026-04-18-unified-cli-feature-index.md`, in the
//! "Feature Descriptor Model" section.

mod descriptor;
mod lint;

pub use descriptor::{
    Category, Example, FeatureDescriptor, ParseSlugError, RefKind, Reference, Stability,
};
#[cfg(feature = "serde")]
pub use descriptor::{OwnedExample, OwnedFeatureDescriptor, OwnedReference};
pub use lint::{ensure_all_examples_parseable, ensure_has_example, ensure_unique_paths, LintError};

/// Wrap clap's parse error into a `String` so callers can use
/// [`ensure_all_examples_parseable`] with a clap-derived parser.
///
/// Uses `shlex`-compatible tokenization so descriptor examples can include
/// quoted arguments (e.g. `clean eval "fun x => x"`) exactly as a user would
/// type them at the shell. Naive `split_whitespace` would treat every word
/// inside the quotes as a separate argv entry, causing examples that pass a
/// single shell-quoted string to a positional arg to fail spuriously.
#[cfg(feature = "clap-interop")]
pub fn try_parse_example<C: clap::Parser>(cmd: &str) -> Result<(), String> {
    let argv = shlex::split(cmd)
        .ok_or_else(|| format!("example cmd is not a valid shell-quoted string: {cmd}"))?;
    C::try_parse_from(argv)
        .map(|_| ())
        .map_err(|error| error.to_string())
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use super::*;

    const SAMPLE: FeatureDescriptor = FeatureDescriptor {
        path: &["check"],
        summary: "Type-check a Lean source file",
        description: "Runs the kernel type-checker for one input file.",
        category: Category::Verification,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean check foo.lean",
            what: "check one file",
        }],
        see_also: &["kernel verify"],
        references: &[Reference {
            kind: RefKind::Design,
            label: "Unified CLI design",
            target: "designs/2026-04-18-unified-cli-feature-index.md",
        }],
        domain_root: Some("check"),
        alternative_forms: &[],
        feature_gate: None,
    };

    const NO_EXAMPLES: &[Example] = &[];

    fn descriptor_with_examples(examples: &'static [Example]) -> FeatureDescriptor {
        FeatureDescriptor { examples, ..SAMPLE }
    }

    fn descriptor_with_path(path: &'static [&'static str]) -> FeatureDescriptor {
        FeatureDescriptor { path, ..SAMPLE }
    }

    #[test]
    fn test_category_slug_roundtrip() {
        for &category in Category::all() {
            assert_eq!(Category::from_str(category.as_slug()), Ok(category));
        }
    }

    #[test]
    fn test_category_from_str_unknown_returns_error() {
        assert_eq!(
            Category::from_str("nonesuch"),
            Err(ParseSlugError {
                kind: "category",
                input: "nonesuch".to_owned(),
            })
        );
    }

    #[test]
    fn test_stability_slug_roundtrip() {
        for &stability in Stability::all() {
            assert_eq!(Stability::from_str(stability.as_slug()), Ok(stability));
        }
    }

    #[test]
    fn test_stability_ordering() {
        assert!(Stability::V1 < Stability::Experimental);
    }

    #[test]
    fn test_ensure_has_example_empty_fails() {
        let descriptor = descriptor_with_examples(NO_EXAMPLES);

        assert_eq!(
            ensure_has_example(&descriptor),
            Err(LintError::NoExamples {
                path: "check".to_owned()
            })
        );
    }

    #[test]
    fn test_ensure_has_example_nonempty_passes() {
        assert_eq!(ensure_has_example(&SAMPLE), Ok(()));
    }

    #[test]
    fn test_ensure_all_examples_parseable_success() {
        assert_eq!(ensure_all_examples_parseable(&SAMPLE, |_| Ok(())), Ok(()));
    }

    #[test]
    fn test_ensure_all_examples_parseable_failure() {
        assert_eq!(
            ensure_all_examples_parseable(&SAMPLE, |_| Err(String::from("bad"))),
            Err(LintError::ExampleParseFailed {
                path: "check".to_owned(),
                index: 0,
                cmd: "clean check foo.lean",
                reason: String::from("bad"),
            })
        );
    }

    #[test]
    fn test_ensure_unique_paths_duplicate_fails() {
        let duplicate = FeatureDescriptor {
            summary: "A different summary",
            ..SAMPLE
        };

        assert_eq!(
            ensure_unique_paths(&[&SAMPLE, &duplicate]),
            Err(LintError::DuplicatePath("check".to_owned()))
        );
    }

    #[test]
    fn test_ensure_unique_paths_all_unique_passes() {
        let unique = descriptor_with_path(&["kernel", "verify"]);

        assert_eq!(ensure_unique_paths(&[&SAMPLE, &unique]), Ok(()));
    }

    #[test]
    fn test_feature_descriptor_equality_by_path() {
        let descriptor = FeatureDescriptor {
            summary: "Different summary",
            description: "Different description",
            ..SAMPLE
        };

        assert_eq!(SAMPLE, descriptor);
    }

    #[test]
    fn test_matches_search_case_insensitive() {
        let descriptor = FeatureDescriptor {
            summary: "check a file",
            ..SAMPLE
        };

        assert!(descriptor.matches_search("CHECK"));
    }

    #[test]
    fn test_matches_search_no_match() {
        assert!(!SAMPLE.matches_search("nonesuch"));
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_feature_descriptor_json_roundtrip() {
        let json = serde_json::to_string(&SAMPLE).unwrap();
        let value: serde_json::Value = serde_json::from_str(&json).unwrap();

        assert!(value["path"].is_array());
        assert_eq!(value["path"][0].as_str(), Some(SAMPLE.path[0]));
        assert_eq!(value["summary"].as_str(), Some(SAMPLE.summary));
        assert_eq!(value["description"].as_str(), Some(SAMPLE.description));
        assert_eq!(value["category"].as_str(), Some("verification"));
        assert_eq!(value["stability"].as_str(), Some("v1"));
        assert_eq!(
            value["examples"][0]["cmd"].as_str(),
            Some("clean check foo.lean")
        );
        assert_eq!(
            value["examples"][0]["what"].as_str(),
            Some("check one file")
        );
        assert_eq!(value["see_also"][0].as_str(), Some(SAMPLE.see_also[0]));
        assert_eq!(value["references"][0]["kind"].as_str(), Some("design"));
        assert_eq!(
            value["references"][0]["label"].as_str(),
            Some("Unified CLI design")
        );
        assert_eq!(
            value["references"][0]["target"].as_str(),
            Some("designs/2026-04-18-unified-cli-feature-index.md")
        );
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_owned_feature_descriptor_roundtrip() {
        let json = serde_json::to_string(&SAMPLE).expect("descriptor serializes");
        let owned: OwnedFeatureDescriptor =
            serde_json::from_str(&json).expect("owned descriptor deserializes from static output");

        let expected_path: Vec<String> = SAMPLE.path.iter().map(|s| (*s).to_owned()).collect();
        assert_eq!(owned.path, expected_path);
        assert_eq!(owned.summary, SAMPLE.summary);
        assert_eq!(owned.description, SAMPLE.description);
        assert_eq!(owned.category, SAMPLE.category);
        assert_eq!(owned.stability, SAMPLE.stability);
        assert_eq!(owned.examples.len(), SAMPLE.examples.len());
        assert_eq!(owned.examples[0].cmd, SAMPLE.examples[0].cmd);
        assert_eq!(owned.examples[0].what, SAMPLE.examples[0].what);
        assert_eq!(owned.see_also, vec![SAMPLE.see_also[0].to_owned()]);
        assert_eq!(owned.references.len(), SAMPLE.references.len());
        assert_eq!(owned.references[0].kind, SAMPLE.references[0].kind);
        assert_eq!(owned.references[0].label, SAMPLE.references[0].label);
        assert_eq!(owned.references[0].target, SAMPLE.references[0].target);
    }

    #[cfg(feature = "clap-interop")]
    #[test]
    fn test_try_parse_example_with_clap_parser() {
        #[derive(clap::Parser)]
        struct MiniCli {
            file: String,
        }

        assert_eq!(try_parse_example::<MiniCli>("clean foo.lean"), Ok(()));
    }

    // --- Phase 4/5 fields ---------------------------------------------------

    #[test]
    fn test_new_fields_defaults_on_sample() {
        // `alternative_forms` defaults to empty for the sample descriptor; the
        // other two fields have explicit values. This asserts the populated
        // shape matches what mechanical bulk population produces so we catch
        // regressions where a migration accidentally drops a default.
        assert_eq!(SAMPLE.alternative_forms, &[] as &[&str]);
        assert_eq!(SAMPLE.domain_root, Some("check"));
        assert_eq!(SAMPLE.feature_gate, None);
    }

    #[test]
    fn test_domain_root_matches_path_root_for_sample() {
        // When `domain_root` is set, it must equal `path[0]`. This matches the
        // Phase 4 grouping invariant consumed by `clean features`: every
        // descriptor with a non-None `domain_root` lives under that verb tree.
        let descriptor = SAMPLE;
        if let Some(root) = descriptor.domain_root {
            assert_eq!(
                descriptor.path[0],
                root,
                "domain_root `{root}` must match path[0] for `{}`",
                descriptor.path_display()
            );
        }
    }

    #[test]
    fn test_alternative_forms_have_valid_arity() {
        // Every alt form is a full shell invocation, so it must start with
        // `clean ` and contain at least one additional token. We exercise this
        // with a synthetic descriptor since SAMPLE has no alt forms.
        let descriptor = FeatureDescriptor {
            alternative_forms: &["clean kern verify", "clean k verify"],
            ..SAMPLE
        };
        for form in descriptor.alternative_forms {
            assert!(
                form.starts_with("clean "),
                "alt form `{form}` must start with `clean `"
            );
            // Length (in tokens) is >=2: `clean` + at least one subcommand.
            assert!(
                form.split_whitespace().count() >= 2,
                "alt form `{form}` must have at least one subcommand token"
            );
        }
    }

    #[test]
    fn test_feature_gate_is_recorded_as_static_str() {
        // Phase 5 uses `feature_gate` to produce actionable "missing feature"
        // errors. This test covers the round-trip through `FeatureDescriptor`
        // and verifies the value is preserved on update-syntax clones.
        let descriptor = FeatureDescriptor {
            feature_gate: Some("math-overlays"),
            ..SAMPLE
        };
        assert_eq!(descriptor.feature_gate, Some("math-overlays"));
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_new_fields_serialize_to_json() {
        // Phase 4/5: the three new fields must appear in the JSON output so
        // downstream tooling (`clean features --json`, docs/CLI.md generator)
        // can consume them without opting in.
        let descriptor = FeatureDescriptor {
            domain_root: Some("kernel"),
            alternative_forms: &["clean kern verify"],
            feature_gate: Some("math-overlays"),
            ..SAMPLE
        };
        let json = serde_json::to_string(&descriptor).expect("descriptor serializes");
        let value: serde_json::Value = serde_json::from_str(&json).expect("valid json");
        assert_eq!(value["domain_root"].as_str(), Some("kernel"));
        assert_eq!(
            value["alternative_forms"][0].as_str(),
            Some("clean kern verify")
        );
        assert_eq!(value["feature_gate"].as_str(), Some("math-overlays"));
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_owned_feature_descriptor_defaults_new_fields_when_missing() {
        // Legacy JSON fixtures written before Phase 4/5 may omit the three new
        // fields. The `#[serde(default)]` attributes on `OwnedFeatureDescriptor`
        // must let them round-trip without the new keys.
        let legacy_json = r#"{
            "path": ["check"],
            "summary": "legacy summary",
            "description": "legacy description",
            "category": "verification",
            "stability": "v1",
            "examples": [],
            "see_also": [],
            "references": []
        }"#;
        let owned: OwnedFeatureDescriptor =
            serde_json::from_str(legacy_json).expect("legacy JSON deserializes");
        assert_eq!(owned.domain_root, None);
        assert!(owned.alternative_forms.is_empty());
        assert_eq!(owned.feature_gate, None);
    }
}
