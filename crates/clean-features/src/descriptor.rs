// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use core::hash::{Hash, Hasher};
use core::str::FromStr;

const ALL_CATEGORIES: &[Category] = &[
    Category::Verification,
    Category::Import,
    Category::Build,
    Category::Proof,
    Category::Kernel,
    Category::Meta,
    Category::Dev,
    Category::OperatorTools,
];

const ALL_STABILITIES: &[Stability] = &[
    Stability::V1,
    Stability::Usable,
    Stability::Building,
    Stability::Experimental,
];

/// Top-level grouping for a feature.
///
/// Controls the section in `clean features` and the branch in the explore TUI
/// tree.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "kebab-case"))]
pub enum Category {
    /// Kernel type-checking and semantic verification workflows.
    Verification,
    /// Import and translation pipelines.
    Import,
    /// Build and compilation workflows.
    Build,
    /// Proof search and tactic-oriented features.
    Proof,
    /// Kernel internals and soundness-oriented features.
    Kernel,
    /// CLI self-description features such as `features` and `help`.
    Meta,
    /// Developer tooling, benchmarking, and service workflows.
    Dev,
    /// Operator-only standalone tools that are documented in the feature index
    /// but are NOT wired into the top-level `clean` clap subcommand tree.
    ///
    /// Descriptors under this category describe binaries that callers invoke
    /// directly (e.g. `cargo run --locked -p clean-mathverse --release --bin mathverse_convert -- …`).
    /// They participate in `clean features` discovery and `clean help <path>`
    /// output but do NOT require a matching clap subcommand — the feature
    /// coverage drift test skips the clap-routability check for this category.
    ///
    /// Added in Epic #3436 Phase 3.5 (see #3513) so operator tools like
    /// `mathverse_convert` and `mathverse_shard` are discoverable without forcing
    /// absorption (which would add a third entry point with no user benefit and
    /// bloat the default `clean` binary).
    OperatorTools,
}

impl Category {
    /// Return the lowercase slug used by `--category <value>` filters.
    #[must_use]
    pub const fn as_slug(self) -> &'static str {
        match self {
            Self::Verification => "verification",
            Self::Import => "import",
            Self::Build => "build",
            Self::Proof => "proof",
            Self::Kernel => "kernel",
            Self::Meta => "meta",
            Self::Dev => "dev",
            Self::OperatorTools => "operator-tools",
        }
    }

    /// Return all known categories in declaration order.
    #[must_use]
    pub const fn all() -> &'static [Self] {
        ALL_CATEGORIES
    }
}

impl FromStr for Category {
    type Err = ParseSlugError;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        match input {
            "verification" => Ok(Self::Verification),
            "import" => Ok(Self::Import),
            "build" => Ok(Self::Build),
            "proof" => Ok(Self::Proof),
            "kernel" => Ok(Self::Kernel),
            "meta" => Ok(Self::Meta),
            "dev" => Ok(Self::Dev),
            "operator-tools" => Ok(Self::OperatorTools),
            _ => Err(ParseSlugError {
                kind: "category",
                input: input.to_owned(),
            }),
        }
    }
}

/// User-facing stability marker for a feature.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "kebab-case"))]
pub enum Stability {
    /// Stable, public surface that is covered by semver.
    V1,
    /// Works for intended cases, but the interface is not yet semver-stable.
    Usable,
    /// Under active development with partial coverage.
    Building,
    /// Research prototype that may change without notice.
    Experimental,
}

impl Stability {
    /// Return the lowercase slug used by stability filters and JSON output.
    #[must_use]
    pub const fn as_slug(self) -> &'static str {
        match self {
            Self::V1 => "v1",
            Self::Usable => "usable",
            Self::Building => "building",
            Self::Experimental => "experimental",
        }
    }

    /// Return all known stability levels in declaration order.
    #[must_use]
    pub const fn all() -> &'static [Self] {
        ALL_STABILITIES
    }
}

impl FromStr for Stability {
    type Err = ParseSlugError;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        match input {
            "v1" => Ok(Self::V1),
            "usable" => Ok(Self::Usable),
            "building" => Ok(Self::Building),
            "experimental" => Ok(Self::Experimental),
            _ => Err(ParseSlugError {
                kind: "stability",
                input: input.to_owned(),
            }),
        }
    }
}

/// A concrete invocation of a feature.
///
/// The example command must parse under the consuming clap parser.
///
/// Only `Serialize` is derived under the `serde` feature because the fields
/// borrow `'static` data from the compiled binary. See [`OwnedExample`] for
/// a `Deserialize` counterpart.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct Example {
    /// Command as a user types it, for example `"clean check foo.lean"`.
    pub cmd: &'static str,
    /// One-line description of what this example demonstrates.
    pub what: &'static str,
}

/// Owned counterpart of [`Example`] used for `Deserialize` round-trips.
///
/// Descriptors in the compiled binary are static data; when callers need to
/// load descriptors from a JSON file (for example in tests, documentation
/// generators, or external tooling), they deserialize into
/// [`OwnedFeatureDescriptor`] / [`OwnedExample`] / [`OwnedReference`] which
/// own their strings on the heap.
#[cfg(feature = "serde")]
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct OwnedExample {
    /// Command as a user would type it.
    pub cmd: String,
    /// One-line description of what this example demonstrates.
    pub what: String,
}

/// What sort of supporting material a [`Reference`] points to.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "kebab-case"))]
pub enum RefKind {
    /// A design document, typically under `designs/`.
    Design,
    /// A GitHub issue or other issue tracker identifier.
    Issue,
    /// A documentation page such as a markdown file under `docs/`.
    Doc,
    /// A workspace crate name.
    Crate,
}

/// Pointer from a feature descriptor to supporting material.
///
/// Only `Serialize` is derived under the `serde` feature. See
/// [`OwnedReference`] for the deserialize counterpart.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct Reference {
    /// What sort of material this reference points to.
    pub kind: RefKind,
    /// Human-readable label for the reference.
    pub label: &'static str,
    /// URL, repo path, issue number, or crate name.
    pub target: &'static str,
}

/// Owned counterpart of [`Reference`] used for `Deserialize` round-trips.
#[cfg(feature = "serde")]
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct OwnedReference {
    /// What sort of material this reference points to.
    pub kind: RefKind,
    /// Human-readable label for the reference.
    pub label: String,
    /// URL, repo path, issue number, or crate name.
    pub target: String,
}

/// Single invocable feature of the `clean` CLI.
///
/// One descriptor exists per command path. All fields use `&'static` data so
/// per-crate descriptor arrays can be declared as `const` or `static` values.
///
/// Only `Serialize` is derived under the `serde` feature. See
/// [`OwnedFeatureDescriptor`] for the deserialize counterpart.
#[derive(Debug, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct FeatureDescriptor {
    /// Command path as a sequence of subcommand segments, for example
    /// `&["kernel", "verify"]`. The displayed form is produced by
    /// [`FeatureDescriptor::path_display`].
    pub path: &'static [&'static str],
    /// One-line description shown in `clean features`.
    pub summary: &'static str,
    /// Long-form markdown rendered by `clean help <path>`.
    pub description: &'static str,
    /// Top-level grouping for the feature.
    pub category: Category,
    /// User-facing stability marker.
    pub stability: Stability,
    /// Concrete invocations that demonstrate the feature.
    pub examples: &'static [Example],
    /// Other feature paths the user likely wants next. Each entry is the
    /// space-joined form of another descriptor's `path` (e.g. `"kernel verify"`).
    pub see_also: &'static [&'static str],
    /// Supporting materials such as design docs, issues, and crate docs.
    pub references: &'static [Reference],
    /// Top-level verb this descriptor lives under (e.g. `"kernel"` for
    /// `kernel.verify`). Used by Phase 4 of Epic #3436 to group `clean
    /// features` output by verb tree. When `Some(root)`, `path[0]` must equal
    /// `root`; `None` opts out of domain-root grouping.
    ///
    /// Default is `None` so pre-Phase-4 descriptor literals continue to
    /// compile without change.
    pub domain_root: Option<&'static str>,
    /// Alias command forms for shortened or alternate invocations (e.g.
    /// `["clean kern verify", "clean k verify"]`). Each entry is a full
    /// shell-quoted command as a user would type it, including the `clean`
    /// prefix. Used by Phase 5 of Epic #3436 to surface abbreviations in
    /// `clean help <path>` and to drive "did you mean" resolution.
    ///
    /// Default is `&[]` (no aliases).
    pub alternative_forms: &'static [&'static str],
    /// Cargo feature flag the descriptor is gated behind (e.g.
    /// `"carcara-verify"`, `"math-overlays"`). Used by Phase 5 of Epic #3436
    /// to produce actionable missing-feature messages and to filter the
    /// feature index when a build was compiled without the gate.
    ///
    /// Default is `None` (feature is unconditionally available).
    pub feature_gate: Option<&'static str>,
}

/// Owned counterpart of [`FeatureDescriptor`] used for `Deserialize`
/// round-trips.
///
/// The static [`FeatureDescriptor`] uses `&'static` fields so descriptors can
/// live in `const` arrays; `serde::Deserialize` cannot produce `'static`
/// borrows from heap data. Callers that need to load descriptors at runtime
/// (for example, a test harness reading a JSON fixture) deserialize into this
/// owned type.
#[cfg(feature = "serde")]
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct OwnedFeatureDescriptor {
    /// Command path as a sequence of subcommand segments.
    pub path: Vec<String>,
    /// One-line description shown in `clean features`.
    pub summary: String,
    /// Long-form markdown rendered by `clean help <path>`.
    pub description: String,
    /// Top-level grouping for the feature.
    pub category: Category,
    /// User-facing stability marker.
    pub stability: Stability,
    /// Concrete invocations that demonstrate the feature.
    pub examples: Vec<OwnedExample>,
    /// Other feature paths the user likely wants next (space-joined form).
    pub see_also: Vec<String>,
    /// Supporting materials such as design docs, issues, and crate docs.
    pub references: Vec<OwnedReference>,
    /// Top-level verb this descriptor lives under. Mirrors
    /// [`FeatureDescriptor::domain_root`]. Defaults to `None` so JSON
    /// fixtures produced before Phase 4 continue to deserialize.
    #[serde(default)]
    pub domain_root: Option<String>,
    /// Alias command forms for shortened or alternate invocations. Mirrors
    /// [`FeatureDescriptor::alternative_forms`]. Defaults to an empty vec so
    /// JSON fixtures produced before Phase 5 continue to deserialize.
    #[serde(default)]
    pub alternative_forms: Vec<String>,
    /// Cargo feature flag the descriptor is gated behind. Mirrors
    /// [`FeatureDescriptor::feature_gate`]. Defaults to `None`.
    #[serde(default)]
    pub feature_gate: Option<String>,
}

impl FeatureDescriptor {
    /// Return the command path joined by single spaces, e.g. `"kernel verify"`.
    ///
    /// This is the user-facing form used by `clean help <path>`, by entries
    /// in `see_also`, and by the case-insensitive search in
    /// [`Self::matches_search`].
    #[must_use]
    pub fn path_display(&self) -> String {
        self.path.join(" ")
    }

    /// Return whether `query` matches the descriptor's path, summary, or
    /// description using a case-insensitive substring search.
    #[must_use]
    pub fn matches_search(&self, query: &str) -> bool {
        let needle = query.to_ascii_lowercase();
        if self.path_display().to_ascii_lowercase().contains(&needle) {
            return true;
        }
        [self.summary, self.description]
            .into_iter()
            .any(|field| field.to_ascii_lowercase().contains(&needle))
    }
}

impl PartialEq for FeatureDescriptor {
    fn eq(&self, other: &Self) -> bool {
        self.path == other.path
    }
}

impl Eq for FeatureDescriptor {}

impl Hash for FeatureDescriptor {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.path.hash(state);
    }
}

/// Error returned when a category or stability slug is not recognized.
#[derive(Debug, thiserror::Error, PartialEq, Eq)]
#[error("unknown {kind} slug: `{input}`")]
pub struct ParseSlugError {
    /// The type of slug that was being parsed.
    pub kind: &'static str,
    /// The unrecognized user input.
    pub input: String,
}
