// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Export-level filtering for persistent environment extension entries.
//!
//! Controls which extension entries are included when writing .olean files.
//! This complements [`OLeanLevel`](crate::module::OLeanLevel) (which controls
//! the file-level partitioning into `.olean` / `.olean.server` / `.olean.private`)
//! by providing fine-grained per-entry filtering within a single part.
//!
//! # Example
//!
//! ```rust
//! use clean_olean::olean_level::{ExportLevel, ExportEntriesConfig, ExportFilter};
//!
//! let config = ExportEntriesConfig {
//!     default_level: ExportLevel::Exported,
//!     overrides: [("_private_ext".to_string(), ExportLevel::Omitted)]
//!         .into_iter()
//!         .collect(),
//! };
//! let filter = ExportFilter::new(config);
//! assert!(filter.should_export("my_ext"));
//! assert!(!filter.should_export("_private_ext"));
//! ```

use std::collections::HashMap;

use crate::module::ParsedExtension;

/// Controls whether an individual extension entry is exported in .olean output.
///
/// Unlike [`OLeanLevel`](crate::module::OLeanLevel) which determines the *file*
/// a module part is written to, `ExportLevel` determines whether a specific
/// named extension entry is included at all.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[non_exhaustive]
pub enum ExportLevel {
    /// Entry is included in the exported .olean output (default).
    #[default]
    Exported,
    /// Entry is kept but marked private (not visible to downstream importers).
    Private,
    /// Entry is omitted entirely from the output.
    Omitted,
}

impl ExportLevel {
    /// Returns `true` if this level causes the entry to appear in output.
    #[must_use]
    pub fn is_visible(&self) -> bool {
        !matches!(self, ExportLevel::Omitted)
    }
}

impl std::fmt::Display for ExportLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExportLevel::Exported => write!(f, "exported"),
            ExportLevel::Private => write!(f, "private"),
            ExportLevel::Omitted => write!(f, "omitted"),
        }
    }
}

/// Configuration for which extension entries to export.
///
/// Combines a default level with per-name overrides so callers can
/// selectively include or exclude specific extensions.
#[derive(Debug, Clone)]
pub struct ExportEntriesConfig {
    /// Default level applied to extensions without an explicit override.
    pub default_level: ExportLevel,
    /// Per-extension-name overrides. Keys are extension names (e.g., `"reducibility"`).
    pub overrides: HashMap<String, ExportLevel>,
}

impl Default for ExportEntriesConfig {
    fn default() -> Self {
        default_export_config()
    }
}

/// Wraps an [`ExportEntriesConfig`] and provides filtering operations.
#[derive(Debug, Clone)]
pub struct ExportFilter {
    config: ExportEntriesConfig,
}

impl ExportFilter {
    /// Create a new filter from the given configuration.
    #[must_use]
    pub fn new(config: ExportEntriesConfig) -> Self {
        Self { config }
    }

    /// Returns `true` if the named extension should appear in the output.
    ///
    /// Checks the override map first; falls back to the default level.
    #[must_use]
    pub fn should_export(&self, name: &str) -> bool {
        self.get_level(name).is_visible()
    }

    /// Get the export level for the named extension.
    ///
    /// Looks up the override map first, then falls back to the default.
    #[must_use]
    pub fn get_level(&self, name: &str) -> ExportLevel {
        self.config
            .overrides
            .get(name)
            .copied()
            .unwrap_or(self.config.default_level)
    }

    /// Returns a reference to the underlying configuration.
    #[must_use]
    pub fn config(&self) -> &ExportEntriesConfig {
        &self.config
    }
}

/// Filter a slice of parsed extensions according to the given filter.
///
/// Returns a new `Vec` containing only the extensions whose names pass
/// the filter's `should_export` check.
///
/// # Example
///
/// ```rust
/// use clean_olean::olean_level::{ExportLevel, ExportEntriesConfig, ExportFilter, filter_exports};
/// use clean_olean::module::ParsedExtension;
///
/// let extensions = vec![
///     ParsedExtension {
///         extension_name: "reducibility".into(),
///         entries: vec![],
///         undecoded_entries: 0,
///     },
///     ParsedExtension {
///         extension_name: "_debug_info".into(),
///         entries: vec![],
///         undecoded_entries: 0,
///     },
/// ];
/// let config = ExportEntriesConfig {
///     default_level: ExportLevel::Exported,
///     overrides: [("_debug_info".to_string(), ExportLevel::Omitted)]
///         .into_iter()
///         .collect(),
/// };
/// let filter = ExportFilter::new(config);
/// let filtered = filter_exports(&extensions, &filter);
/// assert_eq!(filtered.len(), 1);
/// assert_eq!(filtered[0].extension_name, "reducibility");
/// ```
#[must_use]
pub fn filter_exports(entries: &[ParsedExtension], filter: &ExportFilter) -> Vec<ParsedExtension> {
    entries
        .iter()
        .filter(|ext| filter.should_export(&ext.extension_name))
        .cloned()
        .collect()
}

/// Returns the default export configuration.
///
/// The default exports all entries (no overrides). This matches Lean 4's
/// standard behavior where all persistent extensions are included in the
/// `.olean` output.
#[must_use]
pub fn default_export_config() -> ExportEntriesConfig {
    ExportEntriesConfig {
        default_level: ExportLevel::Exported,
        overrides: HashMap::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ── ExportLevel enum tests ──────────────────────────────────────────

    #[test]
    fn test_export_level_default_is_exported() {
        let level: ExportLevel = Default::default();
        assert_eq!(level, ExportLevel::Exported);
    }

    #[test]
    fn test_export_level_display() {
        assert_eq!(format!("{}", ExportLevel::Exported), "exported");
        assert_eq!(format!("{}", ExportLevel::Private), "private");
        assert_eq!(format!("{}", ExportLevel::Omitted), "omitted");
    }

    #[test]
    fn test_export_level_is_visible() {
        assert!(ExportLevel::Exported.is_visible());
        assert!(ExportLevel::Private.is_visible());
        assert!(!ExportLevel::Omitted.is_visible());
    }

    #[test]
    fn test_export_level_equality() {
        assert_eq!(ExportLevel::Exported, ExportLevel::Exported);
        assert_ne!(ExportLevel::Exported, ExportLevel::Private);
        assert_ne!(ExportLevel::Exported, ExportLevel::Omitted);
        assert_ne!(ExportLevel::Private, ExportLevel::Omitted);
    }

    // ── ExportFilter with overrides ─────────────────────────────────────

    #[test]
    fn test_filter_no_overrides_exports_all() {
        let config = default_export_config();
        let filter = ExportFilter::new(config);

        assert!(filter.should_export("reducibility"));
        assert!(filter.should_export("any_name"));
        assert!(filter.should_export(""));
    }

    #[test]
    fn test_filter_override_omits_entry() {
        let config = ExportEntriesConfig {
            default_level: ExportLevel::Exported,
            overrides: [("secret".to_string(), ExportLevel::Omitted)]
                .into_iter()
                .collect(),
        };
        let filter = ExportFilter::new(config);

        assert!(filter.should_export("reducibility"));
        assert!(!filter.should_export("secret"));
    }

    #[test]
    fn test_filter_override_private_is_visible() {
        let config = ExportEntriesConfig {
            default_level: ExportLevel::Exported,
            overrides: [("internal".to_string(), ExportLevel::Private)]
                .into_iter()
                .collect(),
        };
        let filter = ExportFilter::new(config);

        assert!(filter.should_export("internal"));
        assert_eq!(filter.get_level("internal"), ExportLevel::Private);
    }

    #[test]
    fn test_filter_default_omitted_with_exported_override() {
        let config = ExportEntriesConfig {
            default_level: ExportLevel::Omitted,
            overrides: [("keep_me".to_string(), ExportLevel::Exported)]
                .into_iter()
                .collect(),
        };
        let filter = ExportFilter::new(config);

        assert!(!filter.should_export("anything"));
        assert!(filter.should_export("keep_me"));
    }

    #[test]
    fn test_filter_get_level_falls_back_to_default() {
        let config = ExportEntriesConfig {
            default_level: ExportLevel::Private,
            overrides: HashMap::new(),
        };
        let filter = ExportFilter::new(config);

        assert_eq!(filter.get_level("any"), ExportLevel::Private);
    }

    #[test]
    fn test_filter_get_level_uses_override() {
        let config = ExportEntriesConfig {
            default_level: ExportLevel::Exported,
            overrides: [("special".to_string(), ExportLevel::Omitted)]
                .into_iter()
                .collect(),
        };
        let filter = ExportFilter::new(config);

        assert_eq!(filter.get_level("normal"), ExportLevel::Exported);
        assert_eq!(filter.get_level("special"), ExportLevel::Omitted);
    }

    // ── default_export_config ───────────────────────────────────────────

    #[test]
    fn test_default_export_config_exports_everything() {
        let config = default_export_config();

        assert_eq!(config.default_level, ExportLevel::Exported);
        assert!(config.overrides.is_empty());
    }

    #[test]
    fn test_export_entries_config_default_trait() {
        let config: ExportEntriesConfig = Default::default();

        assert_eq!(config.default_level, ExportLevel::Exported);
        assert!(config.overrides.is_empty());
    }

    // ── filter_exports function ─────────────────────────────────────────

    #[test]
    fn test_filter_exports_empty_entries() {
        let filter = ExportFilter::new(default_export_config());
        let result = filter_exports(&[], &filter);
        assert!(result.is_empty());
    }

    #[test]
    fn test_filter_exports_keeps_all_with_default_config() {
        let extensions = vec![
            ParsedExtension {
                extension_name: "ext_a".into(),
                entries: vec![],
                undecoded_entries: 0,
            },
            ParsedExtension {
                extension_name: "ext_b".into(),
                entries: vec![],
                undecoded_entries: 0,
            },
        ];
        let filter = ExportFilter::new(default_export_config());
        let result = filter_exports(&extensions, &filter);

        assert_eq!(result.len(), 2);
        assert_eq!(result[0].extension_name, "ext_a");
        assert_eq!(result[1].extension_name, "ext_b");
    }

    #[test]
    fn test_filter_exports_omits_matching() {
        let extensions = vec![
            ParsedExtension {
                extension_name: "keep".into(),
                entries: vec![],
                undecoded_entries: 0,
            },
            ParsedExtension {
                extension_name: "drop".into(),
                entries: vec![],
                undecoded_entries: 0,
            },
            ParsedExtension {
                extension_name: "also_keep".into(),
                entries: vec![],
                undecoded_entries: 0,
            },
        ];
        let config = ExportEntriesConfig {
            default_level: ExportLevel::Exported,
            overrides: [("drop".to_string(), ExportLevel::Omitted)]
                .into_iter()
                .collect(),
        };
        let filter = ExportFilter::new(config);
        let result = filter_exports(&extensions, &filter);

        assert_eq!(result.len(), 2);
        assert_eq!(result[0].extension_name, "keep");
        assert_eq!(result[1].extension_name, "also_keep");
    }

    #[test]
    fn test_filter_exports_mixed_levels() {
        let extensions = vec![
            ParsedExtension {
                extension_name: "public".into(),
                entries: vec![],
                undecoded_entries: 0,
            },
            ParsedExtension {
                extension_name: "internal".into(),
                entries: vec![],
                undecoded_entries: 0,
            },
            ParsedExtension {
                extension_name: "secret".into(),
                entries: vec![],
                undecoded_entries: 0,
            },
        ];
        let config = ExportEntriesConfig {
            default_level: ExportLevel::Exported,
            overrides: [
                ("internal".to_string(), ExportLevel::Private),
                ("secret".to_string(), ExportLevel::Omitted),
            ]
            .into_iter()
            .collect(),
        };
        let filter = ExportFilter::new(config);
        let result = filter_exports(&extensions, &filter);

        // Private is visible, Omitted is not
        assert_eq!(result.len(), 2);
        assert_eq!(result[0].extension_name, "public");
        assert_eq!(result[1].extension_name, "internal");
    }

    // ── ExportFilter::config accessor ───────────────────────────────────

    #[test]
    fn test_filter_config_accessor() {
        let config = ExportEntriesConfig {
            default_level: ExportLevel::Private,
            overrides: [("x".to_string(), ExportLevel::Omitted)]
                .into_iter()
                .collect(),
        };
        let filter = ExportFilter::new(config);
        let cfg = filter.config();

        assert_eq!(cfg.default_level, ExportLevel::Private);
        assert_eq!(cfg.overrides.len(), 1);
        assert_eq!(cfg.overrides["x"], ExportLevel::Omitted);
    }
}
