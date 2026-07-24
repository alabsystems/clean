// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended Lean 4 compatibility infrastructure for elaboration-time shims.

use crate::error::ElabError;
use clean_kernel::name::Name;
use clean_kernel::Expr;
use hashbrown::HashMap;
use std::fmt;
use thiserror::Error;

const DEFAULT_TARGET_VERSION: Lean4Version = Lean4Version::new(4, 13, 0);
const OLEAN_MAGIC_PREFIX: u32 = u32::from_le_bytes(*b"olea");

#[derive(Debug, Error)]
pub(crate) enum CompatLayerError {
    #[error("invalid Lean 4 version `{input}`; expected `major.minor.patch`")]
    InvalidVersionFormat { input: String },
    #[error("invalid {component} component in Lean 4 version `{input}`")]
    InvalidVersionComponent {
        input: String,
        component: &'static str,
        #[source]
        source: std::num::ParseIntError,
    },
    #[error("`.olean` header too short: expected at least 8 bytes, got {len}")]
    OleanHeaderTooShort { len: usize },
    #[error("invalid `.olean` magic prefix 0x{found:08x}")]
    InvalidOleanMagic { found: u32 },
}

impl From<CompatLayerError> for ElabError {
    fn from(err: CompatLayerError) -> Self {
        ElabError::ParseError(err.to_string())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Lean4Version {
    pub(crate) major: u32,
    pub(crate) minor: u32,
    pub(crate) patch: u32,
}

impl Lean4Version {
    #[must_use]
    pub(crate) const fn new(major: u32, minor: u32, patch: u32) -> Self {
        Self {
            major,
            minor,
            patch,
        }
    }

    pub(crate) fn parse(input: &str) -> Result<Self, ElabError> {
        let trimmed = input.trim();
        let components: Vec<_> = trimmed.split('.').collect();
        if components.len() != 3 || components.iter().any(|part| part.is_empty()) {
            return Err(CompatLayerError::InvalidVersionFormat {
                input: input.to_owned(),
            }
            .into());
        }

        let major = parse_component(input, "major", components[0])?;
        let minor = parse_component(input, "minor", components[1])?;
        let patch = parse_component(input, "patch", components[2])?;
        Ok(Self::new(major, minor, patch))
    }
}

impl fmt::Display for Lean4Version {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}.{}", self.major, self.minor, self.patch)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CompatConfig {
    pub(crate) target_version: Lean4Version,
    pub(crate) warn_deprecated: bool,
    pub(crate) allow_legacy_syntax: bool,
    pub(crate) strict_universe_check: bool,
}

impl Default for CompatConfig {
    fn default() -> Self {
        Self {
            target_version: DEFAULT_TARGET_VERSION,
            warn_deprecated: true,
            allow_legacy_syntax: true,
            strict_universe_check: false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum CompatTransform {
    RewriteMatchSyntax,
    InsertDoReturn,
    LegacyStructureSyntax,
    DeprecatedTacticAlias { old: String, new: String },
    UniverseAnnotation,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DeprecatedWarning {
    pub(crate) feature: String,
    pub(crate) deprecated_in: Lean4Version,
    pub(crate) replacement: Option<String>,
    pub(crate) removal_version: Option<Lean4Version>,
}

impl fmt::Display for DeprecatedWarning {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "feature `{}` was deprecated in {}",
            self.feature, self.deprecated_in
        )?;
        if let Some(replacement) = &self.replacement {
            write!(f, "; use `{replacement}` instead")?;
        }
        if let Some(removal_version) = self.removal_version {
            write!(f, "; scheduled for removal in {removal_version}")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Default)]
pub(crate) struct CompatLayer {
    pub(crate) transforms: Vec<(Lean4Version, CompatTransform)>,
    pub(crate) deprecated_features: Vec<DeprecatedWarning>,
    pub(crate) tactic_aliases: HashMap<String, (Lean4Version, String)>,
}

impl CompatLayer {
    pub(crate) fn register_transform(&mut self, version: Lean4Version, transform: CompatTransform) {
        self.transforms.push((version, transform));
    }

    pub(crate) fn apply_transforms(
        &self,
        expr: &Expr,
        config: &CompatConfig,
    ) -> Result<Expr, ElabError> {
        let _enabled_transform_count = self
            .transforms
            .iter()
            .filter(|(version, transform)| {
                *version <= config.target_version && transform_enabled(transform, config)
            })
            .count();
        Ok(expr.clone())
    }

    #[must_use]
    pub(crate) fn check_deprecated(
        &self,
        name: &Name,
        config: &CompatConfig,
    ) -> Option<DeprecatedWarning> {
        if !config.warn_deprecated {
            return None;
        }

        let surface_name = name.to_string();
        self.deprecated_features
            .iter()
            .find(|warning| {
                warning.feature == surface_name && warning.deprecated_in <= config.target_version
            })
            .cloned()
    }

    #[must_use]
    pub(crate) fn translate_tactic_name(
        &self,
        name: &str,
        version: &Lean4Version,
    ) -> Option<String> {
        self.tactic_aliases
            .get(name)
            .and_then(|(alias_version, new_name)| {
                (version <= alias_version).then(|| new_name.clone())
            })
    }
}

#[must_use]
pub(crate) fn default_compat_layer() -> CompatLayer {
    let mut layer = CompatLayer::default();
    populate_default_transforms(&mut layer);
    populate_default_tactic_aliases(&mut layer);
    populate_default_deprecations(&mut layer);
    layer
}

/// Register built-in compatibility transforms.
fn populate_default_transforms(layer: &mut CompatLayer) {
    let v4_0_0 = Lean4Version::new(4, 0, 0);
    let v4_1_0 = Lean4Version::new(4, 1, 0);
    let v4_2_0 = Lean4Version::new(4, 2, 0);
    let v4_3_0 = Lean4Version::new(4, 3, 0);

    layer.register_transform(v4_0_0, CompatTransform::RewriteMatchSyntax);
    layer.register_transform(v4_1_0, CompatTransform::InsertDoReturn);
    layer.register_transform(v4_2_0, CompatTransform::LegacyStructureSyntax);
    layer.register_transform(v4_0_0, CompatTransform::UniverseAnnotation);
    layer.register_transform(
        v4_1_0,
        CompatTransform::DeprecatedTacticAlias {
            old: "squeeze_simp".to_owned(),
            new: "simp?".to_owned(),
        },
    );
    layer.register_transform(
        v4_3_0,
        CompatTransform::DeprecatedTacticAlias {
            old: "library_search".to_owned(),
            new: "exact?".to_owned(),
        },
    );
    layer.register_transform(
        v4_3_0,
        CompatTransform::DeprecatedTacticAlias {
            old: "suggest".to_owned(),
            new: "exact?".to_owned(),
        },
    );
    layer.register_transform(
        v4_2_0,
        CompatTransform::DeprecatedTacticAlias {
            old: "tauto".to_owned(),
            new: "omega".to_owned(),
        },
    );
}

/// Register built-in tactic name aliases.
fn populate_default_tactic_aliases(layer: &mut CompatLayer) {
    let v4_0_0 = Lean4Version::new(4, 0, 0);
    let v4_1_0 = Lean4Version::new(4, 1, 0);
    let v4_2_0 = Lean4Version::new(4, 2, 0);
    let v4_3_0 = Lean4Version::new(4, 3, 0);

    register_tactic_alias(layer, "squeeze_simp", v4_1_0, "simp?");
    register_tactic_alias(layer, "library_search", v4_3_0, "exact?");
    register_tactic_alias(layer, "suggest", v4_3_0, "exact?");
    register_tactic_alias(layer, "ring_nf", v4_0_0, "ring");
    register_tactic_alias(layer, "dec_trivial", v4_0_0, "decide");
    register_tactic_alias(layer, "obviously", v4_0_0, "decide");
    register_tactic_alias(layer, "tauto", v4_2_0, "omega");
}

/// Register built-in deprecation warnings.
fn populate_default_deprecations(layer: &mut CompatLayer) {
    let v4_0_0 = Lean4Version::new(4, 0, 0);
    let v4_1_0 = Lean4Version::new(4, 1, 0);
    let v4_2_0 = Lean4Version::new(4, 2, 0);
    let v4_3_0 = Lean4Version::new(4, 3, 0);
    let v4_8_0 = Lean4Version::new(4, 8, 0);
    let v5_0_0 = Lean4Version::new(5, 0, 0);

    let w = &mut layer.deprecated_features;
    push_warning(
        w,
        "match",
        v4_0_0,
        Some("match ... with | pattern => result"),
        None,
    );
    push_warning(
        w,
        "do",
        v4_1_0,
        Some("structured `do` blocks with explicit `return` placement"),
        None,
    );
    push_warning(
        w,
        "structure",
        v4_2_0,
        Some("modern structure field syntax"),
        None,
    );
    push_warning(w, "squeeze_simp", v4_1_0, Some("simp?"), Some(v5_0_0));
    push_warning(w, "library_search", v4_3_0, Some("exact?"), Some(v5_0_0));
    push_warning(w, "suggest", v4_3_0, Some("exact?"), Some(v5_0_0));
    push_warning(w, "tauto", v4_2_0, Some("omega"), Some(v4_8_0));
}

pub(crate) fn detect_lean4_version(olean_header: &[u8]) -> Result<Lean4Version, ElabError> {
    if olean_header.len() < 8 {
        return Err(CompatLayerError::OleanHeaderTooShort {
            len: olean_header.len(),
        }
        .into());
    }

    let magic = u32::from_le_bytes(olean_header[0..4].try_into().expect("slice length checked"));
    if magic != OLEAN_MAGIC_PREFIX {
        return Err(CompatLayerError::InvalidOleanMagic { found: magic }.into());
    }

    let raw_version =
        u32::from_le_bytes(olean_header[4..8].try_into().expect("slice length checked"));
    let major = (raw_version >> 16) & 0xff;
    let minor = (raw_version >> 8) & 0xff;
    let patch = raw_version & 0xff;
    Ok(Lean4Version::new(major, minor, patch))
}

#[must_use]
pub(crate) fn version_supports_feature(version: &Lean4Version, feature: &str) -> bool {
    let required_version = match feature {
        "do_notation_v2" => Lean4Version::new(4, 1, 0),
        "structure_eta" => Lean4Version::new(4, 2, 0),
        "match_discriminant_refinement" => Lean4Version::new(4, 3, 0),
        "mathverse_tactic" => Lean4Version::new(4, 2, 0),
        "grind_tactic" => Lean4Version::new(4, 8, 0),
        "exact_suggestions" => Lean4Version::new(4, 3, 0),
        "universe_annotations" => Lean4Version::new(4, 0, 0),
        _ => return false,
    };
    version >= &required_version
}

fn parse_component(original: &str, component: &'static str, input: &str) -> Result<u32, ElabError> {
    input.parse::<u32>().map_err(|source| {
        CompatLayerError::InvalidVersionComponent {
            input: original.to_owned(),
            component,
            source,
        }
        .into()
    })
}

fn transform_enabled(transform: &CompatTransform, config: &CompatConfig) -> bool {
    match transform {
        CompatTransform::RewriteMatchSyntax
        | CompatTransform::InsertDoReturn
        | CompatTransform::LegacyStructureSyntax => config.allow_legacy_syntax,
        CompatTransform::UniverseAnnotation => config.strict_universe_check,
        CompatTransform::DeprecatedTacticAlias { .. } => true,
    }
}

fn push_warning(
    warnings: &mut Vec<DeprecatedWarning>,
    feature: &str,
    deprecated_in: Lean4Version,
    replacement: Option<&str>,
    removal_version: Option<Lean4Version>,
) {
    warnings.push(DeprecatedWarning {
        feature: feature.to_owned(),
        deprecated_in,
        replacement: replacement.map(str::to_owned),
        removal_version,
    });
}

fn register_tactic_alias(
    layer: &mut CompatLayer,
    old_name: &str,
    version: Lean4Version,
    new_name: &str,
) {
    layer
        .tactic_aliases
        .insert(old_name.to_owned(), (version, new_name.to_owned()));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lean4_version_parse_and_display_roundtrip() {
        let version = Lean4Version::parse("4.13.2").unwrap();
        assert_eq!(version, Lean4Version::new(4, 13, 2));
        assert_eq!(version.to_string(), "4.13.2");
    }

    #[test]
    fn deprecated_lookup_respects_config_version() {
        let layer = default_compat_layer();
        let config = CompatConfig {
            target_version: Lean4Version::new(4, 3, 0),
            ..CompatConfig::default()
        };

        let warning = layer
            .check_deprecated(&Name::from_string("library_search"), &config)
            .unwrap();

        assert_eq!(warning.replacement.as_deref(), Some("exact?"));
    }

    #[test]
    fn tactic_alias_translation_is_version_gated() {
        let layer = default_compat_layer();
        assert_eq!(
            layer.translate_tactic_name("library_search", &Lean4Version::new(4, 3, 0)),
            Some("exact?".to_owned())
        );
        assert_eq!(
            layer.translate_tactic_name("library_search", &Lean4Version::new(4, 4, 0)),
            None
        );
    }

    #[test]
    fn detect_lean4_version_from_stub_olean_header() {
        let mut header = Vec::from(*b"olea");
        header.extend_from_slice(&(u32::from(4u8) << 16 | u32::from(13u8) << 8).to_le_bytes());

        let version = detect_lean4_version(&header).unwrap();
        assert_eq!(version, Lean4Version::new(4, 13, 0));
    }

    #[test]
    fn feature_support_table_is_monotonic() {
        assert!(version_supports_feature(
            &Lean4Version::new(4, 8, 0),
            "grind_tactic"
        ));
        assert!(!version_supports_feature(
            &Lean4Version::new(4, 7, 0),
            "grind_tactic"
        ));
    }
}
