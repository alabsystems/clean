// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the extended Lean 4 compatibility layer.

use crate::lean4_compat_ext::{
    default_compat_layer, detect_lean4_version, version_supports_feature, CompatConfig,
    CompatLayer, CompatTransform, DeprecatedWarning, Lean4Version, OLEAN_MAGIC_PREFIX,
};
use clean_kernel::name::Name;
use clean_kernel::Expr;

// ─── Lean4Version tests ──────────────────────────────────────────────────────

#[test]
fn test_version_new_and_display() {
    let v = Lean4Version::new(4, 13, 0);
    assert_eq!(v.to_string(), "4.13.0");
}

#[test]
fn test_version_parse_valid() {
    let v = Lean4Version::parse("4.3.1").expect("should parse valid version");
    assert_eq!(v, Lean4Version::new(4, 3, 1));
}

#[test]
fn test_version_parse_zero() {
    let v = Lean4Version::parse("0.0.0").expect("should parse zero version");
    assert_eq!(v, Lean4Version::new(0, 0, 0));
}

#[test]
fn test_version_parse_large_numbers() {
    let v = Lean4Version::parse("100.200.255").expect("should parse large version");
    assert_eq!(v, Lean4Version::new(100, 200, 255));
}

#[test]
fn test_version_parse_invalid_too_few_parts() {
    assert!(Lean4Version::parse("4.3").is_err());
}

#[test]
fn test_version_parse_invalid_too_many_parts() {
    assert!(Lean4Version::parse("4.3.1.0").is_err());
}

#[test]
fn test_version_parse_invalid_empty() {
    assert!(Lean4Version::parse("").is_err());
}

#[test]
fn test_version_parse_invalid_non_numeric() {
    assert!(Lean4Version::parse("4.x.0").is_err());
}

#[test]
fn test_version_parse_invalid_negative() {
    assert!(Lean4Version::parse("4.-1.0").is_err());
}

#[test]
fn test_version_parse_trims_whitespace() {
    let v = Lean4Version::parse("  4.1.0  ").expect("should trim whitespace");
    assert_eq!(v, Lean4Version::new(4, 1, 0));
}

#[test]
fn test_version_parse_empty_component() {
    assert!(Lean4Version::parse("4..0").is_err());
}

#[test]
fn test_version_ordering_major() {
    assert!(Lean4Version::new(5, 0, 0) > Lean4Version::new(4, 99, 99));
}

#[test]
fn test_version_ordering_minor() {
    assert!(Lean4Version::new(4, 2, 0) > Lean4Version::new(4, 1, 99));
}

#[test]
fn test_version_ordering_patch() {
    assert!(Lean4Version::new(4, 1, 2) > Lean4Version::new(4, 1, 1));
}

#[test]
fn test_version_ordering_equal() {
    assert_eq!(Lean4Version::new(4, 1, 0), Lean4Version::new(4, 1, 0));
}

#[test]
fn test_version_copy_semantics() {
    let v1 = Lean4Version::new(4, 0, 0);
    let v2 = v1; // Copy
    assert_eq!(v1, v2);
}

// ─── CompatConfig tests ─────────────────────────────────────────────────────

#[test]
fn test_config_default() {
    let config = CompatConfig::default();
    assert_eq!(config.target_version, Lean4Version::new(4, 13, 0));
    assert!(config.warn_deprecated);
    assert!(config.allow_legacy_syntax);
    assert!(!config.strict_universe_check);
}

#[test]
fn test_config_custom() {
    let config = CompatConfig {
        target_version: Lean4Version::new(4, 0, 0),
        warn_deprecated: false,
        allow_legacy_syntax: false,
        strict_universe_check: true,
    };
    assert_eq!(config.target_version, Lean4Version::new(4, 0, 0));
    assert!(!config.warn_deprecated);
    assert!(!config.allow_legacy_syntax);
    assert!(config.strict_universe_check);
}

// ─── CompatTransform tests ──────────────────────────────────────────────────

#[test]
fn test_transform_equality() {
    assert_eq!(
        CompatTransform::RewriteMatchSyntax,
        CompatTransform::RewriteMatchSyntax
    );
    assert_ne!(
        CompatTransform::RewriteMatchSyntax,
        CompatTransform::InsertDoReturn
    );
}

#[test]
fn test_transform_tactic_alias_equality() {
    let t1 = CompatTransform::DeprecatedTacticAlias {
        old: "tidy".to_owned(),
        new: "aesop".to_owned(),
    };
    let t2 = CompatTransform::DeprecatedTacticAlias {
        old: "tidy".to_owned(),
        new: "aesop".to_owned(),
    };
    assert_eq!(t1, t2);
}

#[test]
fn test_transform_tactic_alias_inequality() {
    let t1 = CompatTransform::DeprecatedTacticAlias {
        old: "tidy".to_owned(),
        new: "aesop".to_owned(),
    };
    let t2 = CompatTransform::DeprecatedTacticAlias {
        old: "obviously".to_owned(),
        new: "decide".to_owned(),
    };
    assert_ne!(t1, t2);
}

#[test]
fn test_transform_debug_repr() {
    let t = CompatTransform::UniverseAnnotation;
    let dbg = format!("{t:?}");
    assert!(dbg.contains("UniverseAnnotation"));
}

// ─── DeprecatedWarning tests ────────────────────────────────────────────────

#[test]
fn test_deprecated_warning_display_full() {
    let w = DeprecatedWarning {
        feature: "library_search".to_owned(),
        deprecated_in: Lean4Version::new(4, 3, 0),
        replacement: Some("exact?".to_owned()),
        removal_version: Some(Lean4Version::new(5, 0, 0)),
    };
    let s = w.to_string();
    assert!(s.contains("library_search"));
    assert!(s.contains("4.3.0"));
    assert!(s.contains("exact?"));
    assert!(s.contains("5.0.0"));
}

#[test]
fn test_deprecated_warning_display_no_replacement() {
    let w = DeprecatedWarning {
        feature: "old_thing".to_owned(),
        deprecated_in: Lean4Version::new(4, 0, 0),
        replacement: None,
        removal_version: None,
    };
    let s = w.to_string();
    assert!(s.contains("old_thing"));
    assert!(s.contains("4.0.0"));
    assert!(!s.contains("instead"));
    assert!(!s.contains("removal"));
}

#[test]
fn test_deprecated_warning_display_replacement_only() {
    let w = DeprecatedWarning {
        feature: "foo".to_owned(),
        deprecated_in: Lean4Version::new(4, 2, 0),
        replacement: Some("bar".to_owned()),
        removal_version: None,
    };
    let s = w.to_string();
    assert!(s.contains("bar"));
    assert!(!s.contains("removal"));
}

// ─── CompatLayer tests ──────────────────────────────────────────────────────

#[test]
fn test_layer_default_is_empty() {
    let layer = CompatLayer::default();
    assert!(layer.transforms.is_empty());
    assert!(layer.deprecated_features.is_empty());
    assert!(layer.tactic_aliases.is_empty());
}

#[test]
fn test_layer_register_transform() {
    let mut layer = CompatLayer::default();
    layer.register_transform(
        Lean4Version::new(4, 0, 0),
        CompatTransform::RewriteMatchSyntax,
    );
    assert_eq!(layer.transforms.len(), 1);
}

#[test]
fn test_layer_apply_transforms_returns_clone() {
    let layer = default_compat_layer();
    let config = CompatConfig::default();
    let expr = Expr::const_str("Nat.add");
    let result = layer
        .apply_transforms(&expr, &config)
        .expect("should succeed");
    assert_eq!(result, expr);
}

#[test]
fn test_layer_apply_transforms_with_restrictive_version() {
    let layer = default_compat_layer();
    let config = CompatConfig {
        target_version: Lean4Version::new(3, 0, 0),
        ..CompatConfig::default()
    };
    let expr = Expr::const_str("Nat.add");
    let result = layer
        .apply_transforms(&expr, &config)
        .expect("should succeed");
    assert_eq!(result, expr);
}

#[test]
fn test_layer_check_deprecated_found() {
    let layer = default_compat_layer();
    let config = CompatConfig::default();
    let name = Name::from_string("library_search");
    let warning = layer.check_deprecated(&name, &config);
    assert!(warning.is_some());
    let w = warning.unwrap();
    assert_eq!(w.feature, "library_search");
    assert_eq!(w.replacement.as_deref(), Some("exact?"));
}

#[test]
fn test_layer_check_deprecated_not_found() {
    let layer = default_compat_layer();
    let config = CompatConfig::default();
    let name = Name::from_string("nonexistent_tactic");
    assert!(layer.check_deprecated(&name, &config).is_none());
}

#[test]
fn test_layer_check_deprecated_disabled() {
    let layer = default_compat_layer();
    let config = CompatConfig {
        warn_deprecated: false,
        ..CompatConfig::default()
    };
    let name = Name::from_string("library_search");
    assert!(layer.check_deprecated(&name, &config).is_none());
}

#[test]
fn test_layer_check_deprecated_version_filter() {
    let layer = default_compat_layer();
    // library_search deprecated in 4.3.0 -- querying with 4.2.0 should not find it
    let config = CompatConfig {
        target_version: Lean4Version::new(4, 2, 0),
        ..CompatConfig::default()
    };
    let name = Name::from_string("library_search");
    assert!(layer.check_deprecated(&name, &config).is_none());
}

#[test]
fn test_layer_translate_tactic_name_found() {
    let layer = default_compat_layer();
    let v = Lean4Version::new(4, 2, 0);
    let result = layer.translate_tactic_name("library_search", &v);
    assert_eq!(result.as_deref(), Some("exact?"));
}

#[test]
fn test_layer_translate_tactic_name_version_too_new() {
    let layer = default_compat_layer();
    // library_search alias version is 4.3.0 -- querying with 4.4.0 should not match
    let v = Lean4Version::new(4, 4, 0);
    assert!(layer.translate_tactic_name("library_search", &v).is_none());
}

#[test]
fn test_layer_translate_tactic_name_exact_boundary() {
    let layer = default_compat_layer();
    // library_search alias version is 4.3.0 -- querying with exactly 4.3.0 should match
    let v = Lean4Version::new(4, 3, 0);
    assert_eq!(
        layer.translate_tactic_name("library_search", &v).as_deref(),
        Some("exact?")
    );
}

#[test]
fn test_layer_translate_tactic_name_unknown() {
    let layer = default_compat_layer();
    let v = Lean4Version::new(4, 0, 0);
    assert!(layer.translate_tactic_name("unknown_tactic", &v).is_none());
}

#[test]
fn test_layer_translate_various_aliases() {
    let layer = default_compat_layer();
    let v = Lean4Version::new(4, 0, 0);
    assert_eq!(
        layer.translate_tactic_name("obviously", &v).as_deref(),
        Some("decide")
    );
    assert_eq!(
        layer.translate_tactic_name("ring_nf", &v).as_deref(),
        Some("ring")
    );
    assert_eq!(
        layer.translate_tactic_name("dec_trivial", &v).as_deref(),
        Some("decide")
    );
}

// ─── default_compat_layer tests ─────────────────────────────────────────────

#[test]
fn test_default_layer_has_transforms() {
    let layer = default_compat_layer();
    assert!(layer.transforms.len() >= 6);
}

#[test]
fn test_default_layer_has_deprecated() {
    let layer = default_compat_layer();
    assert!(layer.deprecated_features.len() >= 5);
}

#[test]
fn test_default_layer_has_tactic_aliases() {
    let layer = default_compat_layer();
    assert!(layer.tactic_aliases.len() >= 7);
}

// ─── detect_lean4_version tests ─────────────────────────────────────────────

fn make_olean_header(major: u8, minor: u8, patch: u8) -> Vec<u8> {
    let mut buf = Vec::with_capacity(8);
    buf.extend_from_slice(&OLEAN_MAGIC_PREFIX.to_le_bytes());
    let version_word = (u32::from(major) << 16) | (u32::from(minor) << 8) | u32::from(patch);
    buf.extend_from_slice(&version_word.to_le_bytes());
    buf
}

#[test]
fn test_detect_version_valid() {
    let header = make_olean_header(4, 13, 0);
    let v = detect_lean4_version(&header).expect("should parse valid header");
    assert_eq!(v, Lean4Version::new(4, 13, 0));
}

#[test]
fn test_detect_version_with_patch() {
    let header = make_olean_header(4, 8, 3);
    let v = detect_lean4_version(&header).expect("should parse");
    assert_eq!(v, Lean4Version::new(4, 8, 3));
}

#[test]
fn test_detect_version_too_short() {
    assert!(detect_lean4_version(&[0u8; 4]).is_err());
}

#[test]
fn test_detect_version_bad_magic() {
    let mut header = make_olean_header(4, 0, 0);
    header[0] = 0xFF; // corrupt magic
    assert!(detect_lean4_version(&header).is_err());
}

#[test]
fn test_detect_version_extra_bytes_ok() {
    let mut header = make_olean_header(4, 5, 1);
    header.extend_from_slice(&[0u8; 100]); // extra data
    let v = detect_lean4_version(&header).expect("extra bytes should be ignored");
    assert_eq!(v, Lean4Version::new(4, 5, 1));
}

#[test]
fn test_detect_version_empty_input() {
    assert!(detect_lean4_version(&[]).is_err());
}

#[test]
fn test_detect_version_exactly_8_bytes() {
    let header = make_olean_header(4, 0, 0);
    assert_eq!(header.len(), 8);
    let v = detect_lean4_version(&header).expect("exactly 8 bytes should work");
    assert_eq!(v, Lean4Version::new(4, 0, 0));
}

// ─── version_supports_feature tests ─────────────────────────────────────────

#[test]
fn test_feature_do_notation_v2() {
    assert!(!version_supports_feature(
        &Lean4Version::new(4, 0, 0),
        "do_notation_v2"
    ));
    assert!(version_supports_feature(
        &Lean4Version::new(4, 1, 0),
        "do_notation_v2"
    ));
    assert!(version_supports_feature(
        &Lean4Version::new(4, 13, 0),
        "do_notation_v2"
    ));
}

#[test]
fn test_feature_structure_eta() {
    assert!(!version_supports_feature(
        &Lean4Version::new(4, 1, 0),
        "structure_eta"
    ));
    assert!(version_supports_feature(
        &Lean4Version::new(4, 2, 0),
        "structure_eta"
    ));
}

#[test]
fn test_feature_grind_tactic() {
    assert!(!version_supports_feature(
        &Lean4Version::new(4, 7, 0),
        "grind_tactic"
    ));
    assert!(version_supports_feature(
        &Lean4Version::new(4, 8, 0),
        "grind_tactic"
    ));
}

#[test]
fn test_feature_unknown() {
    assert!(!version_supports_feature(
        &Lean4Version::new(99, 99, 99),
        "nonexistent_feature"
    ));
}

#[test]
fn test_feature_universe_annotations_always_supported() {
    assert!(version_supports_feature(
        &Lean4Version::new(4, 0, 0),
        "universe_annotations"
    ));
}

#[test]
fn test_feature_mathverse_tactic() {
    assert!(!version_supports_feature(
        &Lean4Version::new(4, 1, 0),
        "mathverse_tactic"
    ));
    assert!(version_supports_feature(
        &Lean4Version::new(4, 2, 0),
        "mathverse_tactic"
    ));
}

#[test]
fn test_feature_exact_suggestions() {
    assert!(!version_supports_feature(
        &Lean4Version::new(4, 2, 0),
        "exact_suggestions"
    ));
    assert!(version_supports_feature(
        &Lean4Version::new(4, 3, 0),
        "exact_suggestions"
    ));
}

#[test]
fn test_feature_match_discriminant_refinement() {
    assert!(!version_supports_feature(
        &Lean4Version::new(4, 2, 0),
        "match_discriminant_refinement"
    ));
    assert!(version_supports_feature(
        &Lean4Version::new(4, 3, 0),
        "match_discriminant_refinement"
    ));
}

// ─── Integration / cross-cutting tests ──────────────────────────────────────

#[test]
fn test_roundtrip_version_display_parse() {
    let v = Lean4Version::new(4, 13, 2);
    let s = v.to_string();
    let parsed = Lean4Version::parse(&s).expect("roundtrip should succeed");
    assert_eq!(v, parsed);
}

#[test]
fn test_deprecated_check_known_features() {
    let layer = default_compat_layer();
    let config = CompatConfig::default();
    let known = ["library_search", "squeeze_simp", "suggest", "tauto"];
    for name_str in &known {
        let name = Name::from_string(name_str);
        assert!(
            layer.check_deprecated(&name, &config).is_some(),
            "expected deprecated warning for '{name_str}'"
        );
    }
}

#[test]
fn test_default_layer_tactic_alias_consistency() {
    // Key deprecated tactics should have matching aliases
    let layer = default_compat_layer();
    let v = Lean4Version::new(4, 0, 0);
    let tactic_features = ["obviously", "dec_trivial", "ring_nf"];
    for name in &tactic_features {
        assert!(
            layer.translate_tactic_name(name, &v).is_some(),
            "tactic alias missing for '{name}'"
        );
    }
}

#[test]
fn test_compat_layer_error_display() {
    use crate::lean4_compat_ext::CompatLayerError;
    let err = CompatLayerError::OleanHeaderTooShort { len: 3 };
    let msg = err.to_string();
    assert!(msg.contains("3"));
    assert!(msg.contains("8"));
}
