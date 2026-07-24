// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended name mangling (`mangle_ext`).

use super::mangle_ext::*;
use clean_kernel::Name;

// ========================================================================
// MangleTarget basics
// ========================================================================

#[test]
fn test_target_c_mangle_prefix() {
    let name = Name::from_string("foo");
    let mangled = mangle_c(&name);
    assert!(mangled.starts_with("l_"), "C prefix: {}", mangled);
}

#[test]
fn test_target_rust_mangle_prefix() {
    let name = Name::from_string("foo");
    let mangled = mangle_rust(&name);
    assert!(mangled.starts_with("clean_"), "Rust prefix: {}", mangled);
}

#[test]
fn test_target_llvm_mangle_prefix() {
    let name = Name::from_string("foo");
    let mangled = mangle_llvm(&name);
    assert!(mangled.starts_with("@clean_"), "LLVM prefix: {}", mangled);
}

#[test]
fn test_default_config_uses_c_target() {
    let config = MangleConfig::default();
    let name = Name::from_string("foo");
    let mangled = mangle_ext(&name, &config);
    assert!(
        mangled.starts_with("l_"),
        "Default target should be C: {}",
        mangled
    );
}

// ========================================================================
// mangle_c / mangle_rust / mangle_llvm shortcuts
// ========================================================================

#[test]
fn test_mangle_c_simple() {
    let name = Name::from_string("Nat.add");
    let mangled = mangle_c(&name);
    assert!(mangled.starts_with("l_"), "C mangled: {}", mangled);
    assert!(mangled.contains("Nat"), "Should contain Nat: {}", mangled);
}

#[test]
fn test_mangle_rust_simple() {
    let name = Name::from_string("Nat.add");
    let mangled = mangle_rust(&name);
    assert!(mangled.starts_with("clean_"), "Rust mangled: {}", mangled);
}

#[test]
fn test_mangle_llvm_simple() {
    let name = Name::from_string("Nat.add");
    let mangled = mangle_llvm(&name);
    assert!(mangled.starts_with("@clean_"), "LLVM mangled: {}", mangled);
}

// ========================================================================
// mangle_ext with config
// ========================================================================

#[test]
fn test_mangle_ext_export_override() {
    let name = Name::from_string("Nat.add");
    let config = MangleConfig {
        export_override: Some("lean_nat_add".to_string()),
        ..Default::default()
    };
    assert_eq!(mangle_ext(&name, &config), "lean_nat_add");
}

#[test]
fn test_mangle_ext_no_namespace() {
    let name = Name::from_string("Nat.add");
    let config = MangleConfig {
        encode_namespaces: false,
        ..Default::default()
    };
    let mangled = mangle_ext(&name, &config);
    // Without namespace encoding, only last component is used.
    assert_eq!(mangled, "l_add");
}

#[test]
fn test_mangle_ext_with_namespace() {
    let name = Name::from_string("Nat.add");
    let config = MangleConfig::default();
    let mangled = mangle_ext(&name, &config);
    assert_eq!(mangled, "l_Nat_add");
}

#[test]
fn test_mangle_ext_type_suffix() {
    let name = Name::from_string("foo");
    let config = MangleConfig {
        encode_type_suffix: true,
        ..Default::default()
    };
    let mangled = mangle_ext(&name, &config);
    assert!(
        mangled.contains("_T_"),
        "Should have type suffix: {}",
        mangled
    );
}

#[test]
fn test_mangle_ext_max_length() {
    let name = Name::from_string("Very.Long.Namespace.Path.To.Some.Function");
    let config = MangleConfig {
        max_length: Some(20),
        ..Default::default()
    };
    let mangled = mangle_ext(&name, &config);
    assert!(
        mangled.len() <= 20,
        "Should be truncated: len={} '{}'",
        mangled.len(),
        mangled
    );
}

#[test]
fn test_mangle_ext_max_length_no_truncation_needed() {
    let name = Name::from_string("foo");
    let config = MangleConfig {
        max_length: Some(100),
        ..Default::default()
    };
    let mangled = mangle_ext(&name, &config);
    assert_eq!(mangled, "l_foo");
}

// ========================================================================
// namespace_encode
// ========================================================================

#[test]
fn test_namespace_encode_simple() {
    let name = Name::from_string("Nat.add");
    assert_eq!(namespace_encode(&name), "Nat_add");
}

#[test]
fn test_namespace_encode_deep() {
    let name = Name::from_string("Init.Data.List.Basic");
    assert_eq!(namespace_encode(&name), "Init_Data_List_Basic");
}

#[test]
fn test_namespace_encode_anonymous() {
    let name = Name::anon();
    assert_eq!(namespace_encode(&name), "");
}

#[test]
fn test_namespace_encode_single() {
    let name = Name::from_string("Nat");
    assert_eq!(namespace_encode(&name), "Nat");
}

#[test]
fn test_namespace_encode_numeric() {
    let name = Name::anon().str("foo").num(42);
    let encoded = namespace_encode(&name);
    assert!(encoded.contains("foo"), "Should have foo: {}", encoded);
    assert!(encoded.contains("42"), "Should have 42: {}", encoded);
}

#[test]
fn test_namespace_encode_underscore() {
    let name = Name::from_string("foo_bar");
    let encoded = namespace_encode(&name);
    // underscore in component doubles to __
    assert_eq!(encoded, "foo__bar");
}

// ========================================================================
// demangle
// ========================================================================

#[test]
fn test_demangle_c_prefix() {
    assert_eq!(demangle("l_Nat_add"), Some("Nat.add".to_string()));
}

#[test]
fn test_demangle_rust_prefix() {
    let name = Name::from_string("Nat.add");
    let mangled = mangle_rust(&name);
    let demangled = demangle(&mangled);
    assert_eq!(demangled, Some("Nat.add".to_string()));
}

#[test]
fn test_demangle_llvm_prefix() {
    assert_eq!(demangle("@clean_Nat_add"), Some("Nat.add".to_string()));
}

#[test]
fn test_demangle_unknown_prefix() {
    assert_eq!(demangle("unknown_prefix"), None);
}

#[test]
fn test_demangle_underscore_in_name() {
    // foo__bar is a doubled underscore -> literal _
    assert_eq!(demangle("l_foo__bar"), Some("foo_bar".to_string()));
}

#[test]
fn test_demangle_ascii_escape() {
    // _x2b is '+'
    assert_eq!(demangle("l__x2b"), Some("+".to_string()));
}

#[test]
fn test_demangle_unicode_escape_u() {
    // _u03b1 is alpha
    assert_eq!(demangle("l__u03b1"), Some("\u{03b1}".to_string()));
}

#[test]
fn test_demangle_unicode_escape_big_u() {
    // _U0001d54a is mathematical double-struck S
    assert_eq!(demangle("l__U0001d54a"), Some("\u{1d54a}".to_string()));
}

#[test]
fn test_demangle_disambiguation_stripped() {
    // _00 disambiguation prefix should be removed
    assert_eq!(demangle("l__00foo"), Some("foo".to_string()));
}

// ========================================================================
// encode_type_suffix
// ========================================================================

#[test]
fn test_encode_type_suffix_simple() {
    assert_eq!(encode_type_suffix("Nat"), "_T_Nat");
}

#[test]
fn test_encode_type_suffix_special_chars() {
    let suffix = encode_type_suffix("Nat->Bool");
    assert!(suffix.starts_with("_T_"), "suffix: {}", suffix);
    assert!(suffix.contains("Nat"), "suffix: {}", suffix);
}

// ========================================================================
// Collision detection and resolution
// ========================================================================

#[test]
fn test_detect_collisions_no_collisions() {
    let names = vec![
        Name::from_string("Nat.add"),
        Name::from_string("Nat.sub"),
        Name::from_string("List.map"),
    ];
    let config = MangleConfig::default();
    let collisions = detect_collisions(&names, &config);
    assert!(
        collisions.is_empty(),
        "Expected no collisions: {:?}",
        collisions
    );
}

#[test]
fn test_detect_collisions_with_collision() {
    // Force collision by using export override
    let names = vec![Name::from_string("Nat.add"), Name::from_string("Nat.sub")];
    let config = MangleConfig {
        export_override: Some("same_name".to_string()),
        ..Default::default()
    };
    let collisions = detect_collisions(&names, &config);
    assert_eq!(collisions.len(), 1);
    assert_eq!(collisions["same_name"].len(), 2);
}

#[test]
fn test_resolve_collision() {
    let name = Name::from_string("foo");
    let config = MangleConfig::default();
    let resolved = resolve_collision(&name, 0, &config);
    assert!(resolved.ends_with("_C0"), "Resolved: {}", resolved);

    let resolved2 = resolve_collision(&name, 1, &config);
    assert!(resolved2.ends_with("_C1"), "Resolved: {}", resolved2);
    assert_ne!(resolved, resolved2);
}

// ========================================================================
// Statistics
// ========================================================================

#[test]
fn test_collect_stats_basic() {
    let names = vec![
        Name::from_string("Nat.add"),
        Name::from_string("Nat.sub"),
        Name::from_string("List.map"),
    ];
    let config = MangleConfig::default();
    let stats = collect_stats(&names, &config);
    assert_eq!(stats.total_mangled, 3);
    assert_eq!(stats.collisions_detected, 0);
    assert!(stats.max_name_length > 0);
    assert_eq!(stats.unicode_names, 0);
}

#[test]
fn test_collect_stats_unicode() {
    let names = vec![
        Name::from_string("\u{03b1}"),
        Name::from_string("\u{03b2}"),
        Name::from_string("foo"),
    ];
    let config = MangleConfig::default();
    let stats = collect_stats(&names, &config);
    assert_eq!(stats.total_mangled, 3);
    assert_eq!(stats.unicode_names, 2);
}

// ========================================================================
// encode_unicode_safe
// ========================================================================

#[test]
fn test_encode_unicode_safe_ascii() {
    assert_eq!(encode_unicode_safe("hello"), "hello");
}

#[test]
fn test_encode_unicode_safe_unicode() {
    let encoded = encode_unicode_safe("\u{03b1}");
    assert_eq!(encoded, "_u03b1");
}

#[test]
fn test_encode_unicode_safe_mixed() {
    let encoded = encode_unicode_safe("Nat\u{03b1}");
    assert_eq!(encoded, "Nat_u03b1");
}

#[test]
fn test_encode_unicode_safe_high_unicode() {
    let encoded = encode_unicode_safe("\u{1d54a}");
    assert_eq!(encoded, "_U0001d54a");
}

// ========================================================================
// is_valid_c_ident / is_valid_rust_ident
// ========================================================================

#[test]
fn test_is_valid_c_ident() {
    assert!(is_valid_c_ident("foo"));
    assert!(is_valid_c_ident("_foo"));
    assert!(is_valid_c_ident("foo123"));
    assert!(is_valid_c_ident("_"));
    assert!(!is_valid_c_ident(""));
    assert!(!is_valid_c_ident("123foo"));
    assert!(!is_valid_c_ident("foo-bar"));
    assert!(!is_valid_c_ident("foo.bar"));
}

#[test]
fn test_is_valid_rust_ident() {
    assert!(is_valid_rust_ident("foo"));
    assert!(is_valid_rust_ident("_foo"));
    assert!(is_valid_rust_ident("_"));
    assert!(!is_valid_rust_ident(""));
    assert!(!is_valid_rust_ident("123foo"));
}

// ========================================================================
// Mangled output validity
// ========================================================================

#[test]
fn test_c_mangled_is_valid_c_ident() {
    let names = vec![
        Name::from_string("Nat.add"),
        Name::from_string("List.map"),
        Name::from_string("foo_bar"),
    ];
    for name in &names {
        let mangled = mangle_c(name);
        assert!(
            is_valid_c_ident(&mangled),
            "C mangled output should be valid C ident: {} -> {}",
            name,
            mangled
        );
    }
}

#[test]
fn test_rust_mangled_is_valid_rust_ident() {
    let names = vec![
        Name::from_string("Nat.add"),
        Name::from_string("List.map"),
        Name::from_string("foo_bar"),
    ];
    for name in &names {
        let mangled = mangle_rust(name);
        assert!(
            is_valid_rust_ident(&mangled),
            "Rust mangled output should be valid Rust ident: {} -> {}",
            name,
            mangled
        );
    }
}

// ========================================================================
// Round-trip: mangle then demangle
// ========================================================================

#[test]
fn test_roundtrip_c_simple() {
    let name = Name::from_string("Nat.add");
    let mangled = mangle_c(&name);
    let demangled = demangle(&mangled).expect("should demangle");
    assert_eq!(demangled, "Nat.add");
}

#[test]
fn test_roundtrip_c_deep_namespace() {
    let name = Name::from_string("Init.Data.List.Basic");
    let mangled = mangle_c(&name);
    let demangled = demangle(&mangled).expect("should demangle");
    assert_eq!(demangled, "Init.Data.List.Basic");
}

#[test]
fn test_roundtrip_c_underscore() {
    let name = Name::from_string("foo_bar");
    let mangled = mangle_c(&name);
    let demangled = demangle(&mangled).expect("should demangle");
    assert_eq!(demangled, "foo_bar");
}

#[test]
fn test_roundtrip_rust_simple() {
    let name = Name::from_string("Nat.add");
    let mangled = mangle_rust(&name);
    let demangled = demangle(&mangled).expect("should demangle");
    assert_eq!(demangled, "Nat.add");
}

#[test]
fn test_roundtrip_llvm_simple() {
    let name = Name::from_string("Nat.add");
    let mangled = mangle_llvm(&name);
    let demangled = demangle(&mangled).expect("should demangle");
    assert_eq!(demangled, "Nat.add");
}

// ========================================================================
// Edge cases
// ========================================================================

#[test]
fn test_mangle_ext_anonymous() {
    let name = Name::anon();
    let mangled = mangle_c(&name);
    assert_eq!(mangled, "l_");
}

#[test]
fn test_different_targets_differ() {
    let name = Name::from_string("Nat.add");
    let c = mangle_c(&name);
    let rust = mangle_rust(&name);
    let llvm = mangle_llvm(&name);
    assert_ne!(c, rust);
    assert_ne!(c, llvm);
    assert_ne!(rust, llvm);
}

#[test]
fn test_mangle_ext_unicode_name() {
    let name = Name::from_string("\u{03b1}");
    let mangled = mangle_c(&name);
    assert!(mangled.starts_with("l_"), "Unicode mangled: {}", mangled);
    // Unicode chars should be encoded as escape sequences
    assert!(
        mangled.contains("_u03b1") || mangled.contains("_00"),
        "Encoded: {}",
        mangled
    );
}

#[test]
fn test_mangle_collision_resolution_differs() {
    let name = Name::from_string("foo");
    let config = MangleConfig::default();
    let base = mangle_ext(&name, &config);
    let r0 = resolve_collision(&name, 0, &config);
    let r1 = resolve_collision(&name, 1, &config);
    // Resolved names differ from base and from each other
    assert_ne!(base, r0);
    assert_ne!(base, r1);
    assert_ne!(r0, r1);
}
