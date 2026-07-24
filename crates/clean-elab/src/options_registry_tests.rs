// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

// -- Registry construction ------------------------------------------------

#[test]
fn test_registry_new_has_standard_options() {
    let reg = OptionsRegistry::new();
    assert!(reg.len() >= 10, "should have at least 10 standard options");
    assert!(reg.is_registered("maxHeartbeats"));
    assert!(reg.is_registered("maxRecDepth"));
    assert!(reg.is_registered("pp.all"));
    assert!(reg.is_registered("pp.universes"));
    assert!(reg.is_registered("pp.notation"));
    assert!(reg.is_registered("pp.proofs"));
    assert!(reg.is_registered("autoImplicit"));
    assert!(reg.is_registered("relaxedAutoImplicit"));
    assert!(reg.is_registered("trace.Meta.isDefEq"));
    assert!(reg.is_registered("linter.unusedVariables"));
}

#[test]
fn test_registry_standard_defaults() {
    let reg = OptionsRegistry::new();
    assert_eq!(
        reg.get_default("maxHeartbeats"),
        Some(&OptionValue::Nat(200_000))
    );
    assert_eq!(reg.get_default("maxRecDepth"), Some(&OptionValue::Nat(512)));
    assert_eq!(reg.get_default("pp.all"), Some(&OptionValue::Bool(false)));
    assert_eq!(
        reg.get_default("autoImplicit"),
        Some(&OptionValue::Bool(true))
    );
}

#[test]
fn test_registry_unknown_option_returns_none() {
    let reg = OptionsRegistry::new();
    assert_eq!(reg.get_default("nonexistent.option"), None);
    assert!(!reg.is_registered("nonexistent.option"));
}

#[test]
fn test_registry_register_custom_option() {
    let mut reg = OptionsRegistry::new();
    let initial_count = reg.len();
    reg.register("custom.myFlag", OptionValue::Bool(true), "A custom flag");
    assert_eq!(reg.len(), initial_count + 1);
    assert!(reg.is_registered("custom.myFlag"));
    assert_eq!(
        reg.get_default("custom.myFlag"),
        Some(&OptionValue::Bool(true))
    );
}

#[test]
fn test_registry_all_options_iterator() {
    let reg = OptionsRegistry::new();
    let all: Vec<_> = reg.all_options().collect();
    assert_eq!(all.len(), reg.len());
    // BTreeMap order: sorted by name
    for window in all.windows(2) {
        assert!(window[0].name() <= window[1].name());
    }
}

#[test]
fn test_registry_overwrite_existing() {
    let mut reg = OptionsRegistry::new();
    reg.register("maxHeartbeats", OptionValue::Nat(999), "Overwritten");
    assert_eq!(
        reg.get_default("maxHeartbeats"),
        Some(&OptionValue::Nat(999))
    );
}

// -- FileOptions get/set/reset --------------------------------------------

#[test]
fn test_file_options_get_default() {
    let reg = OptionsRegistry::new();
    let opts = FileOptions::new(&reg);
    assert_eq!(opts.get_nat("maxHeartbeats"), Some(200_000));
    assert_eq!(opts.get_bool("pp.all"), Some(false));
    assert!(!opts.has_overrides());
}

#[test]
fn test_file_options_set_and_get() {
    let reg = OptionsRegistry::new();
    let mut opts = FileOptions::new(&reg);
    opts.set("maxHeartbeats", OptionValue::Nat(400_000))
        .expect("should set maxHeartbeats");
    assert_eq!(opts.get_nat("maxHeartbeats"), Some(400_000));
    assert!(opts.has_overrides());
    assert_eq!(opts.override_count(), 1);
}

#[test]
fn test_file_options_set_bool() {
    let reg = OptionsRegistry::new();
    let mut opts = FileOptions::new(&reg);
    opts.set("pp.all", OptionValue::Bool(true))
        .expect("should set pp.all");
    assert_eq!(opts.get_bool("pp.all"), Some(true));
}

#[test]
fn test_file_options_reset_falls_back_to_default() {
    let reg = OptionsRegistry::new();
    let mut opts = FileOptions::new(&reg);
    opts.set("maxHeartbeats", OptionValue::Nat(400_000))
        .expect("should set");
    assert_eq!(opts.get_nat("maxHeartbeats"), Some(400_000));

    let removed = opts.reset("maxHeartbeats");
    assert!(removed);
    assert_eq!(opts.get_nat("maxHeartbeats"), Some(200_000));
    assert!(!opts.has_overrides());
}

#[test]
fn test_file_options_reset_nonexistent_returns_false() {
    let reg = OptionsRegistry::new();
    let mut opts = FileOptions::new(&reg);
    assert!(!opts.reset("maxHeartbeats"));
}

// -- Error cases ----------------------------------------------------------

#[test]
fn test_file_options_set_unknown_option() {
    let reg = OptionsRegistry::new();
    let mut opts = FileOptions::new(&reg);
    let err = opts
        .set("nonexistent.option", OptionValue::Bool(true))
        .unwrap_err();
    assert!(matches!(err, OptionError::UnknownOption { .. }));
    let msg = err.to_string();
    assert!(msg.contains("nonexistent.option"), "error: {msg}");
}

#[test]
fn test_file_options_set_type_mismatch_nat_to_bool() {
    let reg = OptionsRegistry::new();
    let mut opts = FileOptions::new(&reg);
    let err = opts
        .set("maxHeartbeats", OptionValue::Bool(true))
        .unwrap_err();
    assert!(matches!(err, OptionError::TypeMismatch { .. }));
    let msg = err.to_string();
    assert!(msg.contains("maxHeartbeats"), "error: {msg}");
    assert!(msg.contains("Nat"), "error: {msg}");
    assert!(msg.contains("Bool"), "error: {msg}");
}

#[test]
fn test_file_options_set_type_mismatch_bool_to_string() {
    let reg = OptionsRegistry::new();
    let mut opts = FileOptions::new(&reg);
    let err = opts
        .set("pp.all", OptionValue::String("yes".to_string()))
        .unwrap_err();
    assert!(matches!(err, OptionError::TypeMismatch { .. }));
}

// -- Typed getters with wrong type ----------------------------------------

#[test]
fn test_file_options_get_bool_on_nat_returns_none() {
    let reg = OptionsRegistry::new();
    let opts = FileOptions::new(&reg);
    // maxHeartbeats is Nat, not Bool
    assert_eq!(opts.get_bool("maxHeartbeats"), None);
}

#[test]
fn test_file_options_get_nat_on_bool_returns_none() {
    let reg = OptionsRegistry::new();
    let opts = FileOptions::new(&reg);
    // pp.all is Bool, not Nat
    assert_eq!(opts.get_nat("pp.all"), None);
}

#[test]
fn test_file_options_get_string_on_nat_returns_none() {
    let reg = OptionsRegistry::new();
    let opts = FileOptions::new(&reg);
    assert_eq!(opts.get_string("maxHeartbeats"), None);
}

#[test]
fn test_file_options_get_nonexistent_returns_none() {
    let reg = OptionsRegistry::new();
    let opts = FileOptions::new(&reg);
    assert_eq!(opts.get("nonexistent"), None);
    assert_eq!(opts.get_bool("nonexistent"), None);
    assert_eq!(opts.get_nat("nonexistent"), None);
    assert_eq!(opts.get_string("nonexistent"), None);
}

// -- OptionValue display --------------------------------------------------

#[test]
fn test_option_value_display() {
    assert_eq!(format!("{}", OptionValue::Bool(true)), "true");
    assert_eq!(format!("{}", OptionValue::Nat(42)), "42");
    assert_eq!(
        format!("{}", OptionValue::String("hello".to_string())),
        "\"hello\""
    );
}

// -- OptionDecl accessors -------------------------------------------------

#[test]
fn test_option_decl_accessors() {
    let reg = OptionsRegistry::new();
    let decl = reg.all_options().find(|d| d.name() == "maxHeartbeats");
    let decl = decl.expect("maxHeartbeats should exist");
    assert_eq!(decl.name(), "maxHeartbeats");
    assert_eq!(decl.default(), &OptionValue::Nat(200_000));
    assert!(!decl.description().is_empty());
}

// -- String option round-trip ---------------------------------------------

#[test]
fn test_file_options_string_option_round_trip() {
    let mut reg = OptionsRegistry::new();
    reg.register(
        "pp.format",
        OptionValue::String("default".to_string()),
        "Pretty-printer format mode",
    );
    let mut opts = FileOptions::new(&reg);
    assert_eq!(opts.get_string("pp.format"), Some("default"));

    opts.set("pp.format", OptionValue::String("compact".to_string()))
        .expect("should set string option");
    assert_eq!(opts.get_string("pp.format"), Some("compact"));
}

// -- OptionValue::Name variant --------------------------------------------

#[test]
fn test_option_value_name_variant() {
    let val = OptionValue::Name("Lean.Elab".to_string());
    assert_eq!(val.kind_name(), "Name");
    assert_eq!(format!("{val}"), "`Lean.Elab`");
}

#[test]
fn test_register_name_option() {
    let mut reg = OptionsRegistry::new();
    reg.register(
        "trace.profiler.output",
        OptionValue::Name("default".to_string()),
        "Profiler output trace name",
    );
    assert!(reg.is_registered("trace.profiler.output"));
    assert_eq!(
        reg.get_default("trace.profiler.output"),
        Some(&OptionValue::Name("default".to_string()))
    );
}

#[test]
fn test_file_options_name_get_set() {
    let mut reg = OptionsRegistry::new();
    reg.register(
        "trace.output",
        OptionValue::Name("default.trace".to_string()),
        "Trace output name",
    );
    let mut opts = FileOptions::new(&reg);
    assert_eq!(opts.get_name("trace.output"), Some("default.trace"));

    opts.set(
        "trace.output",
        OptionValue::Name("custom.trace".to_string()),
    )
    .expect("should set name option");
    assert_eq!(opts.get_name("trace.output"), Some("custom.trace"));
}

#[test]
fn test_file_options_get_name_on_bool_returns_none() {
    let reg = OptionsRegistry::new();
    let opts = FileOptions::new(&reg);
    assert_eq!(opts.get_name("pp.all"), None);
}

// -- get_option returns full OptionDecl -----------------------------------

#[test]
fn test_get_option_returns_decl() {
    let reg = OptionsRegistry::new();
    let decl = reg.get_option("maxHeartbeats");
    let decl = decl.expect("maxHeartbeats should exist");
    assert_eq!(decl.name(), "maxHeartbeats");
    assert_eq!(decl.default(), &OptionValue::Nat(200_000));
    assert!(!decl.description().is_empty());
}

#[test]
fn test_get_option_nonexistent_returns_none() {
    let reg = OptionsRegistry::new();
    assert!(reg.get_option("nonexistent.option").is_none());
}

// -- register_option with pre-built OptionDecl ----------------------------

#[test]
fn test_register_option_with_decl() {
    let mut reg = OptionsRegistry::new();
    let decl = OptionDecl::new(
        "custom.depth",
        OptionValue::Nat(100),
        "Custom recursion depth",
    );
    reg.register_option("custom.depth", decl);
    let retrieved = reg.get_option("custom.depth").expect("should exist");
    assert_eq!(retrieved.name(), "custom.depth");
    assert_eq!(retrieved.default(), &OptionValue::Nat(100));
    assert_eq!(retrieved.description(), "Custom recursion depth");
}

// -- validate_option ------------------------------------------------------

#[test]
fn test_validate_option_correct_type() {
    let reg = OptionsRegistry::new();
    reg.validate_option("maxHeartbeats", &OptionValue::Nat(500_000))
        .expect("Nat value for Nat option should pass");
    reg.validate_option("pp.all", &OptionValue::Bool(true))
        .expect("Bool value for Bool option should pass");
}

#[test]
fn test_validate_option_wrong_type() {
    let reg = OptionsRegistry::new();
    let err = reg
        .validate_option("maxHeartbeats", &OptionValue::Bool(true))
        .unwrap_err();
    assert!(matches!(err, OptionError::TypeMismatch { .. }));
    let msg = err.to_string();
    assert!(msg.contains("Nat"), "error: {msg}");
    assert!(msg.contains("Bool"), "error: {msg}");
}

#[test]
fn test_validate_option_unknown() {
    let reg = OptionsRegistry::new();
    let err = reg
        .validate_option("nonexistent", &OptionValue::Bool(false))
        .unwrap_err();
    assert!(matches!(err, OptionError::UnknownOption { .. }));
}

#[test]
fn test_validate_option_name_type_mismatch() {
    let mut reg = OptionsRegistry::new();
    reg.register(
        "trace.name",
        OptionValue::Name("default".to_string()),
        "A name option",
    );
    let err = reg
        .validate_option("trace.name", &OptionValue::Nat(42))
        .unwrap_err();
    assert!(matches!(err, OptionError::TypeMismatch { .. }));
    let msg = err.to_string();
    assert!(msg.contains("Name"), "error: {msg}");
    assert!(msg.contains("Nat"), "error: {msg}");
}

// -- OptionDecl construction ----------------------------------------------

#[test]
fn test_option_decl_construction() {
    let decl = OptionDecl::new("my.option", OptionValue::Bool(false), "My custom option");
    assert_eq!(decl.name(), "my.option");
    assert_eq!(decl.default(), &OptionValue::Bool(false));
    assert_eq!(decl.description(), "My custom option");
}

// -- OptionValue all variants ---------------------------------------------

#[test]
fn test_option_value_all_variants() {
    let bool_val = OptionValue::Bool(true);
    let nat_val = OptionValue::Nat(42);
    let str_val = OptionValue::String("hello".to_string());
    let name_val = OptionValue::Name("Lean.Meta".to_string());

    assert_eq!(bool_val.kind_name(), "Bool");
    assert_eq!(nat_val.kind_name(), "Nat");
    assert_eq!(str_val.kind_name(), "String");
    assert_eq!(name_val.kind_name(), "Name");

    // Each variant is distinct
    assert_ne!(bool_val, nat_val);
    assert_ne!(str_val, name_val);
}

// -- Registry default has builtins ----------------------------------------

#[test]
fn test_registry_default_has_builtins() {
    let reg = OptionsRegistry::default();
    // All five requested built-ins must be present
    assert!(reg.is_registered("pp.all"));
    assert!(reg.is_registered("pp.notation"));
    assert!(reg.is_registered("pp.universes"));
    assert!(reg.is_registered("maxHeartbeats"));
    assert!(reg.is_registered("maxRecDepth"));

    // Verify their types
    assert_eq!(reg.get_default("pp.all"), Some(&OptionValue::Bool(false)));
    assert_eq!(
        reg.get_default("pp.notation"),
        Some(&OptionValue::Bool(true))
    );
    assert_eq!(
        reg.get_default("pp.universes"),
        Some(&OptionValue::Bool(false))
    );
    assert_eq!(
        reg.get_default("maxHeartbeats"),
        Some(&OptionValue::Nat(200_000))
    );
    assert_eq!(reg.get_default("maxRecDepth"), Some(&OptionValue::Nat(512)));
}
