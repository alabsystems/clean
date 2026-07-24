// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::options_registry::{FileOptions, OptionError, OptionValue, OptionsRegistry};
use super::options_registry_ext::*;

// ============================================================================
// OptionCategory inference
// ============================================================================

#[test]
fn test_infer_category_pp_prefix() {
    assert_eq!(infer_category("pp.all"), OptionCategory::Pp);
    assert_eq!(infer_category("pp.universes"), OptionCategory::Pp);
    assert_eq!(infer_category("pp.notation"), OptionCategory::Pp);
    assert_eq!(infer_category("pp.proofs"), OptionCategory::Pp);
}

#[test]
fn test_infer_category_tactic_prefix() {
    assert_eq!(infer_category("tactic.hygienic"), OptionCategory::Tactic);
    assert_eq!(infer_category("tactic.timeout"), OptionCategory::Tactic);
}

#[test]
fn test_infer_category_tactic_extended_prefixes() {
    assert_eq!(infer_category("aesop.maxRuleApps"), OptionCategory::Tactic);
    assert_eq!(infer_category("simp.maxSteps"), OptionCategory::Tactic);
    assert_eq!(infer_category("mathverse.debug"), OptionCategory::Tactic);
    assert_eq!(infer_category("linarith.exponent"), OptionCategory::Tactic);
    assert_eq!(infer_category("ring.cache"), OptionCategory::Tactic);
}

#[test]
fn test_infer_category_linter_prefix() {
    assert_eq!(
        infer_category("linter.unusedVariables"),
        OptionCategory::Linter
    );
}

#[test]
fn test_infer_category_trace_prefix() {
    assert_eq!(infer_category("trace.Meta.isDefEq"), OptionCategory::Trace);
}

#[test]
fn test_infer_category_kernel_names() {
    assert_eq!(infer_category("maxHeartbeats"), OptionCategory::Kernel);
    assert_eq!(infer_category("maxRecDepth"), OptionCategory::Kernel);
    assert_eq!(infer_category("kernel.diagnostics"), OptionCategory::Kernel);
}

#[test]
fn test_infer_category_elaboration_names() {
    assert_eq!(infer_category("autoImplicit"), OptionCategory::Elaboration);
    assert_eq!(
        infer_category("relaxedAutoImplicit"),
        OptionCategory::Elaboration
    );
    assert_eq!(
        infer_category("elab.structureLike"),
        OptionCategory::Elaboration
    );
}

#[test]
fn test_infer_category_unknown_is_custom() {
    assert_eq!(infer_category("custom.myOption"), OptionCategory::Custom);
    assert_eq!(infer_category("something.else"), OptionCategory::Custom);
}

// ============================================================================
// OptionCategory title
// ============================================================================

#[test]
fn test_category_titles() {
    assert_eq!(OptionCategory::Pp.title(), "Pretty Printer");
    assert_eq!(OptionCategory::Tactic.title(), "Tactic");
    assert_eq!(OptionCategory::Elaboration.title(), "Elaboration");
    assert_eq!(OptionCategory::Kernel.title(), "Kernel");
    assert_eq!(OptionCategory::Linter.title(), "Linter");
    assert_eq!(OptionCategory::Trace.title(), "Trace");
    assert_eq!(OptionCategory::Custom.title(), "Custom");
}

#[test]
fn test_category_default_is_custom() {
    assert_eq!(OptionCategory::default(), OptionCategory::Custom);
}

// ============================================================================
// OptionChangeTracker
// ============================================================================

#[test]
fn test_change_tracker_default_is_empty() {
    let tracker = OptionChangeTracker::default();
    assert!(tracker.history.is_empty());
}

#[test]
fn test_change_tracker_record_single() {
    let mut tracker = OptionChangeTracker::default();
    let change = tracker.record(
        "maxHeartbeats",
        OptionValue::Nat(200_000),
        OptionValue::Nat(400_000),
    );
    assert_eq!(tracker.history.len(), 1);
    assert_eq!(change.name, "maxHeartbeats");
    assert_eq!(change.old_value, OptionValue::Nat(200_000));
    assert_eq!(change.new_value, OptionValue::Nat(400_000));
    assert!(change.timestamp > 0);
}

#[test]
fn test_change_tracker_record_multiple() {
    let mut tracker = OptionChangeTracker::default();
    let _ = tracker.record("a", OptionValue::Bool(false), OptionValue::Bool(true));
    let _ = tracker.record("b", OptionValue::Nat(1), OptionValue::Nat(2));
    let _ = tracker.record("a", OptionValue::Bool(true), OptionValue::Bool(false));
    assert_eq!(tracker.history.len(), 3);
    assert_eq!(tracker.history[0].name, "a");
    assert_eq!(tracker.history[1].name, "b");
    assert_eq!(tracker.history[2].name, "a");
}

#[test]
fn test_change_tracker_filter_by_name() {
    let mut tracker = OptionChangeTracker::default();
    let _ = tracker.record("pp.all", OptionValue::Bool(false), OptionValue::Bool(true));
    let _ = tracker.record(
        "maxHeartbeats",
        OptionValue::Nat(200_000),
        OptionValue::Nat(400_000),
    );
    let _ = tracker.record("pp.all", OptionValue::Bool(true), OptionValue::Bool(false));

    let pp_changes: Vec<_> = tracker
        .history
        .iter()
        .filter(|c| c.name == "pp.all")
        .collect();
    assert_eq!(pp_changes.len(), 2);

    let hb_changes: Vec<_> = tracker
        .history
        .iter()
        .filter(|c| c.name == "maxHeartbeats")
        .collect();
    assert_eq!(hb_changes.len(), 1);

    let none: Vec<_> = tracker
        .history
        .iter()
        .filter(|c| c.name == "nonexistent")
        .collect();
    assert!(none.is_empty());
}

#[test]
fn test_change_tracker_clear() {
    let mut tracker = OptionChangeTracker::default();
    let _ = tracker.record("a", OptionValue::Bool(false), OptionValue::Bool(true));
    let _ = tracker.record("b", OptionValue::Nat(1), OptionValue::Nat(2));
    assert_eq!(tracker.history.len(), 2);
    tracker.clear();
    assert!(tracker.history.is_empty());
}

// ============================================================================
// diff_options
// ============================================================================

#[test]
fn test_diff_options_no_changes() {
    let reg = OptionsRegistry::new();
    let a = FileOptions::new(&reg);
    let b = FileOptions::new(&reg);
    let diff = diff_options(&a, &b, &reg);
    assert!(diff.is_empty());
}

#[test]
fn test_diff_options_single_change() {
    let reg = OptionsRegistry::new();
    let a = FileOptions::new(&reg);
    let mut b = FileOptions::new(&reg);
    b.set("pp.all", OptionValue::Bool(true))
        .expect("should set");
    let diff = diff_options(&a, &b, &reg);
    assert_eq!(diff.len(), 1);
    assert_eq!(diff[0].name, "pp.all");
    assert_eq!(diff[0].old_value, OptionValue::Bool(false));
    assert_eq!(diff[0].new_value, OptionValue::Bool(true));
}

#[test]
fn test_diff_options_multiple_changes() {
    let reg = OptionsRegistry::new();
    let a = FileOptions::new(&reg);
    let mut b = FileOptions::new(&reg);
    b.set("pp.all", OptionValue::Bool(true)).expect("set");
    b.set("maxHeartbeats", OptionValue::Nat(400_000))
        .expect("set");
    let diff = diff_options(&a, &b, &reg);
    assert_eq!(diff.len(), 2);
}

#[test]
fn test_diff_options_symmetric() {
    let reg = OptionsRegistry::new();
    let a = FileOptions::new(&reg);
    let mut b = FileOptions::new(&reg);
    b.set("pp.all", OptionValue::Bool(true)).expect("set");
    let forward = diff_options(&a, &b, &reg);
    let reverse = diff_options(&b, &a, &reg);
    assert_eq!(forward.len(), reverse.len());
    assert_eq!(forward[0].old_value, reverse[0].new_value);
    assert_eq!(forward[0].new_value, reverse[0].old_value);
}

// ============================================================================
// OptionProfile
// ============================================================================

#[test]
fn test_profile_new_empty() {
    let p = OptionProfile::new("test", "A test profile");
    assert_eq!(p.name, "test");
    assert_eq!(p.description, "A test profile");
    assert!(p.overrides.is_empty());
}

#[test]
fn test_profile_insert_overrides() {
    let mut p = OptionProfile::new("test", "");
    p.overrides
        .insert("pp.all".to_string(), OptionValue::Bool(true));
    p.overrides
        .insert("maxHeartbeats".to_string(), OptionValue::Nat(400_000));
    assert_eq!(p.overrides.len(), 2);
}

#[test]
fn test_profile_apply_to_file_options() {
    let reg = OptionsRegistry::new();
    let mut opts = FileOptions::new(&reg);
    let mut p = OptionProfile::new("high-perf", "High performance");
    p.overrides
        .insert("maxHeartbeats".to_string(), OptionValue::Nat(800_000));
    p.overrides
        .insert("pp.all".to_string(), OptionValue::Bool(true));
    let applied = p.apply_to(&mut opts).expect("apply should succeed");
    assert_eq!(applied, 2);
    assert_eq!(opts.get_nat("maxHeartbeats"), Some(800_000));
    assert_eq!(opts.get_bool("pp.all"), Some(true));
}

#[test]
fn test_profile_apply_to_rejects_unknown() {
    let reg = OptionsRegistry::new();
    let mut opts = FileOptions::new(&reg);
    let mut p = OptionProfile::new("bad", "");
    p.overrides
        .insert("nonexistent.option".to_string(), OptionValue::Bool(true));
    let result = p.apply_to(&mut opts);
    assert!(result.is_err());
}

#[test]
fn test_profile_from_file_options_captures_overrides() {
    let reg = OptionsRegistry::new();
    let mut opts = FileOptions::new(&reg);
    opts.set("pp.all", OptionValue::Bool(true)).expect("set");
    opts.set("maxHeartbeats", OptionValue::Nat(600_000))
        .expect("set");
    let profile = OptionProfile::from_file_options(&opts, &reg);
    assert_eq!(profile.overrides.len(), 2);
    assert_eq!(
        profile.overrides.get("pp.all"),
        Some(&OptionValue::Bool(true))
    );
    assert_eq!(
        profile.overrides.get("maxHeartbeats"),
        Some(&OptionValue::Nat(600_000))
    );
}

#[test]
fn test_profile_from_file_options_default_captures_nothing() {
    let reg = OptionsRegistry::new();
    let opts = FileOptions::new(&reg);
    let profile = OptionProfile::from_file_options(&opts, &reg);
    assert!(profile.overrides.is_empty());
}

#[test]
fn test_profile_json_roundtrip() {
    let mut p = OptionProfile::new("test-profile", "For testing");
    p.overrides
        .insert("pp.all".to_string(), OptionValue::Bool(true));
    p.overrides
        .insert("maxHeartbeats".to_string(), OptionValue::Nat(999));
    let json = p.to_json_string().expect("serialize");
    let restored = OptionProfile::from_json_str(&json).expect("deserialize");
    assert_eq!(restored.name, p.name);
    assert_eq!(restored.description, p.description);
    assert_eq!(restored.overrides, p.overrides);
}

#[test]
fn test_profile_json_contains_expected_fields() {
    let mut p = OptionProfile::new("test-profile", "For testing");
    p.overrides
        .insert("pp.all".to_string(), OptionValue::Bool(true));
    let json = p.to_json_string().expect("serialize");
    assert!(json.contains("test-profile"));
    assert!(json.contains("For testing"));
    assert!(json.contains("pp.all"));
}

#[test]
fn test_profile_roundtrip_through_file_options() {
    let reg = OptionsRegistry::new();
    let mut opts = FileOptions::new(&reg);
    opts.set("pp.all", OptionValue::Bool(true)).expect("set");
    opts.set("maxHeartbeats", OptionValue::Nat(777))
        .expect("set");

    // Capture to profile.
    let profile = OptionProfile::from_file_options(&opts, &reg);

    // Apply to fresh FileOptions.
    let mut fresh = FileOptions::new(&reg);
    profile.apply_to(&mut fresh).expect("apply");

    // Same effective values.
    assert_eq!(fresh.get_bool("pp.all"), Some(true));
    assert_eq!(fresh.get_nat("maxHeartbeats"), Some(777));
}

#[test]
fn test_profile_save_and_load() {
    let mut p = OptionProfile::new("disk-test", "Save/load roundtrip");
    p.overrides
        .insert("pp.all".to_string(), OptionValue::Bool(true));
    p.overrides
        .insert("maxHeartbeats".to_string(), OptionValue::Nat(12345));

    let path = std::env::temp_dir().join("clean_test_profile.json");
    p.save_to_path(&path).expect("save");
    let loaded = OptionProfile::load_from_path(&path).expect("load");
    assert_eq!(loaded.name, "disk-test");
    assert_eq!(loaded.overrides, p.overrides);
    let _ = std::fs::remove_file(&path);
}

// ============================================================================
// ValidatedRegistry -- categories
// ============================================================================

#[test]
fn test_validated_registry_auto_categorizes() {
    let reg = OptionsRegistry::new();
    let vreg = ValidatedRegistry::new(reg);
    assert_eq!(vreg.category_of("pp.all"), Some(OptionCategory::Pp));
    assert_eq!(
        vreg.category_of("maxHeartbeats"),
        Some(OptionCategory::Kernel)
    );
    assert_eq!(
        vreg.category_of("linter.unusedVariables"),
        Some(OptionCategory::Linter)
    );
    assert_eq!(
        vreg.category_of("trace.Meta.isDefEq"),
        Some(OptionCategory::Trace)
    );
}

#[test]
fn test_validated_registry_unregistered_returns_none() {
    let reg = OptionsRegistry::new();
    let vreg = ValidatedRegistry::new(reg);
    assert_eq!(vreg.category_of("nonexistent.option"), None);
}

#[test]
fn test_validated_registry_override_category() {
    let reg = OptionsRegistry::new();
    let mut vreg = ValidatedRegistry::new(reg);
    assert_eq!(
        vreg.category_of("maxHeartbeats"),
        Some(OptionCategory::Kernel)
    );
    vreg.categorize_option("maxHeartbeats", OptionCategory::Elaboration)
        .expect("categorize");
    assert_eq!(
        vreg.category_of("maxHeartbeats"),
        Some(OptionCategory::Elaboration)
    );
}

#[test]
fn test_validated_registry_categorize_unknown_fails() {
    let reg = OptionsRegistry::new();
    let mut vreg = ValidatedRegistry::new(reg);
    let result = vreg.categorize_option("nonexistent", OptionCategory::Custom);
    assert!(result.is_err());
}

// ============================================================================
// ValidatedRegistry -- constraints
// ============================================================================

#[test]
fn test_constraint_none_accepts_any() {
    let reg = OptionsRegistry::new();
    let vreg = ValidatedRegistry::new(reg);
    vreg.validate_with_constraints("maxHeartbeats", &OptionValue::Nat(0))
        .expect("should accept 0");
    vreg.validate_with_constraints("maxHeartbeats", &OptionValue::Nat(u64::MAX))
        .expect("should accept max");
}

#[test]
fn test_constraint_nat_range_in_bounds() {
    let reg = OptionsRegistry::new();
    let mut vreg = ValidatedRegistry::new(reg);
    vreg.add_constraint("maxHeartbeats", OptionConstraint::NatRange(0, 1_000_000))
        .expect("add");
    vreg.validate_with_constraints("maxHeartbeats", &OptionValue::Nat(0))
        .expect("min accepted");
    vreg.validate_with_constraints("maxHeartbeats", &OptionValue::Nat(500_000))
        .expect("middle accepted");
    vreg.validate_with_constraints("maxHeartbeats", &OptionValue::Nat(1_000_000))
        .expect("max accepted");
}

#[test]
fn test_constraint_nat_range_out_of_bounds() {
    let reg = OptionsRegistry::new();
    let mut vreg = ValidatedRegistry::new(reg);
    vreg.add_constraint("maxHeartbeats", OptionConstraint::NatRange(100, 1_000_000))
        .expect("add");
    let err = vreg
        .validate_with_constraints("maxHeartbeats", &OptionValue::Nat(50))
        .unwrap_err();
    assert!(matches!(err, ExtOptionsError::OutOfRange { .. }));
    let msg = err.to_string();
    assert!(msg.contains("50"), "error: {msg}");
    assert!(msg.contains("100"), "error: {msg}");
    assert!(msg.contains("1000000"), "error: {msg}");
}

#[test]
fn test_constraint_nat_range_invalid_range_rejected() {
    let reg = OptionsRegistry::new();
    let mut vreg = ValidatedRegistry::new(reg);
    let result = vreg.add_constraint("maxHeartbeats", OptionConstraint::NatRange(1000, 100));
    assert!(result.is_err());
}

#[test]
fn test_constraint_nat_range_wrong_type_rejected() {
    let reg = OptionsRegistry::new();
    let mut vreg = ValidatedRegistry::new(reg);
    // pp.all is Bool, NatRange should fail
    let result = vreg.add_constraint("pp.all", OptionConstraint::NatRange(0, 100));
    assert!(result.is_err());
}

#[test]
fn test_constraint_string_one_of_accepted() {
    let mut reg = OptionsRegistry::new();
    reg.register(
        "pp.format",
        OptionValue::String("default".to_string()),
        "Format",
    );
    let mut vreg = ValidatedRegistry::new(reg);
    vreg.add_constraint(
        "pp.format",
        OptionConstraint::StringOneOf(vec![
            "default".to_string(),
            "compact".to_string(),
            "verbose".to_string(),
        ]),
    )
    .expect("add");
    vreg.validate_with_constraints("pp.format", &OptionValue::String("compact".to_string()))
        .expect("compact accepted");
}

#[test]
fn test_constraint_string_one_of_rejected() {
    let mut reg = OptionsRegistry::new();
    reg.register(
        "pp.format",
        OptionValue::String("default".to_string()),
        "Format",
    );
    let mut vreg = ValidatedRegistry::new(reg);
    vreg.add_constraint(
        "pp.format",
        OptionConstraint::StringOneOf(vec!["default".to_string(), "compact".to_string()]),
    )
    .expect("add");
    let err = vreg
        .validate_with_constraints("pp.format", &OptionValue::String("verbose".to_string()))
        .unwrap_err();
    assert!(matches!(err, ExtOptionsError::NotAllowed { .. }));
}

#[test]
fn test_constraint_string_one_of_empty_rejected() {
    let mut reg = OptionsRegistry::new();
    reg.register(
        "pp.format",
        OptionValue::String("default".to_string()),
        "Format",
    );
    let mut vreg = ValidatedRegistry::new(reg);
    let result = vreg.add_constraint("pp.format", OptionConstraint::StringOneOf(vec![]));
    assert!(result.is_err());
}

#[test]
fn test_constraint_depends_on_satisfied() {
    let reg = OptionsRegistry::new();
    let mut vreg = ValidatedRegistry::new(reg);
    vreg.add_constraint(
        "pp.universes",
        OptionConstraint::DependsOn("pp.all".to_string(), OptionValue::Bool(true)),
    )
    .expect("add");
    let mut opts = FileOptions::new(vreg.registry());
    opts.set("pp.all", OptionValue::Bool(true)).expect("set");
    vreg.validate_with_file_options("pp.universes", &OptionValue::Bool(true), &opts)
        .expect("dependency met");
}

#[test]
fn test_constraint_depends_on_violated() {
    let reg = OptionsRegistry::new();
    let mut vreg = ValidatedRegistry::new(reg);
    vreg.add_constraint(
        "pp.universes",
        OptionConstraint::DependsOn("pp.all".to_string(), OptionValue::Bool(true)),
    )
    .expect("add");
    let opts = FileOptions::new(vreg.registry());
    // pp.all defaults to false.
    let err = vreg
        .validate_with_file_options("pp.universes", &OptionValue::Bool(true), &opts)
        .unwrap_err();
    assert!(matches!(err, ExtOptionsError::DependencyNotMet { .. }));
}

#[test]
fn test_constraint_depends_on_without_context_uses_defaults() {
    let reg = OptionsRegistry::new();
    let mut vreg = ValidatedRegistry::new(reg);
    vreg.add_constraint(
        "pp.universes",
        OptionConstraint::DependsOn("pp.all".to_string(), OptionValue::Bool(true)),
    )
    .expect("add");
    // validate_with_constraints uses default FileOptions, so pp.all=false
    // This should fail the dependency check.
    let err = vreg
        .validate_with_constraints("pp.universes", &OptionValue::Bool(true))
        .unwrap_err();
    assert!(matches!(err, ExtOptionsError::DependencyNotMet { .. }));
}

#[test]
fn test_constraint_base_error_forwarded() {
    let reg = OptionsRegistry::new();
    let vreg = ValidatedRegistry::new(reg);
    let err = vreg
        .validate_with_constraints("nonexistent", &OptionValue::Bool(true))
        .unwrap_err();
    assert!(matches!(
        err,
        ExtOptionsError::Base(OptionError::UnknownOption { .. })
    ));
}

#[test]
fn test_constraint_type_mismatch_forwarded() {
    let reg = OptionsRegistry::new();
    let vreg = ValidatedRegistry::new(reg);
    let err = vreg
        .validate_with_constraints("maxHeartbeats", &OptionValue::Bool(true))
        .unwrap_err();
    assert!(matches!(
        err,
        ExtOptionsError::Base(OptionError::TypeMismatch { .. })
    ));
}

// ============================================================================
// ValidatedRegistry -- apply_profile
// ============================================================================

#[test]
fn test_apply_profile_with_constraints() {
    let reg = OptionsRegistry::new();
    let mut vreg = ValidatedRegistry::new(reg);
    vreg.add_constraint("maxHeartbeats", OptionConstraint::NatRange(100, 1_000_000))
        .expect("add");

    let mut profile = OptionProfile::new("test", "");
    profile
        .overrides
        .insert("maxHeartbeats".to_string(), OptionValue::Nat(500_000));

    let mut opts = FileOptions::new(vreg.registry());
    let applied = vreg.apply_profile(&profile, &mut opts).expect("apply");
    assert_eq!(applied, 1);
    assert_eq!(opts.get_nat("maxHeartbeats"), Some(500_000));
}

#[test]
fn test_apply_profile_rejects_out_of_range() {
    let reg = OptionsRegistry::new();
    let mut vreg = ValidatedRegistry::new(reg);
    vreg.add_constraint("maxHeartbeats", OptionConstraint::NatRange(100, 1_000_000))
        .expect("add");

    let mut profile = OptionProfile::new("bad", "");
    profile
        .overrides
        .insert("maxHeartbeats".to_string(), OptionValue::Nat(50));

    let mut opts = FileOptions::new(vreg.registry());
    let result = vreg.apply_profile(&profile, &mut opts);
    assert!(result.is_err());
}

// ============================================================================
// Documentation generation
// ============================================================================

#[test]
fn test_generate_option_docs_has_header() {
    let reg = OptionsRegistry::new();
    let vreg = ValidatedRegistry::new(reg);
    let docs = generate_option_docs(&vreg);
    assert!(docs.starts_with("# Option Reference"));
}

#[test]
fn test_generate_option_docs_has_category_summary() {
    let reg = OptionsRegistry::new();
    let vreg = ValidatedRegistry::new(reg);
    let docs = generate_option_docs(&vreg);
    assert!(docs.contains("| Category | Count |"));
}

#[test]
fn test_generate_option_docs_has_categories() {
    let reg = OptionsRegistry::new();
    let vreg = ValidatedRegistry::new(reg);
    let docs = generate_option_docs(&vreg);
    assert!(docs.contains("## Kernel"));
    assert!(docs.contains("## Pretty Printer"));
    assert!(docs.contains("## Linter"));
}

#[test]
fn test_generate_option_docs_has_table_rows() {
    let reg = OptionsRegistry::new();
    let vreg = ValidatedRegistry::new(reg);
    let docs = generate_option_docs(&vreg);
    assert!(docs.contains("| `maxHeartbeats`"));
    assert!(docs.contains("| `pp.all`"));
    assert!(docs.contains("| `linter.unusedVariables`"));
}

#[test]
fn test_generate_option_docs_includes_constraint_info() {
    let mut reg = OptionsRegistry::new();
    reg.register(
        "pp.format",
        OptionValue::String("default".to_string()),
        "Format mode",
    );
    let mut vreg = ValidatedRegistry::new(reg);
    vreg.add_constraint(
        "pp.format",
        OptionConstraint::StringOneOf(vec!["default".to_string(), "compact".to_string()]),
    )
    .expect("add");
    let docs = generate_option_docs(&vreg);
    assert!(docs.contains("StringOneOf"));
}

#[test]
fn test_generate_option_docs_skips_empty_categories() {
    let reg = OptionsRegistry::new();
    let vreg = ValidatedRegistry::new(reg);
    let docs = generate_option_docs(&vreg);
    // No tactic options in base registry.
    assert!(!docs.contains("## Tactic"));
}

// ============================================================================
// ExtOptionsError display
// ============================================================================

#[test]
fn test_ext_error_out_of_range_display() {
    let err = ExtOptionsError::OutOfRange {
        name: "test".to_string(),
        value: 50,
        min: 100,
        max: 1000,
    };
    let msg = err.to_string();
    assert!(msg.contains("test"));
    assert!(msg.contains("50"));
    assert!(msg.contains("100"));
    assert!(msg.contains("1000"));
}

#[test]
fn test_ext_error_not_allowed_display() {
    let err = ExtOptionsError::NotAllowed {
        name: "format".to_string(),
        value: "bad".to_string(),
        allowed: vec!["a".to_string(), "b".to_string()],
    };
    let msg = err.to_string();
    assert!(msg.contains("format"));
    assert!(msg.contains("bad"));
}

#[test]
fn test_ext_error_dependency_not_met_display() {
    let err = ExtOptionsError::DependencyNotMet {
        name: "pp.universes".to_string(),
        dep_name: "pp.all".to_string(),
        required: "true".to_string(),
        actual: "false".to_string(),
    };
    let msg = err.to_string();
    assert!(msg.contains("pp.universes"));
    assert!(msg.contains("pp.all"));
    assert!(msg.contains("true"));
    assert!(msg.contains("false"));
}

#[test]
fn test_ext_error_constraint_type_mismatch_display() {
    let err = ExtOptionsError::ConstraintTypeMismatch {
        name: "pp.all".to_string(),
        constraint: "NatRange",
        actual: "Bool",
    };
    let msg = err.to_string();
    assert!(msg.contains("pp.all"));
    assert!(msg.contains("NatRange"));
    assert!(msg.contains("Bool"));
}

#[test]
fn test_ext_error_serialization_display() {
    let err = ExtOptionsError::Serialization {
        message: "bad json".to_string(),
    };
    let msg = err.to_string();
    assert!(msg.contains("serialize"));
    assert!(msg.contains("bad json"));
}

#[test]
fn test_ext_error_deserialization_display() {
    let err = ExtOptionsError::Deserialization {
        message: "unexpected token".to_string(),
    };
    let msg = err.to_string();
    assert!(msg.contains("deserialize"));
    assert!(msg.contains("unexpected token"));
}

#[test]
fn test_ext_error_from_option_error() {
    let base = OptionError::UnknownOption {
        name: "foo".to_string(),
    };
    let ext: ExtOptionsError = base.into();
    assert!(matches!(
        ext,
        ExtOptionsError::Base(OptionError::UnknownOption { .. })
    ));
}

// ============================================================================
// OptionConstraint::None removes constraints
// ============================================================================

#[test]
fn test_constraint_none_removes_existing() {
    let reg = OptionsRegistry::new();
    let mut vreg = ValidatedRegistry::new(reg);
    vreg.add_constraint("maxHeartbeats", OptionConstraint::NatRange(100, 1_000_000))
        .expect("add");
    // Adding None should remove the constraint
    vreg.add_constraint("maxHeartbeats", OptionConstraint::None)
        .expect("remove");
    // Should now accept any value
    vreg.validate_with_constraints("maxHeartbeats", &OptionValue::Nat(1))
        .expect("accept");
}
