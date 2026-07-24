// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the extended macro hygiene module (level 3: `macro_hygiene_ext3`).

use clean_kernel::Name;

use crate::macro_hygiene_ext3::*;

// ===========================================================================
// 1. ScopeColor
// ===========================================================================

#[test]
fn test_scope_color_transparent() {
    let c = ScopeColor::transparent();
    assert!(c.is_transparent());
    assert_eq!(c.id(), 0);
}

#[test]
fn test_scope_color_fresh_unique() {
    let a = ScopeColor::fresh();
    let b = ScopeColor::fresh();
    assert_ne!(a, b);
    assert!(!a.is_transparent());
    assert!(!b.is_transparent());
}

#[test]
fn test_scope_color_display_transparent() {
    assert_eq!(
        format!("{}", ScopeColor::transparent()),
        "color:transparent"
    );
}

#[test]
fn test_scope_color_display_fresh() {
    let c = ScopeColor::fresh();
    let s = format!("{c}");
    assert!(s.starts_with("color#"));
}

// ===========================================================================
// 2. BindingStatus
// ===========================================================================

#[test]
fn test_binding_status_display() {
    assert_eq!(format!("{}", BindingStatus::Bound), "bound");
    assert_eq!(format!("{}", BindingStatus::Free), "free");
}

// ===========================================================================
// 3. Context construction and scope depth
// ===========================================================================

#[test]
fn test_new_context_starts_at_root() {
    let ctx = HygieneExt3Ctx::new();
    assert!(ctx.current_color().is_transparent());
    assert_eq!(ctx.scope_depth(), 1);
}

#[test]
fn test_default_context_equals_new() {
    let a = HygieneExt3Ctx::new();
    let b = HygieneExt3Ctx::default();
    assert_eq!(a.scope_depth(), b.scope_depth());
    assert_eq!(a.current_color(), b.current_color());
}

#[test]
fn test_enter_colored_scope_increases_depth() {
    let mut ctx = HygieneExt3Ctx::new();
    let color = ctx.enter_colored_scope().unwrap();
    assert_eq!(ctx.scope_depth(), 2);
    assert_eq!(ctx.current_color(), color);
    assert!(!color.is_transparent());
}

#[test]
fn test_leave_colored_scope_decreases_depth() {
    let mut ctx = HygieneExt3Ctx::new();
    let color = ctx.enter_colored_scope().unwrap();
    let popped = ctx.leave_colored_scope().unwrap();
    assert_eq!(popped, color);
    assert_eq!(ctx.scope_depth(), 1);
    assert!(ctx.current_color().is_transparent());
}

#[test]
fn test_leave_scope_underflow() {
    let mut ctx = HygieneExt3Ctx::new();
    let err = ctx.leave_colored_scope().unwrap_err();
    assert!(matches!(err, HygieneExt3Error::ScopeUnderflow));
}

#[test]
fn test_color_stack_returns_full_stack() {
    let mut ctx = HygieneExt3Ctx::new();
    let c1 = ctx.enter_colored_scope().unwrap();
    let c2 = ctx.enter_colored_scope().unwrap();
    let stack = ctx.color_stack();
    assert_eq!(stack.len(), 3);
    assert!(stack[0].is_transparent());
    assert_eq!(stack[1], c1);
    assert_eq!(stack[2], c2);
}

#[test]
fn test_is_color_active_root_always_active() {
    let ctx = HygieneExt3Ctx::new();
    assert!(ctx.is_color_active(ScopeColor::transparent()));
}

#[test]
fn test_is_color_active_for_pushed_color() {
    let mut ctx = HygieneExt3Ctx::new();
    let c = ctx.enter_colored_scope().unwrap();
    assert!(ctx.is_color_active(c));
}

#[test]
fn test_is_color_active_false_for_popped_color() {
    let mut ctx = HygieneExt3Ctx::new();
    let c = ctx.enter_colored_scope().unwrap();
    ctx.leave_colored_scope().unwrap();
    assert!(!ctx.is_color_active(c));
}

// ===========================================================================
// 4. Name binding
// ===========================================================================

#[test]
fn test_introduce_binding_visible() {
    let mut ctx = HygieneExt3Ctx::new();
    let name = Name::from_string("x");
    ctx.introduce_binding(&name, false);
    assert_eq!(ctx.bindings_for(&name).len(), 1);
}

#[test]
fn test_introduce_binding_no_duplicates() {
    let mut ctx = HygieneExt3Ctx::new();
    let name = Name::from_string("x");
    ctx.introduce_binding(&name, false);
    ctx.introduce_binding(&name, false);
    assert_eq!(ctx.bindings_for(&name).len(), 1);
}

#[test]
fn test_introduce_binding_different_scopes() {
    let mut ctx = HygieneExt3Ctx::new();
    let name = Name::from_string("x");
    ctx.introduce_binding(&name, false);
    ctx.enter_colored_scope().unwrap();
    ctx.introduce_binding(&name, true);
    assert_eq!(ctx.bindings_for(&name).len(), 2);
}

#[test]
fn test_names_in_color() {
    let mut ctx = HygieneExt3Ctx::new();
    let a = Name::from_string("a");
    let b = Name::from_string("b");
    ctx.introduce_binding(&a, false);
    ctx.introduce_binding(&b, false);
    let root_color = ScopeColor::transparent();
    let names = ctx.names_in_color(root_color);
    assert_eq!(names.len(), 2);
    assert!(names.iter().any(|n| n.to_string() == "a"));
    assert!(names.iter().any(|n| n.to_string() == "b"));
}

#[test]
fn test_names_in_color_empty_for_unused_color() {
    let ctx = HygieneExt3Ctx::new();
    let names = ctx.names_in_color(ScopeColor::fresh());
    assert!(names.is_empty());
}

// ===========================================================================
// 5. Binding status analysis
// ===========================================================================

#[test]
fn test_binding_status_free_for_unknown_name() {
    let ctx = HygieneExt3Ctx::new();
    let name = Name::from_string("unknown");
    assert_eq!(ctx.binding_status(&name), BindingStatus::Free);
}

#[test]
fn test_binding_status_bound_in_root() {
    let mut ctx = HygieneExt3Ctx::new();
    let name = Name::from_string("x");
    ctx.introduce_binding(&name, false);
    assert_eq!(ctx.binding_status(&name), BindingStatus::Bound);
}

#[test]
fn test_binding_status_bound_from_parent() {
    let mut ctx = HygieneExt3Ctx::new();
    let name = Name::from_string("x");
    ctx.introduce_binding(&name, false);
    ctx.enter_colored_scope().unwrap();
    assert_eq!(ctx.binding_status(&name), BindingStatus::Bound);
}

#[test]
fn test_binding_status_free_after_scope_exit() {
    let mut ctx = HygieneExt3Ctx::new();
    let color = ctx.enter_colored_scope().unwrap();
    let name = Name::from_string("local");
    ctx.introduce_binding(&name, false);
    assert_eq!(ctx.binding_status(&name), BindingStatus::Bound);
    ctx.leave_colored_scope().unwrap();
    // The binding was in the now-popped scope, no root binding exists.
    assert_eq!(ctx.binding_status(&name), BindingStatus::Free);
    let _ = color;
}

// ===========================================================================
// 6. Name resolution
// ===========================================================================

#[test]
fn test_resolve_name_success() {
    let mut ctx = HygieneExt3Ctx::new();
    let name = Name::from_string("x");
    ctx.introduce_binding(&name, false);
    let binding = ctx.resolve_name(&name).unwrap();
    assert_eq!(binding.name, name);
    assert!(binding.color.is_transparent());
}

#[test]
fn test_resolve_name_unresolved() {
    let mut ctx = HygieneExt3Ctx::new();
    let name = Name::from_string("missing");
    let err = ctx.resolve_name(&name).unwrap_err();
    assert!(matches!(err, HygieneExt3Error::Unresolved { .. }));
}

#[test]
fn test_resolve_name_picks_innermost() {
    let mut ctx = HygieneExt3Ctx::new();
    let name = Name::from_string("x");
    ctx.introduce_binding(&name, false);
    let inner_color = ctx.enter_colored_scope().unwrap();
    ctx.introduce_binding(&name, true);
    let binding = ctx.resolve_name(&name).unwrap();
    assert_eq!(binding.color, inner_color);
    assert!(binding.macro_generated);
}

// ===========================================================================
// 7. Cross-scope reference tracking
// ===========================================================================

#[test]
fn test_track_reference_same_scope_no_xref() {
    let mut ctx = HygieneExt3Ctx::new();
    let name = Name::from_string("x");
    ctx.introduce_binding(&name, false);
    ctx.track_reference(&name);
    assert!(ctx.cross_scope_refs().is_empty());
}

#[test]
fn test_track_reference_cross_scope() {
    let mut ctx = HygieneExt3Ctx::new();
    let name = Name::from_string("x");
    ctx.introduce_binding(&name, false);
    ctx.enter_colored_scope().unwrap();
    ctx.track_reference(&name);
    assert_eq!(ctx.cross_scope_refs().len(), 1);
    let xref = &ctx.cross_scope_refs()[0];
    assert_eq!(xref.name, name);
    assert!(xref.definition_scope.is_transparent());
    assert!(!xref.reference_scope.is_transparent());
}

#[test]
fn test_track_reference_unbound_records_violation() {
    let mut ctx = HygieneExt3Ctx::new();
    let name = Name::from_string("unbound");
    ctx.track_reference(&name);
    assert_eq!(ctx.violations().len(), 1);
    assert_eq!(
        ctx.violations()[0].kind,
        Ext3ViolationKind::UnboundReference
    );
}

#[test]
fn test_cross_scope_ref_display() {
    let xref = CrossScopeRef {
        name: Name::from_string("x"),
        reference_scope: ScopeColor::fresh(),
        definition_scope: ScopeColor::transparent(),
    };
    let s = format!("{xref}");
    assert!(s.contains("`x`"));
    assert!(s.contains("color:transparent"));
}

// ===========================================================================
// 8. Capture analysis
// ===========================================================================

#[test]
fn test_detect_capture_none_when_no_conflict() {
    let mut ctx = HygieneExt3Ctx::new();
    let name = Name::from_string("x");
    ctx.introduce_binding(&name, false);
    assert!(ctx.detect_capture(&name).is_none());
}

#[test]
fn test_detect_capture_found() {
    let mut ctx = HygieneExt3Ctx::new();
    let name = Name::from_string("x");
    ctx.introduce_binding(&name, false);
    ctx.enter_colored_scope().unwrap();
    ctx.introduce_binding(&name, true);
    let report = ctx.detect_capture(&name).expect("should find capture");
    assert_eq!(report.captured_name, name);
    assert!(report.original_scope.is_transparent());
    assert!(report.fix_suggestion.contains("gensym"));
}

#[test]
fn test_detect_all_captures() {
    let mut ctx = HygieneExt3Ctx::new();
    let x = Name::from_string("x");
    let y = Name::from_string("y");
    ctx.introduce_binding(&x, false);
    ctx.introduce_binding(&y, false);
    ctx.enter_colored_scope().unwrap();
    ctx.introduce_binding(&x, true);
    // y is not captured
    let reports = ctx.detect_all_captures();
    assert_eq!(reports.len(), 1);
    assert_eq!(reports[0].captured_name, x);
}

#[test]
fn test_captures_accumulate() {
    let mut ctx = HygieneExt3Ctx::new();
    let name = Name::from_string("z");
    ctx.introduce_binding(&name, false);
    ctx.enter_colored_scope().unwrap();
    ctx.introduce_binding(&name, true);
    ctx.detect_capture(&name);
    ctx.detect_capture(&name);
    // Should accumulate (both calls find the same capture)
    assert_eq!(ctx.captures().len(), 2);
}

#[test]
fn test_capture_report_display() {
    let report = CaptureReport {
        captured_name: Name::from_string("foo"),
        capturer_scope: ScopeColor::fresh(),
        original_scope: ScopeColor::transparent(),
        fix_suggestion: "rename it".to_owned(),
    };
    let s = format!("{report}");
    assert!(s.contains("`foo`"));
    assert!(s.contains("rename it"));
}

// ===========================================================================
// 9. Violation reporting
// ===========================================================================

#[test]
fn test_record_violation() {
    let mut ctx = HygieneExt3Ctx::new();
    let name = Name::from_string("v");
    ctx.record_violation(
        &name,
        Ext3ViolationKind::ScopeLeak,
        "test violation",
        Some("fix it"),
    );
    assert_eq!(ctx.violations().len(), 1);
    assert_eq!(ctx.violations()[0].kind, Ext3ViolationKind::ScopeLeak);
    assert_eq!(
        ctx.violations()[0].fix_suggestion.as_deref(),
        Some("fix it")
    );
}

#[test]
fn test_record_violation_without_fix() {
    let mut ctx = HygieneExt3Ctx::new();
    let name = Name::from_string("v");
    ctx.record_violation(&name, Ext3ViolationKind::InvariantBroken, "broken", None);
    assert!(ctx.violations()[0].fix_suggestion.is_none());
}

#[test]
fn test_take_violations_drains() {
    let mut ctx = HygieneExt3Ctx::new();
    let name = Name::from_string("v");
    ctx.record_violation(&name, Ext3ViolationKind::ScopeLeak, "leak", None);
    let vs = ctx.take_violations();
    assert_eq!(vs.len(), 1);
    assert!(ctx.violations().is_empty());
}

#[test]
fn test_violation_report_empty() {
    let ctx = HygieneExt3Ctx::new();
    let report = ctx.violation_report();
    assert_eq!(report, "No hygiene violations detected.");
}

#[test]
fn test_violation_report_nonempty() {
    let mut ctx = HygieneExt3Ctx::new();
    let name = Name::from_string("x");
    ctx.record_violation(&name, Ext3ViolationKind::ScopeLeak, "leak", None);
    let report = ctx.violation_report();
    assert!(report.contains("1 hygiene violation(s)"));
    assert!(report.contains("ScopeLeak"));
}

#[test]
fn test_ext3_violation_display() {
    let v = Ext3Violation {
        name: Name::from_string("x"),
        kind: Ext3ViolationKind::AccidentalCapture,
        scope: ScopeColor::transparent(),
        message: "captured".to_owned(),
        fix_suggestion: Some("rename".to_owned()),
    };
    let s = format!("{v}");
    assert!(s.contains("AccidentalCapture"));
    assert!(s.contains("captured"));
    assert!(s.contains("rename"));
}

#[test]
fn test_ext3_violation_display_no_fix() {
    let v = Ext3Violation {
        name: Name::from_string("x"),
        kind: Ext3ViolationKind::ScopeLeak,
        scope: ScopeColor::transparent(),
        message: "leaked".to_owned(),
        fix_suggestion: None,
    };
    let s = format!("{v}");
    assert!(!s.contains("fix:"));
}

#[test]
fn test_ext3_violation_kind_display() {
    assert_eq!(
        format!("{}", Ext3ViolationKind::AccidentalCapture),
        "AccidentalCapture"
    );
    assert_eq!(format!("{}", Ext3ViolationKind::ScopeLeak), "ScopeLeak");
    assert_eq!(
        format!("{}", Ext3ViolationKind::UnboundReference),
        "UnboundReference"
    );
    assert_eq!(
        format!("{}", Ext3ViolationKind::ColorBoundaryViolation),
        "ColorBoundaryViolation"
    );
    assert_eq!(
        format!("{}", Ext3ViolationKind::InvariantBroken),
        "InvariantBroken"
    );
}

// ===========================================================================
// 10. Hygiene invariant validation
// ===========================================================================

#[test]
fn test_validate_invariants_clean() {
    let mut ctx = HygieneExt3Ctx::new();
    let vs = ctx.validate_invariants();
    assert!(vs.is_empty());
}

#[test]
fn test_validate_invariants_with_scopes() {
    let mut ctx = HygieneExt3Ctx::new();
    ctx.enter_colored_scope().unwrap();
    ctx.enter_colored_scope().unwrap();
    let vs = ctx.validate_invariants();
    assert!(vs.is_empty());
}

// ===========================================================================
// 11. Full audit
// ===========================================================================

#[test]
fn test_full_audit_clean() {
    let mut ctx = HygieneExt3Ctx::new();
    let name = Name::from_string("x");
    ctx.introduce_binding(&name, false);
    let vs = ctx.full_audit();
    assert!(vs.is_empty());
}

#[test]
fn test_full_audit_detects_capture() {
    let mut ctx = HygieneExt3Ctx::new();
    let name = Name::from_string("x");
    ctx.introduce_binding(&name, false);
    ctx.enter_colored_scope().unwrap();
    ctx.introduce_binding(&name, true);
    let vs = ctx.full_audit();
    // Should detect the capture
    assert!(
        vs.iter()
            .any(|v| v.kind == Ext3ViolationKind::AccidentalCapture)
            || ctx.captures().iter().any(|c| c.captured_name == name)
    );
}

#[test]
fn test_full_audit_detects_leak_after_scope_exit() {
    let mut ctx = HygieneExt3Ctx::new();
    let name = Name::from_string("local");
    ctx.enter_colored_scope().unwrap();
    ctx.introduce_binding(&name, false);
    ctx.leave_colored_scope().unwrap();
    // Now the binding is from a popped scope.
    let vs = ctx.full_audit();
    assert!(vs.iter().any(|v| v.kind == Ext3ViolationKind::ScopeLeak));
}

// ===========================================================================
// 12. Scope statistics
// ===========================================================================

#[test]
fn test_statistics_initial() {
    let ctx = HygieneExt3Ctx::new();
    let stats = ctx.statistics();
    assert_eq!(stats.max_depth_reached, 0);
    assert_eq!(stats.total_colors_allocated, 0);
    assert_eq!(stats.total_violations, 0);
}

#[test]
fn test_statistics_after_operations() {
    let mut ctx = HygieneExt3Ctx::new();
    ctx.enter_colored_scope().unwrap();
    let name = Name::from_string("x");
    ctx.introduce_binding(&name, false);
    ctx.track_reference(&name);
    let stats = ctx.statistics();
    assert_eq!(stats.total_colors_allocated, 1);
    assert_eq!(stats.total_bindings_introduced, 1);
    assert!(stats.total_references_tracked >= 1);
    assert_eq!(stats.max_depth_reached, 2);
}

#[test]
fn test_statistics_captures_counted() {
    let mut ctx = HygieneExt3Ctx::new();
    let name = Name::from_string("x");
    ctx.introduce_binding(&name, false);
    ctx.enter_colored_scope().unwrap();
    ctx.introduce_binding(&name, true);
    ctx.detect_capture(&name);
    assert_eq!(ctx.statistics().total_captures_detected, 1);
}

#[test]
fn test_statistics_violations_counted() {
    let mut ctx = HygieneExt3Ctx::new();
    let name = Name::from_string("v");
    ctx.record_violation(&name, Ext3ViolationKind::ScopeLeak, "test", None);
    assert_eq!(ctx.statistics().total_violations, 1);
}

#[test]
fn test_statistics_cross_scope_refs_counted() {
    let mut ctx = HygieneExt3Ctx::new();
    let name = Name::from_string("x");
    ctx.introduce_binding(&name, false);
    ctx.enter_colored_scope().unwrap();
    ctx.track_reference(&name);
    assert_eq!(ctx.statistics().cross_scope_refs, 1);
}

// ===========================================================================
// 13. Error types
// ===========================================================================

#[test]
fn test_error_display_scope_underflow() {
    let err = HygieneExt3Error::ScopeUnderflow;
    assert!(format!("{err}").contains("underflow"));
}

#[test]
fn test_error_display_unknown_color() {
    let err = HygieneExt3Error::UnknownColor {
        color: ScopeColor::fresh(),
    };
    assert!(format!("{err}").contains("unknown color"));
}

#[test]
fn test_error_display_unresolved() {
    let err = HygieneExt3Error::Unresolved {
        name: "x".to_owned(),
        scope: ScopeColor::transparent(),
    };
    assert!(format!("{err}").contains("unresolved"));
}

#[test]
fn test_error_display_depth_exceeded() {
    let err = HygieneExt3Error::DepthExceeded { max: 256 };
    assert!(format!("{err}").contains("256"));
}
