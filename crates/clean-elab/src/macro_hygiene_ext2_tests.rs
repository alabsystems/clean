// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the extended macro hygiene module (`macro_hygiene_ext2`).

use clean_kernel::Name;

use crate::macro_hygiene_ext2::*;

// ===========================================================================
// 1. Scope stamping
// ===========================================================================

#[test]
fn test_scope_stamp_root_is_root() {
    assert!(ScopeStamp::root().is_root());
    assert_eq!(ScopeStamp::root().id(), 0);
}

#[test]
fn test_scope_stamp_fresh_is_unique() {
    let a = ScopeStamp::fresh();
    let b = ScopeStamp::fresh();
    assert_ne!(a, b);
    assert!(!a.is_root());
    assert!(!b.is_root());
}

#[test]
fn test_scope_stamp_display() {
    let s = ScopeStamp::root();
    assert_eq!(format!("{s}"), "scope#0");
}

#[test]
fn test_enter_scope_increases_depth() {
    let mut ctx = HygieneExt2Ctx::new();
    assert_eq!(ctx.scope_depth(), 1);
    ctx.enter_scope();
    assert_eq!(ctx.scope_depth(), 2);
    ctx.enter_scope();
    assert_eq!(ctx.scope_depth(), 3);
}

#[test]
fn test_leave_scope_decreases_depth() {
    let mut ctx = HygieneExt2Ctx::new();
    let s = ctx.enter_scope();
    assert_eq!(ctx.scope_depth(), 2);
    let popped = ctx.leave_scope().expect("should succeed");
    assert_eq!(popped, s);
    assert_eq!(ctx.scope_depth(), 1);
}

#[test]
fn test_leave_scope_underflow() {
    let mut ctx = HygieneExt2Ctx::new();
    let err = ctx.leave_scope().unwrap_err();
    assert!(matches!(err, HygieneExt2Error::ScopeUnderflow));
}

#[test]
fn test_current_scope_tracks_stack() {
    let mut ctx = HygieneExt2Ctx::new();
    assert!(ctx.current_scope().is_root());
    let s1 = ctx.enter_scope();
    assert_eq!(ctx.current_scope(), s1);
    let s2 = ctx.enter_scope();
    assert_eq!(ctx.current_scope(), s2);
    ctx.leave_scope().unwrap();
    assert_eq!(ctx.current_scope(), s1);
}

// ===========================================================================
// 2. Name resolution in macro context
// ===========================================================================

#[test]
fn test_resolve_name_simple() {
    let mut ctx = HygieneExt2Ctx::new();
    let n = Name::from_string("x");
    ctx.introduce_binding(&n, false);
    let binding = ctx.resolve_name(&n).expect("should resolve");
    assert_eq!(binding.name, n);
    assert!(!binding.macro_generated);
}

#[test]
fn test_resolve_name_unresolved() {
    let mut ctx = HygieneExt2Ctx::new();
    let n = Name::from_string("nonexistent");
    let err = ctx.resolve_name(&n).unwrap_err();
    assert!(matches!(err, HygieneExt2Error::Unresolved { .. }));
}

#[test]
fn test_resolve_name_in_nested_scope() {
    let mut ctx = HygieneExt2Ctx::new();
    let n = Name::from_string("x");
    ctx.introduce_binding(&n, false);
    ctx.enter_scope();
    // Name introduced in root should be visible in nested scope.
    let binding = ctx.resolve_name(&n).expect("should resolve");
    assert_eq!(binding.name, n);
}

#[test]
fn test_resolve_name_shadowed_by_inner_scope() {
    let mut ctx = HygieneExt2Ctx::new();
    let n = Name::from_string("x");
    ctx.introduce_binding(&n, false);
    let inner = ctx.enter_scope();
    ctx.introduce_binding(&n, true);
    let binding = ctx.resolve_name(&n).expect("should resolve");
    assert_eq!(binding.scope, inner);
    assert!(binding.macro_generated);
}

#[test]
fn test_resolve_after_leaving_scope() {
    let mut ctx = HygieneExt2Ctx::new();
    let n = Name::from_string("y");
    ctx.enter_scope();
    ctx.introduce_binding(&n, true);
    ctx.leave_scope().unwrap();
    // The binding was in a scope that is no longer on the stack.
    let err = ctx.resolve_name(&n).unwrap_err();
    assert!(matches!(err, HygieneExt2Error::Unresolved { .. }));
}

#[test]
fn test_resolution_counter_increments() {
    let mut ctx = HygieneExt2Ctx::new();
    let n = Name::from_string("z");
    ctx.introduce_binding(&n, false);
    ctx.resolve_name(&n).unwrap();
    ctx.resolve_name(&n).unwrap();
    assert_eq!(ctx.stats().resolutions, 2);
}

// ===========================================================================
// 3. Syntax quotation hygiene
// ===========================================================================

#[test]
fn test_quote_syntax_captures_scope() {
    let mut ctx = HygieneExt2Ctx::new();
    let s1 = ctx.enter_scope();
    let q = ctx.quote_syntax("fun x => x");
    assert_eq!(q.scope, s1);
    assert_eq!(q.text, "fun x => x");
    assert!(q.anti_quotes.is_empty());
}

#[test]
fn test_quote_syntax_with_anti_quotes() {
    let mut ctx = HygieneExt2Ctx::new();
    let scope = ctx.enter_scope();
    let aqs = vec![AntiQuote {
        placeholder: "$e".to_owned(),
        origin_scope: scope,
    }];
    let q = ctx.quote_syntax_with_anti_quotes("fun x => $e", aqs);
    assert_eq!(q.anti_quotes.len(), 1);
    assert_eq!(q.anti_quotes[0].placeholder, "$e");
}

// ===========================================================================
// 4. Anti-quotation handling
// ===========================================================================

#[test]
fn test_anti_quote_valid() {
    let mut ctx = HygieneExt2Ctx::new();
    let s = ctx.enter_scope();
    let aq = AntiQuote {
        placeholder: "$e".to_owned(),
        origin_scope: s,
    };
    ctx.process_anti_quote(&aq).expect("should succeed");
    assert_eq!(ctx.stats().anti_quotes_processed, 1);
}

#[test]
fn test_anti_quote_scope_mismatch() {
    let mut ctx = HygieneExt2Ctx::new();
    let s = ctx.enter_scope();
    ctx.leave_scope().unwrap();
    // `s` is no longer on the stack.
    let aq = AntiQuote {
        placeholder: "$e".to_owned(),
        origin_scope: s,
    };
    let err = ctx.process_anti_quote(&aq).unwrap_err();
    assert!(matches!(err, HygieneExt2Error::AntiQuoteMismatch { .. }));
    assert_eq!(ctx.stats().violations_detected, 1);
}

#[test]
fn test_anti_quote_root_always_visible() {
    let mut ctx = HygieneExt2Ctx::new();
    let aq = AntiQuote {
        placeholder: "$root_expr".to_owned(),
        origin_scope: ScopeStamp::root(),
    };
    ctx.process_anti_quote(&aq).expect("root always visible");
}

// ===========================================================================
// 5. Macro-generated binding detection
// ===========================================================================

#[test]
fn test_detect_no_shadow_when_only_user() {
    let mut ctx = HygieneExt2Ctx::new();
    let n = Name::from_string("x");
    ctx.introduce_binding(&n, false);
    ctx.detect_macro_binding_shadow(&n);
    assert!(ctx.violations().is_empty());
}

#[test]
fn test_detect_no_shadow_when_only_macro() {
    let mut ctx = HygieneExt2Ctx::new();
    let n = Name::from_string("x");
    ctx.introduce_binding(&n, true);
    ctx.detect_macro_binding_shadow(&n);
    assert!(ctx.violations().is_empty());
}

#[test]
fn test_detect_shadow_user_and_macro() {
    let mut ctx = HygieneExt2Ctx::new();
    let n = Name::from_string("x");
    ctx.introduce_binding(&n, false);
    ctx.enter_scope();
    ctx.introduce_binding(&n, true);
    ctx.detect_macro_binding_shadow(&n);
    assert_eq!(ctx.violations().len(), 1);
    assert_eq!(
        ctx.violations()[0].kind,
        Ext2ViolationKind::MacroBindingShadow
    );
}

#[test]
fn test_detect_shadow_reports_once() {
    let mut ctx = HygieneExt2Ctx::new();
    let n = Name::from_string("x");
    ctx.introduce_binding(&n, false);
    ctx.enter_scope();
    ctx.introduce_binding(&n, true);
    ctx.detect_macro_binding_shadow(&n);
    ctx.detect_macro_binding_shadow(&n);
    // Each call appends independently (caller controls dedup).
    assert_eq!(ctx.violations().len(), 2);
}

// ===========================================================================
// 6. Scope merging for nested macros
// ===========================================================================

#[test]
fn test_scope_merge_makes_child_visible() {
    let mut ctx = HygieneExt2Ctx::new();
    let n = Name::from_string("helper");
    let s1 = ctx.enter_scope();
    ctx.introduce_binding(&n, true);
    ctx.leave_scope().unwrap();
    // s1 is off-stack; introduce a new scope and merge s1 into it.
    let s2 = ctx.enter_scope();
    ctx.merge_scopes(s1, s2);
    // Now s1 names should be visible via merge.
    let binding = ctx.resolve_name(&n).expect("should resolve via merge");
    assert_eq!(binding.scope, s1);
}

#[test]
fn test_scope_merge_stats() {
    let mut ctx = HygieneExt2Ctx::new();
    let s1 = ScopeStamp::fresh();
    let s2 = ScopeStamp::fresh();
    ctx.merge_scopes(s1, s2);
    assert_eq!(ctx.stats().scope_merges, 1);
}

#[test]
fn test_scope_merge_chain() {
    let mut ctx = HygieneExt2Ctx::new();
    let n = Name::from_string("deep");
    let s1 = ctx.enter_scope();
    ctx.introduce_binding(&n, false);
    ctx.leave_scope().unwrap();
    let s2 = ScopeStamp::fresh();
    let s3 = ctx.enter_scope();
    // Chain: s1 -> s2 -> s3 (s3 is on stack).
    ctx.merge_scopes(s1, s2);
    ctx.merge_scopes(s2, s3);
    let binding = ctx.resolve_name(&n).expect("should resolve via chain");
    assert_eq!(binding.scope, s1);
}

// ===========================================================================
// 7. Unhygienic escape hatch
// ===========================================================================

#[test]
fn test_unhygienic_escape_introduces_in_parent() {
    let mut ctx = HygieneExt2Ctx::new();
    ctx.enter_scope();
    let n = Name::from_string("captured");
    ctx.introduce_unhygienic(&n);
    ctx.leave_scope().unwrap();
    // Binding was injected into root; should be visible after leaving.
    let binding = ctx.resolve_name(&n).expect("should resolve in root");
    assert!(binding.unhygienic);
    assert!(binding.scope.is_root());
}

#[test]
fn test_unhygienic_escape_records_violation() {
    let mut ctx = HygieneExt2Ctx::new();
    ctx.enter_scope();
    let n = Name::from_string("leak");
    ctx.introduce_unhygienic(&n);
    let violations = ctx.violations();
    assert_eq!(violations.len(), 1);
    assert_eq!(violations[0].kind, Ext2ViolationKind::UnhygienicEscape);
}

#[test]
fn test_unhygienic_escape_stats() {
    let mut ctx = HygieneExt2Ctx::new();
    ctx.enter_scope();
    ctx.introduce_unhygienic(&Name::from_string("a"));
    ctx.introduce_unhygienic(&Name::from_string("b"));
    assert_eq!(ctx.stats().unhygienic_escapes, 2);
}

// ===========================================================================
// 8. Hygiene violation detection and reporting
// ===========================================================================

#[test]
fn test_audit_no_violations_on_clean_ctx() {
    let mut ctx = HygieneExt2Ctx::new();
    let n = Name::from_string("safe");
    ctx.introduce_binding(&n, false);
    ctx.audit_all_bindings();
    assert!(ctx.violations().is_empty());
}

#[test]
fn test_audit_detects_leaked_bindings() {
    let mut ctx = HygieneExt2Ctx::new();
    let n = Name::from_string("leaked");
    let s = ctx.enter_scope();
    ctx.introduce_binding(&n, false);
    ctx.leave_scope().unwrap();
    // `n` was introduced in `s`, which is off the stack.
    ctx.audit_all_bindings();
    assert!(!ctx.violations().is_empty());
    assert_eq!(ctx.violations()[0].kind, Ext2ViolationKind::ScopeLeak);
    assert_eq!(ctx.violations()[0].scope, s);
}

#[test]
fn test_check_name_specific_violations() {
    let mut ctx = HygieneExt2Ctx::new();
    let leaked = Name::from_string("leaked");
    let safe = Name::from_string("safe");
    let s = ctx.enter_scope();
    ctx.introduce_binding(&leaked, false);
    ctx.leave_scope().unwrap();
    ctx.introduce_binding(&safe, false);
    let v1 = ctx.check_name(&leaked);
    assert!(!v1.is_empty());
    assert_eq!(v1[0].scope, s);
    let v2 = ctx.check_name(&safe);
    assert!(v2.is_empty());
}

#[test]
fn test_take_violations_clears_list() {
    let mut ctx = HygieneExt2Ctx::new();
    ctx.enter_scope();
    ctx.introduce_unhygienic(&Name::from_string("x"));
    assert!(!ctx.violations().is_empty());
    let taken = ctx.take_violations();
    assert!(!taken.is_empty());
    assert!(ctx.violations().is_empty());
}

// ===========================================================================
// 9. Statistics
// ===========================================================================

#[test]
fn test_stats_initial_zeros() {
    let ctx = HygieneExt2Ctx::new();
    let s = ctx.stats();
    assert_eq!(s.scopes_created, 0);
    assert_eq!(s.resolutions, 0);
    assert_eq!(s.violations_detected, 0);
    assert_eq!(s.anti_quotes_processed, 0);
    assert_eq!(s.unhygienic_escapes, 0);
    assert_eq!(s.scope_merges, 0);
}

#[test]
fn test_stats_scopes_created() {
    let mut ctx = HygieneExt2Ctx::new();
    ctx.enter_scope();
    ctx.enter_scope();
    assert_eq!(ctx.stats().scopes_created, 2);
}

#[test]
fn test_stats_accumulate_across_operations() {
    let mut ctx = HygieneExt2Ctx::new();
    let n = Name::from_string("x");
    ctx.introduce_binding(&n, false);
    ctx.enter_scope();
    ctx.resolve_name(&n).unwrap();
    ctx.introduce_unhygienic(&Name::from_string("y"));
    let s = ctx.stats();
    assert_eq!(s.scopes_created, 1);
    assert_eq!(s.resolutions, 1);
    assert_eq!(s.unhygienic_escapes, 1);
    assert!(s.violations_detected >= 1); // unhygienic escape counts
}

// ===========================================================================
// Edge cases and integration-style tests
// ===========================================================================

#[test]
fn test_names_in_scope_sorted() {
    let mut ctx = HygieneExt2Ctx::new();
    let s = ctx.enter_scope();
    ctx.introduce_binding(&Name::from_string("beta"), false);
    ctx.introduce_binding(&Name::from_string("alpha"), false);
    ctx.introduce_binding(&Name::from_string("gamma"), false);
    let names: Vec<String> = ctx
        .names_in_scope(s)
        .iter()
        .map(|n| n.to_string())
        .collect();
    assert_eq!(names, vec!["alpha", "beta", "gamma"]);
}

#[test]
fn test_scope_stack_accessor() {
    let mut ctx = HygieneExt2Ctx::new();
    let s1 = ctx.enter_scope();
    let s2 = ctx.enter_scope();
    assert_eq!(ctx.scope_stack(), &[ScopeStamp::root(), s1, s2]);
}

#[test]
fn test_deeply_nested_scopes() {
    let mut ctx = HygieneExt2Ctx::new();
    let mut scopes = Vec::new();
    for _ in 0..20 {
        scopes.push(ctx.enter_scope());
    }
    assert_eq!(ctx.scope_depth(), 21);
    for s in scopes.into_iter().rev() {
        let popped = ctx.leave_scope().unwrap();
        assert_eq!(popped, s);
    }
    assert_eq!(ctx.scope_depth(), 1);
}

#[test]
fn test_default_trait() {
    let ctx = HygieneExt2Ctx::default();
    assert_eq!(ctx.scope_depth(), 1);
    assert!(ctx.current_scope().is_root());
}

#[test]
fn test_ext2_violation_kind_display() {
    assert_eq!(format!("{}", Ext2ViolationKind::ScopeLeak), "ScopeLeak");
    assert_eq!(
        format!("{}", Ext2ViolationKind::MacroBindingShadow),
        "MacroBindingShadow"
    );
    assert_eq!(
        format!("{}", Ext2ViolationKind::AntiQuoteScopeMismatch),
        "AntiQuoteScopeMismatch"
    );
    assert_eq!(
        format!("{}", Ext2ViolationKind::UnresolvedInMacro),
        "UnresolvedInMacro"
    );
    assert_eq!(
        format!("{}", Ext2ViolationKind::UnhygienicEscape),
        "UnhygienicEscape"
    );
}

#[test]
fn test_error_display() {
    let err = HygieneExt2Error::ScopeUnderflow;
    assert_eq!(format!("{err}"), "scope stack underflow");
}

#[test]
fn test_introduce_binding_dedup() {
    let mut ctx = HygieneExt2Ctx::new();
    let n = Name::from_string("x");
    ctx.introduce_binding(&n, false);
    ctx.introduce_binding(&n, false);
    let names = ctx.names_in_scope(ScopeStamp::root());
    assert_eq!(names.len(), 1);
}

#[test]
fn test_multi_name_resolution_innermost_wins() {
    let mut ctx = HygieneExt2Ctx::new();
    let n = Name::from_string("x");
    ctx.introduce_binding(&n, false);
    let s1 = ctx.enter_scope();
    ctx.introduce_binding(&n, true);
    let binding = ctx.resolve_name(&n).unwrap();
    assert_eq!(binding.scope, s1);
    assert!(binding.macro_generated);
}

#[test]
fn test_quote_syntax_root_scope() {
    let ctx = HygieneExt2Ctx::new();
    let q = ctx.quote_syntax("Nat.zero");
    assert!(q.scope.is_root());
}

#[test]
fn test_full_workflow_macro_expansion() {
    let mut ctx = HygieneExt2Ctx::new();

    // User introduces a name in root.
    let user_x = Name::from_string("x");
    ctx.introduce_binding(&user_x, false);

    // Macro expands, enters a new scope.
    let macro_scope = ctx.enter_scope();
    let macro_y = Name::from_string("y");
    ctx.introduce_binding(&macro_y, true);

    // Macro quotes syntax referencing user's x.
    let aq = AntiQuote {
        placeholder: "$x".to_owned(),
        origin_scope: ScopeStamp::root(),
    };
    ctx.process_anti_quote(&aq).expect("root origin visible");

    // Macro resolves its own y.
    let binding_y = ctx.resolve_name(&macro_y).unwrap();
    assert_eq!(binding_y.scope, macro_scope);

    // User's x is still visible inside macro.
    let binding_x = ctx.resolve_name(&user_x).unwrap();
    assert!(!binding_x.macro_generated);

    // Leave macro scope.
    ctx.leave_scope().unwrap();

    // y is no longer visible.
    assert!(ctx.resolve_name(&macro_y).is_err());

    // Stats reflect the session.
    assert_eq!(ctx.stats().scopes_created, 1);
    assert_eq!(ctx.stats().resolutions, 3);
    assert_eq!(ctx.stats().anti_quotes_processed, 1);
}
