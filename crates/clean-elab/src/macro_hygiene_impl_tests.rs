// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the `macro_hygiene` module.
//!
//! Covers: scope uniqueness, stack push/pop, name introduction and resolution,
//! visibility, gensym uniqueness, ambiguous resolution, renaming, nesting,
//! depth tracking, empty context, and multiple names in one scope.

use crate::macro_hygiene::{HygieneCtx, HygieneResolution, MacroScope};
use std::collections::HashSet;

// ---------------------------------------------------------------------------
// MacroScope basics
// ---------------------------------------------------------------------------

#[test]
fn test_macro_scope_root_is_zero() {
    let root = MacroScope::root();
    assert_eq!(root.id(), 0);
    assert!(root.is_root());
}

#[test]
fn test_macro_scope_non_root() {
    let mut ctx = HygieneCtx::new();
    let s = ctx.fresh_scope();
    assert!(!s.is_root());
    assert_ne!(s, MacroScope::root());
}

#[test]
fn test_fresh_scope_ids_are_unique() {
    let mut ctx = HygieneCtx::new();
    let mut seen = HashSet::new();
    for _ in 0..100 {
        let s = ctx.fresh_scope();
        assert!(seen.insert(s.id()), "scope IDs must be unique");
    }
    assert_eq!(seen.len(), 100);
}

#[test]
fn test_fresh_scope_ids_are_monotonically_increasing() {
    let mut ctx = HygieneCtx::new();
    let s1 = ctx.fresh_scope();
    let s2 = ctx.fresh_scope();
    let s3 = ctx.fresh_scope();
    assert!(s1.id() < s2.id());
    assert!(s2.id() < s3.id());
}

// ---------------------------------------------------------------------------
// Push / pop scope stack
// ---------------------------------------------------------------------------

#[test]
fn test_push_pop_scope_stack() {
    let mut ctx = HygieneCtx::new();
    assert_eq!(ctx.scope_depth(), 1); // root

    let s1 = ctx.fresh_scope();
    ctx.push_scope(s1);
    assert_eq!(ctx.scope_depth(), 2);
    assert_eq!(ctx.current_scope(), s1);

    let popped = ctx.pop_scope();
    assert_eq!(popped, Some(s1));
    assert_eq!(ctx.scope_depth(), 1);
    assert_eq!(ctx.current_scope(), MacroScope::root());
}

#[test]
fn test_pop_scope_refuses_to_pop_root() {
    let mut ctx = HygieneCtx::new();
    assert_eq!(ctx.scope_depth(), 1);
    let result = ctx.pop_scope();
    assert_eq!(result, None, "must not pop the root scope");
    assert_eq!(ctx.scope_depth(), 1);
}

#[test]
fn test_nested_push_pop() {
    let mut ctx = HygieneCtx::new();
    let s1 = ctx.fresh_scope();
    let s2 = ctx.fresh_scope();
    let s3 = ctx.fresh_scope();

    ctx.push_scope(s1);
    ctx.push_scope(s2);
    ctx.push_scope(s3);
    assert_eq!(ctx.scope_depth(), 4); // root + 3

    assert_eq!(ctx.pop_scope(), Some(s3));
    assert_eq!(ctx.pop_scope(), Some(s2));
    assert_eq!(ctx.pop_scope(), Some(s1));
    assert_eq!(ctx.pop_scope(), None); // root protected
}

// ---------------------------------------------------------------------------
// Introduce and resolve name
// ---------------------------------------------------------------------------

#[test]
fn test_introduce_and_resolve_name() {
    let mut ctx = HygieneCtx::new();
    let s = ctx.fresh_scope();
    ctx.push_scope(s);
    ctx.introduce_name("x", s);

    match ctx.resolve_name("x") {
        HygieneResolution::Resolved(hyg) => {
            assert_eq!(hyg.raw_name, "x");
            assert_eq!(hyg.scope, s);
            assert!(!hyg.is_gensym);
        }
        other => panic!("expected Resolved, got {other:?}"),
    }
}

#[test]
fn test_resolve_name_not_found() {
    let ctx = HygieneCtx::new();
    assert!(matches!(
        ctx.resolve_name("nonexistent"),
        HygieneResolution::Unresolved
    ));
}

#[test]
fn test_name_visible_only_in_its_scope() {
    let mut ctx = HygieneCtx::new();
    let s1 = ctx.fresh_scope();

    // Introduce x in s1 but don't push s1
    ctx.introduce_name("x", s1);

    // s1 is not on the stack, so x should be unresolved
    assert!(matches!(
        ctx.resolve_name("x"),
        HygieneResolution::Unresolved
    ));

    // Now push s1 and resolve again
    ctx.push_scope(s1);
    assert!(matches!(
        ctx.resolve_name("x"),
        HygieneResolution::Resolved(_)
    ));
}

#[test]
fn test_name_becomes_invisible_after_pop() {
    let mut ctx = HygieneCtx::new();
    let s = ctx.fresh_scope();
    ctx.push_scope(s);
    ctx.introduce_name("y", s);

    assert!(matches!(
        ctx.resolve_name("y"),
        HygieneResolution::Resolved(_)
    ));

    ctx.pop_scope();

    assert!(matches!(
        ctx.resolve_name("y"),
        HygieneResolution::Unresolved
    ));
}

// ---------------------------------------------------------------------------
// Gensym
// ---------------------------------------------------------------------------

#[test]
fn test_gensym_produces_unique_names() {
    let mut ctx = HygieneCtx::new();
    let mut seen = HashSet::new();
    for _ in 0..50 {
        let hyg = ctx.gensym("_v");
        assert!(hyg.is_gensym);
        assert!(hyg.raw_name.starts_with("_v_hygiene_"));
        assert!(seen.insert(hyg.raw_name.clone()), "gensym must be unique");
    }
    assert_eq!(seen.len(), 50);
}

#[test]
fn test_gensym_is_introduced_in_current_scope() {
    let mut ctx = HygieneCtx::new();
    let s = ctx.fresh_scope();
    ctx.push_scope(s);

    let hyg = ctx.gensym("tmp");
    assert_eq!(hyg.scope, s);

    // The generated name should be resolvable
    match ctx.resolve_name(&hyg.raw_name) {
        HygieneResolution::Resolved(resolved) => {
            assert_eq!(resolved.raw_name, hyg.raw_name);
            assert_eq!(resolved.scope, s);
        }
        other => panic!("expected Resolved for gensym, got {other:?}"),
    }
}

#[test]
fn test_gensym_uses_prefix() {
    let mut ctx = HygieneCtx::new();
    let h1 = ctx.gensym("alpha");
    let h2 = ctx.gensym("beta");
    assert!(h1.raw_name.starts_with("alpha_hygiene_"));
    assert!(h2.raw_name.starts_with("beta_hygiene_"));
}

// ---------------------------------------------------------------------------
// Ambiguous resolution
// ---------------------------------------------------------------------------

#[test]
fn test_ambiguous_resolution_same_name_multiple_scopes() {
    let mut ctx = HygieneCtx::new();
    let s1 = ctx.fresh_scope();
    let s2 = ctx.fresh_scope();

    ctx.introduce_name("z", s1);
    ctx.introduce_name("z", s2);

    ctx.push_scope(s1);
    ctx.push_scope(s2);

    match ctx.resolve_name("z") {
        HygieneResolution::Ambiguous(names) => {
            assert_eq!(names.len(), 2);
            let scope_ids: HashSet<u64> = names.iter().map(|n| n.scope.id()).collect();
            assert!(scope_ids.contains(&s1.id()));
            assert!(scope_ids.contains(&s2.id()));
        }
        other => panic!("expected Ambiguous, got {other:?}"),
    }
}

#[test]
fn test_single_visible_scope_not_ambiguous() {
    let mut ctx = HygieneCtx::new();
    let s1 = ctx.fresh_scope();
    let s2 = ctx.fresh_scope();

    ctx.introduce_name("w", s1);
    ctx.introduce_name("w", s2);

    // Only push s1 -- s2 not on stack
    ctx.push_scope(s1);

    match ctx.resolve_name("w") {
        HygieneResolution::Resolved(hyg) => {
            assert_eq!(hyg.scope, s1);
        }
        other => panic!("expected Resolved, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// is_visible
// ---------------------------------------------------------------------------

#[test]
fn test_is_visible_true_for_introduced_scope() {
    let mut ctx = HygieneCtx::new();
    let s = ctx.fresh_scope();
    ctx.introduce_name("a", s);
    assert!(ctx.is_visible("a", s));
}

#[test]
fn test_is_visible_false_for_wrong_scope() {
    let mut ctx = HygieneCtx::new();
    let s1 = ctx.fresh_scope();
    let s2 = ctx.fresh_scope();
    ctx.introduce_name("a", s1);
    assert!(!ctx.is_visible("a", s2));
}

#[test]
fn test_is_visible_false_for_unknown_name() {
    let ctx = HygieneCtx::new();
    assert!(!ctx.is_visible("unknown", MacroScope::root()));
}

// ---------------------------------------------------------------------------
// rename_for_hygiene
// ---------------------------------------------------------------------------

#[test]
fn test_rename_for_hygiene_appends_scope_id() {
    let mut ctx = HygieneCtx::new();
    let s = ctx.fresh_scope();
    ctx.push_scope(s);
    ctx.introduce_name("var", s);

    let renamed = ctx.rename_for_hygiene("var");
    assert_eq!(renamed, format!("var_{}", s.id()));
}

#[test]
fn test_rename_for_hygiene_unknown_name_unchanged() {
    let ctx = HygieneCtx::new();
    let renamed = ctx.rename_for_hygiene("untouched");
    assert_eq!(renamed, "untouched");
}

#[test]
fn test_rename_for_hygiene_no_visible_scope_unchanged() {
    let mut ctx = HygieneCtx::new();
    let s = ctx.fresh_scope();
    // Introduce but don't push
    ctx.introduce_name("q", s);
    let renamed = ctx.rename_for_hygiene("q");
    assert_eq!(renamed, "q");
}

// ---------------------------------------------------------------------------
// Nested scopes
// ---------------------------------------------------------------------------

#[test]
fn test_nested_scopes_innermost_wins_rename() {
    let mut ctx = HygieneCtx::new();
    let s1 = ctx.fresh_scope();
    let s2 = ctx.fresh_scope();

    ctx.push_scope(s1);
    ctx.introduce_name("n", s1);
    ctx.push_scope(s2);
    ctx.introduce_name("n", s2);

    // With both visible, rename should use the last visible = s2
    let renamed = ctx.rename_for_hygiene("n");
    assert_eq!(renamed, format!("n_{}", s2.id()));
}

// ---------------------------------------------------------------------------
// Scope depth tracking
// ---------------------------------------------------------------------------

#[test]
fn test_scope_depth_tracking() {
    let mut ctx = HygieneCtx::new();
    assert_eq!(ctx.scope_depth(), 1); // root

    let s1 = ctx.fresh_scope();
    ctx.push_scope(s1);
    assert_eq!(ctx.scope_depth(), 2);

    let s2 = ctx.fresh_scope();
    ctx.push_scope(s2);
    assert_eq!(ctx.scope_depth(), 3);

    ctx.pop_scope();
    assert_eq!(ctx.scope_depth(), 2);

    ctx.pop_scope();
    assert_eq!(ctx.scope_depth(), 1);
}

// ---------------------------------------------------------------------------
// Empty context
// ---------------------------------------------------------------------------

#[test]
fn test_empty_context_defaults() {
    let ctx = HygieneCtx::new();
    assert_eq!(ctx.scope_depth(), 1);
    assert_eq!(ctx.current_scope(), MacroScope::root());
    assert!(ctx.all_scopes().len() == 1);
    assert_eq!(ctx.all_scopes()[0], MacroScope::root());
    assert!(matches!(
        ctx.resolve_name("anything"),
        HygieneResolution::Unresolved
    ));
}

#[test]
fn test_default_trait_matches_new() {
    let ctx1 = HygieneCtx::new();
    let ctx2 = HygieneCtx::default();
    assert_eq!(ctx1.scope_depth(), ctx2.scope_depth());
    assert_eq!(ctx1.current_scope(), ctx2.current_scope());
}

// ---------------------------------------------------------------------------
// Multiple names same scope
// ---------------------------------------------------------------------------

#[test]
fn test_multiple_names_same_scope() {
    let mut ctx = HygieneCtx::new();
    let s = ctx.fresh_scope();
    ctx.push_scope(s);

    ctx.introduce_name("a", s);
    ctx.introduce_name("b", s);
    ctx.introduce_name("c", s);

    let names = ctx.names_in_scope(s);
    assert_eq!(names, vec!["a", "b", "c"]);

    for name in &["a", "b", "c"] {
        assert!(matches!(
            ctx.resolve_name(name),
            HygieneResolution::Resolved(_)
        ));
    }
}

#[test]
fn test_names_in_scope_empty_for_fresh() {
    let mut ctx = HygieneCtx::new();
    let s = ctx.fresh_scope();
    assert!(ctx.names_in_scope(s).is_empty());
}

// ---------------------------------------------------------------------------
// Duplicate introduce is idempotent
// ---------------------------------------------------------------------------

#[test]
fn test_introduce_name_idempotent() {
    let mut ctx = HygieneCtx::new();
    let s = ctx.fresh_scope();
    ctx.push_scope(s);

    ctx.introduce_name("x", s);
    ctx.introduce_name("x", s);
    ctx.introduce_name("x", s);

    // Should resolve once, not be ambiguous
    assert!(matches!(
        ctx.resolve_name("x"),
        HygieneResolution::Resolved(_)
    ));

    assert_eq!(ctx.names_in_scope(s), vec!["x"]);
}

// ---------------------------------------------------------------------------
// Display impls
// ---------------------------------------------------------------------------

#[test]
fn test_display_macro_scope() {
    let s = MacroScope::root();
    assert_eq!(format!("{s}"), "MacroScope(0)");
}

#[test]
fn test_display_hygienic_name() {
    use crate::macro_hygiene::HygienicName;

    let name = HygienicName {
        raw_name: "x".to_owned(),
        scope: MacroScope::root(),
        is_gensym: false,
    };
    assert_eq!(format!("{name}"), "x [MacroScope(0)]");

    let gensym = HygienicName {
        raw_name: "tmp".to_owned(),
        scope: MacroScope::root(),
        is_gensym: true,
    };
    assert_eq!(format!("{gensym}"), "tmp [MacroScope(0); gensym]");
}

#[test]
fn test_display_hygiene_resolution() {
    let ctx = HygieneCtx::new();
    let unresolved = ctx.resolve_name("missing");
    assert_eq!(format!("{unresolved}"), "Unresolved");
}

// ---------------------------------------------------------------------------
// all_scopes returns correct state
// ---------------------------------------------------------------------------

#[test]
fn test_all_scopes_reflects_stack() {
    let mut ctx = HygieneCtx::new();
    let s1 = ctx.fresh_scope();
    let s2 = ctx.fresh_scope();

    ctx.push_scope(s1);
    ctx.push_scope(s2);

    let scopes = ctx.all_scopes();
    assert_eq!(scopes.len(), 3);
    assert_eq!(scopes[0], MacroScope::root());
    assert_eq!(scopes[1], s1);
    assert_eq!(scopes[2], s2);
}
