// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Phase 1d: Proptest equivalents of Kani timeout harnesses for LocalContext (#982).
//!
//! Migrated from designs/2026-03-04-982-proptest-alternative.md
//!
//! Kani harnesses verify_local_context_push_pop and verify_local_context_lookup
//! timeout because LocalContext stores expressions containing Arc<Level> and
//! Arc<Name>, causing CBMC SAT explosion on the recursive types. These proptests
//! exercise real production LocalContext operations with varying expressions.

use clean_kernel::{BinderInfo, Expr, Level, LocalContext, Name};
use proptest::prelude::*;

/// Strategy for generating names of varying depth.
fn name_strategy() -> impl Strategy<Value = Name> {
    prop::collection::vec("[a-z]{1,4}", 1..4).prop_map(|segs| {
        segs.iter()
            .fold(Name::anon(), |parent, seg| parent.str(seg))
    })
}

/// Strategy for generating type expressions.
fn type_strategy() -> impl Strategy<Value = Expr> {
    prop_oneof![
        Just(Expr::prop()),
        Just(Expr::type_()),
        Just(Expr::sort(Level::succ(Level::succ(Level::zero())))),
        Just(Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop())),
        Just(Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_())),
    ]
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    // ================================================================
    // Push/pop roundtrip (Kani equivalent: verify_local_context_push_pop)
    //
    // Push a declaration, verify it's findable, pop it, verify it's gone.
    // ================================================================

    #[test]
    fn prop_local_context_push_pop_roundtrip(
        name in name_strategy(),
        ty in type_strategy()
    ) {
        let mut ctx = LocalContext::new();
        prop_assert!(ctx.is_empty());

        let id = ctx.push(name.clone(), ty.clone(), BinderInfo::Default);

        // Should find it
        let decl = ctx.get(id);
        prop_assert!(decl.is_some(), "Should find pushed decl");
        let decl = decl.unwrap();
        prop_assert_eq!(&decl.name, &name);
        prop_assert_eq!(ctx.len(), 1);

        // Pop it
        let popped = ctx.pop();
        prop_assert!(popped.is_some(), "pop on non-empty context should succeed");
        let popped = popped.unwrap();
        prop_assert_eq!(popped.id, id);
        prop_assert_eq!(&popped.name, &name);

        // Should not find it anymore
        prop_assert!(ctx.get(id).is_none(), "Should not find popped decl");
        prop_assert!(ctx.is_empty());
    }

    // ================================================================
    // Lookup multiple entries (Kani equivalent: verify_local_context_lookup)
    //
    // Push several entries, verify all are findable by ID, verify ordering.
    // ================================================================

    #[test]
    fn prop_local_context_lookup_multiple(
        count in 1usize..10
    ) {
        let mut ctx = LocalContext::new();
        let mut ids = Vec::new();
        let mut names = Vec::new();

        for i in 0..count {
            let name = Name::from_string(&format!("x{}", i));
            let id = ctx.push(name.clone(), Expr::prop(), BinderInfo::Default);
            ids.push(id);
            names.push(name);
        }

        prop_assert_eq!(ctx.len(), count);

        // All should be findable
        for (i, id) in ids.iter().enumerate() {
            let decl = ctx.get(*id);
            prop_assert!(decl.is_some(), "Should find decl at index {}", i);
            prop_assert_eq!(&decl.unwrap().name, &names[i]);
        }
    }

    // ================================================================
    // Push with varying types, verify type is stored correctly
    // ================================================================

    #[test]
    fn prop_local_context_type_preserved(
        name in name_strategy(),
        ty in type_strategy()
    ) {
        let mut ctx = LocalContext::new();
        let id = ctx.push(name.clone(), ty.clone(), BinderInfo::Default);

        let decl = ctx.get(id).unwrap();
        prop_assert_eq!(&decl.type_, &ty,
            "Stored type should match pushed type");
        prop_assert_eq!(decl.bi, BinderInfo::Default.into());
    }

    // ================================================================
    // Push multiple, pop all in reverse order (LIFO)
    // ================================================================

    #[test]
    fn prop_local_context_lifo_order(count in 1usize..10) {
        let mut ctx = LocalContext::new();
        let mut ids = Vec::new();

        for i in 0..count {
            let name = Name::from_string(&format!("v{}", i));
            let id = ctx.push(name, Expr::prop(), BinderInfo::Default);
            ids.push(id);
        }

        prop_assert_eq!(ctx.len(), count);

        // Pop in reverse order (LIFO)
        for i in (0..count).rev() {
            let popped = ctx.pop();
            prop_assert!(popped.is_some(), "Pop at index {} should succeed", i);
            prop_assert_eq!(popped.unwrap().id, ids[i]);
        }

        prop_assert!(ctx.is_empty());
        prop_assert!(ctx.pop().is_none(), "Pop on empty should return None");
    }

    // ================================================================
    // Let binding roundtrip
    // ================================================================

    #[test]
    fn prop_local_context_let_roundtrip(
        name in name_strategy(),
        ty in type_strategy(),
        val in type_strategy()
    ) {
        let mut ctx = LocalContext::new();
        let id = ctx.push_let(name.clone(), ty.clone(), val.clone());

        let decl = ctx.get(id);
        prop_assert!(decl.is_some(), "should find let binding by id");
        let decl = decl.unwrap();
        prop_assert_eq!(&decl.name, &name);
        prop_assert_eq!(&decl.type_, &ty);
        prop_assert!(decl.value.is_some(), "Let binding should have value");
        prop_assert_eq!(decl.value.as_ref().unwrap(), &val,
            "Let binding value should match pushed value");

        let popped = ctx.pop().unwrap();
        prop_assert_eq!(popped.id, id);
        prop_assert!(popped.value.is_some(), "popped let binding should have value");
        prop_assert_eq!(popped.value.as_ref().unwrap(), &val,
            "Popped let binding value should match pushed value");
    }

    // ================================================================
    // Mixed push and push_let
    // ================================================================

    #[test]
    fn prop_local_context_mixed_decls(count in 1usize..6) {
        let mut ctx = LocalContext::new();
        let mut ids = Vec::new();
        let mut is_let = Vec::new();

        for i in 0..count {
            let name = Name::from_string(&format!("m{}", i));
            if i % 2 == 0 {
                let id = ctx.push(name, Expr::type_(), BinderInfo::Default);
                ids.push(id);
                is_let.push(false);
            } else {
                let id = ctx.push_let(name, Expr::type_(), Expr::prop());
                ids.push(id);
                is_let.push(true);
            }
        }

        prop_assert_eq!(ctx.len(), count);

        // Verify each entry
        for (i, id) in ids.iter().enumerate() {
            let decl = ctx.get(*id).unwrap();
            if is_let[i] {
                prop_assert!(decl.value.is_some(), "Let at {} should have value", i);
            } else {
                prop_assert!(decl.value.is_none(), "Non-let at {} should not have value", i);
            }
        }
    }

    // ================================================================
    // Iterator matches stored entries
    // ================================================================

    #[test]
    fn prop_local_context_iter(count in 0usize..8) {
        let mut ctx = LocalContext::new();
        let mut names = Vec::new();

        for i in 0..count {
            let name = Name::from_string(&format!("it{}", i));
            ctx.push(name.clone(), Expr::prop(), BinderInfo::Default);
            names.push(name);
        }

        let iter_names: Vec<_> = ctx.iter().map(|d| d.name.clone()).collect();
        prop_assert_eq!(iter_names.len(), count);
        for (i, name) in iter_names.iter().enumerate() {
            prop_assert_eq!(name, &names[i]);
        }
    }
}
