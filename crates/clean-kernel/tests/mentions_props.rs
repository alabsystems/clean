// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Phase 1d: Proptest equivalents of Kani timeout harness for mentions_name (#982).
//!
//! Migrated from designs/2026-03-04-982-proptest-alternative.md
//!
//! Kani harness verify_mentions_name_detects_const times out because the
//! MentionsNameVisitor recurses through expressions containing Arc<Level>
//! and Arc<Name>, causing CBMC SAT explosion. These proptests exercise the
//! real production mentions_name with varying expression shapes.

use clean_kernel::expr::Expr;
use clean_kernel::inductive::mentions_name;
use clean_kernel::name::Name;
use clean_kernel::BinderInfo;
use proptest::prelude::*;

/// Strategy for generating target names with varying structure.
fn name_strategy() -> impl Strategy<Value = Name> {
    prop::collection::vec("[a-z]{1,4}", 1..6).prop_map(|segs| {
        segs.iter()
            .fold(Name::anon(), |parent, seg| parent.str(seg))
    })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    // ================================================================
    // Direct Const detection (Kani equivalent: verify_mentions_name_detects_const)
    // ================================================================

    /// mentions_name detects direct Const occurrence.
    #[test]
    fn prop_mentions_name_detects_const(name in name_strategy()) {
        let c = Expr::const_(name.clone(), vec![]);
        prop_assert!(mentions_name(&c, &name),
            "mentions_name should detect direct Const: {:?}", name);
    }

    // ================================================================
    // Nested detection: Const inside App, Pi, Lam, Let
    // ================================================================

    /// mentions_name detects Const in App argument.
    #[test]
    fn prop_mentions_name_in_app_arg(name in name_strategy()) {
        let c = Expr::const_(name.clone(), vec![]);
        let app = Expr::app(Expr::type_(), c);
        prop_assert!(mentions_name(&app, &name),
            "mentions_name should detect Const in App arg: {:?}", name);
    }

    /// mentions_name detects Const in App function position.
    #[test]
    fn prop_mentions_name_in_app_fn(name in name_strategy()) {
        let c = Expr::const_(name.clone(), vec![]);
        let app = Expr::app(c, Expr::prop());
        prop_assert!(mentions_name(&app, &name),
            "mentions_name should detect Const in App fn: {:?}", name);
    }

    /// mentions_name detects Const in Pi domain.
    #[test]
    fn prop_mentions_name_in_pi_domain(name in name_strategy()) {
        let c = Expr::const_(name.clone(), vec![]);
        let pi = Expr::pi(BinderInfo::Default, c, Expr::prop());
        prop_assert!(mentions_name(&pi, &name),
            "mentions_name should detect Const in Pi domain: {:?}", name);
    }

    /// mentions_name detects Const in Pi codomain.
    #[test]
    fn prop_mentions_name_in_pi_codomain(name in name_strategy()) {
        let c = Expr::const_(name.clone(), vec![]);
        let pi = Expr::pi(BinderInfo::Default, Expr::type_(), c);
        prop_assert!(mentions_name(&pi, &name),
            "mentions_name should detect Const in Pi codomain: {:?}", name);
    }

    /// mentions_name detects Const in deeply nested Pi.
    #[test]
    fn prop_mentions_name_in_deep_pi(name in name_strategy()) {
        let c = Expr::const_(name.clone(), vec![]);
        let deep = Expr::pi(BinderInfo::Default, Expr::type_(),
            Expr::pi(BinderInfo::Default, Expr::prop(),
                Expr::pi(BinderInfo::Default, c, Expr::type_())));
        prop_assert!(mentions_name(&deep, &name),
            "mentions_name should detect in nested Pi: {:?}", name);
    }

    /// mentions_name detects Const inside lambda body.
    #[test]
    fn prop_mentions_name_in_lam_body(name in name_strategy()) {
        let c = Expr::const_(name.clone(), vec![]);
        let lam = Expr::lam(BinderInfo::Default, Expr::type_(), c);
        prop_assert!(mentions_name(&lam, &name),
            "mentions_name should detect Const in lambda body: {:?}", name);
    }

    /// mentions_name detects Const inside let value.
    #[test]
    fn prop_mentions_name_in_let_val(name in name_strategy()) {
        let c = Expr::const_(name.clone(), vec![]);
        let let_e = Expr::let_named(Name::anon(), Expr::type_(), c, Expr::bvar(0), false);
        prop_assert!(mentions_name(&let_e, &name),
            "mentions_name should detect Const in let value: {:?}", name);
    }

    // ================================================================
    // Negative: absent name returns false
    // ================================================================

    /// mentions_name returns false when name is not present.
    #[test]
    fn prop_mentions_name_absent(
        target in name_strategy(),
        other in name_strategy()
    ) {
        prop_assume!(target != other);
        let c = Expr::const_(other.clone(), vec![]);
        prop_assert!(!mentions_name(&c, &target),
            "mentions_name should not detect absent name: target={:?}, other={:?}", target, other);
    }

    /// mentions_name on expression without any Const nodes.
    #[test]
    fn prop_mentions_name_no_const(name in name_strategy()) {
        let e = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::prop());
        prop_assert!(!mentions_name(&e, &name),
            "mentions_name should return false for expr with no Const");
    }
}
