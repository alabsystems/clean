// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lift_bvar() {
        // BVar(0) lifted by 1 at depth 0 should become BVar(1)
        let e = Expr::from_kind(ExprKind::BVar(0));
        assert_eq!(e.lift(1), Expr::from_kind(ExprKind::BVar(1)));

        // BVar(0) inside a lambda should NOT be lifted (it's bound)
        // We test lift_at directly for this
        let e = Expr::from_kind(ExprKind::BVar(0));
        assert_eq!(e.lift_at(1, 1), Expr::from_kind(ExprKind::BVar(0))); // BVar(0) < start=1, no change
        assert_eq!(e.lift_at(0, 1), Expr::from_kind(ExprKind::BVar(1))); // BVar(0) >= start=0, lifted

        let e = Expr::from_kind(ExprKind::BVar(2));
        assert_eq!(e.lift_at(1, 3), Expr::from_kind(ExprKind::BVar(5))); // BVar(2) >= start=1, lifted by 3
    }

    #[test]
    fn test_instantiate() {
        // (λ x. x) instantiated with y should give y
        let body = Expr::from_kind(ExprKind::BVar(0));
        let val = Expr::fvar(FVarId(42));
        let result = body.instantiate(&val);
        assert_eq!(result, Expr::fvar(FVarId(42)));

        // (λ x. λ y. x) - inner body should have BVar(1) for x
        // instantiate outer: BVar(1) -> should become BVar(0) after shift
        let inner_body = Expr::from_kind(ExprKind::BVar(1)); // refers to outer x
        let val = Expr::fvar(FVarId(99));
        let result = inner_body.instantiate(&val);
        // BVar(1) at depth 0: 1 > 0, so becomes BVar(0) (shifted down)
        assert_eq!(result, Expr::from_kind(ExprKind::BVar(0)));
    }

    #[test]
    fn test_abstract_fvar() {
        let fvar = Expr::fvar(FVarId(42));
        let result = fvar.abstract_fvar(FVarId(42));
        assert_eq!(result, Expr::from_kind(ExprKind::BVar(0)));

        // Different fvar should not be abstracted
        let result = fvar.abstract_fvar(FVarId(99));
        assert_eq!(result, Expr::fvar(FVarId(42)));
    }

    #[test]
    fn test_has_loose_bvars() {
        assert!(Expr::from_kind(ExprKind::BVar(0)).has_loose_bvars());
        assert!(Expr::from_kind(ExprKind::BVar(ExprMeta::MAX_BVAR_RANGE - 1)).has_loose_bvars());
        assert!(!Expr::fvar(FVarId(0)).has_loose_bvars());
        assert!(!Expr::prop().has_loose_bvars());

        // Lambda binds the BVar(0), so no loose bvars
        let lam = Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(0)),
        );
        assert!(!lam.has_loose_bvars());

        // BVar(1) inside lambda is loose (refers outside)
        let lam = Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(1)),
        );
        assert!(lam.has_loose_bvars());
    }

    #[test]
    fn test_has_loose_bvar_range_unbounded_shift() {
        let lam = Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(0)),
        );
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            lam.has_loose_bvar_in_range(u32::MAX, u32::MAX)
        }));
        let has_bvar = result.expect("range shift at u32::MAX should not panic");
        assert!(!has_bvar, "range [MAX, MAX) should be empty after shift");
    }

    #[test]
    fn test_zfc_has_loose_bvar_range_unbounded_shift() {
        let pred = Expr::from_kind(ExprKind::BVar(0));
        let set_expr = ZFCSetExpr::Separation {
            set: Arc::new(Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty))),
            pred: Arc::new(pred),
        };
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            set_expr.has_loose_bvar_in_range(u32::MAX, u32::MAX)
        }));
        assert!(
            result.is_ok(),
            "ZFC range shift at u32::MAX should not panic"
        );
        assert!(
            !result.unwrap(),
            "range [MAX, MAX) should be empty after shift"
        );
    }

    // =========================================================================
    // Mutation Testing Kill Tests
    // =========================================================================

    #[test]
    fn test_is_sort_predicates() {
        // Kill mutants: is_sort can return true always
        assert!(Expr::prop().is_sort());
        assert!(Expr::type_().is_sort());
        assert!(!Expr::from_kind(ExprKind::BVar(0)).is_sort());
        assert!(!Expr::fvar(FVarId(0)).is_sort());
        assert!(!Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(0))
        )
        .is_sort());
        assert!(!Expr::nat_lit(42).is_sort());
    }

    #[test]
    fn test_is_prop_predicate() {
        // Kill mutant: is_prop can return true always
        assert!(Expr::prop().is_prop());
        assert!(!Expr::type_().is_prop());
        assert!(
            !Expr::from_kind(ExprKind::Sort(Level::succ(Level::succ(Level::zero())))).is_prop()
        );
        assert!(!Expr::from_kind(ExprKind::BVar(0)).is_prop());
    }

    #[test]
    fn test_instantiate_at_boundary_conditions() {
        // Kill mutants: instantiate_at > vs >= comparison

        // BVar(0) at depth 0 should be replaced
        let body = Expr::from_kind(ExprKind::BVar(0));
        let val = Expr::prop();
        assert_eq!(body.instantiate(&val), Expr::prop());

        // BVar(1) at depth 0 should be decremented to BVar(0)
        let body = Expr::from_kind(ExprKind::BVar(1));
        assert_eq!(body.instantiate(&val), Expr::from_kind(ExprKind::BVar(0)));

        // BVar(2) at depth 0 should become BVar(1)
        let body = Expr::from_kind(ExprKind::BVar(2));
        assert_eq!(body.instantiate(&val), Expr::from_kind(ExprKind::BVar(1)));

        // Inside a binder, BVar(0) refers to the binder, not substituted
        // λ (x : Prop). x -> x is BVar(0) at depth 1, so no substitution
        let inner = Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(0)),
        );
        // Instantiating the outer level shouldn't change inner BVar(0)
        let result = inner.instantiate(&val);
        assert_eq!(
            result,
            Expr::lam(
                BinderInfo::Default,
                Expr::prop(),
                Expr::from_kind(ExprKind::BVar(0))
            )
        );
    }

    #[test]
    fn test_instantiate_arithmetic() {
        // Kill mutant: instantiate_at + with * in body.instantiate_at(val, depth + 1)
        // This tests that depth is incremented correctly under binders

        // Simple case: λ x. BVar(1) -- BVar(1) refers to the substitution target
        // When instantiated at depth 0, the body is processed at depth 1
        // BVar(1) at depth 1: 1 == 1, so gets replaced with val.lift(1)
        let lam = Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(1)),
        );
        let val = Expr::type_();
        let result = lam.instantiate(&val);

        // Body should have BVar(1) replaced with Type.lift(1) = Type
        // (Type has no loose bvars so lifting doesn't change it)
        match &result.kind {
            ExprKind::Lam(_, _, body) => {
                assert_eq!(body.as_ref(), &Expr::type_());
            }
            _ => panic!("Expected lambda"),
        }

        // More complex: test that BVar references above the binder are decremented
        // λ x. BVar(2) -- BVar(2) is above the substitution depth
        // At depth 1: BVar(2) > 1, so becomes BVar(1)
        let lam = Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(2)),
        );
        let result = lam.instantiate(&val);
        match &result.kind {
            ExprKind::Lam(_, _, body) => {
                assert_eq!(body.as_ref(), &Expr::from_kind(ExprKind::BVar(1)));
            }
            _ => panic!("Expected lambda"),
        }
    }

    #[test]
    fn test_lift_at_arithmetic() {
        // Kill mutants: lift_at + with * or -

        // BVar(2) at start=1 lifted by 3 should be BVar(5), not BVar(6) or BVar(-1)
        let e = Expr::from_kind(ExprKind::BVar(2));
        assert_eq!(e.lift_at(1, 3), Expr::from_kind(ExprKind::BVar(5))); // 2 >= 1, so 2+3=5

        // BVar(0) at start=1 should NOT be lifted
        let e = Expr::from_kind(ExprKind::BVar(0));
        assert_eq!(e.lift_at(1, 3), Expr::from_kind(ExprKind::BVar(0))); // 0 < 1, no change

        // Test inside nested binders - start should increment
        // λ x. λ y. BVar(0)  -- BVar(0) refers to y, shouldn't be lifted
        let inner = Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(0)),
        );
        let outer = Expr::lam(BinderInfo::Default, Expr::prop(), inner);
        let result = outer.lift(1);

        // Inner BVar(0) is under 2 binders, so start becomes 0+1+1=2
        // BVar(0) < 2, no change
        match &result.kind {
            ExprKind::Lam(_, _, body) => match &body.as_ref().kind {
                ExprKind::Lam(_, _, inner_body) => {
                    assert_eq!(inner_body.as_ref(), &Expr::from_kind(ExprKind::BVar(0)));
                }
                _ => panic!("Expected nested lambda"),
            },
            _ => panic!("Expected lambda"),
        }

        // λ x. BVar(1) -- BVar(1) refers outside lambda, should be lifted
        let lam = Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(1)),
        );
        let result = lam.lift(1);
        match &result.kind {
            ExprKind::Lam(_, _, body) => {
                // Under one binder, start=1. BVar(1) >= 1, so lifted to BVar(2)
                assert_eq!(body.as_ref(), &Expr::from_kind(ExprKind::BVar(2)));
            }
            _ => panic!("Expected lambda"),
        }
    }

    #[test]
    fn test_has_loose_bvar_in_range_logic() {
        // Kill mutants: has_loose_bvar_in_range && to ||, < to <=, etc.

        // BVar(5) in range [3, 7) should be loose
        assert!(Expr::from_kind(ExprKind::BVar(5)).has_loose_bvar_in_range(3, 7));

        // BVar(3) in range [3, 7) should be loose (inclusive start)
        assert!(Expr::from_kind(ExprKind::BVar(3)).has_loose_bvar_in_range(3, 7));

        // BVar(7) in range [3, 7) should NOT be loose (exclusive end)
        assert!(!Expr::from_kind(ExprKind::BVar(7)).has_loose_bvar_in_range(3, 7));

        // BVar(2) in range [3, 7) should NOT be loose (below start)
        assert!(!Expr::from_kind(ExprKind::BVar(2)).has_loose_bvar_in_range(3, 7));

        // App: requires EITHER f OR a to have loose bvar (||, not &&)
        let app_with_loose = Expr::app(Expr::from_kind(ExprKind::BVar(5)), Expr::prop());
        assert!(app_with_loose.has_loose_bvar_in_range(3, 7));

        let app_without_loose = Expr::app(Expr::prop(), Expr::type_());
        assert!(!app_without_loose.has_loose_bvar_in_range(3, 7));
    }

    #[test]
    fn test_has_loose_bvar_nested_binders_arithmetic() {
        // Kill mutant: has_loose_bvar_in_range start + 1 with * or -

        // λ x. BVar(0) -- BVar(0) at depth 1 is NOT loose (bound by lambda)
        let lam = Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(0)),
        );
        assert!(!lam.has_loose_bvars());

        // λ x. BVar(1) -- BVar(1) at depth 1 IS loose (refers outside)
        let lam = Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(1)),
        );
        assert!(lam.has_loose_bvars());

        // λ x. λ y. BVar(2) -- BVar(2) at depth 2 IS loose
        let inner = Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(2)),
        );
        let outer = Expr::lam(BinderInfo::Default, Expr::prop(), inner);
        assert!(outer.has_loose_bvars());

        // λ x. λ y. BVar(1) -- BVar(1) at depth 2 is NOT loose (refers to x)
        let inner = Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(1)),
        );
        let outer = Expr::lam(BinderInfo::Default, Expr::prop(), inner);
        assert!(!outer.has_loose_bvars());
    }

    #[test]
    fn test_abstract_fvar_at_arithmetic() {
        // Kill mutants: abstract_fvar_at + with * or -

        // FVar(42) at depth 0 becomes BVar(0)
        let fvar = Expr::fvar(FVarId(42));
        assert_eq!(
            fvar.abstract_fvar(FVarId(42)),
            Expr::from_kind(ExprKind::BVar(0))
        );

        // Inside a lambda, FVar(42) becomes BVar(1) (depth increases)
        let lam = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::fvar(FVarId(42)));
        let result = lam.abstract_fvar(FVarId(42));
        match &result.kind {
            ExprKind::Lam(_, _, body) => {
                assert_eq!(body.as_ref(), &Expr::from_kind(ExprKind::BVar(1))); // depth was 0+1=1
            }
            _ => panic!("Expected lambda"),
        }

        // Doubly nested: FVar becomes BVar(2)
        let inner = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::fvar(FVarId(42)));
        let outer = Expr::lam(BinderInfo::Default, Expr::prop(), inner);
        let result = outer.abstract_fvar(FVarId(42));
        match &result.kind {
            ExprKind::Lam(_, _, body) => match &body.as_ref().kind {
                ExprKind::Lam(_, _, inner_body) => {
                    assert_eq!(inner_body.as_ref(), &Expr::from_kind(ExprKind::BVar(2)));
                    // depth was 0+1+1=2
                }
                _ => panic!("Expected nested lambda"),
            },
            _ => panic!("Expected lambda"),
        }
    }

    #[test]
    fn test_abstract_fvar_bvar_shift() {
        // Kill mutant: BVar(idx) >= depth should increment, testing idx + 1

        // BVar(0) at depth 0: 0 >= 0, should shift to BVar(1)
        let bvar = Expr::from_kind(ExprKind::BVar(0));
        let result = bvar.abstract_fvar(FVarId(42));
        assert_eq!(result, Expr::from_kind(ExprKind::BVar(1))); // shifted up by 1

        // BVar(5) at depth 3: 5 >= 3, should shift to BVar(6)
        let bvar = Expr::from_kind(ExprKind::BVar(5));
        let result = bvar.abstract_fvar_at(FVarId(42), 3);
        assert_eq!(result, Expr::from_kind(ExprKind::BVar(6)));

        // BVar(2) at depth 5: 2 < 5, should NOT shift
        let bvar = Expr::from_kind(ExprKind::BVar(2));
        let result = bvar.abstract_fvar_at(FVarId(42), 5);
        assert_eq!(result, Expr::from_kind(ExprKind::BVar(2)));
    }

    // =========================================================================
    // Additional Mutation Testing Kill Tests - expr.rs survivors
    // =========================================================================

    #[test]
    fn test_instantiate_at_greater_than() {
        // Kill mutant: replace > with >= in Expr::instantiate_at (line 173)
        // BVar(idx) > depth, not >=, because if idx == depth we substitute, not decrement

        // BVar(0) at depth 0: 0 == 0, gets substituted (not 0 > 0)
        let body = Expr::from_kind(ExprKind::BVar(0));
        let val = Expr::type_();
        let result = body.instantiate_at(&val, 0);
        assert_eq!(
            result,
            Expr::type_(),
            "BVar(0) at depth 0 should be substituted"
        );

        // BVar(1) at depth 0: 1 > 0, gets decremented to BVar(0)
        let body = Expr::from_kind(ExprKind::BVar(1));
        let result = body.instantiate_at(&val, 0);
        assert_eq!(
            result,
            Expr::from_kind(ExprKind::BVar(0)),
            "BVar(1) at depth 0 should become BVar(0)"
        );

        // BVar(1) at depth 1: 1 == 1, gets substituted
        let body = Expr::from_kind(ExprKind::BVar(1));
        let result = body.instantiate_at(&val, 1);
        assert_eq!(
            result,
            val.lift(1),
            "BVar(1) at depth 1 should be substituted with lifted val"
        );
    }

    #[test]
    fn test_lift_at_plus_vs_times() {
        // Kill mutants: replace + with * in Expr::lift_at (lines 240, 245)
        // Tests that idx + amount is used, not idx * amount

        // BVar(2) with amount=3: should be 2+3=5, not 2*3=6
        let e = Expr::from_kind(ExprKind::BVar(2));
        assert_eq!(
            e.lift_at(0, 3),
            Expr::from_kind(ExprKind::BVar(5)),
            "2 + 3 = 5, not 2 * 3 = 6"
        );

        // BVar(3) with amount=2: should be 3+2=5, not 3*2=6
        let e = Expr::from_kind(ExprKind::BVar(3));
        assert_eq!(
            e.lift_at(0, 2),
            Expr::from_kind(ExprKind::BVar(5)),
            "3 + 2 = 5, not 3 * 2 = 6"
        );

        // BVar(1) with amount=1: + and * give same result (2), so test with larger values
        let e = Expr::from_kind(ExprKind::BVar(4));
        assert_eq!(
            e.lift_at(0, 3),
            Expr::from_kind(ExprKind::BVar(7)),
            "4 + 3 = 7, not 4 * 3 = 12"
        );
    }

    #[test]
    fn test_lift_overflow_panics() {
        let e = Expr::from_kind(ExprKind::BVar(ExprMeta::MAX_BVAR_RANGE - 1));
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| e.lift(1)));
        assert!(
            result.is_err(),
            "lift should panic on metadata range overflow"
        );
    }

    #[test]
    fn test_checked_add_u32_overflow_saturates_not_panics() {
        // Verify that checked_add_u32 saturates at u32::MAX instead of panicking.
        // BVar(u32::MAX) cannot be constructed (ExprMeta caps at 1M), but the
        // arithmetic helper must still be safe as defense-in-depth.
        use super::checked_add_u32;
        assert_eq!(checked_add_u32(u32::MAX, 1, "test"), u32::MAX);
        assert_eq!(checked_add_u32(u32::MAX, u32::MAX, "test"), u32::MAX);
        assert_eq!(
            checked_add_u32(u32::MAX / 2 + 1, u32::MAX / 2 + 1, "test"),
            u32::MAX
        );
        // Normal cases still work
        assert_eq!(checked_add_u32(10, 20, "test"), 30);
        assert_eq!(checked_add_u32(0, 0, "test"), 0);
    }

    #[test]
    fn test_has_loose_bvar_or_vs_and() {
        // Kill mutants: replace || with && in Expr::has_loose_bvar_in_range (lines 272, 276, 277)
        // The function should return true if ANY part has a loose bvar (||), not if ALL do (&&)

        // App: only function has loose bvar
        let app_f_loose = Expr::app(Expr::from_kind(ExprKind::BVar(5)), Expr::prop());
        assert!(
            app_f_loose.has_loose_bvar_in_range(0, 10),
            "f has loose bvar"
        );

        // App: only argument has loose bvar
        let app_a_loose = Expr::app(Expr::prop(), Expr::from_kind(ExprKind::BVar(5)));
        assert!(
            app_a_loose.has_loose_bvar_in_range(0, 10),
            "a has loose bvar"
        );

        // Pi: only domain has loose bvar
        let pi_dom_loose = Expr::pi(
            BinderInfo::Default,
            Expr::from_kind(ExprKind::BVar(5)),
            Expr::prop(),
        );
        assert!(
            pi_dom_loose.has_loose_bvar_in_range(0, 10),
            "domain has loose bvar"
        );

        // Let: only type has loose bvar
        let let_ty_loose = Expr::let_named(
            Name::anon(),
            Expr::from_kind(ExprKind::BVar(5)),
            Expr::prop(),
            Expr::prop(),
            false,
        );
        assert!(
            let_ty_loose.has_loose_bvar_in_range(0, 10),
            "type has loose bvar"
        );

        // Let: only value has loose bvar
        let let_val_loose = Expr::let_named(
            Name::anon(),
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(5)),
            Expr::prop(),
            false,
        );
        assert!(
            let_val_loose.has_loose_bvar_in_range(0, 10),
            "value has loose bvar"
        );
    }

    #[test]
    fn test_has_loose_bvar_range_plus_arithmetic() {
        // Kill mutants: replace + with * or - in Expr::has_loose_bvar_in_range (lines 272, 277)
        // Tests that end.saturating_add(1) and start + 1 work correctly

        // Under 1 binder, BVar(0) is bound, BVar(1) is loose
        // With start=0, end=MAX, under binder start becomes 1, end becomes MAX+1 (saturated)
        // BVar(0) < 1, so not in range (bound by lambda)
        let lam_bound = Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(0)),
        );
        assert!(
            !lam_bound.has_loose_bvars(),
            "BVar(0) under lambda is bound"
        );

        // BVar(1) under lambda: with start=1, 1 >= 1 and 1 < MAX, so it IS loose
        let lam_loose = Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(1)),
        );
        assert!(lam_loose.has_loose_bvars(), "BVar(1) under lambda is loose");

        // Double nested: BVar(1) at depth 2 is bound (bound by inner), BVar(2) is loose
        let inner = Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::lam(
                BinderInfo::Default,
                Expr::prop(),
                Expr::from_kind(ExprKind::BVar(1)),
            ),
        );
        assert!(!inner.has_loose_bvars(), "BVar(1) under 2 lambdas is bound");

        // BVar(2) under 2 lambdas IS loose (indices 0 and 1 are bound)
        let inner_loose = Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::lam(
                BinderInfo::Default,
                Expr::prop(),
                Expr::from_kind(ExprKind::BVar(2)),
            ),
        );
        assert!(
            inner_loose.has_loose_bvars(),
            "BVar(2) under 2 lambdas is loose"
        );
    }

    #[test]
    fn test_abstract_fvar_at_plus_vs_other() {
        // Kill mutants: replace + with - or * in Expr::abstract_fvar_at (line 317)
        // Tests idx + 1 for shifting BVars

        // BVar(0) at depth 0: 0 >= 0, should become BVar(1) (0 + 1)
        let bvar = Expr::from_kind(ExprKind::BVar(0));
        let result = bvar.abstract_fvar_at(FVarId(99), 0);
        assert_eq!(
            result,
            Expr::from_kind(ExprKind::BVar(1)),
            "BVar(0) + 1 = BVar(1)"
        );

        // BVar(3) at depth 2: 3 >= 2, should become BVar(4) (3 + 1)
        let bvar = Expr::from_kind(ExprKind::BVar(3));
        let result = bvar.abstract_fvar_at(FVarId(99), 2);
        assert_eq!(
            result,
            Expr::from_kind(ExprKind::BVar(4)),
            "BVar(3) + 1 = BVar(4), not BVar(2) or BVar(3)"
        );

        // BVar(5) at depth 3: 5 >= 3, should become BVar(6) (5 + 1, not 5 - 1 = 4 or 5 * 1 = 5)
        let bvar = Expr::from_kind(ExprKind::BVar(5));
        let result = bvar.abstract_fvar_at(FVarId(99), 3);
        assert_eq!(
            result,
            Expr::from_kind(ExprKind::BVar(6)),
            "BVar(5) + 1 = BVar(6)"
        );
    }

    fn expect_lam_body(expr: &Expr) -> &Expr {
        let ExprKind::Lam(_, _, body) = &expr.kind else {
            panic!("Expected Lam");
        };
        body.as_ref()
    }

    fn expect_pi_body(expr: &Expr) -> &Expr {
        let ExprKind::Pi(_, _, body) = &expr.kind else {
            panic!("Expected Pi");
        };
        body.as_ref()
    }

    fn expect_let_parts(expr: &Expr) -> (&Expr, &Expr) {
        let ExprKind::Let(_, _, val, body, _) = &expr.kind else {
            panic!("Expected Let");
        };
        (val.as_ref(), body.as_ref())
    }

    fn lam_bvar(idx: u32) -> Expr {
        Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(idx)),
        )
    }

    fn pi_bvar(idx: u32) -> Expr {
        Expr::pi(
            BinderInfo::Default,
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(idx)),
        )
    }

    // =========================================================================
    // Targeted Mutation Kill Tests - depth+1 vs depth*1 vs depth-1
    // =========================================================================

    #[test]
    fn test_lift_at_binder_depth_increment() {
        // Kill mutants at lines 240, 245: replace + with * in body.lift_at(start + 1, amount)
        // When start=0, start+1=1 vs start*1=0 behaves differently

        // Test: lift λ x. BVar(0) by 5
        // The inner BVar(0) is at depth start=0 in the outer expression
        // Under the lambda, start becomes 0+1=1
        // BVar(0) < 1, so NO lift (it's bound by the lambda)
        // If start*1=0 instead, BVar(0) >= 0, it WOULD be lifted (wrong!)
        let lam = Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(0)),
        );
        let result = lam.lift(5);
        assert_eq!(
            expect_lam_body(&result),
            &Expr::from_kind(ExprKind::BVar(0)),
            "BVar(0) under lambda should NOT be lifted (bound)"
        );

        // Test: lift λ x. BVar(1) by 5
        // Under lambda, start becomes 1. BVar(1) >= 1, so lift to BVar(6)
        let lam = Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(1)),
        );
        let result = lam.lift(5);
        assert_eq!(
            expect_lam_body(&result),
            &Expr::from_kind(ExprKind::BVar(6)),
            "BVar(1) under lambda should be lifted to BVar(6)"
        );

        // Test: lift (Π x: Prop. BVar(0)) by 3
        // Pi also increments depth. BVar(0) should NOT be lifted.
        let pi = Expr::pi(
            BinderInfo::Default,
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(0)),
        );
        let result = pi.lift(3);
        assert_eq!(
            expect_pi_body(&result),
            &Expr::from_kind(ExprKind::BVar(0)),
            "BVar(0) under Pi should NOT be lifted (bound)"
        );

        // Test: let x = Prop in BVar(0) lifted by 3
        // Let binds the body at +1 depth
        let let_expr = Expr::let_named(
            Name::anon(),
            Expr::prop(),
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(0)),
            false,
        );
        let result = let_expr.lift(3);
        assert_eq!(
            expect_let_parts(&result).1,
            &Expr::from_kind(ExprKind::BVar(0)),
            "BVar(0) in let body should NOT be lifted (bound)"
        );

        // Test Pi body lift with start > 0
        // Π x. BVar(2) lifted starting at cutoff 1
        // Under Pi, cutoff becomes 1+1=2. BVar(2) >= 2, so lifted.
        let pi = Expr::pi(
            BinderInfo::Default,
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(2)),
        );
        let result = pi.lift_at(1, 3);
        assert_eq!(
            expect_pi_body(&result),
            &Expr::from_kind(ExprKind::BVar(5)),
            "BVar(2) should be lifted to BVar(5)"
        );
    }

    #[test]
    fn test_has_loose_bvar_nested_depth_arithmetic() {
        // Kill mutants at lines 272, 277: replace + with * or - in nested binder checks
        // λ x. Π y. BVar(1): depth becomes 2, so index 1 stays bound.
        let outer_lam = Expr::lam(BinderInfo::Default, Expr::prop(), pi_bvar(1));
        assert!(
            !outer_lam.has_loose_bvars(),
            "BVar(1) under 2 binders refers to outer binder, NOT loose"
        );

        // λ x. Π y. BVar(2): depth becomes 2, so index 2 is loose at the boundary.
        let outer_lam = Expr::lam(BinderInfo::Default, Expr::prop(), pi_bvar(2));
        assert!(
            outer_lam.has_loose_bvars(),
            "BVar(2) under 2 binders IS loose (refers outside)"
        );

        // let x = BVar(5) in λ y. BVar(1): the loose value keeps the whole let loose.
        let let_expr = Expr::let_named(
            Name::anon(),
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(5)),
            lam_bvar(1),
            false,
        );
        assert!(
            let_expr.has_loose_bvars(),
            "let with loose BVar(5) in value is loose"
        );

        // let x = Prop in λ y. BVar(2): let+lambda depth is 2, so index 2 is loose.
        let let_expr =
            Expr::let_named(Name::anon(), Expr::prop(), Expr::prop(), lam_bvar(2), false);
        assert!(
            let_expr.has_loose_bvars(),
            "BVar(2) under let+lambda IS loose"
        );

        // let x = Prop in λ y. BVar(1): let+lambda depth is 2, so index 1 stays bound.
        let let_expr =
            Expr::let_named(Name::anon(), Expr::prop(), Expr::prop(), lam_bvar(1), false);
        assert!(
            !let_expr.has_loose_bvars(),
            "BVar(1) under let+lambda refers to let binding, NOT loose"
        );
    }

    #[test]
    fn test_abstract_fvar_nested_depth_plus_one() {
        // Kill mutants at line 317: replace depth + 1 with depth - 1 or depth * 1

        // λ x. (FVar(42)) should become λ x. BVar(1)
        // Under λ, depth becomes 0+1=1, so FVar -> BVar(1)
        let lam = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::fvar(FVarId(42)));
        let result = lam.abstract_fvar(FVarId(42));
        assert_eq!(
            expect_lam_body(&result),
            &Expr::from_kind(ExprKind::BVar(1)),
            "FVar under lambda becomes BVar(1), not BVar(0) or BVar(-1)"
        );

        // Π x. (FVar(42)) should become Π x. BVar(1)
        let pi = Expr::pi(BinderInfo::Default, Expr::prop(), Expr::fvar(FVarId(42)));
        let result = pi.abstract_fvar(FVarId(42));
        assert_eq!(
            expect_pi_body(&result),
            &Expr::from_kind(ExprKind::BVar(1)),
            "FVar under Pi becomes BVar(1)"
        );

        // let x = FVar(42) in FVar(42)
        // Value: at depth 0, FVar -> BVar(0)
        // Body: at depth 0+1=1, FVar -> BVar(1)
        let let_expr = Expr::let_named(
            Name::anon(),
            Expr::prop(),
            Expr::fvar(FVarId(42)),
            Expr::fvar(FVarId(42)),
            false,
        );
        let result = let_expr.abstract_fvar(FVarId(42));
        let (val, body) = expect_let_parts(&result);
        assert_eq!(
            val,
            &Expr::from_kind(ExprKind::BVar(0)),
            "FVar in let value becomes BVar(0)"
        );
        assert_eq!(
            body,
            &Expr::from_kind(ExprKind::BVar(1)),
            "FVar in let body becomes BVar(1)"
        );

        // Triple nested: λ x. λ y. λ z. FVar(42)
        // At innermost level, depth = 3, so FVar -> BVar(3)
        let inner = Expr::fvar(FVarId(42));
        let l1 = Expr::lam(BinderInfo::Default, Expr::prop(), inner);
        let l2 = Expr::lam(BinderInfo::Default, Expr::prop(), l1);
        let l3 = Expr::lam(BinderInfo::Default, Expr::prop(), l2);
        let result = l3.abstract_fvar(FVarId(42));
        assert_eq!(
            expect_lam_body(expect_lam_body(expect_lam_body(&result))),
            &Expr::from_kind(ExprKind::BVar(3)),
            "FVar under 3 lambdas becomes BVar(3)"
        );
    }

    #[test]
    fn test_instantiate_at_gt_vs_gte() {
        // Kill mutant at line 173: replace > with >= in instantiate_at
        // When idx == depth, we substitute. When idx > depth, we decrement.
        // With >=, idx == depth would ALSO decrement (wrong!)

        // BVar(0) at depth 0: idx == depth, should SUBSTITUTE
        let body = Expr::from_kind(ExprKind::BVar(0));
        let val = Expr::type_();
        let result = body.instantiate_at(&val, 0);
        assert_eq!(
            result,
            Expr::type_(),
            "BVar(0) at depth 0: == case, should substitute"
        );

        // BVar(1) at depth 0: idx > depth, should DECREMENT to BVar(0)
        let body = Expr::from_kind(ExprKind::BVar(1));
        let result = body.instantiate_at(&val, 0);
        assert_eq!(
            result,
            Expr::from_kind(ExprKind::BVar(0)),
            "BVar(1) at depth 0: > case, should decrement"
        );

        // BVar(1) at depth 1: idx == depth, should SUBSTITUTE with val.lift(1)
        let body = Expr::from_kind(ExprKind::BVar(1));
        let result = body.instantiate_at(&val, 1);
        // val is Type, which has no loose bvars, so lift(1) = Type
        assert_eq!(
            result,
            Expr::type_(),
            "BVar(1) at depth 1: == case, should substitute"
        );

        // BVar(2) at depth 1: idx > depth, should decrement to BVar(1)
        let body = Expr::from_kind(ExprKind::BVar(2));
        let result = body.instantiate_at(&val, 1);
        assert_eq!(
            result,
            Expr::from_kind(ExprKind::BVar(1)),
            "BVar(2) at depth 1: > case, should decrement"
        );

        // Nested: λ x. BVar(1) instantiated with Type
        // Body BVar(1) is at depth 1, idx 1 == depth 1, so substitute
        let lam = Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(1)),
        );
        let result = lam.instantiate(&val);
        match &result.kind {
            ExprKind::Lam(_, _, body) => {
                // BVar(1) at depth 1 gets substituted with Type.lift(1) = Type
                assert_eq!(
                    body.as_ref(),
                    &Expr::type_(),
                    "BVar(1) under lambda at depth 0 refers to substitution target"
                );
            }
            _ => panic!("Expected Lam"),
        }
    }

    // =========================================================================
    // Kill: expr.rs:196:57 - Let body in instantiate_at (depth + 1)
    // =========================================================================
    #[test]
    fn test_instantiate_at_let_body_depth() {
        // This tests that the Let body correctly increments depth by 1
        // Mutation: depth + 1 -> depth - 1 or depth * 1 should fail
        let val = Expr::type_();

        // let x = Prop in BVar(1) - BVar(1) at depth 1 should be substituted
        // If depth is wrong (e.g., depth - 1 = -1 = u32::MAX), this breaks
        // If depth is wrong (e.g., depth * 1 = 0), BVar(1) > 0 so gets decremented
        let let_expr = Expr::let_named(
            Name::anon(),
            Expr::prop(),
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(1)),
            false,
        );
        let result = let_expr.instantiate(&val);
        match &result.kind {
            ExprKind::Let(_, _, _, body, _) => {
                // BVar(1) at depth 1: 1 == 1, so substitute with val.lift(1) = Type
                assert_eq!(
                    body.as_ref(),
                    &Expr::type_(),
                    "BVar(1) in let body should be substituted at depth 1"
                );
            }
            _ => panic!("Expected Let"),
        }

        // let x = Prop in BVar(0) - BVar(0) at depth 1 is the let-bound variable
        // Should NOT be substituted (0 < 1)
        let let_expr = Expr::let_named(
            Name::anon(),
            Expr::prop(),
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(0)),
            false,
        );
        let result = let_expr.instantiate(&val);
        match &result.kind {
            ExprKind::Let(_, _, _, body, _) => {
                assert_eq!(
                    body.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(0)),
                    "BVar(0) in let body refers to let binding, not substituted"
                );
            }
            _ => panic!("Expected Let"),
        }

        // let x = Prop in BVar(2) - BVar(2) at depth 1 should decrement to BVar(1)
        let let_expr = Expr::let_named(
            Name::anon(),
            Expr::prop(),
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(2)),
            false,
        );
        let result = let_expr.instantiate(&val);
        match &result.kind {
            ExprKind::Let(_, _, _, body, _) => {
                assert_eq!(
                    body.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(1)),
                    "BVar(2) in let body should decrement to BVar(1)"
                );
            }
            _ => panic!("Expected Let"),
        }
    }

    // =========================================================================
    // Kill: expr.rs:239:45 - Pi body in lift_at (start + 1)
    // =========================================================================
    #[test]
    fn test_lift_at_pi_body_start() {
        // This tests that the Pi body correctly increments start by 1
        // Mutation: start + 1 -> start - 1 should fail

        // π x : Prop . BVar(1) - BVar(1) is outside the pi (refers to external)
        // When lifting from start=0 by amount=2, the body is processed at start=1
        // BVar(1) >= 1, so it should become BVar(3)
        let pi = Expr::pi(
            BinderInfo::Default,
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(1)),
        );
        let result = pi.lift(2);
        match &result.kind {
            ExprKind::Pi(_, _, body) => {
                // At start=1, BVar(1) >= 1, so lift by 2: BVar(3)
                assert_eq!(
                    body.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(3)),
                    "BVar(1) in pi body should lift to BVar(3)"
                );
            }
            _ => panic!("Expected Pi"),
        }

        // π x : Prop . BVar(0) - BVar(0) is the pi-bound variable
        // At start=1: BVar(0) < 1, should NOT be lifted
        let pi = Expr::pi(
            BinderInfo::Default,
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(0)),
        );
        let result = pi.lift(2);
        match &result.kind {
            ExprKind::Pi(_, _, body) => {
                assert_eq!(
                    body.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(0)),
                    "BVar(0) in pi body should not be lifted"
                );
            }
            _ => panic!("Expected Pi"),
        }
    }

    // =========================================================================
    // Kill: expr.rs:244:45 - Let body in lift_at (start + 1)
    // =========================================================================
    #[test]
    fn test_lift_at_let_body_start() {
        // This tests that the Let body correctly increments start by 1
        // Mutation: start + 1 -> start - 1 should fail

        // let x = Prop in BVar(1) - BVar(1) refers outside the let
        // When lifting from start=0 by amount=3, the body is processed at start=1
        // BVar(1) >= 1, so it should become BVar(4)
        let let_expr = Expr::let_named(
            Name::anon(),
            Expr::prop(),
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(1)),
            false,
        );
        let result = let_expr.lift(3);
        match &result.kind {
            ExprKind::Let(_, _, _, body, _) => {
                assert_eq!(
                    body.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(4)),
                    "BVar(1) in let body should lift to BVar(4)"
                );
            }
            _ => panic!("Expected Let"),
        }

        // let x = Prop in BVar(0) - BVar(0) is the let-bound variable
        // At start=1: BVar(0) < 1, should NOT be lifted
        let let_expr = Expr::let_named(
            Name::anon(),
            Expr::prop(),
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(0)),
            false,
        );
        let result = let_expr.lift(3);
        match &result.kind {
            ExprKind::Let(_, _, _, body, _) => {
                assert_eq!(
                    body.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(0)),
                    "BVar(0) in let body should not be lifted"
                );
            }
            _ => panic!("Expected Let"),
        }

        // Critical case: let x = Prop in BVar(2)
        // If mutation is start - 1 = 0 - 1 = u32::MAX, this would break
        // At start=1: BVar(2) >= 1, lift by 3: BVar(5)
        let let_expr = Expr::let_named(
            Name::anon(),
            Expr::prop(),
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(2)),
            false,
        );
        let result = let_expr.lift(3);
        match &result.kind {
            ExprKind::Let(_, _, _, body, _) => {
                assert_eq!(
                    body.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(5)),
                    "BVar(2) in let body should lift to BVar(5)"
                );
            }
            _ => panic!("Expected Let"),
        }
    }

    // =========================================================================
    // lean4lean Theorem Coverage: Lift-Instantiate Commutation
    // Reference: Theory/VExpr.lean - lift_instN_lo, lift_inst_hi, inst_liftN
    // =========================================================================

    #[test]
    fn test_lift_inst_commutation_lo() {
        // lean4lean theorem: lift_instN_lo
        // For e with no loose bvars < lo, and lo <= k:
        //   lift(inst(e, v, lo), k, n) = inst(lift(e, k+1, n), lift(v, k, n), lo)
        //
        // Simplified case where lo = 0 (most common):
        //   lift(inst(e, v), k, n) = inst(lift(e, k+1, n), lift(v, k, n))

        // Case 1: Simple substitution
        // e = BVar(0), v = Prop
        // inst(BVar(0), Prop) = Prop
        // lift(Prop, 0, 5) = Prop (Prop has no BVars)
        // LHS = lift(inst(BVar(0), Prop), 0, 5) = lift(Prop, 0, 5) = Prop
        //
        // lift(BVar(0), 1, 5) = BVar(0) (0 < 1, not lifted)
        // lift(Prop, 0, 5) = Prop
        // inst(BVar(0), Prop) = Prop
        // RHS = inst(lift(BVar(0), 1, 5), lift(Prop, 0, 5)) = inst(BVar(0), Prop) = Prop
        let e = Expr::from_kind(ExprKind::BVar(0));
        let v = Expr::prop();
        let lhs = e.clone().instantiate(&v).lift_at(0, 5);
        let rhs = e.lift_at(1, 5).instantiate(&v.lift_at(0, 5));
        assert_eq!(lhs, rhs, "lift_inst_commutation_lo case 1");

        // Case 2: BVar survives substitution
        // e = BVar(2), v = Prop at depth 0
        // inst(BVar(2), Prop, 0) = BVar(1) (2 > 0, decrement)
        // lift(BVar(1), 0, 5) = BVar(6)
        //
        // lift(BVar(2), 1, 5) = BVar(7) (2 >= 1, add 5)
        // inst(BVar(7), Prop) = BVar(6) (7 > 0, decrement)
        let e = Expr::from_kind(ExprKind::BVar(2));
        let v = Expr::prop();
        let lhs = e.clone().instantiate(&v).lift_at(0, 5);
        let rhs = e.lift_at(1, 5).instantiate(&v.lift_at(0, 5));
        assert_eq!(lhs, rhs, "lift_inst_commutation_lo case 2");

        // Case 3: Nested expression
        // e = App(BVar(0), BVar(1))
        // v = Prop
        // inst: App(Prop, BVar(0))
        // lift by 3: App(Prop, BVar(3))
        let e = Expr::app(
            Expr::from_kind(ExprKind::BVar(0)),
            Expr::from_kind(ExprKind::BVar(1)),
        );
        let v = Expr::prop();
        let lhs = e.clone().instantiate(&v).lift_at(0, 3);
        let rhs = e.lift_at(1, 3).instantiate(&v.lift_at(0, 3));
        assert_eq!(lhs, rhs, "lift_inst_commutation_lo case 3");

        // Case 4: Lambda expression
        // e = λ x: Prop. BVar(1) (BVar(1) refers to outer var)
        // v = Type
        // inst(λ x. BVar(1), Type) at depth 0:
        //   body: inst(BVar(1), Type, 1) = Type (1 == 1, substitute)
        // Result: λ x: Prop. Type
        let e = Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(1)),
        );
        let v = Expr::type_();
        let lhs = e.clone().instantiate(&v).lift_at(0, 2);
        let rhs = e.lift_at(1, 2).instantiate(&v.lift_at(0, 2));
        assert_eq!(lhs, rhs, "lift_inst_commutation_lo case 4 - lambda");
    }

    #[test]
    fn test_lift_inst_commutation_hi() {
        // lean4lean theorem: lift_inst_hi (when k < lo)
        // For k < lo:
        //   lift(inst(e, v, lo), k, n) = inst(lift(e, k, n), v, lo + n)
        //
        // This handles the case where we lift below the substitution point.

        // Case: e = BVar(2), substitute at lo=1, lift at k=0
        // k=0 < lo=1, so use lift_inst_hi formula
        // inst(BVar(2), v, 1) = BVar(1) (2 > 1, decrement)
        // lift(BVar(1), 0, 3) = BVar(4)
        //
        // lift(BVar(2), 0, 3) = BVar(5)
        // inst(BVar(5), v, 4) = BVar(4) (5 > 4, decrement)
        let e = Expr::from_kind(ExprKind::BVar(2));
        let v = Expr::prop();
        let lhs = e.clone().instantiate_at(&v, 1).lift_at(0, 3);
        let rhs = e.lift_at(0, 3).instantiate_at(&v, 4); // lo + n = 1 + 3 = 4
        assert_eq!(lhs, rhs, "lift_inst_commutation_hi");
    }

    #[test]
    fn test_inst_lift_identity() {
        // lean4lean theorem: inst_liftN / inst_lift
        // For closed v (no loose bvars):
        //   inst(lift(e, 0, 1), v, 0) = e
        //
        // Lifting by 1 then instantiating at 0 is identity for closed v.

        // Case 1: Simple BVar
        // lift(BVar(0), 0, 1) = BVar(1)
        // inst(BVar(1), Prop, 0) = BVar(0) (1 > 0, decrement)
        let e = Expr::from_kind(ExprKind::BVar(0));
        let v = Expr::prop(); // closed
        let result = e.clone().lift(1).instantiate(&v);
        assert_eq!(result, e, "inst_lift_identity for BVar(0)");

        // Case 2: Higher BVar
        // lift(BVar(5), 0, 1) = BVar(6)
        // inst(BVar(6), Prop, 0) = BVar(5)
        let e = Expr::from_kind(ExprKind::BVar(5));
        let result = e.clone().lift(1).instantiate(&v);
        assert_eq!(result, e, "inst_lift_identity for BVar(5)");

        // Case 3: Nested expression
        let e = Expr::app(
            Expr::from_kind(ExprKind::BVar(0)),
            Expr::app(Expr::from_kind(ExprKind::BVar(1)), Expr::prop()),
        );
        let result = e.clone().lift(1).instantiate(&v);
        assert_eq!(result, e, "inst_lift_identity for nested App");

        // Case 4: Lambda
        // lift(λ x. BVar(1), 0, 1) = λ x. BVar(2)
        // inst at depth 0, body at depth 1: inst(BVar(2), Prop, 1) = BVar(1)
        // Result: λ x. BVar(1)
        let e = Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(1)),
        );
        let result = e.clone().lift(1).instantiate(&v);
        assert_eq!(result, e, "inst_lift_identity for lambda");
    }

    // =========================================================================
    // MData Tests
    // =========================================================================

    #[test]
    fn test_mdata_basic() {
        // Create metadata with a simple key-value pair
        let metadata: MDataMap = vec![(Name::from_string("key"), MDataValue::Bool(true))];
        let inner = Expr::prop();
        let mdata = Expr::mdata(metadata.clone(), inner.clone());

        // Check construction
        match &mdata.kind {
            ExprKind::MData(m, i) => {
                assert_eq!(m, &metadata);
                assert_eq!(i.as_ref(), &inner);
            }
            _ => panic!("Expected MData"),
        }
    }

    #[test]
    fn test_mdata_strip() {
        // strip_mdata should recursively remove MData wrappers
        let inner = Expr::type_();
        let mdata1 = Expr::mdata(vec![], inner.clone());
        let mdata2 = Expr::mdata(vec![], mdata1);

        // strip_mdata should return the innermost non-MData expression
        assert_eq!(mdata2.strip_mdata(), &inner);
    }

    #[test]
    fn test_mdata_instantiate() {
        // MData should pass through instantiate
        let metadata: MDataMap = vec![];
        let inner = Expr::from_kind(ExprKind::BVar(0));
        let mdata = Expr::mdata(metadata.clone(), inner);

        let val = Expr::prop();
        let result = mdata.instantiate(&val);

        // Should be MData wrapping the instantiated result
        match &result.kind {
            ExprKind::MData(_, inner) => {
                assert_eq!(inner.as_ref(), &Expr::prop());
            }
            _ => panic!("Expected MData after instantiate"),
        }
    }

    #[test]
    fn test_mdata_lift() {
        // MData should pass through lift
        let inner = Expr::from_kind(ExprKind::BVar(0));
        let mdata = Expr::mdata(vec![], inner);

        let result = mdata.lift(1);

        match &result.kind {
            ExprKind::MData(_, inner) => {
                assert_eq!(inner.as_ref(), &Expr::from_kind(ExprKind::BVar(1)));
            }
            _ => panic!("Expected MData after lift"),
        }
    }

    #[test]
    fn test_mdata_has_loose_bvars() {
        // MData should check inner for loose bvars
        let inner_with_bvar = Expr::from_kind(ExprKind::BVar(0));
        let mdata_with_bvar = Expr::mdata(vec![], inner_with_bvar);
        assert!(mdata_with_bvar.has_loose_bvars());

        let inner_without_bvar = Expr::prop();
        let mdata_without_bvar = Expr::mdata(vec![], inner_without_bvar);
        assert!(!mdata_without_bvar.has_loose_bvars());
    }

    #[test]
    fn test_mdata_level_params() {
        // MData should propagate level parameter instantiation
        let u = Name::from_string("u");
        let inner = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
        let mdata = Expr::mdata(vec![], inner);

        let subst = vec![(u, Level::succ(Level::zero()))];
        let result = mdata.instantiate_level_params(&subst);

        match &result.kind {
            ExprKind::MData(_, inner) => {
                assert_eq!(
                    inner.as_ref(),
                    &Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))
                );
            }
            _ => panic!("Expected MData after level param instantiation"),
        }
    }

    // =========================================================================
    // Tests for subst_fvar
    // =========================================================================

    #[test]
    fn test_subst_fvar_basic() {
        // Substituting FVar(42) with Prop should replace it
        let fvar = Expr::fvar(FVarId(42));
        let result = fvar.subst_fvar(FVarId(42), &Expr::prop());
        assert_eq!(result, Expr::prop());

        // Different FVar should not be replaced
        let fvar = Expr::fvar(FVarId(42));
        let result = fvar.subst_fvar(FVarId(99), &Expr::prop());
        assert_eq!(result, Expr::fvar(FVarId(42)));
    }

    #[test]
    fn test_subst_fvar_unchanged() {
        // BVar should not be affected
        let bvar = Expr::from_kind(ExprKind::BVar(5));
        let result = bvar.subst_fvar(FVarId(42), &Expr::prop());
        assert_eq!(result, Expr::from_kind(ExprKind::BVar(5)));

        // Sort should not be affected
        let sort = Expr::type_();
        let result = sort.subst_fvar(FVarId(42), &Expr::prop());
        assert_eq!(result, Expr::type_());

        // Const should not be affected
        let c = Expr::from_kind(ExprKind::Const(Name::from_string("Nat"), LevelVec::new()));
        let result = c.subst_fvar(FVarId(42), &Expr::prop());
        assert_eq!(
            result,
            Expr::from_kind(ExprKind::Const(Name::from_string("Nat"), LevelVec::new()))
        );

        // Literal should not be affected
        let lit = Expr::nat_lit(123);
        let result = lit.subst_fvar(FVarId(42), &Expr::prop());
        assert_eq!(result, Expr::nat_lit(123));
    }

    #[test]
    fn test_subst_fvar_in_app() {
        // Substitute FVar in function position
        let app = Expr::app(Expr::fvar(FVarId(42)), Expr::type_());
        let result = app.subst_fvar(FVarId(42), &Expr::prop());
        assert_eq!(result, Expr::app(Expr::prop(), Expr::type_()));

        // Substitute FVar in argument position
        let app = Expr::app(Expr::type_(), Expr::fvar(FVarId(42)));
        let result = app.subst_fvar(FVarId(42), &Expr::prop());
        assert_eq!(result, Expr::app(Expr::type_(), Expr::prop()));

        // Substitute FVar in both positions
        let app = Expr::app(Expr::fvar(FVarId(42)), Expr::fvar(FVarId(42)));
        let result = app.subst_fvar(FVarId(42), &Expr::prop());
        assert_eq!(result, Expr::app(Expr::prop(), Expr::prop()));
    }

    #[test]
    fn test_subst_fvar_in_binders() {
        // Lambda: substitute in type and body
        let lam = Expr::lam(
            BinderInfo::Default,
            Expr::fvar(FVarId(42)),
            Expr::fvar(FVarId(42)),
        );
        let result = lam.subst_fvar(FVarId(42), &Expr::type_());
        match &result.kind {
            ExprKind::Lam(_, ty, body) => {
                assert_eq!(ty.as_ref(), &Expr::type_());
                assert_eq!(body.as_ref(), &Expr::type_());
            }
            _ => panic!("Expected Lam"),
        }

        // Pi: substitute in type and body
        let pi = Expr::pi(
            BinderInfo::Default,
            Expr::fvar(FVarId(42)),
            Expr::fvar(FVarId(42)),
        );
        let result = pi.subst_fvar(FVarId(42), &Expr::type_());
        match &result.kind {
            ExprKind::Pi(_, ty, body) => {
                assert_eq!(ty.as_ref(), &Expr::type_());
                assert_eq!(body.as_ref(), &Expr::type_());
            }
            _ => panic!("Expected Pi"),
        }

        // Let: substitute in type, value, and body
        let let_expr = Expr::from_kind(ExprKind::Let(
            Name::anon(),
            Arc::new(Expr::fvar(FVarId(42))),
            Arc::new(Expr::fvar(FVarId(42))),
            Arc::new(Expr::fvar(FVarId(42))),
            false,
        ));
        let result = let_expr.subst_fvar(FVarId(42), &Expr::prop());
        match &result.kind {
            ExprKind::Let(_, ty, val, body, _) => {
                assert_eq!(ty.as_ref(), &Expr::prop());
                assert_eq!(val.as_ref(), &Expr::prop());
                assert_eq!(body.as_ref(), &Expr::prop());
            }
            _ => panic!("Expected Let"),
        }
    }

    #[test]
    fn test_subst_fvar_in_proj() {
        // Projection with FVar
        let proj = Expr::from_kind(ExprKind::Proj(
            Name::from_string("fst"),
            0,
            Arc::new(Expr::fvar(FVarId(42))),
        ));
        let result = proj.subst_fvar(FVarId(42), &Expr::type_());
        match &result.kind {
            ExprKind::Proj(name, idx, e) => {
                assert_eq!(name, &Name::from_string("fst"));
                assert_eq!(*idx, 0);
                assert_eq!(e.as_ref(), &Expr::type_());
            }
            _ => panic!("Expected Proj"),
        }
    }

    #[test]
    fn test_subst_fvar_in_mdata() {
        // MData should propagate substitution
        let mdata = Expr::mdata(vec![], Expr::fvar(FVarId(42)));
        let result = mdata.subst_fvar(FVarId(42), &Expr::prop());
        match &result.kind {
            ExprKind::MData(_, inner) => {
                assert_eq!(inner.as_ref(), &Expr::prop());
            }
            _ => panic!("Expected MData"),
        }
    }

    #[test]
    fn test_subst_fvar_nested() {
        // Deep nesting: λx. λy. FVar(42)
        let inner = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::fvar(FVarId(42)));
        let outer = Expr::lam(BinderInfo::Default, Expr::prop(), inner);
        let result = outer.subst_fvar(FVarId(42), &Expr::type_());

        match &result.kind {
            ExprKind::Lam(_, _, body) => match &body.as_ref().kind {
                ExprKind::Lam(_, _, inner_body) => {
                    assert_eq!(inner_body.as_ref(), &Expr::type_());
                }
                _ => panic!("Expected nested Lam"),
            },
            _ => panic!("Expected Lam"),
        }
    }

    // =========================================================================
    // Tests for instantiate_rev (multi-arg substitution)
    // Part of #3210.
    // =========================================================================

    #[test]
    fn test_instantiate_rev_empty() {
        // Empty vals should return unchanged expression
        let body = Expr::from_kind(ExprKind::BVar(0));
        let result = body.clone().instantiate_rev(&[]);
        assert_eq!(result, body);
    }

    #[test]
    fn test_instantiate_rev_single_arg() {
        // Single arg should behave like instantiate
        let body = Expr::from_kind(ExprKind::BVar(0));
        let val = Expr::fvar(FVarId(42));
        let result = body.instantiate_rev(std::slice::from_ref(&val));
        assert_eq!(result, body.instantiate(&val));
    }

    #[test]
    fn test_instantiate_rev_two_args() {
        // λ x₀. λ x₁. body  with body = App(BVar(1), BVar(0))
        // x₀ = BVar(1) in body, x₁ = BVar(0) in body
        // instantiate_rev([a₀, a₁]) should give App(a₀, a₁)
        // vals[0] = a₀ replaces BVar(0), vals[1] = a₁ replaces BVar(1)
        // But wait: convention is vals[0] replaces BVar(0) = x₁ (innermost)
        // vals[1] replaces BVar(1) = x₀ (outermost)
        let body = Expr::app(
            Expr::from_kind(ExprKind::BVar(1)), // x₀
            Expr::from_kind(ExprKind::BVar(0)), // x₁
        );
        let a0 = Expr::fvar(FVarId(100)); // replaces x₁ (BVar(0))
        let a1 = Expr::fvar(FVarId(200)); // replaces x₀ (BVar(1))
        let result = body.instantiate_rev(&[a0.clone(), a1.clone()]);
        assert_eq!(result, Expr::app(a1, a0));
    }

    #[test]
    fn test_instantiate_rev_higher_bvars_shifted() {
        // BVar(2) with 2 substitution values should be shifted down by 2 → BVar(0)
        let body = Expr::from_kind(ExprKind::BVar(2));
        let a0 = Expr::fvar(FVarId(100));
        let a1 = Expr::fvar(FVarId(200));
        let result = body.instantiate_rev(&[a0, a1]);
        assert_eq!(result, Expr::from_kind(ExprKind::BVar(0)));
    }

    #[test]
    fn test_instantiate_rev_matches_sequential_instantiate() {
        // For a body with BVar(0) and BVar(1), instantiate_rev([v0, v1])
        // should give the same result as sequential instantiation:
        //   body.instantiate(v1).instantiate(v0)
        // Actually: instantiate_rev replaces BVar(i) with vals[i], which is
        // equivalent to applying the outermost lambda first then innermost.
        // Sequential: body.instantiate(v1) replaces BVar(0) with v1, shifting BVar(1)->BVar(0)
        // Then .instantiate(v0) replaces the new BVar(0) with v0.
        let body = Expr::app(
            Expr::from_kind(ExprKind::BVar(1)),
            Expr::from_kind(ExprKind::BVar(0)),
        );
        let v0 = Expr::prop(); // for BVar(0) = innermost lambda param
        let v1 = Expr::type_(); // for BVar(1) = outermost lambda param

        let multi_result = body.instantiate_rev(&[v0.clone(), v1.clone()]);
        let seq_result = body.instantiate(&v0).instantiate(&v1);
        assert_eq!(multi_result, seq_result);
    }

    #[test]
    fn test_instantiate_rev_under_binder() {
        // λ z. App(BVar(2), BVar(1))
        // With 2 substitution values: BVar(0) bound by lambda (unchanged),
        // BVar(1) → vals[0] lifted by 1, BVar(2) → vals[1] lifted by 1
        let inner = Expr::lam(
            crate::expr::BinderData::default(),
            Expr::prop(),
            Expr::app(
                Expr::from_kind(ExprKind::BVar(2)),
                Expr::from_kind(ExprKind::BVar(1)),
            ),
        );
        let v0 = Expr::fvar(FVarId(10));
        let v1 = Expr::fvar(FVarId(20));
        let result = inner.instantiate_rev(&[v0.clone(), v1.clone()]);
        // Under the binder, depth=1:
        // BVar(2): 2 >= 1 && 2 < 1+2=3, so idx=2, i=2-1=1, vals[1]=v1 lifted by 1
        // BVar(1): 1 >= 1 && 1 < 3, so idx=1, i=1-1=0, vals[0]=v0 lifted by 1
        // FVars don't have loose bvars, so lift is identity
        match &result.kind {
            ExprKind::Lam(_, _, body) => {
                assert_eq!(body.as_ref(), &Expr::app(v1, v0),);
            }
            _ => panic!("Expected Lam"),
        }
    }

    // =========================================================================
    // Tests for instantiate_level_params
    // =========================================================================

    #[test]
    fn test_instantiate_level_params_sort() {
        // Sort(u) with u -> Type1 should become Sort(Type1)
        let u = Name::from_string("u");
        let sort = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
        let subst = vec![(u, Level::succ(Level::zero()))];
        let result = sort.instantiate_level_params(&subst);
        assert_eq!(
            result,
            Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))
        );
    }

    #[test]
    fn test_instantiate_level_params_const() {
        // Const with level params
        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let levels: LevelVec =
            smallvec::smallvec![Level::param(u.clone()), Level::param(v.clone())];
        let c = Expr::from_kind(ExprKind::Const(Name::from_string("List"), levels));

        let subst = vec![
            (u, Level::zero()),
            (v, Level::succ(Level::succ(Level::zero()))),
        ];
        let result = c.instantiate_level_params(&subst);

        match &result.kind {
            ExprKind::Const(name, lvls) => {
                assert_eq!(name, &Name::from_string("List"));
                assert_eq!(lvls.len(), 2);
                assert_eq!(lvls[0], Level::zero());
                assert_eq!(lvls[1], Level::succ(Level::succ(Level::zero())));
            }
            _ => panic!("Expected Const"),
        }
    }

    #[test]
    fn test_instantiate_level_params_empty_subst() {
        // Empty substitution should return same expression
        let u = Name::from_string("u");
        let sort = Expr::from_kind(ExprKind::Sort(Level::param(u)));
        let subst: Vec<(Name, Level)> = vec![];
        let result = sort.instantiate_level_params(&subst);
        assert_eq!(result, sort);
    }

    #[test]
    fn test_instantiate_level_params_unchanged() {
        // BVar, FVar, Lit should pass through unchanged
        let u = Name::from_string("u");
        let subst = vec![(u, Level::zero())];

        assert_eq!(
            Expr::from_kind(ExprKind::BVar(0)).instantiate_level_params(&subst),
            Expr::from_kind(ExprKind::BVar(0))
        );
        assert_eq!(
            Expr::fvar(FVarId(42)).instantiate_level_params(&subst),
            Expr::fvar(FVarId(42))
        );
        assert_eq!(
            Expr::nat_lit(123).instantiate_level_params(&subst),
            Expr::nat_lit(123)
        );
    }

    #[test]
    fn test_instantiate_level_params_in_binders() {
        // Lambda with Sort(u) in type and body
        let u = Name::from_string("u");
        let lam = Expr::lam(
            BinderInfo::Default,
            Expr::from_kind(ExprKind::Sort(Level::param(u.clone()))),
            Expr::from_kind(ExprKind::Sort(Level::param(u.clone()))),
        );
        let subst = vec![(u, Level::succ(Level::zero()))];
        let result = lam.instantiate_level_params(&subst);

        match &result.kind {
            ExprKind::Lam(_, ty, body) => {
                assert_eq!(
                    ty.as_ref(),
                    &Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))
                );
                assert_eq!(
                    body.as_ref(),
                    &Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))
                );
            }
            _ => panic!("Expected Lam"),
        }

        // Pi with levels
        let v = Name::from_string("v");
        let pi = Expr::pi(
            BinderInfo::Default,
            Expr::from_kind(ExprKind::Sort(Level::param(v.clone()))),
            Expr::from_kind(ExprKind::Sort(Level::param(v.clone()))),
        );
        let subst = vec![(v, Level::zero())];
        let result = pi.instantiate_level_params(&subst);

        match &result.kind {
            ExprKind::Pi(_, ty, body) => {
                assert_eq!(ty.as_ref(), &Expr::prop());
                assert_eq!(body.as_ref(), &Expr::prop());
            }
            _ => panic!("Expected Pi"),
        }
    }

    #[test]
    fn test_instantiate_level_params_in_app() {
        // App with levels in subexpressions
        let u = Name::from_string("u");
        let app = Expr::app(
            Expr::from_kind(ExprKind::Sort(Level::param(u.clone()))),
            Expr::from_kind(ExprKind::Sort(Level::param(u.clone()))),
        );
        let subst = vec![(u, Level::succ(Level::zero()))];
        let result = app.instantiate_level_params(&subst);

        match &result.kind {
            ExprKind::App(f, a) => {
                assert_eq!(
                    f.as_ref(),
                    &Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))
                );
                assert_eq!(
                    a.as_ref(),
                    &Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))
                );
            }
            _ => panic!("Expected App"),
        }
    }

    #[test]
    fn test_instantiate_level_params_in_let() {
        // Let with levels in all parts
        let u = Name::from_string("u");
        let let_expr = Expr::from_kind(ExprKind::Let(
            Name::anon(),
            Arc::new(Expr::from_kind(ExprKind::Sort(Level::param(u.clone())))),
            Arc::new(Expr::from_kind(ExprKind::Sort(Level::param(u.clone())))),
            Arc::new(Expr::from_kind(ExprKind::Sort(Level::param(u.clone())))),
            false,
        ));
        let subst = vec![(u, Level::zero())];
        let result = let_expr.instantiate_level_params(&subst);

        match &result.kind {
            ExprKind::Let(_, ty, val, body, _) => {
                assert_eq!(ty.as_ref(), &Expr::prop());
                assert_eq!(val.as_ref(), &Expr::prop());
                assert_eq!(body.as_ref(), &Expr::prop());
            }
            _ => panic!("Expected Let"),
        }
    }

    #[test]
    fn test_instantiate_level_params_in_proj() {
        // Proj with level in inner expression
        let u = Name::from_string("u");
        let proj = Expr::from_kind(ExprKind::Proj(
            Name::from_string("fst"),
            0,
            Arc::new(Expr::from_kind(ExprKind::Sort(Level::param(u.clone())))),
        ));
        let subst = vec![(u, Level::succ(Level::zero()))];
        let result = proj.instantiate_level_params(&subst);

        match &result.kind {
            ExprKind::Proj(name, idx, e) => {
                assert_eq!(name, &Name::from_string("fst"));
                assert_eq!(*idx, 0);
                assert_eq!(
                    e.as_ref(),
                    &Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))
                );
            }
            _ => panic!("Expected Proj"),
        }
    }

    #[test]
    fn test_instantiate_level_params_multiple() {
        // Multiple different params
        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let w = Name::from_string("w");

        let app = Expr::app(
            Expr::app(
                Expr::from_kind(ExprKind::Sort(Level::param(u.clone()))),
                Expr::from_kind(ExprKind::Sort(Level::param(v.clone()))),
            ),
            Expr::from_kind(ExprKind::Sort(Level::param(w.clone()))),
        );

        let subst = vec![
            (u, Level::zero()),
            (v, Level::succ(Level::zero())),
            (w, Level::succ(Level::succ(Level::zero()))),
        ];
        let result = app.instantiate_level_params(&subst);

        // Check the result has all three params substituted
        match &result.kind {
            ExprKind::App(f, a) => {
                assert_eq!(
                    a.as_ref(),
                    &Expr::from_kind(ExprKind::Sort(Level::succ(Level::succ(Level::zero()))))
                );
                match &f.as_ref().kind {
                    ExprKind::App(f2, a2) => {
                        assert_eq!(f2.as_ref(), &Expr::prop());
                        assert_eq!(
                            a2.as_ref(),
                            &Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))
                        );
                    }
                    _ => panic!("Expected nested App"),
                }
            }
            _ => panic!("Expected App"),
        }
    }

    #[test]
    fn test_instantiate_level_params_direct_small_subst() {
        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let expr = Expr::from_kind(ExprKind::Const(
            Name::from_string("List"),
            smallvec::smallvec![Level::param(u.clone()), Level::param(v.clone())],
        ));

        let result = expr.instantiate_level_params_direct(
            &[u.clone(), v.clone()],
            &[Level::zero(), Level::succ(Level::zero())],
        );

        assert_eq!(
            result,
            Expr::from_kind(ExprKind::Const(
                Name::from_string("List"),
                smallvec::smallvec![Level::zero(), Level::succ(Level::zero())],
            ))
        );
    }

    #[test]
    fn test_instantiate_level_params_direct_large_subst() {
        let names: Vec<Name> = (0..5)
            .map(|i| Name::from_string(&format!("u{i}")))
            .collect();
        let expr = Expr::from_kind(ExprKind::Const(
            Name::from_string("Big"),
            names.iter().cloned().map(Level::param).collect(),
        ));
        let levels: Vec<Level> = (0..5).map(|i| Level::zero().add_offset(i)).collect();

        let direct = expr.instantiate_level_params_direct(&names, &levels);
        let pair_subst: Vec<(Name, Level)> = names.iter().cloned().zip(levels.clone()).collect();
        let via_pairs = expr.instantiate_level_params(&pair_subst);

        assert_eq!(
            direct, via_pairs,
            "large substitutions should match the existing HashMap-backed path"
        );
    }

    // =========================================================================
    // Tests for strip_mdata
    // =========================================================================

    #[test]
    fn test_strip_mdata_basic() {
        // Non-MData expression returns self
        let prop = Expr::prop();
        assert_eq!(prop.strip_mdata(), &prop);

        let bvar = Expr::from_kind(ExprKind::BVar(5));
        assert_eq!(bvar.strip_mdata(), &bvar);
    }

    #[test]
    fn test_strip_mdata_single() {
        // Single layer of MData
        let inner = Expr::type_();
        let mdata = Expr::mdata(vec![], inner.clone());
        assert_eq!(mdata.strip_mdata(), &inner);
    }

    #[test]
    fn test_strip_mdata_nested() {
        // Nested MData layers should all be stripped
        let inner = Expr::prop();
        let mdata1 = Expr::mdata(vec![], inner.clone());
        let mdata2 = Expr::mdata(vec![], mdata1);
        let mdata3 = Expr::mdata(vec![], mdata2);
        assert_eq!(mdata3.strip_mdata(), &inner);
    }

    #[test]
    fn test_strip_mdata_with_metadata() {
        // MData with actual metadata
        let inner = Expr::fvar(FVarId(42));
        let metadata = vec![
            (Name::from_string("key1"), MDataValue::Bool(true)),
            (Name::from_string("key2"), MDataValue::Nat(100)),
        ];
        let mdata = Expr::mdata(metadata, inner.clone());
        assert_eq!(mdata.strip_mdata(), &inner);
    }

    #[test]
    fn test_strip_mdata_various_inner() {
        // Test with various inner expression types
        let exprs = vec![
            Expr::from_kind(ExprKind::BVar(0)),
            Expr::fvar(FVarId(1)),
            Expr::type_(),
            Expr::prop(),
            Expr::nat_lit(42),
            Expr::lam(
                BinderInfo::Default,
                Expr::prop(),
                Expr::from_kind(ExprKind::BVar(0)),
            ),
            Expr::pi(
                BinderInfo::Default,
                Expr::type_(),
                Expr::from_kind(ExprKind::BVar(0)),
            ),
            Expr::app(Expr::fvar(FVarId(1)), Expr::fvar(FVarId(2))),
        ];

        for inner in exprs {
            let mdata = Expr::mdata(vec![], inner.clone());
            assert_eq!(
                mdata.strip_mdata(),
                &inner,
                "strip_mdata failed for {:?}",
                inner
            );
        }
    }

    // =========================================================================
    // Tests for get_app_fn and get_app_args
    // =========================================================================

    #[test]
    fn test_get_app_fn_basic() {
        // Non-App returns self
        let prop = Expr::prop();
        assert_eq!(prop.get_app_fn(), &prop);

        let fvar = Expr::fvar(FVarId(42));
        assert_eq!(fvar.get_app_fn(), &fvar);
    }

    #[test]
    fn test_get_app_fn_single() {
        // Single application: f(x) -> f
        let f = Expr::fvar(FVarId(1));
        let x = Expr::fvar(FVarId(2));
        let app = Expr::app(f.clone(), x);
        assert_eq!(app.get_app_fn(), &f);
    }

    #[test]
    fn test_get_app_fn_nested() {
        // Nested applications: f(x)(y)(z) -> f
        let f = Expr::fvar(FVarId(1));
        let x = Expr::fvar(FVarId(2));
        let y = Expr::fvar(FVarId(3));
        let z = Expr::fvar(FVarId(4));
        let app = Expr::app(Expr::app(Expr::app(f.clone(), x), y), z);
        assert_eq!(app.get_app_fn(), &f);
    }

    #[test]
    fn test_get_app_args_empty() {
        // Non-App returns empty vec
        let prop = Expr::prop();
        assert!(prop.get_app_args().is_empty());
    }

    #[test]
    fn test_get_app_args_single() {
        // Single application: f(x) -> [x]
        let f = Expr::fvar(FVarId(1));
        let x = Expr::fvar(FVarId(2));
        let app = Expr::app(f, x.clone());

        let args = app.get_app_args();
        assert_eq!(args.len(), 1);
        assert_eq!(args[0], &x);
    }

    #[test]
    fn test_get_app_args_multiple() {
        // Multiple applications: f(x)(y)(z) -> [x, y, z]
        let f = Expr::fvar(FVarId(1));
        let x = Expr::fvar(FVarId(2));
        let y = Expr::fvar(FVarId(3));
        let z = Expr::fvar(FVarId(4));
        let app = Expr::app(Expr::app(Expr::app(f, x.clone()), y.clone()), z.clone());

        let args = app.get_app_args();
        assert_eq!(args.len(), 3);
        assert_eq!(args[0], &x);
        assert_eq!(args[1], &y);
        assert_eq!(args[2], &z);
    }

    // =========================================================================
    // Size assertions (Issue #337)
    // =========================================================================

    /// Verify Expr enum size for regression detection.
    ///
    /// The lib.rs documentation mentions "Small expression nodes (16 bytes target)".
    /// However, the actual size is larger due to:
    /// - Named struct variants (CubicalPath, CubicalHComp, CubicalTransp)
    /// - Name containing SmallVec/String
    /// - Multiple Arc fields per variant
    ///
    /// Current baseline: 136 bytes (measured 2026-01-28)
    /// This test prevents accidental size regressions from new variants/fields.
    /// See issue #337 for tracking the 16-byte aspirational target.
    #[test]
    fn test_expr_size_regression() {
        use std::mem::size_of;

        let expr_size = size_of::<Expr>();
        let arc_size = size_of::<Arc<Expr>>();

        // Arc<Expr> should be pointer-sized (8 bytes on 64-bit)
        assert_eq!(arc_size, 8, "Arc<Expr> should be pointer-sized");

        // Baseline: 136 bytes as of 2026-01-28.
        // This threshold catches regressions (size increases) but doesn't fail
        // on current implementation. Decrease when optimization work is done.
        //
        // Size breakdown:
        // - Largest variant: Const(Name, LevelVec) or MData(MDataMap, Arc<Expr>)
        // - Name: SmallVec + potential String = ~88 bytes
        // - LevelVec/MDataMap: Vec-like = ~24 bytes
        // - Plus discriminant and alignment padding
        let baseline = 136;
        let tolerance = 16; // Allow small variations from padding/alignment changes

        assert!(
            expr_size <= baseline + tolerance,
            "Expr size {} exceeds baseline {} + tolerance {} - new field/variant added?",
            expr_size,
            baseline,
            tolerance
        );

        // Document current size for future reference
        if expr_size != baseline {
            eprintln!(
                "Note: Expr size changed from {} to {} bytes (within tolerance)",
                baseline, expr_size
            );
        }
    }

    // =========================================================================
    // collect_constants tests
    // =========================================================================

    #[test]
    fn test_collect_constants_empty() {
        // Non-constant expressions should return empty set
        assert!(Expr::from_kind(ExprKind::BVar(0))
            .collect_constants()
            .is_empty());
        assert!(Expr::fvar(FVarId(42)).collect_constants().is_empty());
        assert!(Expr::prop().collect_constants().is_empty());
        assert!(Expr::type_().collect_constants().is_empty());
        assert!(Expr::nat_lit(123).collect_constants().is_empty());
    }

    #[test]
    fn test_collect_constants_single() {
        let name = Name::from_string("Nat.add");
        let e = Expr::from_kind(ExprKind::Const(name.clone(), LevelVec::new()));
        let constants = e.collect_constants();
        assert_eq!(constants.len(), 1);
        assert!(constants.contains(&name));
    }

    #[test]
    fn test_collect_constants_nested() {
        // Test App(Const(f), Const(x))
        let f = Name::from_string("f");
        let x = Name::from_string("x");
        let app = Expr::app(
            Expr::from_kind(ExprKind::Const(f.clone(), LevelVec::new())),
            Expr::from_kind(ExprKind::Const(x.clone(), LevelVec::new())),
        );
        let constants = app.collect_constants();
        assert_eq!(constants.len(), 2);
        assert!(constants.contains(&f));
        assert!(constants.contains(&x));
    }

    #[test]
    fn test_collect_constants_duplicates() {
        // Same constant appearing multiple times should only appear once in result
        let name = Name::from_string("Nat.add");
        let app = Expr::app(
            Expr::from_kind(ExprKind::Const(name.clone(), LevelVec::new())),
            Expr::from_kind(ExprKind::Const(name.clone(), LevelVec::new())),
        );
        let constants = app.collect_constants();
        assert_eq!(constants.len(), 1);
        assert!(constants.contains(&name));
    }

    #[test]
    fn test_collect_constants_lambda() {
        // λ (x : T). f x
        let t = Name::from_string("T");
        let f = Name::from_string("f");
        let body = Expr::app(
            Expr::from_kind(ExprKind::Const(f.clone(), LevelVec::new())),
            Expr::from_kind(ExprKind::BVar(0)), // x
        );
        let lam = Expr::lam(
            BinderInfo::Default,
            Expr::from_kind(ExprKind::Const(t.clone(), LevelVec::new())),
            body,
        );
        let constants = lam.collect_constants();
        assert_eq!(constants.len(), 2);
        assert!(constants.contains(&t));
        assert!(constants.contains(&f));
    }

    #[test]
    fn test_collect_constants_pi() {
        // ∀ (x : A), B x
        let a = Name::from_string("A");
        let b = Name::from_string("B");
        let body = Expr::app(
            Expr::from_kind(ExprKind::Const(b.clone(), LevelVec::new())),
            Expr::from_kind(ExprKind::BVar(0)),
        );
        let pi = Expr::pi(
            BinderInfo::Default,
            Expr::from_kind(ExprKind::Const(a.clone(), LevelVec::new())),
            body,
        );
        let constants = pi.collect_constants();
        assert_eq!(constants.len(), 2);
        assert!(constants.contains(&a));
        assert!(constants.contains(&b));
    }

    #[test]
    fn test_collect_constants_let() {
        // let x : T := v in b
        let t = Name::from_string("T");
        let v = Name::from_string("V");
        let b = Name::from_string("B");
        let let_expr = Expr::let_named(
            Name::anon(),
            Expr::from_kind(ExprKind::Const(t.clone(), LevelVec::new())),
            Expr::from_kind(ExprKind::Const(v.clone(), LevelVec::new())),
            Expr::from_kind(ExprKind::Const(b.clone(), LevelVec::new())),
            false,
        );
        let constants = let_expr.collect_constants();
        assert_eq!(constants.len(), 3);
        assert!(constants.contains(&t));
        assert!(constants.contains(&v));
        assert!(constants.contains(&b));
    }

    #[test]
    fn test_collect_constants_proj() {
        // T.proj_0(x)
        let x = Name::from_string("X");
        let proj = Expr::from_kind(ExprKind::Proj(
            Name::from_string("T"),
            0,
            Arc::new(Expr::from_kind(ExprKind::Const(x.clone(), LevelVec::new()))),
        ));
        let constants = proj.collect_constants();
        // Note: projection type name is not an Expr::from_kind(ExprKind::Const), so only X is collected
        assert_eq!(constants.len(), 1);
        assert!(constants.contains(&x));
    }

    // =========================================================================
    // Scaling tests: verify O(n) complexity of core operations
    // =========================================================================

    /// Build a wide application chain for testing:
    /// (((f a₀) a₁) a₂) ... aₙ
    fn build_wide_app(width: usize) -> Expr {
        let f = Expr::from_kind(ExprKind::Const(Name::from_string("f"), LevelVec::new()));
        let mut e = f;
        for i in 0..width {
            let arg = Expr::from_kind(ExprKind::Const(
                Name::from_string(&format!("a{i}")),
                LevelVec::new(),
            ));
            e = Expr::from_kind(ExprKind::App(Arc::new(e), Arc::new(arg)));
        }
        e
    }

    /// Build an expression with many references to the same FVar for testing.
    /// Creates: (((fvar fvar) fvar) ... fvar) with n applications
    fn build_fvar_chain(n: usize, fvar: &Expr) -> Expr {
        let mut e = fvar.clone();
        for _ in 0..n {
            e = Expr::from_kind(ExprKind::App(Arc::new(e), Arc::new(fvar.clone())));
        }
        e
    }

    /// Build a chain of App nodes with free BVar(0) references:
    /// (((BVar(0) BVar(0)) BVar(0)) ... BVar(0)) with n applications
    fn build_bvar_chain(n: usize) -> Expr {
        let bvar = Expr::from_kind(ExprKind::BVar(0));
        let mut e = bvar.clone();
        for _ in 0..n {
            e = Expr::from_kind(ExprKind::App(Arc::new(e), Arc::new(bvar.clone())));
        }
        e
    }

    /// Assert that an operation scales linearly (not quadratically).
    /// Runs `op` at three sizes [n, 2n, 4n] with 10 iterations each,
    /// checking the 4x-input ratio stays below 40x time.
    fn assert_linear_scaling(name: &str, sizes: [usize; 3], op: impl Fn(usize)) {
        use std::time::Instant;
        let mut times = Vec::new();
        for &n in &sizes {
            let start = Instant::now();
            for _ in 0..10 {
                op(n);
            }
            times.push(start.elapsed().as_nanos());
        }
        let ratio = times[2] as f64 / times[0] as f64;
        assert!(
            ratio < 40.0,
            "{name}: 4x input gave {ratio:.1}x time ({}ns, {}ns, {}ns)",
            times[0],
            times[1],
            times[2]
        );
    }

    // Scaling tests use expressions with free BVars/FVars to ensure the O(n)
    // traversal executes (expressions without free BVars short-circuit via the
    // loose_bvar_range() O(1) guard — see #1281).

    #[test]
    fn test_instantiate_scaling() {
        let _serial = crate::test_utils::serial_test_guard();
        let val = Expr::from_kind(ExprKind::Const(Name::from_string("v"), LevelVec::new()));
        assert_linear_scaling("instantiate", [500, 1000, 2000], |n| {
            let expr = build_bvar_chain(n);
            let result = expr.instantiate(&val);
            assert_ne!(result, expr);
        });
    }

    #[test]
    fn test_lift_scaling() {
        let _serial = crate::test_utils::serial_test_guard();
        assert_linear_scaling("lift", [500, 1000, 2000], |n| {
            let expr = build_bvar_chain(n);
            let result = expr.lift(5);
            assert_ne!(result, expr);
        });
    }

    #[test]
    fn test_abstract_fvar_scaling() {
        let _serial = crate::test_utils::serial_test_guard();
        let fvar_id = FVarId(42);
        let fvar = Expr::from_kind(ExprKind::FVar(fvar_id));
        assert_linear_scaling("abstract_fvar", [500, 1000, 2000], |n| {
            let expr = build_fvar_chain(n, &fvar);
            let result = expr.abstract_fvar(fvar_id);
            assert_ne!(result, expr);
        });
    }

    #[test]
    fn test_subst_fvar_scaling() {
        let _serial = crate::test_utils::serial_test_guard();
        let fvar_id = FVarId(42);
        let fvar = Expr::from_kind(ExprKind::FVar(fvar_id));
        let repl = Expr::from_kind(ExprKind::Const(Name::from_string("r"), LevelVec::new()));
        assert_linear_scaling("subst_fvar", [500, 1000, 2000], |n| {
            let expr = build_fvar_chain(n, &fvar);
            let result = expr.subst_fvar(fvar_id, &repl);
            assert_ne!(result, expr);
        });
    }

    #[test]
    fn test_wide_app_scaling() {
        let _serial = crate::test_utils::serial_test_guard();
        assert_linear_scaling("get_app_args", [500, 1000, 2000], |n| {
            let expr = build_wide_app(n);
            assert_eq!(expr.get_app_args().len(), n);
        });
    }

    #[test]
    fn test_get_app_num_args_scaling() {
        let _serial = crate::test_utils::serial_test_guard();
        assert_linear_scaling("get_app_num_args", [500, 1000, 2000], |n| {
            let expr = build_wide_app(n);
            assert_eq!(expr.get_app_num_args(), n);
        });
    }

    // =========================================================================
    // Mode-specific lift/instantiate tests (#1029)
    // Tests for SProp, Cubical, Classical, and ZFC expression variants
    // =========================================================================

    #[test]
    fn test_lift_sprop() {
        // SProp is a constant - lifting should be identity
        let e = Expr::from_kind(ExprKind::SProp);
        assert_eq!(
            e.lift(5),
            Expr::from_kind(ExprKind::SProp),
            "SProp should be unchanged by lift"
        );
    }

    #[test]
    fn test_lift_squash() {
        // Squash wraps an expression - lifting should traverse
        let inner = Expr::from_kind(ExprKind::BVar(0));
        let squash = Expr::from_kind(ExprKind::Squash(Arc::new(inner)));
        let lifted = squash.lift(3);

        match &lifted.kind {
            ExprKind::Squash(inner) => {
                assert_eq!(
                    inner.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(3)),
                    "Squash inner should be lifted"
                );
            }
            _ => panic!("Expected Squash"),
        }
    }

    #[test]
    fn test_lift_squash_composition() {
        // Test lift composition law for Squash: lift(a).lift(b) == lift(a+b)
        let inner = Expr::from_kind(ExprKind::BVar(2));
        let squash = Expr::from_kind(ExprKind::Squash(Arc::new(inner)));

        let lifted_ab = squash.clone().lift(3).lift(4);
        let lifted_sum = squash.lift(7);
        assert_eq!(lifted_ab, lifted_sum, "Squash lift composition law");
    }

    #[test]
    fn test_lift_cubical_constants() {
        // Cubical interval constants should be unchanged by lift
        assert_eq!(
            Expr::from_kind(ExprKind::CubicalInterval).lift(5),
            Expr::from_kind(ExprKind::CubicalInterval),
            "CubicalInterval unchanged"
        );
        assert_eq!(
            Expr::from_kind(ExprKind::CubicalI0).lift(5),
            Expr::from_kind(ExprKind::CubicalI0),
            "CubicalI0 unchanged"
        );
        assert_eq!(
            Expr::from_kind(ExprKind::CubicalI1).lift(5),
            Expr::from_kind(ExprKind::CubicalI1),
            "CubicalI1 unchanged"
        );
    }

    #[test]
    fn test_lift_cubical_path() {
        // CubicalPath has ty, left, right - all should be lifted
        let path = Expr::from_kind(ExprKind::CubicalPath {
            ty: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
            left: Arc::new(Expr::from_kind(ExprKind::BVar(1))),
            right: Arc::new(Expr::from_kind(ExprKind::BVar(2))),
        });
        let lifted = path.lift(5);

        match &lifted.kind {
            ExprKind::CubicalPath { ty, left, right } => {
                assert_eq!(
                    ty.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(5)),
                    "CubicalPath ty lifted"
                );
                assert_eq!(
                    left.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(6)),
                    "CubicalPath left lifted"
                );
                assert_eq!(
                    right.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(7)),
                    "CubicalPath right lifted"
                );
            }
            _ => panic!("Expected CubicalPath"),
        }
    }

    #[test]
    fn test_lift_cubical_path_composition() {
        // Test lift composition law for CubicalPath
        let path = Expr::from_kind(ExprKind::CubicalPath {
            ty: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
            left: Arc::new(Expr::from_kind(ExprKind::BVar(1))),
            right: Arc::new(Expr::from_kind(ExprKind::BVar(2))),
        });

        let lifted_ab = path.clone().lift(2).lift(3);
        let lifted_sum = path.lift(5);
        assert_eq!(lifted_ab, lifted_sum, "CubicalPath lift composition law");
    }

    #[test]
    fn test_lift_cubical_path_lam() {
        // CubicalPathLam has a body that binds - start should increment
        let path_lam = Expr::from_kind(ExprKind::CubicalPathLam {
            body: Arc::new(Expr::from_kind(ExprKind::BVar(0))), // bound by the path lambda
        });
        let lifted = path_lam.lift(5);

        match &lifted.kind {
            ExprKind::CubicalPathLam { body } => {
                // BVar(0) is bound (< 1), so not lifted
                assert_eq!(
                    body.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(0)),
                    "CubicalPathLam bound BVar not lifted"
                );
            }
            _ => panic!("Expected CubicalPathLam"),
        }

        // Now with BVar(1) which is free
        let path_lam = Expr::from_kind(ExprKind::CubicalPathLam {
            body: Arc::new(Expr::from_kind(ExprKind::BVar(1))),
        });
        let lifted = path_lam.lift(5);

        match &lifted.kind {
            ExprKind::CubicalPathLam { body } => {
                // BVar(1) >= 1, so lifted to BVar(6)
                assert_eq!(
                    body.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(6)),
                    "CubicalPathLam free BVar lifted"
                );
            }
            _ => panic!("Expected CubicalPathLam"),
        }
    }

    #[test]
    fn test_lift_cubical_path_app() {
        // CubicalPathApp has path and arg - both should be lifted
        let path_app = Expr::from_kind(ExprKind::CubicalPathApp {
            path: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
            arg: Arc::new(Expr::from_kind(ExprKind::BVar(1))),
        });
        let lifted = path_app.lift(3);

        match &lifted.kind {
            ExprKind::CubicalPathApp { path, arg } => {
                assert_eq!(
                    path.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(3)),
                    "CubicalPathApp path lifted"
                );
                assert_eq!(
                    arg.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(4)),
                    "CubicalPathApp arg lifted"
                );
            }
            _ => panic!("Expected CubicalPathApp"),
        }
    }

    #[test]
    fn test_lift_cubical_hcomp() {
        // CubicalHComp has ty, phi, u, base - all should be lifted
        let hcomp = Expr::from_kind(ExprKind::CubicalHComp {
            ty: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
            phi: Arc::new(Expr::from_kind(ExprKind::BVar(1))),
            u: Arc::new(Expr::from_kind(ExprKind::BVar(2))),
            base: Arc::new(Expr::from_kind(ExprKind::BVar(3))),
        });
        let lifted = hcomp.lift(4);

        match &lifted.kind {
            ExprKind::CubicalHComp { ty, phi, u, base } => {
                assert_eq!(
                    ty.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(4)),
                    "CubicalHComp ty lifted"
                );
                assert_eq!(
                    phi.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(5)),
                    "CubicalHComp phi lifted"
                );
                assert_eq!(
                    u.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(6)),
                    "CubicalHComp u lifted"
                );
                assert_eq!(
                    base.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(7)),
                    "CubicalHComp base lifted"
                );
            }
            _ => panic!("Expected CubicalHComp"),
        }
    }

    #[test]
    fn test_lift_cubical_transp() {
        // CubicalTransp has ty, phi, base - all should be lifted
        let transp = Expr::from_kind(ExprKind::CubicalTransp {
            ty: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
            phi: Arc::new(Expr::from_kind(ExprKind::BVar(1))),
            base: Arc::new(Expr::from_kind(ExprKind::BVar(2))),
        });
        let lifted = transp.lift(3);

        match &lifted.kind {
            ExprKind::CubicalTransp { ty, phi, base } => {
                assert_eq!(
                    ty.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(3)),
                    "CubicalTransp ty lifted"
                );
                assert_eq!(
                    phi.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(4)),
                    "CubicalTransp phi lifted"
                );
                assert_eq!(
                    base.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(5)),
                    "CubicalTransp base lifted"
                );
            }
            _ => panic!("Expected CubicalTransp"),
        }
    }

    #[test]
    fn test_lift_zfc_set() {
        // ZFCSet wraps ZFCSetExpr - test various variants
        let empty = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty));
        assert_eq!(empty.lift(5), empty, "ZFCSet Empty unchanged by lift");

        let infinity = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Infinity));
        assert_eq!(
            infinity.lift(5),
            infinity,
            "ZFCSet Infinity unchanged by lift"
        );

        // Singleton with BVar
        let singleton = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Singleton(Arc::new(
            Expr::from_kind(ExprKind::BVar(0)),
        ))));
        let lifted = singleton.lift(3);
        match &lifted.kind {
            ExprKind::ZFCSet(ZFCSetExpr::Singleton(inner)) => {
                assert_eq!(
                    inner.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(3)),
                    "ZFCSet Singleton inner lifted"
                );
            }
            _ => panic!("Expected ZFCSet Singleton"),
        }
    }

    #[test]
    fn test_lift_zfc_mem() {
        // ZFCMem has element and set - both should be lifted
        let mem = Expr::from_kind(ExprKind::ZFCMem {
            element: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
            set: Arc::new(Expr::from_kind(ExprKind::BVar(1))),
        });
        let lifted = mem.lift(2);

        match &lifted.kind {
            ExprKind::ZFCMem { element, set } => {
                assert_eq!(
                    element.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(2)),
                    "ZFCMem element lifted"
                );
                assert_eq!(
                    set.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(3)),
                    "ZFCMem set lifted"
                );
            }
            _ => panic!("Expected ZFCMem"),
        }
    }

    #[test]
    fn test_lift_zfc_comprehension() {
        // ZFCComprehension has domain and pred (which binds)
        let comp = Expr::from_kind(ExprKind::ZFCComprehension {
            domain: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
            pred: Arc::new(Expr::from_kind(ExprKind::BVar(0))), // bound by comprehension
        });
        let lifted = comp.lift(3);

        match &lifted.kind {
            ExprKind::ZFCComprehension { domain, pred } => {
                // domain is lifted at current start
                assert_eq!(
                    domain.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(3)),
                    "ZFCComprehension domain lifted"
                );
                // pred is under binder, BVar(0) < 1, so not lifted
                assert_eq!(
                    pred.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(0)),
                    "ZFCComprehension bound pred not lifted"
                );
            }
            _ => panic!("Expected ZFCComprehension"),
        }

        // Test with free BVar in pred
        let comp = Expr::from_kind(ExprKind::ZFCComprehension {
            domain: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
            pred: Arc::new(Expr::from_kind(ExprKind::BVar(1))), // free, refers outside
        });
        let lifted = comp.lift(3);

        match &lifted.kind {
            ExprKind::ZFCComprehension { domain, pred } => {
                assert_eq!(domain.as_ref(), &Expr::from_kind(ExprKind::BVar(3)));
                // BVar(1) >= 1, so lifted to BVar(4)
                assert_eq!(
                    pred.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(4)),
                    "ZFCComprehension free pred lifted"
                );
            }
            _ => panic!("Expected ZFCComprehension"),
        }
    }

    #[test]
    fn test_lift_zfc_set_additional() {
        // Test remaining ZFCSetExpr variants: Pair, Union, PowerSet, Separation, Replacement, Choice

        // Pair with two BVars
        let pair = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Pair(
            Arc::new(Expr::from_kind(ExprKind::BVar(0))),
            Arc::new(Expr::from_kind(ExprKind::BVar(1))),
        )));
        let lifted = pair.lift(4);
        match &lifted.kind {
            ExprKind::ZFCSet(ZFCSetExpr::Pair(a, b)) => {
                assert_eq!(
                    a.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(4)),
                    "Pair first element lifted"
                );
                assert_eq!(
                    b.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(5)),
                    "Pair second element lifted"
                );
            }
            _ => panic!("Expected ZFCSet Pair"),
        }

        // Union wrapping a set
        let union = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Union(Arc::new(
            Expr::from_kind(ExprKind::BVar(2)),
        ))));
        let lifted = union.lift(3);
        match &lifted.kind {
            ExprKind::ZFCSet(ZFCSetExpr::Union(inner)) => {
                assert_eq!(
                    inner.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(5)),
                    "Union inner lifted"
                );
            }
            _ => panic!("Expected ZFCSet Union"),
        }

        // PowerSet wrapping a set
        let powerset = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::PowerSet(Arc::new(
            Expr::from_kind(ExprKind::BVar(1)),
        ))));
        let lifted = powerset.lift(2);
        match &lifted.kind {
            ExprKind::ZFCSet(ZFCSetExpr::PowerSet(inner)) => {
                assert_eq!(
                    inner.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(3)),
                    "PowerSet inner lifted"
                );
            }
            _ => panic!("Expected ZFCSet PowerSet"),
        }

        // Separation: set and pred, where pred binds
        let sep = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Separation {
            set: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
            pred: Arc::new(Expr::from_kind(ExprKind::BVar(0))), // bound by separation
        }));
        let lifted = sep.lift(3);
        match &lifted.kind {
            ExprKind::ZFCSet(ZFCSetExpr::Separation { set, pred }) => {
                assert_eq!(
                    set.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(3)),
                    "Separation set lifted"
                );
                // pred BVar(0) is bound (< 1), not lifted
                assert_eq!(
                    pred.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(0)),
                    "Separation bound pred not lifted"
                );
            }
            _ => panic!("Expected ZFCSet Separation"),
        }

        // Separation with free BVar in pred
        let sep = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Separation {
            set: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
            pred: Arc::new(Expr::from_kind(ExprKind::BVar(1))), // free, refers outside
        }));
        let lifted = sep.lift(3);
        match &lifted.kind {
            ExprKind::ZFCSet(ZFCSetExpr::Separation { set, pred }) => {
                assert_eq!(set.as_ref(), &Expr::from_kind(ExprKind::BVar(3)));
                // BVar(1) >= 1, so lifted to BVar(4)
                assert_eq!(
                    pred.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(4)),
                    "Separation free pred lifted"
                );
            }
            _ => panic!("Expected ZFCSet Separation"),
        }

        // Replacement: set and func, where func binds
        let repl = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Replacement {
            set: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
            func: Arc::new(Expr::from_kind(ExprKind::BVar(0))), // bound by replacement
        }));
        let lifted = repl.lift(2);
        match &lifted.kind {
            ExprKind::ZFCSet(ZFCSetExpr::Replacement { set, func }) => {
                assert_eq!(
                    set.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(2)),
                    "Replacement set lifted"
                );
                // func BVar(0) is bound (< 1), not lifted
                assert_eq!(
                    func.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(0)),
                    "Replacement bound func not lifted"
                );
            }
            _ => panic!("Expected ZFCSet Replacement"),
        }

        // Replacement with free BVar in func
        let repl = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Replacement {
            set: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
            func: Arc::new(Expr::from_kind(ExprKind::BVar(2))), // free (2 >= 1)
        }));
        let lifted = repl.lift(2);
        match &lifted.kind {
            ExprKind::ZFCSet(ZFCSetExpr::Replacement { set, func }) => {
                assert_eq!(set.as_ref(), &Expr::from_kind(ExprKind::BVar(2)));
                // BVar(2) >= 1, so lifted to BVar(4)
                assert_eq!(
                    func.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(4)),
                    "Replacement free func lifted"
                );
            }
            _ => panic!("Expected ZFCSet Replacement"),
        }

        // Choice wrapping an expression
        let choice = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Choice(Arc::new(
            Expr::from_kind(ExprKind::BVar(3)),
        ))));
        let lifted = choice.lift(1);
        match &lifted.kind {
            ExprKind::ZFCSet(ZFCSetExpr::Choice(inner)) => {
                assert_eq!(
                    inner.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(4)),
                    "Choice inner lifted"
                );
            }
            _ => panic!("Expected ZFCSet Choice"),
        }
    }

    #[test]
    fn test_lift_composition_binding_variants() {
        // Test lift composition law for variants that have binding predicates
        // This ensures lift(a).lift(b) == lift(a+b) even with bound variables

        // CubicalPathLam composition with free variable in body
        let path_lam = Expr::from_kind(ExprKind::CubicalPathLam {
            body: Arc::new(Expr::from_kind(ExprKind::BVar(2))), // free (2 >= 1)
        });
        let lifted_ab = path_lam.clone().lift(1).lift(2);
        let lifted_sum = path_lam.lift(3);
        assert_eq!(
            lifted_ab, lifted_sum,
            "CubicalPathLam lift composition with free var"
        );

        // ZFCComprehension composition with free variable in pred
        let comp = Expr::from_kind(ExprKind::ZFCComprehension {
            domain: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
            pred: Arc::new(Expr::from_kind(ExprKind::BVar(2))), // free (2 >= 1)
        });
        let lifted_ab = comp.clone().lift(2).lift(1);
        let lifted_sum = comp.lift(3);
        assert_eq!(
            lifted_ab, lifted_sum,
            "ZFCComprehension lift composition with free var"
        );

        // ZFCSet Separation composition
        let sep = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Separation {
            set: Arc::new(Expr::from_kind(ExprKind::BVar(1))),
            pred: Arc::new(Expr::from_kind(ExprKind::BVar(3))), // free (3 >= 1)
        }));
        let lifted_ab = sep.clone().lift(2).lift(2);
        let lifted_sum = sep.lift(4);
        assert_eq!(
            lifted_ab, lifted_sum,
            "ZFCSet Separation lift composition with free var"
        );

        // ZFCSet Replacement composition
        let repl = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Replacement {
            set: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
            func: Arc::new(Expr::from_kind(ExprKind::BVar(1))), // free (1 >= 1)
        }));
        let lifted_ab = repl.clone().lift(3).lift(1);
        let lifted_sum = repl.lift(4);
        assert_eq!(
            lifted_ab, lifted_sum,
            "ZFCSet Replacement lift composition with free var"
        );
    }

    #[test]
    fn test_instantiate_mode_specific() {
        // Test instantiate for mode-specific variants

        let val = Expr::type_();

        // SProp is closed - instantiate should return same
        let sprop = Expr::from_kind(ExprKind::SProp);
        assert_eq!(
            sprop.instantiate(&val),
            Expr::from_kind(ExprKind::SProp),
            "SProp unchanged"
        );

        // Squash with BVar(0) should be substituted
        let squash = Expr::from_kind(ExprKind::Squash(Arc::new(Expr::from_kind(ExprKind::BVar(
            0,
        )))));
        let inst = squash.instantiate(&val);
        match &inst.kind {
            ExprKind::Squash(inner) => {
                assert_eq!(inner.as_ref(), &Expr::type_(), "Squash BVar(0) substituted");
            }
            _ => panic!("Expected Squash"),
        }

        // CubicalPath with BVars
        let path = Expr::from_kind(ExprKind::CubicalPath {
            ty: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
            left: Arc::new(Expr::prop()),
            right: Arc::new(Expr::from_kind(ExprKind::BVar(1))), // becomes BVar(0) after instantiate
        });
        let inst = path.instantiate(&val);
        match &inst.kind {
            ExprKind::CubicalPath { ty, left, right } => {
                assert_eq!(ty.as_ref(), &Expr::type_(), "CubicalPath ty substituted");
                assert_eq!(left.as_ref(), &Expr::prop(), "CubicalPath left unchanged");
                assert_eq!(
                    right.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(0)),
                    "CubicalPath right decremented"
                );
            }
            _ => panic!("Expected CubicalPath"),
        }

        // ZFCMem with BVars
        let mem = Expr::from_kind(ExprKind::ZFCMem {
            element: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
            set: Arc::new(Expr::from_kind(ExprKind::BVar(1))),
        });
        let inst = mem.instantiate(&val);
        match &inst.kind {
            ExprKind::ZFCMem { element, set } => {
                assert_eq!(
                    element.as_ref(),
                    &Expr::type_(),
                    "ZFCMem element substituted"
                );
                assert_eq!(
                    set.as_ref(),
                    &Expr::from_kind(ExprKind::BVar(0)),
                    "ZFCMem set decremented"
                );
            }
            _ => panic!("Expected ZFCMem"),
        }
    }

    #[test]
    fn test_composition_mode_specific() {
        // Test lift composition law for mode-specific variants
        // lift(a).lift(b) == lift(a + b)

        // ZFC membership
        let mem = Expr::from_kind(ExprKind::ZFCMem {
            element: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
            set: Arc::new(Expr::from_kind(ExprKind::BVar(1))),
        });
        let lifted_ab = mem.clone().lift(3).lift(2);
        let lifted_sum = mem.lift(5);
        assert_eq!(lifted_ab, lifted_sum, "ZFCMem lift composition");

        // Cubical hcomp
        let hcomp = Expr::from_kind(ExprKind::CubicalHComp {
            ty: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
            phi: Arc::new(Expr::from_kind(ExprKind::BVar(1))),
            u: Arc::new(Expr::from_kind(ExprKind::BVar(2))),
            base: Arc::new(Expr::from_kind(ExprKind::BVar(3))),
        });
        let lifted_ab = hcomp.clone().lift(1).lift(4);
        let lifted_sum = hcomp.lift(5);
        assert_eq!(lifted_ab, lifted_sum, "CubicalHComp lift composition");
    }

    // =========================================================================
    // Value preservation tests (pre-#1326 baseline)
    // =========================================================================
    // These tests verify VALUE EQUALITY is preserved when substitution encounters
    // unchanged sub-expressions. They do NOT yet test SHARING (Arc::ptr_eq).
    //
    // Currently substitution always allocates new Arcs even when the expression
    // is unchanged. When #1326 adds Option<Expr> return semantics, ADD Arc::ptr_eq
    // assertions to verify sharing is preserved (Arc identity, not just equality).

    #[test]
    fn test_instantiate_preserves_value_on_closed_expr() {
        // A closed expression (no loose BVars) should be unchanged after instantiate.
        // Value must be preserved even though sharing (Arc identity) currently is not.
        let closed = Expr::const_str("Nat");
        let val = Expr::fvar(FVarId(99));
        let result = closed.instantiate(&val);
        assert_eq!(
            result, closed,
            "Closed expr should be unchanged by instantiate"
        );
    }

    #[test]
    fn test_instantiate_preserves_value_on_nested_closed() {
        // Nested closed expression: App(Nat, Nat.zero) has no loose BVars
        let nat = Arc::new(Expr::const_str("Nat"));
        let zero = Arc::new(Expr::const_str("Nat.zero"));
        let app = Expr::from_kind(ExprKind::App(nat, zero));
        let val = Expr::fvar(FVarId(100));
        let result = app.instantiate(&val);
        assert_eq!(
            result, app,
            "Nested closed expr should be unchanged by instantiate"
        );
    }

    #[test]
    fn test_lift_preserves_value_on_closed_expr() {
        // A closed expression (no loose BVars) should be unchanged after lift.
        let closed = Expr::const_str("Bool");
        let result = closed.lift(5);
        assert_eq!(result, closed, "Closed expr should be unchanged by lift");
    }

    #[test]
    fn test_subst_fvar_preserves_value_when_fvar_absent() {
        // Substituting for an FVar that doesn't appear should preserve value.
        let expr = Expr::from_kind(ExprKind::App(
            Arc::new(Expr::const_str("Nat.succ")),
            Arc::new(Expr::const_str("Nat.zero")),
        ));
        let replacement = Expr::const_str("Bool");
        let result = expr.subst_fvar(FVarId(999), &replacement);
        assert_eq!(
            result, expr,
            "Expr without target FVar should be unchanged by subst_fvar"
        );
    }

    #[test]
    fn test_abstract_fvar_preserves_value_when_fvar_absent() {
        // Abstracting over an FVar that doesn't appear in a fully-closed expression
        // (no BVars, no matching FVars) should preserve value.
        // Note: abstract_fvar shifts BVar indices >= depth, so we use only Const nodes
        // to test the "no change" case cleanly.
        let expr = Expr::from_kind(ExprKind::App(
            Arc::new(Expr::const_str("Nat.add")),
            Arc::new(Expr::const_str("Nat.zero")),
        ));
        let result = expr.abstract_fvar(FVarId(888));
        assert_eq!(
            result, expr,
            "Expr without target FVar should be unchanged by abstract_fvar"
        );
    }

    #[test]
    fn test_instantiate_level_params_preserves_value_when_no_params() {
        // An expression with no level params should be unchanged after substitution.
        let expr = Expr::from_kind(ExprKind::App(
            Arc::new(Expr::from_kind(ExprKind::BVar(0))),
            Arc::new(Expr::from_kind(ExprKind::BVar(1))),
        ));
        let subst = vec![(Name::from_string("u"), Level::zero())];
        let result = expr.instantiate_level_params(&subst);
        assert_eq!(
            result, expr,
            "Expr with no level params should be unchanged"
        );
    }

    // =========================================================================
    // Sharing preservation regression tests (pre-#1326 regression baseline)
    // =========================================================================
    // These tests target the specific case where substitution traverses a
    // compound expression whose leaves are ALL unchanged. Post-#1326, the
    // substitution should return the SAME Arc (sharing preserved). Currently
    // it always allocates new Arcs, so we test value equality only and mark
    // Arc::ptr_eq checks as TODO.
    //
    // Key scenarios tested:
    // 1. instantiate on App/Lam/Pi where all children are closed (no loose BVars)
    // 2. lift on closed subtrees within compound expressions
    // 3. subst_fvar on compound expressions where FVar is absent from all children
    // 4. abstract_fvar on compound expressions where FVar and BVars are absent

    #[test]
    fn test_sharing_instantiate_closed_app_children() {
        // App(Const("f"), Const("a")) — both children are closed leaves.
        // instantiate should return an equal expression (and post-#1326, same Arc).
        let f = Arc::new(Expr::const_str("f"));
        let a = Arc::new(Expr::const_str("a"));
        let app = Expr::from_kind(ExprKind::App(f.clone(), a.clone()));
        let val = Expr::fvar(FVarId(42));
        let result = app.instantiate(&val);
        assert_eq!(
            result, app,
            "instantiate on App with closed children should preserve value"
        );
        // Phase 2b (#1326): sharing-preserving substitution returns None for closed
        // subtrees, so Arc identity is preserved through the clone path.
        if let ExprKind::App(rf, ra) = &result.kind {
            assert!(
                Arc::ptr_eq(rf, &f),
                "function child should share Arc identity"
            );
            assert!(
                Arc::ptr_eq(ra, &a),
                "argument child should share Arc identity"
            );
        } else {
            panic!("expected App");
        }
    }

    #[test]
    fn test_sharing_instantiate_closed_lam() {
        // Lam(Default, Const("A"), Const("b")) — body is closed (no BVar(0) reference).
        // The body Const("b") is not affected by instantiate at all.
        let ty = Arc::new(Expr::const_str("A"));
        let body = Arc::new(Expr::const_str("b"));
        let lam = Expr::from_kind(ExprKind::Lam(
            BinderInfo::Default.into(),
            ty.clone(),
            body.clone(),
        ));
        let val = Expr::fvar(FVarId(99));
        let result = lam.instantiate(&val);
        assert_eq!(
            result, lam,
            "instantiate on Lam with closed body should preserve value"
        );
        if let ExprKind::Lam(_, rty, rbody) = &result.kind {
            assert!(Arc::ptr_eq(rty, &ty), "type should share Arc identity");
            assert!(Arc::ptr_eq(rbody, &body), "body should share Arc identity");
        } else {
            panic!("expected Lam");
        }
    }

    #[test]
    fn test_sharing_instantiate_closed_pi() {
        // Pi(Default, Const("A"), Const("B")) — both domain and codomain are closed.
        let domain = Arc::new(Expr::const_str("A"));
        let codomain = Arc::new(Expr::const_str("B"));
        let pi = Expr::from_kind(ExprKind::Pi(
            BinderInfo::Default.into(),
            domain.clone(),
            codomain.clone(),
        ));
        let val = Expr::from_kind(ExprKind::BVar(5)); // won't match depth 0
        let result = pi.instantiate(&val);
        assert_eq!(
            result, pi,
            "instantiate on Pi with closed children should preserve value"
        );
        if let ExprKind::Pi(_, rd, rc) = &result.kind {
            assert!(Arc::ptr_eq(rd, &domain), "domain should share Arc identity");
            assert!(
                Arc::ptr_eq(rc, &codomain),
                "codomain should share Arc identity"
            );
        } else {
            panic!("expected Pi");
        }
    }

    #[test]
    fn test_sharing_lift_closed_app_children() {
        // App(Const("f"), Const("a")) — lift(n) on closed expression should be identity.
        let f = Arc::new(Expr::const_str("f"));
        let a = Arc::new(Expr::const_str("a"));
        let app = Expr::from_kind(ExprKind::App(f.clone(), a.clone()));
        let result = app.lift(10);
        assert_eq!(
            result, app,
            "lift on App with closed children should preserve value"
        );
        if let ExprKind::App(rf, ra) = &result.kind {
            assert!(
                Arc::ptr_eq(rf, &f),
                "lift should preserve function Arc identity"
            );
            assert!(
                Arc::ptr_eq(ra, &a),
                "lift should preserve argument Arc identity"
            );
        } else {
            panic!("expected App");
        }
    }

    #[test]
    fn test_sharing_subst_fvar_absent_from_app() {
        // App(Const("f"), Const("a")) — subst_fvar for a non-existent FVar.
        let f = Arc::new(Expr::const_str("f"));
        let a = Arc::new(Expr::const_str("a"));
        let app = Expr::from_kind(ExprKind::App(f.clone(), a.clone()));
        let replacement = Expr::const_str("replacement");
        let result = app.subst_fvar(FVarId(777), &replacement);
        assert_eq!(
            result, app,
            "subst_fvar for absent FVar should preserve value"
        );
        if let ExprKind::App(rf, ra) = &result.kind {
            assert!(Arc::ptr_eq(rf, &f), "function should share Arc identity");
            assert!(Arc::ptr_eq(ra, &a), "argument should share Arc identity");
        } else {
            panic!("expected App");
        }
    }

    #[test]
    fn test_sharing_subst_fvar_absent_nested() {
        // App(Lam(_, Const("A"), Const("B")), Const("c"))
        // subst_fvar for non-existent FVar — entire tree should be unchanged.
        let inner_ty = Arc::new(Expr::const_str("A"));
        let inner_body = Arc::new(Expr::const_str("B"));
        let lam = Arc::new(Expr::from_kind(ExprKind::Lam(
            BinderInfo::Default.into(),
            inner_ty.clone(),
            inner_body.clone(),
        )));
        let arg = Arc::new(Expr::const_str("c"));
        let app = Expr::from_kind(ExprKind::App(lam.clone(), arg.clone()));
        let replacement = Expr::const_str("X");
        let result = app.subst_fvar(FVarId(888), &replacement);
        assert_eq!(
            result, app,
            "nested subst_fvar for absent FVar should preserve value"
        );
        if let ExprKind::App(rf, ra) = &result.kind {
            assert!(
                Arc::ptr_eq(rf, &lam),
                "function subtree should share Arc identity"
            );
            assert!(
                Arc::ptr_eq(ra, &arg),
                "argument subtree should share Arc identity"
            );
        } else {
            panic!("expected App");
        }
    }

    #[test]
    fn test_sharing_abstract_fvar_absent_from_const_tree() {
        // App(Const("f"), Const("a")) — abstract_fvar for absent FVar on a tree
        // with no BVars (so no BVar shifting occurs either).
        let f = Arc::new(Expr::const_str("f"));
        let a = Arc::new(Expr::const_str("a"));
        let app = Expr::from_kind(ExprKind::App(f.clone(), a.clone()));
        let result = app.abstract_fvar(FVarId(999));
        assert_eq!(
            result, app,
            "abstract_fvar for absent FVar on const-only tree should preserve value"
        );
        if let ExprKind::App(rf, ra) = &result.kind {
            assert!(Arc::ptr_eq(rf, &f), "function should share Arc identity");
            assert!(Arc::ptr_eq(ra, &a), "argument should share Arc identity");
        } else {
            panic!("expected App");
        }
    }

    #[test]
    fn test_sharing_instantiate_level_params_no_match() {
        // App(BVar(0), BVar(1)) — no level params anywhere.
        // instantiate_level_params with non-matching param should be identity.
        let f = Arc::new(Expr::from_kind(ExprKind::BVar(0)));
        let a = Arc::new(Expr::from_kind(ExprKind::BVar(1)));
        let app = Expr::from_kind(ExprKind::App(f.clone(), a.clone()));
        let subst = vec![(Name::from_string("nonexistent"), Level::zero())];
        let result = app.instantiate_level_params(&subst);
        assert_eq!(
            result, app,
            "instantiate_level_params with no matching params should preserve value"
        );
        if let ExprKind::App(rf, ra) = &result.kind {
            assert!(Arc::ptr_eq(rf, &f), "function should share Arc identity");
            assert!(Arc::ptr_eq(ra, &a), "argument should share Arc identity");
        } else {
            panic!("expected App");
        }
    }

    // ═════════════════════════════════════════════════════════════════════
    // ExprMeta tests (#1326 Phase 1)
    // ═════════════════════════════════════════════════════════════════════

    #[test]
    fn test_expr_meta_pack_zero() {
        let m = ExprMeta::pack(0, 0, 0, false, false, false, false);
        assert_eq!(m.hash(), 0);
        assert_eq!(m.approx_depth(), 0);
        assert!(!m.has_fvar());
        assert!(!m.has_expr_mvar());
        assert!(!m.has_level_mvar());
        assert!(!m.has_level_param());
        assert_eq!(m.loose_bvar_range(), 0);
        assert!(!m.has_loose_bvars());
        assert_eq!(m.raw(), 0);
        assert_eq!(m, ExprMeta::ZERO);
    }

    #[test]
    fn test_expr_meta_pack_hash_only() {
        let m = ExprMeta::pack(0xDEAD_BEEF, 0, 0, false, false, false, false);
        assert_eq!(m.hash(), 0xDEAD_BEEF);
        assert_eq!(m.approx_depth(), 0);
        assert_eq!(m.loose_bvar_range(), 0);
    }

    #[test]
    fn test_expr_meta_pack_all_flags() {
        let m = ExprMeta::pack(42, 5, 10, true, true, true, true);
        assert_eq!(m.hash(), 42);
        assert_eq!(m.approx_depth(), 10);
        assert!(m.has_fvar());
        assert!(m.has_expr_mvar());
        assert!(m.has_level_mvar());
        assert!(m.has_level_param());
        assert_eq!(m.loose_bvar_range(), 5);
        assert!(m.has_loose_bvars());
    }

    #[test]
    fn test_expr_meta_depth_saturates() {
        let m = ExprMeta::pack(0, 0, 300, false, false, false, false);
        assert_eq!(m.approx_depth(), 255);
    }

    #[test]
    fn test_expr_meta_bvar_range_panics_on_overflow() {
        // Match Lean 4: panic on loose_bvar_range > MAX_BVAR_RANGE (1,048,575).
        // Previously saturated, but saturation caused incorrect O(1) guard behavior (#1363).
        let result = std::panic::catch_unwind(|| {
            ExprMeta::pack(0, 2_000_000, 0, false, false, false, false)
        });
        let err = result.expect_err("expected panic for too many bound variables");
        let msg = err
            .downcast_ref::<String>()
            .map(|s| s.as_str())
            .unwrap_or("");
        assert!(
            msg.contains("too many bound variables"),
            "expected 'too many bound variables' panic, got: {msg}"
        );
    }

    #[test]
    fn test_expr_meta_individual_flags() {
        let fvar = ExprMeta::pack(0, 0, 0, true, false, false, false);
        assert!(fvar.has_fvar());
        assert!(!fvar.has_expr_mvar());

        let emvar = ExprMeta::pack(0, 0, 0, false, true, false, false);
        assert!(!emvar.has_fvar());
        assert!(emvar.has_expr_mvar());
        assert!(!emvar.has_level_mvar());

        let lmvar = ExprMeta::pack(0, 0, 0, false, false, true, false);
        assert!(lmvar.has_level_mvar());
        assert!(!lmvar.has_level_param());

        let lparam = ExprMeta::pack(0, 0, 0, false, false, false, true);
        assert!(lparam.has_level_param());
        assert!(!lparam.has_fvar());
    }

    #[test]
    fn test_expr_meta_roundtrip_max_values() {
        let m = ExprMeta::pack(u32::MAX, 1_048_575, 255, true, true, true, true);
        assert_eq!(m.hash(), u32::MAX);
        assert_eq!(m.approx_depth(), 255);
        assert_eq!(m.loose_bvar_range(), 1_048_575);
        assert!(m.has_fvar());
        assert!(m.has_expr_mvar());
        assert!(m.has_level_mvar());
        assert!(m.has_level_param());
    }

    #[test]
    fn test_mix_hash_deterministic() {
        let h1 = mix_hash(0, 0);
        let h2 = mix_hash(0, 0);
        assert_eq!(h1, h2);
    }

    #[test]
    fn test_mix_hash_different_inputs() {
        let h1 = mix_hash(0, 1);
        let h2 = mix_hash(0, 2);
        assert_ne!(h1, h2);
    }

    #[test]
    fn test_mix_hash_order_matters() {
        let h1 = mix_hash(1, 2);
        let h2 = mix_hash(2, 1);
        assert_ne!(h1, h2);
    }

    #[test]
    fn test_mk_app_meta_depth_increment() {
        let leaf = ExprMeta::pack(1, 0, 0, false, false, false, false);
        let app = ExprMeta::mk_app_meta(leaf, leaf);
        assert_eq!(app.approx_depth(), 1);
    }

    #[test]
    fn test_mk_app_meta_flags_or() {
        let f = ExprMeta::pack(0, 0, 0, true, false, false, false);
        let a = ExprMeta::pack(0, 0, 0, false, true, false, false);
        let app = ExprMeta::mk_app_meta(f, a);
        assert!(app.has_fvar());
        assert!(app.has_expr_mvar());
        assert!(!app.has_level_mvar());
    }

    #[test]
    fn test_mk_app_meta_bvar_range_max() {
        let f = ExprMeta::pack(0, 3, 0, false, false, false, false);
        let a = ExprMeta::pack(0, 5, 0, false, false, false, false);
        let app = ExprMeta::mk_app_meta(f, a);
        assert_eq!(app.loose_bvar_range(), 5);
    }

    #[test]
    fn test_mk_binder_meta_body_range_decrement() {
        let ty = ExprMeta::pack(0, 0, 0, false, false, false, false);
        let body = ExprMeta::pack(0, 3, 0, false, false, false, false);
        let binder = ExprMeta::mk_binder_meta(ty, body, 0);
        assert_eq!(binder.loose_bvar_range(), 2);
    }

    #[test]
    fn test_mk_binder_meta_body_range_zero_saturates() {
        let ty = ExprMeta::pack(0, 0, 0, false, false, false, false);
        let body = ExprMeta::pack(0, 0, 0, false, false, false, false);
        let binder = ExprMeta::mk_binder_meta(ty, body, 0);
        assert_eq!(binder.loose_bvar_range(), 0);
    }

    #[test]
    fn test_mk_binder_meta_body_range_one_becomes_zero() {
        let ty = ExprMeta::ZERO;
        let body = ExprMeta::pack(0, 1, 0, false, false, false, false);
        let binder = ExprMeta::mk_binder_meta(ty, body, 0);
        assert_eq!(binder.loose_bvar_range(), 0);
        assert!(!binder.has_loose_bvars());
    }

    #[test]
    fn test_mk_let_meta_body_range_decrement() {
        let ty = ExprMeta::ZERO;
        let val = ExprMeta::ZERO;
        let body = ExprMeta::pack(0, 5, 0, false, false, false, false);
        let let_meta = ExprMeta::mk_let_meta(ty, val, body);
        assert_eq!(let_meta.loose_bvar_range(), 4);
    }

    #[test]
    fn test_compute_meta_bvar() {
        let e = Expr::from_kind(ExprKind::BVar(0));
        let m = e.compute_meta();
        assert_eq!(m.loose_bvar_range(), 1);
        assert!(m.has_loose_bvars());
        assert!(!m.has_fvar());
    }

    #[test]
    fn test_compute_meta_bvar_high() {
        let e = Expr::from_kind(ExprKind::BVar(100));
        let m = e.compute_meta();
        assert_eq!(m.loose_bvar_range(), 101);
    }

    #[test]
    fn test_compute_meta_fvar() {
        let e = Expr::from_kind(ExprKind::FVar(FVarId(42)));
        let m = e.compute_meta();
        assert!(m.has_fvar());
        assert!(!m.has_loose_bvars());
    }

    #[test]
    fn test_compute_meta_sort_with_param() {
        let e = Expr::from_kind(ExprKind::Sort(Level::param(Name::from_string("u"))));
        let m = e.compute_meta();
        assert!(m.has_level_param());
        assert!(!m.has_fvar());
    }

    #[test]
    fn test_compute_meta_sort_no_param() {
        let e = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let m = e.compute_meta();
        assert!(!m.has_level_param());
    }

    #[test]
    fn test_compute_meta_const_with_level_params() {
        let e = Expr::const_(
            Name::from_string("foo"),
            vec![Level::param(Name::from_string("u"))],
        );
        let m = e.compute_meta();
        assert!(m.has_level_param());
    }

    #[test]
    fn test_compute_meta_const_no_params() {
        let e = Expr::const_(Name::from_string("foo"), vec![]);
        let m = e.compute_meta();
        assert!(!m.has_level_param());
        assert!(!m.has_fvar());
    }

    #[test]
    fn test_compute_meta_app_propagates_flags() {
        let f = Expr::const_(Name::from_string("f"), vec![]);
        let a = Expr::from_kind(ExprKind::FVar(FVarId(0)));
        let app = Expr::app(f, a);
        let m = app.compute_meta();
        assert!(m.has_fvar());
        assert_eq!(m.approx_depth(), 1);
    }

    #[test]
    fn test_compute_meta_lam_closes_bvar() {
        // λ x : A => x    (body = BVar(0))
        let ty = Expr::const_(Name::from_string("A"), vec![]);
        let body = Expr::from_kind(ExprKind::BVar(0));
        let lam = Expr::lam(BinderInfo::Default, ty, body);
        let m = lam.compute_meta();
        assert_eq!(m.loose_bvar_range(), 0);
        assert!(!m.has_loose_bvars());
    }

    #[test]
    fn test_compute_meta_lam_preserves_outer_bvar() {
        // λ x : A => BVar(1)  — refers to outer binder
        let ty = Expr::const_(Name::from_string("A"), vec![]);
        let body = Expr::from_kind(ExprKind::BVar(1));
        let lam = Expr::lam(BinderInfo::Default, ty, body);
        let m = lam.compute_meta();
        assert_eq!(m.loose_bvar_range(), 1);
        assert!(m.has_loose_bvars());
    }

    #[test]
    fn test_compute_meta_pi_closes_bvar() {
        let ty = Expr::const_(Name::from_string("A"), vec![]);
        let body = Expr::from_kind(ExprKind::BVar(0));
        let pi = Expr::pi(BinderInfo::Default, ty, body);
        let m = pi.compute_meta();
        assert_eq!(m.loose_bvar_range(), 0);
    }

    #[test]
    fn test_compute_meta_let_closes_bvar() {
        let ty = Expr::const_(Name::from_string("A"), vec![]);
        let val = Expr::const_(Name::from_string("v"), vec![]);
        let body = Expr::from_kind(ExprKind::BVar(0));
        let let_expr = Expr::let_named(Name::anon(), ty, val, body, false);
        let m = let_expr.compute_meta();
        assert_eq!(m.loose_bvar_range(), 0);
    }

    #[test]
    fn test_compute_meta_nested_depth() {
        // App(App(f, a), b) should have depth 2
        let f = Expr::const_(Name::from_string("f"), vec![]);
        let a = Expr::const_(Name::from_string("a"), vec![]);
        let b = Expr::const_(Name::from_string("b"), vec![]);
        let app1 = Expr::app(f, a);
        let app2 = Expr::app(app1, b);
        let m = app2.compute_meta();
        assert_eq!(m.approx_depth(), 2);
    }

    #[test]
    fn test_compute_meta_lit() {
        let e = Expr::nat_lit(42);
        let m = e.compute_meta();
        assert!(!m.has_fvar());
        assert!(!m.has_loose_bvars());
        assert_eq!(m.approx_depth(), 0);
    }

    #[test]
    fn test_compute_meta_fvar_hash_includes_id() {
        let f0 = Expr::fvar(FVarId(0));
        let f1 = Expr::fvar(FVarId(1));

        assert_ne!(f0.hash_cached(), f1.hash_cached());
        assert_eq!(f0.hash_cached(), mix_hash(13, 0) as u32);
        assert_eq!(f1.hash_cached(), mix_hash(13, 1) as u32);
    }

    #[test]
    fn test_compute_meta_sort_hash_includes_level() {
        let sort0 = Expr::sort(Level::zero());
        let sort1 = Expr::sort(Level::succ(Level::zero()));

        let expected0 = mix_hash(11, hash_to_u64(&Level::zero())) as u32;
        let expected1 = mix_hash(11, hash_to_u64(&Level::succ(Level::zero()))) as u32;

        assert_ne!(sort0.hash_cached(), sort1.hash_cached());
        assert_eq!(sort0.hash_cached(), expected0);
        assert_eq!(sort1.hash_cached(), expected1);
    }

    #[test]
    fn test_compute_meta_const_hash_includes_name_and_levels() {
        let c0 = Expr::const_(Name::from_string("Nat"), LevelVec::new());
        let mut u_levels = LevelVec::new();
        u_levels.push(Level::param(Name::from_string("u")));
        let c1 = Expr::const_(Name::from_string("Nat"), u_levels);
        let c2 = Expr::const_(Name::from_string("List"), LevelVec::new());

        assert_ne!(c0.hash_cached(), c1.hash_cached());
        assert_ne!(c0.hash_cached(), c2.hash_cached());

        let c0_expected = mix_hash(
            5,
            mix_hash(
                hash_to_u64(&Name::from_string("Nat")),
                hash_to_u64(&LevelVec::new()),
            ),
        ) as u32;
        assert_eq!(c0.hash_cached(), c0_expected);
    }

    #[test]
    fn test_compute_meta_lit_hash_includes_value() {
        let n1 = Expr::nat_lit(1);
        let n2 = Expr::nat_lit(2);

        assert_ne!(n1.hash_cached(), n2.hash_cached());

        let expected1 = mix_hash(3, hash_to_u64(&Literal::Nat(BigNat::Small(1)))) as u32;
        let expected2 = mix_hash(3, hash_to_u64(&Literal::Nat(BigNat::Small(2)))) as u32;
        assert_eq!(n1.hash_cached(), expected1);
        assert_eq!(n2.hash_cached(), expected2);
    }

    #[test]
    fn test_compute_meta_proj_hash_includes_name_and_index() {
        let base = Expr::const_(Name::from_string("Prod.mk"), LevelVec::new());
        let p0 = Expr::proj(Name::from_string("Prod"), 0, base.clone());
        let p1 = Expr::proj(Name::from_string("Prod"), 1, base.clone());
        let p_other = Expr::proj(Name::from_string("Sigma"), 0, base.clone());

        assert_ne!(p0.hash_cached(), p1.hash_cached());
        assert_ne!(p0.hash_cached(), p_other.hash_cached());

        let inner = base.meta();
        let depth = (inner.approx_depth() as u32 + 1).min(255);
        let expected = mix_hash(
            depth as u64,
            mix_hash(
                hash_to_u64(&Name::from_string("Prod")),
                mix_hash(0, inner.hash() as u64),
            ),
        ) as u32;
        assert_eq!(p0.hash_cached(), expected);
    }

    #[test]
    fn test_expr_meta_equality() {
        let m1 = ExprMeta::pack(42, 3, 5, true, false, true, false);
        let m2 = ExprMeta::pack(42, 3, 5, true, false, true, false);
        assert_eq!(m1, m2);

        let m3 = ExprMeta::pack(43, 3, 5, true, false, true, false);
        assert_ne!(m1, m3);
    }

    #[test]
    fn test_expr_meta_hash_impl() {
        use std::collections::HashSet;
        let m1 = ExprMeta::pack(1, 0, 0, false, false, false, false);
        let m2 = ExprMeta::pack(2, 0, 0, false, false, false, false);
        let mut set = HashSet::new();
        set.insert(m1);
        set.insert(m2);
        assert_eq!(set.len(), 2);
        set.insert(m1);
        assert_eq!(set.len(), 2);
    }

    #[test]
    fn test_expr_equality_rejects_same_kind_with_mismatched_meta() {
        let good = Expr::from_kind(ExprKind::BVar(0));
        let forged = Expr::with_meta(
            ExprKind::BVar(0),
            ExprMeta::pack(good.hash_cached(), 7, 0, false, false, false, false),
        );

        assert_ne!(good.meta(), forged.meta());
        assert_ne!(good, forged);
    }

    #[test]
    fn test_expr_hashset_keeps_same_kind_with_different_meta_distinct() {
        use std::collections::HashSet;

        let good = Expr::from_kind(ExprKind::BVar(0));
        let forged = Expr::with_meta(
            ExprKind::BVar(0),
            ExprMeta::pack(good.hash_cached(), 9, 0, false, false, false, false),
        );

        let mut set = HashSet::new();
        set.insert(good);
        set.insert(forged);
        assert_eq!(set.len(), 2);
    }

    // =========================================================================
    // infer_implicit / infer_implicit_n unit tests (proof_coverage P1 iter 670)
    // =========================================================================

    /// Non-Pi expression: infer_implicit returns the expression unchanged.
    #[test]
    fn test_infer_implicit_non_pi_is_identity() {
        let sort = Expr::sort(Level::zero());
        assert_eq!(sort.infer_implicit(true), sort);
        assert_eq!(sort.infer_implicit(false), sort);
    }

    /// Single explicit Pi where BVar(0) does NOT appear in the body domain:
    /// should remain Default (explicit).
    ///
    /// `(α : Sort 0) → Sort 0`  — α is unused in any subsequent domain.
    #[test]
    fn test_infer_implicit_single_pi_unused_stays_explicit() {
        let ty = Expr::pi(
            BinderInfo::Default,
            Expr::sort(Level::zero()),
            Expr::sort(Level::zero()),
        );
        let result = ty.infer_implicit(true);
        // Should remain unchanged — no reason to make α implicit
        match &result.kind {
            ExprKind::Pi(bi, _, _) => {
                assert_eq!(
                    bi.info,
                    BinderInfo::Default,
                    "Unused binder should stay explicit"
                );
            }
            _ => panic!("Expected Pi"),
        }
    }

    /// Two-level Pi where BVar(0) of the first binder appears in the second
    /// binder's domain: strict mode should mark the first binder Implicit.
    ///
    /// `(α : Sort 0) → (a : α) → Sort 0`
    /// Here α (BVar 1 in body context, but we check if BVar 0 from the outer
    /// scope appears in the inner Pi's domain) should be marked Implicit
    /// because `a : α` references it.
    #[test]
    fn test_infer_implicit_used_in_domain_becomes_implicit() {
        // Build: (α : Sort 0) → (a : BVar(0)) → Sort 0
        // Inside the outer Pi body, α is BVar(0).
        // The inner Pi's domain is BVar(0) which refers to α — the outer binder.
        // So α appears in a subsequent explicit domain and should become Implicit.
        let inner_pi = Expr::pi(
            BinderInfo::Default,
            Expr::from_kind(ExprKind::BVar(0)), // a : α (α is BVar 0 inside outer Pi body)
            Expr::sort(Level::zero()),
        );
        let outer_pi = Expr::pi(BinderInfo::Default, Expr::sort(Level::zero()), inner_pi);
        let result = outer_pi.infer_implicit(true);

        // α should be marked Implicit because it appears in the next domain
        match &result.kind {
            ExprKind::Pi(bi, _, _) => {
                assert_eq!(
                    bi.info,
                    BinderInfo::Implicit,
                    "Binder used in subsequent domain should become Implicit"
                );
            }
            _ => panic!("Expected Pi"),
        }
    }

    /// Already-implicit binder should NOT be changed by infer_implicit.
    ///
    /// `{α : Sort 0} → Sort 0`
    #[test]
    fn test_infer_implicit_already_implicit_unchanged() {
        let ty = Expr::pi(
            BinderInfo::Implicit,
            Expr::sort(Level::zero()),
            Expr::sort(Level::zero()),
        );
        let result = ty.infer_implicit(true);
        match &result.kind {
            ExprKind::Pi(bi, _, _) => {
                assert_eq!(
                    bi.info,
                    BinderInfo::Implicit,
                    "Already implicit should stay implicit"
                );
            }
            _ => panic!("Expected Pi"),
        }
    }

    /// infer_implicit_n with n=0 returns the expression unchanged regardless.
    #[test]
    fn test_infer_implicit_n_zero_is_identity() {
        let inner = Expr::pi(
            BinderInfo::Default,
            Expr::from_kind(ExprKind::BVar(1)),
            Expr::sort(Level::zero()),
        );
        let ty = Expr::pi(BinderInfo::Default, Expr::sort(Level::zero()), inner);
        let result = ty.infer_implicit_n(0, true);
        // With n=0, even binders that would be marked Implicit remain Default
        match &result.kind {
            ExprKind::Pi(bi, _, _) => {
                assert_eq!(
                    bi.info,
                    BinderInfo::Default,
                    "infer_implicit_n(0) should not modify any binders"
                );
            }
            _ => panic!("Expected Pi"),
        }
    }

    /// infer_implicit_n with n=1 only processes the first binder.
    ///
    /// `(α : Sort 0) → (a : α) → (b : α) → Sort 0`
    /// Only α should be considered; a stays Default.
    #[test]
    fn test_infer_implicit_n_one_processes_only_first() {
        // Build: (α : Sort 0) → (a : α) → (b : α) → Sort 0
        // Inside outer Pi body: α = BVar(0)
        // Inside inner Pi body: α = BVar(1) (shifted by inner binder)
        let innermost = Expr::pi(
            BinderInfo::Default,
            Expr::from_kind(ExprKind::BVar(1)), // b : α (α shifted past inner binder)
            Expr::sort(Level::zero()),
        );
        let inner = Expr::pi(
            BinderInfo::Default,
            Expr::from_kind(ExprKind::BVar(0)), // a : α (α = BVar(0) inside outer body)
            innermost,
        );
        let outer = Expr::pi(BinderInfo::Default, Expr::sort(Level::zero()), inner);

        let result = outer.infer_implicit_n(1, true);

        // First binder: α used in domain of a → Implicit
        match &result.kind {
            ExprKind::Pi(bi, _, body) => {
                assert_eq!(
                    bi.info,
                    BinderInfo::Implicit,
                    "First binder should be Implicit"
                );
                // Second binder: a should remain Default (n=1 means we only processed 1)
                match &body.kind {
                    ExprKind::Pi(bi2, _, _) => {
                        assert_eq!(
                            bi2.info,
                            BinderInfo::Default,
                            "Second binder should remain Default with n=1"
                        );
                    }
                    _ => panic!("Expected inner Pi"),
                }
            }
            _ => panic!("Expected outer Pi"),
        }
    }

    /// Strict vs non-strict: BVar appearing only in result body.
    ///
    /// `(α : Sort 0) → α`
    /// In strict mode, α should stay Default (only checks domains).
    /// In non-strict mode, α should become Implicit (checks body too).
    #[test]
    fn test_infer_implicit_strict_vs_non_strict() {
        // (α : Sort 0) → BVar(0)  where BVar(0) = α in result body
        let ty = Expr::pi(
            BinderInfo::Default,
            Expr::sort(Level::zero()),
            Expr::from_kind(ExprKind::BVar(0)),
        );

        // Strict: α appears in body only, not in any domain → stays Default
        let strict_result = ty.infer_implicit(true);
        match &strict_result.kind {
            ExprKind::Pi(bi, _, _) => {
                assert_eq!(
                    bi.info,
                    BinderInfo::Default,
                    "Strict mode: BVar in body only should stay Default"
                );
            }
            _ => panic!("Expected Pi"),
        }

        // Non-strict: α appears in body → becomes Implicit
        let non_strict_result = ty.infer_implicit(false);
        match &non_strict_result.kind {
            ExprKind::Pi(bi, _, _) => {
                assert_eq!(
                    bi.info,
                    BinderInfo::Implicit,
                    "Non-strict mode: BVar in body should become Implicit"
                );
            }
            _ => panic!("Expected Pi"),
        }
    }

    /// Verify that `Expr::drop` handles deeply nested expression trees
    /// without stack overflow, exercising the iterative teardown path.
    ///
    /// A 20,000-deep App chain has `approx_depth` saturated at 255,
    /// so `Expr::drop` enters the iterative worklist path. This test
    /// proves the iterative drop is correct by dropping without
    /// `mem::forget` and without stack overflow.
    #[test]
    fn test_deep_expr_drop_iterative() {
        let func = Expr::const_(Name::from_string("f"), vec![]);
        let mut deep_expr = Expr::fvar(FVarId(0));
        for _ in 0..20_000 {
            deep_expr = Expr::app(func.clone(), deep_expr);
        }

        // Depth should be saturated at MAX_DEPTH (255).
        assert_eq!(
            deep_expr.meta.approx_depth(),
            255,
            "20k-deep chain should saturate depth at 255"
        );

        // Drop naturally — exercises iterative_drop_kind via Expr::drop.
        // If the iterative path is broken, this would stack overflow.
        drop(deep_expr);
    }

    /// Verify iterative drop handles deep Pi chains (binder expressions).
    #[test]
    fn test_deep_pi_chain_drop_iterative() {
        let base = Expr::sort(Level::zero());
        let mut deep_pi = base;
        for _ in 0..20_000 {
            deep_pi = Expr::pi(BinderInfo::Default, Expr::sort(Level::zero()), deep_pi);
        }

        assert_eq!(
            deep_pi.meta.approx_depth(),
            255,
            "20k-deep Pi chain should saturate depth at 255"
        );

        // Drop naturally — should not stack overflow.
        drop(deep_pi);
    }

    /// Verify iterative drop handles deep Let chains.
    #[test]
    fn test_deep_let_chain_drop_iterative() {
        let val = Expr::nat_lit(0);
        let ty = Expr::sort(Level::zero());
        let mut deep_let = Expr::fvar(FVarId(1));
        for _ in 0..20_000 {
            deep_let = Expr::let_named(Name::anon(), ty.clone(), val.clone(), deep_let, false);
        }

        assert_eq!(
            deep_let.meta.approx_depth(),
            255,
            "20k-deep Let chain should saturate depth at 255"
        );

        // Drop naturally — should not stack overflow.
        drop(deep_let);
    }

    /// Verify that Arc refcounting interacts correctly with iterative drop.
    /// When multiple references share deep sub-trees, only the last Arc
    /// owner triggers iterative teardown.
    #[test]
    fn test_shared_deep_subtree_drop() {
        let func = Expr::const_(Name::from_string("f"), vec![]);
        let mut deep_subtree = Expr::fvar(FVarId(0));
        for _ in 0..20_000 {
            deep_subtree = Expr::app(func.clone(), deep_subtree);
        }

        // Create two expressions sharing the same deep subtree via Arc.
        let shared = Arc::new(deep_subtree);
        let expr1 = Expr::from_kind(ExprKind::App(shared.clone(), shared.clone()));
        let expr2 = Expr::from_kind(ExprKind::App(shared.clone(), shared.clone()));

        // Drop shared reference first — subtree stays alive.
        drop(shared);

        // Drop expr1 — subtree refcount decrements but doesn't reach zero.
        drop(expr1);

        // Drop expr2 — last owner, triggers iterative teardown of the subtree.
        drop(expr2);
    }

    #[test]
    fn test_display_deeply_nested_no_stack_overflow() {
        // Build a deeply nested App chain: f(f(f(...f(x)...)))
        // 10_000 levels deep — would overflow without stack_safe guard.
        let mut expr = Expr::fvar(FVarId(0));
        let f = Expr::fvar(FVarId(1));
        for _ in 0..10_000 {
            expr = Expr::from_kind(ExprKind::App(Arc::new(f.clone()), Arc::new(expr)));
        }
        // Should not overflow — stack_safe guard in display_expr_ctx protects.
        let s = format!("{}", expr);
        assert!(!s.is_empty());
    }

    #[test]
    fn test_display_deeply_nested_mdata_no_stack_overflow() {
        // MData wrapping calls display_expr_ctx directly (the recursive path).
        // Build deeply nested MData chain.
        let mut expr = Expr::prop();
        for _ in 0..10_000 {
            expr = Expr::from_kind(ExprKind::MData(Vec::new(), Arc::new(expr)));
        }
        let s = format!("{}", expr);
        assert!(!s.is_empty());
    }

    #[test]
    fn test_multiplicity_mul_semiring_table() {
        // Full 3x3 truth table for Multiplicity::mul. Companion to the
        // false-positive note on the exhaustive match in expr/types.rs
        // (Trust ledger 2026-06-10: "unreachable code reached" — vcgen
        // models the enum discriminant as unconstrained).
        use crate::expr::Multiplicity::{Many, One, Zero};
        let all = [Zero, One, Many];
        for a in all {
            assert_eq!(Zero.mul(a), Zero);
            assert_eq!(a.mul(Zero), Zero);
            assert_eq!(One.mul(a), a);
            assert_eq!(a.mul(One), a);
        }
        assert_eq!(Many.mul(Many), Many);
    }

    #[test]
    fn test_display_sort_small_levels_exact() {
        // Pins display_level_as_nat behavior across the iterative rewrite
        // (Trust ledger 2026-06-10: arithmetic overflow (Add) @ expr/display.rs:17).
        assert_eq!(format!("{}", Expr::sort(Level::zero())), "Prop");
        assert_eq!(
            format!("{}", Expr::sort(Level::succ(Level::zero()))),
            "Type"
        );
        assert_eq!(
            format!("{}", Expr::sort(Level::succ(Level::succ(Level::zero())))),
            "Type 1"
        );
    }

    #[test]
    fn test_display_sort_deep_succ_chain_no_stack_overflow() {
        // display_level_as_nat is now iterative + checked_add: total on all
        // inputs, stack-safe on deep Succ chains (previously recursive with a
        // panicking `n + 1`).
        let mut level = Level::zero();
        for _ in 0..20_000 {
            level = Level::succ(level);
        }
        assert_eq!(format!("{}", Expr::sort(level)), "Type 19999");
    }

    #[test]
    fn test_debug_deeply_nested_no_stack_overflow() {
        // ExprKind's derived Debug recursively traverses Arc<Expr> children.
        // Expr::Debug wraps in stack_safe to prevent overflow.
        let mut expr = Expr::fvar(FVarId(0));
        let f = Expr::fvar(FVarId(1));
        for _ in 0..10_000 {
            expr = Expr::from_kind(ExprKind::App(Arc::new(f.clone()), Arc::new(expr)));
        }
        let s = format!("{:?}", expr);
        assert!(!s.is_empty());
    }

    // ════════════════════════════════════════════════════════════════════════════
    // Regression: kind() accessor returns same value as pub(crate) field (#1397)
    // ════════════════════════════════════════════════════════════════════════════

    /// Verify kind() accessor agrees with internal field for all ExprKind variants.
    #[test]
    fn test_kind_accessor_matches_field() {
        let bvar = Expr::bvar(3);
        assert_eq!(bvar.kind(), &bvar.kind);

        let sort = Expr::sort(Level::zero());
        assert_eq!(sort.kind(), &sort.kind);

        let c = Expr::const_(Name::from_string("Nat"), vec![]);
        assert_eq!(c.kind(), &c.kind);

        let lam = Expr::lam(
            BinderInfo::Default,
            Expr::sort(Level::zero()),
            Expr::bvar(0),
        );
        assert_eq!(lam.kind(), &lam.kind);

        let pi = Expr::pi(
            BinderInfo::Default,
            Expr::sort(Level::zero()),
            Expr::sort(Level::succ(Level::zero())),
        );
        assert_eq!(pi.kind(), &pi.kind);

        let app = Expr::app(Expr::const_(Name::from_string("f"), vec![]), Expr::bvar(0));
        assert_eq!(app.kind(), &app.kind);
    }

    /// Verify metadata remains consistent: hash and equality agree after
    /// construction through different paths.
    #[test]
    fn test_metadata_consistent_after_construction() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        fn hash_expr(e: &Expr) -> u64 {
            let mut h = DefaultHasher::new();
            e.hash(&mut h);
            h.finish()
        }

        // Two exprs built identically must have same hash and be equal
        let e1 = Expr::app(
            Expr::lam(
                BinderInfo::Default,
                Expr::sort(Level::zero()),
                Expr::bvar(0),
            ),
            Expr::const_(Name::from_string("Nat"), vec![]),
        );
        let e2 = Expr::app(
            Expr::lam(
                BinderInfo::Default,
                Expr::sort(Level::zero()),
                Expr::bvar(0),
            ),
            Expr::const_(Name::from_string("Nat"), vec![]),
        );
        assert_eq!(e1, e2, "structurally identical exprs must be equal");
        assert_eq!(
            hash_expr(&e1),
            hash_expr(&e2),
            "hash must agree for equal exprs"
        );

        // Cloned expr has same metadata
        let e3 = e1.clone();
        assert_eq!(e1, e3);
        assert_eq!(hash_expr(&e1), hash_expr(&e3));

        // from_kind produces correct metadata
        let e4 = Expr::from_kind(ExprKind::BVar(42));
        assert_eq!(e4.kind(), &ExprKind::BVar(42));
        assert_eq!(e4.meta(), e4.kind.compute_meta());
    }

    /// Verify that from_kind always produces metadata matching the kind's
    /// compute_meta(). This is the invariant that #1397 protects by making
    /// `kind` private — without mutation access, metadata can never desync.
    #[test]
    fn test_from_kind_metadata_invariant() {
        let kinds = vec![
            ExprKind::BVar(0),
            ExprKind::BVar(255),
            ExprKind::Sort(Level::zero()),
            ExprKind::Sort(Level::succ(Level::succ(Level::zero()))),
            ExprKind::Const(
                Name::from_string("Nat.add"),
                smallvec::smallvec![Level::zero()],
            ),
            ExprKind::App(
                Arc::new(Expr::const_(Name::from_string("f"), vec![])),
                Arc::new(Expr::bvar(0)),
            ),
            ExprKind::Lam(
                BinderInfo::Default.into(),
                Arc::new(Expr::sort(Level::zero())),
                Arc::new(Expr::bvar(0)),
            ),
            ExprKind::Pi(
                BinderInfo::Implicit.into(),
                Arc::new(Expr::sort(Level::zero())),
                Arc::new(Expr::sort(Level::succ(Level::zero()))),
            ),
            ExprKind::Let(
                Name::from_string("x"),
                Arc::new(Expr::sort(Level::zero())),
                Arc::new(Expr::bvar(0)),
                Arc::new(Expr::bvar(0)),
                false,
            ),
            ExprKind::Lit(Literal::Nat(BigNat::Small(42))),
            ExprKind::Lit(Literal::String("hello".into())),
        ];

        for kind in kinds {
            let expected_meta = kind.compute_meta();
            let expr = Expr::from_kind(kind.clone());
            assert_eq!(
                expr.meta(),
                expected_meta,
                "from_kind metadata must match compute_meta for {:?}",
                std::mem::discriminant(&kind),
            );
            // kind() accessor must return the original kind
            assert_eq!(
                expr.kind(),
                &kind,
                "kind() accessor must return the original kind"
            );
        }
    }

    /// Verify Deref<Target=ExprKind> agrees with kind() accessor.
    #[test]
    fn test_deref_agrees_with_kind_accessor() {
        let e = Expr::pi(
            BinderInfo::Default,
            Expr::sort(Level::zero()),
            Expr::bvar(0),
        );
        // Deref gives ExprKind, kind() gives &ExprKind — must match
        assert_eq!(&*e, e.kind());
    }

    // =========================================================================
    // Lift composition law: core binding variants (#1029)
    // lift(a).lift(b) == lift(a+b) for Lam, Pi, Let
    // These binders increment the start parameter internally, so composition
    // correctness depends on the Lifter's fold_binder_body_opt being correct.
    // =========================================================================

    #[test]
    fn test_lift_composition_lam() {
        // Lambda with free BVar in body: λ (x:Prop). BVar(2)
        // BVar(2) is free (2 >= 1 under binder)
        let lam = Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(2)),
        );
        let lifted_ab = lam.clone().lift(3).lift(4);
        let lifted_sum = lam.lift(7);
        assert_eq!(
            lifted_ab, lifted_sum,
            "Lam lift composition with free BVar in body"
        );
    }

    #[test]
    fn test_lift_composition_lam_bound_var() {
        // Lambda with bound BVar in body: λ (x:Prop). BVar(0)
        // BVar(0) is bound (0 < 1 under binder), should be unchanged
        let lam = Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(0)),
        );
        let lifted_ab = lam.clone().lift(2).lift(5);
        let lifted_sum = lam.lift(7);
        assert_eq!(
            lifted_ab, lifted_sum,
            "Lam lift composition with bound BVar"
        );
    }

    #[test]
    fn test_lift_composition_lam_domain_has_bvar() {
        // Lambda with BVar in domain: λ (x:BVar(0)). BVar(1)
        // Both domain BVar(0) and body BVar(1) (free, since 1>=1) should be lifted
        let lam = Expr::lam(
            BinderInfo::Default,
            Expr::from_kind(ExprKind::BVar(0)),
            Expr::from_kind(ExprKind::BVar(1)),
        );
        let lifted_ab = lam.clone().lift(2).lift(3);
        let lifted_sum = lam.lift(5);
        assert_eq!(
            lifted_ab, lifted_sum,
            "Lam lift composition with BVar in domain"
        );
    }

    #[test]
    fn test_lift_composition_pi() {
        // Pi with free BVar: Π (x:BVar(1)). BVar(3)
        let pi = Expr::pi(
            BinderInfo::Default,
            Expr::from_kind(ExprKind::BVar(1)),
            Expr::from_kind(ExprKind::BVar(3)),
        );
        let lifted_ab = pi.clone().lift(1).lift(2);
        let lifted_sum = pi.lift(3);
        assert_eq!(lifted_ab, lifted_sum, "Pi lift composition");
    }

    #[test]
    fn test_lift_composition_pi_bound_var() {
        // Pi with bound BVar: Π (x:Prop). BVar(0)
        let pi = Expr::pi(
            BinderInfo::Default,
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(0)),
        );
        let lifted_ab = pi.clone().lift(4).lift(3);
        let lifted_sum = pi.lift(7);
        assert_eq!(lifted_ab, lifted_sum, "Pi lift composition with bound var");
    }

    #[test]
    fn test_lift_composition_let() {
        // Let with free BVar in body: let x : Prop := Prop in BVar(2)
        // BVar(2) is free (2 >= 1 under let binder)
        let let_expr = Expr::let_named(
            Name::anon(),
            Expr::prop(),
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(2)),
            false,
        );
        let lifted_ab = let_expr.clone().lift(2).lift(3);
        let lifted_sum = let_expr.lift(5);
        assert_eq!(
            lifted_ab, lifted_sum,
            "Let lift composition with free BVar in body"
        );
    }

    #[test]
    fn test_lift_composition_let_bvar_in_val() {
        // Let with BVar in value: let x : Prop := BVar(0) in BVar(1)
        let let_expr = Expr::let_named(
            Name::anon(),
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(0)),
            Expr::from_kind(ExprKind::BVar(1)),
            false,
        );
        let lifted_ab = let_expr.clone().lift(1).lift(4);
        let lifted_sum = let_expr.lift(5);
        assert_eq!(
            lifted_ab, lifted_sum,
            "Let lift composition with BVar in value"
        );
    }

    #[test]
    fn test_lift_composition_proj() {
        // Proj(name, idx, BVar(1))
        let proj = Expr::proj(
            Name::from_string("Prod"),
            0,
            Expr::from_kind(ExprKind::BVar(1)),
        );
        let lifted_ab = proj.clone().lift(2).lift(3);
        let lifted_sum = proj.lift(5);
        assert_eq!(lifted_ab, lifted_sum, "Proj lift composition");
    }

    #[test]
    fn test_lift_composition_mdata() {
        // MData wrapping BVar
        let metadata: MDataMap = vec![(Name::from_string("key"), MDataValue::Bool(true))];
        let mdata = Expr::mdata(metadata, Expr::from_kind(ExprKind::BVar(0)));
        let lifted_ab = mdata.clone().lift(3).lift(2);
        let lifted_sum = mdata.lift(5);
        assert_eq!(lifted_ab, lifted_sum, "MData lift composition");
    }

    #[test]
    fn test_lift_composition_cubical_transp() {
        let transp = Expr::from_kind(ExprKind::CubicalTransp {
            ty: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
            phi: Arc::new(Expr::from_kind(ExprKind::BVar(1))),
            base: Arc::new(Expr::from_kind(ExprKind::BVar(2))),
        });
        let lifted_ab = transp.clone().lift(2).lift(3);
        let lifted_sum = transp.lift(5);
        assert_eq!(lifted_ab, lifted_sum, "CubicalTransp lift composition");
    }

    #[test]
    fn test_lift_composition_cubical_path_app() {
        let path_app = Expr::from_kind(ExprKind::CubicalPathApp {
            path: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
            arg: Arc::new(Expr::from_kind(ExprKind::BVar(1))),
        });
        let lifted_ab = path_app.clone().lift(1).lift(3);
        let lifted_sum = path_app.lift(4);
        assert_eq!(lifted_ab, lifted_sum, "CubicalPathApp lift composition");
    }

    // =========================================================================
    // Instantiate/lift identity for mode-specific variants (#1029)
    // inst(lift(e, 1), v) == e for closed v
    // =========================================================================

    #[test]
    fn test_inst_lift_identity_squash() {
        let v = Expr::prop();
        let e = Expr::from_kind(ExprKind::Squash(Arc::new(Expr::from_kind(ExprKind::BVar(
            0,
        )))));
        let result = e.clone().lift(1).instantiate(&v);
        assert_eq!(
            result, e,
            "inst(lift(Squash(BVar(0)), 1), v) == Squash(BVar(0))"
        );
    }

    #[test]
    fn test_inst_lift_identity_cubical_path() {
        let v = Expr::prop();
        let e = Expr::from_kind(ExprKind::CubicalPath {
            ty: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
            left: Arc::new(Expr::from_kind(ExprKind::BVar(1))),
            right: Arc::new(Expr::prop()),
        });
        let result = e.clone().lift(1).instantiate(&v);
        assert_eq!(result, e, "inst(lift(CubicalPath, 1), v) == CubicalPath");
    }

    #[test]
    fn test_inst_lift_identity_cubical_path_lam() {
        // CubicalPathLam binds, so body BVar(1) is free (refers outside)
        let v = Expr::prop();
        let e = Expr::from_kind(ExprKind::CubicalPathLam {
            body: Arc::new(Expr::from_kind(ExprKind::BVar(1))),
        });
        let result = e.clone().lift(1).instantiate(&v);
        assert_eq!(
            result, e,
            "inst(lift(CubicalPathLam, 1), v) == CubicalPathLam"
        );
    }

    #[test]
    fn test_inst_lift_identity_cubical_path_app() {
        let v = Expr::prop();
        let e = Expr::from_kind(ExprKind::CubicalPathApp {
            path: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
            arg: Arc::new(Expr::from_kind(ExprKind::BVar(2))),
        });
        let result = e.clone().lift(1).instantiate(&v);
        assert_eq!(
            result, e,
            "inst(lift(CubicalPathApp, 1), v) == CubicalPathApp"
        );
    }

    #[test]
    fn test_inst_lift_identity_cubical_hcomp() {
        let v = Expr::prop();
        let e = Expr::from_kind(ExprKind::CubicalHComp {
            ty: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
            phi: Arc::new(Expr::from_kind(ExprKind::BVar(1))),
            u: Arc::new(Expr::from_kind(ExprKind::BVar(2))),
            base: Arc::new(Expr::from_kind(ExprKind::BVar(3))),
        });
        let result = e.clone().lift(1).instantiate(&v);
        assert_eq!(result, e, "inst(lift(CubicalHComp, 1), v) == CubicalHComp");
    }

    #[test]
    fn test_inst_lift_identity_cubical_transp() {
        let v = Expr::prop();
        let e = Expr::from_kind(ExprKind::CubicalTransp {
            ty: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
            phi: Arc::new(Expr::from_kind(ExprKind::BVar(1))),
            base: Arc::new(Expr::from_kind(ExprKind::BVar(2))),
        });
        let result = e.clone().lift(1).instantiate(&v);
        assert_eq!(
            result, e,
            "inst(lift(CubicalTransp, 1), v) == CubicalTransp"
        );
    }

    #[test]
    fn test_inst_lift_identity_zfc_mem() {
        let v = Expr::prop();
        let e = Expr::from_kind(ExprKind::ZFCMem {
            element: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
            set: Arc::new(Expr::from_kind(ExprKind::BVar(1))),
        });
        let result = e.clone().lift(1).instantiate(&v);
        assert_eq!(result, e, "inst(lift(ZFCMem, 1), v) == ZFCMem");
    }

    #[test]
    fn test_inst_lift_identity_zfc_comprehension() {
        // ZFCComprehension binds in pred, so pred BVar(1) is free
        let v = Expr::prop();
        let e = Expr::from_kind(ExprKind::ZFCComprehension {
            domain: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
            pred: Arc::new(Expr::from_kind(ExprKind::BVar(1))),
        });
        let result = e.clone().lift(1).instantiate(&v);
        assert_eq!(
            result, e,
            "inst(lift(ZFCComprehension, 1), v) == ZFCComprehension"
        );
    }

    #[test]
    fn test_inst_lift_identity_proj() {
        let v = Expr::prop();
        let e = Expr::proj(
            Name::from_string("Prod"),
            0,
            Expr::from_kind(ExprKind::BVar(0)),
        );
        let result = e.clone().lift(1).instantiate(&v);
        assert_eq!(result, e, "inst(lift(Proj, 1), v) == Proj");
    }

    #[test]
    fn test_inst_lift_identity_mdata() {
        let v = Expr::prop();
        let metadata: MDataMap = vec![(Name::from_string("key"), MDataValue::Bool(true))];
        let e = Expr::mdata(metadata, Expr::from_kind(ExprKind::BVar(0)));
        let result = e.clone().lift(1).instantiate(&v);
        assert_eq!(result, e, "inst(lift(MData, 1), v) == MData");
    }

    #[test]
    fn test_inst_lift_identity_let() {
        // Let binds, so body BVar(1) is free
        let v = Expr::prop();
        let e = Expr::let_named(
            Name::anon(),
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(0)),
            Expr::from_kind(ExprKind::BVar(1)),
            false,
        );
        let result = e.clone().lift(1).instantiate(&v);
        assert_eq!(result, e, "inst(lift(Let, 1), v) == Let");
    }

    // =========================================================================
    // Nested composition: multi-level binder chains (#1029)
    // Tests that lift composition holds through nested binding structures
    // =========================================================================

    #[test]
    fn test_lift_composition_nested_lam_pi() {
        // λ (x:Prop). Π (y:BVar(0)). BVar(2)
        // BVar(2) is free (needs to escape both binders: 2 >= 2)
        let inner = Expr::pi(
            BinderInfo::Default,
            Expr::from_kind(ExprKind::BVar(0)),
            Expr::from_kind(ExprKind::BVar(2)),
        );
        let e = Expr::lam(BinderInfo::Default, Expr::prop(), inner);
        let lifted_ab = e.clone().lift(3).lift(2);
        let lifted_sum = e.lift(5);
        assert_eq!(lifted_ab, lifted_sum, "Nested Lam-Pi lift composition");
    }

    #[test]
    fn test_lift_composition_nested_let_in_lam() {
        // λ (x:Prop). let y : Prop := BVar(0) in BVar(2)
        // BVar(0) in val refers to x (bound), BVar(2) in body is free (2 >= 2)
        let inner = Expr::let_named(
            Name::anon(),
            Expr::prop(),
            Expr::from_kind(ExprKind::BVar(0)),
            Expr::from_kind(ExprKind::BVar(2)),
            false,
        );
        let e = Expr::lam(BinderInfo::Default, Expr::prop(), inner);
        let lifted_ab = e.clone().lift(1).lift(4);
        let lifted_sum = e.lift(5);
        assert_eq!(lifted_ab, lifted_sum, "Nested Let-in-Lam lift composition");
    }

    #[test]
    fn test_inst_lift_identity_nested_lam() {
        // inst(lift(λ x. λ y. BVar(2), 1), v) == λ x. λ y. BVar(2)
        // BVar(2) is free wrt both binders
        let v = Expr::prop();
        let e = Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::lam(
                BinderInfo::Default,
                Expr::prop(),
                Expr::from_kind(ExprKind::BVar(2)),
            ),
        );
        let result = e.clone().lift(1).instantiate(&v);
        assert_eq!(result, e, "inst(lift(nested Lam, 1), v) identity");
    }
}
