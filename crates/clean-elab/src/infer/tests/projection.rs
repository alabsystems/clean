// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Projection and namespace resolution tests

use super::*;

fn issue796_cover_env() -> Environment {
    let mut env = Environment::with_prelude();
    let cover = parse_decl_for_elab(
        r"inductive Cover : (x y z : List α) -> Type u
| done  : Cover [] [] []
| left  : Cover x y z -> Cover (t :: x) y (t :: z)
| right : Cover x y z -> Cover x (t :: y) (t :: z)
| both  : Cover x y z -> Cover (t :: x) (t :: y) (t :: z)",
    )
    .unwrap();
    crate::elaborate_decl_and_register(&mut env, &cover)
        .expect("Cover should elaborate and register");
    env
}

#[test]
fn test_projection_index_resolves_struct_name() {
    let env = pair_env();
    // Surface `.1` is 1-based (Lean); it resolves to kernel field index 0 (first field).
    let expr = elab_with_env(&env, "fun (p : Pair) => p.1").unwrap();

    match expr.kind() {
        ExprKind::Lam(_, _, body) => match body.kind() {
            ExprKind::Proj(struct_name, idx, _) => {
                assert_eq!(struct_name, &Name::from_string("Pair"));
                assert_eq!(*idx, 0);
            }
            other => panic!("expected projection, got {other:?}"),
        },
        other => panic!("expected lambda, got {other:?}"),
    }
}

#[test]
fn test_projection_index_second_field_is_one_based() {
    // Regression for the numeric-projection off-by-one: surface `.2` (1-based) must
    // resolve to kernel field index 1 (the second field), agreeing with `.snd`.
    let env = pair_env();
    let expr = elab_with_env(&env, "fun (p : Pair) => p.2").unwrap();

    match expr.kind() {
        ExprKind::Lam(_, _, body) => match body.kind() {
            ExprKind::Proj(struct_name, idx, _) => {
                assert_eq!(struct_name, &Name::from_string("Pair"));
                assert_eq!(*idx, 1);
            }
            other => panic!("expected projection, got {other:?}"),
        },
        other => panic!("expected lambda, got {other:?}"),
    }
}

#[test]
fn test_projection_named_field_lookup() {
    let env = pair_env();
    let expr = elab_with_env(&env, "fun (p : Pair) => p.snd").unwrap();

    match expr.kind() {
        ExprKind::Lam(_, _, body) => match body.kind() {
            ExprKind::Proj(struct_name, idx, _) => {
                assert_eq!(struct_name, &Name::from_string("Pair"));
                assert_eq!(*idx, 1);
            }
            other => panic!("expected projection, got {other:?}"),
        },
        other => panic!("expected lambda, got {other:?}"),
    }
}

#[test]
fn test_namespace_projection_resolves_const() {
    let env = namespace_env();
    let expr = elab_with_env(&env, "whnf_to.refl").unwrap();

    match expr.kind() {
        ExprKind::Const(name, _) => {
            assert_eq!(name, &Name::from_string("whnf_to.refl"));
        }
        other => panic!("expected const, got {other:?}"),
    }
}

#[test]
fn test_projection_prefers_struct_over_namespace_const() {
    let env = pair_env_with_namespaced_const();
    let expr = elab_with_env(&env, "pairVal.snd").unwrap();

    match expr.kind() {
        ExprKind::Proj(struct_name, idx, target) => {
            assert_eq!(struct_name, &Name::from_string("Pair"));
            assert_eq!(*idx, 1);
            assert!(
                matches!(target.kind(), ExprKind::Const(name, _) if *name == Name::from_string("pairVal"))
            );
        }
        other => panic!("expected projection, got {other:?}"),
    }
}

#[test]
fn test_projection_unknown_field_error() {
    let env = pair_env();
    let err = elab_with_env(&env, "fun (p : Pair) => p.frst").expect_err("should fail");

    let ElabError::UnknownProjectionField {
        field, suggestions, ..
    } = &err
    else {
        panic!("expected UnknownProjectionField, got {err:?}");
    };
    assert_eq!(field, "frst");
    assert_eq!(suggestions.first().map(String::as_str), Some("fst"));

    let diagnostics = err.agent_diagnostics();
    assert!(diagnostics
        .iter()
        .any(|diag| diag.code == "structure.unknown_projection_field"
            && diag.facts.get("field").map(String::as_str) == Some("frst")
            && diag
                .suggestions
                .iter()
                .any(|suggestion| suggestion.replacement.as_deref() == Some("fst"))));
}

#[test]
fn test_projection_index_oob_error() {
    let env = pair_env();
    // Pair has 2 fields, so `.1`/`.2` are valid (1-based); `.3` is out of bounds.
    let err = elab_with_env(&env, "fun (p : Pair) => p.3").expect_err("should fail");

    assert!(matches!(
        err,
        ElabError::ProjectionIndexOutOfBounds { idx: 3, .. }
    ));
}

#[test]
fn test_namespace_only_prefix_resolves_qualified_const() {
    let env = namespace_only_env();
    // Parser produces Proj(Ident("Foo"), Named("bar")) for "Foo.bar"
    // Since "Foo" is not a constant, the fallback should try "Foo.bar"
    let expr = elab_with_env(&env, "Foo.bar").unwrap();

    match expr.kind() {
        ExprKind::Const(name, _) => {
            assert_eq!(name, &Name::from_string("Foo.bar"));
        }
        other => panic!("expected const Foo.bar, got {other:?}"),
    }
}

#[test]
fn test_projection_receiver_error_and_namespace_retry_restore_expected_context() {
    let env = namespace_only_env();
    let mut ctx = ElabCtx::new(&env);
    let outer_expected = Expr::type_();
    ctx.current_expected_type = Some(outer_expected.clone());
    ctx.push_local("outerProjectionLocal".to_string(), Expr::prop());
    let locals_before = ctx.locals.clone();
    let span = clean_parser::Span::dummy();

    // This reaches the fallible receiver attempt after the result-level expected
    // type has been hidden. Neither the receiver error nor its failed qualified
    // fallback may strand `current_expected_type = None`.
    let missing_receiver = SurfaceExpr::Ident(span, "MissingReceiver".to_string());
    let missing_field = clean_parser::Projection::Named("field".to_string());
    assert!(ctx.elab_proj(&missing_receiver, &missing_field).is_err());
    assert_eq!(ctx.current_expected_type, Some(outer_expected.clone()));
    assert_eq!(ctx.locals, locals_before);

    // Reuse the same context for the namespace-only success path. `Foo` is not
    // a value, but `Foo.bar` is a real declaration.
    let namespace_receiver = SurfaceExpr::Ident(span, "Foo".to_string());
    let namespace_field = clean_parser::Projection::Named("bar".to_string());
    let result = ctx
        .elab_proj(&namespace_receiver, &namespace_field)
        .expect("namespace fallback should remain usable after receiver failure");
    assert!(
        matches!(result.kind(), ExprKind::Const(name, _) if *name == Name::from_string("Foo.bar")),
        "expected namespace-qualified constant, got {result:?}"
    );
    assert_eq!(ctx.current_expected_type, Some(outer_expected));
    assert_eq!(ctx.locals, locals_before);
}

#[test]
fn test_namespace_only_multi_segment_resolves_qualified_const() {
    let mut env = Environment::new();
    // Only add Foo.Bar.baz, NOT Foo or Foo.Bar
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Foo.Bar.baz"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    // Parser produces Proj(Proj(Ident("Foo"), "Bar"), "baz")
    // Both Foo and Foo.Bar are not constants, so fallback collects full name
    let expr = elab_with_env(&env, "Foo.Bar.baz").unwrap();

    match expr.kind() {
        ExprKind::Const(name, _) => {
            assert_eq!(name, &Name::from_string("Foo.Bar.baz"));
        }
        other => panic!("expected const Foo.Bar.baz, got {other:?}"),
    }
}

#[test]
fn test_namespace_only_fails_when_no_constant_exists() {
    let env = Environment::new();
    // Neither NonExistent nor NonExistent.foo exists
    let err = elab_with_env(&env, "NonExistent.foo").expect_err("should fail");

    assert!(matches!(err, ElabError::UnknownIdent(s) if s == "NonExistent"));
}

#[test]
fn test_namespace_only_with_parenthesized_base() {
    // Test that (Foo).bar still works when Foo.bar is a constant
    // Parser may produce Proj(Paren(Ident("Foo")), "bar")
    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Foo.bar"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    // This tests that we handle parentheses properly
    // Note: The parser might strip parens in projection context
    let result = elab_with_env(&env, "(Foo).bar");
    // Either succeeds with the constant, or fails trying to elaborate Foo
    // The important thing is it doesn't panic
    match result {
        Ok(ref expr) if matches!(expr.kind(), ExprKind::Const(name, _) if *name == Name::from_string("Foo.bar")) =>
        {
            // Successfully resolved to Foo.bar constant
        }
        Err(ElabError::UnknownIdent(_)) => {
            // Also acceptable - parentheses may prevent fallback
        }
        other => panic!("unexpected result: {other:?}"),
    }
}

/// B03 flip (was #3139): dot notation on an unknown ident in a def BODY is a
/// loud unknown-identifier error.
///
/// This test previously pinned the pre-B03 bug: in `def foo := G.Adj` the
/// body identifier `G` was silently AUTO-BOUND as an implicit (type `Sort u`)
/// and `.Adj` then produced a sorry placeholder — an unascribed typo became
/// an accepted, sorry-tainted declaration. Lean binds auto-implicits only in
/// declaration headers (`Lean/Elab/MutualDef.lean` `elabHeaders` under
/// `withAutoBoundImplicit`); a bare unknown ident in a VALUE position is
/// `unknown identifier`. The #3139 sorry recovery still applies to
/// signature-position auto-implicits (e.g. `G.Adj` in a binder type).
#[test]
fn test_dot_notation_unknown_body_ident_rejected_loud() {
    let _env = Environment::with_prelude();
    let result = elab_decl("def foo := G.Adj");
    match result {
        Err(ElabError::UnknownIdent(_) | ElabError::UnknownIdentWithSuggestions { .. }) => {}
        other => {
            panic!("unknown body ident `G` must be a loud unknown-identifier error, got: {other:?}")
        }
    }
}

/// #796: Dot notation on type-valued expression resolves via namespace.
///
/// When the base of a dot notation is a type constant (e.g., `Nat.myFunc`),
/// and the namespace lookup in the Const path succeeds, the constant is
/// returned directly. This test verifies the existing Const path works.
#[test]
fn test_dot_notation_type_const_namespace_lookup() {
    let mut env = Environment::with_prelude();

    // Add Nat.myCustomFunc as a constant (using a name not in prelude)
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat.myCustomFunc"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            Expr::const_(Name::from_string("Nat"), vec![]),
            Expr::const_(Name::from_string("Nat"), vec![]),
        ),
    })
    .unwrap();

    // `Nat.myCustomFunc` should resolve as a constant via namespace lookup
    let result = elab_with_env(&env, "Nat.myCustomFunc");
    assert!(
        result.is_ok(),
        "Nat.myCustomFunc should resolve via namespace lookup, got {result:?}"
    );
    let expr = result.unwrap();
    assert!(
        matches!(expr.kind(), ExprKind::Const(name, _) if name.to_string() == "Nat.myCustomFunc"),
        "expected Const(Nat.myCustomFunc), got {expr:?}"
    );
}

/// #796: Dot notation on type-valued expression — Sort fallback path.
///
/// When the base expression's type is Sort (meaning the expression is
/// a type), and the field doesn't exist as a namespaced constant,
/// elab_dot_notation should return UnknownIdent rather than the
/// confusing "cannot extract type name from Sort(...)" error.
#[test]
fn test_dot_notation_sort_type_returns_clear_error() {
    let env = Environment::with_prelude();

    // `Nat.nonexistent_field` — Nat is a constant of type Type,
    // and there's no Nat.nonexistent_field constant.
    // The old code would fail with "cannot extract type name from Sort(...)".
    // The new code returns UnknownIdent for the missing field.
    let result = elab_with_env(&env, "Nat.nonexistent_field");
    assert!(
        result.is_err(),
        "Nat.nonexistent_field should fail: {result:?}"
    );
    // Should be an UnknownIdent, not a NotImplemented about Sort
    match &result {
        Err(ElabError::UnknownIdent(_)) => {
            // Correct: clear error about unknown identifier
        }
        Err(ElabError::NotImplemented(msg)) if msg.contains("Sort") => {
            panic!("should not get Sort error, got: {msg}");
        }
        Err(e) => {
            // Other errors are acceptable (e.g., type resolution)
            // as long as they're not the confusing Sort message
            let msg = format!("{e:?}");
            assert!(
                !msg.contains("cannot extract type name from Sort"),
                "should not get Sort extraction error, got: {e:?}"
            );
        }
        Ok(_) => panic!("should not succeed"),
    }
}

/// #796: Application of anonymous constructor to function-valued base.
///
/// `f .done` should parse as `App(f, Ident(".done"))` since the space
/// separates the leading dot from `f`. The elaborator resolves `.done`
/// to `Cover.done` with type `Cover [] [] []`, but unifying this with
/// `Cover x y z` (where x, y, z are lambda-bound FVars) requires index
/// unification which is not yet implemented. The test verifies the parser
/// correctly treats `.done` as an argument (not silently dropping it).
#[test]
fn test_issue796_function_dot_ctor_projection_reinterprets_as_application() {
    // After #3421: non-adjacent `f .done` is parsed as `App(f, Ident(".done"))`,
    // NOT as `Proj(f, "done")`. This is correct Lean 4 semantics: a space before
    // the dot means anonymous constructor, not projection. The elaborator then
    // resolves `.done` to `Cover.done : Cover [] [] []`.
    //
    // The original test used `f : Cover x y z -> Prop` with abstract parameters,
    // which means `.done` (type `Cover [] [] []`) can't unify with `Cover x y z`.
    // That test only passed before because parse_expr silently dropped `.done`
    // (Dot was not in is_plain_atom_start, so the app loop broke and `.done`
    // remained unconsumed).
    //
    // Updated to use `Cover (@List.nil α) (@List.nil α) (@List.nil α)` where
    // `.done` actually typechecks: `Cover.done : Cover [] [] []` unifies
    // directly with the parameter type `Cover (@List.nil α) (@List.nil α)
    // (@List.nil α)` (both reduce to `Cover [] [] []` modulo α).
    let env = issue796_cover_env();
    let result = elab_with_env(
        &env,
        "fun {α : Type} (f : Cover (@List.nil α) (@List.nil α) (@List.nil α) -> Prop) => f .done",
    );
    // Elaboration must SUCCEED: `.done` is parsed as an argument (not
    // silently dropped by the parser, #3421) and the elaborator resolves it
    // to `Cover.done` applied to f. The important behaviour is that the
    // parser treats `f .done` as application, not projection, and the
    // leading-dot constructor lookup succeeds.
    assert!(
        result.is_ok(),
        "f .done should elaborate as f applied to Cover.done, got {result:?}"
    );
}

#[test]
fn test_issue796_leading_dot_ctor_with_expected_indexed_type() {
    let env = issue796_cover_env();
    let result = elab_with_env(
        &env,
        "fun {α : Type} (x y z : List α) (t : α) (c : Cover x y z) => ((.left c) : Cover (t :: x) y (t :: z))",
    );
    assert!(
        result.is_ok(),
        "leading-dot constructor application should use the indexed Cover expectation, got {result:?}"
    );
}

#[test]
fn test_issue796_linear_done_decl_registers_after_cover() {
    let mut env = issue796_cover_env();
    let linear_done = parse_decl_for_elab(
        r"inductive LinearDone : Cover x y z -> Prop
| done : LinearDone .done",
    )
    .unwrap();
    crate::elaborate_decl_and_register(&mut env, &linear_done)
        .expect("LinearDone should elaborate and register after Cover");
}

#[test]
fn test_issue796_linear_left_decl_registers_after_cover() {
    let mut env = issue796_cover_env();
    let linear_left = parse_decl_for_elab(
        r"inductive LinearLeft : Cover x y z -> Prop
| left : LinearLeft c -> LinearLeft (.left c)",
    )
    .unwrap();
    crate::elaborate_decl_and_register(&mut env, &linear_left)
        .expect("LinearLeft should elaborate and register after Cover");
}

/// Regression test for #3421: dot notation `.ok`/`.error` not resolved for Except type.
///
/// Except is declared as an axiom (not a registered inductive), so the anonymous
/// constructor resolution must fall back to looking up `Except.ok` / `Except.error`
/// as constants directly.
#[test]
fn test_issue3421_except_dot_ok_resolves() {
    let env = Environment::with_prelude();
    // Fully-qualified form should always work
    let result = elab_with_env(&env, "(Except.ok 42 : Except Nat Nat)");
    assert!(
        result.is_ok(),
        "Except.ok should resolve via fully-qualified name, got {result:?}"
    );
}

#[test]
fn test_issue3421_except_dot_ok_anonymous_ctor() {
    let mut env = Environment::with_prelude();
    // Anonymous constructor `.ok` should resolve when expected type is Except
    let decl = parse_decl_for_elab("def test : Except Nat Nat := .ok 42").unwrap();
    let result = crate::elaborate_decl_and_register(&mut env, &decl);
    assert!(
        result.is_ok(),
        "Anonymous constructor .ok should resolve for Except type, got {result:?}"
    );
}

#[test]
fn test_issue3421_except_dot_error_anonymous_ctor() {
    let mut env = Environment::with_prelude();
    // Anonymous constructor `.error` should resolve when expected type is Except
    let decl = parse_decl_for_elab("def test : Except Nat Nat := .error 99").unwrap();
    let result = crate::elaborate_decl_and_register(&mut env, &decl);
    assert!(
        result.is_ok(),
        "Anonymous constructor .error should resolve for Except type, got {result:?}"
    );
}

#[test]
fn test_issue3421_except_dot_ok_with_user_error_type() {
    let mut env = Environment::with_prelude();
    // First register a user-defined error type
    let err_decl = parse_decl_for_elab("inductive MyError where | notFound").unwrap();
    crate::elaborate_decl_and_register(&mut env, &err_decl).expect("MyError should register");
    // Now test the exact repro from the issue
    let decl = parse_decl_for_elab("def test : Except MyError Nat := .ok 42").unwrap();
    let result = crate::elaborate_decl_and_register(&mut env, &decl);
    assert!(
        result.is_ok(),
        "Anonymous constructor .ok should resolve for Except MyError Nat, got {result:?}"
    );
}

#[test]
fn test_issue3421_except_dot_error_with_user_error_type() {
    let mut env = Environment::with_prelude();
    // First register a user-defined error type
    let err_decl = parse_decl_for_elab("inductive MyError where | notFound").unwrap();
    crate::elaborate_decl_and_register(&mut env, &err_decl).expect("MyError should register");

    // Verify MyError.notFound exists as a constant
    assert!(
        env.get_const(&Name::from_string("MyError.notFound"))
            .is_some(),
        "MyError.notFound should be in the environment"
    );

    // Test 1: Fully qualified argument works
    let decl1 =
        parse_decl_for_elab("def test1 : Except MyError Nat := .error MyError.notFound").unwrap();
    let result1 = crate::elaborate_decl_and_register(&mut env, &decl1);
    assert!(
        result1.is_ok(),
        ".error with fully-qualified MyError.notFound should work, got {result1:?}"
    );

    // Test 2: Expression-level test for .error with expected type
    let except_myerror_nat = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Except"), vec![Level::zero()]),
            Expr::const_(Name::from_string("MyError"), vec![]),
        ),
        Expr::const_(Name::from_string("Nat"), vec![]),
    );
    let mut ctx = ElabCtx::new(&env);
    let ctor = ctx.elab_leading_dot_ctor_with_expected_type(".error", &except_myerror_nat);
    assert!(
        ctor.is_ok(),
        "elab_leading_dot_ctor_with_expected_type should resolve .error, got {ctor:?}"
    );
    let ctor_expr = ctor.unwrap();
    // The result should not contain FVars (unsolved metas)
    assert!(
        !format!("{ctor_expr:?}").contains("FVar"),
        "Constructor expression should not contain FVars (unsolved metas), got {ctor_expr:?}"
    );

    // Test 3: Test .notFound resolution directly with expected type MyError
    {
        let mut ctx2 = ElabCtx::new(&env);
        let my_error_ty = Expr::const_(Name::from_string("MyError"), vec![]);
        ctx2.set_expected_type(Some(my_error_ty));
        let surface = parse_expr(".notFound").unwrap();
        let result = ctx2.elaborate(&surface);
        assert!(
            result.is_ok(),
            ".notFound should resolve with expected type MyError, got {result:?}"
        );
    }

    // Test 4: Full def with anonymous constructor argument
    let decl2 = parse_decl_for_elab("def test2 : Except MyError Nat := .error .notFound").unwrap();
    let result2 = crate::elaborate_decl_and_register(&mut env, &decl2);
    assert!(
        result2.is_ok(),
        "Anonymous constructor .error .notFound should resolve for Except MyError Nat, got {result2:?}"
    );
}

/// Track GH: leading-dot constructor in application HEAD position whose
/// expected argument type is an *unresolved metavariable* — recover the
/// inductive from the constructor suffix alone.
///
/// Mirrors the real `TrustIr/Semantics` shape `throw (.typeError msg)`: `throw`
/// has signature `{ε} {m} [MonadExcept ε m] {α} → ε → m α`, so its argument's
/// expected type is the still-open `?ε` (pinned only later by the
/// `MonadExcept` instance). Before the fix, the dot-ctor head `.typeError` saw
/// an expected type whose WHNF head is a metavariable, not a `Const`, and
/// hard-failed with `UnknownIdent(".typeError")`. The suffix-recovery fallback
/// scans registered inductives for a unique owner of a `.typeError`
/// constructor (here `SemErr`) and resolves it; the kernel re-checks the
/// resulting term, so an over-eager match cannot leak unsoundness.
#[test]
fn test_track_gh_leading_dot_ctor_head_meta_expected_type() {
    let mut env = Environment::with_prelude();

    let err_decl = parse_decl_for_elab(
        "inductive SemErr where\n  | ub : String → SemErr\n  | typeError : String → SemErr",
    )
    .unwrap();
    crate::elaborate_decl_and_register(&mut env, &err_decl).expect("SemErr should register");

    let m_decl = parse_decl_for_elab("abbrev M (a : Type) : Type := Except SemErr a").unwrap();
    crate::elaborate_decl_and_register(&mut env, &m_decl).expect("M abbrev should register");

    // `throw (.typeError msg)` — the dot-ctor's expected arg type is `?ε`.
    let decl =
        parse_decl_for_elab("def f (msg : String) : M Nat := throw (.typeError msg)").unwrap();
    let result = crate::elaborate_decl_and_register(&mut env, &decl);
    assert!(
        result.is_ok(),
        "throw (.typeError msg) should resolve via suffix recovery, got {result:?}"
    );
}

/// Track GH: an *ambiguous* leading-dot constructor suffix with no usable
/// expected type must NOT be silently resolved to an arbitrary inductive — the
/// fallback is unambiguous-only and otherwise preserves the prior
/// `UnknownIdent` failure. Guards against the suffix-recovery fallback guessing.
#[test]
fn test_track_gh_leading_dot_ctor_ambiguous_suffix_rejected() {
    let mut env = Environment::with_prelude();

    crate::elaborate_decl_and_register(
        &mut env,
        &parse_decl_for_elab("inductive AaGh where\n  | shared : AaGh").unwrap(),
    )
    .expect("AaGh should register");
    crate::elaborate_decl_and_register(
        &mut env,
        &parse_decl_for_elab("inductive BbGh where\n  | shared : BbGh").unwrap(),
    )
    .expect("BbGh should register");

    // Two inductives own a `.shared` constructor → ambiguous → recovery refuses.
    let mut ctx = ElabCtx::new(&env);
    let meta = ctx.fresh_meta(Expr::type_());
    let resolved = ctx.elab_leading_dot_ctor_with_expected_type(".shared", &meta);
    assert!(
        resolved.is_err(),
        "ambiguous .shared with a metavar expected type must not resolve, got {resolved:?}"
    );
}

/// Track UU: dot notation on a FUNCTION-TYPED field.
///
/// Mirrors `TrustIr.MachineState.lookupValue` / `bindValue` and
/// `Sem.lookupValue`: a struct field whose declared type is a `def` that
/// unfolds to a `Pi` (function) type, plus a method on that struct accessed via
/// dot notation. Before the fix, `s.tbl.get id` and `{ s with tbl := ... }`
/// failed with "cannot extract type name from Pi(...)" because the resolver
/// WHNF'd the receiver type (unfolding the alias to a function type and losing
/// its head), and `s.lookupValue id` failed with "Unknown projection field" on
/// the structure (no fall-through from a missing field to a same-namespace
/// method). Each decl is registered, so the kernel re-checks the resolved term.
#[test]
fn test_track_uu_function_typed_field_dot_notation() {
    let mut env = Environment::with_prelude();

    let decls = [
        // A key type for the table.
        "structure Key where\n  k : Nat",
        // A value carried by the table.
        "inductive Val where | mk : Nat → Val",
        // Function-typed *alias*: `Tbl` unfolds to a Pi. This is the crux.
        "def Tbl := Key → Option Val",
        "def Tbl.empty : Tbl := fun _ => none",
        // Method whose self-slot type (`Tbl`) unfolds to a Pi.
        "def Tbl.get (m : Tbl) (key : Key) : Option Val := m key",
        // `.set` returns the function-typed alias (its codomain unfolds to a
        // Pi). The body intentionally avoids `==`/if-then-else: that path hits a
        // *separate, pre-existing* "contains free variables" registration bug
        // (the same one blocking the real `ValueMap.set`), unrelated to Track UU.
        "def Tbl.set (m : Tbl) (_key : Key) (v : Val) : Tbl := fun _ => some v",
        // Structure with a function-typed field.
        "structure St where\n  tbl : Tbl\n  n : Nat",
        // (A) dot notation on a function-typed FIELD: `s.tbl.get key`.
        "def St.lookup (s : St) (key : Key) : Option Val := s.tbl.get key",
        // (B) function-typed field inside a struct-update literal: `s.tbl.set ...`.
        "def St.store (s : St) (key : Key) (v : Val) : St := { s with tbl := s.tbl.set key v }",
        // (C) method dot-notation on the STRUCT receiver (method, not a field).
        "def St.method (s : St) (key : Key) : Option Val := s.lookup key",
        // (D) genuine field projection must still work.
        "def St.getN (s : St) : Nat := s.n",
    ];

    for src in decls {
        let decl =
            parse_decl_for_elab(src).unwrap_or_else(|e| panic!("parse failed for `{src}`: {e:?}"));
        crate::elaborate_decl_and_register(&mut env, &decl)
            .unwrap_or_else(|e| panic!("elaborate+register failed for `{src}`: {e:?}"));
    }

    // The function-typed-field dot-notation methods are now in the environment,
    // kernel-checked (registration runs `add_decl`).
    for name in ["St.lookup", "St.store", "St.method", "St.getN"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered after Track UU fix"
        );
    }
}

/// Track UU negative guard: a genuinely-unknown struct field still errors with
/// `UnknownProjectionField` (the method fall-through must not swallow real
/// typos). Without this, the structure-method fall-through could mask field
/// errors and degrade diagnostics.
#[test]
fn test_track_uu_unknown_struct_field_still_errors() {
    let mut env = Environment::with_prelude();
    let decl = parse_decl_for_elab("structure Box where\n  x : Nat").unwrap();
    crate::elaborate_decl_and_register(&mut env, &decl).expect("Box should register");

    let err = elab_with_env(&env, "fun (b : Box) => b.totallyMissingField")
        .expect_err("unknown field should still error");
    assert!(
        matches!(err, ElabError::UnknownProjectionField { ref field, .. } if field == "totallyMissingField"),
        "expected UnknownProjectionField for a genuine unknown field, got {err:?}"
    );
}
