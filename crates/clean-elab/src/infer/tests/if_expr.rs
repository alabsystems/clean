// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! If/if-let/if-decidable elaboration tests

use super::*;

fn option_nat_axiom_env(name: &str) -> Environment {
    let mut env = Environment::with_prelude();
    let option_nat = Expr::app(
        Expr::const_(Name::from_string("Option"), vec![Level::zero()]),
        Expr::const_(Name::from_string("Nat"), vec![]),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::app(
            Expr::const_(Name::from_string("Option"), vec![Level::zero()]),
            option_nat,
        ),
    })
    .unwrap();
    env
}

fn count_const_occurrences(expr: &Expr, needle: &str) -> usize {
    match expr.kind() {
        ExprKind::Const(name, _) => usize::from(name.to_string() == needle),
        ExprKind::App(func, arg) => {
            count_const_occurrences(func, needle) + count_const_occurrences(arg, needle)
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            count_const_occurrences(ty, needle) + count_const_occurrences(body, needle)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            count_const_occurrences(ty, needle)
                + count_const_occurrences(val, needle)
                + count_const_occurrences(body, needle)
        }
        _ => 0,
    }
}

fn contains_meta_fvar(expr: &Expr) -> bool {
    match expr.kind() {
        ExprKind::FVar(id) => MetaState::from_fvar(*id).is_some(),
        ExprKind::App(func, arg) => contains_meta_fvar(func) || contains_meta_fvar(arg),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            contains_meta_fvar(ty) || contains_meta_fvar(body)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            contains_meta_fvar(ty) || contains_meta_fvar(val) || contains_meta_fvar(body)
        }
        _ => false,
    }
}

#[test]
fn test_if_let_var_pattern() {
    // if let x := e then t else f
    // Variable patterns are irrefutable, so this optimizes to: let x := e in t
    // (no casesOn needed since the pattern always matches)
    let expr = elab("if let x := 42 then x else 0").unwrap();
    assert!(
        matches!(expr.kind(), ExprKind::Let(_, _, _, _, _)),
        "expected Let for irrefutable if-let var pattern, got {expr:?}"
    );
}

#[test]
fn test_if_let_wildcard_pattern() {
    // if let _ := e then t else f
    // Wildcard patterns are irrefutable, so this optimizes to: let _ := e in t
    // (no casesOn needed since the pattern always matches)
    let expr = elab("if let _ := 42 then 1 else 0").unwrap();
    assert!(
        matches!(expr.kind(), ExprKind::Let(_, _, _, _, _)),
        "expected Let for irrefutable if-let wildcard pattern, got {expr:?}"
    );
}

#[test]
fn test_if_decidable_basic() {
    // if h : p then t else e  desugars to  dite p (fun h => t) (fun h => e)
    // We need a Prop for this, using True which is a valid Prop
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // Build surface expression directly since parsing `if h : True then ...` needs True defined
    let prop = SurfaceExpr::Ident(clean_parser::Span::dummy(), "True".to_string());
    let then_br = SurfaceExpr::Lit(clean_parser::Span::dummy(), SurfaceLit::Nat(1));
    let else_br = SurfaceExpr::Lit(clean_parser::Span::dummy(), SurfaceLit::Nat(0));
    let surface = SurfaceExpr::IfDecidable(
        clean_parser::Span::dummy(),
        "h".to_string(),
        Box::new(prop),
        Box::new(then_br),
        Box::new(else_br),
    );

    // This will fail because True isn't defined in expression context
    // Auto-implicit (#164) only applies in declaration contexts
    let result = ctx.elaborate(&surface);
    // We expect UnknownIdent for "True" since it's not in the empty environment
    assert!(
        matches!(result, Err(ElabError::UnknownIdent(ref name)) if name == "True"),
        "expected UnknownIdent(True), got {result:?}"
    );
}

#[test]
fn test_if_decidable_with_prop_env() {
    // Test if-decidable with the prelude's genuine True/Decidable declarations
    // and canonical Decidable True instance.
    use clean_kernel::expr::ExprKind;
    let env = Environment::with_prelude();

    let mut ctx = ElabCtx::new(&env);

    let prop = SurfaceExpr::Ident(clean_parser::Span::dummy(), "True".to_string());
    let then_br = SurfaceExpr::Lit(clean_parser::Span::dummy(), SurfaceLit::Nat(1));
    let else_br = SurfaceExpr::Lit(clean_parser::Span::dummy(), SurfaceLit::Nat(0));
    let surface = SurfaceExpr::IfDecidable(
        clean_parser::Span::dummy(),
        "h".to_string(),
        Box::new(prop),
        Box::new(then_br),
        Box::new(else_br),
    );

    let result = ctx.elaborate(&surface);
    assert!(result.is_ok(), "if-decidable should elaborate: {result:?}");

    let expr = result.unwrap();
    // Result should be: dite True (fun h => 1) (fun h => 0)
    // Which is an application
    assert!(
        matches!(expr.kind(), ExprKind::App(_, _)),
        "expected App for dite, got {expr:?}"
    );
}

#[test]
fn test_if_decidable_failures_restore_expected_and_branch_locals_for_reuse() {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let outer_expected = Expr::type_();
    ctx.current_expected_type = Some(outer_expected.clone());
    ctx.push_local("outerWitness".to_string(), Expr::prop());
    let locals_before = ctx.locals.clone();

    let ident = |name: &str| SurfaceExpr::Ident(clean_parser::Span::dummy(), name.to_string());
    let true_prop = ident("True");
    let valid_branch = ident("Prop");

    // Failure while elaborating the condition occurs after taking the expected
    // type but before introducing either witness.
    let missing_prop = ident("missingDecidableCondition");
    assert!(ctx
        .elab_if_decidable("h", &missing_prop, &valid_branch, &valid_branch)
        .is_err());
    assert_eq!(ctx.locals, locals_before);
    assert_eq!(ctx.current_expected_type, Some(outer_expected.clone()));

    // Failure in each branch occurs with a different `h` local active.
    let missing_then = ident("missingThenBranch");
    assert!(ctx
        .elab_if_decidable("h", &true_prop, &missing_then, &valid_branch)
        .is_err());
    assert_eq!(ctx.locals, locals_before);
    assert_eq!(ctx.current_expected_type, Some(outer_expected.clone()));
    assert!(ctx.lookup_local("h").is_none());

    let missing_else = ident("missingElseBranch");
    assert!(ctx
        .elab_if_decidable("h", &true_prop, &valid_branch, &missing_else)
        .is_err());
    assert_eq!(ctx.locals, locals_before);
    assert_eq!(ctx.current_expected_type, Some(outer_expected.clone()));
    assert!(ctx.lookup_local("h").is_none());

    // The same context remains usable, and a successful retry also restores
    // the exact surrounding expected/local state.
    let result = ctx
        .elab_if_decidable("h", &true_prop, &valid_branch, &valid_branch)
        .expect("context should remain reusable after decidable-if failures");
    assert!(
        matches!(result.get_app_fn().kind(), ExprKind::Const(name, _) if name.to_string() == "dite")
    );
    assert_eq!(ctx.locals, locals_before);
    assert_eq!(ctx.current_expected_type, Some(outer_expected));
    assert!(ctx.lookup_local("h").is_none());
}

// =========================================================================
// Issue #1702 regression tests: ite and if-let desugaring fixes
// =========================================================================

/// Build an environment with Nat, Decidable, True, and ite for if-expression tests.
///
/// Declares:
/// - `Nat : Type` (axiom, needed for nat literals)
/// - `Decidable : Prop → Type` (axiom, matching Lean 4's data-carrying Decidable)
/// - `True : Prop` (axiom, used as a Prop-valued condition)
/// - `ite.{u} : {α : Sort u} → Prop → [Decidable c] → α → α → α`
fn ite_env() -> Environment {
    use clean_kernel::env::Declaration;
    use clean_kernel::{KernelClassInfo, KernelInstanceInfo};
    let mut env = Environment::new();

    // Nat : Type
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    // Decidable : Prop → Type (data-carrying, lives in Sort 1)
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Decidable"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, Expr::prop(), Expr::type_()),
    })
    .unwrap();
    env.register_class(KernelClassInfo {
        name: Name::from_string("Decidable"),
        num_params: 1,
        out_params: vec![],
        semi_out_params: vec![],
    });

    // True : Prop (so we have a Prop-valued condition for ite)
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("True"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    // ite.{u} : {α : Sort u} → (c : Prop) → [Decidable c] → α → α → α
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());
    let sort_u = Expr::sort(u_level.clone());
    // Build type from inside out:
    //   return type α = bvar(4)
    let body = Expr::bvar(4);
    //   Π (b : α), α  — α is bvar(3) at depth 4
    let pi_b = Expr::pi(BinderInfo::Default, Expr::bvar(3), body);
    //   Π (a : α), ...  — α is bvar(2) at depth 3
    let pi_a = Expr::pi(BinderInfo::Default, Expr::bvar(2), pi_b);
    //   Π [h : Decidable c], ...  — c is bvar(0) at depth 2 (bindings: α, c)
    let decidable_c = Expr::app(
        Expr::const_(Name::from_string("Decidable"), vec![]),
        Expr::bvar(0),
    );
    let pi_h = Expr::pi(BinderInfo::InstImplicit, decidable_c, pi_a);
    //   Π (c : Prop), ...
    let pi_c = Expr::pi(BinderInfo::Default, Expr::prop(), pi_h);
    //   Π {α : Sort u}, ...
    let ite_type = Expr::pi(BinderInfo::Implicit, sort_u, pi_c);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("ite"),
        level_params: vec![u],
        type_: ite_type,
    })
    .unwrap();

    // Shape tests below need genuine evidence for their `True` condition.
    // Register an explicit test axiom as the Decidable instance; the production
    // elaborator must never fill this slot with a synthetic sorry.
    let inst_name = Name::from_string("instDecidableTrueForIfTest");
    let inst_ty = Expr::app(
        Expr::const_(Name::from_string("Decidable"), vec![]),
        Expr::const_(Name::from_string("True"), vec![]),
    );
    env.add_decl(Declaration::Axiom {
        name: inst_name.clone(),
        level_params: vec![],
        type_: inst_ty.clone(),
    })
    .unwrap();
    env.register_instance(KernelInstanceInfo {
        name: inst_name.clone(),
        class_name: Name::from_string("Decidable"),
        priority: 1000,
        type_: Some(inst_ty),
        value: Some(Expr::const_(inst_name, vec![])),
    });

    env
}

/// Issue #1702 finding #4: ite desugaring must produce 5-arg application
/// (@ite α cond decidable_inst then else), not 3-arg (ite cond then else).
///
/// Macro expansion converts SurfaceExpr::If to App(Ident("ite"), [cond, then, else]).
/// The elaborator's elab_app inserts implicit α and [Decidable c] arguments,
/// producing 5 total applications. This test verifies the full elaboration path.
#[test]
fn test_issue1702_ite_has_five_args() {
    use clean_parser::{Span, SurfaceExpr, SurfaceLit};

    let env = ite_env();
    let mut ctx = ElabCtx::new(&env);

    // Build: if True then 1 else 0
    // True is Prop-valued, matching ite's (c : Prop) parameter.
    let cond = Box::new(SurfaceExpr::Ident(Span::dummy(), "True".to_string()));
    let then_br = Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1)));
    let else_br = Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)));
    let surface = SurfaceExpr::If(Span::dummy(), cond, then_br, else_br);

    let expr = ctx
        .elaborate(&surface)
        .expect("if-expression should elaborate in regression test");

    // Count the number of App nodes in the spine (should be 5 for @ite)
    let mut count = 0u32;
    let mut curr = &expr;
    while let ExprKind::App(func, _) = curr.kind() {
        count += 1;
        curr = func;
    }
    // @ite α cond inst then else = exactly 5 applications
    assert_eq!(
        count, 5,
        "ite should have exactly 5 args (α, cond, inst, then, else), got {count} apps in: {expr:?}"
    );
    // Head should be a Const named "ite"
    assert!(
        matches!(curr.kind(), ExprKind::Const(n, _) if n.to_string() == "ite"),
        "head of ite application should be Const(ite), got: {curr:?}"
    );
}

/// Build an environment with Nat (axiom) and MyOpt (myNone | mySome) inductive type.
fn my_opt_env() -> Option<Environment> {
    use clean_kernel::env::Declaration;
    use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
    let mut env = Environment::new();

    // Nat : Type (needed so nat literals can type-check)
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .ok()?;
    let my_opt = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("MyOpt"),
            type_: Expr::pi(BinderInfo::Implicit, Expr::type_(), Expr::type_()),
            constructors: vec![
                Constructor {
                    name: Name::from_string("MyOpt.myNone"),
                    type_: Expr::pi(
                        BinderInfo::Implicit,
                        Expr::type_(),
                        Expr::app(
                            Expr::const_(Name::from_string("MyOpt"), vec![]),
                            Expr::bvar(0),
                        ),
                    ),
                },
                Constructor {
                    name: Name::from_string("MyOpt.mySome"),
                    type_: Expr::pi(
                        BinderInfo::Implicit,
                        Expr::type_(),
                        Expr::pi(
                            BinderInfo::Default,
                            Expr::bvar(0),
                            Expr::app(
                                Expr::const_(Name::from_string("MyOpt"), vec![]),
                                Expr::bvar(1),
                            ),
                        ),
                    ),
                },
            ],
        }],
    };
    env.add_inductive(my_opt).ok()?;
    Some(env)
}

/// Issue #1702 finding #2: if-let Ctor pattern must use constructor index
/// to place casesOn alternatives, not hardcode else-first/ctor-second.
///
/// Macro expansion converts IfLet to Match, then elab_match builds casesOn.
/// casesOn arg order: motive → alt_ctor0 → alt_ctor1 → … → major (scrutinee).
/// Matching myNone (ctor 0) with then-branch must place then at alt_ctor0.
#[test]
fn test_issue1702_if_let_ctor_uses_constructor_index() {
    use clean_kernel::{BigNat, Literal};
    use clean_parser::{Span, SurfaceArg, SurfaceExpr, SurfaceLit, SurfacePattern};

    let env = my_opt_env().expect("MyOpt inductive registration should succeed in regression test");

    // Use mySome on the scrutinee so infer_type has concrete data for MyOpt α.
    let scrutinee = Box::new(SurfaceExpr::App(
        Span::dummy(),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            "MyOpt.mySome".to_string(),
        )),
        vec![SurfaceArg::positional(SurfaceExpr::Lit(
            Span::dummy(),
            SurfaceLit::Nat(7),
        ))],
    ));
    let then_br = Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1)));
    let else_br = Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)));
    // Match the FIRST constructor in MyOpt to distinguish correct ctor-index placement:
    // - Correct ordering: alt_ctor0=then, alt_ctor1=else (possibly lambda-wrapped)
    // - Regressed hardcoded ordering would swap these positions
    let pat = SurfacePattern::Ctor("myNone".to_string(), vec![]);
    let surface = SurfaceExpr::IfLet(Span::dummy(), pat, scrutinee, then_br, else_br);

    let mut ctx = ElabCtx::new(&env);
    let expr = ctx
        .elaborate(&surface)
        .expect("if-let constructor regression test must elaborate");

    // Flatten ((head arg0) arg1 ... argN) into head + args.
    let mut args: Vec<&Expr> = Vec::new();
    let mut curr = &expr;
    while let ExprKind::App(func, arg) = curr.kind() {
        args.push(arg.as_ref());
        curr = func.as_ref();
    }
    args.reverse();

    assert!(
        matches!(curr.kind(), ExprKind::Const(n, _) if n.to_string() == "MyOpt.casesOn"),
        "if-let ctor should elaborate to MyOpt.casesOn, got head: {curr:?}"
    );
    // casesOn args (Lean-faithful layout): {α} (implicit), motive, scrutinee
    // (major premise), alt_myNone (ctor 0), alt_mySome (ctor 1).
    // The implicit type parameter α is inserted by elab_app for the recursor.
    assert!(
        args.len() >= 5,
        "MyOpt.casesOn needs at least α + motive + scrutinee + 2 alts, got {} args: {expr:?}",
        args.len()
    );

    // args[0] = α (implicit type param), args[1] = motive,
    // args[2] = scrutinee (major premise — Lean-faithful casesOn order),
    // args[3] = alt for myNone (ctor 0), args[4] = alt for mySome (ctor 1).
    //
    // myNone (ctor 0) alternative should contain then-branch value (1).
    // myNone is nullary, so its casesOn alternative is the bare body.
    let alt_my_none = args[3];
    assert!(
        matches!(
            alt_my_none.kind(),
            ExprKind::Lit(Literal::Nat(BigNat::Small(1)))
        ),
        "constructor-index ordering regression: alt for myNone (ctor 0) should be then-branch 1, \
         got: {alt_my_none:?}"
    );

    // mySome (ctor 1) alternative should contain else-branch value (0).
    // mySome takes a field, so its casesOn alternative is a lambda wrapping the body.
    let alt_my_some = args[4];
    fn extract_lambda_body(e: &Expr) -> &Expr {
        match e.kind() {
            ExprKind::Lam(_, _, body) => body.as_ref(),
            _ => e,
        }
    }
    let else_body = extract_lambda_body(alt_my_some);
    assert!(
        matches!(
            else_body.kind(),
            ExprKind::Lit(Literal::Nat(BigNat::Small(0)))
        ),
        "constructor-index ordering regression: alt for mySome (ctor 1) body should be \
         else-branch 0, got alt: {alt_my_some:?}"
    );
}

/// Issue #1719 originally fixed stale field-type extraction for excess
/// sub-patterns. After #796 constructor-arity hardening, the same shape must
/// now fail closed before any fallback typing happens.
#[test]
fn test_issue1719_if_let_excess_subpats_return_ctor_arity_mismatch() {
    use clean_parser::{Span, SurfaceArg, SurfaceExpr, SurfaceLit, SurfacePattern};

    let env = my_opt_env().expect("MyOpt inductive registration should succeed");

    // Scrutinee: MyOpt.mySome 7
    let scrutinee = Box::new(SurfaceExpr::App(
        Span::dummy(),
        Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            "MyOpt.mySome".to_string(),
        )),
        vec![SurfaceArg::positional(SurfaceExpr::Lit(
            Span::dummy(),
            SurfaceLit::Nat(7),
        ))],
    ));
    let then_br = Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1)));
    let else_br = Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)));

    // Pattern with 2 sub-patterns when mySome only has 1 field.
    // This should now fail closed with ConstructorPatternArityMismatch.
    let pat = SurfacePattern::Ctor(
        "mySome".to_string(),
        vec![
            SurfacePattern::Var("x".to_string()),
            SurfacePattern::Var("y".to_string()),
        ],
    );
    let surface = SurfaceExpr::IfLet(Span::dummy(), pat, scrutinee, then_br, else_br);

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        matches!(
            result,
            Err(ElabError::ConstructorPatternArityMismatch {
                ref ctor_name,
                expected: 1,
                actual: 2,
                ..
            }) if ctor_name == "MyOpt.mySome"
        ),
        "expected constructor arity mismatch for if-let MyOpt.mySome pattern, got {result:?}"
    );
}

#[test]
fn test_if_let_ctor_nested_literal_pattern_elaborates() {
    use clean_parser::{Span, SurfaceExpr, SurfaceLit, SurfacePattern};

    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();

    let surface = SurfaceExpr::IfLet(
        Span::dummy(),
        SurfacePattern::Ctor(
            "Nat.succ".to_string(),
            vec![SurfacePattern::Lit(SurfaceLit::Nat(0))],
        ),
        Box::new(SurfaceExpr::Ident(Span::dummy(), "n".to_string())),
        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1))),
        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "expected nested ctor literal if-let pattern to elaborate via nested casesOn, got {result:?}"
    );
}

/// Nat.succ(k + 1) in if-let desugars to nested casesOn targeting Nat.succ (#796).
#[test]
fn test_if_let_ctor_nested_numeral_add_pattern_elaborates() {
    use clean_parser::{Span, SurfaceExpr, SurfaceLit, SurfacePattern};

    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();

    let surface = SurfaceExpr::IfLet(
        Span::dummy(),
        SurfacePattern::Ctor(
            "Nat.succ".to_string(),
            vec![SurfacePattern::NumeralAdd(
                Box::new(SurfacePattern::Var("k".to_string())),
                1,
            )],
        ),
        Box::new(SurfaceExpr::Ident(Span::dummy(), "n".to_string())),
        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1))),
        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "Nat.succ(k + 1) nested ctor numeral-add if-let pattern should elaborate with nested casesOn, got {result:?}"
    );
}

#[test]
fn test_if_let_recursive_nested_ctor_pattern_typechecks() {
    use clean_parser::{Span, SurfaceExpr, SurfaceLit, SurfacePattern};

    let env = option_nat_axiom_env("opt");
    let surface = SurfaceExpr::IfLet(
        Span::dummy(),
        SurfacePattern::Ctor(
            "Option.some".to_string(),
            vec![SurfacePattern::Ctor(
                "Option.some".to_string(),
                vec![SurfacePattern::Var("x".to_string())],
            )],
        ),
        Box::new(SurfaceExpr::Ident(Span::dummy(), "opt".to_string())),
        Box::new(SurfaceExpr::Ident(Span::dummy(), "x".to_string())),
        Box::new(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0))),
    );

    let mut ctx = ElabCtx::new(&env);
    let result = ctx
        .elaborate(&surface)
        .expect("recursive nested ctor if-let should elaborate");
    let result_ty = ctx
        .infer_type(&result)
        .expect("recursive nested ctor if-let should produce a well-typed term");

    assert!(
        ctx.is_def_eq(&result_ty, &Expr::const_(Name::from_string("Nat"), vec![])),
        "expected recursive nested ctor if-let to have type Nat, got {result_ty:?}"
    );
    assert!(
        count_const_occurrences(&result, "Option.casesOn") >= 2,
        "expected recursive nested ctor if-let to lower through two Option.casesOn layers, got {result:?}"
    );
}

// =========================================================================
// Issue #2786 regression: enum-valued if branches must share a result type
// =========================================================================

/// Build an environment with Ordering (inductive), Decidable, True, and ite
/// for testing enum-valued if-expression branches.
fn ordering_ite_env() -> Environment {
    let mut env = ite_env();

    // Add Ordering as an inductive type with lt, eq, gt constructors.
    env.init_ordering()
        .expect("Ordering inductive registration should succeed");

    env
}

/// Issue #2786: if-expression with enum-valued branches (Ordering.eq / Ordering.gt)
/// must elaborate successfully by sharing a common result type across both branches.
///
/// Before the fix, `elab_if` elaborated branches in isolation, which caused
/// `ExpectedSort(Const("Ordering"))` when branches were bare enum constructors
/// because no shared type constraint was propagated.
#[test]
fn test_issue2786_if_enum_valued_branches_share_result_type() {
    use clean_parser::{Span, SurfaceExpr};

    let env = ordering_ite_env();
    let mut ctx = ElabCtx::new(&env);

    // Build: if True then Ordering.eq else Ordering.gt
    let cond = Box::new(SurfaceExpr::Ident(Span::dummy(), "True".to_string()));
    let then_br = Box::new(SurfaceExpr::Ident(Span::dummy(), "Ordering.eq".to_string()));
    let else_br = Box::new(SurfaceExpr::Ident(Span::dummy(), "Ordering.gt".to_string()));
    let surface = SurfaceExpr::If(Span::dummy(), cond, then_br, else_br);

    let expr = ctx
        .elaborate(&surface)
        .expect("if with enum-valued branches should elaborate (#2786)");

    // The result should be an ite application.
    let mut args: Vec<&Expr> = Vec::new();
    let mut curr = &expr;
    while let ExprKind::App(func, arg) = curr.kind() {
        args.push(arg.as_ref());
        curr = func.as_ref();
    }
    args.reverse();

    assert!(
        matches!(curr.kind(), ExprKind::Const(n, _) if n.to_string() == "ite"),
        "head of if-expression should be Const(ite), got: {curr:?}"
    );
    // @ite α cond inst then else = exactly 5 applications
    assert_eq!(
        args.len(),
        5,
        "ite should have 5 args (α, cond, inst, then, else), got {} in: {expr:?}",
        args.len()
    );

    // The first arg (α) should be Ordering.
    let alpha = args[0];
    assert!(
        matches!(alpha.kind(), ExprKind::Const(n, _) if n.to_string() == "Ordering"),
        "result type of enum-valued if should be Ordering, got: {alpha:?}"
    );
}

#[test]
fn test_issue3700_forall_if_enum_equality_type_elaborates() {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);

    let surface = parse_expr(
        "∀ (m n : Nat), (if m = n then Ordering.eq else Ordering.gt) = Ordering.lt → False",
    )
    .expect("1079-style enum-valued if theorem type should parse");

    let expr = ctx
        .elaborate(&surface)
        .expect("1079-style enum-valued if theorem type should elaborate");
    let ty = ctx
        .infer_type(&expr)
        .expect("1079-style enum-valued if theorem type should have a type");

    assert!(
        matches!(ty.kind(), ExprKind::Sort(Level::Zero)),
        "1079-style theorem type should elaborate as a proposition, got type {ty:?}"
    );
    assert!(
        !contains_meta_fvar(&expr),
        "1079-style theorem type should not retain unresolved Decidable metavariables: {expr:?}"
    );
}

/// E2E (Task 2): `if ((5 : UInt8) = (5 : UInt8)) then 1 else 0` elaborates by
/// RESOLVING a `Decidable (Eq UInt8 …)` instance — NO synthetic `sorryAx` in the
/// decidable position. Before the `instDecidableEqUInt8` registration (backed by
/// the real `UInt8.decEq` term), `resolve_decidable` fell through to a synthetic
/// sorry. This is the headline acceptance test.
#[test]
fn test_if_uint8_eq_resolves_instance_no_sorry() {
    let env = Environment::with_prelude();
    let expr = elab_with_env(
        &env,
        "if ((5 : UInt8) = (5 : UInt8)) then (1 : Nat) else (0 : Nat)",
    )
    .expect("UInt8 if-eq should elaborate");

    // The sound decision procedure must appear; the synthetic sorry must not.
    assert_eq!(
        count_const_occurrences(&expr, "sorryAx"),
        0,
        "UInt8 if-eq must NOT emit a synthetic sorry: {expr:?}"
    );
    let dispatches_real = count_const_occurrences(&expr, "UInt8.decEq") > 0
        || count_const_occurrences(&expr, "instDecidableEqUInt8") > 0;
    assert!(
        dispatches_real,
        "UInt8 if-eq must dispatch via the real UInt8.decEq / instDecidableEqUInt8 instance: {expr:?}"
    );

    // The whole elaborated term type-checks (no unresolved metas, real instance).
    let ctx = ElabCtx::new(&env);
    let ty = ctx
        .infer_type(&expr)
        .expect("UInt8 if-eq elaborated term should type-check");
    assert!(
        !contains_meta_fvar(&expr),
        "UInt8 if-eq must not retain unresolved Decidable metavariables: {expr:?}"
    );
    let _ = ty;
}

/// Regression: Nat if-eq still resolves the real `Nat.decEq` instance (no sorry),
/// alongside the new UInt8 path.
#[test]
fn test_if_nat_eq_still_resolves_instance_no_sorry() {
    let env = Environment::with_prelude();
    let expr = elab_with_env(
        &env,
        "if ((5 : Nat) = (5 : Nat)) then (1 : Nat) else (0 : Nat)",
    )
    .expect("Nat if-eq should elaborate");
    assert_eq!(
        count_const_occurrences(&expr, "sorryAx"),
        0,
        "Nat if-eq must NOT emit a synthetic sorry: {expr:?}"
    );
}

fn opaque_prop_env() -> Environment {
    use clean_kernel::env::Declaration;

    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("OpaqueP"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("register opaque proposition without a Decidable instance");
    env
}

#[test]
#[serial_test::serial]
fn plain_if_missing_decidable_fails_without_synthetic_sorry() {
    use clean_kernel::sorry::{reset_sorry_counter, synthetic_sorry_count};

    let env = opaque_prop_env();
    reset_sorry_counter();
    let before = synthetic_sorry_count();
    let err = elab_with_env(&env, "if OpaqueP then (1 : Nat) else (0 : Nat)")
        .expect_err("plain if must reject a missing Decidable instance");
    assert!(
        matches!(err, ElabError::FailedToSynthesize { ref class_name, .. } if class_name == &Name::from_string("Decidable")),
        "expected typed Decidable synthesis failure, got {err:?}"
    );
    assert_eq!(synthetic_sorry_count(), before);
}

#[test]
#[serial_test::serial]
fn dependent_if_missing_decidable_fails_without_synthetic_sorry() {
    use clean_kernel::sorry::{reset_sorry_counter, synthetic_sorry_count};

    let env = opaque_prop_env();
    reset_sorry_counter();
    let before = synthetic_sorry_count();
    let err = elab_with_env(&env, "if h : OpaqueP then (1 : Nat) else (0 : Nat)")
        .expect_err("dependent if must reject a missing Decidable instance");
    assert!(
        matches!(err, ElabError::FailedToSynthesize { ref class_name, .. } if class_name == &Name::from_string("Decidable")),
        "expected typed dependent-if Decidable synthesis failure, got {err:?}"
    );
    assert_eq!(synthetic_sorry_count(), before);
}

#[test]
fn conditionals_reject_type_valued_guards_before_instance_synthesis() {
    let env = Environment::with_prelude();
    for source in [
        "if Type then (1 : Nat) else (0 : Nat)",
        "if h : Type then (1 : Nat) else (0 : Nat)",
    ] {
        let err = elab_with_env(&env, source)
            .expect_err("a type-valued expression is neither Bool nor a proposition");
        assert!(
            matches!(err, ElabError::TypeMismatch { ref expected, .. } if expected.contains("condition") || expected.contains("guard")),
            "{source} must fail at condition classification, got {err:?}"
        );
    }
}
