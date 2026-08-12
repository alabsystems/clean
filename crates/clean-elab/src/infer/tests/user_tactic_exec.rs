// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end execution tests for user-defined `elab ... : tactic => <body>`
//! tactics (metaprogramming Phase 1, Option B — substitute-and-delegate).
//!
//! These tests register a user tactic via an `elab` declaration, then invoke it
//! in a `by` proof and verify the resulting proof term kernel-checks (no `sorry`,
//! correct type). They also pin the soundness boundary: a tactic must NOT close a
//! goal it does not legitimately discharge, and a deferred body shape errors
//! honestly rather than fabricating a success.

use super::*;
use clean_parser::parse_expr_with_tactics;

/// Build an environment with `P, Q : Prop` and `hP : P`, plus the foundational
/// pieces tactics rely on.
fn prop_env() -> Environment {
    let mut env = Environment::new();
    env.init_true_false().expect("init_true_false");

    for prop in ["P", "Q"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(prop),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect("add prop axiom");
    }
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hP"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("P"), vec![]),
    })
    .expect("add hP axiom");
    env
}

/// Build an environment with `P, Q : Prop`, `hP : P`, and `f : P → Q`, so a
/// user tactic can build the brand-new term `f hP : Q` at tactic runtime.
fn prop_fn_env() -> Environment {
    let mut env = prop_env();
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("f"),
        level_params: vec![],
        type_: Expr::arrow(p, q),
    })
    .expect("add f axiom");
    env
}

/// Register a tactic-category `elab` declaration into the context, returning
/// nothing — the side effect is the registered handler in `ctx.tactic_registry`.
fn register_elab(ctx: &mut ElabCtx, src: &str) {
    let patterns = ctx.tactic_registry.tactic_patterns();
    let decl = parse_decl_with_tactics(src, &patterns).expect("elab decl should parse");
    ctx.elab_decl(&decl).expect("elab decl should elaborate");
}

/// Parse a `by ...` proof against the context's current tactic patterns.
fn parse_by(ctx: &ElabCtx, src: &str) -> Vec<clean_parser::SurfaceTactic> {
    let patterns = ctx.tactic_registry.tactic_patterns();
    let surface = parse_expr_with_tactics(src, &patterns).expect("by-tactic proof should parse");
    let SurfaceExpr::ByTactic(_, tactics) = surface else {
        panic!("expected ByTactic, got {surface:?}");
    };
    tactics
}

/// `elab "myexact" e:term : tactic => exact e` must close a goal it should,
/// and the resulting proof term must kernel-check (sorry-free, correct type).
#[test]
fn test_user_tactic_myexact_closes_goal_and_kernel_checks() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(&mut ctx, r#"elab "myexact" e:term : tactic => exact e"#);

    let p = Expr::const_(Name::from_string("P"), vec![]);
    ctx.current_expected_type = Some(p.clone());

    let tactics = parse_by(&ctx, "by myexact hP");
    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("user tactic `myexact hP` should close goal `P`");

    assert!(
        !proof.has_fvar_quick(),
        "user-tactic proof should be closed (no residual FVars): {proof:?}"
    );
    let proof_ty = ctx
        .infer_type(&proof)
        .expect("user-tactic proof should have an inferable (kernel-checkable) type");
    assert!(
        ctx.is_def_eq(&proof_ty, &p),
        "user-tactic proof should have type `P`, got {proof_ty:?}"
    );
}

/// A flat tactic SEQUENCE body — `elab "trivP" : tactic => intro h; exact h` —
/// must run end-to-end and close `P → P` with a kernel-checkable proof.
#[test]
fn test_user_tactic_sequence_body_runs_and_kernel_checks() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(&mut ctx, r#"elab "trivP" : tactic => intro h; exact h"#);

    // Goal: P → P
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let target = Expr::arrow(p.clone(), p.clone());
    ctx.current_expected_type = Some(target.clone());

    let tactics = parse_by(&ctx, "by trivP");
    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("user tactic `trivP` (intro h; exact h) should close `P → P`");

    assert!(
        !proof.has_fvar_quick(),
        "sequence-body proof should be closed: {proof:?}"
    );
    let proof_ty = ctx
        .infer_type(&proof)
        .expect("sequence-body proof should have an inferable type");
    assert!(
        ctx.is_def_eq(&proof_ty, &target),
        "sequence-body proof should have type `P → P`, got {proof_ty:?}"
    );
}

/// Soundness: a user tactic must NOT close a goal it does not legitimately
/// discharge. `myexact hP` applied to goal `Q` (with `hP : P`, `P ≠ Q`) must
/// FAIL — never fabricate a proof of `Q`.
#[test]
fn test_user_tactic_wrong_proof_fails_to_close_goal() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(&mut ctx, r#"elab "myexact" e:term : tactic => exact e"#);

    // Goal is Q, but hP : P. `myexact hP` must not close it.
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    ctx.current_expected_type = Some(q);

    let tactics = parse_by(&ctx, "by myexact hP");
    let result = ctx.elab_by_tactic(&tactics);
    assert!(
        result.is_err(),
        "user tactic must not close goal `Q` with a proof of `P`: {result:?}"
    );
}

/// Phase 2: a `do`-notation tactic body — `elab "mydo" e:term : tactic => do exact e` —
/// must close a goal it should, and the resulting proof term must kernel-check
/// (sorry-free, correct type). The `do` action lowers to `exact e` and delegates
/// to the existing kernel-checked evaluator.
#[test]
fn test_user_tactic_do_action_body_closes_goal_and_kernel_checks() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(&mut ctx, r#"elab "mydo" e:term : tactic => do exact e"#);

    let p = Expr::const_(Name::from_string("P"), vec![]);
    ctx.current_expected_type = Some(p.clone());

    let tactics = parse_by(&ctx, "by mydo hP");
    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("`do exact e` user tactic should close goal `P`");

    assert!(
        !proof.has_fvar_quick(),
        "do-body proof should be closed (no residual FVars): {proof:?}"
    );
    let proof_ty = ctx
        .infer_type(&proof)
        .expect("do-body proof should have an inferable (kernel-checkable) type");
    assert!(
        ctx.is_def_eq(&proof_ty, &p),
        "do-body proof should have type `P`, got {proof_ty:?}"
    );
}

/// Phase 2: a `do`-block tactic SEQUENCE — `elab "mydo" : tactic => do intro h; exact h` —
/// must run end-to-end and close `P → P` with a kernel-checkable proof, exactly
/// like the flat-sequence Phase 1 form.
#[test]
fn test_user_tactic_do_sequence_body_runs_and_kernel_checks() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(&mut ctx, "elab \"mydo\" : tactic => do intro h; exact h");

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let target = Expr::arrow(p.clone(), p.clone());
    ctx.current_expected_type = Some(target.clone());

    let tactics = parse_by(&ctx, "by mydo");
    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("`do intro h; exact h` user tactic should close `P → P`");

    assert!(
        !proof.has_fvar_quick(),
        "do-sequence proof should be closed: {proof:?}"
    );
    let proof_ty = ctx
        .infer_type(&proof)
        .expect("do-sequence proof should have an inferable type");
    assert!(
        ctx.is_def_eq(&proof_ty, &target),
        "do-sequence proof should have type `P → P`, got {proof_ty:?}"
    );
}

/// Phase 2: a pure value `let` inside a `do` block —
/// `elab "mydo" : tactic => do let x := hP; exact x` — binds `x` to `hP` for the
/// remainder of the block (no tactic effect), so `exact x` becomes `exact hP`
/// and closes `P` with a kernel-checkable proof.
#[test]
fn test_user_tactic_do_pure_let_binding_closes_goal() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        "elab \"mydo\" : tactic => do let x := hP; exact x",
    );

    let p = Expr::const_(Name::from_string("P"), vec![]);
    ctx.current_expected_type = Some(p.clone());

    let tactics = parse_by(&ctx, "by mydo");
    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("`do let x := hP; exact x` should close goal `P`");

    assert!(
        !proof.has_fvar_quick(),
        "pure-let do-body proof should be closed: {proof:?}"
    );
    let proof_ty = ctx
        .infer_type(&proof)
        .expect("pure-let do-body proof should have an inferable type");
    assert!(
        ctx.is_def_eq(&proof_ty, &p),
        "pure-let do-body proof should have type `P`, got {proof_ty:?}"
    );
}

/// Phase 2: the threadable `let h <- intro` value bind —
/// `elab "mydo" : tactic => do let h <- intro; exact h` — threads the introduced
/// hypothesis name `h` into a later `exact h`, closing `P → P` with a
/// kernel-checkable proof.
#[test]
fn test_user_tactic_do_intro_value_bind_closes_goal() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        "elab \"mydo\" : tactic => do let h <- intro; exact h",
    );

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let target = Expr::arrow(p.clone(), p.clone());
    ctx.current_expected_type = Some(target.clone());

    let tactics = parse_by(&ctx, "by mydo");
    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("`do let h <- intro; exact h` should close `P → P`");

    assert!(
        !proof.has_fvar_quick(),
        "intro-value-bind do-body proof should be closed: {proof:?}"
    );
    let proof_ty = ctx
        .infer_type(&proof)
        .expect("intro-value-bind do-body proof should have an inferable type");
    assert!(
        ctx.is_def_eq(&proof_ty, &target),
        "intro-value-bind do-body proof should have type `P → P`, got {proof_ty:?}"
    );
}

/// Soundness (Phase 2): a `do`-body user tactic must NOT close a goal it does not
/// legitimately discharge. `mydo hP` (lowering to `exact hP`) applied to goal `Q`
/// (with `hP : P`, `P ≠ Q`) must FAIL — never fabricate a proof of `Q`.
#[test]
fn test_user_tactic_do_body_wrong_proof_fails_to_close_goal() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(&mut ctx, r#"elab "mydo" e:term : tactic => do exact e"#);

    let q = Expr::const_(Name::from_string("Q"), vec![]);
    ctx.current_expected_type = Some(q);

    let tactics = parse_by(&ctx, "by mydo hP");
    let result = ctx.elab_by_tactic(&tactics);
    assert!(
        result.is_err(),
        "do-body user tactic must not close goal `Q` with a proof of `P`: {result:?}"
    );
}

/// Phase 3: runtime sub-expression elaboration. The body
/// `do let x := f e; exact x` builds the BRAND-NEW term `f e` (a function
/// application not present in the call-site syntax), elaborates it at tactic
/// runtime against the current goal, and closes `Q` with that kernel term.
/// The resulting proof must kernel-check (sorry-free, type `Q`).
#[test]
fn test_user_tactic_runtime_elaborates_application_and_closes_goal() {
    let env = prop_fn_env();
    let mut ctx = ElabCtx::new(&env);

    // `do let x := f e; exact x`: the let RHS `f e` is elaborated at runtime to a
    // kernel term, then `exact x` closes the goal via the kernel-checked bridge.
    register_elab(
        &mut ctx,
        r#"elab "applyf" e:term : tactic => do let x := f e; exact x"#,
    );

    // Confirm the executable (runtime) handler is registered, not just the
    // honest-error simple handler.
    assert!(
        ctx.tactic_registry.get_compound("applyf").is_some(),
        "runtime-elaboration body must register an executable compound handler"
    );

    // Goal: Q, closed by `f hP : Q` built at runtime.
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    ctx.current_expected_type = Some(q.clone());

    let tactics = parse_by(&ctx, "by applyf hP");
    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("`do let x := f e; exact x` should close goal `Q` with `f hP`");

    assert!(
        !proof.has_fvar_quick(),
        "runtime-elaboration proof should be closed (no residual FVars): {proof:?}"
    );
    let proof_ty = ctx
        .infer_type(&proof)
        .expect("runtime-elaboration proof should have an inferable (kernel-checkable) type");
    assert!(
        ctx.is_def_eq(&proof_ty, &q),
        "runtime-elaboration proof should have type `Q`, got {proof_ty:?}"
    );
}

/// Soundness (Phase 3): the runtime-elaboration path must NOT close a goal it
/// does not legitimately discharge. `do let x := e; exact x` with `e = hP`
/// (`hP : P`) applied to goal `Q` (`P ≠ Q`) must FAIL — the elaborated term is
/// type-checked against the goal by the kernel-checked refine bridge and is
/// rejected, never fabricating a proof of `Q`.
#[test]
fn test_user_tactic_runtime_elab_wrong_proof_fails_to_close_goal() {
    let env = prop_fn_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "rtbind" e:term : tactic => do let x := e; exact x"#,
    );

    // Goal is Q, but `e = hP : P`. The runtime-elaborated `x = hP` must not close Q.
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    ctx.current_expected_type = Some(q);

    let tactics = parse_by(&ctx, "by rtbind hP");
    let result = ctx.elab_by_tactic(&tactics);
    assert!(
        result.is_err(),
        "runtime-elaboration tactic must not close goal `Q` with a proof of `P`: {result:?}"
    );
}

/// Phase 3: the runtime path also accepts `refine` as its terminal close.
/// `do let x := f e; refine x` builds `f e` at runtime and closes `Q`.
#[test]
fn test_user_tactic_runtime_elab_refine_terminal_closes_goal() {
    let env = prop_fn_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "refinef" e:term : tactic => do let x := f e; refine x"#,
    );

    let q = Expr::const_(Name::from_string("Q"), vec![]);
    ctx.current_expected_type = Some(q.clone());

    let tactics = parse_by(&ctx, "by refinef hP");
    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("`do let x := f e; refine x` should close goal `Q` with `f hP`");

    assert!(
        !proof.has_fvar_quick(),
        "runtime refine-terminal proof should be closed: {proof:?}"
    );
    let proof_ty = ctx
        .infer_type(&proof)
        .expect("runtime refine-terminal proof should have an inferable type");
    assert!(
        ctx.is_def_eq(&proof_ty, &q),
        "runtime refine-terminal proof should have type `Q`, got {proof_ty:?}"
    );
}

/// Phase 2 boundary: a deferred `do`-body shape — a `for` loop (control flow) —
/// must NOT register an executable handler; invoking it errors HONESTLY through
/// the simple unsupported handler, never fabricating a success.
#[test]
fn test_user_tactic_do_control_flow_body_deferred_errors_honestly() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    // A `do` body with a `for` loop is control flow (deferred). It parses as a
    // ByTactic([Term(Do([For(..)]))]), which `is_executable_tactic_body`
    // rejects, so only the honest-error simple handler is registered.
    register_elab(
        &mut ctx,
        "elab \"mydofor\" : tactic => do for x in xs do exact x",
    );

    assert!(
        ctx.tactic_registry.get_compound("mydofor").is_none(),
        "control-flow do-body tactic must NOT register an executable handler (deferred)"
    );

    let entry = ctx
        .tactic_registry
        .get("mydofor")
        .cloned()
        .expect("deferred tactic still registers a simple entry for parsing");
    let mut ps = crate::tactic::ProofState::new(Environment::new(), Expr::prop());
    let err = (entry.handler)(&mut ps, &[])
        .expect_err("deferred control-flow do-body handler must error honestly");
    assert!(
        matches!(err, crate::tactic::TacticError::ElaborationFailed { .. }),
        "deferred control-flow body should surface ElaborationFailed, got {err:?}"
    );
}

/// A deferred (unsupported) body shape — a bare `do`-notation monadic body that
/// is NOT wrapped in a `by` tactic block — is not handled by the executable
/// bridge, so no compound handler is registered. Invoking it must error HONESTLY
/// (the simple unsupported handler fires), never fabricating a success.
#[test]
fn test_user_tactic_deferred_do_body_errors_honestly() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    // A `do` body is the deferred monadic shape (Phase 2+). It parses as a
    // SurfaceExpr::Do, not a ByTactic, so only the honest-error simple handler
    // is registered.
    let decl = SurfaceDecl::Elab {
        span: clean_parser::Span::dummy(),
        pattern: vec![
            clean_parser::SyntaxPatternItem::Literal("mydo".to_owned()),
            clean_parser::SyntaxPatternItem::Variable {
                name: "e".to_owned(),
                category: Some("term".to_owned()),
            },
        ],
        category: "tactic".to_owned(),
        body: Box::new(SurfaceExpr::Do(clean_parser::Span::dummy(), vec![])),
    };
    ctx.elab_decl(&decl).expect("deferred elab decl elaborates");

    // No compound handler should be registered for the deferred shape.
    assert!(
        ctx.tactic_registry.get_compound("mydo").is_none(),
        "do-body tactic must NOT register an executable handler (deferred)"
    );

    // The simple handler must report an honest error, never success.
    let entry = ctx
        .tactic_registry
        .get("mydo")
        .cloned()
        .expect("deferred tactic still registers a simple entry for parsing");
    let mut ps = crate::tactic::ProofState::new(Environment::new(), Expr::prop());
    let arg = Expr::const_str("hP");
    let err = (entry.handler)(&mut ps, std::slice::from_ref(&arg))
        .expect_err("deferred do-body handler must error honestly, not fabricate success");
    assert!(
        matches!(err, crate::tactic::TacticError::ElaborationFailed { .. }),
        "deferred body should surface ElaborationFailed, got {err:?}"
    );
}

// ===========================================================================
// Phase 6: variadic (trailing-repetition) user tactics
// ===========================================================================

/// Build an environment with `P, Q, R : Prop`, `hP : P`, and `hR : R`, for
/// variadic `intro`-style tactics over multi-arrow goals.
fn prop3_env() -> Environment {
    let mut env = prop_env();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("R"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("add R axiom");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hR"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("R"), vec![]),
    })
    .expect("add hR axiom");
    env
}

/// Phase 6: a variadic user tactic `elab "intros2" xs:ident* : tactic => intro xs`
/// invoked with TWO arguments (`intros2 a b`) must expand to `intro a; intro b`,
/// introducing both binders of `P → Q → R`; the trailing `exact hR` then closes
/// goal `R` with a kernel-checkable proof. This pins both the 2-arg expansion
/// and the end-to-end kernel close.
#[test]
fn test_variadic_user_tactic_two_idents_expands_and_kernel_checks() {
    let env = prop3_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(&mut ctx, r#"elab "intros2" xs:ident* : tactic => intro xs"#);

    // A compound (variadic) handler must be registered.
    assert!(
        ctx.tactic_registry.get_compound("intros2").is_some(),
        "variadic user tactic should register a compound handler"
    );

    // Goal: P → Q → R. `intros2 a b` -> `intro a; intro b` introduces a:P, b:Q,
    // leaving goal R; `exact hR` discharges it.
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let r = Expr::const_(Name::from_string("R"), vec![]);
    let target = Expr::arrow(p, Expr::arrow(q, r));
    ctx.current_expected_type = Some(target.clone());

    let tactics = parse_by(&ctx, "by intros2 a b; exact hR");
    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("`intros2 a b; exact hR` should close `P → Q → R`");

    assert!(
        !proof.has_fvar_quick(),
        "two-ident variadic proof should be closed: {proof:?}"
    );
    let proof_ty = ctx
        .infer_type(&proof)
        .expect("two-ident variadic proof should have an inferable type");
    assert!(
        ctx.is_def_eq(&proof_ty, &target),
        "two-ident variadic proof should have type `P → Q → R`, got {proof_ty:?}"
    );
}

/// Phase 6: a variadic user tactic that FULLY closes a goal — body
/// `intro xs; exact xs` over goal `P → P`, invoked `closeAll a`, expands to
/// `intro a; exact a` and closes with a kernel-checkable proof.
#[test]
fn test_variadic_user_tactic_full_close_kernel_checks() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "introExact" xs:ident* : tactic => intro xs; exact xs"#,
    );

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let target = Expr::arrow(p.clone(), p.clone());
    ctx.current_expected_type = Some(target.clone());

    // `introExact a` -> `intro a; exact a` closes `P → P`.
    let tactics = parse_by(&ctx, "by introExact a");
    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("variadic `introExact a` should close `P → P`");

    assert!(
        !proof.has_fvar_quick(),
        "variadic-tactic proof should be closed: {proof:?}"
    );
    let proof_ty = ctx
        .infer_type(&proof)
        .expect("variadic-tactic proof should have an inferable type");
    assert!(
        ctx.is_def_eq(&proof_ty, &target),
        "variadic-tactic proof should have type `P → P`, got {proof_ty:?}"
    );
}

/// Phase 6 soundness: a variadic user tactic must NOT fabricate a proof. With
/// body `intro xs; exact xs` and goal `P → Q` (so `intro a; exact a` gives
/// `a : P` for goal `Q`), `introExact a` must FAIL — never close `P → Q`.
#[test]
fn test_variadic_user_tactic_wrong_proof_fails_to_close() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "introExact" xs:ident* : tactic => intro xs; exact xs"#,
    );

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let target = Expr::arrow(p, q);
    ctx.current_expected_type = Some(target);

    let tactics = parse_by(&ctx, "by introExact a");
    let result = ctx.elab_by_tactic(&tactics);
    assert!(
        result.is_err(),
        "variadic tactic must not close `P → Q` with `exact a` where `a : P`: {result:?}"
    );
}

/// Phase 6: invoking a variadic tactic with ZERO repetition args is legal — the
/// repetition-mentioning tactics expand to nothing. Body `exact hP` (no
/// repetition reference) still runs once, closing `P` with `introExact0`.
#[test]
fn test_variadic_user_tactic_zero_args_runs_non_rep_tactic() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    // Body references the repetition var only in `intro xs` (expands to nothing
    // for zero args); the trailing `exact hP` runs once.
    register_elab(
        &mut ctx,
        r#"elab "introExact0" xs:ident* : tactic => intro xs; exact hP"#,
    );

    let p = Expr::const_(Name::from_string("P"), vec![]);
    ctx.current_expected_type = Some(p.clone());

    let tactics = parse_by(&ctx, "by introExact0");
    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("zero-arg variadic should run the non-repetition tactic and close `P`");
    let proof_ty = ctx
        .infer_type(&proof)
        .expect("zero-arg variadic proof should have an inferable type");
    assert!(
        ctx.is_def_eq(&proof_ty, &p),
        "zero-arg variadic proof should have type `P`, got {proof_ty:?}"
    );
}

/// Phase 6 regression: a FLAT (non-repetition) user tactic still registers the
/// ordinary compound handler and still closes its goal with a kernel-checkable
/// proof, byte-for-byte as in Phase 1 — the variadic path must not capture it.
/// `elab "myexact" e:term : tactic => exact e` over goal `P`, invoked
/// `myexact hP`.
#[test]
fn test_flat_user_tactic_unchanged_after_phase6() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(&mut ctx, r#"elab "myexact" e:term : tactic => exact e"#);
    assert!(
        ctx.tactic_registry.get_compound("myexact").is_some(),
        "flat user tactic should still register a compound handler"
    );

    let p = Expr::const_(Name::from_string("P"), vec![]);
    ctx.current_expected_type = Some(p.clone());

    let tactics = parse_by(&ctx, "by myexact hP");
    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("flat user tactic `myexact hP` should still close goal `P`");
    let proof_ty = ctx
        .infer_type(&proof)
        .expect("flat user-tactic proof should have an inferable type");
    assert!(
        ctx.is_def_eq(&proof_ty, &p),
        "flat user-tactic proof should have type `P`, got {proof_ty:?}"
    );
}

/// Phase 6 honest defer: a TERM-category variadic elaborator (`xs:term,*`) is
/// recognized as a repetition pattern but NOT registered (the fold/codegen
/// expansion is out of scope). It must fall through, leaving no user-term elab.
#[test]
fn test_term_variadic_elab_is_deferred() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    // `elab "mklist" xs:term,* : term => ...` — a term repetition. Deferred.
    let decl = parse_decl_with_tactics(
        r#"elab "mklist" xs:term,* : term => xs"#,
        &ctx.tactic_registry.tactic_patterns(),
    )
    .expect("term variadic elab should parse");
    ctx.elab_decl(&decl).expect("deferred term elab elaborates");
    assert!(
        !ctx.user_term_elabs.contains_key("mklist"),
        "term variadic elaborator must be deferred (not registered)"
    );
}

// ===========================================================================
// Phase 7: value-yielding tactic binds (eval_returning, read-out-of-state)
// ===========================================================================

/// Phase 7: the PRINCIPLED value bind reads the introduced hypothesis name out
/// of the proof state (it does not thread the bind name forward). Body
/// `do let g <- intro; exact g`: a bare `intro` introduces a hypothesis named
/// `h` (the default), and `eval_returning` reads that name back, binding `g` to
/// the *actual* introduced hypothesis. `exact g` then closes `P → P` with a
/// kernel-checkable proof — proving the value is recovered from state, not from
/// the bind name `g`.
#[test]
fn test_user_tactic_phase7_value_bind_reads_introduced_hyp_and_closes_goal() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        "elab \"mydo\" : tactic => do let g <- intro; exact g",
    );

    // The executable compound handler must be registered (not just the simple
    // honest-error handler) — the value-bind body is interpretable.
    assert!(
        ctx.tactic_registry.get_compound("mydo").is_some(),
        "value-bind do-body must register an executable compound handler"
    );

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let target = Expr::arrow(p.clone(), p.clone());
    ctx.current_expected_type = Some(target.clone());

    let tactics = parse_by(&ctx, "by mydo");
    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("`do let g <- intro; exact g` should close `P → P`");

    assert!(
        !proof.has_fvar_quick(),
        "phase7 value-bind proof should be closed (no residual FVars): {proof:?}"
    );
    let proof_ty = ctx
        .infer_type(&proof)
        .expect("phase7 value-bind proof should have an inferable (kernel-checkable) type");
    assert!(
        ctx.is_def_eq(&proof_ty, &target),
        "phase7 value-bind proof should have type `P → P`, got {proof_ty:?}"
    );
}

/// Phase 7: two sequential value binds each read a DISTINCT introduced
/// hypothesis. Body `do let a <- intro; let b <- intro; exact b` over goal
/// `P → Q → Q`: the first `intro` introduces `P` (bound to `a`), the second
/// introduces `Q` (bound to `b`), and `exact b` closes the residual `Q`. The
/// resulting proof kernel-checks, pinning that each bind recovers the *current*
/// introduced hypothesis from state.
#[test]
fn test_user_tactic_phase7_two_value_binds_read_distinct_hyps() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        "elab \"mydo2\" : tactic => do let a <- intro; let b <- intro; exact b",
    );

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    // P → Q → Q
    let target = Expr::arrow(p, Expr::arrow(q.clone(), q));
    ctx.current_expected_type = Some(target.clone());

    let tactics = parse_by(&ctx, "by mydo2");
    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("`do let a <- intro; let b <- intro; exact b` should close `P → Q → Q`");

    assert!(
        !proof.has_fvar_quick(),
        "phase7 two-bind proof should be closed: {proof:?}"
    );
    let proof_ty = ctx
        .infer_type(&proof)
        .expect("phase7 two-bind proof should have an inferable type");
    assert!(
        ctx.is_def_eq(&proof_ty, &target),
        "phase7 two-bind proof should have type `P → Q → Q`, got {proof_ty:?}"
    );
}

/// Phase 7 soundness: a value bind of a tactic that yields NO surface value must
/// NOT fabricate a binding. Body `do let x <- exact e; exact x`: `exact` is not
/// value-yielding, so the block is NOT executor-interpretable and only the
/// honest-error simple handler is registered — invoking it errors honestly.
#[test]
fn test_user_tactic_phase7_non_value_yielding_bind_deferred_errors_honestly() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "mydobad" e:term : tactic => do let x <- exact e; exact x"#,
    );

    assert!(
        ctx.tactic_registry.get_compound("mydobad").is_none(),
        "a bind of a non-value-yielding tactic must NOT register an executable handler"
    );

    let entry = ctx
        .tactic_registry
        .get("mydobad")
        .cloned()
        .expect("deferred tactic still registers a simple entry for parsing");
    let mut ps = crate::tactic::ProofState::new(Environment::new(), Expr::prop());
    let arg = Expr::const_str("hP");
    let err = (entry.handler)(&mut ps, std::slice::from_ref(&arg))
        .expect_err("non-value-yielding bind must error honestly, not fabricate success");
    assert!(
        matches!(err, crate::tactic::TacticError::ElaborationFailed { .. }),
        "deferred non-value-yielding bind should surface ElaborationFailed, got {err:?}"
    );
}

/// Phase 7 soundness: the value-bind executor must NOT close a goal it does not
/// legitimately discharge. Body `do let h <- intro; exact h` applied to goal
/// `P → Q` (so `h : P` but the residual goal is `Q`, `P ≠ Q`) must FAIL — the
/// `exact h` is kernel-checked against `Q` and rejected, never fabricating a
/// proof.
#[test]
fn test_user_tactic_phase7_value_bind_wrong_proof_fails_to_close() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        "elab \"mydo\" : tactic => do let h <- intro; exact h",
    );

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    // P → Q: after `intro`, `h : P` but the goal is `Q`.
    let target = Expr::arrow(p, q);
    ctx.current_expected_type = Some(target);

    let tactics = parse_by(&ctx, "by mydo");
    let result = ctx.elab_by_tactic(&tactics);
    assert!(
        result.is_err(),
        "phase7 value bind must not close `P → Q` with `exact h` where `h : P`: {result:?}"
    );
}

// ===========================================================================
// Metaprogram value-constructor evaluator: a term-elaborator body written in
// `MetaM`/`TermElabM` constructor style (`mkConst`/`mkApp`/`Expr.*`) elaborates
// and kernel-checks to the term it programmatically builds.
// ===========================================================================

/// `P, Q : Prop`, `hP : P`, `Nat` + constructors. The base for constructor-body
/// term elaborators that build `Nat` terms programmatically.
fn nat_prop_env() -> Environment {
    let mut env = prop_env();
    env.init_nat().expect("init_nat");
    env
}

/// `elab "myzero" : term => mkConst `Nat.zero` must elaborate to the kernel
/// constant `Nat.zero` and kernel-check at type `Nat`. Before this evaluator the
/// body failed with `UnknownIdent("mkConst")`.
#[test]
fn test_term_elab_mkconst_body_builds_constant_and_kernel_checks() {
    let env = nat_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(&mut ctx, r#"elab "myzero" : term => mkConst `Nat.zero"#);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    ctx.current_expected_type = Some(nat.clone());

    let surface = parse_expr("myzero").expect("`myzero` should parse");
    let term = ctx
        .elaborate(&surface)
        .expect("`mkConst `Nat.zero` body should elaborate to Nat.zero");

    assert_eq!(
        term,
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
        "mkConst body should produce the kernel constant Nat.zero, got {term:?}"
    );
    let ty = ctx
        .infer_type(&term)
        .expect("constructed term must have an inferable (kernel-checkable) type");
    assert!(
        ctx.is_def_eq(&ty, &nat),
        "constructed Nat.zero should have type Nat, got {ty:?}"
    );
}

/// `elab "myone" : term => mkApp (mkConst `Nat.succ) (mkConst `Nat.zero)` must
/// elaborate to the kernel application `Nat.succ Nat.zero` and kernel-check at
/// type `Nat`.
#[test]
fn test_term_elab_mkapp_body_builds_application_and_kernel_checks() {
    let env = nat_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "myone" : term => mkApp (mkConst `Nat.succ) (mkConst `Nat.zero)"#,
    );

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    ctx.current_expected_type = Some(nat.clone());

    let surface = parse_expr("myone").expect("`myone` should parse");
    let term = ctx
        .elaborate(&surface)
        .expect("mkApp body should elaborate to `Nat.succ Nat.zero`");

    let expected = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    assert_eq!(
        term, expected,
        "mkApp body should build `Nat.succ Nat.zero`, got {term:?}"
    );
    let ty = ctx
        .infer_type(&term)
        .expect("constructed application must kernel-check");
    assert!(
        ctx.is_def_eq(&ty, &nat),
        "constructed `Nat.succ Nat.zero` should have type Nat, got {ty:?}"
    );
}

/// Soundness: a constructor body that names a constant that does NOT exist must
/// fail elaboration — the rewrite turns `mkConst `Nope.missing` into the
/// identifier `Nope.missing`, which the elaborator cannot resolve. No fabricated
/// term, no kernel bypass.
#[test]
fn test_term_elab_mkconst_unknown_name_fails_honestly() {
    let env = nat_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(&mut ctx, r#"elab "bad" : term => mkConst `Nope.missing"#);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    ctx.current_expected_type = Some(nat);

    let surface = parse_expr("bad").expect("`bad` should parse");
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_err(),
        "a constructor body naming an unknown constant must fail, not fabricate a term: {result:?}"
    );
}

/// Soundness: a constructor body that builds an ill-typed application must fail
/// the kernel type check. `mkApp (mkConst `Nat.succ) (mkConst `Bool.true)`
/// rewrites to `Nat.succ Bool.true`, which the elaborator rejects (`Nat.succ`
/// expects a `Nat`).
#[test]
fn test_term_elab_mkapp_ill_typed_application_fails() {
    let mut env = nat_prop_env();
    env.init_bool().expect("init_bool");
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "badapp" : term => mkApp (mkConst `Nat.succ) (mkConst `Bool.true)"#,
    );

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    ctx.current_expected_type = Some(nat);

    let surface = parse_expr("badapp").expect("`badapp` should parse");
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_err(),
        "an ill-typed constructed application must be rejected by elaboration: {result:?}"
    );
}

/// A constructor body with a bound pattern variable: `elab "mywrap" e:term :
/// term => mkApp (mkConst `Nat.succ) e` applied to `Nat.zero` builds
/// `Nat.succ Nat.zero`. Verifies the rewrite composes with argument
/// substitution (the bound `e` is substituted, then the builtins are lowered).
#[test]
fn test_term_elab_mkapp_with_bound_arg_substitutes_then_builds() {
    let env = nat_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "mywrap" e:term : term => mkApp (mkConst `Nat.succ) e"#,
    );

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    ctx.current_expected_type = Some(nat.clone());

    let surface = parse_expr("mywrap Nat.zero").expect("`mywrap Nat.zero` should parse");
    let term = ctx
        .elaborate(&surface)
        .expect("mkApp body with bound arg should elaborate");

    let expected = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    assert_eq!(
        term, expected,
        "bound-arg mkApp body should build `Nat.succ Nat.zero`, got {term:?}"
    );
    let ty = ctx
        .infer_type(&term)
        .expect("constructed term must kernel-check");
    assert!(ctx.is_def_eq(&ty, &nat), "result should have type Nat");
}

// ===========================================================================
// Binder constructor builtins: a term-elaborator body written in `MetaM`
// constructor style with `mkLambda`/`mkForall`/`Expr.lam`/`Expr.forallE`
// elaborates and kernel-checks to the binder term it programmatically builds.
// ===========================================================================

/// `elab "myid" : term => mkLambda `x Nat (mkConst `Nat.zero)` must elaborate
/// to the kernel lambda `fun (x : Nat) => Nat.zero` and kernel-check at type
/// `Nat → Nat`.
#[test]
fn test_term_elab_mklambda_body_builds_lambda_and_kernel_checks() {
    let env = nat_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "mylam" : term => mkLambda `x Nat (mkConst `Nat.zero)"#,
    );

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_to_nat = Expr::arrow(nat.clone(), nat.clone());
    ctx.current_expected_type = Some(nat_to_nat.clone());

    let surface = parse_expr("mylam").expect("`mylam` should parse");
    let term = ctx
        .elaborate(&surface)
        .expect("mkLambda body should elaborate to `fun x : Nat => Nat.zero`");

    assert!(
        matches!(term.kind(), ExprKind::Lam(..)),
        "mkLambda body should build a kernel lambda, got {term:?}"
    );
    let ty = ctx
        .infer_type(&term)
        .expect("constructed lambda must kernel-check");
    assert!(
        ctx.is_def_eq(&ty, &nat_to_nat),
        "constructed `fun x : Nat => Nat.zero` should have type Nat → Nat, got {ty:?}"
    );
}

/// `elab "mypi" : term => mkForall `x Nat (mkConst `Nat)` must elaborate to the
/// dependent arrow `(x : Nat) → Nat` (a type) and kernel-check (its type is a
/// `Sort`).
#[test]
fn test_term_elab_mkforall_body_builds_dependent_arrow_and_kernel_checks() {
    let env = nat_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "mypi" : term => mkForall `x Nat (mkConst `Nat)"#,
    );

    let surface = parse_expr("mypi").expect("`mypi` should parse");
    let term = ctx
        .elaborate(&surface)
        .expect("mkForall body should elaborate to `(x : Nat) → Nat`");

    assert!(
        matches!(term.kind(), ExprKind::Pi(..)),
        "mkForall body should build a kernel Pi, got {term:?}"
    );
    // `(x : Nat) → Nat` is a type, so its own type must be a sort.
    let ty = ctx
        .infer_type(&term)
        .expect("constructed Pi must kernel-check");
    assert!(
        matches!(ty.kind(), ExprKind::Sort(_)),
        "constructed `(x : Nat) → Nat` should be a Sort, got {ty:?}"
    );
}

/// `Expr.lam` constructor form with the trailing `BinderInfo` argument builds
/// the same lambda; the `BinderInfo` is dropped and the term kernel-checks.
#[test]
fn test_term_elab_expr_lam_with_binderinfo_builds_lambda() {
    let env = nat_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "mylam2" : term => Expr.lam `x Nat (mkConst `Nat.zero) BinderInfo.default"#,
    );

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_to_nat = Expr::arrow(nat.clone(), nat);
    ctx.current_expected_type = Some(nat_to_nat.clone());

    let surface = parse_expr("mylam2").expect("`mylam2` should parse");
    let term = ctx
        .elaborate(&surface)
        .expect("Expr.lam body should elaborate to a lambda");

    assert!(
        matches!(term.kind(), ExprKind::Lam(..)),
        "Expr.lam body should build a kernel lambda, got {term:?}"
    );
    let ty = ctx
        .infer_type(&term)
        .expect("constructed lambda must kernel-check");
    assert!(
        ctx.is_def_eq(&ty, &nat_to_nat),
        "Expr.lam lambda should have type Nat → Nat, got {ty:?}"
    );
}

/// Soundness: an ill-typed binder body must fail the kernel type check.
/// `mkLambda `x Nat (mkApp (mkConst `Nat.succ) (mkConst `Bool.true))` builds
/// `fun (x : Nat) => Nat.succ Bool.true`, whose body is ill-typed (`Nat.succ`
/// expects a `Nat`), so elaboration must reject it — no fabricated term.
#[test]
fn test_term_elab_mklambda_ill_typed_body_fails() {
    let mut env = nat_prop_env();
    env.init_bool().expect("init_bool");
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "badlam" : term => mkLambda `x Nat (mkApp (mkConst `Nat.succ) (mkConst `Bool.true))"#,
    );

    let surface = parse_expr("badlam").expect("`badlam` should parse");
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_err(),
        "an ill-typed binder body must be rejected by elaboration: {result:?}"
    );
}

// ===========================================================================
// Metaprogram value channel: a term-elaborator body that binds and uses a
// kernel-`Expr` query value (`inferType e`). The query READS the type from the
// kernel-checked elaboration state; nothing is fabricated.
// ===========================================================================

/// Terminal query: `elab "tyOf" e:term : term => inferType e` applied to a
/// `Nat` term must elaborate to the kernel constant `Nat` (the inferred type)
/// and itself kernel-check (its type is a sort). Before the value channel this
/// body failed with `UnknownIdent("inferType")` — its result is a kernel `Expr`
/// with no surface form to rewrite into.
#[test]
fn test_term_elab_infer_type_terminal_query_yields_type_and_kernel_checks() {
    let env = nat_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(&mut ctx, r#"elab "tyOf" e:term : term => inferType e"#);

    // `tyOf Nat.zero` => the type of `Nat.zero`, which is `Nat`.
    let surface = parse_expr("tyOf Nat.zero").expect("`tyOf Nat.zero` should parse");
    let term = ctx
        .elaborate(&surface)
        .expect("`inferType Nat.zero` should evaluate to the type `Nat`");

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    assert!(
        ctx.is_def_eq(&term, &nat),
        "inferType Nat.zero should be the type `Nat`, got {term:?}"
    );
    // The query result is itself a kernel-checkable expression (a type, so its
    // type is a sort).
    let ty = ctx
        .infer_type(&term)
        .expect("the inferred type must itself kernel-check");
    assert!(
        matches!(ty.kind(), ExprKind::Sort(..)),
        "the type of `Nat` must be a sort, got {ty:?}"
    );
}

/// Value channel: `elab "tyOf2" e:term : term => do let t := inferType e; t`
/// binds the query value to `t` and references it in a later position. The
/// reference splices the already-elaborated `Expr` (no re-parse), producing the
/// same result as the terminal form.
#[test]
fn test_term_elab_infer_type_value_channel_binds_and_uses_value() {
    let env = nat_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "tyOf2" e:term : term => do let t := inferType e; t"#,
    );

    let surface = parse_expr("tyOf2 Nat.zero").expect("`tyOf2 Nat.zero` should parse");
    let term = ctx
        .elaborate(&surface)
        .expect("value-channel `let t := inferType e; t` should yield the type `Nat`");

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    assert!(
        ctx.is_def_eq(&term, &nat),
        "value-channel result should be the type `Nat`, got {term:?}"
    );
}

// ===========================================================================
// checkType e ty query: elaborate `e` and `ty`, verify `e : ty` against the
// kernel TC (is_def_eq on the inferred type), and return the kernel-checked `e`
// only on a match — a mismatch fails honestly. READS from the kernel; closes no
// goal and fabricates nothing.
// ===========================================================================

/// Terminal query: `elab "ckd" e:term : term => checkType e Nat` returns `e`
/// (the kernel-checked term) iff `e : Nat`. Applied to `Nat.zero` it returns
/// `Nat.zero`, which still kernel-checks at type `Nat`.
#[test]
fn test_term_elab_check_type_returns_term_when_well_typed_and_kernel_checks() {
    let env = nat_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(&mut ctx, r#"elab "ckd" e:term : term => checkType e Nat"#);

    let surface = parse_expr("ckd Nat.zero").expect("`ckd Nat.zero` should parse");
    let term = ctx
        .elaborate(&surface)
        .expect("`checkType Nat.zero Nat` should return `Nat.zero` (it has type `Nat`)");

    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    assert!(
        ctx.is_def_eq(&term, &zero),
        "checkType should return the original term `Nat.zero`, got {term:?}"
    );
    // The returned term is itself kernel-checkable, and at type `Nat`.
    let ty = ctx
        .infer_type(&term)
        .expect("the checked term must itself kernel-check");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    assert!(
        ctx.is_def_eq(&ty, &nat),
        "the checked term `Nat.zero` must have type `Nat`, got {ty:?}"
    );
}

/// Soundness: `checkType e ty` must REJECT a term that does not have the asserted
/// type. `checkType hP Nat` where `hP : P` (`P : Prop`, `P ≠ Nat`) must fail
/// honestly — the query never returns a term at a type it does not have.
#[test]
fn test_term_elab_check_type_mismatched_type_fails_honestly() {
    // `nat_prop_env` extends `prop_env`, so `hP : P` (P : Prop) is in scope.
    let env = nat_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(&mut ctx, r#"elab "ckbad" e:term : term => checkType e Nat"#);

    // `hP : P`, and `P` is not def-eq to `Nat`, so `checkType hP Nat` must fail.
    let surface = parse_expr("ckbad hP").expect("`ckbad hP` should parse");
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_err(),
        "checkType must reject `hP : P` at type `Nat`: {result:?}"
    );
}

// ===========================================================================
// whnf e query: elaborate `e`, weak-head-normalize via the kernel reducer, and
// return the reduced kernel `Expr`. whnf is meaning-preserving (is_def_eq holds),
// so the result is the same value in normal form and still kernel-valid.
// ===========================================================================

/// Terminal query: `elab "red" e:term : term => whnf e` applied to the reducible
/// term `Nat.pred (Nat.succ Nat.zero)` returns its weak-head normal form
/// `Nat.zero`. The reduced term kernel-checks and is def-eq to the input (whnf is
/// meaning-preserving).
#[test]
fn test_term_elab_whnf_reduces_term_and_kernel_checks() {
    let env = nat_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(&mut ctx, r#"elab "red" e:term : term => whnf e"#);

    // `Nat.pred (Nat.succ Nat.zero)` weak-head-reduces to `Nat.zero`.
    let surface = parse_expr("red (Nat.pred (Nat.succ Nat.zero))")
        .expect("`red (Nat.pred (Nat.succ Nat.zero))` should parse");
    let term = ctx
        .elaborate(&surface)
        .expect("`whnf (Nat.pred (Nat.succ Nat.zero))` should reduce to `Nat.zero`");

    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    assert!(
        ctx.is_def_eq(&term, &zero),
        "whnf of `Nat.pred (Nat.succ Nat.zero)` should be the normal form `0`, got {term:?}"
    );
    // The reduced term must be in weak-head normal form: a `0` value (the kernel
    // normalizes `Nat.pred (Nat.succ Nat.zero)` to the Nat literal `0` / the
    // `Nat.zero` constructor), NOT the unreduced `Nat.pred ...` application. Pin
    // that the reduction actually took place.
    assert!(
        !matches!(term.kind(), ExprKind::App(..)),
        "whnf result must be reduced (not the unreduced `Nat.pred ...` application), got {term:?}"
    );
    let is_zero_value = match term.kind() {
        ExprKind::Const(name, _) => name == &Name::from_string("Nat.zero"),
        ExprKind::Lit(Literal::Nat(n)) => n.is_zero(),
        _ => false,
    };
    assert!(
        is_zero_value,
        "whnf result must be the `0` value (`Nat.zero` ctor or Nat literal 0), got {term:?}"
    );
    // The reduced term still kernel-checks (at type `Nat`).
    let ty = ctx
        .infer_type(&term)
        .expect("the whnf result must itself kernel-check");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    assert!(
        ctx.is_def_eq(&ty, &nat),
        "the whnf result `Nat.zero` must have type `Nat`, got {ty:?}"
    );
}

/// Value channel composing two queries: `do let t := inferType e; checkType e t`
/// binds the inferred type of `e` to `t`, then checks `e : t` and returns `e`.
/// Since `t` is *exactly* the inferred type of `e`, the check always succeeds and
/// the channel returns the kernel-checked `e`. This proves `inferType` and
/// `checkType` compose through the value channel (the bound `Expr` splices into
/// the later query position).
#[test]
fn test_term_elab_value_channel_infer_then_check_composes() {
    let env = nat_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "ic" e:term : term => do let t := inferType e; checkType e t"#,
    );

    let surface = parse_expr("ic Nat.zero").expect("`ic Nat.zero` should parse");
    let term = ctx.elaborate(&surface).expect(
        "value-channel `let t := inferType e; checkType e t` should return the term `Nat.zero`",
    );

    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    assert!(
        ctx.is_def_eq(&term, &zero),
        "the composed query should return the original term `Nat.zero`, got {term:?}"
    );
    // And the returned term kernel-checks.
    let ty = ctx
        .infer_type(&term)
        .expect("the composed-query result must kernel-check");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    assert!(
        ctx.is_def_eq(&ty, &nat),
        "the composed-query result `Nat.zero` must have type `Nat`, got {ty:?}"
    );
}

// ===========================================================================
// Phase 8: tactic-side goal-target query (`getMainTarget`) through the value
// channel. A tactic do-block reads the current goal's target as a kernel `Expr`
// value and uses it in a later statement; the target is READ from the live
// proof state (nothing fabricated) and the resulting proof still kernel-checks.
// ===========================================================================

/// `elab "useTarget" : tactic => do let g := getMainTarget; exact (hP : g)`
/// binds the current goal target (`P`) to `g`, then uses it as the ascription
/// type in `exact (hP : g)`. The value-channel splice replaces `g` with the
/// stored target `Expr`, so `(hP : P)` closes goal `P` with a kernel-checkable
/// proof — proving the target was read from state and threaded as a real term.
#[test]
fn test_user_tactic_phase8_get_main_target_binds_and_uses_target() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "useTarget" : tactic => do let g := getMainTarget; exact (hP : g)"#,
    );

    // The executable compound handler must be registered (the goal-query let
    // routes the block to the stateful executor, not the honest-error handler).
    assert!(
        ctx.tactic_registry.get_compound("useTarget").is_some(),
        "goal-query do-body must register an executable compound handler"
    );

    let p = Expr::const_(Name::from_string("P"), vec![]);
    ctx.current_expected_type = Some(p.clone());

    let tactics = parse_by(&ctx, "by useTarget");
    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("`do let g := getMainTarget; exact (hP : g)` should close goal `P`");

    assert!(
        !proof.has_fvar_quick(),
        "phase8 goal-query proof should be closed (no residual FVars): {proof:?}"
    );
    let proof_ty = ctx
        .infer_type(&proof)
        .expect("phase8 goal-query proof should have an inferable (kernel-checkable) type");
    assert!(
        ctx.is_def_eq(&proof_ty, &p),
        "phase8 goal-query proof should have type `P`, got {proof_ty:?}"
    );
}

/// Soundness (Phase 8): the goal-query path must NOT close a goal it does not
/// legitimately discharge. Body `do let g := getMainTarget; exact (hP : g)`
/// applied to goal `Q` (with `hP : P`, `P ≠ Q`) reads target `Q`, so the
/// ascription `(hP : Q)` is type-checked by the kernel and REJECTED (`hP : P`),
/// never fabricating a proof of `Q`.
#[test]
fn test_user_tactic_phase8_get_main_target_wrong_proof_fails_to_close() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "useTarget" : tactic => do let g := getMainTarget; exact (hP : g)"#,
    );

    let q = Expr::const_(Name::from_string("Q"), vec![]);
    ctx.current_expected_type = Some(q);

    let tactics = parse_by(&ctx, "by useTarget");
    let result = ctx.elab_by_tactic(&tactics);
    assert!(
        result.is_err(),
        "phase8 goal-query must not close `Q` with `(hP : Q)` where `hP : P`: {result:?}"
    );
}

/// The goal-query value channel is scoped to the do-block: after the tactic
/// runs, the bound name (`g`) must NOT resolve in an unrelated elaboration. A
/// stale binding would be a soundness leak (an arbitrary identifier silently
/// resolving to a previously-read goal target).
#[test]
fn test_user_tactic_phase8_get_main_target_binding_does_not_leak() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "useTarget" : tactic => do let g := getMainTarget; exact (hP : g)"#,
    );

    let p = Expr::const_(Name::from_string("P"), vec![]);
    ctx.current_expected_type = Some(p);

    let tactics = parse_by(&ctx, "by useTarget");
    let _ = ctx
        .elab_by_tactic(&tactics)
        .expect("goal-query tactic body should run");

    // `g` was a value-channel binding internal to the tactic body; it must not
    // be resolvable as a free identifier afterward.
    let leaked = parse_expr("g").expect("`g` should parse as an identifier");
    ctx.current_expected_type = None;
    let result = ctx.elaborate(&leaked);
    assert!(
        result.is_err(),
        "goal-query binding `g` must not leak into a later elaboration: {result:?}"
    );
}

/// Soundness: a query whose argument is an unresolvable name must fail honestly
/// — the value channel reads from the elaboration state and never fabricates a
/// type. `inferType Nope.missing` cannot elaborate its argument.
#[test]
fn test_term_elab_infer_type_unknown_arg_fails_honestly() {
    let env = nat_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(&mut ctx, r#"elab "tyBad" e:term : term => inferType e"#);

    let surface = parse_expr("tyBad Nope.missing").expect("`tyBad Nope.missing` should parse");
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_err(),
        "inferType of an unresolvable argument must fail honestly: {result:?}"
    );
}

/// The value channel is scoped to the body: after a value-channel elaboration,
/// the bound name (`t`) must NOT resolve in an unrelated elaboration. A stale
/// binding would be a soundness leak (an arbitrary identifier silently resolving
/// to a previously-computed term).
#[test]
fn test_term_elab_value_channel_binding_does_not_leak() {
    let env = nat_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "tyOf3" e:term : term => do let t := inferType e; t"#,
    );

    let surface = parse_expr("tyOf3 Nat.zero").expect("`tyOf3 Nat.zero` should parse");
    let _ = ctx
        .elaborate(&surface)
        .expect("value-channel body should elaborate");

    // `t` was a value-channel binding internal to the body; it must not be
    // resolvable as a free identifier afterward.
    let leaked = parse_expr("t").expect("`t` should parse as an identifier");
    let result = ctx.elaborate(&leaked);
    assert!(
        result.is_err(),
        "value-channel binding `t` must not leak into a later elaboration: {result:?}"
    );
}

// ===========================================================================
// Metaprogram computed control flow: a term-elaborator body `if <cond> then <a>
// else <b>` whose condition whnf-reduces to a concrete `Bool.true`/`Bool.false`
// is an ELABORATION-TIME decision — only the selected branch is elaborated +
// kernel-checked (NOT a runtime `ite` keeping both branches). A condition that
// does not whnf-reduce to a concrete Bool (stuck / symbolic / non-Bool) DECLINES
// so the body fails honestly via the ordinary `elab_if` path — never an
// arbitrary branch pick.
// ===========================================================================

/// `P, Q : Prop`, `hP : P`, `Nat`, and `Bool`. The base for control-flow body
/// term elaborators whose conditions evaluate to a concrete `Bool`.
fn nat_bool_prop_env() -> Environment {
    let mut env = nat_prop_env();
    env.init_bool().expect("init_bool");
    env
}

/// `elab "pick" : term => if true then Nat.zero else Nat.succ Nat.zero` elaborates
/// to `Nat.zero`: the condition `true` whnf-reduces to `Bool.true`, so the THEN
/// branch is selected at metaprogram time and elaborated. The result is the bare
/// `Nat.zero` constant — NOT an `ite` application — and it kernel-checks at `Nat`.
#[test]
fn test_term_elab_if_true_selects_then_branch_and_kernel_checks() {
    let env = nat_bool_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "pick" : term => if true then Nat.zero else Nat.succ Nat.zero"#,
    );

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    ctx.current_expected_type = Some(nat.clone());

    let surface = parse_expr("pick").expect("`pick` should parse");
    let term = ctx
        .elaborate(&surface)
        .expect("`if true then Nat.zero else ...` should select and elaborate the then branch");

    assert_eq!(
        term,
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
        "a true condition must select the then branch `Nat.zero` (not build an `ite`), got {term:?}"
    );
    // The selected branch must be the literal chosen term, not a runtime `ite`
    // application keeping both branches.
    assert!(
        !matches!(term.kind(), ExprKind::App(..)),
        "computed control flow must select a branch, not build an `ite` app: {term:?}"
    );
    let ty = ctx
        .infer_type(&term)
        .expect("the selected branch must kernel-check");
    assert!(
        ctx.is_def_eq(&ty, &nat),
        "the selected branch `Nat.zero` must have type `Nat`, got {ty:?}"
    );
}

/// `elab "pick2" : term => if false then Nat.zero else Nat.succ Nat.zero`
/// elaborates to `Nat.succ Nat.zero`: the condition `false` whnf-reduces to
/// `Bool.false`, so the ELSE branch is selected and elaborated, kernel-checking
/// at `Nat`.
#[test]
fn test_term_elab_if_false_selects_else_branch_and_kernel_checks() {
    let env = nat_bool_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "pick2" : term => if false then Nat.zero else Nat.succ Nat.zero"#,
    );

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    ctx.current_expected_type = Some(nat.clone());

    let surface = parse_expr("pick2").expect("`pick2` should parse");
    let term = ctx
        .elaborate(&surface)
        .expect("`if false then ... else Nat.succ Nat.zero` should select the else branch");

    let expected = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    assert_eq!(
        term, expected,
        "a false condition must select the else branch `Nat.succ Nat.zero`, got {term:?}"
    );
    let ty = ctx
        .infer_type(&term)
        .expect("the selected else branch must kernel-check");
    assert!(
        ctx.is_def_eq(&ty, &nat),
        "the selected branch `Nat.succ Nat.zero` must have type `Nat`, got {ty:?}"
    );
}

/// Soundness: a wrong-typed *selected* branch must fail elaboration. The
/// condition `true` selects the then branch `Nat.succ Bool.true`, which is
/// intrinsically ill-typed (`Nat.succ` expects a `Nat`, not `Bool.true`), so the
/// chosen branch is kernel-checked by the normal pipeline and REJECTED. The
/// metaprogram-time selection never bypasses the normal type check. (The else
/// branch is well-typed, proving it is the *selected* branch that is checked, not
/// some lucky fall-through.)
#[test]
fn test_term_elab_if_selected_branch_wrong_type_fails_honestly() {
    let env = nat_bool_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "badpick" : term => if true then Nat.succ Bool.true else Nat.zero"#,
    );

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    ctx.current_expected_type = Some(nat);

    let surface = parse_expr("badpick").expect("`badpick` should parse");
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_err(),
        "the selected (then) branch `Nat.succ Bool.true` is ill-typed and must be rejected by \
         the normal kernel-checked pipeline: {result:?}"
    );
}

/// Soundness: a condition that does NOT whnf-reduce to a concrete
/// `Bool.true`/`Bool.false` must DECLINE the computed-control-flow path and fall
/// through to the ordinary `elab_if` (runtime `ite`) handling — never an
/// arbitrary branch pick. Here the condition `n` is a free `Nat` variable: it is
/// not a `Bool` and is stuck, so the metaprogram-time selector declines.
///
/// With the branches being `Nat` constants the fall-through `elab_if` builds the
/// object-level `ite` (the honest non-control-flow path). The KEY assertion is
/// that the result is NOT one of the two branches selected arbitrarily: it is the
/// `ite` application carrying both branches and the (non-Bool) condition.
#[test]
fn test_term_elab_if_stuck_condition_declines_to_runtime_ite() {
    let env = nat_bool_prop_env();
    let mut ctx = ElabCtx::new(&env);

    // `n : Nat` is a non-Bool, stuck condition.
    register_elab(
        &mut ctx,
        r#"elab "stuckpick" n:term : term => if n then Nat.zero else Nat.succ Nat.zero"#,
    );

    let surface = parse_expr("stuckpick Nat.zero").expect("`stuckpick Nat.zero` should parse");
    let result = ctx.elaborate(&surface);
    // Either the fall-through `elab_if` builds the `ite` (an application keeping
    // both branches), or it fails honestly because `Nat.zero` is not a `Bool`
    // condition. In NO case may the selector have arbitrarily returned the bare
    // `Nat.zero` / `Nat.succ Nat.zero` branch term as if the condition decided it.
    match result {
        Ok(term) => {
            let is_bare_then = term == Expr::const_(Name::from_string("Nat.zero"), vec![]);
            let is_bare_else = term
                == Expr::app(
                    Expr::const_(Name::from_string("Nat.succ"), vec![]),
                    Expr::const_(Name::from_string("Nat.zero"), vec![]),
                );
            assert!(
                !is_bare_then && !is_bare_else,
                "a stuck (non-Bool) condition must NOT pick a branch arbitrarily; \
                 expected the honest `ite` fall-through, got the bare branch {term:?}"
            );
        }
        Err(_) => {
            // Honest failure (non-Bool condition) is also acceptable: the selector
            // declined and the ordinary path rejected the ill-typed condition.
        }
    }
}

// ===========================================================================
// CAPSTONE — cross-feature COMPOSITION lock-in.
//
// The tests above pin each metaprogramming feature in isolation. The tests
// below pin that the features COMPOSE inside a single realistic declaration —
// the value channel, argument substitution, computed control flow, term
// constructors, goal/term queries, and the macro layer all working together in
// one body with no cross-feature interference. Each composition test asserts a
// genuinely-correct, distinct, kernel-checked result, and is paired with a
// SOUNDNESS test proving the same composed program fails honestly when it
// should (wrong type / wrong target / unknown const) — never fabricating.
// ===========================================================================

/// COMPOSITION (a) — a user TACTIC whose `do`-body composes a goal QUERY
/// (`getMainTarget`), a runtime-built APPLICATION (`f hP`, a brand-new term not
/// in the call syntax), value THREADING, and an ascription that uses the queried
/// target. Body:
///
/// ```text
/// elab "applyF" : tactic =>
///   do let g := getMainTarget; let x := f hP; exact (x : g)
/// ```
///
/// Over goal `Q` (with `f : P → Q`, `hP : P`), `g` reads target `Q`, `x` is the
/// runtime application `f hP`, and `exact (x : g)` closes `Q` with the proof
/// `f hP`. The result must kernel-check at `Q` — proving the goal-query value
/// and the runtime-built term flow together through one body. Distinct
/// observable: the proof term is the application `f hP` (NOT `hP`).
#[test]
fn test_composition_tactic_get_target_plus_runtime_app_closes_goal() {
    let env = prop_fn_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "applyF" : tactic => do let g := getMainTarget; let x := f hP; exact (x : g)"#,
    );
    assert!(
        ctx.tactic_registry.get_compound("applyF").is_some(),
        "the composed goal-query + runtime-app body must register an executable handler"
    );

    let q = Expr::const_(Name::from_string("Q"), vec![]);
    ctx.current_expected_type = Some(q.clone());

    let tactics = parse_by(&ctx, "by applyF");
    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("composed `getMainTarget` + `f hP` + ascription should close goal `Q`");

    assert!(
        !proof.has_fvar_quick(),
        "composed-tactic proof should be closed (no residual FVars): {proof:?}"
    );
    // Distinct observable: the proof is the runtime application `f hP`, not the
    // bare hypothesis `hP`.
    let expected_proof = Expr::app(
        Expr::const_(Name::from_string("f"), vec![]),
        Expr::const_(Name::from_string("hP"), vec![]),
    );
    assert_eq!(
        proof, expected_proof,
        "the composed proof should be the runtime-built application `f hP`, got {proof:?}"
    );
    let proof_ty = ctx
        .infer_type(&proof)
        .expect("composed proof should have an inferable (kernel-checkable) type");
    assert!(
        ctx.is_def_eq(&proof_ty, &q),
        "composed proof `f hP` should have type `Q`, got {proof_ty:?}"
    );
}

/// SOUNDNESS for composition (a): the SAME composed body over goal `P` (the
/// wrong target) must FAIL. `getMainTarget` reads `P`, the runtime term is
/// `f hP : Q`, so the ascription `(f hP : P)` is kernel-checked and REJECTED
/// (`Q ≠ P`). The composition never fabricates a proof of `P`.
#[test]
fn test_composition_tactic_get_target_plus_runtime_app_wrong_target_fails() {
    let env = prop_fn_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "applyF" : tactic => do let g := getMainTarget; let x := f hP; exact (x : g)"#,
    );

    // Goal is P, but `f hP : Q`. The composed program must not close it.
    let p = Expr::const_(Name::from_string("P"), vec![]);
    ctx.current_expected_type = Some(p);

    let tactics = parse_by(&ctx, "by applyF");
    let result = ctx.elab_by_tactic(&tactics);
    assert!(
        result.is_err(),
        "composed program must not close goal `P` with `f hP : Q`: {result:?}"
    );
}

/// COMPOSITION (b) — a user TERM elaborator composing argument SUBSTITUTION, two
/// distinct value-channel QUERIES (`inferType`, `whnf`), value THREADING, and a
/// terminal `checkType` that consumes both bound values. Body:
///
/// ```text
/// elab "reduceAt" e:term : term =>
///   do let t := inferType e; let r := whnf (Nat.succ e); checkType r t
/// ```
///
/// Applied to `e = Nat.pred (Nat.succ Nat.zero)`:
/// - `t := inferType e` is the kernel type `Nat`;
/// - `r := whnf (Nat.succ e)` reduces `Nat.succ (Nat.pred (Nat.succ Nat.zero))`
///   to its weak-head normal form (the value `1`, def-eq to `Nat.succ Nat.zero`);
/// - `checkType r t` verifies `r : Nat` and returns the kernel-checked `r`.
///
/// The result must kernel-check at `Nat` and be def-eq to `Nat.succ Nat.zero` —
/// proving substitution, two queries, the value channel, and `checkType` all
/// cooperate in one body. Distinct observable: the result reduces to `1`, NOT
/// the un-reduced `Nat.succ (Nat.pred (Nat.succ Nat.zero))` head shape and NOT
/// `Nat.zero`.
#[test]
fn test_composition_term_substitute_infer_whnf_check_compose() {
    let env = nat_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "reduceAt" e:term : term => do let t := inferType e; let r := whnf (Nat.succ e); checkType r t"#,
    );

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    ctx.current_expected_type = Some(nat.clone());

    let surface = parse_expr("reduceAt (Nat.pred (Nat.succ Nat.zero))")
        .expect("`reduceAt (Nat.pred (Nat.succ Nat.zero))` should parse");
    let term = ctx
        .elaborate(&surface)
        .expect("composed substitute + inferType + whnf + checkType body should elaborate");

    let ty = ctx
        .infer_type(&term)
        .expect("composed term must have an inferable (kernel-checkable) type");
    assert!(
        ctx.is_def_eq(&ty, &nat),
        "composed term should have type `Nat`, got {ty:?}"
    );
    // Distinct observable: the value is `1` (= `Nat.succ Nat.zero`), the
    // whnf-reduced result — not `Nat.zero`, and meaning-equal to the input
    // `Nat.succ (Nat.pred (Nat.succ Nat.zero))`.
    let one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    assert!(
        ctx.is_def_eq(&term, &one),
        "composed result should be def-eq to `Nat.succ Nat.zero` (value 1), got {term:?}"
    );
    assert!(
        !ctx.is_def_eq(&term, &Expr::const_(Name::from_string("Nat.zero"), vec![])),
        "composed result must NOT be `Nat.zero` — that would mean the wrong value flowed through"
    );
}

/// SOUNDNESS for composition (b): the value-channel `checkType` must REJECT a
/// term that does not have the threaded type. Body:
///
/// ```text
/// elab "reduceBad" e:term : term =>
///   do let t := inferType e; checkType Bool.true t
/// ```
///
/// With `e = Nat.zero`, `t` is `Nat`, but `checkType Bool.true Nat` fails
/// (`Bool ≠ Nat`). The composition surfaces an honest error and never returns a
/// term at a type it does not have.
#[test]
fn test_composition_term_value_channel_check_type_mismatch_fails() {
    let mut env = nat_prop_env();
    env.init_bool().expect("init_bool");
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "reduceBad" e:term : term => do let t := inferType e; checkType Bool.true t"#,
    );

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    ctx.current_expected_type = Some(nat);

    let surface = parse_expr("reduceBad Nat.zero").expect("`reduceBad Nat.zero` should parse");
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_err(),
        "composed `checkType Bool.true Nat` must fail honestly (Bool != Nat): {result:?}"
    );
}

/// COMPOSITION (b') — computed CONTROL FLOW selecting a branch that is itself a
/// CONSTRUCTOR-building user term elaborator call. Two elaborators compose: the
/// inner `succN` builds `Nat.succ e` from constructors; the outer `branch`
/// selects between an `succN` call and `Nat.zero` via a metaprogram-time `if`.
/// Body:
///
/// ```text
/// elab "succN" e:term : term => mkApp (mkConst `Nat.succ) e
/// elab "branch" : term => if true then succN (succN Nat.zero) else Nat.zero
/// ```
///
/// The `true` condition selects the then branch `succN (succN Nat.zero)`, which
/// re-enters the user-term-elaborator pipeline and builds `Nat.succ (Nat.succ
/// Nat.zero)` through the constructors. The result kernel-checks at `Nat`.
/// Distinct observable: `Nat.succ (Nat.succ Nat.zero)` (value 2), NOT the else
/// branch `Nat.zero`, NOT an `ite` application.
#[test]
fn test_composition_term_if_selects_nested_constructor_elab() {
    let env = nat_bool_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "succN" e:term : term => mkApp (mkConst `Nat.succ) e"#,
    );
    register_elab(
        &mut ctx,
        r#"elab "branch" : term => if true then succN (succN Nat.zero) else Nat.zero"#,
    );

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    ctx.current_expected_type = Some(nat.clone());

    let surface = parse_expr("branch").expect("`branch` should parse");
    let term = ctx
        .elaborate(&surface)
        .expect("`if true` should select the nested constructor-elab branch");

    let two = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
        ),
    );
    assert_eq!(
        term, two,
        "the selected nested-elab branch should build `Nat.succ (Nat.succ Nat.zero)`, got {term:?}"
    );
    let ty = ctx
        .infer_type(&term)
        .expect("composed if + nested constructor-elab term must kernel-check");
    assert!(
        ctx.is_def_eq(&ty, &nat),
        "composed result should have type `Nat`, got {ty:?}"
    );
}

/// SOUNDNESS for composition (b'): a metaprogram-time `if` that selects a branch
/// whose nested constructor-elab body names a NONEXISTENT constant must fail
/// honestly. Body:
///
/// ```text
/// elab "mkBad" : term => mkConst `Nope.missing
/// elab "branchBad" : term => if true then mkBad else Nat.zero
/// ```
///
/// The `true` condition selects `mkBad`, which builds `Nope.missing` — an
/// unresolvable constant — so the chosen branch is rejected by the normal
/// pipeline. The composition never fabricates a term for the unknown name.
#[test]
fn test_composition_term_if_selects_unknown_const_elab_fails() {
    let env = nat_bool_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(&mut ctx, r#"elab "mkBad" : term => mkConst `Nope.missing"#);
    register_elab(
        &mut ctx,
        r#"elab "branchBad" : term => if true then mkBad else Nat.zero"#,
    );

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    ctx.current_expected_type = Some(nat);

    let surface = parse_expr("branchBad").expect("`branchBad` should parse");
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_err(),
        "the selected branch builds an unknown constant and must fail honestly: {result:?}"
    );
}

/// COMPOSITION (c) — a `notation` (macro layer) whose expansion is a NESTED use
/// of a CONSTRUCTOR-building user term elaborator. The two layers compose:
///
/// ```text
/// elab "succOf" e:term : term => mkApp (mkConst `Nat.succ) e
/// notation "TWO" => succOf (succOf Nat.zero)
/// ```
///
/// Elaborating `TWO` first expands the notation to `succOf (succOf Nat.zero)`,
/// then the user-term-elaborator pipeline fires twice (each `succOf` builds a
/// `Nat.succ` via constructors), producing `Nat.succ (Nat.succ Nat.zero)`. The
/// result kernel-checks at `Nat`. This pins the macro layer and the
/// metaprogramming evaluator interoperating with no interference. Distinct
/// observable: `Nat.succ (Nat.succ Nat.zero)` (value 2).
#[test]
fn test_composition_macro_expands_to_nested_constructor_elab() {
    let env = nat_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "succOf" e:term : term => mkApp (mkConst `Nat.succ) e"#,
    );
    let notation_decl = clean_parser::parse_decl(r#"notation "TWO" => succOf (succOf Nat.zero)"#)
        .expect("`notation \"TWO\" => ...` should parse");
    ctx.elab_decl(&notation_decl)
        .expect("notation registers into the macro context");

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    ctx.current_expected_type = Some(nat.clone());

    let surface = parse_expr("TWO").expect("`TWO` should parse");
    let term = ctx.elaborate(&surface).expect(
        "notation should expand and the nested user term elaborators should build the term",
    );

    let two = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
        ),
    );
    assert_eq!(
        term, two,
        "macro `TWO` should expand + elaborate to `Nat.succ (Nat.succ Nat.zero)`, got {term:?}"
    );
    let ty = ctx
        .infer_type(&term)
        .expect("the macro-expanded, elaborator-built term must kernel-check");
    assert!(
        ctx.is_def_eq(&ty, &nat),
        "composed result should have type `Nat`, got {ty:?}"
    );
}

/// SOUNDNESS for composition (c): a `notation` expanding to a user term
/// elaborator call that builds an UNKNOWN constant must fail honestly. Body:
///
/// ```text
/// elab "succOf" e:term : term => mkApp (mkConst `Nat.succ) e
/// notation "BADTWO" => succOf Nope.missing
/// ```
///
/// `BADTWO` expands to `succOf Nope.missing`; the elaborator substitutes the
/// unresolvable `Nope.missing` and the normal pipeline rejects it. The macro +
/// elaborator composition surfaces an honest error, never fabricating a term.
#[test]
fn test_composition_macro_expands_to_elab_with_unknown_const_fails() {
    let env = nat_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "succOf" e:term : term => mkApp (mkConst `Nat.succ) e"#,
    );
    let notation_decl = clean_parser::parse_decl(r#"notation "BADTWO" => succOf Nope.missing"#)
        .expect("`notation \"BADTWO\" => ...` should parse");
    ctx.elab_decl(&notation_decl)
        .expect("notation registers into the macro context");

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    ctx.current_expected_type = Some(nat);

    let surface = parse_expr("BADTWO").expect("`BADTWO` should parse");
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_err(),
        "macro expanding to an elab call naming an unknown constant must fail honestly: {result:?}"
    );
}

// ===========================================================================
// OPTIONAL trailing pattern (`x:term?`) — end-to-end term elaborator.
//
// A single trailing optional binder accepts the optional argument PRESENT or
// ABSENT. Present: the argument is bound and substituted. Absent: the optional
// variable is left unsubstituted (a free identifier) — a body that does not
// reference it elaborates normally; a body that does reference it fails
// honestly. No `Option`/default machinery is fabricated.
// ===========================================================================

/// `elab "presN" x:term? : term => Nat.succ x` invoked WITH its optional argument
/// (`presN Nat.zero`) binds `x = Nat.zero` and elaborates the body to
/// `Nat.succ Nat.zero`, which kernel-checks at `Nat`. Distinct observable:
/// `Nat.succ Nat.zero` (value 1).
#[test]
fn test_optional_term_elab_present_binds_and_kernel_checks() {
    let env = nat_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(&mut ctx, r#"elab "presN" x:term? : term => Nat.succ x"#);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    ctx.current_expected_type = Some(nat.clone());

    let surface = parse_expr("presN Nat.zero").expect("`presN Nat.zero` should parse");
    let term = ctx
        .elaborate(&surface)
        .expect("optional binder present should bind the argument and elaborate the body");

    let expected = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    assert_eq!(
        term, expected,
        "present optional `x = Nat.zero` should build `Nat.succ Nat.zero`, got {term:?}"
    );
    let ty = ctx
        .infer_type(&term)
        .expect("present-optional term must kernel-check");
    assert!(
        ctx.is_def_eq(&ty, &nat),
        "result should have type `Nat`, got {ty:?}"
    );
}

/// `elab "absN" x:term? : term => Nat.zero` invoked WITHOUT its optional argument
/// (bare `absN`) elaborates the body (which does NOT reference the absent `x`) to
/// `Nat.zero`. This proves the optional-absent path: the keyword is recognized at
/// arity-1-less and the body elaborates and kernel-checks. Distinct observable:
/// `Nat.zero` (value 0).
#[test]
fn test_optional_term_elab_absent_unused_var_kernel_checks() {
    let env = nat_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(&mut ctx, r#"elab "absN" x:term? : term => Nat.zero"#);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    ctx.current_expected_type = Some(nat.clone());

    let surface = parse_expr("absN").expect("bare `absN` should parse");
    let term = ctx
        .elaborate(&surface)
        .expect("optional binder absent, body not referencing it, should elaborate");

    assert_eq!(
        term,
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
        "absent-optional body `Nat.zero` should elaborate to the constant Nat.zero, got {term:?}"
    );
    let ty = ctx
        .infer_type(&term)
        .expect("absent-optional term must kernel-check");
    assert!(
        ctx.is_def_eq(&ty, &nat),
        "result should have type `Nat`, got {ty:?}"
    );
}

/// SOUNDNESS for the optional path: when the optional argument is ABSENT and the
/// body DOES reference it, the variable stays a free identifier and elaboration
/// fails honestly — the optional-absent path never fabricates a binding or a
/// default value. `elab "useN" x:term? : term => Nat.succ x` invoked bare
/// (`useN`) must fail because `x` is unbound.
#[test]
fn test_optional_term_elab_absent_used_var_fails_honestly() {
    let env = nat_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(&mut ctx, r#"elab "useN" x:term? : term => Nat.succ x"#);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    ctx.current_expected_type = Some(nat);

    let surface = parse_expr("useN").expect("bare `useN` should parse");
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_err(),
        "an absent optional referenced by the body must fail honestly (unbound `x`), \
         never fabricate a binding: {result:?}"
    );
}

/// The optional binder still REJECTS an over-application: `elab "presN" x:term? :
/// term => Nat.succ x` invoked with two arguments (`presN Nat.zero Nat.zero`) is
/// neither the present (arity 1) nor absent (arity 0) shape, so the user term
/// elaborator declines and the call falls through to the normal pipeline, which
/// fails honestly (a `Nat` is not a function). Pins that optional support widens
/// arity by exactly one, not arbitrarily.
#[test]
fn test_optional_term_elab_over_application_is_not_intercepted() {
    let env = nat_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(&mut ctx, r#"elab "presN" x:term? : term => Nat.succ x"#);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    ctx.current_expected_type = Some(nat);

    let surface =
        parse_expr("presN Nat.zero Nat.zero").expect("`presN Nat.zero Nat.zero` should parse");
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_err(),
        "an over-applied optional keyword must not be intercepted; it falls through and \
         fails honestly: {result:?}"
    );
}

/// DEFERRED: an optional marker on a NON-trailing binder (`a:term? b:term`) is
/// not tractable for the positional substitute-and-reelaborate bridge, so the
/// term elaborator is NOT registered — a call to the keyword falls through and
/// fails honestly as an unknown identifier rather than mis-binding.
///
/// This is also a flip-on-fix sentinel: if non-trailing optional patterns ever
/// gain proper pattern-metadata plumbing, this keyword would start being
/// intercepted and the assertion would flip — prompting a revisit of the
/// `pinned-deferred` status for the non-trailing/multi-position case.
#[test]
fn test_non_trailing_optional_term_elab_is_deferred() {
    let env = nat_prop_env();
    let mut ctx = ElabCtx::new(&env);

    // `a:term? b:term` — the optional is NOT trailing.
    register_elab(&mut ctx, r#"elab "midOpt" a:term? b:term : term => a"#);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    ctx.current_expected_type = Some(nat);

    // Calling with one or two args must NOT be intercepted (the elaborator was
    // deferred at registration), so it fails honestly through the normal path.
    let two_args = parse_expr("midOpt Nat.zero Nat.zero").expect("parses");
    assert!(
        ctx.elaborate(&two_args).is_err(),
        "a non-trailing optional pattern must be deferred (not registered), so the call \
         fails honestly: it must not be intercepted as a user term elaborator"
    );
}

// ===========================================================================
// throwError: first-class custom user errors
// ===========================================================================

/// `P, Q : Prop`, `hP : P`, `Nat`, and `Bool`. The base for tactic bodies whose
/// computed-`if` conditions evaluate to a concrete `Bool`.
fn bool_prop_env() -> Environment {
    let mut env = prop_env();
    env.init_bool().expect("init_bool");
    env
}

/// A user tactic whose body is `do throwError "custom message"` must FAIL
/// elaboration with the user's custom error: the typed [`TacticError::UserThrowError`]
/// carries exactly the message. It closes no goal and fabricates nothing.
#[test]
fn test_user_tactic_throw_error_body_fails_with_custom_message() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "boom" : tactic => do throwError "custom message""#,
    );

    // A supported throwError body IS executable (it raises a real typed error),
    // so a compound handler is registered.
    assert!(
        ctx.tactic_registry.get_compound("boom").is_some(),
        "a `throwError \"msg\"` tactic body must register an executable handler"
    );

    let p = Expr::const_(Name::from_string("P"), vec![]);
    ctx.current_expected_type = Some(p);

    let tactics = parse_by(&ctx, "by boom");
    let err = ctx
        .elab_by_tactic(&tactics)
        .expect_err("`throwError \"custom message\"` must fail elaboration, not close the goal");
    assert!(
        err.to_string().contains("custom message"),
        "the failure must carry the user's custom message, got {err}"
    );
}

/// B89: a `do throwError s!"got {x}"` body whose hole `{x}` is bound to a
/// concrete call-site value (`7`) fails with the message carrying the RENDERED
/// value (`got 7`), not the raw `{x}` placeholder. Interpolation only formats the
/// message text from an already-bound value; it closes no goal.
#[test]
fn test_user_tactic_throw_error_interpolation_renders_bound_value() {
    let env = nat_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "boomx" x:term : tactic => do throwError s!"got {x}""#,
    );
    assert!(
        ctx.tactic_registry.get_compound("boomx").is_some(),
        "a `throwError s!\"…\"` interpolation body must register an executable handler"
    );

    let p = Expr::const_(Name::from_string("P"), vec![]);
    ctx.current_expected_type = Some(p);

    let tactics = parse_by(&ctx, "by boomx 7");
    let err = ctx
        .elab_by_tactic(&tactics)
        .expect_err("`throwError s!\"got {x}\"` must fail elaboration, not close the goal");
    assert!(
        err.to_string().contains("got 7"),
        "the interpolation must render the bound value into the message, got {err}"
    );
}

/// B89: an interpolation hole that does NOT resolve to a concrete renderable
/// value (here `{x}` is bound to a hypothesis identifier, not a literal) must NOT
/// fabricate a message — it surfaces an honest error rather than printing a
/// guessed value. No goal is closed.
#[test]
fn test_user_tactic_throw_error_interpolation_unresolvable_defers_honestly() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "boomh" x:term : tactic => do throwError s!"got {x}""#,
    );

    let p = Expr::const_(Name::from_string("P"), vec![]);
    ctx.current_expected_type = Some(p.clone());

    // `hP` is a hypothesis identifier, not a concrete renderable value: the
    // interpolation declines and an honest error surfaces — the goal is NOT closed
    // and no fabricated value (`hP`) leaks into a success.
    let tactics = parse_by(&ctx, "by boomh hP");
    let result = ctx.elab_by_tactic(&tactics);
    assert!(
        result.is_err(),
        "an unresolvable interpolation must not close the goal: {result:?}"
    );
}

/// B89 (bare form): a non-`do` terminal `throwError s!"got {x}"` body also renders
/// the bound value. Pins the bare-tactic interpolation path alongside the do form.
#[test]
fn test_user_tactic_bare_throw_error_interpolation_renders_bound_value() {
    let env = nat_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "barex" x:term : tactic => throwError s!"saw {x}""#,
    );

    let p = Expr::const_(Name::from_string("P"), vec![]);
    ctx.current_expected_type = Some(p);

    let tactics = parse_by(&ctx, "by barex 42");
    let err = ctx
        .elab_by_tactic(&tactics)
        .expect_err("a bare `throwError s!\"saw {x}\"` body must fail, not close the goal");
    assert!(
        err.to_string().contains("saw 42"),
        "the bare interpolation body must render the bound value, got {err}"
    );
}

/// B89 (term elaborator): a term-position `throwError s!"got {x}"` body renders the
/// bound call-site value into the typed `UserThrowError` message.
#[test]
fn test_term_elab_throw_error_interpolation_renders_bound_value() {
    let env = nat_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "boomtermx" x:term : term => throwError s!"got {x}""#,
    );

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    ctx.current_expected_type = Some(nat);

    let surface = parse_expr("boomtermx 5").expect("`boomtermx 5` should parse");
    let err = ctx
        .elaborate(&surface)
        .expect_err("a `throwError s!\"got {x}\"` term body must fail, not produce a term");
    assert!(
        matches!(err, ElabError::UserThrowError { ref message } if message == "got 5"),
        "term interpolation throwError must surface the rendered message, got {err:?}"
    );
}

/// A computed `if <true-cond> then throwError "bad" else <ok>` fires the
/// throwError when the condition is decided-true at metaprogram time, failing
/// with "bad" rather than running the ok branch.
#[test]
fn test_user_tactic_computed_if_true_throw_error_fires_with_message() {
    let env = bool_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "checkit" : tactic => do if true then throwError "bad" else exact hP"#,
    );
    assert!(
        ctx.tactic_registry.get_compound("checkit").is_some(),
        "a computed-if throwError tactic body must register an executable handler"
    );

    let p = Expr::const_(Name::from_string("P"), vec![]);
    ctx.current_expected_type = Some(p);

    let tactics = parse_by(&ctx, "by checkit");
    let err = ctx
        .elab_by_tactic(&tactics)
        .expect_err("a decided-true `if` must fire `throwError \"bad\"`, not close the goal");
    assert!(
        err.to_string().contains("bad"),
        "the decided-true branch must surface the throwError message `bad`, got {err}"
    );
}

/// The `if <false-cond>` variant takes the ok branch: `if false then throwError
/// "bad" else exact hP` runs `exact hP` and closes goal `P` with a
/// kernel-checkable proof. The throwError never fires.
#[test]
fn test_user_tactic_computed_if_false_takes_ok_branch_and_closes_goal() {
    let env = bool_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "checkit" : tactic => do if false then throwError "bad" else exact hP"#,
    );

    let p = Expr::const_(Name::from_string("P"), vec![]);
    ctx.current_expected_type = Some(p.clone());

    let tactics = parse_by(&ctx, "by checkit");
    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("a decided-false `if` must take the ok branch `exact hP` and close goal `P`");
    assert!(
        !proof.has_fvar_quick(),
        "the ok-branch proof should be closed (no residual FVars): {proof:?}"
    );
    let proof_ty = ctx
        .infer_type(&proof)
        .expect("the ok-branch proof should have an inferable type");
    assert!(
        ctx.is_def_eq(&proof_ty, &p),
        "the ok-branch proof should have type `P`, got {proof_ty:?}"
    );
}

/// A genuinely-unsupported metaprogramming monad op (`logInfo`) preceding a
/// `throwError` must STILL defer honestly: the body is not executor-interpretable
/// (we cannot run `logInfo`), so NO compound handler is registered and the simple
/// honest-error handler surfaces the static `throwError` message. This pins the
/// 1358 integration shape (`do logInfo "foo"; throwError "error"`).
#[test]
fn test_user_tactic_loginfo_before_throw_error_still_defers_honestly() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "logthrow" : tactic => do logInfo "foo"; throwError "error""#,
    );

    // logInfo is genuinely unsupported, so the whole body defers — no executable
    // compound handler is registered.
    assert!(
        ctx.tactic_registry.get_compound("logthrow").is_none(),
        "a do-body containing an unsupported `logInfo` must defer (no compound handler)"
    );

    // The simple handler still surfaces the static throwError message honestly.
    let entry = ctx
        .tactic_registry
        .get("logthrow")
        .cloned()
        .expect("deferred tactic still registers a simple entry for parsing");
    let mut ps = crate::tactic::ProofState::new(Environment::new(), Expr::prop());
    let err = (entry.handler)(&mut ps, &[])
        .expect_err("a deferred logInfo+throwError body must error honestly");
    assert!(
        err.to_string().contains("error"),
        "the deferred handler must surface the static throwError message `error`, got {err}"
    );
}

/// A user *term* elaborator whose body is `throwError "custom message"` must FAIL
/// elaboration with the user's custom error ([`ElabError::UserThrowError`]),
/// producing no term.
#[test]
fn test_term_elab_throw_error_body_fails_with_custom_message() {
    let env = nat_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "boomterm" : term => throwError "custom message""#,
    );

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    ctx.current_expected_type = Some(nat);

    let surface = parse_expr("boomterm").expect("`boomterm` should parse");
    let err = ctx
        .elaborate(&surface)
        .expect_err("a `throwError \"msg\"` term body must fail, not produce a term");
    assert!(
        matches!(err, ElabError::UserThrowError { ref message } if message == "custom message"),
        "term throwError must surface the typed UserThrowError with the message, got {err:?}"
    );
}

/// A term elaborator computed `if true then throwError "bad" else <ok>` fires the
/// throwError when the condition is decided-true at metaprogram time.
#[test]
fn test_term_elab_computed_if_true_throw_error_fires_with_message() {
    let env = nat_bool_prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "pickThrow" : term => if true then throwError "bad" else Nat.zero"#,
    );

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    ctx.current_expected_type = Some(nat);

    let surface = parse_expr("pickThrow").expect("`pickThrow` should parse");
    let err = ctx
        .elaborate(&surface)
        .expect_err("a decided-true `if` must fire `throwError \"bad\"`, not produce a term");
    assert!(
        matches!(err, ElabError::UserThrowError { ref message } if message == "bad"),
        "the decided-true branch must surface the throwError message `bad`, got {err:?}"
    );
}

/// The bare (non-`do`) terminal form `elab "boom" : tactic => throwError "msg"`
/// — parsed as a single `Term(throwError "msg")` tactic — must also fail with the
/// user's custom error, not mis-dispatch `throwError` as a non-existent tactic.
#[test]
fn test_user_tactic_bare_throw_error_body_fails_with_custom_message() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_elab(
        &mut ctx,
        r#"elab "bareboom" : tactic => throwError "custom message""#,
    );

    let p = Expr::const_(Name::from_string("P"), vec![]);
    ctx.current_expected_type = Some(p);

    let tactics = parse_by(&ctx, "by bareboom");
    let err = ctx
        .elab_by_tactic(&tactics)
        .expect_err("a bare `throwError \"custom message\"` body must fail, not close the goal");
    assert!(
        err.to_string().contains("custom message"),
        "the bare throwError body must surface the user's custom message, got {err}"
    );
}

// ===========================================================================
// Proof-site tactic-mode `do` blocks (`by do …`)
// ===========================================================================
//
// A `do` block in tactic position parses as `ByTactic([Term(Do(elems))])` and
// is run by the SAME do-block executor user-defined `elab … : tactic => do …`
// bodies use (`run_tactic_do_block`). These pin that proof-site `by do …`
// closes goals end-to-end with kernel-checkable proofs, and fails honestly when
// the block leaves the goal open.

/// `by do exact hP` closes `P` directly.
#[test]
fn test_proof_site_do_exact_closes_goal_and_kernel_checks() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    let p = Expr::const_(Name::from_string("P"), vec![]);
    ctx.current_expected_type = Some(p.clone());

    let tactics = parse_by(&ctx, "by do exact hP");
    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("`by do exact hP` should close goal `P`");

    assert!(
        !proof.has_fvar_quick(),
        "proof-site do proof should be closed: {proof:?}"
    );
    let proof_ty = ctx
        .infer_type(&proof)
        .expect("proof-site do proof should have an inferable type");
    assert!(
        ctx.is_def_eq(&proof_ty, &p),
        "proof should have type `P`, got {proof_ty:?}"
    );
}

/// `by do intro h; exact h` closes `P → P` (multi-step run form).
#[test]
fn test_proof_site_do_intro_exact_closes_arrow() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let target = Expr::arrow(p.clone(), p.clone());
    ctx.current_expected_type = Some(target.clone());

    let tactics = parse_by(&ctx, "by do intro h; exact h");
    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("`by do intro h; exact h` should close `P → P`");

    assert!(
        !proof.has_fvar_quick(),
        "proof-site do arrow proof should be closed: {proof:?}"
    );
    let proof_ty = ctx
        .infer_type(&proof)
        .expect("proof should have an inferable type");
    assert!(
        ctx.is_def_eq(&proof_ty, &target),
        "proof should have type `P → P`, got {proof_ty:?}"
    );
}

/// `by do intro hp; intro hpq; exact hpq hp` proves modus ponens
/// `P → (P → Q) → Q`. Exercises the multi-arg `exact hpq hp` application fold.
#[test]
fn test_proof_site_do_modus_ponens_closes_goal() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    // P → (P → Q) → Q
    let target = Expr::arrow(
        p.clone(),
        Expr::arrow(Expr::arrow(p.clone(), q.clone()), q.clone()),
    );
    ctx.current_expected_type = Some(target.clone());

    let tactics = parse_by(&ctx, "by do intro hp; intro hpq; exact hpq hp");
    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("`by do intro hp; intro hpq; exact hpq hp` should prove modus ponens");

    assert!(
        !proof.has_fvar_quick(),
        "modus-ponens proof should be closed: {proof:?}"
    );
    let proof_ty = ctx
        .infer_type(&proof)
        .expect("modus-ponens proof should have an inferable type");
    assert!(
        ctx.is_def_eq(&proof_ty, &target),
        "proof should have type `P → (P → Q) → Q`, got {proof_ty:?}"
    );
}

/// `by do let hp <- intro; let hpq <- intro; exact hpq hp` proves modus ponens
/// via the value-bind form (stateful executor path).
#[test]
fn test_proof_site_do_bind_modus_ponens_closes_goal() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let target = Expr::arrow(
        p.clone(),
        Expr::arrow(Expr::arrow(p.clone(), q.clone()), q.clone()),
    );
    ctx.current_expected_type = Some(target.clone());

    let tactics = parse_by(
        &ctx,
        "by do let hp <- intro; let hpq <- intro; exact hpq hp",
    );
    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("bind-form `by do` should prove modus ponens");

    let proof_ty = ctx
        .infer_type(&proof)
        .expect("bind-form proof should have an inferable type");
    assert!(
        ctx.is_def_eq(&proof_ty, &target),
        "proof should have type `P → (P → Q) → Q`, got {proof_ty:?}"
    );
}

/// NEGATIVE: a `by do` block that does NOT close the goal fails with unsolved
/// goals — it must not silently succeed (no false pass).
#[test]
fn test_proof_site_do_incomplete_fails_unsolved() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    // Goal: P → Q, but the block only intros `hp` and never closes `Q`.
    let target = Expr::arrow(p.clone(), q.clone());
    ctx.current_expected_type = Some(target);

    let tactics = parse_by(&ctx, "by do intro hp");
    let err = ctx
        .elab_by_tactic(&tactics)
        .expect_err("an incomplete `by do` block must fail with unsolved goals, not pass");
    let msg = err.to_string();
    assert!(
        msg.contains("nsolved") || msg.contains("oals"),
        "incomplete do-block should report unsolved goals, got {msg}"
    );
}
