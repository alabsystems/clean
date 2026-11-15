// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for tactic-position macro expansion.
//!
//! A `macro "kw" … : tactic => `(tactic| …)` command and a tactic-position
//! `macro_rules` arm register through the SAME substitute-and-delegate bridge
//! as `elab … : tactic` (`user_tactic`), so the macro EXPANDS at tactic
//! position and the resulting proof kernel-checks. Unsupported shapes reject
//! loudly at the declaration (`conv` heads, unbound antiquotations, unknown
//! macro categories) — fail closed, never a silent registration whose use
//! site could mis-expand.

use super::*;
use clean_parser::parse_expr_with_tactics;

/// `P, Q : Prop` and `hP : P`, plus the foundational pieces tactics rely on.
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

/// Elaborate a `macro` / `macro_rules` / `syntax` declaration; the side effect
/// is the handler registered in `ctx.tactic_registry` (and/or the macro ctx).
fn register_decl(ctx: &mut ElabCtx, src: &str) {
    let patterns = ctx.tactic_registry.tactic_patterns();
    let decl = parse_decl_with_tactics(src, &patterns).expect("declaration should parse");
    ctx.elab_decl(&decl).expect("declaration should register");
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

/// e1 probe shape: a nullary tactic macro (`macro "kw" : tactic =>
/// `(tactic| …)`) must register an executable handler and close its goal with
/// a kernel-checkable proof at the use site.
#[test]
fn test_tactic_macro_nullary_registers_and_expands() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_decl(
        &mut ctx,
        r#"macro "closeP" : tactic => `(tactic| exact hP)"#,
    );
    assert!(
        ctx.tactic_registry.get_compound("closeP").is_some(),
        "tactic macro must register an executable compound handler"
    );

    let p = Expr::const_(Name::from_string("P"), vec![]);
    ctx.current_expected_type = Some(p.clone());

    let tactics = parse_by(&ctx, "by closeP");
    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("tactic macro `closeP` should close goal `P`");

    assert!(
        !proof.has_fvar_quick(),
        "macro-expanded proof should be closed (no residual FVars): {proof:?}"
    );
    let proof_ty = ctx
        .infer_type(&proof)
        .expect("macro-expanded proof should have an inferable (kernel-checkable) type");
    assert!(
        ctx.is_def_eq(&proof_ty, &p),
        "macro-expanded proof should have type `P`, got {proof_ty:?}"
    );
}

/// A bound pattern antiquotation (`$e`) is rewritten to its bound name at
/// registration and substituted with the call-site argument at expansion.
#[test]
fn test_tactic_macro_bound_antiquot_substitutes_call_site_arg() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_decl(
        &mut ctx,
        r#"macro "mexact" e:term : tactic => `(tactic| exact $e)"#,
    );

    let p = Expr::const_(Name::from_string("P"), vec![]);
    ctx.current_expected_type = Some(p.clone());

    let tactics = parse_by(&ctx, "by mexact hP");
    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("tactic macro `mexact hP` should close goal `P`");
    let proof_ty = ctx
        .infer_type(&proof)
        .expect("substituted proof should have an inferable type");
    assert!(
        ctx.is_def_eq(&proof_ty, &p),
        "substituted proof should have type `P`, got {proof_ty:?}"
    );
}

/// e3 probe shape: `syntax "kw" : tactic` + `macro_rules | `(tactic| kw) => …`
/// must register an executable handler for `kw` and close its goal.
#[test]
fn test_tactic_macro_rules_arm_registers_and_expands() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_decl(&mut ctx, r#"syntax "solveP" : tactic"#);
    register_decl(
        &mut ctx,
        r#"macro_rules | `(tactic| solveP) => `(tactic| exact hP)"#,
    );
    assert!(
        ctx.tactic_registry.get_compound("solveP").is_some(),
        "tactic macro_rules arm must register an executable compound handler"
    );

    let p = Expr::const_(Name::from_string("P"), vec![]);
    ctx.current_expected_type = Some(p.clone());

    let tactics = parse_by(&ctx, "by solveP");
    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("macro_rules tactic `solveP` should close goal `P`");
    let proof_ty = ctx
        .infer_type(&proof)
        .expect("macro_rules-expanded proof should have an inferable type");
    assert!(
        ctx.is_def_eq(&proof_ty, &p),
        "macro_rules-expanded proof should have type `P`, got {proof_ty:?}"
    );
}

/// Soundness: a macro-expanded tactic must NOT close a goal it does not
/// legitimately discharge. `closeP` (expanding to `exact hP`, `hP : P`)
/// applied to goal `Q` (`P ≠ Q`) must FAIL — never fabricate a proof of `Q`.
#[test]
fn test_tactic_macro_wrong_proof_fails_to_close_goal() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_decl(
        &mut ctx,
        r#"macro "closeP" : tactic => `(tactic| exact hP)"#,
    );

    let q = Expr::const_(Name::from_string("Q"), vec![]);
    ctx.current_expected_type = Some(q);

    let tactics = parse_by(&ctx, "by closeP");
    let result = ctx.elab_by_tactic(&tactics);
    assert!(
        result.is_err(),
        "tactic macro must not close goal `Q` with a proof of `P`: {result:?}"
    );
}

/// Loud rejection (the former pin, flipped per its own doc comment): a macro
/// whose category is unimplemented AND not a registered syntax category is
/// REJECTED at the declaration — the error names the category and lists the
/// supported ones — never silently skipped into a registration that can
/// never fire.
///
/// The category used to be spelled `calc`. That is a Lean 4.8.0 KEYWORD, so
/// Lean refuses the command before any category lookup ("unexpected token
/// 'calc'; expected identifier", measured 2026-09-27) and Clean's parser now
/// does too (`clean_parser::lean_keywords`); the elaborator's rejection is
/// exercised with the non-keyword unknown category `calcx` (Lean: "unknown
/// parser `calcx`").
#[test]
fn test_unknown_category_macro_rejected_loudly() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    let patterns = ctx.tactic_registry.tactic_patterns();
    let keyword = parse_decl_with_tactics(r#"macro "clc" : calc => `(calc| _)"#, &patterns)
        .expect_err("`calc` is a Lean keyword, not a category name");
    assert!(
        format!("{keyword:?}").contains("keyword in Lean 4.8.0"),
        "the refusal must say why: {keyword:?}"
    );

    let decl = parse_decl_with_tactics(r#"macro "clc" : calcx => `(calcx| _)"#, &patterns)
        .expect("declaration should parse");
    let err = ctx
        .elab_decl(&decl)
        .expect_err("an unknown-category macro must be rejected (fail closed)");
    assert!(
        matches!(&err, ElabError::MacroError(msg)
            if msg.contains("calcx") && msg.contains("term") && msg.contains("command")),
        "rejection should name the category and list supported ones, got {err:?}"
    );
}

/// The user-typo scenario the gate exists for: `: tatic` (for `: tactic`)
/// must be a loud error naming the typo'd category — previously the
/// declaration vanished without a trace.
#[test]
fn test_typo_category_macro_rejected_loudly() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    let patterns = ctx.tactic_registry.tactic_patterns();
    let decl = parse_decl_with_tactics(r#"macro "tt" : tatic => `(tactic| skip)"#, &patterns)
        .expect("declaration should parse");
    let err = ctx
        .elab_decl(&decl)
        .expect_err("a typo'd macro category must be rejected (fail closed)");
    assert!(
        matches!(&err, ElabError::MacroError(msg) if msg.contains("tatic")),
        "rejection should name the typo'd category, got {err:?}"
    );
}

/// NEEDS-SUPPORT, not rejection: `attr` is a registered built-in syntax
/// category that Mathlib declares load-bearing macros in (`simps?`,
/// `continuity`, `to_additive?`), so it must stay on the historical skip
/// path until the attr position learns to expand macros.
#[test]
fn test_attr_category_macro_still_skipped_not_rejected() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    let patterns = ctx.tactic_registry.tactic_patterns();
    let decl = parse_decl_with_tactics(r#"macro "aat" : attr => `(attr| _)"#, &patterns)
        .expect("declaration should parse");
    let result = ctx.elab_decl(&decl);
    assert!(
        matches!(result, Ok(ElabResult::Skipped)),
        "attr-category macro must stay on the skip path (needs-support), got {result:?}"
    );
}

/// A category the user declared with `declare_syntax_cat` is legitimate:
/// the unknown-category gate must not reject macros declared in it.
#[test]
fn test_declared_syntax_cat_macro_not_rejected() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    register_decl(&mut ctx, "declare_syntax_cat widget");
    let patterns = ctx.tactic_registry.tactic_patterns();
    let decl = parse_decl_with_tactics(r#"macro "wid" : widget => `(widget| _)"#, &patterns)
        .expect("declaration should parse");
    let result = ctx.elab_decl(&decl);
    assert!(
        matches!(result, Ok(ElabResult::Skipped)),
        "declare_syntax_cat category macro must not be rejected, got {result:?}"
    );
}

/// Fail closed: a `(conv| …)` expansion under `: tactic` is a category this
/// route cannot execute — rejected loudly at the declaration.
#[test]
fn test_tactic_macro_with_conv_expansion_rejected_cleanly() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    let patterns = ctx.tactic_registry.tactic_patterns();
    let decl = parse_decl_with_tactics(r#"macro "cnv2" : tactic => `(conv| lhs)"#, &patterns)
        .expect("declaration should parse");
    let err = ctx
        .elab_decl(&decl)
        .expect_err("a conv-headed expansion must be rejected (fail closed)");
    assert!(
        matches!(&err, ElabError::MacroError(msg) if msg.contains("conv")),
        "conv-headed expansion rejection should name conv, got {err:?}"
    );
}

/// Fail closed: an antiquotation the pattern does not bind must be rejected
/// at the declaration — substituting it silently would mis-expand at every
/// use site.
#[test]
fn test_tactic_macro_unbound_antiquot_rejected_cleanly() {
    let env = prop_env();
    let mut ctx = ElabCtx::new(&env);

    let patterns = ctx.tactic_registry.tactic_patterns();
    let decl = parse_decl_with_tactics(
        r#"macro "loose" : tactic => `(tactic| exact $missing)"#,
        &patterns,
    )
    .expect("declaration should parse");
    let err = ctx
        .elab_decl(&decl)
        .expect_err("an unbound antiquotation must be rejected (fail closed)");
    assert!(
        matches!(&err, ElabError::MacroError(msg) if msg.contains("antiquotation")),
        "unbound-antiquotation rejection should name the antiquotation, got {err:?}"
    );
}
