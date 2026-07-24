// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structural recursion detection tests

use super::*;

fn recursive_extra_param(name: &str, binder_info: BinderInfo) -> RecursiveExtraParam {
    RecursiveExtraParam {
        name: name.to_string(),
        binder_info,
    }
}

// =============================================================================
// Tests for structural recursion detection (#381)
// =============================================================================

#[test]
fn test_is_match_on_decreasing_arg_basic() {
    use clean_parser::{Span, SurfaceExpr};

    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // Set up a recursive def context
    ctx.recursive_def_ctx = Some(RecursiveDefContext {
        func_name: "f".to_string(),
        decreasing_arg_pos: 0,
        decreasing_arg_name: "n".to_string(),
        inductive_type_name: None,
        ih_fvar: None,
        ih_type: None,
        ih_map: HashMap::new(),
        sibling_names: Vec::new(),
        extra_params: vec![],
        wf_measure: None,
    });

    // Test: scrutinee matches decreasing arg
    let scrutinee = SurfaceExpr::Ident(Span::new(0, 1), "n".to_string());
    assert!(ctx.is_match_on_decreasing_arg(&scrutinee));

    // Test: scrutinee doesn't match
    let scrutinee2 = SurfaceExpr::Ident(Span::new(0, 1), "m".to_string());
    assert!(!ctx.is_match_on_decreasing_arg(&scrutinee2));

    // Test: parenthesized scrutinee matches
    let scrutinee3 = SurfaceExpr::Paren(
        Span::new(0, 3),
        Box::new(SurfaceExpr::Ident(Span::new(1, 2), "n".to_string())),
    );
    assert!(ctx.is_match_on_decreasing_arg(&scrutinee3));

    // Test: deeply nested parens ((n)) should also match
    let scrutinee4 = SurfaceExpr::Paren(
        Span::new(0, 5),
        Box::new(SurfaceExpr::Paren(
            Span::new(1, 4),
            Box::new(SurfaceExpr::Ident(Span::new(2, 3), "n".to_string())),
        )),
    );
    assert!(ctx.is_match_on_decreasing_arg(&scrutinee4));
}

#[test]
fn test_is_match_on_decreasing_arg_no_context() {
    use clean_parser::{Span, SurfaceExpr};

    let env = Environment::new();
    let ctx = ElabCtx::new(&env);

    // Without recursive context, should always return false
    let scrutinee = SurfaceExpr::Ident(Span::new(0, 1), "n".to_string());
    assert!(!ctx.is_match_on_decreasing_arg(&scrutinee));
}

/// Test that recursive call substitution with IH works correctly (#381)
/// When elaborating `f k` where `k` is a pattern var with an IH,
/// the recursive call should be replaced with the IH fvar.
#[test]
fn test_recursive_call_ih_substitution() {
    use clean_parser::{Span, SurfaceArg, SurfaceExpr};

    let mut env = Environment::new();
    env.init_nat().expect("init_nat should succeed");

    let mut ctx = ElabCtx::new(&env);

    // Create a fresh IH fvar to use in the test
    let ih_fvar = ctx.push_local(
        "ih_k".to_string(),
        Expr::const_(Name::from_string("Nat"), vec![]),
    );

    // Set up recursive context: function "f" with decreasing arg at position 0
    let mut ih_map = HashMap::new();
    ih_map.insert("k".to_string(), ih_fvar);

    ctx.recursive_def_ctx = Some(RecursiveDefContext {
        func_name: "f".to_string(),
        decreasing_arg_pos: 0,
        decreasing_arg_name: "n".to_string(),
        inductive_type_name: Some(Name::from_string("Nat")),
        ih_fvar: Some(ih_fvar),
        ih_type: Some(Expr::const_(Name::from_string("Nat"), vec![])),
        ih_map,
        sibling_names: Vec::new(),
        extra_params: vec![],
        wf_measure: None,
    });

    // Build surface expression: f k
    // This is a recursive call where k is a pattern variable with an IH
    let surface = SurfaceExpr::App(
        Span::new(0, 3),
        Box::new(SurfaceExpr::Ident(Span::new(0, 1), "f".to_string())),
        vec![SurfaceArg::positional(SurfaceExpr::Ident(
            Span::new(2, 3),
            "k".to_string(),
        ))],
    );

    // Elaborate the expression - should substitute recursive call with IH
    let result = ctx.elaborate(&surface);

    // The result should be the IH fvar, not an application of f
    match result {
        Ok(expr) => {
            // The expression should be an FVar (the IH)
            assert!(
                matches!(expr.kind(), ExprKind::FVar(fv) if *fv == ih_fvar),
                "Expected recursive call f k to be replaced with ih_k, got: {expr:?}"
            );
        }
        Err(e) => {
            // Elaboration errors are not expected for this simple case
            panic!("Elaboration failed unexpectedly: {e:?}");
        }
    }

    ctx.pop_local(); // clean up the pushed local
}

/// Test that recursive fields are correctly identified from recursor rules (#381)
/// For Nat.succ, the single field (the predecessor) should be marked as recursive.
#[test]
fn test_nat_recursive_field_detection() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat should succeed");

    // Get Nat.rec and check its rules
    let nat_rec = env.get_recursor(&Name::from_string("Nat.rec"));
    assert!(nat_rec.is_some(), "Nat.rec should exist after init_nat");

    let rec_val = nat_rec.unwrap();

    // Nat.rec should have 2 rules: one for zero, one for succ
    assert_eq!(rec_val.rules.len(), 2, "Nat.rec should have 2 rules");

    // Find the succ rule
    let succ_rule = rec_val
        .rules
        .iter()
        .find(|r| r.constructor_name == Name::from_string("Nat.succ"))
        .expect("Nat.succ rule should exist");

    // Nat.succ has 1 field (the predecessor), which IS recursive (refers to Nat)
    assert_eq!(succ_rule.num_fields, 1, "Nat.succ has 1 field");
    assert_eq!(
        succ_rule.recursive_fields,
        vec![true],
        "Nat.succ's field should be marked as recursive"
    );

    // Find the zero rule
    let zero_rule = rec_val
        .rules
        .iter()
        .find(|r| r.constructor_name == Name::from_string("Nat.zero"))
        .expect("Nat.zero rule should exist");

    // Nat.zero has 0 fields
    assert_eq!(zero_rule.num_fields, 0, "Nat.zero has 0 fields");
    assert!(
        zero_rule.recursive_fields.is_empty(),
        "Nat.zero has no recursive fields"
    );
}

#[test]
fn test_recursive_numeral_add_arm_includes_ih_binder() {
    use clean_parser::{Span, SurfaceMatchArm, SurfacePattern};

    fn lambda_depth(expr: &Expr) -> usize {
        match expr.kind() {
            ExprKind::Lam(_, _, body) => 1 + lambda_depth(body),
            _ => 0,
        }
    }

    let mut env = Environment::new();
    env.init_nat().expect("init_nat should succeed");

    let mut ctx = ElabCtx::new(&env);
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let arm = SurfaceMatchArm {
        span: Span::dummy(),
        pattern: SurfacePattern::NumeralAdd(Box::new(SurfacePattern::Var("k".to_string())), 1),
        body: SurfaceExpr::Ident(Span::dummy(), "k".to_string()),
    };

    let alt = ctx
        .elaborate_match_arm(&arm, 1, "Nat", &nat_ty, &nat_ty, &[], true)
        .expect("recursive numeral-add arm should elaborate");

    assert_eq!(
        lambda_depth(&alt),
        2,
        "Nat.rec succ case should bind predecessor and IH, got {alt:?}"
    );
}

#[test]
fn test_recursive_numeral_add_offset_two_arm_fails_closed() {
    use clean_parser::{Span, SurfaceMatchArm, SurfacePattern};

    let mut env = Environment::new();
    env.init_nat().expect("init_nat should succeed");

    let mut ctx = ElabCtx::new(&env);
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let arm = SurfaceMatchArm {
        span: Span::dummy(),
        pattern: SurfacePattern::NumeralAdd(Box::new(SurfacePattern::Var("k".to_string())), 2),
        body: SurfaceExpr::Ident(Span::dummy(), "k".to_string()),
    };

    let result = ctx.elaborate_match_arm(&arm, 1, "Nat", &nat_ty, &nat_ty, &[], true);
    assert!(
        matches!(result, Err(ElabError::NotImplemented(ref msg)) if msg.contains("recursive `n + 2` numeral-add patterns")),
        "recursive `n + 2` numeral-add arm should fail closed when reached directly; \
         course-of-values defs are routed away by the decl-level pair-threading \
         transform (see `course_of_values.rs`) before reaching this arm, so this \
         guard remains a defensive fail-closed for unhandled shapes, got {result:?}"
    );
}

/// End-to-end course-of-values recursion: the canonical two-prior `fib`-shape
/// (`| n + 2 => fib (n+1) + fib n`) must elaborate, register, kernel-check, and
/// COMPUTE the real Fibonacci numbers. The decl-level pair-threading transform
/// (`course_of_values.rs`) rewrites it into a single-step auxiliary `fib.cov :
/// Nat → Nat × Nat` plus a projecting wrapper, both lowered via the existing
/// `Nat.rec` (#20) and `Prod` matcher (#21) — no `brecOn`/`below`, no new IR
/// lowering, no axioms.
#[test]
fn test_course_of_values_fib_lowers_and_computes() {
    let src = r"def fib : Nat → Nat
        | 0 => 0
        | 1 => 1
        | n + 2 => fib (n + 1) + fib n";

    let mut env = Environment::with_prelude();
    let decl = parse_decl_for_elab(src).expect("fib equation def should parse");

    let result = crate::elaborate_decl_and_register(&mut env, &decl)
        .expect("course-of-values fib should elaborate and kernel-check");

    // The transform emits two declarations.
    assert!(
        matches!(result, crate::ElabResult::Multiple(ref rs) if rs.len() == 2),
        "course-of-values fib should produce two declarations (aux + wrapper), got {result:?}"
    );

    // Both the wrapper and its auxiliary must be registered.
    assert!(
        env.get_const(&Name::from_string("fib")).is_some(),
        "fib wrapper should be registered"
    );
    let aux = env
        .get_const(&Name::from_string("fib.cov"))
        .expect("fib.cov auxiliary should be registered");

    // The auxiliary is the actual recursion: single-step structural via Nat.rec.
    let aux_val = aux
        .value
        .as_ref()
        .expect("registered auxiliary keeps its value term");
    assert!(
        theorem_proof_uses_const(aux_val, "Nat.rec"),
        "course-of-values auxiliary should be compiled via single-step Nat.rec, got {aux_val:?}"
    );

    // Soundness witness: the closure must contain NO domain-specific or
    // termination axioms — this is genuine `Nat.rec`/`Prod` recursion, not a
    // faked `sorryAx` / fabricated termination axiom.
    let deps = env
        .axiom_deps(&Name::from_string("fib"))
        .expect("fib is registered, axiom_deps should return Some");
    let dep_names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
    assert!(
        !dep_names
            .iter()
            .any(|n| n.contains("sorry") || n.contains("termination")),
        "course-of-values fib must not depend on sorry/termination axioms, got {dep_names:?}"
    );

    // Computational soundness: `rfl` only checks when the kernel REDUCES the
    // lowered term to the right numeral. Distinct, correct Fibonacci values prove
    // real two-back recursion (not a hardcoded constant).
    register_rfl_check(&mut env, "fib_0", "fib 0", "0");
    register_rfl_check(&mut env, "fib_1", "fib 1", "1");
    register_rfl_check(&mut env, "fib_2", "fib 2", "1");
    register_rfl_check(&mut env, "fib_6", "fib 6", "8");
    register_rfl_check(&mut env, "fib_7", "fib 7", "13");
    register_rfl_check(&mut env, "fib_10", "fib 10", "55");
}

// =============================================================================
// Tests for LiftMethod recursion detection (structural.rs:333)
// Covers: find_recursive_calls through SurfaceExpr::LiftMethod — ZERO previous coverage
// =============================================================================

#[test]
fn test_detect_recursion_through_lift_method() {
    use crate::infer::structural::{detect_recursion, RecursiveArg};
    use clean_parser::{Span, SurfaceArg, SurfaceExpr};

    // def f x := do let y <- f x; pure y
    // The recursive call `f x` is wrapped in LiftMethod(<- f x)
    let recursive_call = SurfaceExpr::App(
        Span::new(0, 0),
        Box::new(SurfaceExpr::Ident(Span::new(0, 0), "f".to_string())),
        vec![SurfaceArg::positional(SurfaceExpr::Ident(
            Span::new(0, 0),
            "x".to_string(),
        ))],
    );
    let body = SurfaceExpr::LiftMethod(Span::new(0, 0), Box::new(recursive_call));
    let info = detect_recursion("f", &body);
    assert!(
        info.is_recursive,
        "Should detect recursive call through LiftMethod wrapper"
    );
    assert_eq!(info.calls.len(), 1);
    assert!(matches!(info.calls[0].args[0], RecursiveArg::Var(ref n) if n == "x"));
}

#[test]
fn test_detect_recursion_lift_method_no_call() {
    use crate::infer::structural::detect_recursion;
    use clean_parser::{Span, SurfaceArg, SurfaceExpr};

    // def f x := do let y <- g x; pure y
    // LiftMethod wraps a non-recursive call — should not detect recursion
    let non_recursive_call = SurfaceExpr::App(
        Span::new(0, 0),
        Box::new(SurfaceExpr::Ident(Span::new(0, 0), "g".to_string())),
        vec![SurfaceArg::positional(SurfaceExpr::Ident(
            Span::new(0, 0),
            "x".to_string(),
        ))],
    );
    let body = SurfaceExpr::LiftMethod(Span::new(0, 0), Box::new(non_recursive_call));
    let info = detect_recursion("f", &body);
    assert!(
        !info.is_recursive,
        "Should not detect recursion for non-recursive LiftMethod"
    );
    assert!(info.calls.is_empty());
}

#[test]
fn test_detect_recursion_nested_lift_method_in_app() {
    use crate::infer::structural::{detect_recursion, RecursiveArg};
    use clean_parser::{Span, SurfaceArg, SurfaceExpr};

    // def f x := h (<- f x)
    // App(h, [LiftMethod(App(f, [x]))])
    let recursive_call = SurfaceExpr::App(
        Span::new(0, 0),
        Box::new(SurfaceExpr::Ident(Span::new(0, 0), "f".to_string())),
        vec![SurfaceArg::positional(SurfaceExpr::Ident(
            Span::new(0, 0),
            "x".to_string(),
        ))],
    );
    let body = SurfaceExpr::App(
        Span::new(0, 0),
        Box::new(SurfaceExpr::Ident(Span::new(0, 0), "h".to_string())),
        vec![SurfaceArg::positional(SurfaceExpr::LiftMethod(
            Span::new(0, 0),
            Box::new(recursive_call),
        ))],
    );
    let info = detect_recursion("f", &body);
    assert!(
        info.is_recursive,
        "Should detect recursion through LiftMethod nested in App argument"
    );
    assert_eq!(info.calls.len(), 1);
    assert!(matches!(info.calls[0].args[0], RecursiveArg::Var(ref n) if n == "x"));
}

/// Test that recursive call substitution applies extra params to IH (#1386).
///
/// For `def lift_at (e : KExpr) (cutoff : Nat) : KExpr`, where `e` is the
/// decreasing arg and `cutoff` is an extra param, a recursive call like
/// `lift_at k (Nat.succ cutoff)` should produce `App(ih_k, Nat.succ cutoff)`
/// rather than just `ih_k`.
#[test]
fn test_recursive_call_ih_with_extra_params() {
    use clean_parser::{Span, SurfaceArg, SurfaceExpr};

    let mut env = Environment::new();
    env.init_nat().expect("init_nat should succeed");

    let mut ctx = ElabCtx::new(&env);

    // Push local "cutoff : Nat" — the extra param
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let _cutoff_fvar = ctx.push_local("cutoff".to_string(), nat_ty.clone());

    // Create IH with generalized type: Nat → Nat (takes cutoff, returns Nat)
    let ih_type = Expr::pi(BinderInfo::Default, nat_ty.clone(), nat_ty.clone());
    let ih_fvar = ctx.push_local("ih_k".to_string(), ih_type);

    let mut ih_map = HashMap::new();
    ih_map.insert("k".to_string(), ih_fvar);

    ctx.recursive_def_ctx = Some(RecursiveDefContext {
        func_name: "lift_at".to_string(),
        decreasing_arg_pos: 0,
        decreasing_arg_name: "e".to_string(),
        inductive_type_name: Some(Name::from_string("Nat")),
        ih_fvar: Some(ih_fvar),
        ih_type: Some(nat_ty),
        ih_map,
        sibling_names: Vec::new(),
        extra_params: vec![recursive_extra_param("cutoff", BinderInfo::Default)],
        wf_measure: None,
    });

    // Build surface expression: lift_at k (Nat.succ cutoff)
    // Position 0 is the decreasing arg "k", position 1 is the extra param value
    let surface = SurfaceExpr::App(
        Span::new(0, 10),
        Box::new(SurfaceExpr::Ident(Span::new(0, 7), "lift_at".to_string())),
        vec![
            SurfaceArg::positional(SurfaceExpr::Ident(Span::new(8, 9), "k".to_string())),
            SurfaceArg::positional(SurfaceExpr::App(
                Span::new(10, 25),
                Box::new(SurfaceExpr::Ident(
                    Span::new(10, 18),
                    "Nat.succ".to_string(),
                )),
                vec![SurfaceArg::positional(SurfaceExpr::Ident(
                    Span::new(19, 25),
                    "cutoff".to_string(),
                ))],
            )),
        ],
    );

    let result = ctx.elaborate(&surface);

    match result {
        Ok(expr) => {
            // The result should be App(ih_k, <elaborated Nat.succ cutoff>)
            // NOT just ih_k (which would be wrong without extra param application)
            assert!(
                matches!(expr.kind(), ExprKind::App(_, _)),
                "Expected App(ih_k, ...) for recursive call with extra params, got: {expr:?}"
            );
            // The function part should be the IH fvar
            let fn_part = expr.get_app_fn();
            assert!(
                matches!(fn_part.kind(), ExprKind::FVar(fv) if *fv == ih_fvar),
                "Expected ih_k as function, got: {fn_part:?}"
            );
            // Should have exactly 1 argument (the extra param value)
            let args = expr.get_app_args();
            assert_eq!(
                args.len(),
                1,
                "Expected 1 extra param argument, got {}",
                args.len()
            );
        }
        Err(e) => {
            panic!("Elaboration failed unexpectedly: {e:?}");
        }
    }

    ctx.pop_local();
    ctx.pop_local(); // ih_k, cutoff
}

/// Test that recursive call substitution replays omitted implicit extra params
/// from the local context before explicit extra params (#2013).
#[test]
fn test_recursive_call_ih_with_implicit_and_explicit_extra_params() {
    use clean_parser::{Span, SurfaceArg, SurfaceExpr};

    let mut env = Environment::new();
    env.init_nat().expect("init_nat should succeed");

    let mut ctx = ElabCtx::new(&env);

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let inst_fvar = ctx.push_local("inst".to_string(), nat_ty.clone());
    let x_fvar = ctx.push_local("x".to_string(), nat_ty.clone());

    // IH generalizes over the omitted implicit argument and the explicit one.
    let ih_type = Expr::pi(
        BinderInfo::Implicit,
        nat_ty.clone(),
        Expr::pi(BinderInfo::Default, nat_ty.clone(), nat_ty.clone()),
    );
    let ih_fvar = ctx.push_local("ih_k".to_string(), ih_type);

    let mut ih_map = HashMap::new();
    ih_map.insert("k".to_string(), ih_fvar);

    ctx.recursive_def_ctx = Some(RecursiveDefContext {
        func_name: "carryImplicit".to_string(),
        decreasing_arg_pos: 0,
        decreasing_arg_name: "n".to_string(),
        inductive_type_name: Some(Name::from_string("Nat")),
        ih_fvar: Some(ih_fvar),
        ih_type: Some(nat_ty),
        ih_map,
        sibling_names: Vec::new(),
        extra_params: vec![
            recursive_extra_param("inst", BinderInfo::Implicit),
            recursive_extra_param("x", BinderInfo::Default),
        ],
        wf_measure: None,
    });

    let surface = SurfaceExpr::App(
        Span::new(0, 20),
        Box::new(SurfaceExpr::Ident(
            Span::new(0, 13),
            "carryImplicit".to_string(),
        )),
        vec![
            SurfaceArg::positional(SurfaceExpr::Ident(Span::new(14, 15), "k".to_string())),
            SurfaceArg::positional(SurfaceExpr::Ident(Span::new(16, 17), "x".to_string())),
        ],
    );

    let result = ctx.elaborate(&surface).expect(
        "recursive call with implicit and explicit extra params should elaborate to IH app",
    );

    let fn_part = result.get_app_fn();
    assert!(
        matches!(fn_part.kind(), ExprKind::FVar(fv) if *fv == ih_fvar),
        "Expected ih_k as function, got: {fn_part:?}"
    );

    let args = result.get_app_args();
    assert_eq!(args.len(), 2, "Expected implicit and explicit extra args");
    assert!(
        matches!(args[0].kind(), ExprKind::FVar(fv) if *fv == inst_fvar),
        "Expected first extra arg to reuse implicit inst local, got: {:?}",
        args[0]
    );
    assert!(
        matches!(args[1].kind(), ExprKind::FVar(fv) if *fv == x_fvar),
        "Expected second extra arg to be explicit x local, got: {:?}",
        args[1]
    );

    ctx.pop_local();
    ctx.pop_local();
    ctx.pop_local(); // ih_k, x, inst
}

// =============================================================================
// Tests for recursive theorem termination hints (#1132, B57)
// =============================================================================

/// Walk an expression looking for a `Const` whose name equals `needle`.
fn theorem_proof_uses_const(expr: &Expr, needle: &str) -> bool {
    match expr.kind() {
        ExprKind::Const(name, _) => name.to_string() == needle,
        ExprKind::App(f, a) => {
            theorem_proof_uses_const(f, needle) || theorem_proof_uses_const(a, needle)
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            theorem_proof_uses_const(ty, needle) || theorem_proof_uses_const(body, needle)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            theorem_proof_uses_const(ty, needle)
                || theorem_proof_uses_const(val, needle)
                || theorem_proof_uses_const(body, needle)
        }
        ExprKind::MData(_, inner) | ExprKind::Squash(inner) | ExprKind::Proj(_, _, inner) => {
            theorem_proof_uses_const(inner, needle)
        }
        _ => false,
    }
}

/// A recursive theorem (its proof recurses structurally on `n`) must elaborate,
/// register, and pass the full kernel type check. Previously the theorem path
/// ignored recursion entirely (`recursive_def_ctx` was never installed), so the
/// recursive call `rec_thm_true k` was treated as a self-reference and failed to
/// elaborate. With termination-hint handling ported from the definition path,
/// the recursive call is replaced with the induction hypothesis and the proof
/// is lowered through `Nat.rec`.
#[test]
fn test_recursive_theorem_structural_elaborates_and_kernel_checks() {
    let src = r"theorem rec_thm_true (n : Nat) : True := match n with
        | 0 => True.intro
        | k + 1 => rec_thm_true k";

    let mut env = Environment::with_prelude();
    let decl = parse_decl_for_elab(src).expect("recursive theorem should parse");

    let result = crate::elaborate_decl_and_register(&mut env, &decl)
        .expect("recursive theorem should elaborate and kernel-check");

    assert!(
        matches!(result, crate::ElabResult::Theorem { .. }),
        "expected a Theorem result, got {result:?}"
    );

    // Registration runs the full kernel type check, so a registered constant
    // is a genuinely well-typed proof term. Confirm it was lowered through the
    // recursor (the structural-recursion IH path), not left as a self-reference.
    let constant = env
        .get_const(&Name::from_string("rec_thm_true"))
        .expect("rec_thm_true should be registered");
    let proof = constant
        .value
        .as_ref()
        .expect("registered theorem keeps its proof term");
    assert!(
        theorem_proof_uses_const(proof, "Nat.rec"),
        "recursive theorem proof should be compiled via Nat.rec, got {proof:?}"
    );
}

/// A recursive theorem with an explicit `termination_by` measure must also
/// elaborate and kernel-check rather than ignoring the hint. This exercises the
/// well-founded lowering branch reached through the shared `setup_recursion`
/// helper from the theorem path.
#[test]
fn test_recursive_theorem_termination_by_elaborates_and_kernel_checks() {
    let src = r"theorem rec_thm_true_wf (n : Nat) : True := match n with
        | 0 => True.intro
        | k + 1 => rec_thm_true_wf k
        termination_by n";

    let mut env = Environment::with_prelude();
    let decl =
        parse_decl_for_elab(src).expect("recursive theorem with termination_by should parse");

    let result = crate::elaborate_decl_and_register(&mut env, &decl)
        .expect("recursive theorem with termination_by should elaborate and kernel-check");

    assert!(
        matches!(result, crate::ElabResult::Theorem { .. }),
        "expected a Theorem result, got {result:?}"
    );
    assert!(
        env.get_const(&Name::from_string("rec_thm_true_wf"))
            .is_some(),
        "rec_thm_true_wf should be registered"
    );
}

/// Guard the common case: a non-recursive theorem must NOT enter the recursion
/// path and must elaborate exactly as before.
#[test]
fn test_non_recursive_theorem_unaffected_by_termination_handling() {
    let src = r"theorem refl_thm (n : Nat) : n = n := rfl";

    let mut env = Environment::with_prelude();
    let decl = parse_decl_for_elab(src).expect("non-recursive theorem should parse");

    let result = crate::elaborate_decl_and_register(&mut env, &decl)
        .expect("non-recursive theorem should elaborate and kernel-check");

    assert!(
        matches!(result, crate::ElabResult::Theorem { .. }),
        "expected a Theorem result, got {result:?}"
    );

    // The proof must remain `rfl`, not be rewritten through a recursor.
    let constant = env
        .get_const(&Name::from_string("refl_thm"))
        .expect("refl_thm should be registered");
    let proof = constant
        .value
        .as_ref()
        .expect("registered theorem keeps its proof term");
    assert!(
        !theorem_proof_uses_const(proof, "Nat.rec"),
        "non-recursive theorem proof must not be compiled via Nat.rec, got {proof:?}"
    );
}

// =============================================================================
// Tests for equation-form recursive defs (Task 3, slice 1)
//
// `def f : A → B | pat => ...` is desugared by the parser into a value
// `PatternMatchLambda([_x], Match(_x, arms))` with an EMPTY declaration binder
// list (the arrow type lives in `ty`). `normalize_equation_def` lifts the
// synthetic `_x` lambda binder into a real declaration binder by peeling one
// domain off the arrow/Pi type, turning the equation def into the named-binder
// + `match` shape that already lowers structural recursion via the inductive's
// `.rec`. These tests assert that lowering really happens (the registered value
// uses `T.rec`) and that registration's full kernel type check succeeds — the
// soundness witness, identical to the proven named-binder defs.
// =============================================================================

/// Equation-form factorial on `Nat` must elaborate, register, and kernel-check,
/// and its value must be compiled via `Nat.rec` (genuine structural recursion,
/// no faked termination). Before slice 1 this failed with `TooManyArguments`
/// because the self-name `factorial` was left as a placeholder typed `Nat`.
#[test]
fn test_equation_form_factorial_lowers_via_nat_rec() {
    let src = r"def factorial : Nat → Nat
        | 0 => 1
        | Nat.succ n => Nat.mul (Nat.succ n) (factorial n)";

    let mut env = Environment::with_prelude();
    let decl = parse_decl_for_elab(src).expect("equation-form factorial should parse");

    let result = crate::elaborate_decl_and_register(&mut env, &decl)
        .expect("equation-form factorial should elaborate and kernel-check");

    assert!(
        matches!(result, crate::ElabResult::Definition { .. }),
        "expected a Definition result, got {result:?}"
    );

    let constant = env
        .get_const(&Name::from_string("factorial"))
        .expect("factorial should be registered");
    let val = constant
        .value
        .as_ref()
        .expect("registered definition keeps its value term");
    assert!(
        theorem_proof_uses_const(val, "Nat.rec"),
        "recursive equation def should be compiled via Nat.rec, got {val:?}"
    );
}

/// A second inductive (`List`) exercises the generic `.rec` lowering: an
/// equation-form length function on `List Nat` must lower via `List.rec` and
/// kernel-check.
#[test]
fn test_equation_form_list_length_lowers_via_list_rec() {
    let src = r"def listLen : List Nat → Nat
        | List.nil => 0
        | List.cons _ t => Nat.succ (listLen t)";

    let mut env = Environment::with_prelude();
    let decl = parse_decl_for_elab(src).expect("equation-form list length should parse");

    let result = crate::elaborate_decl_and_register(&mut env, &decl)
        .expect("equation-form list length should elaborate and kernel-check");

    assert!(
        matches!(result, crate::ElabResult::Definition { .. }),
        "expected a Definition result, got {result:?}"
    );

    let constant = env
        .get_const(&Name::from_string("listLen"))
        .expect("listLen should be registered");
    let val = constant
        .value
        .as_ref()
        .expect("registered definition keeps its value term");
    assert!(
        theorem_proof_uses_const(val, "List.rec"),
        "recursive equation def on List should be compiled via List.rec, got {val:?}"
    );
}

/// Guard: a NON-recursive equation def must still lower via the case analysis
/// recursor (`Bool.casesOn` / `Bool.rec`) and must NOT be rewritten as a
/// structural-recursion `.rec` over a decreasing argument. Normalization lifts
/// the binder either way, but recursion detection finds no self-call, so no IH
/// context is installed — the body is plain pattern matching, unchanged.
#[test]
fn test_equation_form_non_recursive_bool_unchanged() {
    let src = r"def negate : Bool → Bool
        | true => false
        | false => true";

    let mut env = Environment::with_prelude();
    let decl = parse_decl_for_elab(src).expect("non-recursive equation def should parse");

    let result = crate::elaborate_decl_and_register(&mut env, &decl)
        .expect("non-recursive equation def should elaborate and kernel-check");

    assert!(
        matches!(result, crate::ElabResult::Definition { .. }),
        "expected a Definition result, got {result:?}"
    );

    let constant = env
        .get_const(&Name::from_string("negate"))
        .expect("negate should be registered");
    let val = constant
        .value
        .as_ref()
        .expect("registered definition keeps its value term");
    // Lowered via Bool case analysis, not a Nat structural recursor.
    assert!(
        theorem_proof_uses_const(val, "Bool.casesOn") || theorem_proof_uses_const(val, "Bool.rec"),
        "non-recursive Bool equation def should lower via Bool.casesOn/Bool.rec, got {val:?}"
    );
    assert!(
        !theorem_proof_uses_const(val, "Nat.rec"),
        "non-recursive equation def must not be compiled via Nat.rec, got {val:?}"
    );
}

/// Regression guard: a NON-recursive MULTI-ARG equation def must still
/// elaborate and kernel-check. As of slice 2, `normalize_equation_def_multiarg`
/// lifts the single `_x` binder into N named binders and rewrites the `Prod.mk`
/// tuple match into a single-scrutinee match on the decreasing position (here
/// the first `Nat`), with `m` folded into the motive. Since no self-call
/// exists, no IH context is installed and the body is plain case analysis —
/// this guards that the widened normalization keeps non-recursive multi-arg
/// defs sound. (Computational correctness is checked in
/// `test_equation_form_multiarg_non_recursive_computes`.)
#[test]
fn test_equation_form_multiarg_non_recursive_still_elaborates() {
    let src = r"def addCases : Nat → Nat → Nat
        | 0, m => m
        | Nat.succ n, m => Nat.succ (Nat.add n m)";

    let mut env = Environment::with_prelude();
    let decl = parse_decl_for_elab(src).expect("multi-arg equation def should parse");

    let result = crate::elaborate_decl_and_register(&mut env, &decl)
        .expect("multi-arg non-recursive equation def should elaborate and kernel-check");

    assert!(
        matches!(result, crate::ElabResult::Definition { .. }),
        "expected a Definition result, got {result:?}"
    );
    assert!(
        env.get_const(&Name::from_string("addCases")).is_some(),
        "addCases should be registered"
    );
}

/// Equation-form recursive THEOREM must also normalize and lower via `Nat.rec`,
/// mirroring the definition path. (The named-binder theorem variant is already
/// covered by `test_recursive_theorem_structural_elaborates_and_kernel_checks`.)
#[test]
fn test_equation_form_recursive_theorem_lowers_via_nat_rec() {
    let src = r"theorem eqn_thm_true : Nat → True
        | 0 => True.intro
        | Nat.succ k => eqn_thm_true k";

    let mut env = Environment::with_prelude();
    let decl = parse_decl_for_elab(src).expect("equation-form recursive theorem should parse");

    let result = crate::elaborate_decl_and_register(&mut env, &decl)
        .expect("equation-form recursive theorem should elaborate and kernel-check");

    assert!(
        matches!(result, crate::ElabResult::Theorem { .. }),
        "expected a Theorem result, got {result:?}"
    );

    let constant = env
        .get_const(&Name::from_string("eqn_thm_true"))
        .expect("eqn_thm_true should be registered");
    let proof = constant
        .value
        .as_ref()
        .expect("registered theorem keeps its proof term");
    assert!(
        theorem_proof_uses_const(proof, "Nat.rec"),
        "recursive equation theorem should be compiled via Nat.rec, got {proof:?}"
    );
}

// =============================================================================
// Tests for MULTI-ARG equation-form recursive defs (Task 3, slice 2)
//
// `def f : A → B → C | p0, q0 => ... | p1, q1 => ...` is desugared by the parser
// into `PatternMatchLambda([_x], Match(_x, arms))` whose arm patterns are
// right-nested `Prod.mk` tuples over the per-argument patterns, with an EMPTY
// declaration binder list. `normalize_equation_def_multiarg` lifts `_x` into N
// named declaration binders (peeling N domains off the arrow/Pi type) and
// rewrites the tuple match into a single-scrutinee match on the decreasing
// position, so the EXISTING single-argument `.rec` lowering fires — the
// trailing pass-through args are folded into the motive via the established
// extra-param machinery. These tests assert the lowering really happens (the
// value uses `T.rec`), that registration's full kernel check passes, and — the
// strongest soundness witness — that `rfl` theorems registered against the same
// environment FORCE the kernel to reduce the lowered `.rec` term to the
// intended numeral / value. No new kernel reducers, no faked termination.
// =============================================================================

/// Register a follow-up `rfl` theorem against an environment that already
/// contains the def under test. Registration runs the FULL kernel type check,
/// and `rfl : lhs = rhs` only checks when the kernel reduces `lhs` (the lowered
/// `.rec` application applied to concrete constructors) to `rhs`. So a green
/// result is a genuine computational soundness witness for the lowering.
fn register_rfl_check(env: &mut Environment, name: &str, lhs: &str, rhs: &str) {
    let src = format!("theorem {name} : {lhs} = {rhs} := rfl");
    let decl = parse_decl_for_elab(&src)
        .unwrap_or_else(|e| panic!("rfl theorem `{name}` should parse: {e:?}"));
    crate::elaborate_decl_and_register(env, &decl).unwrap_or_else(|e| {
        panic!("rfl theorem `{name}` should kernel-check (forces .rec reduction): {e:?}")
    });
    assert!(
        env.get_const(&Name::from_string(name)).is_some(),
        "{name} should be registered after kernel check"
    );
}

/// Multi-arg recursive `Nat.add`-style def: decreasing arg is position 0, the
/// second argument `m` is a pass-through folded into the motive. Must lower via
/// `Nat.rec` and the `rfl` checks must force reduction to the right numerals.
#[test]
fn test_equation_form_multiarg_recursive_nat_add_lowers_via_nat_rec() {
    let src = r"def myAdd : Nat → Nat → Nat
        | 0, m => m
        | Nat.succ n, m => Nat.succ (myAdd n m)";

    let mut env = Environment::with_prelude();
    let decl = parse_decl_for_elab(src).expect("multi-arg equation def should parse");

    let result = crate::elaborate_decl_and_register(&mut env, &decl)
        .expect("multi-arg recursive equation def should elaborate and kernel-check");
    assert!(
        matches!(result, crate::ElabResult::Definition { .. }),
        "expected a Definition result, got {result:?}"
    );

    let constant = env
        .get_const(&Name::from_string("myAdd"))
        .expect("myAdd should be registered");
    let val = constant
        .value
        .as_ref()
        .expect("registered definition keeps its value term");
    assert!(
        theorem_proof_uses_const(val, "Nat.rec"),
        "multi-arg recursive equation def should be compiled via Nat.rec, got {val:?}"
    );

    // Soundness witness: the lowered term must close over NO axioms — no
    // `sorryAx`, no fabricated termination axiom. The lowering is pure `.rec`.
    let deps = env
        .axiom_deps(&Name::from_string("myAdd"))
        .expect("myAdd is registered, axiom_deps should return Some");
    let dep_names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
    assert!(
        dep_names.is_empty(),
        "multi-arg recursive equation def must have an empty axiom closure \
         (genuine structural recursion via Nat.rec), got {dep_names:?}"
    );

    // Computational soundness: force the kernel to reduce the lowered `.rec`.
    register_rfl_check(&mut env, "myAdd_0_5", "myAdd 0 5", "5");
    register_rfl_check(&mut env, "myAdd_2_3", "myAdd 2 3", "5");
    register_rfl_check(&mut env, "myAdd_4_4", "myAdd 4 4", "8");
}

/// Multi-arg recursion where the decreasing argument is NOT the first position:
/// `appendR : Nat → List Nat → List Nat` recurses on the trailing list while the
/// leading `Nat` is a pass-through. Exercises a decreasing position > 0 (the
/// existing extra-param machinery must fold the *leading* binder correctly).
#[test]
fn test_equation_form_multiarg_recursive_decreasing_second_arg() {
    let src = r"def appendR : Nat → List Nat → List Nat
        | h, List.nil => List.cons h List.nil
        | h, List.cons x t => List.cons x (appendR h t)";

    let mut env = Environment::with_prelude();
    let decl = parse_decl_for_elab(src).expect("dec-arg-second equation def should parse");

    let result = crate::elaborate_decl_and_register(&mut env, &decl)
        .expect("dec-arg-second recursive equation def should elaborate and kernel-check");
    assert!(
        matches!(result, crate::ElabResult::Definition { .. }),
        "expected a Definition result, got {result:?}"
    );

    let constant = env
        .get_const(&Name::from_string("appendR"))
        .expect("appendR should be registered");
    let val = constant
        .value
        .as_ref()
        .expect("registered definition keeps its value term");
    assert!(
        theorem_proof_uses_const(val, "List.rec"),
        "recursion on the trailing list arg should lower via List.rec, got {val:?}"
    );

    register_rfl_check(
        &mut env,
        "appendR_nil",
        "appendR 9 List.nil",
        "List.cons 9 List.nil",
    );
    register_rfl_check(
        &mut env,
        "appendR_one",
        "appendR 9 (List.cons 1 List.nil)",
        "List.cons 1 (List.cons 9 List.nil)",
    );
}

/// A NON-recursive multi-arg equation def (`addCases`) is still normalized into
/// N named binders + single-scrutinee match (slice 2 widens this path to all
/// `Prod.mk`-tuple equation defs), so it lowers via the case recursor and
/// computes correctly. Guards that the wider normalization keeps non-recursive
/// multi-arg defs sound (no IH context is installed because no self-call exists).
#[test]
fn test_equation_form_multiarg_non_recursive_computes() {
    let src = r"def addCases : Nat → Nat → Nat
        | 0, m => m
        | Nat.succ n, m => Nat.succ (Nat.add n m)";

    let mut env = Environment::with_prelude();
    let decl = parse_decl_for_elab(src).expect("non-recursive multi-arg def should parse");

    crate::elaborate_decl_and_register(&mut env, &decl)
        .expect("non-recursive multi-arg equation def should elaborate and kernel-check");

    // `addCases (succ n) m = succ (Nat.add n m)`, so `addCases 3 4 = succ (3+4-1) = 7`.
    register_rfl_check(&mut env, "addCases_0_5", "addCases 0 5", "5");
    register_rfl_check(&mut env, "addCases_3_4", "addCases 3 4", "7");
}

/// Out-of-slice guard: a def that structurally matches on TWO positions
/// simultaneously (`| succ n, succ m => ...`) is compiled into a *nested*
/// single-scrutinee match decision tree (slice 3) — the outer match on the
/// decreasing position, an inner match on the second structural position — which
/// lowers via the inductive's `.rec` and kernel-checks. This is the textbook
/// pattern-matrix compilation; the kernel re-checks the resulting `.rec`
/// application, so the lowering cannot escape soundness. The `rfl` checks force
/// the kernel to reduce the lowered term to the intended numerals, witnessing
/// computational faithfulness of the nested compile.
#[test]
fn test_equation_form_multiarg_two_structural_positions_nested_rec() {
    let src = r"def bothMatch : Nat → Nat → Nat
        | 0, 0 => 0
        | Nat.succ n, Nat.succ m => bothMatch n m
        | 0, Nat.succ _ => 99
        | Nat.succ _, 0 => 99";

    let mut env = Environment::with_prelude();
    let decl = parse_decl_for_elab(src).expect("two-structural def should parse");

    let result = crate::elaborate_decl_and_register(&mut env, &decl).expect(
        "two-structural-position recursive equation def should compile to a nested \
         match and kernel-check",
    );
    assert!(
        matches!(result, crate::ElabResult::Definition { .. }),
        "expected a Definition result, got {result:?}"
    );

    let constant = env
        .get_const(&Name::from_string("bothMatch"))
        .expect("bothMatch should be registered");
    let val = constant
        .value
        .as_ref()
        .expect("registered definition keeps its value term");
    assert!(
        theorem_proof_uses_const(val, "Nat.rec"),
        "two-structural recursive equation def should be compiled via Nat.rec, got {val:?}"
    );

    // Empty axiom closure: genuine `.rec`, no fabricated termination / sorry.
    let deps = env
        .axiom_deps(&Name::from_string("bothMatch"))
        .expect("bothMatch is registered, axiom_deps should return Some");
    let dep_names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
    assert!(
        dep_names.is_empty(),
        "nested-match recursive equation def must have an empty axiom closure, got {dep_names:?}"
    );

    // Computational soundness: force the kernel to reduce the nested `.rec`.
    register_rfl_check(&mut env, "bm_0_0", "bothMatch 0 0", "0");
    register_rfl_check(&mut env, "bm_2_2", "bothMatch 2 2", "0");
    register_rfl_check(&mut env, "bm_3_0", "bothMatch 3 0", "99");
    register_rfl_check(&mut env, "bm_0_5", "bothMatch 0 5", "99");
}

/// The `semVectorIntBinOp` shape: leading explicit parameters (`op`, `width`)
/// BEFORE the multi-argument equation arrow, two list-shaped arguments matched
/// simultaneously, and the recursive self-call buried inside a `do` block (a
/// `let _ ← self …` bind). This is the exact trust-ir construct that motivated
/// slice 3 + leading-binder threading + do-block recursion detection. It must
/// lower via `List.rec` and kernel-check with an empty axiom closure.
///
/// The body forwards the recursive bind result directly (`let rest ← self …;
/// pure rest`) — exercising do-block self-call detection without depending on
/// orthogonal list-literal-in-`pure` universe inference, which is env-sensitive
/// and outside this slice. The recursion still threads through the `do` bind and
/// the leading `op`/`width` binders, lowering via `List.rec`.
#[test]
fn test_equation_form_multiarg_leading_binders_do_block_recursion() {
    let src = r#"def semVectorLenX (op : Nat) (width : Nat)
    : List Nat → List Nat → Except String Nat
  | [], [] => Except.ok width
  | x :: lhsRest, y :: rhsRest => do
      let rest ← semVectorLenX op width lhsRest rhsRest
      Except.ok rest
  | [], _ :: _ => Except.error "len"
  | _ :: _, [] => Except.error "len""#;

    let mut env = Environment::with_prelude();
    let decl = parse_decl_for_elab(src).expect("leading-binder do-block def should parse");
    let result = crate::elaborate_decl_and_register(&mut env, &decl).expect(
        "leading-binder + do-block recursive multi-arg equation def should compile and \
         kernel-check",
    );
    assert!(
        matches!(result, crate::ElabResult::Definition { .. }),
        "expected a Definition result, got {result:?}"
    );

    let constant = env
        .get_const(&Name::from_string("semVectorLenX"))
        .expect("semVectorLenX should be registered");
    let val = constant
        .value
        .as_ref()
        .expect("registered definition keeps its value term");
    assert!(
        theorem_proof_uses_const(val, "List.rec"),
        "leading-binder do-block recursive equation def should be compiled via List.rec, got {val:?}"
    );

    // Soundness witness: the closure must not pull in any `sorry` /
    // fabricated-termination axiom. (Unlike the pure-`Nat` cases, a `do`-block
    // over `Except` legitimately references monad constants — `Bind.bind`,
    // `Except.ok/error` — which are ordinary defs, not unsound axioms; we assert
    // the *dangerous* shapes are absent rather than a fully-empty closure.)
    let deps = env
        .axiom_deps(&Name::from_string("semVectorLenX"))
        .expect("semVectorLenX is registered, axiom_deps should return Some");
    let dep_names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
    assert!(
        !dep_names
            .iter()
            .any(|n| n.contains("sorry") || n.contains("Termination") || n.contains("WellFounded")),
        "do-block recursive equation def must not depend on any sorry / fabricated \
         termination axiom (genuine List.rec), got {dep_names:?}"
    );
}
