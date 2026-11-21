// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Typed definition bodies use their declared result before choosing carriers.
//! Unresolved elaborator metavariables must still never enter declarations.

use super::ElabCtx;
use crate::term_info::TermInfoCapture;
use crate::unify::MetaState;
use clean_kernel::{Environment, Name};
use clean_parser::parse_expr;

#[test]
fn test_typed_definition_refuses_an_open_metavariable_without_registration() {
    let mut env = Environment::with_prelude();
    let val = parse_expr("List.length ([] : List _)").expect("fixture parses");
    let mut probe = ElabCtx::new(&env);
    let probe_capture = TermInfoCapture::default();
    probe.set_term_info_capture(Some(probe_capture.clone()));
    let raw = probe
        .elaborate(&val)
        .expect("unconstrained expression elaborates");
    let raw = probe.metas.instantiate(&raw);
    assert!(
        MetaState::expr_has_meta(&raw),
        "fixture leaves an open type: {raw}"
    );
    assert!(
        !raw.has_expr_mvar_quick(),
        "the kernel flag cannot see elaborator metas"
    );
    probe.finish_term_info();
    assert!(
        !probe_capture.take().expect("probe observations").is_empty(),
        "the rejected attempt really creates source observations"
    );
    drop(probe);
    let declarations =
        clean_parser::parse_file("def incomplete : Nat := List.length ([] : List _)")
            .expect("declaration parses");
    let declaration = declarations.first().expect("one declaration");
    // Exercise the actual typed declaration and its residual-meta guard inside
    // the same transaction used by surviving elaboration alternatives. There is
    // no longer a separate inference-first definition-body attempt to invoke.
    let mut ctx = ElabCtx::new(&env);
    let capture = TermInfoCapture::default();
    ctx.set_term_info_capture(Some(capture.clone()));
    let rejected = ctx.with_local_scope_rollback(|ctx| ctx.elab_decl(declaration));
    assert!(
        rejected.is_err(),
        "an open type must fail the real declaration"
    );
    ctx.finish_term_info();
    assert!(
        capture.take().expect("rolled-back observations").is_empty(),
        "a rejected body attempt must not publish its source observations"
    );
    drop(ctx);
    let result = crate::elaborate_decl_and_register_with_warning(&mut env, declaration);
    assert!(
        result.is_err(),
        "the unresolved type must not reach a registered declaration"
    );
    assert!(env.get_const(&Name::from_string("incomplete")).is_none());
}

#[test]
fn test_typed_definition_registers_a_ground_body() {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let capture = TermInfoCapture::default();
    ctx.set_term_info_capture(Some(capture.clone()));
    let val = parse_expr("(fun _ => (0 : Nat)) ([] : List Nat)").expect("fixture must parse");
    let ty = parse_expr("Nat").expect("type parses");
    let (expected, expr) = ctx
        .elab_def_body(&[], Some(&ty), &val)
        .expect("the actual typed body accepts a ground term");
    assert!(!MetaState::expr_has_meta(&expr), "{expr}");
    ctx.finish_term_info();
    let infos = capture.take().expect("committed observations");
    let term = infos
        .last()
        .and_then(|info| info.term.as_ref())
        .expect("the accepted outer body was observed");
    assert_eq!(term.expr, expr);
    assert_eq!(term.expected_type, Some(expected.clone()));
    assert_eq!(term.type_, expected);
    assert_eq!(
        expected,
        clean_kernel::Expr::const_(Name::from_string("Nat"), vec![])
    );
    elab_file("def grounded : Nat := (fun _ => (0 : Nat)) ([] : List Nat)\ntheorem grounded_zero : grounded = 0 := rfl")
        .expect("ground body registers and its computation kernel-checks");
}

#[test]
fn test_typed_numeral_body_observations_use_the_checked_carrier() {
    let env = Environment::with_prelude();
    for (surface_type, numeral) in [
        ("Nat", "1"),
        ("UInt8", "1"),
        ("Nat", "18446744073709551616"),
    ] {
        let ty = parse_expr(surface_type).expect("carrier parses");
        let val = parse_expr(numeral).expect("numeral parses");
        let mut ordinary = ElabCtx::new(&env);
        let reference = ordinary
            .elab_def_body(&[], Some(&ty), &val)
            .expect("typed numeral elaborates without observation");
        let mut observed = ElabCtx::new(&env);
        let capture = TermInfoCapture::default();
        observed.set_term_info_capture(Some(capture.clone()));
        let (expected, expr) = observed
            .elab_def_body(&[], Some(&ty), &val)
            .expect("typed numeral elaborates with observation");
        assert_eq!(reference, (expected.clone(), expr.clone()));
        observed.finish_term_info();
        let infos = capture.take().expect("observations available");
        let outer = infos.last().expect("the numeral body was observed");
        assert_eq!(outer.span, val.span());
        let term = outer.term.as_ref().expect("the body is a term");
        assert_eq!(term.expr, expr);
        assert_eq!(term.expected_type, Some(expected.clone()));
        assert_eq!(term.type_, expected);
        assert!(!MetaState::expr_has_meta(&expr), "{expr}");
        let checker =
            clean_kernel::TypeChecker::with_context(&env, clean_kernel::LocalContext::new());
        let actual_type = checker
            .infer_type_full(&expr)
            .expect("the captured numeral independently kernel-checks");
        assert!(checker.is_def_eq(&actual_type, &expected));
    }
}

/// Elaborate every declaration of `src` into a fresh prelude environment; the
/// first refusal, rendered.
fn elab_file(src: &str) -> Result<(), String> {
    let mut env = Environment::with_prelude();
    for decl in clean_parser::parse_file(src).map_err(|e| format!("parse: {e:?}"))? {
        crate::elaborate_decl_and_register_with_warning(&mut env, &decl)
            .map_err(|e| format!("{e}"))?;
    }
    Ok(())
}

/// Typed bodies pin arithmetic lambda carriers before their first operation.
/// Keep the real computation and false-twin controls from the former retry
/// regression: each definition must register, and refusal belongs to the false claim.
#[test]
fn test_typed_definition_bodies_pin_arithmetic_lambda_carriers() {
    for (def, holds, fails) in [
        (
            "def sq : Nat → Nat := fun x => x * x\n",
            "theorem sq_3 : sq 3 = 9 := rfl\n",
            "theorem sq_3_false : sq 3 = 10 := rfl\n",
        ),
        (
            "def dbl : Nat → Nat := fun x => x + x\n",
            "theorem dbl_4 : dbl 4 = 8 := rfl\n",
            "theorem dbl_4_false : dbl 4 = 9 := rfl\n",
        ),
        (
            "def zr : Nat → Nat := fun x => x - x\n",
            "theorem zr_5 : zr 5 = 0 := rfl\n",
            "theorem zr_5_false : zr 5 = 1 := rfl\n",
        ),
        (
            "def idbl : Int → Int := fun x => x + x\n",
            "theorem idbl_2 : idbl 2 = 4 := rfl\n",
            "theorem idbl_2_false : idbl 2 = 5 := rfl\n",
        ),
        (
            "notation \"DUP \" x => x + x\ndef e12 : Nat → Nat := (DUP ·)\n",
            "theorem e12_4 : e12 4 = 8 := rfl\n",
            "theorem e12_4_false : e12 4 = 9 := rfl\n",
        ),
    ] {
        elab_file(&format!("{def}{holds}"))
            .unwrap_or_else(|e| panic!("pinned Lean 4.8.0 accepts this: {e}\n{def}{holds}"));
        let e = elab_file(&format!("{def}{fails}"))
            .expect_err("pinned Lean 4.8.0 refuses the false twin");
        assert!(
            !e.contains("HMul Nat Nat Nat, got Type") && !e.contains("got Type"),
            "refused at the false claim, not at the definition: {e}"
        );
    }
}
