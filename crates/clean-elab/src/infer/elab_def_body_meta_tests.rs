// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! G46 (ledger (116)) mutation control for the speculative definition-body
//! lane: a term that still mentions an unassigned elaborator metavariable is
//! NOT committed. The lane's guard asked `has_expr_mvar_quick`, which is
//! constant false for elaborator metas (bit-63 FVars), so until 2026-10-08 it
//! committed such a term and the declaration failed later, at the residual
//! metavariable guard, instead of retrying with the expected type.

use super::*;
use crate::term_info::TermInfoCapture;
use clean_kernel::{Environment, Name};
use clean_parser::parse_expr;

fn nat() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

#[test]
fn test_speculative_def_value_lane_refuses_an_open_metavariable() {
    let env = Environment::with_prelude();
    // `List _`'s element type `?α` is pinned by nothing (pinned Lean 4.8.0:
    // "don't know how to synthesize placeholder").
    let val = parse_expr("List.length ([] : List _)").expect("fixture must parse");

    // Non-vacuity: the term ELABORATES, and what it elaborates to still
    // mentions `?α`, so a `None` below is the guard and not a failed
    // elaboration.
    let mut probe = ElabCtx::new(&env);
    let probe_capture = TermInfoCapture::default();
    probe.set_term_info_capture(Some(probe_capture.clone()));
    let raw = probe.elaborate(&val).expect("the fixture elaborates");
    let raw = probe.metas.instantiate(&raw);
    assert!(
        MetaState::expr_has_meta(&raw),
        "the fixture must leave an open metavariable: {raw}"
    );
    assert!(!raw.has_expr_mvar_quick(), "the kernel flag cannot see it");
    probe.finish_term_info();
    assert!(
        !probe_capture.take().expect("probe observations").is_empty(),
        "the rejected attempt really creates source observations"
    );

    let mut ctx = ElabCtx::new(&env);
    let capture = TermInfoCapture::default();
    ctx.set_term_info_capture(Some(capture.clone()));
    let got = ctx
        .try_elab_def_value_without_expected(&val, &nat())
        .expect("the speculative lane reports a failure as `None`, never an error");
    assert!(
        got.is_none(),
        "an open `?α` must send the body to the expected-type lane, got {got:?}"
    );
    ctx.finish_term_info();
    assert!(
        capture.take().expect("rolled-back observations").is_empty(),
        "a rejected body attempt must not publish its source observations"
    );
}

#[test]
fn test_speculative_def_value_lane_commits_a_ground_term() {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let capture = TermInfoCapture::default();
    ctx.set_term_info_capture(Some(capture.clone()));
    let val = parse_expr("(fun _ => (0 : Nat)) ([] : List Nat)").expect("fixture must parse");
    let got = ctx
        .try_elab_def_value_without_expected(&val, &nat())
        .expect("the speculative lane reports a failure as `None`, never an error");
    let expr = got.expect("a ground body is committed by the speculative lane");
    assert!(!MetaState::expr_has_meta(&expr), "{expr}");
    ctx.finish_term_info();
    let infos = capture.take().expect("committed observations");
    let term = infos
        .last()
        .and_then(|info| info.term.as_ref())
        .expect("the accepted outer body was observed");
    assert_eq!(term.expr, expr);
    assert_eq!(term.expected_type, Some(nat()));
    assert_eq!(term.type_, nat());
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

/// The speculative lane's rollback takes its queued open-carrier instance
/// goals with it (integ/r5, 2026-10-16). `fun x => x * x` at `Nat → Nat`
/// queues `HMul ?T ?T ?γ` in this lane, which then fails (G46: the term still
/// holds the instance metavariable) and pops its scope, rolling the id counter
/// back; the queued goal used to survive and pin `Nat` into the expected-type
/// lane's metavariable with the reused id — its `HMul` instance slot — so the
/// kernel refused `fun x => x * x` ("expected HMul Nat Nat Nat, got Type").
/// Pinned Lean 4.8.0 accepts each definition and its computation, and
/// refuses the false twin.
#[test]
fn test_speculative_lane_rollback_drops_its_queued_instance_goals() {
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
