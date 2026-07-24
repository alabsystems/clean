// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Typed tactic-error regressions across the elaboration boundary.

use super::*;
use crate::tactic::TacticError;
use crate::ElabError;
use clean_parser::{Span, SurfaceExpr, SurfaceTactic};

#[test]
fn test_elab_by_tactic_first_retries_recoverable_errors_across_boundary() {
    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("a"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("A"), vec![]),
    })
    .unwrap();

    let mut ctx = ElabCtx::new(&env);
    let target = Expr::const_(Name::from_string("A"), vec![]);
    ctx.current_expected_type = Some(target.clone());

    let tactics = vec![SurfaceTactic::First(
        Span::dummy(),
        vec![
            vec![SurfaceTactic::Named {
                span: Span::dummy(),
                name: "assumption".into(),
                args: vec![],
            }],
            vec![SurfaceTactic::Term(
                Span::dummy(),
                Box::new(SurfaceExpr::Ident(Span::dummy(), "a".into())),
            )],
        ],
    )];

    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("recoverable first-branch failures should reach later branches");
    let proof_ty = ctx
        .infer_type(&proof)
        .expect("first-produced proof should infer");

    assert!(
        ctx.is_def_eq(&proof_ty, &target),
        "proof should solve the goal"
    );
}

#[test]
fn test_elab_by_tactic_unknown_tactic_uses_display_not_debug() {
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);
    ctx.current_expected_type = Some(Expr::prop());

    let err = ctx
        .elab_by_tactic(&[SurfaceTactic::Named {
            span: Span::dummy(),
            name: "unknown_tactic".into(),
            args: vec![],
        }])
        .expect_err("unknown tactics should fail");

    assert!(
        matches!(err, ElabError::TacticFailed(TacticError::UnknownTactic(ref name)) if name == "unknown_tactic"),
        "expected typed unknown tactic error, got: {err:?}"
    );

    let rendered = err.to_string();
    assert!(
        rendered.contains("unknown tactic 'unknown_tactic'"),
        "display output should include the tactic message, got: {rendered}"
    );
    assert!(
        !rendered.contains("UnknownTactic"),
        "display output should not fall back to Debug formatting, got: {rendered}"
    );
}

/// Regression: compound tactic `have h : nonexistent := _` should preserve the
/// upstream `ElabError::UnknownIdent` structurally through the reverse boundary
/// as `TacticError::UpstreamElabError { source }` rather than collapsing to
/// `ElaborationFailed { detail: "..." }`.
#[test]
fn test_reverse_boundary_preserves_upstream_elab_error() {
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);
    ctx.current_expected_type = Some(Expr::prop());

    // `have h : nonexistent := sorry` — the type annotation `nonexistent`
    // will fail elaboration with `ElabError::UnknownIdent`.
    let tactics = vec![SurfaceTactic::Have(
        Span::dummy(),
        Some("h".into()),
        Some(Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            "nonexistent".into(),
        ))),
        Box::new(SurfaceTactic::Named {
            span: Span::dummy(),
            name: "sorry".into(),
            args: vec![],
        }),
    )];

    let err = ctx
        .elab_by_tactic(&tactics)
        .expect_err("unknown type annotation should fail");

    // The outer ElabError should wrap TacticError::UpstreamElabError
    match &err {
        ElabError::TacticFailed(TacticError::UpstreamElabError { source }) => {
            assert!(
                matches!(source.as_ref(), ElabError::UnknownIdent(ref name) if name == "nonexistent"),
                "upstream source should be UnknownIdent, got: {source:?}"
            );
        }
        other => panic!("expected TacticFailed(UpstreamElabError), got: {other:?}"),
    }

    // Display should contain the underlying message, not Debug formatting
    let rendered = err.to_string();
    assert!(
        rendered.contains("Unknown identifier"),
        "display should contain upstream error message, got: {rendered}"
    );
}
