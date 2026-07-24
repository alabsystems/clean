// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Part of `graduate::tests` — spliced into tests/mod.rs via `include!` so
// every test keeps its pre-split `graduate::tests::*` fully-qualified name.
// v3 member cross-check binder-info tolerance: the .olean importer does not
// preserve binder annotations (Lean-implicit binders arrive as Default), so
// the carried-family member cross-check accepts binder-info-only divergence
// — and ONLY that (PProd regression pair + fail-closed forged-recursor twin).

#[test]
fn test_family_member_cross_check_ignores_binder_info_only() {
    // The intake's member cross-check must tolerate binder-info-only
    // differences (the .olean importer does not preserve binder
    // annotations; the kernel ignores them) while rejecting any
    // kernel-meaningful structural difference.
    use super::intake_family::exprs_equal_ignoring_binder_info;
    let implicit_pi = Expr::pi(
        BinderInfo::Implicit,
        Expr::prop(),
        Expr::pi(bd(), Expr::bvar(0), Expr::bvar(1)),
    );
    let default_pi = Expr::pi(
        bd(),
        Expr::prop(),
        Expr::pi(bd(), Expr::bvar(0), Expr::bvar(1)),
    );
    assert!(exprs_equal_ignoring_binder_info(&implicit_pi, &default_pi));
    // Structure still matters: different body index must mismatch.
    let different = Expr::pi(
        bd(),
        Expr::prop(),
        Expr::pi(bd(), Expr::bvar(0), Expr::bvar(0)),
    );
    assert!(!exprs_equal_ignoring_binder_info(&default_pi, &different));
    // ... and so do constants and universe levels.
    assert!(!exprs_equal_ignoring_binder_info(
        &Expr::const_str("GradPilot.a"),
        &Expr::const_str("GradPilot.b")
    ));
    // QTT multiplicity is NOT binder info: a linear binder must mismatch an
    // unrestricted one even when the annotation-blind comparison runs.
    use clean_kernel::expr::{BinderData, Multiplicity};
    let linear_pi = Expr::pi(
        BinderData::new(BinderInfo::Default, Multiplicity::One),
        Expr::prop(),
        Expr::pi(bd(), Expr::bvar(0), Expr::bvar(1)),
    );
    assert!(!exprs_equal_ignoring_binder_info(&default_pi, &linear_pi));
}

/// Rebuild `e` with every `Lam`/`Pi` binder annotation forced to
/// `BinderInfo::Default` — exactly the divergence the `.olean` direct
/// importer introduces (it does not preserve binder annotations).
fn strip_binder_annotations(e: &Expr) -> Expr {
    use clean_kernel::expr::ExprKind;
    match e.kind() {
        ExprKind::App(f, a) => Expr::app(strip_binder_annotations(f), strip_binder_annotations(a)),
        ExprKind::Lam(_, ty, body) => Expr::lam(
            bd(),
            strip_binder_annotations(ty),
            strip_binder_annotations(body),
        ),
        ExprKind::Pi(_, ty, body) => Expr::pi(
            bd(),
            strip_binder_annotations(ty),
            strip_binder_annotations(body),
        ),
        _ => e.clone(),
    }
}

/// The PProd regression, in miniature: a source environment whose family
/// metadata came through the unchecked importer registration path
/// (`TrustedEnvExt`) with the recursor's binder annotations lost — the
/// exact, dump-verified divergence the `.olean` importer produces for
/// Lean-core families. The family must still carry: the recheck replay
/// regenerates the annotated recursor, and the member cross-check must
/// recognize the source constant as the same kernel object.
#[test]
fn test_graduate_v3_family_carries_despite_importer_binder_info_loss() {
    use clean_kernel::env::TrustedEnvExt;

    // Ground truth: the family as the checked kernel path builds it.
    let mut truth = Environment::new();
    add_w_family(&mut truth);
    let true_ind = truth
        .get_inductive(&Name::from_string(W_FAM))
        .expect("truth env has W")
        .clone();
    let true_ctor = truth
        .get_constructor(&Name::from_string(W_MK))
        .expect("truth env has W.mk")
        .clone();
    let true_rec = truth
        .get_recursor(&Name::from_string(W_REC))
        .expect("truth env has W.rec")
        .clone();

    // Source env: registered the way the .olean importer registers families,
    // with the recursor's binder annotations stripped to Default.
    let mut drifted_rec = true_rec.clone();
    drifted_rec.type_ = strip_binder_annotations(&true_rec.type_);
    assert_ne!(
        drifted_rec.type_, true_rec.type_,
        "fixture must reproduce a real binder-info divergence; if add_inductive \
         stopped annotating recursor binders this test needs a new fixture"
    );
    let mut source = Environment::new();
    source.register_inductive(true_ind);
    source.register_constructor(true_ctor);
    source.register_recursor(drifted_rec);
    source
        .add_decl(theorem(USES_W_REC, uses_w_rec_type(), uses_w_rec_value()))
        .expect(
            "proof must typecheck against the drifted recursor (binder info is kernel-meaningless)",
        );

    let tmp = tempfile::tempdir().expect("tempdir");
    let out = tmp.path().join("out");
    let record = graduate(
        &source,
        &names(&[USES_W_REC]),
        &pilot_request(),
        &GraduationBaseline::empty(),
        &out,
    )
    .expect("graduation runs");

    assert_eq!(
        record.result.accepted,
        vec![USES_W_REC.to_string()],
        "binder-info-only importer drift must not block the carried family; rejected: {:?}",
        record.result.rejected
    );
    let thm = entry(&record, USES_W_REC);
    assert!(thm.accepted);
    assert_eq!(thm.carried_inductives, vec![W_FAM.to_string()]);
    assert_eq!(record.carried_inductives.len(), 1);
    assert!(record.carried_inductives[0].kernel.family_checked);

    // The graduated shard still passes the cake gate's checked replay.
    let shard_path = out.join(&record.result.shard_filename);
    let report = verify_cake_shard(&shard_path).expect("cake gate must run");
    assert!(
        report.is_clean(),
        "carried-family shard must pass the cake gate; violations: {:?}",
        report.violations
    );
}

/// The fail-closed twin: a source environment whose stored recursor is
/// GENUINELY different from what the checked replay regenerates (wrong
/// eliminator shape, not a binder annotation) must still reject the whole
/// family — proving the binder-info tolerance did not weaken the cross-check.
#[test]
fn test_graduate_v3_family_genuinely_different_recursor_still_rejected() {
    use clean_kernel::env::TrustedEnvExt;

    let mut truth = Environment::new();
    add_w_family(&mut truth);
    let true_ind = truth
        .get_inductive(&Name::from_string(W_FAM))
        .expect("truth env has W")
        .clone();
    let true_ctor = truth
        .get_constructor(&Name::from_string(W_MK))
        .expect("truth env has W.mk")
        .clone();
    let true_rec = truth
        .get_recursor(&Name::from_string(W_REC))
        .expect("truth env has W.rec")
        .clone();

    // Forged recursor: same name and level params, but the type is a plain
    // `W -> W` — a kernel-meaningful divergence, not metadata.
    let mut forged_rec = true_rec;
    forged_rec.type_ = Expr::pi(bd(), w(), w());
    let mut source = Environment::new();
    source.register_inductive(true_ind);
    source.register_constructor(true_ctor);
    source.register_recursor(forged_rec);
    source
        .add_decl(theorem(USES_W, uses_w_type(), uses_w_value()))
        .expect("candidate proof references only W and W.mk");

    let tmp = tempfile::tempdir().expect("tempdir");
    let out = tmp.path().join("out");
    let record = graduate(
        &source,
        &names(&[USES_W]),
        &pilot_request(),
        &GraduationBaseline::empty(),
        &out,
    )
    .expect("graduation runs");

    assert!(
        record.result.accepted.is_empty(),
        "a genuinely different recursor must reject every dependent"
    );
    let thm = entry(&record, USES_W);
    assert!(!thm.accepted);
    let reason = thm
        .reject_reason
        .as_deref()
        .expect("rejected entry carries a reason");
    assert!(
        reason.contains("does not match"),
        "reject must be the member cross-check, got: {reason}"
    );
    assert!(
        reason.contains(W_REC),
        "reject must name the divergent member, got: {reason}"
    );
    assert!(record.carried_inductives.is_empty());
}
