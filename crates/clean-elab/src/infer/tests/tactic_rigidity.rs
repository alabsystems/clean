// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn check_rigidity_cleanup(source: &str, succeeds: bool) {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let fixed = Name::from_string("fixed");
    ctx.metas.add_rigid_level_param(fixed);
    let flexible = ctx.fresh_universe_param();
    let Level::Param(name) = &flexible else {
        panic!("fresh parameter")
    };
    assert!(!ctx.metas.is_rigid_level_param(name));
    ctx.push_local(
        SurfaceName::from_name(Name::from_string("A")),
        Expr::sort(Level::succ(flexible.clone())),
    );
    let before = ctx.metas.rigid_level_params_snapshot();
    let term = parse_expr(source).expect("test tactic source");
    let result = ctx
        .elaborate_with_expected_type(&term, Some(Expr::const_(Name::from_string("True"), vec![])));
    assert_eq!(result.is_ok(), succeeds, "{result:?}");
    assert_eq!(
        ctx.metas.rigid_level_params_snapshot(),
        before,
        "only temporary rigidity must be removed"
    );
}

#[test]
fn tactic_rigidity_is_restored_after_success() {
    check_rigidity_cleanup("by exact True.intro", true);
}

#[test]
fn tactic_rigidity_is_restored_after_failure() {
    check_rigidity_cleanup("by exact (0 : Nat)", false);
}

#[test]
fn tactic_rigidity_survives_a_failed_alternative() {
    check_rigidity_cleanup("by first | exact (0 : Nat) | exact True.intro", true);
}
