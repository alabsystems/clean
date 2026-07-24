// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bound-variable substitution coverage.

use super::*;

#[test]
fn test_instantiate_bvars_respects_indices() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let body = make_eq(ty.clone(), Expr::bvar(1), Expr::bvar(0));

    let replacements = vec![
        (0, Expr::const_(Name::from_string("a"), vec![])),
        (1, Expr::const_(Name::from_string("b"), vec![])),
    ];

    let instantiated = bridge.instantiate_bvars(&body, &replacements);
    let args = instantiated.get_app_args();

    assert_eq!(args.len(), 3, "Eq should have type, lhs, rhs arguments");
    assert!(
        matches!(args[1].kind(), ExprKind::Const(ref name, _) if name.to_string() == "b"),
        "BVar(1) should be replaced by b"
    );
    assert!(
        matches!(args[2].kind(), ExprKind::Const(ref name, _) if name.to_string() == "a"),
        "BVar(0) should be replaced by a"
    );
}
