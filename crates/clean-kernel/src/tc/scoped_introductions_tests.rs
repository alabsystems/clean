// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::env::Environment;
use crate::expr::{BinderInfo, FVarId};

fn check_paired_value(
    environment: &Environment,
    type_: &Expr,
    value: &Expr,
    introduction_count: usize,
    residual_level: Level,
    accepted: bool,
) {
    let ordinary = TypeChecker::new(environment);
    let _sort = ordinary.infer_sort(type_).unwrap();
    assert_eq!(ordinary.check_type(value, type_).is_ok(), accepted);

    let paired = TypeChecker::new(environment);
    let outer = paired.ctx_len();
    let (opened_type, _, locals, formed) = paired.scoped_definition_type(type_, value).unwrap();
    assert!(formed);
    assert_eq!(
        locals.len(),
        introduction_count,
        "unexpected ordinary fallback"
    );
    assert_eq!(
        paired.infer_type_full(&opened_type).unwrap(),
        Expr::sort(residual_level)
    );
    paired.ctx_truncate_to(outer);

    let paired = TypeChecker::new(environment);
    let mut work = ScopedDeclarationWork {
        id: FVarId::new(0),
        before: 0,
        after_type: 0,
        after_value: None,
        installed: false,
    };
    assert_eq!(
        paired
            .check_scoped_definition(type_, value, &mut work)
            .is_ok(),
        accepted
    );
    assert!(work.after_value.is_some());
    assert_eq!(paired.ctx_len(), outer);
}

#[test]
fn scoped_audit_classical_paired_values_keep_sorts_and_proof_irrelevance() {
    let environment = Environment::try_with_prelude().unwrap();
    assert_eq!(environment.mode(), CleanMode::Classical);
    let binder = BinderInfo::Default;
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_let = |body| {
        Expr::let_named(
            Name::from_string("m"),
            nat.clone(),
            Expr::bvar(0),
            body,
            false,
        )
    };
    let type_ = Expr::pi(binder, nat.clone(), nat_let(nat.clone()));
    let value = Expr::lam(binder, nat.clone(), nat_let(Expr::bvar(0)));
    check_paired_value(
        &environment,
        &type_,
        &value,
        2,
        Level::succ(Level::zero()),
        true,
    );

    // P remains opaque. The body proves p = p, while the expected type is
    // p = q for two different scoped proofs of P.
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::zero()]);
    let refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::zero()]);
    let mut type_ = Expr::apps(eq, [Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)]);
    let mut value = Expr::apps(refl, [Expr::bvar(2), Expr::bvar(1)]);
    for domain in [Expr::bvar(1), Expr::bvar(0), Expr::prop()] {
        type_ = Expr::pi(binder, domain.clone(), type_);
        value = Expr::lam(binder, domain, value);
    }
    check_paired_value(&environment, &type_, &value, 3, Level::zero(), true);

    // Nat terms remain relevant even when the enclosing type is Prop.
    let nat_level = Level::succ(Level::zero());
    let eq = Expr::const_(Name::from_string("Eq"), vec![nat_level.clone()]);
    let refl = Expr::const_(Name::from_string("Eq.refl"), vec![nat_level]);
    let type_ = Expr::pi(
        binder,
        nat.clone(),
        Expr::pi(
            binder,
            nat.clone(),
            Expr::apps(eq, [nat.clone(), Expr::bvar(1), Expr::bvar(0)]),
        ),
    );
    let value = Expr::lam(
        binder,
        nat.clone(),
        Expr::lam(binder, nat.clone(), Expr::apps(refl, [nat, Expr::bvar(1)])),
    );
    check_paired_value(&environment, &type_, &value, 2, Level::zero(), false);
}
