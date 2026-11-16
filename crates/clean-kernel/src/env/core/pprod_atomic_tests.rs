// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0

//! Main's successful PProd initializer is unchanged; errors publish no prefix.

use super::*;
use crate::env::DeclarationVerification;

fn literal_pprod_declaration() -> InductiveDecl {
    let u = Name::from_string("u");
    let v = Name::from_string("v");

    let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
    let sort_v = Expr::from_kind(ExprKind::Sort(Level::param(v.clone())));
    let result_sort = Expr::from_kind(ExprKind::Sort(Level::max(
        Level::max(Level::succ(Level::zero()), Level::param(u.clone())),
        Level::param(v.clone()),
    )));

    let pprod_const = Expr::const_(
        Name::from_string("PProd"),
        vec![Level::param(u.clone()), Level::param(v.clone())],
    );

    // PProd : Sort u → Sort v → Sort (max (max 1 u) v)
    let pprod_type = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, _a) = b.fresh_local(sort_u.clone());
        let (bv_id, _bv) = b.fresh_local(sort_v.clone());
        let e = b.mk_pi(
            bv_id,
            BinderInfo::Default,
            sort_v.clone(),
            result_sort.clone(),
        );
        let e = b.mk_pi(a_id, BinderInfo::Default, sort_u.clone(), e);
        b.finish(e)
    };

    // PProd.mk : {α : Sort u} → {β : Sort v} → α → β → PProd α β
    let pprod_mk_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
        let (beta_id, beta) = b.fresh_local(sort_v.clone());
        let (fst_id, _fst) = b.fresh_local(alpha.clone());
        let (snd_id, _snd) = b.fresh_local(beta.clone());
        let result = Expr::app(Expr::app(pprod_const.clone(), alpha.clone()), beta.clone());
        let e = b.mk_pi(snd_id, BinderInfo::Default, beta, result);
        let e = b.mk_pi(fst_id, BinderInfo::Default, alpha, e);
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, sort_v.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
        b.finish(e)
    };

    InductiveDecl {
        level_params: vec![u.clone(), v.clone()],
        num_params: 2,
        types: vec![InductiveType {
            name: Name::from_string("PProd"),
            type_: pprod_type,
            constructors: vec![Constructor {
                name: Name::from_string("PProd.mk"),
                type_: pprod_mk_type,
            }],
        }],
    }
}

fn checked_family_only() -> Environment {
    let mut env = Environment::new();
    env.init_nat()
        .expect("unchanged main Nat for the collision value");
    assert!(env.get_const(&Name::from_string("PProd")).is_none());
    env.add_inductive(literal_pprod_declaration())
        .expect("ordinary checked main PProd family generation");
    assert!(!env.has_pprod(), "the public completion flag was not set");
    for text in [
        "PProd",
        "PProd.mk",
        "PProd.rec",
        "PProd.casesOn",
        "PProd.recOn",
    ] {
        let name = Name::from_string(text);
        assert!(
            env.get_const(&name).is_some(),
            "actual family member: {text}"
        );
        assert_eq!(
            env.declaration_verification(&name),
            Some(DeclarationVerification::FullKernelCheck)
        );
    }
    for text in ["PProd.fst", "PProd.snd", "PProd.swap"] {
        assert!(env.get_const(&Name::from_string(text)).is_none());
    }
    env
}

fn unchanged(before: &Environment, after: &Environment) {
    // These fixtures have no lazy source or materialized dynamic extensions.
    assert_eq!(
        after.to_bincode().expect("after"),
        before.to_bincode().expect("before")
    );
    assert_eq!(
        after.declaration_verification,
        before.declaration_verification
    );
    assert_eq!(after.generation(), before.generation());
    assert_eq!(after.has_nat(), before.has_nat());
    assert_eq!(after.has_pprod(), before.has_pprod());
}

#[test]
fn public_completion_rolls_back_late_checked_collisions_and_allows_retry() {
    for text in ["PProd.snd", "PProd.swap"] {
        let mut env = checked_family_only();
        let name = Name::from_string(text);
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        env.add_decl(Declaration::Definition {
            name: name.clone(),
            level_params: vec![],
            type_: Expr::arrow(nat.clone(), nat.clone()),
            value: Expr::lam(BinderInfo::Default, nat, Expr::bvar(0)),
            is_reducible: true,
        })
        .expect("ordinary strictly checked identity at the conflicting name");
        assert_eq!(
            env.declaration_verification(&name),
            Some(DeclarationVerification::FullKernelCheck)
        );
        let before = env.clone();

        // The private body is byte-exact main behavior. Its disposable attempt
        // must reach the late collision after actually checking a prefix.
        let mut discarded = before.clone();
        let staged_error = discarded
            .init_pprod_staged()
            .expect_err("late main completion collision");
        assert!(
            matches!(&staged_error, EnvError::DuplicateName(actual) if actual == &name),
            "{staged_error:#?}"
        );
        let fst = Name::from_string("PProd.fst");
        assert!(before.get_const(&fst).is_none());
        assert!(discarded
            .get_const(&fst)
            .expect("actual checked prefix")
            .value
            .is_some());
        assert_eq!(
            discarded.declaration_verification(&fst),
            Some(DeclarationVerification::FullKernelCheck)
        );
        if text == "PProd.swap" {
            let snd = Name::from_string("PProd.snd");
            assert!(discarded
                .get_const(&snd)
                .expect("second checked prefix")
                .value
                .is_some());
            assert_eq!(
                discarded.declaration_verification(&snd),
                Some(DeclarationVerification::FullKernelCheck)
            );
        }

        let error = env
            .init_pprod()
            .expect_err("the public call refuses the same collision");
        assert!(
            matches!(&error, EnvError::DuplicateName(actual) if actual == &name),
            "{error:#?}"
        );
        unchanged(&before, &env);

        env.remove_constant(&name);
        env.init_pprod()
            .expect("remove only the collision and retry");
        assert!(env.has_pprod());
        for text in ["PProd.fst", "PProd.snd", "PProd.swap"] {
            let name = Name::from_string(text);
            assert!(env
                .get_const(&name)
                .expect("checked completion")
                .value
                .is_some());
            assert_eq!(
                env.declaration_verification(&name),
                Some(DeclarationVerification::FullKernelCheck)
            );
        }
        let complete = env.clone();
        env.init_pprod().expect("main's unchanged ready path");
        unchanged(&complete, &env);
    }
}

#[test]
fn public_fresh_and_ready_success_match_the_unchanged_initializer_body() {
    for before in [Environment::new(), checked_family_only()] {
        let mut reference = before.clone();
        reference
            .init_pprod_staged()
            .expect("unchanged main body succeeds");
        let mut actual = before;
        actual
            .init_pprod()
            .expect("transactional public call succeeds");
        assert!(actual.has_pprod());
        unchanged(&reference, &actual);
        let complete = actual.clone();
        actual.init_pprod().expect("same completed ready path");
        unchanged(&complete, &actual);
    }
}
