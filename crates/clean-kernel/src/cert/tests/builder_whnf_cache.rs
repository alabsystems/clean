// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Builder WHNF cache tests.

use std::sync::Arc;

use crate::cert::builder::{CertBuilder, WhnfCache};
use crate::env::{Declaration, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

fn reducible_whnf_fixture() -> (Environment, Expr, Expr) {
    let mut env = Environment::new();
    let alias_name = Name::from_string("builder.whnfAlias");
    let reduced = Expr::from_kind(ExprKind::Sort(Level::zero()));

    env.add_decl(Declaration::Definition {
        name: alias_name.clone(),
        level_params: vec![],
        type_: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
        value: reduced.clone(),
        is_reducible: true,
    })
    .unwrap();

    (env, Expr::const_(alias_name, vec![]), reduced)
}

#[test]
fn test_builder_whnf_cache_reuses_results_across_builders_in_app() {
    let mut env = Environment::new();
    let fun_ty_name = Name::from_string("builder.cachedFunTy");
    let fun_name = Name::from_string("builder.cachedFun");
    let fun_ty_value = Expr::pi(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
        Expr::from_kind(ExprKind::Sort(Level::zero())),
    );

    env.add_decl(Declaration::Definition {
        name: fun_ty_name.clone(),
        level_params: vec![],
        type_: Expr::from_kind(ExprKind::Sort(Level::succ(Level::succ(Level::zero())))),
        value: fun_ty_value,
        is_reducible: true,
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: fun_name.clone(),
        level_params: vec![],
        type_: Expr::const_(fun_ty_name, vec![]),
    })
    .unwrap();

    let cache = Arc::new(WhnfCache::new());
    let expected_type = Expr::from_kind(ExprKind::Sort(Level::zero()));

    let mut first_builder = CertBuilder::new(&env).with_whnf_cache(Arc::clone(&cache));
    let fun = first_builder.const_(fun_name.clone(), vec![]).unwrap();
    let arg = first_builder.sort(Level::zero()).unwrap();
    let app = first_builder.app(fun, arg).unwrap();
    assert_eq!(first_builder.type_of(app), &expected_type);
    assert_eq!(cache.len(), 1);
    assert_eq!(cache.misses(), 1);
    assert_eq!(cache.hits(), 0);

    let mut second_builder = CertBuilder::new(&env).with_whnf_cache(Arc::clone(&cache));
    let fun = second_builder.const_(fun_name, vec![]).unwrap();
    let arg = second_builder.sort(Level::zero()).unwrap();
    let app = second_builder.app(fun, arg).unwrap();
    assert_eq!(second_builder.type_of(app), &expected_type);
    assert_eq!(cache.len(), 1);
    assert_eq!(cache.misses(), 1);
    assert_eq!(cache.hits(), 1);
}

#[test]
fn test_builder_whnf_cache_is_used_by_def_eq() {
    let (env, reducible, reduced) = reducible_whnf_fixture();
    let cache = Arc::new(WhnfCache::new());

    let first_builder = CertBuilder::new(&env).with_whnf_cache(Arc::clone(&cache));
    assert!(first_builder.def_eq(&reducible, &reduced));
    assert_eq!(cache.len(), 2);
    assert_eq!(cache.misses(), 2);
    assert_eq!(cache.hits(), 0);

    let second_builder = CertBuilder::new(&env).with_whnf_cache(Arc::clone(&cache));
    assert!(second_builder.def_eq(&reducible, &reduced));
    assert_eq!(cache.len(), 2);
    assert_eq!(cache.misses(), 2);
    assert_eq!(cache.hits(), 2);
}
