// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::{Environment, Expr, Name};
use clean_olean::{reference_base_closed, reference_source_base_closed, ClosedRecheckOptions};
use std::collections::BTreeSet;

fn name(value: &str) -> Name {
    Name::from_string(value)
}

fn source_coin() -> Environment {
    let mut env = Environment::default();
    let coin = Expr::const_(name("Coin"), vec![]);
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name("Coin"),
            type_: Expr::type_(),
            constructors: ["Coin.heads", "Coin.tails"]
                .map(|n| Constructor {
                    name: name(n),
                    type_: coin.clone(),
                })
                .to_vec(),
        }],
    })
    .expect("source family");
    env
}

fn roots() -> BTreeSet<Name> {
    ["Coin.casesOn", "Coin.recOn"]
        .map(name)
        .into_iter()
        .collect()
}

#[test]
fn source_wrappers_are_admitted_as_checked_definitions() {
    let env = source_coin();
    let options = ClosedRecheckOptions::default();
    let old = reference_base_closed(&env, &roots(), &options).unwrap();
    assert!(old.into_kernel().is_err());
    let base = reference_source_base_closed(&env, &roots(), &options).unwrap();
    assert!(
        base.report.refusals.is_empty(),
        "{:?}",
        base.report.refusals
    );
    let kernel = base
        .into_kernel()
        .expect("both original definitions must be independently checked");
    for n in roots() {
        assert!(kernel.environment().get_recursor(&n).is_none());
        assert_eq!(
            env.get_const(&n).unwrap().value,
            kernel.environment().get_const(&n).unwrap().value
        );
    }
    assert!(kernel
        .environment()
        .get_recursor(&name("Coin.rec"))
        .is_some());
}
