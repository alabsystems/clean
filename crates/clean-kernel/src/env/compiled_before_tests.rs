// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The order record and its scan at the kernel boundary: what is read back
//! is what was recorded, nothing is exported, and a scoped scan judges only
//! the constants in scope (`.olean` import's own-module scan).

use std::collections::HashSet;

use super::*;
use crate::env::{Declaration, Environment};
use crate::expr::Expr;

fn n(s: &str) -> Name {
    Name::from_string(s)
}

/// `T : Type` with `T.a`, and `def <name> : T := <value>`.
fn def(env: &mut Environment, name: &str, value: Expr) {
    env.add_decl(Declaration::Definition {
        name: n(name),
        level_params: vec![],
        type_: Expr::const_(n("T"), vec![]),
        value,
        is_reducible: false,
    })
    .unwrap_or_else(|e| panic!("`{name}` is well-typed: {e:?}"));
}

/// `T`, `slow := T.a`, `fast := T.a`, `caller := slow`, `outer := caller`,
/// `other := slow`.
fn fixture() -> Environment {
    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: n("T"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("`T : Type`");
    env.add_decl(Declaration::Axiom {
        name: n("T.a"),
        level_params: vec![],
        type_: Expr::const_(n("T"), vec![]),
    })
    .expect("`T.a : T`");
    let a = Expr::const_(n("T.a"), vec![]);
    def(&mut env, "slow", a.clone());
    def(&mut env, "fast", a);
    def(&mut env, "caller", Expr::const_(n("slow"), vec![]));
    def(&mut env, "outer", Expr::const_(n("caller"), vec![]));
    def(&mut env, "other", Expr::const_(n("slow"), vec![]));
    env
}

fn rendered(found: &[(Name, CompiledBefore)]) -> Vec<(String, String, String)> {
    found
        .iter()
        .map(|(referrer, why)| {
            (
                referrer.to_string(),
                why.rebound.to_string(),
                why.via.to_string(),
            )
        })
        .collect()
}

fn row(referrer: &str, rebound: &str, via: &str) -> (String, String, String) {
    (referrer.to_owned(), rebound.to_owned(), via.to_owned())
}

#[test]
fn test_compiled_before_binding_unscoped_records_every_earlier_referrer() {
    let env = fixture();
    let found = env.compiled_before_binding(&HashSet::from([n("slow")]), None);
    assert_eq!(
        rendered(&found),
        vec![
            row("caller", "slow", "slow"),
            row("other", "slow", "slow"),
            row("outer", "slow", "caller"),
        ]
    );
}

/// A scope judges only its constants: `outer` and `other` are another
/// module's here, so neither is recorded, and `outer` is not reached through
/// `caller` (a module's code is never named by its imports).
#[test]
fn test_compiled_before_binding_scoped_judges_only_the_scope() {
    let env = fixture();
    let scope = HashSet::from([n("slow"), n("fast"), n("caller")]);
    let found = env.compiled_before_binding(&HashSet::from([n("slow")]), Some(&scope));
    assert_eq!(rendered(&found), vec![row("caller", "slow", "slow")]);
}

#[test]
fn test_compiled_before_record_reads_back_and_exports_nothing() {
    let mut env = fixture();
    assert!(env.compiled_before_record().is_none());
    let found = env.compiled_before_binding(&HashSet::from([n("slow")]), None);
    env.record_compiled_before(found);
    let record = env
        .compiled_before_record()
        .expect("three constants were recorded");
    let mut keys: Vec<String> = record.keys().map(ToString::to_string).collect();
    keys.sort();
    assert_eq!(keys, ["caller", "other", "outer"]);
    assert_eq!(
        record.get(&n("outer")),
        Some(&CompiledBefore {
            rebound: n("slow"),
            via: n("caller"),
        })
    );
    let exported = env
        .get_ext_state::<OrderState>(order_idx())
        .expect("recording registered the extension")
        .export_entries();
    assert!(exported.is_empty(), "{exported:?}");
}
