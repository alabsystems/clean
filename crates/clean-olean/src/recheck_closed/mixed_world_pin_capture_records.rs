// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0

//! Complete raw registry records; expression fields point into the shared DAG.

use super::dag::Tables;
use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use serde_json::{json, Value};
use std::collections::{BTreeMap, BTreeSet};

pub(super) fn record(env: &Environment, name: &Name, tables: &mut Tables) -> Value {
    let constant = env.get_const(name).map(|c| {
        json!({
            "name":tables.name(&c.name), "level_params":tables.names(&c.level_params),
            "type_":tables.expr(&c.type_), "value":c.value.as_ref().map(|e| tables.expr(e)),
            "is_reducible":c.is_reducible, "reducibility":c.reducibility, "kind":c.kind,
            "is_unsafe":env.is_unsafe(name), "is_partial":env.is_partial(name),
        })
    });
    let inductive = env.get_inductive(name).map(|i| json!({
        "name":tables.name(&i.name), "level_params":tables.names(&i.level_params),
        "type_":tables.expr(&i.type_), "num_params":i.num_params, "num_indices":i.num_indices,
        "all_names":tables.names(&i.all_names), "constructor_names":tables.names(&i.constructor_names),
        "is_recursive":i.is_recursive, "is_reflexive":i.is_reflexive,
        "is_large_elim":i.is_large_elim, "is_nested":i.is_nested,
    }));
    let constructor = env.get_constructor(name).map(|c| json!({
        "name":tables.name(&c.name), "inductive_name":tables.name(&c.inductive_name),
        "level_params":tables.names(&c.level_params), "type_":tables.expr(&c.type_),
        "num_params":c.num_params, "num_fields":c.num_fields, "constructor_idx":c.constructor_idx,
    }));
    let recursor = env.get_recursor(name).map(|r| {
        let rules: Vec<_> = r.rules.iter().map(|rule| json!({
            "constructor_name":tables.name(&rule.constructor_name), "num_fields":rule.num_fields,
            "recursive_fields":rule.recursive_fields, "rhs":tables.expr(&rule.rhs),
        })).collect();
        json!({"name":tables.name(&r.name), "arg_order":r.arg_order,
            "level_params":tables.names(&r.level_params), "type_":tables.expr(&r.type_),
            "inductive_name":tables.name(&r.inductive_name), "num_params":r.num_params,
            "num_indices":r.num_indices, "num_motives":r.num_motives, "num_minors":r.num_minors,
            "rules":rules, "is_k":r.is_k})
    });
    let quotient = env.get_quot(name).map(|q| {
        json!({
            "name":tables.name(&q.name), "level_params":tables.names(&q.level_params),
            "type_":tables.expr(&q.type_), "kind":q.kind,
        })
    });
    json!({"name":tables.name(name), "constant":constant, "inductive":inductive,
        "constructor":constructor, "recursor":recursor, "quotient":quotient})
}

pub(super) fn selected(
    env: &Environment,
    names: &BTreeSet<Name>,
    tables: &mut Tables,
) -> BTreeMap<String, Value> {
    let mut records = BTreeMap::new();
    for name in names {
        assert!(
            records
                .insert(name.to_unambiguous_string(), record(env, name, tables))
                .is_none(),
            "ambiguous record name"
        );
    }
    records
}

pub(super) fn base(env: &Environment, tables: &mut Tables) -> Value {
    let names = env
        .constants()
        .map(|c| c.name.clone())
        .chain(env.inductives().map(|c| c.name.clone()))
        .chain(env.constructors().map(|c| c.name.clone()))
        .chain(env.recursors().map(|c| c.name.clone()))
        .chain(env.quotients().map(|c| c.name.clone()))
        .collect();
    json!({"records":selected(env, &names, tables)})
}
