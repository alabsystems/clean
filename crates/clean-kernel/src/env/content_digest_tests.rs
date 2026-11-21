// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The content digest must be a FUNCTION of content: equal for equal
//! environments built in different orders, different when any covered field
//! differs, and linear in a shared DAG's node count.

use super::super::{ConstantInfo, Environment};
use crate::expr::Expr;
use crate::inductive::InductiveVal;
use crate::level::Level;
use crate::name::Name;
use std::sync::Arc;

fn constant(name: &str, ty: Expr) -> ConstantInfo {
    ConstantInfo::new(Name::from_string(name), vec![], ty, None, false)
}

#[test]
fn export_alias_digest_commits_to_every_candidate_in_resolution_order() {
    let alias = Name::from_string("choice");
    let environment = |choices: &[&str]| {
        let mut env = Environment::new();
        for choice in choices {
            env.register_export_alias(alias.clone(), Name::from_string(choice));
        }
        env.content_digest()
    };
    let original = environment(&["A.x", "B.x", "C.x"]);
    assert_ne!(original, environment(&["A.x"]));
    assert_ne!(original, environment(&["A.x", "C.x", "B.x"]));
    assert_eq!(original, environment(&["A.x", "B.x", "C.x", "B.x"]));
}

fn inductive(name: &str, large: bool) -> InductiveVal {
    InductiveVal {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::prop(),
        num_params: 0,
        num_indices: 0,
        all_names: vec![Name::from_string(name)],
        constructor_names: vec![],
        is_recursive: false,
        is_reflexive: false,
        is_large_elim: large,
        is_nested: false,
    }
}

fn section_sha<'a>(d: &'a super::EnvContentDigest, name: &str) -> &'a str {
    d.sections
        .iter()
        .find(|s| s.name == name)
        .map(|s| s.sha256.as_str())
        .expect("section present")
}

#[test]
fn test_content_digest_insertion_order_is_invisible() {
    let mut a = Environment::new();
    let mut b = Environment::new();
    let ca = constant("A", Expr::prop());
    let cb = constant("B", Expr::sort(Level::succ(Level::Zero)));
    a.constants.insert(ca.name.clone(), ca.clone());
    a.constants.insert(cb.name.clone(), cb.clone());
    b.constants.insert(cb.name.clone(), cb);
    b.constants.insert(ca.name.clone(), ca);
    assert_eq!(a.content_digest(), b.content_digest());
}

#[test]
fn test_content_digest_type_change_changes_constants_section() {
    let mut a = Environment::new();
    let mut b = Environment::new();
    let ca = constant("A", Expr::prop());
    let cb = constant("A", Expr::sort(Level::succ(Level::Zero)));
    a.constants.insert(ca.name.clone(), ca);
    b.constants.insert(cb.name.clone(), cb);
    let (da, db) = (a.content_digest(), b.content_digest());
    assert_ne!(da.total, db.total);
    assert_ne!(section_sha(&da, "constants"), section_sha(&db, "constants"));
    assert_eq!(
        section_sha(&da, "inductives"),
        section_sha(&db, "inductives")
    );
}

#[test]
fn test_content_digest_large_elim_flag_is_covered() {
    let mut a = Environment::new();
    let mut b = Environment::new();
    a.inductives
        .insert(Name::from_string("I"), inductive("I", true));
    b.inductives
        .insert(Name::from_string("I"), inductive("I", false));
    let (da, db) = (a.content_digest(), b.content_digest());
    assert_ne!(
        section_sha(&da, "inductives"),
        section_sha(&db, "inductives")
    );
    assert_ne!(da.total, db.total);
}

#[test]
fn test_content_digest_structure_field_table_is_covered() {
    let mut a = Environment::new();
    let b = Environment::new();
    a.structure_fields
        .insert(Name::from_string("S"), vec![Name::from_string("x")]);
    let (da, db) = (a.content_digest(), b.content_digest());
    assert_ne!(
        section_sha(&da, "structure_fields"),
        section_sha(&db, "structure_fields")
    );
}

/// `e_{k+1} = e_k e_k` through ONE shared `Arc`: the tree has 2^k leaves,
/// the DAG k+1 nodes. The digest must equal the digest of the same term
/// built WITHOUT sharing (structure, never addresses), and the shared form
/// at depth 64 must finish — a tree walk would not.
#[test]
fn test_content_digest_shared_dag_equals_unshared_tree_and_is_linear() {
    fn shared(depth: u32) -> Expr {
        let mut e = Arc::new(Expr::const_(Name::from_string("c"), vec![]));
        for _ in 0..depth {
            e = Arc::new(Expr::app_arc(Arc::clone(&e), Arc::clone(&e)));
        }
        Arc::unwrap_or_clone(e)
    }
    fn unshared(depth: u32) -> Expr {
        if depth == 0 {
            Expr::const_(Name::from_string("c"), vec![])
        } else {
            Expr::app(unshared(depth - 1), unshared(depth - 1))
        }
    }
    let digest_of = |e: Expr| {
        let mut env = Environment::new();
        let c = constant("T", e);
        env.constants.insert(c.name.clone(), c);
        env.content_digest()
    };
    assert_eq!(digest_of(shared(10)), digest_of(unshared(10)));
    assert_ne!(digest_of(shared(10)), digest_of(shared(11)));
    // 2^64 leaves as a tree: only the shared-subterm memo finishes this.
    let deep = digest_of(shared(64));
    assert!(deep
        .sections
        .iter()
        .find(|s| s.name == "constants")
        .is_some_and(|s| s.entries.iter().any(|(key, _)| key == "T")));
}

/// A projection's structure is a kernel read of the term that projects: the
/// kernel types `Proj(S, i, e)` from `S`'s records although no `Const` node
/// names `S`. `kernel_references` lists it; `collect_constants` keeps its
/// constants-only meaning.
#[test]
fn test_kernel_references_name_a_projected_structure() {
    let mut env = Environment::new();
    let pair = Name::from_string("TgSixPair");
    let value = Expr::proj(pair.clone(), 0, Expr::bvar(0));
    let user = ConstantInfo::new(
        Name::from_string("tgSixFirst"),
        vec![],
        Expr::prop(),
        Some(value.clone()),
        false,
    );
    env.constants.insert(user.name.clone(), user);
    assert!(env
        .kernel_references(&Name::from_string("tgSixFirst"))
        .contains(&pair));
    assert!(!value.collect_constants().contains(&pair));
    let mut reads = std::collections::HashSet::new();
    value.collect_kernel_reads_into(&mut reads);
    assert!(reads.contains(&pair));
}
