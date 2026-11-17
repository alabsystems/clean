// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Constructed-environment controls for the canonical digest API. These
//! deliberately unchecked test records exercise serialization and reachability;
//! they supply no theorem recheck or proof-authority claim.

use std::collections::BTreeSet;

use clean_kernel::env::{ConstantInfo, ConstantKind, Environment, Reducibility};
use clean_kernel::{Expr, Level, Name};
use clean_olean::meaning_digest::{MeaningDigests, MeaningError, Package};

fn name(text: &str) -> Name {
    Name::from_string(text)
}

fn package() -> Package {
    Package::of_names(
        ["API.body", "API.wrapper", "API.statement", "API.unrelated"]
            .into_iter()
            .map(name)
            .collect(),
    )
}

fn environment(body: u64, proof: u64, hint: Reducibility, flag: bool) -> Environment {
    let mut env = Environment::for_lean_replay();
    for (subject, kind, type_, value) in [
        (
            "API.body",
            ConstantKind::Definition,
            Expr::sort(Level::zero()),
            Expr::nat_lit(body),
        ),
        (
            "API.wrapper",
            ConstantKind::Definition,
            Expr::sort(Level::zero()),
            Expr::const_(name("API.body"), vec![]),
        ),
        (
            "API.statement",
            ConstantKind::Theorem,
            Expr::const_(name("API.wrapper"), vec![]),
            Expr::nat_lit(proof),
        ),
        (
            "API.unrelated",
            ConstantKind::Definition,
            Expr::sort(Level::zero()),
            Expr::nat_lit(42),
        ),
    ] {
        let mut info = ConstantInfo::new_with_reducibility(
            name(subject),
            vec![],
            type_,
            Some(value),
            if subject == "API.body" {
                hint
            } else {
                Reducibility::Regular(0)
            },
            kind,
        );
        if subject == "API.body" {
            info.is_reducible = flag;
        }
        env.add_constant_unchecked_for_test(info);
    }
    env
}

fn digests(env: &Environment) -> Vec<String> {
    let package = package();
    let digests = MeaningDigests::new(env, &package);
    ["API.body", "API.wrapper", "API.statement", "API.unrelated"]
        .into_iter()
        .map(|subject| {
            digests
                .digest(&name(subject))
                .expect("resident package member")
        })
        .collect()
}

#[test]
fn body_and_both_reducibility_fields_move_dependent_meaning() {
    let base = digests(&environment(1, 7, Reducibility::Regular(0), false));
    eprintln!("canonical-api-source {base:?}");
    for (label, env) in [
        ("body", environment(2, 7, Reducibility::Regular(0), false)),
        ("hint", environment(1, 7, Reducibility::Regular(1), false)),
        ("flag", environment(1, 7, Reducibility::Regular(0), true)),
    ] {
        let changed = digests(&env);
        for index in 0..3 {
            assert_ne!(base[index], changed[index], "{label} moves root {index}");
        }
        assert_eq!(
            base[3], changed[3],
            "{label} leaves an unrelated root exact"
        );
    }
    assert_eq!(
        base,
        digests(&environment(1, 8, Reducibility::Regular(0), false)),
        "proof-only edits never move meaning"
    );
}

#[test]
fn restatement_and_inventory_order_preserve_the_same_digest() {
    let env = environment(1, 7, Reducibility::Regular(0), false);
    let package = package();
    let digests = MeaningDigests::new(&env, &package);
    let root = name("API.statement");
    let constant = env.get_const(&root).expect("theorem record");
    let original = digests.digest(&root).expect("digest");
    assert_eq!(
        digests.statement_digest(&root, &constant.level_params, &constant.type_),
        Ok(original.clone())
    );
    assert_ne!(
        digests
            .statement_digest(&root, &[], &Expr::sort(Level::zero()))
            .expect("forged statement"),
        original
    );
    let reversed = Package::of_names(
        ["API.unrelated", "API.statement", "API.wrapper", "API.body"]
            .into_iter()
            .map(name)
            .collect(),
    );
    assert_eq!(
        MeaningDigests::new(&env, &reversed).digest(&root),
        Ok(original)
    );
    assert_eq!(
        digests.closure(&root).expect("closure"),
        ["API.body", "API.wrapper", "API.statement"]
            .into_iter()
            .map(name)
            .collect::<BTreeSet<_>>()
    );
}

#[test]
fn outside_and_missing_reached_members_refuse_without_skipping() {
    let env = environment(1, 7, Reducibility::Regular(0), false);
    let package = package();
    let digests = MeaningDigests::new(&env, &package);
    assert_eq!(
        digests.digest(&name("outside")),
        Err(MeaningError::OutsidePackage("outside".to_owned()))
    );
    let empty = Environment::for_lean_replay();
    assert_eq!(
        MeaningDigests::new(&empty, &package).digest(&name("API.statement")),
        Err(MeaningError::NotResident {
            root: "API.statement".to_owned(),
            name: "API.statement".to_owned()
        })
    );
    let mut missing = Environment::for_lean_replay();
    missing.add_constant_unchecked_for_test(
        env.get_const(&name("API.statement"))
            .expect("statement")
            .clone(),
    );
    assert_eq!(
        MeaningDigests::new(&missing, &package).digest(&name("API.statement")),
        Err(MeaningError::NotResident {
            root: "API.statement".to_owned(),
            name: "API.wrapper".to_owned()
        })
    );
}

#[test]
fn projection_structure_is_a_reached_package_constant() {
    let mut env = environment(1, 7, Reducibility::Regular(0), false);
    env.add_constant_unchecked_for_test(ConstantInfo::new(
        name("API.projection"),
        vec![],
        Expr::sort(Level::zero()),
        Some(Expr::proj(name("API.body"), 0, Expr::nat_lit(0))),
        false,
    ));
    let package = Package::of_names(
        ["API.body", "API.projection"]
            .into_iter()
            .map(name)
            .collect(),
    );
    assert_eq!(
        MeaningDigests::new(&env, &package)
            .closure(&name("API.projection"))
            .expect("projection closure"),
        ["API.body", "API.projection"]
            .into_iter()
            .map(name)
            .collect()
    );
}

#[test]
fn module_inventory_preserves_order_union_and_restatement_count() {
    let env = environment(1, 7, Reducibility::Regular(0), false);
    let package = Package::of_module_names([
        (
            "First".to_owned(),
            vec![name("API.wrapper"), name("API.body")],
        ),
        (
            "Second".to_owned(),
            vec![name("API.body"), name("API.statement")],
        ),
    ]);
    assert_eq!(package.modules(), &["First", "Second"]);
    assert_eq!(
        package.names(),
        &["API.body", "API.wrapper", "API.statement"]
            .into_iter()
            .map(name)
            .collect()
    );
    let roots = [name("API.statement")];
    let digests = MeaningDigests::new(&env, &package);
    assert!(digests
        .describe(&package, &roots)
        .expect("description")
        .contains("2 modules declaring 3 names (1 restated by a later module)"));
    assert_eq!(
        digests.digest(&roots[0]),
        MeaningDigests::new(&env, &self::package()).digest(&roots[0])
    );
}

#[test]
#[should_panic(expected = "the package declares nothing")]
fn empty_name_inventory_is_refused() {
    let _ = Package::of_names(BTreeSet::new());
}

#[test]
#[should_panic(expected = "the package declares nothing")]
fn empty_module_inventory_is_refused() {
    let _ = Package::of_module_names(Vec::new());
}
