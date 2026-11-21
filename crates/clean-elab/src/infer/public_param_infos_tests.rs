// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::{BinderInfo, Environment, Name};

const NAMED: &str =
    include_str!("../../../../tests/fixtures/section_auto_order/named_public_metadata.lean");
const PRUNED: &str =
    include_str!("../../../../tests/fixtures/section_auto_order/named_public_metadata_pruned.lean");
const PRIVATE_EQUATION: &str = include_str!(
    "../../../../tests/fixtures/section_auto_order/named_public_metadata_private_equation.lean"
);

fn run(
    source: &str,
) -> (
    Environment,
    Vec<Result<crate::ElabResult, crate::ElabError>>,
) {
    let mut env = Environment::with_prelude();
    let mut file = crate::FileContext::new();
    file.set_main_module(Name::from_string("PublicParamTest"));
    let declarations = clean_parser::parse_file(source).expect("source controls parse");
    let results = declarations
        .iter()
        .map(|decl| {
            let decl = crate::preprocess_decl_with_context(decl, &mut file);
            crate::elaborate_decl_and_register_with_context(&mut env, &decl, &mut file).and_then(
                |result| {
                    let mut leaves = Vec::new();
                    result.leaf_decls(&mut leaves);
                    let error = leaves.iter().find_map(|leaf| match leaf {
                        crate::ElabResult::Failed { error, .. } => Some((**error).clone()),
                        _ => None,
                    });
                    match error {
                        Some(error) => Err(error),
                        None => Ok(result),
                    }
                },
            )
        })
        .collect();
    (env, results)
}

fn row(env: &Environment, owner: &str, expected: &[(&str, BinderInfo)]) {
    let owner = Name::from_string(owner);
    let names: Vec<_> = expected
        .iter()
        .map(|(name, _)| Name::from_string(name))
        .collect();
    let kinds: Vec<_> = expected.iter().map(|(_, kind)| *kind).collect();
    assert!(env.get_const(&owner).is_some(), "missing owner {owner}");
    assert_eq!(
        env.get_typed_param_names(&owner),
        Some(names.as_slice()),
        "{owner}"
    );
    assert_eq!(
        env.get_param_binder_infos(&owner),
        Some(kinds.as_slice()),
        "{owner}"
    );
}

#[test]
fn public_parameter_rows_include_one_two_and_adjacent_implicit_autos() {
    use BinderInfo::{Default as D, Implicit as I};
    let (env, results) = run(NAMED);
    assert!(results.iter().all(Result::is_ok), "{results:?}");
    row(&env, "oneOwn", &[("p", D), ("α", I), ("x", D), ("hp", D)]);
    for owner in ["twoOwn", "adjacentOwn"] {
        row(
            &env,
            owner,
            &[("p", D), ("α", I), ("β", I), ("x", D), ("y", D), ("hp", D)],
        );
    }
    row(
        &env,
        "capturedNamedOwn",
        &[
            ("α", I),
            ("q", D),
            ("p", D),
            ("β", I),
            ("x", D),
            ("y", D),
            ("hp", D),
            ("hq", D),
        ],
    );
    for consumer in ["oneNamed", "twoNamed", "adjacentNamed", "capturedNamed"] {
        assert!(
            env.get_const(&Name::from_string(consumer)).is_some(),
            "{consumer}"
        );
    }
}

#[test]
fn public_parameter_rows_prune_sections_without_losing_own_auto_slots() {
    use BinderInfo::{Default as D, Implicit as I};
    let (env, results) = run(PRUNED);
    assert!(results.iter().all(Result::is_ok), "{results:?}");
    row(
        &env,
        "prunedOwn",
        &[("p", D), ("α", I), ("x", D), ("hp", D)],
    );
    row(
        &env,
        "prunedAxiomOwn",
        &[("p", D), ("α", I), ("β", I), ("x", D), ("y", D), ("hp", D)],
    );
}

#[test]
fn public_parameter_rows_keep_equation_auto_names_on_the_private_kernel_owner() {
    use BinderInfo::{Default as D, Implicit as I};
    let (env, results) = run(PRIVATE_EQUATION);
    assert!(results.iter().all(Result::is_ok), "{results:?}");
    row(
        &env,
        "_private.PublicParamTest.0.PublicMetadata.equationOwn",
        &[("p", D), ("α", I), ("x", D), ("hp", D)],
    );
    assert!(env
        .get_const(&Name::from_string("PublicMetadata.equationOwn"))
        .is_none());
    assert!(env
        .get_const(&Name::from_string("PublicMetadata.equationNamed"))
        .is_some());
}

#[test]
fn public_parameter_names_preserve_carrier_and_pruned_argument_refusals() {
    for (prefix, rejected) in [
        (NAMED, "def rejected : Bool := adjacentOwn (p := True) (α := Nat) (β := Bool) (x := true) (y := true) (hp := True.intro)"),
        (PRUNED, "def rejected : Nat := prunedOwn (unused := 0) (p := True) (x := 3) (hp := True.intro)"),
    ] {
        let (env, results) = run(&format!("{prefix}\n{rejected}\n"));
        assert!(results[..results.len() - 1].iter().all(Result::is_ok), "setup failed: {results:?}");
        assert!(results.last().is_some_and(Result::is_err), "bad call accepted: {results:?}");
        assert!(env.get_const(&Name::from_string("rejected")).is_none());
    }
}
