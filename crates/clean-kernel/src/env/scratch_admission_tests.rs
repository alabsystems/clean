// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Environment::into_scratch_with_inductive_core` is `add_inductive_core`
//! without the transaction snapshot: an admitted block leaves the same
//! environment (content digest and mutation counter), a refused one returns
//! the same error. The nested fixture is the shape the `.olean` import
//! re-admits through `lean_replay_admit_block`.

use super::tests_nested_elim::{make_env_with_list, tree_decl};
use super::*;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};

/// `add_inductive_core` on one copy, the scratch admission on another.
fn both(
    env: &Environment,
    decl: &InductiveDecl,
) -> (Result<Environment, EnvError>, Result<Environment, EnvError>) {
    let mut transactional = env.clone();
    let transactional = transactional
        .add_inductive_core(decl.clone())
        .map(|()| transactional);
    let scratch = env.clone().into_scratch_with_inductive_core(decl.clone());
    (transactional, scratch)
}

fn assert_same_admission(env: &Environment, decl: &InductiveDecl) {
    let (transactional, scratch) = both(env, decl);
    let transactional = transactional.expect("the block is admitted");
    let scratch = scratch.expect("the scratch admission admits it too");
    assert_eq!(scratch.content_digest(), transactional.content_digest());
    assert_eq!(scratch.generation, transactional.generation);
}

fn assert_same_refusal(env: &Environment, decl: &InductiveDecl) {
    let (transactional, scratch) = both(env, decl);
    let transactional = transactional.map(|_| ()).expect_err("the block is refused");
    let scratch = scratch
        .map(|_| ())
        .expect_err("the scratch admission refuses it too");
    assert_eq!(scratch.to_string(), transactional.to_string());
}

/// `Tree | node : List Tree → Tree` with a constructor of type `ty`.
fn tree_with_node(ty: Expr) -> InductiveDecl {
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("Tree"),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Tree.node"),
                type_: ty,
            }],
        }],
    }
}

#[test]
fn test_scratch_admission_nested_family_leaves_the_transactional_environment() {
    let env = make_env_with_list();
    let decl = tree_decl();
    assert_same_admission(&env, &decl);
    let admitted = env
        .into_scratch_with_inductive_core(decl)
        .expect("Tree is admitted");
    assert!(
        admitted
            .get_recursor(&Name::from_string("Tree.rec_1"))
            .is_some(),
        "the nested pipeline ran: the container recursor is restored"
    );
}

#[test]
fn test_scratch_admission_refusals_match_the_transactional_error() {
    let env = make_env_with_list();
    let tree = Expr::const_(Name::from_string("Tree"), vec![]);
    let list_of = |e: Expr| {
        Expr::app(
            Expr::const_(Name::from_string("List"), vec![Level::zero()]),
            e,
        )
    };
    // A constructor that does not return its inductive.
    assert_same_refusal(&env, &tree_with_node(Expr::prop()));
    // A negative occurrence under the nested container: `List (Tree → Tree)`.
    let negative = Expr::pi(
        BinderInfo::Default,
        list_of(Expr::arrow(tree.clone(), tree.clone())),
        tree,
    );
    assert_same_refusal(&env, &tree_with_node(negative));
}
