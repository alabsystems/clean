// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pins for [`inductive_block_refusals`]. The stored-block shapes are built
//! the way the `.olean` loader registers them: the kernel admits an honest
//! block, and its members, one of them forged, are registered into a FRESH
//! environment through the loader's own structural tier (`TrustedEnvExt`).
//! That tier now refuses a forged recursor record (clean-kernel
//! `env/imported_family.rs`), so the forged-rule fixture makes it resident
//! through the test-only unchecked door to keep the replay's own refusal
//! pinned, and a separate arm pins the block as the loader actually leaves it.

use super::*;
use clean_kernel::env::TrustedEnvExt;
use clean_kernel::expr::Expr;
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn env_with_enum() -> Environment {
    let mut env = Environment::with_prelude();
    let ty = Expr::const_(n("E"), vec![]);
    env.add_inductive_core(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: n("E"),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: n("E.a"),
                    type_: ty.clone(),
                },
                Constructor {
                    name: n("E.b"),
                    type_: ty,
                },
            ],
        }],
    })
    .expect("honest enumeration");
    env
}

/// The honest enumeration's block, stored with `E.rec`'s rule for `E.b`
/// replaced by the rule for `E.a` (`ReplayForgedRule`), resident beside its
/// honest family.
///
/// The loader's structural tier no longer admits such a record: it must equal
/// the recursor the kernel generates from the resident family
/// (`clean-kernel` `env/imported_family.rs`), and this fixture pins that
/// refusal first. The forged record is then made resident through the
/// test-only unchecked door, so the replay's own refusal — the second line,
/// for records that reach an environment by any other route — stays pinned.
fn env_with_forged_rule() -> Environment {
    let honest = env_with_enum();
    let ind = honest.get_inductive(&n("E")).expect("resident").clone();
    let ctors: Vec<_> = ["E.a", "E.b"]
        .into_iter()
        .map(|c| honest.get_constructor(&n(c)).expect("resident").clone())
        .collect();
    let mut rec = honest.get_recursor(&n("E.rec")).expect("resident").clone();
    rec.rules[1].rhs = rec.rules[0].rhs.clone();
    let mut env = Environment::with_prelude();
    assert!(env
        .extend_inductives_structural(std::iter::once(ind))
        .is_empty());
    assert!(env
        .extend_constructors_structural(ctors.into_iter())
        .is_empty());
    let refused = env.extend_recursors_structural(std::iter::once(rec.clone()));
    assert!(
        refused.len() == 1
            && refused[0].0 == n("E.rec")
            && refused[0].1.to_string().contains("iota right-hand side"),
        "the loader's structural tier must refuse the forged rule: {refused:?}"
    );
    env.extend_recursors_unchecked(std::iter::once(rec));
    env
}

fn locals() -> BTreeSet<Name> {
    ["E", "E.a", "E.b", "E.rec"].into_iter().map(n).collect()
}

fn set(names: &[&str]) -> BTreeSet<Name> {
    names.iter().copied().map(n).collect()
}

#[test]
fn test_inductive_block_refusals_honest_block_refuses_nothing() {
    let env = env_with_enum();
    let refused = inductive_block_refusals(&env, &locals(), &locals());
    assert!(refused.is_empty(), "{refused:?}");
}

/// `ReplayForgedRule`: one member differs, and EVERY local member of the
/// block is refused with the block's finding.
#[test]
fn test_inductive_block_refusals_forged_rule_refuses_the_whole_block() {
    let env = env_with_forged_rule();
    let refused = inductive_block_refusals(&env, &locals(), &locals());
    for member in locals() {
        let why = refused.get(&member).expect("every block member is refused");
        assert!(
            why.to_string().contains("Invalid recursor E.rec"),
            "{member}: {why}"
        );
    }
}

/// A recursor alone is enough to reach its block: a member's references
/// exclude its own block, so the replay must find the block by name.
#[test]
fn test_inductive_block_refusals_recursor_reaches_its_block_by_name() {
    let env = env_with_forged_rule();
    let refused = inductive_block_refusals(&env, &locals(), &set(&["E.rec"]));
    assert!(refused.contains_key(&n("E.rec")), "{refused:?}");
    let honest = env_with_enum();
    assert!(inductive_block_refusals(&honest, &locals(), &set(&["E.rec"])).is_empty());
}

/// A local constructor attached to a family this replay does not declare:
/// Lean's replay never generates it.
#[test]
fn test_inductive_block_refusals_constructor_of_foreign_family_is_no_such_constructor() {
    let env = env_with_enum();
    let refused = inductive_block_refusals(&env, &set(&["E.a"]), &set(&["E.a"]));
    let why = refused.get(&n("E.a")).expect("refused");
    assert!(why.to_string().contains("No such constructor E.a"), "{why}");
}

/// A local recursor no local block generates.
#[test]
fn test_inductive_block_refusals_recursor_without_local_block_is_no_such_recursor() {
    let env = env_with_enum();
    let refused = inductive_block_refusals(&env, &set(&["E.rec"]), &set(&["E.rec"]));
    let why = refused.get(&n("E.rec")).expect("refused");
    assert!(why.to_string().contains("No such recursor E.rec"), "{why}");
}

/// Declarations that are not family members are never touched.
#[test]
fn test_inductive_block_refusals_ignores_non_family_declarations() {
    let env = env_with_enum();
    let refused = inductive_block_refusals(&env, &set(&["Nat.add"]), &set(&["Nat.add"]));
    assert!(
        refused.is_empty(),
        "a definition is not a family member: {refused:?}"
    );
}

/// The block as the LOADER leaves it when the stored `E.rec` is forged: the
/// structural tier refuses the record (it is not the recursor the kernel
/// generates), so the type and constructors are resident and `E.rec` is not.
/// Lean's replay refuses the block for its forged recursor; so must this one,
/// rather than pass a block whose stored recursor it never saw.
#[test]
fn test_inductive_block_refusals_recursor_refused_at_load_refuses_the_block() {
    let honest = env_with_enum();
    let ind = honest.get_inductive(&n("E")).expect("resident").clone();
    let ctors: Vec<_> = ["E.a", "E.b"]
        .into_iter()
        .map(|c| honest.get_constructor(&n(c)).expect("resident").clone())
        .collect();
    let mut rec = honest.get_recursor(&n("E.rec")).expect("resident").clone();
    rec.rules[1].rhs = rec.rules[0].rhs.clone();
    let mut env = Environment::with_prelude();
    assert!(env
        .extend_inductives_structural(std::iter::once(ind))
        .is_empty());
    assert!(env
        .extend_constructors_structural(ctors.into_iter())
        .is_empty());
    assert_eq!(
        env.extend_recursors_structural(std::iter::once(rec)).len(),
        1,
        "the forged recursor is refused at load"
    );
    assert!(env.get_recursor(&n("E.rec")).is_none());

    let refused = inductive_block_refusals(&env, &locals(), &locals());
    for member in ["E", "E.a", "E.b"] {
        let why = refused
            .get(&n(member))
            .unwrap_or_else(|| panic!("{member} must be refused: {refused:?}"));
        assert!(
            why.to_string().contains("Invalid recursor E.rec")
                && why
                    .to_string()
                    .contains("refused when the module was imported"),
            "{member}: {why}"
        );
    }
}

#[path = "replay_families_cover_tests.rs"]
mod cover;
