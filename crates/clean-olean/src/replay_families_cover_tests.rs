// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Coverage pins for [`inductive_block_refusals`]: a stored type whose `all`
//! names a block that does not contain it (`replay_forged/ReplayForgedAllGhost`,
//! `ReplayForgedAllOther`) is never rebuilt by any block, so the replay must
//! refuse it, and its constructor, by name, instead of letting the stored
//! family stand. The block is registered through the loader's own structural
//! tier, which checks arity only, so `FAG.mk : (FAG → False) → FAG` (a
//! negative occurrence) is resident exactly as the `.olean` loader leaves it.

use super::*;
use clean_kernel::env::TrustedEnvExt;
use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::inductive::{ConstructorVal, InductiveVal};

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn set(names: &[&str]) -> BTreeSet<Name> {
    names.iter().copied().map(n).collect()
}

/// `env` plus `FAG : Prop | mk : (FAG → False) → FAG`, stored with `all`, no
/// recursor, every other field what Lean's kernel would generate for `[FAG]`.
fn with_negative_block(mut env: Environment, all: &[&str]) -> Environment {
    let fag = Expr::const_(n("FAG"), vec![]);
    let field = Expr::pi(
        BinderInfo::Default,
        fag.clone(),
        Expr::const_(n("False"), vec![]),
    );
    let ind = InductiveVal {
        name: n("FAG"),
        level_params: vec![],
        type_: Expr::prop(),
        num_params: 0,
        num_indices: 0,
        all_names: all.iter().copied().map(n).collect(),
        constructor_names: vec![n("FAG.mk")],
        is_recursive: true,
        is_reflexive: true,
        is_large_elim: false,
        is_nested: false,
    };
    let mk = ConstructorVal {
        name: n("FAG.mk"),
        inductive_name: n("FAG"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, field, fag),
        num_params: 0,
        num_fields: 1,
        constructor_idx: 0,
    };
    assert!(env
        .extend_inductives_structural(std::iter::once(ind))
        .is_empty());
    assert!(env
        .extend_constructors_structural(std::iter::once(mk))
        .is_empty());
    env
}

fn assert_refused_with(refused: &BTreeMap<Name, ReplayRefusal>, name: &str, needle: &str) {
    let why = refused
        .get(&n(name))
        .unwrap_or_else(|| panic!("`{name}` must be refused: {refused:?}"))
        .to_string();
    assert!(
        why.contains(needle),
        "`{name}` refused without `{needle}`: {why}"
    );
}

/// `ReplayForgedAllGhost`: `all := [FAG_ghost]`, a name nothing declares. The
/// block found through `all` is `[FAG_ghost]`, which no wanted declaration is
/// in, so it was skipped and `FAG` was never rebuilt (measured 2026-10-22:
/// every `.olean` lane but the sequential `stamp-verified` modes admitted
/// `forged_all_ghost_false : False`).
#[test]
fn test_inductive_block_refusals_type_whose_all_names_no_block_is_refused() {
    let env = with_negative_block(Environment::with_prelude(), &["FAG_ghost"]);
    let members = set(&["FAG", "FAG.mk"]);
    let refused = inductive_block_refusals(&env, &members, &members);
    assert_refused_with(&refused, "FAG", "No such inductive FAG");
    assert_refused_with(&refused, "FAG", "FAG_ghost");
    assert_refused_with(&refused, "FAG.mk", "No such constructor FAG.mk");
}

/// `ReplayForgedAllOther`: `all := [E, FAG]` with the honest `E` (stored
/// `all := [E]`) first. The block found through `all` is `E`'s own `[E]`,
/// which replays cleanly and never declares `FAG`. `E`'s members stay
/// admitted; `FAG` and its constructor are refused.
#[test]
fn test_inductive_block_refusals_type_whose_all_names_another_block_is_refused() {
    let env = with_negative_block(env_with_enum(), &["E", "FAG"]);
    let members = set(&["E", "E.a", "E.b", "E.rec", "FAG", "FAG.mk"]);
    let refused = inductive_block_refusals(&env, &members, &members);
    assert_refused_with(&refused, "FAG", "No such inductive FAG");
    assert_refused_with(&refused, "FAG.mk", "No such constructor FAG.mk");
    for honest in ["E", "E.a", "E.b", "E.rec"] {
        assert!(
            !refused.contains_key(&n(honest)),
            "the honest block must stay admitted: {refused:?}"
        );
    }
}

/// Control: the same block with its honest `all := [FAG]` IS rebuilt, and the
/// kernel refuses the negative occurrence. The coverage refusal above is what
/// stands in for that rebuild when `all` lies.
#[test]
fn test_inductive_block_refusals_negative_block_with_honest_all_is_rejected_by_the_kernel() {
    let env = with_negative_block(Environment::with_prelude(), &["FAG"]);
    let members = set(&["FAG", "FAG.mk"]);
    let refused = inductive_block_refusals(&env, &members, &members);
    for member in ["FAG", "FAG.mk"] {
        assert_refused_with(&refused, member, "is refused by the kernel");
    }
}

/// Only a WANTED member is refused: a forged type no checked declaration
/// reaches is left alone, as before.
#[test]
fn test_inductive_block_refusals_unwanted_forged_type_is_not_examined() {
    let env = with_negative_block(env_with_enum(), &["FAG_ghost"]);
    let local = set(&["E", "E.a", "E.b", "E.rec", "FAG", "FAG.mk"]);
    let refused = inductive_block_refusals(&env, &local, &set(&["E.a"]));
    assert!(refused.is_empty(), "{refused:?}");
}
