// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pins for the inductive value's regenerated flags (`isRec`, `isReflexive`,
//! `numNested > 0`) and for the block's types among the names a replay
//! generates.
//!
//! Lean's kernel computes `isRec` and `isReflexive` once for the WHOLE block
//! (`inductive.cpp` `declare_inductive_types`, v4.30.0-rc2): every type of
//! `mutual HMA | a : HMA; HMB | b : HMA → HMB end` is stored with
//! `isRec := true`, so the non-recursive `HMA` has no structure or unit-like
//! eta (`is_non_rec_structure`), and `HNR | mk : HBox HNR → HNR` is stored
//! with `isReflexive := true` from its auxiliary declaration (pinned Lean's
//! own `.olean`, `replay_forged/ReplayHonestIndFlags`, measured 2026-10-22).
//! The `.olean` replay checks later declarations against the STORED value, so
//! it must compare each flag with the regenerated one, and the regenerated one
//! must be Lean's.

use super::*;
use crate::env::Declaration;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::level::Level;

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn c(s: &str) -> Expr {
    Expr::const_(name(s), vec![])
}

fn arrow(dom: Expr, cod: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, dom, cod)
}

fn ctor(n: &str, type_: Expr) -> Constructor {
    Constructor {
        name: name(n),
        type_,
    }
}

/// `mutual inductive HMA | a : HMA; inductive HMB | b : HMA → HMB end`.
fn env_with_mutual() -> Environment {
    let mut env = Environment::with_prelude();
    env.add_inductive_core(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![
            InductiveType {
                name: name("HMA"),
                type_: Expr::type_(),
                constructors: vec![ctor("HMA.a", c("HMA"))],
            },
            InductiveType {
                name: name("HMB"),
                type_: Expr::type_(),
                constructors: vec![ctor("HMB.b", arrow(c("HMA"), c("HMB")))],
            },
        ],
    })
    .expect("honest mutual block");
    env
}

/// `inductive U | u : U`, a genuinely non-recursive unit-like type.
fn env_with_unit() -> Environment {
    let mut env = Environment::with_prelude();
    env.add_inductive_core(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name("U"),
            type_: Expr::type_(),
            constructors: vec![ctor("U.u", c("U"))],
        }],
    })
    .expect("honest unit type");
    env
}

/// `structure HBox (α : Type) where f : Nat → α` and
/// `inductive HNR | mk : HBox HNR → HNR`, nested through `HBox`.
fn env_with_nested_reflexive() -> Environment {
    let mut env = Environment::with_prelude();
    let box_of = |e: Expr| Expr::app(c("HBox"), e);
    env.add_inductive_core(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: name("HBox"),
            type_: arrow(Expr::type_(), Expr::type_()),
            constructors: vec![ctor(
                "HBox.mk",
                Expr::pi(
                    BinderInfo::Default,
                    Expr::type_(),
                    arrow(arrow(c("Nat"), Expr::bvar(1)), box_of(Expr::bvar(1))),
                ),
            )],
        }],
    })
    .expect("honest container");
    env.add_inductive_core(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name("HNR"),
            type_: Expr::type_(),
            constructors: vec![ctor("HNR.mk", arrow(box_of(c("HNR")), c("HNR")))],
        }],
    })
    .expect("honest nested family");
    env
}

/// `∀ x y : ty, @Eq.{1} ty x y := fun x y => @Eq.refl.{1} ty x`: true
/// definitionally only through unit-like eta.
fn unit_eta_theorem(ty: &str) -> Declaration {
    let one = Level::succ(Level::zero());
    let t = c(ty);
    let eq = Expr::apps(
        Expr::const_(name("Eq"), vec![one.clone()]),
        [t.clone(), Expr::bvar(1), Expr::bvar(0)],
    );
    let refl = Expr::apps(
        Expr::const_(name("Eq.refl"), vec![one]),
        [t.clone(), Expr::bvar(1)],
    );
    Declaration::Theorem {
        name: name(&format!("{ty}_unit_eta")),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            t.clone(),
            Expr::pi(BinderInfo::Default, t.clone(), eq),
        ),
        value: Expr::lam(
            BinderInfo::Default,
            t.clone(),
            Expr::lam(BinderInfo::Default, t, refl),
        ),
    }
}

/// Lean's block-level `isRec`: the non-recursive `HMA` is recursive because
/// its block is (pinned Lean stores `isRec := true` on `HMA`).
#[test]
fn test_add_inductive_mutual_block_is_recursive_for_every_type() {
    let env = env_with_mutual();
    for ty in ["HMA", "HMB"] {
        let ind = env.get_inductive(&name(ty)).expect("resident");
        assert!(ind.is_recursive, "{ty}: Lean's isRec is block-level");
        assert!(!ind.is_reflexive, "{ty}: no function-typed field");
        assert!(!ind.is_nested, "{ty}: no nested occurrence");
    }
}

/// Lean computes `isReflexive` on the nested block's AUXILIARY declaration:
/// `HBox HNR` becomes an auxiliary type whose constructor takes `Nat → aux`.
#[test]
fn test_add_inductive_nested_block_is_reflexive_through_its_auxiliary_types() {
    let env = env_with_nested_reflexive();
    let hnr = env.get_inductive(&name("HNR")).expect("resident");
    assert!(
        hnr.is_recursive && hnr.is_reflexive && hnr.is_nested,
        "{hnr:?}"
    );
    let hbox = env.get_inductive(&name("HBox")).expect("resident");
    assert!(!hbox.is_recursive && !hbox.is_reflexive && !hbox.is_nested);
}

/// `HMA` is not a non-recursive structure, so no unit-like eta (pinned
/// `leanchecker` refuses `forged_hma_eta`, `replay_forged/ReplayForgedMutualEta`);
/// a genuinely non-recursive unit type keeps it, so the refusal is not vacuous.
#[test]
fn test_unit_eta_needs_a_non_recursive_block() {
    let env = env_with_mutual();
    assert!(
        env.check_decl_readonly_strict(&unit_eta_theorem("HMA"))
            .is_err(),
        "unit-like eta on a member of a recursive mutual block"
    );
    let env = env_with_unit();
    env.check_decl_readonly_strict(&unit_eta_theorem("U"))
        .expect("unit-like eta on a non-recursive unit type");
}

/// The block's types are among the names the replay generated, so a caller
/// can refuse a stored type that no replayed block declares.
#[test]
fn test_lean_replay_inductive_block_generates_the_block_types() {
    let env = env_with_mutual();
    let generated = env
        .lean_replay_inductive_block(&[name("HMB")])
        .expect("an honest mutual block replays to itself");
    for member in ["HMA", "HMB", "HMA.a", "HMB.b", "HMA.rec", "HMB.rec"] {
        assert!(generated.contains(&name(member)), "{member} generated");
    }
    let env = env_with_nested_reflexive();
    let generated = env
        .lean_replay_inductive_block(&[name("HNR")])
        .expect("an honest nested block replays to itself");
    assert!(generated.contains(&name("HNR")), "{generated:?}");
}

/// `ReplayForgedIsRec`: a recursive structure stored with `isRec := false`
/// would get eta from the stored value; the replay refuses the block.
#[test]
fn test_lean_replay_inductive_block_forged_flags_are_invalid_inductive() {
    type Forge = fn(&mut InductiveVal);
    let cases: [(&str, &str, Forge, &str); 4] = [
        (
            "HMA",
            "HMA",
            |i| i.is_recursive = false,
            "recursive flag (isRec)",
        ),
        (
            "HMB",
            "HMB",
            |i| i.is_reflexive = true,
            "reflexive flag (isReflexive)",
        ),
        (
            "HMB",
            "HMB",
            |i| i.is_nested = true,
            "nested flag (numNested > 0)",
        ),
        (
            "HNR",
            "HNR",
            |i| i.is_reflexive = false,
            "reflexive flag (isReflexive)",
        ),
    ];
    for (block, member, forge, field) in cases {
        let mut env = if block == "HNR" {
            env_with_nested_reflexive()
        } else {
            env_with_mutual()
        };
        env.lean_replay_inductive_block(&[name(block)])
            .expect("the honest block replays to itself");
        forge(env.inductives.get_mut(&name(member)).expect("resident"));
        assert_eq!(
            env.lean_replay_inductive_block(&[name(block)]),
            Err(InductiveReplayMismatch::InvalidInductive {
                name: name(member),
                field
            }),
            "{member}: {field}"
        );
    }
}

/// The sequential `stamp-verified` lanes' per-member comparison sees the same
/// flags: a stored `HMA` with a per-type `isRec := false` is refused against
/// the regenerated block.
#[test]
fn test_lean_replay_compare_stored_member_compares_the_flags() {
    let env = env_with_mutual();
    let honest = env.get_inductive(&name("HMA")).expect("resident").clone();
    env.lean_replay_compare_stored_member(StoredFamilyMember::Inductive(&honest))
        .expect("the regenerated member equals itself");
    let mut per_type = honest;
    per_type.is_recursive = false;
    assert_eq!(
        env.lean_replay_compare_stored_member(StoredFamilyMember::Inductive(&per_type)),
        Err(InductiveReplayMismatch::InvalidInductive {
            name: name("HMA"),
            field: "recursive flag (isRec)"
        })
    );
}
