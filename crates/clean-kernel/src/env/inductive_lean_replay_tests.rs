// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pins for [`Environment::lean_replay_inductive_block`]: an honest block
//! replays to itself, and each forgery `leanchecker` refuses in
//! `replay_forged/` (a recursor type with no minor premises, a recursor rule
//! taken from another constructor, a constructor typed `False`) is refused
//! here with the field Lean's `checkPostponed*` would name. Each forgery is
//! applied to the RESIDENT tables, the way the `.olean` loader registers a
//! stored block.

use super::*;
use crate::expr::ExprKind;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::level::Level;

fn name(s: &str) -> Name {
    Name::from_string(s)
}

/// `inductive E | a | b` admitted by the kernel, as a stored block.
fn env_with_enum() -> Environment {
    let mut env = Environment::with_prelude();
    let ty = Expr::const_(name("E"), vec![]);
    env.add_inductive_core(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name("E"),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: name("E.a"),
                    type_: ty.clone(),
                },
                Constructor {
                    name: name("E.b"),
                    type_: ty,
                },
            ],
        }],
    })
    .expect("honest enumeration");
    env
}

/// `inductive L (α : Type) | nil | cons : α → L α → L α`: a recursive,
/// parameterised block whose recursor rules carry induction hypotheses.
fn env_with_list_like() -> Environment {
    let mut env = Environment::with_prelude();
    let l_alpha = Expr::app(Expr::const_(name("L"), vec![]), Expr::bvar(0));
    env.add_inductive_core(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: name("L"),
            type_: Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
            constructors: vec![
                Constructor {
                    name: name("L.nil"),
                    type_: Expr::pi(BinderInfo::Implicit, Expr::type_(), l_alpha.clone()),
                },
                Constructor {
                    name: name("L.cons"),
                    type_: Expr::pi(
                        BinderInfo::Implicit,
                        Expr::type_(),
                        Expr::pi(
                            BinderInfo::Default,
                            Expr::bvar(0),
                            Expr::pi(
                                BinderInfo::Default,
                                Expr::app(Expr::const_(name("L"), vec![]), Expr::bvar(1)),
                                Expr::app(Expr::const_(name("L"), vec![]), Expr::bvar(2)),
                            ),
                        ),
                    ),
                },
            ],
        }],
    })
    .expect("honest list-like family");
    env
}

#[test]
fn test_lean_replay_inductive_block_honest_enum_replays_to_itself() {
    let env = env_with_enum();
    let generated = env
        .lean_replay_inductive_block(&[name("E")])
        .expect("an honest block equals its own regeneration");
    for member in ["E.a", "E.b", "E.rec"] {
        assert!(generated.contains(&name(member)), "{member} generated");
    }
}

#[test]
fn test_lean_replay_inductive_block_honest_recursive_family_replays_to_itself() {
    let env = env_with_list_like();
    let generated = env
        .lean_replay_inductive_block(&[name("L.cons")])
        .expect("a recursive parameterised block equals its regeneration");
    assert!(generated.contains(&name("L.rec")));
}

/// A block member's binder annotations are not part of Lean's `==`.
#[test]
fn test_lean_replay_inductive_block_binder_annotation_difference_is_ignored() {
    let mut env = env_with_list_like();
    let stored = env.recursors.get(&name("L.rec")).expect("resident").clone();
    let ExprKind::Pi(bd, dom, body) = stored.type_.kind() else {
        panic!("recursor type is a Pi");
    };
    let flipped = BinderData::new(
        if bd.info == BinderInfo::Implicit {
            BinderInfo::Default
        } else {
            BinderInfo::Implicit
        },
        bd.mult,
    );
    let retyped = Expr::pi(flipped, dom.as_ref().clone(), body.as_ref().clone());
    env.recursors
        .get_mut(&name("L.rec"))
        .expect("resident")
        .type_ = retyped.clone();
    env.constants
        .get_mut(&name("L.rec"))
        .expect("resident")
        .type_ = retyped;
    env.lean_replay_inductive_block(&[name("L")])
        .expect("binder annotations do not enter the comparison");
}

/// `ReplayForgedRule`: the rule for `E.b` replaced by the rule for `E.a`.
#[test]
fn test_lean_replay_inductive_block_forged_rule_rhs_is_invalid_recursor() {
    let mut env = env_with_enum();
    let rec = env.recursors.get_mut(&name("E.rec")).expect("resident");
    let rule_a = rec.rules[0].rhs.clone();
    rec.rules[1].rhs = rule_a;
    assert_eq!(
        env.lean_replay_inductive_block(&[name("E")]),
        Err(InductiveReplayMismatch::InvalidRecursor {
            name: name("E.rec"),
            field: "rule right-hand side"
        })
    );
}

/// `ReplayForgedRec`: the recursor stored with its minor premises removed,
/// `{motive : E → Sort u} → (t : E) → motive t`, which proves `False`.
#[test]
fn test_lean_replay_inductive_block_forged_recursor_type_is_invalid_recursor() {
    let mut env = env_with_enum();
    let rec = env.recursors.get(&name("E.rec")).expect("resident").clone();
    let u = Level::param(rec.level_params[0].clone());
    let e = Expr::const_(name("E"), vec![]);
    let motive_ty = Expr::pi(BinderInfo::Default, e.clone(), Expr::sort(u));
    let forged_ty = Expr::pi(
        BinderInfo::Implicit,
        motive_ty,
        Expr::pi(
            BinderInfo::Default,
            e,
            Expr::app(Expr::bvar(1), Expr::bvar(0)),
        ),
    );
    let forged = env.recursors.get_mut(&name("E.rec")).expect("resident");
    forged.type_ = forged_ty.clone();
    forged.num_minors = 0;
    env.constants
        .get_mut(&name("E.rec"))
        .expect("resident")
        .type_ = forged_ty;
    let refusal = env
        .lean_replay_inductive_block(&[name("E")])
        .expect_err("a recursor with no minor premises is not the generated one");
    assert!(
        matches!(refusal, InductiveReplayMismatch::InvalidRecursor { ref name, .. } if *name == Name::from_string("E.rec")),
        "{refusal}"
    );
}

/// `ReplayForgedCtor`: the constructor stored with type `False`. Lean rebuilds
/// the declaration from the stored constructor type, and the kernel refuses a
/// constructor that does not return its inductive.
#[test]
fn test_lean_replay_inductive_block_forged_constructor_type_is_rejected() {
    let mut env = env_with_enum();
    let false_ty = Expr::const_(name("False"), vec![]);
    env.constructors
        .get_mut(&name("E.a"))
        .expect("resident")
        .type_ = false_ty.clone();
    env.constants.get_mut(&name("E.a")).expect("resident").type_ = false_ty;
    let refusal = env
        .lean_replay_inductive_block(&[name("E")])
        .expect_err("a constructor typed False is refused");
    assert!(
        matches!(refusal, InductiveReplayMismatch::Rejected { .. }),
        "{refusal}"
    );
}

/// The constant-table mirror is what `infer_type` reads: forging only it (and
/// leaving the constructor registry honest) is refused too.
#[test]
fn test_lean_replay_inductive_block_forged_constant_mirror_is_invalid_constructor() {
    let mut env = env_with_enum();
    env.constants.get_mut(&name("E.b")).expect("resident").type_ =
        Expr::const_(name("False"), vec![]);
    assert_eq!(
        env.lean_replay_inductive_block(&[name("E")]),
        Err(InductiveReplayMismatch::InvalidConstructor {
            name: name("E.b"),
            field: "constant-table entry"
        })
    );
}

#[test]
fn test_lean_replay_inductive_block_forged_field_count_is_invalid_constructor() {
    let mut env = env_with_enum();
    env.constructors
        .get_mut(&name("E.b"))
        .expect("resident")
        .num_fields = 1;
    assert_eq!(
        env.lean_replay_inductive_block(&[name("E")]),
        Err(InductiveReplayMismatch::InvalidConstructor {
            name: name("E.b"),
            field: "number of fields"
        })
    );
}

/// A stored recursor of the block the kernel never generates (`E.rec_1` for a
/// block with no nested occurrence): Lean's "No such recursor".
#[test]
fn test_lean_replay_inductive_block_extra_stored_recursor_is_no_such_recursor() {
    let mut env = env_with_enum();
    let mut extra = env.recursors.get(&name("E.rec")).expect("resident").clone();
    extra.name = name("E.rec_1");
    env.recursors.insert(name("E.rec_1"), extra);
    assert_eq!(
        env.lean_replay_inductive_block(&[name("E")]),
        Err(InductiveReplayMismatch::NoSuchRecursor {
            name: name("E.rec_1"),
            block: name("E")
        })
    );
}

/// The replay never mutates the environment it is asked about.
#[test]
fn test_lean_replay_inductive_block_leaves_the_environment_untouched() {
    let mut env = env_with_enum();
    let rec = env.recursors.get_mut(&name("E.rec")).expect("resident");
    let rule_a = rec.rules[0].rhs.clone();
    rec.rules[1].rhs = rule_a.clone();
    let _ = env.lean_replay_inductive_block(&[name("E")]);
    assert_eq!(
        env.recursors.get(&name("E.rec")).expect("resident").rules[1].rhs,
        rule_a,
        "the forged rule is still what the caller registered"
    );
}

#[path = "inductive_lean_replay_flag_tests.rs"]
mod flag_tests;

#[path = "inductive_lean_replay_dep_nested_tests.rs"]
mod dep_nested_tests;
