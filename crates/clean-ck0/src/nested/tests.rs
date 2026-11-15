// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Phase 1 compares a new occurrence only with those of its key (R176):
//! distinct occurrences are not compared pairwise, and a repeated one is
//! still found, past those of its key that differ when keys collide. The
//! walk steps are `crate::term::WALK_STEPS`.

use super::*;
use crate::inductive::{add_inductive, Constructor};
use crate::minimal_env::MinimalEnv;
use crate::rawexpr::{BinderInfo, RawExpr, RawLevel};
use crate::term::walk_steps;

fn n(s: &str) -> Name {
    Name::from_dotted(s)
}

fn c(s: &str) -> RawExpr {
    RawExpr::Const(n(s), vec![])
}

fn app(f: RawExpr, a: RawExpr) -> RawExpr {
    RawExpr::App(Box::new(f), Box::new(a))
}

fn pi(d: RawExpr, b: RawExpr) -> RawExpr {
    RawExpr::Pi(BinderInfo::Default, Box::new(d), Box::new(b))
}

/// `Sort k`.
fn sort(k: u32) -> RawExpr {
    let level = (0..k).fold(RawLevel::Zero, |l, _| RawLevel::Succ(Box::new(l)));
    RawExpr::Sort(level)
}

/// A tree of `2^height` leaves `Prop` joined by `G`: `2^(height + 2) - 3`
/// nodes.
fn g_tree(height: u32) -> RawExpr {
    match height.checked_sub(1) {
        None => sort(0),
        Some(h) => app(app(c("G"), g_tree(h)), g_tree(h)),
    }
}

/// `T` (the parent) and `G`, constants, and `P (α β : Type) : Type` with
/// `P.mk : (α β : Type) → P α β`.
fn env() -> MinimalEnv {
    let mut env = MinimalEnv::new()
        .with_const(n("T"), 0)
        .with_const(n("G"), 0);
    let own = MinimalEnv::new().with_const(n("P"), 0);
    let p_ctor = pi(
        sort(1),
        pi(
            sort(1),
            app(app(c("P"), RawExpr::BVar(1)), RawExpr::BVar(0)),
        ),
    );
    let decl = InductiveDecl {
        name: n("P"),
        num_level_params: 0,
        num_params: 2,
        type_: Term::validate_closed(&own, &pi(sort(1), pi(sort(1), sort(1)))).expect("P's type"),
        constructors: vec![Constructor {
            name: n("P.mk"),
            type_: Term::validate_closed(&own, &p_ctor).expect("P.mk"),
        }],
    };
    add_inductive(&mut env, decl).expect("P admits");
    env
}

/// Nodes of `t` as a tree.
fn nodes(t: &Term) -> u64 {
    let mut count: u64 = 0;
    let mut stack = vec![t];
    while let Some(x) = stack.pop() {
        count = count.saturating_add(1);
        match x.kind() {
            TermKind::App(a, b) | TermKind::Lam(_, a, b) | TermKind::Pi(_, a, b) => {
                stack.push(a);
                stack.push(b);
            }
            TermKind::Let(a, b, d) => {
                stack.push(a);
                stack.push(b);
                stack.push(d);
            }
            TermKind::Proj(_, _, a) => stack.push(a),
            TermKind::BVar(_)
            | TermKind::Sort(_)
            | TermKind::Const(_)
            | TermKind::Elim(_)
            | TermKind::Lit(_) => {}
        }
    }
    count
}

/// Phase 1 over one constructor type of `decl`.
fn collect(env: &MinimalEnv, decl: &InductiveDecl, ty: &Term) -> Vec<Occurrence> {
    let mut out = Vec::new();
    let mut index = OccIndex::default();
    collect_in_ctor(env, decl, ty, &mut out, &mut index).expect("phase 1 collects");
    out
}

/// `T : Type`, a parent with no parameters and the one constructor
/// `T.mk : ctor`.
fn t_decl(env: &MinimalEnv, ctor: &Term) -> InductiveDecl {
    InductiveDecl {
        name: n("T"),
        num_level_params: 0,
        num_params: 0,
        type_: Term::validate_closed(env, &sort(1)).expect("Type"),
        constructors: vec![Constructor {
            name: n("T.mk"),
            type_: ctor.clone(),
        }],
    }
}

/// `T.mk : P X (Sort 1 → T) → … → P X (Sort 64 → T) → P X (Sort 1 → T) → T`,
/// each `X` its own copy of a tree of height 8 (1,021 nodes), the last field
/// built again from the first: 66,821 nodes. R174 compared field `j` with
/// every earlier occurrence of `P`, walking the equal `X` whole before the
/// second argument differed (about 2,061,600 steps). Now a field is compared
/// only with the occurrence of its key, the repeat with the first field's
/// (1,024 pairs): about 1,300 steps. `term_mentions`, which tests each `X`
/// once, is positivity's, and the steps do not count it.
#[test]
fn test_collect_in_ctor_distinct_occurrences_are_not_compared_pairwise() {
    let env = env();
    let field = |i: u32| {
        app(
            app(c("P"), g_tree(8)),
            pi(sort(i.saturating_add(1)), c("T")),
        )
    };
    let raw = (0u32..64)
        .chain(std::iter::once(0))
        .rev()
        .fold(c("T"), |body, i| pi(field(i), body));
    let ctor = Term::validate_closed(&env, &raw).expect("the constructor validates");
    let decl = t_decl(&env, &ctor);
    let (occurrences, steps) = walk_steps(|| collect(&env, &decl, &ctor));
    let size = nodes(&ctor);
    assert_eq!(size, 66_821);
    assert_eq!(
        occurrences.len(),
        64,
        "the repeat is the first field's occurrence"
    );
    assert!(steps <= size.saturating_mul(2), "{steps} steps");
}

/// `T.mk : P X (Sort 1 → T) → P X (Sort 2 → T) → P X (Sort 3 → T) → P X
/// (Sort 2 → T) → T`, each `X` a tree of height 2, with every key alike:
/// the repeat's key names all three occurrences before it, and it is found
/// at the second, past the first, which differs (R176). Three occurrences.
#[test]
fn test_collect_in_ctor_repeat_is_found_past_a_colliding_key() {
    let env = env();
    let field = |i: u32| app(app(c("P"), g_tree(2)), pi(sort(i), c("T")));
    let raw = [1u32, 2, 3, 2]
        .into_iter()
        .rev()
        .fold(c("T"), |body, i| pi(field(i), body));
    let ctor = Term::validate_closed(&env, &raw).expect("the constructor validates");
    let decl = t_decl(&env, &ctor);
    let _collide = crate::nested_replace::narrow_hashes(Some(1));
    let occurrences = collect(&env, &decl, &ctor);
    assert_eq!(
        occurrences.len(),
        3,
        "the repeat is the second field's occurrence"
    );
}
