// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The walks and the lowering charge what they claim (R176): `same_term`
//! decides as `Term`'s equality, with whole hashes or narrowed ones, and
//! with whole hashes charges one per call that equality makes; the charged
//! lowering returns R174's and charges exactly the nodes it builds when it
//! succeeds; `Mentions` marks what `term_mentions` finds; and `Spine` takes
//! a term apart as `unfold_apps` does.

use proptest::prelude::*;
use proptest::sample::Index;

use super::*;
use crate::nested_replace::equivalence_tests::{
    arb_raw, narrowing, prop_env, r174_lower, validated,
};
use crate::nested_replace::tests::{n, prop, ty};
use crate::nested_replace::{lower_params, lower_params_charged};
use crate::positivity::term_mentions;
use crate::rawexpr::{BinderInfo, RawExpr};
use crate::term::{walk_steps, NODES_BUILT};

/// `raw` with the node `at` places into its pre-order walk changed where
/// only a walk that reaches it sees the change (and `at` is then `None`):
/// a binder's kind, a projection's index, a `let`'s value, an
/// application's argument, or a leaf. Past its last node, `raw` itself.
fn perturb(raw: &RawExpr, at: &mut Option<usize>) -> RawExpr {
    let here = *at == Some(0);
    *at = at.and_then(|k| k.checked_sub(1));
    match raw {
        RawExpr::App(f, a) if here => RawExpr::App(f.clone(), Box::new(other(a))),
        RawExpr::App(f, a) => RawExpr::App(Box::new(perturb(f, at)), Box::new(perturb(a, at))),
        RawExpr::Lam(bi, d, b) if here => RawExpr::Lam(flip(*bi), d.clone(), b.clone()),
        RawExpr::Lam(bi, d, b) => {
            RawExpr::Lam(*bi, Box::new(perturb(d, at)), Box::new(perturb(b, at)))
        }
        RawExpr::Pi(bi, d, b) if here => RawExpr::Pi(flip(*bi), d.clone(), b.clone()),
        RawExpr::Pi(bi, d, b) => {
            RawExpr::Pi(*bi, Box::new(perturb(d, at)), Box::new(perturb(b, at)))
        }
        RawExpr::Let(t, v, b) if here => RawExpr::Let(t.clone(), Box::new(other(v)), b.clone()),
        RawExpr::Let(t, v, b) => RawExpr::Let(
            Box::new(perturb(t, at)),
            Box::new(perturb(v, at)),
            Box::new(perturb(b, at)),
        ),
        RawExpr::Proj(s, i, e) if here => RawExpr::Proj(s.clone(), u32::from(*i == 0), e.clone()),
        RawExpr::Proj(s, i, e) => RawExpr::Proj(s.clone(), *i, Box::new(perturb(e, at))),
        leaf if here => other(leaf),
        leaf => leaf.clone(),
    }
}

/// The nodes of `raw`.
fn raw_nodes(raw: &RawExpr) -> usize {
    let below = match raw {
        RawExpr::Shared(node) => return raw_nodes(node),
        RawExpr::App(f, a) | RawExpr::Lam(_, f, a) | RawExpr::Pi(_, f, a) => {
            raw_nodes(f).saturating_add(raw_nodes(a))
        }
        RawExpr::Let(t, v, b) => raw_nodes(t)
            .saturating_add(raw_nodes(v))
            .saturating_add(raw_nodes(b)),
        RawExpr::Proj(_, _, e) => raw_nodes(e),
        RawExpr::BVar(_)
        | RawExpr::Sort(_)
        | RawExpr::Const(..)
        | RawExpr::Elim(..)
        | RawExpr::Lit(_) => 0,
    };
    below.saturating_add(1)
}

/// `Type` in place of `Prop`, else `Prop`.
fn other(e: &RawExpr) -> RawExpr {
    if *e == prop() {
        ty()
    } else {
        prop()
    }
}

/// The other binder kind of the two the terms use.
fn flip(bi: BinderInfo) -> BinderInfo {
    if bi == BinderInfo::Default {
        BinderInfo::Implicit
    } else {
        BinderInfo::Default
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1024))]

    /// `b` is `a` built apart (sharing no node with it, so the walk goes
    /// to the leaves), `a` with one of its nodes changed, or another term.
    /// With hashes narrowed, the walk cannot stop at a hash and must find
    /// the change itself.
    #[test]
    fn prop_same_term_is_eq_and_charges_its_calls(
        raw_a in arb_raw(),
        raw_c in arb_raw(),
        pick in 0u8..3,
        at in any::<Index>(),
        narrow in narrowing(),
    ) {
        let env = prop_env();
        let a = validated(&env, &raw_a);
        let raw_b = match pick {
            0 => raw_a.clone(),
            1 => perturb(&raw_a, &mut Some(at.index(raw_nodes(&raw_a)))),
            _ => raw_c,
        };
        let b = validated(&env, &raw_b);
        let _narrowed = narrow_hashes(narrow);
        let (equal, calls) = walk_steps(|| a == b);
        let mut pairs: u64 = 0;
        let mut charge = |nodes: u64| {
            pairs = pairs.saturating_add(nodes);
            Ok::<(), NestedError>(())
        };
        let decided = same_term(&a, &b, &mut charge).expect("a free charge never refuses");
        prop_assert_eq!(decided, equal);
        if narrow.is_none() {
            prop_assert_eq!(pairs, calls);
        }
    }

    #[test]
    fn prop_charged_lowering_is_r174s_and_charges_what_it_builds(
        raw in arb_raw(),
        below in 0u32..3,
        np in 0u32..3,
    ) {
        let env = prop_env();
        let t = validated(&env, &raw);
        let mut charged: u64 = 0;
        let mut charge = |nodes: u64| {
            charged = charged.saturating_add(nodes);
            Ok::<(), NestedError>(())
        };
        let before = NODES_BUILT.with(Cell::get);
        let lowered = lower_params_charged(&t, below, np, &mut charge)
            .expect("a free charge never refuses");
        let built = NODES_BUILT.with(Cell::get).saturating_sub(before);
        let oracle = r174_lower(&t, below, np, 0);
        prop_assert!(lowered == oracle);
        prop_assert!(lower_params(&t, below, np) == oracle);
        if lowered.is_some() {
            prop_assert_eq!(charged, built);
        } else {
            prop_assert!(charged >= built.saturating_add(1), "the failing variable is charged");
        }
    }

    #[test]
    fn prop_mentions_marks_what_term_mentions_finds(raw in arb_raw()) {
        let env = prop_env();
        let t = validated(&env, &raw);
        let name = Name::from_dotted("T");
        let marks = Mentions::of(&t, &name);
        let mut stack = vec![&t];
        while let Some(node) = stack.pop() {
            prop_assert_eq!(marks.contains(node), term_mentions(node, &name));
            stack.extend(children(node).into_iter().flatten());
        }
    }

    #[test]
    fn prop_spine_is_unfold_apps(raw in arb_raw()) {
        let env = prop_env();
        let t = validated(&env, &raw);
        let spine = Spine::of(&t);
        let (head, args) = t.unfold_apps();
        prop_assert!(Arc::ptr_eq(&spine.head.kind, &head.kind));
        prop_assert_eq!(spine.args.len(), args.len());
        prop_assert_eq!(spine.apps.len(), args.len());
        for (i, (s, a)) in spine.args.iter().zip(&args).enumerate() {
            prop_assert!(Arc::ptr_eq(&s.kind, &a.kind));
            let prefix = args.get(..=i).unwrap_or_default();
            let app = spine.apps.get(i).expect("an application per argument");
            prop_assert!(**app == Term::apply(head.clone(), prefix));
        }
    }
}

/// With every hash alike, `same_term` tells apart what only the hash told
/// apart before its walk reached it: a `let`'s value, a projection's index,
/// a binder's kind.
#[test]
fn test_same_term_with_hashes_alike_finds_each_difference_itself() {
    let env = prop_env();
    let firsts = [
        RawExpr::Let(Box::new(ty()), Box::new(prop()), Box::new(prop())),
        RawExpr::Proj(n("S"), 0, Box::new(prop())),
        RawExpr::Pi(BinderInfo::Default, Box::new(ty()), Box::new(prop())),
        RawExpr::Lam(BinderInfo::Implicit, Box::new(ty()), Box::new(prop())),
    ];
    let _alike = narrow_hashes(Some(1));
    for raw in &firsts {
        let a = validated(&env, raw);
        let b = validated(&env, &perturb(raw, &mut Some(0)));
        let mut free = |_: u64| Ok::<(), NestedError>(());
        assert!(a != b, "{a:?} and {b:?} differ");
        let same = same_term(&a, &b, &mut free).expect("a free charge never refuses");
        assert!(!same, "{a:?} and {b:?} are told apart");
    }
}

/// The shrunk repeated-pair counterexample found while moving equality to a
/// DAG walk. Its comparison is five popped pairs, not seven tree-path pairs.
#[test]
fn repeated_shared_pair_comparison_matches_the_exact_charge() {
    let env = prop_env();
    let leaf = RawExpr::App(
        Box::new(RawExpr::Const(n("C"), vec![])),
        Box::new(RawExpr::Const(n("P"), vec![])),
    );
    let raw = RawExpr::App(Box::new(leaf.clone()), Box::new(leaf));
    let left = validated(&env, &raw);
    let right = validated(&env, &raw);
    let (equal, calls) = walk_steps(|| left == right);
    let mut charged = 0u64;
    let mut charge = |n: u64| {
        charged = charged.saturating_add(n);
        Ok(())
    };
    assert!(equal);
    assert!(same_term(&left, &right, &mut charge).unwrap());
    assert_eq!(calls, 5);
    assert_eq!(charged, calls);
}
