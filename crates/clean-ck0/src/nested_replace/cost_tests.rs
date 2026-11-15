// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! What phase 3 and the self-reference rewrite look at grows with the term
//! and with what they are charged (R176), never with a spine's square, a
//! nest's depth times its size, or the occurrences' square. The walk steps
//! are `crate::term::WALK_STEPS`, scoped to the test's thread. They do not
//! count `term_mentions`, which is positivity's, so R174's mention walks
//! are not in them. The figures quoted for R174 and for the new code are
//! from the Python model in the R176 review; the bounds leave at least 1.4×
//! headroom over the new ones.

use super::tests::{app, c, env, n, nodes, occ, pi, prop, rewrite, self_ref, term, ty};
use super::*;
use crate::inductive::{add_inductive, Constructor, InductiveDecl};
use crate::minimal_env::MinimalEnv;
use crate::positivity::term_mentions;
use crate::rawexpr::{RawExpr, RawLevel};
use crate::term::walk_steps;

/// [`widen`] of `env()`.
pub(super) fn wide_env() -> MinimalEnv {
    widen(env())
}

/// `env` with the constant `F` and `P (α β : Type) : Type`,
/// `P.mk : (α β : Type) → P α β`.
pub(super) fn widen(env: MinimalEnv) -> MinimalEnv {
    let mut env = env.with_const(n("F"), 0);
    let own = MinimalEnv::new().with_const(n("P"), 0);
    let p_ctor = pi(
        ty(),
        pi(ty(), app(app(c("P"), RawExpr::BVar(1)), RawExpr::BVar(0))),
    );
    let decl = InductiveDecl {
        name: n("P"),
        num_level_params: 0,
        num_params: 2,
        type_: Term::validate_closed(&own, &pi(ty(), pi(ty(), ty()))).expect("P's type"),
        constructors: vec![Constructor {
            name: n("P.mk"),
            type_: Term::validate_closed(&own, &p_ctor).expect("P.mk"),
        }],
    };
    add_inductive(&mut env, decl).expect("P admits");
    env
}

/// A tree of `2^height` leaves `leaf` joined by `G`: `2^(height + 2) - 3`
/// nodes.
fn g_tree(height: u32, leaf: &RawExpr) -> RawExpr {
    match height.checked_sub(1) {
        None => leaf.clone(),
        Some(h) => app(app(c("G"), g_tree(h, leaf)), g_tree(h, leaf)),
    }
}

/// `Sort k`.
fn sort(k: u32) -> RawExpr {
    let level = (0..k).fold(RawLevel::Zero, |l, _| RawLevel::Succ(Box::new(l)));
    RawExpr::Sort(level)
}

/// The argument of the site `C x`, the domain of the second Π of `t`.
fn second_site_arg(t: &Term) -> Option<Term> {
    let TermKind::Pi(_, _, rest) = t.kind() else {
        return None;
    };
    let TermKind::Pi(_, dom, _) = rest.kind() else {
        return None;
    };
    let TermKind::App(_, a) = dom.kind() else {
        return None;
    };
    Some(a.clone())
}

/// Run `f` on a thread with room for terms 1,024 deep, as admission does;
/// the walk steps it counts are that thread's.
fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(8_388_608)
        .spawn(f)
        .expect("thread spawns")
        .join()
        .expect("the test body returns")
}

/// (a) `F T Prop … Prop → T`, 990 arguments, in a parent with no
/// parameters: 1,983 nodes. R174's `unfold_apps` at each of the spine's
/// applications took 990·991/2 = 490,545 argument handles; the spine is now
/// taken apart once: 3,966 steps (1,983 marking, 990 taking it apart, 993
/// rewriting). `F` is no inductive, so nothing is lowered or charged.
#[test]
fn test_replace_nested_long_spine_is_taken_apart_once() {
    let (steps, size, charged, same) = deep(|| {
        let env = wide_env();
        let spine = (1..990).fold(app(c("F"), c("T")), |f, _| app(f, prop()));
        let ctor = term(&env, &pi(spine, c("T")), 0);
        let occs = [occ("C", vec![term(&env, &c("T"), 0)])];
        let ((out, charged), steps) = walk_steps(|| rewrite(&env, &ctor, &occs, 0));
        (steps, nodes(&ctor), charged, out == ctor)
    });
    assert_eq!(size, 1_983);
    assert!(same, "nothing in it matches");
    assert_eq!(charged, 0);
    assert!(steps <= size.saturating_mul(3), "{steps} steps");
}

/// (b) `C T → C (C … (C D)) → T`, 64 applications of `C` around `D`, a tree
/// of height 10 of `Prop` (4,093 nodes), and the occurrence `C T`: 4,227
/// nodes. The nest does not mention `T`. R174 tested each of its 64 sites
/// with `term_mentions` over the whole argument (4,093 + 2(j − 1) nodes
/// popped at the `j`-th from the inside, 265,984 in all, and 1 for `C T`;
/// the steps do not count them), rebuilt the nest and charged nothing; now
/// the nest is returned as it is, the same node (4,235 steps in all), and the
/// first site's one comparison is charged its 1 pair.
#[test]
fn test_replace_nested_nest_without_the_parent_is_not_walked_per_site() {
    let env = wide_env();
    let nest = (0..64).fold(g_tree(10, &prop()), |x, _| app(c("C"), x));
    let ctor = term(&env, &pi(app(c("C"), c("T")), pi(nest, c("T"))), 0);
    let occs = [occ("C", vec![term(&env, &c("T"), 0)])];
    let ((out, charged), steps) = walk_steps(|| rewrite(&env, &ctor, &occs, 0));
    let size = nodes(&ctor);
    assert_eq!(size, 4_227);
    assert_eq!(charged, 1);
    assert!(steps <= size.saturating_mul(2), "{steps} steps");
    let second = |t: &Term| match t.kind() {
        TermKind::Pi(_, _, rest) => match rest.kind() {
            TermKind::Pi(_, d, _) => Some(d.clone()),
            _ => None,
        },
        _ => None,
    };
    let (before, after) = (
        second(&ctor).expect("a field"),
        second(&out).expect("a field"),
    );
    assert!(Arc::ptr_eq(&before.kind, &after.kind), "the nest is itself");
    assert!(
        term_mentions(&out, &n("T._C")),
        "the first field is the auxiliary"
    );
}

/// (c) `P X (Sort 1 → T) → … → P X (Sort 64 → T) → T`, each `X` its own copy
/// of a tree of height 8 (1,021 nodes): 65,793 nodes, and the 64 occurrences
/// phase 1 records. R174 compared the site of field `j` with each earlier
/// occurrence of `P`, walking its equal but separately built `X` whole
/// before the second argument differed (about 2,060,700 steps, none
/// charged: the arguments are closed). Now each site is compared only with
/// the occurrence its key names, 2 pairs (both arguments are that
/// occurrence's own nodes), charged: 128 in all, about 66,300 steps.
#[test]
fn test_replace_nested_distinct_occurrences_are_not_compared_pairwise() {
    let env = wide_env();
    let fields: Vec<RawExpr> = (0u32..64)
        .map(|i| {
            app(
                app(c("P"), g_tree(8, &prop())),
                pi(sort(i.saturating_add(1)), c("T")),
            )
        })
        .collect();
    let raw = fields.into_iter().rev().fold(c("T"), |body, f| pi(f, body));
    let ctor = term(&env, &raw, 0);
    let mut occs = Vec::new();
    let mut cur = &ctor;
    while let TermKind::Pi(_, dom, codom) = cur.kind() {
        let (_, args) = dom.unfold_apps();
        let canon = args
            .iter()
            .map(|a| lower_params(a, 0, 0).expect("a closed argument lowers"))
            .collect();
        occs.push(occ("P", canon));
        cur = codom;
    }
    let ((out, charged), steps) = walk_steps(|| rewrite(&env, &ctor, &occs, 0));
    let size = nodes(&ctor);
    assert_eq!(size, 65_793);
    assert_eq!(charged, 128);
    assert!(steps <= size.saturating_mul(2), "{steps} steps");
    assert!(!term_mentions(&out, &n("P")), "every site is the auxiliary");
}

/// (d) `(A : Type) → C (T A D) → T A`, `D` a closed tree of height 8 (1,021
/// nodes), the occurrence the site's own argument lowered, as phase 1
/// records it. Lowering builds the 3 nodes above `A` and shares `T` and `D`;
/// the comparison looks at 5 pairs, `T` and `D` each the same node on both
/// sides: 8. R174 charged the argument whole: 1,025 nodes.
#[test]
fn test_replace_nested_charges_the_nodes_lowering_builds() {
    let env = wide_env();
    let site_arg = app(app(c("T"), RawExpr::BVar(0)), g_tree(8, &prop()));
    let raw = pi(
        ty(),
        pi(app(c("C"), site_arg), app(c("T"), RawExpr::BVar(1))),
    );
    let ctor = term(&env, &raw, 0);
    let arg = second_site_arg(&ctor).expect("the site's argument");
    let canon = lower_params(&arg, 0, 1).expect("the argument lowers");
    let (out, charged) = rewrite(&env, &ctor, &[occ("C", vec![canon])], 1);
    assert_eq!(charged, 8);
    assert!(term_mentions(&out, &n("T._C")), "the site is the auxiliary");
}

/// (g) The self-reference `C (T A E) Prop … Prop`, 8 arguments, `E` a tree
/// of height 8 with leaves `A` (1,021 nodes), against the occurrence
/// `C (T A Prop)`: R174 charged the parameter argument whole at each of the
/// spine's 8 applications, 8 × 1,025 = 8,200. Now it is lowered once (769
/// nodes built: every node of it but `T` and the 255 `G`s) and compared
/// once (1 pair: the hashes differ): 770.
#[test]
fn test_replace_container_self_ref_compares_a_spine_once() {
    let env = wide_env();
    let param = app(app(c("T"), RawExpr::BVar(0)), g_tree(8, &RawExpr::BVar(0)));
    let raw = (1..8).fold(app(c("C"), param), |f, _| app(f, prop()));
    let site = term(&env, &raw, 1);
    let cargs = [term(&env, &app(app(c("T"), RawExpr::BVar(0)), prop()), 1)];
    let (out, charged) = self_ref(&site, "C", 1, &cargs, 1);
    assert_eq!(charged, 770);
    assert!(out == site, "nothing matches");
}

/// (h) The self-reference `C (G A) A … A`, 501 arguments (1,005 nodes),
/// against the occurrence `C (T A)`: R174 lowered and compared the
/// parameter argument at each of the spine's 501 applications, charging
/// 501 × 3 = 1,503 and unfolding 501·502/2 = 125,751 argument handles. Now
/// the spine is taken apart once, `G A` lowered once (2 nodes) and compared
/// once (1 pair): 3 charged, about 2,012 steps.
#[test]
fn test_replace_container_self_ref_long_spine_is_compared_once() {
    let (steps, size, charged, same) = deep(|| {
        let env = wide_env();
        let head = app(c("C"), app(c("G"), RawExpr::BVar(0)));
        let raw = (0..500).fold(head, |f, _| app(f, RawExpr::BVar(0)));
        let site = term(&env, &raw, 1);
        let cargs = [term(&env, &app(c("T"), RawExpr::BVar(0)), 1)];
        let ((out, charged), steps) = walk_steps(|| self_ref(&site, "C", 1, &cargs, 1));
        (steps, nodes(&site), charged, out == site)
    });
    assert_eq!(size, 1_005);
    assert_eq!(charged, 3);
    assert!(same, "nothing matches");
    assert!(steps <= size.saturating_mul(3), "{steps} steps");
}
