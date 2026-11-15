// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The rewrites return what R174's did (R176), on random terms whose sites
//! have every shape (spines headed by a container, by the parent, by
//! neither; occurrences of each arity; `let`s, projections, literals, an
//! eliminator, both binder kinds, a parent at three universe levels), with
//! whole hashes and with hashes narrowed so that keys collide. Every node
//! R174's rewrite visits that does not mention the constant they look for
//! is a node of the result, where R174 rebuilt it, matched sites or not.
//! The oracles are R174's code at 0f4c878c4 with its charges removed, its
//! lowering included, so nothing here shares code with what it checks.

use std::cell::Cell;
use std::collections::HashSet;

use proptest::prelude::*;
use proptest::sample::Index;
use proptest::test_runner::{TestCaseResult, TestRunner};

use super::cost_tests::widen;
use super::tests::{app, c, n, parent_env, pi, prop, rewrite, self_ref, ty};
use super::*;
use crate::minimal_env::MinimalEnv;
use crate::positivity::term_mentions;
use crate::rawexpr::{BinderInfo, RawExpr, RawLevel, RawLit};

/// The proptests' environment: the parent `T` has one universe parameter,
/// and `C`, `P`, `G` and `F` are as in the unit tests.
pub(super) fn prop_env() -> MinimalEnv {
    widen(parent_env(1))
}

/// `raw` validated as the proptests take it: under three loose variables,
/// with one universe parameter.
pub(super) fn validated(env: &MinimalEnv, raw: &RawExpr) -> Term {
    Term::validate(env, raw, 3, 1).expect("the term validates")
}

/// `0`, `u` or `u + 1`.
fn level() -> impl Strategy<Value = RawLevel> {
    prop_oneof![
        Just(RawLevel::Zero),
        Just(RawLevel::Param(0)),
        Just(RawLevel::Succ(Box::new(RawLevel::Param(0)))),
    ]
}

/// An explicit or an implicit binder.
fn binder() -> impl Strategy<Value = BinderInfo> {
    prop_oneof![Just(BinderInfo::Default), Just(BinderInfo::Implicit)]
}

/// Random terms over `T.{l}` (the parent), `C` and `P` (containers of one
/// and two parameters), `G`, sorts, string literals, `C`'s eliminator and
/// three loose variables: applications, Π and λ of both binder kinds,
/// `let`s and projections.
pub(super) fn arb_raw() -> impl Strategy<Value = RawExpr> {
    let leaf = prop_oneof![
        3 => (0u32..3).prop_map(RawExpr::BVar),
        1 => Just(prop()),
        1 => Just(ty()),
        1 => Just(RawExpr::Sort(RawLevel::Param(0))),
        3 => level().prop_map(|l| RawExpr::Const(n("T"), vec![l])),
        3 => Just(c("C")),
        3 => Just(c("P")),
        1 => Just(c("G")),
        1 => (0u32..2).prop_map(|k| RawExpr::Lit(RawLit::Str(k.to_string()))),
        1 => Just(RawExpr::Elim(n("C"), RawLevel::Zero, vec![])),
    ];
    leaf.prop_recursive(6, 64, 4, |inner| {
        prop_oneof![
            4 => (inner.clone(), inner.clone()).prop_map(|(f, a)| app(f, a)),
            1 => (binder(), inner.clone(), inner.clone())
                .prop_map(|(bi, d, b)| RawExpr::Pi(bi, Box::new(d), Box::new(b))),
            1 => (binder(), inner.clone(), inner.clone())
                .prop_map(|(bi, d, b)| RawExpr::Lam(bi, Box::new(d), Box::new(b))),
            1 => (inner.clone(), inner.clone(), inner.clone())
                .prop_map(|(t, v, b)| RawExpr::Let(Box::new(t), Box::new(v), Box::new(b))),
            1 => (0u32..2, inner).prop_map(|(i, e)| RawExpr::Proj(n("S"), i, Box::new(e))),
        ]
    })
}

/// Whole hashes, or hashes folded onto 1, 3 or 7 values (`narrow_hashes`).
pub(super) fn narrowing() -> impl Strategy<Value = Option<u64>> {
    prop_oneof![
        Just(None),
        Just(Some(1u64)),
        Just(Some(3u64)),
        Just(Some(7u64)),
    ]
}

/// Run `test` on 1,024 cases of `strategy`, failing with the case it fails.
fn check<S: Strategy>(strategy: &S, test: impl Fn(S::Value) -> TestCaseResult) {
    let config = ProptestConfig {
        failure_persistence: None,
        ..ProptestConfig::with_cases(1024)
    };
    if let Err(failure) = TestRunner::new(config).run(strategy, test) {
        panic!("{failure}");
    }
}

/// R174's `lower_params_at` (0f4c878c4), verbatim but for its name.
pub(super) fn r174_lower(t: &Term, below: u32, num_params: u32, local: u32) -> Option<Term> {
    if t.loose <= local {
        return Some(t.clone());
    }
    match t.kind() {
        TermKind::BVar(i) => {
            let i = *i;
            if i < local {
                return Some(Term::bvar(i));
            }
            let enclosing = i.checked_sub(local)?;
            let param_lo = below;
            let param_hi = below.checked_add(num_params)?;
            if enclosing < param_lo {
                return None;
            }
            if enclosing >= param_hi {
                return None;
            }
            let lowered = i.checked_sub(below)?;
            Some(Term::bvar(lowered))
        }
        TermKind::Sort(_) | TermKind::Const(_) | TermKind::Elim(_) | TermKind::Lit(_) => {
            Some(t.clone())
        }
        TermKind::App(f, a) => Some(Term::app(
            r174_lower(f, below, num_params, local)?,
            r174_lower(a, below, num_params, local)?,
        )),
        TermKind::Lam(bi, ty, body) => Some(Term::lam(
            *bi,
            r174_lower(ty, below, num_params, local)?,
            r174_lower(body, below, num_params, local.checked_add(1)?)?,
        )),
        TermKind::Pi(bi, ty, body) => Some(Term::pi(
            *bi,
            r174_lower(ty, below, num_params, local)?,
            r174_lower(body, below, num_params, local.checked_add(1)?)?,
        )),
        TermKind::Let(ty, val, body) => Some(Term::let_(
            r174_lower(ty, below, num_params, local)?,
            r174_lower(val, below, num_params, local)?,
            r174_lower(body, below, num_params, local.checked_add(1)?)?,
        )),
        TermKind::Proj(name, idx, e) => Some(Term::proj(
            name.clone(),
            *idx,
            r174_lower(e, below, num_params, local)?,
        )),
    }
}

/// R174's phase-3 rewrite (`replace_nested_at` at 0f4c878c4) without its
/// charges: the oracle. Each node it visits that does not mention the
/// parent is pushed on `kept`.
fn reference(
    env: &dyn Env,
    expr: &Term,
    occs: &[Occurrence],
    np: u32,
    depth: u32,
    kept: &mut Vec<Term>,
) -> Term {
    let parent = n("T");
    if !term_mentions(expr, &parent) {
        kept.push(expr.clone());
    }
    let (head, args) = expr.unfold_apps();
    if let (Some(below), TermKind::Const(k)) = (depth.checked_sub(np), head.kind()) {
        let cname = k.name();
        let cont_np = env.inductive_num_params(cname).filter(|_| *cname != parent);
        let candidate = occs
            .iter()
            .any(|o| o.container == *cname && o.args.len() == args.len());
        let mentions = candidate && args.iter().any(|a| term_mentions(a, &parent));
        if let (Some(cont_np), true) = (cont_np, mentions) {
            let canon: Option<Vec<Term>> =
                args.iter().map(|a| r174_lower(a, below, np, 0)).collect();
            let found = canon.and_then(|canon| {
                occs.iter()
                    .find(|o| o.container == *cname && o.args == canon)
            });
            if let Some(occ) = found {
                let levels: Arc<[Level]> = Arc::from(Vec::new());
                let skip = usize::try_from(cont_np).unwrap_or(usize::MAX);
                return args.iter().skip(skip).fold(
                    aux_applied_to_params(&occ.aux_name, &levels, np, below),
                    |f, a| Term::app(f, reference(env, a, occs, np, depth, kept)),
                );
            }
        }
    }
    map_children_depth(expr, depth, &mut |child, depth| {
        Ok(reference(env, child, occs, np, depth, kept))
    })
    .expect("the oracle does not refuse")
}

/// R174's self-reference rewrite (`self_ref_at` at 0f4c878c4) without its
/// charges, to the auxiliary `T._C`: the oracle. Each node it visits that
/// does not mention the container is pushed on `kept`.
fn reference_self_ref(
    expr: &Term,
    container: &Name,
    ncp: u32,
    cargs: &[Term],
    np: u32,
    below: u32,
    kept: &mut Vec<Term>,
) -> Term {
    if !term_mentions(expr, container) {
        kept.push(expr.clone());
    }
    let (head, args) = expr.unfold_apps();
    let k = usize::try_from(ncp).unwrap_or(usize::MAX);
    let headed = matches!(head.kind(), TermKind::Const(h) if h.name() == container);
    let matches = headed
        && args.len() >= k
        && cargs.len() >= k
        && args
            .iter()
            .take(k)
            .zip(cargs.iter().take(k))
            .all(|(s, o)| r174_lower(s, below, np, 0).is_some_and(|l| &l == o));
    if matches {
        let levels: Arc<[Level]> = Arc::from(Vec::new());
        return args.iter().skip(k).fold(
            aux_applied_to_params(&n("T._C"), &levels, np, below),
            |f, a| {
                let a = reference_self_ref(a, container, ncp, cargs, np, below, kept);
                Term::app(f, a)
            },
        );
    }
    map_children_depth(expr, below, &mut |child, below| {
        Ok(reference_self_ref(
            child, container, ncp, cargs, np, below, kept,
        ))
    })
    .expect("the oracle does not refuse")
}

/// The lowered arguments of every application in `t` headed by `container`
/// (any of `C` and `P` when `None`) with an argument that mentions `needs`,
/// `depth` binders in, with `below = depth - skip`: the occurrences such a
/// site would be matched against, each once.
fn sites(
    t: &Term,
    container: Option<&Name>,
    needs: Option<&Name>,
    np: u32,
    skip: u32,
    depth: u32,
    out: &mut Vec<(Name, Vec<Term>)>,
) {
    let (head, args) = t.unfold_apps();
    if let (TermKind::Const(k), Some(below)) = (head.kind(), depth.checked_sub(skip)) {
        let name = k.name();
        let named = container.map_or(*name == n("C") || *name == n("P"), |c| c == name);
        let mentions = needs.is_none_or(|p| args.iter().any(|a| term_mentions(a, p)));
        if named && mentions {
            let canon: Option<Vec<Term>> =
                args.iter().map(|a| r174_lower(a, below, np, 0)).collect();
            if let Some(canon) = canon {
                if !out.iter().any(|(o, a)| o == name && *a == canon) {
                    out.push((name.clone(), canon));
                }
            }
        }
    }
    let under = depth.saturating_add(1);
    match t.kind() {
        TermKind::App(f, a) => {
            sites(f, container, needs, np, skip, depth, out);
            sites(a, container, needs, np, skip, depth, out);
        }
        TermKind::Pi(_, d, b) | TermKind::Lam(_, d, b) => {
            sites(d, container, needs, np, skip, depth, out);
            sites(b, container, needs, np, skip, under, out);
        }
        TermKind::Let(d, v, b) => {
            sites(d, container, needs, np, skip, depth, out);
            sites(v, container, needs, np, skip, depth, out);
            sites(b, container, needs, np, skip, under, out);
        }
        TermKind::Proj(_, _, e) => sites(e, container, needs, np, skip, depth, out),
        TermKind::BVar(_)
        | TermKind::Sort(_)
        | TermKind::Const(_)
        | TermKind::Elim(_)
        | TermKind::Lit(_) => {}
    }
}

/// The addresses of every node of `t`.
fn addresses(t: &Term, out: &mut HashSet<*const TermKind>) {
    out.insert(Arc::as_ptr(&t.kind));
    match t.kind() {
        TermKind::App(a, b) | TermKind::Pi(_, a, b) | TermKind::Lam(_, a, b) => {
            addresses(a, out);
            addresses(b, out);
        }
        TermKind::Let(a, b, d) => {
            addresses(a, out);
            addresses(b, out);
            addresses(d, out);
        }
        TermKind::Proj(_, _, a) => addresses(a, out),
        _ => {}
    }
}

/// Every node of `kept` is a node of `out`, the same allocation; and
/// whether one of them is not a leaf, which R174 rebuilt.
fn kept_in(out: &Term, kept: &[Term]) -> Result<bool, TestCaseError> {
    let mut present = HashSet::new();
    addresses(out, &mut present);
    for t in kept {
        prop_assert!(present.contains(&Arc::as_ptr(&t.kind)), "{t:?} is rebuilt");
    }
    Ok(kept.iter().any(|t| {
        matches!(
            t.kind(),
            TermKind::App(..)
                | TermKind::Lam(..)
                | TermKind::Pi(..)
                | TermKind::Let(..)
                | TermKind::Proj(..)
        )
    }))
}

/// A constructor-shaped term: `np` parameters of type `Type`, then `parts`'
/// fields, then its last part.
fn constructor(parts: &[RawExpr], np: u32) -> RawExpr {
    let mut rev = parts.iter().rev();
    let body = rev.next().cloned().unwrap_or_else(prop);
    let fields = rev.fold(body, |b, f| pi(f.clone(), b));
    (0..np).fold(fields, |b, _| pi(ty(), b))
}

/// Phase 3 returns R174's term on constructor-shaped terms (the parent's
/// parameters, three random fields, a random body), with occurrences taken
/// from the term's own sites (so that some match) and a random subset of
/// them kept. The cases where a site matched beside a kept node that is
/// not a leaf are counted, so the check cannot pass by never meeting one.
#[test]
fn prop_replace_nested_is_r174s_and_keeps_what_does_not_mention_the_parent() {
    let strategy = (
        proptest::collection::vec(arb_raw(), 4),
        0u32..3,
        proptest::collection::vec(any::<bool>(), 1..8),
        narrowing(),
    );
    let substantive = Cell::new(0u32);
    check(&strategy, |(parts, np, keep, narrow)| {
        let _narrowed = narrow_hashes(narrow);
        let env = prop_env();
        let expr = validated(&env, &constructor(&parts, np));
        let parent = n("T");
        let mut found = Vec::new();
        sites(&expr, None, Some(&parent), np, np, 0, &mut found);
        let occs: Vec<Occurrence> = found
            .into_iter()
            .zip(keep.iter().cycle())
            .filter(|(_, chosen)| **chosen)
            .enumerate()
            .map(|(i, ((container, args), _))| Occurrence {
                container,
                args,
                levels: vec![],
                aux_name: n(&format!("T._{i}")),
            })
            .collect();
        let (out, _) = rewrite(&env, &expr, &occs, np);
        let mut kept = Vec::new();
        prop_assert!(out == reference(&env, &expr, &occs, np, 0, &mut kept));
        if kept_in(&out, &kept)? && out != expr {
            substantive.set(substantive.get().saturating_add(1));
        }
        Ok(())
    });
    assert!(substantive.get() > 0, "no case matched beside a kept node");
}

/// The self-reference rewrite returns R174's term, with the occurrence's
/// arguments taken from one of the term's own container sites when it has
/// one (so that it can match), else random; counted as phase 3's.
#[test]
fn prop_replace_container_self_ref_is_r174s_and_keeps_what_does_not_mention_it() {
    let strategy = (
        arb_raw(),
        (0u32..3, 0u32..3, any::<bool>()),
        any::<Index>(),
        proptest::collection::vec(arb_raw(), 0..3),
        narrowing(),
    );
    let substantive = Cell::new(0u32);
    check(
        &strategy,
        |(raw, (np, ncp, two), pick, raw_cargs, narrow)| {
            let _narrowed = narrow_hashes(narrow);
            let env = prop_env();
            let expr = validated(&env, &raw);
            let container = if two { "P" } else { "C" };
            let name = n(container);
            let mut found = Vec::new();
            sites(&expr, Some(&name), None, np, 0, 0, &mut found);
            let cargs: Vec<Term> = if found.is_empty() {
                raw_cargs.iter().map(|a| validated(&env, a)).collect()
            } else {
                found.swap_remove(pick.index(found.len())).1
            };
            let (out, _) = self_ref(&expr, container, ncp, &cargs, np);
            let mut kept = Vec::new();
            let expected = reference_self_ref(&expr, &name, ncp, &cargs, np, 0, &mut kept);
            prop_assert!(out == expected);
            if kept_in(&out, &kept)? && out != expr {
                substantive.set(substantive.get().saturating_add(1));
            }
            Ok(())
        },
    );
    assert!(substantive.get() > 0, "no case matched beside a kept node");
}
