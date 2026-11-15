// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Phase 3 lowers a site's arguments only where an occurrence could match,
//! each at most once, returns what does not mention the parent as it is,
//! and charges each node lowering builds and each pair of nodes a
//! comparison looks at, before it does either (R174, R176); a key shared
//! by occurrences that differ costs their comparisons and refuses nothing.

use super::*;
use crate::inductive::{add_inductive, Constructor, InductiveDecl};
use crate::minimal_env::MinimalEnv;
use crate::positivity::term_mentions;
use crate::rawexpr::{BinderInfo, RawExpr, RawLevel};
use crate::term::NODES_BUILT;

pub(super) fn n(s: &str) -> Name {
    Name::from_dotted(s)
}

pub(super) fn c(s: &str) -> RawExpr {
    RawExpr::Const(n(s), vec![])
}

pub(super) fn app(f: RawExpr, a: RawExpr) -> RawExpr {
    RawExpr::App(Box::new(f), Box::new(a))
}

pub(super) fn pi(d: RawExpr, b: RawExpr) -> RawExpr {
    RawExpr::Pi(BinderInfo::Default, Box::new(d), Box::new(b))
}

pub(super) fn ty() -> RawExpr {
    RawExpr::Sort(RawLevel::Succ(Box::new(RawLevel::Zero)))
}

pub(super) fn prop() -> RawExpr {
    RawExpr::Sort(RawLevel::Zero)
}

/// [`parent_env`] with a parent that has no universe parameter.
pub(super) fn env() -> MinimalEnv {
    parent_env(0)
}

/// `T` with `t_levels` universe parameters, `G`, and the one-parameter
/// inductive `C (α : Type) : Type` with `C.mk : (α : Type) → C α`.
pub(super) fn parent_env(t_levels: u32) -> MinimalEnv {
    let mut env = MinimalEnv::new()
        .with_const(n("T"), t_levels)
        .with_const(n("G"), 0);
    let own = MinimalEnv::new().with_const(n("C"), 0);
    let decl = InductiveDecl {
        name: n("C"),
        num_level_params: 0,
        num_params: 1,
        type_: Term::validate_closed(&own, &pi(ty(), ty())).expect("the type validates"),
        constructors: vec![Constructor {
            name: n("C.mk"),
            type_: Term::validate_closed(&own, &pi(ty(), app(c("C"), RawExpr::BVar(0))))
                .expect("the ctor validates"),
        }],
    };
    add_inductive(&mut env, decl).expect("the container admits");
    env
}

pub(super) fn term(env: &MinimalEnv, raw: &RawExpr, ctx: u32) -> Term {
    Term::validate(env, raw, ctx, 0).expect("the term validates")
}

pub(super) fn occ(container: &str, args: Vec<Term>) -> Occurrence {
    Occurrence {
        container: n(container),
        args,
        levels: vec![],
        aux_name: n(&format!("T._{container}")),
    }
}

/// Nodes of `t` as a tree.
pub(super) fn nodes(t: &Term) -> u64 {
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

/// Rewrite `ctor` of a parent `T` with `np` parameters, adding up what is
/// charged.
pub(super) fn rewrite(env: &MinimalEnv, ctor: &Term, occs: &[Occurrence], np: u32) -> (Term, u64) {
    let levels: Arc<[Level]> = Arc::from(Vec::new());
    let index = OccIndex::of(occs);
    let mut charged: u64 = 0;
    let mut charge = |nodes: u64| {
        charged = charged.saturating_add(nodes);
        Ok::<(), NestedError>(())
    };
    let out = replace_nested(env, ctor, &n("T"), occs, &index, &levels, np, &mut charge)
        .expect("the rewrite succeeds");
    (out, charged)
}

/// The self-references to `container` (with `ncp` parameters, the
/// occurrence's `cargs`) in `site`, of a parent with `np` parameters, made
/// the auxiliary `T._C`, adding up what is charged.
pub(super) fn self_ref(
    site: &Term,
    container: &str,
    ncp: u32,
    cargs: &[Term],
    np: u32,
) -> (Term, u64) {
    let levels: Arc<[Level]> = Arc::from(Vec::new());
    let mut charged: u64 = 0;
    let mut charge = |nodes: u64| {
        charged = charged.saturating_add(nodes);
        Ok::<(), NestedError>(())
    };
    let out = replace_container_self_ref(
        site,
        &n(container),
        ncp,
        cargs,
        &n("T._C"),
        &levels,
        np,
        &mut charge,
    )
    .expect("the rewrite succeeds");
    (out, charged)
}

/// `(A : Type) → C (T A) → T A`.
fn one_site(env: &MinimalEnv) -> (Term, Occurrence) {
    let ctor = term(
        env,
        &pi(
            ty(),
            pi(
                app(c("C"), app(c("T"), RawExpr::BVar(0))),
                app(c("T"), RawExpr::BVar(1)),
            ),
        ),
        0,
    );
    let canon = term(env, &app(c("T"), RawExpr::BVar(0)), 1);
    (ctor, occ("C", vec![canon]))
}

/// `(A : Type) → C (T A) → T A`: the site's one argument mentions the
/// parameter. Lowering it builds 2 nodes (the application and `A`; `T` is
/// shared), and comparing the copy with the occurrence looks at 3 pairs: 5.
/// R174 charged the argument whole, 3 nodes, and the comparison nothing.
#[test]
fn test_replace_nested_matching_site_is_charged_what_it_builds_and_compares() {
    let env = env();
    let (ctor, o) = one_site(&env);
    let (out, charged) = rewrite(&env, &ctor, &[o], 1);
    assert_eq!(charged, 5);
    assert!(
        term_mentions(&out, &n("T._C")),
        "the site is rewritten to the auxiliary"
    );
}

/// `C T → T` in a parent with no parameters: the argument is closed, so
/// lowering returns it and builds nothing, and only the comparison with the
/// occurrence, 1 pair (an equal leaf), is charged. R174 charged nothing.
#[test]
fn test_replace_nested_closed_argument_is_charged_only_its_comparison() {
    let env = env();
    let ctor = term(&env, &pi(app(c("C"), c("T")), c("T")), 0);
    let (out, charged) = rewrite(&env, &ctor, &[occ("C", vec![term(&env, &c("T"), 0)])], 0);
    assert_eq!(charged, 1);
    assert!(
        term_mentions(&out, &n("T._C")),
        "the site is rewritten to the auxiliary"
    );
}

/// `(A : Type) → C (T A) (T A) (T A) (T A) → T A`, the occurrence `C (T A)`.
/// No occurrence is of `C` with four, three or two arguments, so of the
/// spine's applications only `C (T A)` is lowered (2 nodes) and compared (3
/// pairs): before R174 each was lowered in turn, ten argument copies, and
/// R174 charged the one it lowered whole, 3.
#[test]
fn test_replace_nested_site_no_occurrence_could_match_is_not_lowered() {
    let env = env();
    let spine = (0..4).fold(c("C"), |f, _| app(f, app(c("T"), RawExpr::BVar(0))));
    let ctor = term(&env, &pi(ty(), pi(spine, app(c("T"), RawExpr::BVar(1)))), 0);
    let canon = term(&env, &app(c("T"), RawExpr::BVar(0)), 1);
    let (out, charged) = rewrite(&env, &ctor, &[occ("C", vec![canon])], 1);
    assert_eq!(
        charged, 5,
        "only the application the occurrence matches is lowered and compared"
    );
    assert!(
        term_mentions(&out, &n("T._C")),
        "that application is rewritten to the auxiliary"
    );
}

/// `(A : Type) → G Prop Prop → C (T A) → T A`: the first field does not
/// mention `T`, so its rewrite is the field itself, the same node, where
/// R174 rebuilt every node of it; the second field's site is charged 5.
#[test]
fn test_replace_nested_field_without_the_parent_is_returned_uncopied() {
    let env = env();
    let ctor = term(
        &env,
        &pi(
            ty(),
            pi(
                app(app(c("G"), prop()), prop()),
                pi(
                    app(c("C"), app(c("T"), RawExpr::BVar(1))),
                    app(c("T"), RawExpr::BVar(2)),
                ),
            ),
        ),
        0,
    );
    let canon = term(&env, &app(c("T"), RawExpr::BVar(0)), 1);
    let (out, charged) = rewrite(&env, &ctor, &[occ("C", vec![canon])], 1);
    let field = |t: &Term| match t.kind() {
        TermKind::Pi(_, _, rest) => match rest.kind() {
            TermKind::Pi(_, d, _) => Some(d.clone()),
            _ => None,
        },
        _ => None,
    };
    let (before, after) = (
        field(&ctor).expect("a field"),
        field(&out).expect("a field"),
    );
    assert!(Arc::ptr_eq(&before.kind, &after.kind));
    assert_eq!(charged, 5);
    assert!(
        term_mentions(&out, &n("T._C")),
        "the second field is rewritten to the auxiliary"
    );
}

/// `C X → C X → T`, `X` = `Prop → T` with `Prop` a tree of height 4 (61
/// nodes; `X` 63), in a parent with no parameters, the occurrence the first
/// site's own argument (as phase 1 records it). The first comparison is the
/// same node, 1 pair; the second site's `X` is another allocation of an
/// equal term, so its comparison looks at all 63 pairs: 64. R174 charged
/// nothing for either.
#[test]
fn test_replace_nested_equal_copy_is_charged_every_pair_compared() {
    let env = env();
    let tree = (0..4).fold(prop(), |t, _| app(app(c("G"), t.clone()), t));
    let x = || pi(tree.clone(), c("T"));
    // Validate independently so scoped hash-consing cannot turn this
    // deliberately unequal-allocation fixture into two identical pointers.
    fn tree_copy(t: &Term) -> Term {
        let kind = match t.kind() {
            TermKind::App(a, b) => TermKind::App(tree_copy(a), tree_copy(b)),
            TermKind::Pi(i, a, b) => TermKind::Pi(*i, tree_copy(a), tree_copy(b)),
            other => other.clone(),
        };
        Term::mk(kind)
    }
    let left_x = tree_copy(&term(&env, &x(), 0));
    let right_x = tree_copy(&term(&env, &x(), 0));
    assert!(!Arc::ptr_eq(&left_x.kind, &right_x.kind));
    let c_term = term(&env, &c("C"), 0);
    let ctor = Term::pi(
        BinderInfo::Default,
        Term::app(c_term.clone(), left_x),
        Term::pi(
            BinderInfo::Default,
            Term::app(c_term, right_x),
            term(&env, &c("T"), 0),
        ),
    );
    let first_arg = match ctor.kind() {
        TermKind::Pi(_, dom, _) => match dom.kind() {
            TermKind::App(_, a) => Some(a.clone()),
            _ => None,
        },
        _ => None,
    }
    .expect("the first site's argument");
    assert_eq!(nodes(&first_arg), 63);
    let (out, charged) = rewrite(&env, &ctor, &[occ("C", vec![first_arg])], 0);
    assert_eq!(charged, 64);
    assert!(
        !term_mentions(&out, &n("C")),
        "both sites are the auxiliary"
    );
}

/// `(A : Type) → C (G A) (T A) → T A`, the occurrence `C (T A)`: the
/// spine's application of one argument, `C (G A)`, does not mention `T`, so
/// it is not lowered though an occurrence has its arity, and no occurrence
/// has two arguments: nothing is charged and nothing matches.
#[test]
fn test_replace_nested_application_without_the_parent_is_not_lowered() {
    let env = env();
    let g_a = app(c("G"), RawExpr::BVar(0));
    let site = app(app(c("C"), g_a), app(c("T"), RawExpr::BVar(0)));
    let ctor = term(&env, &pi(ty(), pi(site, app(c("T"), RawExpr::BVar(1)))), 0);
    let canon = term(&env, &app(c("T"), RawExpr::BVar(0)), 1);
    let (out, charged) = rewrite(&env, &ctor, &[occ("C", vec![canon])], 1);
    assert_eq!(
        charged, 0,
        "an application without the parent is not lowered"
    );
    assert!(out == ctor, "nothing matches");
}

/// `(A : Type) → (x : A) → C (T A) (G x) (T A) → T A`, the occurrences
/// `C (T A) (T A) (T A)`, `C (T A) (T A)` and `C (T A)`. At three arguments
/// `T A` is lowered (2 nodes) and `G x` fails at `x` (2 nodes looked at);
/// the application of two needs `G x` and is not lowered again; the
/// application of one is compared (3 pairs) and matches: 7. R174 charged
/// each application's arguments whole: 9, 6 and 3, 18.
#[test]
fn test_replace_nested_argument_that_fails_to_lower_is_lowered_once() {
    let env = env();
    let t_a = || app(c("T"), RawExpr::BVar(1));
    let site = app(
        app(app(c("C"), t_a()), app(c("G"), RawExpr::BVar(0))),
        t_a(),
    );
    let fields = pi(RawExpr::BVar(0), pi(site, app(c("T"), RawExpr::BVar(2))));
    let ctor = term(&env, &pi(ty(), fields), 0);
    let canon = || term(&env, &app(c("T"), RawExpr::BVar(0)), 1);
    let occs = [
        occ("C", vec![canon(), canon(), canon()]),
        occ("C", vec![canon(), canon()]),
        occ("C", vec![canon()]),
    ];
    let (out, charged) = rewrite(&env, &ctor, &occs, 1);
    assert_eq!(charged, 7);
    assert!(
        term_mentions(&out, &n("T._C")),
        "the application of one argument is the auxiliary"
    );
}

/// `(A : Type) → C (T A) → T A` with every key alike, and the occurrences
/// `C (T (G A))` (auxiliary `T._D`) and `C (T A)`, in that order. The site's
/// key names both; the first is compared and differs at its third pair
/// (`G A` against `A`: with hashes alike the walk reaches them), the second
/// is compared (3 pairs) and matches. A collision costs its comparison and
/// is never a refusal: 2 nodes lowered and 6 pairs, 8.
#[test]
fn test_replace_nested_colliding_key_is_compared_past_the_occurrence_that_differs() {
    let env = env();
    let (ctor, o) = one_site(&env);
    let t_g_a = term(&env, &app(c("T"), app(c("G"), RawExpr::BVar(0))), 1);
    let first = Occurrence {
        aux_name: n("T._D"),
        ..occ("C", vec![t_g_a])
    };
    let _collide = narrow_hashes(Some(1));
    let (out, charged) = rewrite(&env, &ctor, &[first, o], 1);
    assert_eq!(charged, 8);
    assert!(
        term_mentions(&out, &n("T._C")),
        "the second occurrence matches"
    );
    assert!(!term_mentions(&out, &n("T._D")), "the first does not");
}

/// `(A : Type) → C (T.{u} A) → T.{u} A`, a parent with a universe
/// parameter, and the occurrence `C (T.{u} A)`: the parent is found by its
/// name whatever its levels, and the site is the auxiliary, charged 5 as
/// in a parent without one. R174 charged 3.
#[test]
fn test_replace_nested_parent_with_a_universe_level_is_matched() {
    let env = parent_env(1);
    let t_u = |a: u32| {
        let t = RawExpr::Const(n("T"), vec![RawLevel::Param(0)]);
        app(t, RawExpr::BVar(a))
    };
    let raw = pi(ty(), pi(app(c("C"), t_u(0)), t_u(1)));
    let ctor = Term::validate(&env, &raw, 0, 1).expect("the constructor validates");
    let canon = Term::validate(&env, &t_u(0), 1, 1).expect("the argument validates");
    let (out, charged) = rewrite(&env, &ctor, &[occ("C", vec![canon])], 1);
    assert_eq!(charged, 5);
    assert!(term_mentions(&out, &n("T._C")), "the site is the auxiliary");
}

/// A charge that refuses stops the rewrite with its refusal.
#[test]
fn test_replace_nested_refused_charge_is_the_rewrites_refusal() {
    let env = env();
    let (ctor, o) = one_site(&env);
    let occs = [o];
    let index = OccIndex::of(&occs);
    let levels: Arc<[Level]> = Arc::from(Vec::new());
    let mut refuse = |_: u64| -> Result<(), NestedError> {
        Err(NestedError::NonUniformNesting {
            ind: n("T"),
            container: n("C"),
        })
    };
    let out = replace_nested(&env, &ctor, &n("T"), &occs, &index, &levels, 1, &mut refuse);
    assert!(
        matches!(out, Err(NestedError::NonUniformNesting { .. })),
        "{out:?}"
    );
}

/// Each node is charged before it is built: with room for `allowed` of the
/// 5 charges `(A : Type) → C (T A) → T A` makes, the rewrite refuses having
/// built at most `allowed` nodes (none at all for 0 or 1: the application is
/// charged first and built only once `A` is).
#[test]
fn test_replace_nested_refusal_comes_before_the_node_it_refuses() {
    let env = env();
    let (ctor, o) = one_site(&env);
    let occs = [o];
    let index = OccIndex::of(&occs);
    let levels: Arc<[Level]> = Arc::from(Vec::new());
    for allowed in 0u64..5 {
        let mut left = allowed;
        let mut charge = |nodes: u64| {
            if nodes > left {
                return Err(NestedError::NonUniformNesting {
                    ind: n("T"),
                    container: n("C"),
                });
            }
            left = left.saturating_sub(nodes);
            Ok(())
        };
        let before = NODES_BUILT.with(std::cell::Cell::get);
        let out = replace_nested(&env, &ctor, &n("T"), &occs, &index, &levels, 1, &mut charge);
        let built = NODES_BUILT
            .with(std::cell::Cell::get)
            .saturating_sub(before);
        assert!(out.is_err(), "{allowed} of 5 is refused");
        assert!(
            built <= allowed,
            "{built} nodes built for {allowed} charged"
        );
        if allowed < 2 {
            assert_eq!(built, 0, "nothing is built before its charge");
        }
    }
}

/// The auxiliary's self-reference rewrite charges what it builds and
/// compares: `C (T A)` against the occurrence `C (T A)`, 2 nodes built to
/// lower `T A` and 3 pairs compared: 5. R174 charged the argument whole, 3.
#[test]
fn test_replace_container_self_ref_charges_what_it_builds_and_compares() {
    let env = env();
    let site = term(&env, &app(c("C"), app(c("T"), RawExpr::BVar(0))), 1);
    let canon = term(&env, &app(c("T"), RawExpr::BVar(0)), 1);
    let (out, charged) = self_ref(&site, "C", 1, &[canon], 1);
    assert_eq!(charged, 5);
    assert!(
        term_mentions(&out, &n("T._C")),
        "the self-reference is the auxiliary"
    );
}

/// Lowering a closed term returns the term itself, not a copy.
#[test]
fn test_lower_params_closed_term_is_returned_uncopied() {
    let env = env();
    let closed = term(&env, &pi(ty(), app(c("C"), c("T"))), 0);
    let lowered = lower_params(&closed, 3, 2).expect("a closed term lowers");
    assert!(Arc::ptr_eq(&closed.kind, &lowered.kind));
}
