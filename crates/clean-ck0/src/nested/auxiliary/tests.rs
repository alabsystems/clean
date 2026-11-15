// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! An auxiliary's container parameters are substituted in one pass, which
//! builds only its result, and decides as substituting one at a time did
//! (R176).

use proptest::prelude::*;

use super::*;
use crate::minimal_env::MinimalEnv;
use crate::name::Name;
use crate::rawexpr::{RawExpr, RawLevel};
use crate::term::NODES_BUILT;

/// The substitution as it was before R176, one parameter at a time.
fn one_at_a_time(ty: &Term, args: &[Term]) -> Term {
    let mut t = ty.clone();
    for arg in args {
        if let TermKind::Pi(_, _, codom) = t.kind() {
            t = codom.instantiate(arg);
        } else {
            break;
        }
    }
    t
}

/// Nodes of `t` as a tree, a shared subterm counted at each occurrence.
fn tree_size(t: &Term) -> u64 {
    let below = match t.kind() {
        TermKind::App(a, b) | TermKind::Lam(_, a, b) | TermKind::Pi(_, a, b) => {
            tree_size(a).saturating_add(tree_size(b))
        }
        TermKind::Let(a, b, c) => tree_size(a)
            .saturating_add(tree_size(b))
            .saturating_add(tree_size(c)),
        TermKind::Proj(_, _, a) => tree_size(a),
        _ => 0,
    };
    below.saturating_add(1)
}

fn built_by<T>(f: impl FnOnce() -> T) -> (T, u64) {
    let before = NODES_BUILT.with(std::cell::Cell::get);
    let out = f();
    (
        out,
        NODES_BUILT
            .with(std::cell::Cell::get)
            .saturating_sub(before),
    )
}

fn ty() -> RawExpr {
    RawExpr::Sort(RawLevel::Succ(Box::new(RawLevel::Zero)))
}

fn pi(d: RawExpr, b: RawExpr) -> RawExpr {
    RawExpr::Pi(BinderInfo::Default, Box::new(d), Box::new(b))
}

fn app(f: RawExpr, a: RawExpr) -> RawExpr {
    RawExpr::App(Box::new(f), Box::new(a))
}

/// An environment that knows the constant `G`; validation checks scope, not
/// types.
fn g_env() -> MinimalEnv {
    MinimalEnv::new().with_const(Name::from_dotted("G"), 0)
}

/// A `G` tree of `height` whose leaves are `BVar(0)`, the parent's parameter.
fn x_tree(height: u32) -> RawExpr {
    match height.checked_sub(1) {
        None => RawExpr::BVar(0),
        Some(h) => {
            let g = RawExpr::Const(Name::from_dotted("G"), vec![]);
            app(app(g, x_tree(h)), x_tree(h))
        }
    }
}

/// `(α_1 … α_n : Type) → α_1 → … → α_n → G α_1 α_n`, over one outer
/// variable, the parent's parameter.
fn telescope(n: u32) -> Term {
    let g = RawExpr::Const(Name::from_dotted("G"), vec![]);
    // Under the `n` parameters and `n` fields, `α_1` is `BVar(2n - 1)` and
    // `α_n` is `BVar(n)`.
    let first = n.saturating_mul(2).saturating_sub(1);
    let mut body = app(app(g, RawExpr::BVar(first)), RawExpr::BVar(n));
    // The field `α_{j+1}` sits under the `n` parameters and `j` fields, so it
    // is `BVar(n - 1)` for every `j`.
    for _ in 0..n {
        body = pi(RawExpr::BVar(n.saturating_sub(1)), body);
    }
    for _ in 0..n {
        body = pi(ty(), body);
    }
    Term::validate(&g_env(), &body, 1, 0).expect("the telescope validates")
}

/// 60 parameters, each given a 29-node tree over the parent's parameter. One
/// at a time, each substitution rebuilds the copies of every earlier one,
/// since they hold a loose variable; in one pass each node is built once.
#[test]
fn test_substitute_params_builds_only_its_result() {
    let n = 60;
    let ty = telescope(n);
    let x = Term::validate(&g_env(), &x_tree(3), 1, 0).expect("X validates");
    let args = vec![x; 60];
    let (once, built) = built_by(|| substitute_params(&ty, &args).expect("60 binders take 60"));
    assert!(
        built <= tree_size(&once),
        "built {built} for a result of {}",
        tree_size(&once)
    );
    let (seq, seq_built) = built_by(|| one_at_a_time(&ty, &args));
    assert_eq!(once, seq);
    assert!(
        seq_built > tree_size(&seq).saturating_mul(10),
        "the old loop built {seq_built}"
    );
}

/// Fewer leading Π binders than arguments is refused, as Lean's
/// `instantiate_pi_params` refuses it; as many is not.
#[test]
fn test_substitute_params_more_arguments_than_binders_is_refused() {
    let ty = telescope(2);
    let x = Term::validate(&g_env(), &x_tree(1), 1, 0).expect("X validates");
    assert_eq!(substitute_params(&ty, &vec![x.clone(); 5]), None);
    assert_eq!(
        substitute_params(&ty, &vec![x.clone(); 4]),
        Some(one_at_a_time(&ty, &vec![x; 4]))
    );
}

/// More arguments than the type's leading Π binders, one of them a Π: one
/// at a time went on into the Π that argument brought in and took the
/// fourth argument there; one pass refuses. A random case of
/// `prop_substitute_params_is_one_at_a_time` found this shape on R176's
/// first version, which stopped at the type's own first non-Π instead.
#[test]
fn test_substitute_params_past_the_binders_refuses_where_one_at_a_time_entered_an_argument() {
    let env = g_env();
    let at = |raw: &RawExpr| Term::validate(&env, raw, 3, 0).expect("validates");
    // `Π (x : Type) (y : x) (z : y), y`, then `[v0, Π (w : v0), w, v0, v0]`.
    let ty = at(&pi(
        ty(),
        pi(RawExpr::BVar(0), pi(RawExpr::BVar(0), RawExpr::BVar(1))),
    ));
    let args = [
        at(&RawExpr::BVar(0)),
        at(&pi(RawExpr::BVar(0), RawExpr::BVar(0))),
        at(&RawExpr::BVar(0)),
        at(&RawExpr::BVar(0)),
    ];
    assert_eq!(substitute_params(&ty, &args), None);
    assert_eq!(one_at_a_time(&ty, &args), at(&RawExpr::BVar(0)));
}

/// `C` registered by hand with one parameter and the type `container_ty`
/// (`Type` has no Π binder for the parameter, `Type → Type` has one), and a
/// constructor `C.c0 : (α : Type) → α → C α`.
fn container_env(container_ty: &RawExpr) -> MinimalEnv {
    let c = || RawExpr::Const(Name::from_dotted("C"), vec![]);
    let own = MinimalEnv::new().with_const(Name::from_dotted("C"), 0);
    let ctor = pi(ty(), pi(RawExpr::BVar(0), app(c(), RawExpr::BVar(1))));
    MinimalEnv::new().with_container_inductive(
        Name::from_dotted("C"),
        0,
        1,
        Term::validate_closed(&own, container_ty).expect("the container type"),
        false,
        vec![(
            Name::from_dotted("C.c0"),
            Term::validate_closed(&own, &ctor).expect("the container constructor"),
        )],
    )
}

/// `T : Type` with `T.c0 : C T → T`, nested in `container_env`'s `C`.
fn nested_in_c(env: &mut MinimalEnv) -> Result<(), NestedError> {
    let own = env.clone().with_const(Name::from_dotted("T"), 0);
    let t = || RawExpr::Const(Name::from_dotted("T"), vec![]);
    let c_t = app(RawExpr::Const(Name::from_dotted("C"), vec![]), t());
    let valid = |raw: &RawExpr| Term::validate_closed(&own, raw).expect("the decl validates");
    crate::nested::add_inductive_nested(
        env,
        InductiveDecl {
            name: Name::from_dotted("T"),
            num_level_params: 0,
            num_params: 0,
            type_: valid(&ty()),
            constructors: vec![Constructor {
                name: Name::from_dotted("T.c0"),
                type_: valid(&pi(c_t, t())),
            }],
        },
    )
}

/// Through admission: a container whose type has fewer leading Π binders
/// than its parameters is refused when a block nests in it; the same
/// container with the binder admits the block.
#[test]
fn test_nested_in_a_container_with_too_few_binders_is_refused() {
    let mut bad = container_env(&ty());
    match nested_in_c(&mut bad) {
        Err(NestedError::Aux {
            source: AdmitError::Derivation { detail, .. },
            ..
        }) => assert!(
            detail.contains(
                "has fewer leading Pi binders than the parameter arguments container 'C' is \
                 given (1)"
            ),
            "{detail}"
        ),
        other => panic!("expected the too-few-binders refusal, got {other:?}"),
    }
    let mut good = container_env(&pi(ty(), ty()));
    nested_in_c(&mut good).expect("the well-formed container admits the block");
}

/// Terms over three outer variables (`BVar` below 3 everywhere, so every
/// index is in scope), with binders of each kind.
fn arb_raw() -> impl Strategy<Value = RawExpr> {
    let leaf = prop_oneof![
        (0u32..3).prop_map(RawExpr::BVar),
        Just(ty()),
        Just(RawExpr::Const(Name::from_dotted("G"), vec![])),
    ];
    leaf.prop_recursive(5, 48, 3, |inner| {
        prop_oneof![
            (inner.clone(), inner.clone()).prop_map(|(f, a)| app(f, a)),
            (inner.clone(), inner.clone()).prop_map(|(d, b)| RawExpr::Lam(
                BinderInfo::Default,
                Box::new(d),
                Box::new(b)
            )),
            (inner.clone(), inner.clone()).prop_map(|(d, b)| pi(d, b)),
            (inner.clone(), inner.clone(), inner).prop_map(|(t, v, b)| RawExpr::Let(
                Box::new(t),
                Box::new(v),
                Box::new(b)
            )),
        ]
    })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    /// One pass decides as one at a time did, on random telescopes and
    /// arguments with loose variables, whenever the type has a leading Π
    /// binder for each argument, and refuses exactly when it has fewer.
    #[test]
    fn prop_substitute_params_is_one_at_a_time(
        pis in 0u32..5,
        body in arb_raw(),
        raw_args in proptest::collection::vec(arb_raw(), 0..6),
    ) {
        let mut raw_ty = body;
        for _ in 0..pis {
            raw_ty = pi(ty(), raw_ty);
        }
        let mut binders = 0usize;
        let mut at = &raw_ty;
        while let RawExpr::Pi(_, _, b) = at {
            binders = binders.saturating_add(1);
            at = &**b;
        }
        let env = g_env();
        let ty = Term::validate(&env, &raw_ty, 3, 0).expect("the type validates");
        let args: Vec<Term> = raw_args
            .iter()
            .map(|a| Term::validate(&env, a, 3, 0).expect("the argument validates"))
            .collect();
        match substitute_params(&ty, &args) {
            Some(once) => {
                prop_assert!(args.len() <= binders);
                prop_assert_eq!(once, one_at_a_time(&ty, &args));
            }
            None => prop_assert!(args.len() > binders),
        }
    }
}
