// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Property-based laws for `def_eq` (design §8 obligation: reflexivity,
//! symmetry, and a transitivity corpus). Terms are drawn from a small validated
//! grammar over a fixed env; def_eq must be reflexive and symmetric on every
//! sample, and transitive on a reduction-closed corpus.

use clean_ck0::rawexpr::BinderInfo;
use clean_ck0::{
    is_def_eq, BigNat, Budget, Env, MinimalEnv, Name, RawExpr, RawLevel, RawLit, Term,
};
use proptest::prelude::*;

fn n(s: &str) -> Name {
    Name::from_dotted(s)
}

fn env() -> MinimalEnv {
    let formers = MinimalEnv::new().with_const_typed(
        n("Nat"),
        0,
        Term::validate_closed(
            &MinimalEnv::new(),
            &RawExpr::Sort(RawLevel::Succ(Box::new(RawLevel::Zero))),
        )
        .expect("sort"),
    );
    let nat_t = Term::validate_closed(&formers, &RawExpr::Const(n("Nat"), vec![])).expect("nat");
    let succ_t = Term::validate_closed(
        &formers,
        &RawExpr::Pi(
            BinderInfo::Default,
            Box::new(RawExpr::Const(n("Nat"), vec![])),
            Box::new(RawExpr::Const(n("Nat"), vec![])),
        ),
    )
    .expect("succ ty");
    let add_t = Term::validate_closed(
        &formers,
        &RawExpr::Pi(
            BinderInfo::Default,
            Box::new(RawExpr::Const(n("Nat"), vec![])),
            Box::new(RawExpr::Pi(
                BinderInfo::Default,
                Box::new(RawExpr::Const(n("Nat"), vec![])),
                Box::new(RawExpr::Const(n("Nat"), vec![])),
            )),
        ),
    )
    .expect("add ty");
    formers
        .with_const_typed(n("Nat.zero"), 0, nat_t)
        .with_const_typed(n("Nat.succ"), 0, succ_t)
        .with_const_typed(n("Nat.add"), 0, add_t)
}

/// A small grammar of closed Nat-typed raw terms.
fn raw_term() -> impl Strategy<Value = RawExpr> {
    let leaf = prop_oneof![
        (0u64..20).prop_map(|v| RawExpr::Lit(RawLit::Nat(BigNat::from_u64(v)))),
        Just(RawExpr::Const(n("Nat.zero"), vec![])),
    ];
    leaf.prop_recursive(4, 32, 2, |inner| {
        prop_oneof![
            inner.clone().prop_map(|e| RawExpr::App(
                Box::new(RawExpr::Const(n("Nat.succ"), vec![])),
                Box::new(e)
            )),
            (inner.clone(), inner).prop_map(|(a, b)| RawExpr::App(
                Box::new(RawExpr::App(
                    Box::new(RawExpr::Const(n("Nat.add"), vec![])),
                    Box::new(a)
                )),
                Box::new(b),
            )),
        ]
    })
}

fn deq(e: &dyn Env, a: &Term, b: &Term) -> bool {
    let mut bud = Budget::default_budget();
    is_def_eq(e, a, b, &mut bud).expect("within budget")
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn prop_reflexivity(raw in raw_term()) {
        let e = env();
        let t = Term::validate_closed(&e, &raw).expect("validates");
        prop_assert!(deq(&e, &t, &t.clone()));
    }

    #[test]
    fn prop_symmetry(ra in raw_term(), rb in raw_term()) {
        let e = env();
        let a = Term::validate_closed(&e, &ra).expect("a");
        let b = Term::validate_closed(&e, &rb).expect("b");
        prop_assert_eq!(deq(&e, &a, &b), deq(&e, &b, &a));
    }

    #[test]
    fn prop_transitivity_via_normal_form(ra in raw_term(), rb in raw_term(), rc in raw_term()) {
        // If a==b and b==c then a==c (the corpus is reduction-closed, so this is
        // a real transitivity check, not vacuous: many distinct expressions
        // share a normal form here).
        let e = env();
        let a = Term::validate_closed(&e, &ra).expect("a");
        let b = Term::validate_closed(&e, &rb).expect("b");
        let c = Term::validate_closed(&e, &rc).expect("c");
        if deq(&e, &a, &b) && deq(&e, &b, &c) {
            prop_assert!(deq(&e, &a, &c));
        }
    }
}
