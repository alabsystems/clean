// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The differential (R176): the one pass against the rules as they stood
//! (`reference.rs`), on generated containers and constructor types: foreign
//! containers nested in one another and in themselves, Π, λ, `let`,
//! projections, heads that are not constants, loose variables, and block
//! types in every polarity. The container oracle is compared slot by slot,
//! fresh and with one set of obligations kept across its yes answers; a
//! block's check refuses every constructor after its first refusal; and on a
//! constructor both admit, the one pass reads no more than the rules did.

use proptest::prelude::*;
use proptest::strategy::ValueTree;
use proptest::test_runner::TestRunner;

use super::super::variance::Obligations;
use super::super::Positivity;
use super::{
    app, check, check_before, cost, konst, lam, n, pi, reference, telescope, ty, with_container,
    Rules,
};
use crate::bignat::BigNat;
use crate::level::Level;
use crate::minimal_env::MinimalEnv;
use crate::name::Name;
use crate::term::{ElimRef, Lit, Term};

/// `Hom (X Y : Type)` with `Hom.c0 : (X Y : Type) → (X → Y) → Hom X Y`.
fn hom_env() -> MinimalEnv {
    let field = pi(Term::bvar(1), Term::bvar(1));
    let ret = app(app(konst("Hom"), Term::bvar(2)), Term::bvar(1));
    with_container(
        MinimalEnv::new(),
        "Hom",
        2,
        vec![telescope(vec![ty(), ty(), field], ret)],
    )
}

/// `Hom T T → T` requires both of `Hom`'s slots, and slot 0 is contravariant:
/// the check is refused while discharging, after both slots were marked seen
/// and taken off the pending list. Read as established, the same constructor
/// would be admitted the second time; every check after a refusal refuses,
/// `T → T` too.
#[test]
fn test_positivity_a_check_refused_in_discharge_refuses_every_later_constructor() {
    let env = hom_env();
    let block = [n("T")];
    let ctor = pi(app(app(konst("Hom"), konst("T")), konst("T")), konst("T"));
    assert_eq!(check_before(&env, &block, &ctor), Err(()));
    let mut positivity = Positivity::new(&env, &block);
    assert_eq!(positivity.check_ctor(&ctor), Err(()));
    assert_eq!(positivity.check_ctor(&ctor), Err(()));
    assert_eq!(check(&env, &block, &pi(konst("T"), konst("T"))), Ok(()));
    assert_eq!(positivity.check_ctor(&pi(konst("T"), konst("T"))), Err(()));
}

const NAMES: [&str; 9] = ["T", "U", "C1", "C2", "C3", "H", "W", "Nat", "X"];
const CONTAINERS: [&str; 5] = ["C1", "C2", "C3", "H", "W"];

/// The names each slot property asks about: the containers, a constant that
/// is no inductive, and a block type.
const ASKED: [&str; 7] = ["C1", "C2", "C3", "H", "W", "Nat", "T"];

fn elim() -> Term {
    let env = MinimalEnv::new().with_inductive(n("Eq"), 0, false);
    Term::elim(ElimRef::mk(&env, n("Eq"), Level::zero(), vec![]).expect("Eq's eliminator"))
}

fn arb_const() -> impl Strategy<Value = Term> {
    prop::sample::select(NAMES.to_vec()).prop_map(konst)
}

/// Terms over the block types `T`, `U`, the containers, two other constants,
/// variables `0..5` (bound or loose) and every node shape, applications headed
/// by constants, variables and any term.
fn arb_term() -> impl Strategy<Value = Term> {
    let leaf = prop_oneof![
        3 => (0u32..5).prop_map(Term::bvar),
        4 => arb_const(),
        1 => Just(ty()),
        1 => Just(Term::lit(Lit::Nat(BigNat::from_u64(0)))),
        1 => Just(elim()),
    ];
    leaf.prop_recursive(6, 48, 4, |inner| {
        let head = prop_oneof![
            3 => arb_const(),
            1 => (0u32..5).prop_map(Term::bvar),
            1 => inner.clone(),
        ];
        prop_oneof![
            4 => (head, prop::collection::vec(inner.clone(), 1..4))
                .prop_map(|(h, args)| Term::apply(h, &args)),
            3 => (inner.clone(), inner.clone()).prop_map(|(d, b)| pi(d, b)),
            1 => (inner.clone(), inner.clone()).prop_map(|(d, b)| lam(d, b)),
            1 => (inner.clone(), inner.clone(), inner.clone())
                .prop_map(|(t, v, b)| Term::let_(t, v, b)),
            1 => inner.prop_map(|e| Term::proj(n("S"), 0, e)),
        ]
    })
}

/// A telescope of up to five domains over a return type.
fn arb_telescope() -> impl Strategy<Value = Term> {
    (prop::collection::vec(arb_term(), 0..6), arb_term())
        .prop_map(|(doms, ret)| telescope(doms, ret))
}

/// Each container known (with 1 to 3 parameters and up to two constructors,
/// which may use any container, cycles included) or not an inductive at all.
fn arb_env() -> impl Strategy<Value = MinimalEnv> {
    let one = prop_oneof![
        1 => Just(None::<(u32, Vec<Term>)>),
        6 => (1u32..4, prop::collection::vec(arb_telescope(), 0..3)).prop_map(Some),
    ];
    prop::collection::vec(one, CONTAINERS.len()).prop_map(|known| {
        CONTAINERS
            .iter()
            .zip(known)
            .fold(MinimalEnv::new(), |env, (name, c)| match c {
                Some((np, ctors)) => with_container(env, name, np, ctors),
                None => env,
            })
    })
}

fn arb_block() -> impl Strategy<Value = Vec<Name>> {
    prop::bool::ANY.prop_map(|two| {
        if two {
            vec![n("T"), n("U")]
        } else {
            vec![n("T")]
        }
    })
}

/// Whether slot `slot` of `name` is strictly positive, asked of `obligations`.
fn slot_positive(obligations: &mut Obligations<'_>, name: &str, slot: usize) -> bool {
    obligations.require(&n(name), slot);
    obligations.discharge().is_ok()
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(2048))]

    /// One pass decides every constructor type as the rules did. On one both
    /// admit, both read all of it and of each container slot it needs, and
    /// the pass reads no more nodes and constructor lists than the rules did:
    /// a node once (a head that is not a constant twice, as the rules read
    /// it) and a slot's constructors once, where the rules read a leaf or an
    /// argument again for each question and scanned a slot again at each use.
    #[test]
    fn test_positivity_one_pass_decides_as_the_rules_did_reading_no_more(
        env in arb_env(),
        block in arb_block(),
        ctor in arb_telescope(),
    ) {
        let now = cost(&env, &block, &ctor, Rules::Now);
        let before = cost(&env, &block, &ctor, Rules::Before);
        prop_assert_eq!(now.verdict, before.verdict);
        if now.verdict.is_ok() {
            prop_assert!(now.reads <= before.reads, "{:?} against {:?}", now, before);
            prop_assert!(now.lists <= before.lists, "{:?} against {:?}", now, before);
        }
    }

    /// Over a block's constructors, one check refuses the first constructor
    /// the rules refused, and every constructor after that.
    #[test]
    fn test_positivity_one_check_per_block_refuses_the_constructor_the_rules_refused(
        env in arb_env(),
        block in arb_block(),
        ctors in prop::collection::vec(arb_telescope(), 1..5),
    ) {
        let mut positivity = Positivity::new(&env, &block);
        let got = ctors.iter().position(|c| positivity.check_ctor(c).is_err());
        let want = ctors
            .iter()
            .position(|c| check_before(&env, &block, c).is_err());
        prop_assert_eq!(got, want);
        if got.is_some() {
            for c in &ctors {
                prop_assert_eq!(positivity.check_ctor(c), Err(()));
            }
        }
    }

    /// Each slot decides as the oracle did, asked of a fresh check and of one
    /// kept across every question it answered yes to (a refusal replaces it).
    #[test]
    fn test_positivity_each_container_slot_decides_as_the_oracle_did(env in arb_env()) {
        let mut kept = Obligations::new(&env);
        for name in ASKED {
            for slot in 0..4usize {
                let want = reference::container_param_strictly_positive(&env, &n(name), slot, &[]);
                let fresh = slot_positive(&mut Obligations::new(&env), name, slot);
                prop_assert_eq!(fresh, want, "{} slot {}, fresh", name, slot);
                let shared = slot_positive(&mut kept, name, slot);
                prop_assert_eq!(shared, want, "{} slot {}, kept", name, slot);
                if !shared {
                    kept = Obligations::new(&env);
                }
            }
        }
    }
}

/// The generators draw each verdict, and each oracle answer, at least 1 time
/// in 20 (a model of them, branching as proptest 1.11's `prop_recursive`
/// does, drew about two thirds admitted and a quarter of the slots positive),
/// so the properties above cannot pass by never meeting one.
#[test]
fn test_positivity_generators_draw_every_verdict() {
    let mut runner = TestRunner::deterministic();
    let cases = (arb_env(), arb_block(), arb_telescope());
    let [mut admitted, mut refused, mut positive, mut negative] = [0u64; 4];
    for _ in 0..512 {
        let (env, block, ctor) = cases
            .new_tree(&mut runner)
            .expect("a generated case")
            .current();
        let count = if check_before(&env, &block, &ctor).is_ok() {
            &mut admitted
        } else {
            &mut refused
        };
        *count = count.saturating_add(1);
        for name in ASKED {
            for slot in 0..4usize {
                let count =
                    if reference::container_param_strictly_positive(&env, &n(name), slot, &[]) {
                        &mut positive
                    } else {
                        &mut negative
                    };
                *count = count.saturating_add(1);
            }
        }
    }
    let ctors = admitted.saturating_add(refused);
    let slots = positive.saturating_add(negative);
    for (count, total) in [
        (admitted, ctors),
        (refused, ctors),
        (positive, slots),
        (negative, slots),
    ] {
        assert!(
            count.saturating_mul(20) >= total,
            "admitted {admitted}, refused {refused}, positive {positive}, negative {negative}"
        );
    }
}
