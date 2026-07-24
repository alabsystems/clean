// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for mutual inductive type handling (Even/Odd).
//!
//! Non-mutual field-type tests (Wrapped, HO, Stream) are in
//! `inductive_field_types.rs`.

use super::*;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};

/// Create the standard Even/Odd mutual inductive environment for tests.
fn make_even_odd_env() -> (Environment, Name, Name) {
    let mut env = Environment::new();
    let even = Name::from_string("Even");
    let odd = Name::from_string("Odd");
    let even_ref = Expr::const_(even.clone(), vec![]);
    let odd_ref = Expr::const_(odd.clone(), vec![]);

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![
            InductiveType {
                name: even.clone(),
                type_: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
                constructors: vec![
                    Constructor {
                        name: Name::from_string("Even.zero"),
                        type_: even_ref.clone(),
                    },
                    Constructor {
                        name: Name::from_string("Even.succ_odd"),
                        type_: Expr::pi(BinderInfo::Default, odd_ref.clone(), even_ref.clone()),
                    },
                ],
            },
            InductiveType {
                name: odd.clone(),
                type_: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
                constructors: vec![Constructor {
                    name: Name::from_string("Odd.succ_even"),
                    type_: Expr::pi(BinderInfo::Default, even_ref, odd_ref),
                }],
            },
        ],
    };
    env.add_inductive(decl).expect("should succeed");
    (env, even, odd)
}

#[test]
fn test_mutual_inductive_even_odd() {
    let (env, even, odd) = make_even_odd_env();

    // Both inductives should exist
    assert!(env.get_inductive(&even).is_some(), "Even registered");
    assert!(env.get_inductive(&odd).is_some(), "Odd registered");

    // Check all_names for mutual block
    let even_val = env.get_inductive(&even).expect("should succeed");
    assert_eq!(even_val.all_names.len(), 2);
    assert!(even_val.all_names.contains(&even));
    assert!(even_val.all_names.contains(&odd));

    let odd_val = env.get_inductive(&odd).expect("should succeed");
    assert_eq!(odd_val.all_names.len(), 2);

    // All eliminators should exist
    for suffix in &["rec", "casesOn", "recOn"] {
        for name in &["Even", "Odd"] {
            let full = Name::from_string(&format!("{name}.{suffix}"));
            assert!(env.get_recursor(&full).is_some(), "{full} should exist");
        }
    }

    // Verify recursor structure for mutual inductives (#3237).
    // num_motives = number of types in the mutual block = 2
    // num_minors = total constructors across all types = 3
    // rules.len() = constructors for THIS type only
    let even_rec = env
        .get_recursor(&Name::from_string("Even.rec"))
        .expect("should succeed");
    assert_eq!(even_rec.num_motives, 2, "Even.rec 2 motives");
    assert_eq!(even_rec.num_minors, 3, "Even.rec 3 total minors");
    assert_eq!(even_rec.rules.len(), 2, "Even.rec 2 rules");

    let odd_rec = env
        .get_recursor(&Name::from_string("Odd.rec"))
        .expect("should succeed");
    assert_eq!(odd_rec.num_motives, 2, "Odd.rec 2 motives");
    assert_eq!(odd_rec.num_minors, 3, "Odd.rec 3 total minors");
    assert_eq!(odd_rec.rules.len(), 1, "Odd.rec 1 rule");
}

#[test]
fn test_mutual_no_confusion_heals_as_complete_block_after_late_eq() {
    let (mut env, even, odd) = make_even_odd_env();
    env.init_punit()
        .expect("PUnit is required by noConfusionType");

    // The fixture intentionally declares the mutual block before Eq. Initial
    // generation therefore fails closed without installing declarations that
    // could participate in their own validation.
    for member in [&even, &odd] {
        for suffix in ["noConfusionType", "noConfusion"] {
            let name = Name::from_string(&format!("{member}.{suffix}"));
            assert!(
                env.get_const(&name).is_none(),
                "{name} must be absent before Eq"
            );
            assert_eq!(env.declaration_verification(&name), None);
        }
    }

    env.init_eq()
        .expect("late Eq should repair the complete Even/Odd block");
    for member in [&even, &odd] {
        for suffix in ["noConfusionType", "noConfusion"] {
            let name = Name::from_string(&format!("{member}.{suffix}"));
            assert_eq!(
                env.declaration_verification(&name),
                Some(crate::env::DeclarationVerification::FullKernelCheck),
                "{name} must be rooted only after the whole block succeeds"
            );
        }
    }
}

#[test]
fn test_mutual_inductive_recursors_have_correct_structure() {
    let (env, _even, _odd) = make_even_odd_env();

    // Even.rec should detect succ_odd's Odd field as recursive (mutual block).
    let even_rec = env
        .get_recursor(&Name::from_string("Even.rec"))
        .expect("should succeed");
    assert_eq!(even_rec.rules.len(), 2);

    let succ_odd_rule = &even_rec.rules[1];
    assert_eq!(succ_odd_rule.num_fields, 1);
    assert!(
        succ_odd_rule.recursive_fields[0],
        "succ_odd's Odd field should be recursive in mutual context"
    );

    // Odd.rec: succ_even's Even field should be recursive
    let odd_rec = env
        .get_recursor(&Name::from_string("Odd.rec"))
        .expect("should succeed");
    assert_eq!(odd_rec.rules.len(), 1);
    let succ_even_rule = &odd_rec.rules[0];
    assert_eq!(succ_even_rule.num_fields, 1);
    assert!(
        succ_even_rule.recursive_fields[0],
        "succ_even's Even field should be recursive in mutual context"
    );
}

#[test]
fn test_mutual_inductive_recursor_minor_premise_has_ih() {
    let (env, _even, _odd) = make_even_odd_env();

    // Even.rec type should include motives for both types and IH in minor premises.
    let even_rec = env
        .get_recursor(&Name::from_string("Even.rec"))
        .expect("should succeed");

    // zero has no fields
    assert_eq!(even_rec.rules[0].num_fields, 0);
    assert!(even_rec.rules[0].recursive_fields.is_empty());

    // succ_odd has 1 field (Odd) which should be marked recursive
    assert_eq!(even_rec.rules[1].num_fields, 1);
    assert!(
        even_rec.rules[1].recursive_fields[0],
        "succ_odd's Odd field recursive in mutual context"
    );

    // Odd.rec: succ_even's Even field marked recursive
    let odd_rec = env
        .get_recursor(&Name::from_string("Odd.rec"))
        .expect("should succeed");
    assert_eq!(odd_rec.rules[0].num_fields, 1);
    assert!(
        odd_rec.rules[0].recursive_fields[0],
        "succ_even's Even field recursive in mutual context"
    );

    // Verify num_motives = 2 for mutual inductives (one per type in block)
    assert_eq!(even_rec.num_motives, 2, "Even.rec has 2 motives");
    assert_eq!(odd_rec.num_motives, 2, "Odd.rec has 2 motives");
}

// ---- Iota reduction tests for mutual inductives ----

/// Helper: create Even/Odd env returning Expr references (for iota tests).
fn make_even_odd_env_refs() -> (Environment, Expr, Expr) {
    let mut env = Environment::new();
    let even = Name::from_string("Even");
    let odd = Name::from_string("Odd");
    let even_ref = Expr::const_(even.clone(), vec![]);
    let odd_ref = Expr::const_(odd.clone(), vec![]);

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![
            InductiveType {
                name: even,
                type_: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
                constructors: vec![
                    Constructor {
                        name: Name::from_string("Even.zero"),
                        type_: even_ref.clone(),
                    },
                    Constructor {
                        name: Name::from_string("Even.succ_odd"),
                        type_: Expr::pi(BinderInfo::Default, odd_ref.clone(), even_ref.clone()),
                    },
                ],
            },
            InductiveType {
                name: odd,
                type_: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
                constructors: vec![Constructor {
                    name: Name::from_string("Odd.succ_even"),
                    type_: Expr::pi(BinderInfo::Default, even_ref.clone(), odd_ref.clone()),
                }],
            },
        ],
    };
    env.add_inductive(decl)
        .expect("add Even/Odd mutual inductive");
    (env, even_ref, odd_ref)
}

/// Build a standard set of motives and minors for Even.rec / Odd.rec tests.
///
/// Returns (motive_even, motive_odd, minor_zero, minor_succ_odd, minor_succ_even, p, q, r)
/// where:
///   minor_zero       = p  (proof for Even.zero case)
///   minor_succ_odd   = lambda(o: Odd). lambda(ih: Prop). q
///   minor_succ_even  = lambda(e: Even). lambda(ih: Prop). r
fn make_motives_and_minors(even_ref: &Expr, odd_ref: &Expr) -> (Expr, Expr, Expr, Expr, Expr) {
    let motive_even = Expr::lam(BinderInfo::Default, even_ref.clone(), Expr::prop());
    let motive_odd = Expr::lam(BinderInfo::Default, odd_ref.clone(), Expr::prop());
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let r = Expr::const_(Name::from_string("R"), vec![]);

    let minor_succ_odd = Expr::lam(
        BinderInfo::Default,
        odd_ref.clone(),
        Expr::lam(BinderInfo::Default, Expr::prop(), q),
    );
    let minor_succ_even = Expr::lam(
        BinderInfo::Default,
        even_ref.clone(),
        Expr::lam(BinderInfo::Default, Expr::prop(), r),
    );

    (
        motive_even,
        motive_odd,
        minor_succ_odd,
        minor_succ_even,
        Expr::const_(Name::from_string("P"), vec![]),
    )
}

/// Iota reduction: Even.rec on Even.zero reduces to the zero minor (P).
///
/// Even.rec expects: motive_even motive_odd minor_zero minor_succ_odd minor_succ_even major
/// When major = Even.zero, iota fires the zero rule and returns minor_zero = P.
#[test]
fn test_mutual_iota_even_rec_zero() {
    let (env, even_ref, odd_ref) = make_even_odd_env_refs();
    let tc = TypeChecker::new(&env);

    let (motive_even, motive_odd, minor_succ_odd, minor_succ_even, p) =
        make_motives_and_minors(&even_ref, &odd_ref);

    let even_rec = Expr::const_(Name::from_string("Even.rec"), vec![Level::zero()]);
    let major = Expr::const_(Name::from_string("Even.zero"), vec![]);

    let mut app = even_rec;
    app = Expr::app(app, motive_even);
    app = Expr::app(app, motive_odd);
    app = Expr::app(app, p.clone());
    app = Expr::app(app, minor_succ_odd);
    app = Expr::app(app, minor_succ_even);
    app = Expr::app(app, major);

    let result = tc.whnf(&app);
    assert_eq!(
        result, p,
        "Even.rec on Even.zero should reduce to zero minor P"
    );
}

/// Iota reduction: Even.rec on Even.succ_odd(Odd.succ_even(Even.zero)) reduces
/// to the succ_odd minor applied to the field and IH.
///
/// The minor is lambda(o: Odd). lambda(ih: Prop). Q, so the result is Q.
#[test]
fn test_mutual_iota_even_rec_succ_odd() {
    let (env, even_ref, odd_ref) = make_even_odd_env_refs();
    let tc = TypeChecker::new(&env);

    let (motive_even, motive_odd, minor_succ_odd, minor_succ_even, p) =
        make_motives_and_minors(&even_ref, &odd_ref);
    let q = Expr::const_(Name::from_string("Q"), vec![]);

    let even_rec = Expr::const_(Name::from_string("Even.rec"), vec![Level::zero()]);

    // major: Even.succ_odd(Odd.succ_even(Even.zero))
    let major = Expr::app(
        Expr::const_(Name::from_string("Even.succ_odd"), vec![]),
        Expr::app(
            Expr::const_(Name::from_string("Odd.succ_even"), vec![]),
            Expr::const_(Name::from_string("Even.zero"), vec![]),
        ),
    );

    let mut app = even_rec;
    app = Expr::app(app, motive_even);
    app = Expr::app(app, motive_odd);
    app = Expr::app(app, p);
    app = Expr::app(app, minor_succ_odd);
    app = Expr::app(app, minor_succ_even);
    app = Expr::app(app, major);

    let result = tc.whnf(&app);
    assert_eq!(
        result, q,
        "Even.rec on Even.succ_odd should reduce to Q via succ_odd minor"
    );
}

/// Iota reduction: Odd.rec on Odd.succ_even(Even.zero) reduces to
/// the succ_even minor applied to the field and IH.
///
/// Odd.rec expects: motive_even motive_odd minor_zero minor_succ_odd minor_succ_even major
/// When major = Odd.succ_even(Even.zero), the succ_even minor fires.
/// minor_succ_even = lambda(e: Even). lambda(ih: Prop). R  =>  result = R.
#[test]
fn test_mutual_iota_odd_rec_succ_even() {
    let (env, even_ref, odd_ref) = make_even_odd_env_refs();
    let tc = TypeChecker::new(&env);

    let (motive_even, motive_odd, minor_succ_odd, minor_succ_even, p) =
        make_motives_and_minors(&even_ref, &odd_ref);
    let r = Expr::const_(Name::from_string("R"), vec![]);

    let odd_rec = Expr::const_(Name::from_string("Odd.rec"), vec![Level::zero()]);

    // major: Odd.succ_even(Even.zero)
    let major = Expr::app(
        Expr::const_(Name::from_string("Odd.succ_even"), vec![]),
        Expr::const_(Name::from_string("Even.zero"), vec![]),
    );

    let mut app = odd_rec;
    app = Expr::app(app, motive_even);
    app = Expr::app(app, motive_odd);
    app = Expr::app(app, p);
    app = Expr::app(app, minor_succ_odd);
    app = Expr::app(app, minor_succ_even);
    app = Expr::app(app, major);

    let result = tc.whnf(&app);
    assert_eq!(
        result, r,
        "Odd.rec on Odd.succ_even should reduce to R via succ_even minor"
    );
}

/// Iota reduction: Odd.rec on a deeper term Odd.succ_even(Even.succ_odd(Odd.succ_even(Even.zero)))
/// still reduces correctly to R via the succ_even minor.
#[test]
fn test_mutual_iota_odd_rec_deep_nesting() {
    let (env, even_ref, odd_ref) = make_even_odd_env_refs();
    let tc = TypeChecker::new(&env);

    let (motive_even, motive_odd, minor_succ_odd, minor_succ_even, p) =
        make_motives_and_minors(&even_ref, &odd_ref);
    let r = Expr::const_(Name::from_string("R"), vec![]);

    let odd_rec = Expr::const_(Name::from_string("Odd.rec"), vec![Level::zero()]);

    // Build: Odd.succ_even(Even.succ_odd(Odd.succ_even(Even.zero)))
    // Represents Odd 3 (or depth-3 nesting of mutual constructors)
    let even_zero = Expr::const_(Name::from_string("Even.zero"), vec![]);
    let odd_one = Expr::app(
        Expr::const_(Name::from_string("Odd.succ_even"), vec![]),
        even_zero,
    );
    let even_two = Expr::app(
        Expr::const_(Name::from_string("Even.succ_odd"), vec![]),
        odd_one,
    );
    let major = Expr::app(
        Expr::const_(Name::from_string("Odd.succ_even"), vec![]),
        even_two,
    );

    let mut app = odd_rec;
    app = Expr::app(app, motive_even);
    app = Expr::app(app, motive_odd);
    app = Expr::app(app, p);
    app = Expr::app(app, minor_succ_odd);
    app = Expr::app(app, minor_succ_even);
    app = Expr::app(app, major);

    let result = tc.whnf(&app);
    assert_eq!(
        result, r,
        "Odd.rec on deep Even/Odd nesting should still reduce to R"
    );
}

/// Iota reduction: Even.rec and Odd.rec on the same term produce different
/// results (cross-recursor independence).
///
/// Even.rec on Even.zero -> P, Odd.rec on Odd.succ_even(Even.zero) -> R.
/// Verifies that the two recursors are independent and each fires its own rules.
#[test]
fn test_mutual_iota_cross_recursor_independence() {
    let (env, even_ref, odd_ref) = make_even_odd_env_refs();
    let tc = TypeChecker::new(&env);

    let (motive_even, motive_odd, minor_succ_odd, minor_succ_even, p) =
        make_motives_and_minors(&even_ref, &odd_ref);
    let r = Expr::const_(Name::from_string("R"), vec![]);

    // Even.rec Even.zero -> P
    let even_rec = Expr::const_(Name::from_string("Even.rec"), vec![Level::zero()]);
    let even_major = Expr::const_(Name::from_string("Even.zero"), vec![]);

    let mut even_app = even_rec;
    even_app = Expr::app(even_app, motive_even.clone());
    even_app = Expr::app(even_app, motive_odd.clone());
    even_app = Expr::app(even_app, p.clone());
    even_app = Expr::app(even_app, minor_succ_odd.clone());
    even_app = Expr::app(even_app, minor_succ_even.clone());
    even_app = Expr::app(even_app, even_major);

    // Odd.rec Odd.succ_even(Even.zero) -> R
    let odd_rec = Expr::const_(Name::from_string("Odd.rec"), vec![Level::zero()]);
    let odd_major = Expr::app(
        Expr::const_(Name::from_string("Odd.succ_even"), vec![]),
        Expr::const_(Name::from_string("Even.zero"), vec![]),
    );

    let mut odd_app = odd_rec;
    odd_app = Expr::app(odd_app, motive_even);
    odd_app = Expr::app(odd_app, motive_odd);
    odd_app = Expr::app(odd_app, p.clone());
    odd_app = Expr::app(odd_app, minor_succ_odd);
    odd_app = Expr::app(odd_app, minor_succ_even);
    odd_app = Expr::app(odd_app, odd_major);

    let even_result = tc.whnf(&even_app);
    let odd_result = tc.whnf(&odd_app);

    assert_eq!(even_result, p, "Even.rec on Even.zero -> P");
    assert_eq!(odd_result, r, "Odd.rec on Odd.succ_even(Even.zero) -> R");
    assert_ne!(
        even_result, odd_result,
        "Different recursors produce different results"
    );
}
