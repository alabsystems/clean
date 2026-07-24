// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Iota reduction tests — structure eta, mutual inductives, and large eliminators.
//!
//! Tests for structure eta expansion during iota reduction, mutual inductive
//! types (Even/Odd), and large eliminators with multiple indices.

use super::*;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};

/// Create Pair structure: struct Pair where fst : Nat; snd : Nat.
/// Returns (env, pair_name, nat_expr).
fn make_pair_env() -> (Environment, Name, Expr) {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let pair_name = Name::from_string("Pair");
    let pair_ref = Expr::const_(pair_name.clone(), vec![]);
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: pair_name.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Pair.mk"),
                type_: Expr::pi(
                    BinderInfo::Default,
                    nat.clone(),
                    Expr::pi(BinderInfo::Default, nat.clone(), pair_ref),
                ),
            }],
        }],
    };
    env.add_inductive(decl).expect("add Pair inductive");
    (env, pair_name, nat)
}

/// Build Nat.succ^n(Nat.zero) — a unary Nat numeral.
fn nat_numeral(n: u32) -> Expr {
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let mut result = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    for _ in 0..n {
        result = Expr::app(succ.clone(), result);
    }
    result
}

/// Structure eta: Pair.rec on constructor form should extract fields.
#[test]
fn test_iota_reduction_structure_eta_direct() {
    let (env, pair_name, nat) = make_pair_env();
    let tc = TypeChecker::new(&env);
    let pair_ref = Expr::const_(pair_name.clone(), vec![]);
    let three = nat_numeral(3);
    let seven = nat_numeral(7);
    let pair_val = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Pair.mk"), vec![]),
            three.clone(),
        ),
        seven.clone(),
    );
    let rec = Expr::const_(
        Name::from_string("Pair.rec"),
        vec![Level::succ(Level::zero())],
    );
    let motive = Expr::lam(BinderInfo::Default, pair_ref, nat.clone());
    let minor = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(BinderInfo::Default, nat.clone(), Expr::bvar(1)),
    );
    let app = Expr::app(Expr::app(Expr::app(rec, motive), minor), pair_val);
    let result = tc.whnf(&app);
    assert!(
        tc.is_def_eq(&result, &three),
        "Expected fst=3, got {:?}",
        result
    );
}

/// Structure eta: Pair.mk(p.0, p.1) should also reduce via eta expansion.
#[test]
fn test_iota_reduction_structure_eta_reconstructed() {
    let (env, pair_name, nat) = make_pair_env();
    let tc = TypeChecker::new(&env);
    let pair_ref = Expr::const_(pair_name.clone(), vec![]);
    let three = nat_numeral(3);
    let seven = nat_numeral(7);
    let pair_val = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Pair.mk"), vec![]),
            three.clone(),
        ),
        seven,
    );
    let reconstructed = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Pair.mk"), vec![]),
            Expr::proj(pair_name.clone(), 0, pair_val.clone()),
        ),
        Expr::proj(pair_name, 1, pair_val),
    );
    let rec = Expr::const_(
        Name::from_string("Pair.rec"),
        vec![Level::succ(Level::zero())],
    );
    let motive = Expr::lam(BinderInfo::Default, pair_ref, nat.clone());
    let minor = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(BinderInfo::Default, nat, Expr::bvar(1)),
    );
    let app = Expr::app(Expr::app(Expr::app(rec, motive), minor), reconstructed);
    let result = tc.whnf(&app);
    assert!(
        tc.is_def_eq(&result, &three),
        "Reconstructed: expected fst=3, got {:?}",
        result
    );
}

/// Create Even/Odd mutual inductive environment.
fn make_even_odd_env() -> (Environment, Expr, Expr) {
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

/// Mutual inductive iota: Even.rec on Even.zero reduces to zero_case.
///
/// With mutual recursors (#3237), Even.rec expects:
///   motive_even motive_odd minor_zero minor_succ_odd minor_succ_even major
/// (2 motives + 3 minors + 1 major = 6 args)
#[test]
fn test_iota_reduction_mutual_inductive_zero() {
    let (env, even_ref, odd_ref) = make_even_odd_env();
    let tc = TypeChecker::new(&env);

    let even_rec = Expr::const_(Name::from_string("Even.rec"), vec![Level::zero()]);
    let motive_even = Expr::lam(BinderInfo::Default, even_ref.clone(), Expr::prop());
    let motive_odd = Expr::lam(BinderInfo::Default, odd_ref.clone(), Expr::prop());
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let r = Expr::const_(Name::from_string("R"), vec![]);

    // minor_zero: P (a Prop value for motive_even Even.zero)
    // minor_succ_odd: λ(o:Odd). λ(ih:Prop). Q
    let minor_succ_odd = Expr::lam(
        BinderInfo::Default,
        odd_ref.clone(),
        Expr::lam(BinderInfo::Default, Expr::prop(), q),
    );
    // minor_succ_even: λ(e:Even). λ(ih:Prop). R
    let minor_succ_even = Expr::lam(
        BinderInfo::Default,
        even_ref,
        Expr::lam(BinderInfo::Default, Expr::prop(), r),
    );

    // Even.rec motive_even motive_odd P minor_succ_odd minor_succ_even Even.zero
    let mut app = even_rec;
    app = Expr::app(app, motive_even);
    app = Expr::app(app, motive_odd);
    app = Expr::app(app, p.clone());
    app = Expr::app(app, minor_succ_odd);
    app = Expr::app(app, minor_succ_even);
    app = Expr::app(app, Expr::const_(Name::from_string("Even.zero"), vec![]));

    assert_eq!(tc.whnf(&app), p, "Even.rec on Even.zero should reduce to P");
}

/// Mutual inductive iota: Even.rec on Even.succ_odd(x) reduces via
/// the succ_odd minor premise.
///
/// The iota rule for Even.succ_odd applies:
///   minor_succ_odd field IH
/// where IH = Odd.rec motives minors field (the recursive call on the Odd field).
/// We just verify the first step reduces (applies the minor to the field).
#[test]
fn test_iota_reduction_mutual_inductive_succ() {
    let (env, even_ref, odd_ref) = make_even_odd_env();
    let tc = TypeChecker::new(&env);

    let even_rec = Expr::const_(Name::from_string("Even.rec"), vec![Level::zero()]);
    let motive_even = Expr::lam(BinderInfo::Default, even_ref.clone(), Expr::prop());
    let motive_odd = Expr::lam(BinderInfo::Default, odd_ref.clone(), Expr::prop());
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let r = Expr::const_(Name::from_string("R"), vec![]);

    // minor_succ_odd: λ(o:Odd). λ(ih:Prop). Q
    let minor_succ_odd = Expr::lam(
        BinderInfo::Default,
        odd_ref.clone(),
        Expr::lam(BinderInfo::Default, Expr::prop(), q.clone()),
    );
    // minor_succ_even: λ(e:Even). λ(ih:Prop). R
    let minor_succ_even = Expr::lam(
        BinderInfo::Default,
        even_ref,
        Expr::lam(BinderInfo::Default, Expr::prop(), r),
    );

    // major: Even.succ_odd(Odd.succ_even(Even.zero))
    let even_two = Expr::app(
        Expr::const_(Name::from_string("Even.succ_odd"), vec![]),
        Expr::app(
            Expr::const_(Name::from_string("Odd.succ_even"), vec![]),
            Expr::const_(Name::from_string("Even.zero"), vec![]),
        ),
    );

    // Even.rec motive_even motive_odd P minor_succ_odd minor_succ_even even_two
    let mut app = even_rec;
    app = Expr::app(app, motive_even);
    app = Expr::app(app, motive_odd);
    app = Expr::app(app, p);
    app = Expr::app(app, minor_succ_odd);
    app = Expr::app(app, minor_succ_even);
    app = Expr::app(app, even_two);

    // After iota, succ_odd_minor is applied to the field and IH.
    // The minor is λ(o:Odd). λ(ih:Prop). Q, so result is Q.
    assert_eq!(
        tc.whnf(&app),
        q,
        "Even.rec on Even.succ_odd should reduce to Q"
    );
}

/// Create Triple : Nat → Nat → Nat → Type (3 indices, 0 params).
fn make_triple_env() -> (Environment, Name, Expr) {
    let mut env = Environment::new();
    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);
    let nat_decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Nat.zero"),
                    type_: nat_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Nat.succ"),
                    type_: Expr::arrow(nat_ref.clone(), nat_ref.clone()),
                },
            ],
        }],
    };
    env.add_inductive(nat_decl).expect("add Nat inductive");
    let triple_name = Name::from_string("Triple");
    let triple_type = Expr::pi(
        BinderInfo::Default,
        nat_ref.clone(),
        Expr::pi(
            BinderInfo::Default,
            nat_ref.clone(),
            Expr::pi(BinderInfo::Default, nat_ref.clone(), Expr::type_()),
        ),
    );
    // Triple.mk : (a b c : Nat) → Triple (succ a) b c
    // First index is succ(a), NOT a bare BVar, so fixedIndicesToParams won't
    // promote any indices (contiguous-prefix rule stops at position 0).
    let triple_mk_type = Expr::pi(
        BinderInfo::Default,
        nat_ref.clone(),
        Expr::pi(
            BinderInfo::Default,
            nat_ref.clone(),
            Expr::pi(
                BinderInfo::Default,
                nat_ref.clone(),
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(triple_name.clone(), vec![]),
                            Expr::app(
                                Expr::const_(Name::from_string("Nat.succ"), vec![]),
                                Expr::bvar(2),
                            ),
                        ),
                        Expr::bvar(1),
                    ),
                    Expr::bvar(0),
                ),
            ),
        ),
    );
    let triple_decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: triple_name.clone(),
            type_: triple_type,
            constructors: vec![Constructor {
                name: Name::from_string("Triple.mk"),
                type_: triple_mk_type,
            }],
        }],
    };
    env.add_inductive(triple_decl)
        .expect("add Triple inductive");
    (env, triple_name, nat_ref)
}

/// Large eliminator: Triple with 3 indices. Verifies args_before_major handles
/// multiple indices correctly.
#[test]
fn test_iota_reduction_large_eliminator() {
    let (env, triple_name, nat_ref) = make_triple_env();

    let rec_val = env
        .get_recursor(&Name::from_string("Triple.rec"))
        .expect("get Triple.rec");
    assert_eq!(rec_val.num_params, 0);
    assert_eq!(rec_val.num_indices, 3);

    let tc = TypeChecker::new(&env);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let one = nat_numeral(1);
    let two = nat_numeral(2);
    // Triple.mk 0 1 2 : Triple (succ 0) 1 2
    let major = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Triple.mk"), vec![]),
                zero.clone(),
            ),
            one.clone(),
        ),
        two.clone(),
    );
    let succ_zero = Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), zero);
    let rec = Expr::const_(Name::from_string("Triple.rec"), vec![Level::zero()]);
    let motive = Expr::lam(
        BinderInfo::Default,
        nat_ref.clone(),
        Expr::lam(
            BinderInfo::Default,
            nat_ref.clone(),
            Expr::lam(
                BinderInfo::Default,
                nat_ref.clone(),
                Expr::lam(
                    BinderInfo::Default,
                    Expr::app(
                        Expr::app(
                            Expr::app(Expr::const_(triple_name, vec![]), Expr::bvar(2)),
                            Expr::bvar(1),
                        ),
                        Expr::bvar(0),
                    ),
                    Expr::prop(),
                ),
            ),
        ),
    );
    let minor = Expr::lam(
        BinderInfo::Default,
        nat_ref.clone(),
        Expr::lam(
            BinderInfo::Default,
            nat_ref.clone(),
            Expr::lam(BinderInfo::Default, nat_ref, Expr::type_()),
        ),
    );
    // Triple.rec motive minor (succ 0) 1 2 major
    let app = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(Expr::app(rec, motive), minor), succ_zero),
                one,
            ),
            two,
        ),
        major,
    );
    let result = tc.whnf(&app);

    assert_ne!(app, result, "Triple.rec with 3 indices must reduce");
    assert_eq!(result, Expr::type_(), "Triple.rec should reduce to Type");
}
