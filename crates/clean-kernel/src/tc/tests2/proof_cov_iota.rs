// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof coverage tests — iota reduction semantic preservation.
//!
//! Covers:
//! - `try_iota_reduction` contract: If Some(result) is returned, then e ≡ result
//! - Nat.rec and Bool.rec reduction with def_eq verification

use super::*;

// ===== iota_reduction semantic preservation tests =====
// try_iota_reduction (tc/reduction.rs:31) has a contract:
//   ENSURES: Semantic preservation: If Some(result) is returned, then e ≡ result
// Existing tests verify computation correctness but NOT that the result is
// definitionally equal to the input via is_def_eq.

/// Test iota reduction semantic preservation: Nat.rec zero ≡ case_zero.
/// Verifies the contract that `e ≡ result` by checking is_def_eq(e, result).
#[test]
fn test_iota_semantic_preservation_nat_rec_zero() {
    use crate::inductive::{Constructor, InductiveDecl, InductiveType};

    let mut env = Environment::new();

    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);

    env.add_inductive(InductiveDecl {
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
    })
    .expect("env setup: add Nat inductive");

    let tc = TypeChecker::new(&env);

    let rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let motive = Expr::lam(BinderInfo::Default, nat_ref.clone(), Expr::prop());
    let case_zero = Expr::type_();
    let case_succ = Expr::lam(
        BinderInfo::Default,
        nat_ref.clone(),
        Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(1)),
    );
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // Build: Nat.rec motive case_zero case_succ Nat.zero
    let app = Expr::app(
        Expr::app(
            Expr::app(Expr::app(rec.clone(), motive.clone()), case_zero.clone()),
            case_succ.clone(),
        ),
        zero,
    );

    let result = tc.whnf(&app);
    assert_eq!(result, case_zero, "Nat.rec zero should reduce to case_zero");

    // Semantic preservation: the original expression and the reduced result
    // should be definitionally equal.
    assert!(
        tc.is_def_eq(&app, &result),
        "Iota reduction semantic preservation: Nat.rec zero ≡ case_zero"
    );
}

/// Test iota reduction semantic preservation: Bool.rec true ≡ case_true.
#[test]
fn test_iota_semantic_preservation_bool_rec() {
    use crate::inductive::{Constructor, InductiveDecl, InductiveType};

    let mut env = Environment::new();

    let bool_name = Name::from_string("Bool");
    let bool_ref = Expr::const_(bool_name.clone(), vec![]);

    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: bool_name.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Bool.true"),
                    type_: bool_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Bool.false"),
                    type_: bool_ref.clone(),
                },
            ],
        }],
    })
    .expect("env setup: add Bool inductive");

    let tc = TypeChecker::new(&env);

    let rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
    let motive = Expr::lam(BinderInfo::Default, bool_ref.clone(), Expr::prop());
    let case_true = Expr::type_();
    let case_false = Expr::prop();
    let tt = Expr::const_(Name::from_string("Bool.true"), vec![]);

    let app = Expr::app(
        Expr::app(
            Expr::app(Expr::app(rec, motive), case_true.clone()),
            case_false,
        ),
        tt,
    );

    let result = tc.whnf(&app);
    assert_eq!(
        result, case_true,
        "Bool.rec true should reduce to case_true"
    );

    // Semantic preservation
    assert!(
        tc.is_def_eq(&app, &result),
        "Iota reduction semantic preservation: Bool.rec true ≡ case_true"
    );
}
