// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level signature checks for the Real downcast axioms used by the
//! LRA additive reconstruction path (#302).
//!
//! Lean 4 core does not define a `Real` type with these exact theorem names.
//! The parity claim for these axioms is semantic:
//! - `Real.ofNat_eq_ofInt` mirrors cast-coherence (`Int.ofNat_eq_natCast` +
//!   `Ring.intCast_natCast`)
//! - `Real.ofInt_le_to_Int` mirrors `OrderedRing.le_of_intCast_le_intCast`
//! - `Real.ofInt_lt_to_Int` mirrors `OrderedRing.lt_of_intCast_lt_intCast`

use clean_kernel::{Environment, Expr, ExprKind, Level, Name, TypeChecker};

fn pi_domain_at(expr: &Expr, depth: usize) -> Option<&Expr> {
    let mut current = expr;
    for _ in 0..depth {
        match current.kind() {
            ExprKind::Pi(_, _, body) => current = body,
            _ => return None,
        }
    }
    match current.kind() {
        ExprKind::Pi(_, domain, _) => Some(domain),
        _ => None,
    }
}

fn pi_body_after(expr: &Expr, depth: usize) -> Option<&Expr> {
    let mut current = expr;
    for _ in 0..depth {
        match current.kind() {
            ExprKind::Pi(_, _, body) => current = body,
            _ => return None,
        }
    }
    Some(current)
}

fn mk_eq_real(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                Expr::const_(Name::from_string("Real"), vec![]),
            ),
            lhs,
        ),
        rhs,
    )
}

fn mk_real_ofnat(n: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Real.ofNat"), vec![]), n)
}

fn mk_real_ofint(i: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Real.ofInt"), vec![]), i)
}

fn mk_int_ofnat(n: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Int.ofNat"), vec![]), n)
}

fn mk_real_cmp(cmp_name: &str, inst_name: &str, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string(cmp_name), vec![Level::zero()]),
                    Expr::const_(Name::from_string("Real"), vec![]),
                ),
                Expr::const_(Name::from_string(inst_name), vec![]),
            ),
            lhs,
        ),
        rhs,
    )
}

fn mk_int_cmp(cmp_name: &str, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string(cmp_name), vec![]), lhs),
        rhs,
    )
}

#[test]
fn verify_real_ofnat_eq_ofint_signature() {
    let mut env = Environment::new();
    env.init_real_linear_order().unwrap();
    let tc = TypeChecker::new(&env);

    let axiom_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("Real.ofNat_eq_ofInt"),
            vec![],
        ))
        .expect("Real.ofNat_eq_ofInt should be declared");
    let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
    assert_eq!(
        pi_domain_at(&axiom_type, 0),
        Some(&nat_const),
        "Real.ofNat_eq_ofInt binder 0 should be Nat"
    );

    let expected = mk_eq_real(
        mk_real_ofnat(Expr::bvar(0)),
        mk_real_ofint(mk_int_ofnat(Expr::bvar(0))),
    );
    let body = pi_body_after(&axiom_type, 1).expect("missing Real.ofNat_eq_ofInt body");
    assert!(
        tc.is_def_eq(body, &expected),
        "Real.ofNat_eq_ofInt should state Real.ofNat n = Real.ofInt (Int.ofNat n)"
    );
}

#[test]
fn verify_real_ofint_le_to_int_signature() {
    let mut env = Environment::new();
    env.init_real_linear_order().unwrap();
    let tc = TypeChecker::new(&env);

    let axiom_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("Real.ofInt_le_to_Int"),
            vec![],
        ))
        .expect("Real.ofInt_le_to_Int should be declared");
    let int_const = Expr::const_(Name::from_string("Int"), vec![]);
    assert_eq!(
        pi_domain_at(&axiom_type, 0),
        Some(&int_const),
        "Real.ofInt_le_to_Int binder 0 should be Int"
    );
    assert_eq!(
        pi_domain_at(&axiom_type, 1),
        Some(&int_const),
        "Real.ofInt_le_to_Int binder 1 should be Int"
    );

    let expected_hyp = mk_real_cmp(
        "LE.le",
        "instLEReal",
        mk_real_ofint(Expr::bvar(1)),
        mk_real_ofint(Expr::bvar(0)),
    );
    assert!(
        tc.is_def_eq(
            pi_domain_at(&axiom_type, 2).expect("missing downcast hypothesis binder"),
            &expected_hyp,
        ),
        "Real.ofInt_le_to_Int hypothesis should be a Real LE.le proof over Real.ofInt endpoints"
    );

    let expected_body = mk_int_cmp("Int.le", Expr::bvar(2), Expr::bvar(1));
    let body = pi_body_after(&axiom_type, 3).expect("missing Real.ofInt_le_to_Int body");
    assert!(
        tc.is_def_eq(body, &expected_body),
        "Real.ofInt_le_to_Int should conclude Int.le a b"
    );
}

#[test]
fn verify_real_ofint_lt_to_int_signature() {
    let mut env = Environment::new();
    env.init_real_linear_order().unwrap();
    let tc = TypeChecker::new(&env);

    let axiom_type = tc
        .infer_type(&Expr::const_(
            Name::from_string("Real.ofInt_lt_to_Int"),
            vec![],
        ))
        .expect("Real.ofInt_lt_to_Int should be declared");
    let int_const = Expr::const_(Name::from_string("Int"), vec![]);
    assert_eq!(
        pi_domain_at(&axiom_type, 0),
        Some(&int_const),
        "Real.ofInt_lt_to_Int binder 0 should be Int"
    );
    assert_eq!(
        pi_domain_at(&axiom_type, 1),
        Some(&int_const),
        "Real.ofInt_lt_to_Int binder 1 should be Int"
    );

    let expected_hyp = mk_real_cmp(
        "LT.lt",
        "instLTReal",
        mk_real_ofint(Expr::bvar(1)),
        mk_real_ofint(Expr::bvar(0)),
    );
    assert!(
        tc.is_def_eq(
            pi_domain_at(&axiom_type, 2).expect("missing downcast hypothesis binder"),
            &expected_hyp,
        ),
        "Real.ofInt_lt_to_Int hypothesis should be a Real LT.lt proof over Real.ofInt endpoints"
    );

    let expected_body = mk_int_cmp("Int.lt", Expr::bvar(2), Expr::bvar(1));
    let body = pi_body_after(&axiom_type, 3).expect("missing Real.ofInt_lt_to_Int body");
    assert!(
        tc.is_def_eq(body, &expected_body),
        "Real.ofInt_lt_to_Int should conclude Int.lt a b"
    );
}
