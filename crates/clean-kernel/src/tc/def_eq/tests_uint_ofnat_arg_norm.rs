// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `<T>.ofNat <nat-expr>` normalises its ARGUMENT instead of unfolding its head.
//!
//! `UInt32.ofNat` is a definition, so whnf δ-unfolds it and descends into the
//! `ofBitVec (BitVec.ofFin 32 (Fin.ofNat …))` carrier tower carrying an
//! UNREDUCED `Nat` argument. Both sides of a `rfl` then grind that tower
//! structurally at a cost set by the VALUE. Measured 2026-09-17 before the
//! pass: `def u : UInt32 := 1000 * 1000` with `theorem : u = 1000000 := rfl`
//! peaked around fifteen gigabytes, and `200 * 200` against forty thousand
//! took 2.12 GB and 35 s; after it, both are 0.05 GB and under a second.
//!
//! These arms pin the MECHANISM rather than a timing, because the defect is a
//! slow accept and not a wrong answer: before the pass the same theorems still
//! type-checked, just enormously. Reverting the pass turns
//! `test_ofnat_argument_is_normalised` red immediately.

use crate::env::Environment;
use crate::expr::{Expr, ExprKind, Literal};
use crate::name::Name;
use crate::tc::TypeChecker;

fn uint32_of_nat(arg: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("UInt32.ofNat"), vec![]), arg)
}

fn nat_lit_of(e: &Expr) -> Option<u64> {
    match e.kind() {
        ExprKind::Lit(Literal::Nat(n)) => n.to_u64(),
        _ => None,
    }
}

#[test]
fn test_ofnat_argument_is_normalised() {
    let mut env = Environment::with_prelude();
    env.init_native_reducers();
    let tc = TypeChecker::new(&env);

    // `UInt32.ofNat (Nat.mul 100 100)` -- the shape a `def u : UInt32 := 100 * 100`
    // reaches def-eq as, once `UInt32.mul` has δ-unfolded.
    let nat_mul = Expr::apps(
        Expr::const_(Name::from_string("Nat.mul"), vec![]),
        vec![Expr::nat_lit(100), Expr::nat_lit(100)],
    );
    let expr = uint32_of_nat(nat_mul);

    let reduced = tc
        .reduce_native_for_test(&expr)
        .expect("UInt32.ofNat with a reducible Nat argument must normalise that argument");

    // The head is UNCHANGED -- this pass rebuilds the same application with a
    // reduced argument. It never returns a raw payload literal in a carrier
    // position, which is what got the analogous `BitVec.ofNat` widening
    // reverted (`test_bitvec_of_nat_parks_on_ofnat_wrapped_value`).
    let head = reduced.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => {
            assert_eq!(
                *name,
                Name::from_string("UInt32.ofNat"),
                "head must be preserved"
            );
        }
        other => panic!("expected the same UInt32.ofNat head, got {other:?}"),
    }
    let args = reduced.get_app_args();
    assert_eq!(args.len(), 1, "UInt32.ofNat is unary");
    assert_eq!(
        nat_lit_of(args[0]),
        Some(10_000),
        "the Nat argument must be reduced to its literal"
    );
}

#[test]
fn test_ofnat_declines_when_the_argument_is_already_a_literal() {
    // TERMINATION. The pass rebuilds the application, keeping the same head, so
    // it must make no claim on a term it cannot improve -- otherwise whnf would
    // re-enter it forever.
    let mut env = Environment::new();
    env.init_native_reducers();
    let tc = TypeChecker::new(&env);

    let expr = uint32_of_nat(Expr::nat_lit(10_000));
    assert!(
        tc.reduce_native_for_test(&expr).is_none(),
        "an already-literal argument is not progress and must decline"
    );
}

#[test]
fn test_ofnat_declines_when_the_argument_does_not_reach_a_literal() {
    // A non-value argument leaves the term to the ordinary δι path, exactly as
    // before the pass.
    let mut env = Environment::new();
    env.init_native_reducers();
    let tc = TypeChecker::new(&env);

    let opaque = Expr::const_(Name::from_string("someOpaqueNat"), vec![]);
    assert!(
        tc.reduce_native_for_test(&uint32_of_nat(opaque)).is_none(),
        "an argument that does not reduce to a literal must decline"
    );
}

#[test]
fn test_usize_of_nat_is_excluded() {
    // `USize`'s width is `System.Platform.numBits`, abstract in v4.30; every
    // USize reducer is intentionally unregistered and pinned as such
    // (`native_reducers_uint_tests.rs`). A width-abstract `ofNat` has no
    // literal value to normalise to, so it must not be swept in with the
    // concrete widths.
    let mut env = Environment::new();
    env.init_native_reducers();
    let tc = TypeChecker::new(&env);

    let nat_mul = Expr::apps(
        Expr::const_(Name::from_string("Nat.mul"), vec![]),
        vec![Expr::nat_lit(100), Expr::nat_lit(100)],
    );
    let expr = Expr::app(
        Expr::const_(Name::from_string("USize.ofNat"), vec![]),
        nat_mul,
    );
    assert!(
        tc.reduce_native_for_test(&expr).is_none(),
        "USize.ofNat must stay stuck"
    );
}

#[test]
fn test_every_concrete_width_is_covered() {
    // The defect is not UInt32's: measured the same on UInt16 and UInt64.
    let mut env = Environment::with_prelude();
    env.init_native_reducers();
    let tc = TypeChecker::new(&env);

    for ty in ["UInt8", "UInt16", "UInt32", "UInt64"] {
        let nat_add = Expr::apps(
            Expr::const_(Name::from_string("Nat.add"), vec![]),
            vec![Expr::nat_lit(3), Expr::nat_lit(4)],
        );
        let expr = Expr::app(
            Expr::const_(Name::from_string(&format!("{ty}.ofNat")), vec![]),
            nat_add,
        );
        let reduced = tc
            .reduce_native_for_test(&expr)
            .unwrap_or_else(|| panic!("{ty}.ofNat must normalise its argument"));
        assert_eq!(
            nat_lit_of(reduced.get_app_args()[0]),
            Some(7),
            "{ty}.ofNat argument must reduce"
        );
    }
}
