// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The theory gate on the kernel's own folds that Lean's kernel lacks
//! (`TypeChecker::hardwired_fold_admitted`, self-proof unit F1), asked of the
//! fold functions themselves under PRODUCTION authority: over
//! `Environment::with_prelude` the three `Int` heads and `Nat.pred` hold
//! `fold` rows, so authority admits them and the theory is what decides.
//!
//! The verdict-level half, through the reference entry over forged heads, is
//! `crates/clean-olean/tests/reference_entry_fold_theory.rs`.

use crate::env::{Declaration, Environment, KernelTheory};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;
use crate::tc::TypeChecker;

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn c(s: &str) -> Expr {
    Expr::const_(n(s), vec![])
}

/// `2^64`: the smallest literal `reduce_int`'s scope guard fires on.
const BIG: u128 = 1 << 64;

fn of_nat(v: u128) -> Expr {
    Expr::app(c("Int.ofNat"), Expr::nat_lit_u128(v))
}

fn checker(env: &Environment, theory: KernelTheory) -> TypeChecker<'_> {
    let mut tc = TypeChecker::new(env);
    tc.set_kernel_theory(theory);
    tc
}

/// `e` is the literal `want` itself (`BigNat` literals are kept normalized).
fn is_nat_lit(e: &Expr, want: u128) -> bool {
    *e == Expr::nat_lit_u128(want)
}

/// `reduce_int` fires in `Extended`, declines in `LeanReference`, and under
/// `Lean` follows the differential rule the registry reducers follow.
#[test]
fn test_reduce_int_declines_in_the_reference_theory() {
    let env = Environment::with_prelude();
    for (head, want) in [
        ("Int.add", BIG + 3),
        ("Int.sub", BIG - 3),
        ("Int.mul", BIG * 3),
    ] {
        assert!(
            env.native_fold_authorized(&n(head)),
            "{head}: control, authority admits the prelude's definition"
        );
        let term = Expr::apps(c(head), [of_nat(BIG), of_nat(3)]);
        let extended = checker(&env, KernelTheory::Extended);
        let folded = extended
            .reduce_int(&term)
            .unwrap_or_else(|| panic!("{head}: control, the fold fires in Extended"));
        assert!(
            extended.is_def_eq(&folded, &of_nat(want)),
            "{head}: the fold's {folded:?} is not the arithmetic answer"
        );
        assert!(
            checker(&env, KernelTheory::LeanReference)
                .reduce_int(&term)
                .is_none(),
            "{head}: reduce_int fired in the reference theory"
        );
        assert_eq!(
            checker(&env, KernelTheory::Lean)
                .reduce_int(&term)
                .is_some(),
            env.lean_theory_exclusion(&n(head)).is_none(),
            "{head}: the Lean profile follows its differential rule"
        );
    }
}

/// The `Nat.pred` arm of `reduce_nat` fires in `Extended` and declines in
/// `LeanReference`; Lean's own `Nat.succ` and `Nat.add` folds stay on there.
#[test]
fn test_nat_pred_fold_declines_in_the_reference_theory() {
    let env = Environment::with_prelude();
    let pred = n("Nat.pred");
    assert!(
        env.native_fold_authorized(&pred),
        "control: authority admits the prelude's Nat.pred"
    );
    for value in [5, BIG] {
        let term = Expr::app(c("Nat.pred"), Expr::nat_lit_u128(value));
        let folded = checker(&env, KernelTheory::Extended)
            .reduce_nat(&term)
            .expect("control: the fold fires in Extended");
        assert!(is_nat_lit(&folded, value - 1), "got {folded:?}");
        assert!(
            checker(&env, KernelTheory::LeanReference)
                .reduce_nat(&term)
                .is_none(),
            "Nat.pred {value}: the fold fired in the reference theory"
        );
        assert_eq!(
            checker(&env, KernelTheory::Lean)
                .reduce_nat(&term)
                .is_some(),
            env.lean_theory_exclusion(&pred).is_none(),
            "the Lean profile follows its differential rule"
        );
    }
    // Lean's own extensions are untouched by the gate.
    let reference = checker(&env, KernelTheory::LeanReference);
    let succ = reference
        .reduce_nat(&Expr::app(c("Nat.succ"), Expr::nat_lit(5)))
        .expect("Nat.succ on a literal is Lean's own extension");
    assert!(is_nat_lit(&succ, 6), "got {succ:?}");
    let sum = reference
        .reduce_nat(&Expr::apps(
            c("Nat.add"),
            [Expr::nat_lit(2), Expr::nat_lit(3)],
        ))
        .expect("Nat.add on literals is Lean's own extension");
    assert!(is_nat_lit(&sum, 5), "got {sum:?}");
}

/// Declining the fold loses no small verdict: the reference theory still
/// decides `Nat.pred 5 = 4` by unfolding the definition, as Lean's kernel
/// does, and still refuses `Nat.pred 5 = 5`.
#[test]
fn test_reference_theory_decides_nat_pred_by_unfolding() {
    let env = Environment::with_prelude();
    let reference = checker(&env, KernelTheory::LeanReference);
    let term = Expr::app(c("Nat.pred"), Expr::nat_lit(5));
    assert!(reference.is_def_eq(&term, &Expr::nat_lit(4)));
    assert!(!reference.is_def_eq(&term, &Expr::nat_lit(5)));
}

/// One checker whose theory moves: the verdict follows the theory both ways
/// (the admission memo is dropped with the theory, `forget_registry`).
#[test]
fn test_clean_only_fold_verdict_follows_a_theory_change() {
    let env = Environment::with_prelude();
    let term = Expr::app(c("Nat.pred"), Expr::nat_lit(5));
    let mut tc = TypeChecker::new(&env);
    assert_eq!(tc.kernel_theory(), KernelTheory::Extended);
    assert!(tc.reduce_nat(&term).is_some());
    tc.set_kernel_theory(KernelTheory::LeanReference);
    assert!(tc.reduce_nat(&term).is_none());
    tc.set_kernel_theory(KernelTheory::Extended);
    assert!(tc.reduce_nat(&term).is_some());
}

/// `Lean.reduceBool` / `Lean.reduceNat` over the opaque identities. Authority
/// admits an opaque identity structurally (world `identity`,
/// `env/native_fold_authority.rs`), so in production the evaluation is
/// reachable wherever that opaque is declared: it fires in `Extended`,
/// declines in `LeanReference`, and under `Lean` follows the differential rule
/// (neither head is on the list, so it declines).
#[test]
fn test_reduce_bool_and_reduce_nat_decline_in_the_reference_theory() {
    let mut env = Environment::with_prelude();
    for (head, ty) in [("Lean.reduceBool", "Bool"), ("Lean.reduceNat", "Nat")] {
        assert!(
            env.get_const(&n(head)).is_none(),
            "the prelude does not declare {head}"
        );
        env.add_decl(Declaration::Opaque {
            name: n(head),
            level_params: vec![],
            type_: Expr::pi(BinderInfo::Default, c(ty), c(ty)),
            value: Expr::lam(BinderInfo::Default, c(ty), Expr::bvar(0)),
        })
        .expect("the opaque identity is well typed");
    }
    for (constant, ty, value) in [
        ("f1BoolTrue", "Bool", c("Bool.true")),
        ("f1NatSeven", "Nat", Expr::nat_lit(7)),
    ] {
        env.add_decl(Declaration::Definition {
            name: n(constant),
            level_params: vec![],
            type_: c(ty),
            value,
            is_reducible: false,
        })
        .expect("a closed constant");
    }
    for (head, constant, want) in [
        ("Lean.reduceBool", "f1BoolTrue", c("Bool.true")),
        ("Lean.reduceNat", "f1NatSeven", Expr::nat_lit(7)),
    ] {
        assert_eq!(
            env.native_fold_verdict(&n(head)).ok(),
            Some("identity"),
            "{head}: control, authority admits the opaque identity"
        );
        let term = Expr::app(c(head), c(constant));
        let evaluated = checker(&env, KernelTheory::Extended)
            .try_reduce_native(&term)
            .unwrap_or_else(|| panic!("{head}: control, the evaluation fires in Extended"));
        assert_eq!(evaluated, want, "{head}");
        assert!(
            checker(&env, KernelTheory::LeanReference)
                .try_reduce_native(&term)
                .is_none(),
            "{head}: evaluated in the reference theory"
        );
        assert_eq!(
            checker(&env, KernelTheory::Lean)
                .try_reduce_native(&term)
                .is_some(),
            env.lean_theory_exclusion(&n(head)).is_none(),
            "{head}: the Lean profile follows its differential rule"
        );
        assert!(
            env.lean_theory_exclusion(&n(head)).is_some(),
            "{head}: nothing compared it against δι, so the Lean profile declines it"
        );
    }
}
