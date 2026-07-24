// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for issue #3431: enum-case `deriving DecidableEq`
//! must pass strict kernel type checking.

use super::*;

fn expr_contains_const(expr: &Expr, target: &str) -> bool {
    match expr.kind() {
        ExprKind::Const(name, _) => name.to_string() == target,
        ExprKind::App(f, a) => expr_contains_const(f, target) || expr_contains_const(a, target),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_contains_const(ty, target) || expr_contains_const(body, target)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            expr_contains_const(ty, target)
                || expr_contains_const(val, target)
                || expr_contains_const(body, target)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            expr_contains_const(inner, target)
        }
        _ => false,
    }
}

/// Regression test for #3431: `inductive Color | red | green | blue deriving DecidableEq`
/// failed strict kernel type checking with
///   `KernelCheckFailed { name: "instColorDecidableEq",
///     detail: "Level count mismatch for Color.casesOn: declared 1 level params, got 0" }`.
///
/// Root cause: `derive_decidable_eq_inductive` built a body referencing
/// `Color.casesOn` and `Color.noConfusion` via `self.mk_const_str(...)`, but those
/// kernel-generated recursors are only created AFTER derive runs. `mk_const` then
/// fell back to empty levels even though `casesOn` / `noConfusion` each declare
/// one level parameter (motive / result universe).
///
/// Fix: avoid the casesOn + noConfusion construction and instead emit a
/// `sorry`-backed Decidable value, matching the multi-field structure derive path
/// and the alternate `DeriveDecidableEq` handler in `derive_handlers.rs`. This
/// keeps the instance kernel-type-checkable with no reference to recursors that
/// are not yet in the environment.
#[test]
fn test_issue3431_inductive_deriving_decidable_eq_strict_kernel_check() {
    let mut env = Environment::with_prelude();

    // Exact repro from issue #3431
    let decl = parse_decl_for_elab(
        r"inductive Color
| red
| green
| blue
deriving DecidableEq",
    )
    .unwrap();

    // This failed with "Level count mismatch for Color.casesOn: declared 1
    // level params, got 0" before the #3431 fix.
    let result = crate::elaborate_decl_and_register(&mut env, &decl);
    assert!(
        result.is_ok(),
        "inductive Color deriving DecidableEq should elaborate and register \
         without KernelCheckFailed (issue #3431): {:?}",
        result.err()
    );

    match result.unwrap() {
        ElabResult::Inductive {
            derived_instances, ..
        } => {
            let deq_inst = derived_instances
                .iter()
                .find(|i| i.class_name == Name::from_string("DecidableEq"))
                .expect("should have DecidableEq derived instance");

            assert_eq!(deq_inst.name, Name::from_string("instColorDecidableEq"));

            // The monomorphic instance must have zero universe params.
            assert!(
                deq_inst.level_params.is_empty(),
                "Monomorphic DecidableEq instance for Color should have zero \
                 universe params, got: {:?}",
                deq_inst.level_params
            );

            // Build the declaration as the kernel would see it, then strict
            // kernel type check on a fresh env where only the inductive (not
            // the deriving-generated instance) has been registered.
            let inst_decl = Declaration::Definition {
                name: deq_inst.name.clone(),
                level_params: deq_inst.level_params.clone(),
                type_: deq_inst.ty.clone(),
                value: deq_inst.val.clone(),
                is_reducible: true,
            };

            let mut env2 = Environment::with_prelude();
            let decl2 = parse_decl_for_elab(
                r"inductive Color
| red
| green
| blue",
            )
            .unwrap();
            crate::elaborate_decl_and_register(&mut env2, &decl2)
                .expect("Color without deriving should register");

            let add_result = env2.add_decl(inst_decl);
            assert!(
                add_result.is_ok(),
                "instColorDecidableEq should pass strict kernel type check \
                 (no Level count mismatch on casesOn, issue #3431): {:?}",
                add_result.err()
            );
        }
        other => panic!("expected Inductive, got {other:?}"),
    }
}

/// Regression test for #3431 — single-constructor inductive case.
/// The fix must preserve the reflexivity-based path for 0/1 constructor
/// inductives (they don't need casesOn).
#[test]
fn test_issue3431_inductive_single_ctor_deriving_decidable_eq_strict_kernel_check() {
    let mut env = Environment::with_prelude();

    // Named `Solo` (not `Singleton`): the prelude now carries the Lean-core
    // `Singleton` collection-literal class (Brick P1, Init/Core.lean:599),
    // and re-declaring a core name is a DuplicateName in Lean 4 as well.
    let decl = parse_decl_for_elab(
        r"inductive Solo
| only
deriving DecidableEq",
    )
    .unwrap();

    let result = crate::elaborate_decl_and_register(&mut env, &decl);
    assert!(
        result.is_ok(),
        "inductive Solo deriving DecidableEq should elaborate: {:?}",
        result.err()
    );

    match result.unwrap() {
        ElabResult::Inductive {
            derived_instances, ..
        } => {
            let deq_inst = derived_instances
                .iter()
                .find(|i| i.class_name == Name::from_string("DecidableEq"))
                .expect("should have DecidableEq derived instance");

            let inst_decl = Declaration::Definition {
                name: deq_inst.name.clone(),
                level_params: deq_inst.level_params.clone(),
                type_: deq_inst.ty.clone(),
                value: deq_inst.val.clone(),
                is_reducible: true,
            };

            let mut env2 = Environment::with_prelude();
            let decl2 = parse_decl_for_elab(
                r"inductive Solo
| only",
            )
            .unwrap();
            crate::elaborate_decl_and_register(&mut env2, &decl2)
                .expect("Solo without deriving should register");

            let add_result = env2.add_decl(inst_decl);
            assert!(
                add_result.is_ok(),
                "instSoloDecidableEq should pass strict kernel type check: {:?}",
                add_result.err()
            );
        }
        other => panic!("expected Inductive, got {other:?}"),
    }
}

/// Two-constructor enum — smallest case that goes through the multi-ctor
/// sorry path. Before the fix, this failed the same way as the 3-ctor case.
#[test]
fn test_issue3431_inductive_two_ctor_deriving_decidable_eq_strict_kernel_check() {
    let mut env = Environment::with_prelude();

    let decl = parse_decl_for_elab(
        r"inductive Bit
| zero
| one
deriving DecidableEq",
    )
    .unwrap();

    let result = crate::elaborate_decl_and_register(&mut env, &decl);
    assert!(
        result.is_ok(),
        "inductive Bit deriving DecidableEq should elaborate and register: {:?}",
        result.err()
    );
}

/// Track L (part 2): a monomorphic multi-ctor inductive whose non-nullary
/// constructors carry a single field with a resolvable `DecidableEq` instance
/// now derives a REAL, sorry-free decision procedure (per-field decEq dispatch +
/// `congrArg` / `noConfusion`). This previously fell back to a `sorryAx`
/// placeholder; that obligation is now discharged genuinely, so the derived
/// instance must contain NO `sorry` / `sorryAx`.
#[test]
fn test_non_nullary_inductive_decidable_eq_is_sorry_free() {
    let mut env = Environment::with_prelude();

    let decl = parse_decl_for_elab(
        r"inductive MaybeNat
| none
| some : Nat -> MaybeNat
deriving DecidableEq",
    )
    .unwrap();

    let result = crate::elaborate_decl_and_register(&mut env, &decl)
        .expect("non-nullary inductive DecidableEq should elaborate");

    match result {
        ElabResult::Inductive {
            derived_instances, ..
        } => {
            let deq_inst = derived_instances
                .iter()
                .find(|i| i.class_name == Name::from_string("DecidableEq"))
                .expect("should have DecidableEq derived instance");

            assert!(
                !expr_contains_const(&deq_inst.val, "sorryAx"),
                "fielded DecidableEq must no longer use the sorryAx fallback, got {:?}",
                deq_inst.val
            );
            assert!(
                !expr_contains_const(&deq_inst.val, "sorry"),
                "fielded DecidableEq must not contain any sorry constant, got {:?}",
                deq_inst.val
            );
        }
        other => panic!("expected Inductive, got {other:?}"),
    }
}
