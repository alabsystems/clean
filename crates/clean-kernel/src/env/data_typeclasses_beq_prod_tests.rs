// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `instBEqProd` through the kernel: registered as a checked definition, and
//! it COMPUTES — `(1, 2) == (1, 2)` reduces to `true` and `(1, 2) == (1, 3)`
//! to `false`, so the instance can neither prove a Lean-false equation nor
//! leave a Lean-true one stuck.

use super::*;
use crate::env::types::ConstantKind;
use crate::tc::TypeChecker;

fn nat() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

fn pair(a: u64, b: u64) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Prod.mk"),
            vec![Level::zero(), Level::zero()],
        ),
        [nat(), nat(), Expr::nat_lit(a), Expr::nat_lit(b)],
    )
}

/// `@BEq.beq (Nat × Nat) (@instBEqProd Nat Nat instBEqNat instBEqNat) l r`.
fn beq_pairs(l: Expr, r: Expr) -> Expr {
    let prod_nn = Expr::apps(
        Expr::const_(
            Name::from_string("Prod"),
            vec![Level::zero(), Level::zero()],
        ),
        [nat(), nat()],
    );
    let inst_nat = Expr::const_(Name::from_string("instBEqNat"), vec![]);
    let inst = Expr::apps(
        Expr::const_(
            Name::from_string("instBEqProd"),
            vec![Level::zero(), Level::zero()],
        ),
        [nat(), nat(), inst_nat.clone(), inst_nat],
    );
    Expr::apps(
        Expr::const_(Name::from_string("BEq.beq"), vec![Level::zero()]),
        [prod_nn, inst, l, r],
    )
}

fn bool_const(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

#[test]
fn test_inst_beq_prod_registered_checked_definition_axiom_free() {
    let env = Environment::with_prelude();
    let name = Name::from_string("instBEqProd");
    let info = env.get_const(&name).expect("instBEqProd is registered");
    assert_eq!(info.kind, ConstantKind::Definition);
    assert!(info.value.is_some(), "instBEqProd keeps its value");
    assert!(
        env.instances().any(|i| i.name == name),
        "instBEqProd is registered as a BEq instance"
    );
    let deps = env.axiom_deps(&name).expect("registered");
    assert!(deps.is_empty(), "axiom closure must be empty, got {deps:?}");
    let tc = TypeChecker::with_mode(&env, env.mode());
    let _checked = tc
        .infer_type(&Expr::const_(name, vec![Level::zero(), Level::zero()]))
        .expect("instBEqProd type-checks at levels 0 0");
}

#[test]
fn test_inst_beq_prod_equal_pairs_reduce_to_true() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let e = beq_pairs(pair(1, 2), pair(1, 2));
    assert!(tc.is_def_eq(&e, &bool_const("Bool.true")));
    assert!(!tc.is_def_eq(&e, &bool_const("Bool.false")));
}

#[test]
fn test_inst_beq_prod_unequal_second_component_is_false_not_true() {
    // Negative control: Lean 4.8 refuses `((1, 2) == (1, 3)) = true := rfl`.
    let env = Environment::with_prelude();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let e = beq_pairs(pair(1, 2), pair(1, 3));
    assert!(tc.is_def_eq(&e, &bool_const("Bool.false")));
    assert!(!tc.is_def_eq(&e, &bool_const("Bool.true")));
    // And the first component is compared too.
    let e = beq_pairs(pair(0, 3), pair(1, 3));
    assert!(!tc.is_def_eq(&e, &bool_const("Bool.true")));
}

#[test]
fn test_inst_beq_prod_import_mode_is_not_seeded() {
    // Under `.olean` import Lean's genuine `instBEqProd` must win; a seeded
    // stub would shadow it (first-registered-wins).
    let env = Environment::try_with_prelude_for_import().expect("import prelude builds");
    assert!(env.get_const(&Name::from_string("instBEqProd")).is_none());
}
