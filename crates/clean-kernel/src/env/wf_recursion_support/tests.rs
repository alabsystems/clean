// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for well-founded recursion support (Parts 1 and 2).

use crate::env::test_helpers::assert_const;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

#[test]
fn test_wf_recursion_support_init() {
    let mut env = Environment::new();
    assert!(!env.has_wf_recursion_support());
    env.init_wf_recursion_support()
        .expect("init_wf_recursion_support should succeed");
    assert!(env.has_wf_recursion_support());

    for name in &[
        // Part 1
        "WellFoundedRelation",
        "WellFoundedRelation.mk",
        "WellFoundedRelation.rel",
        "WellFoundedRelation.wf",
        "SizeOf",
        "SizeOf.mk",
        "SizeOf.sizeOf",
        "sizeOf",
        "InvImage",
        "InvImage.wf",
        "Nat.lt_wfRel",
        "invImage",
        "measure",
        "sizeOfWFRel",
        // Part 2: equation compiler support
        "Acc.inv",
        "WellFounded.fixFEq",
        "WellFounded.recursion",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_wf_recursion_support_idempotent() {
    let mut env = Environment::new();
    env.init_wf_recursion_support().unwrap();
    env.init_wf_recursion_support()
        .expect("second init should succeed");
}

#[test]
fn test_well_founded_relation_type_checks() {
    let mut env = Environment::new();
    env.init_wf_recursion_support().unwrap();
    let tc = TypeChecker::new(&env);
    let wfr = Expr::const_(
        Name::from_string("WellFoundedRelation"),
        vec![Level::succ(Level::zero())],
    );
    let ty = tc.infer_type(&wfr).expect("WellFoundedRelation type");
    assert!(matches!(&ty.kind, ExprKind::Pi(..)));
}

#[test]
fn test_sizeof_type_checks() {
    let mut env = Environment::new();
    env.init_wf_recursion_support().unwrap();
    let tc = TypeChecker::new(&env);
    let sizeof = Expr::const_(
        Name::from_string("SizeOf"),
        vec![Level::succ(Level::zero())],
    );
    let ty = tc.infer_type(&sizeof).expect("SizeOf type");
    assert!(matches!(&ty.kind, ExprKind::Pi(..)));
}

#[test]
fn test_inv_image_type_checks() {
    let mut env = Environment::new();
    env.init_wf_recursion_support().unwrap();
    let tc = TypeChecker::new(&env);
    let inv = Expr::const_(
        Name::from_string("InvImage"),
        vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
    );
    let ty = tc.infer_type(&inv).expect("InvImage type");
    assert!(matches!(&ty.kind, ExprKind::Pi(..)));
}

#[test]
fn test_nat_lt_wfrel_type() {
    let mut env = Environment::new();
    env.init_wf_recursion_support().unwrap();
    let tc = TypeChecker::new(&env);
    let nat_lt = Expr::const_(Name::from_string("Nat.lt_wfRel"), vec![]);
    let ty = tc.infer_type(&nat_lt).expect("Nat.lt_wfRel type");
    let head = ty.get_app_fn();
    assert!(
        matches!(&head.kind, ExprKind::Const(n, _) if n == &Name::from_string("WellFoundedRelation")),
    );
}

#[test]
fn test_measure_type() {
    let mut env = Environment::new();
    env.init_wf_recursion_support().unwrap();
    let tc = TypeChecker::new(&env);
    let measure = Expr::const_(
        Name::from_string("measure"),
        vec![Level::succ(Level::zero())],
    );
    let ty = tc.infer_type(&measure).expect("measure type");
    assert!(matches!(&ty.kind, ExprKind::Pi(..)));
}

// Part 2 tests: Acc.inv, WellFounded.fixFEq, WellFounded.recursion

#[test]
fn test_acc_inv_type_checks() {
    let mut env = Environment::new();
    env.init_wf_recursion_support().unwrap();
    let tc = TypeChecker::new(&env);
    let acc_inv = Expr::const_(
        Name::from_string("Acc.inv"),
        vec![Level::succ(Level::zero())],
    );
    let ty = tc.infer_type(&acc_inv).expect("Acc.inv should type-check");
    assert!(
        matches!(&ty.kind, ExprKind::Pi(..)),
        "Acc.inv should have Pi type"
    );
}

#[test]
fn test_acc_inv_is_definition() {
    let mut env = Environment::new();
    env.init_wf_recursion_support().unwrap();
    let info = env
        .get_const(&Name::from_string("Acc.inv"))
        .expect("Acc.inv should be registered");
    assert!(
        info.value.is_some(),
        "Acc.inv should be a definition with a value"
    );
    assert_eq!(
        info.level_params.len(),
        1,
        "Acc.inv should have 1 universe param [u]"
    );
}

#[test]
fn test_fix_f_eq_is_axiom_free_theorem() {
    // Track GG: `WellFounded.fixFEq` was DISCHARGED from a bare
    // `Declaration::Axiom` to a genuine kernel-checked `Declaration::Theorem`
    // whose proof is `@Acc.rec` on the accessibility witness (Acc.intro case
    // closes by `Eq.refl`, both sides iota-reducing to the common value).
    use crate::env::types::ConstantKind;

    let mut env = Environment::new();
    env.init_wf_recursion_support().unwrap();
    let info = env
        .get_const(&Name::from_string("WellFounded.fixFEq"))
        .expect("WellFounded.fixFEq should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "fixFEq should be a Theorem, not an Axiom (Track GG discharge)"
    );
    assert!(
        info.value.is_some(),
        "fixFEq should carry a kernel-checked proof value"
    );
    assert_eq!(
        info.level_params.len(),
        2,
        "fixFEq should have 2 universe params [u, v]"
    );

    // SOUNDNESS: the proof's transitive axiom closure must be EMPTY — no
    // domain axioms, no trust markers (sorry/sorryAx). It depends only on
    // `Acc.rec`, `WellFounded.fixF`, `Acc.inv`, `Acc.intro`, `Eq`/`Eq.refl`.
    let deps = env
        .axiom_deps(&Name::from_string("WellFounded.fixFEq"))
        .expect("fixFEq deps");
    assert!(
        deps.is_empty(),
        "fixFEq must be axiom-free, found deps: {deps:?}"
    );

    // And it classifies as Constructive.
    assert_eq!(
        env.proof_quality(&Name::from_string("WellFounded.fixFEq")),
        Some(crate::env::ProofQuality::Constructive),
        "fixFEq should be a Constructive theorem"
    );
}

#[test]
fn test_fix_f_eq_type_checks() {
    let mut env = Environment::new();
    env.init_wf_recursion_support().unwrap();
    let tc = TypeChecker::new(&env);
    let fix_f_eq = Expr::const_(
        Name::from_string("WellFounded.fixFEq"),
        vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
    );
    let ty = tc
        .infer_type(&fix_f_eq)
        .expect("WellFounded.fixFEq should type-check");
    assert!(
        matches!(&ty.kind, ExprKind::Pi(..)),
        "fixFEq should have Pi type"
    );
}

#[test]
fn test_wf_recursion_type_checks() {
    let mut env = Environment::new();
    env.init_wf_recursion_support().unwrap();
    let tc = TypeChecker::new(&env);
    let recursion = Expr::const_(
        Name::from_string("WellFounded.recursion"),
        vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
    );
    let ty = tc
        .infer_type(&recursion)
        .expect("WellFounded.recursion should type-check");
    assert!(
        matches!(&ty.kind, ExprKind::Pi(..)),
        "WellFounded.recursion should have Pi type"
    );
}

#[test]
fn test_wf_recursion_is_definition() {
    let mut env = Environment::new();
    env.init_wf_recursion_support().unwrap();
    let info = env
        .get_const(&Name::from_string("WellFounded.recursion"))
        .expect("WellFounded.recursion should be registered");
    assert!(
        info.value.is_some(),
        "WellFounded.recursion should be a definition with a value"
    );
    assert_eq!(
        info.level_params.len(),
        2,
        "WellFounded.recursion should have 2 universe params [u, v]"
    );
}

#[test]
fn test_wf_recursion_same_type_as_fix() {
    let mut env = Environment::new();
    env.init_wf_recursion_support().unwrap();
    let tc = TypeChecker::new(&env);
    let levels = vec![Level::succ(Level::zero()), Level::succ(Level::zero())];
    let fix_ty = tc
        .infer_type(&Expr::const_(
            Name::from_string("WellFounded.fix"),
            levels.clone(),
        ))
        .expect("fix type");
    let rec_ty = tc
        .infer_type(&Expr::const_(
            Name::from_string("WellFounded.recursion"),
            levels,
        ))
        .expect("recursion type");
    assert!(
        tc.is_def_eq(&fix_ty, &rec_ty),
        "WellFounded.recursion and WellFounded.fix should have the same type"
    );
}
