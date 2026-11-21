// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::env::{ConstantKind, ProofQuality};
use crate::tc::TypeChecker;
use std::collections::BTreeSet;

fn statement(ty_name: &str, operation: &str) -> Expr {
    let to_nat = k(&format!("{ty_name}.toNat"));
    let a = Expr::app(to_nat.clone(), Expr::bvar(1));
    let b = Expr::app(to_nat.clone(), Expr::bvar(0));
    let actual = Expr::app(
        to_nat,
        Expr::apps(
            k(&format!("{ty_name}.{operation}")),
            [Expr::bvar(1), Expr::bvar(0)],
        ),
    );
    let equality = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [k("Nat"), actual, Expr::apps(k("Nat.land"), [a, b])],
    );
    Expr::pi(
        BinderInfo::Default,
        k(ty_name),
        Expr::pi(BinderInfo::Default, k(ty_name), equality),
    )
}

fn axioms(env: &Environment) -> BTreeSet<Name> {
    env.constants()
        .filter(|info| info.kind == ConstantKind::Axiom)
        .map(|info| info.name.clone())
        .collect()
}

#[test]
fn test_uint_land_source_to_nat_has_exact_telescope_and_complete_strict_proof() {
    let env = Environment::with_prelude();
    for (ty_name, _) in WIDTHS {
        let name = Name::from_string(&format!("{ty_name}.toNat_land"));
        let info = env.get_const(&name).expect("native source bridge");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert_eq!(info.type_, statement(ty_name, "land"));
        env.check_decl_readonly_strict(&Declaration::Theorem {
            name: Name::from_string(&format!("UIntLandReplay.{ty_name}")),
            level_params: vec![],
            type_: info.type_.clone(),
            value: info
                .value
                .clone()
                .expect("actual modulus-elimination proof"),
        })
        .expect("strict replay of complete source operation proof");
        assert!(env.axiom_deps(&name).expect("full closure").is_empty());
        assert!(env
            .trust_marker_deps(&name)
            .expect("marker closure")
            .is_empty());
        assert!(env
            .foundational_axiom_deps(&name)
            .expect("foundational closure")
            .is_empty());
        assert_eq!(env.proof_quality(&name), Some(ProofQuality::Constructive));
    }
}

#[test]
fn test_uint_land_source_bridge_refuses_actual_or_operation_mutation() {
    let env = Environment::with_prelude();
    for (ty_name, _) in WIDTHS {
        assert_eq!(
            env.get_const(&Name::from_string(&format!("{ty_name}.lor")))
                .expect("actual OR operation must exist before the negative control")
                .kind,
            ConstantKind::Definition
        );
        let proof = env
            .get_const(&Name::from_string(&format!("{ty_name}.toNat_land")))
            .expect("registered")
            .value
            .clone()
            .expect("complete proof");
        // The altered universal claim is false for a=1, b=2 at every width.
        let error = env
            .check_decl_readonly_strict(&Declaration::Theorem {
                name: Name::from_string(&format!("UIntLandMutant.{ty_name}")),
                level_params: vec![],
                type_: statement(ty_name, "lor"),
                value: proof,
            })
            .expect_err("actual OR must not retain the source AND proof");
        assert!(
            matches!(
                error,
                EnvError::TypeCheckFailed {
                    source: crate::tc::TypeError::TypeMismatch { .. },
                    ..
                }
            ),
            "expected typed source mismatch, got: {error}"
        );
        assert!(!crate::tc::declaration_budget_exhausted());
    }
}

#[test]
fn test_uint_land_source_actual_definitions_cover_word_boundaries() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::with_mode(&env, env.mode());
    for (ty_name, maximum) in [
        ("UInt8", u64::from(u8::MAX)),
        ("UInt16", u64::from(u16::MAX)),
        ("UInt32", u64::from(u32::MAX)),
        ("UInt64", u64::MAX),
    ] {
        let from_nat = k(&format!("{ty_name}.ofNat"));
        let left = Expr::app(from_nat.clone(), Expr::nat_lit(maximum));
        let right = Expr::app(from_nat, Expr::nat_lit(1));
        let actual = Expr::app(
            k(&format!("{ty_name}.toNat")),
            Expr::apps(k(&format!("{ty_name}.land")), [left, right]),
        );
        assert!(
            tc.is_def_eq(&actual, &Expr::nat_lit(maximum & 1)),
            "{ty_name}: actual finite-carrier normalization"
        );
        assert_eq!(
            env.get_const(&Name::from_string(&format!("{ty_name}.land")))
                .expect("actual source operation")
                .kind,
            ConstantKind::Definition
        );
    }
}

#[test]
fn test_uint_land_source_bridge_is_exact_idempotent_and_adds_no_axioms() {
    let mut env = Environment::new();
    env.register_nat_land_bound_proof()
        .expect("canonical bound foundation");
    env.init_uint_floor_tonat_lemmas()
        .expect("finite source carrier foundation");
    let before = axioms(&env);
    env.register_uint_land_tonat_proofs()
        .expect("source bridges");
    assert_eq!(axioms(&env), before);
    let originals: Vec<_> = WIDTHS
        .iter()
        .map(|(ty_name, _)| {
            env.get_const(&Name::from_string(&format!("{ty_name}.toNat_land")))
                .expect("registered")
                .clone()
        })
        .collect();
    let count = env.num_constants();
    env.register_uint_land_tonat_proofs().expect("exact repeat");
    for original in originals {
        let retained = env.get_const(&original.name).expect("retained");
        assert_eq!(retained.type_, original.type_);
        assert_eq!(retained.value, original.value);
    }
    assert_eq!(env.num_constants(), count);
    assert_eq!(axioms(&env), before);
}

#[test]
fn test_uint_land_source_bridge_preserves_imports_and_refuses_hostile_names() {
    let mut imported = Environment::new();
    imported.suppress_lossy_structure_stubs = true;
    imported
        .register_uint_land_tonat_proofs()
        .expect("suppressed native overlay");
    for (ty_name, _) in WIDTHS {
        assert!(imported
            .get_const(&Name::from_string(&format!("{ty_name}.toNat_land")))
            .is_none());
    }
    let mut hostile = Environment::new();
    hostile
        .register_nat_land_bound_proof()
        .expect("actual prerequisites");
    hostile
        .init_uint_floor_tonat_lemmas()
        .expect("actual source carrier");
    let name = Name::from_string("UInt8.toNat_land");
    hostile
        .add_decl(Declaration::Axiom {
            name: name.clone(),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect("hostile existing name");
    assert!(hostile.register_uint_land_tonat_proofs().is_err());
    assert_eq!(
        hostile.get_const(&name).expect("not discharged").kind,
        ConstantKind::Axiom
    );
}
