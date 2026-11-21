// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::env::{ConstantKind, ProofQuality};
use crate::tc::TypeChecker;
use std::collections::BTreeSet;

fn statement(ty: &str, mask: Option<u64>, operation: &str) -> Expr {
    let left = app(&format!("{ty}.toNat"), [Expr::bvar(1)]);
    let right = app(&format!("{ty}.toNat"), [Expr::bvar(0)]);
    let amount = match mask {
        Some(width) => app("Nat.mod", [right, Expr::nat_lit(width)]),
        None => right,
    };
    let residue = app(
        "Nat.mod",
        [
            app(
                "Nat.mul",
                [left, app("Nat.pow", [Expr::nat_lit(2), amount])],
            ),
            k(&format!("{ty}.size")),
        ],
    );
    let actual = app(
        &format!("{ty}.toNat"),
        [app(
            &format!("{ty}.{operation}"),
            [Expr::bvar(1), Expr::bvar(0)],
        )],
    );
    let goal = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [k("Nat"), actual, residue],
    );
    Expr::pi(
        BinderInfo::Default,
        k(ty),
        Expr::pi(BinderInfo::Default, k(ty), goal),
    )
}
fn axioms(env: &Environment) -> BTreeSet<Name> {
    env.constants()
        .filter(|i| i.kind == ConstantKind::Axiom)
        .map(|i| i.name.clone())
        .collect()
}
#[test]
fn uint_shiftleft_source_has_exact_masked_multiplication_telescope_and_strict_proof() {
    let env = Environment::with_prelude();
    let helper = Name::from_string("Nat.shiftLeft_eq");
    let info = env
        .get_const(&helper)
        .expect("actual recursive shift induction");
    let a = Expr::bvar(1);
    let b = Expr::bvar(0);
    let expected = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [
            k("Nat"),
            app("Nat.shiftLeft", [a.clone(), b.clone()]),
            app("Nat.mul", [a, app("Nat.pow", [Expr::nat_lit(2), b])]),
        ],
    );
    let expected = Expr::pi(
        BinderInfo::Default,
        k("Nat"),
        Expr::pi(BinderInfo::Default, k("Nat"), expected),
    );
    assert_eq!(
        info.type_, expected,
        "independent complete Nat shift-product telescope"
    );
    env.check_decl_readonly_strict(&Declaration::Theorem {
        name: Name::from_string("ShiftLeftReplay.NatInduction"),
        level_params: vec![],
        type_: info.type_.clone(),
        value: info.value.clone().unwrap(),
    })
    .expect("complete stored induction proof");
    assert!(env.axiom_deps(&helper).unwrap().is_empty());
    assert!(env.trust_marker_deps(&helper).unwrap().is_empty());
    for (ty, width) in WIDTHS {
        let name = Name::from_string(&format!("{ty}.toNat_shiftLeft"));
        let info = env.get_const(&name).expect("always-on source bridge");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert_eq!(info.type_, statement(ty, Some(width), "shiftLeft"));
        env.check_decl_readonly_strict(&Declaration::Theorem {
            name: Name::from_string(&format!("ShiftLeftReplay.{ty}")),
            level_params: vec![],
            type_: info.type_.clone(),
            value: info.value.clone().expect("complete actual source proof"),
        })
        .expect("strict complete source replay");
        assert!(env.axiom_deps(&name).unwrap().is_empty());
        assert!(env.trust_marker_deps(&name).unwrap().is_empty());
        assert_eq!(env.proof_quality(&name), Some(ProofQuality::Constructive));
    }
}
#[test]
fn uint_shiftleft_source_refuses_missing_wrong_mask_and_right_shift() {
    let env = Environment::with_prelude();
    for (ty, width) in WIDTHS {
        assert_eq!(
            env.get_const(&Name::from_string(&format!("{ty}.shiftRight")))
                .unwrap()
                .kind,
            ConstantKind::Definition
        );
        let proof = env
            .get_const(&Name::from_string(&format!("{ty}.toNat_shiftLeft")))
            .unwrap()
            .value
            .clone()
            .unwrap();
        for (index, claim) in [
            statement(ty, None, "shiftLeft"),
            statement(ty, Some(width / 2), "shiftLeft"),
            statement(ty, Some(width), "shiftRight"),
        ]
        .into_iter()
        .enumerate()
        {
            let error = env
                .check_decl_readonly_strict(&Declaration::Theorem {
                    name: Name::from_string(&format!("ShiftLeftMutant.{ty}.{index}")),
                    level_params: vec![],
                    type_: claim,
                    value: proof.clone(),
                })
                .expect_err("altered masking or source operation must not retain the proof");
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
}
#[test]
fn uint_shiftleft_actual_source_covers_zero_and_width_boundaries_and_masked_amounts() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::with_mode(&env, env.mode());
    for (ty, width) in WIDTHS {
        let maximum = if width == 64 {
            u64::MAX
        } else {
            (1_u64 << width) - 1
        };
        for word in [0, 1, maximum, 1_u64 << (width - 1)] {
            for amount in [0, width - 1, width, width + 1, maximum] {
                let actual = app(
                    &format!("{ty}.toNat"),
                    [app(
                        &format!("{ty}.shiftLeft"),
                        [
                            app(&format!("{ty}.ofNat"), [Expr::nat_lit(word)]),
                            app(&format!("{ty}.ofNat"), [Expr::nat_lit(amount)]),
                        ],
                    )],
                );
                assert!(
                    tc.is_def_eq(
                        &actual,
                        &Expr::nat_lit((word << (amount % width)) & maximum)
                    ),
                    "{ty}: word={word}, amount={amount}"
                );
            }
        }
    }
}
#[test]
fn uint_shiftleft_registration_is_exact_and_adds_no_axioms() {
    let mut env = Environment::new();
    env.init_uint_floor_tonat_lemmas()
        .expect("real source carrier foundation");
    let before = axioms(&env);
    env.register_uint_shiftleft_tonat_proofs()
        .expect("register strict source proofs");
    assert_eq!(axioms(&env), before);
    let originals: Vec<_> = WIDTHS
        .iter()
        .map(|(ty, _)| {
            env.get_const(&Name::from_string(&format!("{ty}.toNat_shiftLeft")))
                .unwrap()
                .clone()
        })
        .collect();
    let count = env.num_constants();
    env.register_uint_shiftleft_tonat_proofs()
        .expect("exact repeat");
    assert_eq!(env.num_constants(), count);
    for original in originals {
        let retained = env.get_const(&original.name).unwrap();
        assert_eq!(retained.type_, original.type_);
        assert_eq!(retained.value, original.value);
    }
    assert_eq!(axioms(&env), before);
}
#[test]
fn uint_shiftleft_registration_preserves_imports_and_refuses_hostile_names() {
    let mut imported = Environment::new();
    imported.suppress_lossy_structure_stubs = true;
    imported
        .register_uint_shiftleft_tonat_proofs()
        .expect("suppressed overlay");
    for (ty, _) in WIDTHS {
        assert!(imported
            .get_const(&Name::from_string(&format!("{ty}.toNat_shiftLeft")))
            .is_none());
    }
    let mut hostile = Environment::new();
    hostile
        .init_uint_floor_tonat_lemmas()
        .expect("actual source carrier");
    let name = Name::from_string("UInt8.toNat_shiftLeft");
    hostile
        .add_decl(Declaration::Axiom {
            name: name.clone(),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .unwrap();
    assert!(hostile.register_uint_shiftleft_tonat_proofs().is_err());
    assert_eq!(hostile.get_const(&name).unwrap().kind, ConstantKind::Axiom);
}
