// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::env::{ConstantInfo, TrustedEnvExt};
use clean_kernel::expr::ExprKind;
use clean_olean::{ClosedRecheckRefusal, ImportedConeGate};
use std::collections::BTreeSet;

fn returns(ty: &Expr, value: &Expr) -> Expr {
    match ty.kind() {
        ExprKind::Pi(binder, domain, body) => {
            Expr::lam(*binder, (**domain).clone(), returns(body, value))
        }
        _ => value.clone(),
    }
}

fn replace(env: &Environment, name: &str, value: Expr) -> Environment {
    let original = env
        .get_const(&n(name))
        .expect("genuine declared member")
        .clone();
    let checker = TypeChecker::new(env);
    assert!(
        checker.check_type(&value, &original.type_).is_ok(),
        "mutation must be well typed: {name}"
    );
    let mut forged = env.clone();
    assert!(forged.forget_decl(&original.name));
    assert!(forged
        .extend_constants_structural(std::iter::once(ConstantInfo {
            value: Some(value),
            ..original
        }))
        .is_empty());
    forged
}

fn refusal(env: &Environment, key: &str, dependent: &str, expected_binding: &str) {
    assert!(
        !env.native_fold_authorized(&n(key)),
        "tampered {key} retained native fold authority"
    );
    let mut base = Environment::for_lean_replay();
    clean_olean::declare_environment_world(&mut base, LeanWorld::Lean435.tag()).unwrap();
    let mut gate = ImportedConeGate::new(&base);
    let verdict = gate.check(env, &BTreeSet::from([n(dependent)]));
    assert!(!verdict.passed(true), "mutated {key} admitted: {verdict:?}");
    assert!(
        verdict.refusals.iter().any(|failure| matches!(failure,
            ClosedRecheckRefusal::ExtensionBindingMismatch { name, .. } if name == expected_binding
        )),
        "{key}: expected exact binding refusal, got {verdict:?}"
    );
    eprintln!("LEAN435_FORGERY {key} dependent={dependent}: {verdict:?}");
}

#[test]
fn genuine_435_wrong_heads_and_unchanged_heads_with_tampered_helpers_refuse() {
    let (_dir, env) = oracle::fixture();
    for (key, helper, dependent) in [
        ("Nat.div", "Nat.div.go", "Bindings435.divAlias"),
        ("Nat.mod", "Nat.modCore", "Bindings435.modAlias"),
        ("Char.ofNat", "Char.ofNatAux", "Bindings435.charAlias"),
        (
            "String.ofList",
            "String.utf8EncodeChar",
            "Bindings435.stringOrder",
        ),
    ] {
        let honest = env.get_const(&n(key)).unwrap();
        let answer = if key == "String.ofList" {
            Expr::str_lit("")
        } else if key == "Char.ofNat" {
            // Inline the genuine function at zero, so the replacement does
            // not recursively mention the very name being forged.
            zero_char(&env)
        } else {
            Expr::nat_lit(0)
        };
        refusal(
            &replace(&env, key, returns(&honest.type_, &answer)),
            key,
            dependent,
            key,
        );
        let actual_helper = env
            .get_const(&n(helper))
            .unwrap_or_else(|| panic!("missing actual helper {helper}"));
        let answer = if key == "String.ofList" {
            Expr::app(Expr::const_(n("List.nil"), vec![Level::zero()]), c("UInt8"))
        } else if key == "Char.ofNat" {
            zero_char(&env)
        } else {
            Expr::nat_lit(0)
        };
        let forged = replace(&env, helper, returns(&actual_helper.type_, &answer));
        assert_eq!(
            forged.get_const(&n(key)).unwrap().value,
            honest.value,
            "the head's own bytes must be unchanged in the helper mutation"
        );
        // String's representation family includes the UTF8 relation. A
        // computational UTF8 helper mutation is refused at that earlier
        // family binding, before the unchanged conversion can be replayed.
        let binding = if key == "String.ofList" {
            "String"
        } else {
            key
        };
        refusal(&forged, key, dependent, binding);
    }
}

fn zero_char(env: &Environment) -> Expr {
    let mut checker = TypeChecker::new(env);
    checker.set_heartbeat_limit(native_fold_review::REVIEW_HEARTBEATS);
    let value = checker.whnf(&Expr::app(c("Char.ofNat"), Expr::nat_lit(0x110000)));
    assert!(checker.check_type(&value, &c("Char")).is_ok());
    assert!(!value.collect_constants().contains(&n("Char.ofNat")));
    assert!(!value.collect_constants().contains(&n("Char.ofNatAux")));
    value
}
