// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Exercise the actual consumer's vocabulary check, without test-only kernel
//! admission doors or changes to process-global construction policy.

use super::{verify_prelude_vocabulary, FiniteError};
use clean_kernel::env::{
    set_mm_axiom_only, ConstantKind, Declaration, Environment, MmAxiomOnlyGuard,
};
use clean_kernel::{BinderInfo, Expr, Name};

#[test]
fn warm_reference_rejects_same_typed_bool_not_then_accepts_original() {
    let good = Environment::try_with_prelude().expect("ordinary prelude");
    verify_prelude_vocabulary(&good).expect("valid caller warms the reference");
    let name = Name::from_string("Bool.not");
    let expected = good.get_const(&name).expect("ordinary Bool.not").clone();
    assert_eq!(expected.kind, ConstantKind::Definition);

    // The caller owns this deliberately corrupted environment. Use only the
    // existing public deletion and FULLY CHECKED declaration addition paths.
    // A well-typed constant function is not the blessed Bool.not definition.
    let mut corrupted = good.clone();
    assert!(corrupted.forget_decl(&name));
    corrupted
        .add_decl(Declaration::Definition {
            name: name.clone(),
            level_params: expected.level_params.clone(),
            type_: expected.type_.clone(),
            value: Expr::lam(
                BinderInfo::Default,
                Expr::const_str("Bool"),
                Expr::const_str("Bool.true"),
            ),
            is_reducible: expected.is_reducible,
        })
        .expect("same-typed mutant passes checked declaration admission");
    let mutant = corrupted.get_const(&name).expect("mutant is present");
    assert_eq!(mutant.kind, expected.kind);
    assert_eq!(mutant.type_, expected.type_);
    assert_ne!(
        mutant.value, expected.value,
        "fixture must change semantics"
    );
    assert!(matches!(
        verify_prelude_vocabulary(&corrupted),
        Err(FiniteError::VocabularySquatted { name }) if name == "Bool.not"
    ));
    verify_prelude_vocabulary(&good).expect("caller corruption cannot poison the reference");
}

#[test]
fn missing_prelude_is_a_named_consumer_refusal() {
    let empty = Environment::default();
    let Err(FiniteError::MissingPrelude { missing }) = verify_prelude_vocabulary(&empty) else {
        panic!("an empty caller environment must be refused before reference comparison")
    };
    assert!(missing.iter().any(|name| name == "Bool.not"));
    assert!(missing.iter().any(|name| name == "Nat.add"));
}

#[test]
fn warm_reference_reports_metamath_policy_refusal_and_recovers() {
    let good = Environment::try_with_prelude().expect("ordinary prelude");
    verify_prelude_vocabulary(&good).expect("valid caller warms the reference");
    // Only this fresh thread's MM flags change; no environment-variable races
    // and no raw prelude is constructed under proof-dropping MM policy.
    std::thread::spawn(move || {
        {
            let _two_pass = MmAxiomOnlyGuard::enter();
            for axiom_only in [false, true] {
                set_mm_axiom_only(axiom_only);
                assert!(matches!(
                    verify_prelude_vocabulary(&good),
                    Err(FiniteError::Internal(message)) if message.contains("Metamath two-pass")
                ));
            }
        }
        verify_prelude_vocabulary(&good).expect("MM refusal must not replace the warm reference");
    })
    .join()
    .unwrap();
}
