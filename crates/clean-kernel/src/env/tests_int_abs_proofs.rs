// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Guards that `Int.abs_zero` and `Int.abs_nonneg` are GENUINELY ELIMINATED —
//! kernel-checked `Declaration::Theorem`s with `ProofQuality::Constructive`
//! (empty domain-axiom closure), not admitted `Declaration::Axiom`s.
//!
//! `Int.abs i ≡ Int.ofNat (Int.natAbs i)` is always an `ofNat _`, so both facts
//! hold by construction:
//! - `Int.abs_zero`   : `@Eq.refl Int Int.zero` (def-eq reduction).
//! - `Int.abs_nonneg` : `@Int.NonNeg.mk (Int.natAbs a)` transported across
//!   `Int.add_zero` — the `Int.mul_nonneg` pattern.

use crate::env::axiom_audit::ProofQuality;
use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::Expr;
use crate::name::Name;
use crate::tc::TypeChecker;

fn env() -> Environment {
    let mut env = Environment::new();
    env.init_int_abs_props()
        .expect("init_int_abs_props should succeed");
    env
}

fn assert_constructive_theorem(name: &str) {
    let env = env();
    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should be registered"));
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "{name} must be a kernel-checked Theorem (genuinely proven), got {:?}",
        info.kind
    );
    assert!(
        info.value.is_some(),
        "{name} Theorem must retain its proof value"
    );

    // Kernel re-checks the proof term against its canonical type.
    let tc = TypeChecker::with_mode(&env, env.mode());
    let _ = tc
        .infer_type(&Expr::const_(Name::from_string(name), vec![]))
        .unwrap_or_else(|err| panic!("{name} should kernel-type-check, got {err:?}"));

    // Empty domain-axiom closure.
    let q = env
        .proof_quality(&Name::from_string(name))
        .expect("proof_quality");
    assert!(
        matches!(q, ProofQuality::Constructive),
        "{name} must be Constructive (no domain axiom in closure), got {q:?}"
    );

    // No `Rat.`/`Int.`-level admitted axiom and no sorry in the closure.
    let deps = env
        .axiom_deps(&Name::from_string(name))
        .expect("axiom_deps");
    for n in deps.iter().map(|n| n.to_string()) {
        assert!(
            n != "sorry" && n != "sorryAx",
            "{name} must be sorry-free, reached {n}"
        );
    }
}

#[test]
fn test_int_abs_zero_is_constructive_theorem() {
    assert_constructive_theorem("Int.abs_zero");
}

#[test]
fn test_int_abs_nonneg_is_constructive_theorem() {
    assert_constructive_theorem("Int.abs_nonneg");
}
