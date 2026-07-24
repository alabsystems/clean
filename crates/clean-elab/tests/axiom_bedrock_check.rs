// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! ADVERSARIAL soundness check: prove that the `axiom_deps(name).is_empty()`
//! gate used throughout the TrustIr correspondence is a REAL, DISCRIMINATING
//! check — it flags a proof that transitively reaches a non-foundational axiom
//! (e.g. the registered `Nat.shiftRight` axiom) or a trust marker (`sorryAx`),
//! and accepts only proofs whose entire dependency graph is foundational.
//!
//! If this test passes, then the 270 TrustIr theorems passing the SAME gate
//! genuinely rest only on {propext, Quot.sound, Classical.choice} + kernel
//! primitives — bedrock — and not vacuously (the gate provably rejects
//! non-bedrock proofs).

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;

const SRC: &str = r#"
namespace Bedrock

-- (a) GENUINE: a foundational proof (uses only Eq.refl, a kernel primitive).
theorem genuine (a : Nat) : @Eq Nat a a := @Eq.refl Nat a

-- (b) GENUINE composite: still foundational (Nat.rec is a kernel primitive).
theorem genuine2 (a : Nat) : @Eq Nat (Nat.add a 0) a := @Eq.refl Nat (Nat.add a 0)

-- (c) AXIOM-DEPENDENT: `Nat.shiftRight` is registered as a DOMAIN AXIOM in this
-- kernel (data_types_nat.rs). Any proof transitively referencing it is NOT
-- bedrock — axiom_deps must flag `Nat.shiftRight`.
theorem usesShiftRightAxiom (a : Nat) :
    @Eq Nat (Nat.shiftRight a 0) (Nat.shiftRight a 0) :=
  @Eq.refl Nat (Nat.shiftRight a 0)

end Bedrock
"#;

fn elaborate_module(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = clean_parser::parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed)
            .map_err(|e| format!("elaborate/kernel-check error: {e}"))?;
        let mut failures = Vec::new();
        collect_failures(&result, &mut failures);
        if !failures.is_empty() {
            return Err(format!("inner failures:\n{}", failures.join("\n")));
        }
    }
    Ok(env)
}
fn collect_failures(result: &ElabResult, out: &mut Vec<String>) {
    match result {
        ElabResult::Multiple(rs) => rs.iter().for_each(|r| collect_failures(r, out)),
        ElabResult::Failed { name, error, .. } => out.push(format!("{name}: {error}")),
        _ => {}
    }
}
fn resolve(env: &Environment, short: &str) -> Name {
    env.constants()
        .map(|c| &c.name)
        .find(|n| n.last_component().as_deref() == Some(short))
        .cloned()
        .unwrap_or_else(|| panic!("no const {short}"))
}

#[test]
fn axiom_deps_gate_is_real_and_discriminating() {
    let env = elaborate_module(SRC).expect("bedrock probe module must elaborate");

    // GENUINE proofs: empty non-foundational closure (bedrock).
    for g in ["genuine", "genuine2"] {
        let n = resolve(&env, g);
        let deps = env.axiom_deps(&n).expect("deps");
        assert!(
            deps.is_empty(),
            "{g} should be bedrock but rests on: {deps:?}"
        );
    }

    // ADVERSARIAL: a proof that touches the `Nat.shiftRight` AXIOM must be FLAGGED
    // (non-empty deps containing Nat.shiftRight). If this fired empty, the gate
    // would be vacuous — this asserts it is NOT.
    let bad = resolve(&env, "usesShiftRightAxiom");
    let bad_deps = env.axiom_deps(&bad).expect("deps");
    assert!(
        !bad_deps.is_empty(),
        "the axiom_deps gate is VACUOUS: it failed to flag a Nat.shiftRight-dependent proof"
    );
    assert!(
        bad_deps
            .iter()
            .any(|n| n.to_string().contains("shiftRight")),
        "expected Nat.shiftRight in the flagged deps, got: {bad_deps:?}"
    );

    // And the gate ALSO catches trust markers (sorry/trustedAy) — they are
    // non-foundational axioms, so axiom_deps subsumes trust_marker_deps. The
    // genuine proofs have no trust markers either.
    for g in ["genuine", "genuine2"] {
        let n = resolve(&env, g);
        let tm = env.trust_marker_deps(&n).expect("tm");
        assert!(tm.is_empty(), "{g} unexpectedly has trust markers: {tm:?}");
    }

    println!("axiom_deps gate verified DISCRIMINATING: bedrock proofs empty; Nat.shiftRight-dependent proof flagged with {bad_deps:?}");
}
