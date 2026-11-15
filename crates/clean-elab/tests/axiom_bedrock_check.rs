// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! ADVERSARIAL soundness check: prove that the `axiom_deps(name).is_empty()`
//! gate used throughout the TrustIr correspondence is a REAL, DISCRIMINATING
//! check — it flags a proof that reaches a non-foundational axiom, directly or
//! through a definition or a lemma, and accepts only proofs whose entire
//! dependency graph is foundational.
//!
//! If this test passes, then the 270 TrustIr theorems passing the SAME gate
//! genuinely rest only on {propext, Quot.sound, Classical.choice} + kernel
//! primitives — bedrock — and not vacuously (the gate provably rejects
//! non-bedrock proofs).
//!
//! THE ADVERSARY IS DECLARED HERE, NOT BORROWED FROM THE PRELUDE. Until
//! 2026-09-29 the probe used `Nat.shiftRight`, then a prelude domain axiom;
//! the full prelude has since discharged it to a Definition
//! (`register_nat_shiftright_def`, `Nat.iterDiv2`), the probe reached no axiom
//! at all, and this test reported the gate "VACUOUS" when the gate was fine and
//! the FIXTURE had gone stale. A domain axiom this file declares cannot be
//! discharged out from under it, so the adversarial half now measures the gate
//! and nothing else. `Nat.shiftRight` stays as a POSITIVE control: a proof
//! through it is bedrock now, and turning it back into an axiom would redden
//! that line, not this one.

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

-- (c) GENUINE through `Nat.shiftRight`, a Definition in the full prelude
-- (`register_nat_shiftright_def`) -- it was a domain axiom when this file was
-- written, and was this test's adversary.
theorem viaShiftRight (a : Nat) :
    @Eq Nat (Nat.shiftRight a 0) (Nat.shiftRight a 0) :=
  @Eq.refl Nat (Nat.shiftRight a 0)

-- (d) ADVERSARIAL: domain axioms declared here, so no prelude change can
-- discharge them. Each proof below must be FLAGGED with the axiom it reaches.
axiom domainValue : Nat
axiom domainFact : @Eq Nat 0 1

-- directly, in the proof term
theorem usesAxiomDirectly : @Eq Nat 0 1 := domainFact

-- through a definition the proof unfolds
def viaDef : Nat := Nat.add domainValue 0
theorem usesAxiomThroughDef : @Eq Nat viaDef viaDef := @Eq.refl Nat viaDef

-- through a lemma that is itself flagged
theorem usesAxiomThroughLemma : @Eq Nat 0 1 := usesAxiomDirectly

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
    for g in ["genuine", "genuine2", "viaShiftRight"] {
        let n = resolve(&env, g);
        let deps = env.axiom_deps(&n).expect("deps");
        assert!(
            deps.is_empty(),
            "{g} should be bedrock but rests on: {deps:?}"
        );
    }

    // The adversaries really are AXIOMS of this environment (declared, not
    // defined); that they are non-foundational is what the flags below show.
    for ax in ["domainValue", "domainFact"] {
        let n = resolve(&env, ax);
        let kind = env.get_const(&n).map(|c| c.kind);
        assert!(
            matches!(kind, Some(clean_kernel::env::ConstantKind::Axiom)),
            "{ax} must be registered as an axiom, got {kind:?}"
        );
    }

    // ADVERSARIAL: every proof reaching a domain axiom -- directly, through a
    // definition it unfolds, or through a lemma -- must be FLAGGED with that
    // axiom. If any came back empty, the gate would be vacuous.
    for (thm, reaches) in [
        ("usesAxiomDirectly", "domainFact"),
        ("usesAxiomThroughDef", "domainValue"),
        ("usesAxiomThroughLemma", "domainFact"),
    ] {
        let bad = resolve(&env, thm);
        let bad_deps = env.axiom_deps(&bad).expect("deps");
        let axiom = resolve(&env, reaches);
        assert!(
            bad_deps.contains(&axiom),
            "the axiom_deps gate is VACUOUS: {thm} reaches the domain axiom {axiom} and was \
             not flagged with it, got: {bad_deps:?}"
        );
    }

    // And the gate ALSO catches trust markers (sorry/trustedAy) — they are
    // non-foundational axioms, so axiom_deps subsumes trust_marker_deps. The
    // genuine proofs have no trust markers either.
    for g in ["genuine", "genuine2", "viaShiftRight"] {
        let n = resolve(&env, g);
        let tm = env.trust_marker_deps(&n).expect("tm");
        assert!(tm.is_empty(), "{g} unexpectedly has trust markers: {tm:?}");
    }

    println!("axiom_deps gate verified DISCRIMINATING: bedrock proofs empty; every domain-axiom proof flagged");
}
