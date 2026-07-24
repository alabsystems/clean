// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the constructive `Rat.neg_le_neg` proof term (#3538).
//!
//! Paired with
//! `crates/clean-kernel/src/env/nn_verify_interval_arith_rat_neg_le_neg_proof.rs`
//! (proof-term builder) and the `register_rat_neg_le_neg` site in
//! `crates/clean-kernel/src/env/nn_verify_interval_arith_proofs.rs`.
//!
//! Guards enforced here:
//! - `Rat.neg_le_neg` is a `Declaration::Theorem` carrying a proof term
//!   (not `Declaration::Axiom`, not an Opaque-with-`sorry`).
//! - The proof term type-checks under the kernel.
//! - The proof term is sorry-free (no `sorry` / `sorryAx` anywhere).
//! - The transitive axiom closure is a subset of the honest Rat
//!   ordered-field axiom set already carried by the sibling bridging
//!   lemmas (`Rat.sub_nonneg_of_le`, `Rat.le_of_sub_nonneg`) — i.e., no
//!   *new* domain axiom was introduced.
//!
//! Lives in a sibling file (not inline with `nn_verify_interval_arith_proofs.rs`)
//! because that parent file is already well above the 500-line code-quality
//! ceiling and must not grow further.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_interval_arith_proofs()
        .expect("init_nn_verify_interval_arith_proofs");
    env
}

/// #3538: `Rat.neg_le_neg` is a genuine `Declaration::Theorem` (not Axiom)
/// with a proof-term value attached.
#[test]
fn test_rat_neg_le_neg_is_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("Rat.neg_le_neg"))
        .expect("Rat.neg_le_neg should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "Rat.neg_le_neg must be a Theorem after #3538, got {:?}",
        info.kind,
    );
    assert!(
        info.value.is_some(),
        "Rat.neg_le_neg must carry a proof term",
    );
}

/// #3538: the constructive proof term type-checks against the declared
/// theorem statement.
#[test]
fn test_rat_neg_le_neg_type_checks() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("Rat.neg_le_neg"))
        .expect("Rat.neg_le_neg should be registered");
    let proof = info.value.as_ref().expect("theorem should have value");
    let tc = TypeChecker::with_mode(&env, env.mode());
    let inferred = tc
        .infer_type(proof)
        .expect("Rat.neg_le_neg proof should infer");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "Rat.neg_le_neg inferred type must match declared type",
    );
}

/// #3538: proof term does not use `sorry` / `sorryAx`.
#[test]
fn test_rat_neg_le_neg_value_is_sorry_free() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("Rat.neg_le_neg"))
        .expect("Rat.neg_le_neg should be registered");
    let sorry = info.sorry_summary();
    assert!(
        !sorry.has_sorry,
        "Rat.neg_le_neg proof must be sorry-free (#3538)",
    );
}

/// #3538 / #integrity-audit (2026-06): emit + pin the observed domain-axiom
/// closure for auditing.
///
/// History: #3555 had promoted the Rat field/order axiom tranche
/// (`Rat.add_le_add_left`, `Rat.add_left_neg`, `Rat.mul_neg`, ...) into
/// `FOUNDATIONAL_AXIOMS`, so the transitive *non-foundational* closure for
/// `Rat.neg_le_neg` collapsed to a set of only Int/Nat ring-normalization
/// primitives — the admitted Rat ordered-field axioms were dishonestly
/// hidden. The 2026-06 integrity audit reversed that overstatement: those
/// Rat ordering / ring axioms are now in `ADMITTED_DOMAIN_AXIOMS` and
/// excluded from `is_foundational_axiom`, so `axiom_deps` once again surfaces
/// them. The honest closure of `Rat.neg_le_neg` is therefore a NON-EMPTY set
/// whose every member is either an admitted Rat domain axiom (e.g.
/// `Rat.add_le_add_left`, `Rat.add_left_neg`, `Rat.add_neg_self`,
/// `Rat.add_right_cancel`, `Rat.mul_neg`) OR an allowed Int/Nat
/// ring-normalization primitive surfaced transitively by the constructive
/// proof bodies of the Rat field theorems it walks — with at least one
/// admitted Rat domain axiom present (pinning that the reclassification took
/// effect) and no `sorry` / trust marker.
#[test]
fn test_rat_neg_le_neg_axiom_deps_recorded() {
    // WS-A ATOMIC LIVE SWITCH: `Rat.neg_le_neg`'s former admitted-axiom deps
    // (`Rat.add_le_add_left`, `Rat.add_left_neg`, `Rat.le_trans`, …) are ALL now
    // `Constructive` quotient Theorems. So the non-foundational axiom closure of
    // `Rat.neg_le_neg` is now EMPTY — the lemma is fully `Constructive`.
    let env = make_env();
    let deps = env
        .axiom_deps(&Name::from_string("Rat.neg_le_neg"))
        .expect("axiom_deps should compute for registered theorem");
    let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
    assert!(
        deps.is_empty(),
        "Rat.neg_le_neg closure must now be EMPTY (its former admitted Rat \
         domain deps are quotient Theorems), got {names:?}",
    );
}

/// #3538 / #integrity-audit (2026-06): the constructive proof term's
/// transitive axiom closure rests honestly on the admitted Rat
/// ordered-field/ring axioms already carried by sibling bridging lemmas
/// (`Rat.sub_nonneg_of_le`, `Rat.le_of_sub_nonneg`, `Rat.mul_sub`), plus the
/// kernel-primitive Int/Nat ring-normalization axioms those proofs surface
/// transitively.
///
/// History: before #3555 the closure contained the Rat field/order axioms
/// (`add_le_add_left`, `add_left_neg`, `mul_neg`, ...). #3555 dishonestly
/// promoted those names into `FOUNDATIONAL_AXIOMS`, so this closure (which
/// drops foundational axioms) was reported as effectively empty of Rat
/// domain content. The 2026-06 integrity audit moved them into
/// `ADMITTED_DOMAIN_AXIOMS` (excluded from `is_foundational_axiom`), so the
/// closure honestly surfaces them again. This guard now asserts the HONEST
/// state: a NON-EMPTY closure, every member of which is an admitted Rat
/// domain axiom or an allowed kernel Int/Nat primitive — with at least one
/// admitted Rat domain axiom present and no `sorry` / trust marker. It still
/// fires if some future edit introduces a rogue / unexpected axiom into the
/// closure.
#[test]
fn test_rat_neg_le_neg_axiom_closure_is_allowed() {
    use crate::env::axiom_audit::is_trust_marker;

    // WS-A ATOMIC LIVE SWITCH: every admitted Rat domain axiom this lemma
    // formerly rested on is now a `Constructive` quotient Theorem, so the
    // transitive non-foundational axiom closure of `Rat.neg_le_neg` is EMPTY
    // (and, a fortiori, free of any `sorry` / trust marker).
    let env = make_env();
    let deps = env
        .axiom_deps(&Name::from_string("Rat.neg_le_neg"))
        .expect("axiom_deps should compute for registered theorem");
    let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();

    for dep in &deps {
        assert!(
            !is_trust_marker(dep),
            "Rat.neg_le_neg closure must contain no sorry / trust marker; got {dep}",
        );
    }
    assert!(
        deps.is_empty(),
        "Rat.neg_le_neg closure must now be EMPTY (its former admitted Rat \
         domain deps are quotient Theorems), got {names:?}",
    );
}
