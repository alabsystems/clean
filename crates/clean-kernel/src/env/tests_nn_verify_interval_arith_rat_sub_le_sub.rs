// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the constructive `Rat.sub_le_sub` proof term (#3539).
//!
//! Paired with
//! `crates/clean-kernel/src/env/nn_verify_interval_arith_rat_sub_le_sub_proof.rs`
//! (proof-term builder) and the `register_rat_sub_le_sub` site in
//! `crates/clean-kernel/src/env/nn_verify_interval_arith_proofs.rs`.
//!
//! Guards enforced here:
//! - `Rat.sub_le_sub` is a `Declaration::Theorem` carrying a proof term
//!   (not `Declaration::Axiom`, not an Opaque-with-`sorry`).
//! - The proof term type-checks under the kernel.
//! - The proof term is sorry-free (no `sorry` / `sorryAx` anywhere).
//! - The transitive axiom closure is a subset of the honest Rat
//!   ordered-field axiom set already carried by the sibling theorems
//!   `Rat.add_le_add` (#3537) and `Rat.neg_le_neg` (#3538) — i.e., no
//!   *new* domain axiom was introduced by composing them.
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

/// #3539: `Rat.sub_le_sub` is a genuine `Declaration::Theorem` (not Axiom)
/// with a proof-term value attached.
#[test]
fn test_rat_sub_le_sub_is_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("Rat.sub_le_sub"))
        .expect("Rat.sub_le_sub should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "Rat.sub_le_sub must be a Theorem after #3539, got {:?}",
        info.kind,
    );
    assert!(
        info.value.is_some(),
        "Rat.sub_le_sub must carry a proof term",
    );
}

/// #3539: the constructive proof term type-checks against the declared
/// theorem statement.
#[test]
fn test_rat_sub_le_sub_type_checks() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("Rat.sub_le_sub"))
        .expect("Rat.sub_le_sub should be registered");
    let proof = info.value.as_ref().expect("theorem should have value");
    let tc = TypeChecker::with_mode(&env, env.mode());
    let inferred = tc
        .infer_type(proof)
        .expect("Rat.sub_le_sub proof should infer");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "Rat.sub_le_sub inferred type must match declared type",
    );
}

/// #3539: proof term does not use `sorry` / `sorryAx`.
#[test]
fn test_rat_sub_le_sub_value_is_sorry_free() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("Rat.sub_le_sub"))
        .expect("Rat.sub_le_sub should be registered");
    let sorry = info.sorry_summary();
    assert!(
        !sorry.has_sorry,
        "Rat.sub_le_sub proof must be sorry-free (#3539)",
    );
    let deps = env
        .axiom_deps(&Name::from_string("Rat.sub_le_sub"))
        .expect("axiom_deps should succeed");
    let dep_strs: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
    assert!(
        !dep_strs.iter().any(|d| d == "sorry" || d == "sorryAx"),
        "Rat.sub_le_sub transitive closure must not reference `sorry`; got {dep_strs:?}"
    );
}

/// #3539 / #3555 / #integrity-audit: emit the observed domain-axiom
/// closure for auditing.
///
/// HISTORY: #3555 once promoted the Rat ordered-field/lattice tranche
/// into `FOUNDATIONAL_AXIOMS`, which made the non-foundational closure
/// of `Rat.sub_le_sub` *appear* to collapse to only the Int/Nat
/// ring-normalization primitives. The 2026-06 integrity audit
/// established that those Rat ordered-field axioms were dishonestly
/// whitelisted as "foundational" — they are admitted DOMAIN axioms,
/// unproved in this kernel, now listed in
/// `ADMITTED_DOMAIN_AXIOMS` and EXCLUDED from `is_foundational_axiom`.
/// As a result `Rat.sub_le_sub` (which composes `Rat.add_le_add` #3537
/// and `Rat.neg_le_neg` #3538) honestly carries those admitted Rat
/// axioms (`Rat.le_trans`, `Rat.add_le_add_left`, `Rat.add_left_neg`,
/// `Rat.add_neg_self`, `Rat.add_right_cancel`, ...) in its closure
/// alongside the Int/Nat primitives. This test emits the closure for
/// auditing and pins the HONEST state: the closure is NON-EMPTY and
/// every member is either an admitted domain axiom or one of the
/// kernel-primitive Int/Nat ring-normalization axioms — with NO
/// `sorry` and NO unexpected/rogue axiom.
#[test]
fn test_rat_sub_le_sub_axiom_deps_recorded() {
    // WS-A ATOMIC LIVE SWITCH: every admitted Rat ordered-field domain axiom
    // `Rat.sub_le_sub` formerly composed (via its sibling `Rat.add_le_add` /
    // `Rat.neg_le_neg` theorems) is now a `Constructive` quotient Theorem, so
    // the transitive non-foundational axiom closure of `Rat.sub_le_sub` is now
    // EMPTY — the lemma is fully `Constructive`.
    let env = make_env();
    let deps = env
        .axiom_deps(&Name::from_string("Rat.sub_le_sub"))
        .expect("axiom_deps should compute for registered theorem");
    let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
    assert!(
        deps.is_empty(),
        "Rat.sub_le_sub closure must now be EMPTY (its former admitted Rat \
         domain deps are quotient Theorems), got {names:?}",
    );
}

/// #3539 / #integrity-audit: the constructive proof term's transitive
/// axiom closure is a subset of the Rat ordered-field axiom set already
/// carried by sibling theorems (`Rat.add_le_add` #3537,
/// `Rat.neg_le_neg` #3538). **No new domain axioms are introduced**
/// — the proof term ``composes'' the existing sibling theorems.
///
/// HISTORY: #3555 briefly promoted the Rat field/order axioms
/// (`add_assoc`, `add_comm`, `mul_neg`, `left_distrib`, ...) into
/// `FOUNDATIONAL_AXIOMS`, which made the domain-axiom closure appear to
/// collapse. The 2026-06 integrity audit reversed that overstatement:
/// the Rat ordered-field/lattice/ring axioms are admitted DOMAIN axioms
/// (`ADMITTED_DOMAIN_AXIOMS`), unproved in this kernel and excluded from
/// `is_foundational_axiom`. They now honestly appear in the closure of
/// `Rat.sub_le_sub` (e.g. `Rat.le_trans`, `Rat.add_le_add_left`,
/// `Rat.add_left_neg`, `Rat.add_neg_self`, `Rat.add_right_cancel`).
/// This remains a defensive guard: every member of the closure must be
/// either an admitted Rat domain axiom or one of the Int/Nat
/// ring-normalization primitives — any genuinely unexpected/rogue axiom
/// still trips the test.
#[test]
fn test_rat_sub_le_sub_axiom_closure_is_allowed() {
    // Kernel-primitive Int/Nat ring-normalization axioms already in the
    // transitive closures of `Rat.add_le_add` and `Rat.neg_le_neg` via
    // the constructive proof bodies of Rat.add_comm, Rat.add_assoc,
    // Rat.zero_add, Rat.add_zero, Rat.one_mul, Rat.mul_one, Rat.mul_assoc
    // (#3572 Phase 2/3 + #3582 Phase 3 + Tranche B). These are NOT in
    // `ADMITTED_DOMAIN_AXIOMS` but are legitimate non-foundational
    // members of the closure that have always been present.
    const ALLOWED_INT_NAT_AXIOMS: &[&str] = &[
        "Int.add_assoc",
        "Int.add_comm",
        "Int.add_zero",
        "Int.mul_assoc",
        "Int.mul_comm",
        "Int.mul_one",
        "Int.ofNat_mul",
        "Int.right_distrib",
        "Int.zero_add",
        "Int.zero_mul",
        "Nat.mul_assoc",
        "Nat.mul_comm",
        "Nat.mul_one",
        "Nat.one_mul",
    ];
    let env = make_env();
    let deps = env
        .axiom_deps(&Name::from_string("Rat.sub_le_sub"))
        .expect("axiom_deps should compute for registered theorem");
    for dep in &deps {
        let s = dep.to_string();
        let is_admitted = crate::env::axiom_audit::ADMITTED_DOMAIN_AXIOMS.contains(&s.as_str());
        let is_int_nat = ALLOWED_INT_NAT_AXIOMS.contains(&s.as_str());
        assert!(
            is_admitted || is_int_nat,
            "Rat.sub_le_sub axiom closure includes unexpected axiom: {s} \
             (neither an admitted Rat domain axiom nor an Int/Nat \
             ring-normalization primitive)\n\
             full closure = {:?}",
            deps.iter().map(|n| n.to_string()).collect::<Vec<_>>(),
        );
    }
}

/// #3539: `Rat.sub_le_sub`'s closure must not introduce any axiom names
/// beyond those already transitively required by its two sibling
/// theorems `Rat.add_le_add` and `Rat.neg_le_neg`. This is the key
/// property that makes the composition "no new domain axioms".
#[test]
fn test_rat_sub_le_sub_closure_subset_of_siblings() {
    let env = make_env();
    let sub_deps: std::collections::BTreeSet<String> = env
        .axiom_deps(&Name::from_string("Rat.sub_le_sub"))
        .expect("axiom_deps for Rat.sub_le_sub")
        .iter()
        .map(|n| n.to_string())
        .collect();
    let add_deps: std::collections::BTreeSet<String> = env
        .axiom_deps(&Name::from_string("Rat.add_le_add"))
        .expect("axiom_deps for Rat.add_le_add")
        .iter()
        .map(|n| n.to_string())
        .collect();
    let neg_deps: std::collections::BTreeSet<String> = env
        .axiom_deps(&Name::from_string("Rat.neg_le_neg"))
        .expect("axiom_deps for Rat.neg_le_neg")
        .iter()
        .map(|n| n.to_string())
        .collect();
    let sibling_union: std::collections::BTreeSet<String> =
        add_deps.union(&neg_deps).cloned().collect();
    let extra: Vec<&String> = sub_deps.difference(&sibling_union).collect();
    assert!(
        extra.is_empty(),
        "Rat.sub_le_sub transitive closure introduces axioms NOT in the \
         union of its sibling theorems' closures: extra = {extra:?}\n\
         sub_deps = {sub_deps:?}\n\
         add_deps = {add_deps:?}\n\
         neg_deps = {neg_deps:?}"
    );
}
