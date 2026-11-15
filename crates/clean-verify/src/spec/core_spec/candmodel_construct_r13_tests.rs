// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R13 tests — the funext derivation, its non-vacuity, and the two refusals
//! that measure what funext is doing.

use super::*;
use crate::test_utils::parse_check;

/// Register R13 into a freshly-built substitution spec if the bundle stage has
/// not already done it. Lets every test below run identically before and after
/// the stage is wired into `bundles.rs`.
fn r13_spec() -> Specification {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    if spec.definitions().contains_key("spec_funext") {
        return spec;
    }
    spec.add_candmodel_construct_r13()
        .expect("R13 should register into the substitution spec");
    spec
}

/// Parse every generated source. Microseconds, versus a whole spec build.
#[test]
fn test_candmodel_r13_sources_parse() {
    for (name, src) in r13_all_sources() {
        parse_check(&src).unwrap_or_else(|e| panic!("R13 source {name} does not parse: {e}"));
    }
    parse_check(&probe_pointwise_refl()).expect("the negative-control probe must parse");
}

/// No name registered twice, and the load-bearing ones are all present.
#[test]
fn test_candmodel_r13_names_are_unique() {
    let mut seen = std::collections::BTreeSet::new();
    for (name, _) in r13_all_sources() {
        assert!(seen.insert(name.clone()), "R13 registers {name} twice");
    }
    for required in [
        "spec_fneq",
        "spec_fnapp",
        "spec_quot_fn",
        "spec_funext",
        "spec_funext_nd",
        "spec_funext_witness",
        "r13_vd_arr_funext",
        "r13_venvD_funext",
        "r13_sval_env_congr",
        "r13_piCandDep_fn_congr",
        "r13_wkPiDep_env_congr",
    ] {
        assert!(seen.contains(required), "R13 lost {required}");
    }
}

/// The derivation must route through the quotient, not through anything else.
/// A future edit that "simplifies" `spec_funext` into an axiom, or into a
/// `sorry`, or into `Eq.refl`, changes these strings.
#[test]
fn test_candmodel_r13_derivation_routes_through_quot_sound() {
    let v = val_funext();
    for needed in ["@Quot.sound", "@Quot.mk", "Eq.cong", "spec_fnapp"] {
        assert!(
            v.contains(needed),
            "spec_funext's proof no longer uses {needed}: {v}"
        );
    }
    let app = src_fnapp();
    assert!(
        app.contains("@Quot.lift"),
        "spec_fnapp must extract through Quot.lift: {app}"
    );
    assert!(
        !v.contains("sorry") && !v.contains("Classical") && !v.contains("propext"),
        "spec_funext's proof reaches outside the quotient toolkit: {v}"
    );
}

/// ITERATION TOOL. Registers both tables into a substitution spec and reports
/// EVERY failure in one message instead of dying on the first.
#[test]
fn test_candmodel_r13_scratch_elaborates() {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    if spec.definitions().contains_key("spec_funext") {
        return;
    }
    let mut failures: Vec<String> = Vec::new();
    if let Err(e) = spec.env_mut().init_funext() {
        panic!("R13 cannot install the quotient bundle: {e}");
    }
    for (kind, name, src) in r13_decl_sources() {
        let r = match kind {
            "inductive" => spec.add_inductive(&src, "r13 scratch"),
            _ => spec.add_recursive_def(&src, "r13 scratch"),
        };
        if let Err(e) = r {
            failures.push(format!("DECL {name}: {e}"));
        }
    }
    for (name, ty, val) in r13_theorem_sources() {
        if let Err(e) = add_thm(&mut spec, &name, ty, val, &[], "r13 scratch") {
            failures.push(format!("THM {name}: {e}"));
        }
    }
    assert!(
        failures.is_empty(),
        "R13 registration failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// Every R13 constant is registered and every theorem re-verifies.
#[test]
fn test_candmodel_r13_registered_and_reverifies() {
    let spec = r13_spec();
    for (name, _) in r13_all_sources() {
        assert!(
            spec.definitions().contains_key(&name),
            "R13 constant {name} is not registered"
        );
    }
    for (name, _, _) in r13_theorem_sources() {
        spec.verify_definition(&name)
            .unwrap_or_else(|e| panic!("R13 theorem {name} does not re-verify: {e:?}"));
    }
}

/// CENSUS. `spec_funext`'s computed axiom closure — by kernel ground truth, not
/// by the declared `axiom_deps` field — must be empty: `Quot.sound` and the
/// quotient primitives are kernel-foundational and short-circuited by
/// `Environment::axiom_deps`, and nothing else is reached.
#[test]
fn test_candmodel_r13_axiom_closure_is_empty() {
    let spec = r13_spec();
    for name in [
        "spec_funext",
        "spec_funext_nd",
        "spec_funext_witness",
        "r13_vd_arr_funext",
        "r13_venvD_funext",
        "r13_sval_env_congr",
        "r13_piCandDep_fn_congr",
        "r13_wkPiDep_env_congr",
    ] {
        let closure = crate::spec_axiom_closure::computed_axiom_closure(&spec, name);
        assert!(
            closure.is_empty(),
            "{name} rests on non-foundational axioms: {closure:?}"
        );
        let markers = crate::spec_axiom_closure::computed_trust_markers(&spec, name);
        assert!(
            markers.is_empty(),
            "{name} reaches a trust marker: {markers:?}"
        );
    }
}

/// The quotient bundle really did arrive, and `funext` arrived as a VALUE-
/// BEARING theorem rather than as a fresh axiom. If a future kernel change
/// demotes it, the census would move silently; this catches it here.
#[test]
fn test_candmodel_r13_quotient_bundle_is_present_and_funext_is_not_an_axiom() {
    use clean_kernel::{ConstantKind, Name};
    let spec = r13_spec();
    for prim in ["Quot", "Quot.mk", "Quot.lift", "Quot.ind", "Quot.sound"] {
        assert!(
            spec.env().get_const(&Name::from_string(prim)).is_some(),
            "{prim} missing from the R13 environment"
        );
    }
    let funext = spec
        .env()
        .get_const(&Name::from_string("funext"))
        .expect("init_funext must register the kernel-side derivation");
    assert_ne!(
        funext.kind,
        ConstantKind::Axiom,
        "the kernel's funext must stay a CHECKED theorem derived from Quot.sound, never an axiom"
    );
}

/// CENSUS, by kernel ground truth, over the bundle R13 actually changes.
///
/// `tests/axiom_ratchet.rs::no_new_admitted_axioms_in_spec` is the
/// authoritative gate. **It fits on this box, and the figure that said
/// otherwise was false** — measured 2026-09-17: that gate over the FULL spec
/// runs in 18m30s at **2.75 GB peak RSS** under `heavy_gate.sh run 4`. The
/// "28.87 GB peak RSS" this comment used to cite was a CARRIED peak, never a
/// measurement (`_prior_peak_rss_gb` raises a weight and never lowers it), and
/// `docs/archive/CLAUDE_MD_HISTORY.md` had already retracted it. It cited
/// `data/suite_state/clean-verify__test__axiom_ratchet.json`, the very file
/// that refutes it — 2.04 GB over 569 samples. Check the file a sentence
/// cites, not only its number.
///
/// This subset check stays as the FAST per-rung one, against the substitution
/// bundle that is the only environment this rung modifies. It is NOT a
/// substitute for the authoritative gate, which should be run before landing.
#[test]
fn test_candmodel_r13_admits_no_new_census_axiom() {
    let spec = r13_spec();
    const GOLDEN_JSON: &str = include_str!("../../../../../data/clean_verify_axiom_ratchet.json");
    let golden: std::collections::BTreeSet<String> = {
        let v: serde_json::Value =
            serde_json::from_str(GOLDEN_JSON).expect("axiom ratchet golden must parse");
        v["axioms"]
            .as_array()
            .expect("golden has an `axioms` array")
            .iter()
            .filter_map(|e| e["name"].as_str().map(str::to_string))
            .collect()
    };
    let live: Vec<String> = crate::axiom_ratchet::live_env_axioms(&spec)
        .into_iter()
        .map(|a| a.name)
        .collect();
    let newly = crate::axiom_ratchet::newly_admitted_axioms(&live, &golden);
    assert!(
        newly.is_empty(),
        "R13 newly admitted kernel axioms into the substitution bundle: {newly:?}"
    );
    for prim in ["Quot", "Quot.mk", "Quot.lift", "Quot.ind", "Quot.sound"] {
        assert!(
            live.iter().any(|n| n == prim),
            "{prim} should be a live env axiom of the R13 bundle"
        );
        assert!(
            golden.contains(prim),
            "{prim} should already be in the golden"
        );
    }
    assert!(
        !live.iter().any(|n| n == "funext"),
        "funext must NOT be a live env axiom — it is a checked theorem derived from Quot.sound"
    );
}

/// MEASUREMENT, not a claim: `Eq.refl` at `spec_funext_witness`'s statement is
/// REJECTED by the kernel. `Nat.add` recurses on its second argument, so
/// `fun n => Nat.add Nat.zero n` is stuck on the variable and is not
/// definitionally `fun n => n`. Without this, the witness would be compatible
/// with funext having done nothing.
#[test]
fn test_candmodel_r13_reflexivity_is_refused_at_the_witness() {
    let mut spec = r13_spec();
    let refused = spec.add_definition(SpecDefinition {
        name: "r13_refl_probe".to_string(),
        type_src: TY_FUNEXT_WITNESS.to_string(),
        value_src: Some(VAL_FUNEXT_WITNESS_REFL_PROBE.to_string()),
        is_axiom: false,
        description: "negative control".to_string(),
        category: AxiomCategory::DerivedLemma,
        proof_status: ProofStatus::DerivedProved,
        elaborated_type: None,
        elaborated_value: None,
        dependencies: None,
        axiom_deps: HashSet::new(),
    });
    assert!(
        refused.is_err(),
        "Eq.refl closed the funext witness — the two functions are definitionally equal after \
         all, and spec_funext_witness is not a non-vacuity witness"
    );
}

/// MEASUREMENT. The general statement, with the pointwise hypothesis IN HAND,
/// is still not closable by reflexivity — this is R12's "pointwise congruence
/// does not substitute" as a machine-checked refusal rather than as prose.
#[test]
fn test_candmodel_r13_pointwise_does_not_substitute() {
    let mut spec = r13_spec();
    assert!(
        spec.add_recursive_def(&probe_pointwise_refl(), "negative control")
            .is_err(),
        "the pointwise hypothesis substituted definitionally — R12's stated obstruction is not \
         real and R13's derivation is unnecessary"
    );
}

/// R12's TWO HORNS are about universes and about structural recursion.
/// Extensionality is neither, and R13 must not be read as touching them. These
/// are R12's own source facts, re-asserted from R12's tables so a future edit
/// that quietly weakens either horn fails here too.
#[test]
fn test_candmodel_r13_leaves_r12_horns_standing() {
    use super::super::candmodel_construct_r12_src as r12;
    assert!(
        r12::SRC_PI_CAND_V.contains(": KExpr -> Type 1 :="),
        "HORN 1 (predicativity) no longer reads as one universe up"
    );
    let sval = r12::src_sval();
    let body = sval.split(":=").nth(1).expect("sval has a body");
    assert!(
        !body.contains("sval"),
        "HORN 2 (the recursion horn) no longer holds: sval's body became self-referential"
    );
}

/// The drift-proof premise gate. Derives the name set from R13's OWN tables
/// rather than from a hand-written list, and additionally checks `Quot` — the
/// value-less type former this rung newly puts in hypothesis position — so a
/// later edit that drops `spec_quot_fn` cannot go unnoticed. The hand-written
/// list in `premise_witness::tests::test_candmodel_ladder_premises_are_witnessed`
/// is the standing-rule record; this is the guard.
#[test]
fn test_candmodel_r13_introduces_no_unwitnessed_premise() {
    let spec = r13_spec();
    let mut mine: std::collections::BTreeSet<String> =
        r13_all_sources().into_iter().map(|(n, _)| n).collect();
    mine.insert("Quot".to_string());
    let live: Vec<String> = crate::premise_witness::unwitnessed_premises(&spec)
        .into_iter()
        .map(|u| u.predicate)
        .filter(|p| mine.contains(p))
        .collect();
    assert!(
        live.is_empty(),
        "R13 assumes predicates nothing concludes: {live:?}"
    );
}
