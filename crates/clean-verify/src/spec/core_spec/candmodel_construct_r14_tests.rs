// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R14 tests — the two operations, the two semantic lemmas, their
//! discriminating witnesses, and the refusal that measures what weakening does.

use super::*;
use crate::test_utils::parse_check;

/// Register R14 into a freshly-built substitution spec if the bundle stage has
/// not already done it. Lets every test below run identically before and after
/// the stage is wired into `bundles.rs`.
fn r14_spec() -> Specification {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    if spec.definitions().contains_key("wk_psub") {
        return spec;
    }
    spec.add_candmodel_construct_r14()
        .expect("R14 should register into the substitution spec");
    spec
}

/// Parse every generated source. Microseconds, versus a whole spec build.
#[test]
fn test_candmodel_r14_sources_parse() {
    for (name, src) in r14_all_sources() {
        parse_check(&src).unwrap_or_else(|e| panic!("R14 source {name} does not parse: {e}"));
    }
    parse_check(&probe_wk_lift_wrong_shape()).expect("the negative-control probe must parse");
    parse_check(&probe_cast_irrel_refl()).expect("the irrelevance probe must parse");
}

/// No name registered twice, and the load-bearing ones are all present.
#[test]
fn test_candmodel_r14_names_are_unique() {
    let mut seen = std::collections::BTreeSet::new();
    for (name, _) in r14_all_sources() {
        assert!(seen.insert(name.clone()), "R14 registers {name} twice");
    }
    for required in [
        "skins",
        "wk_lift",
        "wk_lift0",
        "wk_up",
        "wk_psub",
        "wk_inst",
        "venvLiftD",
        "venvSubD",
        "r14_val_lift",
        "r14_val_psub",
        "r14_val_inst",
        "r14_val_beta",
    ] {
        assert!(seen.contains(required), "R14 lost {required}");
    }
}

/// ITERATION TOOL. Registers the whole table into a substitution spec and
/// reports EVERY failure in one message instead of dying on the first — the
/// R13 pattern, and the reason a rung this size fits in a handful of cycles.
#[test]
fn test_candmodel_r14_scratch_elaborates() {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    if spec.definitions().contains_key("wk_psub") {
        return;
    }
    let mut failures: Vec<String> = Vec::new();
    for item in r14_items() {
        match item {
            R14Item::Def { name, src } => {
                if let Err(e) = spec.add_recursive_def(&src, "r14 scratch") {
                    failures.push(format!("DEF {name}: {e}"));
                }
            }
            R14Item::Thm { name, ty, val } => {
                if let Err(e) = add_thm(&mut spec, &name, ty, val, &[], "r14 scratch") {
                    failures.push(format!("THM {name}: {e}"));
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "R14 registration failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// Every R14 constant is registered and every theorem re-verifies.
#[test]
fn test_candmodel_r14_registered_and_reverifies() {
    let spec = r14_spec();
    for (name, _) in r14_all_sources() {
        assert!(
            spec.definitions().contains_key(&name),
            "R14 constant {name} is not registered"
        );
    }
    for item in r14_items() {
        if let R14Item::Thm { name, .. } = item {
            spec.verify_definition(&name)
                .unwrap_or_else(|e| panic!("R14 theorem {name} does not re-verify: {e:?}"));
        }
    }
}

/// The OPERATIONS must delta-unfold. `r14_val_lift`'s var case has to reduce
/// `wk_lift` through `WK.rec` down to `r14_wk_lift_var`, and `wk_up`'s succ
/// branch has to expose `wk_lift0`. An `add_definition` registration lowers to
/// `Declaration::Opaque` and stops that dead — the elaborator fact R12 paid an
/// elaboration cycle to learn. This asserts the whole operation spine is
/// registered as reducible definitions.
#[test]
fn test_candmodel_r14_operations_delta_unfold() {
    use clean_kernel::{ConstantKind, Name};
    let spec = r14_spec();
    for op in [
        "skins",
        "r14_wkpos",
        "r14_wkCastT",
        "r14_wkCastS",
        "r14_vdCast",
        "r14_wk_lift_var",
        "wk_lift",
        "wk_lift0",
        "wk_up",
        "wk_psub",
        "r14_scons_typed",
        "wk_inst",
        "venvLiftD",
        "venvSubD",
    ] {
        let c = spec
            .env()
            .get_const(&Name::from_string(op))
            .unwrap_or_else(|| panic!("{op} missing from the R14 environment"));
        assert_eq!(
            c.kind,
            ConstantKind::Definition,
            "{op} must be a reducible Definition; Opaque or Theorem stops the reduction every \
             later R14 proof depends on"
        );
    }
}

/// CENSUS. The computed axiom closure — by kernel ground truth, not by the
/// declared `axiom_deps` field — must be empty for every headline constant.
/// `r13_venvD_funext` reaches `Quot.sound` and the quotient formers, and
/// `Environment::axiom_deps` short-circuits those as kernel-foundational.
#[test]
fn test_candmodel_r14_axiom_closure_is_empty() {
    let spec = r14_spec();
    for name in [
        "r14_skins_idx",
        "r14_sval_cast_term",
        "r14_sval_cast_shape",
        "r14_vdCast_refl",
        "r14_vdCast_irrel",
        "r14_cast_idx",
        "r14_venvLift_at",
        "r14_val_lift",
        "r14_val_lift0",
        "r14_val_psub",
        "r14_val_inst",
        "r14_val_beta",
        "r14_sval_transports_real_beta",
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

/// CENSUS, by kernel ground truth, over the bundle R14 actually changes.
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
fn test_candmodel_r14_admits_no_new_census_axiom() {
    let spec = r14_spec();
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
        "R14 newly admitted kernel axioms into the substitution bundle: {newly:?}"
    );
}

/// MEASUREMENT, not a claim. The weakened derivation of the old variable is at
/// shape `Sk.ty`, and the kernel REFUSES the same construction claimed at the
/// INSERTED slot's shape `Sk.kd Sk.ty`. Without this, `r14_wk_lift_shifts`
/// would be compatible with `wk_lift` returning a derivation that had confused
/// the two slots.
#[test]
fn test_candmodel_r14_weakening_does_not_confuse_the_inserted_slot() {
    let mut spec = r14_spec();
    assert!(
        spec.add_recursive_def(&probe_wk_lift_wrong_shape(), "negative control")
            .is_err(),
        "the weakened derivation typechecked at the INSERTED slot's shape — wk_lift is confusing \
         the inserted slot with the shifted variable and r14_wk_lift_shifts witnesses nothing"
    );
}

/// MEASUREMENT, and the first spelling of this test was itself REFUTED, so read
/// what it actually says. The irrelevance step `r14_vdCast_irrel` performs — two
/// casts along two proofs of the SAME shape equality agree — IS closable by
/// `Eq.refl`, because the kernel applies proof irrelevance; this asserts that
/// the probe registers cleanly. What was refused (measured 2026-08-27) is the
/// identical step written INLINE as the base minor of `r14_cast_idx`'s
/// `Eq.rec`: there the ELABORATOR's unifier compared the two proof binders as
/// free variables and reported `fvar mismatch`. So the fact is a POSITION
/// dependence — an irrelevance step must be a standalone, kernel-checked
/// constant that the elaborated proof term APPLIES — and that is why
/// `r14_vdCast_irrel` exists as its own constant instead of being inlined. If
/// the standalone form ever stops being accepted, this rung's structure is
/// wrong and this test says so.
#[test]
fn test_candmodel_r14_cast_irrelevance_needs_a_standalone_constant() {
    let mut spec = r14_spec();
    spec.add_recursive_def(&probe_cast_irrel_refl(), "position control")
        .expect(
            "the kernel no longer identifies two proofs of the same Prop in argument position, \
             so r14_vdCast_irrel's standalone factoring is not the right fix and the rung's \
             cast layer needs re-deriving",
        );
}

/// The `skins` laws the whole rung's transport-freeness rests on really are
/// `Eq.refl`. A future re-spelling of `skins` with a decidable comparison would
/// leave these provable only by `funext`, and every binder case of `wk_lift`
/// would silently start needing a transport.
#[test]
fn test_candmodel_r14_skins_laws_are_definitional() {
    assert!(
        VAL_SKINS_ZERO.contains("Eq.refl") && VAL_SKINS_SUCC.contains("Eq.refl"),
        "the skins laws are no longer definitional"
    );
    assert!(
        SRC_SKINS.contains("Nat.rec"),
        "skins must recurse on the CUTOFF; a decidable comparison re-opens every transport site"
    );
    let _ = r14_spec();
}

/// R12's TWO HORNS are about universes and about structural recursion.
/// Substitution is neither, exactly as extensionality was neither. Re-asserted
/// from R12's own source tables, as `test_candmodel_r13_leaves_r12_horns_
/// standing` does, so a future edit that quietly weakens either horn fails here
/// too.
#[test]
fn test_candmodel_r14_leaves_r12_horns_standing() {
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

/// The drift-proof premise gate. Derives the name set from R14's OWN table
/// rather than from a hand-written list. The hand-written list in
/// `premise_witness::tests::test_candmodel_ladder_premises_are_witnessed` is the
/// standing-rule record; this is the guard.
#[test]
fn test_candmodel_r14_introduces_no_unwitnessed_premise() {
    let spec = r14_spec();
    let mine: std::collections::BTreeSet<String> =
        r14_all_sources().into_iter().map(|(n, _)| n).collect();
    let live: Vec<String> = crate::premise_witness::unwitnessed_premises(&spec)
        .into_iter()
        .map(|u| u.predicate)
        .filter(|p| mine.contains(p))
        .collect();
    assert!(
        live.is_empty(),
        "R14 assumes predicates nothing concludes: {live:?}"
    );
}
