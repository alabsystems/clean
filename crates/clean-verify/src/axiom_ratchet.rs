// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! No-new-axioms ratchet for the clean-verify self-verification spec.
//!
//! ## Why this exists
//!
//! An *axiom* in the spec (a [`SpecDefinition`] with `is_axiom: true`) is an
//! ASSUMPTION the kernel does not check for truth — it only checks that the
//! statement is a well-formed type. Two FALSE axioms (`micro_whnf_beta`,
//! `micro_whnf_idempotent`) sat in the spec as `is_axiom: true` for a long time
//! before being caught and retired by hand (commit 11e047bd). Now that the
//! kernel sits at its 3-axiom bedrock (`Classical.choice`, `Quot.sound`,
//! `propext`) and the spec's admitted-axiom debt is actively being DRAINED, no
//! NEW admitted axiom should ever be added silently.
//!
//! ## What the ratchet guarantees
//!
//! The kernel side is already pinned fail-closed by
//! `golden_matches_live_axioms` (`data/soundness_tcb.json`). This module is the
//! analogous guard for the clean-verify spec: the checked-in golden
//! (`data/clean_verify_axiom_ratchet.json`) lists the FULL set of currently
//! admitted-axiom NAMES, and [`newly_admitted_axioms`] reports any LIVE axiom
//! name that is NOT in the golden.
//!
//! The semantics are deliberately **SUBSET, not equality**:
//!
//! - Adding a new admitted axiom → the live set acquires a name not in the
//!   golden → [`newly_admitted_axioms`] returns it → the ratchet test FAILS.
//!   Admitting an axiom therefore becomes an EXPLICIT, REVIEWED act: a developer
//!   must either prove it instead, or add the name to the golden with a
//!   justification (a visible, reviewable diff).
//! - Draining an axiom (proving it, demoting it from `is_axiom: true`) → the
//!   live set SHRINKS → it stays a subset of the golden → the ratchet still
//!   PASSES. The golden may legitimately list names that have since been
//!   drained; that is fine and expected (the ongoing drain must never be
//!   blocked).
//!
//! ## Census by kernel GROUND TRUTH, not the `is_axiom` flag
//!
//! The authoritative census is [`live_env_axioms`]: it walks the kernel
//! [`Specification::env`] for every constant the kernel holds as
//! [`ConstantKind::Axiom`] (value-less, taken on faith). This is what the kernel
//! literally assumes — and it closes a hole the original flag-based
//! [`live_admitted_axioms`] could not see. `prepare_definition_decl`
//! (`spec/definition_registration.rs`) lowers a `SpecDefinition` to
//! `Declaration::Axiom` SOLELY when the value is absent, NEVER consulting the
//! `is_axiom` flag. So a `{is_axiom:false, value_src:None}` def becomes a GENUINE
//! kernel axiom that the flag-based census never reports (C1), and axioms
//! injected straight into the env via `env_mut().add_decl` have no
//! `SpecDefinition` at all (M1). The env census subsumes both.
//!
//! The definitional-disagreement gate uses the same live
//! [`ConstantKind::Axiom`] source of truth. It cross-checks every spec-marked
//! axiom one-to-one against that census, fails closed on metadata/kind/type
//! divergence, and separately reports environment-only kernel foundations and
//! trust-marker tripwires.

use std::collections::BTreeSet;

use clean_kernel::ConstantKind;

use crate::spec::{AxiomCategory, Specification};

/// A single live admitted-axiom census entry (a [`crate::spec::SpecDefinition`]
/// with `is_axiom: true`), recorded with its tracking category so the golden
/// can distinguish the irreducible [`AxiomCategory::FoundationalRule`]
/// inference rules from the [`AxiomCategory::HelperAxiom`] debt that is being
/// drained.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdmittedAxiom {
    /// The spec definition name.
    pub name: String,
    /// Tracking category at the time of the census.
    pub category: AxiomCategory,
}

/// Human-readable category label used in the golden file and diagnostics.
#[must_use]
pub fn category_label(category: AxiomCategory) -> &'static str {
    match category {
        AxiomCategory::FoundationalRule => "FoundationalRule",
        AxiomCategory::DerivedLemma => "DerivedLemma",
        AxiomCategory::HelperAxiom => "HelperAxiom",
        // `AxiomCategory` is `#[non_exhaustive]` for DOWNSTREAM crates only; in
        // its defining crate the match is exhaustive, so a catch-all arm here is
        // unreachable. Adding a variant therefore fails to compile at this site
        // — which is what the former `_ => "Other"` arm was trying to buy, only
        // now it is checked instead of silently mislabelling the new variant.
    }
}

/// Enumerate the LIVE admitted axioms of a built spec.
///
/// This reuses the spec's own definition census ([`Specification::definitions`])
/// — it does NOT re-parse source — so it sees exactly the axioms the running
/// system admits. Both the [`AxiomCategory::FoundationalRule`] inference rules
/// (which carry `is_axiom: true`) and the [`AxiomCategory::HelperAxiom`] /
/// [`AxiomCategory::DerivedLemma`] debt that is still `is_axiom: true` are
/// included. The result is sorted by name for deterministic output.
#[must_use]
pub fn live_admitted_axioms(spec: &Specification) -> Vec<AdmittedAxiom> {
    let mut out: Vec<AdmittedAxiom> = spec
        .definitions()
        .values()
        .filter(|def| def.is_axiom)
        .map(|def| AdmittedAxiom {
            name: def.name.clone(),
            category: def.category,
        })
        .collect();
    out.sort_by(|a, b| a.name.cmp(&b.name));
    out
}

/// Why a name is a *kernel* axiom (a value-less declaration the kernel takes on
/// faith), classified by joining the kernel env census against the spec's own
/// [`crate::spec::SpecDefinition`] map.
///
/// This is the ground-truth provenance behind [`EnvAdmittedAxiom`]. It exists
/// because the kernel admits ANY value-less declaration as a genuine
/// `Declaration::Axiom` — `prepare_definition_decl` keys SOLELY on
/// value-absence, NEVER on the `SpecDefinition::is_axiom` flag. So the flag and
/// the lowered kernel form can DIVERGE, and the env census must report each
/// shape:
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum AxiomOrigin {
    /// A [`crate::spec::SpecDefinition`] with `is_axiom: true` that lowered to a
    /// kernel axiom (the flag and the kernel agree — the historically-tracked
    /// [`AxiomCategory::FoundationalRule`] / [`AxiomCategory::HelperAxiom`] debt).
    FlagAxiom,
    /// A [`crate::spec::SpecDefinition`] with `is_axiom: false` that NONETHELESS
    /// lowered to a kernel axiom because it is value-less (no `value_src` and no
    /// `elaborated_value`) — the C1 hole: a "pending"/"proved"-flagged leaf that
    /// the kernel still treats as a bare assumption. The flag/lowered-form
    /// divergence the old flag-based ratchet never saw.
    PendingLeaf,
    /// A kernel axiom with NO backing [`crate::spec::SpecDefinition`] at all —
    /// injected straight into the env (e.g. the kernel's 3-axiom bedrock
    /// `propext` / `Quot.sound` / `Classical.choice`, the `Quot` quotient
    /// primitives, trust markers, or `init_*` env injections). The M1 blind spot
    /// the old defs-based ratchet never saw.
    EnvInjected,
}

/// Human-readable origin label used in the golden file and diagnostics.
#[must_use]
pub fn origin_label(origin: AxiomOrigin) -> &'static str {
    match origin {
        AxiomOrigin::FlagAxiom => "FlagAxiom",
        AxiomOrigin::PendingLeaf => "PendingLeaf",
        AxiomOrigin::EnvInjected => "EnvInjected",
        // `AxiomOrigin` is `#[non_exhaustive]` for DOWNSTREAM crates only; in its
        // defining crate this match is exhaustive, so a catch-all arm is
        // unreachable. A new variant fails to compile here rather than being
        // silently labelled "Other".
    }
}

/// A single live kernel-env axiom census entry: a constant the kernel env holds
/// as [`ConstantKind::Axiom`] (value-less, taken on faith), recorded with the
/// [`AxiomOrigin`] explaining how it became one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnvAdmittedAxiom {
    /// The kernel constant name.
    pub name: String,
    /// How the name became a kernel axiom (flag, pending-leaf divergence, or
    /// env-injected).
    pub origin: AxiomOrigin,
}

/// Classify one kernel-axiom NAME by its (optional) backing spec definition.
///
/// Decoupled from [`Specification`] so the guard logic can be unit-tested with a
/// synthetic env/def set (see the fail-closed demo): given the name of a
/// constant the kernel holds as [`ConstantKind::Axiom`] and the
/// `(is_axiom, value_present)` triple of its `SpecDefinition` (or `None` if no
/// spec def backs it), return the [`AxiomOrigin`].
///
/// `value_present` is `value_src.is_some() || elaborated_value.is_some()` — the
/// SAME value-absence predicate the kernel lowering uses in
/// `prepare_definition_decl`. A value-less def that lowered to a kernel axiom is
/// the C1 hole regardless of its `is_axiom` flag.
#[must_use]
pub fn classify_env_axiom(backing: Option<(bool, bool)>) -> AxiomOrigin {
    match backing {
        None => AxiomOrigin::EnvInjected,
        Some((is_axiom, _)) if is_axiom => AxiomOrigin::FlagAxiom,
        // is_axiom == false but the kernel still made it an axiom (value-less):
        // the flag/lowered-form divergence.
        Some(_) => AxiomOrigin::PendingLeaf,
    }
}

/// Enumerate the LIVE kernel-env axioms of a built spec — the GROUND TRUTH.
///
/// Walks [`Specification::env`]'s constants for every [`ConstantKind::Axiom`]
/// (the value-less declarations the kernel literally takes on faith), then joins
/// each name against the spec's [`crate::spec::SpecDefinition`] map to record its
/// [`AxiomOrigin`]. This is authoritative in a way the flag-based
/// [`live_admitted_axioms`] is NOT: it sees
///
/// 1. value-less defs flagged `is_axiom: false` that STILL lower to kernel
///    axioms (the C1 flag/value divergence), and
/// 2. axioms injected into the env with no `SpecDefinition` at all (the M1
///    env-vs-defs blind spot).
///
/// The result is sorted by name for deterministic output.
#[must_use]
pub fn live_env_axioms(spec: &Specification) -> Vec<EnvAdmittedAxiom> {
    let defs = spec.definitions();
    let mut out: Vec<EnvAdmittedAxiom> = spec
        .env()
        .constants()
        .filter(|c| c.kind == ConstantKind::Axiom)
        .map(|c| {
            let name = c.name.to_string();
            let backing = defs.get(&name).map(|d| {
                (
                    d.is_axiom,
                    d.value_src.is_some() || d.elaborated_value.is_some(),
                )
            });
            EnvAdmittedAxiom {
                origin: classify_env_axiom(backing),
                name,
            }
        })
        .collect();
    out.sort_by(|a, b| a.name.cmp(&b.name));
    out.dedup_by(|a, b| a.name == b.name);
    out
}

/// The pure, fail-closed subset check at the heart of the ratchet.
///
/// Returns the set of LIVE axiom names that are NOT present in `golden`, sorted.
/// A non-empty result is the fail-closed signal: a new axiom has been admitted
/// silently and must be either proved away or added to the golden in a reviewed
/// diff. Removals/drains (`live ⊆ golden`) yield an empty result and PASS.
///
/// This function is deliberately decoupled from [`Specification`] so it can be
/// unit-tested with a synthetic live set (see the crate tests), demonstrating
/// that the guard actually catches a new admission.
#[must_use]
pub fn newly_admitted_axioms<S: AsRef<str>>(live: &[S], golden: &BTreeSet<String>) -> Vec<String> {
    let mut new_names: Vec<String> = live
        .iter()
        .map(|s| s.as_ref())
        .filter(|name| !golden.contains(*name))
        .map(str::to_string)
        .collect();
    new_names.sort();
    new_names.dedup();
    new_names
}

#[cfg(test)]
mod tests {
    use super::*;

    fn golden(names: &[&str]) -> BTreeSet<String> {
        names.iter().map(|s| (*s).to_string()).collect()
    }

    #[test]
    fn test_newly_admitted_empty_when_live_is_subset_of_golden() {
        let g = golden(&["a", "b", "c"]);
        // Live is a strict subset (a drain happened) — must PASS (empty).
        let live = ["a", "c"];
        assert!(
            newly_admitted_axioms(&live, &g).is_empty(),
            "a drained (subset) live set must not be flagged"
        );
    }

    #[test]
    fn test_newly_admitted_empty_when_live_equals_golden() {
        let g = golden(&["a", "b", "c"]);
        let live = ["a", "b", "c"];
        assert!(
            newly_admitted_axioms(&live, &g).is_empty(),
            "an unchanged live set must not be flagged"
        );
    }

    /// FAIL-CLOSED demonstration (analogous to the fidelity_gate fail-closed
    /// test): feed the check a synthetic live set containing a fabricated extra
    /// axiom name and assert it is reported as a violation. This proves the
    /// guard actually catches a NEW admission without adding a real axiom.
    #[test]
    fn test_newly_admitted_flags_fabricated_new_axiom() {
        let g = golden(&["church_rosser_whnf", "ConstantExtension"]);
        let live = [
            "church_rosser_whnf",
            "ConstantExtension",
            "fabricated_false_axiom_should_be_caught",
        ];
        let new = newly_admitted_axioms(&live, &g);
        assert_eq!(
            new,
            vec!["fabricated_false_axiom_should_be_caught".to_string()],
            "the ratchet must flag a live axiom name absent from the golden"
        );
    }

    #[test]
    fn test_newly_admitted_reports_all_new_names_sorted_and_deduped() {
        let g = golden(&["keep"]);
        let live = ["zeta_new", "alpha_new", "keep", "alpha_new"];
        let new = newly_admitted_axioms(&live, &g);
        assert_eq!(
            new,
            vec!["alpha_new".to_string(), "zeta_new".to_string()],
            "all new names must be reported, sorted and de-duplicated"
        );
    }

    // ----- env-truth census classification (the C1-hole-closing logic) -----

    #[test]
    fn test_classify_env_axiom_no_specdef_is_env_injected() {
        // A kernel axiom with no backing SpecDefinition (e.g. propext,
        // Quot.sound, a trust marker, an init_* env injection): the M1 blind
        // spot the defs-based census never saw.
        assert_eq!(classify_env_axiom(None), AxiomOrigin::EnvInjected);
    }

    #[test]
    fn test_classify_env_axiom_flag_true_is_flag_axiom() {
        // is_axiom:true that lowered to an axiom — flag and kernel agree.
        // (value-presence is irrelevant once is_axiom is set.)
        assert_eq!(
            classify_env_axiom(Some((true, false))),
            AxiomOrigin::FlagAxiom
        );
        assert_eq!(
            classify_env_axiom(Some((true, true))),
            AxiomOrigin::FlagAxiom
        );
    }

    /// THE C1 EXPLOIT SHAPE, at the pure-logic level: a SpecDefinition with
    /// `is_axiom:false` AND no value (`value_present == false`) is value-less, so
    /// `prepare_definition_decl` lowers it to a GENUINE kernel `Declaration::Axiom`
    /// — yet the old flag-based census (which filtered on `is_axiom`) NEVER SAW
    /// it. The env-truth census reports it as a [`AxiomOrigin::PendingLeaf`]. This
    /// is the divergence the hardening closes.
    #[test]
    fn test_classify_env_axiom_flag_false_valueless_is_pending_leaf() {
        assert_eq!(
            classify_env_axiom(Some((false, false))),
            AxiomOrigin::PendingLeaf,
            "a value-less is_axiom:false def lowers to a kernel axiom — the C1 hole"
        );
    }

    #[test]
    fn test_origin_label_round_trips_known_variants() {
        assert_eq!(origin_label(AxiomOrigin::FlagAxiom), "FlagAxiom");
        assert_eq!(origin_label(AxiomOrigin::PendingLeaf), "PendingLeaf");
        assert_eq!(origin_label(AxiomOrigin::EnvInjected), "EnvInjected");
    }

    /// FAIL-CLOSED DEMO of the env-truth census against the SUBSET check: feed
    /// the ratchet a synthetic LIVE env-axiom set (built the way `live_env_axioms`
    /// builds names) that contains a fabricated value-less leaf NOT in the golden,
    /// and assert the ratchet flags it. This proves the C1 exploit shape — a
    /// value-less, `is_axiom:false` def silently lowering to a kernel axiom —
    /// is caught by the env-truth census + subset check, without adding any real
    /// axiom to the spec.
    #[test]
    fn test_env_census_subset_check_catches_fabricated_valueless_leaf() {
        // The synthetic env-axiom name set the kernel would expose for a spec
        // that contains a fabricated `{is_axiom:false, value_src:None,
        // elaborated_value:None}` definition. classify_env_axiom tags it
        // PendingLeaf (the C1 shape); the SUBSET check below catches it.
        let fabricated = "fabricated_valueless_false_axiom_C1_exploit";
        assert_eq!(
            classify_env_axiom(Some((false, false))),
            AxiomOrigin::PendingLeaf,
            "the fabricated value-less leaf is a PendingLeaf kernel axiom"
        );

        // The golden pins only the legitimate kernel axioms; the fabricated leaf
        // is absent.
        let golden_names = golden(&["propext", "Quot.sound", "church_rosser_whnf"]);
        let live_env_names = [
            "Quot.sound",
            "church_rosser_whnf",
            "propext",
            fabricated, // the C1 leaf the env census now SEES (old census did not)
        ];
        let violations = newly_admitted_axioms(&live_env_names, &golden_names);
        assert_eq!(
            violations,
            vec![fabricated.to_string()],
            "the env-truth ratchet must flag a value-less leaf that lowered to a \
             kernel axiom but is absent from the golden (the C1 exploit shape)"
        );
    }
}
