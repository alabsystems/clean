// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! COQ-5: qualified Coq axiom name → [`AxiomProfile`] bit mapping.
//!
//! Maps the FULLY-QUALIFIED axiom names reported by a kernel recheck verdict
//! (`recheck_and_classify` → `domain_axioms`, spelled per the shared Coq
//! naming convention: DirPath segments reversed + `.` + Id, e.g.
//! `Coq.Logic.Classical_Prop.classic`) onto the named `AxiomProfile` bits the
//! shard trust machinery gates on.
//!
//! **Fail-closed default:** any axiom name this table does not recognize maps
//! to [`AxiomProfile::AXIOMATIZED`] — a trust-gated bit — so an unmapped
//! domain axiom can never launder a declaration into an ungated profile.
//!
//! **Proof irrelevance encoding choice:** `types.rs` carries a
//! `PROOF_IRRELEVANCE` alias that shares bit 3 with `FUNC_EXT` (a legacy
//! origin/main compatibility alias, not a dedicated bit). We deliberately map
//! `Coq.Logic.ProofIrrelevance.proof_irrelevance` to that existing alias
//! rather than minting a PROP_EXT approximation: the alias is the crate's one
//! named home for the axiom, and reusing it keeps this table consistent with
//! every other consumer of `AxiomProfile::PROOF_IRRELEVANCE`. (Proof
//! irrelevance is a consequence of propositional extensionality, so PROP_EXT
//! would also have been defensible; if `types.rs` ever grows a dedicated bit,
//! only this table needs updating.)
//!
//! **Univalence:** UniMath / HoTT namespaces assume univalence pervasively
//! (see [`crate::coq::ecosystem::ecosystem_base_profile`], which stamps
//! `UNIVALENCE` on the UniMath and HoTT ecosystems); any axiom under those
//! prefixes — or any axiom literally named `univalence` — carries
//! [`AxiomProfile::UNIVALENCE`]. The checked Coq shard writer refuses to ever
//! stamp `KernelVerified` on a univalence-tainted declaration (Clean's kernel
//! is not a univalent foundation, so such a proof is only valid *relative to*
//! the univalence axiom).

use crate::types::AxiomProfile;

/// Union of the profile bits of every axiom in `domain_axioms`.
///
/// Input names must be fully qualified (shared Coq naming convention).
/// Unrecognized names contribute the fail-closed
/// [`AxiomProfile::AXIOMATIZED`] bit.
pub(crate) fn coq_axiom_profile_bits(domain_axioms: &[String]) -> AxiomProfile {
    domain_axioms.iter().fold(AxiomProfile::NONE, |acc, name| {
        acc | classify_coq_axiom(name)
    })
}

/// `true` iff any axiom in `domain_axioms` carries the univalence taint
/// (UniMath/HoTT namespace or a literal `univalence` axiom). A tainted
/// declaration must NEVER be stamped `KernelVerified` (COQ-5 policy).
pub(crate) fn is_univalence_tainted(domain_axioms: &[String]) -> bool {
    domain_axioms
        .iter()
        .any(|name| classify_coq_axiom(name).has(AxiomProfile::UNIVALENCE))
}

/// Classify ONE fully-qualified Coq axiom name.
///
/// Explicit table first, then namespace rules, then the fail-closed
/// [`AxiomProfile::AXIOMATIZED`] default.
pub(crate) fn classify_coq_axiom(name: &str) -> AxiomProfile {
    // --- Explicit, exact qualified names -----------------------------------
    match name {
        // Classical logic: excluded middle and its double-negation spelling.
        "Coq.Logic.Classical_Prop.classic" | "Coq.Logic.Classical_Prop.NNPP" => {
            return AxiomProfile::LEM;
        }
        // Choice-family axioms (relational/functional choice, epsilon,
        // definite/indefinite description).
        "Coq.Logic.ClassicalChoice.choice"
        | "Coq.Logic.ClassicalChoice.relational_choice"
        | "Coq.Logic.ClassicalEpsilon.constructive_indefinite_description"
        | "Coq.Logic.ClassicalEpsilon.epsilon"
        | "Coq.Logic.ClassicalDescription.constructive_definite_description"
        | "Coq.Logic.ClassicalUniqueChoice.dependent_unique_choice"
        | "Coq.Logic.Epsilon.epsilon_statement"
        | "Coq.Logic.IndefiniteDescription.constructive_indefinite_description"
        | "Coq.Logic.Description.constructive_definite_description" => {
            return AxiomProfile::CHOICE;
        }
        // Functional extensionality (plain and dependent).
        "Coq.Logic.FunctionalExtensionality.functional_extensionality"
        | "Coq.Logic.FunctionalExtensionality.functional_extensionality_dep" => {
            return AxiomProfile::FUNC_EXT;
        }
        // Propositional extensionality.
        "Coq.Logic.PropExtensionality.propositional_extensionality" => {
            return AxiomProfile::PROP_EXT;
        }
        // Proof irrelevance → the crate's existing PROOF_IRRELEVANCE alias
        // (bit 3, shared with FUNC_EXT — see module docs for the rationale).
        "Coq.Logic.ProofIrrelevance.proof_irrelevance" => {
            return AxiomProfile::PROOF_IRRELEVANCE;
        }
        _ => {}
    }

    // --- Namespace rules ----------------------------------------------------
    // UniMath / HoTT namespaces, or an axiom literally named `univalence`
    // (e.g. `UniMath.Foundations.UnivalenceAxiom.univalence`,
    // `HoTT.Types.Universe.univalence_axiom`): univalence taint.
    if name.starts_with("UniMath.")
        || name.starts_with("HoTT.")
        || last_segment_has(name, "univalence")
    {
        return AxiomProfile::UNIVALENCE;
    }
    // The remaining `Coq.Logic.Classical*` modules (Classical_Pred_Type,
    // ClassicalFacts, …) postulate/derive classical logic; a choice-named
    // axiom inside them is CHOICE, everything else is LEM.
    if name.starts_with("Coq.Logic.Classical") {
        return if last_segment_has(name, "choice")
            || last_segment_has(name, "description")
            || last_segment_has(name, "epsilon")
        {
            AxiomProfile::CHOICE
        } else {
            AxiomProfile::LEM
        };
    }
    // Whole-module rules for the extensionality modules (auxiliary axioms /
    // alternate spellings inside them state the same principle).
    if name.starts_with("Coq.Logic.FunctionalExtensionality.") {
        return AxiomProfile::FUNC_EXT;
    }
    if name.starts_with("Coq.Logic.PropExtensionality") {
        return AxiomProfile::PROP_EXT;
    }

    // --- Fail-closed default ------------------------------------------------
    AxiomProfile::AXIOMATIZED
}

/// `true` iff the final `.`-separated segment of `name` contains `needle`
/// (ASCII case-insensitive).
fn last_segment_has(name: &str, needle: &str) -> bool {
    let last = name.rsplit('.').next().unwrap_or(name);
    last.to_ascii_lowercase().contains(needle)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn names(list: &[&str]) -> Vec<String> {
        list.iter().map(ToString::to_string).collect()
    }

    #[test]
    fn test_classify_classic_and_nnpp_map_to_lem() {
        assert_eq!(
            classify_coq_axiom("Coq.Logic.Classical_Prop.classic"),
            AxiomProfile::LEM
        );
        assert_eq!(
            classify_coq_axiom("Coq.Logic.Classical_Prop.NNPP"),
            AxiomProfile::LEM
        );
    }

    #[test]
    fn test_classify_choice_axioms_map_to_choice() {
        for axiom in [
            "Coq.Logic.ClassicalChoice.choice",
            "Coq.Logic.ClassicalEpsilon.constructive_indefinite_description",
            "Coq.Logic.Epsilon.epsilon_statement",
            "Coq.Logic.Description.constructive_definite_description",
        ] {
            assert_eq!(
                classify_coq_axiom(axiom),
                AxiomProfile::CHOICE,
                "choice axiom {axiom} must map to CHOICE"
            );
        }
    }

    #[test]
    fn test_classify_functional_extensionality_maps_to_func_ext() {
        assert_eq!(
            classify_coq_axiom("Coq.Logic.FunctionalExtensionality.functional_extensionality"),
            AxiomProfile::FUNC_EXT
        );
        assert_eq!(
            classify_coq_axiom("Coq.Logic.FunctionalExtensionality.functional_extensionality_dep"),
            AxiomProfile::FUNC_EXT
        );
    }

    #[test]
    fn test_classify_prop_extensionality_maps_to_prop_ext() {
        assert_eq!(
            classify_coq_axiom("Coq.Logic.PropExtensionality.propositional_extensionality"),
            AxiomProfile::PROP_EXT
        );
    }

    #[test]
    fn test_classify_proof_irrelevance_uses_existing_alias_bit() {
        let bits = classify_coq_axiom("Coq.Logic.ProofIrrelevance.proof_irrelevance");
        assert_eq!(bits, AxiomProfile::PROOF_IRRELEVANCE);
        // Documented consequence of the types.rs alias layout: bit 3 is shared
        // with FUNC_EXT. Assert it so a future dedicated bit surfaces here.
        assert_eq!(AxiomProfile::PROOF_IRRELEVANCE, AxiomProfile::FUNC_EXT);
    }

    #[test]
    fn test_classify_univalence_names() {
        assert_eq!(
            classify_coq_axiom("UniMath.Foundations.UnivalenceAxiom.univalenceAxiom"),
            AxiomProfile::UNIVALENCE
        );
        assert_eq!(
            classify_coq_axiom("HoTT.Types.Universe.isequiv_equiv_path"),
            AxiomProfile::UNIVALENCE
        );
        assert_eq!(
            classify_coq_axiom("SomeLib.Core.univalence"),
            AxiomProfile::UNIVALENCE
        );
    }

    #[test]
    fn test_classify_unrecognized_axiom_fails_closed_to_axiomatized() {
        // Fail-closed default: an unmapped domain axiom is trust-gated.
        let bits = classify_coq_axiom("Coq.Reals.Raxioms.completeness");
        assert_eq!(bits, AxiomProfile::AXIOMATIZED);
        assert!(bits.is_trust_gated());
    }

    #[test]
    fn test_profile_bits_union_over_all_axioms() {
        let axioms = names(&[
            "Coq.Logic.Classical_Prop.classic",
            "Coq.Logic.FunctionalExtensionality.functional_extensionality",
            "Some.Unknown.axiom",
        ]);
        let bits = coq_axiom_profile_bits(&axioms);
        assert!(bits.has(AxiomProfile::LEM));
        assert!(bits.has(AxiomProfile::FUNC_EXT));
        assert!(bits.has(AxiomProfile::AXIOMATIZED));
        assert!(!bits.has(AxiomProfile::UNIVALENCE));
    }

    #[test]
    fn test_profile_bits_empty_input_is_none() {
        assert_eq!(coq_axiom_profile_bits(&[]), AxiomProfile::NONE);
    }

    #[test]
    fn test_is_univalence_tainted() {
        assert!(is_univalence_tainted(&names(&[
            "Coq.Logic.Classical_Prop.classic",
            "UniMath.Foundations.UnivalenceAxiom.univalenceAxiom",
        ])));
        assert!(!is_univalence_tainted(&names(&[
            "Coq.Logic.Classical_Prop.classic",
            "Some.Unknown.axiom",
        ])));
        assert!(!is_univalence_tainted(&[]));
    }
}
