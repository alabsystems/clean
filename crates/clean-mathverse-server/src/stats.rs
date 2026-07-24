//! Honest corpus statistics, computed once at load time.
//!
//! The headline number is **`kernel_verified`** — declarations whose stored
//! import confidence is `KernelVerified`. For the shipped `mathverse-v1.x`
//! corpus this is deliberately reported as-is (it is 0): trust is *import /
//! source confidence*, not Clean-kernel re-verification. See [`crate::trust`].

use std::collections::BTreeMap;

use clean_mathverse::library::MathverseLibrary;
use clean_mathverse::types::{AxiomProfile, ImportConfidence};
use serde::Serialize;

/// Canonical (bit index, display name) table for [`AxiomProfile`] flags.
///
/// One entry per *distinct* bit (aliases like `CLASSICAL == CHOICE` are not
/// double-counted). Kept in sync with `clean_mathverse::types::AxiomProfile`.
const AXIOM_FLAGS: &[(u32, &str)] = &[
    (0, "Classical.choice"),
    (1, "lem"),
    (2, "propext"),
    (3, "funext"),
    (4, "Quot.sound"),
    (5, "univalence"),
    (6, "large_elimination"),
    (7, "hol_axioms"),
    (8, "mizar_tarski_grothendieck"),
    (10, "universe_inconsistency"),
    (11, "axiomatized"),
    (12, "bridge_axiom"),
    (13, "real_axioms"),
    (14, "lra_trusted"),
    (15, "float_approx"),
    (16, "nn_abstraction"),
    (17, "coq_sprop"),
    (18, "coq_module_functor"),
    (19, "coq_coinductive"),
    (20, "isabelle_lcf_erased"),
    (21, "agda_cubical"),
    (22, "idris_qtt"),
    (23, "smt_oracle"),
    (24, "sat_certificate"),
    (25, "atp_certificate"),
    (26, "arxiv_nl_import"),
];

/// Decode the set axiom-profile bits into human-readable axiom names.
pub fn decode_axioms(profile: AxiomProfile) -> Vec<String> {
    let bits = profile.0;
    AXIOM_FLAGS
        .iter()
        .filter(|(bit, _)| bits & (1u64 << bit) != 0)
        .map(|(_, name)| (*name).to_string())
        .collect()
}

fn confidence_name(c: ImportConfidence) -> &'static str {
    match c {
        ImportConfidence::KernelVerified => "KernelVerified",
        ImportConfidence::Translated => "Translated",
        ImportConfidence::Axiomatized => "Axiomatized",
        ImportConfidence::Unverified => "Unverified",
        ImportConfidence::SourceVerified => "SourceVerified",
        ImportConfidence::KernelCheckedConditional => "KernelCheckedConditional",
        ImportConfidence::KernelBridged => "KernelBridged",
    }
}

/// Aggregate, serializable view of the loaded corpus.
#[derive(Debug, Clone, Serialize, Default)]
pub struct CorpusStats {
    /// Total declarations across all loaded shards.
    pub total_declarations: u64,
    /// Number of shards merged into the live library.
    pub shards_loaded: usize,
    /// Number of shards skipped (unreadable / duplicate constants).
    pub shards_skipped: usize,
    /// The honest headline: declarations stamped `KernelVerified`.
    pub kernel_verified: u64,
    /// Declarations carrying a proof term (`value_idx != NO_VALUE`).
    pub with_proof_term: u64,
    /// Declarations whose transitive axiom closure is non-empty.
    pub axiom_bearing: u64,
    /// Count by import-confidence / trust level.
    pub by_trust_level: BTreeMap<String, u64>,
    /// Count by source proof system.
    pub by_source_system: BTreeMap<String, u64>,
    /// Count by declaration kind.
    pub by_decl_kind: BTreeMap<String, u64>,
    /// Count of declarations carrying each axiom flag.
    pub by_axiom_flag: BTreeMap<String, u64>,
}

impl CorpusStats {
    /// Compute statistics by a single pass over the merged library.
    pub fn compute(
        library: &MathverseLibrary,
        shards_loaded: usize,
        shards_skipped: usize,
    ) -> Self {
        let mut s = CorpusStats {
            shards_loaded,
            shards_skipped,
            ..Default::default()
        };
        let n = library.constant_count() as u32;
        s.total_declarations = n as u64;
        for idx in 0..n {
            let Some(h) = library.get_constant(idx) else {
                continue;
            };

            let trust = h.confidence().map(confidence_name).unwrap_or("Unknown");
            *s.by_trust_level.entry(trust.to_string()).or_default() += 1;
            if matches!(h.confidence(), Ok(ImportConfidence::KernelVerified)) {
                s.kernel_verified += 1;
            }

            let source = h
                .source()
                .map(|src| format!("{src:?}"))
                .unwrap_or_else(|raw| format!("Unknown({raw})"));
            *s.by_source_system.entry(source).or_default() += 1;

            let kind = h
                .decl_kind()
                .map(|k| format!("{k:?}"))
                .unwrap_or_else(|raw| format!("Unknown({raw})"));
            *s.by_decl_kind.entry(kind).or_default() += 1;

            if h.has_value() {
                s.with_proof_term += 1;
            }
            let profile = h.profile();
            if profile.axiom_count() > 0 {
                s.axiom_bearing += 1;
            }
            for name in decode_axioms(profile) {
                *s.by_axiom_flag.entry(name).or_default() += 1;
            }
        }
        s
    }
}
