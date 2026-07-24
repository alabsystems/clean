// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Transitive-axiom-closure audit for gamma_crown `constructive: true` claims.
//!
//! For a given conjecture, this module initializes the conjecture's
//! Environment (via the same entry points used by `verify_gamma_crown`),
//! enumerates every `Declaration::Theorem` whose name starts with the
//! conjecture's declared namespace prefix, and computes
//! `env.axiom_deps(name)` — the transitive domain-axiom closure — for each
//! theorem. A theorem is `is_constructive` iff that closure is empty (i.e.
//! only FOUNDATIONAL_AXIOMS were reachable).
//!
//! The output is `serde`-serializable so both the `verify_constructive_claims`
//! compat-shim binary and the `clean kernel verify-constructive-claims`
//! subcommand can emit identical JSON to the Python audit gate
//! (`scripts/axiom_audit/verify.py`).
//!
//! # Exit-code contract
//!
//! The callers wrap [`build_audit`] with this exit-code mapping (preserved
//! from the original standalone binary):
//!
//! | Code | Meaning                                                              |
//! |------|----------------------------------------------------------------------|
//! | 0    | All theorems constructive, OR `--allow-empty` + no theorems found.   |
//! | 1    | At least one theorem has a non-foundational axiom closure.           |
//! | 2    | Usage error (missing/unknown flag, unknown conjecture ID).           |
//! | 3    | Initialization error (conjecture builder failed).                    |
//! | 4    | No theorems registered in the conjecture's namespace.                |
//!
//! Part of Epic #3436 Phase 3.5 (#3510); originally #3435 (audit schema + gate).

use serde::Serialize;

use crate::env::gamma_crown_verify::CONJECTURE_IDS;
use crate::{ConstantKind, Environment, Name};

/// Namespaces consulted when selecting theorems to audit for a conjecture.
///
/// These MUST match `gamma_crown_verify::conjecture_axiom_prefixes`. Keeping
/// them local keeps the gate self-contained and avoids making the private
/// helper public for one consumer.
pub fn conjecture_theorem_prefixes(id: &str) -> &'static [&'static str] {
    match id {
        "C001" => &["NNVerify.C001."],
        "C002" => &["NNVerify.C002."],
        "C003" => &["NNVerify.ECLipsE.", "NNVerify.Lipschitz."],
        "C004" => &["NNVerify.C004."],
        "C005" => &["NNVerify.McCormick."],
        "C006" => &["NNVerify.C006."],
        "C007" => &["NNVerify.C007."],
        "C008" => &["NNVerify.ibp_tightness_"],
        "C009" => &[
            "NNVerification.ibp_wrapping_",
            "NNVerification.crown_",
            "NNVerification.norm_product_",
            "NNVerification.ratio_",
            "NNVerification.c009_",
            "NNVerification.C009",
        ],
        "C010" => &["NNVerify.C010.", "NNVerify.RobustnessGen."],
        "C011" => &["NNVerify.C011."],
        "C012" => &["NNVerify.C012."],
        "C028" => &["NNVerify.C028."],
        "C029" => &["NNVerify.PacProof."],
        "C030" => &["NNVerify.OrbitCROWN."],
        _ => &[],
    }
}

/// Per-theorem audit record emitted in the JSON output.
#[derive(Clone, Debug, Serialize)]
pub struct TheoremAudit {
    /// Theorem name (e.g. `NNVerify.C004.crown_equals_ibp`).
    pub name: String,
    /// Transitive domain-axiom closure (sorted, stable order for diffing).
    pub closure: Vec<String>,
    /// True iff `closure` is empty — all transitive deps were foundational.
    pub is_constructive: bool,
}

/// Aggregate report for one conjecture.
#[derive(Clone, Debug, Serialize)]
pub struct ConjectureAudit {
    pub conjecture: String,
    pub theorems: Vec<TheoremAudit>,
    /// Count of theorems that failed the constructive check.
    pub non_constructive_count: usize,
    /// True iff every theorem in scope passes and at least one was found.
    pub all_constructive: bool,
}

/// Return `true` iff `id` is a known `gamma_crown` conjecture identifier.
#[must_use]
pub fn is_known_conjecture(id: &str) -> bool {
    CONJECTURE_IDS.contains(&id)
}

/// Compute the constructive-claims audit for a single conjecture.
///
/// The caller is responsible for initializing the Environment (see
/// `gamma_crown_verify::init_conjecture`) and for translating the returned
/// record into the canonical exit code (see module docs).
#[must_use]
pub fn build_audit(id: &str, env: &Environment) -> ConjectureAudit {
    let prefixes = conjecture_theorem_prefixes(id);

    // Collect theorem names belonging to this conjecture's namespace.
    let mut theorem_names: Vec<Name> = env
        .constants()
        .filter(|c| c.kind == ConstantKind::Theorem)
        .filter(|c| {
            let s = c.name.to_string();
            prefixes.iter().any(|p| s.starts_with(p))
        })
        .map(|c| c.name.clone())
        .collect();
    theorem_names.sort_by_key(|a| a.to_string());

    let mut theorems: Vec<TheoremAudit> = Vec::with_capacity(theorem_names.len());
    for name in &theorem_names {
        let closure = env.axiom_deps(name).unwrap_or_default();
        let mut closure_strs: Vec<String> = closure.iter().map(|n| n.to_string()).collect();
        closure_strs.sort();
        let is_constructive = closure_strs.is_empty();
        theorems.push(TheoremAudit {
            name: name.to_string(),
            closure: closure_strs,
            is_constructive,
        });
    }

    let non_constructive_count = theorems.iter().filter(|t| !t.is_constructive).count();
    // `all_constructive` requires at least one theorem AND zero failures.
    let all_constructive = !theorems.is_empty() && non_constructive_count == 0;

    ConjectureAudit {
        conjecture: id.to_string(),
        theorems,
        non_constructive_count,
        all_constructive,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn known_conjecture_ids_match_overlay() {
        // Every ID published by the overlay must have a known prefix table
        // entry. Missing entries silently drop theorems and cause
        // `--allow-empty`-gated false-passes.
        for id in CONJECTURE_IDS {
            let prefixes = conjecture_theorem_prefixes(id);
            assert!(
                !prefixes.is_empty(),
                "no theorem prefix registered for known conjecture `{id}` — \
                 constructive-claims audit would silently report zero theorems"
            );
        }
    }

    #[test]
    fn unknown_conjecture_has_no_prefixes() {
        assert_eq!(conjecture_theorem_prefixes("not-a-real-id"), &[] as &[&str]);
    }

    #[test]
    fn is_known_conjecture_matches_overlay() {
        for id in CONJECTURE_IDS {
            assert!(is_known_conjecture(id), "overlay id `{id}` must be known");
        }
        assert!(!is_known_conjecture("C999"));
        assert!(!is_known_conjecture(""));
    }

    #[test]
    fn build_audit_empty_env_reports_zero_theorems() {
        // An empty env has no theorems under any namespace — the audit
        // returns zero theorems and `all_constructive = false` (the
        // invariant keeps `--allow-empty` as the only pass condition).
        let env = Environment::new();
        let audit = build_audit("C008", &env);
        assert_eq!(audit.conjecture, "C008");
        assert!(audit.theorems.is_empty());
        assert_eq!(audit.non_constructive_count, 0);
        assert!(!audit.all_constructive);
    }

    #[test]
    fn build_audit_unknown_conjecture_has_no_theorems() {
        // Unknown IDs have an empty prefix list, so no theorems match even
        // if the env is populated. Callers map this to exit code 4 when
        // `--allow-empty` is not set.
        let env = Environment::new();
        let audit = build_audit("not-a-real-id", &env);
        assert!(audit.theorems.is_empty());
        assert!(!audit.all_constructive);
    }
}
