// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Transitive-axiom-closure honesty guard for the clean-verify spec.
//!
//! ## Why this exists (M2 guard-hardening)
//!
//! Each [`crate::spec::SpecDefinition`] carries TWO hand-maintained honesty
//! labels that an adversarial audit found could DIVERGE from ground truth:
//!
//!  - `proof_status`: claims `DerivedProved` ("constructive — rests only on the
//!    spec's foundational inference rules + the kernel's logical foundation")
//!    vs `DerivedPending` / `Axiom`; and
//!  - `axiom_deps`: a hand-written `HashSet<String>` purporting to be the
//!    transitive NON-foundational axiom closure (the residual trust gap).
//!
//! Neither field is ever RECOMPUTED. So a def can read `DerivedProved` with
//! `axiom_deps: {}` ("empty closure") while its TRUE transitive closure still
//! reaches a value-less kernel axiom that is NOT part of the foundational base.
//! The confirmed case is `kernel_whnf_returns_def_eq`: stamped empty-closure
//! but its proof term chains `whnf_to_preserves_def_eq → whnf_step_preserves_def_eq
//! → whnf_step_beta_sound → beta_reduces_preserves_def_eq`, and the last is a
//! value-less [`clean_kernel::ConstantKind::Axiom`] (a `DerivedPending` leaf,
//! a `DerivedLemma` NOT a `FoundationalRule`). The project's cardinal rule —
//! "prove" requires the transitive axiom closure to rest only on the
//! foundational base — makes a mislabeled empty-closure a masquerade-shaped
//! OVERCLAIM.
//!
//! ## The spec's foundational base
//!
//! The spec models the type theory ABSTRACTLY. Historically, typing,
//! definitional equality, reduction relations, and product/conjunction
//! primitives included value-less modeling axioms tagged
//! [`crate::spec::AxiomCategory::FoundationalRule`]. The current live
//! environment has drained those declarations to checked inductives,
//! definitions, or theorems: the kernel-ground-truth axiom census now contains
//! only the kernel logical foundation, quotient primitives, and unreachable
//! trust tripwires. The category remains a conservative classification hook so
//! a future value-less foundational rule is explicit rather than silently
//! counted as domain debt.
//!
//! The conservative foundational base a DerivedProved closure is allowed to
//! rest on is:
//!
//!   (kernel logical foundation: `propext` / `Quot.sound` / `Classical.choice` /
//!    the `Quot` primitives / `Eq.refl` / …)
//!   ∪ (any spec `AxiomCategory::FoundationalRule` axiom, currently none).
//!
//! [`clean_kernel::Environment::axiom_deps`] ALREADY drops the kernel logical
//! foundation (it only collects NON-foundational `ConstantKind::Axiom`s), so the
//! closure it returns over the spec env contains exactly: the spec
//! `FoundationalRule` axioms + the spec `HelperAxiom`/`DerivedLemma`-pending
//! axiom leaves + any trust markers. The honesty residual is that closure MINUS
//! the spec's `FoundationalRule` names. Empty residual ⇔ genuinely
//! `DerivedProved`-eligible.
//!
//! ## What this module computes — by KERNEL GROUND TRUTH
//!
//! It REUSES the kernel's own transitive-closure machinery
//! ([`clean_kernel::Environment::axiom_deps`] /
//! [`clean_kernel::Environment::trust_marker_deps`]) applied to the spec's live
//! kernel env ([`Specification::env`]). `prepare_definition_decl` elaborates
//! every `value_src` and registers it via `add_decl`, so the env holds the REAL
//! proof terms; walking them is the authoritative closure the hand fields are
//! validated against. The foundational `FoundationalRule` name set is read FROM
//! THE LIVE SPEC (never hardcoded), so it tracks the spec automatically.
//!
//! The fail-closed test lives in `tests/spec_axiom_closure_honesty.rs`.

use std::collections::BTreeSet;

use clean_kernel::Name;

use crate::spec::{AxiomCategory, ProofStatus, SpecDefinition, Specification};

/// The four kernel trust markers whose transitive presence in any spec proof is
/// a CRITICAL masquerade. Mirrors the kernel `TRUST_MARKERS`
/// (`env/axiom_audit.rs`); named here as a guard constant so the honesty audit
/// reads self-contained and a kernel rename surfaces as a drift
/// (`test_forbidden_trust_markers_match_kernel_set`).
pub const FORBIDDEN_TRUST_MARKERS: &[&str] = &["sorry", "sorryAx", "trustedArith", "trustedAy"];

/// The names of the spec's self-declared foundational inference-rule base: every
/// [`SpecDefinition`] tagged [`AxiomCategory::FoundationalRule`].
///
/// These classify abstract modeling primitives. The current live census has no
/// value-less spec-owned declarations, but a `DerivedProved` closure would be
/// allowed to rest on a deliberately categorized foundational rule (the kernel
/// logical foundation is already excluded by
/// [`clean_kernel::Environment::axiom_deps`]).
///
/// Read fresh from the live spec so it tracks any re-categorization
/// automatically — never hardcoded.
#[must_use]
pub fn foundational_rule_names(spec: &Specification) -> BTreeSet<String> {
    spec.definitions()
        .values()
        .filter(|d| d.category == AxiomCategory::FoundationalRule)
        .map(|d| d.name.clone())
        .collect()
}

/// Compute the transitive closure of all NON-(kernel-foundational) axioms
/// reachable from the spec constant `name`, by KERNEL GROUND TRUTH.
///
/// Delegates to [`clean_kernel::Environment::axiom_deps`], which walks the
/// constant's elaborated type + value `Expr` trees, follows every referenced
/// constant transitively, and collects each one the env holds as
/// [`clean_kernel::ConstantKind::Axiom`] that is NOT a kernel-foundational axiom
/// (`propext` / `Quot.sound` / `Classical.choice` / the `Quot` primitives /
/// `Eq.refl` / …). Trust markers (`sorry` / … ) ARE included.
///
/// The result therefore contains the spec's `FoundationalRule` modeling
/// primitives + its `HelperAxiom`/pending leaves + any trust markers. Returns an
/// empty set if the constant is absent from the env.
#[must_use]
pub fn computed_axiom_closure(spec: &Specification, name: &str) -> BTreeSet<String> {
    let kname = Name::from_string(name);
    spec.env()
        .axiom_deps(&kname)
        .map(|deps| deps.into_iter().map(|n| n.to_string()).collect())
        .unwrap_or_default()
}

/// The subset of [`computed_axiom_closure`] that are TRUST MARKERS
/// (`sorry` / `sorryAx` / `trustedArith` / `trustedAy`).
///
/// A non-empty result is the CRITICAL signal: a spec proof transitively rests
/// on an incomplete-proof sentinel or an unverified decision-procedure bridge.
#[must_use]
pub fn computed_trust_markers(spec: &Specification, name: &str) -> BTreeSet<String> {
    let kname = Name::from_string(name);
    spec.env()
        .trust_marker_deps(&kname)
        .map(|deps| deps.into_iter().map(|n| n.to_string()).collect())
        .unwrap_or_default()
}

/// The Eq BUILT-INS and quotient primitives that CLAUDE.md lists as part of the
/// foundational base. Most (`Eq.symm` / `Eq.trans` / `Eq.subst` / `funext`) are
/// registered as kernel `Declaration::Theorem`s and so are ALREADY absent from
/// [`clean_kernel::Environment::axiom_deps`] (the BFS short-circuits on
/// `kind == Axiom`); the `Quot*` primitives are already in the kernel
/// `FOUNDATIONAL_AXIOMS` allowlist. This set is therefore mostly redundant with
/// what `axiom_deps` already excludes — it is included EXPLICITLY so the honesty
/// base reads self-contained and matches CLAUDE.md's stated foundational base
/// verbatim, and so a future kernel demotion of any of these to a value-less
/// `Axiom` cannot silently turn into counted DEBT.
pub const EXPLICIT_FOUNDATIONAL_BASE: &[&str] = &[
    // Kernel logical foundation (already excluded by axiom_deps; listed for clarity).
    "propext",
    "Quot.sound",
    "Classical.choice",
    // Quotient primitives.
    "Quot",
    "Quot.mk",
    "Quot.lift",
    "Quot.ind",
    // Eq built-ins (CLAUDE.md: foundational).
    "Eq",
    "Eq.refl",
    "Eq.symm",
    "Eq.trans",
    "Eq.subst",
    "Eq.substType",
    "Eq.cong",
    "Eq.ndrec",
    "Eq.mpr",
    "Eq.mp",
];

/// The complete honest FOUNDATIONAL BASE a `DerivedProved` closure is allowed to
/// rest on: the spec's own [`AxiomCategory::FoundationalRule`] names (read fresh
/// from the live spec) ∪ [`EXPLICIT_FOUNDATIONAL_BASE`] (the Eq built-ins +
/// quotient primitives). The kernel logical foundation is already excluded by
/// [`computed_axiom_closure`]. Anything in a closure NOT in this base (and not a
/// trust marker) is genuine DEBT.
#[must_use]
pub fn foundational_base(spec: &Specification) -> BTreeSet<String> {
    let mut base = foundational_rule_names(spec);
    base.extend(EXPLICIT_FOUNDATIONAL_BASE.iter().map(|s| (*s).to_string()));
    base
}

/// Pure partition of a RAW axiom closure into `(trust_markers, residual_debt)`
/// against a foundational base: `residual_debt = closure − base − trust_markers`,
/// `trust_markers = closure ∩ FORBIDDEN_TRUST_MARKERS`.
///
/// The real audit path AND the synthetic unit test both route through this so the
/// classification logic is exercised by a hermetic test (no full spec build).
#[must_use]
pub fn partition_closure(
    closure: &BTreeSet<String>,
    foundational: &BTreeSet<String>,
) -> (BTreeSet<String>, BTreeSet<String>) {
    let markers: BTreeSet<String> = closure
        .iter()
        .filter(|a| FORBIDDEN_TRUST_MARKERS.contains(&a.as_str()))
        .cloned()
        .collect();
    let residual: BTreeSet<String> = closure
        .iter()
        .filter(|a| !foundational.contains(*a))
        .filter(|a| !FORBIDDEN_TRUST_MARKERS.contains(&a.as_str()))
        .cloned()
        .collect();
    (markers, residual)
}

/// The honesty RESIDUAL of a spec constant: its transitive closure MINUS the
/// spec's `FoundationalRule` base MINUS the trust markers. This is exactly the
/// set of NON-foundational DOMAIN / PENDING axioms (`HelperAxiom`s and value-less
/// `DerivedPending` leaves) the proof genuinely rests on — i.e. what the
/// hand-maintained [`SpecDefinition::axiom_deps`] field is supposed to record.
///
/// Empty residual ⇔ the closure is `⊆ FoundationalRule ∪ kernel-foundational`
/// (the `DerivedProved`-eligible condition).
#[must_use]
pub fn residual_domain_axioms(
    spec: &Specification,
    name: &str,
    foundational: &BTreeSet<String>,
) -> BTreeSet<String> {
    let closure = computed_axiom_closure(spec, name);
    partition_closure(&closure, foundational).1
}

/// A single honesty violation for one spec definition. Ordered most-severe
/// first so a sort surfaces the CRITICAL masquerade at the top.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum HonestyViolation {
    /// (a) CRITICAL: the def's transitive closure reaches a forbidden trust
    /// marker (`sorry` / `sorryAx` / `trustedArith` / `trustedAy`). A sound
    /// checker would never certify a proof resting on one.
    ForbiddenTrustMarkerReach {
        /// The offending definition name.
        def: String,
        /// The trust marker(s) reached, sorted.
        markers: Vec<String>,
    },
    /// (b) A `DerivedProved` def whose honesty RESIDUAL is non-empty — i.e. it
    /// actually rests on a `HelperAxiom` or a value-less pending leaf. The
    /// `DerivedProved` label overclaims "constructive".
    DerivedProvedOverclaim {
        /// The offending definition name.
        def: String,
        /// The non-foundational, non-trust axiom names it truly rests on, sorted.
        residual: Vec<String>,
    },
    /// (c) The hand-maintained `axiom_deps` field is NOT a superset of the
    /// computed domain-axiom residual: it under-reports the trust gap.
    AxiomDepsUnderReports {
        /// The offending definition name.
        def: String,
        /// Residual domain axioms present in the computed closure but ABSENT
        /// from the hand `axiom_deps`, sorted.
        missing: Vec<String>,
    },
}

impl std::fmt::Display for HonestyViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HonestyViolation::ForbiddenTrustMarkerReach { def, markers } => write!(
                f,
                "CRITICAL (a) `{def}` transitively reaches forbidden trust marker(s) {markers:?} \
                 — a spec proof must NEVER rest on sorry/sorryAx/trustedArith/trustedAy"
            ),
            HonestyViolation::DerivedProvedOverclaim { def, residual } => write!(
                f,
                "OVERCLAIM (b) `{def}` is labeled DerivedProved but its TRUE transitive closure \
                 rests on non-foundational axiom(s) {residual:?} — re-label DerivedPending (or \
                 prove the offending leaf)"
            ),
            HonestyViolation::AxiomDepsUnderReports { def, missing } => write!(
                f,
                "MISMATCH (c) `{def}` hand axiom_deps UNDER-REPORTS the true domain closure; \
                 missing {missing:?} — correct the axiom_deps field to its true computed residual"
            ),
        }
    }
}

/// Audit ONE spec definition against the kernel-ground-truth closure, returning
/// every honesty violation it exhibits (possibly several).
///
/// `foundational` is the spec's `FoundationalRule` name set (see
/// [`foundational_rule_names`]); pass it once and reuse across the whole audit.
#[must_use]
pub fn audit_definition_honesty(
    spec: &Specification,
    def: &SpecDefinition,
    foundational: &BTreeSet<String>,
) -> Vec<HonestyViolation> {
    let mut out = Vec::new();

    // (a) Forbidden trust-marker reach — CRITICAL.
    let markers = computed_trust_markers(spec, &def.name);
    if !markers.is_empty() {
        out.push(HonestyViolation::ForbiddenTrustMarkerReach {
            def: def.name.clone(),
            markers: markers.into_iter().collect(),
        });
    }

    // Honesty residual: closure − FoundationalRule − trust markers.
    let residual = residual_domain_axioms(spec, &def.name, foundational);

    // (b) DerivedProved honesty: residual must be EMPTY.
    if def.proof_status == ProofStatus::DerivedProved && !residual.is_empty() {
        out.push(HonestyViolation::DerivedProvedOverclaim {
            def: def.name.clone(),
            residual: residual.iter().cloned().collect(),
        });
    }

    // (c) axiom_deps fidelity: hand field must be a superset of the residual.
    let hand: BTreeSet<String> = def.axiom_deps.iter().cloned().collect();
    let missing: Vec<String> = residual.difference(&hand).cloned().collect();
    if !missing.is_empty() {
        out.push(HonestyViolation::AxiomDepsUnderReports {
            def: def.name.clone(),
            missing,
        });
    }

    out
}

/// Audit the WHOLE spec, returning every honesty violation across all
/// definitions, sorted (CRITICAL trust-marker reaches first).
#[must_use]
pub fn audit_spec_honesty(spec: &Specification) -> Vec<HonestyViolation> {
    let foundational = foundational_rule_names(spec);
    let mut out: Vec<HonestyViolation> = spec
        .definitions()
        .values()
        .flat_map(|def| audit_definition_honesty(spec, def, &foundational))
        .collect();
    out.sort();
    out
}

/// Partition an honesty audit into the three rule categories, for reporting.
/// Returns `(forbidden, overclaims, mismatches)`.
#[must_use]
pub fn partition_violations(
    violations: &[HonestyViolation],
) -> (
    Vec<&HonestyViolation>,
    Vec<&HonestyViolation>,
    Vec<&HonestyViolation>,
) {
    let mut forbidden = Vec::new();
    let mut overclaims = Vec::new();
    let mut mismatches = Vec::new();
    for v in violations {
        match v {
            HonestyViolation::ForbiddenTrustMarkerReach { .. } => forbidden.push(v),
            HonestyViolation::DerivedProvedOverclaim { .. } => overclaims.push(v),
            HonestyViolation::AxiomDepsUnderReports { .. } => mismatches.push(v),
        }
    }
    (forbidden, overclaims, mismatches)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_forbidden_trust_markers_match_kernel_set() {
        // Pin our guard constant to the kernel's own trust-marker predicate so a
        // kernel rename surfaces here rather than silently widening the gap.
        for m in FORBIDDEN_TRUST_MARKERS {
            assert!(
                clean_kernel::is_trust_marker(&Name::from_string(m)),
                "{m} must be a kernel trust marker"
            );
        }
    }

    #[test]
    fn test_partition_closure_flags_synthetic_sorry() {
        // Synthetic closure: a foundational rule, a domain axiom, and a `sorry`
        // trust marker. The partition MUST surface `sorry` as a trust marker
        // (CRITICAL) and MUST NOT silently fold it into the residual.
        let foundational: BTreeSet<String> = ["Typing.var".to_string()].into_iter().collect();
        let closure: BTreeSet<String> = [
            "Typing.var".to_string(),         // foundational — excluded from both
            "church_rosser_whnf".to_string(), // domain axiom — residual debt
            "sorry".to_string(),              // FORBIDDEN trust marker — must be flagged
        ]
        .into_iter()
        .collect();

        let (markers, residual) = partition_closure(&closure, &foundational);

        assert!(
            markers.contains("sorry"),
            "a synthetic closure containing `sorry` MUST be flagged as a trust marker"
        );
        assert_eq!(markers.len(), 1, "exactly the `sorry` marker, nothing else");
        assert!(
            !residual.contains("sorry"),
            "a trust marker must NEVER be laundered into the residual debt set"
        );
        assert!(
            !residual.contains("Typing.var"),
            "a foundational-rule name must be excluded from the residual debt"
        );
        assert_eq!(
            residual,
            ["church_rosser_whnf".to_string()].into_iter().collect(),
            "residual debt = closure − foundational − trust markers"
        );
    }

    #[test]
    fn test_partition_closure_flags_all_four_trust_markers() {
        let foundational = BTreeSet::new();
        for m in FORBIDDEN_TRUST_MARKERS {
            let closure: BTreeSet<String> = [(*m).to_string()].into_iter().collect();
            let (markers, residual) = partition_closure(&closure, &foundational);
            assert!(
                markers.contains(*m),
                "{m} must be flagged as a trust marker"
            );
            assert!(residual.is_empty(), "{m} must not appear as residual debt");
        }
    }

    #[test]
    fn test_violation_ordering_puts_critical_first() {
        let critical = HonestyViolation::ForbiddenTrustMarkerReach {
            def: "z".to_string(),
            markers: vec!["sorry".to_string()],
        };
        let overclaim = HonestyViolation::DerivedProvedOverclaim {
            def: "a".to_string(),
            residual: vec!["x".to_string()],
        };
        let mismatch = HonestyViolation::AxiomDepsUnderReports {
            def: "a".to_string(),
            missing: vec!["x".to_string()],
        };
        let mut v = [mismatch, overclaim.clone(), critical.clone()];
        v.sort();
        assert_eq!(
            v[0], critical,
            "CRITICAL trust-marker reach must sort first"
        );
        assert_eq!(v[1], overclaim, "overclaim sorts before mismatch");
    }
}
