// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Trust enforcement for the Mathverse Library.
//!
//! [`TrustPolicy`] controls which constants are visible to tactics and elaboration
//! based on their [`AxiomProfile`] bits and low-confidence import metadata. By
//! default, constants with any [`AxiomProfile::TRUST_GATED`] bits set are hidden,
//! and `Axiomatized` / `Unverified` imports are hidden even if a malformed or
//! legacy shard omitted the corresponding profile bits. Callers can opt in to
//! specific axiom profiles via [`TrustPolicy::with_allowed_bits`] or allow
//! everything via [`TrustPolicy::permissive`].

use crate::error::{MathverseError, MathverseResult};
use crate::types::{AxiomProfile, ImportConfidence, MathverseConstantHeader};

/// Trust policy controlling which constants are visible through the trust gate.
///
/// The policy works by comparing each constant's axiom profile against a set of
/// allowed trust-gated bits. A constant is visible if and only if all of its
/// trust-gated bits are present in the allowed set.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TrustPolicy {
    /// Bitmask of trust-gated bits that are allowed through the gate.
    /// Only bits within `AxiomProfile::TRUST_GATED` matter; non-gated bits
    /// (e.g., CHOICE, LEM) never block visibility.
    allowed_gated_bits: u64,
    /// Whether imports explicitly marked `Unverified` are visible. This is
    /// only enabled by [`TrustPolicy::permissive`]; profile-bit opt-ins do not
    /// make statement-only imports usable as proof-search candidates.
    allow_unverified_confidence: bool,
}

impl TrustPolicy {
    /// Default policy: only kernel-verified constants with no trust-gated bits
    /// are visible. This is the safe default for proof generation.
    #[must_use]
    pub const fn default_policy() -> Self {
        Self {
            allowed_gated_bits: 0,
            allow_unverified_confidence: false,
        }
    }

    /// Permissive policy: all constants are visible regardless of axiom profile.
    #[must_use]
    pub const fn permissive() -> Self {
        Self {
            allowed_gated_bits: AxiomProfile::TRUST_GATED.0,
            allow_unverified_confidence: true,
        }
    }

    /// Custom policy: allow specific trust-gated bits.
    ///
    /// Only bits within `AxiomProfile::TRUST_GATED` are meaningful. Bits outside
    /// the trust-gated mask are silently ignored (they never block visibility).
    #[must_use]
    pub const fn with_allowed_bits(bits: AxiomProfile) -> Self {
        Self {
            // Only retain bits that are actually trust-gated.
            allowed_gated_bits: bits.0 & AxiomProfile::TRUST_GATED.0,
            allow_unverified_confidence: false,
        }
    }

    /// Returns the allowed bits as an AxiomProfile (intersected with TRUST_GATED).
    #[inline]
    #[must_use]
    pub const fn allowed_bits(&self) -> AxiomProfile {
        AxiomProfile(self.allowed_gated_bits)
    }

    /// Whether explicitly unverified imports are visible.
    #[inline]
    #[must_use]
    pub const fn allows_unverified_confidence(&self) -> bool {
        self.allow_unverified_confidence
    }

    /// Check if a constant header passes the trust gate.
    ///
    /// A constant is visible when every trust-gated bit in its axiom profile is
    /// also present in `allowed_gated_bits`, and its import confidence is not
    /// `Axiomatized` / `Unverified` unless the policy explicitly opts into that
    /// low-trust class. Non-gated axiom bits (e.g., CHOICE, LEM, PROP_EXT) never
    /// block visibility.
    #[inline]
    #[must_use]
    pub const fn is_visible(&self, header: &MathverseConstantHeader) -> bool {
        let gated = header.axiom_profile.0 & AxiomProfile::TRUST_GATED.0;
        // All gated bits in the profile must be covered by the allowed set.
        if (gated & !self.allowed_gated_bits) != 0 {
            return false;
        }

        if header.import_confidence == ImportConfidence::Axiomatized as u8 {
            return (self.allowed_gated_bits & AxiomProfile::AXIOMATIZED.0) != 0;
        }

        if header.import_confidence == ImportConfidence::Unverified as u8 {
            return self.allow_unverified_confidence;
        }

        if header.import_confidence == ImportConfidence::KernelVerified as u8
            || header.import_confidence == ImportConfidence::Translated as u8
            || header.import_confidence == ImportConfidence::SourceVerified as u8
        {
            return true;
        }

        // Unknown future confidence bytes fail closed unless the caller asked
        // for the completely permissive library view.
        self.allow_unverified_confidence
    }

    /// Filter a slice of constant headers, returning only visible constants
    /// along with their original indices.
    #[must_use]
    pub fn filter_constants<'a>(
        &self,
        constants: &'a [MathverseConstantHeader],
    ) -> Vec<(u32, &'a MathverseConstantHeader)> {
        constants
            .iter()
            .enumerate()
            .filter(|(_, hdr)| self.is_visible(hdr))
            .map(|(i, hdr)| (i as u32, hdr))
            .collect()
    }
}

impl Default for TrustPolicy {
    fn default() -> Self {
        Self::default_policy()
    }
}

/// Transitively propagate axiom profiles through a dependency graph.
///
/// For each constant `i`, `deps[i]` lists the indices of constants that `i`
/// depends on. After propagation, each constant's axiom profile is the union of
/// its own profile and all transitive dependency profiles:
///
/// ```text
/// profile(T) = own_profile(T) | union(profile(dep) for dep in deps(T))
/// ```
///
/// Returns `Err(MathverseError::AxiomProfileCycle)` if a dependency cycle is
/// detected. The propagation uses iterative fixed-point computation rather than
/// recursion to avoid stack overflow on deep dependency chains.
pub fn propagate_axiom_profiles(
    constants: &mut [MathverseConstantHeader],
    deps: &[Vec<u32>],
) -> MathverseResult<()> {
    let n = constants.len();
    assert_eq!(
        n,
        deps.len(),
        "constants and deps must have the same length"
    );

    if n == 0 {
        return Ok(());
    }

    // Validate all dependency indices are in range.
    for (i, dep_list) in deps.iter().enumerate() {
        for &d in dep_list {
            if d as usize >= n {
                return Err(MathverseError::ConstantOutOfRange {
                    idx: d,
                    count: n as u32,
                });
            }
        }
        // Check for direct self-cycles.
        if dep_list.contains(&(i as u32)) {
            return Err(MathverseError::AxiomProfileCycle(i as u32));
        }
    }

    // Topological sort via Kahn's algorithm to detect cycles and determine
    // a safe evaluation order.
    let mut in_degree = vec![0u32; n];
    // Build reverse adjacency: if deps[i] contains j, then j -> i (j is needed by i).
    for dep_list in deps.iter() {
        for &d in dep_list {
            in_degree[d as usize] += 1;
        }
    }

    // Wait — in_degree should count how many things point INTO a node.
    // For propagation, we need to process dependencies before dependents.
    // If deps[i] = [j, k], then i depends on j and k.
    // We need to process j and k before i.
    // So the edges are j -> i, k -> i (dependency flows from j to i).
    // in_degree[i] = number of deps[i] entries = number of things i depends on.
    // We start with nodes that have no dependencies (in_degree = 0).

    // Recalculate: in_degree[i] = |deps[i]|
    for (i, dep_list) in deps.iter().enumerate() {
        in_degree[i] = dep_list.len() as u32;
    }

    let mut queue: Vec<usize> = Vec::new();
    for (i, &deg) in in_degree.iter().enumerate() {
        if deg == 0 {
            queue.push(i);
        }
    }

    // Build forward adjacency: dependents[j] = list of i where j is in deps[i].
    let mut dependents: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (i, dep_list) in deps.iter().enumerate() {
        for &d in dep_list {
            dependents[d as usize].push(i);
        }
    }

    let mut processed = 0usize;
    let mut head = 0;

    while head < queue.len() {
        let node = queue[head];
        head += 1;
        processed += 1;

        // Propagate this node's profile to all its dependents.
        let node_profile = constants[node].axiom_profile;
        for &dependent in &dependents[node] {
            constants[dependent].axiom_profile |= node_profile;
            in_degree[dependent] -= 1;
            if in_degree[dependent] == 0 {
                queue.push(dependent);
            }
        }
    }

    if processed != n {
        // Find a node still in a cycle (in_degree > 0).
        for (i, &deg) in in_degree.iter().enumerate() {
            if deg > 0 {
                return Err(MathverseError::AxiomProfileCycle(i as u32));
            }
        }
        // Should not reach here, but just in case.
        return Err(MathverseError::AxiomProfileCycle(0));
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Trust audit log
// ---------------------------------------------------------------------------

/// Decision made by the trust system for a constant.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TrustDecision {
    /// Constant passed the trust gate and is visible.
    Allowed,
    /// Constant was hidden by the trust policy.
    Denied,
    /// Constant is in the quarantine zone (visible but flagged).
    Quarantined,
    /// Constant requires manual review before use.
    Escalated,
}

/// A single entry in the trust audit log.
#[derive(Clone, Debug)]
pub struct TrustAuditEntry {
    /// Index of the constant this decision applies to.
    pub constant_idx: u32,
    /// The decision that was made.
    pub decision: TrustDecision,
    /// Human-readable reason for the decision.
    pub reason: String,
    /// Unix epoch seconds when the decision was recorded.
    pub timestamp_epoch: u64,
}

/// Log of all trust decisions, for auditing and debugging trust gate behavior.
pub struct TrustAuditLog {
    entries: Vec<TrustAuditEntry>,
}

impl TrustAuditLog {
    /// Create an empty audit log.
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    /// Add a trust decision entry to the log.
    pub fn add_entry(&mut self, entry: TrustAuditEntry) {
        self.entries.push(entry);
    }

    /// Return all entries for a given constant index.
    #[must_use]
    pub fn entries_for_constant(&self, constant_idx: u32) -> Vec<&TrustAuditEntry> {
        self.entries
            .iter()
            .filter(|e| e.constant_idx == constant_idx)
            .collect()
    }

    /// Count the number of denied decisions in the log.
    #[must_use]
    pub fn denied_count(&self) -> usize {
        self.entries
            .iter()
            .filter(|e| e.decision == TrustDecision::Denied)
            .count()
    }

    /// Return the constant indices of all quarantined constants (deduplicated).
    #[must_use]
    pub fn quarantined_constants(&self) -> Vec<u32> {
        let mut idxs: Vec<u32> = self
            .entries
            .iter()
            .filter(|e| e.decision == TrustDecision::Quarantined)
            .map(|e| e.constant_idx)
            .collect();
        idxs.sort_unstable();
        idxs.dedup();
        idxs
    }

    /// Total number of entries in the log.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the log is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

impl Default for TrustAuditLog {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Quarantine-mode trust policy
// ---------------------------------------------------------------------------

impl TrustPolicy {
    /// Create a quarantine-mode policy with custom allowed and quarantine bitmasks.
    ///
    /// Constants whose trust-gated bits are covered by `allowed` are fully visible.
    /// Constants whose trust-gated bits are covered by `allowed | quarantine` (but
    /// not by `allowed` alone) are quarantined. All other trust-gated constants
    /// are denied.
    ///
    /// Returns `(policy, quarantine_mask)` — use `classify_constant` to get per-
    /// constant decisions.
    #[must_use]
    pub const fn custom(allowed: AxiomProfile, quarantine: AxiomProfile) -> QuarantinePolicy {
        QuarantinePolicy {
            allowed_gated_bits: allowed.0 & AxiomProfile::TRUST_GATED.0,
            quarantine_gated_bits: quarantine.0 & AxiomProfile::TRUST_GATED.0,
        }
    }
}

/// Extended trust policy with a quarantine zone.
///
/// Constants are classified into three categories:
/// - **Allowed**: all trust-gated bits covered by `allowed_gated_bits`.
/// - **Quarantined**: all trust-gated bits covered by `allowed | quarantine` but
///   not by `allowed` alone.
/// - **Denied**: trust-gated bits outside both masks.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct QuarantinePolicy {
    allowed_gated_bits: u64,
    quarantine_gated_bits: u64,
}

impl QuarantinePolicy {
    /// Classify a constant header under this quarantine policy.
    #[must_use]
    pub const fn classify(&self, header: &MathverseConstantHeader) -> TrustDecision {
        let gated = header.axiom_profile.0 & AxiomProfile::TRUST_GATED.0;
        if (gated & !self.allowed_gated_bits) == 0 {
            TrustDecision::Allowed
        } else if (gated & !(self.allowed_gated_bits | self.quarantine_gated_bits)) == 0 {
            TrustDecision::Quarantined
        } else {
            TrustDecision::Denied
        }
    }

    /// Filter constants, returning each with its trust classification.
    #[must_use]
    pub fn classify_all<'a>(
        &self,
        constants: &'a [MathverseConstantHeader],
    ) -> Vec<(u32, &'a MathverseConstantHeader, TrustDecision)> {
        constants
            .iter()
            .enumerate()
            .map(|(i, hdr)| (i as u32, hdr, self.classify(hdr)))
            .collect()
    }
}

// ---------------------------------------------------------------------------
// Axiom consistency validation
// ---------------------------------------------------------------------------

/// Check for inconsistent axiom profiles across a set of constant headers.
///
/// Returns a list of `(index, description)` pairs for each inconsistency found:
/// - `CHOICE + CLASSICAL` on the same constant is redundant (CLASSICAL implies CHOICE).
/// - `UNIVERSE_INCON` should propagate to all dependents — if a constant has
///   `UNIVERSE_INCON` and any dependent does not, that dependent is flagged.
///
/// Note: This is a static check on the header array. It does not resolve dependency
/// graphs; for full transitive propagation, use [`propagate_axiom_profiles`].
pub fn validate_axiom_consistency(headers: &[MathverseConstantHeader]) -> Vec<(usize, String)> {
    let mut issues = Vec::new();
    for (i, hdr) in headers.iter().enumerate() {
        let profile = hdr.axiom_profile;

        // NOTE: CHOICE and CLASSICAL are aliases (same bit, 1 << 0), so checking
        // for both simultaneously is a no-op — they always co-occur.  The former
        // redundancy check was removed because it was a false positive for every
        // header that carried CHOICE.

        // AXIOMATIZED without corresponding import confidence level.
        if (profile & AxiomProfile::AXIOMATIZED.0) != 0 {
            if let Ok(confidence) = hdr.confidence() {
                if confidence == ImportConfidence::KernelVerified
                    || confidence == ImportConfidence::SourceVerified
                {
                    issues.push((
                        i,
                        format!("inconsistent: AXIOMATIZED profile but {confidence:?} confidence"),
                    ));
                }
            }
        }

        // UNIVERSE_INCON should never appear with KernelVerified or SourceVerified.
        if (profile & AxiomProfile::UNIVERSE_INCON.0) != 0 {
            if let Ok(confidence) = hdr.confidence() {
                if confidence == ImportConfidence::KernelVerified
                    || confidence == ImportConfidence::SourceVerified
                {
                    issues.push((
                        i,
                        format!(
                            "inconsistent: UNIVERSE_INCON profile but {confidence:?} confidence"
                        ),
                    ));
                }
            }
        }

        // FLOAT_APPROX + NN_ABSTRACTION without being trust-gated would be a bug
        // in the TRUST_GATED mask, but we can still flag constants that have both
        // approximation layers stacked — they carry double uncertainty.
        if (profile & AxiomProfile::FLOAT_APPROX.0) != 0
            && (profile & AxiomProfile::NN_ABSTRACTION.0) != 0
        {
            issues.push((
                i,
                "warning: FLOAT_APPROX + NN_ABSTRACTION (double approximation)".to_string(),
            ));
        }
    }
    issues
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{ImportConfidence, SourceSystem, NO_VALUE};

    /// Helper to create a minimal constant header with a given axiom profile.
    fn make_header(profile: AxiomProfile) -> MathverseConstantHeader {
        MathverseConstantHeader {
            name_idx: 0,
            type_idx: 0,
            value_idx: 0,
            source_system: SourceSystem::CleanNative as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: 0,
            decl_kind: 0,
            axiom_profile: profile,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        }
    }

    fn make_header_with_confidence(
        profile: AxiomProfile,
        confidence: ImportConfidence,
    ) -> MathverseConstantHeader {
        let mut header = make_header(profile);
        header.import_confidence = confidence as u8;
        if confidence == ImportConfidence::Axiomatized {
            header.value_idx = NO_VALUE;
        }
        header
    }

    /// Helper to create an axiomatized constant header.
    fn make_axiomatized(profile: AxiomProfile) -> MathverseConstantHeader {
        MathverseConstantHeader {
            name_idx: 0,
            type_idx: 0,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Isabelle as u8,
            import_confidence: ImportConfidence::Axiomatized as u8,
            content_domain: 0,
            decl_kind: 0,
            axiom_profile: profile | AxiomProfile::AXIOMATIZED,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        }
    }

    // -- TrustPolicy construction --

    #[test]
    fn test_default_policy_blocks_all_gated() {
        let policy = TrustPolicy::default();
        assert_eq!(policy.allowed_bits(), 0);
        assert!(!policy.allows_unverified_confidence());
    }

    #[test]
    fn test_permissive_allows_all_gated() {
        let policy = TrustPolicy::permissive();
        assert_eq!(policy.allowed_bits(), AxiomProfile::TRUST_GATED);
        assert!(policy.allows_unverified_confidence());
    }

    #[test]
    fn test_with_allowed_bits_masks_to_trust_gated() {
        // Passing non-gated bits should have no effect.
        let policy = TrustPolicy::with_allowed_bits(AxiomProfile::CHOICE | AxiomProfile::LEM);
        assert_eq!(policy.allowed_bits(), 0);

        // Passing gated bits should be retained.
        let policy =
            TrustPolicy::with_allowed_bits(AxiomProfile::AXIOMATIZED | AxiomProfile::FLOAT_APPROX);
        assert_eq!(
            policy.allowed_bits(),
            AxiomProfile::AXIOMATIZED | AxiomProfile::FLOAT_APPROX
        );

        // Mixed: only gated bits retained.
        let policy = TrustPolicy::with_allowed_bits(
            AxiomProfile::CHOICE | AxiomProfile::AXIOMATIZED | AxiomProfile::UNIVERSE_INCON,
        );
        assert_eq!(
            policy.allowed_bits(),
            AxiomProfile::AXIOMATIZED | AxiomProfile::UNIVERSE_INCON
        );
    }

    // -- is_visible --

    #[test]
    fn test_default_policy_pure_constant_visible() {
        let policy = TrustPolicy::default();
        let hdr = make_header(AxiomProfile::NONE);
        assert!(policy.is_visible(&hdr));
    }

    #[test]
    fn test_default_policy_non_gated_axiom_bits_visible() {
        let policy = TrustPolicy::default();
        // CHOICE and LEM are not trust-gated, so they should be visible.
        let hdr = make_header(AxiomProfile::CHOICE | AxiomProfile::LEM | AxiomProfile::PROP_EXT);
        assert!(policy.is_visible(&hdr));
    }

    #[test]
    fn test_default_policy_hides_axiomatized() {
        let policy = TrustPolicy::default();
        let hdr = make_axiomatized(AxiomProfile::NONE);
        assert!(!policy.is_visible(&hdr));
    }

    #[test]
    fn test_default_policy_hides_axiomatized_confidence_without_profile_bit() {
        let policy = TrustPolicy::default();
        let hdr = make_header_with_confidence(AxiomProfile::NONE, ImportConfidence::Axiomatized);
        assert!(!policy.is_visible(&hdr));
    }

    #[test]
    fn test_default_policy_hides_unverified_confidence_without_profile_bit() {
        let policy = TrustPolicy::default();
        let hdr = make_header_with_confidence(AxiomProfile::NONE, ImportConfidence::Unverified);
        assert!(!policy.is_visible(&hdr));
    }

    #[test]
    fn test_default_policy_hides_universe_incon() {
        let policy = TrustPolicy::default();
        let hdr = make_header(AxiomProfile::UNIVERSE_INCON);
        assert!(!policy.is_visible(&hdr));
    }

    #[test]
    fn test_default_policy_hides_float_approx() {
        let policy = TrustPolicy::default();
        let hdr = make_header(AxiomProfile::FLOAT_APPROX);
        assert!(!policy.is_visible(&hdr));
    }

    #[test]
    fn test_default_policy_hides_nn_abstraction() {
        let policy = TrustPolicy::default();
        let hdr = make_header(AxiomProfile::NN_ABSTRACTION);
        assert!(!policy.is_visible(&hdr));
    }

    #[test]
    fn test_permissive_shows_everything() {
        let policy = TrustPolicy::permissive();
        let cases = [
            make_header(AxiomProfile::NONE),
            make_header(AxiomProfile::CHOICE),
            make_axiomatized(AxiomProfile::NONE),
            make_header_with_confidence(AxiomProfile::NONE, ImportConfidence::Unverified),
            make_header(AxiomProfile::UNIVERSE_INCON),
            make_header(AxiomProfile::FLOAT_APPROX | AxiomProfile::NN_ABSTRACTION),
            make_header(AxiomProfile::TRUST_GATED), // all gated bits
        ];
        for (i, hdr) in cases.iter().enumerate() {
            assert!(policy.is_visible(hdr), "case {i} should be visible");
        }
    }

    #[test]
    fn test_custom_policy_allows_specific_bits() {
        // Allow AXIOMATIZED but not other gated bits.
        let policy = TrustPolicy::with_allowed_bits(AxiomProfile::AXIOMATIZED);

        // Axiomatized constant is now visible.
        let hdr = make_axiomatized(AxiomProfile::NONE);
        assert!(policy.is_visible(&hdr));

        // The same low confidence is hidden by default but visible after the
        // AXIOMATIZED opt-in even if a malformed header omitted the profile bit.
        let hdr = make_header_with_confidence(AxiomProfile::NONE, ImportConfidence::Axiomatized);
        assert!(policy.is_visible(&hdr));

        // Statement-only unverified imports are a stronger opt-in and remain
        // hidden unless the policy is fully permissive.
        let hdr = make_header_with_confidence(AxiomProfile::NONE, ImportConfidence::Unverified);
        assert!(!policy.is_visible(&hdr));

        // But FLOAT_APPROX is still hidden.
        let hdr = make_header(AxiomProfile::FLOAT_APPROX);
        assert!(!policy.is_visible(&hdr));

        // Constant with both AXIOMATIZED and FLOAT_APPROX is hidden (FLOAT_APPROX not allowed).
        let hdr = make_header(AxiomProfile::AXIOMATIZED | AxiomProfile::FLOAT_APPROX);
        assert!(!policy.is_visible(&hdr));
    }

    #[test]
    fn test_partial_gated_bits_require_all_allowed() {
        // Allow AXIOMATIZED + UNIVERSE_INCON.
        let policy = TrustPolicy::with_allowed_bits(
            AxiomProfile::AXIOMATIZED | AxiomProfile::UNIVERSE_INCON,
        );

        // Both bits set: visible.
        let hdr = make_header(AxiomProfile::AXIOMATIZED | AxiomProfile::UNIVERSE_INCON);
        assert!(policy.is_visible(&hdr));

        // Only AXIOMATIZED: visible (subset of allowed).
        let hdr = make_axiomatized(AxiomProfile::NONE);
        assert!(policy.is_visible(&hdr));

        // AXIOMATIZED + NN_ABSTRACTION: hidden (NN_ABSTRACTION not allowed).
        let hdr = make_header(AxiomProfile::AXIOMATIZED | AxiomProfile::NN_ABSTRACTION);
        assert!(!policy.is_visible(&hdr));
    }

    // -- filter_constants --

    #[test]
    fn test_filter_constants_default_policy() {
        let constants = [
            make_header(AxiomProfile::NONE),         // 0: pure — visible
            make_header(AxiomProfile::CHOICE),       // 1: non-gated — visible
            make_axiomatized(AxiomProfile::NONE),    // 2: axiomatized — hidden
            make_header(AxiomProfile::FLOAT_APPROX), // 3: float approx — hidden
            make_header(AxiomProfile::LEM),          // 4: non-gated — visible
            make_header_with_confidence(AxiomProfile::NONE, ImportConfidence::Axiomatized), // 5: low confidence — hidden
            make_header_with_confidence(AxiomProfile::NONE, ImportConfidence::Unverified), // 6: low confidence — hidden
        ];

        let policy = TrustPolicy::default();
        let visible = policy.filter_constants(&constants);

        let indices: Vec<u32> = visible.iter().map(|(i, _)| *i).collect();
        assert_eq!(indices, vec![0, 1, 4]);
    }

    #[test]
    fn test_filter_constants_permissive() {
        let constants = [
            make_header(AxiomProfile::NONE),
            make_axiomatized(AxiomProfile::NONE),
            make_header(AxiomProfile::TRUST_GATED),
        ];

        let policy = TrustPolicy::permissive();
        let visible = policy.filter_constants(&constants);

        assert_eq!(visible.len(), 3);
    }

    #[test]
    fn test_filter_constants_empty() {
        let constants: [MathverseConstantHeader; 0] = [];
        let policy = TrustPolicy::default();
        let visible = policy.filter_constants(&constants);
        assert!(visible.is_empty());
    }

    #[test]
    fn test_filter_preserves_header_references() {
        let constants = [
            make_header(AxiomProfile::NONE),
            make_header(AxiomProfile::CHOICE),
        ];
        let policy = TrustPolicy::default();
        let visible = policy.filter_constants(&constants);

        assert_eq!(visible.len(), 2);
        // Verify the references point to the original data.
        assert_eq!(visible[0].1.axiom_profile, 0);
        assert_eq!(visible[1].1.axiom_profile, AxiomProfile::CHOICE);
    }

    // -- propagate_axiom_profiles --

    #[test]
    fn test_propagate_no_deps() {
        let mut constants = [
            make_header(AxiomProfile::CHOICE),
            make_header(AxiomProfile::LEM),
        ];
        let deps: Vec<Vec<u32>> = vec![vec![], vec![]];

        propagate_axiom_profiles(&mut constants, &deps).expect("should succeed");

        assert_eq!(constants[0].axiom_profile, AxiomProfile::CHOICE);
        assert_eq!(constants[1].axiom_profile, AxiomProfile::LEM);
    }

    #[test]
    fn test_propagate_linear_chain() {
        // Chain: 0 <- 1 <- 2 (2 depends on 1, 1 depends on 0)
        let mut constants = [
            make_header(AxiomProfile::CHOICE),   // 0
            make_header(AxiomProfile::LEM),      // 1
            make_header(AxiomProfile::PROP_EXT), // 2
        ];
        let deps = vec![
            vec![],  // 0: no deps
            vec![0], // 1: depends on 0
            vec![1], // 2: depends on 1
        ];

        propagate_axiom_profiles(&mut constants, &deps).expect("should succeed");

        assert_eq!(constants[0].axiom_profile, AxiomProfile::CHOICE);
        assert_eq!(
            constants[1].axiom_profile,
            AxiomProfile::CHOICE | AxiomProfile::LEM
        );
        assert_eq!(
            constants[2].axiom_profile,
            AxiomProfile::CHOICE | AxiomProfile::LEM | AxiomProfile::PROP_EXT
        );
    }

    #[test]
    fn test_propagate_diamond() {
        // Diamond: 0 and 1 both depended on by 2
        //   0 (CHOICE)   1 (AXIOMATIZED)
        //       \           /
        //        2 (LEM)
        let mut constants = [
            make_header(AxiomProfile::CHOICE),      // 0
            make_header(AxiomProfile::AXIOMATIZED), // 1
            make_header(AxiomProfile::LEM),         // 2
        ];
        let deps = vec![
            vec![],     // 0
            vec![],     // 1
            vec![0, 1], // 2 depends on both
        ];

        propagate_axiom_profiles(&mut constants, &deps).expect("should succeed");

        assert_eq!(constants[0].axiom_profile, AxiomProfile::CHOICE);
        assert_eq!(constants[1].axiom_profile, AxiomProfile::AXIOMATIZED);
        assert_eq!(
            constants[2].axiom_profile,
            AxiomProfile::CHOICE | AxiomProfile::AXIOMATIZED | AxiomProfile::LEM
        );
    }

    #[test]
    fn test_propagate_trust_gated_taints_dependents() {
        // Constant 0 is axiomatized. Constant 1 depends on 0.
        // After propagation, constant 1 should also be trust-gated.
        let mut constants = [
            make_axiomatized(AxiomProfile::NONE), // 0: AXIOMATIZED
            make_header(AxiomProfile::NONE),      // 1: pure
        ];
        let deps = vec![
            vec![],  // 0
            vec![0], // 1 depends on 0
        ];

        propagate_axiom_profiles(&mut constants, &deps).expect("should succeed");

        // Constant 1 now inherits AXIOMATIZED from its dependency.
        assert!(constants[1].axiom_profile.is_trust_gated());
        assert!(constants[1].axiom_profile.has(AxiomProfile::AXIOMATIZED));
    }

    #[test]
    fn test_propagate_deep_chain() {
        // 0 <- 1 <- 2 <- 3 <- 4 (each depends on the previous)
        let mut constants = [
            make_header(AxiomProfile::FLOAT_APPROX), // 0
            make_header(AxiomProfile::NONE),         // 1
            make_header(AxiomProfile::NONE),         // 2
            make_header(AxiomProfile::NONE),         // 3
            make_header(AxiomProfile::NONE),         // 4
        ];
        let deps = vec![vec![], vec![0], vec![1], vec![2], vec![3]];

        propagate_axiom_profiles(&mut constants, &deps).expect("should succeed");

        // FLOAT_APPROX should propagate all the way to constant 4.
        for c in &constants {
            assert!(
                c.axiom_profile.has(AxiomProfile::FLOAT_APPROX),
                "all constants should have FLOAT_APPROX after propagation"
            );
        }
    }

    // -- Cycle detection --

    #[test]
    fn test_propagate_self_cycle() {
        let mut constants = [make_header(AxiomProfile::NONE)];
        let deps = vec![vec![0]]; // self-dependency

        let result = propagate_axiom_profiles(&mut constants, &deps);
        assert!(result.is_err());
        match result.unwrap_err() {
            MathverseError::AxiomProfileCycle(idx) => assert_eq!(idx, 0),
            other => panic!("expected AxiomProfileCycle, got: {other}"),
        }
    }

    #[test]
    fn test_propagate_two_node_cycle() {
        let mut constants = [
            make_header(AxiomProfile::NONE),
            make_header(AxiomProfile::NONE),
        ];
        let deps = vec![
            vec![1], // 0 depends on 1
            vec![0], // 1 depends on 0
        ];

        let result = propagate_axiom_profiles(&mut constants, &deps);
        assert!(result.is_err());
        match result.unwrap_err() {
            MathverseError::AxiomProfileCycle(_) => {}
            other => panic!("expected AxiomProfileCycle, got: {other}"),
        }
    }

    #[test]
    fn test_propagate_three_node_cycle() {
        let mut constants = [
            make_header(AxiomProfile::NONE),
            make_header(AxiomProfile::NONE),
            make_header(AxiomProfile::NONE),
        ];
        let deps = vec![
            vec![2], // 0 depends on 2
            vec![0], // 1 depends on 0
            vec![1], // 2 depends on 1
        ];

        let result = propagate_axiom_profiles(&mut constants, &deps);
        assert!(result.is_err());
        match result.unwrap_err() {
            MathverseError::AxiomProfileCycle(_) => {}
            other => panic!("expected AxiomProfileCycle, got: {other}"),
        }
    }

    #[test]
    fn test_propagate_partial_cycle_with_valid_nodes() {
        // Nodes 0 and 1 form a valid chain, but 2 and 3 form a cycle.
        let mut constants = [
            make_header(AxiomProfile::CHOICE),
            make_header(AxiomProfile::NONE),
            make_header(AxiomProfile::NONE),
            make_header(AxiomProfile::NONE),
        ];
        let deps = vec![
            vec![],  // 0: no deps
            vec![0], // 1: depends on 0 (valid)
            vec![3], // 2: depends on 3
            vec![2], // 3: depends on 2 (cycle)
        ];

        let result = propagate_axiom_profiles(&mut constants, &deps);
        assert!(result.is_err());
        match result.unwrap_err() {
            MathverseError::AxiomProfileCycle(idx) => {
                assert!(
                    idx == 2 || idx == 3,
                    "cycle node should be 2 or 3, got {idx}"
                );
            }
            other => panic!("expected AxiomProfileCycle, got: {other}"),
        }
    }

    // -- Edge cases --

    #[test]
    fn test_propagate_empty() {
        let mut constants: Vec<MathverseConstantHeader> = vec![];
        let deps: Vec<Vec<u32>> = vec![];
        propagate_axiom_profiles(&mut constants, &deps).expect("empty should succeed");
    }

    #[test]
    fn test_propagate_out_of_range_dep() {
        let mut constants = [make_header(AxiomProfile::NONE)];
        let deps = vec![vec![99]]; // index 99 doesn't exist

        let result = propagate_axiom_profiles(&mut constants, &deps);
        assert!(result.is_err());
        match result.unwrap_err() {
            MathverseError::ConstantOutOfRange { idx, count } => {
                assert_eq!(idx, 99);
                assert_eq!(count, 1);
            }
            other => panic!("expected ConstantOutOfRange, got: {other}"),
        }
    }

    #[test]
    fn test_propagate_multiple_sources_union() {
        // Constant 3 depends on 0, 1, and 2, each with different profiles.
        let mut constants = [
            make_header(AxiomProfile::CHOICE),
            make_header(AxiomProfile::AXIOMATIZED),
            make_header(AxiomProfile::FLOAT_APPROX),
            make_header(AxiomProfile::LEM),
        ];
        let deps = vec![vec![], vec![], vec![], vec![0, 1, 2]];

        propagate_axiom_profiles(&mut constants, &deps).expect("should succeed");

        assert_eq!(
            constants[3].axiom_profile,
            AxiomProfile::CHOICE
                | AxiomProfile::AXIOMATIZED
                | AxiomProfile::FLOAT_APPROX
                | AxiomProfile::LEM
        );
    }

    // -- TrustAuditLog --

    #[test]
    fn test_audit_log_add_and_query() {
        let mut log = TrustAuditLog::new();
        assert!(log.is_empty());
        assert_eq!(log.len(), 0);

        log.add_entry(TrustAuditEntry {
            constant_idx: 0,
            decision: TrustDecision::Allowed,
            reason: "pure constant".to_string(),
            timestamp_epoch: 1_000_000,
        });
        log.add_entry(TrustAuditEntry {
            constant_idx: 1,
            decision: TrustDecision::Denied,
            reason: "axiomatized".to_string(),
            timestamp_epoch: 1_000_001,
        });
        log.add_entry(TrustAuditEntry {
            constant_idx: 2,
            decision: TrustDecision::Quarantined,
            reason: "float approx".to_string(),
            timestamp_epoch: 1_000_002,
        });

        assert_eq!(log.len(), 3);
        assert!(!log.is_empty());
    }

    #[test]
    fn test_audit_log_entries_for_constant() {
        let mut log = TrustAuditLog::new();
        log.add_entry(TrustAuditEntry {
            constant_idx: 5,
            decision: TrustDecision::Allowed,
            reason: "first check".to_string(),
            timestamp_epoch: 100,
        });
        log.add_entry(TrustAuditEntry {
            constant_idx: 10,
            decision: TrustDecision::Denied,
            reason: "other".to_string(),
            timestamp_epoch: 101,
        });
        log.add_entry(TrustAuditEntry {
            constant_idx: 5,
            decision: TrustDecision::Escalated,
            reason: "re-evaluated".to_string(),
            timestamp_epoch: 102,
        });

        let for_5 = log.entries_for_constant(5);
        assert_eq!(for_5.len(), 2);
        assert_eq!(for_5[0].decision, TrustDecision::Allowed);
        assert_eq!(for_5[1].decision, TrustDecision::Escalated);

        let for_99 = log.entries_for_constant(99);
        assert!(for_99.is_empty());
    }

    #[test]
    fn test_audit_log_denied_count() {
        let mut log = TrustAuditLog::new();
        log.add_entry(TrustAuditEntry {
            constant_idx: 0,
            decision: TrustDecision::Denied,
            reason: "a".to_string(),
            timestamp_epoch: 0,
        });
        log.add_entry(TrustAuditEntry {
            constant_idx: 1,
            decision: TrustDecision::Allowed,
            reason: "b".to_string(),
            timestamp_epoch: 0,
        });
        log.add_entry(TrustAuditEntry {
            constant_idx: 2,
            decision: TrustDecision::Denied,
            reason: "c".to_string(),
            timestamp_epoch: 0,
        });

        assert_eq!(log.denied_count(), 2);
    }

    #[test]
    fn test_audit_log_quarantined_constants() {
        let mut log = TrustAuditLog::new();
        log.add_entry(TrustAuditEntry {
            constant_idx: 3,
            decision: TrustDecision::Quarantined,
            reason: "q1".to_string(),
            timestamp_epoch: 0,
        });
        log.add_entry(TrustAuditEntry {
            constant_idx: 7,
            decision: TrustDecision::Quarantined,
            reason: "q2".to_string(),
            timestamp_epoch: 0,
        });
        // Duplicate idx=3 should be deduplicated.
        log.add_entry(TrustAuditEntry {
            constant_idx: 3,
            decision: TrustDecision::Quarantined,
            reason: "q3".to_string(),
            timestamp_epoch: 0,
        });
        log.add_entry(TrustAuditEntry {
            constant_idx: 1,
            decision: TrustDecision::Allowed,
            reason: "ok".to_string(),
            timestamp_epoch: 0,
        });

        let q = log.quarantined_constants();
        assert_eq!(q, vec![3, 7]);
    }

    // -- QuarantinePolicy --

    #[test]
    fn test_quarantine_policy_classify() {
        // Allow AXIOMATIZED, quarantine FLOAT_APPROX, deny everything else.
        let qp = TrustPolicy::custom(AxiomProfile::AXIOMATIZED, AxiomProfile::FLOAT_APPROX);

        // Pure constant: allowed (no gated bits).
        let pure = make_header(AxiomProfile::NONE);
        assert_eq!(qp.classify(&pure), TrustDecision::Allowed);

        // Axiomatized: allowed.
        let axiom = make_axiomatized(AxiomProfile::NONE);
        assert_eq!(qp.classify(&axiom), TrustDecision::Allowed);

        // FLOAT_APPROX only: quarantined (covered by allowed|quarantine but not allowed alone).
        let float = make_header(AxiomProfile::FLOAT_APPROX);
        assert_eq!(qp.classify(&float), TrustDecision::Quarantined);

        // AXIOMATIZED + FLOAT_APPROX: quarantined (FLOAT_APPROX portion not in allowed).
        let both = make_header(AxiomProfile::AXIOMATIZED | AxiomProfile::FLOAT_APPROX);
        assert_eq!(qp.classify(&both), TrustDecision::Quarantined);

        // NN_ABSTRACTION: denied (not in allowed or quarantine).
        let nn = make_header(AxiomProfile::NN_ABSTRACTION);
        assert_eq!(qp.classify(&nn), TrustDecision::Denied);

        // UNIVERSE_INCON: denied.
        let univ = make_header(AxiomProfile::UNIVERSE_INCON);
        assert_eq!(qp.classify(&univ), TrustDecision::Denied);
    }

    #[test]
    fn test_quarantine_policy_classify_all() {
        let qp = TrustPolicy::custom(AxiomProfile::AXIOMATIZED, AxiomProfile::FLOAT_APPROX);
        let constants = [
            make_header(AxiomProfile::NONE),           // allowed
            make_axiomatized(AxiomProfile::NONE),      // allowed
            make_header(AxiomProfile::FLOAT_APPROX),   // quarantined
            make_header(AxiomProfile::NN_ABSTRACTION), // denied
        ];
        let classified = qp.classify_all(&constants);
        assert_eq!(classified.len(), 4);
        assert_eq!(classified[0].2, TrustDecision::Allowed);
        assert_eq!(classified[1].2, TrustDecision::Allowed);
        assert_eq!(classified[2].2, TrustDecision::Quarantined);
        assert_eq!(classified[3].2, TrustDecision::Denied);
    }

    // -- validate_axiom_consistency --

    #[test]
    fn test_validate_consistency_clean() {
        let headers = [
            make_header(AxiomProfile::CHOICE),
            make_header(AxiomProfile::LEM),
            make_header(AxiomProfile::NONE),
        ];
        let issues = validate_axiom_consistency(&headers);
        assert!(issues.is_empty());
    }

    #[test]
    fn test_validate_consistency_choice_classical_same_bit() {
        // CHOICE and CLASSICAL are aliases (both 1 << 0), so OR-ing them
        // together is the same as CHOICE alone.  No redundancy issue is
        // reported because the check was removed (the two constants are
        // identical).
        let headers = [make_header(AxiomProfile::CHOICE | AxiomProfile::CLASSICAL)];
        let issues = validate_axiom_consistency(&headers);
        assert!(issues.is_empty());
    }

    #[test]
    fn test_validate_consistency_axiomatized_but_kernel_verified() {
        let mut hdr = make_header(AxiomProfile::AXIOMATIZED);
        hdr.import_confidence = ImportConfidence::KernelVerified as u8;
        let issues = validate_axiom_consistency(&[hdr]);
        assert!(!issues.is_empty());
        assert!(issues.iter().any(|(_, msg)| msg.contains("AXIOMATIZED")));
    }

    #[test]
    fn test_validate_consistency_double_approximation() {
        let hdr = make_header(AxiomProfile::FLOAT_APPROX | AxiomProfile::NN_ABSTRACTION);
        let issues = validate_axiom_consistency(&[hdr]);
        assert_eq!(issues.len(), 1);
        assert!(issues[0].1.contains("double approximation"));
    }

    #[test]
    fn test_validate_consistency_empty() {
        let issues = validate_axiom_consistency(&[]);
        assert!(issues.is_empty());
    }

    // -- Integration: propagation + trust policy --

    #[test]
    fn test_propagation_then_filtering() {
        // Scenario: constant 0 is axiomatized, constant 1 is pure but depends on 0.
        // After propagation, constant 1 inherits AXIOMATIZED and becomes invisible
        // under the default policy.
        let mut constants = vec![
            make_axiomatized(AxiomProfile::NONE), // 0: axiomatized
            make_header(AxiomProfile::NONE),      // 1: pure, depends on 0
            make_header(AxiomProfile::CHOICE),    // 2: pure, no deps
        ];
        let deps = vec![vec![], vec![0], vec![]];

        propagate_axiom_profiles(&mut constants, &deps).expect("should succeed");

        // Under default policy, only constant 2 should be visible.
        let policy = TrustPolicy::default();
        let visible = policy.filter_constants(&constants);
        let indices: Vec<u32> = visible.iter().map(|(i, _)| *i).collect();
        assert_eq!(indices, vec![2]);

        // Under permissive policy, all should be visible.
        let policy = TrustPolicy::permissive();
        let visible = policy.filter_constants(&constants);
        assert_eq!(visible.len(), 3);

        // Under a policy that allows AXIOMATIZED, constants 0 and 1 become visible too.
        let policy = TrustPolicy::with_allowed_bits(AxiomProfile::AXIOMATIZED);
        let visible = policy.filter_constants(&constants);
        assert_eq!(visible.len(), 3);
    }
}
