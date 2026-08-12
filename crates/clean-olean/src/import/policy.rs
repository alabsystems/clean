// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Import trust policy for `.olean` loading.

use super::load_parse::LoadModule;
use super::ImportError;
use crate::module::ParsedModule;
use clean_kernel::env::ProofValueElision;

/// Policy decision for unpinned external `.olean` imports.
///
/// This is only an admission policy. `Allow` is the historical behavior, and
/// `Reject` fails closed unless a future caller supplies a real pin/hash
/// verification path before registration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnpinnedOleanImportPolicy {
    /// Preserve legacy behavior and allow unpinned `.olean` constants.
    Allow,
    /// Reject unpinned `.olean` constants before they are registered.
    Reject,
}

/// Which declaration KINDS a `.olean` import registers into the environment.
///
/// The default ([`ImportKinds::All`]) registers every kind — the historical
/// behavior. [`ImportKinds::InductiveFamiliesOnly`] registers ONLY the
/// inductive-family kinds (`Inductive` / `Constructor` / `Recursor` / `Quot`)
/// and SKIPS `Definition` / `Theorem` / `Axiom` / `Opaque`. It is the eager leg
/// of the Phase-1 zero-copy HYBRID closure loader (see
/// `~/kv-ceiling-roadmap.md`): the inductive families cannot be served lazily
/// (the `.mathverse` shard format cannot losslessly carry recursor reduction
/// rules — a confirmed false-accept hole), so they stay eager; the
/// definitional kinds ARE served lazily by a `ConstantSource` over the closure
/// shards, so registering them eagerly here would defeat the memory win.
///
/// SOUNDNESS: filtering by kind only changes WHICH trusted-closure constants
/// live in `Environment::constants` vs. are served by the lazy source. A name's
/// `ConstantInfo` is identical either way (the lazy source materializes the same
/// bytes the eager path would have built), pinned by the eager-vs-lazy
/// KernelVerified-set invariance gate. It never adds, drops, or alters a
/// verdict — a definitional constant skipped here is reachable through
/// `Environment::get_const`'s lazy fallback.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ImportKinds {
    /// Register every declaration kind (historical default).
    All,
    /// Register only the inductive-family kinds (`Inductive` / `Constructor` /
    /// `Recursor` / `Quot`); skip the lazily-servable definitional kinds.
    InductiveFamiliesOnly,
}

/// Admission policy for loading constants from `.olean` files.
///
/// The default intentionally preserves existing callers: unpinned imports are
/// allowed and then tagged with origin metadata. Use
/// [`OleanImportPolicy::reject_unpinned_external`] to fail closed before
/// registration. This type does not perform package pin or hash verification.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OleanImportPolicy {
    unpinned_external: UnpinnedOleanImportPolicy,
    /// Bounded-memory closure loading (WS3): which never-unfolded proof VALUES
    /// to DROP at registration time so the proof-term Expr DAGs are freed as
    /// each module is loaded — capping PEAK resident memory rather than only
    /// steady-state. Default [`ProofValueElision::None`] preserves every value.
    proof_elision: ProofValueElision,
    /// Phase-1 zero-copy HYBRID closure loading: which declaration KINDS to
    /// register. Default [`ImportKinds::All`] is the historical behavior;
    /// [`ImportKinds::InductiveFamiliesOnly`] registers only the inductive
    /// families eagerly and leaves the definitional kinds to the lazy
    /// `ConstantSource`. See [`ImportKinds`].
    import_kinds: ImportKinds,
    /// Defer the O(env) HEURISTIC instance/structure-field backfill passes
    /// (`register_class_typed_definitions_as_instances`,
    /// `register_structure_fields_from_projections`) so they run ONCE after the
    /// whole import closure is loaded instead of after EVERY module.
    ///
    /// PERF: those two passes each re-scan the entire growing environment. Run
    /// per-module across an N-module closure (e.g. `Init` ≈ 320 modules / 57K
    /// constants) that is O(N × env) — a quadratic that dominates the `Init`
    /// pre-load. Deferring collapses it to a single O(env) pass.
    ///
    /// SOUNDNESS/BEHAVIOR: both passes are additive, idempotent, and
    /// order-insensitive w.r.t. the DECODED real-`@[class]`/`@[instance]`
    /// registrations (which still run per-module BEFORE the deferred passes, so
    /// first-writer-wins is preserved). The final registry is identical to the
    /// per-module schedule; only WHEN the heuristic runs changes. Default
    /// `false` keeps the historical per-module schedule for every existing
    /// caller. Only the closure entry [`load_module_with_deps_with_import_policy`]
    /// honours it (it runs the single end-pass), so it is safe to set only on
    /// that path.
    defer_global_instance_backfill: bool,
}

impl OleanImportPolicy {
    /// Construct a policy from the unpinned external import decision.
    #[must_use]
    pub const fn new(unpinned_external: UnpinnedOleanImportPolicy) -> Self {
        Self {
            unpinned_external,
            proof_elision: ProofValueElision::None,
            import_kinds: ImportKinds::All,
            defer_global_instance_backfill: false,
        }
    }

    /// Return a copy of this policy with the given bounded-memory proof-value
    /// elision applied at registration time (WS3).
    ///
    /// SOUNDNESS: with [`ProofValueElision::OpaqueOnly`] this is verdict-
    /// preserving — the kernel never δ-unfolds an `Opaque` value, so dropping it
    /// before it is ever stored cannot change a type-check result. Only ever set
    /// this on a TRUSTED IMPORTED CLOSURE load; never on a module whose own
    /// decls must be kernel-checked with their values intact.
    #[must_use]
    pub const fn with_proof_elision(mut self, proof_elision: ProofValueElision) -> Self {
        self.proof_elision = proof_elision;
        self
    }

    /// The configured bounded-memory proof-value elision.
    #[must_use]
    pub const fn proof_elision(self) -> ProofValueElision {
        self.proof_elision
    }

    /// Return a copy of this policy restricting registration to the given
    /// declaration KINDS (Phase-1 zero-copy HYBRID closure loading).
    ///
    /// SOUNDNESS: see [`ImportKinds`]. Restricting kinds only moves a
    /// definitional constant from the eager `Environment::constants` map to the
    /// lazy `ConstantSource`; `get_const` returns the identical `ConstantInfo`
    /// either way, so no verdict can change. Only ever set
    /// [`ImportKinds::InductiveFamiliesOnly`] on a TRUSTED IMPORTED CLOSURE load
    /// whose definitional kinds are simultaneously installed as a lazy source.
    #[must_use]
    pub const fn with_import_kinds(mut self, import_kinds: ImportKinds) -> Self {
        self.import_kinds = import_kinds;
        self
    }

    /// The configured declaration-kind registration filter.
    #[must_use]
    pub const fn import_kinds(self) -> ImportKinds {
        self.import_kinds
    }

    /// Return a copy of this policy that DEFERS the O(env) heuristic
    /// instance/structure-field backfill passes to a single end-of-closure run.
    ///
    /// See [`defer_global_instance_backfill`](Self::defer_global_instance_backfill).
    /// Only [`load_module_with_deps_with_import_policy`] acts on this (it runs the
    /// single deferred pass after the closure loads); set it only on that path.
    #[must_use]
    pub const fn with_deferred_global_instance_backfill(mut self) -> Self {
        self.defer_global_instance_backfill = true;
        self
    }

    /// Whether the O(env) heuristic instance/structure-field backfill is deferred
    /// to a single end-of-closure pass (see
    /// [`with_deferred_global_instance_backfill`](Self::with_deferred_global_instance_backfill)).
    #[must_use]
    pub const fn defer_global_instance_backfill(self) -> bool {
        self.defer_global_instance_backfill
    }

    /// Whether this policy registers only inductive-family kinds (the eager leg
    /// of the Phase-1 HYBRID closure loader).
    #[must_use]
    pub const fn inductive_families_only(self) -> bool {
        matches!(self.import_kinds, ImportKinds::InductiveFamiliesOnly)
    }

    /// Legacy/default behavior: load unpinned `.olean` constants and tag them.
    #[must_use]
    pub const fn allow_unpinned_legacy() -> Self {
        Self::new(UnpinnedOleanImportPolicy::Allow)
    }

    /// Reject unpinned external `.olean` constants before registration.
    #[must_use]
    pub const fn reject_unpinned_external() -> Self {
        Self::new(UnpinnedOleanImportPolicy::Reject)
    }

    /// The configured decision for unpinned external `.olean` constants.
    #[must_use]
    pub const fn unpinned_external(self) -> UnpinnedOleanImportPolicy {
        self.unpinned_external
    }

    pub(crate) fn check_parsed_module(
        self,
        module: &ParsedModule,
        module_name: Option<&str>,
    ) -> Result<(), ImportError> {
        let olean_constants = module
            .constants
            .iter()
            .filter(|constant| !constant.name.is_empty() || constant.type_.is_some())
            .count();
        let clean_payload_constants = module
            .clean_payload
            .as_ref()
            .map_or(0, crate::payload::CleanPayload::total_constants);
        self.check_unpinned_counts(module_name, olean_constants, clean_payload_constants)
    }

    pub(crate) fn check_load_module(
        self,
        module: &LoadModule,
        module_name: Option<&str>,
    ) -> Result<(), ImportError> {
        let olean_constants = module
            .constants
            .iter()
            .filter(|constant| !constant.name.is_empty() || constant.type_ptr != 0)
            .count();
        let clean_payload_constants = module
            .clean_payload
            .as_ref()
            .map_or(0, crate::payload::CleanPayload::total_constants);
        self.check_unpinned_counts(module_name, olean_constants, clean_payload_constants)
    }

    fn check_unpinned_counts(
        self,
        module_name: Option<&str>,
        olean_constants: usize,
        clean_payload_constants: usize,
    ) -> Result<(), ImportError> {
        if self.unpinned_external == UnpinnedOleanImportPolicy::Allow {
            return Ok(());
        }

        if olean_constants == 0 && clean_payload_constants == 0 {
            return Ok(());
        }

        Err(ImportError::UnpinnedExternalOleanRejected {
            module: module_name.unwrap_or("<unknown>").to_string(),
            olean_constants,
            clean_payload_constants,
        })
    }
}

impl Default for OleanImportPolicy {
    fn default() -> Self {
        Self::allow_unpinned_legacy()
    }
}

#[cfg(test)]
mod import_kinds_tests {
    use super::*;

    #[test]
    fn test_default_policy_imports_all_kinds() {
        let p = OleanImportPolicy::default();
        assert_eq!(p.import_kinds(), ImportKinds::All);
        assert!(!p.inductive_families_only());
    }

    #[test]
    fn test_with_import_kinds_restricts_to_inductive_families() {
        let p = OleanImportPolicy::default().with_import_kinds(ImportKinds::InductiveFamiliesOnly);
        assert_eq!(p.import_kinds(), ImportKinds::InductiveFamiliesOnly);
        assert!(p.inductive_families_only());
    }

    #[test]
    fn test_import_kinds_is_orthogonal_to_proof_elision_and_unpinned() {
        // The HYBRID kinds filter composes with the other policy knobs without
        // disturbing them (the closure loader sets all three).
        let p = OleanImportPolicy::reject_unpinned_external()
            .with_proof_elision(ProofValueElision::OpaqueOnly)
            .with_import_kinds(ImportKinds::InductiveFamiliesOnly);
        assert_eq!(p.unpinned_external(), UnpinnedOleanImportPolicy::Reject);
        assert_eq!(p.proof_elision(), ProofValueElision::OpaqueOnly);
        assert!(p.inductive_families_only());
    }
}
