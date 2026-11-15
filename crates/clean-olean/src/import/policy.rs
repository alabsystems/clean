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

/// Which of `artifact_ledger`'s module-trust rules 1-3 a load leaves to the
/// caller's replay, recording instead of refusing the import (see
/// [`OleanImportPolicy::with_replay_refusals`] and
/// [`OleanImportPolicy::with_module_replay_refusals`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LeftToReplay {
    /// Nothing: every rule refuses the import (the default).
    Nothing,
    /// Rules 1, 2 and 3 (`clean olean replay`'s load of a whole closure).
    /// Only that verb constructs it, so a build without the `cli` feature
    /// never does.
    #[cfg_attr(not(any(feature = "cli", test)), allow(dead_code))]
    AllThreeRules,
    /// Rules 1 and 3, for the one module a caller replays; rule 2, a name an
    /// EARLIER artifact referred to before any of its imports declared it,
    /// still refuses the import.
    ModuleRules,
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
    /// Historical API spelling: retry explicit persistent instance records at
    /// the end of a closure, after more referenced constants are available.
    /// Per-module source-backed registration still runs. The former global
    /// definition-type heuristic is removed: a class-valued definition is not
    /// an instance, and a structure is not a class without source metadata.
    /// This option never authorizes inference of missing registrations or
    /// changes the proof-value/inductive loading policies above. Only
    /// [`load_module_with_deps_with_import_policy`] runs the final retry.
    defer_global_instance_backfill: bool,
    /// Register only what Lean's kernel reads: the declarations and their
    /// safety. Skips every elaborator-side table the loader otherwise derives
    /// (persistent extension entries — instances, classes, simp lemmas,
    /// structure metadata, aliases, reducibility attributes — and the binder
    /// name side tables). See [`Self::with_kernel_only`].
    kernel_only: bool,
    /// Record, rather than refuse the import for, the artifact-consistency
    /// findings a replay refuses itself, per declaration. See
    /// [`Self::with_replay_refusals`] and [`Self::with_module_replay_refusals`].
    left_to_replay: LeftToReplay,
    /// Whether a refused completion of an artifact's own stub refuses the
    /// import (R131). See [`Self::refusing_refused_completions`].
    refused_completions: RefusedCompletions,
}

/// What a load does with a value a later part of an artifact gives for that
/// artifact's own value-free stub, when the kernel refuses it at the checked
/// upgrade (R131).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RefusedCompletions {
    /// Recorded (`LoadSummary::refused_completions`); the stub stays resident.
    /// An import trusted as Lean's importer trusts it, in whatever environment
    /// the caller supplies (the default).
    Recorded,
    /// The import is refused (`ImportError::CompletionRefused`): a re-check
    /// lane's load over Lean's world.
    RefuseImport,
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
            kernel_only: false,
            left_to_replay: LeftToReplay::Nothing,
            refused_completions: RefusedCompletions::Recorded,
        }
    }

    /// Return a copy of this policy under which a value a later part of an
    /// artifact gives for that artifact's own value-free stub, refused by the
    /// kernel at the checked upgrade, refuses the import
    /// (`ImportError::CompletionRefused`, R131) — the policy of a RE-CHECK lane
    /// (verify-batch, `stamp-verified`, the mathverse sharded worker's imports),
    /// which loads over Lean's world (`Environment::for_lean_replay`) and must
    /// not trust a stub whose declaration, as Lean reads it, the kernel refused
    /// (review finding S1: the sharded worker counted such a stub as an accepted
    /// axiom and verified its user).
    ///
    /// Not the default. An import loaded the way Lean's importer loads it — the
    /// elaborator's, over Clean's prelude — trusts its declarations, and there
    /// the kernel's verdict on Lean's value is not Lean's: measured 2026-10-23,
    /// `Init.GetElem`'s `Array.instLawfulGetElemNatLtSize` is refused over
    /// `Environment::try_with_prelude_for_import` and admitted over
    /// `Environment::for_lean_replay`. Such a load records the refusal
    /// (`LoadSummary::refused_completions`) and keeps the stub. A load that
    /// leaves rules to a replay records it under either setting, for the replay
    /// to refuse by name.
    #[must_use]
    pub const fn refusing_refused_completions(mut self) -> Self {
        self.refused_completions = RefusedCompletions::RefuseImport;
        self
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
    pub(crate) const fn import_kinds(self) -> ImportKinds {
        self.import_kinds
    }

    /// Retain the historical option spelling while requesting an end-of-closure
    /// retry of explicit persistent instance records, never heuristic inference.
    ///
    /// See [`defer_global_instance_backfill`](Self::defer_global_instance_backfill).
    /// Only [`load_module_with_deps_with_import_policy`] acts on this (it runs the
    /// single deferred pass after the closure loads); set it only on that path.
    #[must_use]
    pub(crate) const fn with_deferred_global_instance_backfill(mut self) -> Self {
        self.defer_global_instance_backfill = true;
        self
    }

    /// Whether explicit persistent instance records receive a final retry (see
    /// [`with_deferred_global_instance_backfill`](Self::with_deferred_global_instance_backfill)).
    #[must_use]
    pub(crate) const fn defer_global_instance_backfill(self) -> bool {
        self.defer_global_instance_backfill
    }

    /// Return a copy of this policy that registers only what Lean's kernel
    /// reads (the `clean olean replay` load).
    ///
    /// `Lean.Environment.replay` checks declarations against a kernel
    /// environment, and Lean's kernel reads no environment extension: not the
    /// instance, simp or structure tables, and not the reducibility
    /// ATTRIBUTES either (it unfolds by the definitions' own hints). Clean's
    /// loader derives all of those per module, and several passes rescan the
    /// whole environment each time, which made a replay's load quadratic in
    /// the closure: profiled 2026-09-25 on `Init.Data.String.TakeDrop`
    /// (286 modules, 31 s to load, 28 ms to replay). Skipping them changes no
    /// declaration the kernel sees; it drops `@[irreducible]` from the
    /// kernel's unfolding strategy, which is what Lean's kernel does too.
    /// Only for a caller that runs nothing but the kernel over the result.
    ///
    /// It also confines the `.olean.private` stub upgrade (#3134). The loader
    /// otherwise fills ANY value-less resident constant from a later
    /// declaration of that name, another module's axiom included. Lean merges
    /// two declarations of one name only where a theorem subsumes an axiom
    /// (`finalizeImport`'s `subsumesInfo`); a definition over an imported axiom
    /// aborts its import, and its `addDecl` refuses the name as already
    /// declared. So here another module's value-less constant is filled only by
    /// a THEOREM over a safe AXIOM (the module's own stub as before), and any
    /// other such declaration is a duplicate (`LoadSummary::shadowed_declarations`),
    /// decided like every other. Measured 2026-09-26 with the pinned
    /// `leanchecker` on `ReplayForgedBoolDef` (`def bool_ax_b := true` over an
    /// imported `axiom bool_ax_b : Bool` beside `bool_ax_hb : bool_ax_b =
    /// false`): refused in both modes, with the proof of `False` that unfolds
    /// it refused as ill-typed, while `clean olean replay --fresh` upgraded the
    /// imported axiom and admitted every declaration, that proof included.
    #[must_use]
    #[cfg(any(feature = "cli", test))]
    pub(crate) const fn with_kernel_only(mut self) -> Self {
        self.kernel_only = true;
        self
    }

    /// Whether this policy registers only what Lean's kernel reads.
    #[must_use]
    pub(crate) const fn kernel_only(self) -> bool {
        self.kernel_only
    }

    /// Whether the `.olean.private` stub upgrade may fill ANOTHER module's
    /// value-less constant only with a theorem over a safe axiom (see
    /// `Self::with_kernel_only`): under a kernel-only load, and under any load
    /// that leaves rule 1 to the caller's replay, where rule 1 no longer
    /// refuses the import before the upgrade could fill another module's
    /// axiom.
    #[must_use]
    pub(crate) const fn confines_stub_upgrade(self) -> bool {
        self.kernel_only || !matches!(self.left_to_replay, LeftToReplay::Nothing)
    }

    /// Return a copy of this policy under which the loader RECORDS, instead of
    /// refusing the whole import for, three artifact-consistency findings of
    /// `artifact_ledger` (the `clean olean replay` load):
    ///
    /// - rule 1, a declaration whose name a different artifact already
    ///   declared ([`ImportError::ConflictingDeclaration`]): the first is kept
    ///   and the later one is recorded in `LoadSummary::shadowed_declarations`
    ///   (or `restated_declarations`), as every duplicate Lean's import merges
    ///   already is;
    /// - rule 2, a reference to a name only a LATER artifact declares
    ///   ([`ImportError::ForwardReference`]), and rule 3, a safe declaration
    ///   that depends on itself, directly or through a cycle
    ///   ([`ImportError::DefinitionalCycle`]): registered as stored.
    ///
    /// `leanchecker` refuses none of these at load. `leanchecker <M>` never
    /// imports `M` (it reads `M`'s constants and replays them, so a
    /// redeclaration is the kernel's `already declared`), trusts `M`'s imports
    /// (it exits 0 on `ReplayCrossB` over `ReplayCrossA`'s `cross_forged :=
    /// cross_forged`), and its replay refuses a self-dependent declaration as
    /// an unknown constant, per declaration. A name two IMPORTED modules
    /// declare is refused by Lean's `finalizeImport`, and the replay reports it
    /// by name from the record this keeps. Refusing any of them at load made
    /// `clean olean replay` report five `replay_forged` modules as an
    /// unnamed load error, and refuse `ReplayCrossB`, which Lean accepts.
    ///
    /// Only for a caller that replays every declaration it admits through the
    /// kernel in Lean's order and refuses these itself: an environment loaded
    /// under it is not fit to be trusted as an import. Rule 1 also stood guard
    /// over the `.olean.private` stub upgrade, which is confined here as under
    /// `Self::with_kernel_only` ([`Self::confines_stub_upgrade`]).
    #[must_use]
    #[cfg(any(feature = "cli", test))]
    pub(crate) const fn with_replay_refusals(mut self) -> Self {
        self.left_to_replay = LeftToReplay::AllThreeRules;
        self
    }

    /// Return a copy of this policy for the ONE module a caller replays over
    /// imports it trusts ([`crate::load_module_with_deps_replaying_module`], the
    /// mathverse sharded worker's load). Rules 1 and 3 are left to the replay,
    /// as under [`Self::with_replay_refusals`]: the module's redeclaration of
    /// an import's name is recorded in `LoadSummary::shadowed_declarations`, and
    /// its self-dependent declaration registers as stored, for the replay to
    /// refuse by name. Rule 2 still refuses the import: a name the module
    /// declares that an EARLIER artifact (an import) referred to before any of
    /// that artifact's imports declared it is the import's inconsistency, not a
    /// declaration of the module the replay checks. Without it, a forged import
    /// `i : False := x` and the module's `x : False := i` would replay `x` over
    /// the trusted `i` and admit it.
    ///
    /// The stub upgrade is confined as under [`Self::with_replay_refusals`].
    #[must_use]
    pub(crate) const fn with_module_replay_refusals(mut self) -> Self {
        self.left_to_replay = LeftToReplay::ModuleRules;
        self
    }

    /// Whether rule 1 of `artifact_ledger` (a name another artifact already
    /// declared) is left to the caller's replay: the later declaration is
    /// recorded, not refused.
    #[must_use]
    pub(crate) const fn leaves_conflicts_to_replay(self) -> bool {
        !matches!(self.left_to_replay, LeftToReplay::Nothing)
    }

    /// Whether rule 2 of `artifact_ledger` (a name referred to before any
    /// import declared it, supplied by a later artifact) refuses the import.
    #[must_use]
    pub(crate) const fn refuses_forward_references(self) -> bool {
        !matches!(self.left_to_replay, LeftToReplay::AllThreeRules)
    }

    /// Whether rule 3 of `artifact_ledger` (a safe declaration that depends on
    /// itself) refuses the import.
    #[must_use]
    pub(crate) const fn refuses_definitional_cycles(self) -> bool {
        matches!(self.left_to_replay, LeftToReplay::Nothing)
    }

    /// Whether a refused completion of an artifact's own stub refuses the
    /// import (R131, [`ImportError::CompletionRefused`]): under
    /// [`Self::refusing_refused_completions`], for a load that leaves nothing
    /// to a replay. Otherwise it is recorded (`LoadSummary::refused_completions`).
    #[must_use]
    pub(crate) const fn refuses_refused_completions(self) -> bool {
        matches!(self.refused_completions, RefusedCompletions::RefuseImport)
            && matches!(self.left_to_replay, LeftToReplay::Nothing)
    }

    /// Whether a load under this policy checks R142's invariant over each
    /// artifact it loads (`import::authoritative_values`): a re-check lane's
    /// load ([`Self::refusing_refused_completions`]) and a load that leaves
    /// rules to a replay, which records what the invariant finds for the replay
    /// to refuse by name. Under it a completion's value is checked BEFORE the
    /// policy's proof elision drops it, never dropped first. Not under a load
    /// of the inductive families alone, which registers no definitional kind.
    #[must_use]
    pub(crate) const fn checks_authoritative_values(self) -> bool {
        (matches!(self.refused_completions, RefusedCompletions::RefuseImport)
            || !matches!(self.left_to_replay, LeftToReplay::Nothing))
            && !matches!(self.import_kinds, ImportKinds::InductiveFamiliesOnly)
    }

    /// Whether this policy registers only inductive-family kinds (the eager leg
    /// of the Phase-1 HYBRID closure loader).
    #[must_use]
    pub(crate) const fn inductive_families_only(self) -> bool {
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
