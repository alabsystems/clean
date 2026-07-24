// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! In-process Mathverse Library provider for proof-state premise selection.
//!
//! The Mathverse corpus is what makes the library "visible" during proof
//! search: when a proof state is rendered for an AI agent, this provider runs
//! [`clean_mathverse::premise_select::search_for_kernel_goal`] over the loaded
//! corpus and returns trust-filtered [`MathverseCandidate`]s for the focused
//! goal.
//!
//! The provider is intentionally lazy and corpus-optional: if no `.mathverse`
//! shards are discovered at startup, the handle stays empty and the server runs
//! exactly as before (an empty candidate list), so a corpus-less deployment is
//! a supported configuration rather than a hard error.
//!
//! ## Why a process-global mirror
//!
//! [`crate::proof_state::mathverse_candidates_for_state`] is the single choke
//! point that every proof-state path funnels through, and it is reached from
//! ~20 call sites that do not all have a `ServerState` in scope. Rather than
//! thread a handle through every signature, [`ServerState`] owns the handle and
//! registers a clone of it into a process-global [`OnceLock`] at startup. The
//! choke-point function reads the global. The global is just an `Arc` clone of
//! the same handle the `ServerState` owns — there is no second copy of the
//! corpus.

use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, OnceLock};

use clean_kernel::Expr;
use clean_mathverse::library::MathverseLibrary;
use clean_mathverse::premise_select::{search_for_kernel_goal, PremiseCandidate, PremiseConfig};
use clean_mathverse::shard::ShardReader;
use clean_mathverse::shard_verify::discover_mathverse_files;
use clean_mathverse::trust::TrustPolicy;
use clean_mathverse::types::{ContentDomain, ImportConfidence, SourceSystem, TrustLevel};

use crate::proof_state::MathverseCandidate;

/// Environment variable naming the directory of `.mathverse` shards to load.
pub const MATHVERSE_DIR_ENV: &str = "CLEAN_MATHVERSE_DIR";

/// Maximum candidates returned per goal.
const MAX_CANDIDATES: usize = 16;

/// Shared, cheaply-cloneable handle to the (optionally loaded) corpus.
///
/// The library itself is not `Sync` (it uses interior `RefCell`/`Cell` for its
/// lazy BM25 index) and `search_for_kernel_goal` needs `&mut` to register the
/// query expression in its arena, so the library lives behind a [`Mutex`]. The
/// inner `Option` is `None` when no corpus was discovered.
#[derive(Clone, Default)]
pub struct MathverseProvider {
    inner: Arc<Mutex<Option<MathverseLibrary>>>,
}

impl std::fmt::Debug for MathverseProvider {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let loaded = self
            .inner
            .lock()
            .map(|guard| guard.is_some())
            .unwrap_or(false);
        f.debug_struct("MathverseProvider")
            .field("loaded", &loaded)
            .finish()
    }
}

impl MathverseProvider {
    /// An empty provider that yields no candidates (corpus-less default).
    #[must_use]
    pub fn empty() -> Self {
        Self::default()
    }

    /// Build a provider by discovering and loading a corpus from `dir`.
    ///
    /// Every `.mathverse` shard under `dir` (recursively) is merged into a
    /// single in-memory library. If `dir` holds no shards, an empty provider is
    /// returned (the server then runs corpus-less). A shard that fails to read
    /// is skipped rather than aborting the whole load, so one corrupt file does
    /// not take the server offline.
    #[must_use]
    pub fn from_dir(dir: &Path) -> Self {
        let files = discover_mathverse_files(dir);
        if files.is_empty() {
            return Self::empty();
        }

        // Default trust policy: only kernel-verified / source-verified /
        // translated constants are visible. Statement-only `Unverified` imports
        // never surface as proof-search candidates under this policy.
        let mut library = MathverseLibrary::new(TrustPolicy::default_policy());
        let mut loaded_any = false;
        for path in &files {
            match ShardReader::from_file(path) {
                Ok(reader) => {
                    if library.load_shard_deferred(&reader).is_ok() {
                        loaded_any = true;
                    }
                }
                Err(_) => continue,
            }
        }

        if !loaded_any {
            return Self::empty();
        }
        // Single O(N) dependency-adjacency rebuild after the bulk load above
        // (deferred per shard so the multi-shard load stays O(N), not O(N²)).
        library.build_deps();

        Self {
            inner: Arc::new(Mutex::new(Some(library))),
        }
    }

    /// Discover a corpus from the environment.
    ///
    /// Reads [`MATHVERSE_DIR_ENV`]; if set and it points at a directory, loads
    /// it. Otherwise returns an empty provider. This keeps the server's default
    /// behavior (corpus-less, empty candidates) unless an operator explicitly
    /// points it at a shard directory.
    #[must_use]
    pub fn discover() -> Self {
        match std::env::var_os(MATHVERSE_DIR_ENV) {
            Some(raw) => {
                let dir = PathBuf::from(raw);
                if dir.is_dir() {
                    Self::from_dir(&dir)
                } else {
                    Self::empty()
                }
            }
            None => Self::empty(),
        }
    }

    /// Whether a corpus is loaded (vs. the corpus-less empty default).
    #[must_use]
    pub fn is_loaded(&self) -> bool {
        self.inner
            .lock()
            .map(|guard| guard.is_some())
            .unwrap_or(false)
    }

    /// Number of constants in the loaded corpus (0 when corpus-less).
    #[must_use]
    pub fn constant_count(&self) -> usize {
        self.inner
            .lock()
            .ok()
            .and_then(|guard| guard.as_ref().map(MathverseLibrary::constant_count))
            .unwrap_or(0)
    }

    /// Search the corpus for trust-filtered candidates relevant to `goal`.
    ///
    /// `context_names` are the local hypothesis names already in scope (used for
    /// dependency-neighbor search). Returns an empty vector when no corpus is
    /// loaded, when the mutex is poisoned, or when nothing relevant is found.
    #[must_use]
    pub fn candidates_for_goal(
        &self,
        goal: &Expr,
        context_names: &[&str],
    ) -> Vec<MathverseCandidate> {
        let mut guard = match self.inner.lock() {
            Ok(guard) => guard,
            Err(_) => return Vec::new(),
        };
        let library = match guard.as_mut() {
            Some(library) => library,
            None => return Vec::new(),
        };

        let config = PremiseConfig {
            max_results: MAX_CANDIDATES,
            // Only surface candidates whose import confidence is at least as
            // trustworthy as `KernelVerified`. Combined with the library's
            // `default_policy`, this fails closed on statement-only imports.
            min_trust: Some(ImportConfidence::KernelVerified),
            ..PremiseConfig::default()
        };

        let ranked = search_for_kernel_goal(library, goal, context_names, &config);
        ranked.iter().map(premise_to_candidate).collect()
    }
}

/// Adapt a backend [`PremiseCandidate`] into the wire-facing [`MathverseCandidate`].
fn premise_to_candidate(candidate: &PremiseCandidate) -> MathverseCandidate {
    let domain = ContentDomain::try_from(candidate.header.content_domain)
        .ok()
        .map(content_domain_label)
        .map(str::to_string);

    MathverseCandidate {
        name: candidate.name.clone(),
        // The backend does not pretty-print the candidate's type; the name plus
        // source/trust/domain labels are the load-bearing payload for an agent.
        type_pp: String::new(),
        relevance: candidate.score,
        trust_level: trust_level_label(candidate.trust_level).to_string(),
        source_system: Some(source_system_label(candidate.source_system).to_string()),
        domain,
    }
}

/// Stable display label for a [`TrustLevel`].
fn trust_level_label(level: TrustLevel) -> &'static str {
    match level {
        TrustLevel::KernelVerified => "KernelVerified",
        TrustLevel::AxiomDependent => "AxiomDependent",
        TrustLevel::CertificateReplayed => "CertificateReplayed",
        TrustLevel::PartiallyAxiomatized => "PartiallyAxiomatized",
        TrustLevel::TrustedOracle => "TrustedOracle",
        _ => "Unknown",
    }
}

/// Stable display label for a [`ContentDomain`].
fn content_domain_label(domain: ContentDomain) -> &'static str {
    match domain {
        ContentDomain::PureMath => "PureMath",
        ContentDomain::Software => "Software",
        ContentDomain::Complexity => "Complexity",
        ContentDomain::NnVerification => "NnVerification",
        ContentDomain::Physics => "Physics",
        ContentDomain::Logic => "Logic",
        ContentDomain::Cryptography => "Cryptography",
    }
}

/// Stable display label for a [`SourceSystem`] (a few common systems; others
/// fall through to their `Debug` spelling via [`source_system_fallback`]).
fn source_system_label(system: SourceSystem) -> String {
    match system {
        SourceSystem::Lean4 => "Lean4".to_string(),
        SourceSystem::Coq => "Coq".to_string(),
        SourceSystem::Isabelle => "Isabelle".to_string(),
        SourceSystem::Metamath => "Metamath".to_string(),
        SourceSystem::Mizar => "Mizar".to_string(),
        SourceSystem::HolLight => "HolLight".to_string(),
        SourceSystem::Hol4 => "Hol4".to_string(),
        SourceSystem::Agda => "Agda".to_string(),
        SourceSystem::CleanNative => "CleanNative".to_string(),
        other => source_system_fallback(other),
    }
}

/// Fallback label for source systems without a hand-written name.
fn source_system_fallback(system: SourceSystem) -> String {
    format!("{system:?}")
}

// ---------------------------------------------------------------------------
// Process-global handle
// ---------------------------------------------------------------------------

static GLOBAL_PROVIDER: OnceLock<MathverseProvider> = OnceLock::new();

/// Register the process-global provider. First writer wins; later calls are
/// ignored (idempotent), so repeated `ServerState` construction in tests does
/// not panic. `ServerState::new`/`from_root` call this with their own handle.
pub fn install_global(provider: MathverseProvider) {
    let _ = GLOBAL_PROVIDER.set(provider);
}

/// The process-global provider, or an empty one if none was installed.
#[must_use]
pub fn global() -> MathverseProvider {
    GLOBAL_PROVIDER
        .get()
        .cloned()
        .unwrap_or_else(MathverseProvider::empty)
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::expr::Expr;
    use clean_kernel::flat::{FlatExpr, FlatLevel};
    use clean_mathverse::shard::ShardWriter;
    use clean_mathverse::types::{
        AxiomProfile, ContentDomain as CD, ImportConfidence as IC, MathverseConstantHeader,
        SourceSystem as SS,
    };
    use tempfile::tempdir;

    /// Write a tiny one-constant `.mathverse` shard under `dir` whose single
    /// constant is a `Sort 0`-typed declaration named `const_name`, stamped
    /// `KernelVerified` with a pure axiom profile so it passes the trust gate.
    fn write_corpus_shard(dir: &Path, const_name: &str) {
        let mut writer = ShardWriter::new();
        let name_idx = writer.add_string(const_name);
        let l0 = writer.add_level(FlatLevel::zero());
        let ty = writer.add_expr(FlatExpr::sort(l0));
        writer.add_constant(MathverseConstantHeader {
            name_idx,
            type_idx: ty,
            value_idx: ty,
            source_system: SS::Lean4 as u8,
            import_confidence: IC::KernelVerified as u8,
            content_domain: CD::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
        writer
            .write_to_file(dir.join("corpus.mathverse"))
            .expect("write corpus shard");
    }

    #[test]
    fn test_empty_provider_returns_no_candidates() {
        let provider = MathverseProvider::empty();
        assert!(!provider.is_loaded());
        assert_eq!(provider.constant_count(), 0);

        let goal = Expr::const_str("corpus_lemma");
        let candidates = provider.candidates_for_goal(&goal, &[]);
        assert!(
            candidates.is_empty(),
            "corpus-less provider must return no candidates"
        );
    }

    #[test]
    fn test_from_dir_empty_dir_is_corpusless() {
        let dir = tempdir().expect("tempdir");
        let provider = MathverseProvider::from_dir(dir.path());
        assert!(
            !provider.is_loaded(),
            "a directory with no shards yields a corpus-less provider"
        );
    }

    #[test]
    fn test_loaded_corpus_surfaces_known_lemma() {
        let dir = tempdir().expect("tempdir");
        write_corpus_shard(dir.path(), "corpus_lemma");

        let provider = MathverseProvider::from_dir(dir.path());
        assert!(provider.is_loaded(), "corpus directory should load");
        assert_eq!(provider.constant_count(), 1);

        // A goal mentioning the corpus lemma by name should retrieve it.
        let goal = Expr::const_str("corpus_lemma");
        let candidates = provider.candidates_for_goal(&goal, &[]);
        assert!(
            candidates.iter().any(|c| c.name == "corpus_lemma"),
            "known corpus lemma should appear as a candidate; got {candidates:?}"
        );
        let found = candidates
            .iter()
            .find(|c| c.name == "corpus_lemma")
            .expect("candidate present");
        assert_eq!(found.source_system.as_deref(), Some("Lean4"));
        assert_eq!(found.trust_level, "KernelVerified");
        assert_eq!(found.domain.as_deref(), Some("PureMath"));
    }
}
