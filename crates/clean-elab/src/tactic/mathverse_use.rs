// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `mathverse_use` tactic: search the Mathverse Library for a proof of the current goal.
//!
//! This tactic bridges the elaborator's proof state with the mathverse library's
//! premise selection system. When invoked, it:
//!
//! 1. Extracts the goal type and renders it as text for search
//! 2. Calls [`clean_mathverse::premise_select::search_for_goal`] to find candidates
//! 3. For each candidate, reconstructs the proof `Expr` from shard data
//! 4. Attempts to close the goal via `exact` with the reconstructed proof
//!
//! # Usage (in Lean)
//!
//! ```lean
//! theorem foo : 1 + 1 = 2 := by mathverse_use
//! theorem bar : forall n, n + 0 = n := by mathverse_use
//! ```
//!
//! # Feature gate
//!
//! This module requires the `mathverse-library` feature flag on `clean-elab`.

use clean_kernel::Expr;

use super::{ProofState, TacticError, TacticResult};

#[cfg(feature = "mathverse-library")]
use clean_mathverse::library::MathverseLibrary;
#[cfg(feature = "mathverse-library")]
use clean_mathverse::premise_select::{search_for_kernel_goal, PremiseCandidate, PremiseConfig};
#[cfg(feature = "mathverse-library")]
use clean_mathverse::search::MathverseSearch;
#[cfg(feature = "mathverse-library")]
use clean_mathverse::types::{DeclKind, ImportConfidence, MathverseConstantHeader};

#[cfg(feature = "mathverse-library")]
use super::mathverse_env::{MathverseEnvError, MathverseEnvironment};

// ---------------------------------------------------------------------------
// Thread-local mathverse library handle
// ---------------------------------------------------------------------------

/// Trust gate mode for mathverse_use filtering.
///
/// Controls which mathverse library constants are eligible as candidates.
/// `Strict` mode (default for `mathverse_use`) requires `KernelVerified` trust.
/// `Relaxed` mode (for `mathverse_use!` bang variant) accepts `SourceVerified` and above.
/// `RelaxedFoundational` admits `KernelVerified` constants *plus* constants whose
/// only non-KV transitive dependencies are the closed Lean 4
/// `FOUNDATIONAL_AXIOMS` allowlist (`propext`, `Quot.sound`, `Classical.choice`
/// + the `Eq`/`Quot`/`funext` built-ins), consulted via the kernel's single
/// source of truth [`clean_kernel::is_foundational_axiom`].
///
/// # Soundness
///
/// `RelaxedFoundational` is a **consumption / visibility** gate, NOT the minting
/// of a `KernelVerified` verdict. It decides what a *consumer* may rely on. It
/// is sound because a theorem whose transitive dependency closure bottoms out
/// only in `KernelVerified` facts plus the 3 trusted foundational axioms is
/// exactly as trustworthy as the accepted TCB allows — it admits NO
/// domain-specific axiom. The closure property is enforced structurally:
/// [`validate_dependency_loader_trust`] applies the per-dependency admission
/// predicate to EVERY member of the candidate's transitive closure
/// ([`MathverseLibrary::walk_deps`]), so admitting all of them is equivalent to
/// "closure ⊆ (KernelVerified ∪ FOUNDATIONAL_AXIOMS)".
///
/// A foundational dependency is admitted ONLY when it is BOTH declared as an
/// `Axiom` (`DeclKind::Axiom`) AND its name passes `is_foundational_axiom`.
/// Requiring `DeclKind::Axiom` means a non-axiom declaration that merely shares
/// a foundational name cannot slip through, and delegating to
/// `is_foundational_axiom` (which itself short-circuits `sorry`/`sorryAx` trust
/// markers and excludes `ADMITTED_DOMAIN_AXIOMS`) means a domain-specific or
/// trust-marker axiom can never be admitted.
#[cfg(feature = "mathverse-library")]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TrustGate {
    /// Only accept `ImportConfidence::KernelVerified` candidates.
    Strict,
    /// Accept `KernelVerified` and `SourceVerified` candidates.
    /// Added when `mathverse_use!` bang variant is wired up.
    Relaxed,
    /// Accept `KernelVerified` candidates plus constants whose only non-KV
    /// transitive dependencies are the closed `FOUNDATIONAL_AXIOMS` allowlist.
    /// Opt-in; `Strict` remains the default for `mathverse_use`.
    RelaxedFoundational,
}

#[cfg(feature = "mathverse-library")]
impl TrustGate {
    /// Check if a candidate's trust level passes this gate based on its
    /// import confidence alone.
    ///
    /// For `RelaxedFoundational` this is the `KernelVerified`-only half of the
    /// admission rule; the foundational-axiom half requires the declaration's
    /// name and kind and is applied via [`Self::accepts_dependency`] over the
    /// full transitive closure. Returning `KernelVerified`-only here keeps the
    /// confidence-only contract honest (a bare confidence cannot prove a
    /// constant is a foundational axiom), and is byte-identical to `Strict`
    /// for the candidate-level pre-filter.
    pub(crate) fn accepts(self, confidence: ImportConfidence) -> bool {
        match self {
            // RelaxedFoundational is KernelVerified-or-foundational; the
            // foundational half needs name+kind, so on confidence alone it
            // matches Strict (KernelVerified only). The closure walk in
            // `validate_dependency_loader_trust` admits the foundational deps.
            Self::Strict | Self::RelaxedFoundational => {
                confidence == ImportConfidence::KernelVerified
            }
            Self::Relaxed => {
                confidence == ImportConfidence::KernelVerified
                    || confidence == ImportConfidence::SourceVerified
            }
        }
    }

    /// Check if a single transitive dependency passes this gate.
    ///
    /// This is the authoritative per-dependency admission predicate used by
    /// [`validate_dependency_loader_trust`]. For `Strict` and `Relaxed` it is
    /// exactly [`Self::accepts`] on the dependency's confidence (byte-identical
    /// pre-existing behavior). For `RelaxedFoundational` a dependency is
    /// admitted iff it is `KernelVerified` OR it is a genuine foundational
    /// axiom — declared as an `Axiom` whose name passes the kernel's single
    /// source of truth [`clean_kernel::is_foundational_axiom`].
    ///
    /// Requiring `DeclKind::Axiom` is load-bearing for soundness: it prevents a
    /// non-axiom declaration that happens to share a foundational name from
    /// being admitted, and `is_foundational_axiom` excludes
    /// `ADMITTED_DOMAIN_AXIOMS` and short-circuits trust markers, so no
    /// domain-specific or `sorry`-bearing axiom can pass.
    pub(crate) fn accepts_dependency(
        self,
        confidence: ImportConfidence,
        decl_kind: DeclKind,
        dep_name: &str,
    ) -> bool {
        if self.accepts(confidence) {
            return true;
        }
        match self {
            Self::RelaxedFoundational => {
                decl_kind == DeclKind::Axiom
                    && clean_kernel::is_foundational_axiom(&clean_kernel::name::Name::from_string(
                        dep_name,
                    ))
            }
            Self::Strict | Self::Relaxed => false,
        }
    }
}

/// Default maximum number of mathverse constants to load per tactic
/// invocation. Prevents catastrophic latency from deeply-connected dependency
/// graphs. This is a LATENCY guard, not a trust boundary: every loaded
/// dependency is still checked through the active `TrustGate` and re-registered
/// via the kernel's checked `Environment::add_decl`, so raising it can never
/// admit untrusted or unchecked declarations. Overridable via the
/// `MATHVERSE_DEP_BUDGET` env var (mirrors `max_closure_modules()` in
/// `clean_mathverse::cli::closure_load`) so the operator can raise it for
/// densely-connected goals when there is latency budget to spare.
#[cfg(feature = "mathverse-library")]
const DEFAULT_MATHVERSE_DEP_BUDGET: usize = 20_000;

/// Resolve the per-invocation dependency-load budget, honoring the
/// `MATHVERSE_DEP_BUDGET` env var (positive integer) and falling back to
/// [`DEFAULT_MATHVERSE_DEP_BUDGET`]. Mirrors the `max_closure_modules()` env
/// resolver in `clean_mathverse::cli::closure_load`.
#[cfg(feature = "mathverse-library")]
fn mathverse_dep_budget() -> usize {
    std::env::var("MATHVERSE_DEP_BUDGET")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .filter(|&n| n > 0)
        .unwrap_or(DEFAULT_MATHVERSE_DEP_BUDGET)
}

/// LRU cache capacity for the per-thread MathverseEnvironment.
#[cfg(feature = "mathverse-library")]
const MATHVERSE_ENV_CACHE_SIZE: usize = 4096;

#[cfg(feature = "mathverse-library")]
use std::cell::RefCell;

#[cfg(feature = "mathverse-library")]
thread_local! {
    /// Thread-local mathverse library instance.
    ///
    /// Tactics cannot accept extra parameters beyond `ProofState` + args, so
    /// the mathverse library is stored as a thread-local. Call
    /// [`set_mathverse_library`] before invoking `mathverse_use` / `mathverse_suggest`.
    static MATHVERSE_LIBRARY: RefCell<Option<MathverseLibrary>> = const { RefCell::new(None) };

    /// Thread-local mathverse environment for caching loaded dependency closures.
    static MATHVERSE_ENV: RefCell<MathverseEnvironment> = RefCell::new(
        MathverseEnvironment::new(MATHVERSE_ENV_CACHE_SIZE)
    );
}

/// Install an `MathverseLibrary` for the current thread.
///
/// Must be called before `mathverse_use` or `mathverse_suggest` can succeed.
/// Typically called once during server/elaborator initialization after
/// loading shards.
#[cfg(feature = "mathverse-library")]
pub fn set_mathverse_library(library: MathverseLibrary) {
    MATHVERSE_LIBRARY.with(|cell| {
        *cell.borrow_mut() = Some(library);
    });
}

/// Remove the thread-local mathverse library (for cleanup / testing).
#[cfg(feature = "mathverse-library")]
pub fn clear_mathverse_library() {
    MATHVERSE_LIBRARY.with(|cell| {
        *cell.borrow_mut() = None;
    });
}

// ---------------------------------------------------------------------------
// mathverse_use tactic
// ---------------------------------------------------------------------------

/// The `mathverse_use` tactic: search Mathverse Library for a proof of the current goal.
///
/// Extracts the goal type, searches the mathverse library for matching theorems,
/// and attempts to close the goal with the best match.
///
/// # Errors
///
/// - `TacticError::NoGoals` if no goals remain
/// - `TacticError::SearchExhausted` if no matching theorem is found
/// - `TacticError::SearchExhausted` if the mathverse library is not loaded
pub(crate) fn eval_mathverse_use(state: &mut ProofState, _args: &[Expr]) -> TacticResult {
    #[cfg(feature = "mathverse-library")]
    {
        eval_mathverse_use_impl(state)
    }
    #[cfg(not(feature = "mathverse-library"))]
    {
        let _ = state;
        Err(TacticError::SearchExhausted {
            tactic: "mathverse_use".into(),
            detail:
                "mathverse-library feature not enabled; rebuild with --features mathverse-library"
                    .into(),
        })
    }
}

/// Public strict `mathverse_use` runner for integration layers that already own an
/// active [`ProofState`].
///
/// This intentionally does not construct goals or load shards by itself. Callers
/// must build the tactic-level target/context, install an [`MathverseLibrary`] with
/// [`set_mathverse_library`], then call this function to run the same strict
/// KernelVerified path used by the `mathverse_use` tactic.
// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[allow(dead_code)]
pub fn run_strict_mathverse_use(state: &mut ProofState) -> TacticResult {
    #[cfg(feature = "mathverse-library")]
    {
        eval_mathverse_use_impl(state)
    }
    #[cfg(not(feature = "mathverse-library"))]
    {
        let _ = state;
        Err(TacticError::SearchExhausted {
            tactic: "mathverse_use".into(),
            detail:
                "mathverse-library feature not enabled; rebuild with --features mathverse-library"
                    .into(),
        })
    }
}

/// Public **opt-in** `RelaxedFoundational` `mathverse_use` runner for
/// integration layers that already own an active [`ProofState`].
///
/// Identical to [`run_strict_mathverse_use`] except it admits a candidate
/// whose only non-`KernelVerified` transitive dependencies are the closed
/// `FOUNDATIONAL_AXIOMS` allowlist (`propext` / `Quot.sound` /
/// `Classical.choice` + the `Eq`/`Quot`/`funext` built-ins), consulted via the
/// kernel's single source of truth `clean_kernel::is_foundational_axiom`. This
/// makes the `KernelVerified` Mathverse corpus consumable: a deep theorem whose
/// closure bottoms out only in `KernelVerified` facts plus the 3 trusted
/// foundational axioms is admitted, where `Strict` would reject it on its first
/// non-KV transitive dependency.
///
/// This is a **consumption / visibility** gate, NOT the minting of a
/// `KernelVerified` verdict — the kernel check is unchanged. `Strict` remains
/// the default; callers must explicitly select this mode.
// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[allow(dead_code)]
pub fn run_relaxed_foundational_mathverse_use(state: &mut ProofState) -> TacticResult {
    #[cfg(feature = "mathverse-library")]
    {
        eval_mathverse_use_with_trust(state, TrustGate::RelaxedFoundational)
    }
    #[cfg(not(feature = "mathverse-library"))]
    {
        let _ = state;
        Err(TacticError::SearchExhausted {
            tactic: "mathverse_use".into(),
            detail:
                "mathverse-library feature not enabled; rebuild with --features mathverse-library"
                    .into(),
        })
    }
}

#[cfg(feature = "mathverse-library")]
fn eval_mathverse_use_impl(state: &mut ProofState) -> TacticResult {
    eval_mathverse_use_with_trust(state, TrustGate::Strict)
}

/// Core implementation shared by strict and relaxed mathverse_use variants.
#[cfg(feature = "mathverse-library")]
fn eval_mathverse_use_with_trust(state: &mut ProofState, trust_gate: TrustGate) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?;
    let target = state.metas.instantiate(&goal.target);

    // Collect constant names from the local context as search context
    let context_names: Vec<String> = goal
        .local_ctx
        .iter()
        .map(|decl| decl.name.clone())
        .collect();
    let context_refs: Vec<&str> = context_names.iter().map(|s| s.as_str()).collect();

    let config = PremiseConfig {
        max_results: 10,
        ..PremiseConfig::default()
    };

    // Search the mathverse library using discrimination tree + BM25 + symbol overlap.
    // Fix for #3412: previously passed None for goal_type_idx, bypassing the
    // discrimination tree entirely. Now we use search_for_kernel_goal which
    // converts the goal Expr into the library's FlatExpr arena for disc tree search.
    let candidates = MATHVERSE_LIBRARY.with(|cell| {
        let mut borrow = cell.borrow_mut();
        let library = borrow
            .as_mut()
            .ok_or_else(|| TacticError::SearchExhausted {
                tactic: "mathverse_use".into(),
                detail: "no Mathverse Library loaded; call set_mathverse_library() first".into(),
            })?;
        let raw = search_for_kernel_goal(library, &target, &context_refs, &config);

        // Filter candidates by trust gate using ImportConfidence + DeclKind +
        // name from the header. The authoritative whole-closure check happens
        // later in `validate_dependency_loader_trust`; this is a cheap
        // pre-filter on the candidate itself. Using `accepts_dependency`
        // (rather than confidence alone) keeps the candidate-level decision
        // consistent with the per-dependency rule under `RelaxedFoundational`.
        let filtered: Vec<PremiseCandidate> = raw
            .into_iter()
            .filter(|c| {
                let confidence = ImportConfidence::try_from(c.header.import_confidence)
                    .unwrap_or(ImportConfidence::Unverified);
                let decl_kind = c.header.decl_kind().unwrap_or(DeclKind::Theorem);
                trust_gate.accepts_dependency(confidence, decl_kind, &c.name)
            })
            .collect();

        Ok(filtered)
    })?;

    if candidates.is_empty() {
        return Err(TacticError::SearchExhausted {
            tactic: "mathverse_use".into(),
            detail: format!(
                "no matching theorem found in Mathverse Library (trust gate: {trust_gate:?})"
            ),
        });
    }

    // Try each candidate: load deps, build Expr with universe args, and attempt exact
    let mut last_err = None;
    for candidate in &candidates {
        match try_apply_candidate(state, candidate, trust_gate) {
            Ok(()) => return Ok(()),
            Err(e) => last_err = Some(e),
        }
    }

    Err(last_err.unwrap_or_else(|| TacticError::SearchExhausted {
        tactic: "mathverse_use".into(),
        detail: format!(
            "found {} candidates but none could close the goal",
            candidates.len()
        ),
    }))
}

/// Attempt to close the current goal using an mathverse library candidate.
///
/// 1. Loads the candidate's transitive dependencies into the proof state's
///    environment via `MathverseEnvironment` (cached, budget-limited).
/// 2. Builds `Expr::const_(name, fresh_levels)` with fresh universe parameters
///    for each of the constant's declared level parameters.
/// 3. Attempts to close the goal via `exact`.
#[cfg(feature = "mathverse-library")]
fn try_apply_candidate(
    state: &mut ProofState,
    candidate: &PremiseCandidate,
    trust_gate: TrustGate,
) -> TacticResult {
    let name = clean_kernel::name::Name::from_string(&candidate.name);

    // Step 1: Load the candidate's transitive dependencies into the environment.
    // Uses the thread-local MathverseEnvironment cache to avoid redundant loads.
    let dep_load_result = MATHVERSE_LIBRARY.with(|lib_cell| {
        let lib_borrow = lib_cell.borrow();
        let library = lib_borrow
            .as_ref()
            .ok_or_else(|| TacticError::SearchExhausted {
                tactic: "mathverse_use".into(),
                detail: "no Mathverse Library loaded".into(),
            })?;

        validate_dependency_loader_trust(&state.env, candidate, library, trust_gate)?;

        MATHVERSE_ENV.with(|env_cell| {
            let mut env_borrow = env_cell.borrow_mut();
            match env_borrow.load_with_deps(&candidate.name, library, mathverse_dep_budget()) {
                Ok(decls) => Ok(decls),
                Err(MathverseEnvError::BudgetExceeded { loaded, limit }) => {
                    Err(TacticError::SearchExhausted {
                        tactic: "mathverse_use".into(),
                        detail: format!(
                            "dependency budget exceeded for `{}`: {loaded} deps > {limit} limit",
                            candidate.name
                        ),
                    })
                }
                Err(e) => Err(TacticError::SearchExhausted {
                    tactic: "mathverse_use".into(),
                    detail: format!("failed to load deps for `{}`: {e}", candidate.name),
                }),
            }
        })
    })?;

    // Add loaded dependency declarations to the proof state's environment.
    //
    // `validate_dependency_loader_trust` has already checked the whole
    // dependency closure, not just the selected candidate: every missing
    // declaration passed the active `TrustGate`, its type/value shard
    // expressions reconstructed, proof/value-bearing declarations were not
    // metadata-only, and missing declarations whose `DeclKind` cannot be
    // faithfully replayed by this skeleton loader were rejected.
    //
    // The remaining replayable subset is theorem/axiom skeletons, so register
    // them through checked `Environment::add_decl`. Kernel rejection is
    // fail-closed and leaves the candidate unusable; metadata-incomplete
    // definition/opaque/quotient/inductive-family dependencies remain rejected
    // before this point until the mathverse shard loader preserves full
    // DeclKind/topological/InductiveDecl replay metadata.
    for decl in dep_load_result {
        let decl_name = decl_declaration_name(&decl);
        if state.env.get_const(&decl_name).is_none() {
            let dep_name = decl_name.to_string();
            state
                .env
                .add_decl(decl)
                .map_err(|err| TacticError::SearchExhausted {
                    tactic: "mathverse_use".into(),
                    detail: format!(
                        "dependency loader rejected `{}`: checked registration for dependency `{dep_name}` failed: {err}",
                        candidate.name
                    ),
                })?;
        }
    }

    // Step 2: Build the constant expression with fresh universe parameters.
    // If the constant is now in the environment (from dep loading or already
    // present), mk_const will read its level_params and create fresh Level::Param
    // for each. Otherwise, falls back to empty levels.
    //
    // NOTE: The mathverse shard format does not yet store universe level parameters
    // (level_lists table not implemented, see lean4/env_import.rs:235). All mathverse
    // constants are currently loaded with empty level_params, so mk_const will
    // produce empty levels. Once #3355 (C1) is fully wired through to shard
    // loading, the declarations will carry correct level_params and this code
    // will automatically produce correct fresh universe metavariables.
    let proof_expr = state.mk_const(&name);

    // Step 3: Try exact with the constant reference.
    super::exact(state, proof_expr)
}

#[cfg(feature = "mathverse-library")]
pub(crate) fn validate_dependency_loader_trust(
    env: &clean_kernel::Environment,
    candidate: &PremiseCandidate,
    library: &MathverseLibrary,
    trust_gate: TrustGate,
) -> TacticResult {
    let dep_indices: Vec<_> = library.walk_deps(candidate.constant_idx).collect();
    let budget = mathverse_dep_budget();
    if dep_indices.len() > budget {
        return Err(TacticError::SearchExhausted {
            tactic: "mathverse_use".into(),
            detail: format!(
                "dependency budget exceeded for `{}`: {} deps > {} limit",
                candidate.name,
                dep_indices.len(),
                budget
            ),
        });
    }

    for idx in dep_indices {
        let dep_name = library
            .get_name(idx)
            .ok_or_else(|| TacticError::SearchExhausted {
                tactic: "mathverse_use".into(),
                detail: format!(
                "dependency loader rejected `{}`: missing shard name for dependency index {idx}",
                candidate.name
            ),
            })?;
        let header = library
            .get_constant(idx)
            .ok_or_else(|| TacticError::SearchExhausted {
                tactic: "mathverse_use".into(),
                detail: format!(
                "dependency loader rejected `{}`: missing shard header for dependency `{dep_name}`",
                candidate.name
            ),
            })?;

        let confidence = header
            .confidence()
            .map_err(|raw| TacticError::SearchExhausted {
                tactic: "mathverse_use".into(),
                detail: format!(
                    "dependency loader rejected `{}`: dependency `{dep_name}` has unknown import confidence {raw}",
                    candidate.name
                ),
            })?;

        let decl_kind = header
            .decl_kind()
            .map_err(|raw| TacticError::SearchExhausted {
                tactic: "mathverse_use".into(),
                detail: format!(
                    "dependency loader rejected `{}`: dependency `{dep_name}` has unknown declaration kind {raw}",
                    candidate.name
                ),
            })?;

        // Per-dependency trust admission over the FULL transitive closure.
        //
        // Applying this to every member of `walk_deps` is what gives the
        // closure property: if every dependency is admitted, then the candidate
        // theorem's transitive closure is ⊆ (KernelVerified ∪
        // FOUNDATIONAL_AXIOMS) under `RelaxedFoundational` (or ⊆ KernelVerified
        // under `Strict`). On rejection we name the FIRST offending dependency
        // — the dependency that is neither KernelVerified nor (under
        // `RelaxedFoundational`) a foundational axiom — which is the actionable
        // diagnostic the consumer needs.
        if !trust_gate.accepts_dependency(confidence, decl_kind, dep_name) {
            return Err(TacticError::SearchExhausted {
                tactic: "mathverse_use".into(),
                detail: format!(
                    "dependency loader rejected `{}`: dependency `{dep_name}` has trust {confidence:?} (kind {}), below {trust_gate:?}",
                    candidate.name,
                    decl_kind_name(decl_kind)
                ),
            });
        }

        validate_reconstructable_dependency(&candidate.name, dep_name, header, decl_kind, library)?;

        if idx == candidate.constant_idx && !matches!(decl_kind, DeclKind::Theorem) {
            return Err(TacticError::SearchExhausted {
                tactic: "mathverse_use".into(),
                detail: format!(
                    "dependency loader rejected `{}`: selected candidate is {}, not a theorem declaration",
                    candidate.name,
                    decl_kind_name(decl_kind)
                ),
            });
        }

        let dep_kernel_name = clean_kernel::name::Name::from_string(dep_name);
        if env.get_const(&dep_kernel_name).is_none()
            && !can_replay_missing_dependency(decl_kind, header)
        {
            let metadata_requirement = if is_inductive_family_decl(decl_kind) {
                "full InductiveDecl data"
            } else {
                "full DeclKind-preserving metadata"
            };
            return Err(TacticError::SearchExhausted {
                tactic: "mathverse_use".into(),
                detail: format!(
                    "dependency loader rejected `{}`: dependency `{dep_name}` is {} metadata without {metadata_requirement} for checked registration",
                    candidate.name,
                    decl_kind_name(decl_kind)
                ),
            });
        }
    }

    Ok(())
}

#[cfg(feature = "mathverse-library")]
fn validate_reconstructable_dependency(
    candidate_name: &str,
    dep_name: &str,
    header: &MathverseConstantHeader,
    decl_kind: DeclKind,
    library: &MathverseLibrary,
) -> TacticResult {
    use clean_mathverse::shard_reconstruct::reconstruct_from_shard;

    let _ = reconstruct_from_shard(
        library.exprs(),
        library.levels(),
        library.strings(),
        header.type_idx,
    )
    .map_err(|e| TacticError::SearchExhausted {
        tactic: "mathverse_use".into(),
        detail: format!(
            "dependency loader rejected `{candidate_name}`: dependency `{dep_name}` type reconstruction failed: {e}"
        ),
    })?;

    if is_proof_value_decl(decl_kind) {
        if !header.has_value() {
            return Err(TacticError::SearchExhausted {
                tactic: "mathverse_use".into(),
                detail: format!(
                    "dependency loader rejected `{candidate_name}`: dependency `{dep_name}` is {} but has no proof/value expression",
                    decl_kind_name(decl_kind)
                ),
            });
        }

        let _ = reconstruct_from_shard(
            library.exprs(),
            library.levels(),
            library.strings(),
            header.value_idx,
        )
        .map_err(|e| TacticError::SearchExhausted {
            tactic: "mathverse_use".into(),
            detail: format!(
                "dependency loader rejected `{candidate_name}`: dependency `{dep_name}` value reconstruction failed: {e}"
            ),
        })?;
    }

    Ok(())
}

#[cfg(feature = "mathverse-library")]
fn is_proof_value_decl(decl_kind: DeclKind) -> bool {
    matches!(
        decl_kind,
        DeclKind::Theorem | DeclKind::Definition | DeclKind::Opaque
    )
}

#[cfg(feature = "mathverse-library")]
fn can_replay_missing_dependency(decl_kind: DeclKind, header: &MathverseConstantHeader) -> bool {
    match decl_kind {
        DeclKind::Theorem => header.has_value(),
        DeclKind::Axiom => !header.has_value(),
        _ => false,
    }
}

#[cfg(feature = "mathverse-library")]
fn is_inductive_family_decl(decl_kind: DeclKind) -> bool {
    matches!(
        decl_kind,
        DeclKind::Inductive | DeclKind::Constructor | DeclKind::Recursor
    )
}

#[cfg(feature = "mathverse-library")]
fn decl_kind_name(decl_kind: DeclKind) -> &'static str {
    match decl_kind {
        DeclKind::Theorem => "theorem",
        DeclKind::Definition => "definition",
        DeclKind::Axiom => "axiom",
        DeclKind::Opaque => "opaque",
        DeclKind::Inductive => "inductive",
        DeclKind::Constructor => "constructor",
        DeclKind::Recursor => "recursor",
        DeclKind::Quot => "quotient",
        _ => "unknown declaration kind",
    }
}

/// Extract the name from a `Declaration` enum variant.
#[cfg(feature = "mathverse-library")]
fn decl_declaration_name(decl: &clean_kernel::Declaration) -> clean_kernel::name::Name {
    match decl {
        clean_kernel::Declaration::Definition { name, .. }
        | clean_kernel::Declaration::Axiom { name, .. }
        | clean_kernel::Declaration::Theorem { name, .. }
        | clean_kernel::Declaration::Opaque { name, .. } => name.clone(),
    }
}

// ---------------------------------------------------------------------------
// mathverse_suggest tactic
// ---------------------------------------------------------------------------

/// The `mathverse_suggest` tactic: show ranked mathverse library candidates without applying.
///
/// Prints the top candidates to stderr for interactive use, then returns
/// an error (the goal is not closed).
pub(crate) fn eval_mathverse_suggest(state: &mut ProofState, _args: &[Expr]) -> TacticResult {
    #[cfg(feature = "mathverse-library")]
    {
        eval_mathverse_suggest_impl(state)
    }
    #[cfg(not(feature = "mathverse-library"))]
    {
        let _ = state;
        Err(TacticError::SearchExhausted {
            tactic: "mathverse_suggest".into(),
            detail:
                "mathverse-library feature not enabled; rebuild with --features mathverse-library"
                    .into(),
        })
    }
}

#[cfg(feature = "mathverse-library")]
fn eval_mathverse_suggest_impl(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?;
    let target = state.metas.instantiate(&goal.target);

    let context_names: Vec<String> = goal
        .local_ctx
        .iter()
        .map(|decl| decl.name.clone())
        .collect();
    let context_refs: Vec<&str> = context_names.iter().map(|s| s.as_str()).collect();

    let config = PremiseConfig {
        max_results: 10,
        ..PremiseConfig::default()
    };

    // Use search_for_kernel_goal for disc tree + BM25 + symbol overlap (fix #3412).
    let candidates = MATHVERSE_LIBRARY.with(|cell| {
        let mut borrow = cell.borrow_mut();
        let library = borrow
            .as_mut()
            .ok_or_else(|| TacticError::SearchExhausted {
                tactic: "mathverse_suggest".into(),
                detail: "no Mathverse Library loaded; call set_mathverse_library() first".into(),
            })?;
        Ok(search_for_kernel_goal(
            library,
            &target,
            &context_refs,
            &config,
        ))
    })?;

    if candidates.is_empty() {
        return Err(TacticError::SearchExhausted {
            tactic: "mathverse_suggest".into(),
            detail: "no candidates found in Mathverse Library".into(),
        });
    }

    // Log candidates for interactive feedback
    tracing::info!(
        "mathverse_suggest: {} candidate(s) for goal:",
        candidates.len()
    );
    for (i, c) in candidates.iter().enumerate().take(10) {
        tracing::info!(
            "  {}. {} (score: {:.3}, system: {:?}, trust: {:?})",
            i + 1,
            c.name,
            c.score,
            c.source_system,
            c.trust_level,
        );
    }

    // Don't close the goal — this is informational only
    Err(TacticError::SearchExhausted {
        tactic: "mathverse_suggest".into(),
        detail: format!(
            "showing {} candidates (use mathverse_use to apply)",
            candidates.len()
        ),
    })
}

/// Entry point for the `mathverse_use!` bang variant (relaxed trust).
///
/// Accepts `SourceVerified` constants in addition to `KernelVerified`.
/// Not yet wired into the tactic registry; will be connected by #3359 follow-up.
// 2026-07-31: staged entry point with no caller yet — it is the sole production
// constructor of `TrustGate::Relaxed` and the registry wiring is the pending
// half of #3359. Kept (not deleted) because deleting it would also strand the
// `Relaxed` gate variant and its tests in `mathverse_use_tests`.
#[allow(dead_code)]
#[cfg(feature = "mathverse-library")]
pub(crate) fn eval_mathverse_use_relaxed(state: &mut ProofState) -> TacticResult {
    eval_mathverse_use_with_trust(state, TrustGate::Relaxed)
}
