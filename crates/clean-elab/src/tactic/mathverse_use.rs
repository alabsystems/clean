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

#[cfg(test)]
#[path = "mathverse_context_tests.rs"]
mod context_tests;

/// Encode only exact names supported by the legacy Mathverse dotted-name
/// protocol. This is not source spelling: its decoder interprets numeric
/// components as `Name::Num`, so a numeric-looking `Name::Str` is unsupported.
/// Unsupported names omit an optional neighborhood hint; they are never
/// flattened into a different global identity.
fn mathverse_context_path(name: &clean_kernel::Name) -> Option<String> {
    use clean_kernel::name::NameInner;
    let mut parts = Vec::new();
    let mut current = name;
    loop {
        match current.inner() {
            NameInner::Anon => break,
            NameInner::Str(parent, part) => {
                if part.is_empty() || part.contains('.') || part.parse::<u64>().is_ok() {
                    return None;
                }
                parts.push(part.to_string());
                current = parent.as_ref();
            }
            NameInner::Num(parent, index) => {
                parts.push(index.to_string());
                current = parent.as_ref();
            }
        }
    }
    if parts.is_empty() {
        return None;
    }
    parts.reverse();
    Some(parts.join("."))
}

/// Neighborhood lookup consumes global constant keys, not local binder labels.
/// Collect exact constants from instantiated local types and let values, then
/// cross the checked legacy path boundary solely for that search hint. The
/// target expression, candidate validation, trust policy and kernel check do
/// not use this projection.
pub fn mathverse_context_names(
    metas: &crate::unify::MetaState,
    locals: &[super::LocalDecl],
) -> Vec<String> {
    let mut names = std::collections::BTreeSet::new();
    for local in locals {
        names.extend(metas.instantiate(&local.ty).collect_constants());
        if let Some(value) = &local.value {
            names.extend(metas.instantiate(value).collect_constants());
        }
    }
    names.iter().filter_map(mathverse_context_path).collect()
}

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
    /// The gate's name as it is written in source, for refusal messages.
    ///
    /// A real renderer rather than `{:?}` (see `crate::error_render`): the text
    /// is the same, but it is a decision stated here instead of whatever the
    /// derived `Debug` happens to print.
    #[must_use]
    pub(crate) const fn label(self) -> &'static str {
        match self {
            Self::Strict => "Strict",
            Self::Relaxed => "Relaxed",
            Self::RelaxedFoundational => "RelaxedFoundational",
        }
    }

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

    /// The installed library's merged arenas viewed as one `ShardReader`, built
    /// ONCE per install and reused across citations.
    ///
    /// The checked inductive-family replay operates on a `ShardReader`, and
    /// `merged_reader_for` CLONES all five arenas — acceptable once, ruinous
    /// per-citation (a 196,981-constant / 3.1M-expr corpus clones gigabytes).
    /// Built lazily so a session that never cites a structure never pays for it.
    static MATHVERSE_MERGED_READER: RefCell<Option<clean_mathverse::shard::ShardReader>> =
        const { RefCell::new(None) };
}

/// Install an `MathverseLibrary` for the current thread.
///
/// Must be called before `mathverse_use` or `mathverse_suggest` can succeed.
/// Typically called once during server/elaborator initialization after
/// loading shards.
#[cfg(feature = "mathverse-library")]
pub fn set_mathverse_library(library: MathverseLibrary) {
    // Invalidate the merged-reader cache: it is derived from the library's
    // arenas, so a stale one would replay families out of the PREVIOUS corpus.
    MATHVERSE_MERGED_READER.with(|cell| *cell.borrow_mut() = None);
    // Invalidate the reconstruction memo for the SAME reason — it is keyed by
    // NAME only, so after a swap it will serve the PREVIOUS corpus's
    // reconstruction of a name the new corpus also defines. That is not merely
    // stale: `validate_dependency_loader_trust` reads the NEW library's headers
    // while the `Declaration` handed to `add_decl` is the OLD library's, so the
    // gate validates one declaration and the environment installs another.
    // Demonstrated with two libraries defining `adv_stale` at different types:
    // the type installed was library A's, after the gate had checked B's.
    MATHVERSE_ENV.with(|cell| cell.borrow_mut().clear());
    MATHVERSE_LIBRARY.with(|cell| {
        *cell.borrow_mut() = Some(library);
    });
}

/// Remove the thread-local mathverse library (for cleanup / testing).
#[cfg(feature = "mathverse-library")]
pub fn clear_mathverse_library() {
    MATHVERSE_MERGED_READER.with(|cell| *cell.borrow_mut() = None);
    MATHVERSE_LIBRARY.with(|cell| {
        *cell.borrow_mut() = None;
    });
}

/// A prelude stub retired for the duration of one citation, kept so it can be
/// put back if the genuine declaration never arrived.
#[cfg(feature = "mathverse-library")]
pub(crate) struct DischargedStub {
    /// Restore order. A family head must come back before its constructors and
    /// before any definition typed in terms of it (`Fact.mk : {p} → p → Fact p`
    /// does not type-check without `Fact`).
    rank: u8,
    /// The name is in the candidate's own dependency closure, so the gate
    /// admitted the citation on the promise that the genuine declaration would
    /// take the stub's place. If it is restored instead, the promise was broken
    /// and the citation must NOT be reported as closed — see
    /// [`load_candidate_closure`]. Collision-clearing sweeps
    /// (family members outside the closure) set this to `false`: nothing in the
    /// proof term references them, so putting them back is routine.
    in_closure: bool,
    name: clean_kernel::name::Name,
    decl: clean_kernel::Declaration,
}

/// Retire the prelude's FABRICATED stubs for members of `candidate`'s shard
/// closure, so the genuine declarations can install through the checked paths.
///
/// # The problem this solves
///
/// `Environment::with_prelude` hand-rolls a handful of Mathlib/Lean-core names
/// as bare `Declaration::Axiom` carriers — `Fact`, `Fact.mk`, `Fact.out`
/// (`env/algebra_substructures.rs::init_fact`), `Monad`
/// (`env/data_monad.rs`), the `OptionT`/`StateT`/`ExceptT` helpers — so that
/// hand-rolled instances resolve before any library is loaded. In real Lean
/// those are a *structure*, its *constructor*, and *proved* definitions. Every
/// downstream consumer then hits one of two walls:
///
/// * KIND substitution — `Fact` is an `Inductive` row in the shard and an
///   `Axiom` in the environment, so `validate_dependency_loader_trust`'s
///   residency rule correctly refuses the citation ("stub substitution"). That
///   refusal is right and stays; the fix is to stop the stub being resident,
///   not to weaken the discriminator.
/// * SILENT substitution — `Fact.out` is a `KernelVerified` **Theorem** row in
///   the shard and a value-free `Axiom` in the environment. Kinds do not clash,
///   so the residency rule admits it by design, the loader (which only adds
///   names it finds ABSENT) never installs the real proof, and a by-name
///   citation of `Fact.out` closes against Clean's own assumption. That is a
///   success reported about the wrong declaration, and it is the reason this
///   pass cannot be scoped to inductive families alone.
///
/// # What is discharged, and why each condition is load-bearing
///
/// The resident copy must be a **value-free `Axiom` that is not shape-backed** —
/// exactly [`clean_kernel::Environment::discharge_axiom_stub_for_inductive_import`]'s
/// contract, which never removes a definition, a theorem, or anything backed by
/// an inductive/constructor/recursor. And the shard row must be one the checked
/// paths can genuinely replace:
///
/// * `Inductive`/`Constructor`/`Recursor` — replaced by
///   [`replay_inductive_families_for`], which rebuilds the family on a scratch
///   clone, installs it through checked `add_inductive`, and byte-matches every
///   regenerated member against the shard before committing.
/// * `Theorem`/`Definition`/`Opaque` **with a value** and **`KernelVerified`
///   confidence** — replaced by the loader's checked `add_decl`, which
///   re-type-checks the value here, in this environment. Confidence is required
///   not for trust (the kernel re-checks regardless) but so the gate will admit
///   the replacement instead of rejecting a citation that used to pass.
/// * Nothing else. `Quot` rows are kernel primitives whose prelude axioms ARE
///   the correct representation, and value-less `Axiom` rows (`propext`,
///   `Classical.choice`) are genuine axioms, not fabrications. Both are
///   excluded by kind.
///
/// # Soundness
///
/// A carrier is discharged only after it is AUTHENTICATED against the shard
/// row that will replace it: same universe arity and a definitionally equal
/// type ([`TypeAgreementMode::DefEqOnly`]). That is the contract main's
/// 2026-11-14 source-authority correction states for every holder of
/// discharge authority (census row `axiom-stub-discharge`): whatever was
/// checked against the carrier stays correct against its replacement. A
/// carrier that fails it stays resident and the citation is refused by the
/// residency rule.
///
/// This never admits anything the gate would have rejected: it only *removes*
/// unchecked assumptions, and every replacement arrives through `add_inductive`
/// or `add_decl` with the kernel doing the checking. If a replacement fails to
/// materialize, [`restore_unreplaced_stubs`] puts the carrier back and the
/// citation fails closed on the gate's own diagnostic — the session is left
/// byte-identical to how it was found. Scoped to the gates that demand
/// `KernelVerified`, so `Relaxed` behavior is unchanged.
#[cfg(feature = "mathverse-library")]
pub(crate) fn discharge_fabricated_stubs_for(
    env: &mut clean_kernel::Environment,
    candidate: &PremiseCandidate,
    library: &MathverseLibrary,
    trust_gate: TrustGate,
) -> Vec<DischargedStub> {
    use clean_kernel::env::ConstantKind;
    use clean_kernel::name::Name;

    if !matches!(
        trust_gate,
        TrustGate::Strict | TrustGate::RelaxedFoundational
    ) {
        return Vec::new();
    }

    let debug = std::env::var("CLEAN_STUB_DEBUG").is_ok();
    let mut discharged: Vec<DischargedStub> = Vec::new();
    let mut take_stub = |env: &mut clean_kernel::Environment,
                         name: &Name,
                         rank: u8,
                         in_closure: bool,
                         why: &str| {
        // Shape-backed names are the genuine article already; anything that is
        // not a bare value-free `Axiom` is not a fabricated carrier and must be
        // left alone (`discharge_…` would refuse it anyway).
        if env.get_inductive(name).is_some()
            || env.get_constructor(name).is_some()
            || env.get_recursor(name).is_some()
        {
            return;
        }
        let Some(info) = env.get_const(name) else {
            return;
        };
        if !matches!(info.kind, ConstantKind::Axiom) || info.value.is_some() {
            return;
        }
        // AUTHENTICATE BEFORE REMOVAL (the discharge contract of census row
        // `axiom-stub-discharge`, data/env_bypass_census.json, as main's
        // 2026-11-14 source-authority correction states it for the Fact
        // bootstrap). Everything already in the environment that mentions this
        // carrier was checked against the carrier's TYPE. The replacement is the
        // shard's declaration of the same name, so it may take the carrier's
        // place only when its universe arity matches and its type is
        // definitionally equal to the carrier's; otherwise those earlier checks
        // would describe a constant that no longer exists. No shard row, or any
        // disagreement, leaves the carrier resident, and the residency rule then
        // refuses the citation on its own diagnostic.
        let rendered = name.to_string();
        let Some(shard_header) = library
            .lookup_constant_idx(&rendered)
            .and_then(|idx| library.get_constant(idx))
        else {
            return;
        };
        if let Err(refusal) = check_type_agreement(
            env,
            &candidate.name,
            &rendered,
            name,
            shard_header,
            library,
            TypeAgreementMode::DefEqOnly,
        ) {
            if debug {
                eprintln!("CLEAN_STUB_DEBUG: kept carrier `{name}` ({why}): {refusal}");
            }
            return;
        }
        let decl = clean_kernel::Declaration::Axiom {
            name: name.clone(),
            level_params: info.level_params.clone(),
            type_: info.type_.clone(),
        };
        if env.discharge_axiom_stub_for_inductive_import(name) {
            if debug {
                eprintln!("CLEAN_STUB_DEBUG: discharged fabricated stub `{name}` ({why})");
            }
            discharged.push(DischargedStub {
                rank,
                in_closure,
                name: name.clone(),
                decl,
            });
        }
    };

    // Pass 1 — closure rows.
    let mut family_heads: Vec<Name> = Vec::new();
    for idx in library.walk_deps(candidate.constant_idx) {
        let (Some(dep_name), Some(header)) = (library.get_name(idx), library.get_constant(idx))
        else {
            continue;
        };
        let Ok(decl_kind) = header.decl_kind() else {
            continue;
        };
        let name = Name::from_string(dep_name);

        let rank = match decl_kind {
            DeclKind::Inductive => {
                family_heads.push(name.clone());
                0
            }
            DeclKind::Constructor | DeclKind::Recursor => 1,
            DeclKind::Theorem | DeclKind::Definition | DeclKind::Opaque => {
                if !header.has_value()
                    || !matches!(header.confidence(), Ok(ImportConfidence::KernelVerified))
                {
                    continue;
                }
                2
            }
            // Quotient primitives and genuine axioms: never fabrications.
            DeclKind::Quot | DeclKind::Axiom => continue,
            // `DeclKind` is `#[non_exhaustive]`; a kind this pass has not been
            // reasoned about is never discharged.
            _ => continue,
        };
        take_stub(env, &name, rank, true, &format!("shard row {decl_kind:?}"));
    }

    // Pass 2 — family MEMBERS that the closure never mentions.
    //
    // `add_inductive` mints the head, every constructor, and the recursor, so a
    // fabricated stub on ANY of those names aborts the checked replay with
    // `Duplicate declaration` — and a member need not appear in this
    // candidate's dependency closure at all. That is exactly how the measured
    // failure presented: `Fact.out`'s closure names `Fact` but not `Fact.mk`,
    // so discharging only the closure rows left `Fact.mk`'s stub in place and
    // the replay of `Fact` failed on it (`WS16 … Duplicate declaration:
    // Fact.mk`), which the gate then reported as `Fact … below Strict` — the
    // wrong layer.
    //
    // Lean mints constructors and recursors inside their type's own namespace,
    // so the members to clear are the `<head>.` prefixed names. The predicate
    // is unchanged (value-free `Axiom`, not shape-backed) and anything the
    // replay does not actually claim is restored, so an over-wide prefix costs
    // nothing but a re-add.
    //
    // One pass over the environment with the head names in a set, rather than a
    // namespace map: a session that preloaded a real `.olean` closure has
    // ~170k constants and would otherwise pay a full map build per citation.
    family_heads.retain(|head| env.get_const(head).is_none() && env.get_inductive(head).is_none());
    if !family_heads.is_empty() {
        let heads: std::collections::HashSet<String> =
            family_heads.iter().map(ToString::to_string).collect();
        let members: Vec<(Name, String)> = env
            .constants()
            .filter(|info| matches!(info.kind, ConstantKind::Axiom) && info.value.is_none())
            .filter_map(|info| {
                let rendered = info.name.to_string();
                let cut = rendered.rfind('.')?;
                heads
                    .get(&rendered[..cut])
                    .map(|head| (info.name.clone(), head.clone()))
            })
            .collect();
        for (member, head) in members {
            take_stub(
                env,
                &member,
                1,
                false,
                &format!("member of replayed family `{head}`"),
            );
        }
    }

    discharged.sort_by_key(|s| s.rank);
    discharged
}

/// Put back every stub from [`discharge_fabricated_stubs_for`] whose genuine
/// declaration did not arrive.
///
/// Without this, a citation that fails anywhere after the discharge would leave
/// the session's environment permanently short a prelude carrier — the loss
/// would outlive the failed tactic and change unrelated later elaboration. A
/// restored carrier is exactly what was there before (same name, level params
/// and type, re-checked by `add_decl`), so the failing citation still fails
/// closed on the residency rule, with its original diagnostic.
///
/// Restores lowest rank first and then iterates to a fixpoint, because a stub's
/// type can mention another discharged name.
///
/// Returns the names of restored stubs that were IN THE CANDIDATE'S CLOSURE.
/// That list must be empty on an otherwise-successful load: the gate admitted
/// those dependencies only because the discharge made them absent, so restoring
/// one means the citation would rest on the fabricated axiom after all. The
/// caller turns a non-empty list into a rejection.
#[cfg(feature = "mathverse-library")]
pub(crate) fn restore_unreplaced_stubs(
    env: &mut clean_kernel::Environment,
    stubs: Vec<DischargedStub>,
) -> Vec<clean_kernel::name::Name> {
    if stubs.is_empty() {
        return Vec::new();
    }
    let debug = std::env::var("CLEAN_STUB_DEBUG").is_ok();
    let mut restored_in_closure = Vec::new();
    let mut pending = stubs;
    loop {
        let before = pending.len();
        let mut still_failing = Vec::new();
        for stub in pending {
            let present = env.get_const(&stub.name).is_some()
                || env.get_inductive(&stub.name).is_some()
                || env.get_constructor(&stub.name).is_some()
                || env.get_recursor(&stub.name).is_some();
            if present {
                continue;
            }
            if env.add_decl(stub.decl.clone()).is_err() {
                still_failing.push(stub);
                continue;
            }
            if debug {
                eprintln!(
                    "CLEAN_STUB_DEBUG: restored stub `{}` (genuine declaration never arrived)",
                    stub.name
                );
            }
            if stub.in_closure {
                restored_in_closure.push(stub.name);
            }
        }
        if still_failing.is_empty() || still_failing.len() == before {
            break;
        }
        pending = still_failing;
    }
    restored_in_closure
}

/// Install every INDUCTIVE FAMILY in `candidate`'s dependency closure into
/// `env`, through the kernel's **checked** `add_inductive`.
///
/// # Why this runs BEFORE the trust gate
///
/// Inductives, constructors and recursors are value-less, so `stamp-verified`
/// can never mark them `KernelVerified` and `TrustGate::Strict` can never admit
/// them on confidence. Lean CORE families (`Eq`, `Iff`, `And`) escape only
/// because `Environment::with_prelude` makes them RESIDENT, and the residency
/// rule admits a dependency the loader will not add. Mathlib's own structures
/// (`Unique`, `Fact`, `CommMonoid`) are not resident, so every theorem
/// mentioning one is rejected.
///
/// Replaying the families first makes their members resident, after which the
/// EXISTING residency rule admits them with no change to the gate at all. The
/// admission is honest precisely because the kernel validated them:
/// `replay_inductive_family_checked` rebuilds each family on a scratch clone,
/// installs it via checked `add_inductive`, and byte-matches the regenerated
/// members against the shard before committing. Nothing here trusts the shard's
/// encoding.
///
/// Best-effort by design: a family that fails to replay is simply not installed,
/// and the trust gate then rejects the citation fail-closed with its own
/// diagnostic. This never widens what is admitted — it only ever ADDS
/// kernel-validated declarations to `env`.
#[cfg(feature = "mathverse-library")]
fn replay_inductive_families_for(
    env: &mut clean_kernel::Environment,
    candidate: &PremiseCandidate,
    library: &MathverseLibrary,
) {
    use clean_mathverse::verify::incremental::{
        merged_reader_for, replay_inductive_family_checked, InductiveReplayPolicy,
    };

    // Which closure members are inductive family entry points that are NOT
    // already present? Checked first so a session citing only core-closure
    // content never builds the (expensive) merged reader.
    let pending: Vec<u32> = library
        .walk_deps(candidate.constant_idx)
        .filter(|idx| {
            library
                .get_constant(*idx)
                .is_some_and(|h| h.decl_kind() == Ok(DeclKind::Inductive))
        })
        .filter(|idx| {
            library.get_name(*idx).is_some_and(|n| {
                env.get_const(&clean_kernel::name::Name::from_string(n))
                    .is_none()
            })
        })
        .collect();
    // Env-gated trace. Kept because the failure this diagnosed was SILENT: the
    // replay returned "no metadata" and the family was simply absent, with the
    // gate then reporting a trust rejection that pointed at the wrong layer.
    // `CLEAN_WS16_DEBUG` covers the replay internals; this covers whether the
    // pre-pass reached them at all.
    if std::env::var("CLEAN_FAMILY_DEBUG").is_ok() {
        eprintln!(
            "CLEAN_FAMILY_DEBUG: `{}` -> {} pending inductive famil{}",
            candidate.name,
            pending.len(),
            if pending.len() == 1 { "y" } else { "ies" }
        );
    }
    if pending.is_empty() {
        return;
    }

    MATHVERSE_MERGED_READER.with(|cell| {
        let mut slot = cell.borrow_mut();
        if slot.is_none() {
            *slot = Some(merged_reader_for(library));
        }
        let Some(reader) = slot.as_ref() else {
            return;
        };
        for idx in pending {
            // `.olean`-sourced corpora carry their own convenience definitions,
            // so install only the kernel certificate and let those arrive via
            // the normal checked `add_decl` path.
            // Whether or not it installs, the result needs no handling here:
            // a family left uninstalled is rejected fail-closed by the gate below.
            let _ = replay_inductive_family_checked(
                env,
                reader,
                idx,
                InductiveReplayPolicy::LeanFaithful,
            );
        }
    });
}

// ---------------------------------------------------------------------------
// mathverse_use tactic
// ---------------------------------------------------------------------------

/// `mathverse_apply <name>` — the registry entry point.
///
/// Takes the lemma NAME as an identifier argument (not a term: the constant is
/// not in the environment until this tactic loads it), then applies it to the
/// goal with argument synthesis. See [`mathverse_apply_named`].
pub(crate) fn eval_mathverse_apply(state: &mut ProofState, args: &[Expr]) -> TacticResult {
    #[cfg(feature = "mathverse-library")]
    {
        let Some(first) = args.first() else {
            return Err(TacticError::MissingArgument {
                tactic: "mathverse_apply".into(),
                expected: "a library constant name, e.g. `mathverse_apply Nat.add_comm`".into(),
            });
        };
        let surface = super::builtins::expr_to_hyp_name(state, first)?;
        // The library is keyed by the legacy dotted-name protocol. Encode the
        // STRUCTURAL name through the same checked encoder the search path uses
        // for its context keys, never the diagnostic `Display` spelling: a name
        // that protocol cannot spell (an empty component, one containing `.`, or
        // one that reads as a number) is refused rather than flattened into a
        // different library identity.
        let Some(name) = mathverse_context_path(surface.name()) else {
            return Err(TacticError::InvalidTarget {
                tactic: "mathverse_apply".into(),
                detail: format!(
                    "`{surface}` cannot be spelled in the Mathverse Library's dotted-name \
                     protocol, so it names no library constant"
                ),
            });
        };
        run_mathverse_apply(state, &name)
    }
    #[cfg(not(feature = "mathverse-library"))]
    {
        let _ = (state, args);
        Err(TacticError::SearchExhausted {
            tactic: "mathverse_apply".into(),
            detail:
                "mathverse-library feature not enabled; rebuild with --features mathverse-library"
                    .into(),
        })
    }
}

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
pub(crate) fn run_relaxed_foundational_mathverse_use(state: &mut ProofState) -> TacticResult {
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

    let context_names = mathverse_context_names(&state.metas, &goal.local_ctx);
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
                "no matching theorem found in Mathverse Library (trust gate: {})",
                crate::error_render::opaque(&trust_gate)
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

/// Is a Mathverse Library installed on this thread?
///
/// The `import Mathverse.…` arm uses this to decide whether it must discover
/// and load shards, or whether a caller (a test, an embedder, the server) has
/// already installed one via [`set_mathverse_library`].
#[cfg(feature = "mathverse-library")]
#[must_use]
pub(crate) fn mathverse_library_installed() -> bool {
    MATHVERSE_LIBRARY.with(|cell| cell.borrow().is_some())
}

/// The `SourceSystem` of `name` in the installed library, or `None` when the
/// name is absent (or hidden by the library's trust policy).
///
/// Used by `import Mathverse.<Corpus>.<Name>` to check that the constant it is
/// about to install really comes from the corpus the user asked for. Pure
/// lookup — one hash probe, no environment, no trust decision.
#[cfg(feature = "mathverse-library")]
pub(crate) fn mathverse_constant_source_system(
    name: &str,
) -> Option<clean_mathverse::types::SourceSystem> {
    MATHVERSE_LIBRARY.with(|lib_cell| {
        let lib_borrow = lib_cell.borrow();
        let library = lib_borrow.as_ref()?;
        let idx = library.lookup_constant_idx(name)?;
        let header = library.get_constant(idx)?;
        clean_mathverse::types::SourceSystem::try_from(header.source_system).ok()
    })
}

/// Resolve `name` in the installed library to the [`PremiseCandidate`] the
/// SEARCH path would have produced for it.
///
/// Extracted from [`mathverse_apply_named`] so the tactic path and the import
/// path build the *same* candidate and hand it to the *same* loader. Pure
/// lookup: it touches no environment and makes no trust decision — `score`,
/// `trust_level` and `match_reason` are inert search metadata, and the actual
/// admission decision is `TrustGate::accepts_dependency` over the header's real
/// `import_confidence`, taken inside `validate_dependency_loader_trust`.
///
/// `tactic` only labels the error so the caller's surface (`mathverse_apply`
/// vs. `import Mathverse`) is recognisable in the message.
#[cfg(feature = "mathverse-library")]
fn synthesize_named_candidate(name: &str, tactic: &str) -> Result<PremiseCandidate, TacticError> {
    MATHVERSE_LIBRARY.with(|lib_cell| {
        let lib_borrow = lib_cell.borrow();
        let library = lib_borrow
            .as_ref()
            .ok_or_else(|| TacticError::SearchExhausted {
                tactic: tactic.into(),
                detail: "no Mathverse Library loaded; call set_mathverse_library() first".into(),
            })?;
        let idx =
            library
                .lookup_constant_idx(name)
                .ok_or_else(|| TacticError::SearchExhausted {
                    tactic: tactic.into(),
                    detail: format!(
                        "`{name}` is not in the installed Mathverse Library (or is hidden by the \
                     library's trust policy)"
                    ),
                })?;
        let header = *library
            .get_constant(idx)
            .ok_or_else(|| TacticError::SearchExhausted {
                tactic: tactic.into(),
                detail: format!("`{name}` resolved to index {idx} with no header"),
            })?;
        Ok::<_, TacticError>(PremiseCandidate {
            name: name.to_string(),
            constant_idx: idx,
            // Score/reason are search metadata; a by-name citation did not come
            // from ranking, and nothing downstream reads them.
            score: 1.0,
            source_system: clean_mathverse::types::SourceSystem::try_from(header.source_system)
                .unwrap_or(clean_mathverse::types::SourceSystem::Isabelle),
            // Derived from the header exactly as for a search candidate, never
            // a fixed tier. Nothing on the load path reads it: the ACTUAL
            // admission decision is `TrustGate::accepts_dependency` over the
            // header's real `import_confidence`, in
            // `validate_dependency_loader_trust`.
            trust_level: clean_mathverse::types::TrustLevel::from(&header),
            match_reason: clean_mathverse::premise_select::MatchReason::NameSimilarity,
            header,
        })
    })
}

/// Install the library constant `name` and its full transitive closure into
/// `env`, gated by `trust_gate`.
///
/// This is the loading half of [`mathverse_apply_named`] with the goal-directed
/// tail removed, so it can serve an `import Mathverse.…` declaration, which has
/// an environment but no proof state. It is the SAME two calls the tactic makes
/// — `synthesize_named_candidate` then [`load_candidate_closure`] — and
/// therefore the same gate: fabricated-stub discharge with its fail-closed
/// re-check, checked inductive-family replay, `validate_dependency_loader_trust`
/// (kind discriminator, `validate_resident_type_agreement`, the foundational
/// axiom restriction, `accepts_dependency` over the FULL transitive closure) and
/// checked `Environment::add_decl`. There is no second, weaker path.
///
/// After the load, `name` is an ordinary resident constant, so the elaborator's
/// unmodified name resolution finds it and library content becomes usable as a
/// TERM (`:= eq_or_ne x y`), not only through the citation tactic.
///
/// # Errors
///
/// [`TacticError::SearchExhausted`] if no library is installed, the name is not
/// in it, or the trust gate rejects any member of its closure. The detail names
/// the actual reason (stub substitution, resident type disagreement,
/// non-foundational axiom, dependency budget) — never a bare "not found".
#[cfg(feature = "mathverse-library")]
pub(crate) fn mathverse_load_named(
    env: &mut clean_kernel::Environment,
    name: &str,
    trust_gate: TrustGate,
    tactic: &str,
) -> TacticResult {
    let candidate = synthesize_named_candidate(name, tactic)?;
    load_candidate_closure(env, &candidate, trust_gate)
}

#[cfg(feature = "mathverse-library")]
/// Cite a library constant **BY NAME** and apply it to the goal, synthesizing
/// its arguments — the `exact add_comm a b` experience, for Mathverse content.
///
/// # Why this exists alongside `mathverse_use`
///
/// `mathverse_use` is a NULLARY goal-directed search: it takes no arguments,
/// applies whatever premise selection ranks first, and closes the goal only if
/// the candidate's WHOLE type unifies. That cannot express "I know the lemma I
/// want." This does.
///
/// The loading half is identical — the same family replay, the same
/// `TrustGate` over the full transitive closure, the same checked `add_decl`.
/// The difference is the final step: [`super::apply`] instead of
/// [`super::exact`], so the lemma's telescope is opened into metavariables,
/// unified against the goal, and any unsolved premise becomes a subgoal.
///
/// # Errors
///
/// - [`TacticError::SearchExhausted`] if no library is installed, the name is
///   not in it, or the trust gate rejects some member of its closure.
/// - [`TacticError::TypeMismatch`] if the named lemma's conclusion cannot unify
///   with the goal — a genuine mismatch, not a search miss.
#[cfg(feature = "mathverse-library")]
pub(crate) fn mathverse_apply_named(
    state: &mut ProofState,
    name: &str,
    trust_gate: TrustGate,
) -> TacticResult {
    // Resolve the name to a library constant and install its gated closure.
    // Shared verbatim with the `import Mathverse.…` path — see
    // `mathverse_load_named`.
    mathverse_load_named(&mut state.env, name, trust_gate, "mathverse_apply")?;

    // Pin the GOAL's universe parameters as rigid before instantiating the
    // lemma.
    //
    // `mk_const` instantiates a universe-polymorphic constant with
    // `fresh_universe_param()`, producing `Sort(Param("u_0"))` where the goal —
    // reconstructed from the shard — carries the declared `Sort(Param("u"))`.
    // `unify_levels` (unify/unifier/mod.rs:508-515) already knows how to
    // reconcile that: it collapses a FRESH param onto a DECLARED one, but only
    // when `is_rigid_level_param(declared) && !is_rigid_level_param(fresh)`. A
    // shard-reconstructed `u` was never registered, so neither side was rigid,
    // the branch never fired, and citation of every universe-polymorphic
    // constant failed with `Param("u")` vs `Param("u_0")` (measured: first
    // divergence at char 90 of 1484 for `Classical.skolem`).
    //
    // Registering them here is not a workaround, it is the correct statement of
    // intent: from a citation's point of view the goal's universes ARE rigid.
    // You may instantiate the LEMMA's universes to fit the goal; you may not
    // rename the GOAL's universes to fit the lemma. That asymmetry is exactly
    // what the existing branch encodes.
    //
    // Added, not replaced: `set_rigid_level_params` overwrites the set, and
    // discarding params an outer elaboration pinned would let this tactic
    // silently un-rigidify someone else's declaration. `add_rigid_level_param`
    // is the meta state's own join-the-existing-set entry point.
    {
        let goal_target = state
            .current_goal()
            .ok_or(TacticError::NoGoals)?
            .target
            .clone();
        // The production collector (iterative, no depth cap), not the
        // test-only `auto_param_ext` prototype: a parameter deep in the goal
        // must still be pinned rigid.
        let goal_params = crate::infer::collect_level_params(&[&goal_target]);
        if std::env::var("CLEAN_UNIV_DEBUG").is_ok() {
            eprintln!("UNIV_DEBUG: goal universe params = {goal_params:?}");
        }
        for param in goal_params {
            state.metas.add_rigid_level_param(param);
        }
    }

    let proof_expr = state.mk_const(&clean_kernel::name::Name::from_string(name));

    // EXACT first, then APPLY.
    //
    // `apply` alone is not enough: `apply_aux_acc`
    // (tactic/proof_term.rs) peels a `Pi` and only THEN unifies the codomain
    // against the goal — it never tries the ZERO-argument case. So `apply f`
    // cannot close a goal that is exactly `f`'s type, whereas Lean's `apply`
    // can (zero is a valid arity). Measured: citing a constant whose own type
    // is the goal failed with a TypeMismatch through `apply` and succeeds
    // through `exact`.
    //
    // Rather than change a core tactic every other caller depends on, the
    // citation tactic covers both arities itself, which is what a user means by
    // "use this lemma" regardless:
    //   * exact — the lemma IS the goal (no arguments needed)
    //   * apply — the lemma proves the goal once its arguments are synthesized,
    //             leaving each unsolved premise as a subgoal
    //
    // `exact` fails before closing the goal when it does not unify, so falling
    // through leaves the proof state usable.
    // KNOWN GAP — universe-polymorphic constants (evidenced 2026-07-28).
    //
    // `mk_const` (tactic/core/factory.rs:149-162) instantiates a constant's
    // universes with `fresh_universe_param()`, so citing `Classical.skolem`
    // builds `Sort(Param("u_0"))` while the goal - reconstructed from the shard
    // - carries the DECLARED `Sort(Param("u"))`. Diffing the two types, that is
    // the FIRST divergence, at char 90 of 1484:
    //
    //   expected  Sort(Param("u"))
    //   actual    Sort(Param("u_0"))
    //
    // `unify_levels` (unify/unifier/mod.rs:508-515) resolves Param-vs-Param by
    // rigidity, but a shard-reconstructed `u` was never registered in
    // `rigid_level_params`, so neither side is rigid and the orientation rule
    // that would collapse the fresh param onto the declared one does not fire.
    //
    // Not fixed here: the candidate fixes are in `mk_const` or in core level
    // unification, both used by every tactic, and this needs its own change
    // with its own tests rather than a drive-by from the citation path.
    // Monomorphic constants cite correctly today.
    //
    // On failure report BOTH errors. Returning only `apply`'s is actively
    // misleading: `apply` peels a Pi before unifying, so when the goal IS the
    // lemma's (Pi) type it reports a shape mismatch like `App vs Pi` from its
    // over-peeled codomain — which masks the real reason `exact` declined and
    // sends the reader after a nonexistent structural bug.
    match super::exact(state, proof_expr.clone()) {
        Ok(()) => Ok(()),
        Err(exact_err) => match super::apply(state, proof_expr) {
            Ok(()) => Ok(()),
            Err(apply_err) => Err(TacticError::SearchExhausted {
                tactic: "mathverse_apply".into(),
                detail: format!(
                    "`{name}` did not close the goal. exact: {exact_err} | apply: {apply_err} \
                     (note: `apply` peels a Pi before unifying, so on a goal that IS the lemma's \
                     type its error is expected and the `exact` one is the informative half)"
                ),
            }),
        },
    }
}

/// `mathverse_apply <name>` under the default [`TrustGate::Strict`].
#[cfg(feature = "mathverse-library")]
pub fn run_mathverse_apply(state: &mut ProofState, name: &str) -> TacticResult {
    mathverse_apply_named(state, name, TrustGate::Strict)
}

#[cfg(feature = "mathverse-library")]
/// Install `candidate`'s transitive closure into `env`: replay any
/// inductive families through checked `add_inductive`, validate every member of
/// the closure against `trust_gate`, then register the replayable declarations
/// through checked `add_decl` in topological order.
///
/// Shared by the SEARCH path ([`try_apply_candidate`]), the BY-NAME tactic path
/// ([`mathverse_apply_named`]) and the IMPORT path ([`mathverse_load_named`], via
/// `import Mathverse.…` in `lib.rs`) so a named citation, a searched one and an
/// imported one carry exactly the same trust guarantees — a second loader would
/// be a second trust story, and they would drift.
///
/// Takes `&mut Environment` rather than `&mut ProofState` because it never
/// touched anything else on the state (no goals, no metas, no instances) and
/// because the import path has only an environment: the term elaborator's
/// `ElabCtx` holds an IMMUTABLE `&Environment` for its whole lifetime
/// (`infer/mod.rs`), so a constant can only be installed at the declaration
/// driver that owns `&mut Environment`.
#[cfg(feature = "mathverse-library")]
fn load_candidate_closure(
    env: &mut clean_kernel::Environment,
    candidate: &PremiseCandidate,
    trust_gate: TrustGate,
) -> TacticResult {
    // Step 0: retire the prelude's FABRICATED stubs for members of this closure,
    // so the genuine declarations can install through the checked paths below.
    // Restored afterwards for whatever did not get replaced, so a failed load
    // leaves the session exactly as it found it. See
    // `discharge_fabricated_stubs_for`.
    let restore = MATHVERSE_LIBRARY.with(|lib_cell| {
        let lib_borrow = lib_cell.borrow();
        lib_borrow.as_ref().map_or_else(Vec::new, |library| {
            discharge_fabricated_stubs_for(env, candidate, library, trust_gate)
        })
    });
    let result = load_candidate_closure_inner(env, candidate, trust_gate);
    let restored_in_closure = restore_unreplaced_stubs(env, restore);
    // FAIL-CLOSED. The gate admitted a discharged dependency on its shard
    // confidence precisely because the discharge made it absent — i.e. on the
    // promise that the genuine, kernel-checked declaration would take the
    // stub's place. If the loader silently did not install it (it only adds
    // names it finds absent, and its cross-citation cache can skip one), the
    // restore above puts the fabricated axiom back, and reporting the citation
    // closed would report success about the wrong declaration. Reject instead.
    if result.is_ok() && !restored_in_closure.is_empty() {
        return Err(TacticError::SearchExhausted {
            tactic: "mathverse_use".into(),
            detail: format!(
                "dependency loader rejected `{}`: the genuine declaration for `{}` never replaced the prelude's fabricated axiom carrier, so the citation would rest on a stub",
                candidate.name,
                restored_in_closure
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join("`, `")
            ),
        });
    }
    result
}

#[cfg(feature = "mathverse-library")]
fn load_candidate_closure_inner(
    env: &mut clean_kernel::Environment,
    candidate: &PremiseCandidate,
    trust_gate: TrustGate,
) -> TacticResult {
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

        // Install any inductive FAMILIES in the closure first, through checked
        // `add_inductive`. They are value-less and can never satisfy the
        // confidence gate; making them resident is what lets the existing
        // residency rule admit them, and it is honest because the kernel
        // validated each one. Must precede the gate — the gate rejects on the
        // first inadmissible dependency, so a family installed afterwards would
        // never be reached. See `replay_inductive_families_for`.
        replay_inductive_families_for(env, candidate, library);

        validate_dependency_loader_trust(env, candidate, library, trust_gate)?;

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
        if env.get_const(&decl_name).is_none() {
            let dep_name = decl_name.to_string();
            env.add_decl(decl)
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
    // The previous note here claimed the shard format does not store universe
    // level parameters. That is FALSE and was actively misleading: the format
    // carries both a per-declaration level-param name range
    // (`MathverseConstantHeader::level_params_{start,count}`, reconstructed by
    // `mathverse_env.rs::header_to_declaration` via `reconstruct_level_params`)
    // and a `level_lists` table for per-`Const` universe ARGUMENTS
    // (`shard.rs`, exposed by `MathverseLibrary::level_lists`). What was actually
    // broken was the consumer: every reconstruction site called the no-arg
    // `reconstruct_from_shard`, which hardcodes an empty level-list table
    // (`shard_reconstruct.rs:56-63`). Those sites now pass
    // `library.level_lists()`.
    Ok(())
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
    load_candidate_closure(&mut state.env, candidate, trust_gate)?;
    let name = clean_kernel::name::Name::from_string(&candidate.name);
    let proof_expr = state.mk_const(&name);
    // EXACT, deliberately: the nullary search path closes a goal only when the
    // candidate's whole type unifies. The by-name path uses `apply` instead.
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

    // Names this citation stood on without installing; see the PROVENANCE note below.
    let mut resident_dependencies: Vec<String> = Vec::new();

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

        let dep_kernel_name = clean_kernel::name::Name::from_string(dep_name);

        // RESIDENCY BEFORE TRUST — but residency means KERNEL-CHECKED residency.
        //
        // The shard-confidence gate exists to bound what this tactic ADDS to the
        // environment. A dependency already present is not added — the loader
        // only `add_decl`s declarations absent from `env` — so vetting it on
        // shard confidence rejects a candidate over a constant we will never
        // touch.
        //
        // This is not a nicety; it is what made the lane usable at all. Value-less
        // declarations (Inductive / Constructor / Recursor / Quot) can NEVER be
        // stamped `KernelVerified`, because `stamp-verified` only stamps names
        // whose VALUE the kernel accepted, and these have no value. Every real
        // theorem's closure contains `Eq`, `Eq.refl`, `Eq.rec`, `And`, `Iff` …,
        // so on confidence alone `Strict` is unsatisfiable at 100% stamping
        // coverage — not merely unsatisfied. Those constants are exactly the ones
        // `Environment::with_prelude` already supplies.
        //
        // SOUNDNESS — why this is `declaration_verification`, not `get_const`.
        //
        // Name presence is NOT evidence of a kernel check. `.olean` import
        // registers through `extend_{inductives,constructors,recursors,constants}
        // _unchecked` (clean-olean `import/load_register.rs`), which records
        // `DeclarationVerification::Unchecked`: no positivity check, no universe
        // check, eliminators taken verbatim from the file. A lane such as
        // `MATHVERSE_PRELOAD_OLEAN` therefore made unchecked material resident,
        // and a name-presence test admitted it into a `TrustGate::Strict` closure
        // — printing "GOAL CLOSED … via TrustGate::Strict" over declarations no
        // kernel ever validated. That is the exact failure this gate exists to
        // prevent.
        //
        // `FullKernelCheck` is written only by paths that ran the kernel's full
        // check on the exact type/value pair: `Environment::add_decl`
        // (`decl_add.rs`), the checked inductive/constructor path
        // (`inductive_builder.rs` — positivity, nested positivity, block
        // agreement, strict field occurrence, and a real `TypeChecker` over type
        // formers and constructor types), and `validate_and_stamp_recursor` after
        // `check_decl_readonly_strict` (`registration.rs`). The map is
        // `serde(skip)`, so a deserialized environment yields `None` and is
        // rejected rather than implicitly trusted. This test can therefore only
        // ever admit FEWER dependencies than name presence did.
        //
        // Residency is earned two ways, both through that checked path:
        // `Environment::with_prelude` (measured: all 51 constants this lane
        // admits by residency are `FullKernelCheck`, recursors included), and
        // `replay_inductive_family_checked` via `replay_inductive_families_for`,
        // which rebuilds a family on a scratch clone, installs it through checked
        // `add_inductive`, and byte-matches the regenerated members against the
        // shard before committing.
        //
        // INVARIANT. The candidate's transitive closure is
        // ⊆ (admitted-by-gate ∪ kernel-checked ambient environment). The second
        // set is no longer "whatever happens to share a name with a closure
        // member" — it is exactly the declarations this kernel checked itself.
        //
        // On rejection we still name the FIRST offending dependency, which is
        // the actionable diagnostic.
        let name_resident = env.get_const(&dep_kernel_name).is_some();
        let already_resident = matches!(
            env.declaration_verification(&dep_kernel_name),
            Some(clean_kernel::DeclarationVerification::FullKernelCheck)
        );

        // SHADOWED-BY-UNCHECKED. A name that is resident WITHOUT a full kernel
        // check cannot be rescued by shard confidence, and this is not a
        // conservative flourish — it is the only correct verdict. The loader adds
        // a declaration only when `state.env.get_const(name).is_none()`, so for a
        // name-resident constant the environment's copy is what the kernel will
        // type-check the citation against; the shard's `KernelVerified` row is
        // never installed and its stamp says nothing about the term actually
        // used. Admitting it would let unchecked `.olean` material stand in for a
        // verified declaration under a gate that promises the opposite.
        //
        // Scoped to the gates that demand `KernelVerified`. `Relaxed` is the
        // explicitly weaker bang-variant gate and keeps its previous behavior.
        if name_resident
            && !already_resident
            && matches!(
                trust_gate,
                TrustGate::Strict | TrustGate::RelaxedFoundational
            )
        {
            return Err(TacticError::SearchExhausted {
                tactic: "mathverse_use".into(),
                detail: format!(
                    "dependency loader rejected `{}`: dependency `{dep_name}` is resident in the environment without a full kernel check ({}); the loader will not replace it, so its shard trust {} cannot apply under {}",
                    candidate.name,
                    declaration_verification_label(env.declaration_verification(&dep_kernel_name)),
                    import_confidence_label(confidence),
                    trust_gate.label()
                ),
            });
        }

        // SILENT SUBSTITUTION. Residency is matched by NAME, so a resident
        // declaration that was genuinely kernel-checked can still be a DIFFERENT
        // declaration than the one the shard closure names. The measured instance:
        // `Environment::with_prelude` seeds hand-rolled `Declaration::Axiom` stubs
        // called `Fact`, `Fact.mk`, `Fact.out` (`env/algebra_substructures.rs`
        // `init_fact`), plus `Finset`/`Multiset`. The kernel really did check those
        // axioms — they are `FullKernelCheck` — but they are Clean's stubs, not
        // Mathlib's structure, so a citation resting on them reports success
        // against something other than the theorem's actual closure.
        //
        // The cheapest sound discriminator is KIND, and it is exact for this
        // family: an axiom stub can never present as an inductive. A shard row
        // claiming `Inductive`/`Constructor`/`Recursor` must be backed by the
        // corresponding structured kernel value, which only `add_inductive` (or a
        // checked family replay) can create. `Fact` fails immediately —
        // `get_inductive` is `None` for an axiom — and the citation fails closed
        // instead of quietly succeeding against a stub.
        //
        // Scope, stated honestly: KIND alone catches kind substitution, not type
        // substitution. TYPE substitution is now caught by the companion check
        // `validate_resident_type_agreement` immediately below. VALUE
        // substitution — a resident `Definition` with the very same type but a
        // different body — is deliberately ADMITTED, not overlooked: Prop-typed
        // residents are exempt by proof irrelevance, and for the rest the checked
        // `add_decl` registration below re-checks every installed value against
        // the resident bodies, so a divergence the proof depends on fails at the
        // kernel. Measured pool, reachability and the one live witness
        // (`Nat.beq`) are in that function's SCOPE note; the property is pinned
        // by `mathverse_value_substitution_tests.rs`.
        //
        // The complementary lever is `discharge_fabricated_stubs_for` (above),
        // which retires the fabricated carrier so the genuine declaration can
        // install through `add_inductive`/`add_decl` and this check then passes
        // on the RIGHT declaration. It is deliberately narrower than
        // `Environment::try_with_prelude_for_import`, which is NOT the "suppress
        // exactly the `Fact`/`Finset`/`Multiset` stubs" switch an earlier note
        // here claimed: measured against HEAD it drops 1,159 of the prelude's
        // 1,885 constants (‑35 inductives, ‑38 constructors, ‑105 recursors,
        // including `Subtype`, `Fintype`, `Char`, `String`, `BitVec` and the
        // whole `Preorder`…`Field` hierarchy). Those are value-less rows the
        // shard can never stamp `KernelVerified`, so switching a consumer to it
        // trades this refusal for a strictly larger unsatisfiable-by-
        // construction hole.
        if already_resident
            && matches!(
                trust_gate,
                TrustGate::Strict | TrustGate::RelaxedFoundational
            )
        {
            let shape_backed = match decl_kind {
                DeclKind::Inductive => env.get_inductive(&dep_kernel_name).is_some(),
                DeclKind::Constructor => env.get_constructor(&dep_kernel_name).is_some(),
                DeclKind::Recursor => env.get_recursor(&dep_kernel_name).is_some(),
                _ => true,
            };
            if !shape_backed {
                return Err(TacticError::SearchExhausted {
                    tactic: "mathverse_use".into(),
                    detail: format!(
                        "dependency loader rejected `{}`: resident declaration `{dep_name}` is not registered as {} in the environment, so it is a different declaration than the shard closure names (stub substitution)",
                        candidate.name,
                        decl_kind_name(decl_kind)
                    ),
                });
            }

            // TYPE SUBSTITUTION — the other half of the same hole. Additive:
            // it runs after the kind test and replaces nothing.
            validate_resident_type_agreement(
                env,
                &candidate.name,
                dep_name,
                &dep_kernel_name,
                header,
                library,
            )?;
        }

        if !already_resident && !trust_gate.accepts_dependency(confidence, decl_kind, dep_name) {
            // Distinguish "absent" from "present but never kernel-checked". The
            // second is the soundness-relevant case and used to be invisible.
            let provenance = if name_resident {
                format!(
                    " (resident but not kernel-checked: {})",
                    declaration_verification_label(env.declaration_verification(&dep_kernel_name))
                )
            } else {
                String::new()
            };
            return Err(TacticError::SearchExhausted {
                tactic: "mathverse_use".into(),
                detail: format!(
                    "dependency loader rejected `{}`: dependency `{dep_name}` has trust {} (kind {}), below {}{provenance}",
                    candidate.name,
                    crate::error_render::opaque(&confidence),
                    decl_kind_name(decl_kind),
                    crate::error_render::opaque(&trust_gate)
                ),
            });
        }

        // The foundational half of `RelaxedFoundational` admits by NAME and
        // kind alone. The name must also denote the kernel's canonical
        // declaration in the live environment (exact statement and universe
        // arity), never a library axiom that merely shares the name.
        //
        // Scoped to dependencies admitted through `accepts_dependency` above,
        // i.e. the NON-resident ones: that is the only path on which the
        // foundational half admits anything. A kernel-checked resident was
        // admitted by the residency rule instead, after the kind discriminator
        // and `validate_resident_type_agreement`; applying this test to it would
        // reject every value-less resident (`Eq`, `Iff`, `And` …) — none of which
        // is a foundational axiom — and make `Strict` unsatisfiable again.
        if !already_resident
            && !trust_gate.accepts(confidence)
            && !env.is_canonical_foundational_axiom(&dep_kernel_name)
        {
            return Err(TacticError::SearchExhausted {
                tactic: "mathverse_use".into(),
                detail: format!(
                    "dependency loader rejected `{}`: dependency `{dep_name}` is admitted only as a \
                     foundational axiom, but the environment holds no canonical kernel declaration \
                     of that name",
                    candidate.name
                ),
            });
        }

        // PROVENANCE. Record the closure members this citation STOOD ON rather
        // than installed. Each passed the kind, type-agreement and
        // `accepts_dependency` gates, so this is not a trust fallback — but the
        // citation's meaning rests on the resident BEING the declaration the
        // shard names, and VALUE agreement is deliberately not enforced (see
        // `validate_resident_type_agreement`'s SCOPE note). Counting them makes
        // that dependence visible instead of silent.
        if already_resident && idx != candidate.constant_idx {
            resident_dependencies.push(dep_name.to_string());
        }

        // Reconstructability only matters for constants we intend to rebuild out
        // of the shard. A resident dependency is used from the environment as-is,
        // so its shard encoding is irrelevant — EXCEPT for the selected candidate
        // itself, which we always rebuild and apply.
        if !already_resident || idx == candidate.constant_idx {
            validate_reconstructable_dependency(
                &candidate.name,
                dep_name,
                header,
                decl_kind,
                library,
            )?;
        }

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

        if !already_resident && !can_replay_missing_dependency(decl_kind, header, &dep_kernel_name)
        {
            // Say WHY. The generic "metadata" wording is right for value-less
            // family members, but an axiom row and a reserved-name row are
            // refused on principle, not for want of data (see
            // `can_replay_missing_dependency`).
            let why = if clean_kernel::is_reserved_ambient_axiom_name(&dep_kernel_name) {
                "its name is reserved for a kernel foundation or trust marker, which only the \
                 ambient environment may supply — no shard row is admitted for checked registration"
                    .to_string()
            } else if matches!(decl_kind, DeclKind::Axiom) {
                "an axiom carries no value for checked registration to re-check, so it must come \
                 from the ambient environment"
                    .to_string()
            } else {
                let metadata_requirement = if is_inductive_family_decl(decl_kind) {
                    "full InductiveDecl data"
                } else {
                    "full DeclKind-preserving metadata"
                };
                format!(
                    "{} metadata without {metadata_requirement} for checked registration",
                    decl_kind_name(decl_kind)
                )
            };
            return Err(TacticError::SearchExhausted {
                tactic: "mathverse_use".into(),
                detail: format!(
                    "dependency loader rejected `{}`: dependency `{dep_name}` is not replayable: {why}",
                    candidate.name
                ),
            });
        }
    }

    // PROVENANCE REPORT. A successful validation means every closure member was
    // either installed from the shard or already resident and kernel-checked.
    // The resident ones are what this citation STANDS ON without having replaced:
    // kind and definitional TYPE are enforced for them, VALUE agreement is not
    // (see `validate_resident_type_agreement`'s SCOPE note). Silent dependence is
    // the part worth being able to see, so name them on request.
    if !resident_dependencies.is_empty() && std::env::var_os("CLEAN_MATHVERSE_PROVENANCE").is_some()
    {
        eprintln!(
            "mathverse-provenance: `{}` stood on {} resident declaration(s) not installed from the shard: {}",
            candidate.name,
            resident_dependencies.len(),
            resident_dependencies.join(", ")
        );
    }

    Ok(())
}

/// Reject a RESIDENT dependency whose TYPE does not agree with the type the
/// shard row carries for the same name.
///
/// # The hole this closes
///
/// The loader adds only declarations it finds ABSENT, so for a resident
/// dependency the environment's copy is the one the kernel will use. Residency
/// is matched by NAME. A resident declaration that shares a name — and, after
/// the kind test above, a KIND — with a shard row can therefore still be a
/// DIFFERENT declaration, and the citation then reports success about the
/// shard's constant while resting on Clean's. Unlike a kind clash, which fails
/// closed, that failure mode succeeds SILENTLY.
///
/// # What is compared, and why definitionally
///
/// Universe parameters are canonicalized POSITIONALLY on both sides first:
/// `Eq.ndrec` is `[u1, u2]` in the shard and `[v, u]` in the prelude — same
/// declaration, different spelling AND different order — so comparing under the
/// original names would reject it. Arity is checked before renaming; a
/// mismatch there is a genuine difference (`List.zip` is 2 shard params vs 1
/// resident) and is rejected on the header alone, with no reconstruction.
///
/// There is no alpha-equivalence pass because none is needed: `ExprKind::Lam`
/// and `ExprKind::Pi` carry `BinderData` and no binder NAME (`expr/types.rs`),
/// so with de Bruijn indices structural equality on `Expr` already IS
/// alpha-equivalence.
///
/// After canonicalization the comparison is:
///
/// 1. structural `Expr ==` — the common case, and free;
/// 2. `TypeChecker::is_def_eq`;
/// 3. `is_def_eq` again after erasing VERIFIED binder gadgets (below).
///
/// Definitional, not syntactic, and that is not a preference — a syntactic
/// comparison is not viable at any level of normalization. Measured over the
/// 308-name Mathlib citation population against `/tmp/mlcc-audit/after`, a
/// maximally normalized syntactic check (level-param canonicalization + mdata
/// stripping + binder-info erasure + level normalization) still rejects
/// 158/308 probes, because the residue is delta: the shard says `Not p` where
/// the prelude states `p → False` (`Classical.em`, `absurd`, `Decidable.rec`,
/// `if_neg`, …), and the shard says `Decidable.decide` where the prelude says
/// `decide`. Those are the same declaration and no amount of syntactic
/// normalization can see it. Raw structural equality rejects 277/308.
///
/// THE TRADE, stated: `is_def_eq` is more permissive than "is the same
/// declaration". It admits a resident whose type is provably equal to the
/// shard's but differently spelled — exactly the `Not p` / `p → False` case
/// above. That permissiveness is load-bearing (it is worth 158/308 probes) and
/// it is sound in the only sense that matters here: a proof term elaborated
/// against one type is accepted by the kernel against any definitionally equal
/// type, so the citation does not become checkable-only-by-accident.
///
/// # Binder gadgets
///
/// `is_def_eq` cannot delta a constant that is not resident, and at the moment
/// this gate runs the closure is not yet installed. Measured, exactly one
/// family in the population is affected: the shard writes `Membership` /
/// `Membership.mem` with an `outParam (Type u)` argument where the prelude
/// writes `Type u`, and `outParam` is not in the prelude. Left alone that
/// costs 7/308 probes.
///
/// So rung 3 erases the Lean 4 binder-annotation gadgets — but only after
/// PROVING, against the shard itself, that each one really is the identity on
/// its first argument (`shard_identity_gadget_arity`), and only for gadgets
/// ABSENT from `env`. Absent from `env` matters twice: it is the only case
/// where `is_def_eq` cannot do the job itself, and it means the RESIDENT type
/// cannot mention the gadget either (a `FullKernelCheck` declaration's type
/// only names resident constants), so the erasure touches the shard side
/// alone. Each erasure step is then literally one delta plus one beta — the
/// reduction `is_def_eq` would have performed had the gadget been installed —
/// so it cannot equate two types that definitional equality would separate.
/// Nothing is assumed about these names: a gadget whose shard value is not an
/// identity, or which the shard does not declare, is not erased.
///
/// # Fail-closed
///
/// Reconstruction failure, unreadable universe parameters, a vanished resident,
/// and heartbeat exhaustion inside `is_def_eq` (which returns `false`) are all
/// REJECTIONS. Measured cost of that policy on the population: zero — there
/// were 0 reconstruction failures across all 11,444 resident-dependency visits.
///
/// # Measured
///
/// Population: the 308-name Mathlib by-name citation set against the union
/// shard `/tmp/mlcc-audit/after` (65,287 constants, 45,478 `KernelVerified`),
/// one process per name. 307/308 closed before this check and 307/308 after,
/// with byte-identical per-name verdicts; the single failure is unrelated
/// (`not_beq_of_ne`, `LawfulBEq` below `Strict`).
///
/// Outside that population the check does bite, as intended. Over a 200-name
/// sample of the corpus-wide candidates — `KernelVerified` theorems whose
/// closure names a resident that is not the shard's declaration — 7 closed
/// before and 6 after. The one that flipped is
/// `_private.Init.Data.Fin.Fold.1.Fin.foldlM_loop_lt`, whose closure names
/// `Nat.succ_add`: Clean's prelude proves it over `Nat.add`
/// (`env/algebra_nat_succ_add_proof.rs`) while Init states it over
/// `HAdd.hAdd`, and Clean's kernel does not reduce that instance-projection
/// chain. Before this check the citation CLOSED and reported success about
/// Init's theorem while resting on Clean's; it is now refused. Whether the two
/// statements are the same theorem is exactly what the environment cannot
/// decide at that moment, which is why the verdict is a refusal.
///
/// # SCOPE — VALUE substitution is admitted, and why that is not a hole
///
/// Type agreement is not DECLARATION agreement: a resident `Definition` /
/// `Opaque` with the same type and a different BODY passes this check. That is
/// deliberate and it was measured before it was decided. Everything in this
/// section is HEAD (`ea7bb04e7`) against the union shard `/tmp/mlcc-audit/after`
/// (65,287 constants, 45,478 `KernelVerified`) and `Environment::with_prelude()`
/// (1,885 constants), 2026-07-31, one process per name.
///
/// ## The exposed set
///
/// | step | n |
/// |---|---|
/// | prelude constants | 1,885 |
/// | collide by NAME with a visible shard row | 1,199 |
/// | refused as shadowed-by-unchecked | 0 (every prelude decl is `FullKernelCheck`) |
/// | refused by the KIND discriminator | 3 (`Fact`, `Fact.mk`, `Monad`) |
/// | refused HERE (141 not def-eq + 22 universe-arity) | 163 |
/// | admitted | 1,033 |
/// | — Prop-TYPED, so proof-irrelevant | 151 |
/// | — non-Prop but the resident carries NO value | 252 |
/// | — **exposed pool** (462 `Definition`, 152 `Recursor`, 16 `Opaque`) | **630** |
///
/// ## Bound 1 — Prop-typed residents are exempt by construction
///
/// Definitional proof irrelevance (`clean-kernel/src/tc/def_eq/proof_irrel.rs`,
/// applied in `def_eq/mod.rs` right after phase-1 WHNF and BEFORE the lazy-delta
/// loop) makes any two inhabitants of the same Prop interchangeable, so a
/// Prop-typed resident's body cannot affect any def-eq outcome. The only MODE
/// in which it is declined is `CleanMode::Cubical` / `CleanMode::Directed`
/// (where it would derive UIP against univalence); `with_prelude()` is
/// `Classical` (measured), so it is live. Its other refusals — a type it cannot
/// infer — only make def-eq more conservative. The exemption keys on the TYPE, not
/// the kind — 14 of the 151 are `Definition`s with Prop types (`rfl`, `Iff.mp`,
/// `And.left`, …). 54 of the 151 are reached by the 308-name population,
/// including its three busiest residents (`rfl` 215, `propext` 208, `Iff.rfl`
/// 163).
///
/// ## Bound 2 — everything the loader ADDS is re-checked against the resident
///
/// The closure members that are ABSENT are registered through checked
/// `Environment::add_decl` (in `load_candidate_closure_inner`), which checks each
/// value against its type IN THE SESSION ENVIRONMENT — i.e. against the
/// residents' actual bodies, never against the shard's. So a value divergence
/// the cited proof actually DEPENDS on is refused by the kernel, and one it does
/// not depend on is immaterial to the proof. And a resident `Definition` /
/// `Opaque` that `add_decl` accepted is a conservative (definitional) extension
/// whatever its body: it can only change which terms are def-eq, never make a
/// false Prop provable. Both halves are pinned in
/// `mathverse_value_substitution_tests.rs` (shard `Victim := 1` vs resident
/// `Victim := 0`; `Victim = 1` is refused, `Victim = Victim` closes).
///
/// The residual harm is therefore PROVENANCE, not soundness: a citation can
/// report success under the shard's name while what the kernel checked was
/// Clean's reading of a closure member.
///
/// ## How much of the pool actually diverges
///
/// Of the 630: 277 structurally identical, 145 `is_def_eq`, 21 after gadget
/// erasure, 17 shard row valueless (`Float.*` / `System.Platform.*` externs), 1
/// unreconstructable (`UInt64.size`), and 169 not def-eq in the BARE prelude.
/// Those 169 are an upper bound, not the answer: 52 become def-eq once the shard
/// value's own closure is installed through checked `add_decl`, because they
/// only failed on constants absent at gate time (`*.match_1`, `*._f`, `trivial`,
/// `not_false`, `Nat.brecOn`) — the same absent-constant artifact the binder
/// gadget note above describes. That leaves 26 conclusive corpus-wide
/// divergences (`Bool.xor`, `Option.filter`, `instBEqOption`, 23
/// `*.noConfusion`) and 91 inconclusive (blocked on inductive aux this
/// measurement did not replay). **All 26 have reach 0 in the population.**
///
/// ## Reachability, which is what closes it
///
/// Only 136 residents are visited at all by the 308 closures — 40 of the 630
/// pool, 7 of the 169, and 0 names this function refuses (consistent with
/// 307/308 before and after `ea7bb04e7`, byte-identical). Six of those 7
/// (`instDecidableTrue` 135, `instDecidableFalse` 132, `instDecidableNot` 128,
/// `Bool.decEq` 3, `instDecidableAnd` 2, `instDecidableOr` 2) are def-eq once the
/// closure installs. The seventh, `Nat.beq` (reach 4), is the single genuine
/// reachable divergence: Clean's prelude uses nested `Nat.rec` where Init uses
/// the `brecOn`-compiled form (`Nat.brecOn … Nat.beq._f`). They are not def-eq
/// as OPEN terms and agreed on every closed input tested (25/25 over `(0..4)²`),
/// so the practical failure mode is a lost `rfl` step, not a false theorem.
///
/// ## Why no value check is built here
///
/// 1. It would reject those six on reach 135/132/128/3/2/2 — 177 of the 308
///    probes name a value-divergent resident (141 restricting to data-typed
///    ones) against today's 307/308 — for zero soundness gain.
/// 2. It cannot be a cheap pre-pass at all. This TYPE check stands alone
///    because a `FullKernelCheck` declaration's type only names resident
///    constants; VALUES have no such property, which is exactly why 6 of the 7
///    are artifacts. A sound value check would have to install the closure
///    first, i.e. run after the work it is supposed to gate.
/// 3. Runtime is not the objection: a full 308-closure census including
///    structural + `is_def_eq` on every value pair runs in 1.74 s wall.
///
/// The proportionate remedy for a genuine witness is a PRELUDE change — make
/// Clean's declaration the one Init/Mathlib carries — which removes the witness
/// instead of refusing the citation, and costs no citability. `Nat.beq` is the
/// one declaration that qualifies today.
///
/// `Multiset`, the long-standing named suspect, is NOT a witness here: it does
/// not occur in the audited shard at all (0 rows named `Multiset*`; the string
/// is absent from the shard bytes), so the loader can never visit it. The
/// structural suspicion is nonetheless real and unresolved —
/// `clean-kernel/src/env/data_types_multiset.rs` defines
/// `Multiset.{u} : Type u → Type u := fun α => @Quot (List α) (@List.Perm α)`
/// where Mathlib has `Quotient (List.isSetoid α)` — it is simply unwitnessed in
/// this corpus.
#[cfg(feature = "mathverse-library")]
fn validate_resident_type_agreement(
    env: &clean_kernel::Environment,
    candidate_name: &str,
    dep_name: &str,
    dep_kernel_name: &clean_kernel::name::Name,
    header: &MathverseConstantHeader,
    library: &MathverseLibrary,
) -> TacticResult {
    check_type_agreement(
        env,
        candidate_name,
        dep_name,
        dep_kernel_name,
        header,
        library,
        TypeAgreementMode::ModuloVerifiedBinderGadgets,
    )
}

/// How much a resident type and a shard type may differ and still count as
/// one declaration.
#[cfg(feature = "mathverse-library")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TypeAgreementMode {
    /// The resident STANDS IN for the shard row (it stays resident and the
    /// citation is checked against it): definitional equality, or equality
    /// after erasing the shard's kernel-verified binder gadgets.
    ModuloVerifiedBinderGadgets,
    /// The shard row will REPLACE the resident (stub discharge): syntactic or
    /// definitional equality only. Every resident that mentions the carrier was
    /// checked against its type, so a looser match would leave those checks
    /// describing a different constant.
    DefEqOnly,
}

/// The comparison behind [`validate_resident_type_agreement`] and the stub
/// discharge's authentication, parameterized by [`TypeAgreementMode`].
#[cfg(feature = "mathverse-library")]
fn check_type_agreement(
    env: &clean_kernel::Environment,
    candidate_name: &str,
    dep_name: &str,
    dep_kernel_name: &clean_kernel::name::Name,
    header: &MathverseConstantHeader,
    library: &MathverseLibrary,
    mode: TypeAgreementMode,
) -> TacticResult {
    use clean_kernel::level::Level;
    use clean_kernel::name::Name;
    use clean_mathverse::shard_reconstruct::{
        reconstruct_level_params, reconstruct_single_subdag_public,
    };

    let reject = |why: &str| {
        let detail = format!(
            "dependency loader rejected `{candidate_name}`: resident declaration `{dep_name}` \
             does not agree in TYPE with the shard row it stands in for ({why}), so the citation \
             would rest on a different declaration than the closure names (type substitution)"
        );
        TacticError::SearchExhausted {
            tactic: "mathverse_use".into(),
            detail,
        }
    };

    // `already_resident` was established through `declaration_verification`;
    // this cannot normally be `None`, and if it ever is we have no resident type
    // to compare against — which is a rejection, not a pass.
    let Some(info) = env.get_const(dep_kernel_name) else {
        return Err(reject(
            "the resident declaration has no constant entry to compare",
        ));
    };

    // `library.level_lists()`, not the no-arg `reconstruct_from_shard`: the
    // latter hardcodes an empty level-list table and would silently drop every
    // `Const`'s universe ARGUMENTS, turning a real universe difference into a
    // spurious match.
    let shard_type = reconstruct_single_subdag_public(
        library.exprs(),
        library.levels(),
        library.strings(),
        library.level_lists(),
        header.type_idx,
    )
    .map_err(|e| reject(&format!("shard type reconstruction failed: {e}")))?;

    let shard_level_params = reconstruct_level_params(
        library.strings(),
        header.level_params_start,
        header.level_params_count,
    )
    .map_err(|e| reject(&format!("shard universe parameters unreadable: {e}")))?;

    // Arity first: decided from the header alone, no reconstruction, and a
    // difference here is never benign — the two declarations do not even take
    // the same number of universes.
    if shard_level_params.len() != info.level_params.len() {
        return Err(reject(&format!(
            "shard declares {} universe parameter(s), the resident declares {}",
            shard_level_params.len(),
            info.level_params.len()
        )));
    }

    // NO CAPTURE. Canonicalization renames both sides' DECLARED parameters into
    // a reserved namespace; a parameter already spelled that way, occurring free
    // in either type, would survive the rename and could be made to collide with
    // the other side's renamed parameter — a crafted false MATCH. A stray
    // reserved parameter is therefore a rejection. Real Lean universe parameters
    // are `u`, `v`, `u_1`, …, so this costs nothing and cannot be relied on by
    // anything legitimate.
    if mentions_reserved_level_param(&shard_type) || mentions_reserved_level_param(&info.type_) {
        return Err(reject(
            "a type mentions a universe parameter in the comparison's reserved \
             `_mathverse_lp_` namespace, which would defeat the renaming",
        ));
    }

    // Positional canonicalization: `Eq.ndrec` is `[u1, u2]` in the shard and
    // `[v, u]` in the prelude — the names AND their order differ for what is one
    // declaration. The substitution is simultaneous
    // (`instantiate_level_params_direct` builds one map), so the fresh names
    // cannot capture each other either.
    let canonical: Vec<Level> = (0..shard_level_params.len())
        .map(|i| Level::param(Name::from_string(&format!("{RESERVED_LEVEL_PREFIX}{i}"))))
        .collect();
    let shard_type = shard_type.instantiate_level_params_direct(&shard_level_params, &canonical);
    let resident_type = info
        .type_
        .instantiate_level_params_direct(&info.level_params, &canonical);

    if shard_type == resident_type {
        return Ok(());
    }

    // Default heartbeat limit deliberately: exhaustion makes `is_def_eq` return
    // `false`, which rejects. That is the fail-closed direction, and it keeps
    // this comparison on the same budget as every other kernel conversion check
    // in the process rather than inventing a private one.
    let tc = clean_kernel::TypeChecker::new(env);
    if tc.is_def_eq(&shard_type, &resident_type) {
        return Ok(());
    }

    if mode == TypeAgreementMode::ModuloVerifiedBinderGadgets {
        let erased = erase_verified_binder_gadgets(env, library, &shard_type);
        if let Some(erased) = erased {
            if erased == resident_type || tc.is_def_eq(&erased, &resident_type) {
                return Ok(());
            }
        }
    }

    Err(reject(
        "the reconstructed shard type is not definitionally equal to the resident type",
    ))
}

/// Namespace the level-parameter canonicalization renames into.
#[cfg(feature = "mathverse-library")]
const RESERVED_LEVEL_PREFIX: &str = "_mathverse_lp_";

/// Does `expr` mention a universe parameter inside [`RESERVED_LEVEL_PREFIX`]?
///
/// Guards the canonicalization in [`validate_resident_type_agreement`] against a
/// crafted shard type that pre-spells the reserved names.
#[cfg(feature = "mathverse-library")]
fn mentions_reserved_level_param(expr: &Expr) -> bool {
    use clean_kernel::level::Level;
    use clean_kernel::{ExprFolderOpt, LevelVec};

    fn level_mentions(level: &Level) -> bool {
        match level {
            Level::Zero => false,
            Level::Succ(inner) => level_mentions(inner),
            Level::Max(l, r) | Level::IMax(l, r) => level_mentions(l) || level_mentions(r),
            Level::Param(name) => name.to_string().starts_with(RESERVED_LEVEL_PREFIX),
        }
    }

    struct Scan {
        found: bool,
    }
    impl ExprFolderOpt for Scan {
        fn fold_sort_opt(&mut self, level: &Level) -> Option<Expr> {
            self.found |= level_mentions(level);
            None
        }
        fn fold_const_opt(
            &mut self,
            _name: &clean_kernel::name::Name,
            levels: &LevelVec,
        ) -> Option<Expr> {
            self.found |= levels.iter().any(level_mentions);
            None
        }
    }

    let mut scan = Scan { found: false };
    // The folder rebuilds nothing (every hook returns `None`); it is used purely
    // as the kernel's own stack-safe traversal.
    let _ = scan.fold_expr_opt(expr);
    scan.found
}

/// Lean 4's binder-annotation gadgets. Each is `@[reducible] def g … := α` in
/// Lean core — the identity on its first argument — but that is NOT taken on
/// faith here: [`shard_identity_gadget_arity`] proves it against the shard's own
/// stored value before any erasure happens.
#[cfg(feature = "mathverse-library")]
const BINDER_GADGET_NAMES: [&str; 4] = ["outParam", "semiOutParam", "optParam", "autoParam"];

/// Depth cap for the erasure fold. Overriding `fold_expr_opt` loses the kernel's
/// crate-private `stack_safe` wrapper, so bound the recursion explicitly.
/// Exceeding it abandons the erasure (returns the term unchanged), which makes
/// the caller fall through to a REJECTION.
#[cfg(feature = "mathverse-library")]
const GADGET_ERASE_MAX_DEPTH: u32 = 512;

/// If the shard declares `name` as a definition whose value is `fun a₁ … aₙ => a₁`,
/// return `n`. Otherwise `None`.
///
/// This is the whole justification for erasing the constant: with that value,
/// `name a₁ … aₙ` delta-then-beta reduces to `a₁` in one step, so replacing the
/// application by its first argument is a reduction the kernel itself would
/// perform. A row that is missing, valueless, not a definition, or whose value
/// is anything else yields `None` and nothing is erased.
#[cfg(feature = "mathverse-library")]
fn shard_identity_gadget_arity(library: &MathverseLibrary, name: &str) -> Option<usize> {
    use clean_kernel::ExprKind;
    use clean_mathverse::shard_reconstruct::reconstruct_single_subdag_public;

    let header = library.lookup_name(name)?;
    if !matches!(header.decl_kind(), Ok(DeclKind::Definition)) || !header.has_value() {
        return None;
    }
    let value = reconstruct_single_subdag_public(
        library.exprs(),
        library.levels(),
        library.strings(),
        library.level_lists(),
        header.value_idx,
    )
    .ok()?;

    let mut arity = 0usize;
    let mut cursor = &value;
    while let ExprKind::Lam(_, _, body) = cursor.kind() {
        arity += 1;
        cursor = body;
    }
    // Body must be the FIRST binder: under de Bruijn, that is index `arity - 1`.
    match cursor.kind() {
        ExprKind::BVar(idx) if arity > 0 && *idx as usize == arity - 1 => Some(arity),
        _ => None,
    }
}

/// Replace every saturated application of a verified identity gadget by its
/// first argument. Returns `None` when nothing was erased (so the caller does
/// not repeat a comparison it already made) or when the depth cap was hit.
#[cfg(feature = "mathverse-library")]
fn erase_verified_binder_gadgets(
    env: &clean_kernel::Environment,
    library: &MathverseLibrary,
    expr: &Expr,
) -> Option<Expr> {
    use clean_kernel::name::Name;

    // Only gadgets ABSENT from `env` are eligible — see the SOUNDNESS note on
    // `validate_resident_type_agreement`. A resident gadget is `is_def_eq`'s job,
    // and erasing one would substitute our reading of it for the environment's.
    let gadgets: Vec<(Name, usize)> = BINDER_GADGET_NAMES
        .iter()
        .filter_map(|name| {
            let kernel_name = Name::from_string(name);
            if env.get_const(&kernel_name).is_some() {
                return None;
            }
            shard_identity_gadget_arity(library, name).map(|arity| (kernel_name, arity))
        })
        .collect();
    if gadgets.is_empty() {
        return None;
    }

    let mut eraser = GadgetEraser {
        gadgets: &gadgets,
        depth: 0,
        truncated: false,
    };
    let folded = clean_kernel::ExprFolderOpt::fold_expr_opt(&mut eraser, expr);
    if eraser.truncated {
        return None;
    }
    folded
}

#[cfg(feature = "mathverse-library")]
struct GadgetEraser<'a> {
    gadgets: &'a [(clean_kernel::name::Name, usize)],
    depth: u32,
    truncated: bool,
}

#[cfg(feature = "mathverse-library")]
impl GadgetEraser<'_> {
    /// `g a₁ … aₙ` where `(g, n)` is a verified gadget ⇒ `a₁`.
    ///
    /// Deliberately the same shape as `clean_mathverse`'s
    /// `graduate::intake::erase_annotation_gadgets`, which performs this rewrite
    /// on the shard-BUILD side. That one hardcodes the four names and their
    /// arities; this one takes neither on faith, because here the rewrite decides
    /// whether a trust gate admits a dependency.
    fn gadget_payload(&self, expr: &Expr) -> Option<Expr> {
        use clean_kernel::ExprKind;

        let ExprKind::Const(name, _) = expr.get_app_fn().kind() else {
            return None;
        };
        let arity = self
            .gadgets
            .iter()
            .find(|(gadget, _)| gadget == name)
            .map(|(_, arity)| *arity)?;
        let args = expr.get_app_args();
        // Saturated only: a partial application is not the identity.
        (args.len() == arity).then(|| args[0].clone())
    }
}

#[cfg(feature = "mathverse-library")]
impl clean_kernel::ExprFolderOpt for GadgetEraser<'_> {
    fn fold_expr_opt(&mut self, expr: &Expr) -> Option<Expr> {
        if self.depth >= GADGET_ERASE_MAX_DEPTH {
            self.truncated = true;
            return None;
        }
        if let Some(payload) = self.gadget_payload(expr) {
            self.depth += 1;
            let folded = self.fold_expr_opt(&payload);
            self.depth -= 1;
            return Some(folded.unwrap_or(payload));
        }
        self.depth += 1;
        let folded = self.fold_expr_opt_inner(expr);
        self.depth -= 1;
        folded
    }
}

#[cfg(feature = "mathverse-library")]
fn validate_reconstructable_dependency(
    candidate_name: &str,
    dep_name: &str,
    header: &MathverseConstantHeader,
    decl_kind: DeclKind,
    library: &MathverseLibrary,
) -> TacticResult {
    use clean_mathverse::shard_reconstruct::reconstruct_single_subdag_public;

    // `library.level_lists()`, not the no-arg helper: the latter hardcodes an
    // empty table and would report a dependency as reconstructable while
    // silently dropping every `Const`'s universe arguments.
    let _ = reconstruct_single_subdag_public(
        library.exprs(),
        library.levels(),
        library.strings(),
        library.level_lists(),
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

        let _ = reconstruct_single_subdag_public(
            library.exprs(),
            library.levels(),
            library.strings(),
            library.level_lists(),
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
/// Can a dependency absent from the environment be rebuilt from its shard header
/// and registered through the CHECKED `add_decl` path?
///
/// `Definition` and `Opaque` are admitted alongside `Theorem` because
/// [`MathverseEnvironment::header_to_declaration`] now preserves the declaration
/// kind and can emit `Declaration::Definition` / `Declaration::Opaque`. Excluding
/// them was a real blocker, not caution: Mathlib closures are dominated by
/// definitions — match auxiliaries such as
/// `_private.Mathlib.Logic.Unique.1.…​.match_1_5` — and rejecting one aborts the
/// whole candidate.
///
/// Still excluded: `Inductive` / `Constructor` / `Recursor` / `Quot`. These carry
/// no value and cannot be rebuilt from a header alone; registering an inductive
/// family needs the full `InductiveDecl` (constructor list, motive arity,
/// recursor rules), which the shard format does not store. They must come from
/// the ambient environment.
///
/// SOUNDNESS: for the VALUE-BEARING kinds, admitting a kind here only makes it
/// eligible for registration; the declaration still goes through the kernel's
/// checked `add_decl`, which type-checks the value against the type, so a
/// wrongly-admitted one fails there rather than being trusted.
///
/// THAT ARGUMENT DOES NOT EXTEND TO `Axiom`, AND USED TO BE STATED AS IF IT DID.
/// An axiom has no value, so `add_decl` (env/decl_add.rs, the `Declaration::Axiom`
/// arm binds `opt_value = None`) validates only that its TYPE is a well-formed
/// Sort. It never checks the statement is true. So an admitted axiom row is
/// asserted into the session environment on the shard's say-so alone.
///
/// A working exploit was built against the old form: a valueless
/// `DeclKind::Axiom` row stamped `KernelVerified`, a `Theorem` row depending on
/// it, and a resident whose VALUE diverges from the shard's (same name, same
/// kind, definitionally equal TYPE, so both the kind discriminator and
/// `validate_resident_type_agreement` admit it). The axiom is true where the
/// shard produced it and false where it lands, `mathverse_apply_named` returned
/// `Ok(())`, and the session environment then proved `Nat.zero = Nat.succ
/// Nat.zero`. Neither existing bound covers it: proof irrelevance says two proofs
/// of a Prop are interchangeable, not that the Prop is inhabited; and the
/// re-check does not exist for a declaration with no value.
///
/// It was unreachable in the shipped corpus only by an UNENFORCED convention —
/// all 15 `Axiom` rows there sit at `Axiomatized`, and `TrustGate::Strict` wants
/// `KernelVerified` — but nothing tied "carries no value" to "cannot be
/// KernelVerified". Any importer that stamps a valueless row `KernelVerified`, or
/// any hand-built shard, reopened it, and the payoff is `False`.
///
/// So the invariant is now ENFORCED HERE, at the point of reliance: NO `Axiom`
/// row is replayed. Every axiom must come from the ambient environment, where
/// something else vouched for it.
///
/// That includes the FOUNDATIONAL names (`propext`, `Quot.sound`,
/// `Classical.choice`, the quotient primitives). This function used to exempt
/// them by NAME, on the argument that the kernel already trusts them and no
/// shard can extend them. Since e20128880 the kernel says otherwise: an axiom
/// is foundational only as the kernel's OWN canonical declaration
/// (`Environment::is_canonical_foundational_axiom`: exact statement and
/// universe arity), and a shard row named `propext` is by construction not that
/// — it is whatever statement the shard carries, possibly `False`. Replaying
/// one would install exactly the counterfeit e20128880 refuses everywhere else.
/// A genuine foundation is resident through the prelude and is admitted by the
/// residency rule instead, so the cost is zero.
///
/// For the same reason no row of ANY kind whose name is reserved for a kernel
/// foundation or trust marker (`clean_kernel::is_reserved_ambient_axiom_name`)
/// is replayed: the elaborator refuses such a declaration from source in every
/// environment, and the shard is not a more trusted source than the user's
/// file. Citability cost is zero by construction: no axiom row is admissible
/// at Strict in the corpus today, and no genuine library declaration takes a
/// reserved name.
fn can_replay_missing_dependency(
    decl_kind: DeclKind,
    header: &MathverseConstantHeader,
    dep_kernel_name: &clean_kernel::name::Name,
) -> bool {
    if clean_kernel::is_reserved_ambient_axiom_name(dep_kernel_name) {
        return false;
    }
    match decl_kind {
        DeclKind::Theorem | DeclKind::Definition | DeclKind::Opaque => header.has_value(),
        // Axiom (see above) / Inductive / Constructor / Recursor / Quot, and any
        // kind added later: fail closed.
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

/// An import confidence as it is spelled in the shard schema, for refusal
/// messages (a real renderer, not `{:?}`; see `crate::error_render`).
#[cfg(feature = "mathverse-library")]
fn import_confidence_label(confidence: ImportConfidence) -> &'static str {
    match confidence {
        ImportConfidence::KernelVerified => "KernelVerified",
        ImportConfidence::KernelBridged => "KernelBridged",
        ImportConfidence::SourceVerified => "SourceVerified",
        ImportConfidence::Translated => "Translated",
        ImportConfidence::KernelCheckedConditional => "KernelCheckedConditional",
        ImportConfidence::Axiomatized => "Axiomatized",
        ImportConfidence::Unverified => "Unverified",
    }
}

/// Which kernel gate a resident declaration passed, for refusal messages.
///
/// `None` is spelled out rather than printed as `None`: it means the
/// environment holds no verification record at all (a deserialized
/// environment, whose map is `serde(skip)`), which is itself the reason the
/// residency rule refuses it.
#[cfg(feature = "mathverse-library")]
fn declaration_verification_label(
    verification: Option<clean_kernel::DeclarationVerification>,
) -> &'static str {
    use clean_kernel::DeclarationVerification;
    match verification {
        Some(DeclarationVerification::FullKernelCheck) => "FullKernelCheck",
        Some(DeclarationVerification::StructuralOnly) => "StructuralOnly",
        Some(DeclarationVerification::Unchecked) => "Unchecked",
        None => "no verification recorded",
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

    let context_names = mathverse_context_names(&state.metas, &goal.local_ctx);
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
