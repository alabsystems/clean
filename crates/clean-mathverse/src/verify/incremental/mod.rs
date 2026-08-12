// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Incremental environment verification for `.mathverse` shard constants.
//!
//! The existing per-constant verifier (`shard_verify/constant_verify.rs`) creates
//! a fresh `Environment` for every constant, so any theorem referencing another
//! constant (e.g., `Nat.add`) fails with "unknown constant". This module builds
//! a dependency graph, topologically sorts constants, and verifies them
//! incrementally in a shared `Environment`.
//!
//! It also supports dependency-aware re-checking of a changed subset:
//! given one or more changed constant names, compute the downstream affected
//! closure, seed unchanged prerequisites into the environment via checked
//! declaration replay, and kernel-check only the affected slice. Simple
//! single-type inductive families are replayed through checked `add_inductive()`
//! by combining typed shard metadata for `InductiveDecl.num_params` with
//! constructor owner/order inferred from return heads, and metadata-backed
//! mutual `all_names` blocks are replayed as one checked `InductiveDecl`.
//! Richer imported recursor skeletons fail closed until shards carry enough
//! metadata to reconcile the full `RecursorVal`; mathverse no longer installs
//! inductive-family skeletons through unchecked declaration insertion.

use std::borrow::Cow;
use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::Arc;
use std::time::Instant;

use clean_kernel::expr::Expr;
use clean_kernel::level::Level;
use clean_kernel::tc::TypeChecker;
use clean_kernel::{ConstantInfo, Declaration, Environment, Name};

// Shared shard-side inductive-family reconstruction (single code path with
// the cake gate's carried-family replay; see `crate::inductive_replay`).
#[cfg(test)]
use crate::inductive_replay::InductiveReplayMetadata;
use crate::inductive_replay::{
    build_inductive_replay_metadata, checked_inductive_replay_matches_shard,
    inductive_all_names_from_header, reconstruct_constant, reconstruct_constant_from_slices,
    types_equal_ignoring_binder_info, NormMode, ReconstructedConstant, ShardFamilyMatch,
    ShardSlices,
};
use crate::library::MathverseLibrary;
use crate::shard::ShardReader;
use crate::types::{DeclKind, ImportConfidence, MathverseConstantHeader, NO_VALUE};

/// Axiom-discharge substitution: replace a named imported `Axiom` with a
/// hand-built kernel proof of its stated type (BRICK 1.0, route-to-100).
pub(crate) mod axiom_discharge;

#[cfg(test)]
mod tests;

// ---------------------------------------------------------------------------
// Inductive-family replay policy
// ---------------------------------------------------------------------------

/// Selects which auxiliary members the checked `add_inductive` family replay
/// generates when it installs a reconstructed `InductiveDecl`.
///
/// The kernel can install an inductive family two ways (both fully checked):
/// `Environment::add_inductive` (generates Clean's OWN convenience definitions —
/// `casesOn`/`recOn`/`noConfusion`/`noConfusionType`/`below`/`brecOn`) and
/// `Environment::add_inductive_core` (installs only the kernel certificate —
/// types, constructors, `rec` — and leaves the convenience definitions to be
/// carried from the source through ordinary checked `add_decl`).
///
/// For `.olean`-SOURCED corpora (the Mathlib stamp), `Generate` is WRONG: Clean's
/// generated convenience definitions are not Lean-faithful (Lean 4 emits the
/// heterogeneous `HEq`-chain `noConfusionType` and freshens the result universe
/// its own way; Clean emits the homogeneous `Eq` form), so they SHADOW the
/// shard's Lean-stored spellings. A downstream constant whose value was
/// elaborated against Lean's spelling (e.g. `Equiv.mk.noConfusion`,
/// `Equiv.noConfusionType` itself) then fails its re-check on a spurious
/// universe / shape mismatch even though it is genuinely valid. `LeanFaithful`
/// (== `add_inductive_core`) skips the generated twins so the shard's own
/// Lean-faithful definitions carry through the checked `add_decl` path and pass.
///
/// SOUNDNESS: both variants install the family through the SAME fully-checked
/// kernel path (positivity, universes, recursor generation all enforced).
/// `LeanFaithful` does not skip any kernel check — it skips *re-deriving* the
/// convenience definitions, which are then proof-checked individually via
/// `add_decl` (their value re-typechecked against the kernel-built `rec`). It
/// can therefore only ADD KernelVerified verdicts (accept genuinely-valid
/// Lean-spelled members that the shadow previously rejected), never false-accept.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum InductiveReplayPolicy {
    /// Generate Clean's own convenience definitions (the legacy default; correct
    /// for Clean-native/prelude content that references Clean's spellings).
    ///
    /// Default: preserves the historical behavior of every existing caller.
    #[default]
    Generate,
    /// Install only the kernel certificate (types/constructors/`rec`); carry the
    /// source's own convenience definitions through `add_decl`. Correct for
    /// `.olean`-sourced (Lean) corpora.
    LeanFaithful,
}

impl InductiveReplayPolicy {
    /// Install `decl` into `env` through the checked kernel path selected by this
    /// policy. Mirrors `graduate::intake::RecheckBase::add_family`.
    fn add_family(
        self,
        env: &mut Environment,
        decl: clean_kernel::inductive::InductiveDecl,
    ) -> Result<(), clean_kernel::KernelEnvError> {
        match self {
            Self::Generate => env.add_inductive(decl),
            Self::LeanFaithful => env.add_inductive_core(decl),
        }
    }
}

// ---------------------------------------------------------------------------
// Report
// ---------------------------------------------------------------------------

/// Result of incremental shard verification.
#[derive(Debug)]
pub struct IncrementalVerifyReport {
    /// Total constants considered by this verification run.
    pub total: usize,
    /// Constants the kernel genuinely proof-checked: a value that typechecked
    /// through `add_decl`, or a checked inductive-family replay. Does NOT include
    /// `NO_VALUE` axioms or value-bearing decls that fell back to an axiom.
    /// Invariant: `kernel_verified_names.len() == kernel_verified`.
    pub kernel_verified: usize,
    /// `NO_VALUE` constants (`DeclKind::Axiom`/`Quot`) the kernel accepted as
    /// well-formed axioms. These are NOT proof-checked.
    pub axiom_accepted: usize,
    /// Value-bearing Lean `unsafe def`s accepted TYPE-ONLY in trusted context
    /// (`AddConstResult::UnsafeAccepted`). Lean's kernel typechecks unsafe
    /// values only in a permissive mode (self-reference allowed) and
    /// structurally bars unsafe consts from proofs, so these can never be
    /// proof-checked: EXCLUDED from `kernel_verified`, but not failures and
    /// never a masked-taint seed.
    pub unsafe_accepted: usize,
    /// Value-bearing `Theorem`/`Definition`/`Opaque` constants that fell back to
    /// an axiom registration (their value failed to typecheck, or no value was
    /// present). These are NOT proof-checked and, when a value was present, may
    /// MASK a failed proof; see `axiom_fallback_names`.
    pub axiom_fallback: usize,
    /// `(name, typecheck error)` for the masked-failure subset of
    /// `axiom_fallback`: constants that HAD a value the kernel rejected before
    /// falling back to an axiom. Constants with no value are NOT listed here.
    pub axiom_fallback_names: Vec<(String, String)>,
    /// `(name, superseded replay failure)` for the family-STAND-IN subset of
    /// `axiom_fallback`: inductive-family roots / constructor rows whose
    /// checked family replay failed and whose STATED TYPE was installed as a
    /// kernel-checked opaque axiom instead ([`try_inductive_family_standin`]).
    /// Statement-only, never a masked-failure taint seed; the message records
    /// which replay stage the stand-in superseded (A2-2 diagnostics).
    pub family_standins: Vec<(String, String)>,
    /// `(name, kernel rejection)` for the STAND-IN-BLOCKED subset of
    /// `axiom_fallback`: value-bearing constants whose value the kernel
    /// rejected while their dependency CONE includes a VALUE-LESS STAND-IN
    /// (a dump-salvaged `AxiomProfile::SALVAGED_STAND_IN` axiom, a family
    /// stand-in, a forced-type-only row, or an earlier stand-in-blocked
    /// fallback) — as a DIRECT dependency or reached TRANSITIVELY through the
    /// dependency graph (conversion δ-unfolds intermediate constants' values,
    /// so the wall is hit arbitrarily deep; see [`standin_blocked_evidence`]).
    /// Such a rejection is NOT evidence of a wrong proof — the
    /// kernel's conversion could not delta/iota-reduce through the stand-in,
    /// which Coq's kernel COULD unfold when it originally checked the value —
    /// so the constant is registered as a CLEAN type-only axiom (same trust
    /// shape as `family_standins`: statement kernel-checked, value claim
    /// withheld, never `KernelVerified`) and seeds NO masked-failure taint.
    /// The kernel reason is preserved here for audit (and in the env-gated
    /// `CLEAN_SPECULATIVE_REJECT_LOG` capture under `STANDIN_BLOCKED`, whose
    /// detail is prefixed `[direct]` / `[transitive]` with the wall kind).
    /// GUARD: a rejection whose DIRECT dependency set intersects the
    /// masked-failure taint set is NEVER classified here — genuine taint
    /// takes precedence.
    pub standin_blocked_fallbacks: Vec<(String, String)>,
    /// Constants that failed kernel type-checking.
    pub failed: usize,
    /// Constants skipped because they could not be ordered due to dependency cycles.
    pub cycle_skipped: usize,
    /// Constants skipped because FlatExpr reconstruction failed.
    pub reconstruct_failed: usize,
    /// Constants registered via the legacy unchecked inductive-family path.
    ///
    /// This remains in the report for compatibility and should stay zero.
    pub inductive_registered: usize,
    /// Unchanged prerequisite constants seeded via checked declaration replay.
    pub seeded_checked: usize,
    /// Unchanged prerequisite constants seeded via the legacy unchecked path.
    ///
    /// This remains in the report for compatibility and should stay zero.
    pub seeded_unchecked: usize,
    /// Per-failure details: (constant name, error message).
    pub failures: Vec<(String, String)>,
    /// Names of the constants Clean's kernel accepted (the `KernelVerified`
    /// verdicts). Invariant: `kernel_verified_names.len() == kernel_verified`.
    /// Used to emit the kernel-verified manifest recording what Clean re-verified.
    pub kernel_verified_names: Vec<String>,
    /// Names of imported `Axiom`s that were DISCHARGED to hand-built kernel
    /// proofs ([`axiom_discharge`]): a source-system axiom that Clean re-proved
    /// as a `Theorem`. Every name here is also in `kernel_verified_names` — this
    /// is the auditable subset recording *which* KernelVerified constants were
    /// axioms in their source system, not the count of an additional verdict.
    pub discharged_axiom_names: Vec<String>,
    /// Wall-clock seconds elapsed.
    pub elapsed_secs: f64,
    /// PARAGON two-tier heartbeat escalation only: constants that failed the
    /// Tier-1 cap SPECIFICALLY on `HeartbeatExceeded` and then PASSED the
    /// escalated Tier-2 cap (`CLEAN_KERNEL_HEARTBEAT_ESCALATE`). This is the
    /// subset of `kernel_verified` attributable to escalation — never a
    /// separately-minted verdict. 0 when escalation is disabled or on the
    /// sequential paths.
    pub heartbeat_escalated_recovered: usize,
}

/// Dependency-aware re-check plan for a changed subset.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IncrementalRecheckPlan {
    /// Requested changed constants that exist in the shard.
    pub requested: Vec<String>,
    /// Requested changed constants not present in the shard.
    pub missing: Vec<String>,
    /// Unchanged prerequisites that must be seeded before re-checking.
    pub seed_order: Vec<String>,
    /// Prerequisites that participate in cycles but can still be seeded before recheck.
    pub seed_cyclic: Vec<String>,
    /// Changed constants plus their downstream dependents, in dependency order.
    pub recheck_order: Vec<String>,
    /// Affected constants skipped because they could not be ordered due to dependency cycles.
    pub cycle_skipped: Vec<String>,
}

// ---------------------------------------------------------------------------
// Dependency graph
// ---------------------------------------------------------------------------

/// Build a dependency graph for all constants in a shard.
///
/// For each constant, walks its type and (if present) value FlatExpr trees,
/// collecting referenced constant names from `FlatExpr::Const` nodes (tag 2).
/// Returns a map from constant name to the set of names it references.
pub fn build_dependency_graph(reader: &ShardReader) -> HashMap<String, HashSet<String>> {
    let mut deps: HashMap<String, HashSet<String>> = HashMap::new();

    for constant in &reader.constants {
        let name = reader
            .strings
            .get(constant.name_idx as usize)
            .cloned()
            .unwrap_or_default();

        let mut refs = HashSet::new();
        collect_const_refs(reader, constant.type_idx, &mut refs);
        if constant.value_idx != NO_VALUE {
            collect_const_refs(reader, constant.value_idx, &mut refs);
        }
        // Remove self-references (a constant may reference itself in recursive defs).
        refs.remove(&name);
        deps.insert(name, refs);
    }

    augment_inductive_family_deps(reader, &mut deps);

    deps
}

/// Fold each inductive type's constructor-field dependencies into the inductive
/// root's dependency set.
///
/// The checked `Environment::add_inductive` replay installs the inductive type
/// AND all of its constructors ATOMICALLY (see
/// [`crate::inductive_replay::build_inductive_replay_metadata`] /
/// `verify::incremental::try_add_inductive_family_checked`). A constructor's
/// field telescope can reference constants the inductive's own TYPE signature
/// never mentions — for a Lean structure / typeclass such as
/// `AddMonoid`, the type is just `Type u → Type u` (no field deps), but
/// `AddMonoid.mk` references the parent classes `AddSemigroup`, `AddZeroClass`,
/// `Zero`, … in its fields. The base `build_dependency_graph` attributes those
/// references to the SEPARATE `AddMonoid.mk` constant, so the topological order
/// is free to place the `AddMonoid` inductive root before `AddSemigroup`; the
/// atomic `add_inductive` then fails with `Unknown constant: AddSemigroup` even
/// though the reconstructed metadata is correct, cascading into every dependent
/// (`Unknown constant: AddMonoid` …).
///
/// Folding the constructor refs into the inductive root's deps makes the
/// topological order register every field dependency BEFORE the atomic
/// `add_inductive`, so the same checked replay the kernel already gates now
/// runs with its dependencies present.
///
/// SOUNDNESS: this only reorders WHEN constants are replayed; it never changes
/// WHAT the kernel checks. `add_inductive` still fully checks positivity,
/// universes, the constructor telescope, and recursor generation; a malformed
/// family still fails closed there. The family's own member names (every type
/// in the mutual block plus every constructor) are excluded from the folded
/// set, and any folded edge that would close a CYCLE in the dependency graph is
/// dropped (see below). The fold can therefore only ever DELAY an inductive
/// root in the topological order behind constants it genuinely needs; it can
/// never reorder anything ahead of its real dependencies, and it can never turn
/// an orderable graph into a cyclic one.
///
/// Cycle safety: a genuine MUTUAL inductive block (`Even`/`Odd`, whose
/// constructors reference each other) would, if folded naively, gain edges in
/// BOTH directions and become a cycle the topological sort then drops entirely.
/// Mutual families are instead the responsibility of the `all_names`-backed
/// replay path (a single checked `add_inductive` over the whole block) or fail
/// closed without it — so this fold must not perturb their scheduling. We
/// therefore add a folded edge `Ind -> Dep` only when `Dep` does not already
/// (transitively, in the base graph) depend back on `Ind`; an edge that would
/// create a cycle is skipped, leaving the base behavior intact for that pair.
fn augment_inductive_family_deps(
    reader: &ShardReader,
    deps: &mut HashMap<String, HashSet<String>>,
) {
    // Map inductive-type owner name -> the family member names to exclude from
    // its folded dependency set (all mutual-block type names + own ctor names).
    let mut family_members: HashMap<String, HashSet<String>> = HashMap::new();
    // Accumulated constructor-field references, keyed by owning inductive name.
    let mut ctor_refs: HashMap<String, HashSet<String>> = HashMap::new();

    for constant in &reader.constants {
        let Ok(decl_kind) = DeclKind::try_from(constant.decl_kind) else {
            continue;
        };
        if decl_kind != DeclKind::Inductive {
            continue;
        }
        let Some(ind_name) = reader.strings.get(constant.name_idx as usize) else {
            continue;
        };
        let mut members: HashSet<String> = HashSet::new();
        members.insert(ind_name.clone());
        if let Ok(Some(all_names)) = inductive_all_names_from_header(reader, constant) {
            for member in all_names {
                members.insert(member.to_string());
            }
        }
        family_members.insert(ind_name.clone(), members);
        ctor_refs.entry(ind_name.clone()).or_default();
    }

    if family_members.is_empty() {
        return;
    }

    // Attribute every constructor's field references to its owning inductive
    // (the return-target head), matching the family-grouping used by the
    // checked replay reconstruction.
    for constant in &reader.constants {
        let Ok(decl_kind) = DeclKind::try_from(constant.decl_kind) else {
            continue;
        };
        if decl_kind != DeclKind::Constructor {
            continue;
        }
        let Some(ctor_name) = reader.strings.get(constant.name_idx as usize) else {
            continue;
        };
        let Ok(reconstructed) = reconstruct_constant(ctor_name, reader, constant) else {
            continue;
        };
        let Some((owner, _)) =
            crate::inductive_replay::constructor_return_target(&reconstructed.type_expr)
        else {
            continue;
        };
        let owner = owner.to_string();
        if !ctor_refs.contains_key(&owner) {
            continue;
        }
        let mut refs = HashSet::new();
        collect_const_refs(reader, constant.type_idx, &mut refs);
        ctor_refs.entry(owner).or_default().extend(refs);
    }

    // Deterministic fold order: the per-pair cycle check below consults the
    // live graph (which already contains earlier folds), so a stable iteration
    // order is required for a reproducible dependency graph.
    let mut ordered: Vec<String> = ctor_refs.keys().cloned().collect();
    ordered.sort_unstable();
    for ind_name in ordered {
        // Union the constructor-field references of EVERY member of this
        // inductive's mutual block. The checked `add_inductive` builds a mutual
        // block as one unit (all types + ctors registered as temps, then
        // type-checked together), so replaying ANY member needs the external
        // deps of ALL siblings' constructors — e.g. `EqCnstr`'s own former/ctors
        // don't reference the external `def RingExpr`, but its sibling
        // `EqCnstrProof`'s ctor does. Attributing refs only per owning inductive
        // let `EqCnstr` sort before `RingExpr`, so the whole-block build it
        // triggers failed with `Unknown constant`. For a single-inductive family
        // (`family_members = {self}`) this union is exactly `ctor_refs[self]` —
        // provably identical to the prior behavior, so non-mutual families
        // (every A1/nested/Class C headline family) are unaffected.
        let mut refs: HashSet<String> = HashSet::new();
        if let Some(members) = family_members.get(&ind_name) {
            for member in members {
                if let Some(member_refs) = ctor_refs.get(member) {
                    refs.extend(member_refs.iter().cloned());
                }
            }
            // Exclude the block's own members (type names + own ctors are built
            // by the block replay itself, not external dependencies).
            for member in members {
                refs.remove(member);
            }
        }
        // Only fold edges that keep the dependency graph acyclic: skip any
        // `Dep` that already (transitively, in the current graph) reaches back
        // to `ind_name`. This protects genuine mutual inductive blocks, whose
        // scheduling is owned by the `all_names`-backed replay / fail-closed
        // paths, from being turned into dropped cycles.
        let mut folded: Vec<String> = refs
            .into_iter()
            .filter(|dep| dep != &ind_name && !depends_on(deps, dep, &ind_name))
            .collect();
        folded.sort_unstable();
        if let Some(ind_deps) = deps.get_mut(&ind_name) {
            ind_deps.extend(folded);
        }
    }
}

/// Does `from` transitively depend on `target` in `deps` (i.e. is there a path
/// `from -> ... -> target` following dependency edges)? Used to keep
/// [`augment_inductive_family_deps`] from folding an edge that would close a
/// cycle. Bounded by the number of nodes; only follows edges present in `deps`.
fn depends_on(deps: &HashMap<String, HashSet<String>>, from: &str, target: &str) -> bool {
    if from == target {
        return true;
    }
    let mut visited: HashSet<&str> = HashSet::new();
    let mut stack: Vec<&str> = vec![from];
    while let Some(node) = stack.pop() {
        if !visited.insert(node) {
            continue;
        }
        let Some(edges) = deps.get(node) else {
            continue;
        };
        for edge in edges {
            if edge == target {
                return true;
            }
            stack.push(edge.as_str());
        }
    }
    false
}

/// Build the reverse dependency graph (dependency -> direct dependents).
pub fn build_reverse_dependency_graph(
    deps: &HashMap<String, HashSet<String>>,
) -> HashMap<String, HashSet<String>> {
    let mut reverse: HashMap<String, HashSet<String>> = deps
        .keys()
        .map(|name| (name.clone(), HashSet::new()))
        .collect();

    for (name, references) in deps {
        for dep in references {
            if deps.contains_key(dep) {
                reverse.entry(dep.clone()).or_default().insert(name.clone());
            }
        }
    }

    reverse
}

/// Walk a FlatExpr tree rooted at `root_idx` and collect all referenced
/// constant names (from tag=2 Const nodes) into `out`.
fn collect_const_refs(reader: &ShardReader, root_idx: u32, out: &mut HashSet<String>) {
    if root_idx as usize >= reader.exprs.len() {
        return;
    }

    let mut visited = HashSet::new();
    let mut stack = vec![root_idx];

    while let Some(idx) = stack.pop() {
        let idx_usize = idx as usize;
        if idx_usize >= reader.exprs.len() || !visited.insert(idx) {
            continue;
        }
        let expr = &reader.exprs[idx_usize];
        let edata = &expr.data;
        let read_u32 = |off: usize| -> u32 {
            u32::from_le_bytes([edata[off], edata[off + 1], edata[off + 2], edata[off + 3]])
        };

        match expr.tag {
            0 | 1 | 7 | 8 | 10 => {} // BVar, Sort, LitNat, LitStr, FVar: no expr children
            2 => {
                // Const: data[0..4] = name_idx
                let name_idx = read_u32(0) as usize;
                if let Some(name) = reader.strings.get(name_idx) {
                    out.insert(name.clone());
                }
            }
            3 => {
                // App: fn, arg
                stack.push(read_u32(0));
                stack.push(read_u32(4));
            }
            4 | 5 => {
                // Lam / Pi: data[0]=binder_info, data[1..5]=ty, data[5..9]=body
                let ty = u32::from_le_bytes([edata[1], edata[2], edata[3], edata[4]]);
                let body = u32::from_le_bytes([edata[5], edata[6], edata[7], edata[8]]);
                stack.push(ty);
                stack.push(body);
            }
            6 => {
                // Let: ty, val, body
                stack.push(read_u32(0));
                stack.push(read_u32(4));
                stack.push(read_u32(8));
            }
            9 => {
                // Proj: data[0..4]=struct name, data[4..6]=field, data[6..10]=expr
                let struct_name_idx = read_u32(0) as usize;
                if let Some(name) = reader.strings.get(struct_name_idx) {
                    out.insert(name.clone());
                }
                let inner = u32::from_le_bytes([edata[6], edata[7], edata[8], edata[9]]);
                stack.push(inner);
            }
            _ => {} // Unknown tag, skip
        }
    }
}

// ---------------------------------------------------------------------------
// Topological sort (Kahn's algorithm)
// ---------------------------------------------------------------------------

/// Result of topological sorting.
pub(crate) struct TopoResult {
    /// Constant names in dependency order (dependencies before dependents).
    pub(crate) order: Vec<String>,
    /// Constant names that could not be ordered due to dependency cycles.
    pub(crate) cyclic: Vec<String>,
}

/// Topologically sort constants using Kahn's algorithm.
///
/// Only considers dependencies that are *within* the shard. External
/// dependencies (references to constants not defined in this shard) are
/// ignored since they cannot be resolved from shard data alone.
pub(crate) fn topological_sort(deps: &HashMap<String, HashSet<String>>) -> TopoResult {
    let included: HashSet<String> = deps.keys().cloned().collect();
    topological_sort_subset(deps, &included)
}

fn topological_sort_subset(
    deps: &HashMap<String, HashSet<String>>,
    included: &HashSet<String>,
) -> TopoResult {
    let all_names: Vec<&String> = deps
        .keys()
        .filter(|name| included.contains(*name))
        .collect();

    // Compute in-degree for each constant (only counting intra-shard deps).
    let mut in_degree: HashMap<&String, usize> = HashMap::new();
    let mut adj: HashMap<&String, Vec<&String>> = HashMap::new();

    for name in &all_names {
        in_degree.entry(name).or_insert(0);
        adj.entry(name).or_default();
    }

    for (name, references) in deps {
        if !included.contains(name) {
            continue;
        }
        for dep in references {
            if included.contains(dep) {
                adj.entry(dep).or_default().push(name);
                *in_degree.entry(name).or_insert(0) += 1;
            }
        }
    }

    for dependents in adj.values_mut() {
        dependents.sort_unstable();
    }

    let mut ready: Vec<&String> = in_degree
        .iter()
        .filter_map(|(name, &degree)| (degree == 0).then_some(*name))
        .collect();
    ready.sort_unstable();
    let mut queue: VecDeque<&String> = ready.into_iter().collect();

    let mut order: Vec<String> = Vec::with_capacity(all_names.len());
    while let Some(name) = queue.pop_front() {
        order.push((*name).clone());
        if let Some(dependents) = adj.get(name) {
            for dependent in dependents {
                if let Some(deg) = in_degree.get_mut(dependent) {
                    *deg -= 1;
                    if *deg == 0 {
                        queue.push_back(dependent);
                    }
                }
            }
        }
    }

    let ordered_set: HashSet<&str> = order.iter().map(|s| s.as_str()).collect();
    let mut cyclic: Vec<String> = all_names
        .into_iter()
        .filter(|n| !ordered_set.contains(n.as_str()))
        .map(|n| (*n).clone())
        .collect();
    cyclic.sort_unstable();

    TopoResult { order, cyclic }
}

struct StronglyConnectedComponents {
    components: Vec<Vec<String>>,
    component_index: HashMap<String, usize>,
}

fn compute_strongly_connected_components(
    deps: &HashMap<String, HashSet<String>>,
) -> StronglyConnectedComponents {
    let reverse_graph = build_reverse_dependency_graph(deps);
    let mut nodes: Vec<String> = deps.keys().cloned().collect();
    nodes.sort_unstable();

    let mut visited = HashSet::new();
    let mut finish_order = Vec::with_capacity(nodes.len());
    for start in &nodes {
        if visited.contains(start) {
            continue;
        }

        let mut stack = vec![(start.clone(), false)];
        while let Some((name, expanded)) = stack.pop() {
            if expanded {
                finish_order.push(name);
                continue;
            }
            if !visited.insert(name.clone()) {
                continue;
            }

            stack.push((name.clone(), true));

            let mut dependencies: Vec<String> = deps
                .get(name.as_str())
                .into_iter()
                .flatten()
                .filter(|dep| deps.contains_key(dep.as_str()))
                .cloned()
                .collect();
            dependencies.sort_unstable();
            for dependency in dependencies.into_iter().rev() {
                if !visited.contains(dependency.as_str()) {
                    stack.push((dependency, false));
                }
            }
        }
    }

    let mut assigned = HashSet::new();
    let mut components = Vec::new();
    let mut component_index = HashMap::new();

    while let Some(start) = finish_order.pop() {
        if !assigned.insert(start.clone()) {
            continue;
        }

        let mut component = vec![start.clone()];
        let mut stack = vec![start];
        while let Some(name) = stack.pop() {
            let mut dependents: Vec<String> = reverse_graph
                .get(name.as_str())
                .into_iter()
                .flatten()
                .filter(|dependent| deps.contains_key(dependent.as_str()))
                .cloned()
                .collect();
            dependents.sort_unstable();
            for dependent in dependents.into_iter().rev() {
                if assigned.insert(dependent.clone()) {
                    component.push(dependent.clone());
                    stack.push(dependent);
                }
            }
        }

        component.sort_unstable();
        let component_idx = components.len();
        for name in &component {
            component_index.insert(name.clone(), component_idx);
        }
        components.push(component);
    }

    StronglyConnectedComponents {
        components,
        component_index,
    }
}

/// Compute a dependency-aware re-check plan for changed constants.
pub fn plan_incremental_recheck<I, S>(
    reader: &ShardReader,
    changed_names: I,
) -> IncrementalRecheckPlan
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    let dep_graph = build_dependency_graph(reader);
    let sccs = compute_strongly_connected_components(&dep_graph);
    let reverse_graph = build_reverse_dependency_graph(&dep_graph);

    let mut seen = HashSet::new();
    let mut requested = Vec::new();
    let mut missing = Vec::new();
    let mut changed_components = HashSet::new();

    for name in changed_names {
        let name = name.as_ref();
        if !seen.insert(name.to_string()) {
            continue;
        }
        if dep_graph.contains_key(name) {
            requested.push(name.to_string());
            if let Some(&component_idx) = sccs.component_index.get(name) {
                changed_components.insert(component_idx);
            }
        } else {
            missing.push(name.to_string());
        }
    }

    let mut changed_set = HashSet::new();
    for component_idx in changed_components {
        changed_set.extend(sccs.components[component_idx].iter().cloned());
    }

    let mut affected = changed_set.clone();
    let mut affected_queue: Vec<String> = changed_set.iter().cloned().collect();
    affected_queue.sort_unstable();
    let mut queue: VecDeque<String> = affected_queue.into_iter().collect();
    while let Some(name) = queue.pop_front() {
        if let Some(dependents) = reverse_graph.get(&name) {
            let mut dependents: Vec<&String> = dependents.iter().collect();
            dependents.sort_unstable();
            for dependent in dependents {
                if affected.insert(dependent.clone()) {
                    queue.push_back(dependent.clone());
                }
            }
        }
    }

    let mut prerequisites = HashSet::new();
    let mut prerequisite_roots: Vec<String> = affected.iter().cloned().collect();
    prerequisite_roots.sort_unstable();
    let mut upstream_queue: VecDeque<String> = prerequisite_roots.into_iter().collect();
    while let Some(name) = upstream_queue.pop_front() {
        if let Some(dependencies) = dep_graph.get(&name) {
            let mut dependencies: Vec<&String> = dependencies
                .iter()
                .filter(|dep| dep_graph.contains_key(dep.as_str()))
                .collect();
            dependencies.sort_unstable();
            for dependency in dependencies {
                if affected.contains(dependency) {
                    continue;
                }
                if prerequisites.insert(dependency.clone()) {
                    upstream_queue.push_back(dependency.clone());
                }
            }
        }
    }

    let recheck_topo = topological_sort_subset(&dep_graph, &affected);
    let seed_topo = topological_sort_subset(&dep_graph, &prerequisites);

    IncrementalRecheckPlan {
        requested,
        missing,
        seed_order: seed_topo.order,
        seed_cyclic: seed_topo.cyclic,
        recheck_order: recheck_topo.order,
        cycle_skipped: recheck_topo.cyclic,
    }
}

// ---------------------------------------------------------------------------
// Incremental verification
// ---------------------------------------------------------------------------

/// Result of adding a single constant.
#[derive(Debug)]
enum AddConstResult {
    /// Genuinely kernel-verified: either a value that typechecked through
    /// `add_decl(Theorem/Definition/Opaque)`, or a checked inductive-family
    /// replay through `add_inductive()`. This is the ONLY honest "Clean's kernel
    /// proof-checked this" verdict.
    KernelVerified,
    /// A `NO_VALUE` constant (`DeclKind::Axiom`/`Quot`) registered via
    /// `add_decl(Axiom)`. The kernel checked the type is well-formed, but there
    /// is no proof term to check — it is an accepted axiom, NOT a proof-check.
    AxiomAccepted,
    /// A `NO_VALUE` `DeclKind::Axiom` whose stated type was DISCHARGED to a
    /// hand-built kernel PROOF ([`axiom_discharge`]): the type was registered
    /// as a `Declaration::Theorem` and the kernel type-checked a genuine proof
    /// term against it. This IS a proof-check — counted with `KernelVerified`
    /// (and additionally recorded in `discharged_axiom_names` for audit). Only
    /// ever reached from the value-less axiom arm, so it can never mask a
    /// rejected VALUE; a builder that declines or a proof the kernel rejects
    /// falls through byte-identically to [`AddConstResult::AxiomAccepted`].
    AxiomDischarged,
    /// A value-bearing Lean `unsafe def` (`DefinitionSafety::Unsafe` in the
    /// shard header) registered TYPE-ONLY in trusted context. Lean's kernel
    /// typechecks unsafe values only in a permissive mode (self-reference
    /// allowed, `lcProof` escape hatch) and structurally bars unsafe consts
    /// from proofs (`#print axioms` never sees them), so the value can never be
    /// proof-checked by a one-shot `add_decl` and never carries proof-grade
    /// trust. NOT a proof-check, NOT a failure, and NOT a masked-failure taint
    /// seed (only other unsafe decls can reference it — upstream-kernel
    /// enforced).
    UnsafeAccepted,
    /// A value-bearing `Theorem`/`Definition`/`Opaque` that did NOT typecheck (or
    /// carried no reconstructable value) and fell back to `add_decl(Axiom)` so
    /// downstream dependents could still resolve it. This is NOT a proof-check
    /// and, when a value WAS present, MASKS a failed proof. `Some(err)` carries
    /// the value typecheck error for that masked-failure case; `None` means no
    /// value was present.
    AxiomFallback(Option<String>),
    /// A failed checked inductive-family replay downgraded to a kernel-checked
    /// STAND-IN axiom of the row's stated type (family arity / constructor
    /// type; [`try_inductive_family_standin`]). Statement-only accounting like
    /// `AxiomFallback(None)`: NOT a proof-check, NEVER KernelVerified, and NOT
    /// a masked-failure taint seed — the stand-in claims strictly less than
    /// the failed family and the weaker claim is itself kernel-checked. The
    /// string carries the superseded replay failure (also appended to the
    /// env-gated speculative capture log).
    FamilyStandin(String),
    /// A value-bearing decl whose value the kernel rejected on a PURE
    /// universe-LEVEL mismatch ([`types_eq_modulo_universe`]): a universe-
    /// collapse reconstruction gap, not a refused proof. The kernel-checked
    /// statement is registered as a clean type-only stand-in (value withheld).
    /// Statement-only accounting like `FamilyStandin` / `AxiomFallback(None)`:
    /// NEVER KernelVerified and NOT a masked-failure taint seed. Joins the
    /// stand-in set so a dependent that reduces through the withheld value
    /// classifies STANDIN_BLOCKED. The string carries the discarded universe
    /// mismatch (diagnostics only).
    UniverseReconStandin(String),
    /// A value-bearing decl whose value the kernel rejected because conversion
    /// got STUCK on a native int63 / float / string primitive
    /// ([`is_int63_primitive_stuck_rejection`]): Coq declares those operations
    /// as `Primitive` (OCaml machine ops), dumped as value-less axioms, so
    /// Clean's kernel has no reduction rule for them. A proof that appeals to
    /// their computation (`Uint63.succ_spec`, `Sint63.to_Z_*`, …) cannot be
    /// re-checked here — the primitive is genuinely OUT-OF-MODEL, exactly like a
    /// `CoFix` coinductive. The kernel-checked STATEMENT is registered as a
    /// clean type-only stand-in (value withheld). Statement-only accounting like
    /// `UniverseReconStandin` / `FamilyStandin`: NEVER KernelVerified and NOT a
    /// masked-failure taint seed. Joins the stand-in set so a dependent that
    /// reduces through the withheld value classifies STANDIN_BLOCKED. The string
    /// carries the discarded primitive-stuck mismatch (diagnostics only).
    Int63PrimitiveStandin(String),
    /// Reconstruction failed.
    ReconstructFailed(String),
    /// Kernel rejected the declaration.
    KernelRejected(String),
}

/// Is `name` a kernel-SYNTHESIZED inductive-family member already installed in
/// `env` by a checked `add_inductive` — i.e. a member the family root's replay
/// already proof-checked, that the shard carries a redundant copy of?
///
/// A registered inductive (`Foo`), its constructors (`Foo.mk`), and its
/// recursor-table entries (`Foo.rec` / `Foo.casesOn` / `Foo.recOn`) are
/// directly answerable from the kernel's checked metadata tables. The reducible
/// convenience definitions Lean and Clean BOTH synthesize from a family —
/// `Foo.noConfusion` / `Foo.noConfusionType` — are ordinary `Definition`s in
/// the env (not in the recursor table), so they are recognized by their
/// kernel-synthesized SUFFIX together with the requirement that their parent
/// `Foo` is a registered inductive. The parent gate is what keeps a genuine
/// user definition that merely happens to be named `<X>.noConfusion` (with `X`
/// NOT an inductive) out of this path: it falls through to the normal
/// `add_decl` replay and is proof-checked on its own value.
fn is_synthesized_inductive_family_member(env: &Environment, name: &Name) -> bool {
    if env.get_inductive(name).is_some()
        || env.get_constructor(name).is_some()
        || env.get_recursor(name).is_some()
    {
        return true;
    }
    // `Foo.noConfusion` / `Foo.noConfusionType`: reducible defs `add_inductive`
    // generates for a non-Prop family. Require the constant to actually exist
    // AND its immediate parent to be a registered inductive.
    let is_no_confusion_suffix = matches!(
        name.last_component().as_deref(),
        Some("noConfusion") | Some("noConfusionType")
    );
    if !is_no_confusion_suffix || env.get_const(name).is_none() {
        return false;
    }
    match name.inner() {
        clean_kernel::name::NameInner::Str(parent, _) => {
            let parent: &Name = parent;
            env.get_inductive(parent).is_some()
        }
        _ => false,
    }
}

/// Accept a shard constant whose name is ALREADY present in `env` as a checked,
/// kernel-synthesized inductive-family member (installed by an earlier
/// `add_inductive` replay of the family root).
///
/// The shard ships its own copy of every family member — including the
/// constructor (`Foo.mk`), the recursor-table entries (`Foo.rec` / `.casesOn` /
/// `.recOn`, which Lean stores as `Definition`/`Recursor` and Clean installs in
/// its recursor table), and the reducible `Foo.noConfusion(Type)` defs. Re-adding
/// any of these through `add_decl` collides with the kernel-synthesized member
/// and fails `Duplicate declaration`; comparing their types with a raw structural
/// `==` falsely rejects members whose only difference is Lean-vs-Clean binder
/// annotations (the same binder-info convention gap WS13 closed for the
/// family-match guard). This function recognizes the redundant copy instead.
///
/// SOUNDNESS: nothing from the shard is installed here — the accepted member is
/// the one the kernel ALREADY built and proof-checked during the checked
/// `add_inductive` replay of the family root (positivity, universes, recursor
/// generation all enforced there). Acceptance still requires the shard copy's
/// level params to match EXACTLY and its type to match up to binder
/// *annotations* only (`types_equal_ignoring_binder_info`; the kernel's
/// `is_def_eq` ignores binder info — see that helper's note). A copy with a
/// genuinely different type, different level params, or a name that is NOT a
/// kernel-synthesized member still fails closed.
fn try_accept_existing_inductive_family_constant(
    env: &Environment,
    reconstructed: &ReconstructedConstant,
) -> Option<AddConstResult> {
    // Two ways a shard constant can be a redundant copy of a checked member:
    //   1. The shard tags it as an inductive-family decl kind
    //      (`Inductive`/`Constructor`/`Recursor`). It MUST then back checked
    //      metadata in the env, or the name collides with something else.
    //   2. The shard tags it as a value-bearing decl (`Definition`/`Theorem`/
    //      `Opaque`) — Lean's spelling of `casesOn`/`recOn`/`noConfusion(Type)`
    //      — but the env already holds the kernel-synthesized member.
    let is_family_decl_kind = matches!(
        reconstructed.decl_kind,
        DeclKind::Inductive | DeclKind::Constructor | DeclKind::Recursor
    );

    let existing = env.get_const(&reconstructed.decl_name)?;

    if is_family_decl_kind {
        let has_checked_metadata = match reconstructed.decl_kind {
            DeclKind::Inductive => env.get_inductive(&reconstructed.decl_name).is_some(),
            DeclKind::Constructor => env.get_constructor(&reconstructed.decl_name).is_some(),
            DeclKind::Recursor => env.get_recursor(&reconstructed.decl_name).is_some(),
            _ => false,
        };
        if !has_checked_metadata {
            return Some(AddConstResult::KernelRejected(format!(
                "existing constant {} is not checked inductive-family metadata",
                reconstructed.decl_name
            )));
        }
    } else if !is_synthesized_inductive_family_member(env, &reconstructed.decl_name) {
        // A value-bearing shard constant whose name is NOT a kernel-synthesized
        // family member: not our case. Hand it back to the normal `add_decl`
        // replay so its value is proof-checked (and a genuine duplicate of an
        // unrelated constant still fails closed there).
        return None;
    }

    // Level params are positional binders: olean call sites instantiate them
    // by POSITION, never by name, so `Eq.{u}` (seeded) and `Eq.{u_1}` (genuine
    // olean spelling) denote the same declaration. Compare alpha-insensitively:
    // same arity, and the shard's type matches after renaming its params to
    // the existing member's names. Different ARITY still fails closed.
    match alpha_type_match_against_existing(
        env,
        existing,
        &reconstructed.level_params,
        &reconstructed.type_expr,
    ) {
        AlphaTypeMatch::ArityMismatch => Some(AddConstResult::KernelRejected(format!(
            "existing checked inductive-family constant {} has different level params",
            reconstructed.decl_name
        ))),
        AlphaTypeMatch::TypeMismatch => Some(AddConstResult::KernelRejected(format!(
            "existing checked inductive-family constant {} has different type",
            reconstructed.decl_name
        ))),
        AlphaTypeMatch::Match => Some(AddConstResult::KernelVerified),
    }
}

/// Outcome of the alpha-insensitive type comparison against an existing env
/// constant ([`alpha_type_match_against_existing`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AlphaTypeMatch {
    /// Same level-param arity and the types match (structurally modulo binder
    /// annotations, or by the kernel's `is_def_eq`).
    Match,
    /// Different level-param arity — a genuine mismatch, never relaxed.
    ArityMismatch,
    /// Same arity but the types differ even under `is_def_eq`.
    TypeMismatch,
}

/// Positionally rename the level params of `expr` from `from` to `to`.
///
/// Level params are positional binders (call sites instantiate by position,
/// never by name), so this rewrite changes spelling only, never meaning.
/// Callers guarantee `from.len() == to.len()`.
fn rename_level_params_positional(expr: &Expr, from: &[Name], to: &[Name]) -> Expr {
    if from == to {
        return expr.clone();
    }
    let renaming: Vec<Level> = to.iter().map(|n| Level::param(n.clone())).collect();
    expr.instantiate_level_params_direct(from, &renaming)
}

/// Compare `type_expr` (parameterized by `level_params`) against `existing`'s
/// stored type, alpha-insensitively on level params: same arity, then equality
/// after positionally renaming the incoming params to the existing names.
///
/// `types_equal_ignoring_binder_info` is tried first — a CONSERVATIVE
/// structural check that canonicalizes binder annotations but does NOT reduce.
/// Two spellings of the same declaration may differ *definitionally* rather
/// than structurally (e.g. a `Sort (max u 0)` vs `Sort u` universe form, a
/// reducible-def unfolding, or an eta difference in a generated
/// `noConfusionType`), so the kernel's full `is_def_eq` is the fallback before
/// declaring a mismatch. `is_def_eq` is exactly the kernel's own equality; a
/// genuinely different type still fails closed.
///
/// Shared by the inductive-family member dedup
/// ([`try_accept_existing_inductive_family_constant`]), the seeded-twin
/// dedup ([`try_accept_seeded_duplicate`]), and the checked family-replay
/// recursor gate ([`crate::inductive_replay::checked_inductive_replay_matches_shard`])
/// so the disciplines cannot drift.
pub(crate) fn alpha_type_match_against_existing(
    env: &Environment,
    existing: &ConstantInfo,
    level_params: &[Name],
    type_expr: &Expr,
) -> AlphaTypeMatch {
    if existing.level_params.len() != level_params.len() {
        return AlphaTypeMatch::ArityMismatch;
    }
    let renamed = rename_level_params_positional(type_expr, level_params, &existing.level_params);
    if types_equal_ignoring_binder_info(&existing.type_, &renamed) {
        return AlphaTypeMatch::Match;
    }
    let tc = TypeChecker::new(env);
    if tc.is_def_eq(&existing.type_, &renamed) {
        AlphaTypeMatch::Match
    } else {
        AlphaTypeMatch::TypeMismatch
    }
}

/// Outcome of the checked inductive-family replay
/// ([`try_add_inductive_family_checked`]).
///
/// Structured (rather than a bare bool) so a failure's STAGE and real error
/// survive into the rejection message — and thus the `CLEAN_WS13_FAILDUMP`
/// line — instead of being collapsed into the generic skeleton-confidence
/// rejection (A2-2 diagnostics; the WS16 eprintln hooks already had this
/// information, but it never reached the report). Diagnostics only: every
/// failure variant is rejected through the SAME
/// [`reject_inductive_family_skeleton_with_failure`] trust decision as before.
#[derive(Debug)]
enum FamilyReplayOutcome {
    /// The family replayed through checked `add_inductive` and is installed.
    Replayed,
    /// Replay failed; the caller rejects the skeleton fail-closed, carrying
    /// the failure stage in the rejection message.
    Failed(FamilyReplayFailure),
}

/// Which stage of the checked inductive-family replay failed, with the real
/// error where one exists.
#[derive(Debug)]
enum FamilyReplayFailure {
    /// `build_inductive_replay_metadata` could not rebuild a checked
    /// `InductiveDecl` from shard metadata (returned `None`). Set
    /// `CLEAN_WS16_DEBUG` for the exact reconstruction step.
    MetadataUnavailable,
    /// The kernel's scratch `add_inductive` replay rejected the reconstructed
    /// declaration (positivity / universe / type error); carries the kernel
    /// error display.
    ScratchRejected(String),
    /// The regenerated family did not byte-match the shard's stored members;
    /// `member` is the first mismatching constant.
    ShardMismatch { member: String, detail: String },
}

impl FamilyReplayFailure {
    /// One-line "stage + real error" description appended to the skeleton
    /// rejection message (and thus the faildump line). Long kernel errors /
    /// type dumps are truncated to keep the line readable.
    fn describe(&self) -> String {
        match self {
            Self::MetadataUnavailable => "family replay failed at metadata reconstruction: \
                 build_inductive_replay_metadata returned None \
                 (set CLEAN_WS16_DEBUG for the exact step)"
                .to_string(),
            Self::ScratchRejected(err) => format!(
                "family replay failed at scratch add_inductive: {}",
                truncate_diagnostic(err)
            ),
            Self::ShardMismatch { member, detail } => format!(
                "family replay failed at checked-replay shard match: member {member}: {}",
                truncate_diagnostic(detail)
            ),
        }
    }
}

/// Character budget for a single embedded diagnostic fragment (kernel error /
/// type dump) inside a rejection message.
const MAX_DIAGNOSTIC_CHARS: usize = 500;

/// Truncate a diagnostic fragment to [`MAX_DIAGNOSTIC_CHARS`] characters.
fn truncate_diagnostic(msg: &str) -> Cow<'_, str> {
    match msg.char_indices().nth(MAX_DIAGNOSTIC_CHARS) {
        Some((byte_idx, _)) => Cow::Owned(format!("{}... [truncated]", &msg[..byte_idx])),
        None => Cow::Borrowed(msg),
    }
}

fn try_add_inductive_family_checked(
    env: &mut Environment,
    reader: &ShardReader,
    constant: &MathverseConstantHeader,
    reconstructed: &ReconstructedConstant,
    policy: InductiveReplayPolicy,
) -> Result<FamilyReplayOutcome, String> {
    let ws16_dbg = |msg: &str| {
        if let Ok(filter) = std::env::var("CLEAN_WS16_DEBUG") {
            let name = reconstructed.decl_name.to_string();
            if filter.trim().is_empty() || filter.split(',').any(|w| w.trim() == name.as_str()) {
                eprintln!("WS16 try_add_inductive_family_checked[{name}]: {msg}");
            }
        }
    };
    // Try each normalization mode in order, committing the first that the
    // kernel accepts and the shard byte-matches:
    //   Shallow — unfold the synonym CONCLUSION head only, keep binder domains
    //             (families with synonym-typed PARAMETERS, e.g. Union/Im).
    //   Deep    — fully delta-unfold synonyms (families whose PREMISES reference
    //             a synonym not yet in scope, e.g. Power_set's `Included`).
    //   Off     — the pre-normalization BASELINE, byte-identical to the original
    //             behavior — the fail-closed final attempt, so a family that
    //             benefits from no mode replays EXACTLY as before and can NEVER
    //             regress. This makes the whole lever add-only.
    let mut last_failure = None;
    let mut winner = None;
    for mode in [NormMode::Shallow, NormMode::Deep, NormMode::Off] {
        match run_family_replay_attempt(env, reader, constant, reconstructed, policy, mode)? {
            Ok(decl) => {
                ws16_dbg(&format!("REPLAY OK ({mode:?})"));
                winner = Some(decl);
                break;
            }
            Err(failure) => {
                ws16_dbg(&format!("{mode:?} attempt failed ({})", failure.describe()));
                last_failure = Some(failure);
            }
        }
    }
    let Some(decl) = winner else {
        return Ok(FamilyReplayOutcome::Failed(
            last_failure.unwrap_or(FamilyReplayFailure::MetadataUnavailable),
        ));
    };

    policy.add_family(env, decl).map_err(|err| {
        format!(
            "checked inductive replay rejected {}: {err}",
            reconstructed.decl_name
        )
    })?;
    Ok(FamilyReplayOutcome::Replayed)
}

/// One checked family-replay attempt against a FRESH scratch clone of `env`:
/// build the family metadata under `mode`, replay it through checked
/// `add_inductive`, and byte-match the regenerated members against the shard.
/// Returns the validated [`InductiveDecl`] to commit on success, or the stage at
/// which it failed. Never mutates `env` (the caller commits the winner).
fn run_family_replay_attempt(
    env: &Environment,
    reader: &ShardReader,
    constant: &MathverseConstantHeader,
    reconstructed: &ReconstructedConstant,
    policy: InductiveReplayPolicy,
    mode: NormMode,
) -> Result<Result<clean_kernel::inductive::InductiveDecl, FamilyReplayFailure>, String> {
    let Some(metadata) = build_inductive_replay_metadata(reader, constant, reconstructed, mode)?
    else {
        return Ok(Err(FamilyReplayFailure::MetadataUnavailable));
    };
    let mut scratch = env.clone();
    if let Err(e) = policy.add_family(&mut scratch, metadata.decl.clone()) {
        return Ok(Err(FamilyReplayFailure::ScratchRejected(e.to_string())));
    }
    if let ShardFamilyMatch::Mismatch { member, detail } =
        checked_inductive_replay_matches_shard(&scratch, reader, &metadata, mode)?
    {
        return Ok(Err(FamilyReplayFailure::ShardMismatch { member, detail }));
    }
    Ok(Ok(metadata.decl))
}

#[cfg(test)]
fn build_single_type_inductive_replay_metadata(
    reader: &ShardReader,
    constant: &MathverseConstantHeader,
    reconstructed: &ReconstructedConstant,
) -> Result<Option<InductiveReplayMetadata>, String> {
    let metadata =
        build_inductive_replay_metadata(reader, constant, reconstructed, NormMode::Shallow)?;
    if metadata
        .as_ref()
        .is_some_and(|metadata| metadata.decl.types.len() != 1)
    {
        return Ok(None);
    }
    Ok(metadata)
}

/// Outcome of the shared reconstruct + replay step.
enum ReplayOutcome {
    /// The constant was reconstructed and the replay decision is final.
    Done(AddConstResult),
    /// A fresh inductive-family constant that needs sibling-scanning replay
    /// (`add_inductive`) which the shared helper deliberately does not perform,
    /// because it requires the full set of sibling constants. The caller owns
    /// that scan (per-shard from a [`ShardReader`], corpus-wide from the merged
    /// constant table). The reconstructed declaration is returned so the caller
    /// does not redo the work.
    NeedsInductiveFamilyReplay(Box<ReconstructedConstant>),
}

/// Shared reconstruct + kernel-replay for a single constant, parameterized only
/// by raw flat slices and the constant header.
///
/// This is the single code path that BOTH the per-shard verifier and the global
/// corpus verifier funnel every constant through, so their reconstruction and
/// kernel-acceptance semantics stay identical. It handles everything that does
/// not require examining sibling constants: reconstruction, accepting an
/// already-present checked inductive-family member, the non-inductive
/// `add_decl` replays (theorem / definition / opaque / axiom / quot), and the
/// fail-closed path for inductive-family skeletons. The one case it cannot
/// decide alone — building a fresh `InductiveDecl` from its constructors — is
/// surfaced as [`ReplayOutcome::NeedsInductiveFamilyReplay`] for the caller.
fn reconstruct_and_replay_one(
    env: &mut Environment,
    name: &str,
    slices: ShardSlices<'_>,
    constant: &MathverseConstantHeader,
    force_type_only: bool,
) -> ReplayOutcome {
    let reconstructed = match reconstruct_constant_from_slices(name, slices, constant) {
        Ok(reconstructed) => reconstructed,
        Err(msg) => return ReplayOutcome::Done(AddConstResult::ReconstructFailed(msg)),
    };

    if let Some(result) = try_accept_existing_inductive_family_constant(env, &reconstructed) {
        return ReplayOutcome::Done(result);
    }

    if reconstructed.decl_kind == DeclKind::Inductive {
        // Constructing a checked `InductiveDecl` needs the constructor/recursor
        // siblings, which only the caller can supply. Defer to it.
        return ReplayOutcome::NeedsInductiveFamilyReplay(Box::new(reconstructed));
    }

    // Lean `unsafe def` lane (2026-07-06 census Class 3): a value-bearing
    // `Definition` stamped `DefinitionSafety::Unsafe` is recursive with NO
    // termination proof — Lean's own kernel typechecks its value only in a
    // permissive mode (self-reference allowed, `lcProof` escape hatch) and
    // structurally bars unsafe consts from proofs, so it can NEVER carry
    // proof-grade trust (`#print axioms` never sees it). Replaying it as a safe
    // Definition through one-shot `add_decl` is guaranteed to fail on the
    // self-reference (`Unknown constant: <self>`) and previously minted a
    // masked-failure axiom fallback WITH a taint seed. Register it TYPE-ONLY
    // instead — byte-identical to what that fallback installed (the kernel
    // still checks the type) — classified `UnsafeAccepted`: trusted context,
    // never KernelVerified, not a failure, no taint (a Lean-produced olean
    // cannot contain a safe decl referencing an unsafe one; upstream-kernel
    // enforced). `partial` defs stay on the ordinary safe path: their kernel
    // values are inhabitant placeholders with no self-reference and already
    // pass. Value-LESS unsafe decls also stay on the existing path (the
    // `AxiomFallback(None)` lane).
    if reconstructed.decl_kind == DeclKind::Definition
        && reconstructed.value_expr.is_some()
        && constant.definition_safety() == Some(clean_olean::DefinitionSafety::Unsafe)
    {
        return ReplayOutcome::Done(accept_unsafe_definition_type_only(env, reconstructed));
    }

    let result = match reconstructed.decl_kind {
        // A constructor row reaching this arm means its parent family never
        // installed checked metadata (a replayed parent would have satisfied
        // `try_accept_existing_inductive_family_constant` above). Try the
        // constructor-TYPE stand-in — kernel-checked against the parent's
        // arity stand-in axiom, if one was installed — before failing closed
        // (see `try_inductive_family_standin`).
        DeclKind::Constructor => try_inductive_family_standin(
            env,
            constant,
            &reconstructed,
            "constructor row without checked family metadata \
             (parent family replay failed)",
        )
        .unwrap_or_else(|| reject_inductive_family_skeleton(constant)),
        // Inductive/Recursor rows without a reconstructable inductive parent
        // fail closed: `add_inductive()` is the only path that installs
        // checked inductive-family metadata from shards, and a recursor TYPE
        // asserts an elimination principle no stand-in may posit.
        DeclKind::Inductive | DeclKind::Recursor => reject_inductive_family_skeleton(constant),
        // Theorems and definitions with a value: try add_decl with type checking.
        DeclKind::Theorem | DeclKind::Definition | DeclKind::Opaque => try_add_decl(
            env,
            reconstructed.decl_name,
            reconstructed.decl_kind,
            reconstructed.level_params,
            reconstructed.type_expr,
            // A SPECULATIVE value whose dependency closure already rests on a
            // masked-failure taint is withheld ENTIRELY (`value = None`): the
            // stated type is registered as a clean axiom, byte-identical to the
            // value-less baseline, so the optimistic value never becomes a
            // taint-eligible KernelVerified nor extends the taint graph.
            if force_type_only {
                None
            } else {
                reconstructed.value_expr.as_ref()
            },
            // A value translated with a DERIVED recursor motive universe (a
            // best-effort guess, `AxiomProfile::SPECULATIVE_MOTIVE`) fails
            // closed: a kernel rejection reverts to a clean type-only axiom
            // instead of a masked-failure taint (byte-identical in effect to
            // the pre-derivation baseline where the value never translated).
            constant
                .profile()
                .has_bit(crate::types::AxiomProfile::SPECULATIVE_MOTIVE.0),
        ),
        // Axioms and quotient types: no value, register as axiom. The kernel
        // only checks the type is well-formed — there is no proof term to
        // check — so this is an accepted axiom, NOT a kernel proof-check.
        DeclKind::Axiom | DeclKind::Quot => {
            if env.get_const(&reconstructed.decl_name).is_some() {
                // A constant with this NAME is already installed — the
                // foundational seeds (`Quot`/`Quot.mk`/`Quot.lift`/`Quot.ind`,
                // `Quot.sound`, `propext`, `Classical.choice`, `sorryAx`).
                // Decide the duplicate honestly instead of dying on
                // `add_decl`'s blanket "Duplicate declaration" (the axiom-kind
                // counterpart of `try_add_decl`'s seeded-dup pre-check).
                try_accept_seeded_axiom_twin(
                    env,
                    &reconstructed.decl_name,
                    &reconstructed.level_params,
                    &reconstructed.type_expr,
                )
            } else {
                // AXIOM-DISCHARGE (BRICK 1.0): before positing a fresh axiom,
                // try to replace it with a hand-built kernel PROOF of its
                // stated type. On success the constant is a genuine
                // kernel-checked `Theorem` (`AxiomDischarged` → KernelVerified).
                // On `NotAttempted`/`ProofRejected` `env` is untouched and we
                // fall through BYTE-IDENTICALLY to the axiom lane below — the
                // discharge runs only in this value-less arm, so it can never
                // mask a rejected value (regressed-0 by construction).
                let direct_discharge = axiom_discharge::attempt_axiom_discharge(
                    env,
                    &reconstructed.decl_name,
                    &reconstructed.level_params,
                    &reconstructed.type_expr,
                );
                if let axiom_discharge::DischargeAttempt::ProofRejected(reason) = &direct_discharge
                {
                    eprintln!(
                        "warning: direct axiom-discharge proof for `{}` was kernel-rejected: \
                         {reason}; trying the lock-pattern fallback",
                        reconstructed.decl_name
                    );
                }
                match direct_discharge {
                    axiom_discharge::DischargeAttempt::Discharged => {
                        AddConstResult::AxiomDischarged
                    }
                    axiom_discharge::DischargeAttempt::NotAttempted
                    | axiom_discharge::DischargeAttempt::ProofRejected(_) => {
                        // AXIOM-DISCHARGE (BRICK 1.1): the GENERIC lock-pattern
                        // rule. When this value-less axiom is a lock equation
                        // `f_def : f = rhs` for a value-free axiom `f` already in
                        // the env, UNSEAL `f` (upgrade its stub to the checked
                        // definition `f := rhs`) and discharge the equation as
                        // `eq_refl`. Making `f` value-bearing unblocks every
                        // constant the seal was stalling; they follow the
                        // equation in topological order (its only handle on `f`).
                        // `NotAttempted`/`ProofRejected` leaves `env` untouched
                        // and falls through BYTE-IDENTICALLY to the axiom lane —
                        // regressed-0 by construction (value-less arm only).
                        let lock_discharge = axiom_discharge::attempt_lock_pattern_discharge(
                            env,
                            &reconstructed.decl_name,
                            &reconstructed.level_params,
                            &reconstructed.type_expr,
                        );
                        if let axiom_discharge::DischargeAttempt::ProofRejected(reason) =
                            &lock_discharge
                        {
                            eprintln!(
                                "warning: lock-pattern axiom-discharge proof for `{}` was \
                                 kernel-rejected: {reason}; retaining the declaration as an axiom",
                                reconstructed.decl_name
                            );
                        }
                        match lock_discharge {
                            axiom_discharge::DischargeAttempt::Discharged => {
                                AddConstResult::AxiomDischarged
                            }
                            axiom_discharge::DischargeAttempt::NotAttempted
                            | axiom_discharge::DischargeAttempt::ProofRejected(_) => {
                                let axiom = Declaration::Axiom {
                                    name: reconstructed.decl_name,
                                    level_params: reconstructed.level_params,
                                    type_: reconstructed.type_expr,
                                };
                                match env.add_decl(axiom) {
                                    Ok(()) => AddConstResult::AxiomAccepted,
                                    Err(err) => AddConstResult::KernelRejected(err.to_string()),
                                }
                            }
                        }
                    }
                }
            }
        }
    };
    ReplayOutcome::Done(result)
}

/// Try to add a single constant to the environment (per-shard path).
///
/// Funnels through the shared [`reconstruct_and_replay_one`]; for a fresh
/// inductive family it performs the sibling-scanning checked replay against the
/// shard `reader`.
fn try_add_constant(
    env: &mut Environment,
    name: &str,
    reader: &ShardReader,
    constant: &MathverseConstantHeader,
    policy: InductiveReplayPolicy,
    force_type_only: bool,
) -> AddConstResult {
    match reconstruct_and_replay_one(
        env,
        name,
        ShardSlices::from_reader(reader),
        constant,
        force_type_only,
    ) {
        ReplayOutcome::Done(result) => result,
        ReplayOutcome::NeedsInductiveFamilyReplay(reconstructed) => {
            match try_add_inductive_family_checked(env, reader, constant, &reconstructed, policy) {
                Ok(FamilyReplayOutcome::Replayed) => AddConstResult::KernelVerified,
                Ok(FamilyReplayOutcome::Failed(failure)) => {
                    // The checked replay could not install the family: fall
                    // back to a kernel-checked ARITY stand-in axiom so the
                    // family NAME resolves downstream (see
                    // `try_inductive_family_standin`); keep the original
                    // fail-closed rejection when the stand-in itself fails.
                    try_inductive_family_standin(env, constant, &reconstructed, &failure.describe())
                        .unwrap_or_else(|| {
                            reject_inductive_family_skeleton_with_failure(constant, Some(&failure))
                        })
                }
                Err(msg) => AddConstResult::KernelRejected(msg),
            }
        }
    }
}

fn reject_inductive_family_skeleton(constant: &MathverseConstantHeader) -> AddConstResult {
    reject_inductive_family_skeleton_with_failure(constant, None)
}

/// Stand-in fallback for an inductive family the checked replay could not
/// install: posit the row's STATED TYPE as an opaque axiom — the kernel
/// re-checks the statement's well-formedness right here — so downstream
/// references to the family name resolve instead of chaining "Unknown
/// constant" failures. Applied to the family root (its arity, e.g.
/// `matrix : forall R m n, Type`) and to constructor rows whose parent
/// family never installed (their stated constructor types).
///
/// Measured motivation (phant-records lever): the mathcomp phant-record
/// families dump fine but their kernel family replay fails on conversion
/// through value-less Hierarchy-Builder stand-ins, and the ABSENT name then
/// chains thousands of dependent rejections (`matrix.matrix.0` alone chained
/// 1,362; `classfun.0` 671, `mx_representation.0` 602, `RMorphism.map.0`
/// 471 — 2026-07 reject-log census).
///
/// TRUST: the stand-in is counted with the CLEAN value-less fallbacks
/// (`AddConstResult::FamilyStandin`, an `axiom_fallback` row) — the same
/// statement-only accounting as the dump-side crash-salvage `CoqAxiom`
/// stand-ins — and is NEVER itself KernelVerified. No masked-failure taint is
/// seeded: unlike a rejected VALUE (a proof claim the kernel refused), the
/// stand-in claims strictly less than the failed family — no constructors'
/// semantics, no recursor, no iota — and the weaker claim is itself
/// kernel-checked here. Every posited type concludes in an opaque constant,
/// so the axiom set stays jointly satisfiable (interpret each opaque family
/// as a constant singleton). A dependent needing the family's STRUCTURE
/// (match/fix/projection reduction) still fails closed against the opaque
/// constant; a dependent that only references the TYPE can now be genuinely
/// kernel-checked. Recursor rows are deliberately NOT eligible: a recursor
/// type asserts an elimination principle — real logical strength the family
/// never proved.
///
/// Fail-closed set: skeleton trust metadata invalid, name already present, or
/// the stated type itself fails the kernel's check → `None` (the caller keeps
/// the original rejection). Diagnostics: the superseded replay failure is
/// recorded on the report's `family_standins` lane and appended to the
/// env-gated speculative capture log (observation only).
fn try_inductive_family_standin(
    env: &mut Environment,
    constant: &MathverseConstantHeader,
    reconstructed: &ReconstructedConstant,
    superseded_failure: &str,
) -> Option<AddConstResult> {
    if validate_inductive_skeleton_trust(constant).is_err() {
        return None;
    }
    if env.get_const(&reconstructed.decl_name).is_some() {
        return None;
    }
    let axiom = Declaration::Axiom {
        name: reconstructed.decl_name.clone(),
        level_params: reconstructed.level_params.clone(),
        type_: reconstructed.type_expr.clone(),
    };
    match env.add_decl(axiom) {
        Ok(()) => {
            log_speculative_capture(
                &reconstructed.decl_name.to_string(),
                REJECT_TAG_FAMILY_STANDIN,
                superseded_failure,
            );
            Some(AddConstResult::FamilyStandin(
                superseded_failure.to_string(),
            ))
        }
        Err(_) => None,
    }
}

/// Fail-closed skeleton rejection, optionally enriched with the family
/// replay's real failure stage (A2-2 diagnostics).
///
/// TRUST DECISION UNCHANGED: both branches reject with
/// [`AddConstResult::KernelRejected`] under exactly the same conditions as
/// before — `failure` only appends "which replay stage actually failed, and
/// why" to the message text, so faildumps stop attributing every family
/// failure to the generic confidence guard.
fn reject_inductive_family_skeleton_with_failure(
    constant: &MathverseConstantHeader,
    failure: Option<&FamilyReplayFailure>,
) -> AddConstResult {
    let stage = failure
        .map(|failure| format!("; {}", failure.describe()))
        .unwrap_or_default();
    if let Err(msg) = validate_inductive_skeleton_trust(constant) {
        return AddConstResult::KernelRejected(format!("{msg}{stage}"));
    }

    let remaining = remaining_inductive_replay_metadata_fields().join(", ");
    AddConstResult::KernelRejected(format!(
        "inductive-family skeleton requires checked add_inductive replay; missing or incompatible metadata remains: {remaining}{stage}"
    ))
}

fn validate_inductive_skeleton_trust(constant: &MathverseConstantHeader) -> Result<(), String> {
    let confidence = constant
        .confidence()
        .map_err(|raw| format!("invalid import_confidence {raw}"))?;
    if confidence != ImportConfidence::KernelVerified {
        return Err(format!(
            "inductive-family skeleton requires KernelVerified confidence, got {confidence:?}"
        ));
    }
    if !constant.axiom_profile.is_kernel_verified() {
        return Err(format!(
            "inductive-family skeleton requires axiom-free metadata, got axiom_profile=0x{:x}",
            constant.axiom_profile.0
        ));
    }
    Ok(())
}

fn remaining_inductive_replay_metadata_fields() -> &'static [&'static str] {
    &["RecursorVal rules/arg_order for imported recursor skeleton reconciliation"]
}

// ---------------------------------------------------------------------------
// Env-gated speculative-rejection capture (observation only)
// ---------------------------------------------------------------------------

/// Env var naming an append-mode TSV file that captures the two SILENT
/// fail-closed lanes of the speculative-value discipline:
///
/// - a SPECULATIVE value the kernel REJECTED (the error is discarded by design
///   and the constant reverts to a clean type-only axiom), and
/// - a SPECULATIVE value WITHHELD before the kernel ever saw it because its
///   dependency closure rests on a masked-failure taint (forced type-only).
///
/// Unset (the default): nothing is captured and no file is touched. Set: one
/// `name<TAB>tag<TAB>detail` line is appended per event. OBSERVATION ONLY —
/// the verify verdicts are byte-identical either way; write failures are
/// deliberately ignored so a bad path can never alter a trust decision.
const SPECULATIVE_REJECT_LOG_ENV: &str = "CLEAN_SPECULATIVE_REJECT_LOG";

/// Tag for a speculative value the kernel actively rejected.
const REJECT_TAG_SPECULATIVE: &str = "SPECULATIVE_REJECT";
/// Tag for a speculative value withheld (forced type-only, rests-on-taint).
const REJECT_TAG_FORCED_TYPE_ONLY: &str = "FORCED_TYPE_ONLY";
/// Tag for a failed inductive-family replay downgraded to a kernel-checked
/// arity/constructor-type stand-in axiom ([`try_inductive_family_standin`]);
/// the detail carries the replay failure the stand-in supersedes.
const REJECT_TAG_FAMILY_STANDIN: &str = "FAMILY_ARITY_STANDIN";
/// Tag for a value rejection reclassified as a universe-COLLAPSE reconstruction
/// gap ([`types_eq_modulo_universe`]): the value's inferred type equals the
/// declared type modulo universe levels, so it is withheld to a clean type-only
/// stand-in (no masked-failure taint). The detail carries the discarded
/// universe mismatch.
const REJECT_TAG_UNIVERSE_STANDIN: &str = "UNIVERSE_RECON_STANDIN";
/// Tag for a value rejection reclassified as a native int63/float/string
/// PRIMITIVE-stuck reconstruction gap ([`is_int63_primitive_stuck_rejection`]):
/// conversion could not reduce a value-less native-primitive `Const`, so the
/// value is withheld to a clean type-only stand-in (no masked-failure taint).
/// The detail carries the discarded primitive-stuck mismatch.
const REJECT_TAG_INT63_STANDIN: &str = "INT63_PRIMITIVE_STANDIN";
/// Tag for a value rejection classified STAND-IN-BLOCKED (the constant's
/// dependency set includes a value-less stand-in, so the rejection is a
/// reconstruction gap, not a refused proof — clean type-only fallback, no
/// taint seed; see `IncrementalVerifyReport::standin_blocked_fallbacks`).
/// The detail carries the kernel's discarded rejection reason.
const REJECT_TAG_STANDIN_BLOCKED: &str = "STANDIN_BLOCKED";
/// Tag for an ordinary masked-failure SEED (a value rejection that keeps full
/// taint semantics; the same `(name, error)` also lands in
/// `IncrementalVerifyReport::axiom_fallback_names`). The detail carries the
/// head of the kernel rejection so root causes can be tabulated from the TSV
/// alone.
const REJECT_TAG_MASKED_SEED: &str = "MASKED_SEED";
/// Companion tag to [`REJECT_TAG_MASKED_SEED`]: one extra line per seed with
/// the dependency-shape evidence — which DIRECT deps are masked-tainted /
/// stand-ins, and which stand-ins are reachable TRANSITIVELY through the
/// dependency graph. This census line is what measured the direct-deps-only
/// classifier's transitive gap (2026-07-12); post-fix it audits the residual:
/// a remaining seed with non-empty transitive witnesses is one the taint
/// precedence guard (correctly) kept masked.
const REJECT_TAG_MASKED_SEED_DEPS: &str = "MASKED_SEED_DEPS";

/// Detail truncation bound: kernel errors embed whole expressions and can run
/// to megabytes; the taxonomy only needs the head.
const REJECT_DETAIL_MAX_CHARS: usize = 300;

/// The capture file path, when capture is enabled.
fn speculative_reject_log_path() -> Option<String> {
    match std::env::var(SPECULATIVE_REJECT_LOG_ENV) {
        Ok(path) if !path.is_empty() => Some(path),
        _ => None,
    }
}

/// Append one `name<TAB>tag<TAB>detail` line to the capture file, if enabled.
///
/// `detail` is flattened to a single line (tabs/newlines become spaces) and
/// truncated to [`REJECT_DETAIL_MAX_CHARS`] chars so the file stays a valid
/// one-record-per-line TSV. Never fails: I/O errors are swallowed on purpose
/// (see [`SPECULATIVE_REJECT_LOG_ENV`] — observation must not perturb replay).
fn log_speculative_capture(name: &str, tag: &str, detail: &str) {
    let Some(path) = speculative_reject_log_path() else {
        return;
    };
    let mut flat: String = detail
        .chars()
        .take(REJECT_DETAIL_MAX_CHARS)
        .map(|c| if c.is_control() { ' ' } else { c })
        .collect();
    if detail.chars().nth(REJECT_DETAIL_MAX_CHARS).is_some() {
        flat.push_str("...");
    }
    use std::io::Write as _;
    if let Ok(mut file) = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(&path)
    {
        let _ = writeln!(file, "{name}\t{tag}\t{flat}");
    }
}

/// The stand-in evidence a value rejection carries (see
/// [`standin_blocked_evidence`]): the opaque wall sits among the DIRECT
/// dependencies, or is reached TRANSITIVELY through the dependency closure
/// (the kernel's conversion δ-unfolds the values of intermediate — even
/// kernel-verified — constants and hits the value-less stand-in arbitrarily
/// deep).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum StandinWall {
    Direct,
    Transitive,
}

impl StandinWall {
    fn as_str(self) -> &'static str {
        match self {
            Self::Direct => "direct",
            Self::Transitive => "transitive",
        }
    }
}

/// Decide whether a VALUE rejection (an `AxiomFallback(Some(_))`) is
/// STAND-IN-BLOCKED: the constant's dependency cone (type + value references,
/// the same graph the taint pre-check reads) includes a VALUE-LESS STAND-IN
/// present in the environment — either among the DIRECT dependencies or
/// reachable TRANSITIVELY (`standin_reachable`, propagated forward in
/// topological order by the replay loops).
///
/// EVIDENCE: every name in `standin_names` is a declaration that carried a
/// kernel-checked VALUE (or checked structure) in its source system — Coq's
/// kernel could delta/iota-reduce through it when it originally checked the
/// rejected value — but is registered here TYPE-ONLY (dump-salvage crash
/// stand-in, family-replay stand-in, forced-type-only row, or an earlier
/// stand-in-blocked fallback). A conversion the kernel cannot complete
/// through such an opaque constant is indistinguishable from a wrong proof
/// by the rejection alone, so the honest verdict is the FamilyStandin shape:
/// register the (kernel-checked) stated type, withhold the value claim,
/// never `KernelVerified`, and seed NO masked-failure taint.
///
/// TRANSITIVE extension (2026-07-12, measured): the shipped classifier
/// deliberately consulted DIRECT deps only, but the kernel's conversion does
/// not stop at direct deps — it δ-unfolds the VALUES of intermediate
/// constants (a dependency that itself kernel-verified can carry the stand-in
/// in its unfolded value), so the opaque wall is hit arbitrarily deep in the
/// dependency cone. The MASKED_SEED census at the 20,234-KV baseline measured
/// exactly this gap: the dominant chain roots (mathcomp `poly_ringType`,
/// `subsetP`, `int_ZmodType`, … and the stdlib `Zquot`/`Qminmax` chains) are
/// rejections with NO direct stand-in dep but a stand-in-contaminated
/// dependency cone. If ANY constant in the cone is a value-less stand-in, the
/// environment the kernel re-checked the value in provably differs from the
/// source system's environment inside that value's dependency cone — the same
/// evidence statement as the direct case, one hop deeper.
///
/// MONOTONE GUARDS (in order):
/// - a rejection whose DIRECT dependencies include a MASKED-FAILURE taint
///   keeps FULL taint semantics (returns `None`): genuine taint always takes
///   precedence, so this classification can never launder a taint chain
///   (taint propagation itself is transitive through the same graph, so the
///   direct check is the complete transitive check — see the taint SOUNDNESS
///   note in `run_incremental_over_reader`);
/// - a rejection with NO stand-in among its direct deps AND no stand-in
///   reachable through its dependency cone is never reclassified (returns
///   `None`): behavior is byte-identical to the pre-lever baseline.
fn standin_blocked_evidence(
    name: &str,
    dep_graph: &HashMap<String, HashSet<String>>,
    masked_tainted: &HashSet<String>,
    standin_names: &HashSet<String>,
    standin_reachable: &HashSet<String>,
) -> Option<StandinWall> {
    if standin_names.is_empty() {
        return None;
    }
    let deps = dep_graph.get(name)?;
    if !masked_tainted.is_empty() && deps.iter().any(|d| masked_tainted.contains(d)) {
        return None;
    }
    if deps.iter().any(|d| standin_names.contains(d)) {
        return Some(StandinWall::Direct);
    }
    if deps.iter().any(|d| standin_reachable.contains(d)) {
        return Some(StandinWall::Transitive);
    }
    None
}

/// Forward-propagation step for the TRANSITIVE stand-in reach set: `name`
/// reaches a stand-in iff any direct dependency IS a stand-in or itself
/// reaches one. Called once per replayed constant, in topological order, so
/// the set is complete for every later dependent (the same argument as the
/// masked-taint propagation). O(direct-degree) per constant.
fn propagate_standin_reach(
    name: &str,
    dep_graph: &HashMap<String, HashSet<String>>,
    standin_names: &HashSet<String>,
    standin_reachable: &mut HashSet<String>,
) {
    if standin_names.is_empty() {
        return;
    }
    let reaches = dep_graph.get(name).is_some_and(|deps| {
        deps.iter()
            .any(|d| standin_names.contains(d) || standin_reachable.contains(d))
    });
    if reaches {
        standin_reachable.insert(name.to_string());
    }
}

/// Capture a forced-type-only event, naming the tainted dependencies that
/// triggered the withhold (the actionable part of the diagnosis).
///
/// Only called when `force_type_only` was computed `true`; does nothing when
/// capture is disabled, so the detail string is never built on the hot path.
fn log_forced_type_only_capture(
    name: &str,
    deps: Option<&HashSet<String>>,
    masked_tainted: &HashSet<String>,
) {
    if speculative_reject_log_path().is_none() {
        return;
    }
    let mut tainted: Vec<&str> = deps
        .map(|deps| {
            deps.iter()
                .filter(|d| masked_tainted.contains(*d))
                .map(String::as_str)
                .collect()
        })
        .unwrap_or_default();
    tainted.sort_unstable();
    let shown = tainted
        .iter()
        .take(8)
        .copied()
        .collect::<Vec<_>>()
        .join(", ");
    let suffix = if tainted.len() > 8 {
        format!(", +{} more", tainted.len() - 8)
    } else {
        String::new()
    };
    log_speculative_capture(
        name,
        REJECT_TAG_FORCED_TYPE_ONLY,
        &format!("value withheld: rests on masked-failure taint via [{shown}{suffix}]"),
    );
}

/// Format the head of a name list as `[a, b, c, +N more]` (cap `shown`).
fn format_name_head(names: &[&str], shown: usize) -> String {
    let head = names
        .iter()
        .take(shown)
        .copied()
        .collect::<Vec<_>>()
        .join(", ");
    if names.len() > shown {
        format!("[{head}, +{} more]", names.len() - shown)
    } else {
        format!("[{head}]")
    }
}

/// Capture an ordinary masked-failure seed (observation only): one
/// [`REJECT_TAG_MASKED_SEED`] line with the kernel rejection head, and one
/// [`REJECT_TAG_MASKED_SEED_DEPS`] line with the dependency-shape evidence
/// (direct tainted deps, direct stand-ins, and stand-ins reachable
/// TRANSITIVELY through the dep graph — the census that measured, and now
/// audits, the classifier's transitive extension).
///
/// Only called on the masked-seed branch; does nothing (and walks nothing)
/// when capture is disabled, so the BFS never runs on the hot path.
fn log_masked_seed_capture(
    name: &str,
    err: &str,
    dep_graph: &HashMap<String, HashSet<String>>,
    masked_tainted: &HashSet<String>,
    standin_names: &HashSet<String>,
) {
    if speculative_reject_log_path().is_none() {
        return;
    }
    log_speculative_capture(name, REJECT_TAG_MASKED_SEED, err);

    let direct: Vec<&str> = dep_graph
        .get(name)
        .map(|deps| deps.iter().map(String::as_str).collect())
        .unwrap_or_default();
    let mut direct_tainted: Vec<&str> = direct
        .iter()
        .copied()
        .filter(|d| masked_tainted.contains(*d))
        .collect();
    direct_tainted.sort_unstable();
    let mut direct_standins: Vec<&str> = direct
        .iter()
        .copied()
        .filter(|d| standin_names.contains(*d))
        .collect();
    direct_standins.sort_unstable();

    // BFS over the dependency graph for stand-ins reachable through
    // intermediate (e.g. kernel-verified) constants.
    let mut visited: HashSet<&str> = direct.iter().copied().collect();
    let mut frontier: Vec<&str> = direct;
    let mut transitive_standins: Vec<&str> = Vec::new();
    let mut transitive_tainted = 0usize;
    while let Some(dep) = frontier.pop() {
        if standin_names.contains(dep) {
            transitive_standins.push(dep);
        }
        if masked_tainted.contains(dep) {
            transitive_tainted += 1;
        }
        if let Some(next) = dep_graph.get(dep) {
            for n in next {
                if visited.insert(n.as_str()) {
                    frontier.push(n.as_str());
                }
            }
        }
    }
    transitive_standins.sort_unstable();

    log_speculative_capture(
        name,
        REJECT_TAG_MASKED_SEED_DEPS,
        &format!(
            "dt={} ds={} tt={} tainted_head={} transitive_standins={}",
            direct_tainted.len(),
            direct_standins.len(),
            transitive_tainted,
            format_name_head(&direct_tainted, 2),
            format_name_head(&transitive_standins, 3),
        ),
    );
}

/// Build the value-bearing [`Declaration`] `try_add_decl` replays through the
/// kernel. Shared with the seeded-duplicate checked-upgrade path so both build
/// byte-identical declarations (including the projection-reducibility rule).
fn build_value_bearing_decl(
    name: &Name,
    decl_kind: DeclKind,
    level_params: &[Name],
    type_: &Expr,
    val: &Expr,
) -> Declaration {
    match decl_kind {
        DeclKind::Theorem => Declaration::Theorem {
            name: name.clone(),
            level_params: level_params.to_vec(),
            type_: type_.clone(),
            value: val.clone(),
        },
        DeclKind::Definition => Declaration::Definition {
            name: name.clone(),
            level_params: level_params.to_vec(),
            type_: type_.clone(),
            value: val.clone(),
            // Structure/class PROJECTIONS must be reducible so the kernel can
            // unfold them during is_def_eq (e.g. DivisionMonoid.toDivInvOneMonoid,
            // OrderBot's parent projections) — otherwise instance diamonds fail
            // to converge and produce spurious Pi-vs-Pi / same-head TypeMismatch
            // rejections. The .olean direct importer already overrides projection
            // bodies to Reducible (clean_olean::import::is_projection_fn_body,
            // #3134); the shard-replay path here previously hardcoded false,
            // dropping that property. SOUNDNESS: unfold_definition gates only on
            // Opaque, never on Reducibility, so this changes only the def-eq
            // tie-break ordering, never the reduction relation — add_decl still
            // fully proof-checks the value; no non-def-eq terms become equal.
            is_reducible: clean_olean::import::is_projection_fn_body(val),
        },
        DeclKind::Opaque => Declaration::Opaque {
            name: name.clone(),
            level_params: level_params.to_vec(),
            type_: type_.clone(),
            value: val.clone(),
        },
        _ => unreachable!("try_add_decl only handles theorem/definition/opaque"),
    }
}

/// Strict structural equality of two kernel types UP TO universe levels:
/// identical except that corresponding `Sort` levels and `Const` universe
/// instantiations may differ freely. CONSERVATIVE — any non-universe
/// structural difference (different head, `BVar`/`FVar`, `Const` NAME, arity,
/// literal, projection name/index, or a variant mismatch) returns `false`.
///
/// Sole use: classify a value REJECTION (see [`is_universe_collapse_rejection`]).
/// A `TypeMismatch` whose two sides are equal modulo universe levels is a
/// universe-COLLAPSE reconstruction gap — the importer floored Coq's floating /
/// algebraic universes to concrete `u32` levels, so a value Coq's own kernel
/// checked lands one level off the declared type (`Sort(Zero)` vs
/// `Sort(Succ Zero)`, …) — NOT a refused proof. Because the check demands
/// byte-identical structure everywhere EXCEPT universe leaves, a genuine
/// wrong-proof mismatch (ANY structural divergence) is never laundered.
fn types_eq_modulo_universe(a: &Expr, b: &Expr) -> bool {
    use clean_kernel::expr::ExprKind as K;
    match (a.kind(), b.kind()) {
        // Metadata is transparent to type checking: unwrap and retry.
        (K::MData(_, inner), _) => types_eq_modulo_universe(inner, b),
        (_, K::MData(_, inner)) => types_eq_modulo_universe(a, inner),
        // Universe-carrying leaves: levels may differ, the rest must match.
        (K::Sort(_), K::Sort(_)) | (K::SProp, K::SProp) => true,
        (K::Const(n1, _), K::Const(n2, _)) => n1 == n2,
        // Level-free leaves: exact match.
        (K::BVar(i), K::BVar(j)) => i == j,
        (K::FVar(i), K::FVar(j)) => i == j,
        (K::Lit(l1), K::Lit(l2)) => l1 == l2,
        // Structural nodes: recurse positionally (binder metadata is irrelevant
        // to the universe-collapse determination, so it is not compared).
        (K::App(f1, x1), K::App(f2, x2)) => {
            types_eq_modulo_universe(f1, f2) && types_eq_modulo_universe(x1, x2)
        }
        (K::Pi(_, d1, b1), K::Pi(_, d2, b2)) | (K::Lam(_, d1, b1), K::Lam(_, d2, b2)) => {
            types_eq_modulo_universe(d1, d2) && types_eq_modulo_universe(b1, b2)
        }
        (K::Let(_, t1, v1, b1, _), K::Let(_, t2, v2, b2, _)) => {
            types_eq_modulo_universe(t1, t2)
                && types_eq_modulo_universe(v1, v2)
                && types_eq_modulo_universe(b1, b2)
        }
        (K::Proj(n1, i1, e1), K::Proj(n2, i2, e2)) => {
            n1 == n2 && i1 == i2 && types_eq_modulo_universe(e1, e2)
        }
        // Any other / mixed variant pair: not provably universe-only.
        _ => false,
    }
}

/// True iff `err` is a value-typecheck rejection whose expected/inferred types
/// are equal modulo universe levels (see [`types_eq_modulo_universe`]) — a
/// universe-collapse reconstruction gap rather than a refused proof, so the
/// value is withheld to a clean type-only stand-in instead of seeding a
/// masked-failure taint.
fn is_universe_collapse_rejection(err: &clean_kernel::KernelEnvError) -> bool {
    let clean_kernel::KernelEnvError::TypeCheckFailed { source, .. } = err else {
        return false;
    };
    matches!(
        source,
        clean_kernel::KernelTypeError::TypeMismatch { expected, inferred, .. }
            if types_eq_modulo_universe(expected, inferred)
    )
}

/// Env-aware companion to [`is_universe_collapse_rejection`]: a `TypeMismatch`
/// whose expected and inferred types become equal MODULO UNIVERSE LEVELS after
/// weak-head-normalizing both sides through the environment (delta-unfolding
/// transparent definitions, then beta). This exposes a universe-collapse gap
/// hidden behind a transparent DEFINITION.
///
/// The motivating shape is a Prop-declared `prod` alias — `leqif m n C :=
/// (m <= n) * ((m == n) = C)`, declared `: Prop`, whose value the template-poly
/// flip renders `prod.{0,0}`. A downstream MONOMORPHIC `prod` projection
/// (`Coq.Init.Datatypes.fst`, `{1,1}`) is applied to `H : leqif m n C`; the
/// kernel rejects `leqif m n C` (folded) against the expected `prod.{1,1} P Q`.
/// After whnf both sides are `prod P Q` differing ONLY in the `{u,v}` universe
/// instance — a genuine universe-collapse reconstruction gap (Coq's own
/// universe-polymorphic `fst` checked it), NOT a refused proof.
///
/// SOUNDNESS: the rejected value is WITHHELD to a clean type-only stand-in —
/// never installed — so no proof term is laundered; only the (universe-variant-
/// equal) declared type is asserted, exactly the trust shape of the existing
/// universe-collapse and stuck-primitive stand-in lanes. The whnf descent
/// requires structural identity everywhere except universe leaves (fuel-bounded,
/// congruent), so any NON-universe divergence still returns `false` and the
/// rejection stays a masked-failure seed.
fn is_universe_collapse_rejection_via_whnf(
    env: &Environment,
    err: &clean_kernel::KernelEnvError,
) -> bool {
    let clean_kernel::KernelEnvError::TypeCheckFailed { source, .. } = err else {
        return false;
    };
    let clean_kernel::KernelTypeError::TypeMismatch {
        expected, inferred, ..
    } = source
    else {
        return false;
    };
    let tc = TypeChecker::new(env);
    reconciles_modulo_universe_via_whnf(&tc, expected, inferred, 64)
}

/// True iff `a` and `b` are equal modulo universe levels after weak-head-
/// normalizing (delta+beta through `tc`) at every level of a fuel-bounded
/// congruence descent. See [`is_universe_collapse_rejection_via_whnf`].
fn reconciles_modulo_universe_via_whnf(
    tc: &TypeChecker<'_>,
    a: &Expr,
    b: &Expr,
    fuel: u32,
) -> bool {
    use clean_kernel::expr::ExprKind as K;
    if fuel == 0 {
        return false;
    }
    // Fast path: already structurally equal modulo universe (no reduction).
    if types_eq_modulo_universe(a, b) {
        return true;
    }
    // Expose the head of each side (unfolds a transparent `leqif`-style def).
    let a = tc.whnf(a);
    let b = tc.whnf(b);
    if types_eq_modulo_universe(&a, &b) {
        return true;
    }
    match (a.kind(), b.kind()) {
        (K::MData(_, inner), _) => reconciles_modulo_universe_via_whnf(tc, inner, &b, fuel - 1),
        (_, K::MData(_, inner)) => reconciles_modulo_universe_via_whnf(tc, &a, inner, fuel - 1),
        (K::App(..), K::App(..)) => {
            let aargs = a.get_app_args();
            let bargs = b.get_app_args();
            aargs.len() == bargs.len()
                && reconciles_modulo_universe_via_whnf(tc, a.get_app_fn(), b.get_app_fn(), fuel - 1)
                && aargs
                    .iter()
                    .zip(bargs.iter())
                    .all(|(x, y)| reconciles_modulo_universe_via_whnf(tc, x, y, fuel - 1))
        }
        (K::Pi(_, d1, c1), K::Pi(_, d2, c2)) | (K::Lam(_, d1, c1), K::Lam(_, d2, c2)) => {
            reconciles_modulo_universe_via_whnf(tc, d1, d2, fuel - 1)
                && reconciles_modulo_universe_via_whnf(tc, c1, c2, fuel - 1)
        }
        _ => false,
    }
}

/// Native machine-primitive module prefixes: Coq declares these operations with
/// the `Primitive` vernacular (OCaml runtime ops — int63 arithmetic/bitwise,
/// float64, persistent arrays, primitive strings), and SerAPI dumps them as
/// value-less axioms. Clean's kernel has NO reduction rule for them, so any
/// conversion that must compute one is genuinely STUCK — an out-of-model
/// reconstruction gap, not a refused proof. `PrimInt63.int` / `PrimFloat.float`
/// carriers model as `Nat` bit-patterns (`coq_primitive_carrier_native`), but
/// the OPERATIONS over them (`add`/`land`/`lsr`/…) stay value-less axioms here.
const NATIVE_PRIMITIVE_MODULE_PREFIXES: &[&str] = &[
    "Coq.Numbers.Cyclic.Int63.PrimInt63.",
    "Coq.Floats.PrimFloat.",
    "Coq.Strings.PrimString.",
    "Coq.Array.PArray.",
];

/// True iff `name` denotes a native machine primitive Clean's kernel cannot
/// reduce: it lives in a `Primitive`-declaring module
/// ([`NATIVE_PRIMITIVE_MODULE_PREFIXES`]) AND is registered VALUE-LESS (an
/// axiom) in `env`. The value-less gate keeps ordinary DEFINED helpers that
/// merely live in those modules (`PrimInt63.id_int`, which DOES reduce) out of
/// the stuck classification.
fn is_stuck_native_primitive(env: &Environment, name: &Name) -> bool {
    let s = name.to_string();
    NATIVE_PRIMITIVE_MODULE_PREFIXES
        .iter()
        .any(|p| s.starts_with(p))
        && env.get_const(name).is_some_and(|c| c.value.is_none())
}

/// True iff the weak-head application spine of `e` is headed by a stuck native
/// primitive ([`is_stuck_native_primitive`]).
fn spine_head_is_stuck_native_primitive(env: &Environment, e: &Expr) -> bool {
    matches!(
        e.get_app_fn().kind(),
        clean_kernel::expr::ExprKind::Const(name, _) if is_stuck_native_primitive(env, name)
    )
}

/// Module-name prefixes for constants whose definitions may transitively unfold
/// to a native machine primitive: the int63 / float64 / primitive-string /
/// persistent-array families (the primitive OPS live in the `Prim*` submodules,
/// but their WRAPPERS — `Uint63.to_Z`, `Uint63.succ`, `Sint63.*` — are what a
/// spec lemma's TYPE names). Broader than [`NATIVE_PRIMITIVE_MODULE_PREFIXES`]
/// (which names only the value-less primitive ops themselves).
const PRIMITIVE_BEARING_MODULE_PREFIXES: &[&str] = &[
    "Coq.Numbers.Cyclic.Int63.",
    "Coq.Floats.",
    "Coq.Strings.PString",
    "Coq.Strings.PrimString",
    "Coq.Array.PArray",
    "Coq.PArray.",
    // int63 ↔ Z Zify injection instances (`Op_digits`, `Op_opp`, `is_zeroE`, …)
    // whose statements reduce through the same native int63 ops.
    "Coq.micromega.ZifyUint63",
    "Coq.micromega.ZifySint63",
];

/// True iff `e` SYNTACTICALLY mentions (as a `Const`, with no reduction) a
/// constant from a primitive-bearing module ([`PRIMITIVE_BEARING_MODULE_PREFIXES`]).
///
/// The cheap syntactic gate that keeps the expensive reduction analysis
/// ([`is_int63_primitive_stuck_rejection`]) off the corpus-wide rejection hot
/// path: a type that names no primitive-bearing constant cannot possibly reduce
/// to a stuck native primitive, so the analysis is skipped. SOUND for the
/// stand-in classification because an int63/float/array/string spec lemma's type
/// always names its own (primitive-bearing) operation — the whnf-reduction that
/// finds the buried primitive necessarily starts from such a constant.
fn mentions_primitive_bearing_const(e: &Expr) -> bool {
    use clean_kernel::expr::ExprKind as K;
    match e.kind() {
        K::Const(name, _) => {
            let s = name.to_string();
            PRIMITIVE_BEARING_MODULE_PREFIXES
                .iter()
                .any(|p| s.starts_with(p))
        }
        K::App(f, a) => mentions_primitive_bearing_const(f) || mentions_primitive_bearing_const(a),
        K::Pi(_, d, b) | K::Lam(_, d, b) => {
            mentions_primitive_bearing_const(d) || mentions_primitive_bearing_const(b)
        }
        K::Let(_, t, v, b, _) => {
            mentions_primitive_bearing_const(t)
                || mentions_primitive_bearing_const(v)
                || mentions_primitive_bearing_const(b)
        }
        K::Proj(_, _, inner) | K::MData(_, inner) => mentions_primitive_bearing_const(inner),
        _ => false,
    }
}

/// Recursion-depth bound for [`types_reconcile_modulo_stuck_primitive`]. Kernel
/// types over int63 spec lemmas nest shallowly (`@eq T lhs rhs` a handful of
/// levels deep); a tight cap keeps the rare, rejected-value-only analysis cheap
/// and total. A term deeper than this classifies conservatively as NOT
/// primitive-only (it stays a masked seed).
const INT63_RECONCILE_FUEL: u32 = 64;

/// True iff some sub-term reachable from `e` (whnf-reducing at every level) is
/// an application whose spine head is a STUCK native primitive
/// ([`spine_head_is_stuck_native_primitive`]) — i.e. reduction of `e` is BLOCKED
/// on a native machine op Clean's kernel cannot compute. The recursive whnf is
/// what unmasks a primitive nested behind a definition or, crucially, sitting in
/// the SCRUTINEE of a stuck recursor/match: `Uint63.to_Z 0` whnf-reduces to a
/// `Nat.rec`/`Bool.rec` blocked on a `PrimInt63.land`/`eqb`-headed scrutinee, so
/// the whnf HEAD is the recursor (not a primitive) while the true obstruction is
/// an argument. Bounded by `fuel` (and returns `false` when exhausted — the
/// term is then conservatively treated as NOT primitive-stuck).
fn subterm_stuck_on_native_primitive(
    tc: &TypeChecker<'_>,
    env: &Environment,
    e: &Expr,
    fuel: u32,
) -> bool {
    use clean_kernel::expr::ExprKind as K;
    if fuel == 0 {
        return false;
    }
    let e = tc.whnf(e);
    if spine_head_is_stuck_native_primitive(env, &e) {
        return true;
    }
    match e.kind() {
        // Scan the head and every application argument: a stuck recursor/match
        // keeps its primitive-blocked scrutinee (and other blocked operands) as
        // arguments of the irreducible spine.
        K::App(..) => {
            subterm_stuck_on_native_primitive(tc, env, e.get_app_fn(), fuel - 1)
                || e.get_app_args()
                    .iter()
                    .any(|arg| subterm_stuck_on_native_primitive(tc, env, arg, fuel - 1))
        }
        K::Pi(_, d, b) | K::Lam(_, d, b) => {
            subterm_stuck_on_native_primitive(tc, env, d, fuel - 1)
                || subterm_stuck_on_native_primitive(tc, env, b, fuel - 1)
        }
        K::Proj(_, _, inner) | K::MData(_, inner) => {
            subterm_stuck_on_native_primitive(tc, env, inner, fuel - 1)
        }
        _ => false,
    }
}

/// Structural comparison of the `expected`/`inferred` types of a value
/// `TypeMismatch` that treats a divergence BLOCKED by a stuck native primitive
/// ([`subterm_stuck_on_native_primitive`]) as reconciled (Coq computes the
/// primitive natively; Clean cannot). It descends through the structure the two
/// types SHARE — matching application spines and binders, and the kernel's own
/// `is_def_eq` (which absorbs β/δ/ι and universe levels) — and, only at the
/// point where they genuinely diverge, asks whether that divergent sub-term is
/// stuck on a native primitive.
///
/// Returns `true` iff the ONLY obstruction to definitional equality is one or
/// more stuck native primitives. This is [`types_eq_modulo_universe`]
/// generalized from "modulo universe leaves" to "modulo stuck native
/// primitives", made reduction-aware.
///
/// PRECISION (the negative controls the tests pin): the primitive check is
/// applied ONLY to the DIVERGENT sub-term, never the whole type. A genuine wrong
/// proof diverges at a NON-primitive position (a different constructor /
/// constant / arity whose divergent sub-term reduces with no native primitive
/// blocking it), so this returns `false` and the rejection stays a
/// masked-failure seed. A mismatch that merely mentions a primitive in a part
/// the two sides SHARE (that part matches and is never scanned) is not
/// laundered.
fn types_reconcile_modulo_stuck_primitive(
    tc: &TypeChecker<'_>,
    env: &Environment,
    a: &Expr,
    b: &Expr,
    fuel: u32,
) -> bool {
    use clean_kernel::expr::ExprKind as K;
    if fuel == 0 {
        // Out of budget: conservatively NOT provably primitive-only.
        return false;
    }
    // The kernel's own conversion first: equal sub-terms (Z arithmetic, shared
    // structure, universe-level slack) reconcile with no primitive involved.
    // (At the TOP level this is always false — the value was rejected, and
    // is_def_eq ⊆ is_le — so a stuck primitive must be found before `true`.)
    if tc.is_def_eq(a, b) {
        return true;
    }
    let a = tc.whnf(a);
    let b = tc.whnf(b);
    // Descend through the structure the two sides SHARE; recurse into the
    // divergent children only.
    match (a.kind(), b.kind()) {
        (K::MData(_, inner), _) => {
            return types_reconcile_modulo_stuck_primitive(tc, env, inner, &b, fuel - 1)
        }
        (_, K::MData(_, inner)) => {
            return types_reconcile_modulo_stuck_primitive(tc, env, &a, inner, fuel - 1)
        }
        // Same application arity AND reconcilable head (same const, etc.): the
        // types agree structurally here, so the divergence is inside one or more
        // arguments — recurse positionally (`@eq Z (to_Z (add x 1)) rhs` vs
        // `@eq Z lhs rhs` descends to the `to_Z (add x 1)` argument).
        (K::App(..), K::App(..)) => {
            let aargs = a.get_app_args();
            let bargs = b.get_app_args();
            if aargs.len() == bargs.len()
                && types_reconcile_modulo_stuck_primitive(
                    tc,
                    env,
                    a.get_app_fn(),
                    b.get_app_fn(),
                    fuel - 1,
                )
            {
                return aargs
                    .iter()
                    .zip(bargs.iter())
                    .all(|(x, y)| types_reconcile_modulo_stuck_primitive(tc, env, x, y, fuel - 1));
            }
        }
        (K::Pi(_, d1, b1), K::Pi(_, d2, b2)) | (K::Lam(_, d1, b1), K::Lam(_, d2, b2)) => {
            return types_reconcile_modulo_stuck_primitive(tc, env, d1, d2, fuel - 1)
                && types_reconcile_modulo_stuck_primitive(tc, env, b1, b2, fuel - 1)
        }
        _ => {}
    }
    // Genuine structural divergence at THIS position (differing heads, arity, or
    // variant). Reconciled ONLY if the divergence is blocked by a stuck native
    // primitive on one side or the other (e.g. `to_Z 0`, which whnf-reduces to a
    // recursor stuck on a `PrimInt63.land` scrutinee, vs the Z constructor `0`).
    subterm_stuck_on_native_primitive(tc, env, &a, fuel - 1)
        || subterm_stuck_on_native_primitive(tc, env, &b, fuel - 1)
}

/// True iff `err` is a value-typecheck rejection whose ONLY obstruction is a
/// STUCK native primitive ([`types_reconcile_modulo_stuck_primitive`]): the
/// proof appeals to int63 / float64 / array / string machine-primitive
/// computation Coq performs natively but Clean's kernel cannot, so the value is
/// withheld to a clean type-only stand-in instead of seeding a masked-failure
/// taint (the CoFix-style out-of-model trust shape). Requires the same
/// `TypeCheckFailed{TypeMismatch}` shape as [`is_universe_collapse_rejection`];
/// a genuine wrong proof (structural divergence away from any primitive) is
/// never laundered.
fn is_int63_primitive_stuck_rejection(
    env: &Environment,
    err: &clean_kernel::KernelEnvError,
) -> bool {
    let clean_kernel::KernelEnvError::TypeCheckFailed { source, .. } = err else {
        return false;
    };
    let clean_kernel::KernelTypeError::TypeMismatch {
        expected, inferred, ..
    } = source
    else {
        return false;
    };
    // Cheap syntactic pre-filter (no reduction): unless one side names a
    // primitive-bearing constant, the reduction analysis cannot find a stuck
    // native primitive — skip it. This keeps the whnf-heavy analysis off the
    // ~all non-int63 rejections across the corpus.
    if !mentions_primitive_bearing_const(expected) && !mentions_primitive_bearing_const(inferred) {
        return false;
    }
    let tc = TypeChecker::new(env);
    types_reconcile_modulo_stuck_primitive(&tc, env, expected, inferred, INT63_RECONCILE_FUEL)
}

/// Maximum successive recursor-motive-universe bumps attempted by the monotone
/// retry: a Set-valued spec inductive lands at level 1, a Type-valued one at
/// level 2, both reachable from the speculative Prop default 0 within two
/// bumps. A tight cap keeps the (rare, rejected-value-only) retry cheap.
const MOTIVE_UNIVERSE_RETRY_BUMPS: usize = 2;

/// True iff `l` is a concrete universe numeral (`Zero` or `Succ^n(Zero)`) — the
/// exact shape `cic_to_flat_expr` emits for a `<ind>.rec.{ℓ}` motive-universe
/// instance (`FlatLevel::succ^ℓ(zero)`). Algebraic levels (`Param`/`Max`/`IMax`)
/// are left untouched: they are already-correct polymorphic instances, not the
/// speculative Prop-default guess this retry corrects.
fn is_concrete_level_numeral(l: &Level) -> bool {
    match l {
        Level::Zero => true,
        Level::Succ(inner) => is_concrete_level_numeral(inner),
        _ => false,
    }
}

/// Rebuild `value` with every `<…>.rec` recursor-instance's concrete-numeral
/// motive-universe bumped by one. Returns `None` when the term carries no such
/// recursor instance (there is nothing to retry).
///
/// SOUNDNESS: a recursor's universe instance annotates only the motive's target
/// sort — it does NOT participate in iota reduction (`I.rec.{0}` and
/// `I.rec.{1}` reduce identically on constructors). So a bumped value that the
/// kernel accepts computes byte-identically to the level-0 value: the retry can
/// change ONLY whether the term typechecks, never what it evaluates to. It is
/// therefore incapable of laundering a wrong proof into a false `KernelVerified`
/// — a genuine branch/structure mismatch is a `Sort`-independent rejection that
/// no level bump can rescue.
fn bump_recursor_motive_levels(value: &Expr) -> Option<Expr> {
    let mut bumped = false;
    let out = bump_recursor_motive_levels_walk(value, &mut bumped);
    bumped.then_some(out)
}

fn bump_recursor_motive_levels_walk(e: &Expr, bumped: &mut bool) -> Expr {
    use clean_kernel::expr::ExprKind as K;
    match e.kind() {
        // Bump ONLY the motive slot (level 0). A monomorphic recursor carries a
        // one-element `[motive]` instance; a TEMPLATE-POLY recursor
        // (`prod.0.rec.{motive,u,v}`) carries the motive followed by the
        // inductive's own universe parameters — those trailing slots are NOT a
        // motive universe and must be left untouched. Both are handled by
        // rebuilding the list with slot 0 bumped and the rest cloned.
        K::Const(name, levels)
            if !levels.is_empty()
                && name.last_component().as_deref() == Some("rec")
                && is_concrete_level_numeral(&levels[0]) =>
        {
            *bumped = true;
            let mut lv = clean_kernel::expr::LevelVec::new();
            lv.push(Level::succ(levels[0].clone()));
            lv.extend(levels[1..].iter().cloned());
            Expr::from_kind(K::Const(name.clone(), lv))
        }
        K::App(f, a) => Expr::from_kind(K::App(
            Arc::new(bump_recursor_motive_levels_walk(f, bumped)),
            Arc::new(bump_recursor_motive_levels_walk(a, bumped)),
        )),
        K::Lam(bd, ty, body) => Expr::from_kind(K::Lam(
            *bd,
            Arc::new(bump_recursor_motive_levels_walk(ty, bumped)),
            Arc::new(bump_recursor_motive_levels_walk(body, bumped)),
        )),
        K::Pi(bd, ty, body) => Expr::from_kind(K::Pi(
            *bd,
            Arc::new(bump_recursor_motive_levels_walk(ty, bumped)),
            Arc::new(bump_recursor_motive_levels_walk(body, bumped)),
        )),
        K::Let(n, ty, val, body, nd) => Expr::from_kind(K::Let(
            n.clone(),
            Arc::new(bump_recursor_motive_levels_walk(ty, bumped)),
            Arc::new(bump_recursor_motive_levels_walk(val, bumped)),
            Arc::new(bump_recursor_motive_levels_walk(body, bumped)),
            *nd,
        )),
        K::Proj(name, idx, inner) => Expr::from_kind(K::Proj(
            name.clone(),
            *idx,
            Arc::new(bump_recursor_motive_levels_walk(inner, bumped)),
        )),
        K::MData(m, inner) => Expr::from_kind(K::MData(
            m.clone(),
            Arc::new(bump_recursor_motive_levels_walk(inner, bumped)),
        )),
        // BVar, FVar, Sort, Lit, non-recursor Const, and the impredicative /
        // cubical extensions carry no bumpable recursor instance: clone as-is.
        _ => e.clone(),
    }
}

/// Rebuild `value` so every recursor reference's universe-level ARITY matches
/// the recursor's declared `level_params` count in `env`. The Coq importer's
/// Case lowering emits `<ind>.<i>.rec` at the speculative motive-universe arity
/// (one level), but a Prop-valued spec inductive gets a PROP-ONLY recursor
/// (`elim_only_at_universe_zero` → zero level params, no motive universe), so
/// the reference OVER-supplies levels and the kernel rejects with
/// `LevelCountMismatch` (`crates/clean-kernel/src/tc/infer.rs`: strict count
/// check). Truncate each over-supplied recursor reference's level list to the
/// declared count — or, in the rarer under-supplied direction, zero-extend it
/// (the motive-universe [bump ladder][`bump_recursor_motive_levels`] then lifts
/// it if the declared sort demands). Returns `None` when no recursor reference
/// needs adjusting (nothing to retry — byte-identical to skipping this step).
///
/// SOUNDNESS (identical to [`bump_recursor_motive_levels`]): a recursor's
/// universe instance annotates only the motive's target sort and NEVER
/// participates in iota reduction (`I.rec.{}` / `I.rec.{0}` / `I.rec.{1}`
/// reduce identically on constructors). So an arity-corrected value the kernel
/// ACCEPTS computes byte-identically to the mis-emitted one: the correction can
/// change ONLY whether the term typechecks, never what it evaluates to — it
/// cannot launder a wrong proof (a genuine branch/structure mismatch is a
/// `Sort`/arity-independent rejection that no level adjustment can rescue).
/// Restricted to `…rec`-named references so the reasoning stays on recursors;
/// the env-count comparison self-gates (only genuine mismatches are touched),
/// and the kernel arbitrates every candidate.
fn fix_recursor_level_counts(env: &Environment, value: &Expr) -> Option<Expr> {
    let mut fixed = false;
    let out = fix_recursor_level_counts_walk(env, value, &mut fixed);
    fixed.then_some(out)
}

fn fix_recursor_level_counts_walk(env: &Environment, e: &Expr, fixed: &mut bool) -> Expr {
    use clean_kernel::expr::ExprKind as K;
    match e.kind() {
        K::Const(name, levels) if name.last_component().as_deref() == Some("rec") => {
            match env.get_const(name) {
                Some(info) if info.level_params.len() != levels.len() => {
                    *fixed = true;
                    let declared = info.level_params.len();
                    // Truncate to `declared` levels (over-supplied — the Prop-only
                    // recursor case), or extend up to it (under-supplied). The
                    // kernel's generated recursor orders its level params
                    // `[motive, <inductive's own universe params>…]`, so a
                    // missing slot 0 is the motive (Prop default `0`, which the
                    // motive-universe bump ladder then lifts if the site needs a
                    // larger motive), while every TRAILING missing slot is one of
                    // the inductive's own universe parameters. A template-poly
                    // recursor (`prod.0.rec.{motive,u,v}`) instantiates those at
                    // `Sort 1` (the {1,1} monomorphic instance), so fill trailing
                    // slots with `Sort 1` (`succ zero`), not `0`. Kernel-arbitrated
                    // and monotone: this only ever runs on an already-rejected
                    // value, and the recursor's universe instance never
                    // participates in iota reduction, so a wrong fill simply
                    // rejects again and the caller falls through to the clean
                    // stand-in — it cannot launder a wrong proof.
                    let mut lv = clean_kernel::expr::LevelVec::new();
                    for i in 0..declared {
                        match levels.get(i) {
                            Some(l) => lv.push(l.clone()),
                            None if i == 0 => lv.push(Level::Zero),
                            None => lv.push(Level::succ(Level::Zero)),
                        }
                    }
                    Expr::from_kind(K::Const(name.clone(), lv))
                }
                // Recursor absent from env, or its arity already matches: leave
                // the reference untouched (a `…rec` Const has no sub-terms).
                _ => e.clone(),
            }
        }
        K::App(f, a) => Expr::from_kind(K::App(
            Arc::new(fix_recursor_level_counts_walk(env, f, fixed)),
            Arc::new(fix_recursor_level_counts_walk(env, a, fixed)),
        )),
        K::Lam(bd, ty, body) => Expr::from_kind(K::Lam(
            *bd,
            Arc::new(fix_recursor_level_counts_walk(env, ty, fixed)),
            Arc::new(fix_recursor_level_counts_walk(env, body, fixed)),
        )),
        K::Pi(bd, ty, body) => Expr::from_kind(K::Pi(
            *bd,
            Arc::new(fix_recursor_level_counts_walk(env, ty, fixed)),
            Arc::new(fix_recursor_level_counts_walk(env, body, fixed)),
        )),
        K::Let(n, ty, val, body, nd) => Expr::from_kind(K::Let(
            n.clone(),
            Arc::new(fix_recursor_level_counts_walk(env, ty, fixed)),
            Arc::new(fix_recursor_level_counts_walk(env, val, fixed)),
            Arc::new(fix_recursor_level_counts_walk(env, body, fixed)),
            *nd,
        )),
        K::Proj(name, idx, inner) => Expr::from_kind(K::Proj(
            name.clone(),
            *idx,
            Arc::new(fix_recursor_level_counts_walk(env, inner, fixed)),
        )),
        K::MData(m, inner) => Expr::from_kind(K::MData(
            m.clone(),
            Arc::new(fix_recursor_level_counts_walk(env, inner, fixed)),
        )),
        // BVar, FVar, Sort, Lit, non-`rec` Const, and impredicative / cubical
        // extensions carry no adjustable recursor reference: clone as-is.
        _ => e.clone(),
    }
}

/// The motive-universe bump loop shared by [`retry_speculative_motive_universe`]:
/// re-check `value` with every concrete-numeral `<…>.rec` motive universe
/// bumped by one, up to [`MOTIVE_UNIVERSE_RETRY_BUMPS`] times, stopping at the
/// first kernel-accepted candidate. Returns `None` when `value` carries no
/// bumpable recursor instance or no bump is accepted.
fn retry_motive_universe_bump_ladder(
    env: &mut Environment,
    name: &Name,
    decl_kind: DeclKind,
    level_params: &[Name],
    type_: &Expr,
    value: &Expr,
) -> Option<AddConstResult> {
    let mut candidate = bump_recursor_motive_levels(value)?;
    for _ in 0..MOTIVE_UNIVERSE_RETRY_BUMPS {
        let decl = build_value_bearing_decl(name, decl_kind, level_params, type_, &candidate);
        if env.add_decl(decl).is_ok() {
            return Some(AddConstResult::KernelVerified);
        }
        match bump_recursor_motive_levels(&candidate) {
            Some(next) => candidate = next,
            None => break,
        }
    }
    None
}

/// Monotone motive-universe retry for a SPECULATIVE value the kernel already
/// REJECTED. Two rejection shapes are corrected, both kernel-arbitrated:
///
/// 1. **Level-COUNT mismatch** ([`fix_recursor_level_counts`]). The importer's
///    Case lowering emits `<ind>.<i>.rec` at the speculative motive-universe
///    ARITY (one level), but a Prop-valued spec inductive gets a PROP-ONLY
///    recursor (`elim_only_at_universe_zero` → zero level params). Realign each
///    recursor reference's level list to the env-declared count and re-check;
///    if the count-corrected value still lands one motive-universe too low on
///    some OTHER (correctly-arity'd) recursor, run the bump ladder ON TOP of
///    the count fix.
/// 2. **Motive-universe too low** ([`bump_recursor_motive_levels`]). A
///    Set/Type-valued spec inductive (`leq_xor_gtn`/`ltn_xor_geq`/
///    `compare_nat : Set`) whose `case:` return predicate the level derivation
///    could not classify emits its recursor at the speculative Prop default
///    `rec.{0}`, one universe too low; the kernel rejects the motive on a
///    `Sort ⋢ Sort` mismatch. Retry with the motive universe bumped.
///
/// MONOTONE by construction: this fires ONLY after `add_decl` rejected the
/// speculative value, so a constant the kernel accepts today (e.g. the
/// genuinely Prop-motive `character`/`order` cluster that verifies at `rec.{0}`)
/// is never re-derived and can never drop. The kernel arbitrates every retry
/// candidate; a wrong adjustment simply rejects again and the caller falls
/// through to the clean type-only axiom, exactly as before.
fn retry_speculative_motive_universe(
    env: &mut Environment,
    name: &Name,
    decl_kind: DeclKind,
    level_params: &[Name],
    type_: &Expr,
    value: &Expr,
) -> Option<AddConstResult> {
    // (1) Level-COUNT fix first: realign every recursor reference's level arity
    //     to the env-declared count, then re-check. If the count-corrected value
    //     still needs a motive-universe lift on some correctly-arity'd recursor,
    //     run the bump ladder on top of the count fix.
    if let Some(count_fixed) = fix_recursor_level_counts(env, value) {
        let decl = build_value_bearing_decl(name, decl_kind, level_params, type_, &count_fixed);
        if env.add_decl(decl).is_ok() {
            return Some(AddConstResult::KernelVerified);
        }
        if let Some(result) = retry_motive_universe_bump_ladder(
            env,
            name,
            decl_kind,
            level_params,
            type_,
            &count_fixed,
        ) {
            return Some(result);
        }
    }
    // (2) No count mismatch (or the count fix did not clear the rejection): the
    //     original motive-universe bump ladder on the un-corrected value —
    //     byte-identical to the pre-count-fix behavior.
    retry_motive_universe_bump_ladder(env, name, decl_kind, level_params, type_, value)
}

/// Number of LEADING universe-instance slots on a template-poly `prod`
/// reference that are NOT the inductive's own `{u,v}` parameters, keyed on the
/// full constant name (the recursor's motive slot). `None` for non-`prod`.
fn template_poly_prod_motive_prefix(name: &Name) -> Option<usize> {
    let prod = crate::coq::alpha::TEMPLATE_POLY_PROD; // "Coq.Init.Datatypes.prod.0"
    let s = name.to_string();
    if s == prod || s == format!("{prod}.0") {
        // The inductive or its constructor: every level is a `{u,v}` param.
        Some(0)
    } else if s == format!("{prod}.rec") {
        // The recursor `prod.0.rec.{motive,u,v}`: level 0 is the motive.
        Some(1)
    } else {
        None
    }
}

/// True iff `l` is exactly `Sort 1` (`succ zero`) — the monomorphic `{1,1}`
/// instance a template-poly `prod` reference carries by default.
fn is_level_one(l: &Level) -> bool {
    matches!(l, Level::Succ(inner) if matches!(inner.as_ref(), Level::Zero))
}

/// True iff `ty` is exactly the sort `Prop` (`Sort Zero`), modulo metadata.
fn type_is_prop_sort(ty: &Expr) -> bool {
    use clean_kernel::expr::ExprKind as K;
    match ty.kind() {
        K::MData(_, inner) => type_is_prop_sort(inner),
        K::Sort(l) => matches!(l, Level::Zero),
        _ => false,
    }
}

/// Peel exactly `n` leading `Pi` binders off `ty` and return the resulting
/// codomain, or `None` if `ty` has fewer than `n` `Pi` binders (metadata
/// transparent). The codomain may be open under the peeled binders — the caller
/// only inspects whether it is a concrete `Sort`, which the peeled bound
/// variables never are, so no substitution is needed.
fn peel_pi_codomain(ty: &Expr, n: usize) -> Option<&Expr> {
    use clean_kernel::expr::ExprKind as K;
    let mut cur = ty;
    let mut remaining = n;
    while remaining > 0 {
        match cur.kind() {
            K::MData(_, inner) => cur = inner,
            K::Pi(_, _, cod) => {
                cur = cod;
                remaining -= 1;
            }
            _ => return None,
        }
    }
    Some(cur)
}

/// Conservative: true iff `term` provably has type `Prop` (`Sort 0`) in `env`.
///
/// This is the ENV-DIRECTED discriminator that decides whether a template-poly
/// `prod`/`pair`/`prod.rec` instance's two TYPE arguments are propositions, so
/// the instance may soundly flip to the `{0,0}` (`Prop`) rendering. It peels the
/// argument's type through the env exactly as far as it can prove:
///   * a bare `Const` whose DECLARED type is `Prop` (an axiom/def `P : Prop`);
///   * an application spine `c a₁ … aₙ` whose head constant's declared type has
///     a `Prop` codomain after peeling its `n` argument binders (`and X Y`,
///     `@eq T x y`, `le m n`, …);
///   * a dependent product `∀ …, C`, which is `Prop` exactly when its codomain
///     `C` is `Prop` (impredicativity — `imax(_, 0) = 0`).
///
/// Anything else — a bound/free-variable head, a `Sort`, a literal, a `let`, a
/// `λ`, a projection — returns FALSE, so the instance conservatively stays at
/// the `{1,1}` (`Type`) rendering. Being conservative is sound in BOTH
/// directions: a false negative merely leaves a genuinely-`Prop` instance at
/// `{1,1}` (the kernel then rejects and the value falls to the clean stand-in,
/// exactly as before this rung), and every candidate the flip does build is
/// still kernel-arbitrated.
#[cfg(test)]
fn is_provably_prop(env: &Environment, term: &Expr) -> bool {
    is_provably_prop_ctx(env, term, &[], 0)
}

/// As [`is_provably_prop`], but carrying a de Bruijn context `prop_ctx` of the
/// enclosing binders' Prop-ness (innermost LAST): `prop_ctx[len-1-i]` is `true`
/// iff the `i`-th bound variable's binder TYPE is the sort `Prop` (`Sort 0`),
/// i.e. that variable denotes a proposition. This lets the flip recognize the
/// real `mathcomp` shape `fun (A B : Prop) (h : A * B) => …` where a `prod`'s
/// two type arguments are de Bruijn variables (`A`/`B`), not literal
/// `is_true`/`eq` heads — the "nested/inner prod instance" the syntactic
/// concrete-arg analysis alone missed (`real_maxrN`).
fn is_provably_prop_ctx(env: &Environment, term: &Expr, prop_ctx: &[bool], depth: usize) -> bool {
    use clean_kernel::expr::ExprKind as K;
    if depth > 128 {
        return false;
    }
    match term.kind() {
        K::MData(_, inner) => is_provably_prop_ctx(env, inner, prop_ctx, depth + 1),
        // `∀ x, C : Prop` ⇔ `C : Prop` (impredicativity: `imax(u_dom, 0) = 0`).
        // `C` lives under the new binder `x : dom`, so extend the context with
        // whether `x` itself denotes a proposition (`dom` is the sort `Prop`).
        K::Pi(_, dom, cod) => {
            let mut ctx = prop_ctx.to_vec();
            ctx.push(type_is_prop_sort(dom));
            is_provably_prop_ctx(env, cod, &ctx, depth + 1)
        }
        // A bare constant: its declared type must itself BE `Prop`.
        K::Const(name, _) => env
            .get_const(name)
            .is_some_and(|c| type_is_prop_sort(&c.type_)),
        // An application `c a₁ … aₙ`: peel `c`'s declared-type telescope by `n`
        // binders and require the resulting codomain to be `Prop`.
        K::App(_, _) => {
            let head = term.get_app_fn();
            let K::Const(name, _) = head.kind() else {
                return false;
            };
            let n = term.get_app_num_args();
            env.get_const(name)
                .and_then(|c| peel_pi_codomain(&c.type_, n))
                .is_some_and(type_is_prop_sort)
        }
        // A bound variable whose binder TYPE is the sort `Prop`: it denotes a
        // proposition, so a `prod`/`pair` over it is a prod-of-Props.
        K::BVar(i) => {
            let idx = *i as usize;
            idx < prop_ctx.len() && prop_ctx[prop_ctx.len() - 1 - idx]
        }
        _ => false,
    }
}

/// ENV-DIRECTED, PER-INSTANCE template-poly `prod` Prop flip (round 3):
/// rebuild `value` flipping EACH template-poly `prod`/`pair`/`prod.rec`
/// application from the monomorphic `{1,1}` (`Type`) instance to `{0,0}`
/// (`Prop`) — the motive level of the recursor is left untouched — but ONLY at
/// the instances whose two TYPE arguments are provably `Prop`
/// ([`is_provably_prop`]). Every other instance (a `Type`-level carrier such as
/// `R1 * R2`) stays at `{1,1}`. Returns `None` when no instance was flipped
/// (nothing to retry).
///
/// This is the round-3 replacement for the round-2 GLOBAL flip: a downstream
/// constant that mixes BOTH universes in one term — a `Type`-level `R1 * R2`
/// carrier at `{1,1}` AND a `Prop`-level `prod P Q` at `{0,0}` — gets each
/// instance rendered at the universe its own arguments demand, which a single
/// global assignment could never satisfy (the 85 round-2 regressions). The
/// `eqmx`/`eqmxP`/`eqmx_refl` gains are retained: their `prod` arguments ARE
/// all-`Prop`, so those instances still flip.
///
/// SOUNDNESS: kernel-arbitrated (only an accepted candidate is `KernelVerified`)
/// and monotone (fires ONLY after the kernel already rejected the `{1,1}`
/// value). The flip changes only the universe instance a `Sort`-polymorphic
/// constructor/recursor is applied at — `prod`'s iota reduction ignores its
/// universe instance entirely — never the term's computational content, so it
/// cannot launder a wrong proof: a genuine structural mismatch rejects at every
/// instance.
fn flip_template_poly_prod_per_instance(env: &Environment, value: &Expr) -> Option<Expr> {
    let mut flipped = false;
    let out = flip_per_instance_walk(env, value, &[], false, &mut flipped);
    flipped.then_some(out)
}

/// As [`flip_template_poly_prod_per_instance`] but BINDER-SORT-AWARE: a `prod`
/// whose two type arguments are de Bruijn variables bound by an enclosing
/// `: Prop` binder (`fun (A B : Prop) (h : A * B) => …`) is ALSO recognized as a
/// prod-of-Props and flipped. This is a strictly LARGER flip than the concrete-
/// arg one, so it is tried ONLY as a fallback AFTER the concrete flip fails (see
/// [`try_prod_flip_kv`]) — a superset flip could otherwise strand a `prod`-of-
/// Props that a `Type` context genuinely needs at `{1,1}`, so escalating keeps
/// the round-3 concrete-flip gains monotone.
fn flip_template_poly_prod_per_instance_deep(env: &Environment, value: &Expr) -> Option<Expr> {
    let mut flipped = false;
    let out = flip_per_instance_walk(env, value, &[], true, &mut flipped);
    flipped.then_some(out)
}

fn flip_per_instance_walk(
    env: &Environment,
    e: &Expr,
    prop_ctx: &[bool],
    binder_aware: bool,
    flipped: &mut bool,
) -> Expr {
    use clean_kernel::expr::ExprKind as K;
    // A template-poly `prod` application (the inductive, its `pair` constructor,
    // or its recursor). All three take their two TYPE arguments (`A : Sort u`,
    // `B : Sort v`) as the FIRST two application arguments (`prod`'s two
    // parameters), so the Prop-analysis keys on `args[0]`/`args[1]`.
    if let K::App(_, _) = e.kind() {
        let head = e.get_app_fn();
        if let K::Const(name, levels) = head.kind() {
            if let Some(prefix) = template_poly_prod_motive_prefix(name) {
                let args = e.get_app_args();
                // Recurse into EVERY argument first (nested `prod`s flip on
                // their own merits, independent of this head's decision).
                let rebuilt_args: Vec<Expr> = args
                    .iter()
                    .map(|&a| flip_per_instance_walk(env, a, prop_ctx, binder_aware, flipped))
                    .collect();
                // Flip THIS instance's `{u,v}` slots only when both TYPE
                // arguments are provably `Prop` (in the current binder context).
                let both_prop = args.len() >= 2
                    && is_provably_prop_ctx(env, args[0], prop_ctx, 0)
                    && is_provably_prop_ctx(env, args[1], prop_ctx, 0);
                let new_head = if both_prop {
                    let mut lv = clean_kernel::expr::LevelVec::new();
                    let mut did = false;
                    for (i, l) in levels.iter().enumerate() {
                        if i >= prefix && is_level_one(l) {
                            lv.push(Level::Zero);
                            did = true;
                        } else {
                            lv.push(l.clone());
                        }
                    }
                    if did {
                        *flipped = true;
                        Expr::from_kind(K::Const(name.clone(), lv))
                    } else {
                        head.clone()
                    }
                } else {
                    head.clone()
                };
                // Reassemble the spine `head arg0 arg1 …` in source order.
                let mut cur = new_head;
                for a in rebuilt_args {
                    cur = Expr::from_kind(K::App(Arc::new(cur), Arc::new(a)));
                }
                return cur;
            }
        }
    }
    // A pushed binder records whether the bound variable denotes a proposition
    // (its type is the sort `Prop`) — but ONLY in binder-aware mode; the
    // concrete-arg mode pushes a placeholder `false` so de Bruijn indices stay
    // aligned while every `BVar` reads as non-Prop (byte-identical to round 3).
    let push_sort = |ty: &Expr| binder_aware && type_is_prop_sort(ty);
    match e.kind() {
        K::App(f, a) => Expr::from_kind(K::App(
            Arc::new(flip_per_instance_walk(
                env,
                f,
                prop_ctx,
                binder_aware,
                flipped,
            )),
            Arc::new(flip_per_instance_walk(
                env,
                a,
                prop_ctx,
                binder_aware,
                flipped,
            )),
        )),
        K::Lam(bd, ty, body) => {
            let ty2 = flip_per_instance_walk(env, ty, prop_ctx, binder_aware, flipped);
            let mut inner_ctx = prop_ctx.to_vec();
            inner_ctx.push(push_sort(ty));
            let body2 = flip_per_instance_walk(env, body, &inner_ctx, binder_aware, flipped);
            Expr::from_kind(K::Lam(*bd, Arc::new(ty2), Arc::new(body2)))
        }
        K::Pi(bd, ty, body) => {
            let ty2 = flip_per_instance_walk(env, ty, prop_ctx, binder_aware, flipped);
            let mut inner_ctx = prop_ctx.to_vec();
            inner_ctx.push(push_sort(ty));
            let body2 = flip_per_instance_walk(env, body, &inner_ctx, binder_aware, flipped);
            Expr::from_kind(K::Pi(*bd, Arc::new(ty2), Arc::new(body2)))
        }
        K::Let(n, ty, val, body, nd) => {
            let ty2 = flip_per_instance_walk(env, ty, prop_ctx, binder_aware, flipped);
            let val2 = flip_per_instance_walk(env, val, prop_ctx, binder_aware, flipped);
            let mut inner_ctx = prop_ctx.to_vec();
            inner_ctx.push(push_sort(ty));
            let body2 = flip_per_instance_walk(env, body, &inner_ctx, binder_aware, flipped);
            Expr::from_kind(K::Let(
                n.clone(),
                Arc::new(ty2),
                Arc::new(val2),
                Arc::new(body2),
                *nd,
            ))
        }
        K::Proj(name, idx, inner) => Expr::from_kind(K::Proj(
            name.clone(),
            *idx,
            Arc::new(flip_per_instance_walk(
                env,
                inner,
                prop_ctx,
                binder_aware,
                flipped,
            )),
        )),
        K::MData(m, inner) => Expr::from_kind(K::MData(
            m.clone(),
            Arc::new(flip_per_instance_walk(
                env,
                inner,
                prop_ctx,
                binder_aware,
                flipped,
            )),
        )),
        _ => e.clone(),
    }
}

/// Try the template-poly `prod` flip candidates in ESCALATING order and return
/// `KernelVerified` on the first the kernel accepts, else `None`:
///   1. concrete-arg flip ([`flip_template_poly_prod_per_instance`]) — the
///      proven round-3 flip;
///   2. binder-sort-aware flip ([`flip_template_poly_prod_per_instance_deep`]) —
///      also flips prods over `: Prop`-bound de Bruijn variables.
///
/// Both flip the value AND the declared type. Escalation keeps the round-3 gains
/// monotone: candidate 2 is a superset flip, tried only after candidate 1 fails,
/// so nothing candidate 1 already verified can be lost, and the kernel arbitrates
/// every candidate. Fires ONLY on an already-rejected value.
fn try_prod_flip_kv(
    env: &mut Environment,
    name: &Name,
    decl_kind: DeclKind,
    level_params: &[Name],
    type_: &Expr,
    val: &Expr,
) -> bool {
    for deep in [false, true] {
        let (fv, ft) = if deep {
            (
                flip_template_poly_prod_per_instance_deep(env, val),
                flip_template_poly_prod_per_instance_deep(env, type_),
            )
        } else {
            (
                flip_template_poly_prod_per_instance(env, val),
                flip_template_poly_prod_per_instance(env, type_),
            )
        };
        if fv.is_some() || ft.is_some() {
            let cand_ty = ft.as_ref().unwrap_or(type_);
            let cand_val = fv.as_ref().unwrap_or(val);
            let decl = build_value_bearing_decl(name, decl_kind, level_params, cand_ty, cand_val);
            if env.add_decl(decl).is_ok() {
                return true;
            }
        }
    }
    false
}

/// Try adding as Theorem first (if value present), then fall back to Axiom.
fn try_add_decl(
    env: &mut Environment,
    name: Name,
    decl_kind: DeclKind,
    level_params: Vec<Name>,
    type_: Expr,
    value: Option<&Expr>,
    speculative: bool,
) -> AddConstResult {
    // A constant with this NAME is already installed (the prelude-seeded env, or
    // an earlier replay). Blindly re-adding would hit `add_decl`'s
    // "Duplicate declaration" and count the row failed even when the olean copy
    // is exactly the already-checked declaration. Decide the duplicate honestly
    // instead: checked axiom-stub upgrade, twin acceptance, or a PRECISE
    // divergence rejection. The inductive-family member path is NOT intercepted
    // here: `try_accept_existing_inductive_family_constant` already ran in
    // `reconstruct_and_replay_one` (before this call), so only its fall-through
    // — non-family names — reaches this pre-check.
    if env.get_const(&name).is_some() {
        return try_accept_seeded_duplicate(env, &name, decl_kind, &level_params, &type_, value);
    }

    // Captures the typecheck error when a value WAS present but the kernel
    // rejected it: that is the concerning masked-failure case the axiom fallback
    // would otherwise hide. Stays `None` when no value was present.
    let mut value_failed: Option<String> = None;
    // Captures a value rejection that is a universe-COLLAPSE reconstruction gap
    // (expected/inferred equal modulo universe levels): a clean stand-in, NOT a
    // masked-failure taint.
    let mut universe_recon: Option<String> = None;
    // Captures a value rejection STUCK on a native int63/float/array/string
    // machine primitive (out-of-model for Clean's kernel): a clean stand-in,
    // NOT a masked-failure taint.
    let mut int63_standin: Option<String> = None;
    if let Some(val) = value {
        let decl = build_value_bearing_decl(&name, decl_kind, &level_params, &type_, val);
        match env.add_decl(decl) {
            // A value that genuinely typechecked: the only honest KernelVerified
            // verdict on this path. (A SPECULATIVE value that typechecks is still
            // a genuine kernel proof — the kernel is the arbiter — so the
            // speculative flag is irrelevant on success.)
            Ok(()) => return AddConstResult::KernelVerified,
            // A SPECULATIVE value (derived recursor motive universe) the kernel
            // rejects is a wrong GUESS, not a refused proof: discard it and fall
            // back to a CLEAN type-only axiom (no masked-failure taint),
            // byte-identical in effect to the value never having translated.
            // The discarded error is the diagnostic blind spot: capture it to
            // the env-gated log (observation only, verdict unchanged).
            Err(err) if speculative => {
                // Monotone motive-universe retry: a Set/Type-valued spec
                // inductive whose `case:` return predicate the level derivation
                // could not classify emits its recursor at the speculative Prop
                // default `rec.{0}`, one universe too low, and the kernel
                // rejects the motive on a `Sort ⋢ Sort` mismatch. Retry the SAME
                // value with the recursor motive universe bumped. This fires
                // ONLY on an already-rejected value (monotone: a constant KV
                // today is never re-derived), and a level bump cannot change a
                // recursor's iota reduction, so an accepted bumped value
                // computes byte-identically to the level-0 value — no fidelity
                // risk. The kernel arbitrates every attempt.
                if let Some(result) = retry_speculative_motive_universe(
                    env,
                    &name,
                    decl_kind,
                    &level_params,
                    &type_,
                    val,
                ) {
                    return result;
                }
                // ROUND 4: a SPECULATIVE-motive value can ALSO carry template-poly
                // `prod`/`pair`/`prod.rec` instances the round-3 {1,1}->{0,0} flip
                // rescues. That flip only ran on the NON-speculative arm, so a
                // speculative constant whose real obstruction is a `Prop`-arg
                // `prod` (the `real_maxrN` / `galois_fixedField` shape) regressed
                // to a clean stand-in instead of `KernelVerified`. Try the
                // per-instance flip on the value AND declared type, then the
                // motive-universe bump ladder ON TOP of the flipped value (one
                // term can need both). Monotone and kernel-arbitrated: this fires
                // ONLY after the value already rejected, so a constant KV today is
                // never re-derived, and a wrong flip simply rejects again and the
                // clean-stand-in disposition below is unchanged.
                if try_prod_flip_kv(env, &name, decl_kind, &level_params, &type_, val) {
                    return AddConstResult::KernelVerified;
                }
                // A term can need BOTH a prod flip AND a motive-universe bump:
                // retry the bump ladder on top of the (concrete) flipped value.
                if let Some(flipped_val) = flip_template_poly_prod_per_instance(env, val) {
                    let flipped_ty = flip_template_poly_prod_per_instance(env, &type_);
                    let cand_ty = flipped_ty.as_ref().unwrap_or(&type_);
                    if let Some(result) = retry_speculative_motive_universe(
                        env,
                        &name,
                        decl_kind,
                        &level_params,
                        cand_ty,
                        &flipped_val,
                    ) {
                        return result;
                    }
                }
                log_speculative_capture(
                    &name.to_string(),
                    REJECT_TAG_SPECULATIVE,
                    &err.to_string(),
                );
            }
            // Any other value rejection. Template-polymorphism, the eqmx flip
            // (round 3, ENV-DIRECTED PER-INSTANCE): the value renders every
            // `prod` reference at the monomorphic {1,1} (`Type`) instance, but a
            // `prod P Q` with `P Q : Prop` used at a `Prop` position (`eqmx` and
            // its cascade) needs `prod.{0,0} P Q : Prop`, while a `Type`-level
            // carrier `R1 * R2` in the SAME term must stay `{1,1}`. Retry the
            // value once with EACH template-poly `prod`/`pair`/`prod.rec`
            // instance flipped {1,1}→{0,0} exactly where its two TYPE arguments
            // are provably `Prop` ([`flip_template_poly_prod_per_instance`]); the
            // kernel arbitrates. This fires on ANY rejection shape (the round-2
            // regressions surfaced as `expected Pi(…`/`expected App(…` mismatches
            // that are not always universe-collapse-classified), and it is
            // monotone: it only ever runs on an already-rejected value, and on
            // failure the ORIGINAL error is classified below exactly as before.
            Err(err) => {
                // Flip BOTH the value AND the declared type: a `prod P Q` with
                // `P Q : Prop` in the declared type is equally floored to the
                // ill-formed `{1,1}`, and its ONLY well-formed rendering is
                // `{0,0}` (P : Sort 0 cannot be a `Sort 1` argument), so the flip
                // reconstructs the universe instance Coq intended without
                // touching the statement's structure. Escalating: concrete-arg
                // flip first (round-3 proven), then the binder-sort-aware flip.
                if try_prod_flip_kv(env, &name, decl_kind, &level_params, &type_, val) {
                    return AddConstResult::KernelVerified;
                }
                // Classify the ORIGINAL {1,1} rejection (the flip did not land):
                //   * a PURE universe-LEVEL mismatch (expected/inferred equal
                //     modulo universe levels) is a universe-collapse
                //     reconstruction gap — the importer floored Coq's floating
                //     levels to concrete `u32`, so a value Coq's own kernel
                //     checked lands one level off the declared type. Withhold to
                //     a clean type-only stand-in (no masked-failure taint);
                //   * a conversion STUCK on a native int63/float/array/string
                //     primitive is genuinely out-of-model — a clean stand-in too;
                //   * anything else is a real value failure and stays a masked
                //     seed. Both strict classifiers demand near-byte-identical
                //     structure, so a genuine wrong proof is never laundered.
                if is_universe_collapse_rejection(&err)
                    || is_universe_collapse_rejection_via_whnf(env, &err)
                {
                    universe_recon = Some(err.to_string());
                } else if is_int63_primitive_stuck_rejection(env, &err) {
                    int63_standin = Some(err.to_string());
                } else {
                    value_failed = Some(err.to_string());
                }
            }
        }
    }
    // Fall back to axiom so downstream dependents can still resolve this name.
    // This is NOT a proof-check; if `value_failed` is `Some`, it masks a value
    // the kernel rejected.
    let axiom = Declaration::Axiom {
        name,
        level_params,
        type_,
    };
    match env.add_decl(axiom) {
        // Exactly one of the reconstruction-gap captures can be set (their
        // guards are mutually exclusive); prefer them over the masked fallback.
        Ok(()) => {
            if let Some(msg) = universe_recon {
                AddConstResult::UniverseReconStandin(msg)
            } else if let Some(msg) = int63_standin {
                AddConstResult::Int63PrimitiveStandin(msg)
            } else {
                AddConstResult::AxiomFallback(value_failed)
            }
        }
        Err(err) => AddConstResult::KernelRejected(err.to_string()),
    }
}

/// Decide a value-bearing shard constant whose NAME already exists in the env
/// (a seeded prelude constant or an earlier replay) — the non-inductive-family
/// fall-through that used to die on `add_decl`'s "Duplicate declaration".
///
/// Three honest outcomes, in order:
///
/// 1. **Checked axiom-stub upgrade.** The existing entry is VALUE-FREE and the
///    olean copy brings a value: attempt the kernel's
///    [`Environment::upgrade_axiom_to_checked_decl`] — the value is fully
///    kernel-checked (with the stub removed, so it cannot discharge the stub's
///    trust with itself) and, on success, REPLACES the unproven stub. That is
///    the genuine value landing in the trust lane (the checked counterpart of
///    the olean loader's unchecked `upgrade_axiom_stubs` healing), and it is
///    the only branch here that installs anything: `KernelVerified`.
/// 2. **Twin acceptance.** The olean copy denotes the SAME declaration the env
///    already holds: level-param arity matches and the type matches after
///    positional level renaming (structural-then-def-eq,
///    [`alpha_type_match_against_existing`] — the same discipline as the
///    inductive-family member dedup). For a `Theorem` whose env copy carries a
///    kernel-checked proof, the type match ALONE suffices: by proof
///    irrelevance any two proofs of the same Prop are interchangeable, and the
///    env copy's proof already passed `add_decl`'s check — the olean proof
///    term adds nothing. For `Definition`/`Opaque` the defining VALUE is the
///    meaning of the constant, so when both sides carry values they must also
///    be def-eq (after the same positional level renaming). Acceptance
///    installs NOTHING — the env's checked copy stays authoritative, exactly
///    the family-member dedup's acceptance philosophy.
/// 3. **Fail-closed divergence.** Anything else is a REAL conflict and is
///    rejected with a message naming precisely what differs (arity, type,
///    value, or a failed stub upgrade) — strictly better diagnostics than
///    "Duplicate declaration", and still fail-closed.
///
/// A twin whose BOTH sides are value-free is accepted as
/// `AxiomFallback(None)`, not `KernelVerified`: the env copy is an unproven
/// axiom, so "twin of an axiom" is exactly what the collision-free replay of
/// this valueless row would have minted — never a proof-check verdict.
fn try_accept_seeded_duplicate(
    env: &mut Environment,
    name: &Name,
    decl_kind: DeclKind,
    level_params: &[Name],
    type_: &Expr,
    value: Option<&Expr>,
) -> AddConstResult {
    let Some(existing) = env.get_const(name).cloned() else {
        // Caller checked presence; fail closed rather than panic if it races.
        return AddConstResult::KernelRejected(format!(
            "duplicate of seeded constant {name}: constant vanished during dedup"
        ));
    };

    // (a) Checked axiom-stub upgrade: value-free env copy + value-bearing olean
    // copy. On success the genuine value LANDS (kernel-checked). On failure,
    // keep the typed error for the divergence message below.
    let mut upgrade_failed: Option<String> = None;
    if existing.value.is_none() {
        if let Some(val) = value {
            let decl = build_value_bearing_decl(name, decl_kind, level_params, type_, val);
            match env.upgrade_axiom_to_checked_decl(decl) {
                Ok(()) => return AddConstResult::KernelVerified,
                Err(e) => upgrade_failed = Some(e.to_string()),
            }
        }
    }

    // (b) Twin equivalence: the type must match alpha-insensitively on level
    // params (positional binders) — structural first, kernel is_def_eq
    // fallback; different arity or type is a real divergence.
    match alpha_type_match_against_existing(env, &existing, level_params, type_) {
        AlphaTypeMatch::ArityMismatch => {
            return AddConstResult::KernelRejected(format!(
                "duplicate of seeded constant {name}: level-param arity {} differs from \
                 seeded arity {}",
                level_params.len(),
                existing.level_params.len()
            ));
        }
        AlphaTypeMatch::TypeMismatch => {
            return AddConstResult::KernelRejected(format!(
                "duplicate of seeded constant {name}: type not definitionally equal to the \
                 seeded copy's type"
            ));
        }
        AlphaTypeMatch::Match => {}
    }

    match (existing.value.as_ref(), value) {
        // Env copy carries a kernel-checked value.
        (Some(existing_value), incoming_value) => {
            if decl_kind == DeclKind::Theorem {
                // Proof irrelevance: the seeded proof of this Prop was checked
                // by add_decl when it was installed; the olean proof term proves
                // the same (alpha-matched) statement. Nothing installed — the
                // env copy stays authoritative.
                return AddConstResult::KernelVerified;
            }
            match incoming_value {
                Some(val) => {
                    // Definition/Opaque: the VALUE is the meaning; require it
                    // def-eq to the seeded one under the same positional level
                    // renaming before accepting the twin.
                    let renamed =
                        rename_level_params_positional(val, level_params, &existing.level_params);
                    let values_match = types_equal_ignoring_binder_info(existing_value, &renamed)
                        || TypeChecker::new(env).is_def_eq(existing_value, &renamed);
                    if values_match {
                        AddConstResult::KernelVerified
                    } else {
                        AddConstResult::KernelRejected(format!(
                            "duplicate of seeded constant {name}: value not definitionally \
                             equal to the seeded copy's value"
                        ))
                    }
                }
                // Olean copy is valueless while the env copy is checked and
                // value-bearing: the env copy is strictly stronger; accept it
                // as authoritative (nothing installed).
                None => AddConstResult::KernelVerified,
            }
        }
        // Env copy is VALUE-FREE and the olean value failed the checked
        // upgrade: fail closed with the real kernel error — accepting the twin
        // on type match alone would launder the unproven stub into a
        // KernelVerified verdict.
        (None, Some(_)) => {
            let err =
                upgrade_failed.unwrap_or_else(|| "checked upgrade was not attempted".to_string());
            AddConstResult::KernelRejected(format!(
                "duplicate of seeded constant {name}: seeded copy is value-free and the \
                 checked stub upgrade failed: {}",
                truncate_diagnostic(&err)
            ))
        }
        // Both sides value-free: a twin of the seeded axiom. Registering this
        // row without the collision would have minted AxiomFallback(None) —
        // mint exactly that, never a proof-check verdict.
        (None, None) => AddConstResult::AxiomFallback(None),
    }
}

/// Decide a valueless `Axiom`/`Quot` shard row whose NAME already exists in
/// the env — the axiom-kind counterpart of [`try_accept_seeded_duplicate`],
/// which [`reconstruct_and_replay_one`]'s Axiom/Quot arm used to bypass
/// straight into `add_decl`'s blanket "Duplicate declaration". In practice
/// these are the foundational seeds every olean restates: `Quot`/`Quot.mk`/
/// `Quot.lift`/`Quot.ind` and `sorryAx`/`Classical.choice` (Init.Prelude),
/// `Quot.sound`/`propext` (Init.Core).
///
/// An axiom row carries no value, so the twin test is TYPE-ONLY: level-param
/// arity plus the alpha-insensitive type match
/// ([`alpha_type_match_against_existing`], structural-then-def-eq — the same
/// discipline as the family-member and seeded-def dedups). Acceptance
/// installs NOTHING and mints `AxiomAccepted` — exactly the verdict the
/// collision-free replay of this valueless row would have produced, never a
/// proof-check verdict (when the env copy is value-bearing it is strictly
/// stronger, and the row's own claim is still only an axiom claim).
/// Divergence fails closed with a message naming precisely what differs.
fn try_accept_seeded_axiom_twin(
    env: &Environment,
    name: &Name,
    level_params: &[Name],
    type_: &Expr,
) -> AddConstResult {
    let Some(existing) = env.get_const(name) else {
        // Caller checked presence; fail closed rather than panic if it races.
        return AddConstResult::KernelRejected(format!(
            "duplicate of seeded constant {name}: constant vanished during dedup"
        ));
    };
    match alpha_type_match_against_existing(env, existing, level_params, type_) {
        AlphaTypeMatch::ArityMismatch => AddConstResult::KernelRejected(format!(
            "duplicate of seeded constant {name}: level-param arity {} differs from \
             seeded arity {}",
            level_params.len(),
            existing.level_params.len()
        )),
        AlphaTypeMatch::TypeMismatch => AddConstResult::KernelRejected(format!(
            "duplicate of seeded constant {name}: axiom type not definitionally equal \
             to the seeded copy's type"
        )),
        AlphaTypeMatch::Match => AddConstResult::AxiomAccepted,
    }
}

/// Register a value-bearing Lean `unsafe def` TYPE-ONLY as a trusted-context
/// axiom-shaped declaration, mark it unsafe in the env, and mint
/// [`AddConstResult::UnsafeAccepted`].
///
/// SOUNDNESS: zero kernel-acceptance change — the `Declaration::Axiom`
/// installed here is byte-identical to what the masked `AxiomFallback` path
/// installs today for the same row (the kernel checks the TYPE; the unsafe
/// value is never checked), so no new term becomes derivable. Only the
/// classification changes (`UnsafeAccepted`: excluded from the KernelVerified
/// numerator, not a failure, no masked-taint seed), matching Lean's own
/// semantics for unsafe defs. `env.mark_unsafe` records the flag so strict
/// checkers (`TypeChecker::set_allow_unsafe(false)`) reject references to it —
/// Lean's structural bar; the default replay allows them, exactly like Lean's
/// permissive unsafe mode.
fn accept_unsafe_definition_type_only(
    env: &mut Environment,
    reconstructed: ReconstructedConstant,
) -> AddConstResult {
    let ReconstructedConstant {
        decl_name,
        level_params,
        type_expr,
        ..
    } = reconstructed;
    if env.get_const(&decl_name).is_some() {
        // Name already installed (a prelude seed or an earlier replay): decide
        // the duplicate via the TYPE-ONLY twin discipline. Acceptance is still
        // the unsafe lane's verdict (never KernelVerified); divergence fails
        // closed with the twin path's precise rejection.
        return match try_accept_seeded_axiom_twin(env, &decl_name, &level_params, &type_expr) {
            AddConstResult::AxiomAccepted => {
                env.mark_unsafe(decl_name);
                AddConstResult::UnsafeAccepted
            }
            other => other,
        };
    }
    let axiom = Declaration::Axiom {
        name: decl_name.clone(),
        level_params,
        type_: type_expr,
    };
    match env.add_decl(axiom) {
        Ok(()) => {
            env.mark_unsafe(decl_name);
            AddConstResult::UnsafeAccepted
        }
        Err(err) => AddConstResult::KernelRejected(err.to_string()),
    }
}

fn seed_constant_for_recheck(
    env: &mut Environment,
    name: &str,
    reader: &ShardReader,
    constant: &MathverseConstantHeader,
    policy: InductiveReplayPolicy,
) -> Option<AddConstResult> {
    let decl_name = Name::from_string(name);
    if env.get_const(&decl_name).is_some() {
        return None;
    }

    // Seeds are foundational prerequisites installed before the recheck taint
    // set is meaningful; the speculative-value fail-closed still applies via the
    // profile bit in `try_add_decl` (no taint-graph pre-check needed here).
    Some(try_add_constant(env, name, reader, constant, policy, false))
}

/// Verify all constants in a shard using incremental environment loading.
///
/// Constants are topologically sorted by dependency order, then each is
/// reconstructed from the shard's FlatExpr arena and added to a shared
/// `Environment` via `add_decl()`.
pub fn verify_shard_incremental(reader: &ShardReader) -> IncrementalVerifyReport {
    verify_shard_incremental_with_env(reader, Environment::new())
}

/// Verify only changed constants and their downstream dependents.
///
/// This computes the affected closure from `changed_names`, seeds unchanged
/// prerequisites into a fresh environment using checked declaration replay, and
/// kernel-checks only the affected slice. Inductive-family skeleton seeds use
/// the same checked replay and fail-closed behavior as full incremental
/// verification.
pub fn verify_shard_incremental_recheck<I, S>(
    reader: &ShardReader,
    changed_names: I,
) -> IncrementalVerifyReport
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    verify_shard_incremental_recheck_with_env(reader, changed_names, Environment::new())
}

/// Variant of [`verify_shard_incremental`] that starts from a caller-supplied
/// environment.
///
/// Shards whose constants reference prelude names (`Nat`, `True`, `Eq`, …)
/// cannot be verified against an empty `Environment::new()` because those
/// names are registered by the prelude init routines rather than shipped in
/// the shard itself. End-to-end tests that round-trip a kernel-built shard
/// should call this with `Environment::try_with_prelude()`; the plain entry
/// point preserves the historical "empty env" behavior for shards that
/// carry all their dependencies internally. See #3576.
pub fn verify_shard_incremental_with_env(
    reader: &ShardReader,
    initial_env: Environment,
) -> IncrementalVerifyReport {
    run_incremental_over_reader(reader, initial_env, InductiveReplayPolicy::default()).1
}

/// Topologically order every constant in `reader` and replay it into `env`.
///
/// Shared core of both the per-shard verifier and the corpus verifier: the
/// corpus path passes a [`ShardReader`] that wraps the merged arenas of the
/// whole library (see [`verify_corpus_incremental`]), so the dependency graph
/// and replay are identical — only the arena scope differs.
fn run_incremental_over_reader(
    reader: &ShardReader,
    initial_env: Environment,
    policy: InductiveReplayPolicy,
) -> (Environment, IncrementalVerifyReport) {
    let start = Instant::now();
    let total = reader.constants.len();

    let dep_graph = build_dependency_graph(reader);
    let topo = topological_sort(&dep_graph);

    let mut env = initial_env;
    let mut kernel_verified = 0usize;
    let mut axiom_accepted = 0usize;
    let mut unsafe_accepted = 0usize;
    let mut axiom_fallback = 0usize;
    let mut axiom_fallback_names: Vec<(String, String)> = Vec::new();
    let mut family_standins: Vec<(String, String)> = Vec::new();
    let mut standin_blocked_fallbacks: Vec<(String, String)> = Vec::new();
    let mut failed = 0usize;
    let mut reconstruct_failed = 0usize;
    let inductive_registered = 0usize;
    let mut failures: Vec<(String, String)> = Vec::new();
    let mut kernel_verified_names: Vec<String> = Vec::new();
    let mut discharged_axiom_names: Vec<String> = Vec::new();

    let name_to_idx: HashMap<&str, usize> = reader
        .constants
        .iter()
        .enumerate()
        .filter_map(|(i, c)| {
            reader
                .strings
                .get(c.name_idx as usize)
                .map(|s| (s.as_str(), i))
        })
        .collect();

    // UNSAFE mutual definitions genuinely reference their cycle siblings —
    // Lean performs no termination/positivity checking on `unsafe def`s and
    // registers the mutual group without value-checking — so a dependency
    // CYCLE among them is EXPECTED, not a shard defect (e.g. the compiled
    // `Lean.Compiler.LCNF.eqAlt/eqCases/eqFunDecl/eqImp` block and
    // `Lean.Meta.FindSplitImpl.visit`, `DefinitionSafety.unsafe` per `lean`).
    // Route unsafe-def cycle members through the ordinary replay AFTER every
    // orderable constant: `try_add_constant` registers a value-bearing unsafe
    // def TYPE-ONLY (`accept_unsafe_definition_type_only`), which is
    // order-independent because the cyclic value is never kernel-checked —
    // exactly Lean's own treatment. SAFE cycle members keep failing closed
    // below ("dependency cycle"): a safe declaration with a genuinely cyclic
    // value cannot have come from a Lean kernel, so the fail-closed verdict
    // is the honest one (and a spurious graph cycle among safe decls is a
    // dep-graph bug to fix, not to launder).
    let cyclic_unsafe: HashSet<&String> = topo
        .cyclic
        .iter()
        .filter(|name| {
            name_to_idx.get(name.as_str()).is_some_and(|&idx| {
                let c = &reader.constants[idx];
                DeclKind::try_from(c.decl_kind) == Ok(DeclKind::Definition)
                    && c.definition_safety() == Some(clean_olean::DefinitionSafety::Unsafe)
            })
        })
        .collect();
    let cycle_skipped = topo.cyclic.len() - cyclic_unsafe.len();

    // SOUNDNESS (masked-failure taint): a value-bearing decl whose value the
    // kernel REJECTS is registered as an axiom of its stated type by
    // `try_add_decl` (an `AxiomFallback(Some(_))`), so downstream names still
    // resolve. That fabricated axiom is a proof the kernel actively refused. A
    // dependent whose value then typechecks ONLY because it rests on that axiom
    // is NOT kernel-established, yet `add_decl` returns `KernelVerified` for it —
    // and `kernel_verified_names` flows verbatim to the `KernelVerifiedManifest`
    // and is stamped `ImportConfidence::KernelVerified` on the shard. We propagate
    // the taint forward through the dependency graph and WITHHOLD the
    // `KernelVerified` verdict from any constant that transitively depends on a
    // masked-failure fallback (recorded in `failures` for audit). Topological
    // order guarantees every dependency is classified before its dependents, so a
    // single direct-dependency check computes the full transitive taint; the
    // check is skipped entirely when nothing is tainted (the common case).
    let mut masked_tainted: HashSet<String> = HashSet::new();

    // VALUE-LESS STAND-INS present in the env (see
    // `standin_blocked_evidence`): declarations whose source system
    // kernel-checked a value/structure for them but which are registered here
    // TYPE-ONLY for reasons that are NOT evidence of a wrong proof. Members:
    // dump-salvaged `SALVAGED_STAND_IN`-profiled axioms (on acceptance),
    // family-replay stand-ins, forced-type-only rows, and stand-in-blocked
    // fallbacks themselves (their dependents face the same opaque wall).
    // Topological order guarantees the set is complete for every dependent.
    let mut standin_names: HashSet<String> = HashSet::new();
    // Constants whose dependency CONE reaches a stand-in through intermediate
    // constants (forward-propagated; see `propagate_standin_reach` /
    // `standin_blocked_evidence`'s transitive extension).
    let mut standin_reachable: HashSet<String> = HashSet::new();

    for name in topo.order.iter().chain(cyclic_unsafe.iter().copied()) {
        let ci = match name_to_idx.get(name.as_str()) {
            Some(&idx) => idx,
            None => continue,
        };
        let constant = &reader.constants[ci];
        propagate_standin_reach(name, &dep_graph, &standin_names, &mut standin_reachable);
        // A SPECULATIVE value (derived recursor motive universe) whose dependency
        // closure already rests on a masked-failure taint must NOT be installed:
        // its value is only taint-ELIGIBLE because we optimistically translated
        // it, and installing it both withholds the value from KernelVerified AND
        // extends the taint graph (value edges the value-less baseline lacked),
        // enlarging the cascade. Force it type-only — a clean axiom, byte-
        // identical to the pre-derivation baseline (where the value never
        // translated). Topological order guarantees the taint set is complete for
        // this name's dependencies. Non-speculative constants are unaffected.
        let force_type_only = !masked_tainted.is_empty()
            && constant
                .profile()
                .has_bit(crate::types::AxiomProfile::SPECULATIVE_MOTIVE.0)
            && dep_graph
                .get(name)
                .is_some_and(|deps| deps.iter().any(|d| masked_tainted.contains(d)));
        if force_type_only {
            log_forced_type_only_capture(name, dep_graph.get(name), &masked_tainted);
        }
        match try_add_constant(&mut env, name, reader, constant, policy, force_type_only) {
            AddConstResult::KernelVerified => {
                if !masked_tainted.is_empty()
                    && dep_graph
                        .get(name)
                        .is_some_and(|deps| deps.iter().any(|d| masked_tainted.contains(d)))
                {
                    // Rests transitively on a masked-failure axiom fallback:
                    // trust-withheld, never stamped KernelVerified.
                    masked_tainted.insert(name.clone());
                    failed += 1;
                    failures.push((
                        name.clone(),
                        "trust-withheld: value typechecks only against a masked-failure \
                         axiom fallback in its dependency closure (proof not kernel-established)"
                            .to_string(),
                    ));
                } else {
                    kernel_verified += 1;
                    kernel_verified_names.push(name.clone());
                }
            }
            AddConstResult::AxiomDischarged => {
                // A value-less axiom whose stated type was PROVEN by a hand-built
                // kernel term (`axiom_discharge`). The proof is self-contained
                // (only foundational `eq`/`eq_refl` + the imported binders — no
                // corpus deps), so the masked-taint guard below can never fire;
                // it is applied anyway to stay identical to the KernelVerified
                // arm (fail-closed if some dependency were ever tainted).
                if !masked_tainted.is_empty()
                    && dep_graph
                        .get(name)
                        .is_some_and(|deps| deps.iter().any(|d| masked_tainted.contains(d)))
                {
                    masked_tainted.insert(name.clone());
                    failed += 1;
                    failures.push((
                        name.clone(),
                        "trust-withheld: discharged proof rests on a masked-failure \
                         axiom fallback in its dependency closure"
                            .to_string(),
                    ));
                } else {
                    kernel_verified += 1;
                    kernel_verified_names.push(name.clone());
                    discharged_axiom_names.push(name.clone());
                }
            }
            AddConstResult::AxiomAccepted => {
                axiom_accepted += 1;
                // A dump-salvaged stand-in axiom is now present in the env: its
                // value-less-ness is a reconstruction gap, not a value-free Coq
                // axiom (see `AxiomProfile::SALVAGED_STAND_IN`), so it joins the
                // stand-in set the rejection classification consults. The env
                // copy must actually be VALUE-LESS: a twin-accepted duplicate
                // of a real value-bearing constant CAN delta-unfold and is no
                // conversion wall.
                if constant
                    .profile()
                    .has_bit(crate::types::AxiomProfile::SALVAGED_STAND_IN.0)
                    && env
                        .get_const(&Name::from_string(name))
                        .is_none_or(|c| c.value.is_none())
                {
                    standin_names.insert(name.clone());
                }
            }
            AddConstResult::UnsafeAccepted => {
                // Trusted-context unsafe def: type-only registration, never
                // KernelVerified, not a failure, and NO taint seed (only other
                // unsafe decls can reference it — upstream-kernel enforced).
                unsafe_accepted += 1;
            }
            AddConstResult::AxiomFallback(opt) => {
                axiom_fallback += 1;
                match opt {
                    // A value the kernel rejected THROUGH a value-less stand-in
                    // (direct dep or reached transitively in the dependency
                    // cone): a reconstruction gap, not a refused proof (see
                    // `standin_blocked_evidence`). Clean type-only fallback —
                    // audited on its own report lane and the env-gated capture
                    // log, NEVER a taint seed. The type-only registration is
                    // itself the same opaque wall for dependents, so the name
                    // joins the stand-in set (the clean-direction mirror of how
                    // masked taint propagates through dependents).
                    Some(err) => {
                        if let Some(wall) = standin_blocked_evidence(
                            name,
                            &dep_graph,
                            &masked_tainted,
                            &standin_names,
                            &standin_reachable,
                        ) {
                            log_speculative_capture(
                                name,
                                REJECT_TAG_STANDIN_BLOCKED,
                                &format!("[{}] {err}", wall.as_str()),
                            );
                            standin_blocked_fallbacks.push((name.clone(), err));
                            standin_names.insert(name.clone());
                        } else {
                            log_masked_seed_capture(
                                name,
                                &err,
                                &dep_graph,
                                &masked_tainted,
                                &standin_names,
                            );
                            axiom_fallback_names.push((name.clone(), err));
                            // Seed the taint: this name is a fabricated axiom
                            // masking a rejected proof; every transitive
                            // dependent is withheld above.
                            masked_tainted.insert(name.clone());
                        }
                    }
                    None => {
                        // A forced-type-only row (speculative value withheld):
                        // a value-less registration of a Coq-checked value —
                        // the stand-in trust shape.
                        //
                        // ALSO: a `SPECULATIVE_MOTIVE` value the kernel REJECTED
                        // (try_add_decl discarded the wrong guess and installed
                        // the stated type as a clean axiom — `value_failed`
                        // stayed `None`, so no masked-failure taint). Its
                        // value-less registration is the SAME opaque wall for
                        // dependents as a forced-type-only row, so it joins the
                        // stand-in set (the clean-direction mirror of how a
                        // masked seed propagates): a dependent that needs the
                        // withheld value then classifies STANDIN_BLOCKED rather
                        // than masked-tainted. This is what closes the cascade
                        // for the instantiated-module (functor-application)
                        // enumeration — the functor members are precisely the
                        // walls their siblings/dependents cannot reduce through.
                        if force_type_only
                            || constant
                                .profile()
                                .has_bit(crate::types::AxiomProfile::SPECULATIVE_MOTIVE.0)
                        {
                            standin_names.insert(name.clone());
                        }
                    }
                }
            }
            // A family-replay stand-in: clean statement-only fallback (see
            // `try_inductive_family_standin`) — counted with the value-less
            // fallbacks, never a taint seed; the superseded replay failure is
            // recorded for diagnostics (and in the env-gated capture log).
            // Joins the stand-in set: the family had checked structure in its
            // source system that this env cannot reduce through.
            AddConstResult::FamilyStandin(superseded) => {
                axiom_fallback += 1;
                family_standins.push((name.clone(), superseded));
                standin_names.insert(name.clone());
            }
            // A value rejected on a PURE universe-LEVEL mismatch (universe-
            // collapse reconstruction gap): clean type-only stand-in, no
            // masked-failure taint. Same trust shape as a stand-in-blocked
            // fallback — statement kernel-checked, value withheld, never
            // KernelVerified — and it is itself the same opaque wall for
            // dependents, so it joins the stand-in set.
            AddConstResult::UniverseReconStandin(msg) => {
                axiom_fallback += 1;
                log_speculative_capture(name, REJECT_TAG_UNIVERSE_STANDIN, &msg);
                standin_blocked_fallbacks.push((name.clone(), msg));
                standin_names.insert(name.clone());
            }
            // A value rejected because conversion is STUCK on a native
            // int63/float/string primitive (`is_int63_primitive_stuck_rejection`):
            // the operation is genuinely OUT-OF-MODEL for Clean's kernel (an
            // OCaml machine op Coq dumps as a value-less axiom), exactly like a
            // `CoFix` coinductive — the proof cannot be re-checked here. Clean
            // type-only stand-in, no masked-failure taint: same trust shape as
            // the universe-collapse / stand-in-blocked fallbacks (statement
            // kernel-checked, value withheld, never KernelVerified), and it is
            // itself the same opaque wall for dependents, so it joins the
            // stand-in set (a dependent that reduces through the withheld value
            // then classifies STANDIN_BLOCKED rather than masked-tainted).
            AddConstResult::Int63PrimitiveStandin(msg) => {
                axiom_fallback += 1;
                log_speculative_capture(name, REJECT_TAG_INT63_STANDIN, &msg);
                standin_blocked_fallbacks.push((name.clone(), msg));
                standin_names.insert(name.clone());
            }
            AddConstResult::ReconstructFailed(msg) => {
                reconstruct_failed += 1;
                failures.push((name.clone(), msg));
            }
            AddConstResult::KernelRejected(msg) => {
                failed += 1;
                failures.push((name.clone(), msg));
            }
        }
    }

    for name in &topo.cyclic {
        // Unsafe-def cycle members were processed through the replay above
        // (type-only registration); only the residual (safe) members fail.
        if !cyclic_unsafe.contains(name) {
            failures.push((name.clone(), "dependency cycle".to_string()));
        }
    }

    let report = IncrementalVerifyReport {
        total,
        kernel_verified,
        axiom_accepted,
        unsafe_accepted,
        axiom_fallback,
        axiom_fallback_names,
        family_standins,
        standin_blocked_fallbacks,
        failed,
        cycle_skipped,
        reconstruct_failed,
        inductive_registered,
        seeded_checked: 0,
        seeded_unchecked: 0,
        failures,
        kernel_verified_names,
        discharged_axiom_names,
        elapsed_secs: start.elapsed().as_secs_f64(),
        heartbeat_escalated_recovered: 0,
    };
    (env, report)
}

/// Re-verify a whole merged corpus in ONE prelude-seeded kernel environment.
///
/// `library` must already hold every shard merged into its global arenas (each
/// shard added via [`MathverseLibrary::load_shard`]). This builds the global
/// dependency graph over ALL merged constants — so a constant in one shard that
/// references one defined in another is now an in-graph edge — topologically
/// sorts it, and replays each constant into the single shared `initial_env`
/// (which the caller seeds with the kernel prelude via
/// `Environment::try_with_prelude`). Cross-shard dependencies therefore resolve,
/// lifting the cap that single-shard re-verification hit when a constant's type
/// or value referenced a constant living in a different size-split shard.
///
/// Reconstruction and replay go through the exact same path
/// ([`reconstruct_and_replay_one`] / [`try_add_constant`]) as the per-shard
/// verifier, so the two cannot drift. The returned report's counts are global.
pub fn verify_corpus_incremental(
    library: &MathverseLibrary,
    initial_env: Environment,
) -> IncrementalVerifyReport {
    let merged = library.as_merged_reader();
    run_incremental_over_reader(&merged, initial_env, InductiveReplayPolicy::default()).1
}

/// Like [`verify_corpus_incremental`], but also returns the populated
/// [`Environment`] after the dependency-ordered replay.
///
/// The replay is the identical code path ([`run_incremental_over_reader`]), so
/// the report is the same; the only difference is the env is handed back rather
/// than dropped. Consumers that need to run further *sound* kernel queries over
/// the verified corpus — e.g. the kernel-confirmed tree-score
/// ([`crate::graduate::tree_score`]), which needs `whnf`/`is_def_eq` to be able
/// to δ-unfold corpus-defined constants — build a [`clean_kernel::tc::TypeChecker`]
/// over this env. Every constant in it was installed through checked `add_decl`
/// (theorem/definition/opaque), checked `add_inductive`, or `add_decl(Axiom)`
/// for value-less carriers — the kernel never accepted an unchecked value, so
/// the env is exactly the kernel-trusted view of the corpus.
pub fn verify_corpus_incremental_with_env(
    library: &MathverseLibrary,
    initial_env: Environment,
) -> (Environment, IncrementalVerifyReport) {
    verify_corpus_incremental_with_env_policy(
        library,
        initial_env,
        InductiveReplayPolicy::default(),
    )
}

/// Like [`verify_corpus_incremental_with_env`], but explicitly selects the
/// [`InductiveReplayPolicy`] for family replay.
///
/// `.olean`-sourced corpora (the Mathlib KV stamp) MUST pass
/// [`InductiveReplayPolicy::LeanFaithful`] so Clean's non-Lean-faithful generated
/// convenience definitions (`noConfusion`/`noConfusionType`/`casesOn`/…) do not
/// shadow the shard's Lean-stored spellings and spuriously fail their downstream
/// re-checks on universe/shape mismatches. See [`InductiveReplayPolicy`].
pub fn verify_corpus_incremental_with_env_policy(
    library: &MathverseLibrary,
    initial_env: Environment,
    policy: InductiveReplayPolicy,
) -> (Environment, IncrementalVerifyReport) {
    let merged = library.as_merged_reader();
    run_incremental_over_reader(&merged, initial_env, policy)
}

/// Variant of [`verify_shard_incremental_recheck`] that starts from a
/// caller-supplied environment.
///
/// This is intended for dependency-aware re-checking after a change:
/// unchanged prerequisites inside the shard are replayed through checked
/// declaration registration, while `initial_env` supplies anything outside
/// the shard (for example, the prelude).
pub fn verify_shard_incremental_recheck_with_env<I, S>(
    reader: &ShardReader,
    changed_names: I,
    initial_env: Environment,
) -> IncrementalVerifyReport
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    let start = Instant::now();
    let plan = plan_incremental_recheck(reader, changed_names);
    let total = plan.recheck_order.len() + plan.cycle_skipped.len();

    let name_to_idx: HashMap<&str, usize> = reader
        .constants
        .iter()
        .enumerate()
        .filter_map(|(i, c)| {
            reader
                .strings
                .get(c.name_idx as usize)
                .map(|s| (s.as_str(), i))
        })
        .collect();

    let mut env = initial_env;
    // The dependency-aware recheck path is not the `.olean` stamp; it keeps the
    // historical generate-aux behavior.
    let policy = InductiveReplayPolicy::default();
    let mut failures = Vec::new();
    let mut seeded_checked = 0usize;
    let seeded_unchecked = 0usize;
    // SOUNDNESS (masked-failure taint): mirror `run_incremental_over_reader` —
    // a masked-failure axiom fallback (a value the kernel REJECTED, registered as
    // an axiom) must not have its taint laundered into a `KernelVerified` verdict
    // on any transitive dependent. A masked failure can appear both while SEEDING
    // prerequisites and in the recheck loop, so we seed the taint set from both.
    let dep_graph = build_dependency_graph(reader);
    let mut masked_tainted: HashSet<String> = HashSet::new();
    // Mirror of the topo-order loop's stand-in set (see
    // `run_incremental_over_reader` / `standin_blocked_evidence`); a
    // stand-in can appear both while SEEDING prerequisites and in the recheck
    // loop, so both phases feed it — as does the transitive reach set.
    let mut standin_names: HashSet<String> = HashSet::new();
    let mut standin_reachable: HashSet<String> = HashSet::new();
    for name in plan.seed_order.iter().chain(plan.seed_cyclic.iter()) {
        if let Some(&idx) = name_to_idx.get(name.as_str()) {
            let seed_constant = &reader.constants[idx];
            propagate_standin_reach(name, &dep_graph, &standin_names, &mut standin_reachable);
            match seed_constant_for_recheck(&mut env, name, reader, seed_constant, policy) {
                // All success verdicts register the prerequisite's declaration
                // into the env through checked replay; the seed step does not
                // distinguish proof-checked from axiom-/unsafe-accepted.
                Some(AddConstResult::AxiomAccepted) => {
                    seeded_checked += 1;
                    // Dump-salvaged stand-in prerequisite (see the topo loop);
                    // only when the env copy is genuinely value-less.
                    if seed_constant
                        .profile()
                        .has_bit(crate::types::AxiomProfile::SALVAGED_STAND_IN.0)
                        && env
                            .get_const(&Name::from_string(name))
                            .is_none_or(|c| c.value.is_none())
                    {
                        standin_names.insert(name.clone());
                    }
                }
                Some(
                    AddConstResult::KernelVerified
                    | AddConstResult::UnsafeAccepted
                    | AddConstResult::AxiomDischarged,
                ) => {
                    seeded_checked += 1;
                }
                Some(AddConstResult::AxiomFallback(opt)) => {
                    seeded_checked += 1;
                    if opt.is_some() {
                        if standin_blocked_evidence(
                            name,
                            &dep_graph,
                            &masked_tainted,
                            &standin_names,
                            &standin_reachable,
                        )
                        .is_some()
                        {
                            // Stand-in-blocked seed rejection: clean type-only
                            // prerequisite, no taint (see the topo loop); it is
                            // itself a stand-in wall for the recheck slice.
                            standin_names.insert(name.clone());
                        } else {
                            // A seeded prerequisite whose value the kernel rejected:
                            // seed the taint so dependents in the recheck loop are withheld.
                            masked_tainted.insert(name.clone());
                        }
                    }
                }
                // A family-replay stand-in prerequisite: registered like a
                // value-less fallback, never a taint seed — and a stand-in
                // wall for the recheck slice.
                Some(AddConstResult::FamilyStandin(_)) => {
                    seeded_checked += 1;
                    standin_names.insert(name.clone());
                }
                // A universe-collapse reconstruction-gap prerequisite: same
                // clean value-less stand-in shape as `FamilyStandin`.
                Some(AddConstResult::UniverseReconStandin(_)) => {
                    seeded_checked += 1;
                    standin_names.insert(name.clone());
                }
                // A native-primitive-stuck reconstruction-gap prerequisite: same
                // clean value-less stand-in shape as `UniverseReconStandin`.
                Some(AddConstResult::Int63PrimitiveStandin(_)) => {
                    seeded_checked += 1;
                    standin_names.insert(name.clone());
                }
                Some(AddConstResult::ReconstructFailed(msg)) => {
                    failures.push((name.clone(), format!("seed reconstruct failed: {msg}")));
                }
                Some(AddConstResult::KernelRejected(msg)) => {
                    failures.push((name.clone(), format!("seed rejected: {msg}")));
                }
                None => {}
            }
        }
    }

    let mut kernel_verified = 0usize;
    let mut axiom_accepted = 0usize;
    let mut unsafe_accepted = 0usize;
    let mut axiom_fallback = 0usize;
    let mut axiom_fallback_names: Vec<(String, String)> = Vec::new();
    let mut family_standins: Vec<(String, String)> = Vec::new();
    let mut standin_blocked_fallbacks: Vec<(String, String)> = Vec::new();
    let mut kernel_verified_names: Vec<String> = Vec::new();
    let mut discharged_axiom_names: Vec<String> = Vec::new();
    let mut failed = 0usize;
    let mut reconstruct_failed = 0usize;
    let inductive_registered = 0usize;

    for name in &plan.recheck_order {
        let Some(&idx) = name_to_idx.get(name.as_str()) else {
            continue;
        };
        let constant = &reader.constants[idx];
        propagate_standin_reach(name, &dep_graph, &standin_names, &mut standin_reachable);
        // See the topo-order loop: a speculative value resting on taint is forced
        // type-only (clean axiom = baseline) rather than installed as a
        // taint-eligible, taint-graph-extending value.
        let force_type_only = !masked_tainted.is_empty()
            && constant
                .profile()
                .has_bit(crate::types::AxiomProfile::SPECULATIVE_MOTIVE.0)
            && dep_graph
                .get(name)
                .is_some_and(|deps| deps.iter().any(|d| masked_tainted.contains(d)));
        if force_type_only {
            log_forced_type_only_capture(name, dep_graph.get(name), &masked_tainted);
        }
        match try_add_constant(&mut env, name, reader, constant, policy, force_type_only) {
            AddConstResult::KernelVerified => {
                if !masked_tainted.is_empty()
                    && dep_graph
                        .get(name)
                        .is_some_and(|deps| deps.iter().any(|d| masked_tainted.contains(d)))
                {
                    masked_tainted.insert(name.clone());
                    failed += 1;
                    failures.push((
                        name.clone(),
                        "trust-withheld: value typechecks only against a masked-failure \
                         axiom fallback in its dependency closure (proof not kernel-established)"
                            .to_string(),
                    ));
                } else {
                    kernel_verified += 1;
                    kernel_verified_names.push(name.clone());
                }
            }
            AddConstResult::AxiomDischarged => {
                // Value-less axiom discharged to a hand-built kernel proof
                // (`axiom_discharge`) — counted with KernelVerified, recorded
                // for audit. Self-contained proof (foundational eq only), so
                // the masked-taint guard mirrors the KernelVerified arm.
                if !masked_tainted.is_empty()
                    && dep_graph
                        .get(name)
                        .is_some_and(|deps| deps.iter().any(|d| masked_tainted.contains(d)))
                {
                    masked_tainted.insert(name.clone());
                    failed += 1;
                    failures.push((
                        name.clone(),
                        "trust-withheld: discharged proof rests on a masked-failure \
                         axiom fallback in its dependency closure"
                            .to_string(),
                    ));
                } else {
                    kernel_verified += 1;
                    kernel_verified_names.push(name.clone());
                    discharged_axiom_names.push(name.clone());
                }
            }
            AddConstResult::AxiomAccepted => {
                axiom_accepted += 1;
                // Dump-salvaged stand-in axiom (see run_incremental_over_reader);
                // only when the env copy is genuinely value-less.
                if constant
                    .profile()
                    .has_bit(crate::types::AxiomProfile::SALVAGED_STAND_IN.0)
                    && env
                        .get_const(&Name::from_string(name))
                        .is_none_or(|c| c.value.is_none())
                {
                    standin_names.insert(name.clone());
                }
            }
            AddConstResult::UnsafeAccepted => {
                // Trusted-context unsafe def: never KernelVerified, not a
                // failure, and NO taint seed (see run_incremental_over_reader).
                unsafe_accepted += 1;
            }
            AddConstResult::AxiomFallback(opt) => {
                axiom_fallback += 1;
                match opt {
                    // Stand-in-blocked value rejection (direct or transitive
                    // wall): clean type-only fallback, no taint seed; the name
                    // joins the stand-in set (see run_incremental_over_reader
                    // for the full rationale).
                    Some(err) => {
                        if let Some(wall) = standin_blocked_evidence(
                            name,
                            &dep_graph,
                            &masked_tainted,
                            &standin_names,
                            &standin_reachable,
                        ) {
                            log_speculative_capture(
                                name,
                                REJECT_TAG_STANDIN_BLOCKED,
                                &format!("[{}] {err}", wall.as_str()),
                            );
                            standin_blocked_fallbacks.push((name.clone(), err));
                            standin_names.insert(name.clone());
                        } else {
                            log_masked_seed_capture(
                                name,
                                &err,
                                &dep_graph,
                                &masked_tainted,
                                &standin_names,
                            );
                            axiom_fallback_names.push((name.clone(), err));
                            masked_tainted.insert(name.clone());
                        }
                    }
                    None => {
                        // Forced-type-only row: value-less registration of a
                        // source-checked value — the stand-in trust shape.
                        if force_type_only {
                            standin_names.insert(name.clone());
                        }
                    }
                }
            }
            // Family-replay stand-in: clean statement-only fallback, no taint
            // (see `try_inductive_family_standin`); a stand-in wall for
            // dependents.
            AddConstResult::FamilyStandin(superseded) => {
                axiom_fallback += 1;
                family_standins.push((name.clone(), superseded));
                standin_names.insert(name.clone());
            }
            // Universe-collapse reconstruction gap: clean type-only stand-in,
            // no taint (see run_incremental_over_reader for the full rationale).
            AddConstResult::UniverseReconStandin(msg) => {
                axiom_fallback += 1;
                log_speculative_capture(name, REJECT_TAG_UNIVERSE_STANDIN, &msg);
                standin_blocked_fallbacks.push((name.clone(), msg));
                standin_names.insert(name.clone());
            }
            // Native int63/float/string primitive-stuck reconstruction gap:
            // clean type-only stand-in, no taint (see run_incremental_over_reader
            // for the full rationale).
            AddConstResult::Int63PrimitiveStandin(msg) => {
                axiom_fallback += 1;
                log_speculative_capture(name, REJECT_TAG_INT63_STANDIN, &msg);
                standin_blocked_fallbacks.push((name.clone(), msg));
                standin_names.insert(name.clone());
            }
            AddConstResult::ReconstructFailed(msg) => {
                reconstruct_failed += 1;
                failures.push((name.clone(), msg));
            }
            AddConstResult::KernelRejected(msg) => {
                failed += 1;
                failures.push((name.clone(), msg));
            }
        }
    }

    for name in &plan.missing {
        failures.push((name.clone(), "requested constant not found".to_string()));
    }
    for name in &plan.cycle_skipped {
        failures.push((name.clone(), "dependency cycle".to_string()));
    }

    IncrementalVerifyReport {
        total,
        kernel_verified,
        axiom_accepted,
        unsafe_accepted,
        axiom_fallback,
        axiom_fallback_names,
        family_standins,
        standin_blocked_fallbacks,
        failed,
        cycle_skipped: plan.cycle_skipped.len(),
        reconstruct_failed,
        inductive_registered,
        seeded_checked,
        seeded_unchecked,
        failures,
        kernel_verified_names,
        discharged_axiom_names,
        elapsed_secs: start.elapsed().as_secs_f64(),
        heartbeat_escalated_recovered: 0,
    }
}
