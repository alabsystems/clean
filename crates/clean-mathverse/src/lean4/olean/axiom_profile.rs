// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Comprehensive Lean 4 axiom profile computation with transitive closure.
//!
//! Extends the basic per-constant profile from [`crate::lean4::olean::alpha::compute_axiom_profile`]
//! with transitive dependency analysis. If constant A depends on constant B
//! which uses `Classical.choice`, then A also receives `LEAN4_CHOICE`.
//!
//! Axiom classes detected:
//! - **CHOICE** — `Classical.choice` (also sets CLASSICAL alias)
//! - **QUOT** — `Quot`, `Quot.mk`, `Quot.ind`, `Quot.lift`, `Quot.sound`
//! - **PROP_EXT** — `propext`
//! - **FUNC_EXT** — `funext`
//! - **LEM** — `Classical.em`

use std::collections::HashMap;

use clean_kernel::flat::FlatExpr;
use clean_olean::expr::ParsedExpr;
use clean_olean::module::{ConstantKind, ParsedConstant, ParsedModule};

use crate::lean4::olean::alpha::extract_deps;
use crate::types::{AxiomProfile, MathverseConstantHeader};

// ---------------------------------------------------------------------------
// Well-known axiom names
// ---------------------------------------------------------------------------

/// Well-known Lean 4 axiom names and their corresponding profile bits.
const WELL_KNOWN_AXIOMS: &[(&str, AxiomProfile)] = &[
    (
        "Classical.choice",
        AxiomProfile(AxiomProfile::CHOICE.0 | AxiomProfile::CLASSICAL.0),
    ),
    ("Classical.em", AxiomProfile::LEM),
    ("propext", AxiomProfile::PROP_EXT),
    ("funext", AxiomProfile::FUNC_EXT),
    ("Quot", AxiomProfile::QUOT),
    ("Quot.mk", AxiomProfile::QUOT),
    ("Quot.ind", AxiomProfile::QUOT),
    ("Quot.lift", AxiomProfile::QUOT),
    ("Quot.sound", AxiomProfile::QUOT),
];

// ---------------------------------------------------------------------------
// Per-constant axiom profile (enhanced)
// ---------------------------------------------------------------------------

/// Compute the axiom profile for a single Lean 4 constant.
///
/// Recognizes well-known axiom names (including `funext`, `Classical.em`,
/// `Quot.sound`) and sets the AXIOMATIZED bit for axiom/opaque kinds.
/// This is the local (non-transitive) profile.
#[must_use]
pub fn compute_lean4_axiom_profile(constant: &ParsedConstant) -> AxiomProfile {
    let mut profile = AxiomProfile::NONE;

    // Check well-known axiom names.
    for &(name, bits) in WELL_KNOWN_AXIOMS {
        if constant.name == name {
            profile |= bits;
        }
    }

    // Axioms and opaques get the AXIOMATIZED bit.
    match constant.kind {
        ConstantKind::Axiom | ConstantKind::Opaque => {
            profile |= AxiomProfile::AXIOMATIZED;
        }
        _ => {}
    }

    profile
}

// ---------------------------------------------------------------------------
// Dependency extraction from ParsedExpr
// ---------------------------------------------------------------------------

/// Extract all constant names referenced in a `ParsedExpr` tree.
///
/// Walks the expression recursively, collecting names from `Const` nodes.
fn extract_const_refs(expr: &ParsedExpr, out: &mut Vec<String>) {
    match expr {
        ParsedExpr::Const(name, _levels) => {
            out.push(name.clone());
        }
        ParsedExpr::App(func, arg) => {
            extract_const_refs(func, out);
            extract_const_refs(arg, out);
        }
        ParsedExpr::Lam(_name, ty, body, _bi) => {
            extract_const_refs(ty, out);
            extract_const_refs(body, out);
        }
        ParsedExpr::ForallE(_name, ty, body, _bi) => {
            extract_const_refs(ty, out);
            extract_const_refs(body, out);
        }
        ParsedExpr::LetE(_name, ty, val, body, _nondep) => {
            extract_const_refs(ty, out);
            extract_const_refs(val, out);
            extract_const_refs(body, out);
        }
        ParsedExpr::MData(inner) => {
            extract_const_refs(inner, out);
        }
        ParsedExpr::Proj(_name, _field, inner) => {
            extract_const_refs(inner, out);
        }
        // BVar, FVar, MVar, Sort, Lit -- leaf nodes with no constant refs.
        _ => {}
    }
}

/// Extract all constant names referenced in a `ParsedConstant` (type + value).
fn extract_constant_deps(constant: &ParsedConstant) -> Vec<String> {
    let mut refs = Vec::new();
    if let Some(type_expr) = &constant.type_ {
        extract_const_refs(type_expr, &mut refs);
    }
    if let Some(val_expr) = &constant.value {
        extract_const_refs(val_expr, &mut refs);
    }
    refs.sort_unstable();
    refs.dedup();
    refs
}

// ---------------------------------------------------------------------------
// Transitive closure
// ---------------------------------------------------------------------------

/// Compute axiom profiles for all constants in a module with transitive closure.
///
/// Algorithm:
/// 1. Compute local profiles for each constant.
/// 2. Build dependency graph from expression references.
/// 3. Propagate profiles transitively: `profile(A) |= profile(B)` for every
///    constant B referenced by A.
///
/// Returns a map from constant name to its transitive axiom profile.
#[must_use]
pub fn compute_transitive_axiom_profiles(module: &ParsedModule) -> HashMap<String, AxiomProfile> {
    // Step 1: local profiles.
    let mut profiles: HashMap<String, AxiomProfile> =
        HashMap::with_capacity(module.constants.len());
    for constant in &module.constants {
        profiles.insert(constant.name.clone(), compute_lean4_axiom_profile(constant));
    }

    // Step 2: dependency graph.
    let mut deps: HashMap<String, Vec<String>> = HashMap::with_capacity(module.constants.len());
    for constant in &module.constants {
        let constant_deps = extract_constant_deps(constant);
        deps.insert(constant.name.clone(), constant_deps);
    }

    // Step 3: propagate transitively (fixed-point iteration).
    // We iterate until no profile changes. This converges because profiles
    // only grow (bits are added, never removed), and there are finitely many
    // bits.
    loop {
        let mut changed = false;
        for constant in &module.constants {
            let dep_names = match deps.get(&constant.name) {
                Some(d) => d.clone(),
                None => continue,
            };
            let mut accumulated = AxiomProfile::NONE;
            for dep_name in &dep_names {
                if let Some(&dep_profile) = profiles.get(dep_name) {
                    accumulated |= dep_profile;
                }
            }
            if let Some(profile) = profiles.get_mut(&constant.name) {
                let before = *profile;
                *profile |= accumulated;
                if *profile != before {
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    profiles
}

/// Compute axiom profiles for all constants across multiple modules with
/// transitive closure.
///
/// Combines constants from all modules into a single dependency graph before
/// propagating profiles.
#[must_use]
pub fn compute_transitive_profiles_multi(
    modules: &[&ParsedModule],
) -> HashMap<String, AxiomProfile> {
    // Collect all constants across modules.
    let total = modules.iter().map(|m| m.constants.len()).sum();
    let mut profiles: HashMap<String, AxiomProfile> = HashMap::with_capacity(total);
    let mut deps: HashMap<String, Vec<String>> = HashMap::with_capacity(total);

    for module in modules {
        for constant in &module.constants {
            profiles
                .entry(constant.name.clone())
                .or_insert_with(|| compute_lean4_axiom_profile(constant));
            deps.entry(constant.name.clone())
                .or_insert_with(|| extract_constant_deps(constant));
        }
    }

    // Fixed-point propagation.
    loop {
        let mut changed = false;
        let names: Vec<String> = deps.keys().cloned().collect();
        for name in &names {
            let dep_names = match deps.get(name) {
                Some(d) => d.clone(),
                None => continue,
            };
            let mut accumulated = AxiomProfile::NONE;
            for dep_name in &dep_names {
                if let Some(&dep_profile) = profiles.get(dep_name) {
                    accumulated |= dep_profile;
                }
            }
            if let Some(profile) = profiles.get_mut(name) {
                let before = *profile;
                *profile |= accumulated;
                if *profile != before {
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    profiles
}

// ---------------------------------------------------------------------------
// Shard-level transitive closure (post-import propagation)
// ---------------------------------------------------------------------------

/// Propagate axiom-profile bits transitively over an *already-lowered* shard.
///
/// # Why this exists
///
/// The per-constant importers ([`compute_lean4_axiom_profile`] /
/// [`crate::lean4::olean::alpha::compute_axiom_profile`]) only set a bit when a
/// constant *is itself* a named axiom (e.g. literally named `Classical.choice`)
/// or has `Axiom`/`Opaque` kind. They do **not** look at dependencies. A theorem
/// that *uses* `Classical.choice` through any chain of intermediate definitions
/// would therefore be written with `AxiomProfile::NONE` — i.e. reported as
/// kernel-pure when it is not. This is the soundness gap the shard header
/// docstring ("transitive closure of all axiom dependencies") promised to close
/// but did not.
///
/// This function repairs the profiles in place by computing the real transitive
/// closure from the flat dependency graph that is already present in the shard
/// (each constant's `type_idx` / `value_idx` reference a `FlatExpr` arena whose
/// `Const` nodes name their dependencies). It runs a **monotone bitset
/// fixed-point**: a constant's profile is unioned with the profiles of every
/// constant it references, repeated until nothing changes. Because bits are only
/// ever added (never removed) and there are at most 64 bits over a finite set of
/// constants, the iteration always terminates — **even in the presence of
/// dependency cycles** (mutual recursion), which a naive recursive DFS would not
/// handle.
///
/// Dependencies that name a constant not present in `constants` (e.g. references
/// into another shard / module that was not part of this conversion) are simply
/// ignored: their bits are not known here and must be supplied by a cross-shard
/// closure pass. Within a single shard this is exact.
///
/// Returns the number of constants whose profile gained at least one bit (useful
/// for audit logging and for proving in tests that the closure actually did
/// work).
#[must_use]
pub fn propagate_shard_axiom_profiles(
    constants: &mut [MathverseConstantHeader],
    exprs: &[FlatExpr],
    strings: &[String],
) -> usize {
    if constants.is_empty() {
        return 0;
    }

    // Map each constant *name* to the indices of constants that define it.
    // A name can be defined by more than one header (duplicate imports across
    // merged modules), so we keep every owner.
    let mut owners_by_name: HashMap<u32, Vec<usize>> = HashMap::with_capacity(constants.len());
    for (idx, c) in constants.iter().enumerate() {
        owners_by_name.entry(c.name_idx).or_default().push(idx);
    }

    // Build the dependency edge list once: edges[i] = constants referenced by i.
    // Dependencies are gathered from both the type and value expression trees.
    let mut edges: Vec<Vec<usize>> = Vec::with_capacity(constants.len());
    for c in constants.iter() {
        let mut dep_name_indices: Vec<u32> = Vec::new();
        collect_dep_name_indices(exprs, c.type_idx, &mut dep_name_indices);
        if c.has_value() {
            collect_dep_name_indices(exprs, c.value_idx, &mut dep_name_indices);
        }
        dep_name_indices.sort_unstable();
        dep_name_indices.dedup();

        let mut dep_consts: Vec<usize> = Vec::new();
        for name_idx in &dep_name_indices {
            if let Some(owner_list) = owners_by_name.get(name_idx) {
                dep_consts.extend_from_slice(owner_list);
            }
        }
        dep_consts.sort_unstable();
        dep_consts.dedup();
        edges.push(dep_consts);
    }

    // Snapshot the local (pre-closure) profiles so we can count real gains and
    // so propagation reads a stable source within each sweep.
    let mut profiles: Vec<AxiomProfile> = constants.iter().map(|c| c.axiom_profile).collect();
    let initial = profiles.clone();

    // Monotone fixed-point. Bits only grow, so this converges; cycle-safe.
    loop {
        let mut changed = false;
        for i in 0..profiles.len() {
            let mut accumulated = AxiomProfile::NONE;
            for &dep in &edges[i] {
                accumulated |= profiles[dep];
            }
            let before = profiles[i];
            let after = before | accumulated;
            if after != before {
                profiles[i] = after;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // Write the closed profiles back and count constants that gained bits.
    let mut upgraded = 0usize;
    for (i, c) in constants.iter_mut().enumerate() {
        if profiles[i] != initial[i] {
            upgraded += 1;
        }
        c.axiom_profile = profiles[i];
    }

    // `strings` is accepted for symmetry with future name-based diagnostics and
    // to let callers pass the shard string table without a second borrow dance;
    // it is intentionally not required for the closure itself.
    let _ = strings;

    upgraded
}

/// Collect the `name_idx` of every `Const` reachable from `root` in the flat
/// arena. Thin wrapper over [`extract_deps`] that appends into a caller buffer.
fn collect_dep_name_indices(exprs: &[FlatExpr], root: u32, out: &mut Vec<u32>) {
    // `extract_deps` already guards against out-of-range roots and cycles in
    // the expression DAG via an internal visited set.
    out.extend(extract_deps(exprs, root));
}

// ---------------------------------------------------------------------------
// Library-level (cross-shard) transitive closure
// ---------------------------------------------------------------------------

/// Close axiom profiles transitively across *every* shard in an
/// already-assembled library, in place.
///
/// # Why this exists
///
/// [`propagate_shard_axiom_profiles`] (run by
/// [`crate::shard::ShardWriter::finalize_axiom_profiles`] on each shard) is exact
/// *within* a single shard: it unions a constant's profile with every dependency
/// whose defining constant is also in that shard. But when the library builder
/// splits at `shard_size_limit`, a constant's dependency can land in a
/// *different* shard. The within-shard pass cannot see that dependency's
/// profile (its `name_idx` is not in the current shard's string table), so it
/// silently skips it. The result is the cross-shard analogue of the original
/// soundness gap: a theorem in shard B that uses `Classical.choice` only through
/// a constant defined in shard A is written with `AxiomProfile::NONE` — reported
/// kernel-pure when it is not.
///
/// This pass repairs that. After all shards are assembled it:
///
/// 1. Builds one global `name -> AxiomProfile` map and one global
///    `name -> {dep names}` graph by merging every shard's
///    [`crate::shard::ShardWriter::constant_axiom_dep_names`]. When the same name
///    is defined in more than one shard (duplicate imports), the profiles are
///    unioned and the dependency sets merged, so the closure is conservative
///    (never under-reports).
/// 2. Runs a **monotone bitset fixed-point** over the *global* graph: a name's
///    profile is unioned with the profiles of all of its dependencies, repeated
///    until nothing changes. Bits are only ever added and there are finitely
///    many (name, bit) pairs, so this terminates — **even with dependency cycles
///    that span shard boundaries**, which a recursive walk could not handle.
/// 3. Writes the globally-closed profiles back into every shard via
///    [`crate::shard::ShardWriter::apply_closed_axiom_profiles`].
///
/// Dependencies that name a constant defined in *no* shard (genuinely external —
/// e.g. references into a library/release that was not part of this build) carry
/// no known bits and are conservatively ignored, exactly as the within-shard
/// pass treats names absent from its shard. That residual gap is cross-*library*
/// (cross-release), not cross-shard, and is out of scope here.
///
/// Returns the total number of constant headers (summed over all shards) whose
/// profile gained at least one bit from the cross-shard step — useful for audit
/// logging and for proving in tests that the closure did real work.
///
/// Convenience wrapper over [`propagate_cross_shard_axiom_profiles_borrowed`]
/// for callers that own a contiguous slice of writers (e.g. tests).
#[must_use]
pub fn propagate_cross_shard_axiom_profiles(writers: &mut [crate::shard::ShardWriter]) -> usize {
    let mut borrowed: Vec<&mut crate::shard::ShardWriter> = writers.iter_mut().collect();
    propagate_cross_shard_axiom_profiles_borrowed(&mut borrowed)
}

/// Cross-shard closure over a set of *borrowed* writers.
///
/// This is the core entry point used by the library builder, where each writer
/// lives inside a larger per-shard record and can only be borrowed mutably (not
/// moved into a contiguous slice). See
/// [`propagate_cross_shard_axiom_profiles`] for the full algorithm description.
#[must_use]
pub fn propagate_cross_shard_axiom_profiles_borrowed(
    writers: &mut [&mut crate::shard::ShardWriter],
) -> usize {
    if writers.is_empty() {
        return 0;
    }

    // Step 1: merge every shard into one global profile map + dependency graph,
    // keyed by name (cross-shard identity is by name, not by local index).
    // Pre-size to the total constant count (an upper bound on distinct names)
    // so neither map rehashes during the merge. Capacity-only; contents unchanged.
    let total_consts: usize = writers.iter().map(|w| w.constant_count()).sum();
    let mut profiles: HashMap<String, AxiomProfile> = HashMap::with_capacity(total_consts);
    let mut deps: HashMap<String, Vec<String>> = HashMap::with_capacity(total_consts);

    for writer in writers.iter() {
        for entry in writer.constant_axiom_dep_names() {
            if entry.name.is_empty() {
                continue;
            }
            // Union local profiles for names defined in multiple shards so the
            // merge can only ever grow a constant's known axiom set.
            profiles
                .entry(entry.name.clone())
                .and_modify(|p| *p |= entry.profile)
                .or_insert(entry.profile);
            // Merge dependency edges across duplicate definitions.
            let edge_set = deps.entry(entry.name).or_default();
            edge_set.extend(entry.dep_names);
        }
    }

    // Normalize edge lists (dedup) once; this also bounds the inner loop work.
    for edges in deps.values_mut() {
        edges.sort_unstable();
        edges.dedup();
    }

    // Step 2: global monotone fixed-point. Bits only grow, so this converges;
    // cycle-safe across shard boundaries.
    let names: Vec<String> = deps.keys().cloned().collect();
    loop {
        let mut changed = false;
        for name in &names {
            let Some(dep_names) = deps.get(name) else {
                continue;
            };
            let mut accumulated = AxiomProfile::NONE;
            for dep_name in dep_names {
                if let Some(&dep_profile) = profiles.get(dep_name) {
                    accumulated |= dep_profile;
                }
            }
            if let Some(profile) = profiles.get_mut(name) {
                let before = *profile;
                *profile |= accumulated;
                if *profile != before {
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    // Step 3: write the globally-closed profiles back into every shard. Only
    // count headers whose profile actually gained a bit relative to its
    // post-within-shard state, so the return value reflects cross-shard work.
    let mut upgraded = 0usize;
    for writer in writers.iter_mut() {
        upgraded += writer.apply_closed_axiom_profiles(&profiles);
    }
    upgraded
}

// ---------------------------------------------------------------------------
// Module-level statistics
// ---------------------------------------------------------------------------

/// Summary of axiom usage across a module.
#[derive(Clone, Debug, Default)]
pub struct AxiomProfileStats {
    /// Total constants analyzed.
    pub total: usize,
    /// Constants with zero axiom bits (pure).
    pub pure_count: usize,
    /// Constants using Classical.choice or Classical.em.
    pub classical_count: usize,
    /// Constants using quotient axioms.
    pub quot_count: usize,
    /// Constants using propext.
    pub prop_ext_count: usize,
    /// Constants using funext.
    pub func_ext_count: usize,
    /// Constants that are trust-gated (AXIOMATIZED bit set).
    pub trust_gated_count: usize,
}

/// Compute axiom profile statistics for a module using transitive profiles.
#[must_use]
pub fn compute_profile_stats(module: &ParsedModule) -> AxiomProfileStats {
    let profiles = compute_transitive_axiom_profiles(module);
    let mut stats = AxiomProfileStats::default();

    for constant in &module.constants {
        let profile = profiles
            .get(&constant.name)
            .copied()
            .unwrap_or(AxiomProfile::NONE);
        stats.total += 1;
        if profile.is_pure() {
            stats.pure_count += 1;
        }
        if profile.has(AxiomProfile::CHOICE) || profile.has(AxiomProfile::LEM) {
            stats.classical_count += 1;
        }
        if profile.has(AxiomProfile::QUOT) {
            stats.quot_count += 1;
        }
        if profile.has(AxiomProfile::PROP_EXT) {
            stats.prop_ext_count += 1;
        }
        if profile.has(AxiomProfile::FUNC_EXT) {
            stats.func_ext_count += 1;
        }
        if profile.is_trust_gated() {
            stats.trust_gated_count += 1;
        }
    }

    stats
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    include!("axiom_profile_tests.rs");
}
