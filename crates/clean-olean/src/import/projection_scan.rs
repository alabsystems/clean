// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Per-module structure field-table recovery from projection functions, made
//! proportional to what a module ADDS.
//!
//! [`super::load_register::register_structure_fields_from_projections`]
//! scans EVERY constant of the environment, and the importer ran it once per
//! module with extension entries — measured 2026-09-23 at 24-27% of
//! steady-state import samples (`reports/lean4-replacement-audit-2026-09-24/
//! performance.json`, gap 1): a whole-environment pass per module is what made
//! import cost grow faster than the closure.
//!
//! This keeps that scan's first pass — "which constants are canonical
//! projections `S.<field> := λ*. Proj(S, i, _)`" — as an index kept current
//! from the names each module registers, and re-decides only the structures
//! a module touched. The decision per structure is the old one, re-read from
//! the environment at decision time. It is exact because the decision for a
//! structure `S` reads nothing but: whether `S` already has a field table,
//! `S`'s inductive and constructor, and the constants named `S.<x>`. None of
//! those changes unless a module touches `S` (or registers a table for it,
//! which the decision re-reads), so a structure no module touched since its
//! last decision would be decided the same way again.
//!
//! The index is valid only while the loader is the only writer. Every module
//! records a fingerprint of the environment when it finishes; a module that
//! starts on an environment with a different fingerprint (another import
//! declaration's closure-end passes ran, the elaborator added declarations, a
//! load failed half-way) throws the index away and the next decision rebuilds
//! it from every constant — exactly the old whole-environment scan, now once
//! per such change instead of once per module.

use super::load_register::projection_fn_target;
use clean_kernel::env::{
    register_persistent_ext, ConstantKind as KernelConstantKind, EnvExtensionEntry,
    EnvExtensionEntryData, Environment, ExtensionIdx, PersistentExtEntry, PersistentExtState,
};
use clean_kernel::name::{Name, NameInner};
use hashbrown::{HashMap, HashSet};

/// The environment's shape when the last followed module finished.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct EnvFingerprint {
    generation: u64,
    constants: usize,
    inductives: usize,
    constructors: usize,
}

impl EnvFingerprint {
    fn of(env: &Environment) -> Self {
        Self {
            generation: env.generation(),
            constants: env.num_constants(),
            inductives: env.num_inductives(),
            constructors: env.num_constructors(),
        }
    }
}

/// One canonical projection constant `S.<field>` with body `λ*. Proj(S, idx, _)`.
#[derive(Clone, Debug)]
struct Candidate {
    idx: u32,
    field: Name,
    constant: Name,
}

/// In-process loader bookkeeping; never exported, never imported.
#[derive(Clone, Debug, Default)]
pub(crate) struct ProjectionScanState {
    /// Fingerprint at the end of the last module this index followed.
    followed: Option<EnvFingerprint>,
    /// The index must be rebuilt from every constant before the next decision.
    stale: bool,
    /// Structure → its canonical projection constants, in discovery order.
    by_struct: HashMap<Name, Vec<Candidate>>,
    /// Structures touched since the last decision.
    dirty: HashSet<Name>,
}

/// Placeholder entry type: the state carries no persisted entries.
#[derive(Clone, Debug)]
pub(crate) struct ProjectionScanEntry;

impl PersistentExtEntry for ProjectionScanEntry {
    fn to_env_entry(&self) -> EnvExtensionEntry {
        EnvExtensionEntry {
            name: Name::anon(),
            data: EnvExtensionEntryData::Scalar(0),
        }
    }

    fn from_env_entry(_entry: &EnvExtensionEntry) -> Option<Self> {
        None
    }
}

impl PersistentExtState for ProjectionScanState {
    type Entry = ProjectionScanEntry;

    fn add_entry(&mut self, _entry: &Self::Entry) {}

    fn export_entries(&self) -> Vec<EnvExtensionEntry> {
        Vec::new()
    }
}

static PROJECTION_SCAN_IDX: std::sync::OnceLock<ExtensionIdx> = std::sync::OnceLock::new();

fn projection_scan_idx() -> ExtensionIdx {
    *PROJECTION_SCAN_IDX.get_or_init(|| {
        register_persistent_ext::<ProjectionScanState>(Name::from_string(
            "Clean.olean.projectionScan",
        ))
    })
}

fn take_state(env: &mut Environment) -> ProjectionScanState {
    std::mem::take(env.get_ext_state_mut::<ProjectionScanState>(projection_scan_idx()))
}

fn put_state(env: &mut Environment, state: ProjectionScanState) {
    *env.get_ext_state_mut::<ProjectionScanState>(projection_scan_idx()) = state;
}

/// `c` as a canonical projection of the structure it projects, or `None`.
/// The same filter as the whole-environment scan's first pass.
fn candidate_of(c: &clean_kernel::env::ConstantInfo) -> Option<(Name, Candidate)> {
    if !matches!(
        c.kind,
        KernelConstantKind::Definition | KernelConstantKind::Theorem
    ) {
        return None;
    }
    let (struct_name, idx) = projection_fn_target(c.value.as_ref()?)?;
    let field = match c.name.inner() {
        NameInner::Str(parent, component) if **parent == struct_name => {
            Name::anon().str(component.as_ref())
        }
        NameInner::Num(parent, component) if **parent == struct_name => {
            Name::anon().num(*component)
        }
        _ => return None,
    };
    Some((
        struct_name,
        Candidate {
            idx,
            field,
            constant: c.name.clone(),
        },
    ))
}

/// Call before a module registers anything: an environment the index did
/// not see finish (fingerprint mismatch) invalidates the index.
pub(crate) fn begin_module(env: &mut Environment) {
    let now = EnvFingerprint::of(env);
    let mut state = take_state(env);
    if state.followed != Some(now) {
        state.stale = true;
        state.by_struct.clear();
        state.dirty.clear();
    }
    put_state(env, state);
}

/// Record the names a module registered (added, upgraded or replaced).
pub(crate) fn note_touched<'a>(env: &mut Environment, names: impl IntoIterator<Item = &'a Name>) {
    let mut state = take_state(env);
    if !state.stale {
        for name in names {
            if let Some((s, cand)) = env.get_const(name).and_then(candidate_of) {
                state.dirty.insert(s.clone());
                state.by_struct.entry(s).or_default().push(cand);
            }
            if env.get_inductive(name).is_some() {
                state.dirty.insert(name.clone());
            }
            if let Some(ctor) = env.get_constructor(name) {
                state.dirty.insert(ctor.inductive_name.clone());
            }
            if let NameInner::Str(parent, _) | NameInner::Num(parent, _) = name.inner() {
                if state.by_struct.contains_key(&**parent) {
                    state.dirty.insert((**parent).clone());
                }
            }
        }
    }
    put_state(env, state);
}

/// Call when a module finishes: the index has seen everything up to here.
pub(crate) fn end_module(env: &mut Environment) {
    let now = EnvFingerprint::of(env);
    env.get_ext_state_mut::<ProjectionScanState>(projection_scan_idx())
        .followed = Some(now);
}

/// Decide every structure touched since the last decision — the per-module
/// replacement for `register_structure_fields_from_projections`. Returns how
/// many field tables were registered.
pub(crate) fn register_touched_structure_fields(env: &mut Environment) -> usize {
    let mut state = take_state(env);
    if state.stale {
        // The old scan's first pass, over every constant.
        state.by_struct.clear();
        for c in env.constants() {
            if let Some((s, cand)) = candidate_of(c) {
                state.by_struct.entry(s).or_default().push(cand);
            }
        }
        state.dirty = state.by_struct.keys().cloned().collect();
        state.stale = false;
    }
    let mut registered = 0usize;
    let lazy = super::load_register::lazy_definitions(env);
    for struct_name in std::mem::take(&mut state.dirty) {
        if env.get_structure_field_names(&struct_name).is_some() {
            state.by_struct.remove(&struct_name);
            continue;
        }
        let Some(cands) = state.by_struct.get(&struct_name) else {
            continue;
        };
        if let Some(fields) = decide(env, &struct_name, cands) {
            // The same final decision as the whole-environment scan: a table
            // that `structure_table_contradiction` refutes is not believed.
            if super::load_register::register_recovered_structure_table(
                env,
                struct_name.clone(),
                fields,
                lazy,
            ) {
                registered += 1;
                state.by_struct.remove(&struct_name);
            }
        }
    }
    put_state(env, state);
    registered
}

/// The old scan's second pass for one structure: a single-constructor
/// inductive whose recovered projection indices are exactly `0..k`, the field
/// names in index order. Every candidate is re-read from the environment, so
/// a stale index entry can only drop out, never contribute.
fn decide(env: &Environment, struct_name: &Name, cands: &[Candidate]) -> Option<Vec<Name>> {
    let ind = env.get_inductive(struct_name)?;
    if ind.constructor_names.len() != 1 {
        return None;
    }
    let mut idx_map: HashMap<u32, Name> = HashMap::new();
    for cand in cands {
        let still = env
            .get_const(&cand.constant)
            .and_then(candidate_of)
            .is_some_and(|(s, c)| s == *struct_name && c.idx == cand.idx);
        if still {
            idx_map.insert(cand.idx, cand.field.clone());
        }
    }
    let k = u32::try_from(idx_map.len()).ok()?;
    (0..k).map(|i| idx_map.get(&i).cloned()).collect()
}

#[cfg(test)]
#[path = "projection_scan_tests.rs"]
mod tests;
