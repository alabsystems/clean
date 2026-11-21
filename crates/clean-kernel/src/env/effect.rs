// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! What one module's elaboration did to an environment — its EFFECT — over
//! EVERY component of [`Environment`], not only its constants.
//!
//! # Why
//!
//! `clean check` and `clean project check` elaborate a module next to modules
//! it does not import (a sibling import of an importer), and then compare that
//! elaboration with one in exactly the module's own import closure. The
//! comparison used to look at the CONSTANTS the module added and nothing else.
//! A module's effect on its importers is much wider: instance registrations,
//! attributes, simp/aesop/grind sets, structure metadata, aliases, options,
//! extension entries, the prelude's lazy-initialisation flags. Round-24
//! verification of ff6c33c2c: with `P: def c : C := ⟨3⟩` and `Q: namespace N;
//! def c : C := ⟨2⟩; end N; open N; attribute [instance] c`, Q's `attribute`
//! resolved `c` to P's root `c` whenever P was in the environment, so
//! `M: import P; import Q; theorem m : C.v = 3 := rfl` passed although Lean
//! 4.8.0 (which compiles Q without P) registers `N.c` and rejects M. Q adds
//! the same constant (`N.c`) both ways, so the constant comparison saw
//! nothing.
//!
//! # What an effect is
//!
//! For every component, the entries the elaboration changed between a
//! `before` and an `after` environment, with their values AFTER:
//!
//! * keyed maps (`constants`, `classes`, `structure_fields`, …): each key
//!   whose value was added, changed or removed;
//! * accumulating maps (`instances` per class, aesop indices, derive handlers,
//!   extension entries per extension): per key, the elements added and
//!   removed, plus the value after — two sibling modules that each register an
//!   instance of the same class legitimately leave different vectors, and
//!   only the elements each one contributed are its effect;
//! * sets (`instance_names`, the attribute/hint sets, …): each member added or
//!   removed;
//! * every remaining serialized field (the prelude initialisation flags, the
//!   mode, …), captured GENERICALLY by field name through `serde`, so a field
//!   added to [`Environment`] later is covered without editing this file.
//!
//! Pure registration counters are excluded by name (`generation`,
//! `simp_registry_revision`, and the instance-index positions
//! `instance_seqs` / `next_instance_seq`): they count registrations, so they
//! differ with the number of modules already loaded and carry no meaning of
//! their own.
//! `lazy_source` is never written by elaboration; `native_reducers` is
//! compared by its key set (its values are function pointers).
//!
//! # Agreement
//!
//! [`EnvEffect::disagreement`] compares the effect a module has in its own
//! import closure (`self`) with its effect next to strangers (`shared`),
//! reading values of the shared environment after the module. It passes only
//! when
//!
//! * every entry the module changed in its own closure has the SAME value in
//!   the shared environment (so an importer sees exactly what Lean's import of
//!   the module gives), and
//! * the module changed NOTHING next to strangers that it did not change in
//!   its own closure (the shared environment before the module holds the
//!   module's whole import closure, so such a change can only come from a
//!   stranger).
//!
//! A change the module makes in its own closure but not next to strangers is
//! allowed when the value agrees: a stranger that already ran the same lazy
//! prelude initialisation leaves the same entries behind.

use std::collections::BTreeMap;
use std::fmt::Display;
use std::hash::Hash;

use hashbrown::{HashMap, HashSet};
use serde::ser::{self, Serialize};

use super::Environment;
use crate::name::Name;

/// Fields compared by a typed component below, never by the generic scalar
/// capture. Every name here must be a serialized field of [`Environment`];
/// `tests::every_handled_field_is_a_serialized_field` pins that.
pub(super) const TYPED_FIELDS: &[&str] = &[
    "constants",
    "constant_origins",
    "persistent_extensions",
    "extension_states",
    "inductives",
    "constructors",
    "recursors",
    "quotients",
    "structure_fields",
    "structure_field_defaults",
    "structure_parents",
    "classes",
    "instances",
    "instance_names",
    "instance_synth_orders",
    "aesop_rules",
    "aesop_rule_sets",
    "declared_aesop_rule_sets",
    "aesop_target_index",
    "aesop_hyps_index",
    "aesop_unindexed_rules",
    "simp_lemmas",
    "export_aliases",
    "export_alias_others",
    "extern_bindings",
    "implemented_by",
    "export_bindings",
    "deprecated",
    "inline_hints",
    "noinline_hints",
    "always_inline_hints",
    "macro_inline_hints",
    "inline_if_reduce_hints",
    "nospecialize_hints",
    "specialize_hints",
    "csimp_lemmas",
    "congr_lemmas",
    "ext_lemmas",
    "grind_lemmas",
    "refl_lemmas",
    "symm_lemmas",
    "coercion_decls",
    "match_pattern_decls",
    "init_fn_decls",
    "default_instance_decls",
    "derive_handlers",
    "private_decls",
    "protected_decls",
    "noncomputable_decls",
    "partial_decls",
    "unsafe_decls",
    "local_instance_decls",
    "registered_namespaces",
    "param_names",
    "typed_param_names",
    "param_binder_infos",
    "options",
    "staged_headers",
];

/// Registration counters: they grow with every module already loaded, so they
/// differ between any two environments and say nothing about a module.
///
/// The instance-index positions (`instance_seqs`, `next_instance_seq`) are
/// the same kind of counter: a position is only ever compared with another,
/// and the ORDER they give is compared through `instances`, whose per-class
/// vectors are kept in it.
const COUNTER_FIELDS: &[&str] = &[
    "generation",
    "simp_registry_revision",
    "instance_seqs",
    "next_instance_seq",
];

/// A keyed-map component: each changed key with its value after (`None` =
/// removed).
#[derive(Clone, Debug)]
struct MapEffect<K, V> {
    changed: Vec<(K, Option<V>)>,
}

fn map_effect<K, V>(before: &HashMap<K, V>, after: &HashMap<K, V>) -> MapEffect<K, V>
where
    K: Eq + Hash + Clone,
    V: PartialEq + Clone,
{
    let mut changed = Vec::new();
    for (key, value) in after {
        if before.get(key) != Some(value) {
            changed.push((key.clone(), Some(value.clone())));
        }
    }
    for key in before.keys() {
        if !after.contains_key(key) {
            changed.push((key.clone(), None));
        }
    }
    MapEffect { changed }
}

fn map_disagreement<K, V>(
    field: &str,
    own: &MapEffect<K, V>,
    shared: &MapEffect<K, V>,
    shared_after: &HashMap<K, V>,
) -> Option<String>
where
    K: Eq + Hash + Display,
    V: PartialEq,
{
    map_disagreement_by(field, own, shared, |key, value| {
        shared_after.get(key) == value
    })
}

fn map_disagreement_by<K, V>(
    field: &str,
    own: &MapEffect<K, V>,
    shared: &MapEffect<K, V>,
    agrees: impl Fn(&K, Option<&V>) -> bool,
) -> Option<String>
where
    K: Eq + Hash + Display,
{
    for (key, value) in &own.changed {
        if !agrees(key, value.as_ref()) {
            return Some(format!("{field} entry `{key}` differs"));
        }
    }
    let own_keys: HashSet<&K> = own.changed.iter().map(|(key, _)| key).collect();
    shared
        .changed
        .iter()
        .find(|(key, _)| !own_keys.contains(key))
        .map(|(key, _)| {
            format!("{field} entry `{key}` is changed only next to modules it does not import")
        })
}

/// An accumulating component: per changed key, the value after and the
/// elements added and removed.
#[derive(Clone, Debug)]
struct AccEffect<K, T> {
    changed: Vec<AccChange<K, T>>,
}

#[derive(Clone, Debug)]
struct AccChange<K, T> {
    key: K,
    after: Vec<T>,
    added: Vec<T>,
    removed: Vec<T>,
}

/// Elements of `a` not matched one-for-one by an element of `b`.
fn multiset_minus<T: PartialEq + Clone>(a: &[T], b: &[T]) -> Vec<T> {
    let mut used = vec![false; b.len()];
    let mut out = Vec::new();
    for item in a {
        match b
            .iter()
            .enumerate()
            .position(|(idx, other)| !used[idx] && other == item)
        {
            Some(idx) => used[idx] = true,
            None => out.push(item.clone()),
        }
    }
    out
}

fn acc_effect<K, T>(before: &HashMap<K, Vec<T>>, after: &HashMap<K, Vec<T>>) -> AccEffect<K, T>
where
    K: Eq + Hash + Clone,
    T: PartialEq + Clone,
{
    let mut changed = Vec::new();
    for (key, now) in after {
        let was = before.get(key).map_or(&[][..], Vec::as_slice);
        if was != now.as_slice() {
            changed.push(AccChange {
                key: key.clone(),
                after: now.clone(),
                added: multiset_minus(now, was),
                removed: multiset_minus(was, now),
            });
        }
    }
    for (key, was) in before {
        if !after.contains_key(key) && !was.is_empty() {
            changed.push(AccChange {
                key: key.clone(),
                after: Vec::new(),
                added: Vec::new(),
                removed: was.clone(),
            });
        }
    }
    AccEffect { changed }
}

fn acc_disagreement<K, T>(
    field: &str,
    own: &AccEffect<K, T>,
    shared: &AccEffect<K, T>,
    shared_after: &HashMap<K, Vec<T>>,
) -> Option<String>
where
    K: Eq + Hash + Display,
    T: PartialEq,
{
    for change in &own.changed {
        let there = shared_after.get(&change.key).map_or(&[][..], Vec::as_slice);
        if change.added.iter().any(|item| !there.contains(item)) {
            return Some(format!(
                "{field} `{}`: an entry the module adds in its own import closure is missing",
                change.key
            ));
        }
        if change.removed.iter().any(|item| there.contains(item)) {
            return Some(format!(
                "{field} `{}`: an entry the module removes in its own import closure is present",
                change.key
            ));
        }
    }
    for change in &shared.changed {
        let Some(own_change) = own.changed.iter().find(|own| own.key == change.key) else {
            return Some(format!(
                "{field} `{}` is changed only next to modules it does not import",
                change.key
            ));
        };
        if change
            .added
            .iter()
            .any(|item| !own_change.after.contains(item))
            || change
                .removed
                .iter()
                .any(|item| own_change.after.contains(item))
        {
            return Some(format!(
                "{field} `{}`: next to modules it does not import, the module adds or removes \
                 an entry it does not in its own import closure",
                change.key
            ));
        }
    }
    None
}

/// A set component: each changed member and whether it is present after.
#[derive(Clone, Debug)]
struct SetEffect<K> {
    changed: Vec<(K, bool)>,
}

fn set_effect<K: Eq + Hash + Clone>(before: &HashSet<K>, after: &HashSet<K>) -> SetEffect<K> {
    let mut changed = after
        .difference(before)
        .map(|key| (key.clone(), true))
        .collect::<Vec<_>>();
    changed.extend(before.difference(after).map(|key| (key.clone(), false)));
    SetEffect { changed }
}

fn set_disagreement<K: Eq + Hash + Display>(
    field: &str,
    own: &SetEffect<K>,
    shared: &SetEffect<K>,
    shared_after: &HashSet<K>,
) -> Option<String> {
    for (key, present) in &own.changed {
        if shared_after.contains(key) != *present {
            return Some(format!("{field} member `{key}` differs"));
        }
    }
    let own_keys: HashSet<&K> = own.changed.iter().map(|(key, _)| key).collect();
    shared
        .changed
        .iter()
        .find(|(key, _)| !own_keys.contains(key))
        .map(|(key, _)| {
            format!("{field} member `{key}` is changed only next to modules it does not import")
        })
}

/// A single-key view of a top-level vector, so it is compared as an
/// accumulating component.
fn seq_view<T: Clone>(items: &[T]) -> HashMap<&'static str, Vec<T>> {
    let mut map = HashMap::new();
    map.insert("", items.to_vec());
    map
}

/// The generically captured fields: every serialized field of [`Environment`]
/// not in [`TYPED_FIELDS`] or [`COUNTER_FIELDS`], as its bincode bytes.
fn scalar_fields(env: &Environment) -> BTreeMap<&'static str, Vec<u8>> {
    let mut capture = FieldCapture::default();
    // A failure to capture is recorded as a field that never agrees, so a
    // comparison that could not read a field fails closed.
    if env.serialize(&mut capture).is_err() {
        capture
            .fields
            .insert("<environment could not be captured>", vec![0xff]);
    }
    capture.fields
}

/// The effect a module's elaboration had on an environment. Built by
/// [`Environment::effect_since`]; compared by [`EnvEffect::disagreement`].
#[derive(Clone, Debug)]
pub struct EnvEffect {
    constants: MapEffect<Name, super::ConstantInfo>,
    constant_origins: MapEffect<Name, super::ConstantOrigin>,
    declaration_verification: MapEffect<Name, super::DeclarationVerification>,
    codata_origins: MapEffect<Name, super::CodataOrigin>,
    codata_carriers: SetEffect<Name>,
    value_forall_binder_names: MapEffect<Name, super::ValueForallBinderNames>,
    persistent_extensions: MapEffect<Name, super::PersistentEnvExtensionState>,
    matcher_rows: MapEffect<Name, Vec<(usize, super::EnvExtensionEntryData)>>,
    matcher_header_changed: bool,
    extension_entries: AccEffect<Name, super::EnvExtensionEntry>,
    inductives: MapEffect<Name, crate::inductive::InductiveVal>,
    constructors: MapEffect<Name, crate::inductive::ConstructorVal>,
    recursors: MapEffect<Name, crate::inductive::RecursorVal>,
    quotients: MapEffect<Name, crate::quot::QuotVal>,
    structure_fields: MapEffect<Name, Vec<Name>>,
    structure_field_defaults: MapEffect<Name, HashMap<Name, crate::expr::Expr>>,
    structure_parents: MapEffect<Name, Vec<(Name, Name)>>,
    classes: MapEffect<Name, super::KernelClassInfo>,
    instances: AccEffect<Name, super::KernelInstanceInfo>,
    instance_names: SetEffect<Name>,
    instance_synth_orders: MapEffect<Name, Vec<usize>>,
    aesop_rules: AccEffect<&'static str, super::aesop::AesopRule>,
    aesop_priority_overrides: MapEffect<Name, u32>,
    aesop_rule_sets: MapEffect<Name, super::aesop::AesopRuleSet>,
    declared_aesop_rule_sets: SetEffect<Name>,
    aesop_target_index: AccEffect<Name, super::aesop::AesopRule>,
    aesop_hyps_index: AccEffect<Name, super::aesop::AesopRule>,
    aesop_unindexed_rules: AccEffect<&'static str, super::aesop::AesopRule>,
    simp_lemmas: MapEffect<Name, super::SimpLemmaInfo>,
    export_aliases: MapEffect<Name, Name>,
    export_alias_others: AccEffect<Name, Name>,
    extern_bindings: MapEffect<Name, String>,
    implemented_by: MapEffect<Name, Name>,
    native_reducers: SetEffect<Name>,
    export_bindings: MapEffect<Name, String>,
    deprecated: MapEffect<Name, Option<String>>,
    hint_sets: Vec<(&'static str, SetEffect<Name>)>,
    grind_lemmas: AccEffect<&'static str, (Name, super::GrindAttrKind)>,
    derive_handlers: AccEffect<Name, Name>,
    param_names: MapEffect<Name, Vec<String>>,
    typed_param_names: MapEffect<Name, Vec<Name>>,
    param_binder_infos: MapEffect<Name, Vec<crate::expr::BinderInfo>>,
    options: MapEffect<String, Option<String>>,
    scalars: Vec<(&'static str, Vec<u8>)>,
}

/// The attribute / hint name sets, by field name, in a fixed order.
fn hint_sets(env: &Environment) -> [(&'static str, &HashSet<Name>); 23] {
    [
        ("inline_hints", &env.inline_hints),
        ("noinline_hints", &env.noinline_hints),
        ("always_inline_hints", &env.always_inline_hints),
        ("macro_inline_hints", &env.macro_inline_hints),
        ("inline_if_reduce_hints", &env.inline_if_reduce_hints),
        ("nospecialize_hints", &env.nospecialize_hints),
        ("specialize_hints", &env.specialize_hints),
        ("csimp_lemmas", &env.csimp_lemmas),
        ("congr_lemmas", &env.congr_lemmas),
        ("ext_lemmas", &env.ext_lemmas),
        ("refl_lemmas", &env.refl_lemmas),
        ("symm_lemmas", &env.symm_lemmas),
        ("coercion_decls", &env.coercion_decls),
        ("match_pattern_decls", &env.match_pattern_decls),
        ("init_fn_decls", &env.init_fn_decls),
        ("default_instance_decls", &env.default_instance_decls),
        ("private_decls", &env.private_decls),
        ("protected_decls", &env.protected_decls),
        ("noncomputable_decls", &env.noncomputable_decls),
        ("partial_decls", &env.partial_decls),
        ("unsafe_decls", &env.unsafe_decls),
        ("local_instance_decls", &env.local_instance_decls),
        ("registered_namespaces", &env.registered_namespaces),
    ]
}

fn same_matcher_header(
    expected: Option<&super::PersistentEnvExtensionState>,
    actual: Option<&super::PersistentEnvExtensionState>,
) -> bool {
    match (expected, actual) {
        (Some(left), Some(right)) => {
            left.state == right.state && left.imported_entries.len() == right.imported_entries.len()
        }
        (None, None) => true,
        _ => false,
    }
}

/// Matcher lookup reads each name independently. Keep the original bucket, bytes,
/// and multiplicity for that name, including malformed or conflicting rows.
fn matcher_rows(
    state: Option<&super::PersistentEnvExtensionState>,
) -> HashMap<Name, Vec<(usize, super::EnvExtensionEntryData)>> {
    let mut rows = HashMap::<Name, Vec<_>>::new();
    if let Some(state) = state {
        for (module, entries) in state.imported_entries.iter().enumerate() {
            for entry in entries {
                rows.entry(entry.name.clone())
                    .or_default()
                    .push((module, entry.data.clone()));
            }
        }
    }
    rows
}

fn extension_entry_map(env: &Environment) -> HashMap<Name, Vec<super::EnvExtensionEntry>> {
    env.export_extension_states()
        .into_iter()
        .map(|(name, entries)| {
            let entries = if name == Name::from_string("Clean.compiler.csimpSource") {
                super::csimp::effect_entries(&entries)
            } else {
                entries
            };
            (name, entries)
        })
        .collect()
}

fn aesop_rule_vectors(env: &Environment) -> HashMap<&'static str, Vec<super::aesop::AesopRule>> {
    let mut map = HashMap::new();
    map.insert("safe", env.aesop_rules.safe_rules.clone());
    map.insert("unsafe", env.aesop_rules.unsafe_rules.clone());
    map.insert("norm", env.aesop_rules.norm_rules.clone());
    map
}

fn native_reducer_names(env: &Environment) -> HashSet<Name> {
    env.native_reducers.keys().cloned().collect()
}

impl Environment {
    /// The effect of whatever ran between `before` (an earlier state of this
    /// environment) and `self`, over every component. See the module docs.
    #[must_use]
    pub fn effect_since(&self, before: &Environment) -> EnvEffect {
        let scalars_before = scalar_fields(before);
        let scalars = scalar_fields(self)
            .into_iter()
            .filter(|(field, bytes)| scalars_before.get(field) != Some(bytes))
            .collect();
        let before_hints = hint_sets(before);
        let hint_sets = hint_sets(self)
            .iter()
            .zip(before_hints.iter())
            .map(|((field, now), (_, was))| (*field, set_effect(was, now)))
            .collect();
        let persistent_extensions = map_effect(
            before.persistent_extensions.states(),
            self.persistent_extensions.states(),
        );
        let matcher_key = super::matcher::matcher_storage_key();
        let matcher_before = before.persistent_extensions.get(&matcher_key);
        let matcher_after = self.persistent_extensions.get(&matcher_key);
        let matcher_rows = if persistent_extensions
            .changed
            .iter()
            .any(|(key, _)| key == &matcher_key)
        {
            map_effect(&matcher_rows(matcher_before), &matcher_rows(matcher_after))
        } else {
            MapEffect {
                changed: Vec::new(),
            }
        };
        EnvEffect {
            constants: map_effect(&before.constants, &self.constants),
            constant_origins: map_effect(&before.constant_origins, &self.constant_origins),
            declaration_verification: map_effect(
                &before.declaration_verification,
                &self.declaration_verification,
            ),
            codata_origins: map_effect(&before.codata_origins, &self.codata_origins),
            codata_carriers: set_effect(&before.codata_carriers, &self.codata_carriers),
            value_forall_binder_names: map_effect(
                before.value_binder_table(),
                self.value_binder_table(),
            ),
            persistent_extensions,
            matcher_rows,
            matcher_header_changed: !same_matcher_header(matcher_before, matcher_after),
            extension_entries: acc_effect(&extension_entry_map(before), &extension_entry_map(self)),
            inductives: map_effect(&before.inductives, &self.inductives),
            constructors: map_effect(&before.constructors, &self.constructors),
            recursors: map_effect(&before.recursors, &self.recursors),
            quotients: map_effect(&before.quotients, &self.quotients),
            structure_fields: map_effect(&before.structure_fields, &self.structure_fields),
            structure_field_defaults: map_effect(
                &before.structure_field_defaults,
                &self.structure_field_defaults,
            ),
            structure_parents: map_effect(&before.structure_parents, &self.structure_parents),
            classes: map_effect(&before.classes, &self.classes),
            instances: acc_effect(&before.instances, &self.instances),
            instance_names: set_effect(&before.instance_names, &self.instance_names),
            instance_synth_orders: map_effect(
                &before.instance_synth_orders,
                &self.instance_synth_orders,
            ),
            aesop_rules: acc_effect(&aesop_rule_vectors(before), &aesop_rule_vectors(self)),
            aesop_priority_overrides: map_effect(
                &before.aesop_rules.priority_overrides,
                &self.aesop_rules.priority_overrides,
            ),
            aesop_rule_sets: map_effect(&before.aesop_rule_sets, &self.aesop_rule_sets),
            declared_aesop_rule_sets: set_effect(
                &before.declared_aesop_rule_sets,
                &self.declared_aesop_rule_sets,
            ),
            aesop_target_index: acc_effect(&before.aesop_target_index, &self.aesop_target_index),
            aesop_hyps_index: acc_effect(&before.aesop_hyps_index, &self.aesop_hyps_index),
            aesop_unindexed_rules: acc_effect(
                &seq_view(&before.aesop_unindexed_rules),
                &seq_view(&self.aesop_unindexed_rules),
            ),
            simp_lemmas: map_effect(&before.simp_lemmas, &self.simp_lemmas),
            export_aliases: map_effect(&before.export_aliases, &self.export_aliases),
            export_alias_others: acc_effect(&before.export_alias_others, &self.export_alias_others),
            extern_bindings: map_effect(&before.extern_bindings, &self.extern_bindings),
            implemented_by: map_effect(&before.implemented_by, &self.implemented_by),
            native_reducers: set_effect(&native_reducer_names(before), &native_reducer_names(self)),
            export_bindings: map_effect(&before.export_bindings, &self.export_bindings),
            deprecated: map_effect(&before.deprecated, &self.deprecated),
            hint_sets,
            grind_lemmas: acc_effect(
                &seq_view(&before.grind_lemmas),
                &seq_view(&self.grind_lemmas),
            ),
            derive_handlers: acc_effect(&before.derive_handlers, &self.derive_handlers),
            param_names: map_effect(&before.param_names, &self.param_names),
            typed_param_names: map_effect(&before.typed_param_names, &self.typed_param_names),
            param_binder_infos: map_effect(&before.param_binder_infos, &self.param_binder_infos),
            options: map_effect(&before.options, &self.options),
            scalars,
        }
    }
}

impl EnvEffect {
    fn persistent_disagreement(&self, shared: &Self, env: &Environment) -> Option<String> {
        let matcher_key = super::matcher::matcher_storage_key();
        if shared.matcher_header_changed && !self.matcher_header_changed {
            return Some(format!("persistent extension `{matcher_key}` header changed only next to modules it does not import"));
        }
        let opaque = map_disagreement_by(
            "persistent extension",
            &self.persistent_extensions,
            &shared.persistent_extensions,
            |key, expected| {
                let actual = env.persistent_extensions.get(key);
                if key == &matcher_key {
                    // A row change still requires the isolated table's final
                    // presence, opaque bytes and bucket count, even on deletion.
                    same_matcher_header(expected, actual)
                } else {
                    expected == actual
                }
            },
        );
        if opaque.is_some()
            || (self.matcher_rows.changed.is_empty() && shared.matcher_rows.changed.is_empty())
        {
            return opaque;
        }
        map_disagreement(
            "matcher metadata",
            &self.matcher_rows,
            &shared.matcher_rows,
            &matcher_rows(env.persistent_extensions.get(&matcher_key)),
        )
    }

    /// Names of the constants this effect added or changed.
    pub fn changed_constant_names(&self) -> impl Iterator<Item = &Name> {
        self.constants
            .changed
            .iter()
            .filter(|(_, value)| value.is_some())
            .map(|(name, _)| name)
    }

    /// The first component this effect changed, by field name, or `None` when
    /// it changed nothing. `after.effect_since(&other)` is empty exactly when
    /// the two environments agree on every component an effect compares (the
    /// registration counters and `staged_headers` excepted; see the module
    /// docs), which is how the local fact delta checks a replay
    /// ([`super::fact_delta`]).
    #[must_use]
    pub fn first_change(&self) -> Option<String> {
        fn map<K: Display, V>(field: &str, effect: &MapEffect<K, V>) -> Option<String> {
            effect
                .changed
                .first()
                .map(|(key, _)| format!("{field} entry `{key}`"))
        }
        fn acc<K: std::fmt::Debug, T>(field: &str, effect: &AccEffect<K, T>) -> Option<String> {
            effect
                .changed
                .first()
                .map(|change| format!("{field} `{:?}`", change.key))
        }
        fn set<K: Display>(field: &str, effect: &SetEffect<K>) -> Option<String> {
            effect
                .changed
                .first()
                .map(|(key, _)| format!("{field} member `{key}`"))
        }
        let first = [
            map("constants", &self.constants),
            map("constant_origins", &self.constant_origins),
            map("declaration_verification", &self.declaration_verification),
            map("codata_origins", &self.codata_origins),
            set("codata_carriers", &self.codata_carriers),
            map("value_forall_binder_names", &self.value_forall_binder_names),
            map("persistent_extensions", &self.persistent_extensions),
            map("matcher metadata", &self.matcher_rows),
            acc("extension_states", &self.extension_entries),
            map("inductives", &self.inductives),
            map("constructors", &self.constructors),
            map("recursors", &self.recursors),
            map("quotients", &self.quotients),
            map("structure_fields", &self.structure_fields),
            map("structure_field_defaults", &self.structure_field_defaults),
            map("structure_parents", &self.structure_parents),
            map("classes", &self.classes),
            acc("instances", &self.instances),
            set("instance_names", &self.instance_names),
            map("instance_synth_orders", &self.instance_synth_orders),
            acc("aesop_rules", &self.aesop_rules),
            map("aesop_priority_overrides", &self.aesop_priority_overrides),
            map("aesop_rule_sets", &self.aesop_rule_sets),
            set("declared_aesop_rule_sets", &self.declared_aesop_rule_sets),
            acc("aesop_target_index", &self.aesop_target_index),
            acc("aesop_hyps_index", &self.aesop_hyps_index),
            acc("aesop_unindexed_rules", &self.aesop_unindexed_rules),
            map("simp_lemmas", &self.simp_lemmas),
            map("export_aliases", &self.export_aliases),
            acc("export_alias_others", &self.export_alias_others),
            map("extern_bindings", &self.extern_bindings),
            map("implemented_by", &self.implemented_by),
            set("native_reducers", &self.native_reducers),
            map("export_bindings", &self.export_bindings),
            map("deprecated", &self.deprecated),
            acc("grind_lemmas", &self.grind_lemmas),
            acc("derive_handlers", &self.derive_handlers),
            map("param_names", &self.param_names),
            map("typed_param_names", &self.typed_param_names),
            map("param_binder_infos", &self.param_binder_infos),
            map("options", &self.options),
        ]
        .into_iter()
        .flatten()
        .next();
        first
            .or_else(|| {
                self.hint_sets
                    .iter()
                    .find_map(|(field, effect)| set(field, effect))
            })
            .or_else(|| {
                self.scalars
                    .first()
                    .map(|(field, _)| format!("environment field `{field}`"))
            })
    }

    /// Why a module whose effect in its own import closure is `self` and
    /// whose effect next to modules it does not import is `shared` (leaving
    /// `shared_after`) does NOT give its importers what its own closure
    /// gives them, or `None` when it does. See the module docs.
    #[must_use]
    pub fn disagreement(&self, shared: &EnvEffect, shared_after: &Environment) -> Option<String> {
        let env = shared_after;
        let first = [
            map_disagreement(
                "constant",
                &self.constants,
                &shared.constants,
                &env.constants,
            ),
            map_disagreement(
                "constant origin",
                &self.constant_origins,
                &shared.constant_origins,
                &env.constant_origins,
            ),
            map_disagreement(
                "declaration verification",
                &self.declaration_verification,
                &shared.declaration_verification,
                &env.declaration_verification,
            ),
            map_disagreement(
                "codata origin",
                &self.codata_origins,
                &shared.codata_origins,
                &env.codata_origins,
            ),
            set_disagreement(
                "codata carrier",
                &self.codata_carriers,
                &shared.codata_carriers,
                &env.codata_carriers,
            ),
            map_disagreement(
                "value binder names",
                &self.value_forall_binder_names,
                &shared.value_forall_binder_names,
                env.value_binder_table(),
            ),
            self.persistent_disagreement(shared, env),
            acc_disagreement(
                "extension entries",
                &self.extension_entries,
                &shared.extension_entries,
                &extension_entry_map(env),
            ),
            map_disagreement(
                "inductive",
                &self.inductives,
                &shared.inductives,
                &env.inductives,
            ),
            map_disagreement(
                "constructor",
                &self.constructors,
                &shared.constructors,
                &env.constructors,
            ),
            map_disagreement(
                "recursor",
                &self.recursors,
                &shared.recursors,
                &env.recursors,
            ),
            map_disagreement(
                "quotient",
                &self.quotients,
                &shared.quotients,
                &env.quotients,
            ),
            map_disagreement(
                "structure fields",
                &self.structure_fields,
                &shared.structure_fields,
                &env.structure_fields,
            ),
            map_disagreement(
                "structure field defaults",
                &self.structure_field_defaults,
                &shared.structure_field_defaults,
                &env.structure_field_defaults,
            ),
            map_disagreement(
                "structure parents",
                &self.structure_parents,
                &shared.structure_parents,
                &env.structure_parents,
            ),
            map_disagreement("class", &self.classes, &shared.classes, &env.classes),
            acc_disagreement(
                "instances of",
                &self.instances,
                &shared.instances,
                &env.instances,
            ),
            set_disagreement(
                "instance",
                &self.instance_names,
                &shared.instance_names,
                &env.instance_names,
            ),
            map_disagreement(
                "instance synthesis order",
                &self.instance_synth_orders,
                &shared.instance_synth_orders,
                &env.instance_synth_orders,
            ),
            acc_disagreement(
                "aesop rules",
                &self.aesop_rules,
                &shared.aesop_rules,
                &aesop_rule_vectors(env),
            ),
            map_disagreement(
                "aesop priority override",
                &self.aesop_priority_overrides,
                &shared.aesop_priority_overrides,
                &env.aesop_rules.priority_overrides,
            ),
            map_disagreement(
                "aesop rule set",
                &self.aesop_rule_sets,
                &shared.aesop_rule_sets,
                &env.aesop_rule_sets,
            ),
            set_disagreement(
                "declared aesop rule set",
                &self.declared_aesop_rule_sets,
                &shared.declared_aesop_rule_sets,
                &env.declared_aesop_rule_sets,
            ),
            acc_disagreement(
                "aesop target index",
                &self.aesop_target_index,
                &shared.aesop_target_index,
                &env.aesop_target_index,
            ),
            acc_disagreement(
                "aesop hypothesis index",
                &self.aesop_hyps_index,
                &shared.aesop_hyps_index,
                &env.aesop_hyps_index,
            ),
            acc_disagreement(
                "aesop unindexed rules",
                &self.aesop_unindexed_rules,
                &shared.aesop_unindexed_rules,
                &seq_view(&env.aesop_unindexed_rules),
            ),
            map_disagreement(
                "simp lemma",
                &self.simp_lemmas,
                &shared.simp_lemmas,
                &env.simp_lemmas,
            ),
            map_disagreement(
                "export alias",
                &self.export_aliases,
                &shared.export_aliases,
                &env.export_aliases,
            ),
            acc_disagreement(
                "further export alias targets of",
                &self.export_alias_others,
                &shared.export_alias_others,
                &env.export_alias_others,
            ),
            map_disagreement(
                "extern binding",
                &self.extern_bindings,
                &shared.extern_bindings,
                &env.extern_bindings,
            ),
            map_disagreement(
                "implemented_by",
                &self.implemented_by,
                &shared.implemented_by,
                &env.implemented_by,
            ),
            set_disagreement(
                "native reducer",
                &self.native_reducers,
                &shared.native_reducers,
                &native_reducer_names(env),
            ),
            map_disagreement(
                "export binding",
                &self.export_bindings,
                &shared.export_bindings,
                &env.export_bindings,
            ),
            map_disagreement(
                "deprecation",
                &self.deprecated,
                &shared.deprecated,
                &env.deprecated,
            ),
            acc_disagreement(
                "grind lemmas",
                &self.grind_lemmas,
                &shared.grind_lemmas,
                &seq_view(&env.grind_lemmas),
            ),
            acc_disagreement(
                "derive handlers",
                &self.derive_handlers,
                &shared.derive_handlers,
                &env.derive_handlers,
            ),
            map_disagreement(
                "parameter names",
                &self.param_names,
                &shared.param_names,
                &env.param_names,
            ),
            map_disagreement(
                "typed parameter names",
                &self.typed_param_names,
                &shared.typed_param_names,
                &env.typed_param_names,
            ),
            map_disagreement(
                "parameter binder infos",
                &self.param_binder_infos,
                &shared.param_binder_infos,
                &env.param_binder_infos,
            ),
            map_disagreement("option", &self.options, &shared.options, &env.options),
        ]
        .into_iter()
        .flatten()
        .next();
        if first.is_some() {
            return first;
        }
        let shared_hints = hint_sets(env);
        for (((field, own), (_, other)), (_, there)) in self
            .hint_sets
            .iter()
            .zip(shared.hint_sets.iter())
            .zip(shared_hints.iter())
        {
            if let Some(reason) = set_disagreement(field, own, other, there) {
                return Some(reason);
            }
        }
        let shared_scalars = scalar_fields(env);
        for (field, bytes) in &self.scalars {
            if shared_scalars.get(field) != Some(bytes) {
                return Some(format!("environment field `{field}` differs"));
            }
        }
        let own_fields: HashSet<&str> = self.scalars.iter().map(|(field, _)| *field).collect();
        shared
            .scalars
            .iter()
            .find(|(field, _)| !own_fields.contains(field))
            .map(|(field, _)| {
                format!(
                    "environment field `{field}` is changed only next to modules it does not \
                     import"
                )
            })
    }
}

// ---------------------------------------------------------------------------
// Generic capture of the remaining fields
// ---------------------------------------------------------------------------

#[derive(Debug)]
struct CaptureError(String);

impl Display for CaptureError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for CaptureError {}

impl ser::Error for CaptureError {
    fn custom<T: Display>(msg: T) -> Self {
        Self(msg.to_string())
    }
}

/// A `serde` serializer that accepts exactly one struct (the environment) and
/// records each field outside [`TYPED_FIELDS`] / [`COUNTER_FIELDS`] as its
/// bincode bytes. `seen` lists every field name serde presented.
#[derive(Default)]
struct FieldCapture {
    fields: BTreeMap<&'static str, Vec<u8>>,
    seen: Vec<&'static str>,
}

impl ser::SerializeStruct for &mut FieldCapture {
    type Ok = ();
    type Error = CaptureError;

    fn serialize_field<T: ?Sized + Serialize>(
        &mut self,
        key: &'static str,
        value: &T,
    ) -> Result<(), CaptureError> {
        self.seen.push(key);
        if TYPED_FIELDS.contains(&key) || COUNTER_FIELDS.contains(&key) {
            return Ok(());
        }
        let bytes = bincode::serde::encode_to_vec(value, bincode::config::standard())
            .map_err(|err| CaptureError(format!("field `{key}`: {err}")))?;
        self.fields.insert(key, bytes);
        Ok(())
    }

    fn end(self) -> Result<(), CaptureError> {
        Ok(())
    }
}

macro_rules! refuse {
    ($($name:ident($($arg:ty),*) -> $ret:ty;)*) => {
        $(fn $name(self, $(_: $arg),*) -> Result<$ret, CaptureError> {
            Err(CaptureError(concat!("unexpected ", stringify!($name)).to_string()))
        })*
    };
}

impl ser::Serializer for &mut FieldCapture {
    type Ok = ();
    type Error = CaptureError;
    type SerializeSeq = ser::Impossible<(), CaptureError>;
    type SerializeTuple = ser::Impossible<(), CaptureError>;
    type SerializeTupleStruct = ser::Impossible<(), CaptureError>;
    type SerializeTupleVariant = ser::Impossible<(), CaptureError>;
    type SerializeMap = ser::Impossible<(), CaptureError>;
    type SerializeStruct = Self;
    type SerializeStructVariant = ser::Impossible<(), CaptureError>;

    fn serialize_struct(self, _: &'static str, _: usize) -> Result<Self, CaptureError> {
        Ok(self)
    }

    refuse! {
        serialize_bool(bool) -> ();
        serialize_i8(i8) -> ();
        serialize_i16(i16) -> ();
        serialize_i32(i32) -> ();
        serialize_i64(i64) -> ();
        serialize_u8(u8) -> ();
        serialize_u16(u16) -> ();
        serialize_u32(u32) -> ();
        serialize_u64(u64) -> ();
        serialize_f32(f32) -> ();
        serialize_f64(f64) -> ();
        serialize_char(char) -> ();
        serialize_str(&str) -> ();
        serialize_bytes(&[u8]) -> ();
        serialize_none() -> ();
        serialize_unit() -> ();
        serialize_unit_struct(&'static str) -> ();
        serialize_unit_variant(&'static str, u32, &'static str) -> ();
        serialize_seq(Option<usize>) -> Self::SerializeSeq;
        serialize_tuple(usize) -> Self::SerializeTuple;
        serialize_tuple_struct(&'static str, usize) -> Self::SerializeTupleStruct;
        serialize_tuple_variant(&'static str, u32, &'static str, usize) -> Self::SerializeTupleVariant;
        serialize_map(Option<usize>) -> Self::SerializeMap;
        serialize_struct_variant(&'static str, u32, &'static str, usize) -> Self::SerializeStructVariant;
    }

    fn serialize_some<T: ?Sized + Serialize>(self, _: &T) -> Result<(), CaptureError> {
        Err(CaptureError("unexpected serialize_some".to_string()))
    }

    fn serialize_newtype_struct<T: ?Sized + Serialize>(
        self,
        _: &'static str,
        _: &T,
    ) -> Result<(), CaptureError> {
        Err(CaptureError(
            "unexpected serialize_newtype_struct".to_string(),
        ))
    }

    fn serialize_newtype_variant<T: ?Sized + Serialize>(
        self,
        _: &'static str,
        _: u32,
        _: &'static str,
        _: &T,
    ) -> Result<(), CaptureError> {
        Err(CaptureError(
            "unexpected serialize_newtype_variant".to_string(),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn seen_fields(env: &Environment) -> Vec<&'static str> {
        let mut capture = FieldCapture::default();
        env.serialize(&mut capture).expect("capture");
        capture.seen
    }

    /// A misspelled entry in `TYPED_FIELDS` would drop that field from BOTH
    /// comparisons (skipped by the capture, compared by nothing).
    #[test]
    fn every_handled_field_is_a_serialized_field() {
        let seen = seen_fields(&Environment::new());
        for field in TYPED_FIELDS.iter().chain(COUNTER_FIELDS) {
            assert!(
                seen.contains(field),
                "`{field}` is not a serialized Environment field"
            );
        }
        // And the capture really records the rest (the prelude flags).
        assert!(scalar_fields(&Environment::new()).len() > 100);
    }

    #[test]
    fn identical_environments_have_no_effect_and_agree() {
        let env = Environment::with_prelude();
        let effect = env.effect_since(&env.clone());
        assert!(effect.disagreement(&effect, &env).is_none());
        assert!(effect.changed_constant_names().next().is_none());
    }

    fn instance(name: &str, class: &str) -> super::super::KernelInstanceInfo {
        super::super::KernelInstanceInfo {
            name: Name::from_string(name),
            class_name: Name::from_string(class),
            priority: 1000,
            type_: None,
            value: None,
        }
    }

    /// The round-24 shape: the module registers a DIFFERENT instance next to
    /// a stranger than in its own closure, with the same constants.
    #[test]
    fn a_different_instance_registration_disagrees() {
        let base = Environment::new();
        let mut own_after = base.clone();
        own_after.register_instance(instance("N.c", "C"));
        let own = own_after.effect_since(&base);

        let mut stranger = base.clone();
        stranger.register_instance(instance("p", "D"));
        let mut shared_after = stranger.clone();
        shared_after.register_instance(instance("c", "C"));
        let shared = shared_after.effect_since(&stranger);
        assert!(own.disagreement(&shared, &shared_after).is_some());
    }

    /// Two siblings each registering an instance of the SAME class is not a
    /// leak: only the element each contributed is its effect.
    #[test]
    fn sibling_instances_of_one_class_agree() {
        let base = Environment::new();
        let mut own_after = base.clone();
        own_after.register_instance(instance("q", "C"));
        let own = own_after.effect_since(&base);

        let mut stranger = base.clone();
        stranger.register_instance(instance("p", "C"));
        let mut shared_after = stranger.clone();
        shared_after.register_instance(instance("q", "C"));
        let shared = shared_after.effect_since(&stranger);
        assert_eq!(own.disagreement(&shared, &shared_after), None);
    }

    /// An effect that appears only next to a stranger disagrees.
    #[test]
    fn a_change_only_next_to_strangers_disagrees() {
        let base = Environment::new();
        let own = base.effect_since(&base);
        let mut shared_after = base.clone();
        shared_after.register_instance(instance("x", "C"));
        let shared = shared_after.effect_since(&base);
        assert!(own.disagreement(&shared, &shared_after).is_some());
    }

    /// A generically captured field (a prelude initialisation flag) is
    /// compared too.
    #[test]
    fn a_scalar_field_is_compared() {
        let base = Environment::new();
        let mut own_after = base.clone();
        own_after.init_nat().expect("init nat");
        let own = own_after.effect_since(&base);
        // Next to a stranger that already initialised Nat, the module
        // changes nothing, and the values agree.
        let shared = own_after.effect_since(&own_after);
        assert_eq!(own.disagreement(&shared, &own_after), None);
        // Where the flag is still unset, it disagrees.
        assert!(own.disagreement(&base.effect_since(&base), &base).is_some());
    }
}
