// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A LOCAL KERNEL FACT's environment delta: everything one elaboration did to
//! an [`Environment`], recorded so the same compiler can replay it later
//! without elaborating or re-checking (Trust TG6, decision
//! `COMPILE-TIME-FACTS-1`).
//!
//! # What it is for
//!
//! Trust's compiler checks the Clean islands of a crate on every build. The
//! owner's rule (2026-11-05) is that a discharged kernel obligation is a fact:
//! while the content it depends on is unchanged, the compiler reuses it and
//! does not prove it again. Trust keys the fact by that content (island bytes,
//! imported terms, upstream environments, the prelude, the kernel theory, the
//! compiler identity) and stores this delta as its body. A hit APPLIES the
//! delta to the environment the key names; it does not elaborate or check.
//!
//! # What it carries
//!
//! Every component of the environment the elaboration changed, with its value
//! AFTER, so `before + delta == after`:
//!
//! * the keyed tables (constants, inductive records, structure metadata,
//!   classes and instances, simp/aesop/grind data, aliases, bindings, hint and
//!   attribute sets, parameter names, options, …) entry by entry;
//! * the TRANSIENT provenance the kernel keeps out of serialization —
//!   `declaration_verification` and the codata origins — exactly as the
//!   producing check recorded it, and the extension states named in
//!   [`DELTA_CARRIED_EXTENSIONS`] (each definition's value binder names,
//!   which a later named argument reads; `value_binder_names`), entry by
//!   entry; and of the csimp source state (`Clean.compiler.csimpSource`)
//!   the compilation point the elaborator records for every declaration,
//!   as the name with the rules its body resolved to. Applying records the
//!   point against the target's own rule events after checking that they
//!   resolve to those rules, so no event position or local-rule token
//!   crosses a process. The provenance is the one capability the delta adds:
//!   a declaration replayed from a local fact carries the `FullKernelCheck`
//!   stamp of the check that produced it in an earlier process of the same
//!   compiler. `COMPILE-TIME-FACTS-1` makes that a discharge for a fact made
//!   and stored on the same machine by the same compiler identity; nothing
//!   else may apply a delta ([`super::TrustedEnvExt::apply_local_fact_delta`]
//!   is ledgered in `data/env_bypass_census.json`);
//! * every other serialized field (the prelude's lazy-initialisation flags,
//!   the mode, the registration counters, …) GENERICALLY through `serde`, as
//!   its bytes after, so a field added to [`Environment`] later is covered
//!   without editing this file.
//!
//! # What it does not carry, and why that is sound
//!
//! Elaborator-private state: the elaborator's `FileContext` (namespaces,
//! notation, variables, scoped instances) and the typed extension states
//! named in [`ELABORATION_PRIVATE_EXTENSIONS`] (`Clean.elab.declaredIn`,
//! `Clean.elab.mutualLift`, `Clean.olean.scopedInstances`), which export no
//! entries. None of it is read by the kernel or by anything that consumes a
//! checked environment; only a later ELABORATION reads it (every reader is in
//! `clean_elab`, and `clean_olean` writes it only into an `.olean` Clean
//! exports, which no keyed session does). Trust's keyed session therefore
//! marks itself elaboration-stale after a hit and rebuilds by real
//! elaboration before it elaborates anything else.
//!
//! Every OTHER typed extension state is refused, not dropped: an elaboration
//! that writes one stores no fact. The `@[implemented_by]` ORDER record
//! (`Clean.compiler.implementedByOrder`) is why: it exports nothing either,
//! but every compiled lane reads it (`clean_compiler::implemented_by_order`),
//! so a delta that dropped it would hand those lanes an environment whose
//! refusal had vanished. A write is counted per state
//! (`ExtensionStateHolder::writes`), so a state added later is refused until
//! someone shows it is elaboration-private and lists it.
//!
//! # Fail-closed construction
//!
//! [`Environment::local_fact_delta_since`] refuses (and Trust then stores no
//! fact) when the elaboration changed something the delta cannot replay: the
//! kernel theory, the native reducer set, the lazy constant source, the
//! prelude aliases, an exported extension entry (the csimp source state's
//! snapshot excepted, and only when compilation points are its whole change:
//! `csimp::compiled_since`), or a typed extension state outside
//! [`ELABORATION_PRIVATE_EXTENSIONS`] and [`DELTA_CARRIED_EXTENSIONS`]. It then APPLIES the delta
//! it built to a copy of `before` and compares the result with `after` over
//! every component ([`Environment::local_fact_difference`]); any difference
//! refuses. A delta that exists therefore reproduces its `after` exactly, by
//! construction, in the process that made it.

use std::collections::BTreeMap;
use std::fmt::{self, Display};
use std::hash::Hash;

use hashbrown::{HashMap, HashSet};
use serde::ser::{self, Serialize};
use serde::{Deserialize, Serialize as SerializeDerive};

use super::Environment;
use crate::name::Name;

/// The delta format. Part of every Trust fact key, so a format change misses.
pub const LOCAL_FACT_DELTA_FORMAT: &str = "clean_kernel.local_fact_delta.v3";

/// The typed extension states a delta may leave out because only a later
/// elaboration reads them (module docs). Writing any other one refuses.
pub const ELABORATION_PRIVATE_EXTENSIONS: &[&str] = &[
    "Clean.elab.declaredIn",
    "Clean.elab.mutualLift",
    "Clean.olean.scopedInstances",
];

/// The typed extension states a delta CARRIES, by type, as a typed
/// component: per-name tables the kernel owns (module docs). A write to one
/// is replayed, not refused. Of the csimp source state only compilation
/// points are carried ([`super::csimp::compiled_since`]), and of the
/// attribute extension only appended registrations
/// ([`super::ext_attr::tags_since`]); any other change to either refuses.
pub const DELTA_CARRIED_EXTENSIONS: &[&str] = &[
    super::value_binder_names::VALUE_BINDER_NAMES_EXTENSION,
    super::csimp::CSIMP_SOURCE_EXTENSION,
    super::ext_attr::ATTR_EXT_NAME,
];

/// Why a delta could not be built or applied.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FactDeltaError {
    /// The elaboration changed state a delta cannot replay; no fact may be
    /// stored for it.
    Unrepresentable(String),
    /// The delta does not fit the environment it is applied to (an entry it
    /// adds is present, or one it changes is absent): the environment is not
    /// the one the fact's key names.
    BaseMismatch(String),
    /// The generic field capture or reassembly failed.
    Encoding(String),
}

impl Display for FactDeltaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unrepresentable(why) => write!(f, "not representable as a local fact: {why}"),
            Self::BaseMismatch(why) => write!(f, "the fact does not fit this environment: {why}"),
            Self::Encoding(why) => write!(f, "local fact encoding: {why}"),
        }
    }
}

impl std::error::Error for FactDeltaError {}

/// One keyed table's changes: each changed key, its value BEFORE (`None`:
/// absent) and its value after (`None`: removed). Sorted by key. Applying it
/// checks the before value, so a delta never overwrites an entry the
/// producing environment did not have.
#[derive(Clone, Debug, SerializeDerive, Deserialize)]
#[serde(bound(serialize = "K: Serialize, V: Serialize"))]
#[serde(bound(deserialize = "K: Deserialize<'de> + Eq + Hash, V: Deserialize<'de>"))]
struct MapDelta<K, V> {
    changed: Vec<(K, Option<V>, Option<V>)>,
}

impl<K, V> Default for MapDelta<K, V> {
    fn default() -> Self {
        Self {
            changed: Vec::new(),
        }
    }
}

fn map_delta<K, V>(before: &HashMap<K, V>, after: &HashMap<K, V>) -> MapDelta<K, V>
where
    K: Eq + Hash + Clone + Ord,
    V: PartialEq + Clone,
{
    let mut changed = Vec::new();
    for (key, value) in after {
        match before.get(key) {
            Some(was) if was == value => {}
            was => changed.push((key.clone(), was.cloned(), Some(value.clone()))),
        }
    }
    for (key, was) in before {
        if !after.contains_key(key) {
            changed.push((key.clone(), Some(was.clone()), None));
        }
    }
    changed.sort_by(|a, b| a.0.cmp(&b.0));
    MapDelta { changed }
}

/// Check that every entry `delta` changes holds its before value in `table`.
fn map_fits<K, V>(
    field: &str,
    table: &HashMap<K, V>,
    delta: &MapDelta<K, V>,
) -> Result<(), FactDeltaError>
where
    K: Eq + Hash + Display,
    V: PartialEq,
{
    for (key, was, _) in &delta.changed {
        if table.get(key) != was.as_ref() {
            return Err(FactDeltaError::BaseMismatch(format!(
                "{field} entry `{key}` is {} here",
                match (was, table.contains_key(key)) {
                    (Some(_), false) => "absent",
                    (None, true) => "present",
                    _ => "different",
                }
            )));
        }
    }
    Ok(())
}

/// A typed map component: read as one table, written one entry at a time.
/// The persistent-extension storage is one, and writes through it keep the
/// matcher index it holds equal to a decode of what it stores.
trait TypedMap<K, V> {
    /// Every entry.
    fn table(&self) -> &HashMap<K, V>;
    /// Set (`Some`) or remove (`None`) the entry for `key`.
    fn put(&mut self, key: &K, value: Option<V>);
}

impl<K: Eq + Hash + Clone, V> TypedMap<K, V> for HashMap<K, V> {
    fn table(&self) -> &HashMap<K, V> {
        self
    }

    fn put(&mut self, key: &K, value: Option<V>) {
        match value {
            Some(value) => {
                self.insert(key.clone(), value);
            }
            None => {
                self.remove(key);
            }
        }
    }
}

impl TypedMap<Name, super::PersistentEnvExtensionState>
    for super::extension_storage::PersistentExtensions
{
    fn table(&self) -> &HashMap<Name, super::PersistentEnvExtensionState> {
        self.states()
    }

    fn put(&mut self, key: &Name, value: Option<super::PersistentEnvExtensionState>) {
        self.set_state(key, value);
    }
}

/// Apply a delta [`map_fits`] accepted.
fn apply_map<K, V>(
    table: &mut impl TypedMap<K, V>,
    delta: &MapDelta<K, V>,
    relocate: impl Fn(&V) -> V,
) where
    V: Clone,
{
    for (key, was, value) in &delta.changed {
        let value = value.as_ref().map(|value| {
            if was.is_none() {
                relocate(value)
            } else {
                value.clone()
            }
        });
        table.put(key, value);
    }
}

/// One set's changes: each changed member and whether it is present after.
#[derive(Clone, Debug, Default, SerializeDerive, Deserialize)]
struct SetDelta {
    changed: Vec<(Name, bool)>,
}

fn set_delta(before: &HashSet<Name>, after: &HashSet<Name>) -> SetDelta {
    let mut changed: Vec<(Name, bool)> = after
        .difference(before)
        .map(|name| (name.clone(), true))
        .collect();
    changed.extend(before.difference(after).map(|name| (name.clone(), false)));
    changed.sort();
    SetDelta { changed }
}

fn set_fits(field: &str, set: &HashSet<Name>, delta: &SetDelta) -> Result<(), FactDeltaError> {
    for (name, present) in &delta.changed {
        if set.contains(name) == *present {
            return Err(FactDeltaError::BaseMismatch(format!(
                "{field} member `{name}` is already {} here",
                if *present { "present" } else { "absent" }
            )));
        }
    }
    Ok(())
}

fn apply_set(set: &mut HashSet<Name>, delta: &SetDelta) {
    for (name, present) in &delta.changed {
        if *present {
            set.insert(name.clone());
        } else {
            set.remove(name);
        }
    }
}

/// A whole-value component: its value before and after, when it changed.
fn whole_delta<T: PartialEq + Clone>(before: &T, after: &T) -> Option<(T, T)> {
    (before != after).then(|| (before.clone(), after.clone()))
}

/// The registration counters. A delta carries how far its elaboration moved
/// each one, never its value: the environment a fact is applied to may have
/// counted further (an unrelated admission, say), and a counter must never move
/// backwards — a cache keyed on `generation` would serve a stale answer.
const COUNTER_FIELDS: &[&str] = &["generation", "simp_registry_revision", "next_instance_seq"];

fn counter_values(env: &Environment) -> [u64; 3] {
    [
        env.generation,
        env.simp_registry_revision,
        env.next_instance_seq,
    ]
}

fn identity<V: Clone>(value: &V) -> V {
    value.clone()
}

/// Declares the typed components ONCE: the delta struct, how it is built, how
/// it is applied, and how [`Environment`]'s typed and transient fields are
/// moved during the generic reassembly. A field listed here is never part of
/// the generic capture; every other serialized field is.
macro_rules! typed_components {
    (
        maps: [$($map:ident: $key:ty => $value:ty),* $(,)?],
        sets: [$($set:ident),* $(,)?],
        wholes: [$($whole:ident: $whole_ty:ty),* $(,)?],
    ) => {
        /// The delta of one elaboration; see the module docs.
        #[derive(Clone, Debug, SerializeDerive, Deserialize)]
        pub struct EnvFactDelta {
            format: String,
            $($map: MapDelta<$key, $value>,)*
            $($set: SetDelta,)*
            $($whole: Option<($whole_ty, $whole_ty)>,)*
            /// Instance-index positions. A position the elaboration assigned
            /// is RELOCATED onto the target's next position (positions are
            /// compared, never counted; see `Environment::instance_seqs`).
            instance_seqs: MapDelta<Name, u64>,
            /// `next_instance_seq` in the producing environment before.
            instance_seq_base: u64,
            /// How far each of [`COUNTER_FIELDS`] moved, in that order.
            counter_steps: [u64; 3],
            // Transient (serde-skipped) provenance, carried explicitly.
            declaration_verification: MapDelta<Name, super::DeclarationVerification>,
            codata_origins: MapDelta<Name, super::CodataOrigin>,
            value_forall_binder_names: MapDelta<Name, super::ValueForallBinderNames>,
            codata_carriers: SetDelta,
            cumulative_ever: Option<(bool, bool)>,
            /// The csimp compilation points the elaboration recorded, in name
            /// order, each with the rules its body resolved to. Applying
            /// records the point against the target's own rule events, after
            /// checking that they resolve to these rules.
            csimp_compiled: Vec<(Name, Vec<super::csimp::Rule>)>,
            /// The attribute registrations the elaboration appended
            /// (`attrExtension`: a theorem proved by `rfl` is tagged
            /// `defeq`), in an order that rebuilds both of its indexes.
            attr_tags: Vec<super::ext_attr::CarriedTag>,
            /// Each declaration those tags touch, with the registrations it
            /// held before: what the target must hold for the tags to fit.
            attr_tag_bases: Vec<(Name, Vec<(Name, u32)>)>,
            /// Every other serialized field that changed, by name, as its
            /// bincode bytes before and after.
            scalars: Vec<(String, Vec<u8>, Vec<u8>)>,
        }

        /// The serialized fields the typed components own.
        const DELTA_TYPED_FIELDS: &[&str] = &[
            $(stringify!($map),)*
            $(stringify!($set),)*
            $(stringify!($whole),)*
            "instance_seqs",
            "extension_states",
        ];

        fn typed_delta(before: &Environment, after: &Environment) -> EnvFactDelta {
            EnvFactDelta {
                format: LOCAL_FACT_DELTA_FORMAT.to_string(),
                $($map: map_delta(before.$map.table(), after.$map.table()),)*
                $($set: set_delta(&before.$set, &after.$set),)*
                $($whole: whole_delta(&before.$whole, &after.$whole),)*
                instance_seqs: map_delta(&before.instance_seqs, &after.instance_seqs),
                instance_seq_base: before.next_instance_seq,
                counter_steps: [0; 3],
                declaration_verification: map_delta(
                    &before.declaration_verification,
                    &after.declaration_verification,
                ),
                codata_origins: map_delta(&before.codata_origins, &after.codata_origins),
                value_forall_binder_names: map_delta(
                    before.value_binder_table(),
                    after.value_binder_table(),
                ),
                codata_carriers: set_delta(&before.codata_carriers, &after.codata_carriers),
                cumulative_ever: whole_delta(&before.cumulative_ever, &after.cumulative_ever),
                csimp_compiled: Vec::new(),
                attr_tags: Vec::new(),
                attr_tag_bases: Vec::new(),
                scalars: Vec::new(),
            }
        }

        /// Whether every typed component of `delta` fits `env`; changes nothing.
        fn typed_fits(env: &Environment, delta: &EnvFactDelta) -> Result<(), FactDeltaError> {
            $(map_fits(stringify!($map), env.$map.table(), &delta.$map)?;)*
            $(set_fits(stringify!($set), &env.$set, &delta.$set)?;)*
            $(if let Some((was, _)) = &delta.$whole {
                if env.$whole != *was {
                    return Err(FactDeltaError::BaseMismatch(format!(
                        "`{}` is different here",
                        stringify!($whole)
                    )));
                }
            })*
            map_fits("instance_seqs", &env.instance_seqs, &delta.instance_seqs)?;
            map_fits(
                "declaration_verification",
                &env.declaration_verification,
                &delta.declaration_verification,
            )?;
            map_fits("codata_origins", &env.codata_origins, &delta.codata_origins)?;
            map_fits(
                "value_forall_binder_names",
                env.value_binder_table(),
                &delta.value_forall_binder_names,
            )?;
            set_fits("codata_carriers", &env.codata_carriers, &delta.codata_carriers)?;
            super::csimp::compiled_fits(env, &delta.csimp_compiled)
                .map_err(FactDeltaError::BaseMismatch)?;
            super::ext_attr::tags_fit(env, &delta.attr_tag_bases)
                .map_err(FactDeltaError::BaseMismatch)?;
            if let Some((was, _)) = delta.cumulative_ever {
                if env.cumulative_ever != was {
                    return Err(FactDeltaError::BaseMismatch(
                        "`cumulative_ever` is different here".to_string(),
                    ));
                }
            }
            Ok(())
        }

        /// Apply the typed components [`typed_fits`] accepted.
        fn apply_typed(env: &mut Environment, delta: &EnvFactDelta) {
            // The persistent-extension storage re-derives the matcher index
            // it holds when a delta replaces the matcher entries.
            $(apply_map(&mut env.$map, &delta.$map, identity);)*
            $(apply_set(&mut env.$set, &delta.$set);)*
            $(if let Some((_, value)) = &delta.$whole {
                env.$whole = value.clone();
            })*
            let here = env.next_instance_seq;
            let base = delta.instance_seq_base;
            apply_map(&mut env.instance_seqs, &delta.instance_seqs, |seq| {
                if *seq >= base { seq - base + here } else { *seq }
            });
            apply_map(&mut env.declaration_verification, &delta.declaration_verification, identity);
            apply_map(&mut env.codata_origins, &delta.codata_origins, identity);
            // A carried extension state: written only when the delta
            // changes it, so a hit that records no binder names leaves the
            // state untouched.
            if !delta.value_forall_binder_names.changed.is_empty() {
                apply_map(
                    env.value_binder_table_mut(),
                    &delta.value_forall_binder_names,
                    identity,
                );
            }
            apply_set(&mut env.codata_carriers, &delta.codata_carriers);
            // A carried extension state, written only when the delta
            // records a compilation point (`typed_fits` checked the rules).
            if !delta.csimp_compiled.is_empty() {
                super::csimp::record_compiled(
                    env,
                    delta.csimp_compiled.iter().map(|(name, _)| name.clone()),
                );
            }
            if !delta.attr_tags.is_empty() {
                super::ext_attr::apply_tags(env, &delta.attr_tags);
            }
            if let Some((_, value)) = delta.cumulative_ever {
                env.cumulative_ever = value;
            }
        }

        /// Move every typed component and every transient (serde-skipped)
        /// field from `from` to `to`. Together with the generic capture this
        /// is every field of [`Environment`]; the tests pin both halves.
        fn transplant_heavy(from: &mut Environment, to: &mut Environment) {
            $(to.$map = std::mem::take(&mut from.$map);)*
            $(to.$set = std::mem::take(&mut from.$set);)*
            $(to.$whole = std::mem::take(&mut from.$whole);)*
            to.instance_seqs = std::mem::take(&mut from.instance_seqs);
            to.extension_states = std::mem::take(&mut from.extension_states);
            // The serde-skipped fields (pinned against the struct by
            // `tests::transient_fields_are_exactly_the_serde_skipped_ones`).
            to.lazy_source = from.lazy_source.take();
            to.declaration_verification = std::mem::take(&mut from.declaration_verification);
            to.codata_origins = std::mem::take(&mut from.codata_origins);
            to.codata_carriers = std::mem::take(&mut from.codata_carriers);
            to.cumulative_ever = from.cumulative_ever;
            to.native_reducers = std::mem::take(&mut from.native_reducers);
            to.kernel_theory = from.kernel_theory;
            // A function of the environment's content, recomputed on demand.
            to.native_fold_cache = Default::default();
            to.prelude_aliases = std::mem::take(&mut from.prelude_aliases);
            // Scalar reconstruction can change the meaning of reductions.
            // Derived simp structures must not inherit the old origin.
            to.simp_cache_identity = Default::default();
        }

        impl EnvFactDelta {
            /// How many entries the delta changes, for a one-line summary.
            #[must_use]
            pub fn changed_entries(&self) -> usize {
                0 $(+ self.$map.changed.len())*
                    $(+ self.$set.changed.len())*
                    $(+ usize::from(self.$whole.is_some()))*
                    + self.instance_seqs.changed.len()
                    + self.declaration_verification.changed.len()
                    + self.codata_origins.changed.len()
                    + self.value_forall_binder_names.changed.len()
                    + self.codata_carriers.changed.len()
                    + self.csimp_compiled.len()
                    + self.attr_tags.len()
                    + self.scalars.len()
            }
        }
    };
}

typed_components! {
    maps: [
        constants: Name => super::ConstantInfo,
        constant_origins: Name => super::ConstantOrigin,
        persistent_extensions: Name => super::PersistentEnvExtensionState,
        inductives: Name => crate::inductive::InductiveVal,
        constructors: Name => crate::inductive::ConstructorVal,
        recursors: Name => crate::inductive::RecursorVal,
        quotients: Name => crate::quot::QuotVal,
        structure_fields: Name => Vec<Name>,
        structure_field_defaults: Name => HashMap<Name, crate::expr::Expr>,
        structure_parents: Name => Vec<(Name, Name)>,
        classes: Name => super::KernelClassInfo,
        instances: Name => Vec<super::KernelInstanceInfo>,
        instance_synth_orders: Name => Vec<usize>,
        aesop_rule_sets: Name => super::aesop::AesopRuleSet,
        aesop_target_index: Name => Vec<super::aesop::AesopRule>,
        aesop_hyps_index: Name => Vec<super::aesop::AesopRule>,
        simp_lemmas: Name => super::SimpLemmaInfo,
        export_aliases: Name => Name,
        export_alias_others: Name => Vec<Name>,
        extern_bindings: Name => String,
        implemented_by: Name => Name,
        export_bindings: Name => String,
        deprecated: Name => Option<String>,
        derive_handlers: Name => Vec<Name>,
        param_names: Name => Vec<String>,
        typed_param_names: Name => Vec<Name>,
        param_binder_infos: Name => Vec<crate::expr::BinderInfo>,
        options: String => Option<String>,
    ],
    sets: [
        instance_names,
        declared_aesop_rule_sets,
        inline_hints,
        noinline_hints,
        always_inline_hints,
        macro_inline_hints,
        inline_if_reduce_hints,
        nospecialize_hints,
        specialize_hints,
        csimp_lemmas,
        congr_lemmas,
        ext_lemmas,
        refl_lemmas,
        symm_lemmas,
        coercion_decls,
        match_pattern_decls,
        init_fn_decls,
        default_instance_decls,
        private_decls,
        protected_decls,
        noncomputable_decls,
        partial_decls,
        unsafe_decls,
        local_instance_decls,
        registered_namespaces,
        staged_headers,
    ],
    wholes: [
        aesop_rules: super::aesop::AesopRuleSet,
        aesop_unindexed_rules: Vec<super::aesop::AesopRule>,
        grind_lemmas: Vec<(Name, super::GrindAttrKind)>,
    ],
}

impl EnvFactDelta {
    /// The bincode bytes of this delta (`config::standard()`).
    pub fn encode(&self) -> Result<Vec<u8>, FactDeltaError> {
        bincode::serde::encode_to_vec(self, bincode::config::standard())
            .map_err(|err| FactDeltaError::Encoding(err.to_string()))
    }

    /// Decode a delta, refusing trailing bytes and a different format.
    pub fn decode(bytes: &[u8]) -> Result<Self, FactDeltaError> {
        let (delta, used): (Self, usize) =
            bincode::serde::decode_from_slice(bytes, bincode::config::standard())
                .map_err(|err| FactDeltaError::Encoding(err.to_string()))?;
        if used != bytes.len() {
            return Err(FactDeltaError::Encoding(format!(
                "{} trailing byte(s) after the delta",
                bytes.len() - used
            )));
        }
        if delta.format != LOCAL_FACT_DELTA_FORMAT {
            return Err(FactDeltaError::Encoding(format!(
                "delta format `{}`, expected `{LOCAL_FACT_DELTA_FORMAT}`",
                delta.format
            )));
        }
        Ok(delta)
    }

    /// The first component this delta changes that is SESSION state rather
    /// than a record under one declaration's name: options, the aesop and
    /// grind rule lists, extension entries, instance positions. Trust keys a
    /// fact on the per-name records of what it reaches
    /// ([`Environment::kernel_record_digest`],
    /// [`Environment::elaboration_record_digest`]), so a change it does not
    /// key on may happen only inside a keyed operation; an admission window
    /// that makes one stops the session's use of facts.
    #[must_use]
    pub fn changed_session_table(&self) -> Option<&'static str> {
        [
            ("options", self.options.changed.is_empty()),
            (
                "persistent_extensions",
                self.persistent_extensions.changed.is_empty(),
            ),
            ("aesop_rule_sets", self.aesop_rule_sets.changed.is_empty()),
            (
                "aesop_target_index",
                self.aesop_target_index.changed.is_empty(),
            ),
            ("aesop_hyps_index", self.aesop_hyps_index.changed.is_empty()),
            ("aesop_rules", self.aesop_rules.is_none()),
            (
                "aesop_unindexed_rules",
                self.aesop_unindexed_rules.is_none(),
            ),
            ("grind_lemmas", self.grind_lemmas.is_none()),
            ("instance_seqs", self.instance_seqs.changed.is_empty()),
            ("cumulative_ever", self.cumulative_ever.is_none()),
        ]
        .into_iter()
        .find(|(_, unchanged)| !unchanged)
        .map(|(table, _)| table)
    }

    /// The names of the constants this delta adds or changes, sorted.
    #[must_use]
    pub fn changed_constant_names(&self) -> Vec<&Name> {
        self.constants
            .changed
            .iter()
            .filter(|(_, _, value)| value.is_some())
            .map(|(name, _, _)| name)
            .collect()
    }
}

impl Environment {
    /// The delta from `before` (an earlier state of this environment) to
    /// `self`, checked by replay; see the module docs. `Err` means no local
    /// fact may be stored for this elaboration.
    pub fn local_fact_delta_since(
        &self,
        before: &Environment,
    ) -> Result<EnvFactDelta, FactDeltaError> {
        unreplayable_change(before, self, false)?;
        // The one exported extension state a delta carries: compilation
        // points only, checked against the whole typed csimp state.
        let csimp_compiled = super::csimp::compiled_since(before, self)
            .map_err(|why| FactDeltaError::Unrepresentable(why.to_string()))?;
        let (attr_tags, attr_tag_bases) = super::ext_attr::tags_since(before, self)
            .map_err(|why| FactDeltaError::Unrepresentable(why.to_string()))?;
        if let Some(name) = self
            .extension_states
            .written_since(&before.extension_states)
            .into_iter()
            .find(|name| {
                let name = name.to_string();
                !ELABORATION_PRIVATE_EXTENSIONS.contains(&name.as_str())
                    && !DELTA_CARRIED_EXTENSIONS.contains(&name.as_str())
            })
        {
            return Err(FactDeltaError::Unrepresentable(format!(
                "the elaboration wrote the typed extension state `{name}`, which a delta does \
                 not carry"
            )));
        }
        let mut delta = typed_delta(before, self);
        delta.csimp_compiled = csimp_compiled;
        delta.attr_tags = attr_tags;
        delta.attr_tag_bases = attr_tag_bases;
        let scalars_before = scalar_bytes(before)?;
        let scalars_after = scalar_bytes(self)?;
        if scalars_before.keys().ne(scalars_after.keys()) {
            return Err(FactDeltaError::Encoding(
                "the two environments serialize different fields".to_string(),
            ));
        }
        delta.scalars = scalars_after
            .into_iter()
            .filter(|(field, _)| !COUNTER_FIELDS.contains(field))
            .filter_map(|(field, bytes)| {
                let was = &scalars_before[field];
                (*was != bytes).then(|| (field.to_string(), was.clone(), bytes))
            })
            .collect();
        let (was, now) = (counter_values(before), counter_values(self));
        for (index, field) in COUNTER_FIELDS.iter().enumerate() {
            delta.counter_steps[index] = now[index].checked_sub(was[index]).ok_or_else(|| {
                FactDeltaError::Unrepresentable(format!("the counter `{field}` moved backwards"))
            })?;
        }
        // The replay check: the delta must rebuild `self` from `before`.
        let mut replayed = before.clone();
        replayed.apply_local_fact_delta(&delta)?;
        if let Some(difference) = replayed.local_fact_difference(self) {
            return Err(FactDeltaError::Unrepresentable(format!(
                "a replay of the delta differs from the checked environment in {difference}"
            )));
        }
        Ok(delta)
    }

    /// Apply a local fact's delta: the environment the fact's key names
    /// becomes the environment its elaboration produced, with no elaboration
    /// and NO kernel check — the delta's declarations carry the stamps the
    /// producing check recorded. The ONLY caller outside this module is
    /// [`super::TrustedEnvExt::apply_local_fact_delta`], ledgered in
    /// `data/env_bypass_census.json` (row `local-fact-delta`).
    ///
    /// Every check runs before anything changes: every entry the delta
    /// changes must hold its before value here, and every counter must have
    /// room. On `Err` this environment is unchanged.
    pub(crate) fn apply_local_fact_delta(
        &mut self,
        delta: &EnvFactDelta,
    ) -> Result<(), FactDeltaError> {
        if delta.format != LOCAL_FACT_DELTA_FORMAT {
            return Err(FactDeltaError::Encoding(format!(
                "delta format `{}`, expected `{LOCAL_FACT_DELTA_FORMAT}`",
                delta.format
            )));
        }
        typed_fits(self, delta)?;
        let counters = counter_values(self);
        let mut moved = [0u64; 3];
        for (index, field) in COUNTER_FIELDS.iter().enumerate() {
            moved[index] = counters[index]
                .checked_add(delta.counter_steps[index])
                .ok_or_else(|| {
                    FactDeltaError::BaseMismatch(format!("the counter `{field}` would overflow"))
                })?;
        }
        if !delta.scalars.is_empty() {
            // Checks its before bytes first, then swaps in a rebuilt
            // environment only once it has decoded.
            self.reassemble_scalars(&delta.scalars)?;
        }
        // A change only to operational transparency retains the source declaration.
        for (name, before, after) in &delta.constants.changed {
            if let Some(before) = before {
                let same_declaration = after.as_ref().is_some_and(|after| {
                    before.name == after.name
                        && before.kind == after.kind
                        && before.level_params == after.level_params
                        && before.type_ == after.type_
                        && before.value == after.value
                });
                if !same_declaration {
                    self.extension_states.forget_declaration(name);
                }
            }
        }
        apply_typed(self, delta);
        self.generation = moved[0];
        self.simp_registry_revision = moved[1];
        self.next_instance_seq = moved[2];
        // Registry-only replays do not reconstruct scalar state. Rotate for
        // entry changes and for register/remove churn with an unchanged map.
        if !delta.simp_lemmas.changed.is_empty() || delta.counter_steps[1] != 0 {
            self.simp_cache_identity.registry_changed();
        }
        Ok(())
    }

    /// The first component in which `self` and `other` differ, over every
    /// component a local fact carries, or `None` when they agree. Elaborator-
    /// private state (unexported extension states) is not compared: a fact
    /// does not carry it (module docs).
    #[must_use]
    pub fn local_fact_difference(&self, other: &Environment) -> Option<String> {
        if let Err(why) = unreplayable_change(self, other, true) {
            return Some(why.to_string());
        }
        if let Some(change) = self.effect_since(other).first_change() {
            return Some(change);
        }
        // What an effect leaves out: the registration counters, the staged
        // headers and the sticky cumulativity flag.
        if self.generation != other.generation {
            return Some("environment field `generation`".to_string());
        }
        if self.simp_registry_revision != other.simp_registry_revision {
            return Some("environment field `simp_registry_revision`".to_string());
        }
        if self.next_instance_seq != other.next_instance_seq {
            return Some("environment field `next_instance_seq`".to_string());
        }
        if self.instance_seqs != other.instance_seqs {
            return Some("environment field `instance_seqs`".to_string());
        }
        if self.staged_headers != other.staged_headers {
            return Some("environment field `staged_headers`".to_string());
        }
        if self.cumulative_ever != other.cumulative_ever {
            return Some("environment field `cumulative_ever`".to_string());
        }
        None
    }

    /// Replace the generically captured fields named in `scalars` with their
    /// bytes, keeping every other field: capture this environment's light
    /// fields in serialization order, splice, decode, and move the typed and
    /// transient fields back in.
    fn reassemble_scalars(
        &mut self,
        scalars: &[(String, Vec<u8>, Vec<u8>)],
    ) -> Result<(), FactDeltaError> {
        let current = OrderedCapture::capture(self)?;
        let empty = OrderedCapture::capture_typed(&Environment::default())?;
        let replacements: BTreeMap<&str, &[u8]> = scalars
            .iter()
            .map(|(field, _, bytes)| (field.as_str(), bytes.as_slice()))
            .collect();
        for (field, was, _) in scalars {
            match current.fields.iter().find(|(name, _)| name == field) {
                Some((_, Some(bytes))) if bytes == was => {}
                Some((_, Some(_))) => {
                    return Err(FactDeltaError::BaseMismatch(format!(
                        "environment field `{field}` is different here"
                    )));
                }
                _ => {
                    return Err(FactDeltaError::Encoding(format!(
                        "the delta names `{field}`, which is not a generically captured field"
                    )));
                }
            }
        }
        let mut stream = Vec::new();
        for (field, bytes) in &current.fields {
            let piece: &[u8] = match bytes {
                Some(bytes) => replacements.get(field).copied().unwrap_or(bytes),
                None => empty.get(field).ok_or_else(|| {
                    FactDeltaError::Encoding(format!("no empty encoding for `{field}`"))
                })?,
            };
            stream.extend_from_slice(piece);
        }
        let (mut light, used): (Environment, usize) =
            bincode::serde::decode_from_slice(&stream, bincode::config::standard())
                .map_err(|err| FactDeltaError::Encoding(format!("reassembly: {err}")))?;
        if used != stream.len() {
            return Err(FactDeltaError::Encoding(
                "reassembly left trailing bytes".to_string(),
            ));
        }
        transplant_heavy(self, &mut light);
        *self = light;
        Ok(())
    }
}

/// A change no delta can replay, or `Ok`. With `csimp` false the csimp
/// source state's exported snapshot is left to the caller, which must accept
/// it only through [`super::csimp::compiled_since`]. The attribute
/// extension is compared here by its typed state when `csimp` is true (its
/// export order is a hash map's, so two equal states can export in different
/// orders) and left to [`super::ext_attr::tags_since`] otherwise. Every
/// other exported extension entry is compared either way.
fn unreplayable_change(
    before: &Environment,
    after: &Environment,
    csimp: bool,
) -> Result<(), FactDeltaError> {
    let refuse = |why: &str| Err(FactDeltaError::Unrepresentable(why.to_string()));
    if before.kernel_theory != after.kernel_theory {
        return refuse("the kernel theory changed");
    }
    if before.lazy_source.is_some() || after.lazy_source.is_some() {
        return refuse("the environment has a lazy constant source");
    }
    if !std::sync::Arc::ptr_eq(&before.prelude_aliases, &after.prelude_aliases)
        && before.prelude_aliases != after.prelude_aliases
    {
        return refuse("the prelude aliases changed");
    }
    if before.native_reducers.len() != after.native_reducers.len()
        || before
            .native_reducers
            .keys()
            .any(|name| !after.native_reducers.contains_key(name))
    {
        return refuse("the native reducer set changed");
    }
    let exported = |env: &Environment| {
        let mut states = env.export_extension_states();
        states.retain(|(name, _)| {
            let name = name.to_string();
            name != super::ext_attr::ATTR_EXT_NAME
                && (csimp || name != super::csimp::CSIMP_SOURCE_EXTENSION)
        });
        states
    };
    if csimp && !super::ext_attr::same_registrations(before, after) {
        return refuse(&format!(
            "an exported extension entry changed (`{}`)",
            super::ext_attr::ATTR_EXT_NAME
        ));
    }
    let (was, now) = (exported(before), exported(after));
    if was != now {
        // Name the first state that differs: the refusal is read by whoever
        // has to decide whether that state can be carried.
        let changed = now
            .iter()
            .find(|state| !was.contains(state))
            .or_else(|| was.iter().find(|state| !now.contains(state)))
            .map_or_else(String::new, |(name, _)| format!(" (`{name}`)"));
        return refuse(&format!("an exported extension entry changed{changed}"));
    }
    Ok(())
}

/// The bincode bytes of every serialized field outside the typed components.
fn scalar_bytes(env: &Environment) -> Result<BTreeMap<&'static str, Vec<u8>>, FactDeltaError> {
    Ok(OrderedCapture::capture(env)?
        .fields
        .into_iter()
        .filter_map(|(field, bytes)| bytes.map(|bytes| (field, bytes)))
        .collect())
}

// ---------------------------------------------------------------------------
// Generic, ordered field capture
// ---------------------------------------------------------------------------

/// Every serialized field of an [`Environment`], in serialization order: the
/// bincode bytes of each generically captured field, `None` for a typed one
/// (or, in `typed` mode, the reverse).
struct OrderedCapture {
    typed: bool,
    fields: Vec<(&'static str, Option<Vec<u8>>)>,
}

impl OrderedCapture {
    fn capture(env: &Environment) -> Result<Self, FactDeltaError> {
        let mut capture = Self {
            typed: false,
            fields: Vec::new(),
        };
        env.serialize(&mut capture)
            .map_err(|err| FactDeltaError::Encoding(err.0))?;
        Ok(capture)
    }

    /// The bytes of the typed fields only, by name.
    fn capture_typed(env: &Environment) -> Result<BTreeMap<&'static str, Vec<u8>>, FactDeltaError> {
        let mut capture = Self {
            typed: true,
            fields: Vec::new(),
        };
        env.serialize(&mut capture)
            .map_err(|err| FactDeltaError::Encoding(err.0))?;
        Ok(capture
            .fields
            .into_iter()
            .filter_map(|(field, bytes)| bytes.map(|bytes| (field, bytes)))
            .collect())
    }
}

#[derive(Debug)]
struct CaptureError(String);

impl Display for CaptureError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for CaptureError {}

impl ser::Error for CaptureError {
    fn custom<T: Display>(msg: T) -> Self {
        Self(msg.to_string())
    }
}

impl ser::SerializeStruct for &mut OrderedCapture {
    type Ok = ();
    type Error = CaptureError;

    fn serialize_field<T: ?Sized + Serialize>(
        &mut self,
        key: &'static str,
        value: &T,
    ) -> Result<(), CaptureError> {
        let typed = DELTA_TYPED_FIELDS.contains(&key);
        if typed != self.typed {
            self.fields.push((key, None));
            return Ok(());
        }
        let bytes = bincode::serde::encode_to_vec(value, bincode::config::standard())
            .map_err(|err| CaptureError(format!("field `{key}`: {err}")))?;
        self.fields.push((key, Some(bytes)));
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

impl ser::Serializer for &mut OrderedCapture {
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
#[path = "fact_delta_tests.rs"]
mod tests;
