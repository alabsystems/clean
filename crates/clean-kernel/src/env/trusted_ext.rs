// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Trusted cross-crate environment mutation hooks for `.olean` import/export paths.
//!
//! Extracted from env/mod.rs for maintainability (see #307).
//! Contains the `TrustedEnvExt` trait and its implementation for `Environment`.

use crate::inductive::{ConstructorVal, InductiveVal, RecursorVal};
use crate::name::Name;
use std::collections::HashSet;

use super::types::{
    ConstantInfo, Declaration, EnvError, EnvExtensionEntry, PersistentEnvExtensionState,
    Reducibility,
};
use super::Environment;

/// Trusted cross-crate environment mutation hooks for `.olean` import/export paths.
///
/// This trait intentionally mirrors a narrow subset of internal mutation methods.
/// Downstream crates must opt in by importing this trait explicitly.
pub trait TrustedEnvExt {
    fn init_quot(&mut self);
    fn clone_pruned_shadowing_overlay(&self, shadowed_names: &HashSet<Name>) -> Environment;
    fn add_decl_unchecked(&mut self, decl: Declaration);
    fn add_decl_structural(&mut self, decl: Declaration) -> Result<(), EnvError>;
    fn set_param_names(&mut self, name: Name, names: Vec<String>);
    fn set_typed_param_names(&mut self, name: Name, names: Vec<Name>);
    fn set_typed_param_infos(&mut self, name: Name, infos: Vec<(Name, crate::expr::BinderInfo)>);
    /// Register parameter names WITH binder kinds (B01): named args bind by
    /// name; positional args fill remaining *explicit* binders in order
    /// (lean4 `src/Lean/Elab/App.lean`, `ElabAppArgs`).
    fn set_param_infos(&mut self, name: Name, infos: Vec<(String, crate::expr::BinderInfo)>);
    fn register_structure_fields(
        &mut self,
        struct_name: Name,
        field_names: Vec<Name>,
    ) -> Result<(), EnvError>;
    fn register_recursor_unchecked(&mut self, rec_val: RecursorVal);
    fn extend_constants_unchecked(&mut self, constants: impl Iterator<Item = ConstantInfo>);
    fn extend_constants_structural(
        &mut self,
        constants: impl Iterator<Item = ConstantInfo>,
    ) -> Vec<(Name, EnvError)>;
    /// UNCHECKED bulk inductive registration — test-only since 2026-08-24
    /// (R1-IND, census row `ind-meta-bulk`): production callers use
    /// [`TrustedEnvExt::extend_inductives_structural`]. Compiled only under
    /// the `test` cfg or the empty `test-fixtures` feature (enabled by
    /// downstream dev-dependencies), so a production call cannot compile.
    #[cfg(any(test, feature = "test-fixtures"))]
    fn extend_inductives_unchecked(&mut self, inductives: impl Iterator<Item = InductiveVal>);
    /// UNCHECKED bulk constructor registration — test-only since 2026-08-24
    /// (R1-IND); see [`TrustedEnvExt::extend_inductives_unchecked`].
    #[cfg(any(test, feature = "test-fixtures"))]
    fn extend_constructors_unchecked(&mut self, constructors: impl Iterator<Item = ConstructorVal>);
    /// UNCHECKED bulk recursor registration — test-only since 2026-08-24
    /// (R1-IND); see [`TrustedEnvExt::extend_inductives_unchecked`].
    #[cfg(any(test, feature = "test-fixtures"))]
    fn extend_recursors_unchecked(&mut self, recursors: impl Iterator<Item = RecursorVal>);
    /// Structural-tier bulk inductive registration (R1-IND): the same O(1)
    /// checks as `extend_constants_structural` (no duplicate level params, no
    /// metavariables, no free variables, `Level::Param` scope) over every
    /// carried expression; failing records are returned, never inserted.
    fn extend_inductives_structural(
        &mut self,
        inductives: impl Iterator<Item = InductiveVal>,
    ) -> Vec<(Name, EnvError)>;
    /// Structural-tier bulk constructor registration (R1-IND) — see
    /// [`TrustedEnvExt::extend_inductives_structural`].
    fn extend_constructors_structural(
        &mut self,
        constructors: impl Iterator<Item = ConstructorVal>,
    ) -> Vec<(Name, EnvError)>;
    /// Structural-tier bulk recursor registration (R1-IND) — see
    /// [`TrustedEnvExt::extend_inductives_structural`]; the validated set
    /// includes every rule `rhs` (ι-reduction participates in kernel
    /// acceptance).
    fn extend_recursors_structural(
        &mut self,
        recursors: impl Iterator<Item = RecursorVal>,
    ) -> Vec<(Name, EnvError)>;
    fn register_persistent_extension(&mut self, name: Name) -> bool;
    fn add_persistent_extension_entries(
        &mut self,
        name: &Name,
        module_idx: usize,
        entries: Vec<EnvExtensionEntry>,
    );
    fn get_persistent_extension_state(&self, name: &Name) -> Option<&PersistentEnvExtensionState>;
    fn get_persistent_extension_module_entries(
        &self,
        name: &Name,
        module_idx: usize,
    ) -> Option<&[EnvExtensionEntry]>;
    fn register_inductive(&mut self, ind_val: InductiveVal);
    fn register_constructor(&mut self, ctor_val: ConstructorVal);
    fn register_recursor(&mut self, rec_val: RecursorVal);
    fn set_reducibility(&mut self, name: &Name, reducibility: Reducibility) -> bool;
    /// LOCAL KERNEL FACT replay (Trust TG6, decision `COMPILE-TIME-FACTS-1`):
    /// apply a delta that [`Environment::local_fact_delta_since`] built and
    /// replay-checked in an earlier process of the SAME compiler, on the same
    /// machine, keyed by everything the elaboration read. The delta's
    /// declarations enter with the verification stamps the producing check
    /// recorded and are NOT re-checked: that is the capability, and it is
    /// accounted as census row `local-fact-delta` in
    /// `data/env_bypass_census.json`. Its one production caller is Trust's
    /// keyed island session (`trust-certify`, `clean_fact`). On `Err` the
    /// environment may be partially changed and must be discarded.
    fn apply_local_fact_delta(
        &mut self,
        delta: &super::EnvFactDelta,
    ) -> Result<(), super::FactDeltaError>;
    /// UNCHECKED axiom-stub upgrade — test-only since 2026-08-24 (R1-STUB,
    /// census row `axiom-stub-upgrade`): production callers use
    /// [`TrustedEnvExt::upgrade_axiom_stubs_checked`]. Compiled only under the
    /// `test` cfg or the empty `test-fixtures` feature (enabled by downstream
    /// dev-dependencies), so a production call cannot compile.
    #[cfg(any(test, feature = "test-fixtures"))]
    fn upgrade_axiom_stubs(&mut self, constants: impl Iterator<Item = ConstantInfo>) -> usize;
    /// Kernel-checked axiom-stub upgrade (R1-STUB, the G4 checked-tier
    /// precedent): per record, the stub must exist, the incoming type must
    /// kernel-match the stub's type, and the incoming value must
    /// `check_type` against it (`UnknownConst`-tolerant for legitimate
    /// forward/external references); a failing record refuses fail-closed —
    /// the stub stays and the named error is returned. See
    /// [`Environment::upgrade_axiom_stubs_checked`] for the full contract.
    fn upgrade_axiom_stubs_checked(
        &mut self,
        constants: impl Iterator<Item = ConstantInfo>,
    ) -> (usize, Vec<(Name, EnvError)>);
    /// Discharge a bare `Axiom` carrier stub so the genuine imported inductive of
    /// the same name can register in its place. Returns `true` iff a value-free
    /// `Axiom` of this name existed and was removed. See
    /// [`Environment::discharge_axiom_stub_for_inductive_import`] for the
    /// soundness contract.
    #[must_use]
    fn discharge_axiom_stub_for_inductive_import(&mut self, name: &Name) -> bool;
    /// Register a Skolem constant as an UNCHECKED axiom (superposition proof
    /// reconstruction). The sole production caller operates on a dropped
    /// scratch clone of the environment; see
    /// `Environment::add_skolem_axiom` for the soundness contract
    /// (R1-SKOLEM, data/env_bypass_census.json row "skolem-axiom").
    fn add_skolem_axiom(&mut self, name: Name, ty: crate::expr::Expr);
    fn init_native_reducers(&mut self);
    fn init_arith_native_reducers(&mut self);
    fn materialize_extension_states(&mut self);
    fn export_extension_states(&self) -> Vec<(Name, Vec<EnvExtensionEntry>)>;
}

const _: fn(&mut Environment, InductiveVal) = Environment::register_inductive_unchecked;
const _: fn(&mut Environment, ConstructorVal) = Environment::register_constructor_unchecked;

impl TrustedEnvExt for Environment {
    #[inline]
    fn init_quot(&mut self) {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a CAPPED SITE in
        // data/env_bypass_census.json `trusted_ext_delegation_sites` (audit r14
        // M14-3): the excuse is capped at `occurrences` calls and requires this
        // comment, so a 29th delegation, or this one with the comment removed, is
        // COUNTED.
        Environment::init_quot(self);
    }

    #[inline]
    fn clone_pruned_shadowing_overlay(&self, shadowed_names: &HashSet<Name>) -> Environment {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a CAPPED SITE in
        // data/env_bypass_census.json `trusted_ext_delegation_sites` (audit r14
        // M14-3): the excuse is capped at `occurrences` calls and requires this
        // comment, so a 29th delegation, or this one with the comment removed, is
        // COUNTED.
        Environment::clone_pruned_shadowing_overlay(self, shadowed_names)
    }

    #[inline]
    fn add_decl_unchecked(&mut self, decl: Declaration) {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a capped site in
        // data/unchecked_decl_ratchet.json (audit r11 M11-6, which retired the
        // whole-file exclusion that had hidden this and everything beside it).
        Environment::add_decl_unchecked(self, decl);
    }

    #[inline]
    fn add_decl_structural(&mut self, decl: Declaration) -> Result<(), EnvError> {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a capped site in
        // data/unchecked_decl_ratchet.json (audit r11 M11-6, which retired the
        // whole-file exclusion that had hidden this and everything beside it).
        Environment::add_decl_structural(self, decl)
    }

    #[inline]
    fn set_param_names(&mut self, name: Name, names: Vec<String>) {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a CAPPED SITE in
        // data/env_bypass_census.json `trusted_ext_delegation_sites` (audit r14
        // M14-3): the excuse is capped at `occurrences` calls and requires this
        // comment, so a 29th delegation, or this one with the comment removed, is
        // COUNTED.
        Environment::set_param_names(self, name, names);
    }

    #[inline]
    fn set_typed_param_names(&mut self, name: Name, names: Vec<Name>) {
        // SOUNDNESS: typed metadata delegation only. The inherent setter keeps
        // exact Name identities and updates the legacy diagnostic projection;
        // this forward adds no declaration or checking authority. Its own
        // one-call cap and comment are required by env_bypass_census.json.
        Environment::set_typed_param_names(self, name, names);
    }

    #[inline]
    fn set_typed_param_infos(&mut self, name: Name, infos: Vec<(Name, crate::expr::BinderInfo)>) {
        // SOUNDNESS: typed binder metadata delegation only. The inherent setter
        // records exact names and binder kinds; this forward adds no declaration
        // or checking authority. Its own one-call cap and comment are required
        // by env_bypass_census.json, independently of the neighboring setter.
        Environment::set_typed_param_infos(self, name, infos);
    }

    #[inline]
    fn set_param_infos(&mut self, name: Name, infos: Vec<(String, crate::expr::BinderInfo)>) {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a CAPPED SITE in
        // data/env_bypass_census.json `trusted_ext_delegation_sites` (audit r14
        // M14-3): the excuse is capped at `occurrences` calls and requires this
        // comment, so a 29th delegation, or this one with the comment removed, is
        // COUNTED.
        Environment::set_param_infos(self, name, infos);
    }

    #[inline]
    fn register_structure_fields(
        &mut self,
        struct_name: Name,
        field_names: Vec<Name>,
    ) -> Result<(), EnvError> {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a CAPPED SITE in
        // data/env_bypass_census.json `trusted_ext_delegation_sites` (audit r14
        // M14-3): the excuse is capped at `occurrences` calls and requires this
        // comment, so a 29th delegation, or this one with the comment removed, is
        // COUNTED.
        Environment::register_structure_fields(self, struct_name, field_names)
    }

    #[inline]
    fn register_recursor_unchecked(&mut self, rec_val: RecursorVal) {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a CAPPED SITE in
        // data/env_bypass_census.json `trusted_ext_delegation_sites` (audit r14
        // M14-3): the excuse is capped at `occurrences` calls and requires this
        // comment, so a 29th delegation, or this one with the comment removed, is
        // COUNTED.
        Environment::register_recursor_unchecked(self, rec_val);
    }

    #[inline]
    fn extend_constants_unchecked(&mut self, constants: impl Iterator<Item = ConstantInfo>) {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a capped site in
        // data/unchecked_decl_ratchet.json (audit r11 M11-6, which retired the
        // whole-file exclusion that had hidden this and everything beside it).
        Environment::extend_constants_unchecked(self, constants);
    }

    #[inline]
    fn extend_constants_structural(
        &mut self,
        constants: impl Iterator<Item = ConstantInfo>,
    ) -> Vec<(Name, EnvError)> {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a capped site in
        // data/unchecked_decl_ratchet.json (audit r11 M11-6, which retired the
        // whole-file exclusion that had hidden this and everything beside it).
        Environment::extend_constants_structural(self, constants)
    }

    #[cfg(any(test, feature = "test-fixtures"))]
    #[inline]
    fn extend_inductives_unchecked(&mut self, inductives: impl Iterator<Item = InductiveVal>) {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a CAPPED SITE in
        // data/env_bypass_census.json `trusted_ext_delegation_sites` (audit r14
        // M14-3): the excuse is capped at `occurrences` calls and requires this
        // comment, so a 29th delegation, or this one with the comment removed, is
        // COUNTED.
        Environment::extend_inductives_unchecked(self, inductives);
    }

    #[cfg(any(test, feature = "test-fixtures"))]
    #[inline]
    fn extend_constructors_unchecked(
        &mut self,
        constructors: impl Iterator<Item = ConstructorVal>,
    ) {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a CAPPED SITE in
        // data/env_bypass_census.json `trusted_ext_delegation_sites` (audit r14
        // M14-3): the excuse is capped at `occurrences` calls and requires this
        // comment, so a 29th delegation, or this one with the comment removed, is
        // COUNTED.
        Environment::extend_constructors_unchecked(self, constructors);
    }

    #[cfg(any(test, feature = "test-fixtures"))]
    #[inline]
    fn extend_recursors_unchecked(&mut self, recursors: impl Iterator<Item = RecursorVal>) {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a CAPPED SITE in
        // data/env_bypass_census.json `trusted_ext_delegation_sites` (audit r14
        // M14-3): the excuse is capped at `occurrences` calls and requires this
        // comment, so a 29th delegation, or this one with the comment removed, is
        // COUNTED.
        Environment::extend_recursors_unchecked(self, recursors);
    }

    #[inline]
    fn extend_inductives_structural(
        &mut self,
        inductives: impl Iterator<Item = InductiveVal>,
    ) -> Vec<(Name, EnvError)> {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a CAPPED SITE in
        // data/env_bypass_census.json `trusted_ext_delegation_sites` (audit r14
        // M14-3): the excuse is capped at `occurrences` calls and requires this
        // comment, so a 29th delegation, or this one with the comment removed, is
        // COUNTED.
        Environment::extend_inductives_structural(self, inductives)
    }

    #[inline]
    fn extend_constructors_structural(
        &mut self,
        constructors: impl Iterator<Item = ConstructorVal>,
    ) -> Vec<(Name, EnvError)> {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a CAPPED SITE in
        // data/env_bypass_census.json `trusted_ext_delegation_sites` (audit r14
        // M14-3): the excuse is capped at `occurrences` calls and requires this
        // comment, so a 29th delegation, or this one with the comment removed, is
        // COUNTED.
        Environment::extend_constructors_structural(self, constructors)
    }

    #[inline]
    fn extend_recursors_structural(
        &mut self,
        recursors: impl Iterator<Item = RecursorVal>,
    ) -> Vec<(Name, EnvError)> {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a CAPPED SITE in
        // data/env_bypass_census.json `trusted_ext_delegation_sites` (audit r14
        // M14-3): the excuse is capped at `occurrences` calls and requires this
        // comment, so a 29th delegation, or this one with the comment removed, is
        // COUNTED.
        Environment::extend_recursors_structural(self, recursors)
    }

    #[inline]
    fn register_persistent_extension(&mut self, name: Name) -> bool {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a CAPPED SITE in
        // data/env_bypass_census.json `trusted_ext_delegation_sites` (audit r14
        // M14-3): the excuse is capped at `occurrences` calls and requires this
        // comment, so a 29th delegation, or this one with the comment removed, is
        // COUNTED.
        Environment::register_persistent_extension(self, name)
    }

    #[inline]
    fn add_persistent_extension_entries(
        &mut self,
        name: &Name,
        module_idx: usize,
        entries: Vec<EnvExtensionEntry>,
    ) {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a CAPPED SITE in
        // data/env_bypass_census.json `trusted_ext_delegation_sites` (audit r14
        // M14-3): the excuse is capped at `occurrences` calls and requires this
        // comment, so a 29th delegation, or this one with the comment removed, is
        // COUNTED.
        Environment::add_persistent_extension_entries(self, name, module_idx, entries);
    }

    #[inline]
    fn get_persistent_extension_state(&self, name: &Name) -> Option<&PersistentEnvExtensionState> {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a CAPPED SITE in
        // data/env_bypass_census.json `trusted_ext_delegation_sites` (audit r14
        // M14-3): the excuse is capped at `occurrences` calls and requires this
        // comment, so a 29th delegation, or this one with the comment removed, is
        // COUNTED.
        Environment::get_persistent_extension_state(self, name)
    }

    #[inline]
    fn get_persistent_extension_module_entries(
        &self,
        name: &Name,
        module_idx: usize,
    ) -> Option<&[EnvExtensionEntry]> {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a CAPPED SITE in
        // data/env_bypass_census.json `trusted_ext_delegation_sites` (audit r14
        // M14-3): the excuse is capped at `occurrences` calls and requires this
        // comment, so a 29th delegation, or this one with the comment removed, is
        // COUNTED.
        Environment::get_persistent_extension_module_entries(self, name, module_idx)
    }

    #[inline]
    fn register_inductive(&mut self, ind_val: InductiveVal) {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a CAPPED SITE in
        // data/env_bypass_census.json `trusted_ext_delegation_sites` (audit r14
        // M14-3): the excuse is capped at `occurrences` calls and requires this
        // comment, so a 29th delegation, or this one with the comment removed, is
        // COUNTED.
        Environment::register_inductive(self, ind_val);
    }

    #[inline]
    fn register_constructor(&mut self, ctor_val: ConstructorVal) {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a CAPPED SITE in
        // data/env_bypass_census.json `trusted_ext_delegation_sites` (audit r14
        // M14-3): the excuse is capped at `occurrences` calls and requires this
        // comment, so a 29th delegation, or this one with the comment removed, is
        // COUNTED.
        Environment::register_constructor(self, ctor_val);
    }

    #[inline]
    fn register_recursor(&mut self, rec_val: RecursorVal) {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a CAPPED SITE in
        // data/env_bypass_census.json `trusted_ext_delegation_sites` (audit r14
        // M14-3): the excuse is capped at `occurrences` calls and requires this
        // comment, so a 29th delegation, or this one with the comment removed, is
        // COUNTED.
        Environment::register_recursor(self, rec_val);
    }

    #[inline]
    fn set_reducibility(&mut self, name: &Name, reducibility: Reducibility) -> bool {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a CAPPED SITE in
        // data/env_bypass_census.json `trusted_ext_delegation_sites` (audit r14
        // M14-3): the excuse is capped at `occurrences` calls and requires this
        // comment, so a 29th delegation, or this one with the comment removed, is
        // COUNTED.
        Environment::set_reducibility(self, name, reducibility)
    }

    #[inline]
    fn apply_local_fact_delta(
        &mut self,
        delta: &super::EnvFactDelta,
    ) -> Result<(), super::FactDeltaError> {
        // SOUNDNESS: the cross-crate door for a LOCAL KERNEL FACT replay. It
        // inserts the delta's declarations with the stamps the producing check
        // recorded, without re-checking them; the delta was built and
        // replay-checked by `local_fact_delta_since` in an earlier process of
        // the same compiler, and Trust keys it by everything that elaboration
        // read (decision COMPILE-TIME-FACTS-1). Accounted as census row
        // `local-fact-delta` in data/env_bypass_census.json.
        Environment::apply_local_fact_delta(self, delta)
    }

    #[cfg(any(test, feature = "test-fixtures"))]
    #[inline]
    fn upgrade_axiom_stubs(&mut self, constants: impl Iterator<Item = ConstantInfo>) -> usize {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a CAPPED SITE in
        // data/env_bypass_census.json `trusted_ext_delegation_sites` (audit r14
        // M14-3): the excuse is capped at `occurrences` calls and requires this
        // comment, so a 29th delegation, or this one with the comment removed, is
        // COUNTED.
        Environment::upgrade_axiom_stubs(self, constants)
    }

    #[inline]
    fn upgrade_axiom_stubs_checked(
        &mut self,
        constants: impl Iterator<Item = ConstantInfo>,
    ) -> (usize, Vec<(Name, EnvError)>) {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a CAPPED SITE in
        // data/env_bypass_census.json `trusted_ext_delegation_sites` (audit r14
        // M14-3): the excuse is capped at `occurrences` calls and requires this
        // comment, so a 29th delegation, or this one with the comment removed, is
        // COUNTED.
        Environment::upgrade_axiom_stubs_checked(self, constants)
    }

    #[inline]
    fn discharge_axiom_stub_for_inductive_import(&mut self, name: &Name) -> bool {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a CAPPED SITE in
        // data/env_bypass_census.json `trusted_ext_delegation_sites` (audit r14
        // M14-3): the excuse is capped at `occurrences` calls and requires this
        // comment, so a 29th delegation, or this one with the comment removed, is
        // COUNTED.
        Environment::discharge_axiom_stub_for_inductive_import(self, name)
    }

    #[inline]
    fn add_skolem_axiom(&mut self, name: Name, ty: crate::expr::Expr) {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a CAPPED SITE in
        // data/env_bypass_census.json `trusted_ext_delegation_sites` (audit r14
        // M14-3): the excuse is capped at `occurrences` calls and requires this
        // comment, so a 29th delegation, or this one with the comment removed, is
        // COUNTED.
        Environment::add_skolem_axiom(self, name, ty);
    }

    #[inline]
    fn init_native_reducers(&mut self) {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a CAPPED SITE in
        // data/env_bypass_census.json `trusted_ext_delegation_sites` (audit r14
        // M14-3): the excuse is capped at `occurrences` calls and requires this
        // comment, so a 29th delegation, or this one with the comment removed, is
        // COUNTED.
        Environment::init_native_reducers(self);
    }

    #[inline]
    fn init_arith_native_reducers(&mut self) {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a CAPPED SITE in
        // data/env_bypass_census.json `trusted_ext_delegation_sites` (audit r14
        // M14-3): the excuse is capped at `occurrences` calls and requires this
        // comment, so a 29th delegation, or this one with the comment removed, is
        // COUNTED.
        Environment::init_arith_native_reducers(self);
    }

    #[inline]
    fn materialize_extension_states(&mut self) {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a CAPPED SITE in
        // data/env_bypass_census.json `trusted_ext_delegation_sites` (audit r14
        // M14-3): the excuse is capped at `occurrences` calls and requires this
        // comment, so a 29th delegation, or this one with the comment removed, is
        // COUNTED.
        Environment::materialize_extension_states(self);
    }

    #[inline]
    fn export_extension_states(&self) -> Vec<(Name, Vec<EnvExtensionEntry>)> {
        // SOUNDNESS: trait delegation only — forwards to the inherent method of
        // the same name and adds no capability; a caller here already holds an
        // `Environment` and could call it directly. Accounted as a CAPPED SITE in
        // data/env_bypass_census.json `trusted_ext_delegation_sites` (audit r14
        // M14-3): the excuse is capped at `occurrences` calls and requires this
        // comment, so a 29th delegation, or this one with the comment removed, is
        // COUNTED.
        Environment::export_extension_states(self)
    }
}
