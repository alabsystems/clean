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
    fn extend_inductives_unchecked(&mut self, inductives: impl Iterator<Item = InductiveVal>);
    fn extend_constructors_unchecked(&mut self, constructors: impl Iterator<Item = ConstructorVal>);
    fn extend_recursors_unchecked(&mut self, recursors: impl Iterator<Item = RecursorVal>);
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
    fn upgrade_axiom_stubs(&mut self, constants: impl Iterator<Item = ConstantInfo>) -> usize;
    /// Discharge a bare `Axiom` carrier stub so the genuine imported inductive of
    /// the same name can register in its place. Returns `true` iff a value-free
    /// `Axiom` of this name existed and was removed. See
    /// [`Environment::discharge_axiom_stub_for_inductive_import`] for the
    /// soundness contract.
    #[must_use]
    fn discharge_axiom_stub_for_inductive_import(&mut self, name: &Name) -> bool;
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
        Environment::init_quot(self);
    }

    #[inline]
    fn clone_pruned_shadowing_overlay(&self, shadowed_names: &HashSet<Name>) -> Environment {
        Environment::clone_pruned_shadowing_overlay(self, shadowed_names)
    }

    #[inline]
    fn add_decl_unchecked(&mut self, decl: Declaration) {
        Environment::add_decl_unchecked(self, decl);
    }

    #[inline]
    fn add_decl_structural(&mut self, decl: Declaration) -> Result<(), EnvError> {
        Environment::add_decl_structural(self, decl)
    }

    #[inline]
    fn set_param_names(&mut self, name: Name, names: Vec<String>) {
        Environment::set_param_names(self, name, names);
    }

    #[inline]
    fn set_param_infos(&mut self, name: Name, infos: Vec<(String, crate::expr::BinderInfo)>) {
        Environment::set_param_infos(self, name, infos);
    }

    #[inline]
    fn register_structure_fields(
        &mut self,
        struct_name: Name,
        field_names: Vec<Name>,
    ) -> Result<(), EnvError> {
        Environment::register_structure_fields(self, struct_name, field_names)
    }

    #[inline]
    fn register_recursor_unchecked(&mut self, rec_val: RecursorVal) {
        Environment::register_recursor_unchecked(self, rec_val);
    }

    #[inline]
    fn extend_constants_unchecked(&mut self, constants: impl Iterator<Item = ConstantInfo>) {
        Environment::extend_constants_unchecked(self, constants);
    }

    #[inline]
    fn extend_constants_structural(
        &mut self,
        constants: impl Iterator<Item = ConstantInfo>,
    ) -> Vec<(Name, EnvError)> {
        Environment::extend_constants_structural(self, constants)
    }

    #[inline]
    fn extend_inductives_unchecked(&mut self, inductives: impl Iterator<Item = InductiveVal>) {
        Environment::extend_inductives_unchecked(self, inductives);
    }

    #[inline]
    fn extend_constructors_unchecked(
        &mut self,
        constructors: impl Iterator<Item = ConstructorVal>,
    ) {
        Environment::extend_constructors_unchecked(self, constructors);
    }

    #[inline]
    fn extend_recursors_unchecked(&mut self, recursors: impl Iterator<Item = RecursorVal>) {
        Environment::extend_recursors_unchecked(self, recursors);
    }

    #[inline]
    fn register_persistent_extension(&mut self, name: Name) -> bool {
        Environment::register_persistent_extension(self, name)
    }

    #[inline]
    fn add_persistent_extension_entries(
        &mut self,
        name: &Name,
        module_idx: usize,
        entries: Vec<EnvExtensionEntry>,
    ) {
        Environment::add_persistent_extension_entries(self, name, module_idx, entries);
    }

    #[inline]
    fn get_persistent_extension_state(&self, name: &Name) -> Option<&PersistentEnvExtensionState> {
        Environment::get_persistent_extension_state(self, name)
    }

    #[inline]
    fn get_persistent_extension_module_entries(
        &self,
        name: &Name,
        module_idx: usize,
    ) -> Option<&[EnvExtensionEntry]> {
        Environment::get_persistent_extension_module_entries(self, name, module_idx)
    }

    #[inline]
    fn register_inductive(&mut self, ind_val: InductiveVal) {
        Environment::register_inductive(self, ind_val);
    }

    #[inline]
    fn register_constructor(&mut self, ctor_val: ConstructorVal) {
        Environment::register_constructor(self, ctor_val);
    }

    #[inline]
    fn register_recursor(&mut self, rec_val: RecursorVal) {
        Environment::register_recursor(self, rec_val);
    }

    #[inline]
    fn set_reducibility(&mut self, name: &Name, reducibility: Reducibility) -> bool {
        Environment::set_reducibility(self, name, reducibility)
    }

    #[inline]
    fn upgrade_axiom_stubs(&mut self, constants: impl Iterator<Item = ConstantInfo>) -> usize {
        Environment::upgrade_axiom_stubs(self, constants)
    }

    #[inline]
    fn discharge_axiom_stub_for_inductive_import(&mut self, name: &Name) -> bool {
        Environment::discharge_axiom_stub_for_inductive_import(self, name)
    }

    #[inline]
    fn init_native_reducers(&mut self) {
        Environment::init_native_reducers(self);
    }

    #[inline]
    fn init_arith_native_reducers(&mut self) {
        Environment::init_arith_native_reducers(self);
    }

    #[inline]
    fn materialize_extension_states(&mut self) {
        Environment::materialize_extension_states(self);
    }

    #[inline]
    fn export_extension_states(&self) -> Vec<(Name, Vec<EnvExtensionEntry>)> {
        Environment::export_extension_states(self)
    }
}
