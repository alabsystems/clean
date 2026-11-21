// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Lean 4.36 `importModulesCore` at exported or private level for ordinary execution.

use super::{NativeImportHeaders, StableCharProgramCheck, PRELUDE};
use crate::{TypedImport, TypedImportFlags};
use clean_kernel::Name;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Copy, PartialEq, Eq)]
struct ImportState {
    all: bool,
    exported: bool,
    data: bool,
    meta: bool,
    runtime_phase: bool,
    comptime_phase: bool,
}

impl ImportState {
    fn descend(self, flags: &TypedImportFlags, private_level: bool) -> Option<Self> {
        let TypedImportFlags::LeanV2 {
            is_exported,
            import_all,
            is_meta,
        } = *flags
        else {
            return None;
        };
        let data = self.data && (is_exported || self.all);
        let all = private_level || self.all && import_all;
        let meta = self.meta || data && is_meta;
        (data || all || meta).then_some(Self {
            all,
            exported: self.exported && is_exported,
            data,
            meta,
            runtime_phase: all || !meta,
            comptime_phase: all || meta,
        })
    }

    fn join(self, prior: Self) -> Self {
        Self {
            all: self.all || prior.all,
            exported: self.exported || prior.exported,
            data: self.data || prior.data,
            meta: self.meta || prior.meta,
            runtime_phase: self.runtime_phase || prior.runtime_phase,
            comptime_phase: self.comptime_phase || prior.comptime_phase,
        }
    }

    fn imports(self, headers: &NativeImportHeaders) -> &[TypedImport] {
        if !self.data {
            headers.ir.as_deref().unwrap_or_default()
        } else if self.all {
            &headers.private
        } else {
            &headers.public
        }
    }
}

impl StableCharProgramCheck {
    pub(super) fn all_phases(&self, inside_module: bool, roots: &[TypedImport]) -> bool {
        enum Visit<'a> {
            Enter(&'a Name, ImportState),
            Finish(&'a Name, ImportState),
        }

        if inside_module
            && roots.iter().any(|root| {
                !self
                    .imports
                    .get(&root.module_name)
                    .is_some_and(|h| h.is_module)
            })
        {
            return false;
        }
        let root = ImportState {
            all: true,
            exported: inside_module,
            data: true,
            meta: false,
            runtime_phase: false,
            comptime_phase: false,
        };
        let children =
            |state: ImportState, edge: &TypedImport| state.descend(&edge.flags, !inside_module);
        let mut todo: Vec<_> = roots
            .iter()
            .rev()
            .filter_map(|edge| Some(Visit::Enter(&edge.module_name, children(root, edge)?)))
            .collect();
        let mut modules = HashMap::new();
        let mut active = HashSet::new();
        while let Some(step) = todo.pop() {
            let (name, incoming) = match step {
                Visit::Enter(name, incoming) => (name, incoming),
                Visit::Finish(name, state) => {
                    active.remove(name);
                    modules.insert(name, state);
                    continue;
                }
            };
            let Some(headers) = self.imports.get(name) else {
                // The checked graph did not capture this IR-only dependency's ownership.
                return false;
            };
            let selected = match modules.get(name).copied() {
                Some(prior) => {
                    let merged = incoming.join(prior);
                    if merged == prior {
                        continue;
                    }
                    modules.insert(name, merged);
                    // Lean records the join, then revisits the previously selected mainModule?
                    // using the incoming path flags captured by its local goRec function.
                    prior
                }
                None => {
                    if !active.insert(name) {
                        return false;
                    }
                    todo.push(Visit::Finish(name, incoming));
                    incoming
                }
            };
            todo.extend(selected.imports(headers).iter().rev().filter_map(|edge| {
                Some(Visit::Enter(&edge.module_name, children(incoming, edge)?))
            }));
        }
        // finalizeImport requires a main ModuleData for every included module.
        // An initial IR-only visit with no IR can still acquire data on a revisit.
        if modules
            .iter()
            .any(|(name, state)| !state.data && self.imports[*name].ir.is_none())
        {
            return false;
        }
        modules
            .get(&Name::interned(PRELUDE))
            .is_some_and(|s| s.runtime_phase && s.comptime_phase)
    }
}
