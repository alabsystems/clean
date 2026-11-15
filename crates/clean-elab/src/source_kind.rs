// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source declaration kind where logical storage intentionally differs.
//!
//! A body-less source `opaque` is an audited kernel axiom (R134), not a checked
//! definition with a value. Keep that trust classification intact while retaining
//! its source kind for Lean-shaped attribute checks. This metadata never supplies
//! a value, changes ConstantKind, or discharges an assumption.

use std::collections::HashMap;
use std::sync::{Arc, OnceLock};

use clean_kernel::env::{
    register_persistent_ext, ConstantKind, EnvExtensionEntry, EnvExtensionEntryData, ExtensionIdx,
    PersistentExtEntry, PersistentExtState,
};
use clean_kernel::{Environment, Name};

#[derive(Clone, Debug)]
struct Entry {
    name: Name,
    kind: ConstantKind,
}

impl PersistentExtEntry for Entry {
    fn to_env_entry(&self) -> EnvExtensionEntry {
        let tag = match self.kind {
            ConstantKind::Definition => 0,
            ConstantKind::Theorem => 1,
            ConstantKind::Opaque => 2,
            ConstantKind::Axiom => 3,
        };
        EnvExtensionEntry {
            name: self.name.clone(),
            data: EnvExtensionEntryData::Scalar(tag),
        }
    }

    fn from_env_entry(entry: &EnvExtensionEntry) -> Option<Self> {
        let EnvExtensionEntryData::Scalar(tag) = &entry.data else {
            return None;
        };
        let kind = match tag {
            0 => ConstantKind::Definition,
            1 => ConstantKind::Theorem,
            2 => ConstantKind::Opaque,
            3 => ConstantKind::Axiom,
            _ => return None,
        };
        Some(Self {
            name: entry.name.clone(),
            kind,
        })
    }
}

#[derive(Clone, Debug, Default)]
struct State(Arc<HashMap<Name, ConstantKind>>);

impl PersistentExtState for State {
    type Entry = Entry;

    fn add_entry(&mut self, entry: &Entry) {
        Arc::make_mut(&mut self.0).insert(entry.name.clone(), entry.kind);
    }

    fn export_entries(&self) -> Vec<EnvExtensionEntry> {
        let mut entries: Vec<_> = self
            .0
            .iter()
            .map(|(name, kind)| {
                Entry {
                    name: name.clone(),
                    kind: *kind,
                }
                .to_env_entry()
            })
            .collect();
        entries.sort_by(|a, b| a.name.cmp(&b.name));
        entries
    }
}

fn index() -> ExtensionIdx {
    static INDEX: OnceLock<ExtensionIdx> = OnceLock::new();
    *INDEX.get_or_init(|| {
        register_persistent_ext::<State>(Name::from_string("Clean.elab.sourceKind"))
    })
}

/// Record a source/storage distinction only after the declaration was admitted.
pub(crate) fn record(env: &mut Environment, name: &Name, kind: ConstantKind) {
    if env
        .get_const(name)
        .is_some_and(|constant| constant.kind != kind)
    {
        env.add_ext_entry::<State>(
            index(),
            &Entry {
                name: name.clone(),
                kind,
            },
        );
    }
}

pub(crate) fn get(env: &Environment, name: &Name) -> Option<ConstantKind> {
    env.get_ext_state::<State>(index())
        .and_then(|state| state.0.get(name).copied())
        .or_else(|| env.get_const(name).map(|constant| constant.kind))
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{Declaration, Expr, Level};

    #[test]
    fn class_source_kind_roundtrip_retains_opaque_restriction_and_axiom_trust() {
        let mut env = Environment::with_prelude();
        let name = Name::from_string("SourceOpaque");
        env.add_decl(Declaration::Axiom {
            name: name.clone(),
            level_params: vec![],
            type_: Expr::sort(Level::succ(Level::zero())),
        })
        .expect("checked type");
        record(&mut env, &name, ConstantKind::Opaque);
        let entries = env
            .get_ext_state::<State>(index())
            .expect("recorded source kind")
            .export_entries();
        let mut imported = Environment::with_prelude();
        imported
            .add_decl(Declaration::Axiom {
                name: name.clone(),
                level_params: vec![],
                type_: Expr::sort(Level::succ(Level::zero())),
            })
            .expect("checked imported type");
        for encoded in entries {
            let entry = Entry::from_env_entry(&encoded).expect("source kind codec");
            imported.add_ext_entry::<State>(index(), &entry);
        }
        assert_eq!(get(&imported, &name), Some(ConstantKind::Opaque));
        assert_eq!(
            imported.get_const(&name).expect("kernel assumption").kind,
            ConstantKind::Axiom
        );
        assert!(crate::class_attribute::register(&mut imported, &name).is_err());
        assert!(!imported.is_class(&name));
    }

    #[test]
    fn class_source_metadata_cannot_promote_stored_definition_to_axiom_target() {
        let mut env = Environment::with_prelude();
        let name = Name::from_string("ValueBearing");
        env.add_decl(Declaration::Definition {
            name: name.clone(),
            level_params: vec![],
            type_: Expr::sort(Level::succ(Level::zero())),
            value: Expr::const_(Name::from_string("Nat"), vec![]),
            is_reducible: false,
        })
        .expect("checked definition");
        record(&mut env, &name, ConstantKind::Axiom);
        assert!(crate::class_attribute::register(&mut env, &name).is_err());
        assert!(!env.is_class(&name));
        assert_eq!(
            env.get_const(&name).expect("definition").kind,
            ConstantKind::Definition
        );
    }
}
