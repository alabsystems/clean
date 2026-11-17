// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Binder NAMES of every imported constant's TYPE telescope.
//!
//! Lean's named arguments (`LT.lt (self := i) a b`, `le_trans (a := x)`,
//! `Nat.rec (motive := M)`) bind by the NAME of a binder of the function's
//! type (`ElabAppArgs`, `Lean/Elab/App.lean`). Clean's kernel `Expr` keeps no
//! binder names, so for an olean-imported constant the elaborator had nothing
//! to match against and refused every named argument ("no binder names are
//! recorded for `LT.lt`", `compare_of_injective_eq_compareOfLessAndEq`,
//! measured 2026-09-12). This module reads the leading `forallE` binder names
//! of each constant's type off the RAW `.olean` object graph at import (the
//! direct/zero-copy path) or off the parsed type (the `ParsedModule` path)
//! into [`TypeBinderNameState`], an in-process environment extension the
//! elaborator consults through [`type_binder_names`] after its own
//! declaration-parameter table. Only names are recorded; binder kinds are
//! read off the kernel type itself.

use std::collections::HashMap;

use clean_kernel::env::{
    register_persistent_ext, EnvExtensionEntry, EnvExtensionEntryData, Environment, ExtensionIdx,
    PersistentExtEntry, PersistentExtState,
};
use clean_kernel::name::Name;

use super::binder_spine::BinderSpine;
use super::ImportError;
use crate::expr::{expr_tags, ParsedExpr};
use crate::module::ParsedConstant;
use crate::region::{is_ptr, CompactedRegion};

/// Constant → the leading `forallE` binder names of its type, outermost
/// first. In-process state, never exported.
#[derive(Clone, Debug, Default)]
pub struct TypeBinderNameState {
    pub names: HashMap<Name, Vec<Name>>,
}

/// Placeholder entry type: the state is filled by the loader directly and
/// carries no persisted entries.
#[derive(Clone, Debug)]
pub struct TypeBinderNameEntry {
    pub constant: Name,
    pub names: Vec<Name>,
}

impl PersistentExtEntry for TypeBinderNameEntry {
    fn to_env_entry(&self) -> EnvExtensionEntry {
        EnvExtensionEntry {
            name: self.constant.clone(),
            data: EnvExtensionEntryData::Scalar(0),
        }
    }

    fn from_env_entry(_entry: &EnvExtensionEntry) -> Option<Self> {
        None
    }
}

impl PersistentExtState for TypeBinderNameState {
    type Entry = TypeBinderNameEntry;

    fn add_entry(&mut self, entry: &Self::Entry) {
        self.names
            .insert(entry.constant.clone(), entry.names.clone());
    }

    fn export_entries(&self) -> Vec<EnvExtensionEntry> {
        Vec::new()
    }
}

static TYPE_BINDER_NAME_IDX: std::sync::OnceLock<ExtensionIdx> = std::sync::OnceLock::new();

/// The extension index of [`TypeBinderNameState`].
pub fn type_binder_name_idx() -> ExtensionIdx {
    *TYPE_BINDER_NAME_IDX.get_or_init(|| {
        register_persistent_ext::<TypeBinderNameState>(Name::from_string(
            "Clean.olean.typeBinderNames",
        ))
    })
}

/// The recorded binder names of `constant`'s type, if it was imported.
#[must_use]
pub fn type_binder_names<'e>(env: &'e Environment, constant: &Name) -> Option<&'e [Name]> {
    env.get_ext_state::<TypeBinderNameState>(type_binder_name_idx())?
        .names
        .get(constant)
        .map(Vec::as_slice)
}

fn record(env: &mut Environment, name: &str, names: Vec<String>) {
    if names.is_empty() {
        return;
    }
    let idx = type_binder_name_idx();
    let state = env.get_ext_state_mut::<TypeBinderNameState>(idx);
    state.names.insert(
        Name::interned(name),
        names.iter().map(|n| Name::interned(n)).collect(),
    );
}

/// The leading `forallE` binder names of the expression at `ptr` in
/// `region`, outermost first (`mdata` wrappers at the spine are looked
/// through). Stops at the first non-`forallE` node.
fn read_leading_forall_names(
    region: &CompactedRegion<'_>,
    mut ptr: u64,
    constant: &str,
) -> Result<Vec<String>, ImportError> {
    let mut out = Vec::new();
    let mut spine = BinderSpine::new(region, constant)?;
    while is_ptr(ptr) {
        spine.visit(ptr)?;
        let offset = region.ptr_to_offset(ptr)?;
        let header = region.read_header_at(offset)?;
        CompactedRegion::require_expr_fields(&header, offset)?;
        let field_base = offset + 8;
        match header.tag {
            // Layout: name, type, body (see `convert_expr_direct`).
            expr_tags::FORALL_E => {
                let name_ptr = region.read_u64_at(field_base)?;
                let body_ptr = region.read_u64_at(field_base + 16)?;
                out.push(region.resolve_name_ptr(name_ptr)?);
                ptr = body_ptr;
            }
            expr_tags::MDATA => {
                ptr = region.read_u64_at(field_base + 8)?;
            }
            _ => break,
        }
    }
    Ok(out)
}

fn parsed_leading_forall_names(ty: &ParsedExpr) -> Vec<String> {
    let mut out = Vec::new();
    let mut e = ty;
    loop {
        match e {
            ParsedExpr::ForallE(name, _, body, _) => {
                out.push(name.clone());
                e = body;
            }
            ParsedExpr::MData(_, inner) => e = inner,
            _ => return out,
        }
    }
}

/// Direct (zero-copy) path: record every constant of the module, reading its
/// type's binder names straight from `region`.
pub(crate) fn record_type_binder_names_from_region<'a>(
    env: &mut Environment,
    region: &CompactedRegion<'_>,
    constants: impl IntoIterator<Item = (&'a str, u64)>,
) -> Result<(), ImportError> {
    for (name, type_ptr) in constants {
        if type_ptr == 0 {
            continue;
        }
        let names = read_leading_forall_names(region, type_ptr, name)?;
        record(env, name, names);
    }
    Ok(())
}

/// `ParsedModule` path: the same table, read off the parsed types.
pub(crate) fn record_type_binder_names_from_parsed(
    env: &mut Environment,
    constants: &[ParsedConstant],
) {
    for c in constants {
        if let Some(ty) = &c.type_ {
            record(env, &c.name, parsed_leading_forall_names(ty));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::ParsedBinderInfo;

    #[test]
    fn test_parsed_forall_spine_yields_names_in_order_and_stops_at_the_body() {
        let body = ParsedExpr::Const("Prop".to_string(), vec![]);
        let inner = ParsedExpr::ForallE(
            "self".to_string(),
            Box::new(body.clone()),
            Box::new(body.clone()),
            ParsedBinderInfo::InstImplicit,
        );
        let outer = ParsedExpr::ForallE(
            "α".to_string(),
            Box::new(body),
            Box::new(ParsedExpr::MData(Vec::new(), Box::new(inner))),
            ParsedBinderInfo::Implicit,
        );
        assert_eq!(
            parsed_leading_forall_names(&outer),
            vec!["α".to_string(), "self".to_string()]
        );
    }

    #[test]
    fn test_recorded_names_are_served_by_constant() {
        let mut env = Environment::new();
        record(
            &mut env,
            "LT.lt",
            vec!["α".into(), "self".into(), "a".into(), "b".into()],
        );
        let got = type_binder_names(&env, &Name::from_string("LT.lt")).expect("recorded");
        assert_eq!(
            got.iter().map(ToString::to_string).collect::<Vec<_>>(),
            vec!["α", "self", "a", "b"]
        );
        assert!(type_binder_names(&env, &Name::from_string("LT.le")).is_none());
    }
}
