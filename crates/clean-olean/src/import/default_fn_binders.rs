// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Binder NAMES of imported `<Struct>.<field>._default` functions.
//!
//! Lean mints, for every structure field declared with a default, a sibling
//! definition `<Struct>.<field>._default` (`mkDefaultFnOfProjFn`,
//! `src/Lean/Structure.lean`) whose value is abstracted with
//! `mkLambdaFVars (usedOnly := true)` over the structure's parameters and the
//! flattened fields the default USES — so its leading lambdas are named after
//! those fields and carry only them. Ground truth on the pinned v4.30.0-rc2
//! (`set_option pp.explicit true`, `#print`):
//!
//! ```text
//! def Preorder.lt._default.{u_2} : {α : Type u_2} → (α → α → Prop) → α → α → Prop :=
//!   fun {α} le => @id (α → α → Prop) fun a b => And (le a b) (Not (le b a))
//! def LinearOrder.min._default.{u_2} :
//!     {α : Type u_2} → (le : α → α → Prop) → @DecidableLE α (@LE.mk α le) → α → α → α :=
//!   fun {α} le toDecidableLE => @id (α → α → α) fun a b => @ite α (le a b) (toDecidableLE a b) a b
//! def Applicative.seqLeft._default.{u, v} : … :=
//!   fun {f} map mapConst seq => @id (…) fun {α β} a b => @seq β α (@map α (β → α) (@Function.const α β) a) b
//! ```
//!
//! Lean's structure-instance elaborator applies such a function BY NAME
//! (`DefaultFields.mkDefaultValue?`, `src/Lean/Elab/StructInst.lean`): each
//! explicit lambda binder is instantiated with the literal's field of that
//! name, each implicit one with a fresh metavariable. Clean's kernel keeps no
//! binder names, so the names would be gone by the time the elaborator sees
//! the value; this module reads them off the RAW `.olean` object graph at
//! import time (the direct/zero-copy path) or off the parsed expression (the
//! `ParsedModule` path) into [`DefaultFnBinderState`], an in-process
//! environment extension the elaborator consults through
//! [`default_fn_binder_idx`]. A `_default` constant with no entry here is a
//! Clean-native one, and the elaborator keeps its positional rule for it.

use std::collections::HashMap;

use clean_kernel::env::{
    register_persistent_ext, EnvExtensionEntry, EnvExtensionEntryData, Environment, ExtensionIdx,
    PersistentExtEntry, PersistentExtState,
};
use clean_kernel::expr::BinderInfo;
use clean_kernel::name::Name;

use super::binder_spine::BinderSpine;
use super::convert_expr::convert_binder_info;
use super::ImportError;
use crate::expr::{expr_tags, ParsedBinderInfo, ParsedExpr, EXPR_DATA_SCALAR_BYTES};
use crate::module::{ConstantKind, ParsedConstant};
use crate::region::{is_ptr, CompactedRegion};

/// `<Struct>.<field>._default` → the leading lambda binders of its VALUE,
/// outermost first, as `(binder name, binder info)`. In-process state, never
/// exported.
#[derive(Clone, Debug, Default)]
pub struct DefaultFnBinderState {
    pub binders: HashMap<Name, Vec<(Name, BinderInfo)>>,
}

/// Placeholder entry type: the state is filled by the loader directly and
/// carries no persisted entries.
#[derive(Clone, Debug)]
pub struct DefaultFnBinderEntry {
    pub default_fn: Name,
    pub binders: Vec<(Name, BinderInfo)>,
}

impl PersistentExtEntry for DefaultFnBinderEntry {
    fn to_env_entry(&self) -> EnvExtensionEntry {
        EnvExtensionEntry {
            name: self.default_fn.clone(),
            data: EnvExtensionEntryData::Scalar(0),
        }
    }

    fn from_env_entry(_entry: &EnvExtensionEntry) -> Option<Self> {
        None
    }
}

impl PersistentExtState for DefaultFnBinderState {
    type Entry = DefaultFnBinderEntry;

    fn add_entry(&mut self, entry: &Self::Entry) {
        self.binders
            .insert(entry.default_fn.clone(), entry.binders.clone());
    }

    fn export_entries(&self) -> Vec<EnvExtensionEntry> {
        Vec::new()
    }
}

static DEFAULT_FN_BINDER_IDX: std::sync::OnceLock<ExtensionIdx> = std::sync::OnceLock::new();

/// The extension index of [`DefaultFnBinderState`]; the elaborator reads it
/// through `Environment::get_ext_state`.
pub fn default_fn_binder_idx() -> ExtensionIdx {
    *DEFAULT_FN_BINDER_IDX.get_or_init(|| {
        register_persistent_ext::<DefaultFnBinderState>(Name::from_string(
            "Clean.olean.defaultFnBinders",
        ))
    })
}

/// Whether `name` is a Lean default-value function, `<projFn>._default`
/// (`mkDefaultFnOfProjFn` appends the component `_default`).
pub(crate) fn is_default_fn_name(name: &str) -> bool {
    name.rsplit_once('.')
        .is_some_and(|(prefix, last)| last == "_default" && !prefix.is_empty())
}

fn record(env: &mut Environment, name: &str, binders: Vec<(String, ParsedBinderInfo)>) {
    let idx = default_fn_binder_idx();
    let state = env.get_ext_state_mut::<DefaultFnBinderState>(idx);
    state.binders.insert(
        Name::interned(name),
        binders
            .into_iter()
            .map(|(n, bi)| (Name::interned(&n), convert_binder_info(bi)))
            .collect(),
    );
}

/// The leading lambda binders of the expression at `ptr` in `region`,
/// outermost first, read off the raw object graph (`mdata` wrappers at the
/// spine are looked through). Stops at the first non-lambda node.
fn read_leading_lambda_binders(
    region: &CompactedRegion<'_>,
    mut ptr: u64,
    constant: &str,
) -> Result<Vec<(String, ParsedBinderInfo)>, ImportError> {
    let mut out = Vec::new();
    let mut spine = BinderSpine::new(region, constant)?;
    while is_ptr(ptr) {
        spine.visit(ptr)?;
        let offset = region.ptr_to_offset(ptr)?;
        let header = region.read_header_at(offset)?;
        CompactedRegion::require_expr_fields(&header, offset)?;
        let field_base = offset + 8;
        let scalar_base = field_base + header.other as usize * 8;
        match header.tag {
            expr_tags::LAM => {
                // Layout: name, type, body; binderInfo is the byte after the
                // cached 8-byte `Expr.Data` (see `convert_expr_direct`).
                let name_ptr = region.read_u64_at(field_base)?;
                let body_ptr = region.read_u64_at(field_base + 16)?;
                let name = region.resolve_name_ptr(name_ptr)?;
                let bi = ParsedBinderInfo::from_u8(
                    region.bytes_at(scalar_base + EXPR_DATA_SCALAR_BYTES, 1)?[0],
                );
                out.push((name, bi));
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

fn parsed_leading_lambda_binders(value: &ParsedExpr) -> Vec<(String, ParsedBinderInfo)> {
    let mut out = Vec::new();
    let mut e = value;
    loop {
        match e {
            ParsedExpr::Lam(name, _, body, bi) => {
                out.push((name.clone(), *bi));
                e = body;
            }
            ParsedExpr::MData(_, inner) => e = inner,
            _ => return out,
        }
    }
}

/// Direct (zero-copy) path: record every `<…>._default` definition of the
/// module, reading its value's binder names straight from `region`. Runs
/// before the definitional kinds are (lazily) served, so it is independent of
/// the import policy.
pub(crate) fn record_default_fn_binders_from_region<'a>(
    env: &mut Environment,
    region: &CompactedRegion<'_>,
    constants: impl IntoIterator<Item = (&'a str, &'a ConstantKind, u64)>,
) -> Result<(), ImportError> {
    for (name, kind, value_ptr) in constants {
        if !matches!(kind, ConstantKind::Definition) || value_ptr == 0 || !is_default_fn_name(name)
        {
            continue;
        }
        let binders = read_leading_lambda_binders(region, value_ptr, name)?;
        record(env, name, binders);
    }
    Ok(())
}

/// `ParsedModule` path: the same table, read off the parsed values.
pub(crate) fn record_default_fn_binders_from_parsed(
    env: &mut Environment,
    constants: &[ParsedConstant],
) {
    for c in constants {
        if !matches!(c.kind, ConstantKind::Definition) || !is_default_fn_name(&c.name) {
            continue;
        }
        let Some(value) = c.value.as_ref() else {
            continue;
        };
        record(env, &c.name, parsed_leading_lambda_binders(value));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_fn_name_is_the_last_component() {
        assert!(is_default_fn_name("Preorder.lt._default"));
        assert!(is_default_fn_name("LinearOrder.min._default"));
        assert!(!is_default_fn_name("Preorder.lt"));
        assert!(!is_default_fn_name("_default"));
        assert!(!is_default_fn_name("Preorder.lt._default.proof_1"));
    }

    #[test]
    fn test_parsed_lambda_spine_yields_names_in_order_and_stops_at_the_body() {
        let body = ParsedExpr::Const("x".to_string(), vec![]);
        let inner = ParsedExpr::Lam(
            "le".to_string(),
            Box::new(body.clone()),
            Box::new(body.clone()),
            ParsedBinderInfo::Default,
        );
        let outer = ParsedExpr::Lam(
            "α".to_string(),
            Box::new(body),
            Box::new(inner),
            ParsedBinderInfo::Implicit,
        );
        let got = parsed_leading_lambda_binders(&outer);
        assert_eq!(
            got,
            vec![
                ("α".to_string(), ParsedBinderInfo::Implicit),
                ("le".to_string(), ParsedBinderInfo::Default)
            ]
        );
    }
}
