// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `@[induction_eliminator]`: Lean's `customEliminatorExt`
//! (`Lean/Meta/Tactic/ElimInfo.lean`, `mkCustomEliminator`,
//! `getCustomEliminator?`) for the `induction` tactic.
//!
//! A registration is an [`AttrExtEntry`](clean_kernel::env::AttrExtEntry)
//! named [`INDUCTION_ELIMINATOR_ATTR`] in the persistent attribute
//! extension, so it travels with the environment (and a Clean module that
//! imports it) like every other attribute Clean records. Registrations that a
//! Lean-written `.olean` stores in `customEliminatorExt` (Init's
//! `Nat.rec_add_one`, `Nat.casesAuxOn`, `BitVec.cons_induction`, ...) are
//! NOT read: there `induction` / `cases` still fall back to the default
//! recursor, as before this module, and can accept a proof Lean rejects
//! (recorded open in `docs/DECISIONS.md`, PKG-U14 item 13). The lookup key is recomputed
//! from the eliminator's type on every lookup, exactly as Lean computes it at
//! registration: the head constant of each target's type, skipping the
//! targets a later target depends on (`isImplicitTarget`).
//!
//! # Where Clean is narrower than Lean (each a refusal)
//!
//! - Lean's map keeps the LATEST registration for a key. The attribute
//!   extension's per-attribute list is not an ordered log across imports
//!   (its export iterates a hash map), so when two distinct eliminators share
//!   a key [`find_induction_eliminator`] refuses by name instead of guessing
//!   which one is the latest.
//! - `local` / `scoped` registrations are refused where the attribute is
//!   written (`ElabCtx::ensure_known_attributes`); only the global kind is
//!   modeled.
//! - A `tactic.customEliminators` value other than `true` / `false` is
//!   refused by [`custom_eliminators_enabled`].

use clean_kernel::env::{self, AttrExtState, Environment};
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};
use clean_parser::Attribute;

use super::elim_info::{get_elim_info, telescope};

/// The attribute (and attribute-extension entry) name.
pub(crate) const INDUCTION_ELIMINATOR_ATTR: &str = "induction_eliminator";

/// Lean's `tactic.customEliminators` option (default `true`): when `false`,
/// `induction x` ignores every `@[induction_eliminator]` registration and
/// uses the type's recursor (`getElimNameInfo`).
pub(crate) const CUSTOM_ELIMINATORS_OPTION: &str = "tactic.customEliminators";

/// Lean's `mkCustomEliminator` key: the head constant of each target's
/// declared type, for the targets no LATER target's type depends on.
///
/// Fails, as Lean's attribute handler does, when the constant is not an
/// eliminator (`getElimInfo`) or when a keyed target's type is not headed by
/// a constant (`Unexpected eliminator target type`).
///
/// ENSURES: On Ok, the key has at most as many entries as the eliminator has
///   targets
pub(crate) fn induction_eliminator_key(elim_type: &Expr) -> Result<Vec<Name>, String> {
    let info = get_elim_info(elim_type).map_err(|e| e.to_string())?;
    let (binders, _) = telescope(elim_type);
    let mut key = Vec::with_capacity(info.targets_pos.len());
    for (i, &pos) in info.targets_pos.iter().enumerate() {
        let later = info.targets_pos.get(i + 1..).unwrap_or(&[]);
        // Inside binder `y`'s type, binder `pos < y` is `BVar(y - 1 - pos)`.
        // A binder that precedes `pos` cannot mention it.
        let implicit = later.iter().any(|&y| {
            y > pos
                && binders.get(y).is_some_and(|(_, y_ty)| {
                    u32::try_from(y - 1 - pos).is_ok_and(|idx| y_ty.has_loose_bvar(idx))
                })
        });
        if implicit {
            continue;
        }
        let Some((_, target_ty)) = binders.get(pos) else {
            return Err(format!("eliminator target binder {pos} is missing"));
        };
        match target_ty.get_app_fn().strip_mdata().kind() {
            ExprKind::Const(name, _) => key.push(name.clone()),
            _ => {
                return Err(format!(
                    "Unexpected eliminator target type {}",
                    crate::error_render::term(target_ty)
                ))
            }
        }
    }
    Ok(key)
}

/// Validate and record `@[induction_eliminator]` on `decl` (Lean's
/// `addCustomEliminator … (induction := true)`, global kind).
pub(crate) fn register_induction_eliminator(
    env: &mut Environment,
    decl: &Name,
) -> Result<(), String> {
    let info = env
        .get_const(decl)
        .ok_or_else(|| format!("unknown constant '{decl}'"))?;
    induction_eliminator_key(&info.type_)?;
    env.add_ext_entry::<AttrExtState>(
        env::attr_ext_idx(),
        &env::AttrExtEntry {
            decl_name: decl.clone(),
            attr_name: Name::from_string(INDUCTION_ELIMINATOR_ATTR),
            priority: 0,
        },
    );
    Ok(())
}

/// Whether `induction` consults the registry (`tactic.customEliminators`).
///
/// An unset option is Lean's default, `true`. A value that is neither `true`
/// nor `false` is refused rather than read as either.
pub(crate) fn custom_eliminators_enabled(env: &Environment) -> Result<bool, String> {
    match env.get_option(CUSTOM_ELIMINATORS_OPTION) {
        None => Ok(true),
        Some(Some(value)) if value == "true" => Ok(true),
        Some(Some(value)) if value == "false" => Ok(false),
        Some(other) => Err(format!(
            "option `{CUSTOM_ELIMINATORS_OPTION}` has value {other:?}; only `true` and `false` \
             are modeled"
        )),
    }
}

/// Lean's `getCustomEliminator? #[major] (induction := true)`: the eliminator
/// registered for a single target whose type is headed by `major_head`.
///
/// Returns `Ok(None)` when none is registered. Two DISTINCT registered
/// eliminators with that key are refused by name: Lean keeps the latest, and
/// Clean does not keep a registration order it can trust across imports.
/// A registered constant whose key can no longer be computed is refused too,
/// rather than skipped.
pub(crate) fn find_induction_eliminator(
    env: &mut Environment,
    major_head: &Name,
) -> Result<Option<Name>, String> {
    let attr = Name::from_string(INDUCTION_ELIMINATOR_ATTR);
    let registered: Vec<Name> = match env.get_ext_state_or_init::<AttrExtState>(env::attr_ext_idx())
    {
        Some(state) => state.get_decls_with_attr(&attr).to_vec(),
        None => return Ok(None),
    };
    let mut found: Vec<Name> = Vec::new();
    for decl in registered {
        if found.contains(&decl) {
            continue;
        }
        let info = env.get_const(&decl).ok_or_else(|| {
            format!("`@[{INDUCTION_ELIMINATOR_ATTR}]` names `{decl}`, which is not in scope")
        })?;
        let key = induction_eliminator_key(&info.type_)
            .map_err(|e| format!("`@[{INDUCTION_ELIMINATOR_ATTR}]` `{decl}`: {e}"))?;
        if key.len() == 1 && key[0] == *major_head {
            found.push(decl);
        }
    }
    match found.len() {
        0 => Ok(None),
        1 => Ok(found.pop()),
        _ => Err(format!(
            "several `@[{INDUCTION_ELIMINATOR_ATTR}]` eliminators apply to `{major_head}` ({}); \
             Lean uses the latest registration, and Clean does not track registration order \
             across imports",
            found
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", ")
        )),
    }
}

/// Custom-eliminator attributes whose `local` / `scoped` forms the parser
/// lifts (`Attribute::Local` / `Attribute::Scoped`) so they can be refused by
/// name instead of being read as the unmodeled modifier and dropped.
///
/// Returns the attribute as written (`local induction_eliminator`) when `attr`
/// is such a `local` / `scoped` custom-eliminator attribute.
#[must_use]
pub(crate) fn scoped_eliminator_attr(attr: &Attribute) -> Option<String> {
    let (kind, inner) = match attr {
        Attribute::Local(inner) => ("local", inner),
        Attribute::Scoped(inner) => ("scoped", inner),
        _ => return None,
    };
    match inner.as_ref() {
        Attribute::Unknown(name)
            if matches!(name.as_str(), "induction_eliminator" | "cases_eliminator") =>
        {
            Some(format!("{kind} {name}"))
        }
        _ => None,
    }
}
