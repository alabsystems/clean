// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Name resolution helpers for the elaborator.

use crate::namespace::NamespaceState;
use clean_kernel::expr::ExprKind;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr};
use std::collections::BTreeSet;

/// Resolve an identifier against the environment and active namespace state.
///
/// Resolution order mirrors Lean's `resolveGlobalName`
/// (`Lean/ResolveName.lean`, gap sweep B03):
/// 1. `_root_.`-prefixed names force root resolution (marker stripped).
/// 2. Qualify with the current namespace, walking OUTWARD (`A.B.name`,
///    then `A.name`) — `resolveUsingNamespace`.
/// 3. Qualify with each open namespace, in order.
/// 4. Treat `name` as already fully qualified (root-level exact match).
///
/// Returns the first matching constant name found in the environment.
#[must_use]
pub(crate) fn resolve_identifier(
    name: &Name,
    ns_state: &NamespaceState,
    env: &Environment,
) -> Option<Name> {
    if name.is_anon() {
        return None;
    }

    let name_str = name.to_string();
    if let Some(root_name) = name_str.strip_prefix("_root_.") {
        let root = Name::from_string(root_name);
        return env.get_const(&root).is_some().then_some(root);
    }

    // Current-namespace-outward walk (innermost first).
    let current_ns = ns_state.current_namespace();
    if !current_ns.is_anon() {
        let ns_str = current_ns.to_string();
        let mut prefix = ns_str.as_str();
        loop {
            let candidate = Name::from_string(&format!("{prefix}.{name_str}"));
            if env.get_const(&candidate).is_some() {
                return Some(candidate);
            }
            match prefix.rsplit_once('.') {
                Some((parent, _)) => prefix = parent,
                None => break,
            }
        }
    }

    for open_ns in ns_state.open_namespaces() {
        if let Some(candidate) = qualify_name(open_ns, name) {
            if env.get_const(&candidate).is_some() {
                return Some(candidate);
            }
        }
    }

    if env.get_const(name).is_some() {
        return Some(name.clone());
    }

    None
}

/// Collect completion candidates visible from the current namespace context.
///
/// Matches are searched under the current namespace and each open namespace.
/// Results are deduplicated and returned in a stable order.
#[must_use]
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn get_completions(
    prefix: &str,
    ns_state: &NamespaceState,
    env: &Environment,
) -> Vec<Name> {
    let mut matches = BTreeSet::new();

    collect_completions(ns_state.current_namespace(), prefix, env, &mut matches);

    for open_ns in ns_state.open_namespaces() {
        collect_completions(open_ns, prefix, env, &mut matches);
    }

    matches.into_iter().collect()
}

fn qualify_name(namespace: &Name, name: &Name) -> Option<Name> {
    if namespace.is_anon() || name.is_anon() {
        return None;
    }

    let qualified = format!("{namespace}.{name}");
    Some(Name::from_string(&qualified))
}

// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
fn collect_completions(
    namespace: &Name,
    prefix: &str,
    env: &Environment,
    matches: &mut BTreeSet<Name>,
) {
    let search_prefix = completion_search_prefix(namespace, prefix);

    for constant in env.constants() {
        if constant.name.is_anon() {
            continue;
        }

        if constant.name.to_string().starts_with(&search_prefix) {
            matches.insert(constant.name.clone());
        }
    }
}

// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
fn completion_search_prefix(namespace: &Name, prefix: &str) -> String {
    if namespace.is_anon() {
        prefix.to_string()
    } else if prefix.is_empty() {
        format!("{namespace}.")
    } else {
        format!("{namespace}.{prefix}")
    }
}

/// Is `qualified` one of the DERIVED projections Clean materializes for a
/// structure's INHERITED fields — a constant Lean 4 does not declare?
///
/// For `structure C extends P`, `elab_structure::build_inherited_projections`
/// registers `C.f := fun {params} (self : C params) => P.f … (C.toP … self)`
/// for every field `f` projectable on `P`. Lean 4 builds that composition
/// ON THE FLY at each use site (`mkBaseProjections`, `src/Lean/Elab/App.lean`)
/// and adds NO constant: measured against the real `Init` oleans (93,172
/// constants), `Monad.toApplicative` exists while `Monad.pure` and
/// `Applicative.pure` do not.
///
/// The difference is not cosmetic. A constant named `C.f` joins the
/// current-namespace-outward candidate set, so inside `namespace C` a bare `f`
/// resolves to it instead of the root/exported `f` the author wrote — and
/// because the derived projection takes an EXPLICIT `self` the user never
/// supplied, the term is left under-applied with a `Pi` type where the field
/// type was expected. That is the SRCELAB "rigid head clash" cluster: in
/// `Mathlib/Logic/Unique.lean`, `Unique extends Inhabited α` grows
/// `Unique.default : {α} → (self : Unique α) → α`, so `theorem eq_default
/// (a : α) : a = default` inside `namespace Unique` reports
/// `Type mismatch: expected FVar(FVarId(0)), got cannot unify expressions of
/// different shape: Discriminant(6) vs Discriminant(1)` — `Pi` vs `FVar`.
///
/// Recognized structurally rather than by a registry flag so the same verdict
/// holds for any environment that carries the shape, and conservatively: every
/// clause must hold, so a genuine declaration that happens to live in a
/// structure's namespace (`Unique.eq_default`) is never mistaken for one.
///
/// 1. the owner is a structure with recorded `extends` parents;
/// 2. the field is NOT one of the owner's own constructor fields (a direct
///    projection IS a real Lean declaration and must keep resolving);
/// 3. the constant's body is `<anything> (C.toParent … self)`, i.e. its
///    argument's spine head is one of the owner's own `toParent` projections.
#[must_use]
pub(crate) fn is_generated_inherited_projection(env: &Environment, qualified: &Name) -> bool {
    let qualified_str = qualified.to_string();
    let Some((owner_str, field_str)) = qualified_str.rsplit_once('.') else {
        return false;
    };
    let owner = Name::from_string(owner_str);
    let Some(parents) = env.get_structure_parents(&owner) else {
        return false;
    };
    let field = Name::from_string(field_str);
    if env
        .get_structure_field_names(&owner)
        .is_some_and(|fields| fields.contains(&field))
    {
        return false;
    }
    let Some(body) = env
        .get_const(qualified)
        .and_then(|info| info.value.as_ref())
    else {
        return false;
    };
    let mut e = body;
    while let ExprKind::Lam(_, _, inner) | ExprKind::MData(_, inner) = e.kind() {
        e = inner;
    }
    let ExprKind::App(_, subobject_arg) = e.kind() else {
        return false;
    };
    let ExprKind::Const(inner_head, _) = subobject_arg.get_app_fn().kind() else {
        return false;
    };
    parents
        .iter()
        .any(|(to_field, _)| Name::append(&owner, &to_field.to_string()) == *inner_head)
}

/// Depth bound for the subobject walk. A structure's `extends` chain is a DAG
/// whose depth is tiny in practice (Lean's deepest core chain is under 10); the
/// bound only stops a cycle introduced by corrupt metadata from looping.
const SUBOBJECT_WALK_MAX_DEPTH: usize = 32;

/// Compose the kernel projection chain that reads `field` off a value of
/// structure `owner`, descending through `extends` parent SUBOBJECTS — Lean's
/// `mkBaseProjections` (`src/Lean/Elab/App.lean`), built ON THE FLY exactly as
/// Lean builds it, with NO constant of its own.
///
/// `receiver` must already be a value whose type's head is `owner` fully
/// applied (the same precondition the own-field arm of `elab_proj` has, since
/// it is reached from `resolve_projection_target`).
///
/// Returns `Proj(P, i, … Proj(owner, j, receiver) …)`: an own field of `owner`
/// is one `Proj`; an inherited field is the parent's chain wrapped around the
/// `Proj` that reads the `toParent` subobject slot. Multiple parents are tried
/// in constructor order, so a genuine DIAMOND resolves to the first parent that
/// carries the field — the same first-parent-wins rule
/// `elab_structure::build_inherited_projections` applies when it materializes
/// the same composition as a constant.
///
/// SOUNDNESS: this only NAMES a projection target. Every `Proj` it emits is
/// re-checked by the kernel (`infer_type` rejects an index that is not a field
/// of the projected structure, and rejects a receiver of the wrong type), so a
/// wrong walk fails closed rather than admitting a term.
///
/// Returns `None` when the field is not reachable — including for a structure
/// with no recorded `extends` metadata, which is every `.olean`-IMPORTED
/// structure today (`register_structure_parents` has exactly one caller,
/// `crate::register`, on the source-elaboration path). Imported structures are
/// therefore untouched by this walk, which is why it cannot change any verdict
/// on the import lane.
#[must_use]
pub(crate) fn compose_subobject_projection(
    env: &Environment,
    owner: &Name,
    field: &Name,
    receiver: Expr,
    depth: usize,
) -> Option<Expr> {
    if depth >= SUBOBJECT_WALK_MAX_DEPTH {
        return None;
    }
    if let Some(idx) = env.get_structure_field_index(owner, field) {
        return Some(Expr::proj(owner.clone(), idx, receiver));
    }
    // `to_vec` releases the borrow on `env` before the recursive call.
    let parents = env.get_structure_parents(owner)?.to_vec();
    for (to_field, parent_name) in parents {
        let Some(to_idx) = env.get_structure_field_index(owner, &to_field) else {
            continue;
        };
        let parent_receiver = Expr::proj(owner.clone(), to_idx, receiver.clone());
        if let Some(chain) =
            compose_subobject_projection(env, &parent_name, field, parent_receiver, depth + 1)
        {
            return Some(chain);
        }
    }
    None
}

/// The `toParent` subobject field of `owner` through which `field` is reached,
/// or `None` when `field` is an own field / unreachable.
///
/// Same walk as [`compose_subobject_projection`], but returning only the FIRST
/// hop — what a structure-UPDATE rewrite needs (`{ c with inheritedField := v }`
/// ⇝ `{ c with toParent := { c.toParent with inheritedField := v } }`).
#[must_use]
pub(crate) fn inherited_field_subobject_hop(
    env: &Environment,
    owner: &Name,
    field: &Name,
) -> Option<Name> {
    if env.get_structure_field_index(owner, field).is_some() {
        return None;
    }
    let parents = env.get_structure_parents(owner)?.to_vec();
    for (to_field, parent_name) in parents {
        if structure_reaches_field(env, &parent_name, field, 0) {
            return Some(to_field);
        }
    }
    None
}

/// Whether `field` is projectable on `owner`, directly or through a subobject.
#[must_use]
fn structure_reaches_field(env: &Environment, owner: &Name, field: &Name, depth: usize) -> bool {
    if depth >= SUBOBJECT_WALK_MAX_DEPTH {
        return false;
    }
    if env.get_structure_field_index(owner, field).is_some() {
        return true;
    }
    let Some(parents) = env.get_structure_parents(owner).map(<[_]>::to_vec) else {
        return false;
    };
    parents
        .iter()
        .any(|(_, parent)| structure_reaches_field(env, parent, field, depth + 1))
}

/// MEASUREMENT INSTRUMENT — `CLEAN_LEAN4_STRUCT_PARITY=1`.
///
/// OFF by default, and every gate in this repo runs with it off, so the shipped
/// behaviour is unchanged: `structure C extends P` still MATERIALIZES a constant
/// `C.f` for each inherited field `f`.
///
/// Turning it on suppresses that registration, putting Clean's environment on
/// the Lean 4 constant set for structures (measured: real Lean 4 `import Lean`
/// has 1,235 inherited (structure, field) pairs and `import Mathlib` has 9,185,
/// and Lean declares a constant for NONE of them; Clean's own `.olean` IMPORT
/// path likewise declares none). It exists so
/// the size of the remaining work can be MEASURED — run the suite with it on and
/// the failures are exactly the sites that still read an inherited projection as
/// a named constant rather than composing it. See
/// `designs/2026-08-24-inherited-projection-parity.md`.
///
/// It is NOT a supported elaboration mode: with it on, bare-name resolution of
/// an inherited field stops finding a candidate (which is what Lean does — it
/// reports `unknown identifier` — but Clean has not yet re-pointed every
/// consumer at [`compose_subobject_projection`]).
#[must_use]
pub(crate) fn lean4_struct_parity_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("CLEAN_LEAN4_STRUCT_PARITY").is_ok_and(|v| v == "1"))
}

/// CENSUS INSTRUMENT — `CLEAN_STRUCT_PARITY_CENSUS=1`.
///
/// Emits one machine-parsable stderr line per derived inherited projection the
/// `structure` elaborator would register:
///
/// ```text
/// [structparity] generated <Owner>.<field>
/// ```
///
/// `grep -c '^\[structparity\] generated '` over a `clean check` run is then the
/// exact size of the environment gap that run opens against Lean 4, which
/// declares no such constant. Zero cost when the variable is unset beyond one
/// cached boolean check.
pub(crate) fn note_generated_inherited_projection(name: &Name) {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    if *ON.get_or_init(|| std::env::var("CLEAN_STRUCT_PARITY_CENSUS").is_ok_and(|v| v == "1")) {
        eprintln!("[structparity] generated {name}");
    }
}
