// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Processing of `open` and `export` commands.
//!
//! Extracted from `namespace.rs` to keep files under the 500-line limit.
//! These functions populate [`NamespaceState`] aliases by scanning the
//! environment for constants matching the opened/exported namespace prefix.
//!
//! Semantics follow Lean 4 (`src/Lean/Elab/BuiltinCommand.lean` `elabOpen` /
//! `elabExport`, `src/Lean/ResolveName.lean` `OpenDecl`):
//!
//! - `open Foo` — a SIMPLE open: every non-protected direct child of `Foo`
//!   becomes visible by its short name (`OpenDecl.simple`). Protected names
//!   stay qualified-only.
//! - `open Foo (x y)` — EXPLICIT opens for exactly the listed names
//!   (`OpenDecl.explicit`); unknown names are loud errors. Explicit opens may
//!   name protected declarations (protection only gates the simple form).
//! - `open Foo hiding x` — simple open minus the hidden names; each hidden
//!   name must exist (Lean resolves each hidden ident and errors otherwise).
//! - `open Foo renaming x → y` — EXPLICIT opens for ONLY the renamed pairs
//!   (`y ↦ Foo.x`). It does NOT import the rest of the namespace (this was
//!   previously implemented as a full open with renames applied — a silent
//!   divergence from Lean; gap sweep B13).
//! - `export Foo (x)` — registers the alias `currentNs.x ↦ Foo.x` (bare `x`
//!   at root). Export aliases are permanent for the rest of the file (Lean
//!   stores them in the environment alias table), so they are inserted
//!   scope-immune and survive `end`-of-namespace scope pops.
//!
//! The opened namespace itself is resolved as Lean's `resolveNamespace` does
//! ([`resolve_namespaces`]): the first of `current ++ B`, …, `B` that is a
//! namespace (inside `namespace A`, `open B` means `A.B` when it exists), and
//! `D ++ B` for every simple `open D` in force. A simple `open` opens and
//! activates every one of them.

use crate::namespace::{
    append_names, name_has_prefix, parent_name, Alias, NamespaceError, NamespaceState,
};
use clean_kernel::name::Name;
use clean_kernel::Environment;
use clean_parser::{OpenPath, SurfaceName};

/// Process a list of `open` paths, adding aliases to the namespace state.
///
/// For each [`OpenPath`], finds all constants in `env` whose name starts
/// with the namespace prefix and adds short-name aliases for them,
/// respecting selective imports, hiding, and renaming.
///
/// # Errors
///
/// Returns [`NamespaceError::NameNotFound`] when a selective / renamed /
/// hidden name does not exist in the opened namespace (Lean is loud here:
/// each such ident is resolved and unknown names are errors).
pub fn process_open(
    env: &Environment,
    paths: &[OpenPath],
    state: &mut NamespaceState,
) -> Result<(), NamespaceError> {
    for path in paths {
        process_single_open(env, path, state)?;
    }
    Ok(())
}

/// Process `open scoped Foo Bar`: activate each namespace's `scoped` entries
/// (Lean `elabOpenScoped` → `activateScoped`) WITHOUT bringing any name into
/// scope. Returns the namespaces this call newly activated.
pub(crate) fn process_open_scoped(
    env: &Environment,
    paths: &[OpenPath],
    state: &mut NamespaceState,
) -> Vec<Name> {
    let mut activated = Vec::new();
    for path in paths {
        // Lean `elabOpenDecl` (`open scoped`): `activateScoped` on EVERY
        // namespace `resolveNamespace` gives.
        for ns_name in resolve_namespaces(env, state, &path.path) {
            if state.activate_scoped(ns_name.clone()) {
                activated.push(ns_name);
            }
        }
    }
    activated
}

/// The namespaces an `open` command activates (Lean's `elabOpenDecl`:
/// `activateScoped` for every namespace a simple `open`, an `open scoped` or
/// an `open … hiding` resolves to; an explicit or renaming `open` activates
/// none), recorded in `state` as `process_open` / `process_open_scoped` would
/// record them, but WITHOUT bringing any name into scope — for a caller that
/// needs only the instance state an `open … in` command runs under. Returns
/// the namespaces newly activated.
pub(crate) fn open_activations(
    env: &Environment,
    paths: &[OpenPath],
    scoped: bool,
    state: &mut NamespaceState,
) -> Vec<Name> {
    let before = state.activated_scopes().to_vec();
    for path in paths {
        let namespaces = if scoped
            || (path.names.is_empty() && path.renaming.is_empty() && path.hiding.is_empty())
        {
            resolve_namespaces(env, state, &path.path)
        } else if path.names.is_empty() && path.renaming.is_empty() {
            resolve_unique_namespace(env, state, &path.path)
                .map(|ns| vec![ns])
                .unwrap_or_default()
        } else {
            Vec::new()
        };
        for ns in namespaces {
            state.activate_scoped(ns.clone());
            if !scoped {
                state.open_namespace_scoped_hiding(
                    ns,
                    path.hiding
                        .iter()
                        .cloned()
                        .map(SurfaceName::into_name)
                        .collect(),
                );
            }
        }
    }
    state.newly_activated(&before)
}

/// True when `name` denotes any global declaration: a plain constant, an
/// inductive type, a constructor, or a recursor. Mirrors the candidate set
/// `elab_ident` accepts (inductives / ctors / recursors may lack a plain
/// `ConstantInfo` entry).
fn global_exists(env: &Environment, name: &Name) -> bool {
    env.get_const(name).is_some()
        || env.get_inductive(name).is_some()
        || env.get_constructor(name).is_some()
        || env.get_recursor(name).is_some()
}

/// The declaration `qualified` (`ns ++ x`) names for an explicit `open` /
/// `export` member, with Lean's private step (`resolveQualifiedName`,
/// `Lean/ResolveName.lean`): `qualified` itself, else THIS module's private
/// `_private.<main module>.0.qualified`. A sibling module's private name is
/// never reached, since only the current module's prefix is built (G21).
fn member_declaration(env: &Environment, state: &NamespaceState, qualified: Name) -> Option<Name> {
    if global_exists(env, &qualified) {
        return Some(qualified);
    }
    state
        .private_name(&qualified)
        .filter(|private| global_exists(env, private))
}

/// Whether `ns` is a namespace (Lean's `Environment.isNamespace`): one a
/// `namespace` command registered, a proper prefix of a declaration's name
/// (Lean's `registerNamePrefixes`), or one holding `scoped` instance entries
/// (a scoped entry is only ever added inside a `namespace` block, which
/// registers it — also for an `.olean`-imported one).
pub(crate) fn is_namespace(env: &Environment, ns: &Name) -> bool {
    if ns.is_anon() {
        return false;
    }
    if env.is_registered_namespace(ns) {
        return true;
    }
    if env
        .get_ext_state::<clean_olean::ScopedInstanceState>(clean_olean::scoped_instance_idx())
        .is_some_and(|state| {
            state.scope_of.values().any(|scope| scope == ns)
                || state.entries.iter().any(|(scope, _, _)| scope == ns)
        })
    {
        return true;
    }
    env.constants()
        .any(|ci| ci.name != *ns && name_has_prefix(&ci.name, ns))
}

/// Lean 4.8.0's `ResolveName.resolveNamespace` (`Lean/ResolveName.lean`):
/// every namespace the identifier of an `open`/`export` command may denote —
///
/// 1. the first of `current ++ id`, `parent(current) ++ id`, …, `id` that is
///    a namespace (`resolveNamespaceUsingScope?`: inside `namespace A`,
///    `open B` means `A.B` when that exists), then
/// 2. `D ++ id` for every simple `open D` in force that does not hide `id`
///    and makes it a namespace (`resolveNamespaceUsingOpenDecls`, the most
///    recent `open` first).
///
/// `_root_.X` names `X` only. Empty when nothing matches: Lean then reports
/// "unknown namespace".
fn resolve_namespaces(env: &Environment, state: &NamespaceState, ns: &SurfaceName) -> Vec<Name> {
    let root = ns.qualify_under(&SurfaceName::default());
    if root.name() != ns.name() {
        let name = root.into_name();
        return if is_namespace(env, &name) {
            vec![name]
        } else {
            Vec::new()
        };
    }
    let id = ns.name();
    let mut out: Vec<Name> = Vec::new();
    let mut prefix = state.current_namespace().clone();
    loop {
        let candidate = append_names(&prefix, id);
        if is_namespace(env, &candidate) {
            out.push(candidate);
            break;
        }
        if prefix.is_anon() {
            break;
        }
        prefix = parent_name(&prefix);
    }
    // Not deduplicated, as in Lean: inside `namespace A` after `open A`,
    // `N` denotes `A.N` twice, and `export N (x)` then reports "ambiguous
    // identifier 'x', possible interpretations: [N.x, N.x]" (measured on
    // Lean 4.8.0) — the export makes no alias.
    for (open_ns, hidden) in state.open_namespaces_with_hidden().into_iter().rev() {
        if hidden.iter().any(|h| h == id) {
            continue;
        }
        let candidate = append_names(open_ns, id);
        if is_namespace(env, &candidate) {
            out.push(candidate);
        }
    }
    out
}

/// Lean's `resolveUniqueNamespace`: the one namespace the identifier
/// denotes. With none, the identifier itself (its members are then reported
/// missing by the caller; an empty simple `open` stays tolerated); with more
/// than one, "ambiguous namespace".
fn resolve_unique_namespace(
    env: &Environment,
    state: &NamespaceState,
    ns: &SurfaceName,
) -> Result<Name, NamespaceError> {
    let found = resolve_namespaces(env, state, ns);
    match <[_; 1]>::try_from(found) {
        Ok([only]) => Ok(only),
        Err(found) if found.is_empty() => Ok(ns.qualify_under(&SurfaceName::default()).into_name()),
        Err(found) => Err(NamespaceError::UnknownNamespace(format!(
            "ambiguous namespace '{}', possible interpretations: {}",
            ns,
            found
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", ")
        ))),
    }
}

/// Lean's `resolveNameUsingNamespacesCore` for `open N (x)` / `export N (x)`:
/// the one declaration `ns ++ x` among the namespaces `N` denotes.
fn resolve_member(
    env: &Environment,
    state: &NamespaceState,
    namespaces: &[Name],
    fallback_ns: &SurfaceName,
    short: &SurfaceName,
) -> Result<Name, NamespaceError> {
    // Lean resolves `ns ++ x` as a constant name (`resolveGlobalConstNoOverload`),
    // so an ALIAS `ns.x` (an `export` made inside `ns`) names its target
    // (measured on Lean 4.8.0: `namespace K; export N.M (y); end K` then
    // `export K (y)` aliases `y` to `N.M.y`; Clean refused the export as an
    // unknown member and kept a root `y` unambiguous).
    let mut found: Vec<Name> = Vec::new();
    for ns in namespaces {
        let qualified = append_names(ns, short.name());
        if let Some(declaration) = member_declaration(env, state, qualified.clone()) {
            found.push(declaration);
            continue;
        }
        let mut aliased: Vec<Name> = Vec::new();
        for target in state
            .resolve_all(&qualified)
            .into_iter()
            .chain(env.export_alias_targets(&qualified))
        {
            if global_exists(env, target) && !aliased.contains(target) {
                aliased.push(target.clone());
            }
        }
        found.extend(aliased);
    }
    match <[_; 1]>::try_from(found) {
        Ok([only]) => Ok(only),
        Err(found) if found.is_empty() => Err(NamespaceError::NameNotFound {
            namespace: namespaces
                .first()
                .map_or_else(|| fallback_ns.to_string(), ToString::to_string),
            name: short.to_string(),
        }),
        Err(found) => Err(NamespaceError::UnknownNamespace(format!(
            "ambiguous identifier '{}', possible interpretations: {}",
            short,
            found
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", ")
        ))),
    }
}

/// Process a single open path.
fn process_single_open(
    env: &Environment,
    path: &OpenPath,
    state: &mut NamespaceState,
) -> Result<(), NamespaceError> {
    // Explicit mode — `open Foo (x y)`: only the listed names, loud on
    // unknowns (Lean `elabOpenOnly` resolves each ident among every
    // namespace `Foo` denotes and errors when none or several match).
    // Explicit opens are `OpenDecl.explicit` entries, which are NOT filtered
    // by `protected` (only the simple form is).
    if !path.names.is_empty() {
        let namespaces = resolve_namespaces(env, state, &path.path);
        for short in &path.names {
            let qualified = resolve_member(env, state, &namespaces, &path.path, short)?;
            let alias = apply_renaming(short, &path.renaming).into_name();
            state.record_explicit_open(alias.clone(), qualified.clone());
            state.insert_alias_pub(alias, qualified);
        }
        return Ok(());
    }

    // Renaming mode — `open Foo renaming x → y`: ONLY the renamed pairs are
    // brought into scope, as explicit aliases `y ↦ Foo.x` (Lean
    // `elabOpenRenaming` adds one `OpenDecl.explicit` per pair and nothing
    // else, in the unique namespace `Foo` denotes). Unknown source names are
    // loud errors.
    if !path.renaming.is_empty() {
        let ns_name = resolve_unique_namespace(env, state, &path.path)?;
        for rename in &path.renaming {
            let qualified = append_names(&ns_name, rename.from.name());
            let Some(qualified) = member_declaration(env, state, qualified) else {
                return Err(NamespaceError::NameNotFound {
                    namespace: ns_name.to_string(),
                    name: rename.from.to_string(),
                });
            };
            state.record_explicit_open(rename.to.name().clone(), qualified.clone());
            state.insert_alias_pub(rename.to.name().clone(), qualified);
        }
        return Ok(());
    }

    // `open Foo hiding x`: the unique namespace `Foo` denotes (Lean
    // `resolveUniqueNamespace`); each hidden name must exist in it (Lean
    // `elabOpenHiding` resolves every hidden ident; unknowns are errors).
    // A simple `open Foo`: EVERY namespace `Foo` denotes (Lean opens and
    // activates each).
    let namespaces = if path.hiding.is_empty() {
        resolve_namespaces(env, state, &path.path)
    } else {
        let ns_name = resolve_unique_namespace(env, state, &path.path)?;
        for hidden in &path.hiding {
            let qualified = append_names(&ns_name, hidden.name());
            if member_declaration(env, state, qualified).is_none() {
                return Err(NamespaceError::NameNotFound {
                    namespace: ns_name.to_string(),
                    name: hidden.to_string(),
                });
            }
        }
        vec![ns_name]
    };

    // Lean 4 errors on `open` of an unknown namespace, but clean's import
    // lanes legitimately open namespaces whose members arrive later
    // (partial .olean loads, staged preludes), so an open that resolves to
    // NO namespace stays a tolerated no-op here — it opens and activates
    // nothing, as Lean's failed command does not.
    for ns_name in namespaces {
        open_simple(env, &ns_name, &path.hiding, state);
    }
    Ok(())
}

/// One simple `open ns` (optionally minus the hidden names), `ns` a
/// namespace `resolveNamespace` gave: Lean's `OpenDecl.simple ns hiding` and
/// `activateScoped ns`.
fn open_simple(
    env: &Environment,
    ns_name: &Name,
    hiding: &[SurfaceName],
    state: &mut NamespaceState,
) {
    // Simple open (optionally minus the hidden names) activates the
    // namespace's `scoped` entries (Lean 4.8.0, measured: `open Foo` and
    // `open Foo hiding x` activate a `scoped instance`; `open Foo (x)` and
    // `open Foo renaming …` do not), whether or not it has any other member.
    state.activate_scoped(ns_name.clone());

    // Import all non-protected direct children under the prefix.
    for ci in env.constants() {
        if parent_name(&ci.name) == *ns_name {
            let suffix = SurfaceName::from_name(ci.name.clone()).last_component();
            if hiding.contains(&suffix) || env.is_protected(&ci.name) {
                continue;
            }
            state.insert_alias_pub(suffix.into_name(), ci.name.clone());
        }
    }

    // Track the opened namespace itself (scope-rollback aware): the live
    // resolution walk reads `<ns>.<name>` through it, `resolveNamespace`
    // reads it as an open declaration, and diagnostics point at protected
    // members hidden by the simple open ("`x` is protected; use `Foo.x`").
    // The `hiding` suffixes ride along: the live walk would otherwise reach
    // a name this open explicitly removed. The alias loop above already
    // applies the same filter to the frozen table.
    state.open_namespace_scoped_hiding(
        ns_name.clone(),
        hiding.iter().cloned().map(SurfaceName::into_name).collect(),
    );
}

/// Apply renaming rules to a short name.
fn apply_renaming(short: &SurfaceName, renamings: &[clean_parser::OpenRename]) -> SurfaceName {
    for r in renamings {
        if &r.from == short {
            return r.to.clone();
        }
    }
    short.clone()
}

/// Process an `export` command, making names from `source` namespace visible
/// under the current namespace.
///
/// `export Nat (add mul)` in namespace `MyLib` creates aliases:
/// - `MyLib.add` -> `Nat.add`
/// - `MyLib.mul` -> `Nat.mul`
///
/// When `current_ns` is `None` (root), the aliases are the bare names.
///
/// The aliases are inserted scope-IMMUNE (`insert_alias_unscoped`): Lean
/// records exports in the environment's permanent alias table, so an export
/// made inside a `namespace`/`section` block survives the block's alias-scope
/// pop for the rest of the file. Resolution picks them up (a) bare within the
/// declaring namespace via the outward walk and (b) fully qualified
/// (`MyLib.add`) from anywhere.
///
/// # Errors
///
/// Returns [`NamespaceError::NameNotFound`] when an exported name does not
/// exist in the source namespace (Lean `elabExport` resolves each ident and
/// errors on unknowns; the old silent skip hid typos).
pub fn process_export(
    env: &Environment,
    source_ns: &SurfaceName,
    names: &[SurfaceName],
    current_ns: Option<&SurfaceName>,
    state: &mut NamespaceState,
) -> Result<(), NamespaceError> {
    // Lean `elabExport`: each name is resolved among EVERY namespace
    // `source_ns` denotes (`resolveNameUsingNamespaces`).
    let namespaces = resolve_namespaces(env, state, source_ns);

    for short in names {
        let qualified = resolve_member(env, state, &namespaces, source_ns, short)?;

        // The alias lives in the CURRENT namespace: bare at root, qualified
        // (`MyLib.add`) inside `namespace MyLib`.
        let export_short = match current_ns {
            Some(ns) if !ns.is_anonymous() => ns.append(short),
            _ => short.clone(),
        };
        // An ATOMIC alias never reaches a protected declaration (Lean's
        // `getAliases (skipProtected := id.isAtomic)`): a root `export N
        // (x)` of a protected `N.x` leaves `x` unresolvable (measured on
        // Lean 4.8.0). This file's table cannot tell that alias from an
        // explicit `open N (x)`, which does reach it, so it is not entered
        // there; the environment's alias table (registered from
        // `push_export` below) holds it with that filter applied on use.
        let atomic_alias = export_short.parent().is_anonymous();
        if !(atomic_alias && env.is_protected(&qualified)) {
            state.insert_alias_unscoped(export_short.name().clone(), qualified.clone());
        }

        // Record the export for downstream consumers.
        state.push_export(Alias {
            short: export_short.into_name(),
            target: qualified,
        });
    }
    Ok(())
}
