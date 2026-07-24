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
//! The opened namespace itself is resolved OUTWARD from the current namespace
//! (Lean `resolveNamespace`): inside `namespace A`, `open B` prefers `A.B`
//! over root `B`.

use crate::namespace::{Alias, NamespaceError, NamespaceState};
use clean_kernel::name::Name;
use clean_kernel::Environment;
use clean_parser::OpenPath;

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

/// Resolve the namespace named by an `open`/`export` command relative to the
/// current namespace, walking OUTWARD (Lean `resolveNamespace`): inside
/// `namespace A.B`, `open C` tries `A.B.C`, then `A.C`, then root `C`. The
/// first candidate that denotes an existing namespace (some declaration lives
/// strictly under it) or an existing declaration wins; when nothing matches,
/// the name is returned unchanged (the caller decides whether that is an error
/// or a tolerated forward reference).
fn resolve_namespace_outward(env: &Environment, current: &Name, ns: &str) -> String {
    let mut prefixes: Vec<String> = Vec::new();
    if !current.is_anon() {
        let current_str = current.to_string();
        let mut prefix = current_str.as_str();
        loop {
            prefixes.push(format!("{prefix}.{ns}"));
            match prefix.rsplit_once('.') {
                Some((parent, _)) => prefix = parent,
                None => break,
            }
        }
    }
    prefixes.push(ns.to_string());

    for candidate in &prefixes {
        let cand_dot = format!("{candidate}.");
        let is_namespace = env
            .constants()
            .any(|ci| ci.name.to_string().starts_with(&cand_dot));
        if is_namespace || global_exists(env, &Name::from_string(candidate)) {
            return candidate.clone();
        }
    }
    ns.to_string()
}

/// Process a single open path.
fn process_single_open(
    env: &Environment,
    path: &OpenPath,
    state: &mut NamespaceState,
) -> Result<(), NamespaceError> {
    let ns_str = resolve_namespace_outward(env, state.current_namespace(), &path.path.join("."));
    let ns_name = Name::from_string(&ns_str);
    let prefix_dot = format!("{ns_str}.");

    // Explicit mode — `open Foo (x y)`: only the listed names, loud on
    // unknowns (Lean `elabOpenOnly` resolves each ident and errors).
    // Explicit opens are `OpenDecl.explicit` entries, which are NOT filtered
    // by `protected` (only the simple form is).
    if !path.names.is_empty() {
        for short in &path.names {
            let qualified = Name::append(&ns_name, short);
            if !global_exists(env, &qualified) {
                return Err(NamespaceError::NameNotFound {
                    namespace: ns_str,
                    name: short.clone(),
                });
            }
            let alias = apply_renaming(short, &path.renaming);
            state.insert_alias_pub(alias, qualified);
        }
        return Ok(());
    }

    // Renaming mode — `open Foo renaming x → y`: ONLY the renamed pairs are
    // brought into scope, as explicit aliases `y ↦ Foo.x` (Lean
    // `elabOpenRenaming` adds one `OpenDecl.explicit` per pair and nothing
    // else). Unknown source names are loud errors.
    if !path.renaming.is_empty() {
        for rename in &path.renaming {
            let qualified = Name::append(&ns_name, &rename.from);
            if !global_exists(env, &qualified) {
                return Err(NamespaceError::NameNotFound {
                    namespace: ns_str,
                    name: rename.from.clone(),
                });
            }
            state.insert_alias_pub(rename.to.clone(), qualified);
        }
        return Ok(());
    }

    // Hiding validation — each hidden name must exist in the namespace (Lean
    // `elabOpenHiding` resolves every hidden ident; unknowns are errors).
    for hidden in &path.hiding {
        let qualified = Name::append(&ns_name, hidden);
        if !global_exists(env, &qualified) {
            return Err(NamespaceError::NameNotFound {
                namespace: ns_str,
                name: hidden.clone(),
            });
        }
    }

    // Simple open (optionally minus the hidden names): import all
    // non-protected direct children under the prefix.
    let mut found_any = false;
    for ci in env.constants() {
        let ci_str = ci.name.to_string();
        if let Some(suffix) = ci_str.strip_prefix(&prefix_dot) {
            // Only import direct children (no nested dots).
            if !suffix.contains('.') {
                found_any = true;

                // Check hiding list.
                if path.hiding.contains(&suffix.to_string()) {
                    continue;
                }

                // `protected` declarations are excluded from simple opens
                // (Lean `ResolveName.lean`: the `OpenDecl.simple` candidate
                // walk skips `isProtected` names) — `protected def Foo.x`
                // stays qualified-only under `open Foo` (namespaces_scoping/
                // p16).
                if env.is_protected(&ci.name) {
                    continue;
                }

                state.insert_alias_pub(suffix.to_owned(), ci.name.clone());
            }
        }
    }

    if found_any {
        // Track the opened namespace itself (scope-rollback aware) so
        // diagnostics can point at protected members hidden by the simple
        // open ("`x` is protected; use `Foo.x`").
        state.open_namespace_scoped(ns_name);
    } else if env.get_const(&ns_name).is_none() {
        // Lean 4 errors on `open` of an unknown namespace, but clean's import
        // lanes legitimately open namespaces whose members arrive later
        // (partial .olean loads, staged preludes), so an EMPTY simple open
        // stays a tolerated no-op here. The selective / renaming / hiding
        // forms above are loud — they name specific members.
    }

    Ok(())
}

/// Apply renaming rules to a short name.
fn apply_renaming(short: &str, renamings: &[clean_parser::OpenRename]) -> String {
    for r in renamings {
        if r.from == short {
            return r.to.clone();
        }
    }
    short.to_string()
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
    source_ns: &[String],
    names: &[String],
    current_ns: Option<&str>,
    state: &mut NamespaceState,
) -> Result<(), NamespaceError> {
    let ns_str = resolve_namespace_outward(env, state.current_namespace(), &source_ns.join("."));
    let ns_name = Name::from_string(&ns_str);

    for short in names {
        let qualified = Name::append(&ns_name, short);
        if !global_exists(env, &qualified) {
            return Err(NamespaceError::NameNotFound {
                namespace: ns_str,
                name: short.clone(),
            });
        }

        // The alias lives in the CURRENT namespace: bare at root, qualified
        // (`MyLib.add`) inside `namespace MyLib`.
        let export_short = match current_ns {
            Some(ns) if !ns.is_empty() => format!("{ns}.{short}"),
            _ => short.clone(),
        };
        state.insert_alias_unscoped(export_short.clone(), qualified.clone());

        // Record the export for downstream consumers.
        state.push_export(Alias {
            short: export_short,
            target: qualified,
        });
    }
    Ok(())
}
