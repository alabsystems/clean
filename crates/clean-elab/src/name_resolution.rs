// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Name resolution helpers for the elaborator.

use crate::namespace::NamespaceState;
use clean_kernel::name::Name;
use clean_kernel::Environment;
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
