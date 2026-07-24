// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared helper for namespaces whose declarations are all simple `Type u` axioms.
//!
//! Many topology namespaces (PrincipalBundle, Connection, Symplectic, Kahler, Spin)
//! declare all constants with the same signature: `(u : Level) → Type (u+1)`.
//! This module provides a single payload builder for that pattern.

use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

/// Build a payload of simple `Type u` axioms from a list of declaration names.
///
/// Each declaration gets:
/// - `level_params: [u]`
/// - `type_: Sort (u + 1)`  (i.e., `Type u`)
/// - No value (axiom)
/// - Not reducible
pub(crate) fn build_simple_type_u_payload(names: &[&str]) -> Vec<ConstantInfo> {
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());
    let type_u = Expr::sort(Level::succ(u_level));

    names
        .iter()
        .map(|name| ConstantInfo {
            name: Name::from_string(name),
            level_params: vec![u.clone()],
            type_: type_u.clone(),
            value: None,
            is_reducible: false,
            reducibility: Reducibility::Regular(0),
            kind: ConstantKind::Axiom,
        })
        .collect()
}
