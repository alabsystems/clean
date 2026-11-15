// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Refuse to compile a body that builds or takes apart a `String` as the
//! prelude's constructor cell.
//!
//! The prelude models `String` as the structure `String.mk (data : List Char)`,
//! but the native runtime's `String` is a flat byte string
//! (`clean_mk_string`), and every string shim (`l_IO_println`,
//! `l_String_length`, `l_String_decEq`, …) reads that carrier. A compiled body
//! that says `String.mk cs` allocates a one-field constructor cell instead
//! (`clean_alloc_ctor(0, 1, 0, cs)`), and one that projects `s.data` or
//! eliminates a `String` reads field 0 of a byte string
//! (`clean_ctor_get(s, 0)`). Measured 2026-09-25 on the P0_EXEC branch through
//! `clean run`, against pinned Lean v4.30.0-rc2 `lean --run`:
//!
//! * `IO.println (toString (Nat.repr 42))` printed an empty line at exit 0
//!   (Lean: `42`) — the prelude's `Nat.repr` is
//!   `List.asString (Nat.toDigits 10 n)` and `List.asString` is `String.mk`
//!   (`env/data_nat_repr.rs`);
//! * `IO.println ['a', 'b'].asString` printed an empty line at exit 0
//!   (Lean: `ab`);
//! * `IO.println (String.mk [])` printed two garbage bytes at exit 0
//!   (Lean: an empty line);
//! * `toString ("abc" == String.mk ['a', 'b', 'c'])` printed `false` at exit 0
//!   (Lean: `true`);
//! * `"ab".data` died with SIGSEGV and `['x'].asString.length` with SIGBUS.
//!
//! `native_build` already refused a `String.*` body lowered from source by its
//! SYMBOL NAME in the emitted C; a user declaration, or a prelude one outside
//! that namespace (`Nat.repr`, `List.asString`), never met that check. This
//! audit reads the kernel VALUE of every compiled body instead: a
//! computational occurrence of the constructor, the projection, or an
//! eliminator of `String` refuses the build (`native-string-carrier`). Binder
//! types and `∀` are not computational and are not scanned.

use std::collections::HashSet;

use crate::native_string_layout_policy::StringLayoutPolicy;
use clean_kernel::{Expr, ExprKind, Name};

/// The constants whose computational use reads or builds the constructor
/// cell: the constructor, the projection function, and the eliminators.
const STRING_CELL_CONSTS: &[&str] = &[
    // The byte-backed constructor/projection remain closed until their actual
    // checked-source C and TrustCG execution qualifies the complete bridge.
    "String.ofByteArray",
    "String.toByteArray",
    "String.mk",
    "String.data",
    "String.casesOn",
    "String.rec",
    "String.recOn",
];

/// A body that treats the runtime's byte-string `String` as a constructor cell.
#[derive(Debug, thiserror::Error)]
#[error(
    "native build refuses `{decl}`: it {what}, but the native runtime's `String` is a flat \
     byte string, not the prelude's `String.mk (data : List Char)` cell, so the compiled code \
     would print a wrong answer or read past the object (`Nat.repr 42` printed an empty line \
     at exit 0; Lean prints `42`) (native-string-carrier)."
)]
pub(crate) struct StringCarrierRefusal {
    /// The declaration being audited.
    decl: String,
    /// What was found, in words.
    what: String,
}

/// Audit one declaration's value.
pub(crate) fn check_string_carrier(decl: &Name, value: &Expr) -> Result<(), StringCarrierRefusal> {
    check_with_policy(decl, value, StringLayoutPolicy::default())
}

pub(crate) fn check_string_carrier_in_env(
    env: &clean_kernel::Environment,
    decl: &Name,
    value: &Expr,
) -> Result<(), StringCarrierRefusal> {
    let policy = StringLayoutPolicy::from_env(env);
    if !policy.permits_source_decl(env, decl) {
        return check_string_carrier(decl, value);
    }
    check_with_policy(decl, value, policy)
}

fn check_with_policy(
    decl: &Name,
    value: &Expr,
    policy: StringLayoutPolicy,
) -> Result<(), StringCarrierRefusal> {
    match first_cell_use(value, policy) {
        Some(what) => Err(StringCarrierRefusal {
            decl: decl.to_string(),
            what,
        }),
        None => Ok(()),
    }
}

/// The first computational use of the `String` cell in `value`, described.
/// Shared subterms are visited once, as `mentions_actions` does, so a value
/// with heavy sharing costs its node count, not its tree size.
fn first_cell_use(value: &Expr, policy: StringLayoutPolicy) -> Option<String> {
    let mut stack: Vec<&Expr> = vec![value];
    let mut seen: HashSet<*const Expr> = HashSet::new();
    while let Some(e) = stack.pop() {
        if !seen.insert(e as *const Expr) {
            continue;
        }
        match e.kind() {
            ExprKind::Const(name, _) => {
                let text = name.to_string();
                let byte_backed = policy.permits_byte_backed_bodies()
                    && [
                        "String.ofByteArray",
                        "String.toByteArray",
                        "String.rec",
                        "String.recOn",
                        "String.casesOn",
                    ]
                    .iter()
                    .any(|canonical| *name == Name::from_string(canonical));
                if STRING_CELL_CONSTS.contains(&text.as_str()) && !byte_backed {
                    return Some(format!("uses `{text}`"));
                }
            }
            ExprKind::Proj(structure, idx, inner) => {
                if structure.to_string() == "String"
                    && (!policy.permits_byte_backed_bodies() || *idx > 1)
                {
                    return Some("projects a field of a `String`".to_string());
                }
                stack.push(inner);
            }
            ExprKind::App(f, a) => {
                stack.push(f);
                stack.push(a);
            }
            // A binder's type is erased; only the body runs.
            ExprKind::Lam(_, _, body) => stack.push(body),
            ExprKind::Let(_, _, val, body, _) => {
                stack.push(val);
                stack.push(body);
            }
            ExprKind::MData(_, inner) => stack.push(inner),
            // `∀`, sorts, literals, variables: nothing here runs.
            _ => {}
        }
    }
    None
}

#[cfg(test)]
#[path = "native_string_carrier_audit_tests.rs"]
mod tests;
