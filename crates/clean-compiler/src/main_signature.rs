// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The executable entry types recognized by Lean 4.36's LCNF compiler.

use clean_kernel::{Expr, ExprKind, Name};

/// Lean's diagnostic for a compiled global `main` of any other type.
pub const INVALID_MAIN_TYPE: &str =
    "`main` function must have type `(List String →)? IO (UInt32 | Unit | PUnit)`";

/// The two pieces of the process ABI determined by the elaborated type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MainSignature {
    /// Marshal the process arguments as a Lean list of strings.
    pub takes_argv: bool,
    /// Use the returned UInt32 as the exit status.
    pub returns_status: bool,
}

impl MainSignature {
    /// Match Lean's `LCNF.isValidMainType`. The compiler inspects the kernel
    /// expression as written, so even a definitionally equal alias may fail.
    #[must_use]
    pub fn from_type(ty: &Expr) -> Option<Self> {
        fn named(e: &Expr, name: &str) -> bool {
            matches!(e.kind(), ExprKind::Const(n, _) if n == &Name::interned(name))
        }
        let (takes_argv, result) = match ty.kind() {
            ExprKind::Pi(_, domain, result) => match domain.kind() {
                ExprKind::App(list, elem) if named(list, "List") && named(elem, "String") => {
                    (true, result.as_ref())
                }
                _ => return None,
            },
            _ => (false, ty),
        };
        let ExprKind::App(io, result) = result.kind() else {
            return None;
        };
        let returns_status = named(result, "UInt32");
        if named(io, "IO") && (returns_status || named(result, "Unit") || named(result, "PUnit")) {
            Some(Self {
                takes_argv,
                returns_status,
            })
        } else {
            None
        }
    }
}
