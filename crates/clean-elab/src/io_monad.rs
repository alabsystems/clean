// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
// Per-item expect (not a module-level allow): `is_io_operation` is wired from
// io_monad_ext.rs; if production wiring lands, the expectation trips and the
// annotation must be removed item-by-item.

//! IO monad elaboration: type recognition, main entry point detection,
//! and monadic desugaring for IO computations.
//!
//! This module handles the elaboration-time aspects of Lean's IO monad:
//!
//! - **Type recognition:** Detect when expressions or declarations have `IO α` type
//! - **Main detection:** Identify `def main : IO Unit` entry points
//! - **Bind desugaring:** Transform `IO.bind action (fun x => rest)` sequences
//! - **Pure insertion:** Wrap pure values in `IO.pure`
//! - **Error handling:** Recognize `IO.tryCatch` patterns
//! - **IO.Ref operations:** Mutable reference get/set/modify
//! - **Built-in actions:** `IO.println`, `IO.print`, `IO.getLine` recognition
//! - **Entry point validation:** Ensure `main` has type `IO Unit` or `IO UInt32`
//!
//! The module operates at the surface expression level, producing desugared
//! `SurfaceExpr` trees that feed into the normal elaboration pipeline.
//!
//! Reference: Lean 4 `src/Lean/Elab/Do/Basic.lean`, `src/Init/System/IO.lean`

use crate::error::ElabError;
use clean_kernel::Name;
use clean_parser::{SurfaceBinder, SurfaceBinderInfo, SurfaceExpr};

// ---------------------------------------------------------------------------
// IO type names
// ---------------------------------------------------------------------------

/// Known IO type constructor names.
#[cfg_attr(not(test), expect(dead_code))]
const IO_TYPE_NAME: &str = "IO";
#[cfg_attr(not(test), expect(dead_code))]
const IO_UNIT_TYPE: &str = "Unit";
#[cfg_attr(not(test), expect(dead_code))]
const IO_UINT32_TYPE: &str = "UInt32";

/// Known IO operation names used in elaboration.
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) const IO_BIND: &str = "IO.bind";
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) const IO_PURE: &str = "IO.pure";
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) const IO_MAP: &str = "IO.map";
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) const IO_TRY_CATCH: &str = "IO.tryCatch";
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) const IO_CATCH: &str = "IO.catch";
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) const IO_PRINTLN: &str = "IO.println";
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) const IO_PRINT: &str = "IO.print";
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) const IO_GET_LINE: &str = "IO.getLine";
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) const IO_REF_NEW: &str = "IO.Ref.new";
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) const IO_REF_GET: &str = "IO.Ref.get";
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) const IO_REF_SET: &str = "IO.Ref.set";
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) const IO_REF_MODIFY: &str = "IO.Ref.modify";

/// All recognized IO operations for quick membership checks.
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) const IO_OPERATIONS: &[&str] = &[
    IO_BIND,
    IO_PURE,
    IO_MAP,
    IO_TRY_CATCH,
    IO_CATCH,
    IO_PRINTLN,
    IO_PRINT,
    IO_GET_LINE,
    IO_REF_NEW,
    IO_REF_GET,
    IO_REF_SET,
    IO_REF_MODIFY,
    "IO.eprintln",
    "IO.getEnv",
    "IO.currentDir",
    "IO.FS.readFile",
    "IO.FS.writeFile",
    "IO.Process.exit",
    "IO.monoMsNow",
    "IO.panic",
];

// ---------------------------------------------------------------------------
// IO type recognition
// ---------------------------------------------------------------------------

/// Check if a surface expression represents an `IO α` type.
///
/// Recognizes patterns:
/// - `IO α` (application of IO to a type argument)
/// - `IO Unit`, `IO UInt32` (specific IO result types)
///
/// # ENSURES
/// - Returns `true` if the expression is structurally an IO type application
#[must_use]
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) fn is_io_type(expr: &SurfaceExpr) -> bool {
    match expr {
        SurfaceExpr::Ident(_, name) => name == IO_TYPE_NAME,
        SurfaceExpr::App(_, func, _) => {
            if let SurfaceExpr::Ident(_, name) = func.as_ref() {
                name == IO_TYPE_NAME
            } else {
                false
            }
        }
        _ => false,
    }
}

/// Check if a surface expression is `IO Unit`.
#[must_use]
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) fn is_io_unit(expr: &SurfaceExpr) -> bool {
    match expr {
        SurfaceExpr::App(_, func, args) => {
            if let SurfaceExpr::Ident(_, name) = func.as_ref() {
                if name != IO_TYPE_NAME || args.len() != 1 {
                    return false;
                }
                matches!(&args[0].expr, SurfaceExpr::Ident(_, arg_name) if arg_name == IO_UNIT_TYPE)
            } else {
                false
            }
        }
        _ => false,
    }
}

/// Check if a surface expression is `IO UInt32`.
#[must_use]
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) fn is_io_uint32(expr: &SurfaceExpr) -> bool {
    match expr {
        SurfaceExpr::App(_, func, args) => {
            if let SurfaceExpr::Ident(_, name) = func.as_ref() {
                if name != IO_TYPE_NAME || args.len() != 1 {
                    return false;
                }
                matches!(&args[0].expr, SurfaceExpr::Ident(_, arg_name) if arg_name == IO_UINT32_TYPE)
            } else {
                false
            }
        }
        _ => false,
    }
}

/// Extract the result type `α` from an `IO α` surface expression.
///
/// Returns `None` if the expression is not an IO type application.
#[must_use]
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) fn io_result_type(expr: &SurfaceExpr) -> Option<&SurfaceExpr> {
    match expr {
        SurfaceExpr::App(_, func, args) => {
            if let SurfaceExpr::Ident(_, name) = func.as_ref() {
                if name == IO_TYPE_NAME && args.len() == 1 {
                    return Some(&args[0].expr);
                }
            }
            None
        }
        _ => None,
    }
}

/// Check if a name is a known IO operation.
#[must_use]
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) fn is_io_operation(name: &str) -> bool {
    IO_OPERATIONS.contains(&name)
}

// ---------------------------------------------------------------------------
// Main function detection and validation
// ---------------------------------------------------------------------------

/// Result of validating a main function declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) enum MainValidation {
    /// Valid `main : IO Unit` entry point.
    IoUnit,
    /// Valid `main : IO UInt32` entry point (with exit code).
    IoUInt32,
    /// Not a main function (different name).
    NotMain,
    /// Named `main` but has an invalid type.
    InvalidMainType { actual_type: String },
}

/// Check if a declaration name is `main` and validate its type.
///
/// Lean 4 supports two main signatures:
/// - `def main : IO Unit` — standard entry point
/// - `def main : IO UInt32` — entry point returning exit code
/// - `def main (args : List String) : IO Unit` — with command-line args
/// - `def main (args : List String) : IO UInt32` — with args and exit code
///
/// # REQUIRES
/// - `name` is the declaration name
/// - `ty` is the declared return type (after binders)
///
/// # ENSURES
/// - Returns `MainValidation` indicating validity and signature variant
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) fn validate_main(name: &str, ty: Option<&SurfaceExpr>) -> MainValidation {
    if name != "main" {
        return MainValidation::NotMain;
    }

    let Some(ty) = ty else {
        return MainValidation::InvalidMainType {
            actual_type: "<none>".to_owned(),
        };
    };

    if is_io_unit(ty) {
        return MainValidation::IoUnit;
    }

    if is_io_uint32(ty) {
        return MainValidation::IoUInt32;
    }

    // Check for bare `IO` (missing result type annotation)
    if matches!(ty, SurfaceExpr::Ident(_, n) if n == IO_TYPE_NAME) {
        return MainValidation::InvalidMainType {
            actual_type: "IO (missing result type)".to_owned(),
        };
    }

    MainValidation::InvalidMainType {
        actual_type: format!("{ty:?}"),
    }
}

// ---------------------------------------------------------------------------
// IO.bind desugaring
// ---------------------------------------------------------------------------

/// Desugar `IO.bind action (fun x => rest)` from a surface expression.
///
/// Builds: `IO.bind action (fun name => body)`
///
/// This is the core monadic sequencing operation for IO. In do-notation:
/// ```text
/// let x ← action
/// rest
/// ```
/// becomes:
/// ```text
/// IO.bind action (fun x => rest)
/// ```
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) fn mk_io_bind(name: &str, action: SurfaceExpr, body: SurfaceExpr) -> SurfaceExpr {
    let bind_fn = SurfaceExpr::ident(IO_BIND);
    let binder = SurfaceBinder::new(name, None, SurfaceBinderInfo::Explicit);
    let continuation = SurfaceExpr::lambda(vec![binder], body);
    SurfaceExpr::app(bind_fn, vec![action, continuation])
}

/// Desugar a sequence of IO bind steps into nested `IO.bind` calls.
///
/// Each step is a `(name, action)` pair, and the final expression is the
/// terminal value.
///
/// # REQUIRES
/// - `steps` is non-empty, OR `terminal` is provided as the sole result
///
/// # ENSURES
/// - Returns nested `IO.bind` applications threading each step
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) fn desugar_io_binds(
    steps: &[(String, SurfaceExpr)],
    terminal: SurfaceExpr,
) -> SurfaceExpr {
    steps.iter().rev().fold(terminal, |body, (name, action)| {
        mk_io_bind(name, action.clone(), body)
    })
}

// ---------------------------------------------------------------------------
// IO.pure insertion
// ---------------------------------------------------------------------------

/// Wrap a pure value in `IO.pure`.
///
/// Builds: `IO.pure val`
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) fn mk_io_pure(val: SurfaceExpr) -> SurfaceExpr {
    let pure_fn = SurfaceExpr::ident(IO_PURE);
    SurfaceExpr::app(pure_fn, vec![val])
}

/// Wrap a unit value in `IO.pure`.
///
/// Builds: `IO.pure ()`
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) fn mk_io_pure_unit() -> SurfaceExpr {
    mk_io_pure(SurfaceExpr::ident("Unit.unit"))
}

// ---------------------------------------------------------------------------
// IO.map desugaring
// ---------------------------------------------------------------------------

/// Build `IO.map f action`.
///
/// Equivalent to `IO.bind action (fun x => IO.pure (f x))` but more direct.
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) fn mk_io_map(f: SurfaceExpr, action: SurfaceExpr) -> SurfaceExpr {
    let map_fn = SurfaceExpr::ident(IO_MAP);
    SurfaceExpr::app(map_fn, vec![f, action])
}

// ---------------------------------------------------------------------------
// IO error handling
// ---------------------------------------------------------------------------

/// Build `IO.tryCatch action handler`.
///
/// Desugars:
/// ```text
/// try
///   action
/// catch e =>
///   handler
/// ```
/// into:
/// ```text
/// IO.tryCatch action (fun e => handler)
/// ```
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) fn mk_io_try_catch(
    action: SurfaceExpr,
    err_name: &str,
    handler: SurfaceExpr,
) -> SurfaceExpr {
    let try_catch_fn = SurfaceExpr::ident(IO_TRY_CATCH);
    let binder = SurfaceBinder::new(err_name, None, SurfaceBinderInfo::Explicit);
    let handler_fn = SurfaceExpr::lambda(vec![binder], handler);
    SurfaceExpr::app(try_catch_fn, vec![action, handler_fn])
}

// ---------------------------------------------------------------------------
// IO.Ref operations
// ---------------------------------------------------------------------------

/// Build `IO.Ref.new init_val`.
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) fn mk_io_ref_new(init_val: SurfaceExpr) -> SurfaceExpr {
    let ref_new = SurfaceExpr::ident(IO_REF_NEW);
    SurfaceExpr::app(ref_new, vec![init_val])
}

/// Build `IO.Ref.get ref_expr`.
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) fn mk_io_ref_get(ref_expr: SurfaceExpr) -> SurfaceExpr {
    let ref_get = SurfaceExpr::ident(IO_REF_GET);
    SurfaceExpr::app(ref_get, vec![ref_expr])
}

/// Build `IO.Ref.set ref_expr new_val`.
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) fn mk_io_ref_set(ref_expr: SurfaceExpr, new_val: SurfaceExpr) -> SurfaceExpr {
    let ref_set = SurfaceExpr::ident(IO_REF_SET);
    SurfaceExpr::app(ref_set, vec![ref_expr, new_val])
}

/// Build `IO.Ref.modify ref_expr f`.
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) fn mk_io_ref_modify(ref_expr: SurfaceExpr, f: SurfaceExpr) -> SurfaceExpr {
    let ref_modify = SurfaceExpr::ident(IO_REF_MODIFY);
    SurfaceExpr::app(ref_modify, vec![ref_expr, f])
}

// ---------------------------------------------------------------------------
// Built-in IO action constructors
// ---------------------------------------------------------------------------

/// Build `IO.println msg`.
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) fn mk_io_println(msg: SurfaceExpr) -> SurfaceExpr {
    let println_fn = SurfaceExpr::ident(IO_PRINTLN);
    SurfaceExpr::app(println_fn, vec![msg])
}

/// Build `IO.print msg`.
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) fn mk_io_print(msg: SurfaceExpr) -> SurfaceExpr {
    let print_fn = SurfaceExpr::ident(IO_PRINT);
    SurfaceExpr::app(print_fn, vec![msg])
}

/// Build `IO.getLine`.
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) fn mk_io_get_line() -> SurfaceExpr {
    SurfaceExpr::ident(IO_GET_LINE)
}

// ---------------------------------------------------------------------------
// IO monad entry point elaboration
// ---------------------------------------------------------------------------

/// Errors specific to IO monad elaboration.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[allow(dead_code)]
pub(crate) enum IoMonadError {
    /// Main function has wrong type.
    #[error("'main' must have type `IO Unit` or `IO UInt32`, got: {actual}")]
    #[cfg_attr(not(test), expect(dead_code))]
    InvalidMainType { actual: String },

    /// IO bind sequence is empty.
    #[error("empty IO bind sequence")]
    #[cfg_attr(not(test), expect(dead_code))]
    EmptyBindSequence,

    /// IO.tryCatch missing handler.
    #[error("IO.tryCatch requires both action and handler")]
    #[cfg_attr(not(test), expect(dead_code))]
    TryCatchMissingHandler,
}

impl From<IoMonadError> for ElabError {
    fn from(err: IoMonadError) -> Self {
        ElabError::NotImplemented(err.to_string())
    }
}

/// Validate and annotate a declaration as an IO entry point.
///
/// If the declaration is named `main` with a valid IO type, returns
/// the validation result. Otherwise returns `None`.
///
/// This is called during declaration elaboration to detect entry points
/// and emit appropriate metadata for the compiler backend.
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) fn check_io_entry_point(
    name: &str,
    ty: Option<&SurfaceExpr>,
) -> Result<Option<MainValidation>, ElabError> {
    match validate_main(name, ty) {
        MainValidation::NotMain => Ok(None),
        MainValidation::IoUnit => Ok(Some(MainValidation::IoUnit)),
        MainValidation::IoUInt32 => Ok(Some(MainValidation::IoUInt32)),
        MainValidation::InvalidMainType { actual_type } => Err(IoMonadError::InvalidMainType {
            actual: actual_type,
        }
        .into()),
    }
}

/// Build a complete IO program from a sequence of IO statements.
///
/// Given a list of named bind steps and a final expression, produces
/// the fully desugared IO expression tree.
///
/// # Errors
///
/// Returns `IoMonadError::EmptyBindSequence` if both `steps` and
/// `terminal` result in an empty program.
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) fn build_io_program(
    steps: &[(String, SurfaceExpr)],
    terminal: Option<SurfaceExpr>,
) -> Result<SurfaceExpr, ElabError> {
    let terminal = terminal.unwrap_or_else(mk_io_pure_unit);

    if steps.is_empty() {
        return Ok(terminal);
    }

    Ok(desugar_io_binds(steps, terminal))
}

/// Convert a kernel `Name` to a string for IO operation matching.
#[must_use]
#[cfg_attr(not(test), expect(dead_code))]
pub(crate) fn name_to_io_op(name: &Name) -> Option<&'static str> {
    let s = name.to_string();
    IO_OPERATIONS.iter().find(|&&op| op == s).copied()
}
