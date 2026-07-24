// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended IO monad elaboration: error handling, IO references, tasks,
//! file/process/environment operations, monad transformer stacking,
//! and IO purity boundary detection.
//!
//! Reference: Lean 4 `src/Init/System/IO.lean`, `src/Init/Control/`.

use crate::error::ElabError;
use clean_kernel::Name;
use clean_parser::{SurfaceBinder, SurfaceBinderInfo, SurfaceExpr};

// ---------------------------------------------------------------------------
// Extended IO operation names
// ---------------------------------------------------------------------------

pub(crate) const IO_THROW: &str = "IO.throw";
pub(crate) const IO_CATCH: &str = "IO.catch";
pub(crate) const IO_TRY_CATCH: &str = "IO.tryCatch";
pub(crate) const IO_TRY_FINALLY: &str = "IO.tryFinally";

pub(crate) const IOREF_MK: &str = "IORef.mk";
pub(crate) const IOREF_GET: &str = "IORef.get";
pub(crate) const IOREF_SET: &str = "IORef.set";
pub(crate) const IOREF_MODIFY: &str = "IORef.modify";
pub(crate) const IOREF_SWAP: &str = "IORef.swap";

pub(crate) const TASK_SPAWN: &str = "Task.spawn";
pub(crate) const TASK_GET: &str = "Task.get";

pub(crate) const FS_READ_FILE: &str = "IO.FS.readFile";
pub(crate) const FS_WRITE_FILE: &str = "IO.FS.writeFile";
pub(crate) const FS_REMOVE_FILE: &str = "IO.FS.removeFile";
pub(crate) const FS_READ_DIR: &str = "IO.FS.readDir";

pub(crate) const PROCESS_RUN: &str = "IO.Process.run";
pub(crate) const PROCESS_SPAWN: &str = "IO.Process.spawn";

pub(crate) const IO_GET_ENV: &str = "IO.getEnv";
pub(crate) const IO_GET_CWD: &str = "IO.getCwd";

pub(crate) const STATE_T: &str = "StateT";
pub(crate) const EXCEPT_T: &str = "ExceptT";
pub(crate) const READER_T: &str = "ReaderT";

/// All extended IO operations for quick membership checks.
pub(crate) const EXTENDED_IO_OPS: &[&str] = &[
    IO_THROW,
    IO_CATCH,
    IO_TRY_CATCH,
    IO_TRY_FINALLY,
    IOREF_MK,
    IOREF_GET,
    IOREF_SET,
    IOREF_MODIFY,
    IOREF_SWAP,
    TASK_SPAWN,
    TASK_GET,
    FS_READ_FILE,
    FS_WRITE_FILE,
    FS_REMOVE_FILE,
    FS_READ_DIR,
    PROCESS_RUN,
    PROCESS_SPAWN,
    IO_GET_ENV,
    IO_GET_CWD,
];

pub(crate) const MONAD_TRANSFORMERS: &[&str] = &[STATE_T, EXCEPT_T, READER_T];

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration for extended IO monad elaboration.
#[derive(Debug, Clone)]
pub(crate) struct IoMonadExtConfig {
    pub(crate) enforce_purity: bool,
    pub(crate) max_transformer_depth: usize,
}

impl Default for IoMonadExtConfig {
    fn default() -> Self {
        Self {
            enforce_purity: true,
            max_transformer_depth: 8,
        }
    }
}

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors specific to extended IO monad elaboration.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum IoMonadExtError {
    #[error("IO action `{operation}` used in pure context `{context}`")]
    PurityViolation { operation: String, context: String },
    #[error("monad transformer stack depth {depth} exceeds maximum {max}")]
    TransformerStackOverflow { depth: usize, max: usize },
    #[error("unrecognized extended IO operation: {0}")]
    UnrecognizedOp(String),
    #[error("invalid IO type annotation: expected `IO {expected}`, got `{actual}`")]
    InvalidIoType { expected: String, actual: String },
    #[error("IO operation `{op}` requires {expected} arguments, got {actual}")]
    MissingArgument {
        op: String,
        expected: usize,
        actual: usize,
    },
}

impl From<IoMonadExtError> for ElabError {
    fn from(err: IoMonadExtError) -> Self {
        ElabError::NotImplemented(err.to_string())
    }
}

// ---------------------------------------------------------------------------
// Helpers: single-arg and two-arg IO operation constructors
// ---------------------------------------------------------------------------

/// Build `<op> arg`.
fn mk_io_app1(op: &str, arg: SurfaceExpr) -> SurfaceExpr {
    SurfaceExpr::app(SurfaceExpr::ident(op), vec![arg])
}

/// Build `<op> arg1 arg2`.
fn mk_io_app2(op: &str, a: SurfaceExpr, b: SurfaceExpr) -> SurfaceExpr {
    SurfaceExpr::app(SurfaceExpr::ident(op), vec![a, b])
}

/// Build `<op> action (fun err_name => handler)`.
fn mk_io_with_handler(
    op: &str,
    action: SurfaceExpr,
    err_name: &str,
    handler: SurfaceExpr,
) -> SurfaceExpr {
    let binder = SurfaceBinder::new(err_name, None, SurfaceBinderInfo::Explicit);
    let handler_fn = SurfaceExpr::lambda(vec![binder], handler);
    SurfaceExpr::app(SurfaceExpr::ident(op), vec![action, handler_fn])
}

// ---------------------------------------------------------------------------
// IO error handling constructors
// ---------------------------------------------------------------------------

/// Build `IO.throw err`.
pub(crate) fn mk_io_throw(err_val: SurfaceExpr) -> SurfaceExpr {
    mk_io_app1(IO_THROW, err_val)
}

/// Build `IO.catch action (fun err_name => handler)`.
pub(crate) fn mk_io_catch(
    action: SurfaceExpr,
    err_name: &str,
    handler: SurfaceExpr,
) -> SurfaceExpr {
    mk_io_with_handler(IO_CATCH, action, err_name, handler)
}

/// Build `IO.tryCatch action (fun err_name => handler)`.
pub(crate) fn mk_io_try_catch(
    action: SurfaceExpr,
    err_name: &str,
    handler: SurfaceExpr,
) -> SurfaceExpr {
    mk_io_with_handler(IO_TRY_CATCH, action, err_name, handler)
}

/// Build `IO.tryFinally action finalizer`.
pub(crate) fn mk_io_try_finally(action: SurfaceExpr, finalizer: SurfaceExpr) -> SurfaceExpr {
    mk_io_app2(IO_TRY_FINALLY, action, finalizer)
}

// ---------------------------------------------------------------------------
// IORef operation constructors
// ---------------------------------------------------------------------------

/// Build `IORef.mk init_val`.
pub(crate) fn mk_ioref_mk(init_val: SurfaceExpr) -> SurfaceExpr {
    mk_io_app1(IOREF_MK, init_val)
}
/// Build `IORef.get ref_expr`.
pub(crate) fn mk_ioref_get(ref_expr: SurfaceExpr) -> SurfaceExpr {
    mk_io_app1(IOREF_GET, ref_expr)
}
/// Build `IORef.set ref_expr new_val`.
pub(crate) fn mk_ioref_set(r: SurfaceExpr, v: SurfaceExpr) -> SurfaceExpr {
    mk_io_app2(IOREF_SET, r, v)
}
/// Build `IORef.modify ref_expr f`.
pub(crate) fn mk_ioref_modify(r: SurfaceExpr, f: SurfaceExpr) -> SurfaceExpr {
    mk_io_app2(IOREF_MODIFY, r, f)
}
/// Build `IORef.swap ref_expr new_val`.
pub(crate) fn mk_ioref_swap(r: SurfaceExpr, v: SurfaceExpr) -> SurfaceExpr {
    mk_io_app2(IOREF_SWAP, r, v)
}

// ---------------------------------------------------------------------------
// Task operation constructors
// ---------------------------------------------------------------------------

/// Build `Task.spawn action`.
pub(crate) fn mk_task_spawn(action: SurfaceExpr) -> SurfaceExpr {
    mk_io_app1(TASK_SPAWN, action)
}
/// Build `Task.get task_expr`.
pub(crate) fn mk_task_get(task: SurfaceExpr) -> SurfaceExpr {
    mk_io_app1(TASK_GET, task)
}

// ---------------------------------------------------------------------------
// File system operation constructors
// ---------------------------------------------------------------------------

/// Build `IO.FS.readFile path`.
pub(crate) fn mk_fs_read_file(path: SurfaceExpr) -> SurfaceExpr {
    mk_io_app1(FS_READ_FILE, path)
}
/// Build `IO.FS.writeFile path content`.
pub(crate) fn mk_fs_write_file(p: SurfaceExpr, c: SurfaceExpr) -> SurfaceExpr {
    mk_io_app2(FS_WRITE_FILE, p, c)
}
/// Build `IO.FS.removeFile path`.
pub(crate) fn mk_fs_remove_file(path: SurfaceExpr) -> SurfaceExpr {
    mk_io_app1(FS_REMOVE_FILE, path)
}

// ---------------------------------------------------------------------------
// Process and environment operation constructors
// ---------------------------------------------------------------------------

/// Build `IO.Process.run args`.
pub(crate) fn mk_process_run(args: SurfaceExpr) -> SurfaceExpr {
    mk_io_app1(PROCESS_RUN, args)
}
/// Build `IO.Process.spawn config`.
pub(crate) fn mk_process_spawn(cfg: SurfaceExpr) -> SurfaceExpr {
    mk_io_app1(PROCESS_SPAWN, cfg)
}
/// Build `IO.getEnv var_name`.
pub(crate) fn mk_io_get_env(var: SurfaceExpr) -> SurfaceExpr {
    mk_io_app1(IO_GET_ENV, var)
}
/// Build `IO.getCwd`.
pub(crate) fn mk_io_get_cwd() -> SurfaceExpr {
    SurfaceExpr::ident(IO_GET_CWD)
}

// ---------------------------------------------------------------------------
// Monad transformer stacking
// ---------------------------------------------------------------------------

/// Represents a monad transformer layer.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum TransformerLayer {
    StateT { state_type: String },
    ExceptT { error_type: String },
    ReaderT { env_type: String },
}

/// Project a transformer layer into its `(head_name, param)` pair.
/// Internal helper for `TransformerStack::build_type`.
fn layer_head(layer: &TransformerLayer) -> (&'static str, &str) {
    match layer {
        TransformerLayer::StateT { state_type } => (STATE_T, state_type.as_str()),
        TransformerLayer::ExceptT { error_type } => (EXCEPT_T, error_type.as_str()),
        TransformerLayer::ReaderT { env_type } => (READER_T, env_type.as_str()),
    }
}

/// A monad transformer stack over IO.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TransformerStack {
    pub(crate) layers: Vec<TransformerLayer>,
}

impl TransformerStack {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self { layers: Vec::new() }
    }

    /// Push a layer. Errors on overflow.
    pub(crate) fn push(
        &mut self,
        layer: TransformerLayer,
        config: &IoMonadExtConfig,
    ) -> Result<(), IoMonadExtError> {
        if self.layers.len() >= config.max_transformer_depth {
            return Err(IoMonadExtError::TransformerStackOverflow {
                depth: self.layers.len() + 1,
                max: config.max_transformer_depth,
            });
        }
        self.layers.push(layer);
        Ok(())
    }

    #[must_use]
    pub(crate) fn depth(&self) -> usize {
        self.layers.len()
    }

    /// Build the full transformer type expression.
    ///
    /// For `[StateT Nat, ExceptT String]` with result `α`,
    /// produces `StateT Nat (ExceptT String IO) α`.
    /// `layers[0]` is the outermost transformer, `layers[N-1]` is
    /// the innermost, sitting directly over `IO`.
    ///
    /// Closed Gap 10 in Wave 93: the outermost layer is now folded
    /// into a single `App(Ident(head), [param, inner, result_type])`,
    /// rather than a nested `App(App(head, [param, inner]),
    /// [result_type])`. The previous form left the outer App's head
    /// as another App, so `app_fn_name` saw `None` instead of the
    /// expected `StateT` / `ExceptT` / ... head.
    #[must_use]
    pub(crate) fn build_type(&self, result_type: SurfaceExpr) -> SurfaceExpr {
        // Zero layers: `IO α` directly.
        let Some((outermost, intermediates)) = self.layers.split_first() else {
            return SurfaceExpr::app(SurfaceExpr::ident("IO"), vec![result_type]);
        };

        // Walk from the innermost layer outward, wrapping `IO` with
        // each transformer head applied to (param, inner). After the
        // loop `inner` is the un-applied transformer stack rooted at
        // `IO`, i.e. `Layer_2 P_2 (... (Layer_{n-1} P_{n-1} IO))`.
        let mut inner = SurfaceExpr::ident("IO");
        for layer in intermediates.iter().rev() {
            let (name, param) = layer_head(layer);
            inner = SurfaceExpr::app(
                SurfaceExpr::ident(name),
                vec![SurfaceExpr::ident(param), inner],
            );
        }

        // Fold the outermost layer together with the result type so
        // the top expression's head is the transformer ident, not
        // another App. The shape is `head param inner result_type`.
        let (name, param) = layer_head(outermost);
        SurfaceExpr::app(
            SurfaceExpr::ident(name),
            vec![SurfaceExpr::ident(param), inner, result_type],
        )
    }
}

// ---------------------------------------------------------------------------
// Extended IO operation recognition
// ---------------------------------------------------------------------------

#[must_use]
pub(crate) fn is_extended_io_op(name: &str) -> bool {
    EXTENDED_IO_OPS.contains(&name)
}

#[must_use]
pub(crate) fn is_monad_transformer(name: &str) -> bool {
    MONAD_TRANSFORMERS.contains(&name)
}

#[must_use]
pub(crate) fn name_to_ext_io_op(name: &Name) -> Option<&'static str> {
    let s = name.to_string();
    EXTENDED_IO_OPS.iter().find(|&&op| op == s).copied()
}

// ---------------------------------------------------------------------------
// IO type checking
// ---------------------------------------------------------------------------

/// Returns inner type `α` if expression is `IO α`.
#[must_use]
pub(crate) fn check_io_type(expr: &SurfaceExpr) -> Option<&SurfaceExpr> {
    match expr {
        SurfaceExpr::App(_, func, args) => {
            if let SurfaceExpr::Ident(_, name) = func.as_ref() {
                if name == "IO" && args.len() == 1 {
                    return Some(&args[0].expr);
                }
            }
            None
        }
        _ => None,
    }
}

/// Check if expression is a transformer-wrapped IO type (`StateT σ (... IO) α`).
#[must_use]
pub(crate) fn is_transformer_io_type(expr: &SurfaceExpr) -> bool {
    match expr {
        SurfaceExpr::App(_, func, args) => {
            if let SurfaceExpr::Ident(_, name) = func.as_ref() {
                if is_monad_transformer(name) && args.len() >= 2 {
                    return contains_io_base(&args[1].expr);
                }
            }
            false
        }
        _ => false,
    }
}

fn contains_io_base(expr: &SurfaceExpr) -> bool {
    match expr {
        SurfaceExpr::Ident(_, name) => name == "IO",
        SurfaceExpr::App(_, func, args) => {
            if let SurfaceExpr::Ident(_, name) = func.as_ref() {
                if name == "IO" {
                    return true;
                }
                if is_monad_transformer(name) && args.len() >= 2 {
                    return contains_io_base(&args[1].expr);
                }
            }
            false
        }
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Purity boundary detection
// ---------------------------------------------------------------------------

/// Context in which an expression appears, for purity checking.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum PurityContext {
    IoFunction,
    PureFunction { name: String },
    Theorem { name: String },
    StructField { struct_name: String },
}

impl PurityContext {
    #[must_use]
    pub(crate) fn allows_io(&self) -> bool {
        matches!(self, PurityContext::IoFunction)
    }
}

impl std::fmt::Display for PurityContext {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PurityContext::IoFunction => write!(f, "IO function"),
            PurityContext::PureFunction { name } => write!(f, "pure function `{name}`"),
            PurityContext::Theorem { name } => write!(f, "theorem `{name}`"),
            PurityContext::StructField { struct_name } => {
                write!(f, "structure field of `{struct_name}`")
            }
        }
    }
}

/// Check that an IO operation is not used in a pure context.
pub(crate) fn check_io_purity(
    operation: &str,
    ctx: &PurityContext,
    config: &IoMonadExtConfig,
) -> Result<(), IoMonadExtError> {
    if !config.enforce_purity {
        return Ok(());
    }
    if !ctx.allows_io() {
        return Err(IoMonadExtError::PurityViolation {
            operation: operation.to_owned(),
            context: ctx.to_string(),
        });
    }
    Ok(())
}

/// Walk an expression tree checking for IO operations in a pure context.
pub(crate) fn check_expr_purity(
    expr: &SurfaceExpr,
    ctx: &PurityContext,
    config: &IoMonadExtConfig,
) -> Result<(), IoMonadExtError> {
    if ctx.allows_io() || !config.enforce_purity {
        return Ok(());
    }
    check_expr_purity_inner(expr, ctx)
}

fn check_expr_purity_inner(expr: &SurfaceExpr, ctx: &PurityContext) -> Result<(), IoMonadExtError> {
    match expr {
        SurfaceExpr::App(_, func, args) => {
            if let SurfaceExpr::Ident(_, name) = func.as_ref() {
                if is_extended_io_op(name) || crate::io_monad::is_io_operation(name) {
                    return Err(IoMonadExtError::PurityViolation {
                        operation: name.clone(),
                        context: ctx.to_string(),
                    });
                }
            }
            check_expr_purity_inner(func, ctx)?;
            for arg in args {
                check_expr_purity_inner(&arg.expr, ctx)?;
            }
            Ok(())
        }
        SurfaceExpr::Lambda(_, _, body) => check_expr_purity_inner(body, ctx),
        SurfaceExpr::Let(_, _, val, body) => {
            check_expr_purity_inner(val, ctx)?;
            check_expr_purity_inner(body, ctx)
        }
        SurfaceExpr::If(_, cond, then_br, else_br) => {
            check_expr_purity_inner(cond, ctx)?;
            check_expr_purity_inner(then_br, ctx)?;
            check_expr_purity_inner(else_br, ctx)
        }
        _ => Ok(()),
    }
}
