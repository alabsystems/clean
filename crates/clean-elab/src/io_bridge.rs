// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bridge from kernel `Expr` to runtime `IoAction`.
//!
//! When `#eval` produces an expression whose type is `IO α`, this module
//! translates the WHNF-reduced kernel expression tree into an [`IoAction`]
//! tree that [`IoRuntime`] can execute with real side effects.
//!
//! # Translation rules
//!
//! After WHNF reduction, IO expressions are application spines whose head is
//! a `Const`. The bridge pattern-matches on the constant name:
//!
//! | Kernel head | IoAction |
//! |-------------|----------|
//! | `IO.pure` | `Pure(translate_value(val))` |
//! | `IO.bind` | `Bind(translate(action), ...)` |
//! | `IO.println` | `PrintLn(extract_string(msg))` |
//! | `IO.print` | `Print(extract_string(msg))` |
//! | `IO.eprintln` | `EPrintLn(extract_string(msg))` |
//! | `IO.getLine` | `GetLine` |
//! | `IO.FS.readFile` | `ReadFile(extract_string(path))` |
//! | `IO.FS.writeFile` | `WriteFile(...)` |
//! | `IO.FS.appendFile` | `AppendFile(...)` |
//! | `IO.FS.readDir` | `ReadDir(extract_string(path))` |
//! | `IO.FS.pathExists` / `System.FilePath.pathExists` | `PathExists(extract_string(path))` |
//! | `IO.FS.removeFile` | `RemoveFile(extract_string(path))` |
//! | `IO.getEnv` | `GetEnv(extract_string(name))` |
//! | `IO.currentDir` | `CurrentDir` |
//! | `IO.Process.exit` | `ProcessExit(extract_nat(code))` |
//! | `IO.monoMsNow` | `MonoMsNow` |
//! | `IO.monoNanosNow` | `MonoNanosNow` |
//!
//! Operations that [`IoRuntime`] supports but the bridge intentionally does
//! NOT wire (they cannot be translated faithfully from the kernel `Expr`
//! without machinery the bridge lacks): `IO.throw` / `IO.catch` /
//! `IO.tryCatch` (the continuation translator discards the bound error value,
//! so an error-inspecting handler cannot be reconstructed), `IO.Process.output`
//! (takes a structured `SpawnArgs` record + `Array` of args, not flat string
//! literals), and the `Task.*` operations (require turning a kernel thunk into
//! a Rust closure). Routing those here would misrepresent runtime behavior, so
//! they are deliberately left out.

use crate::error::ElabError;
use clean_kernel::expr::{ExprKind, Literal};
use clean_kernel::{Environment, Expr};
use clean_runtime::io_runtime::{IoAction, IoError, IoRuntime, IoValue};

/// Errors specific to the IO bridge translation.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum IoBridgeError {
    /// The expression head is not a recognized IO operation.
    #[error("unrecognized IO operation: {0}")]
    UnrecognizedOp(String),

    /// Expected a string literal argument but got something else.
    #[error("expected string literal, got: {0}")]
    ExpectedString(String),

    /// Expected a natural number literal argument but got something else.
    #[error("expected nat literal, got: {0}")]
    ExpectedNat(String),

    /// IO execution failed.
    #[error("IO execution error: {0}")]
    ExecutionError(#[from] IoError),
}

/// Result of evaluating an IO expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IoEvalResult {
    /// The return value of the IO computation (as a string).
    pub value: String,
    /// Lines printed to stdout during execution.
    pub stdout: Vec<String>,
    /// Lines printed to stderr during execution.
    pub stderr: Vec<String>,
}

impl std::fmt::Display for IoEvalResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for line in &self.stdout {
            writeln!(f, "{line}")?;
        }
        write!(f, "{}", self.value)
    }
}

/// Known IO operation constant names.
///
/// Used by [`is_io_typed`] for fast structural detection without type
/// inference.
pub(crate) const IO_OP_NAMES: &[&str] = &[
    "IO.pure",
    "IO.bind",
    "IO.println",
    "IO.print",
    "IO.eprintln",
    "IO.getLine",
    "IO.FS.readFile",
    "IO.FS.writeFile",
    "IO.FS.appendFile",
    "IO.FS.readDir",
    "IO.FS.pathExists",
    "System.FilePath.pathExists",
    "IO.FS.removeFile",
    "IO.getEnv",
    "IO.currentDir",
    "IO.Process.exit",
    "IO.monoMsNow",
    "IO.monoNanosNow",
    "IO.panic",
];

/// Check whether an expression has IO type via structural name matching.
///
/// Checks the head constant name against [`IO_OP_NAMES`] instead of running
/// type inference, which avoids stack overflow in deep initialization paths.
pub fn is_io_typed(_env: &Environment, expr: &Expr) -> bool {
    let head = expr.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        let name_str = name.to_string();
        IO_OP_NAMES.iter().any(|&op| name_str == op)
    } else {
        false
    }
}

/// Translate a kernel `Expr` (WHNF-reduced IO computation) into an
/// [`IoAction`] tree.
pub fn expr_to_io_action(expr: &Expr) -> Result<IoAction, IoBridgeError> {
    let head = expr.get_app_fn();
    let args = expr.get_app_args();

    match head.kind() {
        ExprKind::Const(name, _) => translate_io_const(&name.to_string(), &args),
        ExprKind::Lam(_, _, body) => expr_to_io_action(body),
        _ => Ok(IoAction::Pure(IoValue::Unit)),
    }
}

/// Dispatch a named IO constant to its corresponding [`IoAction`].
fn translate_io_const(name: &str, args: &[&Expr]) -> Result<IoAction, IoBridgeError> {
    match name {
        "IO.pure" => translate_pure(args),
        "IO.bind" => translate_bind(args),
        "IO.println" => translate_string_to_io(args, "IO.println", IoAction::PrintLn),
        "IO.print" => translate_string_to_io(args, "IO.print", IoAction::Print),
        "IO.eprintln" => translate_string_to_io(args, "IO.eprintln", IoAction::EPrintLn),
        "IO.getLine" => Ok(IoAction::GetLine),
        "IO.FS.readFile" => translate_string_to_io(args, "IO.FS.readFile", IoAction::ReadFile),
        "IO.FS.writeFile" => translate_write_file(args),
        "IO.FS.appendFile" => translate_append_file(args),
        "IO.FS.readDir" => translate_string_to_io(args, "IO.FS.readDir", IoAction::ReadDir),
        "IO.FS.pathExists" | "System.FilePath.pathExists" => {
            translate_string_to_io(args, "IO.FS.pathExists", IoAction::PathExists)
        }
        "IO.FS.removeFile" => {
            translate_string_to_io(args, "IO.FS.removeFile", IoAction::RemoveFile)
        }
        "IO.getEnv" => translate_string_to_io(args, "IO.getEnv", IoAction::GetEnv),
        "IO.currentDir" => Ok(IoAction::CurrentDir),
        "IO.Process.exit" => translate_process_exit(args),
        "IO.monoMsNow" => Ok(IoAction::MonoMsNow),
        "IO.monoNanosNow" => Ok(IoAction::MonoNanosNow),
        "IO.panic" => translate_panic(args),
        other => Err(IoBridgeError::UnrecognizedOp(other.to_owned())),
    }
}

/// Translate `IO.pure {α} val` => `Pure(val)`.
fn translate_pure(args: &[&Expr]) -> Result<IoAction, IoBridgeError> {
    if args.len() >= 2 {
        let val = expr_to_io_value(args[1])?;
        Ok(IoAction::Pure(val))
    } else {
        Ok(IoAction::Pure(IoValue::Unit))
    }
}

/// Translate `IO.bind {α} {β} action cont` => `Bind(action, cont)`.
fn translate_bind(args: &[&Expr]) -> Result<IoAction, IoBridgeError> {
    if args.len() >= 4 {
        let action = expr_to_io_action(args[2])?;
        let cont_expr = args[3].clone();
        Ok(IoAction::Bind(
            Box::new(action),
            Box::new(move |val| translate_continuation(&cont_expr, val)),
        ))
    } else {
        Err(IoBridgeError::UnrecognizedOp(format!(
            "IO.bind with {} args (need 4)",
            args.len()
        )))
    }
}

/// Translate an IO operation that takes a single string argument.
fn translate_string_to_io(
    args: &[&Expr],
    op_name: &str,
    ctor: fn(String) -> IoAction,
) -> Result<IoAction, IoBridgeError> {
    if args.is_empty() {
        return Err(IoBridgeError::ExpectedString(format!(
            "{op_name}: no arguments"
        )));
    }
    let s = extract_string(args[0])?;
    Ok(ctor(s))
}

/// Translate `IO.FS.writeFile path content`.
fn translate_write_file(args: &[&Expr]) -> Result<IoAction, IoBridgeError> {
    if args.len() < 2 {
        return Err(IoBridgeError::ExpectedString(
            "IO.FS.writeFile: need 2 arguments".into(),
        ));
    }
    let path = extract_string(args[0])?;
    let content = extract_string(args[1])?;
    Ok(IoAction::WriteFile(path, content))
}

/// Translate `IO.FS.appendFile path content`.
fn translate_append_file(args: &[&Expr]) -> Result<IoAction, IoBridgeError> {
    if args.len() < 2 {
        return Err(IoBridgeError::ExpectedString(
            "IO.FS.appendFile: need 2 arguments".into(),
        ));
    }
    let path = extract_string(args[0])?;
    let content = extract_string(args[1])?;
    Ok(IoAction::AppendFile(path, content))
}

/// Translate `IO.Process.exit code`.
fn translate_process_exit(args: &[&Expr]) -> Result<IoAction, IoBridgeError> {
    if args.is_empty() {
        return Err(IoBridgeError::ExpectedNat(
            "IO.Process.exit: no arguments".into(),
        ));
    }
    let code = extract_nat(args[0])?;
    Ok(IoAction::ProcessExit(code as i32))
}

/// Translate `IO.panic {α} msg`.
fn translate_panic(args: &[&Expr]) -> Result<IoAction, IoBridgeError> {
    let msg_idx = if args.len() >= 2 { 1 } else { 0 };
    if msg_idx < args.len() {
        let msg = extract_string(args[msg_idx])?;
        Ok(IoAction::Panic(msg))
    } else {
        Err(IoBridgeError::ExpectedString(
            "IO.panic: no message argument".into(),
        ))
    }
}

/// Translate a kernel Expr value (non-IO) to an IoValue.
fn expr_to_io_value(expr: &Expr) -> Result<IoValue, IoBridgeError> {
    match expr.kind() {
        ExprKind::Lit(Literal::String(s)) => Ok(IoValue::String(s.to_string())),
        ExprKind::Lit(Literal::Nat(n)) => Ok(IoValue::Nat(n.to_u64().unwrap_or(0))),
        ExprKind::Const(name, _) => match name.to_string().as_str() {
            "Unit.unit" | "Unit.mk" | "PUnit.unit" => Ok(IoValue::Unit),
            "Bool.true" | "True" => Ok(IoValue::Bool(true)),
            "Bool.false" | "False" => Ok(IoValue::Bool(false)),
            other => Ok(IoValue::String(other.to_owned())),
        },
        _ => Ok(IoValue::String(format!("{expr}"))),
    }
}

/// Extract a string literal from an Expr.
fn extract_string(expr: &Expr) -> Result<String, IoBridgeError> {
    match expr.kind() {
        ExprKind::Lit(Literal::String(s)) => Ok(s.to_string()),
        _ => Err(IoBridgeError::ExpectedString(format!("{expr}"))),
    }
}

/// Extract a natural number literal from an Expr.
fn extract_nat(expr: &Expr) -> Result<u64, IoBridgeError> {
    match expr.kind() {
        ExprKind::Lit(Literal::Nat(n)) => Ok(n.to_u64().unwrap_or(0)),
        _ => Err(IoBridgeError::ExpectedNat(format!("{expr}"))),
    }
}

/// Translate a continuation (lambda) applied to an IoValue.
///
/// Simplified: translates the lambda body directly without substituting the
/// bound variable. Sufficient for patterns like `fun _ => IO.println "hello"`.
fn translate_continuation(cont_expr: &Expr, _val: IoValue) -> IoAction {
    match cont_expr.kind() {
        ExprKind::Lam(_, _, body) => {
            expr_to_io_action(body).unwrap_or(IoAction::Pure(IoValue::Unit))
        }
        _ => expr_to_io_action(cont_expr).unwrap_or(IoAction::Pure(IoValue::Unit)),
    }
}

/// Format an IoValue as a display string.
fn io_value_to_string(val: &IoValue) -> String {
    match val {
        IoValue::Unit => "()".to_owned(),
        IoValue::String(s) => format!("\"{s}\""),
        IoValue::Nat(n) => n.to_string(),
        IoValue::Bool(b) => b.to_string(),
        IoValue::Int(i) => i.to_string(),
        IoValue::Pair(a, b) => {
            format!("({}, {})", io_value_to_string(a), io_value_to_string(b))
        }
        IoValue::List(items) => {
            let inner: Vec<String> = items.iter().map(io_value_to_string).collect();
            format!("[{}]", inner.join(", "))
        }
        IoValue::Task(_) => "<task>".to_owned(),
        _ => "<unknown>".to_owned(),
    }
}

/// Execute an IO-typed kernel expression through the IO runtime.
///
/// Main entry point for `#eval` of IO expressions. Translates the kernel
/// Expr to an IoAction tree, executes it, and returns captured output.
pub fn eval_io_expr(expr: &Expr) -> Result<IoEvalResult, ElabError> {
    let action = expr_to_io_action(expr).map_err(|e| ElabError::NotImplemented(e.to_string()))?;

    let rt = IoRuntime::new();
    let result = rt
        .execute(action)
        .map_err(|e| ElabError::NotImplemented(format!("IO execution failed: {e}")))?;

    Ok(IoEvalResult {
        value: io_value_to_string(&result),
        stdout: rt.stdout_output(),
        stderr: rt.stderr_output(),
    })
}

#[cfg(test)]
#[path = "io_bridge_tests.rs"]
mod tests;
