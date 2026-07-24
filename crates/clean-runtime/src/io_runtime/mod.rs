// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! IO execution layer for clean.
//!
//! Interprets an `IoAction` tree representing Lean 4 IO monadic computations
//! and executes real side effects (print, file I/O, environment access, process
//! control, timers).
//!
//! Lean 4 models IO as a state-passing monad (`IO α ≈ RealWorld → (α × RealWorld)`).
//! At runtime the monad is unrolled into an action tree (`Pure`, `Bind`, `PrintLn`,
//! `GetLine`, `ReadFile`, `WriteFile`, `GetEnv`, `Panic`, etc.) that `IoRuntime`
//! interprets via an iterative trampoline to avoid stack overflow.
//!
//! # Architecture
//!
//! The module is split by concern:
//! - `console` — stdout/stderr/stdin operations
//! - `file` — filesystem operations (read, write, readDir, pathExists)
//! - `process` — subprocess spawn/output/exit
//! - `env` — environment variable and working directory access
//! - `timer` — monotonic clock access

mod console;
mod env;
mod file;
mod process;
pub(crate) mod task_io;
mod timer;

#[cfg(test)]
mod tests_core;
#[cfg(test)]
mod tests_file_process;
#[cfg(test)]
mod tests_task_io;

use std::cell::RefCell;

/// Represents a value produced or consumed by IO actions.
///
/// This is a simplified value domain sufficient for basic IO operations.
/// A future slice will bridge to the kernel's `Expr` type.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum IoValue {
    /// The unit value (Lean `()`).
    Unit,
    /// A string value.
    String(String),
    /// A natural number value.
    Nat(u64),
    /// A boolean value.
    Bool(bool),
    /// An integer value (for exit codes, file sizes, etc.).
    Int(i64),
    /// A pair of values (Lean `Prod`).
    Pair(Box<IoValue>, Box<IoValue>),
    /// A list of values (Lean `List` / `Array`).
    List(Vec<IoValue>),
    /// A task handle wrapping a concurrent computation (`Task α`).
    Task(task_io::IoTaskHandle),
}

/// An executable IO action tree.
///
/// Represents the monadic structure of a Lean 4 IO computation before
/// execution. `Bind` nodes carry boxed closures so continuations can
/// capture arbitrary intermediate state.
#[non_exhaustive]
pub enum IoAction {
    // -- Core monad operations --
    /// Return a pure value without side effects (`IO.pure`).
    Pure(IoValue),
    /// Sequence: execute the first action, feed its result to the continuation (`IO.bind`).
    Bind(Box<IoAction>, Box<dyn FnOnce(IoValue) -> IoAction>),
    /// Transform the result of an action (`IO.map`).
    Map(Box<IoAction>, Box<dyn FnOnce(IoValue) -> IoValue>),

    // -- Error handling --
    /// Throw an error value (`IO.throw`).
    Throw(IoValue),
    /// Catch errors: try the first action, on error run the handler (`IO.catch`).
    Catch(Box<IoAction>, Box<dyn FnOnce(IoValue) -> IoAction>),

    // -- Console I/O --
    /// Print a line to stdout (appends newline) (`IO.println`).
    PrintLn(String),
    /// Print a string to stdout (no newline) (`IO.print`).
    Print(String),
    /// Print a line to stderr (appends newline) (`IO.eprintln`).
    EPrintLn(String),
    /// Read a line from stdin (`IO.getLine`).
    GetLine,

    // -- File I/O --
    /// Read the entire contents of a file (`IO.FS.readFile`).
    ReadFile(String),
    /// Write contents to a file (creates or truncates) (`IO.FS.writeFile`).
    WriteFile(String, String),
    /// Append contents to a file (`IO.FS.appendFile`).
    AppendFile(String, String),
    /// List directory entries (`IO.FS.readDir`).
    ReadDir(String),
    /// Check whether a path exists (`IO.FS.pathExists`).
    PathExists(String),
    /// Remove a file (`IO.FS.removeFile`).
    RemoveFile(String),

    // -- Environment --
    /// Read an environment variable (returns empty string if unset) (`IO.getEnv`).
    GetEnv(String),
    /// Get the current working directory (`IO.currentDir`).
    CurrentDir,

    // -- Process --
    /// Run a process and capture its output (`IO.Process.output`).
    ProcessOutput {
        /// Program to execute.
        cmd: String,
        /// Arguments.
        args: Vec<String>,
    },
    /// Exit the process with a code (`IO.Process.exit`).
    ProcessExit(i32),

    // -- Timers --
    /// Get monotonic time in milliseconds (`IO.monoMsNow`).
    MonoMsNow,
    /// Get monotonic time in nanoseconds (`IO.monoNanosNow`).
    MonoNanosNow,

    // -- Task parallelism --
    /// Spawn a thunk on the thread pool, returning a task handle (`Task.spawn`).
    /// The boxed closure receives `Unit` and returns the computed `IoValue`.
    TaskSpawn(Box<dyn FnOnce() -> IoValue + Send>),
    /// Block until the task completes and return its result (`Task.get`).
    TaskGet(task_io::IoTaskHandle),
    /// Monadic bind on a task: when `task` completes, apply `f` (`Task.bind`).
    TaskBind(
        task_io::IoTaskHandle,
        Box<dyn FnOnce(IoValue) -> IoValue + Send>,
    ),
    /// Functor map on a task: transform the result without blocking (`Task.map`).
    TaskMap(
        task_io::IoTaskHandle,
        Box<dyn FnOnce(IoValue) -> IoValue + Send>,
    ),
    /// Create an already-completed task holding a value (`Task.pure`).
    TaskPure(IoValue),
    /// Convert an IO action into a task (`BaseIO.asTask`).
    AsTask(Box<IoAction>),

    // -- Control --
    /// Abort execution with an error message (Lean `panic`).
    Panic(String),
}

/// Errors that can occur during IO action execution.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum IoError {
    /// An IO action called `Panic`.
    #[error("IO.panic: {0}")]
    Panic(String),

    /// An IO action called `Throw` with an error value.
    #[error("IO.throw: {0:?}")]
    Thrown(IoValue),

    /// A file system operation failed.
    #[error("IO file error on `{path}`: {source}")]
    FileError {
        /// The path involved in the failed operation.
        path: String,
        /// The underlying OS error.
        source: std::io::Error,
    },

    /// Reading from stdin failed.
    #[error("IO stdin error: {0}")]
    StdinError(std::io::Error),

    /// An environment variable lookup failed with an OS error.
    #[error("IO env error for `{name}`: {source}")]
    EnvError {
        /// The variable name.
        name: String,
        /// The underlying error.
        source: std::env::VarError,
    },

    /// Getting the current directory failed.
    #[error("IO currentDir error: {0}")]
    CurrentDirError(std::io::Error),

    /// A process operation failed.
    #[error("IO process error for `{cmd}`: {source}")]
    ProcessError {
        /// The command that failed.
        cmd: String,
        /// The underlying OS error.
        source: std::io::Error,
    },

    /// Process exited with non-zero status.
    #[error("IO process `{cmd}` exited with code {code}")]
    ProcessFailed {
        /// The command that failed.
        cmd: String,
        /// The exit code.
        code: i32,
        /// Captured stdout.
        stdout: String,
        /// Captured stderr.
        stderr: String,
    },

    /// Process exit requested.
    #[error("IO.Process.exit({0})")]
    ProcessExit(i32),

    /// A spawned task panicked or failed.
    #[error("Task failed: {0}")]
    TaskFailed(String),
}

/// Runtime interpreter for IO action trees.
///
/// Captures stdout/stderr output into internal buffers so callers (and tests)
/// can inspect what was printed without actually writing to the process
/// stdout/stderr. Stdin reads delegate to a pluggable reader, defaulting to
/// real stdin.
pub struct IoRuntime {
    /// Captured stdout lines.
    stdout_buf: RefCell<Vec<String>>,
    /// Captured stderr lines.
    stderr_buf: RefCell<Vec<String>>,
    /// Pluggable stdin source (one line per entry, consumed in order).
    stdin_lines: RefCell<Vec<String>>,
}

impl IoRuntime {
    /// Create a new runtime with no pre-loaded stdin.
    #[must_use]
    pub fn new() -> Self {
        Self {
            stdout_buf: RefCell::new(Vec::new()),
            stderr_buf: RefCell::new(Vec::new()),
            stdin_lines: RefCell::new(Vec::new()),
        }
    }

    /// Create a runtime with pre-loaded stdin lines (for testing).
    ///
    /// Lines are consumed in FIFO order by `GetLine` actions.
    #[must_use]
    pub fn with_stdin(lines: Vec<String>) -> Self {
        Self {
            stdout_buf: RefCell::new(Vec::new()),
            stderr_buf: RefCell::new(Vec::new()),
            stdin_lines: RefCell::new(lines),
        }
    }

    /// Return all captured stdout lines.
    pub fn stdout_output(&self) -> Vec<String> {
        self.stdout_buf.borrow().clone()
    }

    /// Return all captured stderr lines.
    pub fn stderr_output(&self) -> Vec<String> {
        self.stderr_buf.borrow().clone()
    }

    /// Execute an IO action tree, returning the final value or an error.
    ///
    /// This is an iterative trampoline: `Bind` chains are flattened into
    /// a loop rather than recursing, so deeply nested monadic chains
    /// cannot overflow the stack.
    pub fn execute(&self, action: IoAction) -> Result<IoValue, IoError> {
        let mut current = action;
        loop {
            match current {
                IoAction::Pure(v) => return Ok(v),
                IoAction::Bind(first, cont) => {
                    let v = self.execute_leaf(*first)?;
                    current = cont(v);
                }
                IoAction::Map(inner, f) => {
                    let v = self.execute(*inner)?;
                    return Ok(f(v));
                }
                IoAction::Catch(try_action, handler) => match self.execute(*try_action) {
                    Ok(v) => return Ok(v),
                    Err(IoError::Thrown(err_val)) => {
                        current = handler(err_val);
                    }
                    Err(e) => return Err(e),
                },
                leaf => return self.execute_leaf(leaf),
            }
        }
    }

    /// Execute a single non-compound action.
    fn execute_leaf(&self, action: IoAction) -> Result<IoValue, IoError> {
        match action {
            IoAction::Pure(v) => Ok(v),
            IoAction::Bind(first, cont) => {
                let v = self.execute(*first)?;
                self.execute(cont(v))
            }
            IoAction::Map(inner, f) => {
                let v = self.execute(*inner)?;
                Ok(f(v))
            }
            IoAction::Catch(try_action, handler) => match self.execute(*try_action) {
                Ok(v) => Ok(v),
                Err(IoError::Thrown(err_val)) => self.execute(handler(err_val)),
                Err(e) => Err(e),
            },

            // Console
            IoAction::PrintLn(s) => self.exec_println(&s),
            IoAction::Print(s) => self.exec_print(&s),
            IoAction::EPrintLn(s) => self.exec_eprintln(&s),
            IoAction::GetLine => self.exec_getline(),

            // File
            IoAction::ReadFile(path) => self.exec_read_file(&path),
            IoAction::WriteFile(path, content) => self.exec_write_file(&path, &content),
            IoAction::AppendFile(path, content) => self.exec_append_file(&path, &content),
            IoAction::ReadDir(path) => self.exec_read_dir(&path),
            IoAction::PathExists(path) => self.exec_path_exists(&path),
            IoAction::RemoveFile(path) => self.exec_remove_file(&path),

            // Environment
            IoAction::GetEnv(name) => self.exec_get_env(&name),
            IoAction::CurrentDir => self.exec_current_dir(),

            // Process
            IoAction::ProcessOutput { cmd, args } => self.exec_process_output(&cmd, &args),
            IoAction::ProcessExit(code) => Err(IoError::ProcessExit(code)),

            // Timers
            IoAction::MonoMsNow => self.exec_mono_ms_now(),
            IoAction::MonoNanosNow => self.exec_mono_nanos_now(),

            // Task parallelism
            IoAction::TaskSpawn(thunk) => task_io::exec_task_spawn(thunk),
            IoAction::TaskGet(handle) => task_io::exec_task_get(&handle),
            IoAction::TaskBind(handle, f) => task_io::exec_task_bind(&handle, f),
            IoAction::TaskMap(handle, f) => task_io::exec_task_map(&handle, f),
            IoAction::TaskPure(val) => Ok(IoValue::Task(task_io::IoTaskHandle::from_value(val))),
            IoAction::AsTask(action) => task_io::exec_as_task(*action, self),

            // Error handling
            IoAction::Throw(v) => Err(IoError::Thrown(v)),
            IoAction::Panic(msg) => Err(IoError::Panic(msg)),
        }
    }
}

impl Default for IoRuntime {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Convenience constructors for building IO action trees
// ---------------------------------------------------------------------------

/// Build a `Bind` chain: `first >>= cont`.
#[must_use]
pub fn io_bind(first: IoAction, cont: impl FnOnce(IoValue) -> IoAction + 'static) -> IoAction {
    IoAction::Bind(Box::new(first), Box::new(cont))
}

/// Build a `Map` chain: `f <$> action`.
#[must_use]
pub fn io_map(action: IoAction, f: impl FnOnce(IoValue) -> IoValue + 'static) -> IoAction {
    IoAction::Map(Box::new(action), Box::new(f))
}

/// Build a `Catch` block: try `action`, on `Throw` run `handler`.
#[must_use]
pub fn io_catch(action: IoAction, handler: impl FnOnce(IoValue) -> IoAction + 'static) -> IoAction {
    IoAction::Catch(Box::new(action), Box::new(handler))
}

/// Sequence two actions, discarding the first result: `first >> second`.
#[must_use]
pub fn io_seq(first: IoAction, second: IoAction) -> IoAction {
    IoAction::Bind(Box::new(first), Box::new(move |_| second))
}

/// Spawn a thunk as a concurrent task (`Task.spawn`).
#[must_use]
pub fn io_task_spawn(thunk: impl FnOnce() -> IoValue + Send + 'static) -> IoAction {
    IoAction::TaskSpawn(Box::new(thunk))
}

/// Convert an IO action into a task (`BaseIO.asTask`).
#[must_use]
pub fn io_as_task(action: IoAction) -> IoAction {
    IoAction::AsTask(Box::new(action))
}
