// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Line-oriented REPL for `clean repl`.
//!
//! Holds a single `Environment::with_prelude()` across prompts so that
//! declarations introduced mid-session (`def`, `theorem`, …) stay visible to
//! later queries. Bare expressions are elaborated and their inferred type is
//! printed; `:`-prefixed meta-commands provide type queries, file loading,
//! environment inspection, and help. Input history is persisted under the
//! platform cache dir (`~/.cache/clean/repl_history` on Linux/macOS).
//!
//! See #3622.

use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::time::Instant;

use anyhow::Result;
use rustyline::error::ReadlineError;
use rustyline::history::FileHistory;
use rustyline::{Config, Editor};

use clean_elab::{ElabCtx, FileContext};
use clean_kernel::{Environment, TypeChecker};
use clean_parser::parse_expr;

const PROMPT: &str = "clean> ";
const BANNER: &str = "\
clean interactive REPL — expressions are elaborated and type-checked.
Type `:help` for commands, `:quit` (or Ctrl-D) to exit.";

/// Entry point: `Commands::Repl` handler.
///
/// The REPL is a human-facing interactive surface — diagnostic output goes to
/// stdout/stderr via `writeln!` (not `tracing`) so the transcript stays clean
/// and avoids the `tracing-subscriber` formatter entirely.
pub(crate) fn run() -> Result<()> {
    let mut session = Session::new();
    let mut rl = line_editor()?;

    let mut out = io::stdout().lock();
    let _ = writeln!(out, "{BANNER}");
    drop(out);

    loop {
        match rl.readline(PROMPT) {
            Ok(line) => {
                let trimmed = line.trim();
                if trimmed.is_empty() {
                    continue;
                }
                let _ = rl.add_history_entry(trimmed);
                match session.handle(trimmed) {
                    Ok(ControlFlow::Continue) => {}
                    Ok(ControlFlow::Exit) => break,
                    Err(err) => {
                        let mut err_out = io::stderr().lock();
                        let _ = writeln!(err_out, "error: {err}");
                    }
                }
            }
            Err(ReadlineError::Interrupted) => {
                // Ctrl-C: discard the current line and re-prompt.
                let mut out = io::stdout().lock();
                let _ = writeln!(out, "(interrupted — type `:quit` to exit)");
            }
            Err(ReadlineError::Eof) => break,
            Err(err) => {
                let mut err_out = io::stderr().lock();
                let _ = writeln!(err_out, "input error: {err}");
                break;
            }
        }
    }

    if let Some(path) = history_path() {
        let _ = rl.save_history(&path);
    }
    Ok(())
}

fn line_editor() -> Result<Editor<(), FileHistory>> {
    let config = Config::builder().auto_add_history(false).build();
    let mut rl: Editor<(), FileHistory> = Editor::with_config(config)?;
    if let Some(path) = history_path() {
        if let Some(parent) = path.parent() {
            let _ = std::fs::create_dir_all(parent);
        }
        let _ = rl.load_history(&path);
    }
    Ok(rl)
}

fn history_path() -> Option<PathBuf> {
    let base = std::env::var_os("XDG_CACHE_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".cache")))?;
    Some(base.join("clean").join("repl_history"))
}

enum ControlFlow {
    Continue,
    Exit,
}

/// Owns the live environment reused across prompts.
struct Session {
    env: Environment,
    file_ctx: FileContext,
}

impl Session {
    fn new() -> Self {
        Self {
            env: Environment::with_prelude(),
            file_ctx: FileContext::new(),
        }
    }

    fn handle(&mut self, line: &str) -> Result<ControlFlow> {
        if let Some(rest) = line.strip_prefix(':') {
            return self.handle_meta(rest.trim());
        }
        self.handle_expr(line)?;
        Ok(ControlFlow::Continue)
    }

    fn handle_meta(&mut self, rest: &str) -> Result<ControlFlow> {
        let (cmd, arg) = match rest.split_once(char::is_whitespace) {
            Some((c, a)) => (c, a.trim()),
            None => (rest, ""),
        };
        match cmd {
            "q" | "quit" | "exit" => Ok(ControlFlow::Exit),
            "help" | "h" | "?" => {
                print_help();
                Ok(ControlFlow::Continue)
            }
            "type" | "t" => {
                if arg.is_empty() {
                    anyhow::bail!(":type requires an expression (e.g. `:type Nat.add`)");
                }
                self.handle_expr(arg)?;
                Ok(ControlFlow::Continue)
            }
            "load" | "l" => {
                if arg.is_empty() {
                    anyhow::bail!(":load requires a file path");
                }
                self.load_file(arg)?;
                Ok(ControlFlow::Continue)
            }
            "env" | "e" => {
                self.print_env(arg);
                Ok(ControlFlow::Continue)
            }
            other => anyhow::bail!("unknown command `:{other}` — try `:help`"),
        }
    }

    fn handle_expr(&self, src: &str) -> Result<()> {
        let start = Instant::now();
        let surface = parse_expr(src)?;
        let mut ctx = ElabCtx::new(&self.env);
        let kernel_expr = ctx.elaborate(&surface)?;
        let tc = TypeChecker::with_mode(&self.env, self.env.mode());
        let ty = tc.infer_type(&kernel_expr)?;
        let elapsed = start.elapsed();
        let mut out = io::stdout().lock();
        let _ = writeln!(out, "{src} : {ty:?}");
        let _ = writeln!(out, "  ({elapsed:?})");
        Ok(())
    }

    fn load_file(&mut self, path_str: &str) -> Result<()> {
        let path = Path::new(path_str);
        if !path.exists() {
            anyhow::bail!("file not found: {}", path.display());
        }
        let content = std::fs::read_to_string(path)?;
        let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
        let decls = clean_parser::parse_file_with_tactics(&content, &patterns)?;
        let mut registered = 0usize;
        let mut failed = 0usize;
        for decl in &decls {
            let processed = clean_elab::preprocess_decl_with_context(decl, &mut self.file_ctx);
            // Thread `file_ctx` so standalone `open`/`export` aliases persist
            // across the loaded file's declarations (gap sweep B13).
            match clean_elab::elaborate_decl_and_register_with_context_and_warning(
                &mut self.env,
                &processed,
                &mut self.file_ctx,
            ) {
                Ok(_) => registered += 1,
                Err(e) => {
                    failed += 1;
                    let mut err_out = io::stderr().lock();
                    let _ = writeln!(err_out, "  ✗ {e:?}");
                }
            }
        }
        let mut out = io::stdout().lock();
        let _ = writeln!(
            out,
            "loaded {}: {registered} registered, {failed} failed ({} declarations seen)",
            path.display(),
            decls.len()
        );
        Ok(())
    }

    fn print_env(&self, filter: &str) {
        let mut names: Vec<String> = self
            .env
            .constants()
            .map(|c| c.name.to_string())
            .filter(|n| filter.is_empty() || n.contains(filter))
            .collect();
        names.sort();
        let shown = names.len().min(50);
        let mut out = io::stdout().lock();
        for name in names.iter().take(shown) {
            let _ = writeln!(out, "  {name}");
        }
        if names.len() > shown {
            let _ = writeln!(
                out,
                "  … ({} more; pass a substring to :env to filter)",
                names.len() - shown
            );
        }
        if names.is_empty() && !filter.is_empty() {
            let _ = writeln!(out, "  (no constants match `{filter}`)");
        }
    }
}

fn print_help() {
    let mut out = io::stdout().lock();
    let _ = writeln!(
        out,
        "\
clean REPL commands:
  <expr>            elaborate and print inferred type
  :type <expr>      same as bare expression (alias: :t)
  :load <file>      elaborate declarations from <file> into the session env (alias: :l)
  :env [substr]     list registered constants (optionally filtered by substring)
  :help             show this help (alias: :h, :?)
  :quit             exit (alias: :q, :exit, Ctrl-D)

Expressions are evaluated against a persistent `Environment::with_prelude()`;
declarations introduced via `:load` remain visible to later queries."
    );
}
