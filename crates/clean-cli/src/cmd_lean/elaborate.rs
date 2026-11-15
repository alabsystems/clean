// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! One file through the module driver, observed as Lean's message log.
//!
//! The steps are the module driver's, composed as `clean check` composes them
//! (`clean_elab::module_driver`): the same environment (`module_environment`,
//! `clean check`'s default prelude), the same notation-seeded parse
//! (`parse_module`), a `FileContext` carrying the `-D` overrides and Lean's
//! main module, the same per-declaration budgets, and `elaborate_decls` — the
//! loop `clean check` and the LSP run. Only the observer is this front door's
//! ([`LeanObserver`]). Imports resolve through Lean's search path
//! ([`super::deps::search_path`]) as `lean FILE` resolves them; there is no
//! intra-project elaboration from source, which `lean` does not do either.

use super::deps::search_path;
use super::dialect::LeanDialect;
use super::locate::LineIndex;
use super::message::{LeanMessage, Pos, RenderOptions, Severity, KIND_ANONYMOUS};
use super::observer::LeanObserver;
use clean_elab::command_line_options::{apply_command_line_options, CommandLineOption};
use clean_elab::module_driver::{
    elaborate_decls, module_elaboration_lock, module_environment, parse_module, surface_decl_span,
    DeclBudgetScope, DriverOptions, EnvironmentSetup,
};
use clean_elab::FileContext;
use clean_kernel::Name;
use clean_parser::ParseError;
use std::io::Write;
use std::path::{Path, PathBuf};

/// The input of one run.
pub(crate) struct Input {
    /// The file, or `None` for `--stdin`.
    pub(crate) path: Option<PathBuf>,
    pub(crate) text: String,
    /// Lean's main module for it.
    pub(crate) main_module: Name,
}

/// Elaborate `input`, printing every message to `out` as it is logged.
/// Returns whether an error was logged (Lean's exit status 1).
///
/// # Errors
///
/// Standing up the environment failed, or writing a message did.
pub(crate) fn elaborate(
    input: &Input,
    defines: &[CommandLineOption],
    render: &RenderOptions,
    out: &mut dyn Write,
) -> anyhow::Result<bool> {
    let _lock = module_elaboration_lock();
    // `parse_module` seeds notation from the file's project-local imports,
    // which it resolves relative to the file; stdin has none.
    let seed_path = input
        .path
        .clone()
        .unwrap_or_else(|| PathBuf::from("<stdin>"));
    let (_harvest, parsed) = parse_module(&seed_path, &input.text);
    let report = match parsed {
        Ok(report) => report,
        Err(error) => {
            let message = parse_error_message(&input.text, &error, render.dialect);
            out.write_all(message.render(render).as_bytes())?;
            out.flush()?;
            return Ok(true);
        }
    };
    let mut env = if report.header.is_prelude {
        let decision = clean_olean::source_world_for_file(&seed_path, None)?;
        clean_elab::module_driver::module_environment_for_header_in_world(
            EnvironmentSetup::default(),
            &decision,
            &report.header,
        )?
        .0
    } else {
        module_environment(EnvironmentSetup::default())?
    };
    let recovery: Vec<(usize, String)> = report
        .diagnostics
        .iter()
        .map(|diag| {
            let named = match &diag.tactic {
                Some(tactic) => format!("the tactic `{tactic}`"),
                None => format!("this `{}`", diag.construct),
            };
            (
                diag.recovery_start.byte,
                format!(
                    "Clean's parser cannot read {named} here ({}): {}",
                    diag.code, diag.message
                ),
            )
        })
        .collect();

    let mut file_ctx = FileContext::new();
    file_ctx.set_file_header(&report.header);
    apply_command_line_options(&mut env, &mut file_ctx, defines);
    file_ctx.set_import_search_paths(search_path(render.dialect));
    file_ctx.set_main_module(input.main_module.clone());

    // Armed after the environment is built, as `clean check` arms them: the
    // budgets bound the file's declarations, not the prelude.
    let _budget = DeclBudgetScope::enter(clean_kernel::cli::DEFAULT_DECL_BUDGET);
    let _automation =
        crate::cmd_core::AutomationBudgetScope::enter(clean_kernel::cli::DEFAULT_AUTOMATION_BUDGET);
    let mut decl_starts: Vec<usize> = report
        .decls
        .iter()
        .filter_map(|decl| surface_decl_span(decl).map(|span| span.start))
        .collect();
    decl_starts.sort_unstable();
    let mut observer = LeanObserver::new(&input.text, render, out, recovery, decl_starts);
    elaborate_decls(
        &mut env,
        &report.decls,
        &input.text,
        &mut file_ctx,
        DriverOptions {
            lean_front_door: true,
            ..DriverOptions::default()
        },
        &mut observer,
    );
    observer.log_recovery_before(usize::MAX);
    observer.flush();
    if let Some(error) = observer.write_error.take() {
        return Err(error.into());
    }
    Ok(observer.error_logged)
}

/// A parse the parser could not recover from, as one error message.
fn parse_error_message(text: &str, error: &ParseError, dialect: LeanDialect) -> LeanMessage {
    // A module-system spelling pinned Lean refuses (plan item
    // `formats-module-spelling-refusals`) carries Lean's own position (1-based
    // line, 0-based codepoint column, `FileMap.toPosition`'s) and the words of
    // pinned 4.30.0-rc2's first message on the file. Under that dialect it
    // prints as `lean` prints that first message: at that position, with no
    // prefix. Lean prints the messages after it too (`namespace Foo` /
    // `private section` / `end Foo` has two), and this prints only the first
    // (`test_module_syntax_refusal_prints_only_the_first_message_known_gap`).
    // It used to take the arm below, at the end of the file, wrapped as
    // "Clean's parser cannot read this file: 1:7: error: …". The variant
    // carries no end position, so the end is the start (Lean's is the end of
    // the unexpected token, visible under `-DprintMessageEndPos=true` and in
    // `--json`, where Lean also sets `keepFullRange`).
    //
    // Every parse is at the v4.30.0-rc2 world, so the words are not Lean
    // 4.8.0's (measured on pinned 4.8.0: its list after `private` has no
    // `'coinductive'` and no `'syntax'`, and it reads `public import Init` as
    // "unexpected identifier; expected command"). Under 4.8.0 the message
    // keeps Clean's prefix, at the carried position.
    if let ParseError::ModuleSyntaxRefused { line, col, message } = error {
        let pos = Pos {
            line: u32::try_from(*line).unwrap_or(u32::MAX),
            column: u32::try_from(*col).unwrap_or(u32::MAX),
        };
        let text = match dialect {
            LeanDialect::V4_30_0Rc2 => message.clone(),
            LeanDialect::V4_8_0 => format!("Clean's parser cannot read this file: {error}"),
        };
        return LeanMessage {
            severity: Severity::Error,
            pos,
            end_pos: Some(pos),
            kind: KIND_ANONYMOUS,
            text,
        };
    }
    let pos = match error {
        // The line is located; the column is the parser's own coordinate,
        // which is not uniformly a column, so the line start stands in.
        ParseError::UnexpectedToken { line, .. } => {
            let index = LineIndex::new(text);
            let line_start = text
                .split_inclusive('\n')
                .take(line.saturating_sub(1))
                .map(str::len)
                .sum::<usize>();
            index.pos(line_start)
        }
        _ => LineIndex::new(text).pos(text.len()),
    };
    LeanMessage {
        severity: Severity::Error,
        pos,
        end_pos: Some(pos),
        kind: KIND_ANONYMOUS,
        text: format!("Clean's parser cannot read this file: {error}"),
    }
}

/// Lean's main module for `path`: under `-R`, the file's real path relative
/// to the root's (`_stdin` when the root does not exist or does not hold the
/// file — measured on both pinned releases, which exit 0 there, so this is no
/// error); without it, relative to the working directory
/// (`clean_elab::path_module_name`, `_stdin` outside it).
pub(crate) fn main_module(path: &Path, root: Option<&Path>) -> Name {
    let Some(root) = root else {
        return clean_elab::path_module_name(path);
    };
    let relative = root.canonicalize().ok().and_then(|real_root| {
        let real_path = path.canonicalize().ok()?;
        real_path
            .strip_prefix(&real_root)
            .ok()
            .map(|relative| relative.with_extension(""))
    });
    match relative {
        Some(relative) => relative
            .components()
            .filter_map(|component| component.as_os_str().to_str())
            .fold(Name::anon(), |name, part| name.str(part)),
        None => Name::anon().str("_stdin"),
    }
}
