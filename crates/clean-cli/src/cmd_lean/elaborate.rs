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
use super::olean_output;
use clean_elab::command_line_options::{apply_command_line_options, CommandLineOption};
use clean_elab::module_driver::{
    elaborate_decls, module_elaboration_lock, module_environment,
    module_environment_and_context_with_import_paths, module_environment_for_header_in_world,
    parse_module, preload_exported_term_syntax, stable_environment_with_imported_syntax,
    surface_decl_span, DeclBudgetScope, DriverOptions, EnvironmentSetup, ImportHandling,
};
use clean_elab::FileContext;
use clean_kernel::Name;
use clean_native::native_build::{emit_checked_native_c_artifact_in_context, NativeCArtifact};
use clean_olean::SourceWorldDecision;
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
    /// The exact world selected by the command line, when required by its dialect.
    pub(crate) source_world: Option<SourceWorldDecision>,
    /// Compile the entry from the same checked environment for stable `--run`.
    pub(crate) native_main: bool,
    /// Native Lean output from this same checked source environment.
    pub(crate) olean_output: Option<PathBuf>,
}

pub(crate) enum Elaboration {
    Failed,
    Checked,
    Native(NativeCArtifact),
}

/// Elaborate `input`, printing every message to `out` as it is logged.
///
/// # Errors
///
/// Environment setup, message output or native code generation failed.
pub(crate) fn elaborate(
    input: &Input,
    defines: &[CommandLineOption],
    render: &RenderOptions,
    out: &mut dyn Write,
) -> anyhow::Result<Elaboration> {
    let _lock = module_elaboration_lock();
    // Preserve project-source notation for the two older front doors. The
    // stable front door reads imports from compiled artifacts.
    let seed_path = input
        .path
        .clone()
        .unwrap_or_else(|| PathBuf::from("<stdin>"));
    let setup = EnvironmentSetup::default();
    let paths = search_path(render.dialect, input.source_world.as_ref());
    let mut fixed_setup = None;
    let mut imports_preloaded = false;
    let mut checked_prelude = None;
    let parsed = if let Some(decision) = &input.source_world {
        let (header, header_decls) = match clean_parser::Parser::parse_header_with_decls_in_world(
            &input.text,
            decision.world(),
        ) {
            Ok(header) => header,
            Err(error) => return report_parse_error(&input.text, &error, render, out),
        };
        let (env, file_ctx, prefixes) = if !header.is_prelude && (input.native_main || !header.imports.is_empty()) {
            imports_preloaded = true;
            stable_environment_with_imported_syntax(
                decision,
                &header,
                paths.clone(),
                input.main_module.clone(),
                &input.text,
                input.native_main,
            )?
        } else {
            let (mut env, mut context) = module_environment_and_context_with_import_paths(
                setup,
                decision,
                &header,
                paths.clone(),
            )?;
            context.set_main_module(input.main_module.clone());
            context.set_file_header(&header);
            let mut prefixes = clean_parser::ImportedTermPrefixes::default();
            if input.native_main && !header.imports.is_empty() {
                let Some(clean_parser::SurfaceDecl::Prelude { span }) = header_decls.first() else {
                    anyhow::bail!("explicit prelude has no parsed header declaration")
                };
                clean_elab::module_driver::elaborate_prelude_header(
                    &mut env,
                    &header_decls,
                    &mut context,
                )?;
                checked_prelude = Some(*span);
                prefixes = preload_exported_term_syntax(
                    &mut env,
                    &mut context,
                    &header,
                    &input.text,
                    input.native_main,
                )?;
                imports_preloaded = true;
            }
            (env, context, prefixes)
        };
        fixed_setup = Some((env, file_ctx));
        clean_parser::parse_file_seeded_in_world_with_imported_terms(
            &input.text,
            &clean_elab::tactic::builtins::builtin_tactic_patterns(),
            &clean_parser::NotationSeed::default(),
            decision.world(),
            &prefixes,
        )
    } else {
        parse_module(&seed_path, &input.text).1
    };
    let report = match parsed {
        Ok(report) => report,
        Err(error) => return report_parse_error(&input.text, &error, render, out),
    };
    let (mut env, mut file_ctx) = if let Some(fixed) = fixed_setup {
        fixed
    } else {
        let env = if report.header.is_prelude {
            let decision = clean_olean::source_world_for_file(&seed_path, None)?;
            module_environment_for_header_in_world(setup, &decision, &report.header)?.0
        } else {
            module_environment(setup)?
        };
        let mut file_ctx = FileContext::new();
        file_ctx.set_documentation_world(render.dialect.world());
        file_ctx.set_import_search_paths(paths);
        (env, file_ctx)
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

    file_ctx.set_file_header(&report.header);
    apply_command_line_options(&mut env, &mut file_ctx, defines);
    file_ctx.set_main_module(input.main_module.clone());
    if input.native_main && !imports_preloaded {
        let implicit_imports = if report.header.is_prelude {
            Vec::new()
        } else {
            vec![Name::from_string("Init")]
        };
        for module in &implicit_imports {
            file_ctx.record_compiler_import(module);
        }
        clean_kernel::env::csimp::begin_source_module(
            &mut env,
            input.main_module.clone(),
            implicit_imports,
        );
    }

    let mut decl_starts: Vec<usize> = report
        .decls
        .iter()
        .filter_map(|decl| surface_decl_span(decl).map(|span| span.start))
        .collect();
    decl_starts.sort_unstable();
    let mut observer = LeanObserver::new(
        &input.text,
        render,
        out,
        recovery,
        decl_starts,
        input.native_main,
    );
    if input.olean_output.is_some() {
        env.set_kernel_theory(clean_kernel::env::KernelTheory::LeanReference);
        if let Some(decl) = report.decls.iter().find(|decl| {
            !matches!(
                decl,
                clean_parser::SurfaceDecl::Import { .. }
                    | clean_parser::SurfaceDecl::Prelude { .. }
            )
        }) {
            clean_elab::prepare_declaration_environment(&mut env, decl);
        }
        observer.capture_export(&report.decls);
    }
    {
        let _budget = DeclBudgetScope::enter(clean_kernel::cli::DEFAULT_DECL_BUDGET);
        let _automation = crate::cmd_core::AutomationBudgetScope::enter(
            clean_kernel::cli::DEFAULT_AUTOMATION_BUDGET,
        );
        let declarations = if let Some(early_span) = checked_prelude {
            let Some((clean_parser::SurfaceDecl::Prelude { span }, body)) =
                report.decls.split_first()
            else {
                anyhow::bail!("native artifact loading requires the same parsed prelude")
            };
            anyhow::ensure!(*span == early_span, "the parsed prelude span changed");
            body
        } else {
            &report.decls
        };
        elaborate_decls(
            &mut env,
            declarations,
            &input.text,
            &mut file_ctx,
            DriverOptions {
                imports: if imports_preloaded {
                    ImportHandling::Preloaded
                } else {
                    ImportHandling::Elaborate
                },
                lean_front_door: true,
                ..DriverOptions::default()
            },
            &mut observer,
        );
    }
    observer.log_recovery_before(usize::MAX);
    observer.flush();
    if let Some(error) = observer.write_error.take() {
        return Err(error.into());
    }
    if observer.error_logged {
        return Ok(Elaboration::Failed);
    }
    if let Some(path) = &input.olean_output {
        anyhow::ensure!(
            !report.has_doc_comments,
            "Lean 4.36 native output cannot serialize source documentation comments"
        );
        let decision = input.source_world.as_ref().ok_or_else(|| {
            anyhow::anyhow!("Lean artifact output requires a stable source world")
        })?;
        let target = olean_output::stable_header(decision)?;
        let source = observer
            .export_source
            .take()
            .ok_or_else(|| anyhow::anyhow!("module driver has no checked artifact capture"))??;
        let parts = source.export(&env, &report.header, &target, &input.main_module)?;
        olean_output::publish(path, parts)?;
    }
    let Some(source) = observer.native_source.take().transpose()? else {
        return Ok(Elaboration::Checked);
    };
    let main = Name::interned("main");
    if env.is_noncomputable(&main)
        || env.is_macro_inline(&main)
        || env.get_const(&main).is_none_or(|info| {
            clean_compiler::main_signature::MainSignature::from_type(&info.type_).is_none()
                || (info.value.is_none()
                    && env.get_extern(&main).is_none()
                    && !env.has_implemented_by(&main))
        })
    {
        eprintln!("(interpreter) unknown declaration 'main'");
        return Ok(Elaboration::Failed);
    }
    emit_checked_native_c_artifact_in_context(&seed_path, "main", &env, &source, Some(&file_ctx), 0)
        .map(Elaboration::Native)
}

fn report_parse_error(
    text: &str,
    error: &ParseError,
    render: &RenderOptions,
    out: &mut dyn Write,
) -> anyhow::Result<Elaboration> {
    let message = parse_error_message(text, error, render.dialect);
    out.write_all(message.render(render).as_bytes())?;
    out.flush()?;
    Ok(Elaboration::Failed)
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
    // The legacy parse defaults to the v4.30.0-rc2 world, so the words are not Lean
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
            LeanDialect::V4_30_0Rc2 | LeanDialect::V4_36_0 => message.clone(),
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
