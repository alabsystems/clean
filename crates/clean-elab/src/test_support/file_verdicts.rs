// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Per-declaration verdicts for a Lean source fixture, driven through the
//! preprocess-then-elaborate loop `clean check` runs, with one `FileContext`
//! threaded through the whole file.
//!
//! Two properties the plain `elaborate_decl_and_register_with_warning` loop
//! does not have, and e2e fixtures need:
//!
//! - a declaration nested in a `namespace … end` / `section … end` block that
//!   FAILS is reported (as an `ElabResult::Failed` leaf of the block) — the
//!   block itself returns `Ok`, so a loop that only checks for `Err` passes
//!   over it silently;
//! - file-scoped state (`open`, the scope of a source `scoped instance`) lives
//!   in the `FileContext` and survives from one command to the next.

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::Environment;
use clean_parser::parse_file;

/// `(name, Ok | Err(rendering))` per leaf declaration, in file order, over the
/// built-in prelude.
pub(crate) fn run_file(src: &str) -> Vec<(String, Result<(), String>)> {
    let mut env = Environment::with_prelude();
    run_file_in(&mut env, src, None)
}

/// [`run_named_file`] with each error rendered as a user sees it (`Display`,
/// what `clean check` prints) instead of its `Debug` structure.
pub(crate) fn run_named_file_messages(
    src: &str,
    module: &str,
) -> Vec<(String, Result<(), String>)> {
    let mut env = Environment::with_prelude();
    run_file_rendered(&mut env, src, Some(module), Render::Message)
}

/// How a failed declaration's error is rendered into its verdict.
#[derive(Clone, Copy)]
enum Render {
    /// `{:?}`: the variant and its fields, which tests match on.
    Structure,
    /// `{}`: the message a user reads.
    Message,
}

/// [`run_file`] for a file whose driver names its module `module` (Lean's
/// main module; a `private` theorem is then `_private.<module>.0.<name>`).
pub(crate) fn run_named_file(src: &str, module: &str) -> Vec<(String, Result<(), String>)> {
    let mut env = Environment::with_prelude();
    run_file_in(&mut env, src, Some(module))
}

/// [`run_named_file`] that also hands back the environment, so a test can
/// read the kernel names a declaration registered (an inductive family, a
/// structure or a class has no verdict row of its own).
pub(crate) fn run_named_file_env(
    src: &str,
    module: &str,
) -> (Environment, Vec<(String, Result<(), String>)>) {
    let mut env = Environment::with_prelude();
    let verdicts = run_file_in(&mut env, src, Some(module));
    (env, verdicts)
}

/// [`run_named_file`] into an environment a previous module left, as a
/// driver elaborates an importer after its imports.
pub(crate) fn run_named_file_in(
    env: &mut Environment,
    src: &str,
    module: &str,
) -> Vec<(String, Result<(), String>)> {
    run_file_in(env, src, Some(module))
}

/// Elaborate `modules` one after another into ONE environment, each with a
/// fresh `FileContext` — how `clean check` elaborates a file after the source
/// modules it imports — and return the verdicts of the LAST one.
///
/// Each module is named `M0`, `M1`, … (Lean's main module, which a `private`
/// name is mangled with — G21), as `clean check` names every file it
/// elaborates.
pub(crate) fn run_modules(modules: &[&str]) -> Vec<(String, Result<(), String>)> {
    let mut env = Environment::with_prelude();
    let mut verdicts = Vec::new();
    for (idx, src) in modules.iter().enumerate() {
        verdicts = run_file_in(&mut env, src, Some(&format!("M{idx}")));
        if idx + 1 < modules.len() {
            assert_all_accepted(&verdicts, "an imported fixture module must elaborate");
        }
    }
    verdicts
}

/// [`run_modules`] with each error rendered as a user sees it (`Display`),
/// also handing back the environment, for a test that asserts both pinned
/// Lean's exact message and what a declaration's attributes left registered.
pub(crate) fn run_modules_env_messages(
    modules: &[&str],
) -> (Environment, Vec<(String, Result<(), String>)>) {
    let mut env = Environment::with_prelude();
    let mut verdicts = Vec::new();
    for (idx, src) in modules.iter().enumerate() {
        verdicts = run_file_rendered(&mut env, src, Some(&format!("M{idx}")), Render::Message);
        if idx + 1 < modules.len() {
            assert_all_accepted(&verdicts, "an imported fixture module must elaborate");
        }
    }
    (env, verdicts)
}

/// [`run_modules`] with NO module names (the regime of a driver that names
/// none, e.g. Trust's): every `private` name stays plain, and an importer is
/// kept from another module's private names only by
/// `FileContext::foreign_private_decls`, the safety net the G21 design keeps
/// for unnamed contexts. Regression tests of that filter run here.
pub(crate) fn run_modules_unnamed(modules: &[&str]) -> Vec<(String, Result<(), String>)> {
    let mut env = Environment::with_prelude();
    let mut verdicts = Vec::new();
    for (idx, src) in modules.iter().enumerate() {
        verdicts = run_file_in(&mut env, src, None);
        if idx + 1 < modules.len() {
            assert_all_accepted(&verdicts, "an imported fixture module must elaborate");
        }
    }
    verdicts
}

fn run_file_in(
    env: &mut Environment,
    src: &str,
    module: Option<&str>,
) -> Vec<(String, Result<(), String>)> {
    run_file_rendered(env, src, module, Render::Structure)
}

/// One module over the prelude, also handing back the environment and the
/// file's `FileContext` (what the file recorded across its commands), each
/// error rendered as a user sees it.
pub(crate) fn run_file_env_context(
    src: &str,
) -> (Environment, FileContext, Vec<(String, Result<(), String>)>) {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    file_ctx.set_main_module(clean_kernel::Name::from_string("M0"));
    let verdicts = run_file_with(&mut env, &mut file_ctx, src, Render::Message);
    (env, file_ctx, verdicts)
}

fn run_file_rendered(
    env: &mut Environment,
    src: &str,
    module: Option<&str>,
    render: Render,
) -> Vec<(String, Result<(), String>)> {
    let mut file_ctx = FileContext::new();
    if let Some(module) = module {
        file_ctx.set_main_module(clean_kernel::Name::from_string(module));
    }
    run_file_with(env, &mut file_ctx, src, render)
}

fn run_file_with(
    env: &mut Environment,
    file_ctx: &mut FileContext,
    src: &str,
    render: Render,
) -> Vec<(String, Result<(), String>)> {
    let show = |e: &dyn std::fmt::Display, d: &dyn std::fmt::Debug| match render {
        Render::Structure => format!("{d:?}"),
        Render::Message => format!("{e}"),
    };
    let decls = parse_file(src).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    let mut verdicts = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, file_ctx);
        match elaborate_decl_and_register_with_context(env, &processed, file_ctx) {
            Ok(result) => {
                let mut leaves = Vec::new();
                result.leaf_decls(&mut leaves);
                for leaf in leaves {
                    match leaf {
                        ElabResult::Failed { name, error, .. } => {
                            verdicts.push((name.to_string(), Err(show(error, error))));
                        }
                        ElabResult::Theorem { name, .. }
                        | ElabResult::Definition { name, .. }
                        | ElabResult::Instance { name, .. } => {
                            verdicts.push((name.to_string(), Ok(())));
                        }
                        _ => {}
                    }
                }
            }
            Err(e) => verdicts.push((
                crate::preprocess_ext::decl_name(decl)
                    .map_or_else(|| "<decl>".to_string(), ToString::to_string),
                Err(show(&e, &e)),
            )),
        }
    }
    verdicts
}

/// Panic with every failing declaration unless all of them elaborated.
pub(crate) fn assert_all_accepted(verdicts: &[(String, Result<(), String>)], why: &str) {
    let failed: Vec<_> = verdicts.iter().filter(|(_, v)| v.is_err()).collect();
    assert!(failed.is_empty(), "{why}: {failed:#?}");
}

/// The verdict of the declaration whose name ends in `name` (a namespace
/// prefix may qualify it).
pub(crate) fn verdict_of<'a>(
    verdicts: &'a [(String, Result<(), String>)],
    name: &str,
) -> &'a Result<(), String> {
    let dotted = format!(".{name}");
    &verdicts
        .iter()
        .find(|(n, _)| n == name || n.ends_with(&dotted))
        .unwrap_or_else(|| panic!("`{name}` must have a verdict; got {verdicts:?}"))
        .1
}

/// Whether a rendered error is an instance-synthesis failure (term-mode
/// `FailedToSynthesize…`, the tactic's `InstanceSynthesisFailed`, or its
/// message form).
pub(crate) fn is_synthesis_failure(err: &str) -> bool {
    [
        "FailedToSynthesize",
        "UnsynthesizedInstanceGoal",
        "InstanceSynthesisFailed",
        "could not synthesize",
    ]
    .iter()
    .any(|face| err.contains(face))
}
