// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Script listing, execution, and documentation.

use crate::cmd_core::resolve_project_dir;
use std::path::PathBuf;

/// Module name used for the synthetic `def main` module generated from a script
/// body before native execution. Prefixed to avoid colliding with project modules.
const SYNTHETIC_SCRIPT_MODULE_PREFIX: &str = "CleanLakeScript_";

/// Lower a parsed lakefile script body into a `main : IO Unit` Lean module.
///
/// Lakefile script bodies are stored as the trimmed lines of the `script` block
/// joined by newlines (indentation is dropped during parsing). To hand the body
/// to the native `main : IO Unit` execution bridge we wrap it in a `def main`.
/// A leading `do` keeps its sequenced statements indented underneath it so the
/// re-emitted module is valid Lean; a single-expression body is inlined.
fn synthesize_script_main_module(body: &str) -> String {
    let trimmed = body.trim();
    if trimmed.is_empty() {
        return "def main : IO Unit := pure ()\n".to_string();
    }

    let mut lines = trimmed.lines();
    let first = lines.next().unwrap_or("").trim();
    if first == "do" {
        let mut module = String::from("def main : IO Unit := do\n");
        for line in lines {
            let line = line.trim();
            if line.is_empty() {
                continue;
            }
            module.push_str("  ");
            module.push_str(line);
            module.push('\n');
        }
        return module;
    }

    // Single-expression (or already-inlined) body: emit it on the def line and
    // append any trailing lines indented as a continuation.
    let mut module = format!("def main : IO Unit := {first}\n");
    for line in lines {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        module.push_str("  ");
        module.push_str(line);
        module.push('\n');
    }
    module
}

/// List scripts defined in lakefile.lean
pub(super) fn lake_script_list(dir: Option<PathBuf>) -> anyhow::Result<()> {
    let cwd = resolve_project_dir(dir)?;
    let config = super::load_project_config(&cwd)?;

    if config.scripts.is_empty() {
        println!("No scripts defined in lakefile.lean.");
        println!("Define scripts using `script <name> := ...` or `script <name> where ...`");
        return Ok(());
    }

    println!("Available scripts:");
    for script in &config.scripts {
        if let Some(ref doc) = script.doc {
            println!("  {} - {}", script.name, doc);
        } else {
            println!("  {}", script.name);
        }
    }

    Ok(())
}

/// Run a script defined in lakefile.lean.
///
/// Lakefile scripts are Lean `IO` bodies. Rather than display the body (the prior
/// placeholder behavior), clean lowers the script body into a synthetic
/// `def main : IO Unit` module and executes it through the same native build/run
/// bridge used by `clean lake run`/`clean lake exe`. Trailing `args` are forwarded
/// to the executed script and the child exit code is preserved by the caller via
/// [`crate::cmd_lake::native_executable_exit_code`].
///
/// The native bridge supports the bounded stdout IO subset (`IO.print`,
/// `IO.println`, do-sequencing); script bodies that need unsupported runtime
/// surfaces fail closed with the same diagnostics as the executable path rather
/// than silently delegating to an external `lean --run`.
pub(super) fn lake_script_run(
    name: &str,
    args: &[String],
    dir: Option<PathBuf>,
) -> anyhow::Result<()> {
    use clean_lake::{LeanExe, Workspace};

    let cwd = resolve_project_dir(dir)?;
    let config = super::load_project_config(&cwd)?;

    let script = config
        .scripts
        .iter()
        .find(|s| s.name == name)
        .ok_or_else(|| {
            anyhow::anyhow!(
                "Script '{name}' not found in lakefile.lean.\n\
                 Use 'clean lake script list' to see available scripts."
            )
        })?;

    // Lower the script body into a synthetic `main : IO Unit` module placed in the
    // package source directory so the workspace module resolver can find it.
    let module_stem = format!(
        "{SYNTHETIC_SCRIPT_MODULE_PREFIX}{}",
        sanitize_module_stem(name)
    );
    let module_source = synthesize_script_main_module(&script.body);

    let ws = Workspace::from_config(&cwd, config.clone());
    let src_dir = ws.src_dir();
    std::fs::create_dir_all(&src_dir).map_err(|err| {
        anyhow::anyhow!(
            "could not create source directory {} for synthetic script module: {err}",
            src_dir.display()
        )
    })?;
    let module_path = src_dir.join(format!("{module_stem}.lean"));
    std::fs::write(&module_path, &module_source).map_err(|err| {
        anyhow::anyhow!(
            "could not write synthetic script module {}: {err}",
            module_path.display()
        )
    })?;

    let exe = LeanExe {
        name: module_stem.clone(),
        root: module_stem,
        src_dir: config.package.src_dir.clone(),
        ..Default::default()
    };

    let result = super::run::build_and_run_synthetic_executable(&ws, &exe, args, false);

    // Always remove the synthetic module source regardless of run outcome.
    let _ = std::fs::remove_file(&module_path);

    result.map_err(|err| {
        if super::native_executable_exit_code(&err).is_some() {
            return err;
        }
        anyhow::anyhow!(
            "clean lake script run is fail-closed for script '{name}': clean lowered the script \
             body into a synthetic `main : IO Unit` module but could not build and execute it \
             through the native bridge. The native bridge currently supports the bounded stdout \
             IO subset (IO.print/IO.println and do-sequencing). Refusing to delegate to external \
             `lean --run`.\nNative blocker: {err:#}"
        )
    })
}

/// Reduce a script name to a Lean-module-identifier-safe stem.
///
/// Non-alphanumeric characters become underscores so arbitrary script names map
/// to a single valid module component for the synthetic `def main` module.
fn sanitize_module_stem(name: &str) -> String {
    let stem: String = name
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect();
    if stem.is_empty() {
        "script".to_string()
    } else {
        stem
    }
}

/// Show documentation for a script
pub(super) fn lake_script_doc(name: &str, dir: Option<PathBuf>) -> anyhow::Result<()> {
    let cwd = resolve_project_dir(dir)?;
    let config = super::load_project_config(&cwd)?;

    let script = config
        .scripts
        .iter()
        .find(|s| s.name == name)
        .ok_or_else(|| {
            anyhow::anyhow!(
                "Script '{name}' not found in lakefile.lean.\n\
                 Use 'clean lake script list' to see available scripts."
            )
        })?;

    println!("Script: {}", script.name);
    if let Some(ref doc) = script.doc {
        println!("Documentation: {doc}");
    } else {
        println!("No documentation available.");
    }
    println!();
    println!("Body:");
    println!("{}", script.body);

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn write_script_project(lakefile_body: &str) -> tempfile::TempDir {
        let dir = tempfile::tempdir().expect("tempdir");
        std::fs::write(dir.path().join("lakefile.lean"), lakefile_body).expect("write lakefile");
        dir
    }

    #[test]
    fn test_synthesize_script_main_module_single_expression_inlines_body() {
        let module = synthesize_script_main_module("IO.println \"hello\"");
        assert_eq!(module, "def main : IO Unit := IO.println \"hello\"\n");
    }

    #[test]
    fn test_synthesize_script_main_module_do_block_reindents_statements() {
        let module = synthesize_script_main_module("do\nIO.print \"hi\"\nIO.println \" there\"");
        assert_eq!(
            module,
            "def main : IO Unit := do\n  IO.print \"hi\"\n  IO.println \" there\"\n"
        );
    }

    #[test]
    fn test_synthesize_script_main_module_empty_body_is_pure_unit() {
        assert_eq!(
            synthesize_script_main_module("   "),
            "def main : IO Unit := pure ()\n"
        );
    }

    #[test]
    fn test_sanitize_module_stem_replaces_non_alphanumeric_with_underscore() {
        assert_eq!(sanitize_module_stem("build-docs.v2"), "build_docs_v2");
    }

    #[test]
    fn test_sanitize_module_stem_non_alphanumeric_maps_to_underscores() {
        assert_eq!(sanitize_module_stem("---"), "___");
    }

    #[test]
    fn test_sanitize_module_stem_empty_falls_back_to_script() {
        assert_eq!(sanitize_module_stem(""), "script");
    }

    #[test]
    fn test_lake_script_run_missing_lakefile_errors_cleanly() {
        let dir = tempfile::tempdir().expect("tempdir");
        let err = lake_script_run("hello", &[], Some(dir.path().to_path_buf()))
            .expect_err("script run should fail when no lakefile exists");
        let msg = format!("{err:#}");
        assert!(
            msg.contains("No lakefile.toml or lakefile.lean found"),
            "diagnostic should name the missing lakefile (both flavors): {msg}"
        );
    }

    #[test]
    fn test_lake_script_run_unknown_script_errors_cleanly() {
        let dir = write_script_project(
            "import Lake\nopen Lake DSL\n\npackage demo\n\nscript hello where\n  IO.println \"hi\"\n",
        );
        let err = lake_script_run("does_not_exist", &[], Some(dir.path().to_path_buf()))
            .expect_err("script run should reject an unknown script name");
        let msg = format!("{err:#}");
        assert!(
            msg.contains("does_not_exist"),
            "diagnostic should name the requested script: {msg}"
        );
        assert!(
            msg.contains("not found in lakefile.lean"),
            "diagnostic should explain the script was not found: {msg}"
        );
        assert!(
            msg.contains("clean lake script list"),
            "diagnostic should suggest listing available scripts: {msg}"
        );
    }

    #[test]
    fn test_lake_script_run_removes_synthetic_module_after_run() {
        // An unknown script must not leave any synthetic module behind, and a
        // resolved-but-unbuildable script must clean up too. Use a body the
        // native bridge can lower so the synthetic module is created then removed.
        let dir = write_script_project(
            "import Lake\nopen Lake DSL\n\npackage demo\n\nscript hello where\n  IO.println \"clean script\"\n",
        );

        let _ = lake_script_run("hello", &[], Some(dir.path().to_path_buf()));

        let synthetic = dir.path().join("CleanLakeScript_hello.lean");
        assert!(
            !synthetic.exists(),
            "synthetic script module should be removed after run at {}",
            synthetic.display()
        );
    }

    #[cfg(unix)]
    #[test]
    fn test_lake_script_run_executes_resolved_script_through_native_bridge() {
        let dir = write_script_project(
            "import Lake\nopen Lake DSL\n\npackage demo\n\nscript greet where\n  IO.println \"script executed\"\n",
        );

        lake_script_run("greet", &[], Some(dir.path().to_path_buf())).expect(
            "resolved IO.println script should build and execute through the native bridge",
        );

        let artifact = dir.path().join(".lake/build/bin/CleanLakeScript_greet");
        assert!(
            artifact.exists(),
            "script run should leave a native executable artifact at {}",
            artifact.display()
        );

        let output = std::process::Command::new(&artifact)
            .output()
            .expect("linked script artifact should execute");
        assert!(
            output.status.success(),
            "linked script artifact should exit successfully: {output:?}"
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            "script executed\n",
            "linked script artifact should print the script payload"
        );
    }

    #[cfg(unix)]
    #[test]
    fn test_lake_script_run_forwards_passthrough_args_to_executed_script() {
        use std::os::unix::fs::PermissionsExt;

        let dir = write_script_project(
            "import Lake\nopen Lake DSL\n\npackage demo\n\nscript echo_args where\n  IO.println \"ignored\"\n",
        );

        // Pre-place a native artifact at the synthetic exe path so the native
        // build short-circuits and our script records its received argv. This
        // proves trailing args reach the spawned script process.
        let marker = dir.path().join("argv.txt");
        let artifact = dir.path().join(".lake/build/bin/CleanLakeScript_echo_args");
        std::fs::create_dir_all(artifact.parent().expect("bin parent")).expect("create bin dir");
        std::fs::write(
            &artifact,
            format!("#!/bin/sh\nprintf '%s' \"$*\" > {}\n", marker.display()),
        )
        .expect("write argv-recording artifact");
        let mut perms = std::fs::metadata(&artifact)
            .expect("artifact metadata")
            .permissions();
        perms.set_mode(0o755);
        std::fs::set_permissions(&artifact, perms).expect("chmod artifact");

        // Stage the synthetic module + a matching freshness sidecar so the
        // freshness gate (#42) reuses the pre-placed argv-recording artifact
        // instead of rebuilding it. `lake_script_run` rewrites this module with
        // identical (deterministic) content before building, so the digest holds.
        let module_stem = format!(
            "{SYNTHETIC_SCRIPT_MODULE_PREFIX}{}",
            sanitize_module_stem("echo_args")
        );
        let config = super::super::load_project_config(dir.path()).expect("load config");
        let ws = clean_lake::Workspace::from_config(dir.path(), config.clone());
        let src_dir = ws.src_dir();
        std::fs::create_dir_all(&src_dir).expect("create synthetic src dir");
        std::fs::write(
            src_dir.join(format!("{module_stem}.lean")),
            synthesize_script_main_module("  IO.println \"ignored\"\n"),
        )
        .expect("pre-stage synthetic module for sidecar digest");
        super::super::build::write_fresh_source_closure_sidecar_for_test(
            &ws,
            &module_stem,
            &module_stem,
        );

        lake_script_run(
            "echo_args",
            &["alpha".to_string(), "beta".to_string()],
            Some(dir.path().to_path_buf()),
        )
        .expect("script run should forward passthrough args and succeed");

        assert_eq!(
            std::fs::read_to_string(&marker).expect("argv marker should be written"),
            "alpha beta",
            "passthrough args should reach the executed script process argv"
        );
    }
}
