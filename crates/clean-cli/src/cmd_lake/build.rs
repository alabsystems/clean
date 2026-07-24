// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Project creation, initialization, building, and cleaning.

use crate::cmd_core::resolve_project_dir;
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

/// Build a Lake project
pub(super) fn lake_build(
    target: Option<String>,
    verbose: bool,
    force: bool,
    jobs: usize,
    dir: Option<PathBuf>,
) -> anyhow::Result<()> {
    use clean_lake::{BuildContext, BuildOptions, Workspace};

    let cwd = resolve_project_dir(dir)?;

    // Load the project's lakefile (lakefile.toml preferred, lakefile.lean fallback)
    let config = super::load_project_config(&cwd)?;
    let pkg_name = config.package.name.clone();

    if verbose {
        println!("Building package: {pkg_name}");
    }

    // Create workspace
    let ws = Workspace::from_config(&cwd, config);

    // Build options
    let options = BuildOptions::new()
        .with_jobs(jobs)
        .with_verbose(verbose)
        .with_force(force);

    // Create build context and build
    let mut ctx = BuildContext::new(ws).with_options(options);

    let requested_target = target.as_deref();
    let result = if let Some(target_name) = requested_target {
        ctx.build_target(target_name)?
    } else {
        ctx.build_all()?
    };

    // Report results
    if verbose || !result.is_success() {
        println!("Build completed in {:.2}s", result.duration.as_secs_f64());
        println!(
            "  {} built, {} skipped, {} failed",
            result.built.len(),
            result.skipped.len(),
            result.failed.len()
        );
    }

    if !result.failed.is_empty() {
        println!("\nBuild errors:");
        for (module, error) in &result.failed {
            println!("  {module}: {error}");
        }
        std::process::exit(1);
    }

    ensure_native_artifacts_for_executable_targets(ctx.workspace(), requested_target)?;

    if result.built.is_empty() && result.skipped.is_empty() {
        println!("Nothing to build.");
    } else if !verbose {
        println!(
            "Build OK ({} modules, {:.2}s)",
            result.built.len() + result.skipped.len(),
            result.duration.as_secs_f64()
        );
    }

    Ok(())
}

pub(super) fn ensure_native_artifacts_for_executable_targets(
    workspace: &clean_lake::Workspace,
    target: Option<&str>,
) -> anyhow::Result<()> {
    let exes: Vec<_> = match target {
        Some(target) => workspace
            .config()
            .exes
            .iter()
            .filter(|exe| exe.name == target)
            .collect(),
        None => workspace.config().exes.iter().collect(),
    };

    for exe in exes {
        ensure_native_artifact_for_executable(workspace, exe)?;
    }

    Ok(())
}

pub(super) fn ensure_native_artifact_for_executable(
    workspace: &clean_lake::Workspace,
    exe: &clean_lake::LeanExe,
) -> anyhow::Result<PathBuf> {
    // Compute the transitive local-.lean source closure once: it gates both the
    // freshness decision below and the sidecar digest we persist after a rebuild.
    let closure = executable_source_closure(workspace, exe)?;
    let digest = source_closure_digest(&closure);
    let sidecar = native_executable_srchash_path(workspace, &exe.name);

    // Reuse the existing binary ONLY if it is present AND fresh against the
    // current source closure. `native_executable_path` answers "where is it";
    // the sidecar digest answers "is it usable". Fail-closed: any missing /
    // mismatched sidecar (or unreadable binary) falls through to a rebuild.
    if let Some(path) = super::run::native_executable_path(workspace, &exe.name) {
        if native_artifact_is_fresh(&sidecar, &digest) {
            return Ok(path);
        }
    }

    let root_path = workspace
        .find_module(&exe.root)
        .ok_or_else(|| anyhow::anyhow!("Root module '{}' not found", exe.root))?;
    let output = super::run::native_executable_build_path(workspace, &exe.name);
    let source_artifact = executable_c_source_artifact_path(workspace, &exe.name);

    // Reuse the shared native-build engine (the same emit + render + cc-link path
    // `clean run` uses) so the Lake surface inherits the full NAT/BOOL/TYPECLASS/IO
    // shim coverage and the embedded clean_runtime materialization. This builds the
    // root module's `main` into a native binary written to `output`, and persists
    // the rendered C translation unit to `source_artifact` for inspection.
    crate::native_build::build_native_executable_with_source_sink(
        &root_path,
        "main",
        0,
        &output,
        Some(&source_artifact),
    )
    .map_err(|err| {
        anyhow::anyhow!(
            "{}\nNative link boundary: {err:#}",
            missing_native_artifact_message(workspace, exe, Some(&source_artifact))
        )
    })?;

    // Persist the source-closure digest the binary was built against. A future
    // `clean lake build`/`run` reuses this binary iff the recomputed digest
    // matches. Best-effort: if the sidecar cannot be written the next run simply
    // sees a missing sidecar and rebuilds (fail-closed, correct-but-slower).
    write_source_closure_sidecar(&sidecar, &digest);

    Ok(output)
}

/// Path to the per-executable source-closure digest sidecar that records what
/// source the native binary was last built against (`.lake/build/bin/<exe>.srchash`).
fn native_executable_srchash_path(workspace: &clean_lake::Workspace, exe_name: &str) -> PathBuf {
    let mut path = super::run::native_executable_build_path(workspace, exe_name);
    let file_name = path
        .file_name()
        .map(|name| format!("{}.srchash", name.to_string_lossy()))
        .unwrap_or_else(|| format!("{exe_name}.srchash"));
    path.set_file_name(file_name);
    path
}

/// Enumerate the transitive intra-project `.lean` source closure for an
/// executable target: the root module plus every locally-resolvable module it
/// (transitively) imports. External / Mathlib / Init imports resolve to `None`
/// via [`clean_elab::resolve_intra_project_import`] and are skipped, so the walk
/// stays bounded inside the project (matching how elaboration bounds the closure).
///
/// A visited set guards against import cycles. The result is sorted (BTreeSet)
/// so the downstream digest is deterministic across runs.
fn executable_source_closure(
    workspace: &clean_lake::Workspace,
    exe: &clean_lake::LeanExe,
) -> anyhow::Result<Vec<PathBuf>> {
    let root_path = workspace
        .find_module(&exe.root)
        .ok_or_else(|| anyhow::anyhow!("Root module '{}' not found", exe.root))?;

    let mut visited: BTreeSet<PathBuf> = BTreeSet::new();
    let mut stack = vec![root_path];

    while let Some(path) = stack.pop() {
        let canonical = std::fs::canonicalize(&path).unwrap_or(path);
        if !visited.insert(canonical.clone()) {
            continue;
        }
        // Unreadable file: keep it in the closure (its absence/identity still
        // participates in the digest) but it contributes no further imports.
        let Ok(source) = std::fs::read_to_string(&canonical) else {
            continue;
        };
        for module in import_modules(&source) {
            if let Some(resolved) = clean_elab::resolve_intra_project_import(&module, &canonical) {
                stack.push(resolved);
            }
        }
    }

    Ok(visited.into_iter().collect())
}

/// Parse `import <Module>` lines from a Lean source file, mirroring the parser
/// used elsewhere in the CLI: strip line comments, stop at the first non-import
/// declaration, and tolerate attribute lines before the import block.
fn import_modules(text: &str) -> Vec<String> {
    let mut imports = Vec::new();
    for line in text.lines() {
        let line = line.split("--").next().unwrap_or("").trim();
        let Some(rest) = line.strip_prefix("import ") else {
            if !line.is_empty() && !line.starts_with("@[") {
                break;
            }
            continue;
        };
        imports.extend(
            rest.split_whitespace()
                .map(|part| {
                    part.trim_matches(|ch: char| {
                        !(ch.is_ascii_alphanumeric() || ch == '_' || ch == '.')
                    })
                })
                .filter(|part| !part.is_empty())
                .map(ToOwned::to_owned),
        );
    }
    imports
}

/// Content-hash the source closure into a stable hex digest. blake3 (already a
/// workspace dep of clean-cli) is used over mtime so the decision is robust to
/// checkout/clone moves and clock skew (per the CLAUDE.md artifact-mobility
/// note). Paths are hashed in sorted order (BTreeSet upstream) for determinism;
/// each file's bytes are hashed, and a length-prefix delimits entries so two
/// distinct closures cannot collide by concatenation.
fn source_closure_digest(closure: &[PathBuf]) -> String {
    let mut hasher = blake3::Hasher::new();
    for path in closure {
        let bytes = std::fs::read(path).unwrap_or_default();
        hasher.update(&(bytes.len() as u64).to_le_bytes());
        hasher.update(&bytes);
    }
    hasher.finalize().to_hex().to_string()
}

/// Freshness predicate: the binary is reusable iff the sidecar exists and its
/// recorded digest equals the freshly-computed closure digest. Any read failure
/// or mismatch is treated as stale (fail-closed → rebuild).
fn native_artifact_is_fresh(sidecar: &Path, digest: &str) -> bool {
    std::fs::read_to_string(sidecar)
        .map(|recorded| recorded.trim() == digest)
        .unwrap_or(false)
}

/// Write the digest sidecar next to the binary, creating the bin dir if needed.
/// Best-effort: failures are non-fatal (next run rebuilds).
fn write_source_closure_sidecar(sidecar: &Path, digest: &str) {
    if let Some(parent) = sidecar.parent() {
        let _ = std::fs::create_dir_all(parent);
    }
    let _ = std::fs::write(sidecar, digest);
}

/// Test-only helper: stage a freshness sidecar matching the current source
/// closure for `exe_name` rooted at `root`, so a pre-written native artifact is
/// treated as fresh and reused (rather than rebuilt) by the freshness gate.
#[cfg(test)]
pub(super) fn write_fresh_source_closure_sidecar_for_test(
    workspace: &clean_lake::Workspace,
    exe_name: &str,
    root: &str,
) {
    let exe = clean_lake::LeanExe {
        name: exe_name.to_string(),
        root: root.to_string(),
        ..Default::default()
    };
    if let Ok(closure) = executable_source_closure(workspace, &exe) {
        let digest = source_closure_digest(&closure);
        write_source_closure_sidecar(
            &native_executable_srchash_path(workspace, exe_name),
            &digest,
        );
    }
}

fn executable_c_source_artifact_path(workspace: &clean_lake::Workspace, exe_name: &str) -> PathBuf {
    workspace
        .build_dir()
        .join("native")
        .join("c")
        .join(format!("{exe_name}.c"))
}

fn missing_native_artifact_message(
    workspace: &clean_lake::Workspace,
    exe: &clean_lake::LeanExe,
    source_artifact: Option<&Path>,
) -> String {
    let expected = super::run::native_executable_build_path(workspace, &exe.name);
    let root_path = workspace.find_module(&exe.root).map_or_else(
        || format!("root module `{}`", exe.root),
        |path| path.display().to_string(),
    );
    let source_note = source_artifact.map_or_else(
        || "clean has not emitted a native source artifact for this target.".to_string(),
        |path| format!("clean emitted C source for `main` at {}.", path.display()),
    );

    format!(
        "clean lake build built Lean module artifacts for executable target '{}', \
         but no native executable was produced at {}. \
         {} \
         clean cannot yet link that source into .lake/build/bin without the \
         compile/runtime link bridge. To use the current native handoff without Lean4, \
         produce a clean-owned executable at that exact path for root {}. \
         Note: `clean compile {} --decl main --emit c|rust` currently emits source only; \
         it does not link the native artifact.",
        exe.name,
        expected.display(),
        source_note,
        root_path,
        root_path
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_lake::{LakeConfig, LeanExe, PackageConfig, Workspace};

    fn executable_workspace() -> (tempfile::TempDir, Workspace) {
        let dir = tempfile::tempdir().expect("tempdir");
        std::fs::write(
            dir.path().join("Main.lean"),
            "def main : IO Unit := pure ()\n",
        )
        .expect("write root module");
        let mut config = LakeConfig::default();
        config.package = PackageConfig::minimal("native_build_surface");
        config.exes.push(LeanExe {
            name: "native_build_surface".to_string(),
            root: "Main".to_string(),
            ..Default::default()
        });
        let ws = Workspace::from_config(dir.path(), config);
        (dir, ws)
    }

    #[test]
    fn missing_native_artifact_message_names_handoff_path_and_compile_limit() {
        let (_dir, ws) = executable_workspace();
        let exe = &ws.config().exes[0];
        let msg = missing_native_artifact_message(&ws, exe, None);

        assert!(
            msg.contains(".lake/build/bin/native_build_surface"),
            "diagnostic should name exact native handoff path: {msg}"
        );
        assert!(
            msg.contains("compile/runtime link bridge"),
            "diagnostic should name the missing native link bridge: {msg}"
        );
        assert!(
            msg.contains("clean compile"),
            "diagnostic should explain the current compile surface: {msg}"
        );
        assert!(
            msg.contains("emits source only"),
            "diagnostic should avoid implying compile already links an executable: {msg}"
        );
    }

    #[test]
    fn missing_native_artifact_message_names_c_source_when_emitted() {
        let (_dir, ws) = executable_workspace();
        let exe = &ws.config().exes[0];
        let source = executable_c_source_artifact_path(&ws, &exe.name);
        let msg = missing_native_artifact_message(&ws, exe, Some(&source));

        assert!(
            msg.contains(".lake/build/native/c/native_build_surface.c"),
            "diagnostic should name emitted C source artifact: {msg}"
        );
        assert!(
            msg.contains("compile/runtime link bridge"),
            "diagnostic should still name the missing linker: {msg}"
        );
    }

    /// The shared native-build engine synthesizes a host `int main(void)` into
    /// the persisted C source artifact and links the executable at the expected
    /// `.lake/build/bin/<name>` path. This exercises the engine end-to-end from a
    /// real Lean root module (not a pre-written C stub) and proves the Lake path
    /// produces both the persisted source and the binary.
    #[test]
    fn ensure_native_artifact_synthesizes_host_main_and_links() {
        let (_dir, ws) = executable_workspace();
        let exe = &ws.config().exes[0];

        let linked = ensure_native_artifact_for_executable(&ws, exe)
            .expect("native artifact engine should synthesize main and link");
        let source = executable_c_source_artifact_path(&ws, &exe.name);
        let wrapped_source = std::fs::read_to_string(&source).expect("read persisted C source");

        assert!(
            wrapped_source.contains("int main(void)"),
            "persisted C source should contain the synthesized host main: {wrapped_source}"
        );
        assert!(
            linked.ends_with(".lake/build/bin/native_build_surface"),
            "link step should produce expected native artifact path: {}",
            linked.display()
        );
        assert!(linked.exists(), "linked executable should exist");
    }

    #[test]
    fn executable_build_surface_accepts_existing_fresh_native_artifact() {
        let (_dir, ws) = executable_workspace();
        let exe = &ws.config().exes[0];
        let path = super::super::run::native_executable_build_path(&ws, "native_build_surface");
        std::fs::create_dir_all(path.parent().expect("bin dir")).expect("create bin dir");
        std::fs::write(&path, "").expect("write native artifact");

        // A fresh sidecar matching the current source closure must short-circuit
        // the rebuild: the existing (empty) artifact is reused verbatim, with no
        // cc invocation. This is the happy-path reuse the freshness gate protects.
        let closure = executable_source_closure(&ws, exe).expect("closure");
        let digest = source_closure_digest(&closure);
        write_source_closure_sidecar(
            &native_executable_srchash_path(&ws, "native_build_surface"),
            &digest,
        );

        ensure_native_artifacts_for_executable_targets(&ws, Some("native_build_surface"))
            .expect("existing fresh native artifact should satisfy executable build surface");

        // Empty (0-byte) artifact proves no rebuild happened (a rebuild would link
        // a real binary). Reuse, not relink.
        assert_eq!(
            std::fs::metadata(&path).expect("artifact metadata").len(),
            0,
            "fresh existing artifact should be reused verbatim, not rebuilt"
        );
    }

    fn cc_available() -> bool {
        let cc = std::env::var("CLEAN_CC")
            .ok()
            .filter(|v| !v.trim().is_empty())
            .or_else(|| std::env::var("CC").ok().filter(|v| !v.trim().is_empty()))
            .unwrap_or_else(|| "cc".to_string());
        std::process::Command::new(cc)
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
    }

    /// Freshness gate: an existing binary with no sidecar must be rebuilt
    /// rather than trusted merely because it occupies the handoff path.
    #[test]
    fn executable_build_surface_rebuilds_when_sidecar_is_missing() {
        if !cc_available() {
            eprintln!("skipping executable_build_surface_rebuilds_when_sidecar_is_missing: no cc");
            return;
        }
        let (_dir, ws) = executable_workspace();
        let path = super::super::run::native_executable_build_path(&ws, "native_build_surface");
        std::fs::create_dir_all(path.parent().expect("bin dir")).expect("create bin dir");
        std::fs::write(&path, "").expect("write empty untrusted native artifact");

        ensure_native_artifacts_for_executable_targets(&ws, Some("native_build_surface"))
            .expect("missing sidecar should trigger a rebuild that links a real binary");

        assert!(
            std::fs::metadata(&path).expect("artifact metadata").len() > 0,
            "artifact without a sidecar should be rebuilt into a real binary"
        );
    }

    /// Freshness gate: an existing binary with a tampered sidecar (digest does
    /// not match the current source closure) must be rebuilt rather than reused.
    #[test]
    fn executable_build_surface_rebuilds_when_sidecar_is_tampered() {
        if !cc_available() {
            eprintln!("skipping executable_build_surface_rebuilds_when_sidecar_is_tampered: no cc");
            return;
        }
        let (_dir, ws) = executable_workspace();
        let path = super::super::run::native_executable_build_path(&ws, "native_build_surface");
        std::fs::create_dir_all(path.parent().expect("bin dir")).expect("create bin dir");
        std::fs::write(&path, "").expect("write empty stale native artifact");
        // Record a digest that cannot match the real closure.
        write_source_closure_sidecar(
            &native_executable_srchash_path(&ws, "native_build_surface"),
            "stale-digest",
        );

        ensure_native_artifacts_for_executable_targets(&ws, Some("native_build_surface"))
            .expect("stale sidecar should trigger a rebuild that links a real binary");

        assert!(
            std::fs::metadata(&path).expect("artifact metadata").len() > 0,
            "stale artifact should have been rebuilt into a real (non-empty) binary"
        );
    }

    #[test]
    fn executable_build_surface_links_trivial_native_artifact() {
        let (_dir, ws) = executable_workspace();
        ensure_native_artifacts_for_executable_targets(&ws, Some("native_build_surface"))
            .expect("trivial executable should compile and link a native artifact");
        let artifact = super::super::run::native_executable_build_path(&ws, "native_build_surface");
        let source = executable_c_source_artifact_path(&ws, "native_build_surface");
        let emitted_source = std::fs::read_to_string(source).expect("read emitted source");

        assert!(
            artifact.exists(),
            "build surface should produce native executable at {}",
            artifact.display()
        );
        assert!(
            emitted_source.contains("int main(void)"),
            "emitted C source should include generated host main wrapper: {emitted_source}"
        );
    }
}

/// Create a new Lake project
pub(super) fn lake_new(name: &str, _lib: bool, exe: bool) -> anyhow::Result<()> {
    use std::fs;

    let project_dir = PathBuf::from(name);

    // Extract project name from path (last component)
    let project_name = project_dir
        .file_name()
        .and_then(|n| n.to_str())
        .ok_or_else(|| anyhow::anyhow!("Invalid project name: {name}"))?;

    // Check if directory already exists
    if project_dir.exists() {
        anyhow::bail!("Directory '{name}' already exists");
    }

    // Create project structure
    fs::create_dir_all(&project_dir)?;
    fs::create_dir_all(project_dir.join(".lake"))?;

    // Generate lakefile.lean
    let lakefile_content = if exe {
        format!(
            r#"import Lake
open Lake DSL

package {project_name} where
  version := "0.1.0"

@[default_target]
lean_exe {project_name} where
  root := `Main
"#
        )
    } else {
        format!(
            r#"import Lake
open Lake DSL

package {project_name} where
  version := "0.1.0"

@[default_target]
lean_lib {project_name} where
  roots := #[`{project_name}]
"#
        )
    };

    fs::write(project_dir.join("lakefile.lean"), lakefile_content)?;

    // Generate initial source file
    let src_dir = project_dir.join(project_name);
    fs::create_dir_all(&src_dir)?;

    if exe {
        // Create Main.lean for executable
        fs::write(
            project_dir.join("Main.lean"),
            r#"def main : IO Unit :=
  IO.println "Hello, world!"
"#,
        )?;
    } else {
        // Create lib root file
        fs::write(
            src_dir.join("Basic.lean"),
            format!(
                r#"-- {project_name}/Basic.lean
-- Main library file

def hello := "world"
"#
            ),
        )?;

        // Create lib root that imports Basic
        fs::write(
            project_dir.join(format!("{project_name}.lean")),
            format!(
                r"import {project_name}.Basic
"
            ),
        )?;
    }

    // Generate lake-manifest.json
    let manifest = r#"{
  "version": 7,
  "packagesDir": ".lake/packages",
  "packages": []
}
"#;
    fs::write(project_dir.join("lake-manifest.json"), manifest)?;

    // Generate .gitignore
    let gitignore = r"/.lake/
*.olean
*.ilean
";
    fs::write(project_dir.join(".gitignore"), gitignore)?;

    println!("Created new Lean project '{project_name}'");
    println!("  lakefile.lean");
    if exe {
        println!("  Main.lean");
    } else {
        println!("  {project_name}.lean");
        println!("  {project_name}/Basic.lean");
    }
    println!("  lake-manifest.json");
    println!("  .gitignore");
    println!("\nTo build:");
    println!("  cd {name}");
    println!("  clean lake build");

    Ok(())
}

/// clean build artifacts
pub(super) fn lake_clean(verbose: bool, dir: Option<PathBuf>) -> anyhow::Result<()> {
    use clean_lake::{BuildContext, Workspace};

    let cwd = resolve_project_dir(dir)?;

    // Best-effort: a missing lakefile (toml or lean) falls through to the bare
    // .lake cleanup below; a malformed lakefile still surfaces as an error.
    let Some(config) = super::try_load_project_config(&cwd)? else {
        // Just clean .lake directory if no lakefile
        let lake_dir = cwd.join(".lake");
        if lake_dir.exists() {
            if verbose {
                println!("Removing .lake directory");
            }
            std::fs::remove_dir_all(&lake_dir)?;
            println!("cleaned build artifacts.");
        } else {
            println!("Nothing to clean.");
        }
        return Ok(());
    };

    // Create workspace from the loaded lakefile
    let ws = Workspace::from_config(&cwd, config);
    let ctx = BuildContext::new(ws);

    if verbose {
        println!(
            "cleaning build directory: {:?}",
            ctx.workspace().build_dir()
        );
    }

    ctx.clean()?;
    println!("cleaned build artifacts.");

    Ok(())
}

/// Initialize lake in current directory
pub(super) fn lake_init(name: Option<String>, dir: Option<PathBuf>) -> anyhow::Result<()> {
    use std::fs;

    let cwd = resolve_project_dir(dir)?;

    // Check if a lakefile already exists (either flavor) so init does not clobber
    // an existing project. clean lake init authors a lakefile.lean template, but a
    // pre-existing lakefile.toml is just as much a project root and must be respected.
    if cwd.join("lakefile.lean").exists() {
        anyhow::bail!("lakefile.lean already exists in current directory");
    }
    if cwd.join("lakefile.toml").exists() {
        anyhow::bail!("lakefile.toml already exists in current directory");
    }

    // Get project name from argument or directory name
    let project_name = name.unwrap_or_else(|| {
        cwd.file_name()
            .and_then(|n| n.to_str())
            .unwrap_or("project")
            .to_string()
    });
    let package_name = lean_identifier_from_project_name(&project_name, CaseStyle::Snake);
    let module_name = lean_identifier_from_project_name(&project_name, CaseStyle::Pascal);
    let test_name = format!("{package_name}_test");

    // Create .lake directory
    fs::create_dir_all(cwd.join(".lake"))?;

    // Generate lakefile.lean
    let lakefile_content = format!(
        r#"import Lake
open Lake DSL

package {package_name} where
  version := "0.1.0"

@[default_target]
lean_lib {module_name} where
  roots := #[`{module_name}]

lean_test {test_name} where
  root := `Test
"#
    );

    fs::write(cwd.join("lakefile.lean"), lakefile_content)?;
    fs::write(
        cwd.join(format!("{module_name}.lean")),
        format!("-- {module_name}: auto-generated by clean lake init\n\ndef hello := \"world\"\n"),
    )?;
    fs::write(cwd.join("Test.lean"), "def main : IO Unit := pure ()\n")?;

    // Generate lake-manifest.json
    let manifest = r#"{
  "version": 7,
  "packagesDir": ".lake/packages",
  "packages": []
}
"#;
    fs::write(cwd.join("lake-manifest.json"), manifest)?;

    println!("Initialized Lean project '{project_name}'");
    println!("  lakefile.lean");
    println!("  {module_name}.lean");
    println!("  Test.lean");
    println!("  lake-manifest.json");

    Ok(())
}

#[derive(Clone, Copy)]
enum CaseStyle {
    Snake,
    Pascal,
}

fn lean_identifier_from_project_name(name: &str, style: CaseStyle) -> String {
    let words: Vec<String> = name
        .split(|c: char| !c.is_ascii_alphanumeric())
        .filter(|part| !part.is_empty())
        .map(|part| part.to_ascii_lowercase())
        .collect();
    let words = if words.is_empty() {
        vec!["project".to_string()]
    } else {
        words
    };

    let mut ident = match style {
        CaseStyle::Snake => words.join("_"),
        CaseStyle::Pascal => words
            .iter()
            .map(|word| {
                let mut chars = word.chars();
                match chars.next() {
                    Some(first) => {
                        let mut out = first.to_ascii_uppercase().to_string();
                        out.push_str(chars.as_str());
                        out
                    }
                    None => String::new(),
                }
            })
            .collect(),
    };

    if ident
        .chars()
        .next()
        .is_none_or(|first| !first.is_ascii_alphabetic())
    {
        ident.insert_str(
            0,
            match style {
                CaseStyle::Snake => "project_",
                CaseStyle::Pascal => "Project",
            },
        );
    }
    ident
}
