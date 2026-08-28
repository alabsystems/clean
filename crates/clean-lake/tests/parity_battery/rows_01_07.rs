// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parity battery rows 01-07: the toml/lean lakefile builds, the path and
//! git require closures, scope-only normalization, and the incremental
//! no-op rebuild. Row semantics are pinned; see `parity_battery.rs`.

use clean_lake::cli::{run_lake, LakeCommand};
use clean_lake::{BuildContext, FetchManager, LakeConfig, LakeError, Workspace};
use tempfile::TempDir;

use crate::common::*;

#[test]
fn row01_toml_lib_build_emits_olean_triple_and_round_trips() {
    let tmp = TempDir::new().expect("tempdir");
    write_file(
        &tmp.path().join("lakefile.toml"),
        "name = \"acme\"\ndefaultTargets = [\"Acme\"]\n\n[[lean_lib]]\nname = \"Acme\"\n",
    );
    write_file(
        &tmp.path().join("Acme.lean"),
        "def acmeVal : Nat := 7\ntheorem acme_eq : acmeVal = 7 := rfl\n",
    );

    let ws = Workspace::load(tmp.path()).expect("TOML workspace should load");
    let mut ctx = BuildContext::new(ws);
    let result = ctx.build_all().expect("build_all should return a result");

    // Exact outcome: the one module builds, nothing skipped, nothing failed.
    assert_eq!(sorted(result.built), vec!["Acme"], "exact built set");
    assert!(result.skipped.is_empty(), "first build skips nothing");
    assert!(result.failed.is_empty(), "no failures: {:?}", result.failed);
    assert_olean_triple(ctx.workspace(), "Acme");

    // The exported .olean is semantic, not name-only: reloading it into a
    // fresh environment restores both the definition and the theorem.
    let mut env = clean_kernel::Environment::new();
    let lib_dir = ctx.workspace().lib_dir();
    clean_olean::load_module_with_deps(&mut env, "Acme", &[lib_dir])
        .expect("built .olean should reload");
    for name in ["acmeVal", "acme_eq"] {
        let n = clean_kernel::name::Name::from_string(name);
        assert!(
            env.get_const(&n).is_some(),
            "{name} must round-trip through the exported .olean"
        );
    }
}

// ---------------------------------------------------------------------------
// Row 02 — lakefile.toml exe builds its root module; portable-run gap pinned
// ---------------------------------------------------------------------------

#[test]
fn row02_toml_exe_builds_root_module_and_portable_run_gap_is_pinned() {
    let tmp = TempDir::new().expect("tempdir");
    write_file(
        &tmp.path().join("lakefile.toml"),
        "name = \"tool\"\ndefaultTargets = [\"tool\"]\n\n\
         [[lean_exe]]\nname = \"tool\"\nroot = \"Main\"\n",
    );
    write_file(
        &tmp.path().join("Main.lean"),
        "def main : IO Unit := pure ()\n",
    );

    let ws = Workspace::load(tmp.path()).expect("TOML workspace should load");
    let mut ctx = BuildContext::new(ws);
    let result = ctx
        .build_target("tool")
        .expect("build_target should return a result");
    assert_eq!(result.built, vec!["Main"], "exe root module builds exactly");
    assert!(result.failed.is_empty(), "no failures: {:?}", result.failed);
    assert_olean_triple(ctx.workspace(), "Main");

    // GAP row (pinned, honest): two shortfalls hold today.
    //  (a) clean-lake itself emits no native executable — native emission is
    //      owned one layer up by clean-cli's `native_build` (measured
    //      2026-08-22: the unified binary emits `.lake/build/bin/tool` which
    //      runs and prints the expected stdout). Running the binary and
    //      comparing stdout therefore belongs to that layer's battery.
    //  (b) the portable `run` verb still requires `lakefile.lean`
    //      (`resolve_project_dir`), so on this TOML-only project it fails
    //      with LakefileNotFound, while the unified binary's clap path does
    //      accept TOML projects.
    // When either capability lands in this crate, this row FAILS and must be
    // UPGRADED (run the produced binary, compare stdout) — never weakened.
    let err = run_lake(&LakeCommand::Run(run_args(tmp.path(), Some("tool"))))
        .expect_err("portable run on a TOML-only project is a pinned gap");
    assert!(
        matches!(err, LakeError::LakefileNotFound(_)),
        "pinned gap error variant, got: {err:?}"
    );
}

// ---------------------------------------------------------------------------
// Row 03 — lakefile.lean lib+exe build; run reports the native gap honestly
// ---------------------------------------------------------------------------

#[test]
fn row03_lakefile_lean_lib_and_exe_build_and_run_is_honest_about_native_gap() {
    let tmp = TempDir::new().expect("tempdir");
    write_file(
        &tmp.path().join("lakefile.lean"),
        "import Lake\nopen Lake DSL\n\n\
         package parity where\n  version := \"0.1.0\"\n\n\
         lean_lib Par where\n  roots := #[`Par]\n\n\
         @[default_target]\nlean_exe parexe where\n  root := `Main\n",
    );
    write_file(&tmp.path().join("Par.lean"), "def parVal : Nat := 1\n");
    write_file(
        &tmp.path().join("Main.lean"),
        "def main : IO Unit := pure ()\n",
    );

    // The DSL lakefile is fully modeled: zero skipped-construct diagnostics,
    // and the @[default_target] attribute lands on the exe.
    let ws = Workspace::load(tmp.path()).expect("DSL workspace should load");
    assert!(
        ws.config().diagnostics.is_empty(),
        "fully-modeled lakefile must carry no diagnostics: {:?}",
        ws.config().diagnostics
    );
    assert_eq!(ws.config().default_targets, vec!["parexe"]);
    assert_eq!(ws.config().exes[0].root, "Main");

    let mut ctx = BuildContext::new(ws);
    let result = ctx.build_all().expect("build_all should return a result");
    assert_eq!(sorted(result.built), vec!["Main", "Par"], "exact built set");
    assert!(result.failed.is_empty(), "no failures: {:?}", result.failed);
    assert_olean_triple(ctx.workspace(), "Par");
    assert_olean_triple(ctx.workspace(), "Main");

    // GAP row (pinned, honest): the portable run verb selects the default
    // target, the rebuild is a no-op, and the summary REPORTS the missing
    // native artifact instead of claiming the program ran. See row 02 for the
    // ownership boundary; upgrade this row when native emission lands here.
    let msg = run_lake(&LakeCommand::Run(run_args(tmp.path(), None)))
        .expect("portable run should succeed for the default exe target");
    assert!(msg.contains("Build succeeded"), "summary: {msg}");
    assert!(msg.contains("'parexe'"), "summary names the target: {msg}");
    assert!(
        msg.contains("no native executable artifact was found"),
        "summary must report the native gap honestly: {msg}"
    );
    assert!(
        !msg.contains("Would run:"),
        "no run command may be claimed without an artifact: {msg}"
    );
}

// ---------------------------------------------------------------------------
// Row 04 — path require: cross-package rfl THROUGH the dep value
// ---------------------------------------------------------------------------

#[test]
fn row04_path_require_cross_package_rfl_through_dep_value() {
    let tmp = TempDir::new().expect("tempdir");
    let proj = tmp.path().join("proj");
    let dep = tmp.path().join("dep");

    // Dependency package, OUTSIDE the root tree so the root's module index
    // cannot see its sources except through the package mechanism.
    write_file(
        &dep.join("lakefile.toml"),
        "name = \"deppkg\"\n\n[[lean_lib]]\nname = \"DepMod\"\n",
    );
    write_file(&dep.join("DepMod.lean"), "def depVal : Nat := 3\n");

    // Root package requires it by path. The rfl proof goes THROUGH the dep
    // value, so a name-only or type-only import of DepMod cannot fake this.
    write_file(
        &proj.join("lakefile.toml"),
        "name = \"rootpkg\"\n\n\
         [[require]]\nname = \"deppkg\"\npath = \"../dep\"\n\n\
         [[lean_lib]]\nname = \"Root\"\n",
    );
    write_file(
        &proj.join("Root.lean"),
        "import DepMod\ndef rootVal : Nat := depVal\ntheorem root_eq : rootVal = 3 := rfl\n",
    );

    // Resolve the declared requires into a manifest (offline: path dep).
    let config = LakeConfig::load_from_dir(&proj).expect("root lakefile.toml loads");
    let fm = FetchManager::new(&proj, &proj.join(".lake/packages"));
    let (manifest, result) = fm
        .resolve_to_manifest(&config.package.dependencies)
        .expect("path-dep resolution should succeed");
    assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
    assert_eq!(result.resolved.len(), 1, "exactly the path dep resolves");
    assert_eq!(result.resolved[0].path.as_deref(), Some("../dep"));
    manifest
        .save(&proj.join("lake-manifest.json"))
        .expect("manifest saves");

    // Build: the dep module is discovered through the package dir, built into
    // the ROOT workspace lib dir, and the rfl through depVal kernel-verifies.
    let result = build_all(&proj);
    assert_eq!(
        sorted(result.built),
        vec!["DepMod", "Root"],
        "exact built set (dep module + root module)"
    );
    assert!(result.skipped.is_empty(), "first build skips nothing");
    assert!(
        result.failed.is_empty(),
        "the rfl THROUGH the dep value must kernel-verify: {:?}",
        result.failed
    );
    let ws = Workspace::load(&proj).expect("workspace reloads");
    assert_olean_triple(&ws, "DepMod");
    assert_olean_triple(&ws, "Root");
}

// ---------------------------------------------------------------------------
// Row 05 — git require chain A→B→C: manifest v7 pinned, closure loaded
// ---------------------------------------------------------------------------

/// The 332-family regression, mechanized end-to-end over GIT requires: with
/// single-olean dependency loading, Root's environment held BMod's constants
/// but never CMod's, so the rfl through both hops was definitionally stuck
/// while the build still reported success (a measured WRONG BUILD — see the
/// closure-loading comment in `build.rs::build_module`). This row pins the
/// fix: the transitive closure resolves into the manifest (v7, concrete SHAs,
/// inherited flags) and the value proof through BOTH hops kernel-verifies.
#[test]
fn row05_git_require_chain_pins_manifest_v7_and_loads_transitive_closure() {
    let tmp = TempDir::new().expect("tempdir");
    let remotes = tmp.path().join("remotes");

    // Leaf "remote" C (a local git repo; constraint: no network).
    let repo_c = remotes.join("depC");
    write_file(
        &repo_c.join("lakefile.toml"),
        "name = \"depC\"\n\n[[lean_lib]]\nname = \"CMod\"\n",
    );
    write_file(&repo_c.join("CMod.lean"), "def cVal : Nat := 9\n");
    git_init_commit(&repo_c);

    // "Remote" B requires C via a git URL (a local path works with git clone).
    let repo_b = remotes.join("depB");
    write_file(
        &repo_b.join("lakefile.toml"),
        &format!(
            "name = \"depB\"\n\n[[require]]\nname = \"depC\"\ngit = \"{}\"\n\n\
             [[lean_lib]]\nname = \"BMod\"\n",
            repo_c.display()
        ),
    );
    write_file(
        &repo_b.join("BMod.lean"),
        "import CMod\ndef bVal : Nat := cVal\n",
    );
    git_init_commit(&repo_b);

    // Root project at the DEFAULT layout (no `srcDir`), with fetched package
    // sources present under `.lake/packages`. This used to need
    // `srcDir = "src"` to keep the module index off those sources; the walk in
    // `Workspace::index_modules` now prunes `.lake/` itself, so the default
    // layout — which is what every real project uses — is exercised here and
    // this row pins that prune against regression.
    let proj = tmp.path().join("proj");
    write_file(
        &proj.join("lakefile.toml"),
        &format!(
            "name = \"rootpkg\"\n\n\
             [[require]]\nname = \"depB\"\ngit = \"{}\"\n\n\
             [[lean_lib]]\nname = \"Root\"\n",
            repo_b.display()
        ),
    );
    write_file(
        &proj.join("Root.lean"),
        "import BMod\ndef rootVal : Nat := bVal\ntheorem root_eq : rootVal = 9 := rfl\n",
    );

    // Resolve: the transitive closure (B AND C) lands in the manifest.
    let config = LakeConfig::load_from_dir(&proj).expect("root lakefile.toml loads");
    let fm = FetchManager::new(&proj, &proj.join(".lake/packages"));
    let (manifest, result) = fm
        .resolve_to_manifest(&config.package.dependencies)
        .expect("git-chain resolution should succeed");
    assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
    let names: Vec<&str> = result.resolved.iter().map(|p| p.name.as_str()).collect();
    assert_eq!(names, vec!["depB", "depC"], "closure lists B then C");
    assert!(!result.resolved[0].inherited, "direct dep is not inherited");
    assert!(result.resolved[1].inherited, "transitive dep is inherited");

    // Manifest v7 pinned (legacy numeric schema), concrete 40-hex SHAs.
    assert_eq!(
        manifest.version.as_numeric(),
        Some(7),
        "manifest schema version is pinned at numeric 7"
    );
    for pkg_name in ["depB", "depC"] {
        let git_pkg = manifest
            .get_package(pkg_name)
            .unwrap_or_else(|| panic!("{pkg_name} listed in manifest"))
            .as_git()
            .unwrap_or_else(|| panic!("{pkg_name} is a git package"));
        assert_eq!(git_pkg.rev.len(), 40, "{pkg_name} rev is a full SHA");
        assert!(
            git_pkg.rev.chars().all(|c| c.is_ascii_hexdigit()),
            "{pkg_name} rev is hex: {}",
            git_pkg.rev
        );
    }
    manifest
        .save(&proj.join("lake-manifest.json"))
        .expect("manifest saves");

    // Build: all three modules build, and the rfl THROUGH BOTH HOPS
    // kernel-verifies (the closure loader, not single-olean loading).
    let result = build_all(&proj);
    assert_eq!(
        sorted(result.built),
        vec!["BMod", "CMod", "Root"],
        "exact built set across the whole require chain"
    );
    assert!(
        result.failed.is_empty(),
        "the rfl through BOTH hops must kernel-verify: {:?}",
        result.failed
    );
    let ws = Workspace::load(&proj).expect("workspace reloads");
    for module in ["CMod", "BMod", "Root"] {
        assert_olean_triple(&ws, module);
    }
}

// ---------------------------------------------------------------------------
// Row 06 — scope-only (Reservoir) require normalization + two override rows
// ---------------------------------------------------------------------------

#[test]
fn row06_scope_only_require_normalizes_offline_with_pinned_overrides() {
    // Convention row: scope-only requires (the shape ALL of real Mathlib's
    // lakefile.toml dependencies use) normalize to the github.com/{scope}/
    // {name} convention with NO network access at parse time.
    let cfg = LakeConfig::parse_toml(
        "name = \"p\"\n\n[[require]]\nname = \"batteries\"\n\
         scope = \"leanprover-community\"\nrev = \"main\"\n",
    )
    .expect("scope-only require must parse");
    let d = &cfg.package.dependencies[0];
    assert_eq!(
        d.git.as_deref(),
        Some("https://github.com/leanprover-community/batteries"),
        "scope-only require derives the conventional GitHub URL"
    );
    assert_eq!(d.scope.as_deref(), Some("leanprover-community"));
    assert_eq!(d.rev.as_deref(), Some("main"));
    assert!(d.path.is_none(), "no path may be synthesized");

    // Override rows: packages whose repository name breaks the convention.
    // URLs verified against a real Mathlib lake-manifest.json (mathlib4 @
    // 43ad0e9d2e14); getting these wrong sends fetch to a nonexistent repo.
    for (name, expected_url) in [
        (
            "importGraph",
            "https://github.com/leanprover-community/import-graph",
        ),
        (
            "proofwidgets",
            "https://github.com/leanprover-community/ProofWidgets4",
        ),
    ] {
        let cfg = LakeConfig::parse_toml(&format!(
            "name = \"p\"\n\n[[require]]\nname = \"{name}\"\nscope = \"leanprover-community\"\n"
        ))
        .expect("override require must parse");
        assert_eq!(
            cfg.package.dependencies[0].git.as_deref(),
            Some(expected_url),
            "override row for {name}"
        );
    }
}

// ---------------------------------------------------------------------------
// Row 07 — incremental no-op rebuild: 0 built, N skipped
// ---------------------------------------------------------------------------

#[test]
fn row07_incremental_noop_rebuild_zero_built_all_skipped() {
    let tmp = TempDir::new().expect("tempdir");
    write_file(
        &tmp.path().join("lakefile.toml"),
        "name = \"incr\"\n\n[[lean_lib]]\nname = \"Incr\"\n",
    );
    write_file(&tmp.path().join("Incr.lean"), "def incrVal : Nat := 1\n");
    write_file(&tmp.path().join("Util.lean"), "def utilVal : Nat := 2\n");

    let first = build_all(tmp.path());
    assert_eq!(sorted(first.built), vec!["Incr", "Util"], "first build");
    assert!(first.skipped.is_empty(), "first build skips nothing");
    assert!(first.failed.is_empty(), "no failures: {:?}", first.failed);

    // Second build with a fresh context: EXACTLY 0 built, N (=2) skipped.
    let second = build_all(tmp.path());
    assert!(
        second.built.is_empty(),
        "no-op rebuild must build nothing: {:?}",
        second.built
    );
    assert_eq!(
        sorted(second.skipped),
        vec!["Incr", "Util"],
        "no-op rebuild must skip every module"
    );
    assert!(second.failed.is_empty(), "no failures: {:?}", second.failed);
}
