// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the `lakefile.toml` model: template parsing, require
//! normalization (path / git / scope-only Reservoir), and the lakefile
//! discovery order. Split out of `toml_config.rs` for file size; declared
//! there behind `#[cfg(test)]`.

use super::*;

/// The canonical Mathlib-dependent template emitted by Lake's own
/// `lake init … math` (verified against `src/lake/Lake/CLI/Init.lean`).
#[test]
fn parse_mathlib_template() {
    let content = r#"
name = "myproject"
version = "0.1.0"
keywords = ["math"]
defaultTargets = ["MyProject"]

[leanOptions]
pp.unicode.fun = true
relaxedAutoImplicit = false

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.30.0"

[[lean_lib]]
name = "MyProject"
"#;
    let cfg = LakeConfig::parse_toml(content).expect("template must parse");
    assert_eq!(cfg.package.name, "myproject");
    assert_eq!(cfg.package.version.as_deref(), Some("0.1.0"));
    assert_eq!(cfg.default_targets, vec!["MyProject".to_string()]);

    assert_eq!(cfg.package.dependencies.len(), 1);
    let dep = &cfg.package.dependencies[0];
    assert_eq!(dep.name, "mathlib");
    // `rev` with no explicit git/version is preserved as the revision.
    assert_eq!(dep.rev.as_deref(), Some("v4.30.0"));

    assert_eq!(cfg.libs.len(), 1);
    assert_eq!(cfg.libs[0].name, "MyProject");
    // Root defaults to the lib name when `roots` is omitted.
    assert_eq!(cfg.libs[0].roots, vec!["MyProject".to_string()]);
}

#[test]
fn parse_exe_with_default_root() {
    let content = r#"
name = "tool"
defaultTargets = ["tool"]

[[lean_exe]]
name = "tool"
"#;
    let cfg = LakeConfig::parse_toml(content).expect("exe lakefile must parse");
    assert_eq!(cfg.exes.len(), 1);
    assert_eq!(cfg.exes[0].name, "tool");
    // Executable root defaults to the exe name.
    assert_eq!(cfg.exes[0].root, "tool");
}

#[test]
fn parse_require_git_string_and_path_forms() {
    let content = r#"
name = "p"

[[require]]
name = "depgit"
git = "https://github.com/example/dep"
rev = "abc123"

[[require]]
name = "deplocal"
path = "../local-dep"
"#;
    let cfg = LakeConfig::parse_toml(content).expect("git/path requires must parse");
    assert_eq!(cfg.package.dependencies.len(), 2);

    let g = &cfg.package.dependencies[0];
    assert_eq!(g.git.as_deref(), Some("https://github.com/example/dep"));
    assert_eq!(g.rev.as_deref(), Some("abc123"));

    let p = &cfg.package.dependencies[1];
    assert_eq!(p.path.as_deref(), Some(Path::new("../local-dep")));
    assert!(p.git.is_none());
}

#[test]
fn parse_require_git_table_form() {
    let content = r#"
name = "p"

[[require]]
name = "deptable"
git = { url = "https://github.com/example/dep", rev = "deadbeef" }
"#;
    let cfg = LakeConfig::parse_toml(content).expect("git-table require must parse");
    let d = &cfg.package.dependencies[0];
    assert_eq!(d.git.as_deref(), Some("https://github.com/example/dep"));
    assert_eq!(d.rev.as_deref(), Some("deadbeef"));
}

#[test]
fn parse_require_source_table_form() {
    let content = r#"
name = "p"

[[require]]
name = "depsrc"

[require.source]
type = "git"
url = "https://github.com/example/src"
rev = "f00"
"#;
    let cfg = LakeConfig::parse_toml(content).expect("source-table require must parse");
    let d = &cfg.package.dependencies[0];
    assert_eq!(d.git.as_deref(), Some("https://github.com/example/src"));
    assert_eq!(d.rev.as_deref(), Some("f00"));
}

/// Scope-only (Reservoir) requires — the shape all of real Mathlib's
/// `lakefile.toml` dependencies use — must normalize to a git dependency
/// offline rather than dying in resolve with "neither git nor path".
#[test]
fn scope_only_require_normalizes_to_github_convention() {
    let content = r#"
name = "p"

[[require]]
name = "batteries"
scope = "leanprover-community"
rev = "main"
"#;
    let cfg = LakeConfig::parse_toml(content).expect("scope-only require must parse");
    let d = &cfg.package.dependencies[0];
    assert_eq!(
        d.git.as_deref(),
        Some("https://github.com/leanprover-community/batteries")
    );
    assert_eq!(d.scope.as_deref(), Some("leanprover-community"));
    assert_eq!(d.rev.as_deref(), Some("main"));
    assert!(d.path.is_none());
}

/// The static override table: packages whose repository name breaks the
/// `github.com/{scope}/{name}` convention. Expected URLs verified against
/// a real Mathlib `lake-manifest.json` (mathlib4 @ 43ad0e9d2e14).
#[test]
fn scope_only_require_override_table_spellings() {
    for (scope, name, url) in [
        (
            "leanprover-community",
            "importGraph",
            "https://github.com/leanprover-community/import-graph",
        ),
        (
            "leanprover-community",
            "proofwidgets",
            "https://github.com/leanprover-community/ProofWidgets4",
        ),
        (
            "leanprover-community",
            "Qq",
            "https://github.com/leanprover-community/quote4",
        ),
        (
            "leanprover",
            "Cli",
            "https://github.com/leanprover/lean4-cli",
        ),
        (
            "leanprover-community",
            "mathlib",
            "https://github.com/leanprover-community/mathlib4",
        ),
    ] {
        assert_eq!(reservoir_offline_git_url(scope, name), url);
    }
    // Overrides key on the exact (scope, name) pair: the same name under a
    // different scope falls back to the convention.
    assert_eq!(
        reservoir_offline_git_url("other-scope", "importGraph"),
        "https://github.com/other-scope/importGraph"
    );
}

/// An overridden package parses end-to-end to the corrected repository.
#[test]
fn scope_only_require_proofwidgets_maps_to_repo_override() {
    let content = r#"
name = "p"

[[require]]
name = "proofwidgets"
scope = "leanprover-community"
version = "0.0.68"
"#;
    let cfg = LakeConfig::parse_toml(content).expect("override require must parse");
    let d = &cfg.package.dependencies[0];
    assert_eq!(
        d.git.as_deref(),
        Some("https://github.com/leanprover-community/ProofWidgets4")
    );
    assert_eq!(d.version.as_deref(), Some("0.0.68"));
}

/// An explicit git URL always wins over the scope-derived one; the scope
/// is still recorded for diagnostics.
#[test]
fn explicit_git_wins_over_scope() {
    let content = r#"
name = "p"

[[require]]
name = "importGraph"
scope = "leanprover-community"
git = "https://example.com/fork/import-graph"
"#;
    let cfg = LakeConfig::parse_toml(content).expect("git+scope require must parse");
    let d = &cfg.package.dependencies[0];
    assert_eq!(
        d.git.as_deref(),
        Some("https://example.com/fork/import-graph")
    );
    assert_eq!(d.scope.as_deref(), Some("leanprover-community"));
}

/// A path require with a scope stays a path require: no git URL is
/// synthesized from the scope.
#[test]
fn path_wins_over_scope() {
    let content = r#"
name = "p"

[[require]]
name = "localdep"
scope = "leanprover-community"
path = "../localdep"
"#;
    let cfg = LakeConfig::parse_toml(content).expect("path+scope require must parse");
    let d = &cfg.package.dependencies[0];
    assert!(d.git.is_none());
    assert_eq!(d.path.as_deref(), Some(Path::new("../localdep")));
}

/// Forward-compatibility: unknown top-level and per-target keys must be
/// ignored, not rejected, so a newer `lakefile.toml` still loads.
#[test]
fn unknown_keys_are_ignored() {
    let content = r#"
name = "p"
someFutureKey = "whatever"
platformIndependent = true

[[lean_lib]]
name = "L"
futureLibKey = 42
"#;
    let cfg = LakeConfig::parse_toml(content).expect("unknown keys must be tolerated");
    assert_eq!(cfg.package.name, "p");
    assert_eq!(cfg.libs[0].name, "L");
}

#[test]
fn explicit_roots_and_globs_preserved() {
    let content = r#"
name = "p"

[[lean_lib]]
name = "L"
srcDir = "src"
roots = ["L", "L.Extra"]
globs = ["L.+"]
"#;
    let cfg = LakeConfig::parse_toml(content).expect("lib with roots/globs must parse");
    let lib = &cfg.libs[0];
    assert_eq!(lib.roots, vec!["L".to_string(), "L.Extra".to_string()]);
    assert_eq!(lib.globs, vec!["L.+".to_string()]);
    assert_eq!(lib.src_dir.as_deref(), Some(Path::new("src")));
}

#[test]
fn toolchain_falls_back_to_lean_version() {
    let content = r#"
name = "p"
toolchain = "leanprover/lean4:v4.30.0-rc2"
"#;
    let cfg = LakeConfig::parse_toml(content).expect("toolchain key must parse");
    assert_eq!(
        cfg.package.lean_version.as_deref(),
        Some("leanprover/lean4:v4.30.0-rc2")
    );
}

/// `subDir` on a git require names the package root INSIDE the repository —
/// how a monorepo publishes several Lake packages from one repo. It used to be
/// deserialized and then discarded (`#[allow(dead_code)]` on both spellings),
/// so the clone succeeded and resolution silently pointed at the repository
/// root: a wrong build with no diagnostic. Both accepted spellings must carry
/// it through to the `Dependency`.
#[test]
fn parse_require_carries_sub_dir_from_git_table_and_source() {
    let content = r#"
name = "monorepo-consumer"

[[require]]
name = "inner"
git = { url = "https://example.com/mono.git", rev = "abc123", subDir = "packages/inner" }

[[require]]
name = "nested"
[require.source]
type = "git"
url = "https://example.com/other.git"
subDir = "sub/pkg"
"#;
    let config = LakeConfig::parse_toml(content).expect("toml lakefile should parse");
    let deps = &config.package.dependencies;
    assert_eq!(deps.len(), 2, "both requires should be modelled: {deps:?}");

    let inner = deps.iter().find(|d| d.name == "inner").expect("inner");
    assert_eq!(inner.git.as_deref(), Some("https://example.com/mono.git"));
    assert_eq!(inner.rev.as_deref(), Some("abc123"));
    assert_eq!(
        inner.sub_dir.as_deref(),
        Some(Path::new("packages/inner")),
        "git-table subDir must reach the Dependency"
    );

    let nested = deps.iter().find(|d| d.name == "nested").expect("nested");
    assert_eq!(nested.git.as_deref(), Some("https://example.com/other.git"));
    assert_eq!(
        nested.sub_dir.as_deref(),
        Some(Path::new("sub/pkg")),
        "[require.source] subDir must reach the Dependency"
    );
}
