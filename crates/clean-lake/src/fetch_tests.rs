// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::path::PathBuf;

#[test]
fn test_git_available() {
    // Git should be available in test environment
    assert!(FetchManager::git_available());
}

#[test]
fn test_fetch_manager_new() {
    let root = Path::new("/tmp/test_project");
    let packages = Path::new("/tmp/test_project/.lake/packages");
    let fm = FetchManager::new(root, packages);
    assert_eq!(fm.root, root);
    assert_eq!(fm.packages_dir, packages);
}

#[test]
fn test_resolve_result_empty() {
    let result = ResolveResult {
        resolved: vec![],
        errors: vec![],
    };
    assert!(result.resolved.is_empty());
    assert!(result.errors.is_empty());
}

#[test]
fn test_resolved_package_git() {
    let pkg = ResolvedPackage {
        name: "std".to_string(),
        url: Some("https://github.com/leanprover/std4".to_string()),
        rev: "abc123def456".to_string(),
        input_rev: Some("main".to_string()),
        path: None,
        inherited: false,
    };
    assert_eq!(pkg.name, "std");
    assert!(pkg.url.is_some(), "git package should have url");
    assert!(pkg.path.is_none(), "git package should not have path");
}

#[test]
fn test_resolved_package_path() {
    let pkg = ResolvedPackage {
        name: "local".to_string(),
        url: None,
        rev: String::new(),
        input_rev: None,
        path: Some("../local-pkg".to_string()),
        inherited: false,
    };
    assert_eq!(pkg.name, "local");
    assert!(pkg.url.is_none(), "path package should not have url");
    assert!(pkg.path.is_some(), "path package should have path");
}

#[test]
fn test_resolve_path_dependency_not_found() {
    use tempfile::tempdir;

    let temp = tempdir().unwrap();
    let root = temp.path();
    let packages_dir = root.join(".lake/packages");

    let fm = FetchManager::new(root, &packages_dir);

    let dep = Dependency {
        name: "missing".to_string(),
        git: None,
        rev: None,
        path: Some(PathBuf::from("nonexistent")),
        version: None,
        scope: None,
        sub_dir: None,
    };

    let result = fm.resolve_dependencies(&[dep]).unwrap();
    assert!(result.resolved.is_empty());
    assert_eq!(result.errors.len(), 1);
    assert!(result.errors[0].1.contains("not found"));
}

#[test]
fn test_resolve_dependency_no_source() {
    use tempfile::tempdir;

    let temp = tempdir().unwrap();
    let root = temp.path();
    let packages_dir = root.join(".lake/packages");

    let fm = FetchManager::new(root, &packages_dir);

    let dep = Dependency {
        name: "invalid".to_string(),
        git: None,
        rev: None,
        path: None,
        version: None,
        scope: None,
        sub_dir: None,
    };

    let result = fm.resolve_dependencies(&[dep]).unwrap();
    assert!(result.resolved.is_empty());
    assert_eq!(result.errors.len(), 1);
    assert!(result.errors[0].1.contains("neither git nor path"));
}

/// A clone failure on a URL derived from a scope-only (Reservoir) require
/// must name the scope/name and say the Reservoir API was not consulted.
/// (No network: the attribution helper is exercised directly.)
#[test]
fn test_scope_only_fetch_error_names_scope_and_reservoir() {
    let dep = Dependency {
        name: "importGraph".to_string(),
        // The URL the offline mapping derives for this (scope, name).
        git: Some("https://github.com/leanprover-community/import-graph".to_string()),
        rev: None,
        path: None,
        version: None,
        scope: Some("leanprover-community".to_string()),
        sub_dir: None,
    };
    let base = LakeError::GitError {
        operation: "clone".to_string(),
        message: "exit status 128".to_string(),
    };
    let msg = attribute_scope_only_fetch_error(
        &dep,
        dep.git.as_deref().expect("git URL set above"),
        base,
    )
    .to_string();
    assert!(
        msg.contains("leanprover-community/importGraph"),
        "must name scope/name: {msg}"
    );
    assert!(msg.contains("Reservoir"), "must mention Reservoir: {msg}");
    assert!(
        msg.contains("not consulted"),
        "must state the API was not consulted: {msg}"
    );
    // The underlying git failure stays visible.
    assert!(
        msg.contains("exit status 128"),
        "must keep the cause: {msg}"
    );
}

/// A failure on an explicitly-written git URL passes through unchanged,
/// even when the require also declared a scope.
#[test]
fn test_explicit_git_fetch_error_passes_through() {
    let dep = Dependency {
        name: "importGraph".to_string(),
        git: Some("https://example.com/fork/import-graph".to_string()),
        rev: None,
        path: None,
        version: None,
        scope: Some("leanprover-community".to_string()),
        sub_dir: None,
    };
    let base = LakeError::GitError {
        operation: "clone".to_string(),
        message: "exit status 128".to_string(),
    };
    let msg = attribute_scope_only_fetch_error(
        &dep,
        dep.git.as_deref().expect("git URL set above"),
        base,
    )
    .to_string();
    assert!(
        !msg.contains("Reservoir"),
        "explicit URL must not be blamed on the offline mapping: {msg}"
    );
}

/// Write a minimal `lakefile.toml` package into `dir`, with the given
/// path-form requires (each relative to `dir`, as Lake declares them).
fn write_lakefile_toml(dir: &Path, name: &str, path_requires: &[(&str, &str)]) {
    std::fs::create_dir_all(dir).unwrap();
    let mut content = format!("name = \"{name}\"\n");
    for (rname, rpath) in path_requires {
        let req = format!("\n[[require]]\nname = \"{rname}\"\npath = \"{rpath}\"\n");
        content.push_str(&req);
    }
    std::fs::write(dir.join("lakefile.toml"), content).unwrap();
}

/// Run a git subcommand in `dir`, panicking with stderr on failure.
fn git(dir: &Path, args: &[&str]) {
    let out = Command::new("git")
        .arg("-C")
        .arg(dir)
        .args(args)
        .output()
        .expect("git should be runnable in the test environment");
    assert!(
        out.status.success(),
        "git {args:?} failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
}

/// Turn `dir` into a single-commit git repo on branch `main`, so it can
/// serve as a local "remote" for clone-based fetch tests (no network).
fn git_init_commit(dir: &Path) {
    git(dir, &["init", "-q", "-b", "main"]);
    git(dir, &["add", "-A"]);
    git(
        dir,
        &[
            "-c",
            "user.email=test@example.com",
            "-c",
            "user.name=Test",
            "-c",
            "commit.gpgsign=false",
            "commit",
            "-q",
            "-m",
            "init",
        ],
    );
}

fn path_dep(name: &str, path: &str) -> Dependency {
    Dependency {
        name: name.to_string(),
        git: None,
        rev: None,
        path: Some(PathBuf::from(path)),
        version: None,
        scope: None,
        sub_dir: None,
    }
}

/// Transitive closure over path deps: root requires B, B's own lakefile
/// requires C — the manifest must list BOTH B and C, with C re-expressed
/// relative to the workspace root and flagged as inherited.
#[test]
fn test_resolve_transitive_path_deps_lists_full_closure() {
    use tempfile::tempdir;

    let temp = tempdir().unwrap();
    let root = temp.path();
    let packages_dir = root.join(".lake/packages");
    // B requires C relative to B's own directory, as Lake declares it.
    write_lakefile_toml(&root.join("depB"), "depB", &[("depC", "../depC")]);
    write_lakefile_toml(&root.join("depC"), "depC", &[]);

    let fm = FetchManager::new(root, &packages_dir);
    let (manifest, result) = fm
        .resolve_to_manifest(&[path_dep("depB", "depB")])
        .expect("resolution should succeed");

    assert!(
        result.errors.is_empty(),
        "unexpected errors: {:?}",
        result.errors
    );
    let names: Vec<&str> = result.resolved.iter().map(|p| p.name.as_str()).collect();
    assert_eq!(names, vec!["depB", "depC"]);
    assert!(!result.resolved[0].inherited, "direct dep is not inherited");
    assert!(result.resolved[1].inherited, "transitive dep is inherited");
    // C's path was declared as "../depC" relative to depB; the manifest
    // entry must be meaningful from the workspace root.
    assert_eq!(result.resolved[1].path.as_deref(), Some("depC"));

    let b = manifest
        .get_package("depB")
        .expect("B listed in manifest")
        .as_path()
        .expect("B is a path package");
    assert_eq!(b.inherited, Some(false));
    let c = manifest
        .get_package("depC")
        .expect("transitive C listed in manifest")
        .as_path()
        .expect("C is a path package");
    assert_eq!(c.path, "depC");
    assert_eq!(c.inherited, Some(true));
}

/// Transitive closure over git deps using local repos as "remotes" (no
/// network): root requires git package B, whose lakefile requires git
/// package C — the manifest must pin concrete commit SHAs for BOTH.
#[test]
fn test_resolve_transitive_git_deps_pins_revs() {
    use tempfile::tempdir;

    let temp = tempdir().unwrap();
    let remotes = temp.path().join("remotes");

    // Leaf repo C.
    let repo_c = remotes.join("depC");
    write_lakefile_toml(&repo_c, "depC", &[]);
    git_init_commit(&repo_c);

    // Repo B requires C via a git URL (a local path works with git clone).
    let repo_b = remotes.join("depB");
    std::fs::create_dir_all(&repo_b).unwrap();
    std::fs::write(
        repo_b.join("lakefile.toml"),
        format!(
            "name = \"depB\"\n\n[[require]]\nname = \"depC\"\ngit = \"{}\"\n",
            repo_c.display()
        ),
    )
    .unwrap();
    git_init_commit(&repo_b);

    let proj = temp.path().join("proj");
    std::fs::create_dir_all(&proj).unwrap();
    let packages_dir = proj.join(".lake/packages");
    let fm = FetchManager::new(&proj, &packages_dir);

    let dep = Dependency {
        name: "depB".to_string(),
        git: Some(repo_b.display().to_string()),
        rev: None,
        path: None,
        version: None,
        scope: None,
        sub_dir: None,
    };

    let (manifest, result) = fm
        .resolve_to_manifest(&[dep])
        .expect("resolution should succeed");
    assert!(
        result.errors.is_empty(),
        "unexpected errors: {:?}",
        result.errors
    );
    assert_eq!(result.resolved.len(), 2, "closure must contain B and C");

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
    assert_eq!(
        manifest
            .get_package("depB")
            .unwrap()
            .as_git()
            .unwrap()
            .inherited,
        Some(false)
    );
    assert_eq!(
        manifest
            .get_package("depC")
            .unwrap()
            .as_git()
            .unwrap()
            .inherited,
        Some(true)
    );
}

/// First-wins conflict policy (matching Lake): when the root requires C
/// directly and B also requires C, the first resolution wins and C is
/// listed exactly once.
#[test]
fn test_resolve_dedup_first_wins() {
    use tempfile::tempdir;

    let temp = tempdir().unwrap();
    let root = temp.path();
    let packages_dir = root.join(".lake/packages");
    write_lakefile_toml(&root.join("depB"), "depB", &[("depC", "../depC")]);
    write_lakefile_toml(&root.join("depC"), "depC", &[]);

    let fm = FetchManager::new(root, &packages_dir);
    let result = fm
        .resolve_dependencies(&[path_dep("depC", "depC"), path_dep("depB", "depB")])
        .expect("resolution should succeed");

    assert!(
        result.errors.is_empty(),
        "unexpected errors: {:?}",
        result.errors
    );
    let names: Vec<&str> = result.resolved.iter().map(|p| p.name.as_str()).collect();
    assert_eq!(names, vec!["depC", "depB"], "C listed once, first-wins");
    assert!(
        !result.resolved[0].inherited,
        "the direct C resolution won over B's transitive require"
    );
}

/// A require cycle (B -> C -> B) must be detected and reported loudly
/// instead of looping; the acyclic part of the closure still resolves.
#[test]
fn test_resolve_cycle_reports_circular_error() {
    use tempfile::tempdir;

    let temp = tempdir().unwrap();
    let root = temp.path();
    let packages_dir = root.join(".lake/packages");
    write_lakefile_toml(&root.join("depB"), "depB", &[("depC", "../depC")]);
    write_lakefile_toml(&root.join("depC"), "depC", &[("depB", "../depB")]);

    let fm = FetchManager::new(root, &packages_dir);
    let result = fm
        .resolve_dependencies(&[path_dep("depB", "depB")])
        .expect("resolution itself should not abort");

    let names: Vec<&str> = result.resolved.iter().map(|p| p.name.as_str()).collect();
    assert_eq!(names, vec!["depB", "depC"], "acyclic part still resolves");
    assert_eq!(result.errors.len(), 1, "the cycle is reported");
    assert_eq!(result.errors[0].0, "depB");
    assert!(
        result.errors[0].1.contains("circular dependency"),
        "error names the cycle: {}",
        result.errors[0].1
    );
    assert!(
        result.errors[0].1.contains("depB -> depC -> depB"),
        "error shows the require chain: {}",
        result.errors[0].1
    );
}

/// A require chain deeper than MAX_RESOLVE_DEPTH stops with a loud
/// depth-bound error instead of expanding forever.
#[test]
fn test_resolve_depth_bound_reports_loud_error() {
    use tempfile::tempdir;

    let temp = tempdir().unwrap();
    let root = temp.path();
    let packages_dir = root.join(".lake/packages");

    let n = MAX_RESOLVE_DEPTH + 5;
    for i in 0..=n {
        let dir = root.join(format!("pkg{i}"));
        let name = format!("pkg{i}");
        if i < n {
            let next = format!("pkg{}", i + 1);
            let rel = format!("../{next}");
            write_lakefile_toml(&dir, &name, &[(next.as_str(), rel.as_str())]);
        } else {
            write_lakefile_toml(&dir, &name, &[]);
        }
    }

    let fm = FetchManager::new(root, &packages_dir);
    let result = fm
        .resolve_dependencies(&[path_dep("pkg0", "pkg0")])
        .expect("resolution itself should not abort");

    assert_eq!(
        result.resolved.len(),
        MAX_RESOLVE_DEPTH + 1,
        "packages up to the bound still resolve"
    );
    assert_eq!(result.errors.len(), 1, "the depth overflow is reported");
    assert!(
        result.errors[0].1.contains("maximum depth"),
        "error names the depth bound: {}",
        result.errors[0].1
    );
}
