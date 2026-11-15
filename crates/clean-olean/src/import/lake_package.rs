// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Whether a Lake package builds a source file (decision R111, G72).
//!
//! A `lean-toolchain` nearer to a file than its enclosing package's names the
//! world only when that package does not build the file: `lake build` of the
//! package runs the package's toolchain on every module it owns, and no Lake
//! build reaches any other file, which only `lean` run from the file's own
//! directory checks (measured 2026-10-22, elan 4.2.3: in a v4.8.0 package with
//! `[[lean_lib]] name = "Inner"`, `lake build Inner.Lib` runs Lean 4.8.0
//! whatever `Inner/lean-toolchain` names; under a package whose only library
//! is `Outer`, `lake build proj.Probe` is "unknown target", and `lean` in
//! `proj/` runs `proj/lean-toolchain`'s Lean).
//!
//! A package owns a module as Lake's `isLocalModule` says: a library owns
//! every module one of its roots is a prefix of (a root defaults to the
//! library's name), an executable its root module, each under the package's
//! `srcDir` joined with the target's own. The lakefile is read line by line,
//! as `lake_module_name`'s `srcDir` scan reads it; a declaration this reading
//! cannot settle (`globs`, a multi-line `roots`) makes the answer
//! [`Ownership::Unknown`], and the caller refuses rather than guesses.

use std::path::{Component, Path, PathBuf};

/// What a package's lakefile says about one of the files under it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Ownership {
    /// One of the package's targets builds the file.
    Owned,
    /// No target of the package builds the file.
    NotOwned,
    /// The lakefile declares something this reading cannot settle.
    Unknown,
}

/// A `lean_lib` (prefix roots) or `lean_exe` (one exact root).
#[derive(Debug, Default)]
struct Target {
    exe: bool,
    name: Option<Vec<String>>,
    roots: Option<Vec<Vec<String>>>,
    src_dir: Option<String>,
}

/// What the line reading found: the package's `srcDir` and its targets, or
/// `None` when it met something it cannot settle.
#[derive(Debug, Default)]
struct Package {
    src_dir: Option<String>,
    targets: Vec<Target>,
}

/// Whether the package rooted at `root` builds `file`.
pub(crate) fn package_owns(root: &Path, file: &Path) -> Ownership {
    let package = if let Ok(text) = std::fs::read_to_string(root.join("lakefile.lean")) {
        read_lean(&text)
    } else if let Ok(text) = std::fs::read_to_string(root.join("lakefile.toml")) {
        read_toml(&text)
    } else {
        None
    };
    let Some(package) = package else {
        return Ownership::Unknown;
    };
    let package_dir = join_src(root, package.src_dir.as_deref());
    for target in &package.targets {
        let base = join_src(&package_dir, target.src_dir.as_deref());
        let Some(module) = module_components(&base, file) else {
            continue;
        };
        let default_root = || target.name.clone().into_iter().collect::<Vec<_>>();
        let roots = target.roots.clone().unwrap_or_else(default_root);
        let owned = if target.exe {
            roots.contains(&module)
        } else {
            roots.iter().any(|root| module.starts_with(root))
        };
        if owned {
            return Ownership::Owned;
        }
    }
    Ownership::NotOwned
}

fn join_src(base: &Path, src_dir: Option<&str>) -> PathBuf {
    match src_dir {
        Some(dir) if !dir.is_empty() && dir != "." => base.join(dir),
        _ => base.to_path_buf(),
    }
}

/// `file`'s module components relative to `base` (no `.lean`), if under it.
fn module_components(base: &Path, file: &Path) -> Option<Vec<String>> {
    let relative = file.strip_prefix(base).ok()?.with_extension("");
    let mut out = Vec::new();
    for component in relative.components() {
        match component {
            Component::Normal(part) => out.push(part.to_str()?.to_string()),
            Component::CurDir => {}
            _ => return None,
        }
    }
    (!out.is_empty()).then_some(out)
}

/// A Lean name as written in a lakefile (`Foo.Bar`, `«Foo.Bar»`, `` `Foo ``):
/// its components, a `«…»` component taken verbatim.
fn name_components(text: &str) -> Option<Vec<String>> {
    let text = text.trim().trim_start_matches('`');
    let mut out = Vec::new();
    let mut rest = text;
    while !rest.is_empty() {
        if let Some(quoted) = rest.strip_prefix('«') {
            let end = quoted.find('»')?;
            out.push(quoted[..end].to_string());
            rest = &quoted[end + '»'.len_utf8()..];
        } else {
            let end = rest.find('.').unwrap_or(rest.len());
            let part = &rest[..end];
            let ident =
                |c: char| c.is_alphanumeric() || c == '_' || c == '\'' || c == '!' || c == '?';
            if part.is_empty() || !part.chars().all(ident) {
                return None;
            }
            out.push(part.to_string());
            rest = &rest[end..];
        }
        rest = match rest.strip_prefix('.') {
            Some(after) if !after.is_empty() => after,
            Some(_) => return None,
            None if rest.is_empty() => rest,
            None => return None,
        };
    }
    (!out.is_empty()).then_some(out)
}

/// The string literal a `key = "…"` / `key := "…"` line sets, if the line
/// sets `key` to one.
fn string_value<'a>(line: &'a str, key: &str, assign: &str) -> Option<&'a str> {
    let rest = line.strip_prefix(key)?.trim_start();
    let body = rest.strip_prefix(assign)?.trim().strip_prefix('"')?;
    let end = body.find('"')?;
    Some(&body[..end])
}

/// Whether `line` assigns `key` (`key =` / `key :=`).
fn assigns(line: &str, key: &str) -> bool {
    line.strip_prefix(key)
        .map(str::trim_start)
        .is_some_and(|rest| rest.starts_with('=') || rest.starts_with(":="))
}

/// `lakefile.toml`, read line by line.
fn read_toml(text: &str) -> Option<Package> {
    let mut package = Package::default();
    // `None`: the package table; `Some(None)`: another table.
    let mut current: Option<Option<usize>> = None;
    for raw in text.lines() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if line.starts_with('[') {
            current = Some(match line {
                "[[lean_lib]]" | "[[lean_exe]]" => {
                    package.targets.push(Target {
                        exe: line == "[[lean_exe]]",
                        ..Target::default()
                    });
                    Some(package.targets.len() - 1)
                }
                _ => None,
            });
            continue;
        }
        match current {
            None => {
                if let Some(dir) = string_value(line, "srcDir", "=") {
                    package.src_dir = Some(dir.to_string());
                }
            }
            Some(None) => {}
            Some(Some(at)) => {
                let target = &mut package.targets[at];
                if assigns(line, "globs") {
                    return None;
                } else if let Some(name) = string_value(line, "name", "=") {
                    target.name = Some(name_components(name)?);
                } else if let Some(dir) = string_value(line, "srcDir", "=") {
                    target.src_dir = Some(dir.to_string());
                } else if let Some(root) = string_value(line, "root", "=") {
                    target.roots = Some(vec![name_components(root)?]);
                } else if assigns(line, "roots") {
                    let list = line.split_once('[')?.1;
                    let list = list.strip_suffix(']')?;
                    let roots = list
                        .split(',')
                        .map(str::trim)
                        .filter(|item| !item.is_empty())
                        .map(|item| name_components(item.trim_matches('"')))
                        .collect::<Option<Vec<_>>>()?;
                    target.roots = Some(roots);
                } else if assigns(line, "name") || assigns(line, "srcDir") || assigns(line, "root")
                {
                    return None;
                }
            }
        }
    }
    Some(package)
}

/// `lakefile.lean`, read line by line: a command starts at column 0, and a
/// target's fields are the indented lines below it.
fn read_lean(text: &str) -> Option<Package> {
    let mut package = Package::default();
    // `None`: outside any target or package; `Some(None)`: the package.
    let mut current: Option<Option<usize>> = None;
    for raw in text.lines() {
        let code = raw.split("--").next().unwrap_or_default();
        if code.trim().is_empty() {
            continue;
        }
        if !code.starts_with([' ', '\t']) {
            let mut command = code.trim();
            if command.starts_with("@[") {
                command = command.split_once(']')?.1.trim();
            }
            current = None;
            for (keyword, exe) in [("lean_lib ", false), ("lean_exe ", true)] {
                if let Some(rest) = command.strip_prefix(keyword) {
                    let name = rest.split_whitespace().next()?;
                    package.targets.push(Target {
                        exe,
                        name: Some(name_components(name)?),
                        ..Target::default()
                    });
                    current = Some(Some(package.targets.len() - 1));
                }
            }
            if command.starts_with("package ") {
                current = Some(None);
            }
            if command.starts_with("target ")
                || (command.contains("lean_lib") && !matches!(current, Some(Some(_))))
            {
                return None;
            }
            continue;
        }
        let line = code.trim();
        match current {
            None => {}
            Some(None) => {
                if let Some(dir) = string_value(line, "srcDir", ":=") {
                    package.src_dir = Some(dir.to_string());
                }
            }
            Some(Some(at)) => {
                let target = &mut package.targets[at];
                if assigns(line, "globs") {
                    return None;
                } else if let Some(dir) = string_value(line, "srcDir", ":=") {
                    target.src_dir = Some(dir.to_string());
                } else if assigns(line, "roots") {
                    let list = line.split_once("#[")?.1.strip_suffix(']')?;
                    let roots = list
                        .split(',')
                        .map(str::trim)
                        .filter(|item| !item.is_empty())
                        .map(name_components)
                        .collect::<Option<Vec<_>>>()?;
                    target.roots = Some(roots);
                } else if assigns(line, "root") {
                    let root = line.split_once('`')?.1;
                    target.roots = Some(vec![name_components(root)?]);
                } else if assigns(line, "srcDir") {
                    return None;
                }
            }
        }
    }
    Some(package)
}

#[cfg(test)]
#[path = "lake_package_tests.rs"]
mod tests;
