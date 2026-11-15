// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The Lean module name of a source file under a Lake package.
//!
//! Lake names a library module by its path relative to the library's
//! `srcDir` (`TrustIr/Constant.lean` under `srcDir := "."` is
//! `TrustIr.Constant`), whatever directory the build runs from. This is the
//! reverse of [`crate::resolve_intra_project_import`], which maps
//! `import TrustIr.Constant` back to that file. Every driver names the file it
//! elaborates with it, so a file's `private` declarations get one kernel name
//! (`_private.TrustIr.Constant.0.<name>`, G21) and its diagnostics one module
//! tag (G14), whether it was invoked by a relative or an absolute path or
//! reached through an `import`.

use crate::imports::nearest_lake_root_for_file;
use clean_kernel::Name;
use std::path::{Component, Path, PathBuf};

/// Lake's module name for `path`: its path, without `.lean`, relative to the
/// deepest of the nearest Lake root's declared `srcDir`s that contains it, or
/// to the root itself.
///
/// `None` when no Lake root (a `lakefile.lean`, `lakefile.toml` or
/// `lake-manifest.json`) encloses the file, when the file does not exist, or
/// when a path component is not UTF-8; the caller keeps its own fallback.
#[must_use]
pub fn lean_module_name_for_file(path: &Path) -> Option<Name> {
    let file = path.canonicalize().ok()?;
    let root = nearest_lake_root_for_file(&file)?;
    let mut bases: Vec<PathBuf> = declared_src_dirs(&root)
        .into_iter()
        .filter_map(|dir| root.join(dir).canonicalize().ok())
        .collect();
    bases.push(root);
    let base = bases
        .into_iter()
        .filter(|base| file.starts_with(base))
        .max_by_key(|base| base.components().count())?;
    let relative = file.strip_prefix(&base).ok()?.with_extension("");
    let mut name = Name::anon();
    for component in relative.components() {
        let Component::Normal(part) = component else {
            return None;
        };
        let part = part.to_str().filter(|part| !part.is_empty())?;
        name = name.str(part);
    }
    (!name.is_anon()).then_some(name)
}

/// The main module a driver names an entry file with: Lake's name for it
/// ([`lean_module_name_for_file`]), else, outside any Lake package, the name
/// `lean <file>` gives it ([`path_module_name`]).
#[must_use]
pub fn entry_module_name(path: &Path) -> Name {
    lean_module_name_for_file(path).unwrap_or_else(|| path_module_name(path))
}

/// `_stdin`: Lean 4.8.0's main module for a file outside the working
/// directory.
const STDIN_MODULE: &str = "_stdin";

/// The module components `lean <file>` (Lean 4.8.0, no `--root`) names a file
/// with, which is `moduleNameOfFileName file (rootDir := cwd)`: the file's
/// REAL path relative to the real working directory, without `.lean`, one
/// component per directory. A file outside the working directory is
/// `_stdin` (measured 2026-10-09: from `loose/`, `lean /abs/…/loose/sub/G.lean`
/// prints `_private.sub.G.0.pt`; from `loose/sub`, `lean ../sub/X.lean`
/// prints `_private.X.0.pt`; from `cwd/`, `lean ../out/H.lean` prints
/// `_private._stdin.0.pt`). A path that does not resolve keeps its spelling
/// as given (Lean would refuse to open it).
fn loose_module_components(path: &Path) -> Vec<String> {
    let real = path.canonicalize().ok();
    let cwd = std::env::current_dir()
        .ok()
        .and_then(|dir| dir.canonicalize().ok());
    let relative: PathBuf = match (real, cwd) {
        (Some(real), Some(cwd)) => match real.strip_prefix(&cwd) {
            Ok(relative) => relative.to_path_buf(),
            Err(_) => return vec![STDIN_MODULE.to_owned()],
        },
        _ => path.to_path_buf(),
    };
    relative
        .with_extension("")
        .components()
        .filter_map(|component| match component {
            Component::Normal(part) => part.to_str().filter(|part| !part.is_empty()),
            _ => None,
        })
        .map(str::to_owned)
        .collect()
}

/// The main module of a file outside any Lake package, `lean <file>`'s rule
/// ([`loose_module_components`]), one string component per path component
/// (Lean's `«agent-501»`: a directory named `501` or `.tmp9` stays one
/// component, never a number or an empty component).
#[must_use]
pub fn path_module_name(path: &Path) -> Name {
    loose_module_components(path)
        .iter()
        .fold(Name::anon(), |name, part| name.str(part))
}

/// [`path_module_name`] with its components joined by `.`, unescaped: the
/// module label of a file outside any Lake package.
#[must_use]
pub fn path_module_label(path: &Path) -> String {
    loose_module_components(path).join(".")
}

/// Every `srcDir` a Lake root's configuration declares as a plain string
/// literal: `srcDir := "src"` in `lakefile.lean` (package, `lean_lib` or
/// `lean_exe` block alike), `srcDir = "src"` in `lakefile.toml`. A form that is
/// not a single literal is skipped, so its files are named from the root.
/// This reads lines the way `clean-lake`'s own lakefile reader does; it does
/// not evaluate the lakefile.
fn declared_src_dirs(root: &Path) -> Vec<String> {
    let text = std::fs::read_to_string(root.join("lakefile.lean"))
        .or_else(|_| std::fs::read_to_string(root.join("lakefile.toml")))
        .unwrap_or_default();
    text.lines().filter_map(src_dir_literal).collect()
}

fn src_dir_literal(line: &str) -> Option<String> {
    let rest = line.trim().strip_prefix("srcDir")?.trim_start();
    let rest = rest
        .strip_prefix(":=")
        .or_else(|| rest.strip_prefix('='))?
        .trim();
    let body = rest.strip_prefix('"')?;
    let end = body.find('"')?;
    let tail = body[end + 1..].trim();
    // Only a lone literal, optionally followed by a line comment.
    if !(tail.is_empty() || tail.starts_with("--") || tail.starts_with('#')) {
        return None;
    }
    let dir = &body[..end];
    (!dir.contains('\\')).then(|| dir.to_owned())
}

#[cfg(test)]
mod tests {
    use super::{lean_module_name_for_file, src_dir_literal};
    use clean_kernel::Name;
    use std::fs;

    fn write(path: &std::path::Path, text: &str) {
        fs::create_dir_all(path.parent().expect("parent")).expect("dirs");
        fs::write(path, text).expect("write");
    }

    #[test]
    fn test_lean_module_name_src_dir_dot_names_from_the_root() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        write(
            &root.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage pkg where\nlean_lib Pkg where\n  srcDir := \".\"\n",
        );
        let file = root.join("Pkg/Sub/A.lean");
        write(&file, "def a := 1\n");
        // An absolute invocation gets the Lake name, not a path-derived one.
        assert_eq!(
            lean_module_name_for_file(&file),
            Some(Name::from_string("Pkg.Sub.A"))
        );
    }

    #[test]
    fn test_lean_module_name_src_dir_subdirectory_is_stripped() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        write(
            &root.join("lakefile.lean"),
            "package pkg where\n  srcDir := \"src\" -- sources\n",
        );
        let inside = root.join("src/Lib/B.lean");
        let outside = root.join("scripts/C.lean");
        write(&inside, "def b := 1\n");
        write(&outside, "def c := 1\n");
        assert_eq!(
            lean_module_name_for_file(&inside),
            Some(Name::from_string("Lib.B"))
        );
        assert_eq!(
            lean_module_name_for_file(&outside),
            Some(Name::from_string("scripts.C"))
        );
    }

    #[test]
    fn test_lean_module_name_toml_src_dir() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        write(
            &root.join("lakefile.toml"),
            "name = \"pkg\"\n[[lean_lib]]\nname = \"Lib\"\nsrcDir = \"lean\"\n",
        );
        let file = root.join("lean/Lib/D.lean");
        write(&file, "def d := 1\n");
        assert_eq!(
            lean_module_name_for_file(&file),
            Some(Name::from_string("Lib.D"))
        );
    }

    #[test]
    fn test_lean_module_name_without_lake_root_is_none() {
        let dir = tempfile::tempdir().expect("tempdir");
        let file = dir.path().join("Loose.lean");
        write(&file, "def l := 1\n");
        assert_eq!(crate::nearest_lake_root_for_file(&file), None);
        assert_eq!(lean_module_name_for_file(&file), None);
        assert_eq!(
            lean_module_name_for_file(&dir.path().join("Missing.lean")),
            None
        );
    }

    #[test]
    fn test_path_module_name_keeps_one_component_per_directory() {
        let name = super::path_module_name(std::path::Path::new("/tmp/.tmp9/501/A.lean"));
        assert_eq!(
            name,
            Name::anon().str("tmp").str(".tmp9").str("501").str("A")
        );
        assert_eq!(
            super::path_module_label(std::path::Path::new("./sub/Deep.lean")),
            "sub.Deep"
        );
    }

    #[test]
    fn test_src_dir_literal_accepts_only_a_lone_literal() {
        assert_eq!(
            src_dir_literal("  srcDir := \"src\""),
            Some("src".to_owned())
        );
        assert_eq!(
            src_dir_literal("srcDir = \"lean\" # toml"),
            Some("lean".to_owned())
        );
        assert_eq!(src_dir_literal("srcDir := \"a\" / \"b\""), None);
        assert_eq!(src_dir_literal("srcDirs := \"a\""), None);
        assert_eq!(src_dir_literal("-- srcDir := \"x\""), None);
    }
}
