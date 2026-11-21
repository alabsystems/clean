// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The search path a `clean lean` run imports through, and `--deps` /
//! `--src-deps`, which print what each header import resolves to on it.
//!
//! Lean's search path is `LEAN_PATH` followed by its own `lib/lean`. The
//! front door's is the same, with "its own" read as the library of the Lean
//! release it models (`~/.elan/toolchains/<release>/lib/lean`, found the way
//! `clean_olean` finds an installed toolchain and never installed by it). It
//! does not discover Lake packages: `lean FILE` does not either (`lake env
//! lean FILE` puts them on `LEAN_PATH`, which is read).
//!
//! Measured on `bin/lean --deps` (2026-10-16): one `.olean` path per import, in
//! header order, with the implicit `Init` first unless the file starts with
//! `prelude`; Lean 4.30.0-rc2 lists the implicit `Init` twice (its header has
//! `public import Init` and `public meta import Init`). An import that does
//! not resolve ends the listing with an error and exit status 1: 4.8.0 prints
//! `unknown package 'P'`; 4.30.0-rc2 prints `unknown module prefix 'P'` and the
//! search path. `--src-deps` (4.30.0-rc2) lists the `.lean` sources instead.

use super::dialect::LeanDialect;
use clean_kernel::name::NameInner;
use clean_olean::{ImportWorld, SourceWorldDecision};
use clean_parser::{Parser, SurfaceName};
use std::path::{Path, PathBuf};

/// `LEAN_PATH` followed by the modelled release's library. Stable Lean
/// preserves empty, missing and repeated entries in dependency diagnostics.
pub(crate) fn search_path(
    dialect: LeanDialect,
    decision: Option<&SourceWorldDecision>,
) -> Vec<PathBuf> {
    let mut paths = environment_paths("LEAN_PATH", dialect);
    if decision.is_none() {
        paths.retain(|path| path.exists());
    }
    if let Some(lib) = selected_library(dialect, decision) {
        if decision.is_some() || !paths.contains(&lib) {
            paths.push(lib);
        }
    }
    paths
}

fn environment_paths(variable: &str, dialect: LeanDialect) -> Vec<PathBuf> {
    let Some(value) = std::env::var_os(variable) else {
        return Vec::new();
    };
    // Unix environment values cross the same Lean String boundary as argv.
    #[cfg(unix)]
    let value = if dialect == LeanDialect::V4_36_0 {
        use std::os::unix::ffi::OsStringExt;
        std::ffi::OsString::from(super::stable_source_text(value.into_vec()))
    } else {
        value
    };
    #[cfg(not(unix))]
    let _ = dialect;
    std::env::split_paths(&value).collect()
}

fn selected_library(
    dialect: LeanDialect,
    decision: Option<&SourceWorldDecision>,
) -> Option<PathBuf> {
    match decision.map(SourceWorldDecision::imports) {
        Some(Ok(ImportWorld::Explicit { lib, .. })) => Some(lib.clone()),
        Some(_) => None,
        None => {
            let toolchain = format!("leanprover/lean4:v{}", dialect.version());
            clean_olean::installed_lean_lib_path(&toolchain)
        }
    }
}

/// Resolve Lean's SDK prefix through the physical executable.
pub(super) fn sdk_prefix_from_executable(prefix: &Path) -> Option<PathBuf> {
    let executable = prefix.join("bin/lean").canonicalize().ok()?;
    Some(executable.parent()?.parent()?.to_owned())
}

/// Modern Lean uses separate environment search paths for the two listings.
fn modern_dependency_paths(
    dialect: LeanDialect,
    decision: Option<&SourceWorldDecision>,
    sources: bool,
) -> Vec<PathBuf> {
    let variable = if sources {
        "LEAN_SRC_PATH"
    } else {
        "LEAN_PATH"
    };
    let mut paths = environment_paths(variable, dialect);
    if let Some(lib) = selected_library(dialect, decision) {
        if let Some(prefix) = lib.parent().and_then(Path::parent) {
            let prefix = sdk_prefix_from_executable(prefix).unwrap_or_else(|| {
                if dialect == LeanDialect::V4_36_0 {
                    prefix.canonicalize().unwrap_or_else(|_| prefix.to_owned())
                } else {
                    prefix.to_owned()
                }
            });
            if sources {
                let src = prefix.join("bin/../src/lean");
                paths.push(src.join("lake"));
                paths.push(src);
            } else {
                paths.push(prefix.join("lib/lean"));
            }
        }
    }
    paths
}

/// The modules a source's header imports, in order, the implicit `Init`
/// included (twice under 4.30.0-rc2, as it lists it).
pub(crate) fn header_imports(dialect: LeanDialect, source: &str) -> Vec<SurfaceName> {
    if dialect.is_modern() {
        let header = Parser::parse_dependency_header(source);
        let mut imports = Vec::new();
        if !header.is_prelude {
            imports.extend([
                SurfaceName::global_path("Init"),
                SurfaceName::global_path("Init"),
            ]);
        }
        imports.extend(header.imports);
        return imports;
    }

    // Lean 4.8 has no module-system header; preserve its separate dialect.
    let mut words = HeaderWords::new(source);
    let mut imports = Vec::new();
    let mut first = words.next();
    if first.as_deref() == Some("prelude") {
        first = words.next();
    } else {
        imports.push(SurfaceName::global_path("Init"));
    }
    let mut word = first;
    while let Some(current) = word {
        match current.as_str() {
            // 4.30 header modifiers: `public`, `meta`, `import all`.
            "public" | "meta" | "private" => word = words.next(),
            "import" => {
                let mut module = words.next();
                if matches!(module.as_deref(), Some("all") | Some("runtime")) {
                    module = words.next();
                }
                match module {
                    Some(module) => imports.push(SurfaceName::from_name(
                        module
                            .split('.')
                            .fold(clean_kernel::Name::anon(), |name, part| name.str(part)),
                    )),
                    None => break,
                }
                word = words.next();
            }
            _ => break,
        }
    }
    imports
}

/// Words of a module header, comments skipped.
struct HeaderWords<'a> {
    rest: &'a str,
}

impl<'a> HeaderWords<'a> {
    fn new(source: &'a str) -> Self {
        Self { rest: source }
    }

    fn skip_trivia(&mut self) {
        loop {
            self.rest = self.rest.trim_start();
            if let Some(after) = self.rest.strip_prefix("--") {
                self.rest = after.find('\n').map_or("", |at| &after[at..]);
            } else if self.rest.starts_with("/-") {
                let mut depth = 0usize;
                let mut end = self.rest.len();
                let bytes = self.rest.as_bytes();
                let mut at = 0;
                while at + 1 < bytes.len() {
                    if bytes[at] == b'/' && bytes[at + 1] == b'-' {
                        depth += 1;
                        at += 2;
                    } else if bytes[at] == b'-' && bytes[at + 1] == b'/' {
                        depth = depth.saturating_sub(1);
                        at += 2;
                        if depth == 0 {
                            end = at;
                            break;
                        }
                    } else {
                        at += 1;
                    }
                }
                self.rest = &self.rest[end..];
            } else {
                return;
            }
        }
    }
}

impl Iterator for HeaderWords<'_> {
    type Item = String;

    fn next(&mut self) -> Option<String> {
        self.skip_trivia();
        let end = self
            .rest
            .find(|c: char| c.is_whitespace())
            .unwrap_or(self.rest.len());
        if end == 0 {
            return None;
        }
        let word = self.rest[..end].to_owned();
        self.rest = &self.rest[end..];
        Some(word)
    }
}

/// Structural components, so a quoted component containing a dot stays whole.
fn module_components(module: &SurfaceName) -> Vec<String> {
    let mut name = module.name();
    let mut parts = Vec::new();
    loop {
        match name.inner() {
            NameInner::Anon => break,
            NameInner::Str(parent, part) => {
                parts.push(part.to_string());
                name = parent;
            }
            NameInner::Num(parent, part) => {
                parts.push(part.to_string());
                name = parent;
            }
        }
    }
    parts.reverse();
    parts
}

/// Preserve the 4.8 scanner's path behavior, including partial names.
fn legacy_module_path(root: &Path, module: &SurfaceName, extension: &str) -> PathBuf {
    let relative: PathBuf = module_components(module).into_iter().collect();
    root.join(relative).with_extension(extension)
}

/// `--deps` / `--src-deps`: the lines to print, and the error that ends the
/// listing, if any.
pub(crate) fn dependency_lines(
    dialect: LeanDialect,
    decision: Option<&SourceWorldDecision>,
    source: &str,
    sources: bool,
) -> (Vec<String>, Option<String>) {
    let modern = dialect.is_modern();
    let paths = if modern {
        modern_dependency_paths(dialect, decision, sources)
    } else {
        search_path(dialect, decision)
    };
    let extension = if modern && sources { "lean" } else { "olean" };
    let mut lines = Vec::new();
    for module in header_imports(dialect, source) {
        let found = if modern {
            clean_olean::lean_package_module_path(module.name(), &paths, extension)
                .ok()
                .flatten()
        } else {
            paths
                .iter()
                .map(|root| legacy_module_path(root, &module, "olean"))
                .find(|candidate| candidate.is_file())
        };
        match found {
            Some(path) => lines.push(path.display().to_string()),
            None => {
                return (
                    lines,
                    Some(unknown_module(dialect, &module, &paths, extension)),
                )
            }
        }
    }
    (lines, None)
}

fn unknown_module(
    dialect: LeanDialect,
    module: &SurfaceName,
    paths: &[PathBuf],
    extension: &str,
) -> String {
    let parts = module_components(module);
    // Lean's path errors render the root with `escape := false`.
    let prefix = parts.first().map_or("[anonymous]", String::as_str);
    if !dialect.is_modern() {
        return format!("unknown package '{prefix}'");
    }
    let entries: Vec<String> = paths.iter().map(|p| p.display().to_string()).collect();
    format!(
        "unknown module prefix '{prefix}'\n\nNo directory '{prefix}' or file '{prefix}.{extension}' in \
         the search path entries:\n{}",
        entries.join("\n")
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn names(dialect: LeanDialect, source: &str) -> Vec<String> {
        header_imports(dialect, source)
            .into_iter()
            .map(|module| module.name().to_string())
            .collect()
    }

    #[test]
    fn test_header_imports_follow_lean_listing() {
        let source = "/- c -/\n-- line\nimport Lean.Data.Json\nimport Std\n#eval 1";
        assert_eq!(
            names(LeanDialect::V4_8_0, source),
            vec!["Init", "Lean.Data.Json", "Std"]
        );
        assert_eq!(
            names(LeanDialect::V4_30_0Rc2, source),
            vec!["Init", "Init", "Lean.Data.Json", "Std"]
        );
        assert_eq!(
            names(LeanDialect::V4_30_0Rc2, "prelude\nimport Init.Prelude\n"),
            vec!["Init.Prelude"]
        );
        assert!(header_imports(LeanDialect::V4_8_0, "prelude\n").is_empty());
    }

    #[test]
    fn module_headers_retain_explicit_imports_and_prelude() {
        assert_eq!(
            names(LeanDialect::V4_30_0Rc2, "module\nimport Lean.Data.Json\n"),
            vec!["Init", "Init", "Lean.Data.Json"]
        );
        assert_eq!(
            names(
                LeanDialect::V4_30_0Rc2,
                "module\nprelude\nimport Lean.Data.Json\n"
            ),
            vec!["Lean.Data.Json"]
        );
        // A body identifier in 4.8, not the modern module marker.
        assert_eq!(
            names(
                LeanDialect::V4_8_0,
                "module\nprelude\nimport Lean.Data.Json\n"
            ),
            vec!["Init"]
        );
    }

    #[test]
    fn modern_dependencies_use_token_boundaries_and_stop_at_the_body() {
        assert_eq!(
            names(
                LeanDialect::V4_30_0Rc2,
                "module/- outer /- nested -/ end -/prelude\nmeta import all\nLean.Data.Json\ndef x := 1\nimport Std\n",
            ),
            vec!["Lean.Data.Json"]
        );
    }

    #[test]
    fn dependency_diagnostics_do_not_turn_into_source_admission() {
        assert_eq!(
            names(LeanDialect::V4_30_0Rc2, "public import Init\n"),
            vec!["Init", "Init", "Init"]
        );
        assert!(Parser::parse_header("public import Init\n").is_err());
        let malformed = "module\nprelude\nimport Init.Prelude\nimport all\n#eval 1\n";
        let imports = header_imports(LeanDialect::V4_30_0Rc2, malformed);
        assert_eq!(imports.len(), 2);
        assert!(imports[1].name().is_anon());
        assert!(clean_olean::lean_package_module_path(imports[1].name(), &[], "olean").is_err());
    }

    #[test]
    fn quoted_components_keep_embedded_dots_in_dependency_paths() {
        let imports = header_imports(
            LeanDialect::V4_30_0Rc2,
            "module\nprelude\nimport «A B».«C.D»\n",
        );
        assert_eq!(imports.len(), 1);
        let root = tempfile::tempdir().unwrap();
        std::fs::create_dir(root.path().join("A B")).unwrap();
        for extension in ["olean", "lean"] {
            let paths = [root.path().to_path_buf()];
            let found = clean_olean::lean_package_module_path(imports[0].name(), &paths, extension);
            assert_eq!(
                found.unwrap(),
                Some(root.path().join("A B").join(format!("C.D.{extension}")))
            );
        }
        assert!(
            unknown_module(LeanDialect::V4_30_0Rc2, &imports[0], &[], "olean")
                .starts_with("unknown module prefix 'A B'")
        );
        let dotted = header_imports(LeanDialect::V4_30_0Rc2, "prelude\nimport «A.B».C\n");
        assert!(
            unknown_module(LeanDialect::V4_30_0Rc2, &dotted[0], &[], "olean")
                .starts_with("unknown module prefix 'A.B'")
        );
    }

    #[test]
    fn legacy_dependency_components_preserve_numeric_text() {
        let imports = header_imports(LeanDialect::V4_8_0, "prelude\nimport A.01\n");
        assert_eq!(module_components(&imports[0]), vec!["A", "01"]);
        assert_eq!(
            legacy_module_path(Path::new("lib"), &imports[0], "olean"),
            PathBuf::from("lib/A/01.olean")
        );
        let partial = header_imports(LeanDialect::V4_8_0, "prelude\nimport A.\n");
        assert_eq!(
            legacy_module_path(Path::new("lib"), &partial[0], "olean"),
            PathBuf::from("lib/A.olean")
        );
        for source in ["prelude\nimport .\n", "prelude\nimport ..\n"] {
            let dots = header_imports(LeanDialect::V4_8_0, source);
            assert_eq!(
                legacy_module_path(Path::new("lib"), &dots[0], "olean"),
                PathBuf::from("lib.olean")
            );
        }
    }
}
