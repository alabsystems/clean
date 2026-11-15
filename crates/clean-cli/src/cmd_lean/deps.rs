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
use std::path::PathBuf;

/// `LEAN_PATH`'s existing entries, then the modelled release's library.
pub(crate) fn search_path(dialect: LeanDialect) -> Vec<PathBuf> {
    let mut paths: Vec<PathBuf> = std::env::var_os("LEAN_PATH")
        .map(|value| {
            std::env::split_paths(&value)
                .filter(|p| p.exists())
                .collect()
        })
        .unwrap_or_default();
    let toolchain = format!("leanprover/lean4:v{}", dialect.version());
    if let Some(lib) = clean_olean::installed_lean_lib_path(&toolchain) {
        if !paths.contains(&lib) {
            paths.push(lib);
        }
    }
    paths
}

/// The modules a source's header imports, in order, the implicit `Init`
/// included (twice under 4.30.0-rc2, as it lists it).
pub(crate) fn header_imports(dialect: LeanDialect, source: &str) -> Vec<String> {
    let mut words = HeaderWords::new(source);
    let mut imports = Vec::new();
    let mut first = words.next();
    if first.as_deref() == Some("prelude") {
        first = words.next();
    } else {
        imports.push("Init".to_owned());
        if dialect.is_modern() {
            imports.push("Init".to_owned());
        }
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
                    Some(module) => imports.push(module),
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

/// The file `module` resolves to with extension `ext` on `paths`.
fn resolve(paths: &[PathBuf], module: &str, ext: &str) -> Option<PathBuf> {
    let relative: PathBuf = module.split('.').collect();
    paths
        .iter()
        .map(|root| root.join(&relative).with_extension(ext))
        .find(|candidate| candidate.is_file())
}

/// The source of a module found in `lib` (`<prefix>/lib/lean`): Lean's
/// `<prefix>/src/lean`, else the `.lean` beside the root on `LEAN_SRC_PATH`.
fn resolve_source(paths: &[PathBuf], module: &str) -> Option<PathBuf> {
    let relative: PathBuf = module.split('.').collect();
    let src_roots = std::env::var_os("LEAN_SRC_PATH")
        .map(|value| std::env::split_paths(&value).collect::<Vec<_>>())
        .unwrap_or_default();
    let toolchain_src = paths
        .iter()
        // Spelled as Lean spells it, from its binary: `<prefix>/bin/../src/lean`.
        .filter_map(|lib| {
            lib.parent()?
                .parent()
                .map(|prefix| prefix.join("bin/../src/lean"))
        });
    src_roots
        .into_iter()
        .chain(toolchain_src)
        .map(|root| root.join(&relative).with_extension("lean"))
        .find(|candidate| candidate.is_file())
}

/// `--deps` / `--src-deps`: the lines to print, and the error that ends the
/// listing, if any.
pub(crate) fn dependency_lines(
    dialect: LeanDialect,
    source: &str,
    sources: bool,
) -> (Vec<String>, Option<String>) {
    let paths = search_path(dialect);
    let mut lines = Vec::new();
    for module in header_imports(dialect, source) {
        let found = if sources {
            resolve_source(&paths, &module)
        } else {
            resolve(&paths, &module, "olean")
        };
        match found {
            Some(path) => lines.push(path.display().to_string()),
            None => return (lines, Some(unknown_module(dialect, &module, &paths))),
        }
    }
    (lines, None)
}

fn unknown_module(dialect: LeanDialect, module: &str, paths: &[PathBuf]) -> String {
    let prefix = module.split('.').next().unwrap_or(module);
    if !dialect.is_modern() {
        return format!("unknown package '{prefix}'");
    }
    let entries: Vec<String> = paths.iter().map(|p| p.display().to_string()).collect();
    format!(
        "unknown module prefix '{prefix}'\n\nNo directory '{prefix}' or file '{prefix}.olean' in \
         the search path entries:\n{}",
        entries.join("\n")
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_header_imports_follow_lean_listing() {
        let source = "/- c -/\n-- line\nimport Lean.Data.Json\nimport Std\n#eval 1";
        assert_eq!(
            header_imports(LeanDialect::V4_8_0, source),
            vec!["Init", "Lean.Data.Json", "Std"]
        );
        assert_eq!(
            header_imports(LeanDialect::V4_30_0Rc2, source),
            vec!["Init", "Init", "Lean.Data.Json", "Std"]
        );
        assert_eq!(
            header_imports(LeanDialect::V4_30_0Rc2, "prelude\nimport Init.Prelude\n"),
            vec!["Init.Prelude"]
        );
        assert!(header_imports(LeanDialect::V4_8_0, "prelude\n").is_empty());
    }
}
