// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parity battery row 16: the **native module-granular build** — the seam a
//! Clean-owned `cake build` needs in order to stop shelling out to Lean's
//! `lake`. Row semantics are pinned; see `parity_battery.rs`.

use std::path::{Path, PathBuf};

use clean_kernel::env::{ConstantKind, Declaration};
use clean_kernel::name::Name;
use clean_lake::{BuildContext, LakeError, Workspace};
use tempfile::TempDir;

use crate::common::*;

// ---------------------------------------------------------------------------
// Row 16 — build BY MODULE NAME, kernel-verify the emitted `.olean`, and pin
//          that the native build path spawns no external toolchain
// ---------------------------------------------------------------------------

/// Three things this row pins that no earlier row does.
///
/// **(a) Module-granular entry point.** Rows 01-03 build through
/// `build_all` / `build_target`, both of which resolve *lakefile target*
/// names. Lean's own Lake also accepts a **module** name (`lake build
/// Foo.Bar`), and `clean cake build` declares its work as a `modules` list —
/// so the missing piece between "clean-lake can build natively" and "Clean's
/// project manager stops calling `lake`" was a module-name entry point.
/// [`BuildContext::build_modules_named`] is it, and this row is its caller.
///
/// **(b) The emitted `.olean` is KERNEL-VERIFIED, not merely reloadable.**
/// Row 01 reloads the artifact and checks the two names are present — a
/// name-only export with a garbage body would satisfy that. Here every
/// declaration the module contributed is pulled back out of the reloaded
/// environment and **re-`add_decl`ed into a second, fresh prelude
/// environment**, which runs the live kernel over its type *and its value*.
/// The fixture is chosen so this discriminates: `native_eq` is a `theorem`
/// whose proof is `rfl` **through** `nativeVal`, so the kernel can only accept
/// it if the export carried the definitional body of `nativeVal` as well as
/// the proof term of `native_eq`.
///
/// **(c) No external toolchain process.** The claim "Clean built this without
/// Lean" is only worth as much as its check, so the row asserts *statically*
/// that every `Command::new` in `crates/clean-lake/src` names a literal
/// program and that the set of those programs is exactly `{"git"}` (the
/// require-fetcher). `lake`, `lean`, `leanc` and `elan` are named explicitly
/// as forbidden so a regression reads as such.
///
/// A dynamic form of (c) — prepend a shim directory holding a sentinel-writing
/// `lake` to `PATH` and assert the sentinel never appears — was written and
/// **rejected**: `std::env::set_var` mutates process-global state while the
/// other 15 rows run on sibling threads, and row 05 spawns `git` from one of
/// them. The static form is race-free, always runs, and fails on the same
/// regression.
#[test]
fn row16_named_module_build_kernel_verifies_and_spawns_no_toolchain() {
    let tmp = TempDir::new().expect("tempdir");
    write_file(
        &tmp.path().join("lakefile.toml"),
        "name = \"nativepkg\"\ndefaultTargets = [\"Native\"]\n\n\
         [[lean_lib]]\nname = \"Native\"\n",
    );
    write_file(
        &tmp.path().join("Native.lean"),
        "def nativeVal : Nat := 41 + 1\ntheorem native_eq : nativeVal = 42 := rfl\n",
    );

    // (a) Build by MODULE name, not by target name.
    let ws = Workspace::load(tmp.path()).expect("TOML workspace should load");
    let mut ctx = BuildContext::new(ws);
    let result = ctx
        .build_modules_named(&["Native".to_string()])
        .expect("build_modules_named should return a result");
    assert_eq!(sorted(result.built), vec!["Native"], "exact built set");
    assert!(result.skipped.is_empty(), "first build skips nothing");
    assert!(result.failed.is_empty(), "no failures: {:?}", result.failed);
    assert_olean_triple(ctx.workspace(), "Native");

    // (b) Kernel-verify the artifact: reload it, then re-check every
    // declaration it carries through the live kernel in a fresh environment.
    let lib_dir = ctx.workspace().lib_dir();
    // The module was built over genuine Init (Lean's implicit `import
    // Init`), and its artifact records that import: it reloads over, and is
    // re-checked in, a fresh copy of that Init.
    let mut reloaded = genuine_init_env();
    clean_olean::load_module_with_deps(&mut reloaded, "Native", &artifact_load_paths(&lib_dir))
        .expect("built .olean should reload");

    let mut recheck = genuine_init_env();
    // Dependency order: the theorem's proof reduces through the definition.
    for name in ["nativeVal", "native_eq"] {
        let n = Name::from_string(name);
        let info = reloaded
            .get_const(&n)
            .unwrap_or_else(|| panic!("{name} must round-trip through the exported .olean"))
            .clone();
        let value = info.value.clone().unwrap_or_else(|| {
            panic!(
                "{name} came back from the .olean with NO value (kind {:?}) — the export is \
                 name-only for this declaration, so nothing about it can be kernel-verified",
                info.kind
            )
        });
        let decl = match info.kind {
            ConstantKind::Theorem => Declaration::Theorem {
                name: info.name.clone(),
                level_params: info.level_params.clone(),
                type_: info.type_.clone(),
                value,
            },
            _ => Declaration::Definition {
                name: info.name.clone(),
                level_params: info.level_params.clone(),
                type_: info.type_.clone(),
                value,
                is_reducible: info.is_reducible,
            },
        };
        recheck.add_decl(decl).unwrap_or_else(|e| {
            panic!("the live kernel REJECTED {name} as reloaded from the emitted .olean: {e}")
        });
    }

    // Fail-closed: a module the workspace cannot provide is an error, never a
    // silent "0 built, 0 failed" that a caller would record as success.
    let ws2 = Workspace::load(tmp.path()).expect("TOML workspace should load");
    let mut ctx2 = BuildContext::new(ws2);
    let err = ctx2
        .build_modules_named(&["Native.NoSuchCleanLakeParityModule".to_string()])
        .expect_err("an unresolvable module name must fail closed");
    assert!(
        matches!(err, LakeError::ModuleNotFound(ref m) if m == "Native.NoSuchCleanLakeParityModule"),
        "pinned fail-closed variant, got: {err:?}"
    );

    // (c) Nothing in clean-lake's build path spawns a Lean toolchain.
    assert_only_git_is_spawned();
}

/// Programs `crates/clean-lake/src` is allowed to spawn. `git` is the
/// require-fetcher (`fetch.rs`); everything else is a regression.
const ALLOWED_SPAWNS: &[&str] = &["git"];

/// Programs whose appearance would mean Clean had delegated to Lean's own
/// toolchain. Listed explicitly so a failure names the actual sin.
const FORBIDDEN_SPAWNS: &[&str] = &["lake", "lean", "leanc", "elan", "lake.exe", "lean.exe"];

/// Assert that every `std::process::Command::new(...)` in this crate's source
/// names a **string literal** program, and that the set of those literals is
/// exactly [`ALLOWED_SPAWNS`].
///
/// Comments are blanked before matching (the repo's `source_scan` rule: a gate
/// that reads raw source counts *mentions*, and this file's own doc comment
/// mentions `Command::new("lake")`). String literals are deliberately **not**
/// blanked — here the literal is the payload being audited, not prose.
fn assert_only_git_is_spawned() {
    let src = crate_src_dir();
    let mut files = Vec::new();
    collect_rs_files(&src, &mut files);
    assert!(
        !files.is_empty(),
        "source scan found no .rs files under {} — the gate would be vacuous",
        src.display()
    );

    let mut found: Vec<(String, String)> = Vec::new();
    for file in &files {
        let Ok(text) = std::fs::read_to_string(file) else {
            panic!("source scan could not read {}", file.display());
        };
        let code = blank_comments(&text);
        let rel = file
            .strip_prefix(&src)
            .unwrap_or(file)
            .display()
            .to_string();
        for site in spawn_sites(&code) {
            match site {
                Some(program) => found.push((rel.clone(), program)),
                None => panic!(
                    "{rel}: a `Command::new(...)` site does not name a literal program, so this \
                     gate cannot tell whether clean-lake spawns a Lean toolchain. Either use a \
                     literal or extend the gate deliberately."
                ),
            }
        }
    }

    for (file, program) in &found {
        assert!(
            !FORBIDDEN_SPAWNS.contains(&program.as_str()),
            "{file} spawns `{program}`: clean-lake's build path must not delegate to the Lean \
             toolchain. `clean lake build` elaborating through Clean's own kernel is the whole \
             claim of this pillar."
        );
        assert!(
            ALLOWED_SPAWNS.contains(&program.as_str()),
            "{file} spawns `{program}`, which is not in the pinned allow-list {ALLOWED_SPAWNS:?}. \
             Adding a spawn to clean-lake needs the same justification as changing a ratchet \
             baseline."
        );
    }

    // Guard against the gate silently becoming vacuous (e.g. a refactor moves
    // every spawn behind a helper): the known `git` sites must still be seen.
    assert!(
        found.iter().any(|(_, p)| p == "git"),
        "source scan saw ZERO Command::new sites in clean-lake — the fetcher's `git` spawns \
         should be visible, so the scanner has stopped matching and proves nothing"
    );
}

/// `crates/clean-lake/src`, resolved from this integration test's manifest dir.
fn crate_src_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("src")
}

fn collect_rs_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    let mut sorted: Vec<_> = entries.filter_map(Result::ok).map(|e| e.path()).collect();
    sorted.sort();
    for path in sorted {
        if path.is_dir() {
            collect_rs_files(&path, out);
        } else if path.extension().and_then(|e| e.to_str()) == Some("rs") {
            out.push(path);
        }
    }
}

/// Replace `//`-line and `/* */`-block comment bodies with spaces, leaving
/// string literals intact (a `//` inside a string literal is not a comment).
fn blank_comments(src: &str) -> String {
    let bytes: Vec<char> = src.chars().collect();
    let mut out = String::with_capacity(src.len());
    let mut i = 0;
    let mut in_string = false;
    let mut in_char = false;
    while i < bytes.len() {
        let c = bytes[i];
        let next = bytes.get(i + 1).copied();
        if in_string {
            if c == '\\' {
                out.push(c);
                if let Some(n) = next {
                    out.push(n);
                }
                i += 2;
                continue;
            }
            if c == '"' {
                in_string = false;
            }
            out.push(c);
            i += 1;
            continue;
        }
        if in_char {
            if c == '\\' {
                out.push(c);
                if let Some(n) = next {
                    out.push(n);
                }
                i += 2;
                continue;
            }
            if c == '\'' {
                in_char = false;
            }
            out.push(c);
            i += 1;
            continue;
        }
        if c == '"' {
            in_string = true;
            out.push(c);
            i += 1;
            continue;
        }
        if c == '\'' && matches!(next, Some(n) if n != '_' && !n.is_alphabetic()) {
            // A char literal, not a lifetime.
            in_char = true;
            out.push(c);
            i += 1;
            continue;
        }
        if c == '/' && next == Some('/') {
            while i < bytes.len() && bytes[i] != '\n' {
                out.push(' ');
                i += 1;
            }
            continue;
        }
        if c == '/' && next == Some('*') {
            let mut depth = 1usize;
            out.push_str("  ");
            i += 2;
            while i < bytes.len() && depth > 0 {
                if bytes[i] == '/' && bytes.get(i + 1) == Some(&'*') {
                    depth += 1;
                    out.push_str("  ");
                    i += 2;
                } else if bytes[i] == '*' && bytes.get(i + 1) == Some(&'/') {
                    depth -= 1;
                    out.push_str("  ");
                    i += 2;
                } else {
                    out.push(if bytes[i] == '\n' { '\n' } else { ' ' });
                    i += 1;
                }
            }
            continue;
        }
        out.push(c);
        i += 1;
    }
    out
}

/// Every `Command::new(` site in `code`; `Some(program)` when the argument is
/// a plain string literal, `None` when it is anything else.
fn spawn_sites(code: &str) -> Vec<Option<String>> {
    const NEEDLE: &str = "Command::new(";
    let mut sites = Vec::new();
    let mut rest = code;
    while let Some(idx) = rest.find(NEEDLE) {
        let after = &rest[idx + NEEDLE.len()..];
        let trimmed = after.trim_start();
        if let Some(body) = trimmed.strip_prefix('"') {
            match body.find('"') {
                Some(end) => sites.push(Some(body[..end].to_string())),
                None => sites.push(None),
            }
        } else {
            sites.push(None);
        }
        rest = after;
    }
    sites
}
