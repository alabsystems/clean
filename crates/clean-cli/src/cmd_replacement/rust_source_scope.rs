// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Which `crates/**/*.rs` files are PRODUCTION, asked of the compiler's
//! reachability rather than of a filename.
//!
//! **AUDIT r14 M14-11.** The `unchecked_decl_ratchet_accounted` lane has two
//! producers — `scripts/check_add_decl_ratchet.py` and
//! [`super::add_decl_bypass_scan`] — and the only arm holding them together
//! compared the SITES each found in today's tree. Two scanners that are blind
//! in the same place agree perfectly on that comparison. Measured, they were
//! not even blind in the same place: the Python side derived production
//! reachability (a `mod`/`#[path]`/`include!` edge reached without a `cfg` that
//! requires `test`) and the Rust side applied a filename predicate alone, so
//! `crates/clean-elab/tests/soundness_gate/{common,baseline}.rs` — 675 lines
//! compiled into a production `[[bin]]` that `scripts/kernel_soundness_gate.sh`
//! RUNS to mint launch evidence — were production to one producer and test code
//! to the other.
//!
//! This module is the Rust half of that one rule, mirroring `classify_paths`
//! in the Python sibling arm for arm. The two are held to the SAME SET, not to
//! the same outcome, by `add_decl_scan_scope_matches_the_python_producer`.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use walkdir::WalkDir;

/// A partition of `crates/**/*.rs` into what the compiler reaches without a
/// `test` gate and what it reaches only behind one.
pub(crate) struct SourceScope {
    pub(crate) production: BTreeSet<PathBuf>,
    /// Reached only through a `cfg`-that-requires-`test` edge, or named like a
    /// test file — and in both cases only where NO production edge reaches it.
    pub(crate) test_only: BTreeSet<PathBuf>,
    pub(crate) all: BTreeSet<PathBuf>,
}

impl SourceScope {
    /// The files a bypass scanner must read: production wins over every
    /// name-shaped exclusion.
    pub(crate) fn in_scope(&self, path: &Path) -> bool {
        self.production.contains(path) || !self.test_only.contains(path)
    }
}

/// True for test FILES by NAME only. Anchored forms exclusively: audit r11
/// M11-3 measured the unanchored `name.contains("test")` dropping 12 live
/// production files, `env/algebra_nat_testbit_*.rs` among them.
pub(crate) fn is_test_named(relative_path: &str) -> bool {
    let name = relative_path.rsplit('/').next().unwrap_or(relative_path);
    relative_path
        .split('/')
        .any(|p| p == "tests" || p == "tests2")
        || name.starts_with("test_")
        || name.starts_with("tests_")
        || name == "test.rs"
        || name == "tests.rs"
        || name.ends_with("_test.rs")
        || name.ends_with("_tests.rs")
}

/// Comment bytes blanked, string literals kept.
///
/// Mirrors `strip_comments_keep_strings`. A gate that reads Rust source must
/// blank comments first or it moves the WRONG WAY on a genuine fix, because
/// CLAUDE.md requires a `// SOUNDNESS:` comment naming the very call the site
/// makes.
pub(crate) fn blank_comments_keep_strings(src: &str) -> String {
    let b = src.as_bytes();
    let mut out = b.to_vec();
    let mut i = 0usize;
    let blank = |out: &mut Vec<u8>, from: usize, to: usize| {
        for byte in out.iter_mut().take(to).skip(from) {
            if *byte != b'\n' {
                *byte = b' ';
            }
        }
    };
    while i < b.len() {
        if b[i] == b'/' && i + 1 < b.len() && b[i + 1] == b'/' {
            let end = b[i..]
                .iter()
                .position(|&c| c == b'\n')
                .map_or(b.len(), |p| i + p);
            blank(&mut out, i, end);
            i = end;
        } else if b[i] == b'/' && i + 1 < b.len() && b[i + 1] == b'*' {
            let mut depth = 1usize;
            let mut j = i + 2;
            while j + 1 < b.len() && depth > 0 {
                if b[j] == b'/' && b[j + 1] == b'*' {
                    depth += 1;
                    j += 2;
                } else if b[j] == b'*' && b[j + 1] == b'/' {
                    depth -= 1;
                    j += 2;
                } else {
                    j += 1;
                }
            }
            let end = if depth == 0 { j } else { b.len() };
            blank(&mut out, i, end);
            i = end;
        } else if b[i] == b'r' && i + 1 < b.len() && (b[i + 1] == b'"' || b[i + 1] == b'#') {
            let mut hashes = 0usize;
            let mut j = i + 1;
            while j < b.len() && b[j] == b'#' {
                hashes += 1;
                j += 1;
            }
            if j < b.len() && b[j] == b'"' {
                j += 1;
                'raw: while j < b.len() {
                    if b[j] == b'"' {
                        let mut k = j + 1;
                        let mut seen = 0usize;
                        while k < b.len() && b[k] == b'#' && seen < hashes {
                            seen += 1;
                            k += 1;
                        }
                        if seen == hashes {
                            j = k;
                            break 'raw;
                        }
                    }
                    j += 1;
                }
                i = j;
            } else {
                i += 1;
            }
        } else if b[i] == b'"' {
            let mut j = i + 1;
            while j < b.len() {
                if b[j] == b'\\' {
                    j += 2;
                    continue;
                }
                if b[j] == b'"' {
                    j += 1;
                    break;
                }
                j += 1;
            }
            i = j;
        } else {
            i += 1;
        }
    }
    String::from_utf8_lossy(&out).into_owned()
}

/// Split on commas at paren depth zero.
fn split_top(args: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut start = 0usize;
    for (idx, ch) in args.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => depth -= 1,
            ',' if depth == 0 => {
                out.push(args[start..idx].trim());
                start = idx + 1;
            }
            _ => {}
        }
    }
    let tail = args[start..].trim();
    if !tail.is_empty() {
        out.push(tail);
    }
    out.retain(|p| !p.is_empty());
    out
}

/// A cfg predicate as a tree.
enum Cfg {
    Atom(String),
    Not(Vec<Cfg>),
    All(Vec<Cfg>),
    Any(Vec<Cfg>),
}

fn cfg_parse(body: &str) -> Cfg {
    let body = body.trim();
    for kind in ["all", "any", "not"] {
        if let Some(rest) = body.strip_prefix(kind) {
            let rest = rest.trim_start();
            if rest.starts_with('(') && rest.ends_with(')') {
                let children = split_top(&rest[1..rest.len() - 1])
                    .into_iter()
                    .map(cfg_parse)
                    .collect();
                return match kind {
                    "all" => Cfg::All(children),
                    "any" => Cfg::Any(children),
                    _ => Cfg::Not(children),
                };
            }
        }
    }
    Cfg::Atom(body.to_string())
}

fn cfg_atoms(node: &Cfg, out: &mut BTreeSet<String>) {
    match node {
        Cfg::Atom(a) => {
            if a != "test" {
                out.insert(a.clone());
            }
        }
        Cfg::Not(cs) | Cfg::All(cs) | Cfg::Any(cs) => {
            for c in cs {
                cfg_atoms(c, out);
            }
        }
    }
}

fn cfg_eval(node: &Cfg, env: &BTreeMap<String, bool>) -> bool {
    match node {
        Cfg::Atom(a) => {
            if a == "test" {
                false
            } else {
                env.get(a).copied().unwrap_or(false)
            }
        }
        Cfg::Not(cs) => !cs.iter().all(|c| cfg_eval(c, env)),
        Cfg::All(cs) => cs.iter().all(|c| cfg_eval(c, env)),
        Cfg::Any(cs) => cs.iter().any(|c| cfg_eval(c, env)),
    }
}

/// The most free atoms this will enumerate before answering PRODUCTION.
const CFG_ATOM_CAP: usize = 12;

/// Is an item under this cfg predicate unreachable whenever `test` is OFF?
///
/// AUDIT r15 M15-1, mirroring the Python sibling arm for arm. The r14 rule
/// dispatched on the outermost connective and then searched the unparsed
/// argument TEXT for the token `test`, which inverted the answer under
/// negation and read inside string literals: `all(not(test))` -- an item
/// compiled in every non-test build -- classified TEST-ONLY, as did
/// `all(unix, feature = "test-utils")`. A `mod` so guarded was dropped by this
/// producer AND by the Python one, which is why the set-equality arm between
/// them stayed green: they were blind in the same place, and a parity test
/// cannot see a shared blindness.
///
/// The rule is the definition, decided rather than pattern-matched: test-only
/// means the predicate is UNSATISFIABLE once `test` is false. Every non-`test`
/// atom is a free variable, so the question is settled by enumeration over the
/// atoms actually present -- which is correct under negation, as a token search
/// cannot be.
pub(crate) fn cfg_body_is_test_only(body: &str) -> bool {
    let tree = cfg_parse(body);
    let mut atoms = BTreeSet::new();
    cfg_atoms(&tree, &mut atoms);
    let atoms: Vec<String> = atoms.into_iter().collect();
    if atoms.len() > CFG_ATOM_CAP {
        // PRODUCTION rather than a guess: a file scanned needlessly costs
        // nothing, a file skipped needlessly is the hole this rule exists for.
        return false;
    }
    for mask in 0u32..(1u32 << atoms.len()) {
        let env: BTreeMap<String, bool> = atoms
            .iter()
            .enumerate()
            .map(|(i, a)| (a.clone(), mask & (1 << i) != 0))
            .collect();
        if cfg_eval(&tree, &env) {
            return false;
        }
    }
    true
}

fn cfg_attr_is_test_only(attr: &str) -> bool {
    let s = attr.trim_end().trim_end_matches(']').trim_end();
    let Some(cpos) = s.find("cfg") else {
        return false;
    };
    let rest = s[cpos + 3..].trim_start();
    if !rest.starts_with('(') || !rest.ends_with(')') {
        return false;
    }
    cfg_body_is_test_only(&rest[1..rest.len() - 1])
}

/// Is the item at `at` inside a contiguous attribute run that requires `test`?
///
/// Textual proximity is not the rule the compiler uses. Measured in the Python
/// sibling: a `#[cfg(test)] use std::fmt as _;` above an UNGUARDED `#[path]`
/// made the override vanish, and one blank line between a genuinely guarded
/// pair made a test include read as production.
pub(crate) fn attribute_run_is_cfg_test(src: &str, at: usize) -> bool {
    let mut head = &src[..at];
    loop {
        let trimmed = head.trim_end();
        if !trimmed.ends_with(']') {
            return false;
        }
        let Some(open) = trimmed.rfind("#[") else {
            return false;
        };
        let attr = &trimmed[open..];
        if attr[2..attr.len() - 1].contains(']') {
            return false;
        }
        if cfg_attr_is_test_only(attr) {
            return true;
        }
        head = &trimmed[..open];
    }
}

/// `mod NAME;` declarations, as (offset of the line start, name).
fn mod_declarations(src: &str) -> Vec<(usize, String)> {
    let mut out = Vec::new();
    let mut offset = 0usize;
    for line in src.split_inclusive('\n') {
        let body = line.trim_end_matches(['\n', '\r']);
        let stripped = body.trim_start_matches([' ', '\t']);
        let mut rest = stripped;
        if let Some(after) = rest.strip_prefix("pub") {
            let after = if after.starts_with('(') {
                match after.find(')') {
                    Some(close) => &after[close + 1..],
                    None => after,
                }
            } else {
                after
            };
            if after.starts_with([' ', '\t']) {
                rest = after.trim_start_matches([' ', '\t']);
            }
        }
        if let Some(after) = rest.strip_prefix("mod") {
            if after.starts_with([' ', '\t']) {
                let name: String = after
                    .trim_start_matches([' ', '\t'])
                    .chars()
                    .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                    .collect();
                let tail =
                    after.trim_start_matches([' ', '\t'])[name.len()..].trim_matches([' ', '\t']);
                if !name.is_empty() && tail == ";" {
                    out.push((offset, name));
                }
            }
        }
        offset += line.len();
    }
    out
}

/// A quoted target and the offset of the construct that names it, for every
/// `#[path = ".."]` and every `include!("..")`.
fn include_edges(src: &str) -> Vec<(usize, String)> {
    let mut out = Vec::new();
    for (marker, opener) in [("#[", "path"), ("include!", "")] {
        let mut from = 0usize;
        while let Some(rel) = src[from..].find(marker) {
            let at = from + rel;
            from = at + marker.len();
            let mut cursor = &src[at + marker.len()..];
            if marker == "#[" {
                cursor = cursor.trim_start();
                let Some(after) = cursor.strip_prefix(opener) else {
                    continue;
                };
                let after = after.trim_start();
                let Some(after) = after.strip_prefix('=') else {
                    continue;
                };
                cursor = after.trim_start();
            } else {
                cursor = cursor.trim_start();
                let Some(after) = cursor.strip_prefix('(') else {
                    continue;
                };
                cursor = after.trim_start();
            }
            if !cursor.starts_with('"') {
                continue;
            }
            let Some(close) = cursor[1..].find('"') else {
                continue;
            };
            out.push((at, cursor[1..1 + close].to_string()));
        }
    }
    out
}

/// Classify every `crates/**/*.rs` under `root`.
pub(crate) fn classify(root: &Path) -> SourceScope {
    let root = root.canonicalize().unwrap_or_else(|_| root.to_path_buf());
    let mut sources: BTreeMap<PathBuf, String> = BTreeMap::new();
    for entry in WalkDir::new(root.join("crates"))
        .into_iter()
        .filter_map(Result::ok)
        .filter(|e| e.path().extension().is_some_and(|x| x == "rs"))
    {
        let Ok(canon) = entry.path().canonicalize() else {
            continue;
        };
        let Ok(bytes) = std::fs::read(&canon) else {
            continue;
        };
        sources.insert(canon, String::from_utf8_lossy(&bytes).into_owned());
    }

    let mut production = BTreeSet::new();
    let mut guarded = BTreeSet::new();
    for (path, raw) in &sources {
        let Ok(rel) = path.strip_prefix(&root) else {
            continue;
        };
        if is_test_named(&rel.to_string_lossy().replace('\\', "/")) {
            continue;
        }
        let src = blank_comments_keep_strings(raw);
        let parent = match path.parent() {
            Some(p) => p.to_path_buf(),
            None => continue,
        };
        for (at, name) in mod_declarations(&src) {
            let guard = attribute_run_is_cfg_test(&src, at);
            for cand in [
                parent.join(format!("{name}.rs")),
                parent.join(&name).join("mod.rs"),
            ] {
                if let Ok(canon) = cand.canonicalize() {
                    if sources.contains_key(&canon) {
                        if guard {
                            guarded.insert(canon);
                        } else {
                            production.insert(canon);
                        }
                    }
                }
            }
        }
        for (at, target) in include_edges(&src) {
            let guard = attribute_run_is_cfg_test(&src, at);
            if let Ok(canon) = parent.join(&target).canonicalize() {
                if sources.contains_key(&canon) {
                    if guard {
                        guarded.insert(canon);
                    } else {
                        production.insert(canon);
                    }
                }
            }
        }
    }

    let mut test_only = BTreeSet::new();
    for path in sources.keys() {
        let rel = path
            .strip_prefix(&root)
            .map(|r| r.to_string_lossy().replace('\\', "/"))
            .unwrap_or_default();
        if !production.contains(path) && (guarded.contains(path) || is_test_named(&rel)) {
            test_only.insert(path.clone());
        }
    }

    SourceScope {
        all: sources.keys().cloned().collect(),
        production,
        test_only,
    }
}
