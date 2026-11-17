// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The module tree, resolved the way rustc resolves it — the Rust half of
//! `classify_paths` in `scripts/check_add_decl_ratchet.py` (2026-11-16), arm
//! for arm; its header states the rule and the measurement that forced it.
//!
//! Roots come from Cargo's target layout. A walk from them carries, per module,
//! the directory `#[path]` resolves in, the directory `mod x;` looks in and
//! whether a cfg-requires-`test` gate has been crossed: a crate root, a
//! `mod.rs` and a `#[path]` target own their own directory, any other `x.rs`
//! reached by `mod x;` owns `x/`, and `include!` text inherits its includer's
//! directories. PRODUCTION is what the walk reaches with no gate crossed, plus
//! every target of an unguarded edge out of a file that is not test-only;
//! TEST-ONLY is what the walk reaches only through a gate (or from a test
//! root), or what is named like a test, and is never production. A file headed
//! `#![cfg(test)]` is gated from its first item, so it and what it declares
//! are test-only whatever reaches them.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::path::{Path, PathBuf};

use walkdir::WalkDir;

use super::lexer::{
    blank_both, headed_cfg_test, include_edges, may_declare_modules, mod_declarations, path_edges,
};
use super::{attribute_run_is_cfg_test, is_test_named, last_attribute, SourceScope};

/// One file's module edges. Each carries its target, whether its own
/// attribute run (or `cfg_attr` condition) requires `test`, and whether it
/// stands at brace depth zero, where the walk may resolve it.
#[derive(Default)]
struct Edges {
    /// (stem, gated, top level, has a default `x.rs` / `x/mod.rs` target)
    decls: Vec<(String, bool, bool, bool)>,
    /// (target, gated, top level), resolved against the `#[path]` directory
    paths: Vec<(String, bool, bool)>,
    /// (target, gated, top level), resolved beside the including file
    includes: Vec<(String, bool, bool)>,
}

/// Does the attribute run ending at `at` carry an unconditional `#[path = ..]`?
fn attribute_run_names_path(src: &str, at: usize) -> bool {
    let mut head = &src[..at];
    while let Some((open, attr)) = last_attribute(head) {
        if attr[2..]
            .trim_start()
            .strip_prefix("path")
            .is_some_and(|rest| rest.trim_start().starts_with('='))
        {
            return true;
        }
        head = &head[..open];
    }
    false
}

/// Brace depth of code-only text at each requested offset.
fn depths_at(code: &str, offsets: &BTreeSet<usize>) -> BTreeMap<usize, i64> {
    let mut out = BTreeMap::new();
    let (mut depth, mut prev) = (0i64, 0usize);
    for &off in offsets {
        for byte in code.as_bytes()[prev..off].iter() {
            match byte {
                b'{' => depth += 1,
                b'}' => depth -= 1,
                _ => {}
            }
        }
        prev = off;
        out.insert(off, depth);
    }
    out
}

fn module_edges(raw: &str) -> Edges {
    if !may_declare_modules(raw) {
        return Edges::default();
    }
    let (keep, full) = blank_both(raw);
    let code_at = |off: usize, first: u8| full.as_bytes().get(off) == Some(&first);
    let decls = mod_declarations(&full);
    let paths: Vec<_> = path_edges(&keep)
        .into_iter()
        .filter(|(off, _, _)| code_at(*off, b'#'))
        .collect();
    let includes: Vec<_> = include_edges(&keep)
        .into_iter()
        .filter(|(off, _)| code_at(*off, b'i'))
        .collect();
    let offsets: BTreeSet<usize> = decls
        .iter()
        .map(|(off, _)| *off)
        .chain(paths.iter().map(|(off, _, _)| *off))
        .chain(includes.iter().map(|(off, _)| *off))
        .collect();
    let depth = depths_at(&full, &offsets);
    let top = |off: &usize| depth.get(off) == Some(&0);
    Edges {
        decls: decls
            .into_iter()
            .map(|(off, stem)| {
                let gated = attribute_run_is_cfg_test(&keep, off);
                (
                    stem,
                    gated,
                    top(&off),
                    !attribute_run_names_path(&keep, off),
                )
            })
            .collect(),
        paths: paths
            .into_iter()
            .map(|(off, target, cond)| {
                let gated = cond || attribute_run_is_cfg_test(&keep, off);
                (target, gated, top(&off))
            })
            .collect(),
        includes: includes
            .into_iter()
            .map(|(off, target)| (target, attribute_run_is_cfg_test(&keep, off), top(&off)))
            .collect(),
    }
}

/// Is this file a Cargo target root by its path SHAPE, and of which kind?
#[derive(Clone, Copy, PartialEq, Eq)]
enum RootKind {
    Production,
    Test,
}

fn target_shape(path: &Path) -> Option<RootKind> {
    let parts: Vec<String> = path
        .iter()
        .map(|c| c.to_string_lossy().into_owned())
        .collect();
    let n = parts.len();
    let name = parts.last()?.as_str();
    if n >= 2 && parts[n - 2] == "src" && (name == "lib.rs" || name == "main.rs") {
        return Some(RootKind::Production);
    }
    if name == "build.rs" && path.parent().is_some_and(|p| p.join("src").is_dir()) {
        return Some(RootKind::Production);
    }
    let shapes: [(&[&str], RootKind); 4] = [
        (&["src", "bin"], RootKind::Production),
        (&["examples"], RootKind::Production),
        (&["benches"], RootKind::Production),
        (&["tests"], RootKind::Test),
    ];
    for (base, kind) in shapes {
        let k = base.len();
        if n > k && parts[n - 1 - k..n - 1] == *base {
            return Some(kind);
        }
        if n > k + 1 && name == "main.rs" && parts[n - 2 - k..n - 2] == *base {
            return Some(kind);
        }
    }
    None
}

/// A root inside a `tests` directory is a TEST root; any other root is
/// production whatever its file name.
fn target_root_kind(path: &Path, rel: &str) -> Option<RootKind> {
    let kind = target_shape(path)?;
    let mut dirs = rel.split('/').collect::<Vec<_>>();
    dirs.pop();
    if dirs.iter().any(|d| *d == "tests" || *d == "tests2") {
        return Some(RootKind::Test);
    }
    Some(kind)
}

/// Resolves a candidate path to the source file it names, once per path.
struct Resolver<'a> {
    sources: &'a BTreeMap<PathBuf, String>,
    cache: HashMap<PathBuf, Option<PathBuf>>,
}

impl Resolver<'_> {
    fn known(&mut self, candidate: PathBuf) -> Option<PathBuf> {
        let sources = self.sources;
        self.cache
            .entry(candidate)
            .or_insert_with_key(|c| c.canonicalize().ok().filter(|p| sources.contains_key(p)))
            .clone()
    }
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
    let rels: BTreeMap<&PathBuf, String> = sources
        .keys()
        .map(|p| {
            let rel = p.strip_prefix(&root).unwrap_or(p);
            (p, rel.to_string_lossy().replace('\\', "/"))
        })
        .collect();
    let named: BTreeSet<PathBuf> = rels
        .iter()
        .filter(|(_, rel)| is_test_named(rel))
        .map(|(p, _)| (*p).clone())
        .collect();
    // A file headed `#![cfg(test)]` is gated from its first item: no non-test
    // build compiles it or anything it declares, whatever reaches it.
    let headed: BTreeSet<PathBuf> = sources
        .iter()
        .filter(|(_, raw)| headed_cfg_test(raw))
        .map(|(p, _)| p.clone())
        .collect();
    let edges: BTreeMap<&PathBuf, Edges> = sources
        .iter()
        .map(|(p, raw)| (p, module_edges(raw)))
        .collect();
    let mut resolver = Resolver {
        sources: &sources,
        cache: HashMap::new(),
    };

    // The walk: (file, dir `#[path]` resolves in, dir `mod x;` looks in, gated).
    let mut work: Vec<(PathBuf, PathBuf, PathBuf, bool)> = Vec::new();
    for (path, rel) in &rels {
        if let (Some(kind), Some(parent)) = (target_root_kind(path, rel), path.parent()) {
            let dir = parent.to_path_buf();
            work.push(((*path).clone(), dir.clone(), dir, kind == RootKind::Test));
        }
    }
    let mut seen = HashSet::new();
    let mut reached: HashMap<PathBuf, (bool, bool)> = HashMap::new();
    let mut walked_dirs: HashMap<PathBuf, BTreeSet<PathBuf>> = HashMap::new();
    let mut path_dirs: HashMap<PathBuf, BTreeSet<PathBuf>> = HashMap::new();
    while let Some(state) = work.pop() {
        if !seen.insert(state.clone()) {
            continue;
        }
        let (path, pdir, mdir, gated) = state;
        let gated = gated || headed.contains(&path);
        let bits = reached.entry(path.clone()).or_default();
        if gated {
            bits.1 = true;
        } else {
            bits.0 = true;
        }
        walked_dirs
            .entry(path.clone())
            .or_default()
            .insert(mdir.clone());
        path_dirs
            .entry(path.clone())
            .or_default()
            .insert(pdir.clone());
        let Some(file_edges) = edges.get(&path) else {
            continue;
        };
        for (stem, guard, top, has_default) in &file_edges.decls {
            if !(*top && *has_default) {
                continue;
            }
            for cand in [
                mdir.join(format!("{stem}.rs")),
                mdir.join(stem).join("mod.rs"),
            ] {
                if let Some(target) = resolver.known(cand) {
                    let own = target.parent().map(Path::to_path_buf).unwrap_or_default();
                    work.push((target, own, mdir.join(stem), gated || *guard));
                }
            }
        }
        for (target, guard, top) in &file_edges.paths {
            if !*top {
                continue;
            }
            if let Some(target) = resolver.known(pdir.join(target)) {
                let own = target.parent().map(Path::to_path_buf).unwrap_or_default();
                work.push((target, own.clone(), own, gated || *guard));
            }
        }
        for (target, guard, top) in &file_edges.includes {
            if !*top {
                continue;
            }
            let beside = path.parent().map(Path::to_path_buf).unwrap_or_default();
            if let Some(target) = resolver.known(beside.join(target)) {
                work.push((target, pdir.clone(), mdir.clone(), gated || *guard));
            }
        }
    }
    let reached_open: BTreeSet<PathBuf> = reached
        .iter()
        .filter(|(_, bits)| bits.0)
        .map(|(p, _)| p.clone())
        .collect();
    let reached_gated_only: BTreeSet<PathBuf> = reached
        .iter()
        .filter(|(_, bits)| !bits.0)
        .map(|(p, _)| p.clone())
        .collect();

    // Production: the open walk, then every unguarded edge out of a file that
    // is not test-only, looked up loosely.
    let mut production = reached_open.clone();
    let mut pending: Vec<PathBuf> = sources
        .keys()
        .filter(|p| {
            !headed.contains(*p)
                && (reached_open.contains(*p)
                    || (!reached_gated_only.contains(*p) && !named.contains(*p)))
        })
        .cloned()
        .collect();
    let mut done = HashSet::new();
    while let Some(path) = pending.pop() {
        if !done.insert(path.clone()) {
            continue;
        }
        let Some(file_edges) = edges.get(&path) else {
            continue;
        };
        let parent = path.parent().map(Path::to_path_buf).unwrap_or_default();
        let stem = path
            .file_stem()
            .map(|s| s.to_os_string())
            .unwrap_or_default();
        let mut mdirs: BTreeSet<PathBuf> = [parent.clone(), parent.join(stem)].into();
        mdirs.extend(walked_dirs.get(&path).into_iter().flatten().cloned());
        let mut pdirs: BTreeSet<PathBuf> = [parent.clone()].into();
        pdirs.extend(path_dirs.get(&path).into_iter().flatten().cloned());
        let mut targets = Vec::new();
        for (stem, guard, _, _) in &file_edges.decls {
            if *guard {
                continue;
            }
            for dir in &mdirs {
                for cand in [
                    dir.join(format!("{stem}.rs")),
                    dir.join(stem).join("mod.rs"),
                ] {
                    targets.extend(resolver.known(cand));
                }
            }
        }
        for (target, guard, _) in &file_edges.paths {
            if !*guard {
                for dir in &pdirs {
                    targets.extend(resolver.known(dir.join(target)));
                }
            }
        }
        for (target, guard, _) in &file_edges.includes {
            if !*guard {
                targets.extend(resolver.known(parent.join(target)));
            }
        }
        for target in targets {
            if !done.contains(&target) && !headed.contains(&target) {
                pending.push(target.clone());
            }
            production.insert(target);
        }
    }

    // Test-only: gated-only or test-named, and never production; a headed file
    // is test-only whatever reaches it.
    let test_only: BTreeSet<PathBuf> = reached_gated_only
        .union(&named)
        .filter(|p| !production.contains(*p))
        .chain(headed.iter())
        .cloned()
        .collect();
    production.retain(|p| !headed.contains(p));
    SourceScope {
        all: sources.keys().cloned().collect(),
        production,
        test_only,
    }
}
