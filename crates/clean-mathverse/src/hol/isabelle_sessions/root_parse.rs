// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ROOT session-header scanning and per-entry theory topo-ordering.
//!
//! Faithful to the Python generator: the same regexes, the same
//! deterministic Kahn topo (stable by name, cycle fallback appends the
//! remainder sorted by name), the same "later duplicate basename wins"
//! file-map semantics.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::LazyLock;

use regex::Regex;

use super::{read_text_py, IsabelleSessionsError};

/// `session NAME (GROUP)? = PARENT +` — the afp-mode header scan
/// (`sess_re` in the Python).
static SESS_RE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(
        r#"session\s+"?([A-Za-z0-9_.\-]+)"?\s*(?:\([^)]*\))?\s*=\s*"?([A-Za-z0-9_.\-]+)"?\s*\+"#,
    )
    .expect("invariant: literal session regex compiles")
});

/// Wave-C variant that also tolerates an `in "dir"` clause
/// (`_SESS_RE_C` in the Python).
static SESS_RE_C: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(
        r#"session\s+"?([A-Za-z0-9_.\-]+)"?\s*(?:\([^)]*\))?\s*(?:in\s+"?[^=]*?"?\s*)?=\s*"?([A-Za-z0-9_.\-]+)"?\s*\+"#,
    )
    .expect("invariant: literal wave-C session regex compiles")
});

/// First `imports … begin` span of a theory header.
static IMPORTS_RE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"(?s)\bimports\b(.*?)\bbegin\b").expect("invariant: literal imports regex compiles")
});

/// Theory-name tokens inside an `imports` span.
static TOKEN_RE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"[A-Za-z0-9_.\-]+").expect("invariant: literal token regex compiles")
});

/// One `session NAME = PARENT +` header found in a ROOT file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RootSessionHeader {
    /// Session name.
    pub(crate) name: String,
    /// Base (parent) session.
    pub(crate) parent: String,
}

/// Scan a ROOT file's text for session headers (afp-mode regex, no `in`
/// clause). Order of appearance is preserved.
pub(crate) fn parse_root_headers(text: &str) -> Vec<RootSessionHeader> {
    header_scan(&SESS_RE, text)
}

/// Scan a ROOT file's text for session headers with the wave-C regex
/// (tolerates `in "dir"`).
pub(crate) fn parse_root_headers_wavec(text: &str) -> Vec<RootSessionHeader> {
    header_scan(&SESS_RE_C, text)
}

fn header_scan(re: &Regex, text: &str) -> Vec<RootSessionHeader> {
    re.captures_iter(text)
        .map(|c| RootSessionHeader {
            name: c[1].to_string(),
            parent: c[2].to_string(),
        })
        .collect()
}

/// Whether `entry_theories_topo` recurses into subdirectories.
///
/// `TopLevelOnly` is used for the HOL-* spine sessions (Wave B), whose
/// session theory set is the top-level `.thy` files of `src/HOL/<Dir>`
/// (recursing would pull sibling sessions' `ex/` theories, which are NOT in
/// the spine session).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TheoryWalk {
    /// Walk the whole entry directory tree (AFP entries).
    Recursive,
    /// Only the immediate directory (HOL-* spine source dirs).
    TopLevelOnly,
}

/// All `.thy` basenames under `dir`, topo-sorted by intra-entry imports.
///
/// This is the TRUE per-process theory set that re-elaborates above the base
/// heap; capping by this count (not the ROOT umbrella list) is what actually
/// bounds cumulative `record_proofs=4` RSS per Poly/ML process — the Lib3
/// lesson. A downward-closed prefix of this order has all its intra-entry
/// imports in an earlier prefix (=> a parent heap), so chunked sub-sessions
/// resolve cleanly.
pub(crate) fn entry_theories_topo(
    dir: &Path,
    walk: TheoryWalk,
) -> Result<Vec<String>, IsabelleSessionsError> {
    let files = collect_thy_files(dir, walk)?;
    let names: BTreeSet<String> = files.keys().cloned().collect();
    let mut deps: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (name, path) in &files {
        let mut file_deps = BTreeSet::new();
        let text = read_text_py(path)?;
        if let Some(cap) = IMPORTS_RE.captures(&text) {
            for tok in TOKEN_RE.find_iter(&cap[1]) {
                let base = tok.as_str().rsplit('.').next().unwrap_or(tok.as_str());
                if names.contains(base) && base != name {
                    file_deps.insert(base.to_string());
                }
            }
        }
        deps.insert(name.clone(), file_deps);
    }
    Ok(kahn_topo(names.into_iter().collect(), &deps))
}

/// Map `.thy` basename → path. Later-walked duplicates override earlier ones
/// (the Python `files[name] = path` semantics); the walk order is made
/// deterministic by sorting directory entries by name.
fn collect_thy_files(
    dir: &Path,
    walk: TheoryWalk,
) -> Result<BTreeMap<String, PathBuf>, IsabelleSessionsError> {
    let mut files = BTreeMap::new();
    match walk {
        TheoryWalk::TopLevelOnly => {
            // Python used os.listdir here, which raises on a missing dir —
            // surface a typed error instead of an empty set.
            for entry in sorted_dir_entries(dir)? {
                insert_if_thy(&mut files, &entry);
            }
        }
        TheoryWalk::Recursive => {
            // Python used os.walk, which silently yields nothing for a
            // missing dir; the caller then reports "no theories parsed".
            if dir.is_dir() {
                walk_recursive(dir, &mut files)?;
            }
        }
    }
    Ok(files)
}

fn walk_recursive(
    dir: &Path,
    files: &mut BTreeMap<String, PathBuf>,
) -> Result<(), IsabelleSessionsError> {
    let mut subdirs = Vec::new();
    for entry in sorted_dir_entries(dir)? {
        if entry.is_dir() {
            subdirs.push(entry);
        } else {
            insert_if_thy(files, &entry);
        }
    }
    // Top-down like os.walk: this dir's files first, then subtrees.
    for sub in subdirs {
        walk_recursive(&sub, files)?;
    }
    Ok(())
}

/// Directory entries sorted by file name (deterministic walk order).
/// Symlinked directories are not followed (os.walk `followlinks=False`).
fn sorted_dir_entries(dir: &Path) -> Result<Vec<PathBuf>, IsabelleSessionsError> {
    let listing = fs::read_dir(dir).map_err(|source| IsabelleSessionsError::ListDir {
        path: dir.to_path_buf(),
        source,
    })?;
    let mut entries = Vec::new();
    for entry in listing {
        let entry = entry.map_err(|source| IsabelleSessionsError::ListDir {
            path: dir.to_path_buf(),
            source,
        })?;
        entries.push(entry.path());
    }
    entries.sort();
    Ok(entries)
}

fn insert_if_thy(files: &mut BTreeMap<String, PathBuf>, path: &Path) {
    if let Some(base) = path
        .file_name()
        .and_then(|n| n.to_str())
        .and_then(|n| n.strip_suffix(".thy"))
    {
        files.insert(base.to_string(), path.to_path_buf());
    }
}

/// Deterministic Kahn topo, byte-identical to the Python: repeated passes
/// over the name-sorted remainder, placing every node whose deps are already
/// placed (nodes placed earlier in the SAME pass count); on a stuck pass
/// (cycle / unresolved) the remainder is appended in name order.
fn kahn_topo(mut remaining: Vec<String>, deps: &BTreeMap<String, BTreeSet<String>>) -> Vec<String> {
    let mut order = Vec::with_capacity(remaining.len());
    let mut placed: BTreeSet<String> = BTreeSet::new();
    while !remaining.is_empty() {
        let mut progressed = false;
        for name in remaining.clone() {
            let ready = deps
                .get(&name)
                .is_none_or(|d| d.iter().all(|x| placed.contains(x)));
            if ready {
                placed.insert(name.clone());
                remaining.retain(|x| *x != name);
                order.push(name);
                progressed = true;
            }
        }
        if !progressed {
            order.append(&mut remaining);
            break;
        }
    }
    order
}

#[cfg(test)]
mod tests {
    use super::*;

    fn deps_of(pairs: &[(&str, &[&str])]) -> BTreeMap<String, BTreeSet<String>> {
        pairs
            .iter()
            .map(|(n, ds)| {
                (
                    (*n).to_string(),
                    ds.iter().map(|d| (*d).to_string()).collect(),
                )
            })
            .collect()
    }

    #[test]
    fn test_parse_root_headers_quoted_group_and_multiline() {
        let text = "session \"Foo\" (AFP) =\n  \"HOL-Library\" +\n  theories\n    A\n";
        let heads = parse_root_headers(text);
        assert_eq!(heads.len(), 1, "one session header expected");
        assert_eq!(heads[0].name, "Foo");
        assert_eq!(heads[0].parent, "HOL-Library");
    }

    #[test]
    fn test_parse_root_headers_afp_regex_rejects_in_clause() {
        let text = "session Tools in \"tools\" = HOL +\n";
        assert!(
            parse_root_headers(text).is_empty(),
            "afp-mode regex must not match `in \"dir\"` sessions (Python parity)"
        );
        let heads = parse_root_headers_wavec(text);
        assert_eq!(heads.len(), 1, "wave-C regex tolerates the `in` clause");
        assert_eq!(heads[0].name, "Tools");
        assert_eq!(heads[0].parent, "HOL");
    }

    #[test]
    fn test_kahn_topo_same_pass_placement_matches_python() {
        // Kappa's deps are placed earlier in the SAME pass — Python places
        // Kappa in that pass too.
        let deps = deps_of(&[
            ("Delta", &["Zeta"]),
            ("Epsilon", &["Zeta"]),
            ("Kappa", &["Delta", "Epsilon"]),
            ("Zeta", &[]),
        ]);
        let names: Vec<String> = deps.keys().cloned().collect();
        assert_eq!(
            kahn_topo(names, &deps),
            vec!["Zeta", "Delta", "Epsilon", "Kappa"]
        );
    }

    #[test]
    fn test_kahn_topo_cycle_appends_rest_by_name() {
        let deps = deps_of(&[("B_Cyc", &["A_Cyc"]), ("A_Cyc", &["B_Cyc"]), ("Solo", &[])]);
        let names: Vec<String> = deps.keys().cloned().collect();
        assert_eq!(kahn_topo(names, &deps), vec!["Solo", "A_Cyc", "B_Cyc"]);
    }
}
