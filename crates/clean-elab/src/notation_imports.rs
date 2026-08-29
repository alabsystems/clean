// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Build the parser's notation environment from the modules a file imports.
//!
//! Clean's parser starts every file from an EMPTY notation registry, so a
//! Mathlib file can only use a symbol Clean hand-wrote into its builtin
//! grammar or that the file itself declares. Lean's notation is an environment
//! extension: `infixr:26 " ⥤ " => Functor`, declared once in
//! `Mathlib/CategoryTheory/Functor/Basic.lean`, is visible in every file that
//! transitively imports it. This module closes that gap for the source lane by
//! walking the import closure at the SOURCE level and handing the parser a
//! [`NotationSeed`].
//!
//! # The boundary of this lane, stated
//!
//! * **Source only.** Modules are resolved with
//!   [`crate::resolve_intra_project_import`], the same resolver the
//!   `clean check` front end and the native build use, and are read as `.lean`
//!   text. A module that resolves to no project-local source contributes
//!   nothing: `clean-olean` decodes no notation extension today, so the
//!   compiled lane is a separate brick, and Lean **core** (`Init.*`, `Std.*`,
//!   which live in the toolchain rather than the checkout) is covered by
//!   Clean's builtin grammar instead.
//! * **Notation commands only.** `notation` / `infix` / `infixl` / `infixr` /
//!   `prefix` / `postfix`. Not `syntax`, not `macro_rules`, not `notation3`.
//! * **No elaboration.** The closure is a line prescan
//!   ([`clean_parser::notation_seed`]); an imported module whose body Clean
//!   cannot yet parse still contributes its notation.
//!
//! # Cost
//!
//! The closure of a mid-depth Mathlib file is on the order of 10³ modules, each
//! read once — [`ImportNotationHarvester`] memoises by canonical path, so the
//! union is read, not the sum over import edges. [`MAX_MODULES`] bounds a
//! pathological closure and [`MAX_MODULE_BYTES`] bounds one file.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};

use clean_parser::notation_seed::{scan_imports, NotationSeed, SeededNotation};

/// Upper bound on modules read for one file's seed. Mathlib's deepest closures
/// are ~1,500 modules; this is a runaway guard, not a policy knob.
const MAX_MODULES: usize = 16_384;

/// Upper bound on the bytes read from any single module.
const MAX_MODULE_BYTES: u64 = 8 * 1024 * 1024;

/// Upper bound on import-chain depth. The walk is recursive (dependencies
/// first), so an adversarial or cyclic-on-disk chain must not be able to
/// exhaust the stack. Mathlib's longest chain is an order of magnitude below
/// this.
const MAX_DEPTH: usize = 512;

/// What one harvest read, for reporting.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct HarvestStats {
    /// Modules resolved to project-local source and read.
    pub modules_read: usize,
    /// Import edges whose module resolved to no project-local `.lean`.
    pub modules_unresolved: usize,
    /// Notation commands harvested.
    pub notations: usize,
}

/// What one module's source contributes, independent of who imported it.
#[derive(Clone)]
struct ModuleScan {
    /// The module names this module itself imports.
    imports: Vec<String>,
    /// The notation commands this module exports.
    notations: Vec<SeededNotation>,
}

/// Process-wide memo, keyed by canonical module path.
///
/// `check_file_body` recurses into a project's intra-project `.lean` imports,
/// and each recursion builds its own seed. Without this the closure would be
/// re-read once per importing file — O(files²) reads on a source-import lane.
/// With it, a module's source is read and scanned at most once per process.
fn module_scan_cache() -> &'static Mutex<HashMap<PathBuf, Option<ModuleScan>>> {
    static CACHE: OnceLock<Mutex<HashMap<PathBuf, Option<ModuleScan>>>> = OnceLock::new();
    CACHE.get_or_init(|| Mutex::new(HashMap::new()))
}

/// Scan one module's source (memoised). `None` means the file could not be
/// read within the size bound.
fn scan_module(path: &Path) -> Option<ModuleScan> {
    if let Ok(cache) = module_scan_cache().lock() {
        if let Some(hit) = cache.get(path) {
            return hit.clone();
        }
    }
    let scanned = read_bounded(path).map(|source| {
        let mut seed = NotationSeed::new();
        seed.harvest_module_source(&source);
        ModuleScan {
            imports: scan_imports(&source),
            notations: seed.entries().to_vec(),
        }
    });
    if let Ok(mut cache) = module_scan_cache().lock() {
        cache.insert(path.to_path_buf(), scanned.clone());
    }
    scanned
}

/// Walks a file's transitive import closure once, harvesting notation.
struct ImportNotationHarvester {
    seed: NotationSeed,
    visited: HashSet<PathBuf>,
    stats: HarvestStats,
}

impl ImportNotationHarvester {
    fn new() -> Self {
        Self {
            seed: NotationSeed::new(),
            visited: HashSet::new(),
            stats: HarvestStats::default(),
        }
    }

    /// Harvest `modules`, each resolved relative to `from`, depth first and
    /// **dependencies first**: a module's own imports are harvested before it
    /// is, so registration order follows the order Lean builds the environment
    /// in. Registration order is what the registry's overlap resolution sees.
    fn walk(&mut self, modules: &[String], from: &Path, depth: usize) {
        if depth > MAX_DEPTH {
            return;
        }
        for module in modules {
            if self.stats.modules_read >= MAX_MODULES {
                return;
            }
            let Some(resolved) = crate::resolve_intra_project_import(module, from) else {
                self.stats.modules_unresolved += 1;
                continue;
            };
            let canonical = resolved.canonicalize().unwrap_or(resolved);
            if !self.visited.insert(canonical.clone()) {
                continue;
            }
            let Some(scan) = scan_module(&canonical) else {
                continue;
            };
            self.stats.modules_read += 1;
            // Dependencies first.
            self.walk(&scan.imports, &canonical, depth + 1);
            for notation in scan.notations {
                self.seed.push(notation);
                self.stats.notations += 1;
            }
        }
    }
}

/// Read a module's source, refusing anything implausibly large.
fn read_bounded(path: &Path) -> Option<String> {
    let metadata = std::fs::metadata(path).ok()?;
    if metadata.len() > MAX_MODULE_BYTES {
        return None;
    }
    std::fs::read_to_string(path).ok()
}

/// Build the notation seed for `path`, whose text is `source`.
///
/// `path` is the importing file; imports resolve relative to it. The file's
/// OWN notation is not seeded — the parser registers that as it reads the
/// file, exactly as before.
pub fn seed_from_imports(path: &Path, source: &str) -> (NotationSeed, HarvestStats) {
    let modules = scan_imports(source);
    if modules.is_empty() {
        return (NotationSeed::new(), HarvestStats::default());
    }
    let mut harvester = ImportNotationHarvester::new();
    harvester.walk(&modules, path, 0);
    (harvester.seed, harvester.stats)
}

#[cfg(test)]
mod tests {
    use super::seed_from_imports;
    use std::fs;
    use tempfile::TempDir;

    /// Write `files` (relative path → contents) into a fresh temp project and
    /// return the directory.
    fn project(files: &[(&str, &str)]) -> TempDir {
        let dir = TempDir::new().expect("tempdir");
        for (rel, contents) in files {
            let path = dir.path().join(rel);
            if let Some(parent) = path.parent() {
                fs::create_dir_all(parent).expect("mkdir");
            }
            fs::write(&path, contents).expect("write");
        }
        dir
    }

    #[test]
    fn test_seed_from_imports_harvests_a_direct_import() {
        let dir = project(&[
            ("Lib/Defs.lean", "notation \"‖\" e \"‖\" => norm e\n"),
            ("Use.lean", "import Lib.Defs\ndef a : Nat := ‖n‖\n"),
        ]);
        let use_path = dir.path().join("Use.lean");
        let source = fs::read_to_string(&use_path).expect("read");
        let (seed, stats) = seed_from_imports(&use_path, &source);
        assert_eq!(stats.modules_read, 1);
        assert_eq!(seed.len(), 1, "the imported notation must be harvested");
    }

    #[test]
    fn test_seed_from_imports_is_transitive() {
        let dir = project(&[
            ("A.lean", "notation \"∞\" => Nat\n"),
            ("B.lean", "import A\nnotation \"⊤\" => Top.top\n"),
            ("C.lean", "import B\ndef c : Type := ∞\n"),
        ]);
        let c = dir.path().join("C.lean");
        let source = fs::read_to_string(&c).expect("read");
        let (seed, stats) = seed_from_imports(&c, &source);
        assert_eq!(stats.modules_read, 2, "B and its own import A");
        assert_eq!(seed.len(), 2);
    }

    #[test]
    fn test_seed_from_imports_reads_a_shared_module_once() {
        let dir = project(&[
            ("Shared.lean", "notation \"∞\" => Nat\n"),
            ("L.lean", "import Shared\n"),
            ("R.lean", "import Shared\n"),
            ("Top.lean", "import L\nimport R\ndef t : Type := ∞\n"),
        ]);
        let top = dir.path().join("Top.lean");
        let source = fs::read_to_string(&top).expect("read");
        let (seed, stats) = seed_from_imports(&top, &source);
        assert_eq!(stats.modules_read, 3, "L, R and Shared — Shared once");
        assert_eq!(
            seed.len(),
            1,
            "the diamond must not register the same notation twice"
        );
    }

    #[test]
    fn test_seed_from_imports_survives_an_import_cycle() {
        // Lean forbids cycles, but the harvester must not recurse forever if
        // one is present on disk.
        let dir = project(&[
            ("P.lean", "import Q\nnotation \"∞\" => Nat\n"),
            ("Q.lean", "import P\n"),
            ("Root.lean", "import P\n"),
        ]);
        let root = dir.path().join("Root.lean");
        let source = fs::read_to_string(&root).expect("read");
        let (seed, stats) = seed_from_imports(&root, &source);
        assert_eq!(stats.modules_read, 2);
        assert_eq!(seed.len(), 1);
    }

    #[test]
    fn test_seed_from_imports_counts_an_unresolvable_module() {
        let dir = project(&[("Only.lean", "import Mathlib.Utterly.Fake\n")]);
        let only = dir.path().join("Only.lean");
        let source = fs::read_to_string(&only).expect("read");
        let (seed, stats) = seed_from_imports(&only, &source);
        assert_eq!(stats.modules_read, 0);
        assert_eq!(stats.modules_unresolved, 1);
        assert!(seed.is_empty());
    }

    #[test]
    fn test_seed_from_imports_on_a_file_with_no_imports_reads_nothing() {
        let dir = project(&[("Alone.lean", "def a : Nat := 1\n")]);
        let alone = dir.path().join("Alone.lean");
        let source = fs::read_to_string(&alone).expect("read");
        let (seed, stats) = seed_from_imports(&alone, &source);
        assert!(seed.is_empty());
        assert_eq!(stats, super::HarvestStats::default());
    }
}
