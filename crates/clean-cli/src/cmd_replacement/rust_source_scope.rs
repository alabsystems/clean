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
//! the same outcome, by `add_decl_scan_scope_matches_the_python_producer`, and
//! each to the same table of known module-tree answers
//! (`the_module_tree_answers_every_layout_correctly`), which a parity arm
//! cannot replace: two producers blind in the same place agree.
//!
//! 2026-11-16: both halves resolve the MODULE TREE from Cargo's target roots
//! ([`module_tree`]) instead of looking for `mod x;` beside the declaring file.
//! Beside-the-file lookup cannot see that an ordinary `foo.rs` owns `foo/`, so
//! a module reached only through `#[cfg(test)] mod foo;` one file up was
//! scanned as production.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

mod lexer;
mod module_tree;

#[cfg(test)]
pub(crate) use lexer::{blank_both, headed_cfg_test};

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

/// Is this attribute a `cfg` whose predicate requires `test`? Anchored at the
/// attribute head (`#!?\[\s*cfg\s*\((.*)\)\s*\]?\s*$`): a tool path makes
/// `cfg` inert to rustc, so `#[rustfmt::cfg(test)]` is not a guard
/// (docs/issues/2026-11-16-python-rust-lexer-copies.md).
pub(crate) fn cfg_attr_is_test_only(attr: &str) -> bool {
    let s = attr.trim();
    let Some(rest) = s.strip_prefix("#!").or_else(|| s.strip_prefix('#')) else {
        return false;
    };
    let Some(rest) = rest.strip_prefix('[') else {
        return false;
    };
    let Some(rest) = rest.trim_start().strip_prefix("cfg") else {
        return false;
    };
    let Some(rest) = rest.trim_start().strip_prefix('(') else {
        return false;
    };
    let tail = rest.trim_end();
    let tail = tail.strip_suffix(']').unwrap_or(tail).trim_end();
    let Some(body) = tail.strip_suffix(')') else {
        return false;
    };
    cfg_body_is_test_only(body.trim())
}

/// The last attribute of the run that ends `head`, as (offset, text): the
/// Python sibling's `_ATTR_RUN_RE.search` (`#\[[^\]]*\]\s*\Z`), whose match
/// starts at the LEFTMOST `#[` after the previous `]`.
pub(crate) fn last_attribute(head: &str) -> Option<(usize, &str)> {
    let trimmed = head.trim_end();
    let close = trimmed.len().checked_sub(1)?;
    if trimmed.as_bytes()[close] != b']' {
        return None;
    }
    let from = trimmed[..close].rfind(']').map_or(0, |p| p + 1);
    let open = from + trimmed[from..close].find("#[")?;
    Some((open, &trimmed[open..]))
}

/// Is the item at `at` inside a contiguous attribute run that requires `test`?
///
/// Textual proximity is not the rule the compiler uses. Measured in the Python
/// sibling: a `#[cfg(test)] use std::fmt as _;` above an UNGUARDED `#[path]`
/// made the override vanish, and one blank line between a genuinely guarded
/// pair made a test include read as production.
pub(crate) fn attribute_run_is_cfg_test(src: &str, at: usize) -> bool {
    let mut head = &src[..at];
    while let Some((open, attr)) = last_attribute(head) {
        if cfg_attr_is_test_only(attr) {
            return true;
        }
        head = &head[..open];
    }
    false
}

/// Classify every `crates/**/*.rs` under `root` by the module tree rustc
/// compiles from each Cargo target root ([`module_tree`]).
pub(crate) fn classify(root: &Path) -> SourceScope {
    module_tree::classify(root)
}
