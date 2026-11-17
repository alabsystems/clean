// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fail-closed access to the repository-pinned Lean toolchain for tests that
//! need artifacts Lean itself produced.
//!
//! Every entry point PANICS rather than skips when the pinned toolchain is
//! absent, with the owner's spelling from `import/load_parse.rs`
//! (`companion_root_tests`): a run that cannot see the pinned Lean is a test
//! FAILURE, never a pass that executed zero test lines.
//!
//! The module is private. `test_support/mod.rs` re-exports exactly the items
//! consumers use — derived 2026-09-15 with `grep -rn "test_support::" crates`
//! over the six integration tests, four unit-test files and the one
//! `clean-compiler` test module that import it:
//!
//! * [`compiled_fixture_dir`] — compile one checked-in fixture family
//!   (`tests/fixtures/lean/<pin>/<family>/`) with the pinned `bin/lean`, once
//!   per content hash, into a cache under the cargo target dir, and return the
//!   directory holding the `.olean` artifacts.
//! * [`run_oracle`] — run the independent upstream dumper
//!   (`tests/fixtures/lean/<pin>/oracle/DumpOlean.lean`, documented in the
//!   README beside it) with the pinned binary and parse its JSON.
//! * [`fixture_root`] — `tests/fixtures/lean/<pin>`, for the one test that reads
//!   a family's declared design file (`typed_names/CONSTANTS`) directly.
//! * [`PINNED_LEAN_REQUIRED`] — the panic message, for a consumer's own
//!   `.expect` on [`crate::pinned_lean_binary`].
//!
//! # Fixture family layout
//!
//! `tests/fixtures/lean/<pin>/<family>/` holds `.lean` sources (sub-directories
//! for hierarchical module names), an `ORDER` file, and a `README.md`. `<pin>`
//! is the text after `:` in the workspace `lean-toolchain` (`v4.30.0-rc2`
//! today), derived at run time so a pin bump looks for fresh fixtures instead
//! of compiling last pin's sources with the new toolchain.
//!
//! `ORDER` lists one step per line, in dependency order:
//!
//! * `Module.part` — compile `Module.part.lean` to `Module.part.olean`
//!   (`lean --root . -o Module.part.olean Module.part.lean`; the module name is
//!   the quoted single component `«Module.part»`);
//! * `Module/part` — compile `Module/part.lean` to `Module/part.olean`
//!   (module name `Module.part`);
//! * `run <script.lean> <args...>` — `lean --run <script.lean> <args...>`, for
//!   generators that write their own artifacts (`writeModule`);
//! * `theory <name>` — copy the `.lean` sources of the theory
//!   `<workspace>/theories/<name>/` into the staging directory and compile its
//!   own `ORDER` there first (Compile steps only), so the family's modules can
//!   `import` the theory's; every file of the theory joins the cache key under
//!   `theory:<name>/<path>`. An import-only `CleanQualification.<name>` module
//!   then imports every one of those roots in ORDER sequence, for complete
//!   single-module `leanchecker --fresh` replay;
//! * `from <family> <stem>` — copy the sibling fixture family's
//!   `<family>/<stem>.lean` into the staging directory and compile it there, so
//!   two families share one source instead of each holding a copy (the
//!   `vf5_f1` family compiles the `semr` family's `SemR.lean`); the copied file
//!   joins the cache key under `from:<family>/<stem>.lean`, and it may not
//!   overwrite a file of the family;
//! * blank lines and `#` comments are ignored.
//!
//! Every step runs with the copied family directory as the working directory
//! and as the whole `LEAN_PATH`, so sibling modules resolve and the toolchain's
//! own stdlib resolves through the binary's sysroot. Measured 2026-09-15 with
//! the oracle's own `selftest` family: a `prelude` module compiles in well
//! under a second, a `module`-header source writes `.olean.server` and
//! `.olean.private` beside the base, and a plain (non-`module`) source writes
//! only the base `.olean`.
//!
//! # Content addressing
//!
//! The cache key is a BLAKE3 digest (the crate already depends on `blake3`)
//! over length-prefixed `(label, bytes)` records: [`RECIPE_VERSION`], the pinned
//! binary's `lean --version` line, then EVERY regular file under the family
//! directory — `ORDER`, the `.lean` sources, `README.md`, `CONSTANTS`,
//! `tools/*`, whatever is there — as `(relative path, bytes)` in sorted path
//! order. Until 2026-09-15 the key covered the version line, `ORDER` and
//! `*.lean` only, so an edit to any other file a recipe or a consumer reads
//! kept serving the directory built before the edit. Compilation happens in a
//! staging directory that is atomically renamed into place, so concurrent test
//! binaries either find the finished directory or build their own identical
//! copy; a crashed build leaves only a `*.tmp-*` directory behind.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{Mutex, OnceLock, PoisonError};

/// The owner's fail-closed spelling (`import/load_parse.rs`, `companion_root_tests`).
pub const PINNED_LEAN_REQUIRED: &str = "explicit pinned Lean fixture is required";
/// Per-family step list, one step per line (see the module documentation).
const ORDER_FILE: &str = "ORDER";
/// The independent upstream dumper, relative to [`fixture_root`].
const ORACLE_SCRIPT: &str = "oracle/DumpOlean.lean";
const CACHE_DIR_NAME: &str = "clean-olean-lean-fixtures";

/// Version of the compile RECIPE this module executes — part of every cache
/// key, because the key can see a family's files but not this code.
///
/// **Bump it whenever the way a step runs changes**: `run_lean`'s argv or
/// environment (`--root . -o`, `--run`, `LEAN_PATH`, the working directory),
/// how an [`OrderStep`] is parsed or executed, or what the staging copy holds.
/// Without the bump a key computed from unchanged files serves the OLD
/// recipe's output under the new code with no diagnostic; with it, the cost is
/// one recompile per family (well under a second each, measured 2026-09-15 on
/// the oracle's `selftest` family). `pinned_lean_tests` pins that the constant
/// is in the key.
///
/// History: `1` — 2026-09-15, the first keyed recipe: `lean --root . -o
/// <stem>.olean <stem>.lean` per `Compile` step, `lean --run <script> <args>`
/// per `Run` step, cwd = `LEAN_PATH` = the staging copy of the family.
/// `2` — 2026-10-26 (R162): the `Theory` step (a theory's `.lean` sources copied
/// into the staging directory and compiled by its own `ORDER` before the
/// family's steps); a family without a `theory` line runs as under `1`.
/// `3` — 2026-10-28: resolve a relative fixture cache before changing child cwd,
/// so LEAN_PATH names the same staging directory for sibling imports.
/// `4` — 2026-10-30: the `From` step (a sibling family's source copied into the
/// staging directory and compiled in its place); a family without a `from`
/// line runs as under `3`.
/// `5` — 2026-11-16: every Theory step also compiles an import-only
/// `CleanQualification.<theory>` aggregate from that theory's exact ORDER.
/// Independent ORDER roots are replayed together; a hand-written partial root
/// cannot silently stand in for the package. The deterministic aggregate is
/// bound by the recipe version and the already hashed theory ORDER bytes.
const RECIPE_VERSION: u32 = 5;

/// Every regular file of a family, `/`-separated path relative to the family
/// directory → bytes. `BTreeMap` so the hash order is the sorted path order.
type FamilyFiles = BTreeMap<String, Vec<u8>>;

static COMPILE_LOCK: Mutex<()> = Mutex::new(());
static LEAN_VERSION: OnceLock<String> = OnceLock::new();

/// One line of an `ORDER` file.
#[derive(Debug, Clone, PartialEq, Eq)]
enum OrderStep {
    /// `lean --root . -o <stem>.olean <stem>.lean`
    Compile(String),
    /// `lean --run <script> <args...>`
    Run(Vec<String>),
    /// `theory <name>`: the theory `<workspace>/theories/<name>/`, compiled first.
    Theory(String),
    /// `from <family> <stem>`: the sibling family's `<stem>.lean`, copied and compiled.
    From { family: String, stem: String },
}

/// The pinned `bin/lean`. Panics with [`PINNED_LEAN_REQUIRED`] when the
/// repository-pinned toolchain is not installed.
#[must_use]
fn pinned_lean_bin() -> PathBuf {
    crate::pinned_lean_binary().expect(PINNED_LEAN_REQUIRED)
}

fn manifest_dir() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
}

/// The Clean workspace root (two levels above this crate's manifest).
#[must_use]
fn workspace_root() -> PathBuf {
    manifest_dir()
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
        .unwrap_or_else(|| {
            panic!(
                "clean-olean manifest {} has no workspace root",
                manifest_dir().display()
            )
        })
}

/// The version half of the workspace `lean-toolchain` pin
/// (`leanprover/lean4:v4.30.0-rc2` → `v4.30.0-rc2`).
#[must_use]
fn pinned_toolchain_version() -> String {
    match std::env::var("CLEAN_LEAN_WORLD") {
        Err(std::env::VarError::NotPresent) => {}
        Err(std::env::VarError::NotUnicode(raw)) => {
            panic!("CLEAN_LEAN_WORLD must be UTF-8, not {raw:?}")
        }
        Ok(requested) => {
            let world = requested
                .parse::<clean_kernel::LeanWorld>()
                .unwrap_or_else(|error| panic!("{error}"));
            assert_eq!(world, clean_kernel::LeanWorld::ORACLE,
                "Lean world {world} has no oracle fixture-family contract; refusing to compile oracle fixtures in another world");
        }
    }
    let file = workspace_root().join("lean-toolchain");
    let raw = fs::read_to_string(&file)
        .unwrap_or_else(|error| panic!("cannot read {}: {error}", file.display()));
    let pin = raw.trim();
    let version = pin.rsplit_once(':').map_or(pin, |(_, version)| version);
    assert!(
        !version.is_empty(),
        "empty Lean toolchain pin in {}",
        file.display()
    );
    let world = version
        .parse::<clean_kernel::LeanWorld>()
        .unwrap_or_else(|error| panic!("{}: {error}", file.display()));
    assert_eq!(
        world,
        clean_kernel::LeanWorld::ORACLE,
        "fixture oracle and lean-toolchain disagree"
    );
    world.tag().to_string()
}

/// `crates/clean-olean/tests/fixtures/lean/<pin>`.
#[must_use]
pub fn fixture_root() -> PathBuf {
    manifest_dir()
        .join("tests")
        .join("fixtures")
        .join("lean")
        .join(pinned_toolchain_version())
}

/// `<workspace>/theories`: the importable Lean theories (R162).
#[must_use]
fn theory_root() -> PathBuf {
    workspace_root().join("theories")
}

/// `<CARGO_TARGET_DIR or <workspace>/target>/clean-olean-lean-fixtures`.
#[must_use]
fn cache_root() -> PathBuf {
    let target = std::env::var_os("CARGO_TARGET_DIR")
        .map_or_else(|| workspace_root().join("target"), PathBuf::from);
    // Keep the caller's existing path interpretation, but make it independent
    // of the Lean child's later cwd. The target may not exist yet, so it cannot
    // be canonicalized here. Absolute overrides and the workspace default stay put.
    let target = if target.is_absolute() {
        target
    } else {
        std::env::current_dir()
            .unwrap_or_else(|error| panic!("cannot resolve relative fixture cache: {error}"))
            .join(target)
    };
    target.join(CACHE_DIR_NAME)
}

/// The pinned binary's `lean --version` line, e.g.
/// `Lean (version 4.30.0-rc2, arm64-apple-darwin24.6.0, commit 3dc1a088b6d2…, Release)`.
/// Spawned once per process.
#[must_use]
fn pinned_lean_version() -> String {
    LEAN_VERSION
        .get_or_init(|| {
            let lean = pinned_lean_bin();
            let output = Command::new(&lean)
                .arg("--version")
                .output()
                .unwrap_or_else(|error| panic!("cannot execute {}: {error}", lean.display()));
            assert!(
                output.status.success(),
                "`{} --version` failed with {}: {}",
                lean.display(),
                output.status,
                String::from_utf8_lossy(&output.stderr)
            );
            String::from_utf8_lossy(&output.stdout).trim().to_string()
        })
        .clone()
}

/// Parse an `ORDER` file. Panics on a malformed line so a typo in a fixture
/// family fails the test that depends on it instead of compiling a subset.
#[must_use]
fn parse_order(text: &str) -> Vec<OrderStep> {
    let mut steps = Vec::new();
    for (index, raw) in text.lines().enumerate() {
        let line_number = index + 1;
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if let Some(rest) = line.strip_prefix("run ") {
            let words: Vec<String> = rest.split_whitespace().map(str::to_string).collect();
            assert!(
                !words.is_empty(),
                "{ORDER_FILE} line {line_number}: `run` needs a script"
            );
            steps.push(OrderStep::Run(words));
            continue;
        }
        if let Some(rest) = line.strip_prefix("theory ") {
            let name = rest.trim();
            assert!(
                !name.is_empty()
                    && name
                        .chars()
                        .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '-'),
                "{ORDER_FILE} line {line_number}: `theory` needs a theory directory name \
                 (`[A-Za-z0-9_-]+`), got `{rest}`"
            );
            steps.push(OrderStep::Theory(name.to_string()));
            continue;
        }
        if let Some(rest) = line.strip_prefix("from ") {
            let words: Vec<&str> = rest.split_whitespace().collect();
            let plain = |word: &str| {
                !word.is_empty()
                    && word
                        .chars()
                        .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '-')
            };
            assert!(
                words.len() == 2 && plain(words[0]) && plain(words[1]),
                "{ORDER_FILE} line {line_number}: `from` needs a sibling family name and a \
                 module stem (`[A-Za-z0-9_-]+` each), got `{rest}`"
            );
            steps.push(OrderStep::From {
                family: words[0].to_string(),
                stem: words[1].to_string(),
            });
            continue;
        }
        assert!(
            !line.contains(char::is_whitespace)
                && !line.ends_with(".lean")
                && !line.ends_with(".olean"),
            "{ORDER_FILE} line {line_number}: expected a bare module path stem \
             (`Module.part` or `Module/part`, no extension), got `{line}`"
        );
        steps.push(OrderStep::Compile(line.to_string()));
    }
    assert!(!steps.is_empty(), "{ORDER_FILE} lists no steps");
    steps
}

/// Every regular file under `root`, recursively, keyed by its `/`-separated
/// path relative to `root`. A symlink is refused rather than followed: its
/// bytes would be whatever it resolves to on this box, which no key may depend
/// on. `DirEntry::file_type` does not follow links, so the check is exact.
fn collect_family_files(root: &Path, dir: &Path, into: &mut FamilyFiles) {
    let entries =
        fs::read_dir(dir).unwrap_or_else(|error| panic!("cannot list {}: {error}", dir.display()));
    for entry in entries {
        let entry = entry
            .unwrap_or_else(|error| panic!("cannot read an entry of {}: {error}", dir.display()));
        let path = entry.path();
        let file_type = entry
            .file_type()
            .unwrap_or_else(|error| panic!("cannot stat {}: {error}", path.display()));
        assert!(
            !file_type.is_symlink(),
            "{} is a symlink; a fixture family holds regular files only",
            path.display()
        );
        if file_type.is_dir() {
            // A theory built in place by `lake build` holds its outputs in
            // `.lake/`; they are not sources and never join a key.
            if entry.file_name() == ".lake" {
                continue;
            }
            collect_family_files(root, &path, into);
            continue;
        }
        assert!(
            file_type.is_file(),
            "{} is neither a directory nor a regular file",
            path.display()
        );
        let relative = path
            .strip_prefix(root)
            .unwrap_or_else(|error| {
                panic!(
                    "{} is not under {}: {error}",
                    path.display(),
                    root.display()
                )
            })
            .to_string_lossy()
            .replace('\\', "/");
        let bytes = fs::read(&path)
            .unwrap_or_else(|error| panic!("cannot read {}: {error}", path.display()));
        into.insert(relative, bytes);
    }
}

fn copy_tree(from: &Path, to: &Path) {
    fs::create_dir_all(to)
        .unwrap_or_else(|error| panic!("cannot create {}: {error}", to.display()));
    let entries = fs::read_dir(from)
        .unwrap_or_else(|error| panic!("cannot list {}: {error}", from.display()));
    for entry in entries {
        let entry = entry
            .unwrap_or_else(|error| panic!("cannot read an entry of {}: {error}", from.display()));
        let source = entry.path();
        let target = to.join(entry.file_name());
        if source.is_dir() {
            copy_tree(&source, &target);
        } else {
            fs::copy(&source, &target).unwrap_or_else(|error| {
                panic!(
                    "cannot copy {} to {}: {error}",
                    source.display(),
                    target.display()
                )
            });
        }
    }
}

/// The cache key: [`content_hash_with_recipe`] at [`RECIPE_VERSION`].
#[must_use]
fn content_hash(lean_version: &str, files: &FamilyFiles) -> String {
    content_hash_with_recipe(RECIPE_VERSION, lean_version, files)
}

/// BLAKE3 over length-prefixed `(label, bytes)` records: the recipe version,
/// the toolchain version line, then every family file in sorted path order.
/// The first 32 hex digits (128 bits) name the cache directory.
#[must_use]
fn content_hash_with_recipe(recipe: u32, lean_version: &str, files: &FamilyFiles) -> String {
    let mut hasher = blake3::Hasher::new();
    let mut feed = |label: &str, bytes: &[u8]| {
        hasher.update(&(label.len() as u64).to_le_bytes());
        hasher.update(label.as_bytes());
        hasher.update(&(bytes.len() as u64).to_le_bytes());
        hasher.update(bytes);
    };
    feed("RECIPE_VERSION", &recipe.to_le_bytes());
    feed("lean --version", lean_version.as_bytes());
    for (path, bytes) in files {
        feed(path, bytes);
    }
    let hex = hasher.finalize().to_hex();
    hex.as_str()[..32].to_string()
}

/// One recipe step. Changing the argv or environment here is a
/// [`RECIPE_VERSION`] bump.
fn run_lean(lean: &Path, cwd: &Path, args: &[&str]) {
    let output = Command::new(lean)
        .current_dir(cwd)
        .env("LEAN_PATH", cwd)
        .args(args)
        .output()
        .unwrap_or_else(|error| panic!("cannot execute {}: {error}", lean.display()));
    assert!(
        output.status.success(),
        "`{} {}` in {} failed with {}\n--- stdout ---\n{}\n--- stderr ---\n{}",
        lean.display(),
        args.join(" "),
        cwd.display(),
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

/// A theory's source directory, every file of it (the cache key's input) and its
/// `ORDER`'s module stems. A theory's `ORDER` lists modules only: no `run`, no
/// nested `theory`.
fn theory_files_and_stems(name: &str) -> (PathBuf, FamilyFiles, Vec<String>) {
    let source = theory_root().join(name);
    assert!(
        source.is_dir(),
        "no Lean theory `{name}` at {}",
        source.display()
    );
    let mut files = FamilyFiles::new();
    collect_family_files(&source, &source, &mut files);
    let order = files.get(ORDER_FILE).unwrap_or_else(|| {
        panic!(
            "theory `{name}` at {} has no {ORDER_FILE}",
            source.display()
        )
    });
    let order = std::str::from_utf8(order).unwrap_or_else(|error| {
        panic!(
            "{} is not UTF-8: {error}",
            source.join(ORDER_FILE).display()
        )
    });
    let stems = parse_order(order)
        .into_iter()
        .map(|step| match step {
            OrderStep::Compile(stem) => stem,
            other => {
                panic!("theory `{name}`'s {ORDER_FILE} may list module stems only, got {other:?}")
            }
        })
        .collect();
    (source, files, stems)
}

/// Copy every `.lean` file under `from` to the same relative path under `to`,
/// refusing to overwrite: a theory's module may not shadow a family's.
fn copy_lean_sources(from: &Path, to: &Path) {
    let mut files = FamilyFiles::new();
    collect_family_files(from, from, &mut files);
    for relative in files.keys().filter(|path| path.ends_with(".lean")) {
        let target = to.join(relative);
        assert!(
            !target.exists(),
            "theory source {relative} would overwrite {}",
            target.display()
        );
        if let Some(parent) = target.parent() {
            fs::create_dir_all(parent)
                .unwrap_or_else(|error| panic!("cannot create {}: {error}", parent.display()));
        }
        fs::copy(from.join(relative), &target).unwrap_or_else(|error| {
            panic!("cannot copy {relative} to {}: {error}", target.display())
        });
    }
}

/// `lean --root . -o <stem>.olean <stem>.lean` in `staging`.
fn compile_stem(lean: &Path, staging: &Path, stem: &str, whose: &str) {
    let lean_source = format!("{stem}.lean");
    let olean = format!("{stem}.olean");
    assert!(
        staging.join(&lean_source).is_file(),
        "{ORDER_FILE} of {whose} names `{stem}` but there is no {lean_source}"
    );
    run_lean(
        lean,
        staging,
        &["--root", ".", "-o", olean.as_str(), lean_source.as_str()],
    );
}

/// One import-only root over the exact theory roster. The aggregate lives
/// outside every theory namespace and declares no subject of its own. Each
/// fixture family has its own staging graph, so legacy KCheck and labelled
/// KCheck declarations are never merged through these generated modules.
fn compile_theory_aggregate(lean: &Path, staging: &Path, name: &str, stems: &[String]) {
    assert!(
        !stems.is_empty(),
        "theory `{name}` has no qualification roots"
    );
    let stem = format!("CleanQualification/{name}");
    let target = staging.join(format!("{stem}.lean"));
    assert!(
        !target.exists(),
        "qualification aggregate would overwrite {}",
        target.display()
    );
    let mut source = String::from("prelude\n");
    for module in stems {
        source.push_str("import ");
        source.push_str(&module.replace('/', "."));
        source.push('\n');
    }
    fs::create_dir_all(target.parent().expect("aggregate parent"))
        .unwrap_or_else(|error| panic!("cannot create aggregate directory: {error}"));
    fs::write(&target, source)
        .unwrap_or_else(|error| panic!("cannot write {}: {error}", target.display()));
    compile_stem(lean, staging, &stem, &format!("theory `{name}` aggregate"));
}

/// Compile the fixture family `tests/fixtures/lean/<pin>/<family>/` with the
/// pinned Lean (once per content hash) and return the directory holding its
/// sources and the emitted `.olean` artifacts.
///
/// Panics — never skips — when the toolchain is absent, when the family or its
/// `ORDER` file is missing, or when any step exits non-zero (the panic message
/// carries Lean's stdout and stderr verbatim).
#[must_use]
pub fn compiled_fixture_dir(family: &str) -> PathBuf {
    let source = fixture_root().join(family);
    assert!(
        source.is_dir(),
        "no Lean fixture family `{family}` at {}",
        source.display()
    );
    let mut files = FamilyFiles::new();
    collect_family_files(&source, &source, &mut files);
    let order = files.get(ORDER_FILE).unwrap_or_else(|| {
        panic!(
            "fixture family `{family}` at {} has no {ORDER_FILE}",
            source.display()
        )
    });
    let order = std::str::from_utf8(order).unwrap_or_else(|error| {
        panic!(
            "{} is not UTF-8: {error}",
            source.join(ORDER_FILE).display()
        )
    });
    let steps = parse_order(order);
    let mut theories = Vec::new();
    for step in &steps {
        if let OrderStep::Theory(name) = step {
            let (theory_source, theory_files, stems) = theory_files_and_stems(name);
            for (path, bytes) in theory_files {
                files.insert(format!("theory:{name}/{path}"), bytes);
            }
            theories.push((name.clone(), theory_source, stems));
        }
        if let OrderStep::From {
            family: sibling,
            stem,
        } = step
        {
            assert!(
                sibling != family,
                "fixture family `{family}`'s {ORDER_FILE} names itself in a `from` line"
            );
            let path = fixture_root().join(sibling).join(format!("{stem}.lean"));
            let bytes = fs::read(&path).unwrap_or_else(|error| {
                panic!(
                    "fixture family `{family}`'s {ORDER_FILE} names {}: {error}",
                    path.display()
                )
            });
            files.insert(format!("from:{sibling}/{stem}.lean"), bytes);
        }
    }
    assert!(
        files.keys().any(|path| path.ends_with(".lean")),
        "fixture family `{family}` at {} has no .lean sources",
        source.display()
    );
    compile_cached(
        &family.replace(['/', '\\'], "_"),
        &source,
        &files,
        &steps,
        &theories,
    )
}

/// The cache and recipe: hash `files`, and on a miss copy the family into a
/// staging directory, run `steps` there (a `Theory` step from
/// `theories`), and publish it atomically.
fn compile_cached(
    tag: &str,
    family_source: &Path,
    files: &FamilyFiles,
    steps: &[OrderStep],
    theories: &[(String, PathBuf, Vec<String>)],
) -> PathBuf {
    let hash = content_hash(&pinned_lean_version(), files);
    let cache = cache_root();
    let published = cache.join(format!("{tag}-{hash}"));

    let _guard = COMPILE_LOCK.lock().unwrap_or_else(PoisonError::into_inner);
    if published.is_dir() {
        return published;
    }
    fs::create_dir_all(&cache)
        .unwrap_or_else(|error| panic!("cannot create {}: {error}", cache.display()));
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |elapsed| elapsed.as_nanos());
    let staging = cache.join(format!("{tag}-{hash}.tmp-{}-{nanos}", std::process::id()));
    if staging.exists() {
        fs::remove_dir_all(&staging)
            .unwrap_or_else(|error| panic!("cannot clear {}: {error}", staging.display()));
    }
    copy_tree(family_source, &staging);

    let lean = pinned_lean_bin();
    for step in steps {
        match step {
            OrderStep::Compile(stem) => compile_stem(&lean, &staging, stem, &format!("`{tag}`")),
            OrderStep::Run(words) => {
                let mut args: Vec<&str> = vec!["--run"];
                args.extend(words.iter().map(String::as_str));
                run_lean(&lean, &staging, &args);
            }
            OrderStep::From {
                family: sibling,
                stem,
            } => {
                let key = format!("from:{sibling}/{stem}.lean");
                let bytes = files
                    .get(&key)
                    .unwrap_or_else(|| panic!("`{key}` was not collected"));
                let target = staging.join(format!("{stem}.lean"));
                assert!(
                    !target.exists(),
                    "`from {sibling} {stem}` would overwrite {}",
                    target.display()
                );
                fs::write(&target, bytes)
                    .unwrap_or_else(|error| panic!("cannot write {}: {error}", target.display()));
                compile_stem(&lean, &staging, stem, &format!("`{tag}`"));
            }
            OrderStep::Theory(name) => {
                let (_, theory_source, stems) = theories
                    .iter()
                    .find(|(n, _, _)| n == name)
                    .unwrap_or_else(|| panic!("theory `{name}` was not collected"));
                copy_lean_sources(theory_source, &staging);
                for stem in stems {
                    compile_stem(&lean, &staging, stem, &format!("theory `{name}`"));
                }
                compile_theory_aggregate(&lean, &staging, name, stems);
            }
        }
    }

    if let Err(error) = fs::rename(&staging, &published) {
        // Another process finished the same content first; the two trees are
        // byte-identical by construction, so ours is redundant.
        assert!(
            published.is_dir(),
            "cannot publish compiled fixture {} as {}: {error}",
            staging.display(),
            published.display()
        );
        fs::remove_dir_all(&staging)
            .unwrap_or_else(|error| panic!("cannot remove {}: {error}", staging.display()));
    }
    published
}

/// Run `lean --run <fixture_root>/oracle/DumpOlean.lean <args...>` with the
/// pinned binary and parse its stdout as JSON.
///
/// Raw mode takes `.olean` part paths (`X.olean X.olean.server X.olean.private`
/// consecutively for one module); env mode takes
/// `--env <Module> --search-path <dir> [--name <Name>]...`. The schema is in
/// the oracle README. Panics with Lean's stderr on a non-zero exit and with the
/// first 2000 characters of stdout when the output is not JSON.
#[must_use]
pub fn run_oracle(args: &[&str]) -> serde_json::Value {
    let root = fixture_root();
    let script = root.join(ORACLE_SCRIPT);
    assert!(
        script.is_file(),
        "oracle dumper missing at {}",
        script.display()
    );
    let lean = pinned_lean_bin();
    let output = Command::new(&lean)
        .current_dir(root)
        .arg("--run")
        .arg(&script)
        .args(args)
        .output()
        .unwrap_or_else(|error| panic!("cannot execute {}: {error}", lean.display()));
    assert!(
        output.status.success(),
        "`{} --run {} {}` failed with {}\n--- stdout ---\n{}\n--- stderr ---\n{}",
        lean.display(),
        script.display(),
        args.join(" "),
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
        let shown = String::from_utf8_lossy(&output.stdout);
        let head: String = shown.chars().take(2000).collect();
        panic!("oracle printed non-JSON ({error}); first 2000 characters:\n{head}")
    })
}

#[cfg(test)]
#[path = "pinned_lean_tests.rs"]
mod pinned_lean_tests;
