// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The packaging requirement for the Clean trust-ir backend, checked on the
//! REAL `clean` binary (two-language roadmap WS6.13; F-119 scout-lean B7/C3,
//! F-118 version identity).
//!
//! Lives here and not in `clean-cli` because cargo sets `CARGO_BIN_EXE_clean`
//! only for the package that declares the `clean` `[[bin]]` — this one — and
//! the requirement is about the SHIPPED binary, not the library. The
//! requirement itself is stated in `docs/PACKAGING_TRUST_IR_BACKEND.md` and
//! the `[workspace.metadata.atpkg]` recipe in the root `Cargo.toml`:
//!
//! 1. the shipped `clean` is built with `--features trust-ir-backend`, so
//!    `--emit trustir|trustir-bin|obj` exist;
//! 2. the pack ships a linkable runtime archive (`clean_runtime.o` +
//!    `runtime_extern.o` + the prelude-shims object) — written out by the
//!    binary itself through `clean native-runtime`;
//! 3. `clean --version` prints the git sha.
//!
//! The tests are split by cargo feature so BOTH builds are pinned:
//!
//! * with `trust-ir-backend` (the recipe's build): `--emit trustir-bin`
//!   emits a module `trust-ir validate` accepts — the positive;
//! * without it (a default build, the pre-WS6.13 pack): clap refuses the
//!   value with its named "invalid value" text, exit 2, never a panic — the
//!   negative twin. The `Trustir`/`TrustirBin`/`Obj` variants are
//!   `#[cfg(feature = "trust-ir-backend")]` in `clean_compiler::cli`, so the
//!   build has no emit path at all, which is the fail-closed outcome.
//!
//! The mutation control for the archive (drop `runtime_extern.o`; the link
//! must fail by exactly `clean_inc`) lives beside the archive builder in
//! `clean-native`'s `native_runtime` tests, where the member set is a
//! parameter; the CLI has no knob to produce a partial archive. Its
//! pack-level twin is here, under the feature: the import set of the shipped
//! binary's own emitted module is linked against the archive the same binary
//! writes, and with `runtime_extern.o` deleted the link fails by exactly the
//! forwarders that module imports
//! (`pack_link_without_runtime_extern_fails_by_exactly_the_imported_forwarders`).

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn clean_path() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_clean"))
}

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
        .expect("workspace root is two parents above crates/clean")
}

fn run_clean(args: &[&str], cwd: &Path) -> Output {
    Command::new(clean_path())
        .args(args)
        .current_dir(cwd)
        .env("CARGO_TERM_COLOR", "never")
        .output()
        .unwrap_or_else(|e| panic!("failed to spawn clean: {e}"))
}

fn stdout(out: &Output) -> String {
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn stderr(out: &Output) -> String {
    String::from_utf8_lossy(&out.stderr).into_owned()
}

/// The commit this test binary was built from — `git rev-parse HEAD` of the
/// repository that TRACKS `crates/clean-cli/build.rs` and whose HEAD commit
/// holds it — or `None` when the
/// sources are not tracked (a source tarball, or one unpacked inside some
/// other repository, whose HEAD is not this build's). The same predicate
/// `build.rs` stamps with (`crates/clean-cli/build_support/provenance.rs`),
/// pinned by `clean-cli`'s `build_provenance_tests`. Not a skip: the
/// `--version` test asserts a DIFFERENT exact outcome for `None`.
fn checkout_head() -> Option<String> {
    let root = workspace_root();
    let tracked = Command::new("git")
        .args([
            "ls-files",
            "--error-unmatch",
            "--",
            "crates/clean-cli/build.rs",
        ])
        .current_dir(&root)
        .output()
        .ok()?;
    if !tracked.status.success() {
        return None;
    }
    let out = Command::new("git")
        .args(["rev-parse", "--verify", "HEAD^{commit}"])
        .current_dir(&root)
        .output()
        .ok()?;
    if !out.status.success() {
        return None;
    }
    let sha = String::from_utf8_lossy(&out.stdout).trim().to_owned();
    if sha.len() != 40 || !sha.bytes().all(|b| b.is_ascii_hexdigit()) {
        return None;
    }
    // The commit itself must hold the build script (the index alone does
    // not: sources staged into a foreign repository are in its index).
    let committed = Command::new("git")
        .args([
            "cat-file",
            "-t",
            &format!("{sha}:./crates/clean-cli/build.rs"),
        ])
        .current_dir(&root)
        .output()
        .ok()?;
    (committed.status.success() && String::from_utf8_lossy(&committed.stdout).trim() == "blob")
        .then_some(sha)
}

/// Requirement 3 (F-118): the version string identifies the build.
#[test]
fn clean_version_prints_the_git_sha_of_the_build() {
    let out = run_clean(&["--version"], &workspace_root());
    assert!(
        out.status.success(),
        "clean --version failed: {}",
        stderr(&out)
    );
    let text = stdout(&out);
    let line = text.trim_end();
    let version = env!("CARGO_PKG_VERSION");
    match checkout_head() {
        Some(sha) => {
            let expected = format!("clean {version}+g{sha}");
            assert_eq!(
                line, expected,
                "clean --version must print the crate version plus the FULL git sha as \
                 `+g<sha>` build metadata (F-118: `clean 0.9.0` identifies no build)"
            );
        }
        None => {
            let expected =
                format!("clean {version} (git sha unknown: built without git provenance)");
            assert_eq!(
                line, expected,
                "a build without git provenance must say so instead of minting a fake sha"
            );
        }
    }
}

/// Requirement 2 (scout-lean C3): the shipped binary writes the runtime
/// archive for the host, with all three members, and names the link line.
#[test]
fn scout_lean_c3_native_runtime_writes_all_three_archive_members() {
    let dir = tempfile::tempdir().expect("tempdir");
    let out_dir = dir.path().join("runtime");
    let out = run_clean(
        &[
            "native-runtime",
            "--out-dir",
            out_dir.to_str().expect("utf8 path"),
        ],
        &workspace_root(),
    );
    assert!(
        out.status.success(),
        "clean native-runtime failed: stdout={} stderr={}",
        stdout(&out),
        stderr(&out)
    );
    for name in [
        "clean_runtime.h",
        "clean_runtime.c",
        "runtime_extern.c",
        "clean_prelude_shims.c",
        "clean_runtime.o",
        "runtime_extern.o",
        "clean_prelude_shims.o",
        "libclean_runtime.a",
    ] {
        assert!(out_dir.join(name).is_file(), "{name} must be written");
    }
    let text = stdout(&out);
    assert!(
        text.contains("members: clean_runtime.o runtime_extern.o clean_prelude_shims.o"),
        "the report must name every member: {text}"
    );
    assert!(
        text.contains("libclean_runtime.a -lm"),
        "the report must print the link line a consumer runs: {text}"
    );
    let listing = Command::new("ar")
        .arg("t")
        .arg(out_dir.join("libclean_runtime.a"))
        .output()
        .expect("spawn ar t");
    assert!(listing.status.success(), "ar t: {}", stderr(&listing));
    let members: Vec<String> = String::from_utf8_lossy(&listing.stdout)
        .lines()
        .map(|l| l.trim().to_owned())
        .filter(|l| l.ends_with(".o"))
        .collect();
    assert_eq!(
        members,
        [
            "clean_runtime.o",
            "runtime_extern.o",
            "clean_prelude_shims.o"
        ]
    );
}

#[test]
fn native_runtime_sources_only_writes_no_archive() {
    let dir = tempfile::tempdir().expect("tempdir");
    let out_dir = dir.path().join("src-only");
    let out = run_clean(
        &[
            "native-runtime",
            "--out-dir",
            out_dir.to_str().expect("utf8 path"),
            "--sources-only",
        ],
        &workspace_root(),
    );
    assert!(out.status.success(), "{}", stderr(&out));
    for name in [
        "clean_runtime.h",
        "clean_runtime.c",
        "runtime_extern.c",
        "clean_prelude_shims.c",
    ] {
        assert!(out_dir.join(name).is_file(), "{name} must be written");
    }
    assert!(!out_dir.join("libclean_runtime.a").exists());
    assert!(stdout(&out).contains("archive: not built (--sources-only)"));
}

/// The runtime products a run must never leave behind from an EARLIER run:
/// the archive and the three member objects.
const STALE_PRODUCTS: [&str; 4] = [
    "libclean_runtime.a",
    "clean_runtime.o",
    "runtime_extern.o",
    "clean_prelude_shims.o",
];

/// Seed `out_dir` with a stale archive and stale objects, as a directory an
/// earlier run (of possibly another binary) built in would hold.
fn seed_stale_products(out_dir: &Path) {
    std::fs::create_dir_all(out_dir).expect("create out dir");
    for name in STALE_PRODUCTS {
        std::fs::write(out_dir.join(name), b"!<arch>\nstale").expect("seed stale product");
    }
}

fn assert_no_stale_products(out_dir: &Path, when: &str) {
    for name in STALE_PRODUCTS {
        assert!(
            out_dir.join(name).symlink_metadata().is_err(),
            "{name} must not remain in the out-dir {when}"
        );
    }
}

/// Run `clean native-runtime --out-dir <out_dir>` with one tool override
/// pointing at a path that cannot launch. Seeds stale products first so
/// the assertion is about the directory a consumer would read, not only the
/// exit code.
fn native_runtime_with_unlaunchable_tool(var: &str) -> (tempfile::TempDir, PathBuf, Output) {
    let dir = tempfile::tempdir().expect("tempdir");
    let out_dir = dir.path().join("runtime");
    seed_stale_products(&out_dir);
    let missing = dir.path().join("no-such-tool");
    let out = Command::new(clean_path())
        .args([
            "native-runtime",
            "--out-dir",
            out_dir.to_str().expect("utf8 path"),
        ])
        .current_dir(workspace_root())
        .env("CARGO_TERM_COLOR", "never")
        .env(var, &missing)
        .output()
        .unwrap_or_else(|e| panic!("failed to spawn clean: {e}"));
    (dir, out_dir, out)
}

/// ADVERSARIAL (review): `--sources-only` into a directory an earlier run
/// BUILT in. The stale archive and objects — compiled, for all a consumer
/// can tell, by an older binary from older sources — must not sit beside
/// the fresh sources as if they were this run's products. Measured on the
/// first cut: `native-runtime --out-dir rt --sources-only` over a built
/// `rt/` left all eight files in place.
#[test]
fn native_runtime_sources_only_removes_stale_products_of_an_earlier_run() {
    let dir = tempfile::tempdir().expect("tempdir");
    let out_dir = dir.path().join("runtime");
    seed_stale_products(&out_dir);
    let out = run_clean(
        &[
            "native-runtime",
            "--out-dir",
            out_dir.to_str().expect("utf8 path"),
            "--sources-only",
        ],
        &workspace_root(),
    );
    assert!(out.status.success(), "{}", stderr(&out));
    assert_no_stale_products(&out_dir, "after --sources-only");
    let text = stdout(&out);
    for name in STALE_PRODUCTS {
        assert!(
            text.contains(&format!("removed stale: {}", out_dir.join(name).display())),
            "the report must name each removed product ({name}): {text}"
        );
    }
    for name in [
        "clean_runtime.h",
        "clean_runtime.c",
        "runtime_extern.c",
        "clean_prelude_shims.c",
    ] {
        assert!(out_dir.join(name).is_file(), "{name} must be written");
    }
}

/// ADVERSARIAL (review): a run that fails BEFORE any compile — no C compiler
/// resolvable at all (`CLEAN_CC`/`CC` unset, an empty `PATH`) — must still
/// leave no archive and no object. The first cut removed the stale archive
/// only after the tool lookups had succeeded, so exactly this failure kept
/// it. Env edits are confined to the child process.
#[test]
fn native_runtime_with_no_compiler_on_path_leaves_no_archive() {
    let dir = tempfile::tempdir().expect("tempdir");
    let out_dir = dir.path().join("runtime");
    seed_stale_products(&out_dir);
    let empty_path = dir.path().join("empty-path");
    std::fs::create_dir_all(&empty_path).expect("create empty PATH dir");
    let out = Command::new(clean_path())
        .args([
            "native-runtime",
            "--out-dir",
            out_dir.to_str().expect("utf8 path"),
        ])
        .current_dir(workspace_root())
        .env("CARGO_TERM_COLOR", "never")
        .env_remove("CLEAN_CC")
        .env_remove("CC")
        .env("PATH", &empty_path)
        .output()
        .unwrap_or_else(|e| panic!("failed to spawn clean: {e}"));
    assert!(
        !out.status.success(),
        "no resolvable compiler must fail the verb: stdout={}",
        stdout(&out)
    );
    let err = stderr(&out);
    assert!(
        err.contains("no C compiler found") && err.contains("CLEAN_CC"),
        "the error must say no compiler resolved and name the override: {err}"
    );
    assert!(!err.contains("panicked"), "not a panic: {err}");
    assert_no_stale_products(&out_dir, "after a build that found no compiler");
    assert!(out_dir.join("runtime_extern.c").is_file());
}

/// ADVERSARIAL (review): fail-closed on the REAL binary. `$CLEAN_CC` naming
/// a compiler that cannot launch is an error that names the override, exits
/// non-zero, and leaves NO archive — not even the stale one that was there
/// before, which a packer reading the directory would otherwise ship.
#[test]
fn native_runtime_with_an_unlaunchable_compiler_leaves_no_archive() {
    let (_dir, out_dir, out) = native_runtime_with_unlaunchable_tool("CLEAN_CC");
    assert!(
        !out.status.success(),
        "an unlaunchable compiler must fail the verb: stdout={}",
        stdout(&out)
    );
    let err = stderr(&out);
    assert!(
        err.contains("failed to launch C compiler") && err.contains("no-such-tool"),
        "the error must name the launch failure and the tool: {err}"
    );
    assert!(!err.contains("panicked"), "not a panic: {err}");
    assert_no_stale_products(&out_dir, "after a build whose compiler could not launch");
    // The sources are still written (they precede the compile), so a packer
    // with its own toolchain can proceed from them.
    assert!(out_dir.join("clean_runtime.h").is_file());
    assert!(out_dir.join("runtime_extern.c").is_file());
}

/// The archiver twin: `$CLEAN_AR` naming a path that cannot launch fails
/// after the objects compiled, and still leaves no archive behind.
#[test]
fn native_runtime_with_an_unlaunchable_archiver_leaves_no_archive() {
    let (_dir, out_dir, out) = native_runtime_with_unlaunchable_tool("CLEAN_AR");
    assert!(
        !out.status.success(),
        "an unlaunchable archiver must fail the verb: stdout={}",
        stdout(&out)
    );
    let err = stderr(&out);
    assert!(
        err.contains("failed to launch archiver") && err.contains("no-such-tool"),
        "the error must name the launch failure and the tool: {err}"
    );
    assert!(!err.contains("panicked"), "not a panic: {err}");
    assert!(
        !out_dir.join("libclean_runtime.a").exists(),
        "no archive may remain after a failed build, stale or partial"
    );
    // The compile step ran with the real compiler before `ar` failed.
    assert!(out_dir.join("clean_runtime.o").is_file());
}

const FIXTURE: &str = "def demoId (x : Nat) : Nat := x\n";

fn write_fixture(dir: &Path) -> PathBuf {
    let file = dir.join("demo.lean");
    std::fs::write(&file, FIXTURE).expect("write fixture");
    file
}

/// Requirement 1, POSITIVE (scout-lean B7: "installed clean lacks
/// trust-ir-backend feature"): the feature build's `--emit trustir-bin`
/// writes a module `trust-ir validate` accepts.
#[cfg(feature = "trust-ir-backend")]
#[test]
fn scout_lean_b7_feature_build_emits_a_module_trust_ir_validate_accepts() {
    let dir = tempfile::tempdir().expect("tempdir");
    let file = write_fixture(dir.path());
    let artifact = dir.path().join("demo.bin");
    let out = run_clean(
        &[
            "compile",
            file.to_str().expect("utf8 path"),
            "--decl",
            "demoId",
            "--emit",
            "trustir-bin",
            "-o",
            artifact.to_str().expect("utf8 path"),
        ],
        &workspace_root(),
    );
    assert!(
        out.status.success(),
        "clean compile --emit trustir-bin failed: {}",
        stderr(&out)
    );
    let bytes = std::fs::read(&artifact).expect("artifact written");
    assert!(!bytes.is_empty());
    let functions = clean_compiler::emit_trust_ir::validate_module_bytes(&bytes)
        .unwrap_or_else(|errors| panic!("trust-ir validate must accept the artifact:\n{errors}"));
    assert!(functions > 0, "the module must carry the lowered function");
    // A well-formed module that merely DECLARED the root (an import with no
    // body) would pass the validator too; the requirement is that the
    // shipped binary lowered it.
    let module = clean_compiler::emit_trust_ir::deserialize_module_bytes(&bytes)
        .unwrap_or_else(|e| panic!("own bytes do not decode: {e}"));
    assert!(
        module
            .functions
            .iter()
            .any(|f| f.name == "demoId" && !f.blocks.is_empty()),
        "the root must be DEFINED (a body, not a bodyless declaration) in the emitted module"
    );
    // A trailing byte is refused, so the acceptance above was a real decode.
    let mut trailing = bytes.clone();
    trailing.push(0);
    assert!(clean_compiler::emit_trust_ir::validate_module_bytes(&trailing).is_err());
}

/// A fixture whose lowering demands BOTH kinds of link symbol: `l_*` prelude
/// shims (`l_Nat_add`, WS6.3's `l_Nat_land`) and the `clean_*` runtime
/// imports every `ExternCalls` module declares.
#[cfg(feature = "trust-ir-backend")]
const MASK_FIXTURE: &str = "def demoMask (x y : Nat) : Nat := (x + y) &&& 255\n";

/// Symbols the linker reports undefined (Mach-O leading `_` stripped): ld64's
/// `"_sym", referenced from:` and GNU ld's ``undefined reference to `sym'``.
/// A copy of `clean_native::native_build::link_probe::linker_undefined`, which
/// is crate-private test plumbing; kept in step by the same two grammars.
#[cfg(feature = "trust-ir-backend")]
fn linker_undefined(stderr: &str) -> std::collections::BTreeSet<String> {
    let mut out = std::collections::BTreeSet::new();
    for line in stderr.lines() {
        if let Some(q0) = line.find('"') {
            if let Some(q1) = line[q0 + 1..].find('"') {
                let inner = &line[q0 + 1..q0 + 1 + q1];
                if line.contains("referenced from") {
                    out.insert(inner.strip_prefix('_').unwrap_or(inner).to_owned());
                    continue;
                }
            }
        }
        if let Some(idx) = line.find("undefined reference to") {
            let rest = &line[idx..];
            if let (Some(b0), Some(b1)) = (rest.find('`'), rest.find('\'')) {
                if b0 < b1 {
                    out.insert(rest[b0 + 1..b1].to_owned());
                }
            }
        }
    }
    out
}

/// Link a C driver that retains every symbol in `demand` by address against
/// `archive` with `cc`; the undefined symbols the linker names (empty on
/// success). A failure naming none panics with the linker's stderr.
#[cfg(feature = "trust-ir-backend")]
fn link_demand_against(
    cc: &str,
    dir: &Path,
    archive: &Path,
    demand: &std::collections::BTreeSet<String>,
) -> std::collections::BTreeSet<String> {
    let prefix = if cfg!(target_vendor = "apple") {
        "_"
    } else {
        ""
    };
    let mut c = String::new();
    for (i, sym) in demand.iter().enumerate() {
        c.push_str(&format!(
            "extern void ref_{i}(void) __asm__(\"{prefix}{sym}\");\n"
        ));
    }
    c.push_str("int main(void) {\n");
    for i in 0..demand.len() {
        c.push_str(&format!(
            "  {{ void* volatile p = (void*)&ref_{i}; (void)p; }}\n"
        ));
    }
    c.push_str("  return 0;\n}\n");
    let driver = dir.join("driver.c");
    std::fs::write(&driver, c).expect("write driver");
    let link = Command::new(cc)
        .arg("-O0")
        .arg("-o")
        .arg(dir.join("driver"))
        .arg(&driver)
        .arg(archive)
        .arg("-lm")
        .output()
        .expect("spawn cc link");
    if link.status.success() {
        return std::collections::BTreeSet::new();
    }
    let text = String::from_utf8_lossy(&link.stderr);
    let undefined = linker_undefined(&text);
    assert!(
        !undefined.is_empty(),
        "link failed without naming an undefined symbol:\n{text}"
    );
    undefined
}

/// The shipped binary's emitted module plus the shipped binary's archive:
/// emit `MASK_FIXTURE` as `trustir-bin`, take every BODYLESS declaration the
/// module carries (the exact set an object lowered from it leaves for the
/// link), write the runtime archive with `clean native-runtime`, and return
/// the pieces.
#[cfg(feature = "trust-ir-backend")]
fn emitted_demand_and_archive() -> (
    tempfile::TempDir,
    String,
    PathBuf,
    std::collections::BTreeSet<String>,
) {
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("mask.lean");
    std::fs::write(&file, MASK_FIXTURE).expect("write fixture");
    let artifact = dir.path().join("mask.bin");
    let out = run_clean(
        &[
            "compile",
            file.to_str().expect("utf8 path"),
            "--decl",
            "demoMask",
            "--emit",
            "trustir-bin",
            "-o",
            artifact.to_str().expect("utf8 path"),
        ],
        &workspace_root(),
    );
    assert!(
        out.status.success(),
        "clean compile failed: {}",
        stderr(&out)
    );
    let bytes = std::fs::read(&artifact).expect("artifact written");
    let module = clean_compiler::emit_trust_ir::deserialize_module_bytes(&bytes)
        .unwrap_or_else(|e| panic!("own bytes do not decode: {e}"));
    let demand: std::collections::BTreeSet<String> = module
        .functions
        .iter()
        .filter(|f| f.blocks.is_empty())
        .map(|f| f.name.clone())
        .collect();
    for must in ["l_Nat_add", "l_Nat_land", "clean_inc", "clean_alloc_ctor"] {
        assert!(
            demand.contains(must),
            "the fixture's module must import {must}; it imports {demand:?}"
        );
    }
    assert!(
        module
            .functions
            .iter()
            .any(|f| f.name == "demoMask" && !f.blocks.is_empty()),
        "the root must be DEFINED in its own module"
    );

    let out_dir = dir.path().join("runtime");
    let out = run_clean(
        &[
            "native-runtime",
            "--out-dir",
            out_dir.to_str().expect("utf8 path"),
        ],
        &workspace_root(),
    );
    assert!(
        out.status.success(),
        "clean native-runtime failed: {}",
        stderr(&out)
    );
    // The compiler the binary itself used, from its own report line.
    let cc = stdout(&out)
        .lines()
        .find_map(|l| l.strip_prefix("link: "))
        .and_then(|l| l.split_whitespace().next())
        .expect("the report names the compiler on its `link:` line")
        .to_owned();
    (dir, cc, out_dir.join("libclean_runtime.a"), demand)
}

/// scout-lean C3 on the REAL pack shape, trust-cg-free (review): every
/// symbol the shipped binary's `--emit trustir-bin` module imports — the
/// `l_*` shims AND the `clean_*` runtime table — is defined by the archive
/// the same binary writes. This is the pack smoke's link step with the
/// emitted object replaced by a driver retaining the module's exact import
/// set; a shim missing from the tables (the WS6.3 `l_Nat_land` lag) or a
/// runtime entry the archive dropped fails here by name.
#[cfg(feature = "trust-ir-backend")]
#[test]
fn scout_lean_c3_emitted_module_imports_resolve_against_the_shipped_archive() {
    let (dir, cc, archive, demand) = emitted_demand_and_archive();
    let undefined = link_demand_against(&cc, dir.path(), &archive, &demand);
    assert!(
        undefined.is_empty(),
        "the shipped archive leaves imports of the shipped binary's own module undefined: \
         {undefined:?} (of {} demanded)",
        demand.len()
    );
}

/// MUTATION CONTROL at the pack level (the roadmap's: "remove
/// `runtime_extern.o` from the archive; the link step must fail by the exact
/// undefined symbol"): with that member deleted, the link of the emitted
/// module's import set fails by EXACTLY the forwarders `runtime_extern.c`
/// exports that the module imports — read from the source the binary wrote,
/// not hand-listed — and nothing else; `clean_inc` is among them.
#[cfg(feature = "trust-ir-backend")]
#[test]
fn pack_link_without_runtime_extern_fails_by_exactly_the_imported_forwarders() {
    let (dir, cc, archive, demand) = emitted_demand_and_archive();
    let extern_src = std::fs::read_to_string(dir.path().join("runtime").join("runtime_extern.c"))
        .expect("runtime_extern.c written by the binary");
    let forwarders: std::collections::BTreeSet<String> = extern_src
        .lines()
        .filter_map(|line| {
            let mut parts = line.strip_prefix("#define ")?.split_whitespace();
            let name = parts.next()?;
            let alias = parts.next()?;
            (name.starts_with("clean_")
                && alias.strip_prefix(name).is_some_and(|rest| rest == "__hdr"))
            .then(|| name.to_owned())
        })
        .collect();
    let expected: std::collections::BTreeSet<String> =
        demand.intersection(&forwarders).cloned().collect();
    assert!(
        expected.contains("clean_inc") && expected.len() >= 5,
        "the fixture must import several forwarders: {expected:?}"
    );
    let removed = Command::new("ar")
        .arg("d")
        .arg(&archive)
        .arg("runtime_extern.o")
        .output()
        .expect("spawn ar d");
    assert!(removed.status.success(), "ar d: {}", stderr(&removed));
    let undefined = link_demand_against(&cc, dir.path(), &archive, &demand);
    assert_eq!(
        undefined, expected,
        "without runtime_extern.o the link must fail by exactly the imported forwarders"
    );
}

/// The feature build exposes all three backend formats to clap.
#[cfg(feature = "trust-ir-backend")]
#[test]
fn feature_build_lists_the_backend_emit_formats() {
    let out = run_clean(&["compile", "-h"], &workspace_root());
    assert!(out.status.success(), "{}", stderr(&out));
    let help = stdout(&out);
    assert!(
        help.contains("[possible values: l5ir, l5cnf, c, rust, trustir, trustir-bin, obj]"),
        "the feature build must offer all seven emit formats: {help}"
    );
}

/// Requirement 1, NEGATIVE TWIN: a default build (no `trust-ir-backend`) has
/// no emit path for the backend formats at all, and clap refuses the value
/// by name — not a panic, not a silent fallback to another format.
#[cfg(not(feature = "trust-ir-backend"))]
#[test]
fn default_build_refuses_emit_trustir_bin_by_name() {
    let dir = tempfile::tempdir().expect("tempdir");
    let file = write_fixture(dir.path());
    let artifact = dir.path().join("demo.bin");
    let out = run_clean(
        &[
            "compile",
            file.to_str().expect("utf8 path"),
            "--decl",
            "demoId",
            "--emit",
            "trustir-bin",
            "-o",
            artifact.to_str().expect("utf8 path"),
        ],
        &workspace_root(),
    );
    assert_eq!(
        out.status.code(),
        Some(2),
        "clap's usage-error exit, not a panic (101) or success: stderr={}",
        stderr(&out)
    );
    let err = stderr(&out);
    assert!(
        err.contains("invalid value 'trustir-bin' for '--emit <EMIT>'"),
        "the refusal must name the value and the flag: {err}"
    );
    assert!(
        err.contains("[possible values: l5ir, l5cnf, c, rust]"),
        "the default build offers exactly the four text formats: {err}"
    );
    assert!(!artifact.exists(), "a refused emit must write nothing");
    assert!(
        !err.contains("panicked"),
        "the refusal must not be a panic: {err}"
    );
}

/// The default build's help offers none of the backend formats, so a packer
/// reading `clean compile -h` sees the gap rather than a flag that fails
/// later.
#[cfg(not(feature = "trust-ir-backend"))]
#[test]
fn default_build_does_not_offer_the_backend_emit_formats() {
    let out = run_clean(&["compile", "-h"], &workspace_root());
    assert!(out.status.success(), "{}", stderr(&out));
    let help = stdout(&out);
    assert!(
        help.contains("[possible values: l5ir, l5cnf, c, rust]"),
        "a default build offers exactly the four text formats: {help}"
    );
}
