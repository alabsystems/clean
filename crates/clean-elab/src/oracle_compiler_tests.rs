// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// Admit the Trust toolchain running this test: the `trustc` beside `$CARGO`
/// (Targo exports it to tests), else beside the Targo that built this crate.
/// These tests need a Trust toolchain, and fail -- never skip -- without one.
fn admit_toolchain_trustc() -> OracleCompiler {
    let cargo =
        std::env::var_os("CARGO").map_or_else(|| PathBuf::from(env!("CARGO")), PathBuf::from);
    admit_beside(&cargo).unwrap_or_else(|err| {
        panic!("the oracle tests need the Trust toolchain's trustc beside {cargo:?}: {err}")
    })
}

/// [`admit_toolchain_trustc`], admitted once for the test process.
pub(crate) fn toolchain_trustc() -> &'static OracleCompiler {
    static TRUSTC: OnceLock<OracleCompiler> = OnceLock::new();
    TRUSTC.get_or_init(admit_toolchain_trustc)
}

/// A scratch directory with a `#!` script that records every run in `ran.log`
/// and prints a Trust identity on `-vV`.
fn impostor_script(dir: &Path) -> (PathBuf, PathBuf) {
    let script = dir.join("trustc");
    let log = dir.join("ran.log");
    std::fs::write(
        &script,
        format!(
            "#!/bin/sh\nprintf '%s\\n' \"$*\" >> '{}'\n\
             printf 'binary: trustc\\ncommit-hash: {}\\ntrust: 0.1.0\\n'\n",
            log.display(),
            "0".repeat(40)
        ),
    )
    .expect("write impostor");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&script, std::fs::Permissions::from_mode(0o755))
            .expect("chmod +x");
    }
    (script, log)
}

const SEAL_VV: &str = "rustc 1.99.0-dev (7d5533b2b 2026-09-23) (trustc 0.1.0)\n\
binary: trustc\n\
commit-hash: 7d5533b2bb9c9417bc09c27f1acd9d0b808f8f15\n\
commit-date: 2026-09-23\n\
host: aarch64-apple-darwin\n\
release: 1.99.0-dev\n\
trust: 0.1.0\n\
LLVM version: 22.1.2\n";

#[test]
fn trust_identity_needs_the_trustc_binary_line_the_trust_line_and_a_full_commit() {
    assert_eq!(
        trust_identity(SEAL_VV).as_deref(),
        Ok("7d5533b2bb9c9417bc09c27f1acd9d0b808f8f15")
    );
    let stock = "rustc 1.98.0 (88d9e12ae 2026-08-18)\nbinary: rustc\n\
                 commit-hash: 88d9e12ae178fab0fb5cc050a94da85685d449ea\n\
                 host: aarch64-apple-darwin\nrelease: 1.98.0\n";
    assert!(trust_identity(stock).is_err(), "stock rustc");
    let without_trust_line = SEAL_VV.replace("trust: 0.1.0\n", "");
    assert_eq!(trust_identity(&without_trust_line), Err("`trust:` line"));
    let rustc_alias = SEAL_VV.replace("binary: trustc", "binary: rustc");
    assert_eq!(trust_identity(&rustc_alias), Err("`binary: trustc` line"));
    let unknown_commit = SEAL_VV.replace("7d5533b2bb9c9417bc09c27f1acd9d0b808f8f15", "unknown");
    assert_eq!(
        trust_identity(&unknown_commit),
        Err("full `commit-hash:` line")
    );
    assert!(trust_identity("").is_err());
}

#[test]
fn stock_install_dirs_are_recognised_by_path() {
    for stock in [
        "$HOME/.rustup/toolchains/stable-aarch64-apple-darwin/bin/rustc",
        "$HOME/.cargo/bin/rustup",
        "/opt/homebrew/Cellar/rust/1.98.0/bin/rustc",
        "/usr/local/Cellar/rust/1.98.0/bin/rustc",
    ] {
        assert!(in_stock_install_dir(Path::new(stock)), "{stock}");
    }
    for trust in [
        "$HOME/toolchains/trust-7d5533b2/bin/trustc",
        "$HOME/Library/Application Support/aterm/pkg/store/trust/9192/bin/trustc",
        "$HOME/.cargo-like/bin/trustc",
    ] {
        assert!(!in_stock_install_dir(Path::new(trust)), "{trust}");
    }
}

/// A script is refused by its first bytes, so it is never run -- not even
/// for `-vV`, whatever it would print.
#[test]
fn a_script_is_refused_without_being_run() {
    let dir = tempfile::tempdir().expect("scratch dir");
    let (script, log) = impostor_script(dir.path());
    assert!(matches!(
        admit(&script),
        Err(OracleCompilerError::NotAnExecutable { .. })
    ));
    assert!(!log.exists(), "the refused script ran");
}

/// A native executable without Trust's identity is refused after `-vV`.
#[cfg(unix)]
#[test]
fn a_native_binary_without_trust_identity_is_refused() {
    let err = admit(Path::new("/usr/bin/true")).expect_err("`true` is not Trust");
    assert!(
        matches!(err, OracleCompilerError::NotTrust { .. }),
        "got {err}"
    );
}

/// Stock Rust as rustup installs it -- a toolchain `rustc`, the `~/.cargo/bin`
/// proxies -- is refused by its path, before it runs: a stand-in under each
/// directory shape always, and this machine's own rustup install where it has
/// one.
#[test]
fn rustup_stock_compilers_and_proxies_are_refused() {
    let dir = tempfile::tempdir().expect("scratch dir");
    let mut candidates = Vec::new();
    let mut logs = Vec::new();
    for shape in [
        ".rustup/toolchains/stable-aarch64-apple-darwin/bin",
        ".cargo/bin",
    ] {
        let bin = dir.path().join(shape);
        std::fs::create_dir_all(&bin).expect("stand-in dir");
        let (script, log) = impostor_script(&bin);
        candidates.push(script);
        logs.push(log);
    }
    let home = std::env::var_os("HOME")
        .map(PathBuf::from)
        .unwrap_or_default();
    candidates.extend(
        [
            ".cargo/bin/rustc",
            ".rustup/toolchains/stable-aarch64-apple-darwin/bin/rustc",
            ".rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin/rustc",
        ]
        .into_iter()
        .map(|installed| home.join(installed))
        .filter(|path| path.exists()),
    );
    for candidate in &candidates {
        let err = admit(candidate).expect_err("stock Rust admitted");
        assert!(
            matches!(err, OracleCompilerError::StockInstallDir { .. }),
            "{}: {err}",
            candidate.display()
        );
    }
    for log in &logs {
        assert!(!log.exists(), "a refused stand-in ran: {}", log.display());
    }
}

#[test]
fn an_explicit_setting_must_be_absolute_and_is_final() {
    assert!(matches!(
        resolve(Some(OsStr::new("trustc")), None),
        Err(OracleCompilerError::NotAbsolute { .. })
    ));
    // A refused explicit compiler is not replaced by the running executable's
    // sibling, even when that sibling would be admitted.
    let toolchain = toolchain_trustc();
    let dir = tempfile::tempdir().expect("scratch dir");
    let (script, _) = impostor_script(dir.path());
    assert!(matches!(
        resolve(Some(script.as_os_str()), Some(toolchain.path())),
        Err(OracleCompilerError::NotAnExecutable { .. })
    ));
}

#[test]
fn without_a_sibling_there_is_no_candidate() {
    let dir = tempfile::tempdir().expect("scratch dir");
    let exe = dir.path().join("clean");
    std::fs::write(&exe, b"").expect("stand-in executable");
    assert!(matches!(
        resolve(None, Some(&exe)),
        Err(OracleCompilerError::NoCandidate { .. })
    ));
    assert!(matches!(
        resolve(None, None),
        Err(OracleCompilerError::NoCandidate { .. })
    ));
}

/// POSITIVE: the `trustc` beside the running executable is admitted by its
/// content (through a symlink too, as a toolchain linked into rustup is), and
/// it is the compiler that runs.
#[cfg(unix)]
#[test]
fn the_sibling_trustc_is_admitted_and_compiles() {
    let toolchain = admit_toolchain_trustc();
    assert_eq!(toolchain.commit().len(), 40);
    assert!(toolchain.sysroot.join("lib/rustlib").is_dir());

    let dir = tempfile::tempdir().expect("scratch dir");
    let exe = dir.path().join("clean");
    std::fs::write(&exe, b"").expect("stand-in executable");
    std::os::unix::fs::symlink(toolchain.path(), dir.path().join("trustc")).expect("symlink");
    let admitted = resolve(None, Some(&exe)).expect("sibling admitted");
    assert_eq!(admitted.path(), toolchain.path());
    assert_eq!(admitted.commit(), toolchain.commit());

    let source = dir.path().join("oracle.rs");
    let binary = dir.path().join("oracle");
    std::fs::write(&source, "fn main() { print!(\"{}\", 2u64 + 2); }\n").expect("source");
    admitted.compile(&source, &binary).expect("compiles");
    assert_eq!(admitted.spawns(), 1);
    let out = Command::new(&binary).output().expect("oracle runs");
    assert_eq!(String::from_utf8_lossy(&out.stdout), "4");
}

/// A compile the admitted compiler rejects is ONE spawn and an error: no
/// retry without the Trust flag, no other compiler.
#[test]
fn a_failed_compile_is_one_spawn_and_an_error() {
    let compiler = admit_toolchain_trustc();
    let dir = tempfile::tempdir().expect("scratch dir");
    let source = dir.path().join("broken.rs");
    std::fs::write(&source, "fn main() { this is not rust }\n").expect("source");
    let err = compiler
        .compile(&source, &dir.path().join("broken"))
        .expect_err("broken source");
    assert!(
        matches!(err, OracleCompilerError::CompileFailed { .. }),
        "got {err}"
    );
    assert_eq!(compiler.spawns(), 1, "a failed compile was retried");
}

/// Inside a Trust toolchain build the oracle compiler must be that
/// toolchain's own commit: a Trust compiler at any other commit is refused,
/// and the same compiler is admitted when its commit is the expected one.
#[test]
fn a_trust_compiler_at_another_commit_is_refused_inside_a_toolchain_build() {
    let toolchain = admit_toolchain_trustc();
    let other = "0".repeat(40);
    let err = admit_expecting(toolchain.path(), Some(&other))
        .expect_err("a Trust compiler at another commit");
    assert!(
        matches!(
            &err,
            OracleCompilerError::CommitMismatch { found, expected, .. }
                if found == toolchain.commit() && *expected == other
        ),
        "got {err}"
    );
    let own = admit_expecting(toolchain.path(), Some(toolchain.commit()))
        .expect("the toolchain's own commit is admitted");
    assert_eq!(own.path(), toolchain.path());
}

/// A compiler at the filesystem root has no `<sysroot>/bin` above it, so it
/// has no sysroot -- never one relative to the working directory.
#[test]
fn a_compiler_without_a_grandparent_directory_has_no_sysroot() {
    assert_eq!(sysroot_of(Path::new("/trustc")), None);
    assert_eq!(
        sysroot_of(Path::new("/opt/trust/bin/trustc")),
        Some(PathBuf::from("/opt/trust"))
    );
}

/// Every process this module starts drops Trust's own controls with
/// `RUSTUP_TOOLCHAIN` and `RUSTC`: a Targo monitor session handed to the
/// caller would make the oracle compile fatal.
#[test]
fn trust_controls_are_scrubbed_from_oracle_processes() {
    for control in [
        "TRUST_TARGO_TEST_MONITOR_SESSION",
        "TRUST_TARGO_VERIFY",
        "TRUST_CG_OUTPUT",
    ] {
        assert!(is_trust_control(OsStr::new(control)), "{control}");
    }
    for other in ["TRUSTED", "RUSTFLAGS", "PATH", "CLEAN_NATIVE_DECIDE_TRUSTC"] {
        assert!(!is_trust_control(OsStr::new(other)), "{other}");
    }
    let command = command_for(Path::new("/nonexistent/trustc"));
    let removed: Vec<&OsStr> = command
        .get_envs()
        .filter_map(|(var, value)| value.is_none().then_some(var))
        .collect();
    for var in SCRUBBED_ENV {
        assert!(removed.contains(&OsStr::new(var)), "{var} is not removed");
    }
}
