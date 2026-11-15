// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `native_decide` compiles its oracle with Trust's own compiler, admitted by
//! CONTENT, or it lets the Clean kernel decide -- never a compiler that PATH
//! or an environment variable happens to name.
//!
//! Every scenario runs the battery test below again in a child process (the
//! resolution is process-wide, so each scenario needs a fresh process); that
//! test asserts the kernel's verdicts, so a scenario that changed an answer
//! fails as loudly as one that ran the wrong compiler. The corpus test checks
//! source declarations the same way -- a fixture file that uses
//! `native_decide`, Lean issue 1825's false `Int` claim beside its true twin,
//! and goals the native path lowers -- and a differential runs it natively and
//! kernel-only: the two must agree declaration for declaration.

use std::path::{Path, PathBuf};
use std::process::Command;

use clean_elab::oracle_compiler::{admit_beside, oracle_compiler, OracleCompiler};
use clean_elab::tactic::{native_decide, ProofState};
use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, Expr, Level, Name};
use clean_parser::parse_file;

/// The tests the scenarios run again, by name, in a child process.
const BATTERY_CHILD: &str = "battery_is_decided_as_the_kernel_decides";
const CORPUS_CHILD: &str = "corpus_is_decided_as_the_kernel_decides";

/// Every variable a pre-fix resolver read to find a compiler.
const COMPILER_VARS: [&str; 4] = [
    "CLEAN_NATIVE_DECIDE_TRUSTC",
    "CLEAN_RUSTC",
    "RUSTC",
    "RUSTUP_TOOLCHAIN",
];

fn nat() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

fn eq(ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty, lhs, rhs],
    )
}

fn nat_add(l: u64, r: u64) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Nat.add"), vec![]),
        [Expr::nat_lit(l), Expr::nat_lit(r)],
    )
}

/// `(label, goal, the kernel's verdict)`. Each goal lowers to a native oracle
/// program, so a compiler is consulted for every one of them unless the
/// resolver refuses it.
fn battery() -> Vec<(&'static str, Expr, &'static str)> {
    let string = || Expr::const_(Name::from_string("String"), vec![]);
    let boolean = || Expr::const_(Name::from_string("Bool"), vec![]);
    let bool_lit = |b: &str| Expr::const_(Name::from_string(b), vec![]);
    vec![
        (
            "true",
            Expr::const_(Name::from_string("True"), vec![]),
            "proved",
        ),
        (
            "false",
            Expr::const_(Name::from_string("False"), vec![]),
            "refuted",
        ),
        (
            "nat_2_add_2_eq_4",
            eq(nat(), nat_add(2, 2), Expr::nat_lit(4)),
            "proved",
        ),
        (
            "nat_2_add_2_eq_5",
            eq(nat(), nat_add(2, 2), Expr::nat_lit(5)),
            "refuted",
        ),
        (
            "string_eq",
            eq(string(), Expr::str_lit("clean"), Expr::str_lit("clean")),
            "proved",
        ),
        (
            "string_ne",
            eq(string(), Expr::str_lit("clean"), Expr::str_lit("lean")),
            "refuted",
        ),
        (
            "bool_ne",
            eq(boolean(), bool_lit("Bool.true"), bool_lit("Bool.false")),
            "refuted",
        ),
    ]
}

/// Decide the battery under this process's oracle compiler, whatever it
/// resolved to: the verdicts are the kernel's. Each goal prints one `VERDICT`
/// line, then the resolution, the compile count and a probe of the admitted
/// compiler, which the scenarios below read when they run this test again in
/// a child process.
#[test]
fn battery_is_decided_as_the_kernel_decides() {
    let mut verdicts = Vec::new();
    for (label, goal, _) in battery() {
        let mut state = ProofState::new(Environment::with_prelude(), goal);
        let verdict = match native_decide(&mut state) {
            Ok(()) if state.is_complete() && state.trusted_axiom_count() == 0 => "proved",
            Ok(()) => "incomplete",
            Err(_) => "refuted",
        };
        println!("VERDICT {label} {verdict}");
        verdicts.push((label.to_owned(), verdict.to_owned()));
    }
    print_oracle();
    print_probe();
    assert_kernel_verdicts(&verdicts);
}

/// After the battery (so `SPAWNS` counts the battery alone): whether this
/// process's admitted compiler builds a working oracle program in this
/// process's environment -- `PROBE compiled`, `PROBE failed <why>`, or
/// `PROBE none` without an admitted compiler. It tells a working native path
/// from one whose every compile fails, which the verdicts and the compile
/// count cannot.
fn print_probe() {
    let Ok(compiler) = oracle_compiler() else {
        println!("PROBE none");
        return;
    };
    let dir = tempfile::tempdir().expect("probe dir");
    let source = dir.path().join("probe.rs");
    let binary = dir.path().join("probe");
    std::fs::write(&source, "fn main() { print!(\"{}\", 6u64 * 7); }\n").expect("probe source");
    let ran = compiler
        .compile(&source, &binary)
        .map_err(|err| err.to_string())
        .and_then(|()| {
            Command::new(&binary)
                .output()
                .map_err(|err| err.to_string())
        });
    match ran {
        Ok(out) if out.stdout == b"42" => println!("PROBE compiled"),
        Ok(out) => println!("PROBE failed: the probe printed {:?}", out.stdout),
        Err(why) => println!("PROBE failed: {}", why.replace('\n', " ")),
    }
}

/// What this process resolved as its oracle compiler, and how many compiles
/// it started.
fn print_oracle() {
    match oracle_compiler() {
        Ok(compiler) => {
            println!("ORACLE admitted {}", compiler.path().display());
            println!("SPAWNS {}", compiler.spawns());
        }
        Err(why) => {
            println!("ORACLE unavailable {why}");
            println!("SPAWNS 0");
        }
    }
}

/// A source file in this repository that uses `native_decide`, relative to the
/// workspace root. Its `import` lines are dropped -- loading real Init from
/// oleans takes the better part of an hour in a debug build -- so the prelude
/// stands in for Init, and a declaration that needs Init fails in both
/// processes alike.
const CORPUS_FILES: [&str; 1] = ["tests/fixtures/tactic_families/g_auto/decide.lean"];

/// Lean 4 issue 1825 (`tests/lean4_compat/lean4_tests/1825.lean`): over `Int`,
/// `-2147483648 + 2147483648 = -18446744069414584320` is FALSE, and an
/// overflowing native evaluator once accepted it. The file writes bare
/// numerals, which Init's default `Neg Int` instance reads as `Int`; on the
/// prelude they stay `Nat` and fail to elaborate (`Neg Nat`) before any
/// tactic runs, so the claim is restated here with its `Int` ascription,
/// beside its TRUE twin: the twin is proved and the claim is refused by the
/// decision itself (Lean's "evaluated that the proposition … is false"), so
/// the refusal measures `native_decide`, not elaboration.
const ISSUE_1825_SOURCE: &str =
    "theorem boom : (-2147483648 : Int) + 2147483648 = 0 := by native_decide\n\
theorem boom' : (-2147483648 : Int) + 2147483648 = -18446744069414584320 := by native_decide\n";

/// Source-level goals the native path lowers, with the kernel's verdicts. They
/// are the corpus's only oracle compiles: the fixture's and 1825's numerals
/// elaborate through `OfNat`, which the native lowering does not take, so the
/// kernel decides those in both processes.
const LOWERING_SOURCE: &str = "theorem nd_true : True := by native_decide\n\
theorem nd_false : False := by native_decide\n\
theorem nd_str : \"clean\" = \"clean\" := by native_decide\n\
theorem nd_str_ne : \"clean\" = \"lean\" := by native_decide\n";
const LOWERING_VERDICTS: [&str; 4] = ["ok", "err", "ok", "err"];

/// Elaborate and kernel-check every declaration of `source` on the prelude:
/// `ok` when it registered with no inner failure, `err` with what failed
/// otherwise.
fn declaration_verdicts(source: &str) -> Vec<(&'static str, String)> {
    fn failed(result: &ElabResult) -> bool {
        match result {
            ElabResult::Multiple(results) => results.iter().any(failed),
            ElabResult::Failed { .. } => true,
            _ => false,
        }
    }
    let decls = match parse_file(source) {
        Ok(decls) => decls,
        Err(err) => return vec![("parse-error", format!("{err:?}"))],
    };
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    decls
        .iter()
        .map(|decl| {
            let processed = preprocess_decl_with_context(decl, &mut file_ctx);
            match elaborate_decl_and_register(&mut env, &processed) {
                Ok(result) if !failed(&result) => ("ok", String::new()),
                Ok(result) => ("err", format!("{result:?}")),
                Err(err) => ("err", err.to_string()),
            }
        })
        .collect()
}

/// Check the corpus under this process's oracle compiler: one `DECL` line per
/// declaration of each source, then the resolution and the compile count. The
/// lowering goals get the kernel's verdicts, and Lean issue 1825's false claim
/// is refused by the decision while its true twin is proved, whatever decided
/// them.
#[test]
fn corpus_is_decided_as_the_kernel_decides() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut sources: Vec<(String, String)> = CORPUS_FILES
        .iter()
        .map(|file| {
            let text = std::fs::read_to_string(root.join(file))
                .unwrap_or_else(|err| panic!("corpus file {file}: {err}"));
            let body: Vec<&str> = text
                .lines()
                .filter(|line| !line.starts_with("import "))
                .collect();
            ((*file).to_owned(), body.join("\n"))
        })
        .collect();
    sources.push(("issue_1825".to_owned(), ISSUE_1825_SOURCE.to_owned()));
    sources.push(("lowering".to_owned(), LOWERING_SOURCE.to_owned()));
    let mut decls = Vec::new();
    for (label, source) in sources {
        for (index, (verdict, detail)) in declaration_verdicts(&source).into_iter().enumerate() {
            println!("DECL {label}#{index} {verdict}");
            decls.push((format!("{label}#{index}"), verdict, detail));
        }
    }
    print_oracle();
    let of_source = |source: &str| -> Vec<(&str, &str)> {
        decls
            .iter()
            .filter(|(label, _, _)| label.starts_with(&format!("{source}#")))
            .map(|(_, verdict, detail)| (*verdict, detail.as_str()))
            .collect()
    };
    let lowering: Vec<&str> = of_source("lowering")
        .into_iter()
        .map(|(verdict, _)| verdict)
        .collect();
    assert_eq!(lowering, LOWERING_VERDICTS);
    let issue_1825 = of_source("issue_1825");
    assert_eq!(
        issue_1825.len(),
        2,
        "Lean issue 1825's twin declarations: {issue_1825:?}"
    );
    assert_eq!(
        issue_1825[0],
        ("ok", ""),
        "the TRUE Int twin of issue 1825 was not proved"
    );
    assert_eq!(
        issue_1825[1].0, "err",
        "issue 1825's FALSE Int claim was accepted"
    );
    // The refusal is the decision's, in pinned Lean's words (v4.30.0-rc2,
    // measured 2026-10-17: "Tactic `native_decide` evaluated that the
    // proposition\n  2 + 2 = 5\nis false" for `2 + 2 = 5 := by native_decide`).
    assert!(
        issue_1825[1]
            .1
            .contains("Tactic `native_decide` evaluated that the proposition")
            && issue_1825[1].1.contains("is false"),
        "issue 1825's false claim must be refused by the decision, not before it: {}",
        issue_1825[1].1
    );
}

/// A scratch directory holding `trustc` and `rustc` impostors: shell scripts
/// that claim Trust's identity on `-vV`, record every invocation in
/// `spawned.log`, and fail every compile (so the kernel still answers and only
/// the log tells that they ran).
struct Impostors {
    dir: tempfile::TempDir,
}

impl Impostors {
    fn new() -> Self {
        let dir = tempfile::tempdir().expect("scratch dir");
        let bin = dir.path().join("bin");
        std::fs::create_dir(&bin).expect("impostor bin dir");
        let log = dir.path().join("spawned.log");
        for name in ["trustc", "rustc"] {
            let script = bin.join(name);
            std::fs::write(
                &script,
                format!(
                    "#!/bin/sh\n\
                     printf '%s %s\\n' \"$0\" \"$*\" >> '{log}'\n\
                     case \"$*\" in *-vV*)\n\
                     printf 'rustc 1.99.0-dev (impostor)\\nbinary: trustc\\n\
                     commit-hash: 0000000000000000000000000000000000000000\\n\
                     host: aarch64-apple-darwin\\nrelease: 1.99.0-dev\\ntrust: 0.1.0\\n'\n\
                     exit 0;;\n\
                     esac\n\
                     exit 1\n",
                    log = log.display()
                ),
            )
            .expect("write impostor");
            make_executable(&script);
        }
        Self { dir }
    }

    fn bin(&self) -> PathBuf {
        self.dir.path().join("bin")
    }

    fn trustc(&self) -> PathBuf {
        self.bin().join("trustc")
    }

    /// `PATH` with the impostors first, then the inherited `PATH`.
    fn first_on_path(&self) -> std::ffi::OsString {
        let mut path = self.bin().into_os_string();
        if let Some(inherited) = std::env::var_os("PATH") {
            path.push(":");
            path.push(inherited);
        }
        path
    }

    /// Every recorded invocation, one per line; empty when none ran.
    fn spawned(&self) -> String {
        std::fs::read_to_string(self.dir.path().join("spawned.log")).unwrap_or_default()
    }
}

#[cfg(unix)]
fn make_executable(path: &Path) {
    use std::os::unix::fs::PermissionsExt;
    std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o755)).expect("chmod +x");
}

#[cfg(not(unix))]
fn make_executable(_path: &Path) {}

/// What a battery child printed.
struct ChildReport {
    /// The battery child's `VERDICT` lines.
    verdicts: Vec<(String, String)>,
    /// The corpus child's `DECL` lines.
    decls: Vec<(String, String)>,
    /// `admitted <path>` or `unavailable <reason>`.
    oracle: String,
    spawns: u64,
    /// The battery child's `PROBE` line: `compiled`, `failed: <why>` or `none`.
    probe: Option<String>,
}

/// Run the battery in a child of `exe` (this test binary, or a link to it).
fn run_child(exe: &Path, env: &[(&str, std::ffi::OsString)]) -> ChildReport {
    run_child_test(exe, BATTERY_CHILD, env)
}

/// Run the child test `child` in a child of `exe`, with every compiler
/// variable removed and then `env` applied, and check it exited cleanly.
fn run_child_test(exe: &Path, child: &str, env: &[(&str, std::ffi::OsString)]) -> ChildReport {
    let mut command = Command::new(exe);
    command
        .args(["--exact", child, "--nocapture"])
        .args(["--test-threads", "1"]);
    for var in COMPILER_VARS {
        command.env_remove(var);
    }
    for (key, value) in env {
        command.env(key, value);
    }
    let output = command.output().expect("launch the child");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success(),
        "child {child} failed ({}):\nstdout:\n{stdout}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    let field = |prefix: &str| {
        stdout
            .lines()
            .find_map(|line| line.split_once(prefix).map(|(_, rest)| rest))
            .unwrap_or_else(|| panic!("child printed no {prefix:?} line:\n{stdout}"))
            .to_owned()
    };
    // libtest prints the first line after `test <name> ... ` on its line.
    let tagged = |tag: &str| -> Vec<(String, String)> {
        stdout
            .lines()
            .filter_map(|line| line.split_once(tag).map(|(_, rest)| rest))
            .filter_map(|rest| rest.split_once(' '))
            .map(|(label, verdict)| (label.to_owned(), verdict.to_owned()))
            .collect()
    };
    ChildReport {
        verdicts: tagged("VERDICT "),
        decls: tagged("DECL "),
        oracle: field("ORACLE "),
        spawns: field("SPAWNS ").parse().expect("spawn count"),
        probe: stdout
            .lines()
            .find_map(|line| line.split_once("PROBE ").map(|(_, rest)| rest.to_owned())),
    }
}

impl ChildReport {
    /// The kernel decided every goal: no compiler admitted, none started.
    fn assert_kernel_decided(&self) {
        assert_kernel_verdicts(&self.verdicts);
        assert!(
            self.oracle.starts_with("unavailable "),
            "an oracle compiler was admitted: {}",
            self.oracle
        );
        assert_eq!(self.spawns, 0, "oracle compiles started");
        assert_eq!(
            self.probe.as_deref(),
            Some("none"),
            "the probe found a compiler"
        );
    }
}

/// The child's verdicts are the kernel's, goal for goal.
fn assert_kernel_verdicts(verdicts: &[(String, String)]) {
    let expected: Vec<(String, String)> = battery()
        .into_iter()
        .map(|(label, _, verdict)| (label.to_owned(), verdict.to_owned()))
        .collect();
    assert_eq!(
        verdicts,
        expected.as_slice(),
        "native_decide verdicts moved"
    );
}

fn this_test_binary() -> PathBuf {
    std::env::current_exe().expect("current test binary")
}

/// NEGATIVE CONTROL: a `trustc` and a `rustc` first on PATH are never run.
/// Before the fix the oracle compiler was the bare name `trustc`, which PATH
/// resolves -- here, to a script that says it is Trust.
#[test]
fn path_trustc_and_rustc_are_never_spawned() {
    let impostors = Impostors::new();
    let report = run_child(&this_test_binary(), &[("PATH", impostors.first_on_path())]);
    report.assert_kernel_decided();
    assert!(
        report.oracle.contains("no oracle compiler"),
        "without a setting or a sibling there is no candidate: {}",
        report.oracle
    );
    assert_eq!(
        impostors.spawned(),
        "",
        "a compiler found on PATH was spawned for native_decide"
    );
}

/// NEGATIVE CONTROL: a compiler an environment variable names is admitted by
/// its content, never by its name or its `-vV`. A script is refused without
/// being run, whatever it prints -- and no other variable is consulted.
#[test]
fn a_named_script_compiler_is_refused_without_being_run() {
    let impostors = Impostors::new();
    let named = impostors.trustc().into_os_string();
    let report = run_child(
        &this_test_binary(),
        &[
            ("CLEAN_NATIVE_DECIDE_TRUSTC", named.clone()),
            ("CLEAN_RUSTC", named.clone()),
            ("RUSTC", named),
        ],
    );
    report.assert_kernel_decided();
    assert!(
        report.oracle.contains("not a native executable"),
        "refused for its content: {}",
        report.oracle
    );
    assert_eq!(
        impostors.spawned(),
        "",
        "a script named as the oracle compiler was run"
    );
}

/// A hard link to this test binary in a scratch directory whose `trustc` is a
/// symlink to `toolchain`'s: a running executable with a sibling Trust
/// compiler. The directory lives as long as the returned guard.
#[cfg(unix)]
fn beside_a_sibling_trustc(toolchain: &OracleCompiler) -> (tempfile::TempDir, PathBuf) {
    let scratch = tempfile::tempdir_in(env!("CARGO_TARGET_TMPDIR")).expect("scratch dir");
    let exe = scratch.path().join("oracle-child");
    link_or_copy(&this_test_binary(), &exe);
    std::os::unix::fs::symlink(toolchain.path(), scratch.path().join("trustc"))
        .expect("sibling trustc");
    (scratch, exe)
}

/// A scratch toolchain whose `bin/trustc` Clean ADMITS but whose every compile
/// fails: `bin/trustc` is a hard link to `toolchain`'s compiler (so its
/// canonical path is here, and its `-vV` is Trust's), `lib` links the
/// compiler's own libraries so it runs, and `lib/rustlib` is empty -- there
/// is no standard library. The running executable is a hard link to this test
/// binary beside it. Returns the guard, that executable and the `trustc`.
#[cfg(unix)]
fn beside_a_trustc_without_std(
    toolchain: &OracleCompiler,
) -> (tempfile::TempDir, PathBuf, PathBuf) {
    let scratch = tempfile::tempdir_in(env!("CARGO_TARGET_TMPDIR")).expect("scratch dir");
    let bin = scratch.path().join("bin");
    let lib = scratch.path().join("lib");
    std::fs::create_dir(&bin).expect("bin dir");
    std::fs::create_dir_all(lib.join("rustlib")).expect("empty rustlib");
    let trustc = bin.join("trustc");
    link_or_copy(toolchain.path(), &trustc);
    let toolchain_lib = toolchain
        .path()
        .parent()
        .and_then(Path::parent)
        .expect("the toolchain's sysroot")
        .join("lib");
    for entry in std::fs::read_dir(&toolchain_lib).expect("the toolchain's lib dir") {
        let library = entry.expect("lib entry").path();
        if library.is_file() {
            let name = library.file_name().expect("library name");
            std::os::unix::fs::symlink(&library, lib.join(name)).expect("link a library");
        }
    }
    let exe = bin.join("oracle-child");
    link_or_copy(&this_test_binary(), &exe);
    let trustc = trustc.canonicalize().expect("the scratch trustc");
    (scratch, exe, trustc)
}

/// Hard-link `from` at `to`, or copy it where a link is refused.
fn link_or_copy(from: &Path, to: &Path) {
    if std::fs::hard_link(from, to).is_err() {
        std::fs::copy(from, to).unwrap_or_else(|err| panic!("copy {from:?} to {to:?}: {err}"));
    }
}

/// This toolchain's `trustc`, admitted: the one beside `$CARGO` (Targo exports
/// it to tests), else beside the Targo that built this test.
fn toolchain_trustc() -> OracleCompiler {
    let cargo =
        std::env::var_os("CARGO").map_or_else(|| PathBuf::from(env!("CARGO")), PathBuf::from);
    admit_beside(&cargo)
        .unwrap_or_else(|err| panic!("these tests need the trustc beside {cargo:?}: {err}"))
}

/// NEGATIVE CONTROL: native compilers that are not Trust's -- every `rustc`
/// of a toolchain rustup installed on this machine (a linked toolchain, such
/// as rustup's `trust` link to a Trust sysroot, is skipped: it is not stock),
/// rustup's `~/.cargo/bin` proxy, and a plain native binary -- are refused when
/// named, and the kernel decides with the same verdicts.
#[test]
fn named_non_trust_native_compilers_are_refused() {
    let home = std::env::var_os("HOME")
        .map(PathBuf::from)
        .unwrap_or_default();
    let rustup_home =
        std::env::var_os("RUSTUP_HOME").map_or_else(|| home.join(".rustup"), PathBuf::from);
    let installed_toolchains = std::fs::read_dir(rustup_home.join("toolchains"))
        .into_iter()
        .flatten()
        .filter_map(Result::ok)
        .filter(|entry| entry.file_type().is_ok_and(|kind| kind.is_dir()))
        .map(|entry| entry.path().join("bin/rustc"));
    let candidates: Vec<PathBuf> = [
        PathBuf::from("/usr/bin/true"),
        home.join(".cargo/bin/rustc"),
    ]
    .into_iter()
    .chain(installed_toolchains)
    .collect();
    let present: Vec<&PathBuf> = candidates.iter().filter(|c| c.exists()).collect();
    assert!(!present.is_empty(), "no native non-Trust binary to name");
    for candidate in present {
        let report = run_child(
            &this_test_binary(),
            &[(
                "CLEAN_NATIVE_DECIDE_TRUSTC",
                candidate.clone().into_os_string(),
            )],
        );
        report.assert_kernel_decided();
    }
}

/// POSITIVE: the `trustc` beside the running executable is the oracle
/// compiler, and it compiles every goal of the battery -- even with the PATH
/// impostors first on PATH, and with a Targo monitor session in the
/// environment, which the oracle compile must not inherit (trustc refuses a
/// compile handed one it was not selected for). The running executable is a
/// hard link to this test binary in a scratch directory whose `trustc` is
/// this toolchain's.
#[cfg(unix)]
#[test]
fn the_sibling_trustc_decides_natively() {
    let toolchain = toolchain_trustc();
    let (_scratch, exe) = beside_a_sibling_trustc(&toolchain);

    let impostors = Impostors::new();
    let report = run_child(
        &exe,
        &[
            ("PATH", impostors.first_on_path()),
            ("TRUST_TARGO_TEST_MONITOR_SESSION", "s1".into()),
        ],
    );
    assert_kernel_verdicts(&report.verdicts);
    assert_eq!(
        report.probe.as_deref(),
        Some("compiled"),
        "the admitted sibling does not build a working oracle in this environment"
    );
    assert_eq!(
        report.oracle,
        format!("admitted {}", toolchain.path().display()),
        "the sibling trustc was not the oracle compiler"
    );
    assert_eq!(
        report.spawns,
        battery().len() as u64,
        "every goal of the battery compiles through the sibling"
    );
    assert_eq!(impostors.spawned(), "", "a PATH compiler was spawned");
}

/// NEGATIVE CONTROL: an ADMITTED compiler whose compile fails is run once per
/// goal -- never retried with other flags (the pre-fix fallback re-ran a
/// compiler that rejected `-Ztrust-verify=off` without it), never replaced by
/// a compiler from PATH -- and the kernel decides every goal with the same
/// verdicts.
#[cfg(unix)]
#[test]
fn a_failing_admitted_compiler_runs_once_per_goal_and_the_kernel_decides() {
    let toolchain = toolchain_trustc();
    let (_scratch, exe, trustc) = beside_a_trustc_without_std(&toolchain);

    let impostors = Impostors::new();
    let report = run_child(&exe, &[("PATH", impostors.first_on_path())]);
    assert_kernel_verdicts(&report.verdicts);
    assert_eq!(
        report.oracle,
        format!("admitted {}", trustc.display()),
        "the scratch trustc was not admitted, so nothing here failed a compile"
    );
    assert_eq!(
        report.spawns,
        battery().len() as u64,
        "a failed oracle compile was retried"
    );
    assert!(
        report
            .probe
            .as_deref()
            .is_some_and(|probe| probe.starts_with("failed")),
        "the scratch trustc was meant to fail every compile: {:?}",
        report.probe
    );
    assert_eq!(impostors.spawned(), "", "a PATH compiler was spawned");
}

/// DIFFERENTIAL over the corpus: the fixture file, issue 1825's twins and the
/// lowering goals get the same verdict per declaration from a process that
/// decides natively (a sibling `trustc`, which compiles an oracle for every
/// lowering goal) and from one that has no oracle compiler (the kernel alone).
/// Each child also holds the corpus test's own assertions, so both cannot be
/// equally wrong.
#[cfg(unix)]
#[test]
fn corpus_verdicts_agree_native_and_kernel_only() {
    let toolchain = toolchain_trustc();
    let (_scratch, native_exe) = beside_a_sibling_trustc(&toolchain);
    let native = run_child_test(&native_exe, CORPUS_CHILD, &[]);
    let kernel = run_child_test(&this_test_binary(), CORPUS_CHILD, &[]);

    assert!(!kernel.decls.is_empty(), "the corpus child checked nothing");
    assert_eq!(
        native.decls, kernel.decls,
        "native and kernel-only verdicts differ"
    );
    assert!(
        kernel.oracle.starts_with("unavailable "),
        "{}",
        kernel.oracle
    );
    assert_eq!(kernel.spawns, 0);
    assert_eq!(
        native.oracle,
        format!("admitted {}", toolchain.path().display())
    );
    assert!(
        native.spawns >= LOWERING_VERDICTS.len() as u64,
        "the native process compiled {} oracles for {} lowering goals, so this compared \
         the kernel with itself",
        native.spawns,
        LOWERING_VERDICTS.len()
    );
}
