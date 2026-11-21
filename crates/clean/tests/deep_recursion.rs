// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! DEEP RECURSION COMPILED AS LOOPS — X4's gap `head-loop-is-not-a-loop` of
//! `docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`.
//!
//! Lean compiles a self tail call as `goto _start`, so a structurally
//! recursive head loop runs in constant stack. Clean's lowering makes an
//! induction hypothesis a call of the synthesized recursive function where it
//! occurs (`to_lcnf/rec_ih.rs`, with a selector for a lifted mutual block,
//! `rec_select.rs`, and the same for a syntactic well-founded step,
//! `rec_wf.rs`), and `tail_loop.rs` turns each self tail call into a jump
//! back to the top of its function, which the C emitter prints as `goto` and
//! the trust-ir emitter as a branch.
//!
//! What is asserted, on EXACT BYTES, at optimisation levels 0, 1 and 2:
//!
//! * `clean run --keep-temp` builds each program of
//!   `tests/fixtures/deep_recursion/programs`, and the kept executable is run
//!   again by itself on a 512 KiB main-thread stack (`ulimit -s 512`), so a
//!   recursion that is not a loop cannot hide behind a large stack (`clean`
//!   itself is not run under that limit: its own main thread parses its
//!   arguments, and a debug build needs more);
//! * every program in [`LOOPS`] prints pinned Lean's bytes (minted from
//!   pinned Lean, see the fixture's README) and exits 0 there;
//! * every program in [`OVERFLOWS`] dies of a signal there after printing a
//!   prefix of Lean's bytes: the NEGATIVE CONTROL `non_tail_deep_1m` (`deep
//!   n + 1`, not a tail call), so the stack really is small and the loop
//!   programs are loops, and two named gaps, pinned so that each fails
//!   loudly the day it closes;
//! * the emitted C of the subjects of [`STRICT_LOOPS`] has a `goto` back edge
//!   in the recursive function, no call of that function, and no
//!   `clean_apply_*` but of an instance constant (opt 0 applies `Decidable`
//!   instances as closures; an induction hypothesis is never one), and with
//!   `trust-ir-backend` the emitted trust-ir has a branch back edge, no self
//!   call and the same closure rule.
//!
//! The trust-cg lane runs the same programs when the `trust-ir-backend`
//! feature is on and `CLEAN_TRUST_CG_BIN` names a trust-cg; it is a
//! measurement of the same lowering through trust-ir and an external
//! backend, nothing more.

#![cfg(unix)]

use std::ffi::OsString;
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::Command;

const FIXTURE: &str = "tests/fixtures/deep_recursion";

/// Programs that must print Lean's bytes and exit 0 on a 512 KiB stack.
const LOOPS: &[&str] = &[
    "for_unit_state",
    "head_loop_10m",
    "io_twice",
    "mutual_acc_1m",
    "poly_loop_10m",
    "swap_loop",
    "tail_k0_10m",
    "two_use_ih",
    "wf_loop_1m",
];

/// Programs that must overflow the 512 KiB stack, each with why.
const OVERFLOWS: &[(&str, &str)] = &[
    (
        "non_tail_deep_1m",
        "NEGATIVE CONTROL: `deep n + 1` is not a tail call",
    ),
    (
        "io_loop_10m",
        "gap `io-loop-through-bind-continuation`: the recursive call sits in the \
         continuation lambda of `IO.bind`, not in `go`'s tail (Lean's binary exits 0)",
    ),
    (
        "mutual_even_odd_10m",
        "gap `mutual-value-pack-not-a-loop`: the elaborator packs a one-argument \
         mutual block into one function returning the pair of results, a non-tail \
         recursion (Lean's binary also overflows here: it has no mutual tail calls)",
    ),
];

const OPT_LEVELS: &[&str] = &["0", "1", "2"];

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn program(name: &str) -> PathBuf {
    repo_root()
        .join(FIXTURE)
        .join("programs")
        .join(format!("{name}.lean"))
}

fn x1_program(name: &str) -> PathBuf {
    repo_root()
        .join("tests/fixtures/advice_replay_checker/programs")
        .join(format!("{name}.lean"))
}

fn expected(name: &str) -> Vec<u8> {
    let path = repo_root()
        .join(FIXTURE)
        .join("expected")
        .join(format!("{name}.stdout"));
    std::fs::read(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

struct Ran {
    code: Option<i32>,
    signal: Option<i32>,
    stdout: Vec<u8>,
    stderr: String,
}

/// Build `name` at `opt` with `clean run --keep-temp` (which also runs it
/// once, on the caller's stack) and return the scratch root that holds the
/// kept build and the kept executable's path.
fn build(
    name: &str,
    opt: &str,
    extra: &[&str],
    envs: &[(&str, OsString)],
) -> Result<(tempfile::TempDir, PathBuf), String> {
    let tmp = tempfile::tempdir().expect("scratch TMPDIR");
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_clean"));
    cmd.arg("run")
        .arg(program(name))
        .args(["--decl", "main", "--opt-level", opt, "--keep-temp"])
        .args(extra)
        .env("TMPDIR", tmp.path())
        .current_dir(tmp.path());
    for (key, value) in envs {
        cmd.env(key, value);
    }
    let out = cmd.output().expect("spawn clean run");
    let stderr = String::from_utf8_lossy(&out.stderr);
    let kept = stderr
        .lines()
        .find_map(|l| l.split_once("kept build directory at ").map(|(_, d)| d))
        .ok_or_else(|| format!("no kept build directory (stderr: {stderr})"))?;
    let binary = PathBuf::from(kept).join("program");
    if !binary.is_file() {
        return Err(format!("{} is not a built program", binary.display()));
    }
    Ok((tmp, binary))
}

/// Run the built `binary` by itself under `ulimit -s 512`.
fn run_small_stack(binary: &Path) -> Ran {
    let cwd = tempfile::tempdir().expect("scratch cwd");
    let out = Command::new("/bin/sh")
        .arg("-c")
        .arg("ulimit -s 512 && exec \"$0\"")
        .arg(binary)
        .current_dir(cwd.path())
        .env_remove("LEAN_MAIN_USE_THREAD")
        .output()
        .expect("spawn the built program");
    Ran {
        code: out.status.code(),
        signal: out.status.signal(),
        stdout: out.stdout,
        stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
    }
}

/// Every loop prints Lean's bytes; every pinned overflow overflows.
fn check_lane(lane: &str, extra: &[&str], envs: &[(&str, OsString)]) {
    let mut failures = Vec::new();
    for opt in OPT_LEVELS {
        for name in LOOPS {
            let ran = match build(name, opt, extra, envs) {
                Ok((_scratch, binary)) => run_small_stack(&binary),
                Err(e) => {
                    failures.push(format!("{name} O{opt}: build: {e}"));
                    continue;
                }
            };
            eprintln!("deep[{lane}] O{opt} {name:<22} code={:?}", ran.code);
            let ok = ran.code == Some(0) && ran.stdout == expected(name) && ran.stderr.is_empty();
            if !ok {
                failures.push(format!(
                    "{name} O{opt}: code {:?} signal {:?}\n--- stdout\n{}\n--- Lean\n{}\n\
                     --- stderr\n{}",
                    ran.code,
                    ran.signal,
                    String::from_utf8_lossy(&ran.stdout),
                    String::from_utf8_lossy(&expected(name)),
                    ran.stderr
                ));
            }
        }
        for (name, why) in OVERFLOWS {
            let ran = match build(name, opt, extra, envs) {
                Ok((_scratch, binary)) => run_small_stack(&binary),
                Err(e) => {
                    failures.push(format!("{name} O{opt}: build: {e}"));
                    continue;
                }
            };
            eprintln!(
                "deep[{lane}] O{opt} {name:<22} code={:?} signal={:?}",
                ran.code, ran.signal
            );
            let overflowed = ran.signal.is_some() && expected(name).starts_with(&ran.stdout);
            if !overflowed {
                failures.push(format!(
                    "{name} O{opt}: expected to overflow a 512 KiB stack ({why}); code {:?}, \
                     signal {:?}, stderr {}",
                    ran.code, ran.signal, ran.stderr
                ));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{lane}: {} failure(s):\n{}",
        failures.len(),
        failures.join("\n\n")
    );
}

#[test]
fn deep_loops_print_leans_bytes_on_a_small_stack_c_lane() {
    check_lane("c", &[], &[]);
}

#[cfg(feature = "trust-ir-backend")]
#[test]
fn deep_loops_print_leans_bytes_on_a_small_stack_trust_cg_lane() {
    let Some(trust_cg) = std::env::var_os("CLEAN_TRUST_CG_BIN") else {
        panic!(
            "CLEAN_TRUST_CG_BIN is not set: this measurement names its trust-cg explicitly; \
             point it at one that accepts --recognize-authority"
        );
    };
    let receipt_dir = tempfile::tempdir().expect("receipt dir");
    let receipt = receipt_dir.path().join("receipt.json");
    let receipt = receipt.to_str().expect("utf-8 receipt path");
    check_lane(
        "trust-cg",
        &["--backend", "trust-cg", "--receipt", receipt],
        &[("CLEAN_TRUST_CG_BIN", trust_cg)],
    );
}

/// Shape subjects whose synthesized recursive function is a pure loop:
/// (program, declaration).
const STRICT_LOOPS: &[(&str, &str)] = &[
    ("head_loop_10m", "headLoop"),
    ("mutual_acc_1m", "evenAcc"),
    ("swap_loop", "swapLoop"),
    ("tail_k0_10m", "down"),
];

/// `clean compile <source> --decl <decl> --emit <emit>` at `opt`.
fn emitted(source: &Path, decl: &str, emit: &str, opt: &str) -> String {
    let dir = tempfile::tempdir().expect("scratch");
    let out = dir.path().join("out");
    let status = Command::new(env!("CARGO_BIN_EXE_clean"))
        .arg("compile")
        .arg(source)
        .args(["--decl", decl, "--emit", emit, "--opt-level", opt, "-o"])
        .arg(&out)
        .current_dir(dir.path())
        .output()
        .expect("spawn clean compile");
    assert!(
        status.status.success(),
        "clean compile {} --decl {decl} --emit {emit}: {}",
        source.display(),
        String::from_utf8_lossy(&status.stderr)
    );
    std::fs::read_to_string(&out).expect("emitted text")
}

/// The C name prefix of `decl`'s synthesized recursive functions
/// (`_lifted.<decl>._rec.<n>`).
fn rec_prefix(decl: &str) -> String {
    format!("l___lifted_{}___rec_", decl.replace('.', "_"))
}

/// Whether `symbol` names one of `decl`'s synthesized recursive functions
/// (`l___lifted_<decl>___rec_<n>__`), not a helper extracted from one, such
/// as the closed term `l___lifted_whnf___rec_0_____boxed__const__0` at opt 1.
fn is_rec_symbol(symbol: &str, decl: &str) -> bool {
    symbol
        .strip_prefix(&rec_prefix(decl))
        .and_then(|rest| rest.strip_suffix("__"))
        .is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()))
}

/// `decl`'s synthesized recursive functions in `c`, as [`c_function`] gives.
fn rec_functions<'a>(c: &'a str, decl: &str) -> Vec<(&'a str, &'a str)> {
    c_function(c, &rec_prefix(decl))
        .into_iter()
        .filter(|(signature, _)| is_rec_symbol(c_symbol(signature), decl))
        .collect()
}

/// The first `clean_apply_*` line of `body` whose closure is not an instance
/// constant (`l_inst…`). At opt 0 a `Decidable` instance is applied as a
/// closure (`clean_apply_2(l_instDecidableEqBool(), a, b)`); an induction
/// hypothesis never is, which is what these pins are about.
fn non_instance_closure(body: &str) -> Option<&str> {
    body.lines()
        .filter(|l| l.contains("clean_apply_"))
        .find(|line| {
            let applied = line.split("clean_apply_").nth(1).unwrap_or_default();
            let callee = applied.split_once('(').map_or("", |(_, rest)| rest);
            !callee.starts_with("l_inst")
        })
}

/// The C functions whose definition line contains `fragment`, each as its
/// signature line and its text up to the line that closes it.
fn c_function<'a>(c: &'a str, fragment: &str) -> Vec<(&'a str, &'a str)> {
    let mut found = Vec::new();
    let mut rest = c;
    while let Some(at) = rest.find(fragment) {
        let line_start = rest[..at].rfind('\n').map_or(0, |i| i + 1);
        let head = &rest[line_start..];
        let sig_end = head.find('\n').unwrap_or(head.len());
        let signature = &head[..sig_end];
        let is_definition = signature.trim_end().ends_with('{');
        if is_definition {
            let body_end = head.find("\n}\n").map_or(head.len(), |i| i + 3);
            found.push((signature, &head[..body_end]));
            rest = &head[body_end..];
        } else {
            rest = &head[sig_end..];
        }
    }
    found
}

/// The C symbol a definition line names: the identifier before its `(`.
fn c_symbol(signature: &str) -> &str {
    let before = signature.split('(').next().unwrap_or_default();
    before.rsplit([' ', '*']).next().unwrap_or_default()
}

fn calls_itself(symbol: &str, body: &str) -> bool {
    body.lines()
        .skip(1)
        .any(|l| l.contains(&format!("{symbol}(")))
}

#[test]
fn recursive_functions_are_loops_in_the_emitted_c() {
    for opt in OPT_LEVELS {
        for (name, decl) in STRICT_LOOPS {
            let c = emitted(&program(name), decl, "c", opt);
            let recs = rec_functions(&c, decl);
            assert!(
                !recs.is_empty(),
                "{name} O{opt}: no recursive function of `{decl}` in\n{c}"
            );
            for (signature, body) in recs {
                let symbol = c_symbol(signature);
                assert!(
                    body.contains("goto _jp"),
                    "{name} O{opt}: `{symbol}` has no back edge:\n{body}"
                );
                assert!(
                    !calls_itself(symbol, body),
                    "{name} O{opt}: `{symbol}` still calls itself:\n{body}"
                );
                assert!(
                    non_instance_closure(body).is_none(),
                    "{name} O{opt}: `{symbol}` applies a closure that is not an instance:\n{body}"
                );
            }
        }
    }
}

/// c33's and c36's `whnf` (X1): the head loop is a jump. Their recursive
/// function is not a PURE loop: c36's `conv` and `walk` call `whnf` in
/// non-tail position (they match on its result; Lean has no mutual tail
/// calls either), and at opt 0 a `Decidable` instance is applied as a
/// closure. So the pin is a back edge, every closure application applying an
/// instance constant (never an induction hypothesis), and in c33 no call of
/// itself.
#[test]
fn the_x1_head_loops_are_jumps_in_the_emitted_c() {
    for opt in OPT_LEVELS {
        for (name, self_calls_allowed) in [
            ("c33_r4_x_report_accumulator", false),
            ("c36_r4_x_report_call_cycle", true),
        ] {
            let c = emitted(&x1_program(name), "whnf", "c", opt);
            let recs = rec_functions(&c, "whnf");
            assert!(
                !recs.is_empty(),
                "{name} O{opt}: no recursive `whnf` in\n{c}"
            );
            for (signature, body) in recs {
                let symbol = c_symbol(signature);
                assert!(
                    body.contains("goto _jp"),
                    "{name} O{opt}: `{symbol}` has no back edge:\n{body}"
                );
                assert!(
                    self_calls_allowed || !calls_itself(symbol, body),
                    "{name} O{opt}: `{symbol}` still calls itself:\n{body}"
                );
                if let Some(line) = non_instance_closure(body) {
                    panic!(
                        "{name} O{opt}: `{symbol}` applies a closure that is not an \
                         instance: {line}"
                    );
                }
            }
        }
    }
}

#[test]
fn a_non_tail_call_stays_a_call_in_the_emitted_c() {
    // N1: `deep n + 1` is not a tail call, so its function calls itself.
    let c = emitted(&program("non_tail_deep_1m"), "deep", "c", "0");
    let recs = rec_functions(&c, "deep");
    assert!(!recs.is_empty(), "no recursive function of `deep` in\n{c}");
    for (signature, body) in recs {
        let symbol = c_symbol(signature);
        assert!(
            calls_itself(symbol, body),
            "`{symbol}` must still call itself:\n{body}"
        );
    }
}

/// The trust-ir text's functions, in module order (`call @func.<i>` names
/// the `i`-th), each as its name and its text.
#[cfg(feature = "trust-ir-backend")]
fn tir_functions(tir: &str) -> Vec<(&str, &str)> {
    let mut found = Vec::new();
    let mut rest = tir;
    while let Some(at) = rest.find("\nfn @") {
        let head = &rest[at + 1..];
        let name = head["fn @".len()..].split('(').next().unwrap_or_default();
        let end = head.find("\n}\n").map_or(head.len(), |i| i + 3);
        found.push((name, &head[..end]));
        rest = &head[end - 1..];
    }
    found
}

/// The block a `br bbN(...)` line jumps to, if it is one.
#[cfg(feature = "trust-ir-backend")]
fn branch_target(line: &str) -> Option<usize> {
    let rest = line.trim_start().strip_prefix("br bb")?;
    let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
    digits.parse().ok()
}

/// The first `clean_apply_*` call in a trust-ir function `body` whose closure
/// argument is not the result of a call of an instance (`inst…`) in that
/// body: the trust-ir form of [`non_instance_closure`].
#[cfg(feature = "trust-ir-backend")]
fn tir_non_instance_closure<'a>(fns: &[(&str, &str)], body: &'a str) -> Option<&'a str> {
    let callee_of = |line: &str| -> Option<usize> {
        line.split("call @func.")
            .nth(1)?
            .split('(')
            .next()?
            .parse()
            .ok()
    };
    body.lines().find(|line| {
        let Some(applied) = callee_of(line) else {
            return false;
        };
        if !fns
            .get(applied)
            .is_some_and(|(n, _)| n.starts_with("clean_apply_"))
        {
            return false;
        }
        let closure = line
            .split(&format!("call @func.{applied}("))
            .nth(1)
            .and_then(|args| args.split([',', ')']).next())
            .unwrap_or_default()
            .trim();
        let defined_by_instance = body
            .lines()
            .find(|l| {
                l.trim_start()
                    .starts_with(&format!("{closure} = call @func."))
            })
            .and_then(callee_of)
            .and_then(|i| fns.get(i))
            .is_some_and(|(n, _)| n.starts_with("inst"));
        !defined_by_instance
    })
}

/// trust-ir: each pure loop's recursive function branches back to a block
/// it already defined, never calls itself, and applies no closure but an
/// instance.
#[cfg(feature = "trust-ir-backend")]
#[test]
fn recursive_functions_are_loops_in_the_emitted_trust_ir() {
    for opt in OPT_LEVELS {
        for (name, decl) in STRICT_LOOPS {
            let tir = emitted(&program(name), decl, "trustir", opt);
            let fns = tir_functions(&tir);
            let rec_name = format!("_lifted.{decl}._rec.");
            let recs: Vec<(usize, &str)> = fns
                .iter()
                .enumerate()
                .filter(|(_, (n, _))| {
                    n.strip_prefix(&rec_name)
                        .is_some_and(|k| !k.is_empty() && k.bytes().all(|b| b.is_ascii_digit()))
                })
                .map(|(i, (_, body))| (i, *body))
                .collect();
            assert!(
                !recs.is_empty(),
                "{name} O{opt}: no `{rec_name}*` in\n{tir}"
            );
            for (idx, body) in recs {
                let mut defined = 0usize;
                let mut back_edge = false;
                for line in body.lines() {
                    if let Some(label) = line.strip_prefix("bb") {
                        let digits: String =
                            label.chars().take_while(char::is_ascii_digit).collect();
                        if let Ok(n) = digits.parse::<usize>() {
                            defined = defined.max(n);
                        }
                    }
                    if branch_target(line).is_some_and(|t| t <= defined) {
                        back_edge = true;
                    }
                }
                assert!(back_edge, "{name} O{opt}: no back edge in\n{body}");
                assert!(
                    !body.contains(&format!("call @func.{idx}(")),
                    "{name} O{opt}: the recursive function calls itself:\n{body}"
                );
                if let Some(line) = tir_non_instance_closure(&fns, body) {
                    panic!(
                        "{name} O{opt}: the recursive function applies a closure that is \
                         not an instance: {line}\n{body}"
                    );
                }
            }
        }
    }
}
