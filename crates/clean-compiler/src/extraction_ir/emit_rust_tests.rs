// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Safe-lazy Rust emission tests (rank 7, B5).
//!
//! These tests COMPILE AND RUN the emitted program. That is the whole point:
//! `crates/clean-compiler/tests/round_trip_compile.rs` only typechecks against
//! no-op stubs, and would happily accept an emitter that emitted nothing. An
//! extraction backend that is never executed is a code generator with no
//! evidence attached.
//!
//! `rustc` is invoked directly rather than through cargo, so the emitted crate
//! is compiled exactly as written — including its `#![forbid(unsafe_code)]`,
//! which is what turns "safe lazy Rust" from a description into a checked
//! property.

use super::*;
use crate::extraction_ir::{eval_nth, Corec, Op};

/// `doubler` in extraction form: state `[n, acc]`, observe `acc`, step
/// `[n+1, acc+acc]`. The same term the reference-semantics tests use.
fn doubler() -> Corec {
    Corec {
        init: vec![Op::Param(0), Op::Param(1)],
        observe: Op::State(1),
        step: vec![
            Op::Succ(Box::new(Op::State(0))),
            Op::Add(Box::new(Op::State(1)), Box::new(Op::State(1))),
        ],
    }
}

/// Compile `src` with rustc and run it, returning stdout lines.
///
/// Returns `None` if rustc is unavailable, so the suite degrades to skipping
/// rather than failing on a machine without a toolchain. A compile FAILURE is
/// never a skip — it panics with the compiler's diagnostics.
/// Invoke `rustc` on an EMITTED program, opting out of Trust verification.
///
/// See `clean-elab/src/tactic/native_decide_eval.rs` for the full rationale.
/// In short: `rustc` resolves through rustup from this repo's
/// `rust-toolchain.toml`, pinned to `channel = "trust"` since 2026-08-18, so it
/// ran Trust's obligation checker over these emitted programs and failed the
/// build on `[overflow:add]` obligations it could not discharge statically.
/// These programs are extraction ARTIFACTS executed for a differential check,
/// not verification targets.
///
/// Probe rather than assume — the flag is trust-only and its spelling has moved
/// once already, so fall back to a plain invocation when it is not understood.
fn rustc_emit(
    src_path: &std::path::Path,
    bin_path: &std::path::Path,
) -> std::io::Result<std::process::Output> {
    use std::process::Command;
    let run = |trust_opt_out: bool| {
        let mut cmd = Command::new("rustc");
        cmd.arg("--edition=2021").arg("-O");
        if trust_opt_out {
            cmd.arg("-Ztrust-verify=off");
        }
        cmd.arg("-o").arg(bin_path).arg(src_path).output()
    };
    let flag_was_rejected = |stderr: &str| {
        stderr.contains("only accepted on the nightly compiler")
            || stderr.contains("unknown unstable option")
            || stderr.contains("unknown debugging option")
            || stderr.contains("incorrect value")
    };
    let out = run(true)?;
    if !out.status.success() && flag_was_rejected(&String::from_utf8_lossy(&out.stderr)) {
        return run(false);
    }
    Ok(out)
}

fn compile_and_run(src: &str, stem: &str) -> Option<Vec<String>> {
    use std::process::Command;

    let dir = tempfile::tempdir().expect("tempdir");
    let src_path = dir.path().join(format!("{stem}.rs"));
    let bin_path = dir.path().join(stem);
    std::fs::write(&src_path, src).expect("write source");

    let out = match rustc_emit(&src_path, &bin_path) {
        Ok(o) => o,
        // No toolchain on this machine.
        Err(_) => return None,
    };
    assert!(
        out.status.success(),
        "the EMITTED program must compile under #![forbid(unsafe_code)]:\n\
         --- stderr ---\n{}\n--- source ---\n{src}",
        String::from_utf8_lossy(&out.stderr)
    );

    let run = Command::new(&bin_path)
        .output()
        .expect("run emitted program");
    assert!(
        run.status.success(),
        "the emitted program must run cleanly, stderr:\n{}",
        String::from_utf8_lossy(&run.stderr)
    );
    Some(
        String::from_utf8_lossy(&run.stdout)
            .lines()
            .map(str::to_string)
            .collect(),
    )
}

/// Compile, run, and return the `STEPS=` counter the emitted program reports on
/// stderr: how many tails were actually COMPUTED rather than served from cache.
fn compile_and_count_steps(src: &str, stem: &str) -> Option<u64> {
    use std::process::Command;
    let dir = tempfile::tempdir().expect("tempdir");
    let src_path = dir.path().join(format!("{stem}.rs"));
    let bin_path = dir.path().join(stem);
    std::fs::write(&src_path, src).expect("write source");
    let out = rustc_emit(&src_path, &bin_path).ok()?;
    assert!(
        out.status.success(),
        "must compile:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let run = Command::new(&bin_path).output().expect("run");
    let err = String::from_utf8_lossy(&run.stderr).to_string();
    err.lines()
        .find_map(|l| l.strip_prefix("STEPS="))
        .map(|n| n.trim().parse::<u64>().expect("numeric STEPS"))
}

/// The emitted program reproduces the values the KERNEL proved.
///
/// `tests/fixtures/codata/is2_indexed_stream.lean` proves `IS2.nth k 0
/// (doubler 0 1)` = 1, 2, 4, 8 by `rfl`. Those values survive the whole chain:
/// source → recognition → IR → emitted Rust → a compiled binary's stdout.
#[test]
fn emitted_program_matches_the_kernel_proved_values() {
    let c = doubler();
    let src = emit_program(&c, &[0, 1], 4);
    let Some(lines) = compile_and_run(&src, "doubler_proved") else {
        eprintln!("rustc unavailable — skipping execution check");
        return;
    };
    assert_eq!(lines, vec!["1", "2", "4", "8"]);
}

/// The emitted program agrees with the reference interpreter, depth by depth.
///
/// Two independent implementations of the same IR — one an interpreter in this
/// crate, one compiled machine code from emitted source. Agreement is the
/// differential the extraction claim rests on at this stage.
#[test]
fn emitted_program_agrees_with_the_reference_interpreter() {
    let c = doubler();
    let params = [3u64, 5];
    const DEPTH: u64 = 20;
    let src = emit_program(&c, &params, DEPTH);
    let Some(lines) = compile_and_run(&src, "doubler_diff") else {
        eprintln!("rustc unavailable — skipping execution check");
        return;
    };
    assert_eq!(lines.len(), DEPTH as usize);
    for (k, line) in lines.iter().enumerate() {
        let want = eval_nth(&c, k as u64, &params).expect("no black hole");
        assert_eq!(
            line.parse::<u64>().expect("numeric output"),
            want,
            "depth {k}: emitted binary disagrees with the reference interpreter"
        );
    }
}

/// A stream that reads its INDEX, so the index step is exercised in the emitted
/// code rather than only in the interpreter.
#[test]
fn emitted_program_advances_the_index() {
    let c = Corec {
        init: vec![Op::Param(0), Op::Lit(0)],
        observe: Op::State(0),
        step: vec![
            Op::Succ(Box::new(Op::State(0))),
            Op::Add(Box::new(Op::State(1)), Box::new(Op::State(1))),
        ],
    };
    let src = emit_program(&c, &[7], 6);
    let Some(lines) = compile_and_run(&src, "index_adv") else {
        eprintln!("rustc unavailable — skipping execution check");
        return;
    };
    assert_eq!(lines, vec!["7", "8", "9", "10", "11", "12"]);
}

/// The emitted source actually carries the safety attribute.
///
/// Cheap, and it fails loudly if the template is ever edited to drop it — at
/// which point every "safe lazy Rust" claim in the docs would silently become
/// unbacked.
#[test]
fn emitted_source_forbids_unsafe() {
    let src = emit_program(&doubler(), &[0, 1], 1);
    assert!(
        src.contains("#![forbid(unsafe_code)]"),
        "the emitted crate must forbid unsafe code"
    );
    assert!(
        !src.contains("unsafe "),
        "the emitted crate must contain no unsafe blocks or functions"
    );
}

/// A malformed IR gives the SAME answer in the emitted binary as in the
/// reference interpreter, rather than crashing.
///
/// The interpreter is total: an out-of-range state slot reads 0. If the emitted
/// Rust indexed directly it would panic instead, and the differential harness
/// would be comparing a number against a crash — two implementations that
/// disagree on exactly the inputs a differential is meant to catch. Both sides
/// must be total, and agree.
#[test]
fn malformed_ir_agrees_between_interpreter_and_binary() {
    let c = Corec {
        init: vec![Op::Lit(1)],
        observe: Op::State(9), // no such slot
        step: vec![Op::State(0)],
    };
    let src = emit_program(&c, &[], 3);
    let Some(lines) = compile_and_run(&src, "malformed") else {
        eprintln!("rustc unavailable — skipping execution check");
        return;
    };
    for (k, line) in lines.iter().enumerate() {
        let want = eval_nth(&c, k as u64, &[]).expect("no black hole");
        assert_eq!(
            line.parse::<u64>().expect("numeric output"),
            want,
            "depth {k}: emitted binary and interpreter must agree even on malformed IR"
        );
    }
}

/// Overflow is REFUSED by both sides, at the same depths, rather than wrapped.
///
/// An adversarial review measured the old behavior: `doubler` at k=64 printed
/// 0 where the source's value is 2^64, and the differential PASSED, because the
/// interpreter wrapped identically. Two implementations agreeing on the same
/// wrong number is worse than either failing — it converts a real source/target
/// divergence into evidence of correctness.
///
/// The source's `Nat` is unbounded and the target's word is 64 bits, so past
/// that point extraction has no faithful value. Both sides now say so.
#[test]
fn overflow_is_refused_by_both_sides_at_the_same_depth() {
    let c = doubler();
    // 1 doubled 64 times is exactly 2^64 -- the first unrepresentable value.
    const DEPTH: u64 = 67;
    let src = emit_program(&c, &[0, 1], DEPTH);
    let Some(lines) = compile_and_run(&src, "overflow") else {
        eprintln!("rustc unavailable — skipping execution check");
        return;
    };
    assert_eq!(lines.len(), DEPTH as usize);

    // k = 63 is the last representable layer.
    assert_eq!(lines[63], "9223372036854775808");
    assert_eq!(
        eval_nth(&c, 63, &[0, 1]).expect("k=63 is representable"),
        9223372036854775808
    );

    // From k = 64 on, BOTH sides refuse.
    for k in 64..DEPTH {
        assert_eq!(
            lines[k as usize], "OVERFLOW",
            "depth {k}: the emitted binary must refuse, not wrap"
        );
        assert_eq!(
            eval_nth(&c, k, &[0, 1]),
            Err(crate::extraction_ir::ForceError::Overflow),
            "depth {k}: the interpreter must refuse, not wrap"
        );
    }
}

/// Call-by-need actually DOES something: walking to depth N computes N-1 tails.
///
/// An adversarial review measured the previous emitter and found the
/// memoization was dead at runtime — MEMO-HIT count 0, and deleting the
/// caching line produced byte-identical output. `nth(k)` rebuilt the stream
/// from its initial state on every call, so no tail was ever re-forced and the
/// suspension cell was decoration.
///
/// The emitted `main` now walks ONE shared stream. That makes the memoization
/// load-bearing, and this test observes it: N-1 computed tails for depth N. An
/// emitter that memoized nothing, or that rebuilt per k, would report a
/// quadratic count here — visible instead of invisible.
#[test]
fn walking_a_shared_stream_computes_each_tail_once() {
    const DEPTH: u64 = 32;
    let src = emit_program(&doubler(), &[0, 1], DEPTH);
    let Some(steps) = compile_and_count_steps(&src, "memo_steps") else {
        eprintln!("rustc unavailable — skipping execution check");
        return;
    };
    assert_eq!(
        steps,
        DEPTH - 1,
        "depth {DEPTH} must compute exactly {} tails; a quadratic count means \
         the stream is being rebuilt per depth and nothing is memoized",
        DEPTH - 1
    );
}

/// The emitted tail is a memoized suspension, not an eager fold.
///
/// Checked structurally on the source: a `RefCell` tail cell that starts `None`
/// and is filled on force. If this ever became a plain loop the numbers would
/// still be right and the lowering would no longer be lazy, which is precisely
/// the substitution this rung must not make silently.
#[test]
fn emitted_tail_is_a_real_suspension() {
    let src = emit_program(&doubler(), &[0, 1], 1);
    assert!(
        src.contains("tail: RefCell<Option<Rc<Layer>>>"),
        "the tail must be a suspension cell"
    );
    assert!(
        src.contains("RefCell::new(None)"),
        "a fresh layer's tail must start unforced"
    );
    assert!(
        src.contains("*l.tail.borrow_mut() = Some("),
        "forcing must memoize the computed tail"
    );
}
