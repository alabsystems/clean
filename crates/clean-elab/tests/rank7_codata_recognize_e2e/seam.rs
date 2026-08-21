// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The seam: lowering output feeds emission input.
//!
//! Split out of the parent integration test on 2026-08-20, unchanged, because
//! adding the Trust opt-out probe to `compile_and_run` (ebf64852a) carried the
//! parent from 493 to 518 lines and broke the paragon `files_over_500` ratchet.
//! Same child-module device the B7 artifacts already use; every test and every
//! assertion below is byte-identical to what the parent ran.

use super::*;

/// Compile and run an emitted program, returning stdout lines.
fn compile_and_run(src: &str, stem: &str) -> Option<Vec<String>> {
    use std::process::Command;
    let dir = tempfile::tempdir().expect("tempdir");
    let src_path = dir.path().join(format!("{stem}.rs"));
    let bin_path = dir.path().join(stem);
    std::fs::write(&src_path, src).expect("write");
    // TRUST OPT-OUT — see `clean-elab/src/tactic/native_decide_eval.rs`, which
    // hit the identical problem and carries the full rationale.
    //
    // `rustc` resolves through rustup from this repo's `rust-toolchain.toml`,
    // pinned to `channel = "trust"` since 2026-08-18. It therefore ran Trust's
    // obligation checker over this EMITTED program and failed the build on
    // `[overflow:add]` obligations it could not discharge statically. The
    // emitted program is an extraction ARTIFACT being executed for a
    // differential check, not a verification target.
    //
    // Probe rather than assume: the flag is trust-only and its spelling has
    // already moved once, so fall back to a plain invocation when the compiler
    // does not understand it.
    let run_rustc = |trust_opt_out: bool| {
        let mut cmd = Command::new("rustc");
        cmd.args(["--edition=2021", "-O"]);
        if trust_opt_out {
            cmd.arg("-Ztrust-verify=off");
        }
        cmd.arg("-o").arg(&bin_path).arg(&src_path).output()
    };
    let flag_was_rejected = |stderr: &str| {
        stderr.contains("only accepted on the nightly compiler")
            || stderr.contains("unknown unstable option")
            || stderr.contains("unknown debugging option")
            || stderr.contains("incorrect value")
    };
    let mut out = run_rustc(true).ok()?;
    if !out.status.success() && flag_was_rejected(&String::from_utf8_lossy(&out.stderr)) {
        out = run_rustc(false).ok()?;
    }
    assert!(
        out.status.success(),
        "emitted program must compile:\n{}\n--- src ---\n{src}",
        String::from_utf8_lossy(&out.stderr)
    );
    let run = Command::new(&bin_path).output().expect("run");
    assert!(
        run.status.success(),
        "emitted program must run cleanly:\n{}",
        String::from_utf8_lossy(&run.stderr)
    );
    Some(
        String::from_utf8_lossy(&run.stdout)
            .lines()
            .map(str::to_string)
            .collect(),
    )
}

/// THE SEAM: the IR the LOWERING produced is the IR the EMITTER compiles.
///
/// This test exists because an adversarial review established that the
/// "end to end" claim was not mechanically backed. Every emitter test fed
/// `emit_program` a `Corec` written by hand in the test file, and
/// `lower_recognized`'s output was only ever handed to the interpreter. The
/// two halves of the chain were joined by the author retyping the IR.
///
/// The review's demonstration: replacing `lower_recognized`'s body with `None`
/// left every emitter test green, and deleting the emitter left every chain
/// test green. Neither half's failure was observable from the other, so
/// "source → recognition → IR → emitted Rust → binary stdout" described a path
/// no test walked.
///
/// Here the binary's stdout is produced from IR that came out of the lowering,
/// and compared against values the KERNEL proved about the source. Break any
/// stage — recognition, lowering, emission — and this goes red.
#[test]
fn the_lowered_ir_is_what_the_emitter_compiles() {
    const SRC: &str = r#"
codata St : Type where
  head : Nat
  tail : St

codef count (n : Nat) : St where
  head := n
  tail := count (Nat.succ n)

theorem k0 : St.head (count 5) = 5 := rfl
theorem k1 : St.head (St.tail (count 5)) = 6 := rfl
theorem k2 : St.head (St.tail (St.tail (count 5))) = 7 := rfl
"#;
    let env = elab(SRC);
    let name = Name::from_string("count");
    let value = env
        .get_const(&name)
        .and_then(|i| i.value.clone())
        .expect("registered");

    let rec = recognize_codata_corec(&env, &name, &value).expect("recognized");
    let ir = clean_compiler::extraction_ir::lower::lower_recognized(&env, &rec).expect("lowers");

    // The emitted source is generated FROM the lowered IR -- not from a
    // hand-written copy of it.
    let src = clean_compiler::extraction_ir::emit_rust::emit_program(&ir, &[5], 8);
    let Some(lines) = compile_and_run(&src, "seam_count") else {
        eprintln!("rustc unavailable — skipping execution check");
        return;
    };

    // Kernel-proved prefix (k0/k1/k2 above), then the continuation.
    assert_eq!(&lines[0..3], &["5", "6", "7"]);
    for (k, line) in lines.iter().enumerate() {
        assert_eq!(line.parse::<u64>().expect("numeric"), 5 + k as u64);
    }
}

/// The same seam for the INDEXED lane, whose index step comes from `tgtF`.
///
/// Pinned separately because the index step is read from a different constant
/// than everything else, and because the observation here never reads the
/// index — so an index dropped entirely would be invisible without this.
#[test]
fn the_lowered_indexed_ir_is_what_the_emitter_compiles() {
    let env = elab(INDEXED);
    let name = Name::from_string("doubler");
    let value = env
        .get_const(&name)
        .and_then(|i| i.value.clone())
        .expect("registered");
    let rec = recognize_codata_corec(&env, &name, &value).expect("recognized");
    let ir = clean_compiler::extraction_ir::lower::lower_recognized(&env, &rec).expect("lowers");

    // Observation: the kernel-proved doubling, from lowered IR.
    let src = clean_compiler::extraction_ir::emit_rust::emit_program(&ir, &[0, 1], 8);
    let Some(lines) = compile_and_run(&src, "seam_doubler") else {
        eprintln!("rustc unavailable — skipping execution check");
        return;
    };
    assert_eq!(&lines[0..4], &["1", "2", "4", "8"]);

    // Index: re-point the observation at the index slot, so a dropped or
    // mis-wired index step cannot hide behind an observation that ignores it.
    let mut idx_ir = ir;
    idx_ir.observe = clean_compiler::extraction_ir::Op::State(0);
    let src = clean_compiler::extraction_ir::emit_rust::emit_program(&idx_ir, &[7, 1], 6);
    let Some(lines) = compile_and_run(&src, "seam_index") else {
        return;
    };
    assert_eq!(lines, vec!["7", "8", "9", "10", "11", "12"]);
}
