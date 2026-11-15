// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A verb's work on a thread with a deep stack.
//!
//! `clean run` and `clean compile` elaborate, lower and emit on recursive
//! walkers, and they used to do it on the process's main thread, whose stack
//! is the shell's limit (8 MB on macOS). Measured 2026-11-12, unit X1 of
//! `docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`: a DEBUG build of
//! `clean run --backend trust-cg` on
//! `tests/fixtures/advice_replay_checker/programs/advice_replay.lean`
//! aborted with "thread 'main' has overflowed its stack" inside
//! `clean_compiler::emit_trust_ir::emit_body`, and the same command printed
//! pinned Lean's bytes once the shell's limit was raised to 12 MB. The stack a
//! verb gets must not depend on the shell that started it or on the build
//! profile, so these verbs get the stack `clean check` already takes.
//!
//! This changes how deep a correct recursion may go and nothing else: the
//! same work runs, on another thread.

/// The stack a compile-or-run verb's worker thread is given. Virtual address
/// space; only what the recursion touches is ever resident.
pub(crate) const VERB_STACK_BYTES: usize = 1024 * 1024 * 1024;

/// Run `work` on a dedicated thread named `name` with [`VERB_STACK_BYTES`] of
/// stack and return what it returned.
///
/// A panic in `work` is re-raised on the calling thread with its own payload,
/// so the process ends as it did when the work ran inline (the panic message
/// is printed once, by the worker). A `std::process::exit` inside `work` ends
/// the process from the worker, as it did from the main thread.
#[cfg(not(target_arch = "wasm32"))]
pub(crate) fn run_on_large_stack<F>(name: &'static str, work: F) -> anyhow::Result<()>
where
    F: FnOnce() -> anyhow::Result<()> + Send + 'static,
{
    let handle = std::thread::Builder::new()
        .name(name.to_string())
        .stack_size(VERB_STACK_BYTES)
        .spawn(work)
        .map_err(|e| anyhow::anyhow!("failed to spawn the {name} worker thread: {e}"))?;
    match handle.join() {
        Ok(result) => result,
        Err(payload) => std::panic::resume_unwind(payload),
    }
}

/// wasm32 has no `std::thread::spawn`; the work runs on the calling thread and
/// the link is expected to set the stack.
#[cfg(target_arch = "wasm32")]
pub(crate) fn run_on_large_stack<F>(_name: &'static str, work: F) -> anyhow::Result<()>
where
    F: FnOnce() -> anyhow::Result<()> + Send + 'static,
{
    work()
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    use super::run_on_large_stack;

    /// Recursion that keeps `depth` frames of at least 16 KiB each alive.
    fn burn(depth: usize) -> u64 {
        let pad = std::hint::black_box([depth as u8; 16 * 1024]);
        if depth == 0 {
            u64::from(pad[0])
        } else {
            burn(depth - 1) + u64::from(pad[pad.len() - 1] & 1)
        }
    }

    /// 2048 frames of 16 KiB are 32 MiB: four times the main thread's default
    /// stack and sixteen times a test thread's. Were the helper to run its
    /// closure on the caller's stack, this test would not fail an assertion:
    /// it would abort the test binary with a stack overflow, which is the
    /// loud failure wanted.
    #[test]
    fn test_run_on_large_stack_deep_recursion_completes() {
        let (tx, rx) = std::sync::mpsc::channel();
        run_on_large_stack("large-stack-test", move || {
            tx.send(burn(2048))?;
            Ok(())
        })
        .expect("the deep recursion returns");
        assert_eq!(rx.recv().expect("the worker sent its sum"), 1024);
    }

    #[test]
    fn test_run_on_large_stack_error_is_returned() {
        let err = run_on_large_stack("large-stack-test", || anyhow::bail!("refused by name"))
            .expect_err("the closure's error is the helper's error");
        assert_eq!(err.to_string(), "refused by name");
    }

    #[test]
    fn test_run_on_large_stack_panic_keeps_its_payload() {
        let caught = std::panic::catch_unwind(|| {
            run_on_large_stack("large-stack-test", || panic!("payload-7f3a"))
        });
        let payload = caught.expect_err("the worker's panic reaches the caller");
        assert_eq!(
            payload.downcast_ref::<&str>().copied(),
            Some("payload-7f3a")
        );
    }
}
