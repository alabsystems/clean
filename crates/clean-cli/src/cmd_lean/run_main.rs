// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `lean --run FILE args…`: once the file elaborated with no error, build its
//! `main` through `clean run`'s path (`clean_native`'s emit-C closure, the
//! embedded runtime, `cc`) and run it with this process's stdio, ending with
//! its status. Lean interprets `main`; Clean compiles it. What is observable
//! is the same contract `clean run` keeps: the program's bytes as written,
//! `IO UInt32`'s value as the exit status, `IO Unit` as 0.

use crate::cmd_run::{exit_disposition, run_inheriting_stdio, signal_name, ExitDisposition};
use clean_native::native_build::{emit_native_c_artifact, NativeCArtifact};
use std::path::Path;

/// Build and run `main` of `file` with `args`; the exit status to end with.
pub(crate) fn run_main(file: &Path, args: &[String]) -> i32 {
    run_artifact(emit_native_c_artifact(file, "main", 0), args)
}

/// Link and run the C emitted from the frontend's checked environment.
pub(crate) fn run_artifact(artifact: anyhow::Result<NativeCArtifact>, args: &[String]) -> i32 {
    let built = artifact.and_then(|artifact| artifact.build_in_scratch(true));
    let built = match built {
        Ok(built) => built,
        Err(error) => {
            eprintln!("clean: `lean --run`: could not build `main` natively: {error:#}");
            return 1;
        }
    };
    let status = match run_inheriting_stdio(built.binary(), args) {
        Ok(status) => status,
        Err(error) => {
            eprintln!("clean: `lean --run`: {error:#}");
            return 1;
        }
    };
    drop(built);
    match exit_disposition(status) {
        ExitDisposition::Success => 0,
        ExitDisposition::Code(code) => code,
        ExitDisposition::Signal(signal) => {
            eprintln!(
                "clean run: program terminated by signal {signal} ({})",
                signal_name(signal)
            );
            128 + signal
        }
    }
}
