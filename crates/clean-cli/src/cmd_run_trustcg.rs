// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean run --backend trust-cg`: the command-line adapter over the
//! experimental trust-cg lane in `clean_native::native_trustcg` (LX0 of
//! `designs/2026-09-30-clean-trust-unified-vision.md`).
//!
//! The lane itself (core, self-checks, license, trust-cg, link) lives in
//! clean-native so Trust can call it the same way. This file only renders the
//! receipt, runs the program with inherited stdio, keeps or removes the build
//! directory, and exits the way the program did.

use anyhow::Context;
use clean_native::native_trustcg::{
    build_with_receipt_retaining, Receipt, ScratchRetention, LOWERED, RUNTIME,
};

use crate::cli::RunArgs;
use crate::cmd_run::{exit_like_program, run_inheriting_stdio};

fn write_receipt(args: &RunArgs, receipt: &Receipt) -> anyhow::Result<()> {
    match &args.receipt {
        Some(path) => {
            let json = serde_json::to_string_pretty(receipt).context("render the receipt")?;
            std::fs::write(path, format!("{json}\n"))
                .with_context(|| format!("write the receipt to {}", path.display()))
        }
        None => {
            eprintln!("{}", receipt.line());
            Ok(())
        }
    }
}

/// `clean run --backend trust-cg`.
pub(crate) fn handle_run_trustcg(args: &RunArgs) -> anyhow::Result<()> {
    let retention = if args.keep_temp {
        ScratchRetention::Keep
    } else {
        ScratchRetention::Remove
    };
    let (receipt, built) =
        build_with_receipt_retaining(&args.file, &args.decl, args.opt_level, retention);
    write_receipt(args, &receipt)?;
    if let Some(dir) = receipt.retained_directory() {
        eprintln!(
            "clean run --backend trust-cg: kept build directory at {}",
            dir.display()
        );
    }
    let built = built.map_err(|err| {
        anyhow::Error::new(err).context(format!(
            "clean run --backend trust-cg (lowered: {LOWERED}; runtime: {RUNTIME}) built nothing"
        ))
    })?;
    let status = run_inheriting_stdio(built.binary(), &args.args)?;
    // Release (or keep) the scratch directory before exiting: `exit` skips
    // destructors.
    if args.keep_temp {
        let _ = built.keep();
    } else {
        drop(built);
    }
    exit_like_program(status)
}
