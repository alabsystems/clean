// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean compile`: the command-line dispatch over Clean's native core
//! (`clean_native::compile`), which owns elaboration, declaration selection,
//! the fidelity audits and every emitter.

use std::io::Write;

use anyhow::Context;
use clean_compiler::cli::CompileArgs;
#[cfg(feature = "trust-ir-backend")]
use clean_compiler::cli::EmitFormat;
use clean_native::compile::compile_to_string;
#[cfg(feature = "trust-ir-backend")]
use clean_native::compile::{compile_to_object, compile_to_trustir_bin};

/// Entry point wired from `dispatch_sync` in `lib.rs`.
pub(crate) fn handle_compile_command(args: CompileArgs) -> anyhow::Result<()> {
    // `--link-artifact` names what a LINKABLE artifact imports; no other
    // format writes one, so accepting the flag there would silently drop it.
    #[cfg(feature = "trust-ir-backend")]
    let links_allowed = args.emit == EmitFormat::TrustirBin;
    #[cfg(not(feature = "trust-ir-backend"))]
    let links_allowed = false;
    if !args.link_artifact.is_empty() && !links_allowed {
        anyhow::bail!(
            "`--link-artifact` applies only to `--emit trustir-bin` (a build with the \
             trust-ir-backend feature); no other format records a module import"
        );
    }
    // The native-object path writes a binary file, not text to stdout.
    #[cfg(feature = "trust-ir-backend")]
    if args.emit == EmitFormat::Obj {
        return compile_to_object(&args);
    }
    // So does the linkable trust-ir artifact.
    #[cfg(feature = "trust-ir-backend")]
    if args.emit == EmitFormat::TrustirBin {
        return compile_to_trustir_bin(&args);
    }

    let output_path = args.output.clone();
    let output = compile_to_string(args)?;
    match output_path {
        Some(path) => std::fs::write(&path, output.as_bytes())
            .with_context(|| format!("failed to write output to {}", path.display()))?,
        None => {
            let mut stdout = std::io::stdout().lock();
            stdout.write_all(output.as_bytes())?;
            if !output.ends_with('\n') {
                writeln!(stdout)?;
            }
        }
    }
    Ok(())
}

#[cfg(all(test, feature = "trust-ir-backend"))]
#[path = "cmd_compile_link_artifact_tests.rs"]
mod link_artifact_tests;
