// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::process::ExitCode;

// Track B1: install mimalloc as the process-wide allocator (behind `--features
// mimalloc`). The default system allocator never returns the PARAGON
// per-module high-water-mark to the OS, so RSS ratchets up to the 13 GB peak
// that OS-jetsam kills the full-corpus run; mimalloc + the per-module
// `mi_collect` purge (clean-mathverse) converts that high-water-mark into
// actually-returned RSS. Soundness-neutral: the allocator never touches the
// kernel, is_def_eq, or any verdict.
#[cfg(feature = "mimalloc")]
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

#[tokio::main]
async fn main() -> ExitCode {
    match clean_cli::run().await {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            let code = clean_cli::forwarded_exit_code(&err)
                .and_then(|code| u8::try_from(code).ok())
                .unwrap_or(1);
            eprintln!("Error: {err:#}");
            ExitCode::from(code)
        }
    }
}
