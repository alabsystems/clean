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

#[cfg(not(target_arch = "wasm32"))]
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

/// wasm32 entry point: tokio has no full wasm runtime, so the CLI future is
/// driven by a minimal single-threaded executor. Every async path that could
/// genuinely suspend (server/LSP transports) is native-only and refuses on
/// wasm before awaiting I/O, so polling to completion cannot park forever.
#[cfg(target_arch = "wasm32")]
fn main() -> ExitCode {
    match block_on(clean_cli::run()) {
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

/// Minimal spin-polling executor for the wasm32 binary (no tokio on wasm).
#[cfg(target_arch = "wasm32")]
fn block_on<F: std::future::Future>(fut: F) -> F::Output {
    use std::pin::pin;
    use std::sync::Arc;
    use std::task::{Context, Poll, Wake, Waker};

    struct NoopWake;
    impl Wake for NoopWake {
        fn wake(self: Arc<Self>) {}
    }

    let waker = Waker::from(Arc::new(NoopWake));
    let mut cx = Context::from_waker(&waker);
    let mut fut = pin!(fut);
    loop {
        match fut.as_mut().poll(&mut cx) {
            Poll::Ready(value) => return value,
            Poll::Pending => std::hint::spin_loop(),
        }
    }
}
