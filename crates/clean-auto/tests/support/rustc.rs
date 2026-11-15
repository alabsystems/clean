// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::path::PathBuf;

/// Resolve the compiler selected for the enclosing Targo invocation.
///
/// Targo does not export `RUSTC` to test processes on every platform, but it
/// does export `CARGO` (its own path): the `trustc` beside it is the compiler
/// that built the crate metadata this probe links, so the ABI matches. Last,
/// `trustc` on PATH. No rustup query, no stock `rustc` (owner directive
/// 2026-09-28).
pub fn cargo_rustc() -> PathBuf {
    if let Some(rustc) = std::env::var_os("RUSTC") {
        return rustc.into();
    }
    let trustc = format!("trustc{}", std::env::consts::EXE_SUFFIX);
    if let Some(cargo) = std::env::var_os("CARGO") {
        let sibling = PathBuf::from(cargo).with_file_name(&trustc);
        if sibling.is_file() {
            return sibling;
        }
    }
    PathBuf::from(trustc)
}
