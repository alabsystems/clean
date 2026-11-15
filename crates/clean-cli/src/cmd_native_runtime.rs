// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean native-runtime` — the front door of
//! [`clean_native::native_runtime`], which writes the linkable Clean runtime
//! archive (`libclean_runtime.a`: the runtime, its external forwarders and
//! the prelude shims) that an object from `clean compile --emit obj` links
//! against. Two-language roadmap WS6.13 (F-119, scout-lean B7/C3). The step,
//! its fail-closed rules and its tests live in clean-native (LX0(b)); this
//! file only routes the parsed arguments and stdout to it.

use crate::cli::NativeRuntimeArgs;

/// Entry point wired from `dispatch_sync` in `lib.rs`.
pub(crate) fn handle_native_runtime_command(args: NativeRuntimeArgs) -> anyhow::Result<()> {
    clean_native::native_runtime::materialize(
        &args.out_dir,
        args.sources_only,
        &mut std::io::stdout().lock(),
    )
}
