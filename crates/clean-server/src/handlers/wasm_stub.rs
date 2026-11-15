// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! wasm32 replacement root for `handlers/` (`mod.rs` stays native-only).
//!
//! The request-handler tree sits on tokio (`ServerState`'s async `RwLock`,
//! timeouts, `spawn_blocking`), which has no full wasm32 backend. The one
//! handler-side capability CLI verbs need without a running server — the
//! read-only declaration validator — is tokio-free; it lives in `clean-elab`'s
//! module driver and is re-exported here exactly as the native tree does.

// Serde-only wire types shared with `proof_state` (which stays on wasm).
// `verify/types.rs` resolves `super::fill_sorries_types`, so both files are
// mounted as siblings here exactly as they sit under the native `verify`
// parent.
#[allow(dead_code)]
#[path = "verify/fill_sorries_types.rs"]
mod fill_sorries_types;
#[allow(dead_code, unused_imports)]
#[path = "verify/types.rs"]
mod verify_types;

// `fill_sorries_types` names these as `super::…`, mirroring the native
// `verify` parent's re-exports.
use verify_types::{TimingBreakdown, VerifyProofError};

pub use clean_elab::module_driver::validate_decl_read_only;
pub use verify_types::TrustSummary;

/// `proof_state` frees the states its cache lets go through this. The native
/// tree hands them to Tokio's blocking pool when the caller is a runtime
/// worker (`off_runtime.rs`); wasm has no runtime, so a value is freed where
/// it is dropped, as the native version does off a runtime.
pub(crate) fn free_off_runtime<T>(value: T) {
    drop(value);
}

/// `proof_state` shares a cached state with its readers through this. The
/// native tree frees the value off the runtime when its last holder lets it
/// go (`off_runtime.rs`); wasm has no runtime, so a plain `Arc` does what the
/// native version does off a runtime.
pub(crate) type Shared<T> = std::sync::Arc<T>;
