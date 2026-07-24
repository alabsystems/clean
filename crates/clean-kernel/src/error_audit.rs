// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `thiserror` audit for issue #1622.
//!
//! Date: 2026-03-27
//!
//! Historical note: this audit was written before the workspace reorg that
//! removed `clean-gpu` and folded the former `clean-commit` surface into
//! `clean-fold`. Treat the crate table below as a dated audit snapshot, not a
//! current workspace inventory.
//!
//! Scope checked:
//! - workspace root `Cargo.toml`
//! - every `crates/*/Cargo.toml`
//! - `fuzz/Cargo.toml`
//! - Rust sources for `thiserror::Error`, `#[derive(Error)]`, and manual
//!   `Display` / `std::error::Error` implementations
//!
//! # Summary
//!
//! - The workspace root declares `thiserror = "2.0"` in
//!   `[workspace.dependencies]`.
//! - No workspace member manifest requests `thiserror 1.x`.
//! - Every workspace member that declares `thiserror` does so via
//!   `thiserror.workspace = true`, so their manifest-level requirement is
//!   uniformly `2.0`.
//! - `Cargo.lock` is still mixed at the resolved-package level:
//!   - `thiserror 2.0.18` is used by workspace crates and several transitive
//!     dependencies.
//!   - `thiserror 1.0.69` is still present, but only through the websocket
//!     stack:
//!     `clean-server -> tokio-tungstenite 0.24.0 -> tungstenite 0.24.0 -> thiserror 1.0.69`.
//! - Conclusion: there is no workspace-member `v1` vs `v2` split to fix. The
//!   only remaining split is transitive, rooted at `clean-server`.
//!
//! # Crates Declaring `thiserror`
//!
//! All entries below resolve their manifest requirement through the workspace
//! root, so each one is effectively on `thiserror = "2.0"`.
//!
//! | Crate | Manifest requirement | Notes |
//! | --- | --- | --- |
//! | `clean-auto` | `thiserror.workspace = true` | active derive/import usage |
//! | `clean-c-sem` | `thiserror.workspace = true` | active derive/import usage |
//! | `clean-commit` | `thiserror.workspace = true` | active derive/import usage |
//! | `clean-compiler` | `thiserror = { workspace = true }` | active derive/import usage |
//! | `clean-elab` | `thiserror.workspace = true` | active derive/import usage |
//! | `clean-fold` | `thiserror.workspace = true` | active derive/import usage |
//! | `clean-gpu` | `thiserror.workspace = true` | active derive/import usage |
//! | `clean-kernel` | `thiserror.workspace = true` | active derive/import usage |
//! | `clean-lake` | `thiserror.workspace = true` | active derive/import usage |
//! | `clean-lsp` | `thiserror.workspace = true` | dependency declared, no direct code usage found |
//! | `clean-macro` | `thiserror.workspace = true` | active derive/import usage |
//! | `clean-olean` | `thiserror.workspace = true` | active derive/import usage |
//! | `clean-parser` | `thiserror.workspace = true` | active derive/import usage |
//! | `clean-runtime` | `thiserror.workspace = true` | active derive/import usage |
//! | `clean-rust-sem` | `thiserror.workspace = true` | active derive/import usage |
//! | `clean-server` | `thiserror.workspace = true` | active derive/import usage; also introduces transitive `thiserror 1.x` via websocket deps |
//! | `clean-sys` | `thiserror.workspace = true` | dependency declared, no direct code usage found |
//! | `clean-tla` | `thiserror.workspace = true` | active derive/import usage |
//! | `clean-verify` | `thiserror.workspace = true` | active derive/import usage |
//!
//! Checked and not declaring `thiserror`:
//! - `clean`
//! - `clean-cli`
//! - `clean-coq-import`
//! - `clean-tlaps-bench`
//! - `fuzz` (excluded from the workspace)
//!
//! # Version Conflict Assessment
//!
//! Manifest-level result:
//! - No conflict inside workspace members.
//! - No crate in this repository declares `thiserror = "1"` or an explicit
//!   `1.x` requirement.
//!
//! Resolved dependency graph result:
//! - `thiserror 2.0.18` is the workspace standard.
//! - `thiserror 1.0.69` is still resolved because `tungstenite 0.24.0` depends
//!   on it.
//! - Reverse-dependency chain for `1.0.69`:
//!   `tungstenite -> tokio-tungstenite -> clean-server -> clean-cli -> clean`.
//!
//! Practical implication:
//! - If issue #1622 is blocked by workspace crates disagreeing on `thiserror`
//!   major version, that blocker does not exist anymore.
//! - If the blocker is instead "the lockfile must contain only one `thiserror`
//!   major", then the websocket dependency chain owned by `clean-server` is the
//!   only place that still needs attention.
//!
//! # Manual `Display` / Error Types Worth Reviewing
//!
//! These are the main manual implementations that could plausibly be converted
//! to `thiserror`, depending on whether the goal is consistency or shared-crate
//! extraction:
//!
//! - `clean-parser::lexer::LexError`
//!   - manual `Display`
//!   - currently embedded in `TokenKind::Error(LexError)`
//!   - easy candidate for `#[derive(thiserror::Error)]` with per-variant
//!     `#[error(...)]` strings
//!
//! - `clean-elab::cert::external::ExternalCertError`
//!   - manual `Display`
//!   - manual `std::error::Error`
//!   - already structured as `{ code, detail }`
//!   - viable `thiserror` candidate, though the explicit constructor helpers and
//!     `code` field likely remain even after conversion
//!
//! - `clean-coq-import::CoqImportError`
//!   - manual `Display`
//!   - manual `std::error::Error`
//!   - does not currently depend on `thiserror`
//!   - candidate only if this crate is part of the shared extraction target or
//!     if error-style consistency is desired across the workspace
//!
//! - `clean-compiler::pass_manager::validate::ValidationError`
//!   - manual `Display`
//!   - currently used more as collected diagnostics (`Vec<ValidationError>`)
//!     than as a standalone `std::error::Error`
//!   - optional `thiserror` cleanup, but lower priority than the items above
//!
//! Lower-signal cases exist for displayable protocol/data structs, but they do
//! not currently look like meaningful `thiserror` migration targets.
//!
//! # Proposed Migration Path
//!
//! 1. Keep the workspace policy on `thiserror 2.x`. No workspace member needs a
//!    `v1 -> v2` manifest update.
//! 2. Decide whether issue #1622 cares about:
//!    - manifest consistency only, or
//!    - a single resolved `thiserror` major in `Cargo.lock`
//! 3. If manifest consistency is enough, the audit is effectively complete:
//!    all workspace members already align on `2.0`.
//! 4. If a single resolved major is required, update or replace the websocket
//!    stack under `clean-server` so `tokio-tungstenite` / `tungstenite` no
//!    longer pull `thiserror 1.x`.
//! 5. For shared crate extraction, standardize manual error types on
//!    `thiserror 2` where it reduces friction:
//!    - first: `LexError`
//!    - second: `ExternalCertError`
//!    - optional: `CoqImportError`
//!    - optional/low priority: `ValidationError`
//! 6. Remove unused `thiserror` declarations from `clean-lsp` and `clean-sys`
//!    unless there is near-term planned usage.
