// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dispatcher for `clean kernel …`.
//!
//! Epic #3436 Phase 3: bundles four orphan kernel binaries under a single
//! top-level verb tree. See `clean_kernel::cli::KernelCommands` for the
//! user-facing surface.
//!
//! Handler strategy (per sub-verb):
//!
//! - **`lrat-conform` (#3443):** in-process. See [`lrat`].
//! - **`soundness-gate` (#3444):** shell-out. See [`soundness`].
//! - **`generate-lean4-baseline` (#3445):** in-process. See [`generate_baseline`].
//! - **`verify-gamma-crown` (#3446):** in-process, feature-gated. See
//!   [`gamma_crown`].
//! - **`verify-constructive-claims` (#3498, #3510):** in-process, feature-gated.
//!   See [`constructive_claims`]. Delegates to
//!   `clean_kernel::env::constructive_claims::build_audit` so both this
//!   handler and the compat-shim binary emit byte-identical JSON.
//! - **`cert verify|inspect|stats` (#3447):** in-process. See [`cert`].
//!
//! Each handler lives in its own file to keep per-file line counts under the
//! 500-line cap and to group related helpers next to their entry point.

use clean_kernel::cli::KernelCommands;

mod cert;
mod classify;
mod constructive_claims;
mod gamma_crown;
mod generate_baseline;
mod lrat;
mod soundness;

pub(crate) fn handle_kernel_command(command: KernelCommands) -> anyhow::Result<()> {
    match command {
        KernelCommands::LratConform {
            ay_lrat_check,
            cake_lpr,
            update_report,
        } => lrat::run(ay_lrat_check, cake_lpr, update_report),
        KernelCommands::SoundnessGate => soundness::run(),
        KernelCommands::VerifyGammaCrown { json, csv, latex } => gamma_crown::run(json, csv, latex),
        KernelCommands::Cert { command } => cert::dispatch(command),
        KernelCommands::GenerateLean4Baseline { output } => generate_baseline::run(output),
        KernelCommands::VerifyConstructiveClaims {
            conjecture,
            allow_empty,
        } => constructive_claims::run(conjecture, allow_empty),
        KernelCommands::Classify {
            names,
            all_constructive,
            why_rejected,
        } => classify::run(names, all_constructive, why_rejected),
    }
}
