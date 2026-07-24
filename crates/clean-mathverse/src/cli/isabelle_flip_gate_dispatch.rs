// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dispatch for `mathverse isabelle-flip-gate` — the standing FLIP-GATE CI verb.
//!
//! `--check` replays every registered flip-gate slice through the real library
//! stream-verify driver (never a subprocess) and asserts each pinned serial
//! lands `KernelVerified`, reporting PASS/FAIL per gate and failing the process
//! on any FAIL. `--add` builds the minimal closure slice for a target serial,
//! confirms it flips under the current binary, pins its BLAKE3 + line count, and
//! appends the registry entry.
//!
//! Both modes acquire verify authority for the replay portion. They try, in order
//! (see [`acquire_verify_lock_waiting`]): the exclusive PRIMARY lock; then — if a
//! live grand holds it — a bounded RAM-gated SIDE-VERIFY LEASE running alongside
//! it (ending the ~30h fix→gate serialization); then, only if the side lease is
//! unavailable, **WAIT** on the primary rather than bypassing it. The acquired mode
//! is printed loudly. A flip gate is a bounded per-serial replay, exactly the
//! side-lease's intended workload.

use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use super::{IsabelleFlipGateArgs, MathverseCliError};
use crate::hol::isabelle_flip_gate::{
    build_and_pin_gate, evaluate_gate, FlipGateRegistry, GATES_DIR_PORTABLE, REGISTRY_REL_PATH,
};
use crate::hol::isabelle_pure_verify::verify_lock::{
    SideLeaseError, VerifyLockError, SIDE_RAM_FLOOR_GB,
};
use crate::hol::isabelle_pure_verify::{SideVerifyLease, VerifyLease, VerifyLock};
use crate::hol::isabelle_sessions::expand_tilde;
use crate::process_env::ScopedEnv;

fn err(e: impl std::fmt::Display) -> MathverseCliError {
    MathverseCliError::IsabelleFlipGate(e.to_string())
}

pub(super) fn cmd_isabelle_flip_gate(args: IsabelleFlipGateArgs) -> Result<(), MathverseCliError> {
    match (args.check, args.add) {
        (true, true) => {
            return Err(err("--check and --add are mutually exclusive; pick one"));
        }
        (false, false) => {
            return Err(err(
                "choose a mode: --check (verify registered gates) or --add",
            ));
        }
        _ => {}
    }

    let registry_path = args
        .registry
        .clone()
        .unwrap_or_else(|| PathBuf::from(REGISTRY_REL_PATH));
    let gates_dir = expand_tilde(
        &args
            .gates_dir
            .clone()
            .unwrap_or_else(|| PathBuf::from(GATES_DIR_PORTABLE)),
    );

    if args.check {
        run_check(&registry_path, &args)
    } else {
        run_add(&registry_path, &gates_dir, &args)
    }
}

/// Replay every registered gate and assert each serial KernelVerifies.
fn run_check(registry_path: &Path, args: &IsabelleFlipGateArgs) -> Result<(), MathverseCliError> {
    let registry = FlipGateRegistry::load(registry_path).map_err(err)?;
    if registry.gates.is_empty() {
        println!(
            "FLIP-GATE CHECK: no gates registered in {} — nothing to verify",
            registry_path.display()
        );
        return Ok(());
    }

    let _replay_env = prepare_replay_env(args.translate_budget);
    let _lease = acquire_verify_lock_waiting(args.lock_timeout_secs)?;

    let mut gates: Vec<_> = registry.gates.iter().collect();
    gates.sort_by_key(|g| g.serial);

    let mut fails = 0usize;
    for gate in &gates {
        match evaluate_gate(gate) {
            Ok(outcome) => {
                let status = if outcome.is_pass() {
                    "PASS"
                } else {
                    fails += 1;
                    "FAIL"
                };
                println!(
                    "[{status}] s{} {} — {}",
                    gate.serial,
                    gate.name,
                    outcome.describe()
                );
            }
            Err(e) => {
                fails += 1;
                println!("[FAIL] s{} {} — replay error: {e}", gate.serial, gate.name);
            }
        }
    }

    let total = gates.len();
    println!(
        "FLIP-GATE CHECK: {total} gate(s), {} PASS, {fails} FAIL",
        total - fails
    );
    if fails > 0 {
        return Err(err(format!(
            "{fails} flip gate(s) FAILED — a claimed flip is NOT corpus-routing-verified; \
             do not launch a grand until every gate passes"
        )));
    }
    Ok(())
}

/// Build + verify + register a new flip gate for `--serial`.
fn run_add(
    registry_path: &Path,
    gates_dir: &Path,
    args: &IsabelleFlipGateArgs,
) -> Result<(), MathverseCliError> {
    let corpus = args
        .corpus
        .as_ref()
        .map(|c| expand_tilde(c))
        .ok_or_else(|| err("--add requires --corpus <path>"))?;
    let serial = args
        .serial
        .ok_or_else(|| err("--add requires --serial <i64>"))?;
    if !corpus.exists() {
        return Err(err(format!("corpus {} does not exist", corpus.display())));
    }

    let mut registry = FlipGateRegistry::load(registry_path).map_err(err)?;
    let description = args
        .description
        .clone()
        .unwrap_or_else(|| format!("flip gate for serial s{serial}"));
    let round = args
        .round
        .clone()
        .unwrap_or_else(|| "unspecified".to_string());

    let _replay_env = prepare_replay_env(args.translate_budget);
    let _lease = acquire_verify_lock_waiting(args.lock_timeout_secs)?;

    let gate = build_and_pin_gate(&registry, &corpus, serial, gates_dir, &description, &round)
        .map_err(err)?;
    println!(
        "REGISTERED: s{} {} -> {} ({} lines, blake3 {}…)",
        gate.serial,
        gate.name,
        gate.slice,
        gate.lines,
        &gate.blake3[..gate.blake3.len().min(12)]
    );

    registry.gates.push(gate);
    registry.save(registry_path).map_err(err)?;
    println!(
        "FLIP-GATE ADD: registry now has {} gate(s) at {}",
        registry.gates.len(),
        registry_path.display()
    );
    Ok(())
}

/// Configure the process environment for a faithful, grand-equivalent tier-1
/// replay: keep the ledger / bridge / snapshot lanes OFF (so `kv` is exactly the
/// `KernelVerified` set), elide proof values (memory; verdict-neutral), and pin
/// the same translate budget the grand uses.
fn prepare_replay_env(translate_budget: u64) -> ScopedEnv {
    let mut env = ScopedEnv::new();
    // No resume / save: sharding is a fresh full replay with absolute line
    // indices; a stray ambient snapshot var would silently divert the driver.
    env.remove("ISA_SNAPSHOT_IN");
    env.remove("ISA_SNAPSHOT_OUT");
    // Tier-1 only: a flip gate asserts a genuine KernelVerified, never a
    // ledger/bridge-assisted verdict.
    env.remove("ISA_TRUSTED_LEDGER");
    env.remove("ISA_BRIDGE_DISCHARGE");
    env.set("ISA_ELIDE_PROOFS", "1");
    env.set("ISA_TRANSLATE_NODE_BUDGET", translate_budget.to_string());
    env.set_if_unset("ISA_PROGRESS_EVERY", "10000");
    env
}

/// Acquire verify authority for the replay, in three tiers (never bypassing):
///
/// 1. **PRIMARY** — the exclusive machine-wide lock. If free, take it and run as
///    the sole verify group.
/// 2. **SIDE LEASE** — if a live grand holds the primary, try a bounded RAM-gated
///    side lease that runs alongside it (this is what ends the ~30h fix→gate
///    serialization). A [`SideLeaseError::NoPrimary`] means the primary freed
///    between our two attempts, so we loop and take the primary.
/// 3. **WAIT** — if the side lease is unavailable (kill-switch, insufficient RAM,
///    another side lease already held, or I/O), poll the primary every 5s exactly
///    as before. `timeout_secs == 0` waits indefinitely; a positive value caps the
///    wait and then fails loud (never bypasses).
///
/// The acquired mode is printed loudly to stderr on success.
fn acquire_verify_lock_waiting(timeout_secs: u64) -> Result<VerifyLease, MathverseCliError> {
    let deadline = (timeout_secs != 0).then(|| Instant::now() + Duration::from_secs(timeout_secs));
    let mut announced_wait = false;
    loop {
        match VerifyLock::acquire_default() {
            Ok(guard) => {
                eprintln!(
                    "verify lock: acquired the PRIMARY lock (exclusive) — this is the sole verify group"
                );
                return Ok(VerifyLease::Primary(guard));
            }
            Err(VerifyLockError::Held { holder, path }) => {
                // Primary is held by a live group — try a bounded side lease.
                match SideVerifyLease::acquire_default() {
                    Ok(side) => {
                        eprintln!(
                            "verify lock: PRIMARY held by {holder} — acquired a bounded SIDE-VERIFY \
                             LEASE (est. free RAM ~{} GiB >= budget {} + {SIDE_RAM_FLOOR_GB} GiB floor); \
                             running ALONGSIDE the primary (verdict-safe: pid-unique scratch + \
                             thread-installed config; RAM is the only gated risk)",
                            side.free_ram_gb(),
                            side.budget_gb()
                        );
                        return Ok(VerifyLease::Side(side));
                    }
                    // The primary freed between our two attempts — loop and take it.
                    Err(SideLeaseError::NoPrimary) => continue,
                    // Side lease unavailable — fall back to WAITING on the primary.
                    Err(side_err) => {
                        if let Some(d) = deadline {
                            if Instant::now() >= d {
                                return Err(err(format!(
                                    "verify lock {path} still held after {timeout_secs}s \
                                     (holder: {holder}); side-verify lease unavailable ({side_err}) \
                                     — refusing to bypass; retry when it frees"
                                )));
                            }
                        }
                        if !announced_wait {
                            eprintln!(
                                "WAITING: PRIMARY verify lock held by {holder}; side-verify lease \
                                 unavailable ({side_err}) — polling every 5s (not bypassing)"
                            );
                            announced_wait = true;
                        }
                        std::thread::sleep(Duration::from_secs(5));
                    }
                }
            }
            Err(e) => return Err(err(e.to_string())),
        }
    }
}
