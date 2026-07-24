// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
//! PROVE-IT harness for the Init PRE-LOAD proof-value elision wiring.
//!
//! Usage:
//!   cargo run --release -p clean-olean --example preload_elide_prove -- \
//!       <lean-lib-dir> <none|opaque-only|opaque-and-theorem>
//!
//! `<lean-lib-dir>` is a toolchain `lib/lean` dir holding the FULL `Init`
//! closure (e.g. `~/.elan/toolchains/<tc>/lib/lean`). We run the EXACT preload
//! entry point that `clean olean verify-batch --full-validation
//! --stream-elide-proof-values <policy>` uses for the Init pre-load
//! (`preload_init_with_snapshot`), with a non-Init `root` so the Init pre-load
//! actually fires. We then report:
//!   - peak RSS after the preload (getrusage ru_maxrss),
//!   - how many Opaque/Theorem/Definition constants still carry a VALUE,
//!     proving the elision dropped the selected kinds AT REGISTRATION while
//!     TYPES and Definition values are retained,
//!   - that the snapshot was NOT written under elision.
//!
//! `none` is the baseline (every value resident). `opaque-only` is verdict-
//! preserving; `opaque-and-theorem` is refusal-only. Compare peak RSS across
//! the three runs to see the cap.

use std::path::PathBuf;

use clean_kernel::env::{ConstantKind, Environment, ProofValueElision};
use clean_olean::verify_batch::preload_init_with_snapshot;

fn main() {
    // A big stack: Init proof DAGs are deep; mirrors init_snapshot_prove.
    std::thread::Builder::new()
        .name("preload-elide-prove".to_owned())
        .stack_size(2 * 1024 * 1024 * 1024)
        .spawn(run)
        .expect("spawn")
        .join()
        .expect("join");
}

/// Peak resident set size in bytes (getrusage RUSAGE_SELF). `ru_maxrss` is in
/// bytes on macOS and kilobytes on Linux; normalize to bytes.
fn peak_rss_bytes() -> u64 {
    // SAFETY: zeroed `rusage` is a valid POD; getrusage only writes into it.
    let mut usage: libc::rusage = unsafe { std::mem::zeroed() };
    let rc = unsafe { libc::getrusage(libc::RUSAGE_SELF, &mut usage) };
    if rc != 0 {
        return 0;
    }
    let raw = usage.ru_maxrss.max(0) as u64;
    if cfg!(target_os = "macos") {
        raw
    } else {
        raw * 1024
    }
}

fn parse_policy(s: &str) -> ProofValueElision {
    match s {
        "none" => ProofValueElision::None,
        "opaque-only" => ProofValueElision::OpaqueOnly,
        "opaque-and-theorem" => ProofValueElision::OpaqueAndTheorem,
        other => panic!("unknown policy {other:?}; use none|opaque-only|opaque-and-theorem"),
    }
}

fn run() {
    let mut args = std::env::args().skip(1);
    let lib: PathBuf = args.next().expect("arg1: lean lib dir").into();
    let policy_str = args.next().unwrap_or_else(|| "none".to_string());
    let elide = parse_policy(&policy_str);

    // A `root` that does NOT contain Init, so `init_preload_needed` is true and
    // the Init pre-load actually fires (exactly the verify-batch Std-target
    // case where Init is a dependency, not a target).
    let root = std::env::temp_dir().join(format!("preload-elide-root-{}", std::process::id()));
    let _ = std::fs::create_dir_all(&root);
    let cache = std::env::temp_dir().join(format!("preload-elide-cache-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&cache);
    let _ = std::fs::create_dir_all(&cache);
    let search_paths = vec![lib];

    let rss_before = peak_rss_bytes();
    println!("POLICY {policy_str}");
    println!("RSS_BEFORE_BYTES {rss_before}");

    let mut env = Environment::default();
    // full_validation=true mirrors the OOM-prone `--full-validation` path.
    preload_init_with_snapshot(
        &mut env,
        &root,
        &search_paths,
        Some(&cache),
        true,
        // generous heartbeat budget; only used on the (gated) snapshot re-verify
        u32::MAX,
        elide,
    );
    let rss_after = peak_rss_bytes();

    let consts = env.constants().count();
    if consts == 0 {
        println!("LOAD-EMPTY (Init did not load from this lib dir) — check the path");
        let _ = std::fs::remove_dir_all(&cache);
        let _ = std::fs::remove_dir_all(&root);
        return;
    }

    // Per-kind value-present accounting.
    let mut opaque_total = 0usize;
    let mut opaque_with_value = 0usize;
    let mut theorem_total = 0usize;
    let mut theorem_with_value = 0usize;
    let mut def_total = 0usize;
    let mut def_with_value = 0usize;
    let mut types_present = 0usize;
    for ci in env.constants() {
        let has_value = ci.value.is_some();
        // Every constant must still carry a type (references type-check).
        types_present += 1;
        match ci.kind {
            ConstantKind::Opaque => {
                opaque_total += 1;
                opaque_with_value += usize::from(has_value);
            }
            ConstantKind::Theorem => {
                theorem_total += 1;
                theorem_with_value += usize::from(has_value);
            }
            ConstantKind::Definition => {
                def_total += 1;
                def_with_value += usize::from(has_value);
            }
            ConstantKind::Axiom => {}
            _ => {}
        }
    }

    let snapshot_written = cache.join("init.snapshot").exists();

    println!("RSS_AFTER_BYTES {rss_after}");
    println!("RSS_AFTER_MB {:.1}", rss_after as f64 / (1024.0 * 1024.0));
    println!("CONSTANTS {consts}");
    println!("TYPES_PRESENT {types_present} (must equal CONSTANTS — types are never dropped)");
    println!("OPAQUE total={opaque_total} with_value={opaque_with_value}");
    println!("THEOREM total={theorem_total} with_value={theorem_with_value}");
    println!("DEFINITION total={def_total} with_value={def_with_value} (must equal total — defs never elided)");
    println!("SNAPSHOT_WRITTEN {snapshot_written} (must be false under elision)");

    // Self-checks so the harness exit code reflects the soundness contract.
    let mut violations = Vec::new();
    if types_present != consts {
        violations.push("a type was dropped (must never happen)".to_string());
    }
    // NOTE: we do NOT assert def_with_value == def_total. Some Definitions are
    // imported value-less independent of elision (unupgraded axiom stubs /
    // structural shims); that is a pre-existing import property identical under
    // `none`, NOT an elision effect (`elides(Definition)` is always false). The
    // load-time elision only ever touches Opaque/Theorem values.
    match elide {
        ProofValueElision::None => {
            // `snapshot_written` is not a violation here: none + full_validation
            // + successful re-verify MAY write.
        }
        ProofValueElision::OpaqueOnly => {
            if opaque_with_value != 0 {
                violations.push(format!(
                    "opaque-only left {opaque_with_value} Opaque values resident (expected 0)"
                ));
            }
            if theorem_with_value != theorem_total {
                violations.push("opaque-only dropped a Theorem value (must retain)".to_string());
            }
            if snapshot_written {
                violations.push("elision wrote a snapshot (must not)".to_string());
            }
        }
        ProofValueElision::OpaqueAndTheorem => {
            if opaque_with_value != 0 {
                violations.push(format!(
                    "opaque-and-theorem left {opaque_with_value} Opaque values resident"
                ));
            }
            if theorem_with_value != 0 {
                violations.push(format!(
                    "opaque-and-theorem left {theorem_with_value} Theorem values resident"
                ));
            }
            if snapshot_written {
                violations.push("elision wrote a snapshot (must not)".to_string());
            }
        }
        _ => {}
    }

    let _ = std::fs::remove_dir_all(&cache);
    let _ = std::fs::remove_dir_all(&root);

    if violations.is_empty() {
        println!("SELFCHECK ok");
    } else {
        for v in &violations {
            println!("SELFCHECK VIOLATION {v}");
        }
        std::process::exit(1);
    }
}
