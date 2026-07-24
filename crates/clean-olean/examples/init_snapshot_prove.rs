// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
//! PROVE-IT harness for the Phase-1 `.clean-cache` Init snapshot (load-time).
//!
//! Usage:
//!   cargo run --release -p clean-olean --example init_snapshot_prove -- \
//!       <lean-lib-dir> <cache-dir> [module]
//!
//! `<lean-lib-dir>` is a toolchain `lib/lean` dir with a FULL closure for
//! `[module]` (default `Init.Core`, small enough to dodge the P3 full-`Init`
//! memory wall while still exercising a real multi-hundred-constant closure).
//!
//! Demonstrates the LOAD-TIME half:
//!   1. COLD: `load_module_with_deps(module)` — the slow path (parse+import+
//!      reconstruct), timed.
//!   2. WARM: `Environment::load_snapshot` of that env — seconds, timed.
//!   3. EQ:   warm env identical to cold (constant/inductive counts + types).
//!   4. TAMPER: bump the snapshot version -> `load_snapshot` returns Mismatch
//!      (the gate refuses reuse), proving fail-safe fallback.

use std::path::PathBuf;
use std::time::Instant;

use clean_kernel::env::{Environment, SnapshotHeader, SnapshotLoadOutcome, SNAPSHOT_VERSION};
use clean_olean::load_module_with_deps;

fn main() {
    std::thread::Builder::new()
        .name("snap-prove".to_owned())
        .stack_size(1024 * 1024 * 1024)
        .spawn(run)
        .expect("spawn")
        .join()
        .expect("join");
}

fn run() {
    let mut args = std::env::args().skip(1);
    let lib: PathBuf = args.next().expect("arg1: lean lib dir").into();
    let cache: PathBuf = args.next().expect("arg2: cache dir").into();
    let module = args.next().unwrap_or_else(|| "Init.Core".to_string());
    let _ = std::fs::remove_dir_all(&cache);
    std::fs::create_dir_all(&cache).expect("mkdir cache");
    let search_paths = vec![lib];
    let snap = cache.join("init.snapshot");

    // -- COLD: full parse + import + reconstruction of the module closure. -----
    let mut cold_env = Environment::default();
    let t0 = Instant::now();
    match load_module_with_deps(&mut cold_env, &module, &search_paths) {
        Ok(_) => {}
        Err(e) => {
            println!("LOAD-ERR {module}: {e:?}");
            return;
        }
    }
    let cold_secs = t0.elapsed().as_secs_f64();
    let cold_consts = cold_env.constants().count();
    let cold_inds = cold_env.inductives().count();
    println!(
        "COLD  module={module} secs={cold_secs:.3} constants={cold_consts} inductives={cold_inds}"
    );

    // -- WRITE the snapshot (in production this is gated on a successful full
    //    re-verify; here we isolate the load-time mechanism cost). -------------
    let hdr = SnapshotHeader::current("prove-it-closure-hash");
    cold_env.save_snapshot(&snap, hdr.clone()).expect("save");
    let bytes = std::fs::metadata(&snap).map(|m| m.len()).unwrap_or(0);
    println!("SNAP  bytes={bytes}");

    // -- WARM: restore from snapshot, timed. ----------------------------------
    let tr = Instant::now();
    let warm_env = match Environment::load_snapshot(&snap, &hdr).expect("load") {
        SnapshotLoadOutcome::Loaded(e) => *e,
        SnapshotLoadOutcome::Mismatch(_) => panic!("matching header must Load"),
    };
    let warm_secs = tr.elapsed().as_secs_f64();
    println!(
        "WARM  secs={warm_secs:.3} constants={}",
        warm_env.constants().count()
    );
    println!(
        "SPEEDUP cold={cold_secs:.3}s warm={warm_secs:.3}s factor={:.1}x",
        cold_secs / warm_secs.max(1e-9)
    );

    // -- EQ: warm env identical to cold. --------------------------------------
    let mut ok = 0usize;
    let mut mism = 0usize;
    for ci in cold_env.constants() {
        match warm_env.get_const(&ci.name) {
            Some(w) if w.type_ == ci.type_ => ok += 1,
            _ => mism += 1,
        }
    }
    println!(
        "EQ    cold_consts={cold_consts} warm_consts={} types_ok={ok} mismatches={mism} \
         inds_eq={}",
        warm_env.constants().count(),
        cold_inds == warm_env.inductives().count()
    );

    // -- TAMPER: bump version; the gate must refuse to reuse. ------------------
    let mut tampered = hdr.clone();
    tampered.snapshot_version = SNAPSHOT_VERSION + 99;
    let outcome = Environment::load_snapshot(&snap, &tampered).expect("parse");
    let reused = matches!(outcome, SnapshotLoadOutcome::Loaded(_));
    println!("TAMPER reused={reused} (must be false => stale snapshot discarded, full re-verify)");

    let _ = std::fs::remove_dir_all(&cache);
}
