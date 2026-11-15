// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! lean4export NDJSON Front Door Fuzz Target
//!
//! Fuzzes `clean_olean::ndjson::check_export_reader` -- the strict reader, the
//! `.olean` structural tier and the replay behind `clean olean replay
//! --from-export` -- with random byte sequences. An export is untrusted input
//! on the kernel's trust path (Lake's external kernels and the Kernel Arena
//! hand it over as is) and must never panic: every input is accepted,
//! rejected or declined. The heartbeat budget bounds each kernel check, so a
//! fuzz input cannot make one run unbounded.
//!
//! Run it as cargo-fuzz builds by default (optimized, debug assertions OFF):
//! with `-a`/`--debug-assertions` or `--dev`, the kernel's debug-only
//! invariants (`infer_type`'s "type of type must be a Sort") fire on ill-typed
//! input the release checks refuse -- the arena's
//! `bad/bugs/proj-of-subst-prop` is one -- and libFuzzer reports that as a
//! crash. Seeds and a dictionary sit beside this target (`seeds/clean_ndjson/`,
//! three of them from the Kernel Arena's Round 2026-09, Zenodo record 22944094,
//! Apache-2.0; `dicts/clean_ndjson.dict`):
//! `cargo fuzz run clean_ndjson corpus/clean_ndjson seeds/clean_ndjson --
//! -dict=dicts/clean_ndjson.dict` (STOCK EXCEPTION, see `fuzz/Cargo.toml`).

#![no_main]

use clean_olean::ndjson::{check_export_reader, ExportCheckOptions};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let report = check_export_reader(
        data,
        ExportCheckOptions {
            max_heartbeats: 100_000,
            axiom_closures: true,
        },
    );
    // The verdict is always one of the three codes.
    assert!(report.exit_code <= 2);
});
