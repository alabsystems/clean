// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Explicit, fail-closed measurement report for real Coq stdlib SerAPI dumps.
//!
//! Usage:
//! `cargo run -p clean-mathverse --example coq_stdlib_translation_report -- \
//! /path/to/coq-sexp/stdlib`
//!
//! Every required dump must exist, import successfully, and contain at least one
//! declaration. A zero exit code therefore cannot mean that missing corpus data
//! was silently skipped. This tool reports translation outcomes; it does not
//! impose or certify a translated/axiomatized quality threshold.

use std::collections::BTreeMap;
use std::error::Error;
use std::path::PathBuf;

use clean_mathverse::coq::alpha::CoqImporter;
use clean_mathverse::shard::ShardWriter;

fn main() -> Result<(), Box<dyn Error>> {
    let base = std::env::args_os()
        .nth(1)
        .map(PathBuf::from)
        .expect("usage: coq_stdlib_translation_report /path/to/coq-sexp/stdlib");

    for module in ["Coq.Init.Logic", "Coq.Init.Datatypes", "Coq.Init.Peano"] {
        let path = base.join(format!("{module}.sexp"));
        let data = std::fs::read_to_string(&path)?;
        let mut writer = ShardWriter::new();
        let stats = CoqImporter.import_sexp(&data, &mut writer)?;
        assert!(stats.total > 0, "{module} dump contained no declarations");

        println!(
            "== {module}: total={} translated={} axiomatized={} \
             value_translation_failed={} skipped={}",
            stats.total,
            stats.translated,
            stats.axiomatized,
            stats.value_translation_failed,
            stats.skipped
        );
        let mut histogram: BTreeMap<&str, u32> = BTreeMap::new();
        for (_, reason) in &stats.value_failure_reasons {
            let key = reason.split(':').next().unwrap_or(reason);
            *histogram.entry(key).or_default() += 1;
        }
        for (reason, count) in histogram {
            println!("   drop[{count:>3}] {reason}");
        }
    }

    Ok(())
}
