// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Census of the imported-recursor check over a real module closure: load a
//! module (and its closure) through the production loader, time it, and group
//! every recursor the kernel refused by reason.
//!
//! Usage:
//!   recursor_import_census <Module.Name> <prelude|bare> <search-path>...
//!
//! `prelude` starts from `Environment::try_with_prelude_for_import()`, the
//! environment both `clean check --imports-prefer-olean` and the Mathlib
//! kernel-verification closure load into; `bare` starts empty.
use clean_kernel::env::Environment;
use clean_olean::import::load_module_with_deps_bounded_shared;
use std::collections::BTreeMap;
use std::path::PathBuf;
use std::time::Instant;

fn reason_class(reason: &str) -> String {
    // "imported family record X refused: <detail>" -> the detail up to its first
    // variable part, so refusals group by kind.
    let detail = reason.split(" refused: ").nth(1).unwrap_or(reason);
    let cut = detail
        .find([':', '(', '{'])
        .map_or(detail, |i| &detail[..i]);
    cut.chars().take(90).collect()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let [_, module, mode, paths @ ..] = args.as_slice() else {
        eprintln!("usage: recursor_import_census <Module> <prelude|bare> <search-path>...");
        std::process::exit(2);
    };
    let search: Vec<PathBuf> = paths.iter().map(PathBuf::from).collect();
    let mut env = match mode.as_str() {
        "prelude" => Environment::try_with_prelude_for_import().unwrap_or_else(|e| {
            eprintln!("prelude: {e}");
            std::process::exit(1)
        }),
        _ => Environment::default(),
    };
    let recursors_before = env.recursors().count();
    let mut visited = hashbrown::HashSet::new();
    let start = Instant::now();
    let summaries = match load_module_with_deps_bounded_shared(
        &mut env,
        module,
        &search,
        100_000,
        &mut visited,
    ) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("load FAILED: {e}");
            std::process::exit(1);
        }
    };
    let load_ms = start.elapsed().as_millis();
    let mut classes: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut skipped_total = 0usize;
    for s in &summaries {
        for sk in &s.skipped_constants {
            skipped_total += 1;
            if sk.reason.contains("imported family record") {
                classes
                    .entry(reason_class(&sk.reason))
                    .or_default()
                    .push(format!("{}  <- {}", sk.name, sk.reason));
            }
        }
    }
    let refused: usize = classes.values().map(Vec::len).sum();
    println!("=== recursor_import_census ===");
    println!("module            : {module}");
    println!("mode              : {mode}");
    println!("modules loaded    : {}", summaries.len());
    println!(
        "constants added   : {}",
        summaries.iter().map(|s| s.added_constants).sum::<usize>()
    );
    println!("load wall ms      : {load_ms}");
    println!(
        "recursors in env  : {} (prelude/native before load: {recursors_before})",
        env.recursors().count()
    );
    println!(
        "Quot.lift kernel-built : {}",
        env.get_quot(&clean_kernel::name::Name::from_string("Quot.lift"))
            .is_some()
    );
    println!("skipped (any)     : {skipped_total}");
    println!("family records refused : {refused}");
    for (class, rows) in &classes {
        let names: std::collections::BTreeSet<&str> = rows
            .iter()
            .filter_map(|row| row.split("  <- ").next())
            .collect();
        println!(
            "  [{} records, {} distinct] {class}",
            rows.len(),
            names.len()
        );
        for name in &names {
            println!("      {name}");
        }
        if let Some(row) = rows.first() {
            println!("      e.g. {}", row.chars().take(400).collect::<String>());
        }
    }
}
