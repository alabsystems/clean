// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Explicit full-stdlib qualification for per-module versus shared dependency
//! loading.
//!
//! Usage:
//! `cargo run -p clean-olean --example diag_full_shared_vs_perloop -- \
//! /path/to/lean/lib/lean /path/to/report-dir`
//!
//! Both paths must load every discovered module successfully and produce the
//! same declaration inventory. Missing toolchain data and inventory drift fail.

use std::collections::HashSet;
use std::error::Error;
use std::io::Write;
use std::path::{Path, PathBuf};

use clean_kernel::Environment;
use clean_olean::{load_module_with_deps, load_modules_with_deps};

fn collect_olean_files(dir: &Path, out: &mut Vec<PathBuf>) -> std::io::Result<()> {
    for entry in std::fs::read_dir(dir)? {
        let path = entry?.path();
        if path.is_dir() {
            collect_olean_files(&path, out)?;
        } else if path.extension().and_then(|ext| ext.to_str()) == Some("olean") {
            out.push(path);
        }
    }
    Ok(())
}

fn declaration_names(env: &Environment) -> HashSet<String> {
    env.constants()
        .map(|constant| constant.name.to_string())
        .chain(env.inductives().map(|inductive| inductive.name.to_string()))
        .chain(
            env.constructors()
                .map(|constructor| constructor.name.to_string()),
        )
        .chain(env.recursors().map(|recursor| recursor.name.to_string()))
        .collect()
}

fn write_names(path: &Path, names: &[&String]) -> std::io::Result<()> {
    let mut file = std::fs::File::create(path)?;
    for name in names {
        writeln!(file, "{name}")?;
    }
    Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
    let mut args = std::env::args_os().skip(1);
    let lib = args
        .next()
        .map(PathBuf::from)
        .expect("usage: diag_full_shared_vs_perloop LEAN_LIB_DIR REPORT_DIR");
    let report_dir = args
        .next()
        .map(PathBuf::from)
        .expect("usage: diag_full_shared_vs_perloop LEAN_LIB_DIR REPORT_DIR");
    assert!(
        lib.join("Init.olean").is_file(),
        "{} does not contain Init.olean",
        lib.display()
    );
    std::fs::create_dir_all(&report_dir)?;

    let mut files = Vec::new();
    collect_olean_files(&lib, &mut files)?;
    files.sort();
    assert!(
        !files.is_empty(),
        "no .olean modules found under {}",
        lib.display()
    );
    let modules: Vec<String> = files
        .iter()
        .map(|path| {
            path.strip_prefix(&lib)
                .expect("walked file must remain under library root")
                .with_extension("")
                .components()
                .filter_map(|component| component.as_os_str().to_str())
                .collect::<Vec<_>>()
                .join(".")
        })
        .collect();
    eprintln!("discovered {} modules", modules.len());
    let search_paths = vec![lib];

    let mut per_module = Environment::default();
    for module in &modules {
        load_module_with_deps(&mut per_module, module, &search_paths)?;
    }
    let per_module_names = declaration_names(&per_module);

    let mut shared = Environment::default();
    load_modules_with_deps(&mut shared, &modules, &search_paths)?;
    let shared_names = declaration_names(&shared);

    let mut only_per_module: Vec<&String> = per_module_names.difference(&shared_names).collect();
    let mut only_shared: Vec<&String> = shared_names.difference(&per_module_names).collect();
    only_per_module.sort();
    only_shared.sort();
    write_names(&report_dir.join("only-in-per-module.txt"), &only_per_module)?;
    write_names(&report_dir.join("only-in-shared.txt"), &only_shared)?;

    println!(
        "per-module={} shared={} only-per-module={} only-shared={}",
        per_module_names.len(),
        shared_names.len(),
        only_per_module.len(),
        only_shared.len()
    );
    assert!(
        only_per_module.is_empty() && only_shared.is_empty(),
        "per-module and shared dependency loading produced different inventories"
    );
    Ok(())
}
