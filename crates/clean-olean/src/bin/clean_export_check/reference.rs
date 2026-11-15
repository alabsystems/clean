// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The command-line quorum member that reads export bytes through the fence.

use std::io::BufReader;
use std::path::PathBuf;
use std::process::ExitCode;

use clean_olean::ndjson::reference_check_export_reader;

use super::STACK_BYTES;

const USAGE: &str =
    "usage: clean_export_check --reference [--json] [--permit <axiom>]... <export.ndjson>";

fn check(args: &[String]) -> Result<u8, String> {
    let mut permits = Vec::new();
    let mut path = None;
    let mut json = false;
    let mut it = args.iter();
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "--reference" => {}
            "--json" => json = true,
            "--permit" => permits.push(it.next().ok_or("--permit needs an axiom")?.clone()),
            flag if flag.starts_with("--") => {
                return Err(format!("unknown reference option {flag}"))
            }
            file => {
                if path.replace(PathBuf::from(file)).is_some() {
                    return Err("exactly one export path".to_owned());
                }
            }
        }
    }
    let path = path.ok_or("no export path")?;
    let file =
        std::fs::File::open(&path).map_err(|e| format!("cannot open {}: {e}", path.display()))?;
    let report = std::thread::Builder::new()
        .name("ndjson-reference".to_owned())
        .stack_size(STACK_BYTES)
        .spawn(move || {
            let permits: Vec<&str> = permits.iter().map(String::as_str).collect();
            reference_check_export_reader(BufReader::new(file), &permits)
        })
        .map_err(|e| format!("cannot start the reference entry: {e}"))?
        .join()
        .map_err(|_| "the reference entry panicked".to_owned())?;
    if json {
        println!(
            "{}",
            serde_json::to_string(&report).map_err(|e| e.to_string())?
        );
    }
    if let Some(error) = &report.reader_error {
        eprintln!("{} ({})", error.message, error.rule);
    }
    for refusal in &report.refusals {
        eprintln!("{refusal}");
    }
    for axiom in &report.unpermitted_axioms {
        eprintln!("unpermitted axiom: {axiom}");
    }
    Ok(u8::from(!report.accepted))
}

pub(super) fn run(args: &[String]) -> ExitCode {
    match check(args) {
        Ok(code) => ExitCode::from(code),
        Err(problem) => {
            eprintln!("clean_export_check --reference: {problem}\n{USAGE}");
            ExitCode::from(2)
        }
    }
}
