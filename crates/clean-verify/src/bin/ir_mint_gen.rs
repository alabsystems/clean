// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regenerate the committed A2 mint artifacts from the committed core module.
//!
//! `cargo run -p clean-verify --bin ir_mint_gen -- <prefix> <core.txt> <tags.json> <out-dir>`
//!
//! The generation is pure: core module in, definition script and record out.
//! `tests/crystal_a2_mint.rs` re-runs the same pure function and fails closed
//! if the committed artifacts are not what it produces, so running this binary
//! is a convenience, never an authority.

use std::process::ExitCode;

use clean_verify::ir_mint;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let [_, prefix, core_path, tags_path, out_dir] = args.as_slice() else {
        eprintln!("usage: ir_mint_gen <prefix> <core.txt> <tags.json> <out-dir>");
        return ExitCode::from(2);
    };
    let tags_text = match std::fs::read_to_string(tags_path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("cannot read {tags_path}: {e}");
            return ExitCode::from(2);
        }
    };
    let core_text = match std::fs::read_to_string(core_path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("cannot read {core_path}: {e}");
            return ExitCode::from(2);
        }
    };
    let sx = match ir_mint::parse(&core_text) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("core module refused: {e}");
            return ExitCode::from(1);
        }
    };
    let tags = match ir_mint::tags::parse(&tags_text) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("tag table refused: {e}");
            return ExitCode::from(1);
        }
    };
    let script = match ir_mint::mint(&sx, prefix, &tags) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("mint refused: {e}");
            return ExitCode::from(1);
        }
    };
    let defs = script.text();
    let (_, ledger) = match ir_mint::mask_text_unwitnessed(&sx) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("mask refused: {e}");
            return ExitCode::from(1);
        }
    };
    let canonical = match ir_mint::print(&sx) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("canonical print refused: {e}");
            return ExitCode::from(1);
        }
    };
    let mut record = String::from("{\n");
    record.push_str(&format!(" \"prefix\": \"{prefix}\",\n"));
    record.push_str(&format!(
        " \"core_digest\": \"{}\",\n",
        ir_mint::digest(&canonical)
    ));
    record.push_str(&format!(
        " \"defs_digest\": \"{}\",\n",
        ir_mint::digest(&defs)
    ));
    record.push_str(&format!(" \"def_count\": {},\n", script.lines.len()));
    record.push_str(" \"text_unwitnessed\": [\n");
    for (i, u) in ledger.iter().enumerate() {
        record.push_str(&format!(
            "  {{ \"slot\": \"{u}\", \"why\": \"trust-ir Display never prints \
             Switch.exhaustive_enum_unreachable\" }}{}\n",
            if i + 1 == ledger.len() { "" } else { "," }
        ));
    }
    record.push_str(" ]\n}\n");

    if let Err(e) = std::fs::write(format!("{out_dir}/{prefix}.defs.txt"), &defs) {
        eprintln!("cannot write defs: {e}");
        return ExitCode::from(2);
    }
    if let Err(e) = std::fs::write(format!("{out_dir}/{prefix}.mint.json"), &record) {
        eprintln!("cannot write record: {e}");
        return ExitCode::from(2);
    }
    print!("{defs}");
    ExitCode::SUCCESS
}
