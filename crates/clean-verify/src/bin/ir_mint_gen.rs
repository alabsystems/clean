// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regenerate the committed A2 mint artifacts from the committed core module.
//!
//! `targo --unverified run --locked -p clean-verify --bin ir_mint_gen -- <prefix> <core.txt> <tags.json> <out-dir>`
//!
//! `targo --unverified run --locked -p clean-verify --bin ir_mint_gen -- --check <prefix> <core.txt> <tags.json> <out-dir>`
//!
//! `--check` recomputes the same two outputs and compares their exact bytes without
//! writing. It checks custody of these inputs and outputs, not kernel acceptance,
//! semantic correctness or freshness of an external artifact/producer.
//!
//! The generation is pure: core module in, definition script and record out.
//! `tests/crystal_a2_mint.rs` re-runs the same pure function and fails closed
//! if the committed artifacts are not what it produces, so running this binary
//! is a convenience, never an authority.

use std::process::ExitCode;

use clean_verify::ir_mint;

fn main() -> ExitCode {
    run(&std::env::args().collect::<Vec<_>>())
}

fn run(args: &[String]) -> ExitCode {
    let (check_only, positional) = match args {
        [_, flag, rest @ ..] if flag == "--check" => (true, rest),
        [_, rest @ ..] => (false, rest),
        _ => return usage(),
    };
    let [prefix, core_path, tags_path, out_dir] = positional else {
        return usage();
    };
    if check_only && prefix == "--check" {
        return usage();
    }
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

    if check_only {
        return check_outputs(out_dir, prefix, &defs, &record);
    }

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

fn usage() -> ExitCode {
    eprintln!("usage: ir_mint_gen [--check] <prefix> <core.txt> <tags.json> <out-dir>");
    ExitCode::from(2)
}

fn check_outputs(out_dir: &str, prefix: &str, defs: &str, record: &str) -> ExitCode {
    let mut code = 0u8;
    for (suffix, expected) in [("defs.txt", defs), ("mint.json", record)] {
        let path = format!("{out_dir}/{prefix}.{suffix}");
        match std::fs::read(&path) {
            Ok(actual) if actual == expected.as_bytes() => {}
            Ok(_) => {
                eprintln!("out of date: {path}");
                code = code.max(1);
            }
            Err(e) => {
                eprintln!("cannot read {path}: {e}");
                code = 2;
            }
        }
    }
    ExitCode::from(code)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::{Path, PathBuf};

    const CASES: &[(&str, &str, &str, &str, &str)] = &[
        (
            "ir_cf",
            include_str!("../spec/core_spec/generated/ir_cf.core.txt"),
            include_str!("../spec/core_spec/generated/ir_cf.tags.json"),
            include_str!("../spec/core_spec/generated/ir_cf.defs.txt"),
            include_str!("../spec/core_spec/generated/ir_cf.mint.json"),
        ),
        (
            "ir_itc",
            include_str!("../spec/core_spec/generated/ir_itc.core.txt"),
            include_str!("../spec/core_spec/generated/ir_itc.tags.json"),
            include_str!("../spec/core_spec/generated/ir_itc.defs.txt"),
            include_str!("../spec/core_spec/generated/ir_itc.mint.json"),
        ),
        (
            "ir_sh",
            include_str!("../spec/core_spec/generated/ir_sh.core.txt"),
            include_str!("../spec/core_spec/generated/ir_sh.tags.json"),
            include_str!("../spec/core_spec/generated/ir_sh.defs.txt"),
            include_str!("../spec/core_spec/generated/ir_sh.mint.json"),
        ),
    ];

    fn inputs(root: &Path, core: &str, tags: &str) -> (PathBuf, PathBuf) {
        let core_path = root.join("input.core.txt");
        let tags_path = root.join("input.tags.json");
        std::fs::write(&core_path, core).expect("core fixture");
        std::fs::write(&tags_path, tags).expect("tags fixture");
        (core_path, tags_path)
    }

    fn args(prefix: &str, core: &Path, tags: &Path, out: &Path) -> Vec<String> {
        vec![
            "ir_mint_gen".to_owned(),
            prefix.to_owned(),
            core.to_str().expect("fixture path").to_owned(),
            tags.to_str().expect("fixture path").to_owned(),
            out.to_str().expect("fixture path").to_owned(),
        ]
    }

    fn check_args(write_args: &[String]) -> Vec<String> {
        let mut result = write_args.to_vec();
        result.insert(1, "--check".to_owned());
        result
    }

    fn files(root: &Path) -> Vec<(PathBuf, Vec<u8>)> {
        let mut result = Vec::new();
        for entry in std::fs::read_dir(root).expect("fixture directory") {
            let path = entry.expect("fixture entry").path();
            if path.is_dir() {
                result.extend(files(&path));
            } else {
                result.push((path.clone(), std::fs::read(path).expect("fixture bytes")));
            }
        }
        result.sort();
        result
    }

    fn checked_without_writes(root: &Path, argv: &[String], expected: u8) {
        let before = files(root);
        assert_eq!(run(argv), ExitCode::from(expected));
        assert_eq!(files(root), before, "check/error paths must not write");
    }

    #[test]
    fn default_writer_and_check_bind_all_three_registered_scripts() {
        for &(prefix, core, tags, registered, recorded) in CASES {
            let dir = tempfile::tempdir().expect("fixture directory");
            let (core_path, tags_path) = inputs(dir.path(), core, tags);
            let argv = args(prefix, &core_path, &tags_path, dir.path());
            assert_eq!(run(&argv), ExitCode::SUCCESS);
            let defs = std::fs::read_to_string(dir.path().join(format!("{prefix}.defs.txt")))
                .expect("writer definitions");
            assert_eq!(defs, registered, "same current registered producer bytes");
            let record_bytes = std::fs::read(dir.path().join(format!("{prefix}.mint.json")))
                .expect("writer record");
            // Keep the pre-change receipt layout/count/ledger as an independent
            // byte oracle. Its historical digest fields are recomputed from the
            // fixed current core/registered definitions in memory only.
            let historical: serde_json::Value =
                serde_json::from_str(recorded).expect("pre-change receipt JSON");
            let mut expected_record = recorded.to_owned();
            for (field, expected) in [
                ("core_digest", ir_mint::digest(core)),
                ("defs_digest", ir_mint::digest(registered)),
            ] {
                let old = historical[field].as_str().expect("pre-change digest");
                let needle = format!(" \"{field}\": \"{old}\"");
                assert_eq!(expected_record.matches(&needle).count(), 1);
                expected_record =
                    expected_record.replacen(&needle, &format!(" \"{field}\": \"{expected}\""), 1);
            }
            assert_eq!(
                record_bytes,
                expected_record.as_bytes(),
                "default writer byte parity"
            );
            let receipt: serde_json::Value =
                serde_json::from_slice(&record_bytes).expect("writer JSON");
            assert_eq!(receipt["prefix"], prefix);
            assert_eq!(receipt["core_digest"], ir_mint::digest(core));
            assert_eq!(receipt["defs_digest"], ir_mint::digest(&defs));
            assert_eq!(receipt["def_count"], defs.lines().count());
            let sx = ir_mint::parse(core).expect("core fixture");
            let (_, ledger) = ir_mint::mask_text_unwitnessed(&sx).expect("ledger fixture");
            assert_eq!(
                receipt["text_unwitnessed"]
                    .as_array()
                    .expect("ledger")
                    .len(),
                ledger.len()
            );
            for (row, slot) in receipt["text_unwitnessed"]
                .as_array()
                .expect("ledger")
                .iter()
                .zip(ledger)
            {
                assert_eq!(row["slot"], slot.to_string());
                assert_eq!(
                    row["why"],
                    "trust-ir Display never prints Switch.exhaustive_enum_unreachable"
                );
            }
            assert_eq!(receipt.as_object().expect("record fields").len(), 5);
            checked_without_writes(dir.path(), &check_args(&argv), 0);
        }
    }

    #[test]
    fn check_rejects_definition_record_fields_ledger_and_format_mutations() {
        let (prefix, core, tags, _, _) = CASES[1];
        let dir = tempfile::tempdir().expect("fixture directory");
        let (core_path, tags_path) = inputs(dir.path(), core, tags);
        let argv = args(prefix, &core_path, &tags_path, dir.path());
        assert_eq!(run(&argv), ExitCode::SUCCESS);
        let defs_path = dir.path().join(format!("{prefix}.defs.txt"));
        let record_path = dir.path().join(format!("{prefix}.mint.json"));
        let defs = std::fs::read(&defs_path).expect("definitions");
        let record = std::fs::read_to_string(&record_path).expect("record");
        let mut changed_defs = defs.clone();
        changed_defs[0] ^= 1;
        std::fs::write(&defs_path, changed_defs).expect("mutated definitions");
        checked_without_writes(dir.path(), &check_args(&argv), 1);
        std::fs::write(&defs_path, &defs).expect("restore definitions");
        for needle in [
            "\"prefix\": \"",
            "\"core_digest\": \"",
            "\"defs_digest\": \"",
            "\"def_count\": ",
            "\"slot\": \"",
            "\"why\": \"",
        ] {
            let offset = record.find(needle).expect("actual receipt field") + needle.len();
            let mut changed = record.as_bytes().to_vec();
            changed[offset] = if changed[offset] == b'0' { b'1' } else { b'0' };
            std::fs::write(&record_path, changed).expect("mutated record field");
            checked_without_writes(dir.path(), &check_args(&argv), 1);
        }
        std::fs::write(&record_path, format!("{record} ")).expect("record whitespace");
        checked_without_writes(dir.path(), &check_args(&argv), 1);
        std::fs::write(&record_path, b"not JSON").expect("malformed record");
        checked_without_writes(dir.path(), &check_args(&argv), 1);
    }

    #[test]
    fn check_uses_current_core_and_tags_bytes() {
        let (prefix, core, tags, _, _) = CASES[0];
        let dir = tempfile::tempdir().expect("fixture directory");
        let (core_path, tags_path) = inputs(dir.path(), core, tags);
        let argv = args(prefix, &core_path, &tags_path, dir.path());
        assert_eq!(run(&argv), ExitCode::SUCCESS);
        // The existing receipt hashes canonical core, not raw whitespace.
        std::fs::write(&core_path, format!("\n{core}\n")).expect("core whitespace");
        checked_without_writes(dir.path(), &check_args(&argv), 0);
        assert_eq!(core.matches("(int 0)").count(), 1);
        std::fs::write(&core_path, core.replacen("(int 0)", "(int 1)", 1))
            .expect("changed constant payload");
        checked_without_writes(dir.path(), &check_args(&argv), 1);
        std::fs::write(&core_path, core).expect("restore core");
        assert_eq!(tags.matches("\"crate_id\": 56").count(), 1);
        std::fs::write(
            &tags_path,
            tags.replacen("\"crate_id\": 56", "\"crate_id\": 57", 1),
        )
        .expect("changed actual enum id");
        checked_without_writes(dir.path(), &check_args(&argv), 1);
    }

    #[test]
    fn check_missing_outputs_and_both_output_reads_fail_without_creation() {
        let (prefix, core, tags, _, _) = CASES[0];
        let dir = tempfile::tempdir().expect("fixture directory");
        let (core_path, tags_path) = inputs(dir.path(), core, tags);
        let missing = dir.path().join("missing-output-directory");
        let argv = args(prefix, &core_path, &tags_path, &missing);
        checked_without_writes(dir.path(), &check_args(&argv), 2);
        assert!(!missing.exists());
        let argv = args(prefix, &core_path, &tags_path, dir.path());
        assert_eq!(run(&argv), ExitCode::SUCCESS);
        let defs_path = dir.path().join(format!("{prefix}.defs.txt"));
        let record_path = dir.path().join(format!("{prefix}.mint.json"));
        let defs = std::fs::read(&defs_path).expect("definitions");
        std::fs::remove_file(&defs_path).expect("remove definitions");
        checked_without_writes(dir.path(), &check_args(&argv), 2);
        assert!(!defs_path.exists());
        std::fs::write(&defs_path, b"wrong definitions").expect("mismatched definitions");
        std::fs::remove_file(&record_path).expect("remove record");
        checked_without_writes(dir.path(), &check_args(&argv), 2);
        assert!(
            !record_path.exists(),
            "a defs mismatch must not skip the record read"
        );
        std::fs::write(&defs_path, defs).expect("restore definitions");
    }

    #[test]
    fn missing_malformed_inputs_and_strict_arity_refuse_without_writes() {
        let (prefix, core, tags, _, _) = CASES[0];
        let dir = tempfile::tempdir().expect("fixture directory");
        let (core_path, tags_path) = inputs(dir.path(), core, tags);
        let argv = args(prefix, &core_path, &tags_path, dir.path());
        let mut extra = check_args(&argv);
        extra.push("unexpected".to_owned());
        let mut unknown = argv.clone();
        unknown.insert(1, "--unknown".to_owned());
        let mut repeated = check_args(&argv);
        repeated[2] = "--check".to_owned();
        for bad in [
            Vec::new(),
            vec!["ir_mint_gen".to_owned()],
            check_args(&argv)[..5].to_vec(),
            extra,
            unknown,
            repeated,
        ] {
            checked_without_writes(dir.path(), &bad, 2);
        }
        for bad in ["(module", "not a core module"] {
            std::fs::write(&core_path, bad).expect("bad core");
            checked_without_writes(dir.path(), &check_args(&argv), 1);
        }
        std::fs::write(&core_path, core).expect("restore core");
        for bad in ["not JSON", "{}"] {
            std::fs::write(&tags_path, bad).expect("bad tags");
            checked_without_writes(dir.path(), &check_args(&argv), 1);
        }
        std::fs::remove_file(&tags_path).expect("remove tags");
        checked_without_writes(dir.path(), &check_args(&argv), 2);
        std::fs::write(&tags_path, tags).expect("restore tags");
        std::fs::remove_file(&core_path).expect("remove core");
        checked_without_writes(dir.path(), &check_args(&argv), 2);
    }
}
