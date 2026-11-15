// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean_export_write --module <M> --lean-path <dir> --lean-version <v>
//! --lean-githash <h> (--target <name> | --targets-containing <text>)
//! --out <export.ndjson>`: the export writer (`clean_olean::ndjson`,
//! `write_export`) as a command.
//!
//! It loads the `.olean` closure of each `--module` from the `--lean-path`
//! directories (in order, as `LEAN_PATH` reads them) into an empty replay
//! environment, selects the targets, and writes their dependency cone as a
//! lean4export NDJSON 3.1.0 export. `--target` names one constant exactly as
//! Clean renders it and may be repeated; `--targets-containing` selects every
//! loaded constant whose rendered name contains the text (`CICL.` selects a
//! theory's public and private declarations alike). At least one selector is
//! required, and a selector that selects nothing is refused.
//!
//! The export is written to `<out>.partial`, read back through Clean's
//! reader and written again (`check_export_round_trip`): only when the second
//! writing is the first, byte for byte, is the file renamed to `<out>`. An
//! existing `<out>` is refused unless `--force` is given. `--lean-version`
//! and `--lean-githash` are the Lean whose kernel rules the declarations are
//! stated for; they are written to the export's `meta` line and never
//! guessed. On success one JSON line on stdout states what was written
//! (records, declarations, axioms, lines, bytes, sha256, table sizes, the
//! modules and the target count).
//!
//! Exit 0: written and read back. Exit 1: refused, with the reason on stderr
//! and nothing at `<out>`. Exit 2: a usage error. A panic exits 1 where
//! panics unwind; the release profile aborts instead, with no exit code, and
//! may leave `<out>.partial` (never `<out>`). The writer checks no
//! declaration: `clean_export_check <export.ndjson>` decides an export, and
//! `scripts/lean_export_replay.sh` asks pinned Lean's kernel.

use std::collections::BTreeSet;
use std::io::{BufReader, BufWriter};
use std::path::PathBuf;
use std::process::ExitCode;

use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use clean_olean::ndjson::{check_export_round_trip, write_export, ExportWriteMeta};

/// The loader's stack, as `clean olean replay` runs it.
const STACK_BYTES: usize = 1024 * 1024 * 1024;

const USAGE: &str = "usage: clean_export_write --module <M>... --lean-path <dir>... \
    --lean-version <v> --lean-githash <h> (--target <name>... | --targets-containing <text>...) \
    --out <export.ndjson> [--force]";

#[derive(Default)]
struct Args {
    modules: Vec<String>,
    lean_paths: Vec<PathBuf>,
    targets: Vec<String>,
    containing: Vec<String>,
    lean_version: Option<String>,
    lean_githash: Option<String>,
    out: Option<PathBuf>,
    force: bool,
}

fn parse(raw: &[String]) -> Result<Args, String> {
    let mut args = Args::default();
    let mut it = raw.iter();
    while let Some(flag) = it.next() {
        if flag == "--force" {
            args.force = true;
            continue;
        }
        let value = it
            .next()
            .ok_or_else(|| format!("{flag} needs a value"))?
            .clone();
        match flag.as_str() {
            "--module" => args.modules.push(value),
            "--lean-path" => args.lean_paths.push(PathBuf::from(value)),
            "--target" => args.targets.push(value),
            "--targets-containing" => args.containing.push(value),
            "--lean-version" => args.lean_version = Some(value),
            "--lean-githash" => args.lean_githash = Some(value),
            "--out" => args.out = Some(PathBuf::from(value)),
            other => return Err(format!("unknown flag {other}")),
        }
    }
    if args.modules.is_empty() {
        return Err("no --module".to_owned());
    }
    if args.lean_paths.is_empty() {
        return Err("no --lean-path".to_owned());
    }
    if args.targets.is_empty() && args.containing.is_empty() {
        return Err("no --target and no --targets-containing".to_owned());
    }
    for (flag, value) in [
        ("--lean-version", &args.lean_version),
        ("--lean-githash", &args.lean_githash),
    ] {
        if value.as_deref().unwrap_or_default().is_empty() {
            return Err(format!("no {flag}"));
        }
    }
    if args.out.is_none() {
        return Err("no --out".to_owned());
    }
    Ok(args)
}

/// Load, select, write, read back, publish. The line for stdout.
fn run(args: &Args) -> Result<String, String> {
    let out = args.out.clone().ok_or("no --out")?;
    if out.exists() && !args.force {
        return Err(format!(
            "{} exists (pass --force to replace it)",
            out.display()
        ));
    }
    let meta = ExportWriteMeta {
        lean_version: args.lean_version.clone().unwrap_or_default(),
        lean_githash: args.lean_githash.clone().unwrap_or_default(),
    };

    let mut env = Environment::for_lean_replay();
    let mut visited = hashbrown::HashSet::new();
    for module in &args.modules {
        clean_olean::load_module_with_deps_shared(&mut env, module, &args.lean_paths, &mut visited)
            .map_err(|e| format!("cannot load module {module}: {e}"))?;
    }

    let mut targets: BTreeSet<Name> = BTreeSet::new();
    for wanted in &args.targets {
        let before = targets.len();
        targets.extend(
            env.constants()
                .filter(|c| c.name.to_string() == *wanted)
                .map(|c| c.name.clone()),
        );
        if targets.len() == before {
            return Err(format!(
                "--target {wanted}: no loaded constant has that name"
            ));
        }
    }
    for text in &args.containing {
        let before = targets.len();
        targets.extend(
            env.constants()
                .filter(|c| c.name.to_string().contains(text.as_str()))
                .map(|c| c.name.clone()),
        );
        if targets.len() == before {
            return Err(format!(
                "--targets-containing {text}: no loaded constant's name contains it"
            ));
        }
    }

    let mut partial = out.clone().into_os_string();
    partial.push(".partial");
    let partial = PathBuf::from(partial);
    let written = (|| {
        let file = std::fs::File::create(&partial)
            .map_err(|e| format!("cannot create {}: {e}", partial.display()))?;
        let summary = write_export(&env, &targets, &meta, BufWriter::new(&file))
            .map_err(|e| e.to_string())?;
        file.sync_all()
            .map_err(|e| format!("cannot sync {}: {e}", partial.display()))?;
        let reread = std::fs::File::open(&partial)
            .map_err(|e| format!("cannot reopen {}: {e}", partial.display()))?;
        check_export_round_trip(BufReader::new(reread), &summary).map_err(|e| e.to_string())?;
        std::fs::rename(&partial, &out)
            .map_err(|e| format!("cannot publish {}: {e}", out.display()))?;
        Ok::<_, String>(summary)
    })();
    let summary = match written {
        Ok(summary) => summary,
        Err(problem) => {
            // Nothing partial is left behind for a later run to mistake for
            // an export.
            let _ = std::fs::remove_file(&partial);
            return Err(problem);
        }
    };
    let line = serde_json::json!({
        "export": out.display().to_string(),
        "modules": args.modules,
        "targets": targets.len(),
        "lean_version": meta.lean_version,
        "lean_githash": meta.lean_githash,
        "round_trip": "read back by Clean's reader and written again, byte-identical",
        "written": summary,
    });
    Ok(line.to_string())
}

fn main() -> ExitCode {
    let raw: Vec<String> = std::env::args().skip(1).collect();
    let args = match parse(&raw) {
        Ok(args) => args,
        Err(problem) => {
            eprintln!("clean_export_write: {problem}\n{USAGE}");
            return ExitCode::from(2);
        }
    };
    let worker = std::thread::Builder::new()
        .name("ndjson-write".to_owned())
        .stack_size(STACK_BYTES)
        .spawn(move || run(&args));
    match worker.map(std::thread::JoinHandle::join) {
        Ok(Ok(Ok(line))) => {
            println!("{line}");
            ExitCode::SUCCESS
        }
        Ok(Ok(Err(problem))) => {
            eprintln!("clean_export_write: refused: {problem}");
            ExitCode::from(1)
        }
        Ok(Err(_)) => {
            eprintln!("clean_export_write: the writer thread panicked");
            ExitCode::from(1)
        }
        Err(e) => {
            eprintln!("clean_export_write: cannot start the writer: {e}");
            ExitCode::from(1)
        }
    }
}
