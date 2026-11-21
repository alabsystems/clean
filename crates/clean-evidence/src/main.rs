// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_evidence::envelope::python_minters;
use clean_evidence::envelope::FreshnessState;
use clean_evidence::trustcore::{
    self, StalenessCheck, DIGEST_MODULE_SOURCE, DIGEST_SOURCE, MODULE_FILE, MODULE_TREE_KEY,
};
use std::{
    ffi::OsString,
    io::{self, Write},
    path::{Path, PathBuf},
    process::ExitCode,
};

mod git;
mod w0_mutation;

const USAGE: &str =
    "Usage: clean-evidence check trustcore-staleness [--repo-root <path>] [--json]\n\
     \x20      clean-evidence check w0-mutation [--repo-root <path>] [--receipt <path>]\n\
     \x20      clean-evidence check python-minters [--repo-root <path>] [--published <commit>]\n\
     \x20      clean-evidence inventory python-minters [--repo-root <path>]\n\
     \x20      clean-evidence inventory python-minters-membership [--repo-root <path>]\n\
     \x20      clean-evidence record python-minters [--repo-root <path>]\n\
     \x20 --json  print the TrustCore verdict as a canonical clean.evidence/v1 record";

/// What the command line asked for.
struct Request {
    root: PathBuf,
    json: bool,
}

fn parse(args: &[OsString]) -> Option<Request> {
    let [check, figure, rest @ ..] = args else {
        return None;
    };
    if check != "check" || figure != "trustcore-staleness" {
        return None;
    }
    let mut request = Request {
        root: PathBuf::from("."),
        json: false,
    };
    let (mut saw_root, mut rest) = (false, rest);
    while let [flag, tail @ ..] = rest {
        rest = tail;
        if flag == "--json" && !request.json {
            request.json = true;
        } else if flag == "--repo-root" && !saw_root {
            let [root, tail @ ..] = rest else {
                return None;
            };
            request.root = PathBuf::from(root);
            saw_root = true;
            rest = tail;
        } else {
            return None;
        }
    }
    Some(request)
}

fn main() -> ExitCode {
    let args: Vec<OsString> = std::env::args_os().skip(1).collect();
    match args.as_slice() {
        [flag] if flag == "--help" || flag == "-h" => {
            println!("{USAGE}");
            return ExitCode::SUCCESS;
        }
        [check, figure, rest @ ..] if check == "check" && figure == "w0-mutation" => {
            return check_w0_mutation(rest);
        }
        [verb, figure, rest @ ..] if verb == "inventory" && figure == "python-minters" => {
            return run_python_minters(rest, PythonMintersMode::Counts);
        }
        [verb, figure, rest @ ..]
            if verb == "inventory" && figure == "python-minters-membership" =>
        {
            return run_python_minters(rest, PythonMintersMode::Membership);
        }
        [verb, figure, rest @ ..] if verb == "check" && figure == "python-minters" => {
            return run_python_minters(rest, PythonMintersMode::Check);
        }
        [verb, figure, rest @ ..] if verb == "record" && figure == "python-minters" => {
            return run_python_minters(rest, PythonMintersMode::Record);
        }
        _ => {}
    }
    let Some(request) = parse(&args) else {
        eprintln!("{USAGE}");
        return ExitCode::from(2);
    };
    if request.json {
        let argv: Vec<String> = std::iter::once("clean-evidence".to_owned())
            .chain(args.iter().map(|arg| arg.to_string_lossy().into_owned()))
            .collect();
        return emit_record(&request, &argv);
    }
    check_trustcore(&request)
}

enum PythonMintersMode {
    Counts,
    Membership,
    Check,
    Record,
}

fn run_python_minters(args: &[OsString], mode: PythonMintersMode) -> ExitCode {
    use python_minters::InventoryError;

    if matches!(args, [flag] if flag == "--help" || flag == "-h") {
        println!("{USAGE}");
        return ExitCode::SUCCESS;
    }
    let (mut root, mut published) = (None, None);
    for pair in args.chunks(2) {
        match pair {
            [flag, value] if flag == "--repo-root" && root.is_none() => {
                root = Some(Path::new(value));
            }
            [flag, value]
                if flag == "--published"
                    && matches!(mode, PythonMintersMode::Check)
                    && published.is_none() =>
            {
                published = Some(value);
            }
            _ => {
                eprintln!("{USAGE}");
                return ExitCode::from(2);
            }
        }
    }
    let root = root.unwrap_or_else(|| Path::new("."));
    let result = match mode {
        PythonMintersMode::Counts => python_minters::inventory(root).and_then(|inventory| {
            serde_json::to_string_pretty(&inventory)
                .map(|json| println!("{json}"))
                .map_err(|error| InventoryError::Invalid(error.to_string()))
        }),
        PythonMintersMode::Membership => python_minters::render(root).map(|json| print!("{json}")),
        PythonMintersMode::Record => {
            let argv = ["clean-evidence", "record", "python-minters"]
                .into_iter()
                .map(str::to_owned)
                .chain(args.iter().map(|arg| arg.to_string_lossy().into_owned()))
                .collect();
            python_minters::record(root, argv).and_then(|bytes| {
                io::stdout().lock().write_all(&bytes).map_err(|error| {
                    InventoryError::Unavailable(format!("cannot write evidence record: {error}"))
                })
            })
        }
        PythonMintersMode::Check => {
            let checked = match published {
                None => python_minters::check(root),
                Some(value) => value
                    .to_str()
                    .ok_or_else(|| {
                        InventoryError::Invalid("the published commit ID must be ASCII".to_owned())
                    })
                    .and_then(|commit| python_minters::check_publication(root, commit)),
            };
            checked.map(|()| println!("PYTHON_MINTERS=ok"))
        }
    };
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(InventoryError::Invalid(error)) => {
            eprintln!("PYTHON_MINTERS=invalid {error}");
            ExitCode::FAILURE
        }
        Err(InventoryError::Unavailable(error)) => {
            eprintln!("PYTHON_MINTERS=unavailable {error}");
            ExitCode::from(3)
        }
    }
}

fn emit_record(request: &Request, argv: &[String]) -> ExitCode {
    let (_, envelope) = match StalenessCheck::record(&request.root, argv) {
        Ok(record) => record,
        Err(error) => {
            eprintln!("FAIL: {error}");
            return ExitCode::FAILURE;
        }
    };
    match envelope.to_canonical_json() {
        Ok(bytes) => print!("{}", String::from_utf8_lossy(&bytes)),
        Err(error) => {
            eprintln!("FAIL: cannot render the record: {error}");
            return ExitCode::FAILURE;
        }
    }
    if envelope.freshness.state == FreshnessState::Fresh {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

fn check_trustcore(request: &Request) -> ExitCode {
    let checked = match trustcore::check(&request.root) {
        Ok(checked) => checked,
        Err(error) => {
            println!("FAIL: cannot hash the trust-core gate sources: {error}");
            println!("TRUSTCORE_STALENESS=stale");
            return ExitCode::FAILURE;
        }
    };
    println!("  current {MODULE_FILE} sha256: {}", checked.file_sha256);
    println!(
        "  current module-tree digest ({MODULE_TREE_KEY}): {}",
        checked.tree_sha256
    );
    println!(
        "  current {DIGEST_MODULE_SOURCE} sha256: {}",
        checked.digest_module_sha256
    );
    println!(
        "  current {DIGEST_SOURCE} sha256: {}",
        checked.digest_source_sha256
    );
    if checked.findings.is_empty() {
        println!("TRUSTCORE_STALENESS=fresh");
        return ExitCode::SUCCESS;
    }
    for finding in &checked.findings {
        println!("  STALE: {finding}");
    }
    println!(
        "  Regenerate the stale trust-core receipts with a HEAD-built clean binary. The --evidence flag writes the report.\n\
         \x20   clean replacement trust-core-evidence --kernel-soundness --evidence reports/kernel-soundness-launch-evidence.json\n\
         \x20   clean replacement trust-core-evidence --deny-sorry --evidence reports/deny-sorry-launch-evidence.json\n\
         \x20   clean replacement axiom-audit --verify data/axiom_audit.json --evidence reports/axiom-audit-launch-evidence.json --json\n\
         \x20 Commit the refreshed artifacts with the gate edit."
    );
    println!("TRUSTCORE_STALENESS=stale");
    ExitCode::FAILURE
}

fn check_w0_mutation(args: &[OsString]) -> ExitCode {
    if matches!(args, [flag] if flag == "--help" || flag == "-h") {
        println!("{USAGE}");
        return ExitCode::SUCCESS;
    }
    let (mut root, mut receipt) = (None, None);
    for pair in args.chunks(2) {
        match pair {
            [flag, value] if flag == "--repo-root" && root.is_none() => {
                root = Some(PathBuf::from(value));
            }
            [flag, value] if flag == "--receipt" && receipt.is_none() => {
                receipt = Some(PathBuf::from(value));
            }
            _ => {
                eprintln!("{USAGE}");
                return ExitCode::from(2);
            }
        }
    }
    let root = root.unwrap_or_else(|| PathBuf::from("."));
    match w0_mutation::check(&root, receipt.as_deref()) {
        Ok(result) => {
            println!(
                "W0_MUTATION_RECEIPT=ok source={} fixtures={}",
                result.source, result.fixtures,
            );
            ExitCode::SUCCESS
        }
        Err(w0_mutation::CheckError::Invalid(message)) => {
            eprintln!("W0_MUTATION_RECEIPT=invalid {message}");
            ExitCode::FAILURE
        }
        Err(w0_mutation::CheckError::Unavailable(message)) => {
            eprintln!("W0_MUTATION_RECEIPT=unavailable {message}");
            ExitCode::from(3)
        }
    }
}
