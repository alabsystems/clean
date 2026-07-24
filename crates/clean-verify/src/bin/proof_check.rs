// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `proof_check` — compat shim for `clean verify proof`.
//!
//! Retained for one release per Epic #3436 because SAT-COMP / SMT-COMP
//! judging scripts hard-code the path to this binary. All real work lives in
//! [`clean_verify::cli`] so the binary stays tiny and delegates to the same
//! dispatcher as the unified CLI. Issue #3511.
//!
//! # Usage
//!
//! ```text
//! proof_check <formula_file> <proof_file> [OPTIONS]
//! ```
//!
//! Accepts the same flags as before (`--competition`, `--smtcomp`, `--satcomp`,
//! `--format`, `--strict`, `--timing`, `--certificate`, `--trim`). Exit codes
//! remain contractual: `0` verified, `10` invalid, `1` error.

use std::path::PathBuf;
use std::process;

use clean_verify::cli::pipeline::{
    parse_format, run_competition, run_pipeline, run_satcomp, run_smtcomp, OwnedProofCheckInputs,
    EXIT_ERROR,
};
use clean_verify::sat_verify::pipeline::ProofFormat;

/// Parsed CLI arguments. Matches the legacy flag set byte-for-byte so
/// external scripts that invoke `proof_check` directly keep working.
struct CliArgs {
    formula_path: PathBuf,
    proof_path: PathBuf,
    format: Option<ProofFormat>,
    strict: bool,
    timing: bool,
    competition: bool,
    smtcomp: bool,
    satcomp: bool,
    certificate_path: Option<PathBuf>,
    trim_output: Option<PathBuf>,
}

fn print_usage() {
    eprintln!(
        "\
Usage: proof_check <formula_file> <proof_file> [OPTIONS]
       proof_check --competition <cnf_file> <proof_file>
       proof_check --smtcomp <formula_file> <proof_file>
       proof_check --satcomp <cnf_file> <proof_file>

Verify SAT/SMT proofs against formulas.

Formats: LRAT (text/binary), DRAT (text/binary), Alethe, SMT-LIB2, VeriPB

Options:
  --format <fmt>    Override auto-detection (lrat|drat|alethe|smtlib2|veripb|auto)
  --strict          Reject proofs with any trusted (unverified) steps
  --timing          Print parse and verification timing
  --competition     Competition mode: LRAT-only, maximum performance
  --smtcomp         SMT-COMP output: valid|holey|invalid|unknown + hole count
  --satcomp         SAT-COMP output: s VERIFIED | s NOT VERIFIED
  --certificate <f> Emit verification certificate to file (JSON)
  --trim <output>   Trim LRAT proof and write minimized proof to file
  --help            Show this message

Exit codes:
  0   Proof verified (valid refutation)
  10  Proof invalid
  1   Error (I/O, parse, unknown format)

Note: this binary is a compat shim for `clean verify proof` (Epic #3436 #3511).
Future development should prefer the unified CLI."
    );
}

fn parse_args() -> Result<CliArgs, String> {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 2 {
        return Err("not enough arguments".to_owned());
    }

    let mut format = None;
    let mut strict = false;
    let mut timing = false;
    let mut competition = false;
    let mut smtcomp = false;
    let mut satcomp = false;
    let mut certificate_path = None;
    let mut trim_output = None;
    let mut positional: Vec<String> = Vec::new();

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--help" | "-h" => {
                print_usage();
                process::exit(0);
            }
            "--strict" => strict = true,
            "--timing" => timing = true,
            "--competition" => competition = true,
            "--smtcomp" => smtcomp = true,
            "--satcomp" => satcomp = true,
            "--format" => {
                i += 1;
                if i >= args.len() {
                    return Err("--format requires an argument".to_owned());
                }
                format = parse_format(&args[i])?;
            }
            "--certificate" => {
                i += 1;
                if i >= args.len() {
                    return Err("--certificate requires an argument".to_owned());
                }
                certificate_path = Some(PathBuf::from(&args[i]));
            }
            "--trim" => {
                i += 1;
                if i >= args.len() {
                    return Err("--trim requires an argument".to_owned());
                }
                trim_output = Some(PathBuf::from(&args[i]));
            }
            arg if arg.starts_with("--format=") => {
                let val = &arg["--format=".len()..];
                format = parse_format(val)?;
            }
            arg if arg.starts_with("--certificate=") => {
                let val = &arg["--certificate=".len()..];
                certificate_path = Some(PathBuf::from(val));
            }
            arg if arg.starts_with("--trim=") => {
                let val = &arg["--trim=".len()..];
                trim_output = Some(PathBuf::from(val));
            }
            arg if arg.starts_with('-') => {
                return Err(format!("unknown option: {arg}"));
            }
            _ => positional.push(args[i].clone()),
        }
        i += 1;
    }

    if positional.len() != 2 {
        return Err(format!(
            "expected 2 positional arguments (formula proof), got {}",
            positional.len()
        ));
    }

    Ok(CliArgs {
        formula_path: PathBuf::from(&positional[0]),
        proof_path: PathBuf::from(&positional[1]),
        format,
        strict,
        timing,
        competition,
        smtcomp,
        satcomp,
        certificate_path,
        trim_output,
    })
}

fn main() {
    let args = match parse_args() {
        Ok(a) => a,
        Err(msg) => {
            eprintln!("error: {msg}");
            eprintln!();
            print_usage();
            process::exit(EXIT_ERROR);
        }
    };

    let inputs = OwnedProofCheckInputs {
        formula_path: args.formula_path,
        proof_path: args.proof_path,
        format: args.format,
        strict: args.strict,
        timing: args.timing,
        certificate_path: args.certificate_path,
        trim_output: args.trim_output,
    };

    let view = inputs.as_inputs();
    let exit_code = if args.smtcomp {
        run_smtcomp(&view)
    } else if args.satcomp {
        run_satcomp(&view)
    } else if args.competition {
        run_competition(&view)
    } else {
        run_pipeline(&view)
    };

    process::exit(exit_code);
}
