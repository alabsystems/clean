// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Per-mode runners for `clean verify proof`.
//!
//! The four runners — default pipeline, competition, SMT-COMP exhibition, and
//! SAT-COMP unsat certificate — and their helpers (certificate emission, LRAT
//! trim) are isolated here so [`super`] can stay under the 500-line file cap.
//!
//! Every runner returns the SAT/SMT-COMP exit-code contract:
//!   * `0` — proof verified
//!   * `10` — proof invalid (not a refutation)
//!   * `1` — error (I/O, parse, unknown format)
//!
//! Exit-code and stdout/stderr parity with the legacy `proof_check` binary is
//! a hard contract (competition judges consume it verbatim). Do not alter
//! the `s VERIFIED` / `s INVALID` / `s NOT VERIFIED` / `valid` / `holey` /
//! `invalid` / `unknown` line texts without simultaneously updating the
//! golden tests in `crates/clean-verify/src/cli/tests.rs`.

use std::time::Instant;

use super::helpers::{emit_certificate, run_trim};
pub use super::helpers::{parse_format, OwnedProofCheckInputs, ProofCheckInputs};

use crate::sat_verify::lrat_kernel_bridge::verify_lrat_competition;
use crate::sat_verify::pipeline::{detect_format, verify_any_proof, PipelineError, TrustLevel};

/// Exit code: proof verified successfully.
pub const EXIT_VERIFIED: i32 = 0;
/// Exit code: proof is invalid.
pub const EXIT_INVALID: i32 = 10;
/// Exit code: error (I/O, parse, unknown format, etc.).
pub const EXIT_ERROR: i32 = 1;

/// Run the LRAT-only competition pipeline (`--competition`).
pub fn run_competition(args: &ProofCheckInputs<'_>) -> i32 {
    let total_start = Instant::now();

    let cnf_bytes = match std::fs::read(args.formula_path) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("c ERROR: reading formula: {e}");
            return EXIT_ERROR;
        }
    };

    let proof_bytes = match std::fs::read(args.proof_path) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("c ERROR: reading proof: {e}");
            return EXIT_ERROR;
        }
    };

    match verify_lrat_competition(&cnf_bytes, &proof_bytes) {
        Ok(result) => {
            if result.valid {
                if args.timing {
                    let total = total_start.elapsed();
                    eprintln!(
                        "c parse_cnf: {:.3}ms  parse_proof: {:.3}ms  verify: {:.3}ms  total: {:.3}ms",
                        result.parse_cnf_time.as_secs_f64() * 1000.0,
                        result.parse_proof_time.as_secs_f64() * 1000.0,
                        result.verify_time.as_secs_f64() * 1000.0,
                        total.as_secs_f64() * 1000.0,
                    );
                    eprintln!(
                        "c vars: {}  clauses: {}  derived: {}  deleted: {}  steps: {}  format: {}",
                        result.num_vars,
                        result.original_clauses,
                        result.derived_clauses,
                        result.deleted_clauses,
                        result.proof_steps,
                        result.proof_format,
                    );
                }
                println!("s VERIFIED");
                EXIT_VERIFIED
            } else {
                println!("s INVALID");
                eprintln!("c proof did not derive a refutation");
                EXIT_INVALID
            }
        }
        Err(e) => {
            println!("s INVALID");
            eprintln!("c ERROR: {e}");
            EXIT_INVALID
        }
    }
}

/// Run the default multi-format pipeline.
pub fn run_pipeline(args: &ProofCheckInputs<'_>) -> i32 {
    let total_start = Instant::now();

    let (formula_bytes, proof_bytes) = match read_pipeline_inputs(args) {
        Ok(bytes) => bytes,
        Err(exit) => return exit,
    };

    let read_time = total_start.elapsed();
    warn_if_format_hint_mismatches(args.format, &proof_bytes);

    let verify_start = Instant::now();
    let result = verify_any_proof(&formula_bytes, &proof_bytes);
    let verify_time = verify_start.elapsed();

    match result {
        Ok(unified) => handle_unified_verdict(
            args,
            &formula_bytes,
            &proof_bytes,
            &unified,
            total_start,
            read_time,
            verify_time,
        ),
        Err(e) => report_pipeline_error(&e),
    }
}

/// Read the formula and proof byte slices, printing the conventional error
/// lines on failure. Returned `i32` is the contractual exit code.
fn read_pipeline_inputs(args: &ProofCheckInputs<'_>) -> Result<(Vec<u8>, Vec<u8>), i32> {
    let formula_bytes = std::fs::read(args.formula_path).map_err(|e| {
        eprintln!("c ERROR: reading formula: {e}");
        EXIT_ERROR
    })?;
    let proof_bytes = std::fs::read(args.proof_path).map_err(|e| {
        eprintln!("c ERROR: reading proof: {e}");
        EXIT_ERROR
    })?;
    Ok((formula_bytes, proof_bytes))
}

/// If `--format <hint>` was provided and auto-detection disagrees, emit the
/// conventional warning line (consumed by some judging scripts).
fn warn_if_format_hint_mismatches(
    hint: Option<crate::sat_verify::pipeline::ProofFormat>,
    proof_bytes: &[u8],
) {
    let Some(hint) = hint else { return };
    let detected = detect_format(proof_bytes);
    if detected != crate::sat_verify::pipeline::ProofFormat::Unknown && detected != hint {
        eprintln!("c WARNING: requested format {hint} but auto-detected {detected}; using {hint}",);
    }
}

/// Handle the `Ok(unified)` branch of the default pipeline: emit timing,
/// apply strict-mode rejection, emit certificate + trim, report verdict.
fn handle_unified_verdict(
    args: &ProofCheckInputs<'_>,
    formula_bytes: &[u8],
    proof_bytes: &[u8],
    unified: &crate::sat_verify::pipeline::UnifiedResult,
    total_start: Instant,
    read_time: std::time::Duration,
    verify_time: std::time::Duration,
) -> i32 {
    if args.timing {
        let total = total_start.elapsed();
        eprintln!(
            "c read: {:.3}ms  verify: {:.3}ms  total: {:.3}ms",
            read_time.as_secs_f64() * 1000.0,
            verify_time.as_secs_f64() * 1000.0,
            total.as_secs_f64() * 1000.0,
        );
        eprintln!(
            "c format: {}  trust: {}  steps_verified: {}  steps_trusted: {}",
            unified.format, unified.trust_level, unified.steps_verified, unified.steps_trusted,
        );
    }

    // SOUNDNESS (root cause C): strict mode rejects any proof that is not
    // FULLY kernel-verified. `steps_trusted > 0` catches blindly-trusted steps,
    // but a proof can also be "holey" — structurally accepted (unchecked theory
    // lemmas / boolean-rule catch-alls) with `steps_trusted == 0`, yet still
    // lean on a false clause laundered into the empty-clause derivation. A
    // strict verdict is a discharge claim, so require `KernelVerified`. See
    // docs/SOUNDNESS_FINDINGS_CLEAN_VERIFY_2026-07.md.
    if args.strict && unified.valid && unified.trust_level != TrustLevel::KernelVerified {
        println!("s INVALID");
        if unified.steps_trusted > 0 {
            eprintln!(
                "c strict mode: {} trusted steps rejected",
                unified.steps_trusted,
            );
        } else {
            eprintln!(
                "c strict mode: holey proof rejected (trust: {}); structurally-accepted \
                 steps are not kernel-verified",
                unified.trust_level,
            );
        }
        return EXIT_INVALID;
    }

    if let Some(cert_path) = args.certificate_path {
        emit_certificate(
            cert_path,
            formula_bytes,
            proof_bytes,
            args.strict,
            &unified.format,
        );
    }

    if let Some(trim_path) = args.trim_output {
        run_trim(proof_bytes, trim_path, &unified.format);
    }

    // SOUNDNESS (root cause C): `s VERIFIED` is a discharge claim — the proof is
    // a fully kernel-verified refutation. `unified.valid` is only a *structural*
    // signal ("derives the empty clause") that is true even when the empty
    // clause rests on an unchecked, structurally-accepted step's (possibly
    // false) clause. Mirror `run_smtcomp`: only accept when the trust level is
    // `KernelVerified`; a holey/partially-verified proof is reported `s HOLEY`
    // and does NOT exit as verified. See
    // docs/SOUNDNESS_FINDINGS_CLEAN_VERIFY_2026-07.md.
    if unified.valid && unified.trust_level == TrustLevel::KernelVerified {
        println!("s VERIFIED");
        EXIT_VERIFIED
    } else if unified.valid && unified.steps_trusted == 0 {
        // Structurally derives the empty clause but leans on unchecked holes.
        println!("s HOLEY");
        eprintln!(
            "c holey: proof derives the empty clause but has structurally-accepted \
             step(s) (trust: {}); not a kernel-verified refutation",
            unified.trust_level,
        );
        EXIT_INVALID
    } else {
        println!("s INVALID");
        for err in &unified.errors {
            eprintln!("c {err}");
        }
        EXIT_INVALID
    }
}

/// Print the `c ERROR: ...` line for a `PipelineError` and return EXIT_ERROR.
fn report_pipeline_error(e: &PipelineError) -> i32 {
    match e {
        PipelineError::UnknownFormat => {
            eprintln!("c ERROR: could not detect proof format");
            eprintln!("c hint: use --format lrat|drat|alethe|smtlib2|veripb to specify explicitly");
        }
        PipelineError::EmptyProof => {
            eprintln!("c ERROR: proof file is empty");
        }
        _ => {
            eprintln!("c ERROR: {e}");
        }
    }
    EXIT_ERROR
}

/// SMT-COMP proof exhibition track output mode.
///
/// Emits three lines on stdout:
///   * Line 1 — `valid` | `holey` | `invalid` | `unknown`
///   * Line 2 — `holes: N`
///   * Line 3 — `steps: N, trusted: N`
///
/// Exit code 0 for `valid` and `holey`, 10 for `invalid`, 1 for errors.
pub fn run_smtcomp(args: &ProofCheckInputs<'_>) -> i32 {
    let formula_bytes = match std::fs::read(args.formula_path) {
        Ok(b) => b,
        Err(e) => {
            println!("unknown");
            eprintln!("c ERROR: reading formula: {e}");
            return EXIT_ERROR;
        }
    };

    let proof_bytes = match std::fs::read(args.proof_path) {
        Ok(b) => b,
        Err(e) => {
            println!("unknown");
            eprintln!("c ERROR: reading proof: {e}");
            return EXIT_ERROR;
        }
    };

    match verify_any_proof(&formula_bytes, &proof_bytes) {
        Ok(unified) => {
            let (verdict, exit_code) = if !unified.valid {
                ("invalid", EXIT_INVALID)
            } else if unified.steps_trusted == 0
                && unified.trust_level == TrustLevel::KernelVerified
            {
                ("valid", EXIT_VERIFIED)
            } else if unified.steps_trusted == 0 {
                ("holey", EXIT_VERIFIED)
            } else {
                ("invalid", EXIT_INVALID)
            };

            println!("{verdict}");
            println!("holes: {}", unified.steps_trusted);
            println!(
                "steps: {}, trusted: {}",
                unified.steps_verified, unified.steps_trusted,
            );

            if args.timing {
                eprintln!(
                    "c format: {}  trust: {}  verify_us: {}",
                    unified.format, unified.trust_level, unified.verification_time_us,
                );
            }

            exit_code
        }
        Err(e) => {
            println!("unknown");
            eprintln!("c ERROR: {e}");
            EXIT_ERROR
        }
    }
}

/// SAT-COMP unsat certificate validation mode.
///
/// Emits `s VERIFIED` or `s NOT VERIFIED` on stdout per SAT-COMP convention.
pub fn run_satcomp(args: &ProofCheckInputs<'_>) -> i32 {
    let cnf_bytes = match std::fs::read(args.formula_path) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("c ERROR: reading CNF: {e}");
            return EXIT_ERROR;
        }
    };

    let proof_bytes = match std::fs::read(args.proof_path) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("c ERROR: reading proof: {e}");
            return EXIT_ERROR;
        }
    };

    match verify_any_proof(&cnf_bytes, &proof_bytes) {
        Ok(unified) => {
            if args.timing {
                eprintln!(
                    "c format: {}  steps_verified: {}  verify_us: {}",
                    unified.format, unified.steps_verified, unified.verification_time_us,
                );
            }

            // SOUNDNESS (root cause C): mirror `run_smtcomp`. `s VERIFIED` is a
            // discharge claim, so require full kernel verification. `unified.valid`
            // alone is only the structural "derives empty clause" signal, which is
            // true even for a holey proof whose empty clause was laundered from a
            // structurally-accepted step. See
            // docs/SOUNDNESS_FINDINGS_CLEAN_VERIFY_2026-07.md.
            if unified.valid && unified.trust_level == TrustLevel::KernelVerified {
                println!("s VERIFIED");
                EXIT_VERIFIED
            } else if unified.valid {
                // Structurally derives the empty clause but not fully verified
                // (structurally-accepted or trusted holes): not a discharge.
                println!("s NOT VERIFIED");
                eprintln!(
                    "c not fully kernel-verified (trust: {}, trusted steps: {})",
                    unified.trust_level, unified.steps_trusted,
                );
                EXIT_INVALID
            } else {
                println!("s NOT VERIFIED");
                for err in &unified.errors {
                    eprintln!("c {err}");
                }
                EXIT_INVALID
            }
        }
        Err(e) => {
            println!("s NOT VERIFIED");
            eprintln!("c ERROR: {e}");
            EXIT_INVALID
        }
    }
}
