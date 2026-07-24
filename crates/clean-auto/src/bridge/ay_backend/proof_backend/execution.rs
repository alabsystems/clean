// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Solver execution and proof extraction pipeline for AyProofBackend.

use super::{AyProofBackend, AyProofQuality, AyProofResult};
use crate::bridge::ay_backend::{AyError, AyResult};
use ay::executor::Executor;
use ay::{parse, ProofQuality};
use ay_proof::{check_proof_with_quality, export_alethe_with_problem_scope};

impl AyProofBackend {
    /// Check satisfiability and optionally extract proof
    ///
    /// If a proof profile with verification_tier >= 1 is configured,
    /// UNSAT proofs will be verified using Carcara before being accepted.
    ///
    /// # Errors
    ///
    /// Returns `TheoryRejected` if the configured logic is not accepted by
    /// the proof profile (checked at start, before any solving).
    pub fn check_sat(&mut self) -> AyResult<AyProofResult> {
        // Early theory acceptance check - fail fast before solving
        // Part of #748: Ensures profile rejection happens before solver errors
        self.ensure_profile_accepts_current_logic()?;

        let last_output = self.execute_script()?;

        // Interpret the result
        match last_output.as_deref() {
            Some("sat") => Ok(AyProofResult::Sat),
            Some("unsat") => {
                let (proof, raw_quality) = self.extract_proof_and_quality();
                let verified = self.verify_proof_if_required(&proof, &raw_quality)?;
                Ok(AyProofResult::Unsat {
                    proof,
                    verified,
                    quality: raw_quality.map(AyProofQuality::from),
                })
            }
            _ => Ok(AyProofResult::Unknown),
        }
    }

    /// Build SMT-LIB script, parse, and execute with panic isolation (#1562).
    fn execute_script(&mut self) -> AyResult<Option<String>> {
        let mut script = format!("(set-logic {})\n", self.logic);
        // Bound every check-sat with a wall-clock deadline. This backend runs
        // IN-PROCESS inside embedders (trust-certify inside trustc): without a
        // `:timeout`, the executor's solve controls stay None all the way down
        // (Executor -> LIA -> IntSat all honour a deadline that never arrives),
        // and one non-converging certify attempt can hold the host process for
        // hours while its BigInt churn grows unbounded (the aterm-lz4 /
        // trustc 300 GB incident ran exactly through here). Same env + default
        // as the trust-router direct backend (`AY_DIRECT_SOLVE_TIMEOUT_MS`,
        // 90 s, 0 disables); a lapsed deadline degrades to Unknown, which the
        // certify caller treats as "no proof" — sound, fail-closed.
        let timeout_ms = std::env::var("AY_DIRECT_SOLVE_TIMEOUT_MS")
            .ok()
            .and_then(|s| s.parse::<u64>().ok())
            .unwrap_or(90_000);
        if timeout_ms > 0 {
            script.push_str(&format!("(set-option :timeout {})\n", timeout_ms));
        }
        for s in self.declarations.iter().chain(self.assertions.iter()) {
            script.push_str(s);
            script.push('\n');
        }
        script.push_str("(check-sat)\n");
        self.last_problem = script.clone();

        let commands =
            parse(&script).map_err(|e| AyError::ScriptError(format!("parse error: {}", e)))?;
        self.executor = Executor::new();
        if self.config.produces_proofs() {
            self.executor.set_produce_proofs(true);
        }

        // catch_unwind isolates ay DPLL(T) panics (ay#1654, ay#3475, ay#3484).
        // Propagate executor errors — swallowing them drops constraints (#2129 AC3).
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut last_output = None;
            for cmd in &commands {
                let output = self
                    .executor
                    .execute(cmd)
                    .map_err(|e| AyError::ScriptError(format!("executor error: {}", e)))?;
                if output.is_some() {
                    last_output = output;
                }
            }
            Ok::<_, AyError>(last_output)
        }));
        match result {
            Ok(inner) => inner,
            Err(payload) => Err(AyError::SolverPanic(
                crate::bridge::ay_backend::panic_payload_to_string(&payload),
            )),
        }
    }

    /// Extract proof string and native quality metrics from the last UNSAT result.
    /// Runs native check before Alethe export to avoid string round-trip.
    fn extract_proof_and_quality(&self) -> (Option<String>, Option<ProofQuality>) {
        if !self.config.produces_proofs() {
            return (None, None);
        }
        match self.executor.last_proof() {
            Some(raw_proof) => {
                let terms = self.executor.terms();
                // On Err, quality is None → verify_proof_if_required falls through to Carcara.
                let quality = check_proof_with_quality(raw_proof, terms)
                    .inspect_err(|error| {
                        tracing::debug!(
                            %error,
                            "native ay-proof check failed; falling through to Carcara"
                        );
                    })
                    .ok();
                let assertions = &self.executor.context().assertions;
                let alethe = export_alethe_with_problem_scope(raw_proof, terms, assertions);
                (Some(alethe), quality)
            }
            None => (None, None),
        }
    }
}
