// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Solver execution and proof extraction pipeline for AyProofBackend.

use super::{AyProofBackend, AyProofQuality, AyProofResult};
use crate::bridge::ay_backend::{AyError, AyResult, AyUnknownReason};
use ay::executor::Executor;
use ay::{parse, ProofQuality};
use ay_proof::check_proof_with_quality;
use std::num::NonZeroU64;
use std::time::Duration;

/// What bounds one solve: the options the script sets right after
/// `set-logic`, which the fresh executor running it applies before the
/// `check-sat`.
#[derive(Debug, Clone, Copy)]
enum SolveBounds {
    /// [`AyProofBackend::check_sat`]: a `:timeout` from
    /// `AY_DIRECT_SOLVE_TIMEOUT_MS`, else 90 s (`0` writes none), and no
    /// `:rlimit`, so only ay's default ground allowance counts.
    Legacy,
    /// [`AyProofBackend::check_sat_with_effort`]: the caller's count as
    /// `:rlimit` and the caller's clock as `:timeout`. Clean reads nothing
    /// from the environment for them.
    Effort {
        effort: NonZeroU64,
        backstop_ms: NonZeroU64,
    },
}

/// The `:timeout` a backstop writes: whole milliseconds rounded up, and never
/// `0`, which ay reads as "no deadline". A backstop always arms a clock.
fn backstop_ms(backstop: Duration) -> NonZeroU64 {
    let ms = u64::try_from(backstop.as_nanos().div_ceil(1_000_000)).unwrap_or(u64::MAX);
    NonZeroU64::new(ms).unwrap_or(NonZeroU64::MIN)
}

impl AyProofBackend {
    /// Check satisfiability and optionally extract proof
    ///
    /// If a proof profile with verification_tier >= 1 is configured,
    /// UNSAT proofs will be verified using Carcara before being accepted.
    ///
    /// This entry sends no count: every solve is bounded by a wall clock
    /// (`AY_DIRECT_SOLVE_TIMEOUT_MS`, else 90 s) and ay's default ground
    /// allowance. [`Self::check_sat_with_effort`] is the counted entry; this
    /// one stays, unchanged, until its embedders have moved to it.
    ///
    /// # Errors
    ///
    /// Returns `TheoryRejected` if the configured logic is not accepted by
    /// the proof profile (checked at start, before any solving).
    pub fn check_sat(&mut self) -> AyResult<AyProofResult> {
        self.solve(SolveBounds::Legacy)
    }

    /// Check satisfiability within the caller's effort, with the caller's
    /// clock only as a backstop, and optionally extract proof.
    ///
    /// `effort` is the caller's count. The fresh executor that runs the
    /// script applies it as `(set-option :rlimit effort)` before the
    /// `check-sat`, in ay's `:rlimit` unit at the pinned revision (SAT
    /// conflicts per SAT solve today). It is nonzero because ay reads
    /// `:rlimit 0` as no limit at all.
    ///
    /// `backstop` is the caller's wall clock, applied as
    /// `(set-option :timeout ms)`: rounded up to whole milliseconds and never
    /// `0`, which ay reads as no deadline. It is ay's deadline for the
    /// `check-sat` command, ay's own post-solve certification included, and
    /// not a bound on this call: after an UNSAT, the proof extraction, the
    /// native `check_proof_with_quality` check, the Alethe export and, at
    /// verification tier 1, the Carcara check run once that command has
    /// returned, under no clock, as they do on [`Self::check_sat`].
    ///
    /// Clean reads nothing from the environment on this path;
    /// `AY_DIRECT_SOLVE_TIMEOUT_MS` belongs to [`Self::check_sat`] alone. ay
    /// still reads its own knobs during the solve (`AY_DT_CERT`,
    /// `AY_DT_LAZY_AUFLIA`, `AY_A2B_BUDGET_SCALE`, among others).
    ///
    /// A solve that ends undecided answers [`AyProofResult::Unknown`] with
    /// ay's reason: [`AyUnknownReason::ResourceLimit`] (`resourceout`) when a
    /// count was spent, and [`AyUnknownReason::Timeout`] (`timeout`) when the
    /// backstop fired, a clock reading and not a property of the formula. At
    /// the pinned ay, neither the count nor the clock is only the caller's:
    ///
    /// - `:rlimit` replaces ay's default conflict allowance but not its
    ///   default decision allowance, so a `resourceout` from ay's ground
    ///   pipeline is the caller's effort or ay's own decision count. ay's
    ///   detail sentence names the conflicts and decisions the solve reached.
    /// - ay's QF_LRA split loop reads no `:rlimit` and gives each SAT
    ///   iteration a wall budget of its own. A lapsed budget resumes the
    ///   search on another path, so the caller's count never stops such a
    ///   solve, and whether it decides before the backstop can move with load.
    /// - A `memout` can be a reading of the whole process's footprint against
    ///   ay's process-wide ceiling. `Executor::new()` does not arm that
    ///   ceiling; ay-bindings' direct execution arms it, once per process, so
    ///   a host that also solves through ay-bindings (trustc) has it armed.
    ///
    /// These belong to ay, which must remove them; this entry does not.
    /// R-AY-PROOF-EFFORT-20261011 in `docs/DECISIONS.md` cites each one's
    /// source.
    ///
    /// # Errors
    ///
    /// As [`Self::check_sat`].
    pub fn check_sat_with_effort(
        &mut self,
        effort: NonZeroU64,
        backstop: Duration,
    ) -> AyResult<AyProofResult> {
        self.solve(SolveBounds::Effort {
            effort,
            backstop_ms: backstop_ms(backstop),
        })
    }

    /// Solve the recorded script under `bounds` and interpret the answer.
    fn solve(&mut self, bounds: SolveBounds) -> AyResult<AyProofResult> {
        // Early theory acceptance check - fail fast before solving
        // Part of #748: Ensures profile rejection happens before solver errors
        self.ensure_profile_accepts_current_logic()?;

        let last_output = self.execute_script(bounds)?;

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
            _ => Ok(self.unknown_result()),
        }
    }

    /// The `Unknown` answer of the last solve, carrying ay's own account of
    /// why it ended undecided. A solve ay gave no reason for reads as
    /// [`AyUnknownReason::Unknown`], ay's "no specific reason".
    fn unknown_result(&self) -> AyProofResult {
        AyProofResult::Unknown {
            reason: self
                .executor
                .unknown_reason()
                .map_or(AyUnknownReason::Unknown, AyUnknownReason::from),
            detail: self.executor.unknown_detail().map(str::to_owned),
        }
    }

    /// Build SMT-LIB script, parse, and execute with panic isolation (#1562).
    fn execute_script(&mut self, bounds: SolveBounds) -> AyResult<Option<String>> {
        let mut script = format!("(set-logic {})\n", self.logic);
        match bounds {
            SolveBounds::Legacy => {
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
            }
            SolveBounds::Effort {
                effort,
                backstop_ms,
            } => {
                // The caller's count decides where the search stops; its clock
                // only backs it up. Both are set before any assertion, on the
                // fresh executor below, and `last_problem` records them.
                script.push_str(&format!("(set-option :rlimit {effort})\n"));
                script.push_str(&format!("(set-option :timeout {backstop_ms})\n"));
            }
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
                // `context().assertions` is the LIVE, POST-PREPROCESSING stack —
                // NOT the authored premise scope. When preprocessing folds an
                // authored assertion to `false` it OVERWRITES that slot, so the
                // authored term is absent under every spelling and the exporter
                // refuses the proof (`reachable assume tN uses non-problem term
                // tM`) via the INFALLIBLE wrapper: a loud stderr line plus an
                // `(error ...)` s-expression handed back as if it were a proof.
                // ay's own accessor supplies `proof_export_scope_assertions()`
                // (problem assertions + originals + recorded raw rebuilds +
                // assumptions, minus an unauthored `false`) and is fallible, so
                // a refusal stays a refusal instead of becoming a fake document.
                // The premise set is NOT widened: membership is still exact
                // `TermId` identity, and every preprocessing-derived formula
                // that is not an authored premise is still rejected.
                let alethe = self
                    .executor
                    .try_export_last_proof_alethe_for_problem_scope()
                    .and_then(|export| {
                        export
                            .inspect_err(|error| {
                                tracing::debug!(
                                    %error,
                                    "ay declined to render an Alethe certificate for this proof"
                                );
                            })
                            .ok()
                    });
                (alethe, quality)
            }
            None => (None, None),
        }
    }
}
