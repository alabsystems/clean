# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

"""
δ measurement harness for 4/δ bound validation.

The 4/δ bound theorem (arXiv:2512.02080) proves that for an LLM prover
with per-iteration success probability δ, the expected number of iterations
to find a proof is bounded by E[n] ≤ 4/δ.

This module measures empirical δ values across FATE benchmark problems
to validate the theorem and identify bottleneck stages in the verification
pipeline.

Usage:
    from clean_fate import cleanVerifier, DeltaMeasurement

    verifier = cleanVerifier()
    dm = DeltaMeasurement(verifier)

    # Run trials for a problem
    for proof_attempt in generated_proofs:
        dm.run_trial("fate_x_001", code, [proof_attempt], timeout=30)

    # Get δ values
    report = dm.report()
    print(f"δ = {report['overall_delta']}")
    print(f"E[n] ≤ {report['expected_iterations_4_over_delta']}")
"""

import statistics
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Optional, TypedDict

if TYPE_CHECKING:
    from clean_fate.verifier import cleanVerifier


class VerifyWithTimingResult(TypedDict):
    """Return type for _verify_with_timing internal method."""

    verified: bool
    stages: list["StageResult"]
    total_ns: int


class BenchmarkStats(TypedDict):
    """Statistics for a single benchmark problem."""

    trials: int
    successes: int
    delta: float
    mean_time_ns: float


class TimingStats(TypedDict):
    """Timing statistics across all trials."""

    mean_ns: float
    median_ns: float
    stdev_ns: float


class DeltaReport(TypedDict):
    """Complete measurement report from DeltaMeasurement.report()."""

    total_trials: int
    overall_delta: float
    expected_iterations_4_over_delta: float
    stage_deltas: dict[str, float]
    timing_stats: TimingStats
    per_benchmark: dict[str, BenchmarkStats]


@dataclass
class StageResult:
    """Result of a single verification stage."""

    stage: str  # parse, elaborate, verify
    success: bool
    time_ns: int
    error: Optional[str] = None


@dataclass
class TrialResult:
    """Result of a single proof attempt."""

    problem_id: str
    attempt_num: int
    stages: list[StageResult]
    overall_success: bool
    total_time_ns: int


@dataclass
class DeltaMeasurement:
    """
    Measure empirical δ for 4/δ bound validation.

    Tracks verification results across multiple proof attempts and calculates
    per-stage and overall success probabilities (δ values).

    The 4/δ bound maps verification stages to theorem stages:
    - parse: CodeGen stage (syntax correctness)
    - elaborate: InvariantSynth stage (type correctness)
    - verify: SMTSolving stage (logical correctness)

    Args:
        verifier: cleanVerifier instance for verification calls
    """

    verifier: "cleanVerifier"
    results: list[TrialResult] = field(default_factory=list)

    def run_trial(
        self,
        problem_id: str,
        code: str,
        proofs: list[str],
        timeout: int = 30,
    ) -> list[TrialResult]:
        """
        Run multiple proof attempts for a single problem.

        Args:
            problem_id: Identifier for the problem (e.g., "fate_x_001")
            code: FATE problem code (complete Lean file with sorry)
            proofs: List of proof attempts to try
            timeout: Verification timeout per proof in seconds

        Returns:
            List of TrialResult for each attempt
        """
        goal, _ = self.verifier._parse_fate_code(code)
        trials = []

        for i, proof in enumerate(proofs):
            result = self._verify_with_timing(goal, proof, timeout)

            trial = TrialResult(
                problem_id=problem_id,
                attempt_num=i,
                stages=result["stages"],
                overall_success=result["verified"],
                total_time_ns=result["total_ns"],
            )
            trials.append(trial)
            self.results.append(trial)

        return trials

    def calculate_delta(self, stage: Optional[str] = None) -> float:
        """
        Calculate empirical δ (stage success probability).

        If stage is None, calculates overall success rate.
        If stage is specified ('parse', 'elaborate', 'verify'),
        calculates that stage's success rate.

        Args:
            stage: Optional stage name to calculate δ for

        Returns:
            δ value between 0 and 1
        """
        if not self.results:
            return 0.0

        if stage is None:
            successes = sum(1 for r in self.results if r.overall_success)
            total = len(self.results)
        else:
            successes = 0
            total = 0
            for r in self.results:
                for s in r.stages:
                    if s.stage == stage:
                        total += 1
                        if s.success:
                            successes += 1

        return successes / total if total > 0 else 0.0

    def calculate_expected_iterations(self) -> float:
        """
        Calculate E[n] based on 4/δ bound.

        E[n] ≤ 4/δ

        Returns:
            Expected number of iterations, or inf if δ = 0
        """
        delta = self.calculate_delta()
        if delta > 0:
            return 4.0 / delta
        return float("inf")

    def report(self) -> DeltaReport:
        """
        Generate measurement report.

        Returns DeltaReport with:
        - total_trials: Number of proof attempts
        - overall_delta: Overall success probability
        - expected_iterations_4_over_delta: E[n] ≤ 4/δ bound
        - stage_deltas: Per-stage δ values
        - timing_stats: Mean, median, stdev of verification times
        - per_benchmark: Per-problem statistics
        """
        stages = ["parse", "elaborate", "verify"]
        stage_deltas = {s: self.calculate_delta(s) for s in stages}

        overall_delta = self.calculate_delta()
        expected_n = self.calculate_expected_iterations()

        times_ns = [r.total_time_ns for r in self.results if r.total_time_ns > 0]

        timing_stats = TimingStats(
            mean_ns=statistics.mean(times_ns) if times_ns else 0.0,
            median_ns=statistics.median(times_ns) if times_ns else 0.0,
            stdev_ns=statistics.stdev(times_ns) if len(times_ns) > 1 else 0.0,
        )

        return DeltaReport(
            total_trials=len(self.results),
            overall_delta=overall_delta,
            expected_iterations_4_over_delta=expected_n,
            stage_deltas=stage_deltas,
            timing_stats=timing_stats,
            per_benchmark=self._per_benchmark_stats(),
        )

    def _per_benchmark_stats(self) -> dict[str, BenchmarkStats]:
        """Calculate stats per problem."""
        by_problem: dict[str, list[TrialResult]] = {}
        for r in self.results:
            if r.problem_id not in by_problem:
                by_problem[r.problem_id] = []
            by_problem[r.problem_id].append(r)

        stats: dict[str, BenchmarkStats] = {}
        for pid, trials in by_problem.items():
            successes = sum(1 for t in trials if t.overall_success)
            times_ns = [t.total_time_ns for t in trials if t.total_time_ns > 0]
            stats[pid] = BenchmarkStats(
                trials=len(trials),
                successes=successes,
                delta=successes / len(trials) if trials else 0,
                mean_time_ns=statistics.mean(times_ns) if times_ns else 0,
            )

        return stats

    def _verify_with_timing(
        self,
        goal: str,
        proof: str,
        timeout: int,
    ) -> VerifyWithTimingResult:
        """
        Verify with per-stage timing.

        Requires clean to return TimingBreakdown in response.
        Falls back to estimated timing if not available.
        """
        self.verifier._request_id += 1
        request = {
            "jsonrpc": "2.0",
            "method": "verifyProof",  # Note: llm/ prefix pending #94
            "params": {
                "goal": goal,
                "proof": proof,
                "timeout_ms": timeout * 1000,
            },
            "id": self.verifier._request_id,
        }

        try:
            response = self.verifier.client.post(self.verifier.endpoint, json=request)
            response.raise_for_status()
            result = response.json().get("result", {})
        except Exception as e:
            return {
                "verified": False,
                "stages": [
                    StageResult("parse", False, 0, str(e)),
                    StageResult("elaborate", False, 0, None),
                    StageResult("verify", False, 0, None),
                ],
                "total_ns": 0,
            }

        timing = result.get("timing", {})
        verified = result.get("verified", False)
        error = result.get("error", {})
        error_msg = error.get("message", "") if error else ""

        # Build stage results
        stages = [
            StageResult("parse", True, timing.get("parse_ns", 0), None),
            StageResult("elaborate", True, timing.get("elaborate_ns", 0), None),
            StageResult("verify", verified, timing.get("verify_ns", 0), None),
        ]

        # If not verified, determine which stage failed
        if not verified and error_msg:
            error_lower = error_msg.lower()
            if "parse" in error_lower or "syntax" in error_lower:
                stages[0] = StageResult("parse", False, stages[0].time_ns, error_msg)
                stages[1] = StageResult("elaborate", False, 0, None)
                stages[2] = StageResult("verify", False, 0, None)
            elif "type" in error_lower or "elaborate" in error_lower or "expected" in error_lower:
                stages[1] = StageResult("elaborate", False, stages[1].time_ns, error_msg)
                stages[2] = StageResult("verify", False, 0, None)
            else:
                # Verification stage failed
                stages[2] = StageResult("verify", False, stages[2].time_ns, error_msg)

        total_ns = timing.get("total_ns") or result.get("time_ns", 0)

        return {
            "verified": verified,
            "stages": stages,
            "total_ns": total_ns,
        }

    def clear(self) -> None:
        """Clear all recorded results."""
        self.results = []
