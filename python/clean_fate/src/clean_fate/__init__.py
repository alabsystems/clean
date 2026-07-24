# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

"""
clean-fate: clean integration for FATE-Eval benchmarking.

This package provides a drop-in replacement for FATE-Eval's Verifier class,
enabling clean-server to be used as the verification backend for FATE benchmarks.

Usage:
    from clean_fate import cleanVerifier, DeltaMeasurement

    verifier = cleanVerifier(endpoint="http://localhost:8000")
    result = verifier.verify(code, timeout=30, extra_info={})

    # For batch verification (requires clean llm/verifyProofBatch)
    results = verifier.batch_verify(codes, timeout=30, max_workers=8)

    # For δ measurement per 4/δ bound
    dm = DeltaMeasurement(verifier)
    dm.run_trial(problem_id, code, proofs, timeout)
    report = dm.report()
"""

from clean_fate.delta import (
    BenchmarkStats,
    DeltaMeasurement,
    DeltaReport,
    StageResult,
    TimingStats,
    TrialResult,
)
from clean_fate.structs import (
    ExtractedTheorem,
    cleanVerifyResult,
    Message,
    Pos,
    SorryLocation,
    SortedMessages,
    TimingBreakdown,
    VerifyFileResult,
)
from clean_fate.verifier import cleanVerifier

__version__ = "0.1.0"
__all__ = [
    "cleanVerifier",
    "cleanVerifyResult",
    "SortedMessages",
    "Message",
    "Pos",
    "TimingBreakdown",
    "VerifyFileResult",
    "ExtractedTheorem",
    "SorryLocation",
    "DeltaMeasurement",
    "StageResult",
    "TrialResult",
    "DeltaReport",
    "BenchmarkStats",
    "TimingStats",
]
