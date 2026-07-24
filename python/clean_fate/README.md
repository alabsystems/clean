# Clean-fate

Python integration package for using Clean as a FATE-Eval verification backend.

## Overview

This package provides a drop-in replacement for FATE-Eval's `Verifier` class,
enabling Clean-server to be used for theorem verification. This delivers
100-1000x speedup over the standard Lean 4 subprocess approach.

## Installation

```bash
cd python/clean_fate
pip install -e .
```

## Requirements

- Python 3.11+
<!-- markdown-link-check-disable-next-line -->
- Clean-server running (default: http://localhost:8000)

## Usage

### Basic Verification

<!-- markdown-link-check-disable -->
```python
from clean_fate import CleanVerifier

verifier = CleanVerifier(endpoint="http://localhost:8000")

# Verify a FATE problem
code = '''
import Mathlib.Data.Nat.Basic

theorem simple : 1 + 1 = 2 := by rfl
'''

result = verifier.verify(code, timeout=30)
print(f"Verified: {result.complete}")
print(f"Time: {result.verify_time:.6f}s")
```
<!-- markdown-link-check-enable -->

### Batch Verification

```python
codes = [code1, code2, code3]
results = verifier.batch_verify(codes, timeout=60)

for i, r in enumerate(results):
    print(f"Problem {i}: {'PASS' if r.complete else 'FAIL'}")
```

### δ Measurement (4/δ Bound)

```python
from clean_fate import CleanVerifier, DeltaMeasurement

verifier = CleanVerifier()
dm = DeltaMeasurement(verifier)

# Run trials for each problem
for problem_id, code, proofs in benchmark_data:
    dm.run_trial(problem_id, code, proofs, timeout=30)

# Get measurement report
report = dm.report()
print(f"Overall δ: {report['overall_delta']:.4f}")
print(f"E[n] ≤ 4/δ = {report['expected_iterations_4_over_delta']:.1f}")
print(f"Stage δ values: {report['stage_deltas']}")
```

## FATE-Eval Integration

To use with FATE-Eval:

<!-- markdown-link-check-disable -->
```python
# In your FATE-Eval config or custom script
from clean_fate import CleanVerifier

# Replace FATE-Eval's verifier
verifier = CleanVerifier(endpoint="http://localhost:8000")

# Use with existing FATE-Eval code
# verifier.verify() and verifier.batch_verify() have compatible signatures
```
<!-- markdown-link-check-enable -->

## API Reference

### CleanVerifier

<!-- markdown-link-check-disable -->
```python
CleanVerifier(
    endpoint: str = "http://localhost:8000",
    lean_workspace: str = None,  # Ignored, for FATE-Eval compat
    lake_path: str = None,       # Ignored, for FATE-Eval compat
)
```
<!-- markdown-link-check-enable -->

**Methods:**
- `verify(code, timeout, extra_info) -> CleanVerifyResult`
- `batch_verify(codes, timeout, max_workers, extra_infos) -> list[CleanVerifyResult]`
- `verify_file(file_path, timeout, extra_info) -> CleanVerifyResult`

### CleanVerifyResult

Compatible with FATE-Eval's `VerifyResult`:

```python
@dataclass
class CleanVerifyResult:
    sorted_messages: SortedMessages
    verified_code: str
    verified_timeout: int
    pass_: bool           # No errors
    complete: bool        # Proof complete (no sorries)
    is_timeout: bool
    verify_time: float    # Seconds
    complete_timestamp: str
    extra_info: dict
    lean_toolchain: str = "Clean"
    timing: TimingBreakdown | None  # Clean extension
    certificate: str | None         # Clean extension
```

### DeltaMeasurement

```python
DeltaMeasurement(verifier: CleanVerifier)
```

**Methods:**
- `run_trial(problem_id, code, proofs, timeout) -> list[TrialResult]`
- `calculate_delta(stage=None) -> float`
- `calculate_expected_iterations() -> float`
- `report() -> dict`
- `clear()` - Reset all results

## Dependencies

- Clean Phase 1 API: `llm/verifyProof` (required)
- Clean Phase 2 API: `llm/verifyProofBatch` (optional, enables batch mode)
- Clean Phase 2 API: `TimingBreakdown` (optional, enables δ measurement)

## License

Apache-2.0 - Copyright 2026 Andrew Yates
