# Benchmarks

Benchmark harnesses and templates for reproducible Clean measurements.

## Usage

```bash
# Copy templates to set up benchmarking
cp -r templates/* .

# Run evaluation
./run_eval.sh --suite default
```

## Files

- `templates/` - Copy these files to start
  - `run_eval.sh` - Evaluation runner script
- `lean4_kernel_bench/` - Lean 4 kernel comparison harness
- `tla/` - TLA benchmark fixtures
- `tlaps/` - TLAPS benchmark fixtures

## Documentation

Public benchmark claims, freshness policy, and release evidence requirements
are documented in ../docs/BENCHMARKS.md.
