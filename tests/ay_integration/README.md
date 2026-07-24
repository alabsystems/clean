# Ay Integration Test Suite

Test files for Ay SMT solver integration with Clean.

## Files

| File | Description | Ay Logic |
|------|-------------|----------|
| `basic_sat.lean` | Propositional SAT/UNSAT | QF_SAT |
| `linear_arith.lean` | Linear integer arithmetic | QF_LIA |
| `bitvector.lean` | Fixed-width bitvector ops | QF_BV |
| `arrays.lean` | Array theory with LIA | QF_AUFLIA |
| `proof_import.lean` | DRAT/LRAT proof verification | - |
| `performance.lean` | Performance benchmarks | Mixed |

## Status

**Phase 2**: Ay FFI integration complete.

The Ay backend (`clean-auto/src/bridge/ay_backend.rs`) provides:
- Expression translation from kernel `Expr` to ay `Term`
- Support for QF_LIA, QF_LRA, QF_UF, QF_BV, QF_AUFLIA logics
- Incremental solving with push/pop
- Model extraction for SAT results
- **Proof extraction** via `AyProofBackend` (exports Alethe format proofs)

## Running Tests

```bash
# Run all Ay integration tests
lake test ay_integration

# Run specific test file
lake test ay_integration/basic_sat

# Run with verbose output (shows SMT-LIB2)
lake test ay_integration -v
```

## Performance Targets

See `performance.lean` for benchmark definitions. Targets from spec:

| Operation | Target |
|-----------|--------|
| FFI overhead | < 10 μs |
| Simple SAT | < 1 ms |
| QF_LIA | < 10 ms |
| QF_BV | < 10 ms |
| DRAT verify | < 100 ms |

## Contact

- Clean: github.com/alabsystems/clean
- Ay: github.com/alabsystems/ay
