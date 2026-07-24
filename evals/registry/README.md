<!-- Andrew Yates <andrewyates.name@gmail.com> -->
# Eval Registry

YAML eval specs live in this directory. Each file defines a single eval; see
`docs/evals.md` for the shared registry/template/results layout and the
required spec fields.

## Registered Evals

| Eval | Spec | Purpose |
| --- | --- | --- |
| `tactic-parity` | [`tactic-parity.yaml`](tactic-parity.yaml) | Lean4 replacement tactic parity and strict reconstruction scorecard. Records each tactic lane's proof-carry/fallback classification, keeps trusted-fallback sites counted-and-blocking, and stays fail-closed (`readiness_gate.status: blocked-pending-generated-counts`) until generated Lean4-vs-clean parity counts exist. Guarded by `crates/clean-elab/src/tactic/tests/tactic_parity_registry.rs` and `scripts/tactic_parity/generated_count_runner.py`. |

## Adding an eval

1. Add `evals/registry/<eval-id>.yaml` following the field list in `docs/evals.md`.
2. List it in the table above with a one-line purpose.
3. If the eval is guarded by a Rust/Python test, name that guard in the purpose
   column so the metadata and the executable check stay tied together.
