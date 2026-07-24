# TLA+ obligation samples

Sample `TlaObligation` JSON files exercised by `clean verify tla` (#3452).

Each file is a serde-encoded [`clean_tla::obligation::TlaObligation`]
(`#[derive(Serialize, Deserialize)]` on the struct and its nested enums).
The serde layout uses the default externally-tagged representation — unit
variants render as bare strings (`"True"`, `"False"`) and struct variants
render as `{"VariantName": { ... fields ... }}`.

## Schema

```json
{
  "module": "<string>",
  "line": <optional u32>,
  "declares": [ <TlaDeclare> ... ],
  "hypotheses": [ { "name": "<string>", "formula": <TlaFormula> } ... ],
  "goal": <TlaFormula>,
  "tactic_hint": "<optional tactic name>"
}
```

See:
- `TlaObligation`, `TlaDeclare`, `TlaFormula`, `TlaExpr` in
  crates/clean-tla/src/{obligation,encoding}.rs for the authoritative
  wire shape.
- `benchmarks/tlaps/` for a richer `BenchmarkObligation` schema used by
  the `clean tlaps bench` / `clean tlaps validate` / `clean tlaps show`
  verbs — that schema is similar but not byte-identical to
  `TlaObligation`'s native serde layout.

## Invocation

```bash
# Verify a single obligation
clean verify tla benchmarks/tla/trivial_true.json

# Verify a bundled smoke-test sample (name matches file stem under
# benchmarks/tla/ at compile time)
clean verify tla --sample trivial_true

# Enumerate bundled samples
clean verify tla --list
```

## Files

| File | Goal | Notes |
|------|------|-------|
| `trivial_true.json` | `True` | Smoke test — no hypotheses, no declarations. |
