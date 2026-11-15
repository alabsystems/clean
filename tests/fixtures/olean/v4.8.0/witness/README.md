# Lean v4.8.0 world witness

`FactLib.olean` is the tracked `.olean` from which `crates/clean-olean/build.rs`
measures the identity of the `v4.8.0` row of `crates/clean-olean/lean_worlds.tsv`
(docs/DECISIONS.md R38, R81): header version 1 and githash
`df668f00e6c08cb63661aacc43d0e83388e2c60d`, the identity every `.olean` of
Trust's vendored v4.8.0 closure carries (`vendor/lean-core-oleans`,
`crates/trust-clean/fixtures/trustir-oleans`).

It is a byte copy of
`reports/2026-09-24-module-trust/round22/fixtures/atk/fact/lib48/FactLib.olean`
(14360 bytes, BLAKE3
`6a9e927fdbd41d163dcfa3e2d0ec9049e8e93270339e26c8f7e2789ed689b8b4`), compiled by
`leanprover/lean4:v4.8.0` from `FactLib.lean` beside it. The copy lives under
`tests/` because the public snapshot ships `tests/` and not `reports/`, and
`build.rs` refuses to build when a tracked world fixture is missing.

Regenerate (the bytes, and so the BLAKE3, may differ; the header identity may not):

```sh
cd tests/fixtures/olean/v4.8.0/witness
elan run leanprover/lean4:v4.8.0 lean FactLib.lean -o FactLib.olean
```
