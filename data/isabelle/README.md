# data/isabelle

Inputs of the Isabelle zproof import that are not code and cannot be
regenerated. Code and session lists live in `scripts/isabelle/` (development tree only).

## `v32_ledger_seed.txt`

The retry seed of the corpus v3.2 ledger burn-down: 123,027 Isabelle proof-term
serials, one per line, ascending, no comments. They are the `trusted-ledger`
axioms of the v3.2 grand over `corpora/main_v32.jsonl` (the "123,027
trusted-ledger axioms" of `docs/analysis/ISABELLE_GRAND_REGEN_2026-07-27.md` and
`docs/analysis/zproof-v32-reject-census.md`).

- **Origin:** `~/isabelle-work/corpora/ledger_seed.txt` on the capture machine,
  written 2026-07-22, copied byte-for-byte on 2026-11-15 (978,107 bytes, sha256
  `6362325583074ca3e9dfa05a86f5f48da7ec8b0ee81fdc40dab057255dc2365d`).
- **Why it is kept:** it cannot be rebuilt. The current
  `corpora/main_v32.jsonl.ledger.tsv` (2026-08-01) has 121,943 rows; the ledger
  shrank after this seed was taken.
- **Consumer:** `scripts/isabelle/v32_ledger_burndown2.sh` (development tree only)
  passes it as `clean mathverse isabelle-import --retry-ledger --retry-seed`,
  which re-attempts only these serials against `corpora/main_v32.snap`. That
  script reads it from `$ISABELLE_WORK_ROOT/corpora/ledger_seed.txt`, beside the
  corpus and snapshot it needs; to rerun it, copy this file there:

  ```bash
  cp data/isabelle/v32_ledger_seed.txt "$ISABELLE_WORK_ROOT/corpora/ledger_seed.txt"
  ```

  A fresh import does not need it: its grand writes a new ledger.
