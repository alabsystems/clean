# Kernel Arena, Round 2026-09 (vendored)

The test suite of the Lean Kernel Arena's Round 2026-09, archived on Zenodo:
record 22944094, DOI [10.5281/zenodo.22944094](https://doi.org/10.5281/zenodo.22944094),
by The Lean Kernel Arena contributors, under the Apache License 2.0. The round
ran at arena commit `5d7ca987618f1136aaa296057b50a2c10c4ce77a`
(<https://github.com/leanprover/lean-kernel-arena>).

| File | What | Source |
|---|---|---|
| `lean-arena-round-2026-09-tests.tar.gz` | the round's 193 tests (71 `bad/`, 122 `good/`), each a lean4export 3.1.0 NDJSON export of Lean 4.29.1, byte for byte | Zenodo file `lean-arena-round-2026-09-tests.tar.gz`, sha256 `98a69742b538296c5f413d0527dfeef8c4d1815fe64b12c8623cd33de63bee0d` (md5 `2dcf78974886c35f22a3ce2dfad69fd9`, as Zenodo lists it) |
| `round-2026-09.table.json` | per test: expected outcome, the timeout of its YAML at the arena commit, its sha256, and the verdicts of the kernels `lake check --paranoid` bundles | derived by `scripts/kernel_arena_round.py` from the Zenodo file `lean-arena-round-2026-09-results.json` (sha256 `c48cab650e1bcfbb4231221d0b68820880a077ac67b37e435bf1a4aa9caff9f7`, not vendored: 4.2 MB, mostly checker output) |
| `declines.json` | the reviewed declines table | this repository |

Vendored rather than fetched (decision R115 in `docs/DECISIONS.md`): the archive
is 3.5 MB compressed, so the battery runs offline and never refuses for want of
a network. The tests read it in memory after checking its sha256
(`tests/support/kernel_arena.rs`); nothing in it is executed.
