# data/spine_set.json — PENDING (recorded state, not silence)

`data/spine_set.json` — the committed spine set that Claim S quantifies over
(designs/2026-08-22-spine-and-lattice-program.md §3.1, job G-SPINE-SET) — is
**not yet minted**, because no whole-crate `clean_kernel` coverage/dump
artifact measured **post-a5aae3bde** exists: both 2026-08-22 censuses
(data/crystal_a0_census_2026-08-22.json,
data/crystal_frontier_census_2026-08-22.json) were measured at `746ef6cee`, an
ancestor of the ctx-Arc change, and their backing dump lives on the trust host
(the Trust host's own scratchpad, `laneTU/wc-tip`), not in this repo. It is minted in two
halves: (1) on a host with a writable `~/trust` (the **[trust-host]**
measurement half — not this machine), re-run the whole-crate dump producer
(laneTU pattern, T-LOCK interim pin-materialization build) against clean
post-a5aae3bde, extended to emit the per-body call-graph, producer-class, and
provenance fields that `scripts/spine_set.py --describe` specifies, with the
driver identified by its dylib sha256; then (2) on the clean side, derive and
commit the artifact with
`scripts/spine_set.py --dump <dump.json> --driver-digest <dylib-sha256> --out data/spine_set.json`
(plus `--boundary` once contract-boundary ledger rows exist). The derivation
fails closed — it never emits a partial spine set from a coverage-only dump —
so until that dump is produced, this file is the artifact's recorded absence.
