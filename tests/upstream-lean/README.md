# `tests/upstream-lean/` — the vanilla-Lean drop-in instrument

Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0

Mirrors `trust/tests/upstream-rust/`. It exists to measure one sentence from
the two-language plan:

> "vanilla Lean is valid input."

## The three clauses, and where each one lives

| Clause | File | Enforced by |
|---|---|---|
| baseline pin | `baseline.toml` | `run_upstream_lean.py` re-reads `tests/lean4_compat/MANIFEST.json` every run and fails on drift |
| expiring exceptions ledger | `exceptions.toml` | `check_ledger_expirations.py` (owner / issue / `reviewed_on` / `expires_on`, all required on an active row) |
| a gate that fails | `corpus.toml` + `run_upstream_lean.py` | exits non-zero on any outcome not covered by an active row |

`run_upstream_lean.py` is wired into `scripts/local_gate.sh` (which `just gate`
and `just gate-fast` run, and which the pre-push hook invokes through the
sibling `trust-cg` meta-gate).

## What was here before, and why it was not enough

Measured 2026-09-01 at clean HEAD `c89b44931`:

* **`crates/clean-parser/src/lean4_compat.rs::lean4_parser_compatibility_suite`**
  walks all 100 corpus files and asserts `percentage >= 85.0` against a measured
  90%. A floor is a ratchet, not a ledger: it says how *many* files may fail,
  never *which*, so a newly fixed file and a newly broken one net to zero and
  the gate stays green.
* **`crates/clean-elab/tests/phase1_full_corpus.rs`** prints `PASS/PART/TIME/FAIL`
  per file and asserts nothing about any of it, and returns early unless
  `CLEAN_PHASE1_FULL_CORPUS=1` — so in a routine run it does not even measure.
* **Neither is in `scripts/local_gate.sh`.** `grep -n 'lean4\|clean-parser\|clean-elab'`
  over that script returned nothing before this change.
* **There was no exceptions ledger at all** — nothing under `tests/lean4_compat/`
  carried an owner, an issue, or an expiry.
* **Nothing routed a single corpus file through `emit_trust_ir`.** Verified: no
  file under `crates/` mentions both `lean4_compat` and `emit_trust_ir`. The
  parser suite stops at parse; the elab lane stops at elaborate-and-check.
  TrustIr is the contract this repo owes trust-cg, so the drop-in claim was
  unmeasured exactly where it is load-bearing.

## Outcomes a probe can have

`clean compile <file> --decl <name> --emit trustir`, classified by
`classify_run`:

| Outcome | Meaning | Waivable? |
|---|---|---|
| `lowers` | exit 0 and a textual TrustIr module on stdout | n/a — the good case |
| `rejected` | clean non-zero exit: parse, elab, or lowering refused | yes |
| `empty` | exit 0 but no module text — a silent success that emitted nothing | yes, review hard |
| `timeout` | no result inside `--timeout` (default 60s) | yes |
| `crashed` | terminated by a signal | **no** |

`crashed` is kept distinct from `rejected` because the two mean opposite things:
a non-zero exit is the compiler *refusing*, which is an accountable answer; a
signal is the compiler *dying*, which is never an acceptable response to valid
upstream input. The runner refuses a waiver for it and refuses to let
`corpus.toml` pin it as expected. This mirrors the standing refusal in the Rust
ledger for the `issue-94923` SIGBUS — a compiler crash needs an owner, not a row.

## Refusals that no ledger row can override

* a `crashed` outcome;
* a **stale waiver** — an active row whose probe produced its *expected*
  outcome. The Rust-side ledger's own closing note records that nothing there
  ever reports a row covering no failure, which is how 71 rows came to waive a
  defect that had been fixed thirteen days before they were written. This
  instrument reports it;
* a **missing or inferred subject** — nothing was measured, so nothing may
  pass. The subject is built from this tree (`--build`) or named
  (`--clean-bin` / `$CLEAN_BIN`); a `clean` on PATH or left in `target/` is
  never used, because it is not the tree under test;
* a **missing pinned Lean library** — every probe runs with
  `baseline.toml`'s Lean library (`~/.elan/toolchains/leanprover--lean4---<version>/lib/lean`)
  as its only import path, so `import Lean` means the same thing on every box;
  a probe whose import Clean answered with its hand-written stand-in reads
  `unsupported`;
* **pin drift** between `baseline.toml` and `tests/lean4_compat/MANIFEST.json`.

## Current state: SEEDED, and split in two legs

`corpus.toml` was seeded 2026-09-20 from a real run (56 probes). Since
2026-10-07 the instrument runs as two gate legs, split by measured cost:

| Leg | Runs | What |
|---|---|---|
| `upstream-lean-dropin` | pre-push hook, `local_gate.sh --fast` and full | `--self-test`, then `--ledger-only`: the ledgers, their expiries, the baseline pin and the ramp. Executes no probe, ~0.6 s. |
| `upstream-lean-probes` | `local_gate.sh` full mode | `--build`: builds `clean --features trust-ir-backend` from the tree (cold 35 min), then every probe under a 240 s CPU budget — 1195 s at load 33-47 (2026-10-07), six `import Lean` probes at 97-191 s each. |

The probe budget is CPU time (RLIMIT_CPU), not wall-clock time: loading the
pinned `Lean` package costs 87-91 s of CPU before a file's first declaration,
and a wall-clock budget measured that plus the box's load.

## What a maintainer must execute

```sh
# 1. read-only preflight, no compiler, runs anywhere
tests/upstream-lean/run_upstream_lean.py --self-test
tests/upstream-lean/check_ledger_expirations.py --self-test
tests/upstream-lean/run_upstream_lean.py --ledger-only

# 2. measure: build the subject from this tree and run every probe
tests/upstream-lean/run_upstream_lean.py --build
# (it builds package `clean`, not the `clean-cli` shim, whose `--emit` has no `trustir`)

# 3. to RE-SEED after a lowering change: propose rows from a REAL run, review every one
tests/upstream-lean/run_upstream_lean.py --build --seed-from-corpus-dir
```

Step 3 prints rows; it never writes them. `expected` is a claim about this
repo's behavior: the agent that commits it reviews every proposed row and
signs it with that commit.

Every probe that comes back `rejected` in step 3 is a decision, not a row:
either the lowering gap gets fixed, or it gets an `exceptions.toml` row with an
owner, an issue and an expiry. Pinning `expected = "rejected"` in `corpus.toml`
is the third option and it is the dangerous one — it records the failure as
*normal* with no owner and no expiry. Prefer `expected = "lowers"` plus a
ledger row, so the debt is visible and dated.

## Known follow-ups, stated so they are inherited knowingly

1. **The corpus is an alphabetical slice.**
   `scripts/lean4_compat/download_tests.sh` iterates GitHub's directory listing
   and breaks at `MAX=100`, so the 100 files are the alphabetical head of ~2500,
   not a sample chosen for construct coverage. Recorded in `baseline.toml`
   `[corpus]` as `selection_is_representative = false`. Repairing it means a
   stratified re-selection and a `MANIFEST.json` bump — deliberately not done
   before a gate existed to read the corpus, since re-selecting first would move
   the numbers before anything could notice.
2. **`baseline.toml`'s per-surface statuses are all `unknown`.** They are seeds.
   Populating them requires the runs above; do not hand-edit them.
3. **Two divergent `pre-push` hooks, and `core.hooksPath` is unset.**
   Measured 2026-09-01: `hooks/pre-push` and `scripts/hooks/pre-push` have
   DIFFERENT content — the first runs the sibling `trust-cg` cross-repo
   soundness meta-gate (falling back to a clean-local subset), the second
   `exec`s `scripts/local_gate.sh --fast`. `hooks/pre-push`'s own install note
   says `core.hooksPath=hooks`; `just install-hooks` sets `scripts/hooks`. And
   `git config --get core.hooksPath` is currently **unset**, so neither runs on
   push today. Out of scope here, but it decides whether this gate leg fires on
   push at all. It does run under `just gate` and `just gate-fast`: the leg sits
   after the `$FAST` branch and there is no early `exit` before it, so both
   modes reach it.
