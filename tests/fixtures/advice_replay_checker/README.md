# `advice_replay_checker` — a Lean-defined checker, compiled and run by Clean

**Unit:** X1 and the measuring half of X3 of
`docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`.
**Test:** `crates/clean/tests/advice_replay_checker.rs` (lanes) and
`crates/clean/tests/advice_replay_checker/elaborator.rs` (`clean check`).
**Pins and gap list:** [`data/kcheck_execution_gaps.json`](../../../data/kcheck_execution_gaps.json).

The plan's `kcheck` is a Lean definition that replays untrusted advice. This
fixture is a small real program of that shape, used to measure which Lean
constructs reach bytes through Clean today and which are refused, by name.

## What is here

* `programs/advice_replay.lean` — the checker. A de Bruijn term type with
  `Nat` literals, successor and addition; an advice type (a list of steps, each
  a path into the term and a rule); `replay`, which applies the advice one step
  at a time under a fuel bound and never searches; `check`, which accepts only
  when the replayed term is structurally the claimed normal form. `main` prints
  one verdict line for each of seventeen embedded cases. The eight cases named
  `corrupt-*` carry advice or a claim that must be refused.
* `programs/advice_replay_no_compare.lean` — the checker with its structural
  comparison removed and nothing else changed (the test re-derives it from the
  checker). It accepts three corrupted cases. It is the negative control: the
  lane must print what Lean prints for this program too.
* `programs/c*.lean` — one construct `kcheck` needs per file: recursion over
  two inductive arguments, substitution under a binder, nested and overlapping
  patterns, `Option` and `Except`, a fuel parameter, structures, `Nat` beyond
  64 and 128 bits, `deriving BEq`, mutual recursion, and so on. A construct a
  lane refuses is a row of the gap list.
* `programs/c24_r4_*.lean` to `programs/c33_r4_*.lean` — the original R4
  probes. c24, c32 and c33 are **acyclic controls**: Lean splits their
  `mutual` blocks, so they do not measure mutual structural recursion.
  They remain pinned on both backends and on `clean check`.
* `programs/c34_r4_i_call_cycle_shared_counter.lean`,
  `c35_r4_ix_walk_call_cycle.lean`, `c36_r4_x_report_call_cycle.lean` —
  the replacement probes for R4 (i), (ix), (x). Their members call one another
  in cycles on the shared Nat predecessor. Each has a successful cycle run
  and a depth refusal; the report probe retains the million-step head loop.
  [`mutual_groups.json`](mutual_groups.json) records the exact source and
  pinned Lean's constant-use sets: **every compiled member uses every member's
  `_f` auxiliary and `Nat.brecOn`**. The mint refuses an acyclic group:

  ```sh
  scripts/heavy_gate.sh run 2 x1-mutual-evidence -- python3 scripts/x1_mutual_evidence.py
  ```

  `--negative-control` runs the original acyclic c24 through the same
  predicate, requires rejection, and cannot overwrite the positive artifact.
  The gap list's `r4_items` names these as the primary probes and
  `acyclic_controls` keeps the original three in the elaborator sweep.
* `programs/c37_head_loop_10000.lean` and `c37_head_loop_100000.lean`,
  beside c27's million-step probe — sampled head-loop depths, with both
  lanes' measured outcomes in the gap list's `head_loop_samples`. The test
  reads those measurements and holds each program to c27 with only its
  step count substituted. These are sampled outcomes, not a claim about
  every intermediate depth. Reproduce the production-caller measurements with

  ```sh
  CLEAN_TRUST_CG_BIN=/path/to/trust-cg scripts/heavy_gate.sh run 4 x1-execution-evidence -- \
    python3 scripts/x1_execution_evidence.py /path/to/clean
  ```

  A full run mints `head_loop_samples` only over unchanged declared inputs
  and unchanged execution pins. `--mint-head-loop-samples` validates and
  publishes an existing complete measurement report; input drift or a moved
  outcome refuses that operation. It never updates the primary outcome pins.

* `rejected/<name>.lean` — programs pinned Lean REJECTS, with Lean's
  transcript in `rejected/expected/`. They are the negative controls of the
  frontend fix of ledger class (197) and of R4 item (vi), plus one false
  acceptance found beside class (197) (`bare_head_outside_namespace`, which
  Clean accepts today; the gap list's `false_acceptances` owns it). The
  transcripts were recorded with
  `LEAN_BACKTRACE=0 lean -Dlinter.all=false --run <name>.lean` from the
  `rejected/` directory; the mint script below refuses a rejected program, so
  it does not mint them.
* `expected/<name>.{stdout,stderr,rc}` — what pinned Lean v4.30.0-rc2 printed,
  byte for byte, and `expected/LEAN_VERSION`. Minted by

  ```sh
  scripts/native_exec_battery_expected.py --fixture tests/fixtures/advice_replay_checker
  ```

  which runs `LEAN_BACKTRACE=0 lean -Dlinter.all=false --run <program>` and
  refuses a program Lean rejects. Every program here exits 0 with an empty
  stderr under Lean. The test compares against these committed bytes and needs
  no Lean install.

## What the test asserts

On the C lane (`clean run`: Clean's elaborator, clean-compiler, emitted C, the
host C compiler) the checker's stdout is Lean's bytes, the mutant's stdout is
Lean's bytes for the mutant, and every probe is either byte-equal or refused
with the text pinned for it. Under `--features trust-ir-backend`, with
`CLEAN_TRUST_CG_BIN` naming a trust-cg, the same programs are run through
`clean run --backend trust-cg` and held to their pins.

The default-feature `crates/clean/tests/large_stack_cli.rs` runs through
`just ci` / `test-fast`. A test-only pthread interposer observes the named
`clean-run` and `clean-compile` threads and queries their actual 1 GiB stack,
while the real CLI runs and compiles the checker. `--version` creates neither
worker. The test also checks the original lowering cause at the source
closure caller. It requires the host C compiler and supports macOS/Linux;
the trust-cg consumer is not needed for these dispatch regressions.

For the R4 probes, `clean check` (the elaborator and kernel, no backend) is
held to each row's `elaborator` pin, and for every program under `rejected/`
`clean check` must refuse it by the pinned name, or accept it under a
`false_acceptances` row.

A program that exits 0 with other bytes fails whatever the pins say. One that
dies on a signal is pinned as `CRASHED` only when what it printed is a prefix
of Lean's bytes; a crash is not a refusal, and is pinned so that its gap is
listed. A refusal that stops being a refusal fails too: that is the day a gap
closed, and its row is re-pinned deliberately.

## What this does not show

The trust-cg lane stamps every body `clean-compiler-unvalidated` and links the
C runtime with the host `cc`. Byte-equal output on that lane says the lowering
ran this program correctly. It is not a codegen license and it does not make
any item of the plan's section 2.1 hold. The gap list records those rows too.

## Adding a program

Add `programs/<name>.lean` with a `main`, mint its expected bytes with the
command above, add its row to `data/kcheck_execution_gaps.json` with the
outcome each lane gives, and, for a refusal, the gap it hits.
