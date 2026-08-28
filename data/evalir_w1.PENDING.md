# EvalIR W1 (fixture widening, +9) — PENDING (recorded state, not silence)

**Wave:** W1 of `docs/analysis/evalir-completion-plan-2026-08-24.md` §5.
**Authored:** 2026-08-24, on the 8 GB authoring box (plan §6 environment).
**Status: AUTHORED + TYPE-CHECKED + E2-SMOKED here; the kernel half (E1) and
therefore every agreement row is UNKNOWN until a big machine runs it.** Per
`docs/SUITE_STATE.md`, UNKNOWN is the correct reading and is never rounded up.

## What landed

* `crates/clean-verify/src/ir_semdiff/wide.rs` — wide obligation builders
  (arbitrary `ir_eval` argument/heap/next-addr tails; values as `ir_d<N>`
  names ≤ 16 and raw decimal literals above, the committed concrete-witness
  encoding). `RunResult::Int`/`EnumTag` widened to `u64`; `RunResult::Unit`
  added for the void-returning `strict_monads`.
* `crates/clean-verify/tests/crystal_a3_semdiff/wide_chains.rs` — **10 chains /
  57 inputs** over already-committed emitted fixtures, covering the plan's
  nine W1 constructors: `icmp`, `binop` (and/or/lshr), `cast` (trunc/zext),
  `condbr`, `call` (two-fixture module, callee at `@func.3657`), `store`,
  `gep`, `insertfield`, `assert`. Subjects: `bvar_in_range`, `is_valid_char`,
  `flat_flags_contains`, `flat_flags_with`, `node_id_index`,
  `get_char_val_trunc`, `has_loose_bvars`, `loose_bvar_range`,
  `strict_monads`, `simp_priority_value`.
* `crates/clean-verify/tests/crystal_a3_semdiff/wide_exec.rs` — E2 generalized:
  multi-fixture modules with post-parse callee-id reassignment, direct
  `InterpretValue` arguments (no harness ⇒ no subtracted overhead), and two
  per-input TEXT harnesses for the pointer-receiving subjects.
* Gate additions in `crates/clean-verify/tests/crystal_a3_semdiff.rs`:
  `crystal_a3_semdiff_wide_measures_encoding_agreement` (the W1 differential),
  `crystal_a3_wide_e2_instrument_smoke` (E2-only, runnable on this box),
  `crystal_a3_wide_lane_exercises_the_nine_w1_constructors` (the +9 pin),
  and the combined coverage print in
  `crystal_a3_coverage_is_reported_over_the_full_irinst_surface`.
* Module-defs re-exports (`ir_br/vc/fc/fw/hlb/sm/pv/gc/ni_module_defs`, plus
  `ir_sm_semdiff_defs`) from `clean_verify::spec` — the battery reads the
  registered stage lines, never a copy.

## Plan deltas (record, not silence)

1. **`meta_tag_shl` is deferred to W0's large-literal path.** Its value is
   `1u64 << 63` and the registered stage leaves that term deliberately
   unreduced (`eval_ir_meta_tag.rs`, `env_push_low_local_meta_tag` rationale:
   normalizing costs 2^63 `Nat.rec` unfoldings). A battery row would either
   hang the kernel on a digit-literal RHS or record a term-level `Eq.refl` as
   a digit comparison the kernel never made. All nine W1 constructors are
   still covered by the other subjects, so the wave's +9 stands without it.
2. **`cast` sub-operators `sext`/`bitcast` ride with delta 1** (they appear
   only in `meta_tag_shl`); the `cast` constructor itself is measured via
   `trunc`/`zext`.
3. **The E2 half of every chain was MEASURED on this box** (the
   `crystal_a3_wide_e2_instrument_smoke` test is spec-free and runs here):
   all 57 rows answer, values match the subjects' known semantics, and the
   per-row step counts equal the analytically expected per-path instruction
   counts — including the two lanes originally drafted as may-refuse
   (`strict_monads`'s 82-field surrogate struct round-trips; the
   `simp_priority_value` byte-gep payload reads execute), so those refusal
   allowances were REMOVED and every chain is held to the full green
   standard. One measured correction along the way: the `Default` input's
   harness must initialize the enum's payload lane — the subject's whole-enum
   `load` reads all 8 bytes and an uninitialized lane is poison whose
   projection faults `undefined_behavior` (recorded in the harness comment).
   The E1 (kernel) half remains the UNKNOWN this file records.
4. **Cost offsets are declared 0 on all ten chains** without a kernel-side
   measurement (none is possible here). The `call` chain
   (`has_loose_bvars`) is the likeliest RED on the first big-box run if the
   two step counters treat frame push/return differently; a mismatch there is
   a finding, not a tuning knob.

## What flips this file

On a big machine (spec registration is the 8.8 GB-class cost this box cannot
pay — CLAUDE.md "Machine limits"):

```bash
# 1. Re-shard (clean-verify::lib inputs moved) and re-run the suite:
scripts/verify_runner_pinned.sh shards plan
scripts/verify_runner_pinned.sh run
# Rows expected UNKNOWN until then: clean-verify__lib (7 shards),
# clean-verify__test__eval_ir, clean-verify__test__crystal_a3_semdiff,
# clean-verify__test__vacuity_firewall, clean-verify__test__crystal_a1_lineage,
# clean-verify__test__crystal_a2_mint* (all GREEN at 3a2aaaa2e before this wave).

# 2. Mint the new dated semdiff artifact with the gate's recorded command
#    (data/crystal_gap2_semdiff_2026-08-20.json `command` field):
cargo test --offline -p clean-verify --test crystal_a3_semdiff -- --nocapture --test-threads=1
# then record data/crystal_gap2_semdiff_<date>.json from that run's output.
# A constructor enters the new artifact's `coverage.exercised` ONLY from rows
# that measured agreement — never from authored rows.

# 3. Re-derive the coverage scoreboard from the committed artifacts:
python3 scripts/evalir_coverage.py            # writes data/evalir_coverage.json
python3 scripts/evalir_coverage.py --check
```

`data/evalir_coverage.json` stays **6/28** until step 3 runs over a minted
artifact that records the new rows — authored battery rows never count
(the script's own derivation rule, and the plan §5 ledger: the coverage
fraction is quoted from the artifact only).
