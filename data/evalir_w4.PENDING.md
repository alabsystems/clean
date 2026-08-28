# EvalIR W4 (float-comparison domain, +1 — the LAST constructor) — PENDING (recorded state, not silence)

**Wave:** W4 of `docs/analysis/evalir-completion-plan-2026-08-24.md` §5 — the
second and final VALUE-DOMAIN wave: the `fcmp` arm's 12/12 `ir_float_fault`
verdicts (`eval_ir_ops.rs`, "12 named places to land") are now 12 real
predicates over the classified binary64 substrate, and **ZERO `ir_exec`
dispatch arms remain tagged unmodelled** (2 → 1 by W3, 1 → 0 here, both
counted down in the dispatch census comment). With the W4 battery lane, every
one of the 28 `IRInst` constructors has battery rows — the exercised print
reaches **28/28**, this wave's exit.
**Authored:** 2026-08-25, on the 8 GB authoring box (plan §6 environment).
**Status: AUTHORED + TYPE-CHECKED + E2-SMOKED here; the kernel half (E1) —
the new comparison defs' registration, the 16 exact vectors, the 3 quantified
boundary witnesses, the stage witnesses, the battery's value probes, and
therefore every agreement row — is UNKNOWN until a big machine runs it.** Per
`docs/SUITE_STATE.md`, UNKNOWN is the correct reading and is never rounded up.

## The design, with its trust-ir ground truth (pinned rev `a4e81b6`)

* **Arm-for-arm the pinned interpreter's `eval_fcmp_f64`**
  (`interpret.rs:6056-6072`): `unordered = lhs.is_nan() || rhs.is_nan()`;
  ordered predicates are `!unordered && cmp`, unordered `unordered || cmp`;
  `gt`/`ge` are `lt`/`le` with operands exchanged, `ne` negates `eq` (both
  exact on non-NaN reals; on a NaN pair the unordered term alone decides).
  Clean side: `ir_fcmp_bool` (`eval_ir_fcmp.rs`), one arm per `IRFCmpOp`.
* **The plan's route exactly: folded comparisons over the bits substrate,
  no new float axioms.** NaN detection is THE classification (`ir_f64_is_nan`
  is an `IRF64Class.rec` over `ir_f64_class`); the non-NaN order is the
  sign-magnitude order the format sorts by (`ir_f64_ltb`: magnitude order,
  reversed on the negative side, with the signed-zero conjunct; `ir_f64_eqb`:
  bit equality OR both magnitudes zero — the format's one many-to-one value).
  Deciders are `ir_nat_ltb`/`ir_nat_eqb` (native BigNat subtraction + one
  iota, walk-equivalence theorems standing) over `ir_f64_mag`'s single exact
  `Nat.sub` — the measured milliseconds class (`CRYSTAL_STATUS.md`
  §folding lane). No new accelerated constant, no new inductive, no new
  relation: `EVAL_IR_FAMILIES` and the vacuity firewall untouched by
  construction.
* **Comparison is TOTAL where arithmetic is not.** Arithmetic refuses NaN
  operands because the result NaN's PAYLOAD is implementation-defined; a
  comparison returns a Bool — no payload exists — so IEEE 754 §5.11 fixes
  every predicate on ANY classified operands. Exactly the plan's W4
  observation; it is why this lane has ZERO declared deltas and no fault
  rows outside the type-error edges.
* **The type/width gate mirrors `ir_float_binop`** (`ir_float_cmp`):
  non-float type → `type_error not_float`; `float_ w`, `w ≠ 64` → tagged
  `unmodelled float_domain`; at 64 the operands coerce through `ir_float2`
  and the predicate decides. Model status inherited from the ir_f64 lanes and
  RESTATED, never strengthened: checked by executed witnesses (and by host-f64
  cross-check tests in the Rust files), explicitly NOT proved to be hardware
  arithmetic (`eval_ir_float.rs` "What this does NOT claim").

## What landed

* `crates/clean-verify/src/spec/core_spec/eval_ir_fcmp.rs` — NEW: the
  comparison band (`ir_f64_is_nan`, `ir_f64_unordered`, `ir_f64_eqb`,
  `ir_f64_ltb`, `ir_f64_leb`, `ir_fcmp_bool`, `ir_float_cmp`, the new
  4-argument `ir_fcmp_eval`), **16 exact vectors** (`ir_exact_fcmp_*`: the
  NaN quadrants for eq/lt in both families, the signed zeros both ways, the
  reversed negative ordering, the operand-exchange predicates, the
  infinities, and the junk-classifies-NaN pair) and **3 universally
  quantified boundary witnesses** (`ir_fcmp_int_ty_faults` over every op/
  width/operand pair; `ir_fcmp_f32_unmodelled` over every op/operand pair;
  `ir_fcmp_not_float_operand` over every op/payload/second operand).
  Registered from `add_eval_ir_compare` (`eval_ir_ops.rs`) at the exact point
  the old 12-fault `ir_fcmp_eval` stood, so registration order for every
  pre-existing def is unchanged. A Rust unit test cross-checks every
  answering witness against host `f64` through the interpreter's formula.
* `crates/clean-verify/src/spec/core_spec/eval_ir_machine.rs` — the fcmp
  dispatch arm now passes `t` (`ir_fcmp_eval op t …`; it was dropped
  pre-W4), and the 28-arm census comment rewritten "exactly one → ZERO
  arms unmodelled" with the count-down history inline (R6).
* `crates/clean-verify/src/spec/core_spec/eval_ir_w4_synth.rs` — one
  synthetic micro-module (`ir_w4_fc_module`): ALL TWELVE predicates on the
  same two f64 parameters in declaration order, twelve-value ret; 4 module
  defs (incl. the `ir_w4_fcn` node builder) + 4 kernel witnesses (ordered
  ascending; the NaN split row; the signed zeros; the quantified
  `ir_w4_fc_not_float` fault edge). Registered as Full-bundle stage
  `add_eval_ir_w4_synth` (bundles.rs, after `add_eval_ir_w3_synth`; reuses
  only `add_eval_ir` names). All `Eq.refl`. Rust unit tests REGENERATE the
  block spine and every witness's 12-bool ret spine from the interpreter's
  formula on host f64 and assert the consts match — one transcription slip
  (two missing closing parens) was caught exactly there, on this box.
* `crates/clean-verify/tests/fixtures/synth/synth_fcmp.trust-ir.txt` — the
  authored E2 twin, `; #synthetic:` self-declaring (freshness-closure
  invariant re-run here: green, 17 passed). `sigs` functy index **924**
  continues the 910-923 convention.
* `crates/clean-verify/tests/crystal_a3_semdiff/w4_chains.rs` — **1 chain /
  9 rows**, `Synthetic`-labeled, E3 absent by construction, reusing the W2a
  table structs; **ZERO declared deltas** — every row is exact twelve-value
  `Ret` agreement (`RunResult::Many`, the W3 vocabulary). Rows cover the four
  NaN quadrants through ALL 12 predicates (plan minimum was eq/lt), plus
  three finite orderings, the signed-zero pair, an infinity row and the
  reversed negative ordering.
* Instrument: `wide_float` (`src/ir_semdiff/wide.rs`, + unit test) — float
  bit patterns ride the raw-literal half of `ir_nat_term` per the plan's
  large-literal rule (literals are not names; the kernel folds them natively
  — the `ir_f64_sign_bit` precedent; nothing here needed the pow2-ladder
  path or the `meta_tag_shl` unreduced-term treatment because no registered
  term is left unreduced).
* Gate additions in `crystal_a3_semdiff.rs`:
  `crystal_a3_semdiff_w4_measures_encoding_agreement` (spec-building, big box
  only), `crystal_a3_w4_e2_instrument_smoke` (E2-only, RUN here — below),
  `crystal_a3_w4_lane_exercises_the_fcmp_constructor` (the final +1 pin,
  which also pins all 12 mnemonics in the fixture), and
  `crystal_a3_coverage_is_reported_over_the_full_irinst_surface` REWRITTEN
  per its own instruction: the `< 28` assert (whose message required exactly
  this rewrite on reaching 28) is now `== 28`, so a fixture edit that
  silently drops a form fails the gate.
* `tests/eval_ir/census.rs` — the 16 `ir_exact_fcmp_*` + 3 `ir_fcmp_*`
  boundary names joined `WITNESSES`, so
  `eval_ir_witnesses_are_registered_and_axiom_free` gates them on the big
  box.
* Dated doc corrections (R6, superseded readings inline): the `IRFCmpOp`
  doc's "no artifact to be about" refusal (retired by B3-SELECT + this
  wave), the `eval_ir_state.rs` exclusion table (FCmp row → modelled; ALSO
  the Overflow row, which W3 left reading "unmodelled" — corrected here with
  W3's date), the registered `SRC_WF_FREM` doc ("and every IRFCmpOp" clause
  dated and closed), the W3 stage/bundles notes that said fcmp "remains
  tagged".

## Plan deltas (record, not silence)

1. **`fcmp.t` is DISPATCHED, not inert — a W5 grid row dies.** The §4(c)
   sketch listed `fcmp.t` among the retained-inert operands wanting an
   irrelevance theorem. The real semantics consults `t` (the width gate,
   exactly like `binop.t`'s float arms), so the pre-W4 dispatch's dropping
   of `t` was itself the gap; the arm now passes it and no irrelevance
   theorem is possible or wanted. Recorded here so W5 derives its grid from
   the post-W4 dispatch.
2. **The f32 fragment boundary is a measured executor asymmetry, tagged
   fail-closed, with no battery row by design.** The pinned interpreter
   ANSWERS binary32 compares (`eval_fcmp_f32`, `interpret.rs:6038-6054`);
   Clean's domain decides only binary64 and tags `float_ w ≠ 64`
   `unmodelled float_domain` — kernel-witnessed universally
   (`ir_fcmp_f32_unmodelled`). A tagged refusal and an answer share no row
   vocabulary (the same class as W2b delta 2), so the boundary lives in the
   stage docs and here, not in a silent gap. It can never become a wrong
   answer.
3. **Junk bit patterns ANSWER under comparisons.** Any `n ≥ 2^64`
   classifies `nan_` (the classification's junk posture), and unlike the
   arithmetic lane — where every junk operation is `unmodelled` — a
   comparison on it returns the NaN answer (ordered false / unordered true):
   `ir_exact_fcmp_junk_oeq`/`_junk_ueq` pin it. No E2 leg exists for junk BY
   CONSTRUCTION: trust-ir's `FloatBits(u64)` cannot carry 2^64, so the junk
   fragment is a Clean-only inhabitant, kernel-witnessed and stated rather
   than battery-measured.
4. **Battery expectations are computed from the pinned interpreter's own
   formula, not hand-copied.** `w4_chains.rs::fcmp12` restates
   `eval_fcmp_f64` on host `f64` (108 Bools across 9 rows); the E2 smoke
   asserts the interpreter really computes it, and the E1 probes measure the
   kernel against it. The three STAGE witnesses' spines are hand-written
   consts, but a Rust test regenerates them from the same formula, so the
   authored/generated split cannot drift.
5. **The plan's W4 float RESIDUE rides the next wave, per the plan's own
   overrun clause.** §5 W4 also names `fneg`/`fabs` (cheap sign-bit wins),
   `fmin`/`fmax`, `ffloor`/`fceil`/`ftrunc`, and dated refusals for
   `frem`/`fsqrt`/the fp casts/`fdiv`-finite. This wave lands fcmp — "fcmp
   alone completes the constructor count and the residue rides the next
   wave" — and the §3.3 residue list in `eval_ir_state.rs` remains accurate
   as written. The `unop`/`binop` float arms stay tagged exactly as before.

## The E2 half, MEASURED here (2026-08-25, `crystal_a3_w4_e2_instrument_smoke`, verbatim values/steps)

```
=== W4 E2 smoke: synth_fcmp ===
  1 vs 2: ordered ascending          -> [bool false, bool true, bool true, bool true, bool false, bool false, bool false, bool true, bool true, bool true, bool false, bool false] @Some(13) steps
  2 vs 1: ordered descending         -> [bool false, bool true, bool false, bool false, bool true, bool true, bool false, bool true, bool false, bool false, bool true, bool true] @Some(13) steps
  1 vs 1: equal finites              -> [bool true, bool false, bool false, bool true, bool false, bool true, bool true, bool false, bool false, bool true, bool false, bool true] @Some(13) steps
  NaN vs 1: left NaN splits the families -> [bool false x6, bool true x6] @Some(13) steps
  1 vs NaN: right NaN splits them too -> [bool false x6, bool true x6] @Some(13) steps
  NaN vs NaN: identical patterns, still unordered -> [bool false x6, bool true x6] @Some(13) steps
  +0 vs -0: different bits, equal value -> [bool true, bool false, bool false, bool true, bool false, bool true, bool true, bool false, bool false, bool true, bool false, bool true] @Some(13) steps
  -1 vs +inf: negative below the top -> [bool false, bool true, bool true, bool true, bool false, bool false, bool false, bool true, bool true, bool true, bool false, bool false] @Some(13) steps
  -2 vs -1: negative ordering reverses -> [bool false, bool true, bool true, bool true, bool false, bool false, bool false, bool true, bool true, bool true, bool false, bool false] @Some(13) steps
```

(The three NaN rows print all twelve Bools in full in the live output; the
x6 contraction here is this file's, the values are verbatim.) Every row is
the authored expectation exactly — 108 Bools, the ordered/unordered split on
all three NaN quadrants, the zeros equal, both orderings, the negative-side
reversal — and every step count is 13 (12 compares + ret), so the declared 0
cost offsets have their measured E2 half. Expected E1 least fuels, analytic
and UNMEASURED: **13 on every row** (tightness: `fuel_out` at 12). The stage
witnesses run at fuel `ir_d14` (sufficient, not least). A mismatch on the
first big-box run is a finding to report, not a knob to turn.

## The inertness argument (the arm computed nothing before, stated and verified)

(i) The dispatch change edits ONE arm's body (and only that arm consumes the
new defs): kernel iota-reduction selects the scrutinee constructor's arm, so
every application over a different constructor reduces exactly as before —
the three `ir_exec_*_irrelevant` theorems included (scrutinees
`switch`/`callindirect`). (ii) No registered module, witness, or battery
fixture constructed `IRInst.fcmp` before this wave — verified by grep: the
sole source occurrence was the dispatch arm itself (the mint's
`ir_mint/shape.rs` row is a parser shape, not a constructed term). The old
`ir_fcmp_eval` had exactly one call site (that arm), so its signature change
(3 → 4 args, gaining `t`) ripples nowhere else. (iii) The new def names
(`ir_f64_is_nan/unordered/eqb/ltb/leb`, `ir_fcmp_bool`, `ir_float_cmp`,
`ir_exact_fcmp_*`, `ir_fcmp_*`, `ir_w4_*`) collide with nothing — grep over
the spec sources shows only the new definition sites. (iv) Every prior gate
RUNNABLE on this box re-ran green after the change: all six E2 instrument
smokes (W1/W2a/W2b/W2c/W3/W4), all six lane pins, the coverage print (now
28/28 exercised), `crystal_a1_lineage` freshness (17 passed), and 57
`ir_semdiff::`/`eval_ir_fcmp`/`eval_ir_w4_synth` lib unit tests. (v) The
kernel-side confirmation of (i)-(ii) is the big-box rerun below — until then
every E1-touching row is UNKNOWN, and since the new comparison defs register
INSIDE `add_eval_ir` (every EvalIr-bundle spec build, via
`add_eval_ir_compare`), the FIRST failure mode to look for is a registration
error breaking every spec-building target at once; the second is a refuted
`ir_exact_fcmp_*` / `ir_w4_*` witness (the kernel RAN the comparison and
disagreed — report, never tune).

## Verified here (2026-08-25, plan §6 environment)

`cargo check --locked -j 2 --workspace` green; `cargo check --locked -j 2 -p
clean-verify --tests` green; `cargo clippy --locked -j 2 -p clean-verify
--all-targets -- -D warnings` green; `cargo fmt -p clean-verify --check`
clean; `scripts/evalir_coverage.py --check` green (unchanged 6/28 — the
scoreboard derives from minted artifacts only).

## The exercised ladder after this wave (battery print, run here)

`crystal_a3_coverage_is_reported_over_the_full_irinst_surface`: 6/28 narrow,
15/28 narrow+W1, 20/28 +W2a, 24/28 +W2b, 26/28 +W2c, 27/28 +W3, **28/28
+W4 — the full constructed-Inst surface is EXERCISED**, and the gate now
pins the 28 (== instead of <, per its own rewrite instruction). Exercised is
not measured; the fraction that counts is the artifact's, and
`data/evalir_coverage.json` stays 6/28 until a big-box mint records the new
rows.

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
# clean-verify__test__crystal_a2_mint* — and any other clean-verify row whose
# input digest covers the crate source. NOTE: like W3 this wave changed
# add_eval_ir itself (the comparison band registers inside
# add_eval_ir_compare), so the FIRST failure mode is a registration error
# breaking every spec-building target at once; the second is a refuted
# witness (report, never tune).

# 2. Run the W4 differential and the narrow/W1/W2a/W2b/W2c/W3 gates with the
#    recorded command (data/crystal_gap2_semdiff_2026-08-20.json `command`):
cargo test --offline -p clean-verify --test crystal_a3_semdiff -- --nocapture --test-threads=1
# then mint data/crystal_gap2_semdiff_<date>.json from that run's output.
# A constructor enters the new artifact's `coverage.exercised` ONLY from rows
# that measured agreement — never from authored rows. W2a's recorded `undef`
# coverage-policy question (evalir_w2a.PENDING.md delta 2) still belongs to
# that mint session; fcmp has nine agreement rows and no delta, so it enters
# normally — and if all rows measure, the artifact's fraction becomes the
# B-SEM exit's 28-with-labels headline (plan §4).

# 3. Re-derive the coverage scoreboard from the committed artifacts:
python3 scripts/evalir_coverage.py            # writes data/evalir_coverage.json
python3 scripts/evalir_coverage.py --check
```

`data/evalir_coverage.json` stays **6/28** until step 3 runs over a minted
artifact recording the new rows (checked here: `--check` green, unchanged).
