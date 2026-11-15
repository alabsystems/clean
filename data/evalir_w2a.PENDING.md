# EvalIR W2a (synthetic micro-modules, +5) — PENDING (recorded state, not silence)

**Wave:** W2a of `docs/analysis/evalir-completion-plan-2026-08-24.md` §5
(the first synthetic tranche: `select`, `undef`, `unreachable`,
`extractelement`, `unop` not_/ctpop).
**Authored:** 2026-08-25, on the 8 GB authoring box (plan §6 environment).
**Status: AUTHORED + TYPE-CHECKED + E2-SMOKED here; the kernel half (E1) —
the stage witnesses, the battery's value/outcome probes, and therefore every
agreement row — is UNKNOWN until a big machine runs it.** Per
`docs/SUITE_STATE.md`, UNKNOWN is the correct reading and is never rounded up.

## What landed

* `crates/clean-verify/src/spec/core_spec/eval_ir_w2a_synth.rs` — five
  hand-authored micro-modules (the `ir_lzm` idiom) + kernel witnesses incl.
  every fault edge: `ir_w2a_sel_*` (on_true/on_false universally quantified
  over the arms; nonbool → `type_error not_bool`), `ir_w2a_ud_on_run`
  (`ret [undef_]`), `ir_w2a_ur_*` (true → 3; false → `ub unreachable`;
  nonbool selector), `ir_w2a_ee_*` (at0/at1/at2 universally quantified over
  the triple; oob → `type_error bad_field`; not_agg; not_int),
  `ir_w2a_uo_*` (ctpop∘not at width 8: 0→8, 255→0, 170→4; bool operand →
  `type_error not_int`). Registered as Full-bundle stage
  `add_eval_ir_w2a_synth` (bundles.rs, after `add_eval_ir_bvar_range`;
  deliberately NOT in the minimal EvalIr bundle so the battery can register
  the re-exported module lines standalone). 31 defs, all `Eq.refl`, no new
  inductives — the vacuity firewall's family list is untouched by
  construction.
* `crates/clean-verify/src/ir_semdiff/synth.rs` — the W2a-sized subset of
  W0's outcome-vocabulary map (`OutcomeClass` Ub/TypeError vs
  `InterpretErrorCode`, partial ON PURPOSE) + the fault-capable E1 obligation
  builder `synth_outcome_obligation` (`SynthOutcome`
  Ret/RetUndef/Ub/TypeError over a closed `IrFaultName`). `EnumModel` gained
  the plan's `Synthetic` label (`src/ir_semdiff/mod.rs`); `wide.rs` gained
  `wide_bool`/`wide_agg`.
* `crates/clean-verify/tests/fixtures/synth/synth_{select,undef,unreachable,
  extractelement,unop}.trust-ir.txt` — the authored E2 twins, each
  self-declaring `SYNTHETIC MODULE` in top-level `; synthetic:` comment
  lines above the `fn` header (see finding 6(a) for why they moved).
* `crates/clean-verify/tests/crystal_a3_semdiff/synth_chains.rs` — **5 chains
  / 19 inputs**, `Synthetic`-labeled, E3 absent by construction on every
  chain; two DECLARED executor deltas (below).
* Gate additions in `crystal_a3_semdiff.rs`:
  `crystal_a3_semdiff_synth_measures_encoding_agreement` (the W2a
  differential — spec-building, big box only),
  `crystal_a3_synth_e2_instrument_smoke` (E2-only, runnable on this box, RUN
  here — below), `crystal_a3_synth_lane_exercises_the_five_w2a_constructors`
  (the +5 pin), and the coverage print extended to the three-lane union.
* `tests/crystal_a1_lineage/freshness_closure.rs` — the fixtures-directory
  closure EXTENDED, not relaxed: `tests/fixtures/synth/` is exempt from the
  live-dump requirement (no producer emits these bodies, so no dump can
  re-derive them) but every file there must carry the `synth_` prefix and
  self-declare `SYNTHETIC MODULE`, so an emitted fixture can never hide from
  the closure by moving directories. (Spec-free test re-run here: green.)

## Plan deltas (record, not silence)

1. **W0 (battery instrument) had not landed; W2a carries the minimal subset
   it needs.** The `Synthetic` chain label, the outcome-vocabulary map
   (two classes only: Clean `ub` ↔ `undefined_behavior`, Clean `type_error`
   ↔ `type_error`), and the fault-capable obligation path now exist in
   `src/ir_semdiff/{mod,synth}.rs`. W0's large-literal (pow2-ladder) path is
   still absent — nothing in W2a needs it; the float lane (W4) and
   `meta_tag_shl` still do.
2. **`undef` has no measurable E2 leg at the pinned trust-ir rev
   (`a4e81b6`).** The reference interpreter refuses to EXECUTE `Inst::Undef`
   ("executing undef would read an undefined value", `undefined_behavior`,
   `interpret.rs:619-623`) where Clean's arm binds `IRScalar.undef_` and the
   module returns it. This is not an `Unsupported*` code, so the plan's W2
   refusal rule ("E2 legs that hit an interpreter `Unsupported*` code are
   recorded `Insufficient`") does not cover it; the lane extends the
   mechanism with per-row DECLARED deltas — asserted to reproduce exactly,
   printed with the dated citation, never counted as agreement.
   **Coverage-policy consequence, flagged not decided:** under
   `scripts/evalir_coverage.py`'s derivation rule a constructor enters
   `coverage.exercised` only from rows that measured agreement — `undef`'s
   rows never can (E1-only), so how the minted artifact should count a
   kernel-witnessed, E2-refused constructor is a decision for the big-box
   mint session, recorded here rather than smuggled either way.
3. **`extractelement` out-of-bounds diverges by fault CLASS.** Clean:
   `type_error bad_field` (`ir_w2a_ee_oob`, fail-closed); trust-ir:
   `undefined_behavior` ("element 3 is out of bounds",
   `interpret.rs:4507-4516`). Declared delta row; the three in-range rows
   measure agreement normally, so the constructor still widens. The §4(c)
   adequacy grid should carry this class split when W5 writes it.
4. **`unop` runs at width 8, not 32.** `ir_nat_ctpop` walks its operand's
   unary magnitude (the O(dividend) cost law re-measured in the bvar_range
   stage comment); a width-32 complement is ~4.29e9 — the five-day class —
   where width-8 values stay ≤ 255. Same choice the committed
   `ir_exact_integer_not`/`ctpop` vectors made at width 4.
5. **Synthetic fixtures live in `tests/fixtures/synth/`, not
   `tests/fixtures/`.** The `crystal_a1_lineage` freshness closure requires
   every top-level `*.trust-ir.txt` to be compared against a live producer
   dump — definitionally impossible for authored modules. See "What landed"
   for the checked invariant that replaces silent exemption.
6. **Instrument findings against the pinned trust-ir parser (both measured
   here, both worth reporting upstream):**
   (a) inside a function header only `; #...` DIRECTIVE lines are skipped —
   a free-text `; comment` between `{` and `bb0` is a parse error
   ("expected 'bb'"); the fixtures first used `; #synthetic:` directive
   lines there. trust-ir 9fb64ff8 (WS4.2, strict parser) then refused every
   `; #word` directive outside its TEXT_DIRECTIVES table ("unknown directive
   `#synthetic` — refusing rather than dropping it", trust-ir@7b9146ba
   crates/trust-ir/src/parser.rs:300-303), so the fixtures now carry the
   declaration as plain top-level `; synthetic:` comments ABOVE the `fn`
   line, where free-text comments parse on both parsers.
   (b) the parser is byte-indexed and PANICS on a char boundary
   (`parser.rs:99`) when a directive line contains multi-byte UTF-8 (an
   em-dash did it); the fixtures are pure ASCII.
7. **Fault rows are unpriced by shape.** `execute_function` reports no step
   count on an error, so the cost pin (offset 0) gates the value-returning
   rows only; E1 fuel thresholds are still probed from below and
   tightness-gated on EVERY row, fault rows included.

## The E2 half, MEASURED here (2026-08-25, `crystal_a3_synth_e2_instrument_smoke`, verbatim values/steps)

```
synth_select          6/6 rows answer: 3,9,0,1,4294967295,4294967295 — all @2 steps
synth_undef           fault undefined_behavior (declared delta 2 reproduces exactly)
synth_unreachable     true -> int 3 @3 steps; false -> fault undefined_behavior (UB class)
synth_extractelement  5 @2, 11 @2, 2 @2; index 3 -> fault undefined_behavior (declared delta 3)
synth_unop            8,0,4,7,7,4 — all @3 steps (= 8 - popcount(x) throughout)
```

Every step count equals the analytic per-path instruction count (select+ret=2;
condbr+const+ret=3; extractelement+ret=2; not+ctpop+ret=3), so the declared 0
cost offsets have their measured E2 half. Expected E1 least fuels, analytic
and UNMEASURED: select rows 2; undef 2; unreachable 3 (true) / 2 (false);
extractelement 2 (ret rows) / 1 (OOB); unop 3. A mismatch on the first big-box
run is a finding to report, not a knob to turn.

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
# input digest covers the crate source. NOTE: the new stage registers inside
# Specification::new(), so the FIRST failure mode to look for is a
# registration error in add_eval_ir_w2a_synth breaking every Full-spec
# target at once; the witnesses themselves are kernel-run at registration.

# 2. Run the W2a differential and the W1/narrow gates with the recorded command
#    (data/crystal_gap2_semdiff_2026-08-20.json `command` field):
cargo test --offline -p clean-verify --test crystal_a3_semdiff -- --nocapture --test-threads=1
# then mint data/crystal_gap2_semdiff_<date>.json from that run's output.
# A constructor enters the new artifact's `coverage.exercised` ONLY from rows
# that measured agreement — never from authored rows; decide delta 2's
# `undef` policy explicitly in that session.

# 3. Re-derive the coverage scoreboard from the committed artifacts:
python3 scripts/evalir_coverage.py            # writes data/evalir_coverage.json
python3 scripts/evalir_coverage.py --check
```

`data/evalir_coverage.json` stays **6/28** until step 3 runs over a minted
artifact recording the new rows (checked here: `--check` green, unchanged).
The battery's EXERCISED print, measured here, is 6/28 narrow, 15/28
narrow+W1, **20/28 narrow+W1+W2a**
(`crystal_a3_coverage_is_reported_over_the_full_irinst_surface`, run on this
box 2026-08-25). Exercised is not measured; the fraction that counts is the
artifact's.
