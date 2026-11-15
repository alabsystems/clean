# EvalIR FLOAT RESIDUE (the wave W4's delta 5 named) — PENDING (recorded state, not silence)

**Wave:** the float RESIDUE of `docs/analysis/evalir-completion-plan-2026-08-24.md`
§3.3 + §5 W4's residue clause, deferred by `evalir_w4.PENDING.md` delta 5
("the residue rides the next wave"). Seven residue operators become REAL —
`fneg`/`fabs` (sign-bit ops), `fmin`/`fmax` (NaN-ignoring minNum/maxNum),
`ffloor`/`fceil`/`ftrunc` (exponent-guided exact rounding) — and every
refusal that remains (`frem`, `fsqrt`, the eight fp casts, `fdiv`-finite,
the binary32 boundary) is now a DATED, kernel-witnessed UNIVERSAL statement
in the `ir_fcmp_f32_unmodelled` idiom, never silence.
**Authored:** 2026-08-25, on the 8 GB authoring box (plan §6 environment).
**Status: AUTHORED + TYPE-CHECKED + E2-SMOKED here; the kernel half (E1) —
the residue band's registration, the 28 executed vectors, the 10 universal
refusal witnesses + the duplication pin, the three synth modules' witnesses,
and every battery agreement row — is UNKNOWN until a big machine runs it.**
Per `docs/SUITE_STATE.md`, UNKNOWN is the correct reading and is never
rounded up.

## Per-operator status (the wave's headline)

| operator | status | where |
|---|---|---|
| `fneg` | **ANSWERS** — sign-bit flip, TOTAL on genuine patterns, NaNs answer payload-preserved; junk (n ≥ 2^64) refused (`ir_f64_is_pattern`) | `ir_f64_fneg`, `eval_ir_float_res.rs` |
| `fabs` | **ANSWERS** — sign-bit clear (= `ir_f64_mag`), same totality/junk posture | `ir_f64_fabs` |
| `fmin` | **ANSWERS** on the classified fragment — one NaN operand returns the OTHER operand (minNum); refused cells: both-NaN (payload), opposite-signed zeros (host may return either) | `ir_f64_fmin_at`/`ir_f64_fmin` |
| `fmax` | **ANSWERS** — the exact mirror | `ir_f64_fmax_at`/`ir_f64_fmax` |
| `ffloor` | **ANSWERS** on every non-NaN pattern — exact exponent-guided rounding, negatives away from zero; NaN refused (libm payload) | `ir_f64_ffloor` via `ir_f64_rnd` |
| `fceil` | **ANSWERS** — positives away from zero; `fceil(-0.5) = -0.0` (sign preserved) | `ir_f64_fceil` |
| `ftrunc` | **ANSWERS** — toward zero, both signs | `ir_f64_ftrunc` |
| `frem` | **DATED REFUSAL** — universal kernel witness `ir_frem_unmodelled` (every type/operand pair); E2 answers (`lhs % rhs`); reason: the fdiv-finite guard-precision cost class | `eval_ir_float_res_witnesses.rs` |
| `fsqrt` | **DATED REFUSAL** — `ir_fsqrt_unmodelled`; E2 answers (`operand.sqrt()`); the plan's own reservation ("the hard one") | same |
| `fdiv` finite/finite | **DATED REFUSAL, now UNIVERSAL** — `ir_fdiv_fin_fin_unmodelled` at the table (every operand pair), promoting the old single-point `ir_f64_w_div_finite_finite_still_refused` | same |
| fp casts (8) | **DATED REFUSALS** — `ir_cast_fptrunc/fpext/fptoui/fptosi/uitofp/sitofp/fptosisat/fptouisat_unmodelled`, each universal over src/dst/operand; E2 answers all eight (`interpret.rs:4005-4143`) | same |
| binary32 residue ops | **DATED REFUSAL** — `ir_fneg_f32_unmodelled` / `ir_fmin_f32_unmodelled` / `ir_ffloor_f32_unmodelled` (one per dispatcher shape); the W4 f32 class carried to the residue dispatchers | same |

Ground truth throughout: trust-ir pinned rev `a4e81b6` —
`eval_float_unop` (`interpret.rs:5964-6010`, F64: `-x`/`abs`/`sqrt`/`floor`/
`ceil`/`trunc`), `eval_float_binop` (`:5919-5950`, F64: `%`/`min`/`max`).
The ir_f64 model status is INHERITED AND RESTATED, never strengthened:
checked by kernel-executed witnesses cross-checked against host `f64`
(this wave's Rust tests), explicitly NOT proved to be hardware arithmetic
(`eval_ir_float.rs` "What this does NOT claim").

## What landed

* `crates/clean-verify/src/spec/core_spec/eval_ir_float_res.rs` — NEW: the
  residue value band (junk gate, `ir_f64_fneg`/`fabs`, the 4x4 min/max
  tables with the `ir_f64_mm_zero` refused cell, the shared `ir_f64_rnd`
  rounding table over `ir_nat_divpow2`/`ir_nat_shl` — the O(bit-length)
  substrate, no new accelerated constant, no new trust) and the typed unary
  dispatcher `ir_float_unop` (+ `ir_float1`). Registered at the END of
  `add_eval_ir_float`, so every pre-existing float def keeps its
  registration position and `add_eval_ir_arith` (next stage) finds the
  names declared.
* **The one duplicated definition, pinned:** `ir_f64_ltb_pre` — the fcmp
  band's `ir_f64_ltb` spelled identically, needed BEFORE `add_eval_ir_compare`
  because `ir_binop_eval`'s fmin/fmax arms elaborate in `add_eval_ir_arith`.
  `ir_f64_ltb_pre_agrees (a b) : Eq Bool (ir_f64_ltb a b) (ir_f64_ltb_pre a b)
  := Eq.refl` — registered after both bands — makes the two definitionally
  equal at UNIVERSALLY QUANTIFIED operands or every spec build fails.
* `crates/clean-verify/src/spec/core_spec/eval_ir_float_res_witnesses.rs` —
  NEW: 28 executed vectors (7 fneg/fabs incl. the NaN-payload row and the
  junk refusal; 9 fmin/fmax incl. one-sided NaN rows and the three refused
  cells executed as refusals; 12 rounding rows incl. the exponent-carry
  `fceil 1.999... = 2.0`, the `fceil(-0.5) = -0.0` signed-zero row, and the
  NaN refusal), the duplication pin, and the 6 non-cast universal refusals.
  Registered from `add_eval_ir_ops` after `add_eval_ir_compare`. The 8
  fp-cast universal refusals register from `add_eval_ir_cast_float_refusals`
  at the END of `add_eval_ir_cast`. Rust tests cross-check every answering
  witness against host `f64` through the interpreter's own formulas.
* `crates/clean-verify/src/spec/core_spec/eval_ir_ops.rs` — `ir_unop_eval`'s
  fneg/fabs/ffloor/fceil/ftrunc arms and `ir_binop_eval`'s fmin/fmax arms
  now dispatch into the residue band (fsqrt and frem stay `ir_float_fault`);
  both docs carry the dated corrections (R6). `add_eval_ir_ops` gained the
  two witness-stage calls.
* `crates/clean-verify/src/spec/core_spec/eval_ir_wfr_synth.rs` — NEW: three
  synthetic micro-modules (`ir_frs_*` sign / `ir_frr_*` round / `ir_frm_*`
  minmax; multi-value rets), 4 whole-program witnesses + the universal
  `ir_frs_not_float` fault edge. Registered as Full-bundle stage
  `add_eval_ir_wfr_synth` (bundles.rs, after `add_eval_ir_w4_synth`; reuses
  only `add_eval_ir` names). Split into three modules BY REFUSAL BOUNDARY so
  NaN rows exist exactly where NaNs answer. Rust unit tests REGENERATE the
  block spines and every witness's ret spine from the interpreter's formulas
  on host f64.
* `crates/clean-verify/tests/fixtures/synth/synth_fsign.trust-ir.txt` /
  `synth_fround.trust-ir.txt` / `synth_fminmax.trust-ir.txt` — the authored
  E2 twins, `; synthetic:` self-declaring above the `fn` header (freshness-closure invariant
  re-run here: green, crystal_a1_lineage 134 passed). `sigs` functy indices
  **925/926/927** continue the 910-924 convention.
* `crates/clean-verify/tests/crystal_a3_semdiff/wfr_chains.rs` — **3 chains /
  28 rows**, `Synthetic`-labeled, E3 absent by construction, reusing the W2a
  table structs; **ZERO declared deltas IN THE ROWS** — every row is exact
  multi-value `Ret` agreement on `RunResult::Float` bit patterns. The wave's
  divergences are CELL-shaped and deliberately have no battery row (a tagged
  refusal and an answer share no row vocabulary — the W2b-delta-2/W4-f32
  class); each is a kernel witness + a grid delta + a row in this file.
* Instrument: `RunResult::Float(u64)` (`src/ir_semdiff/obligations.rs` —
  bit-pattern carrier, no host round-trip, so NaN payloads and signed zeros
  compare exactly), its `clean_scalar`/`wide_ret_values` encodings
  (`wide.rs`, + unit tests), and the E2 `FloatBits` return mapping
  (`tests/crystal_a3_semdiff/wide_exec.rs::map_value`).
* Gate additions in `crystal_a3_semdiff.rs`:
  `crystal_a3_semdiff_wfr_measures_encoding_agreement` (spec-building, big
  box only), `crystal_a3_wfr_e2_instrument_smoke` (E2-only, RUN here —
  below), `crystal_a3_wfr_lane_exercises_the_seven_residue_operators` (the
  per-mnemonic pin). **The `== 28` coverage assert is deliberately
  untouched**: this wave adds OPERATORS inside `unop`/`binop`, not
  constructors, and the coverage test re-ran green (28/28, `== 28` held).
* `tests/eval_ir/census.rs` — all 43 new witness names joined `WITNESSES`
  (28 vectors + pin + 6 universal refusals + 8 cast refusals), so
  `eval_ir_witnesses_are_registered_and_axiom_free` gates them on the big
  box.
* `scripts/evalir_adequacy_grid.py` + `data/evalir_adequacy_grid.json` — the
  grid EXTENDED for the new arms: **5 new declared-delta rows**
  (`frem-answers-in-e2`, `fsqrt-answers-in-e2`, `round-nan-payload`,
  `minmax-ambiguous-cells`, `fp-casts-answer-in-e2`), each anchored to live
  witness names; the residue sources joined the provenance inputs. Totals:
  **92 → 97 rows** (63 relevant / 20 proved / 3 audit-pin / **11 delta**).
  Gate `tests/eval_ir/adequacy_grid.rs` pins the eleven ids. Script `--check`
  + `--self-test` (9/9 arms) green here; the field surface is UNCHANGED (the
  dispatch arms' variables were already all read — the arm RHS text changed,
  which the dispatch echo records).
* `eval_ir_state.rs` — the fragment/exclusion table rewritten with dated
  rows (fmin/fmax and fneg/fabs and ffloor/fceil/ftrunc MODELLED since
  2026-08-25 with their per-cell refusals; frem/fsqrt/fp-casts as dated
  kernel-witnessed refusals; fdiv's finite refusal marked universal) plus
  the dated "float RESIDUE" paragraph. `eval_ir_float_ops.rs`'s `SRC_WF_FREM`
  doc carries its second dated correction (fmin/fmax no longer unmodelled).

## Plan deltas (record, not silence)

1. **fneg/fabs answer NaNs; the rounding family does not.** Not in the plan's
   sketch: IEEE 754 §5.5.1 makes negate/abs QUIET BIT operations (payload
   fully determined — `ir_exact_fneg_nan` pins the flip), while
   floor/ceil/trunc of a NaN go through the host libm, whose result payload
   is implementation-defined — the same class as arithmetic's NaN refusal.
   The battery lanes are split by exactly this boundary.
2. **fneg/fabs REFUSE junk where fcmp ANSWERS on it.** The junk posture is
   result-typed: a comparison returns a Bool (no pattern to mint), a sign op
   returns a PATTERN — flipping bit 63 of a carrier that has bit 64 set
   would mint a valid-looking pattern out of garbage. `ir_f64_is_pattern`
   (n < 2^64) is the gate; `ir_exact_fneg_junk_refused` executes it. Junk
   under min/max classifies `nan_` and is never RETURNED (the genuine
   operand is), so no gate is needed there.
3. **fmin/fmax's two refused cells are about host freedom, not cost.**
   llvm.minnum/maxnum "returns either one of the operands" when they compare
   equal — so an answer on (+0,-0) could be refuted by a conforming host —
   and a both-NaN result's payload is implementation-defined. Both cells are
   kernel-witnessed refusals and grid deltas; deterministic minNum behavior
   (one-sided NaN → other operand) ANSWERS and is battery-measured.
4. **One definition is duplicated, and the duplication is pinned.**
   `ir_f64_ltb_pre` = `ir_f64_ltb` (registration order forced it — see the
   module doc); `ir_f64_ltb_pre_agrees` is a kernel-checked definitional
   equality at free operands, so drift fails every spec build. This is the
   wave's only near-miss against the "two lanes disagree about what a NaN
   is" hazard the fcmp band's doc warns about, and it is closed by
   construction.
5. **The fp-cast refusals did not change behavior, only visibility.** The
   eight arms were already `ir_float_fault`; the wave adds the universal
   witnesses (a refusal that is silence is indistinguishable from a gap) and
   the grid delta naming E2's answering behavior. `inttoptr`/`transmute`
   (width_bounded, non-float reasons) already had witnesses and are
   untouched.

## The E2 half, MEASURED here (2026-08-25, `crystal_a3_wfr_e2_instrument_smoke`, verbatim values/steps)

```
=== WFR E2 smoke: synth_fsign ===
  1.5: both sign ops on a positive   -> [float bits 13832806255468478464, float bits 4609434218613702656] @Some(3) steps
  -1.5: both sign ops on a negative  -> [float bits 4609434218613702656, float bits 4609434218613702656] @Some(3) steps
  +0: fneg makes -0, fabs keeps +0   -> [float bits 9223372036854775808, float bits 0] @Some(3) steps
  -0: both land on +0                -> [float bits 0, float bits 0] @Some(3) steps
  +inf: sign ops on the top          -> [float bits 18442240474082181120, float bits 9218868437227405312] @Some(3) steps
  -inf: sign ops on the bottom       -> [float bits 9218868437227405312, float bits 9218868437227405312] @Some(3) steps
  NaN: bit ops answer, payload kept  -> [float bits 18444492273895866368, float bits 9221120237041090560] @Some(3) steps

=== WFR E2 smoke: synth_fround ===
  1.5: the mid-range split           -> [float bits 4607182418800017408, float bits 4611686018427387904, float bits 4607182418800017408] @Some(4) steps
  -1.5: floor/ceil exchange sides    -> [float bits 13835058055282163712, float bits 13830554455654793216, float bits 13830554455654793216] @Some(4) steps
  0.5: the small-magnitude arm       -> [float bits 0, float bits 4607182418800017408, float bits 0] @Some(4) steps
  -0.5: ceil keeps the minus sign    -> [float bits 13830554455654793216, float bits 9223372036854775808, float bits 9223372036854775808] @Some(4) steps
  2.0: an exact integer is itself    -> [float bits 4611686018427387904, float bits 4611686018427387904, float bits 4611686018427387904] @Some(4) steps
  1.9999...: ceil carries the exponent -> [float bits 4607182418800017408, float bits 4611686018427387904, float bits 4607182418800017408] @Some(4) steps
  +0: a zero is its own rounding     -> [float bits 0, float bits 0, float bits 0] @Some(4) steps
  -0: sign preserved through rounding -> [float bits 9223372036854775808, float bits 9223372036854775808, float bits 9223372036854775808] @Some(4) steps
  +inf: an infinity is its own rounding -> [float bits 9218868437227405312, float bits 9218868437227405312, float bits 9218868437227405312] @Some(4) steps
  -inf: the negative infinity too    -> [float bits 18442240474082181120, float bits 18442240474082181120, float bits 18442240474082181120] @Some(4) steps
  2^51-scale half: one fractional bit -> [float bits 4836865999795912704, float bits 4836865999795912706, float bits 4836865999795912704] @Some(4) steps

=== WFR E2 smoke: synth_fminmax ===
  1 vs 2: opposite picks             -> [float bits 4607182418800017408, float bits 4611686018427387904] @Some(3) steps
  2 vs 1: picks follow value, not slot -> [float bits 4607182418800017408, float bits 4611686018427387904] @Some(3) steps
  -2 vs -1: negative order reverses  -> [float bits 13835058055282163712, float bits 13830554455654793216] @Some(3) steps
  NaN vs 2: one NaN is ignored       -> [float bits 4611686018427387904, float bits 4611686018427387904] @Some(3) steps
  2 vs NaN: on the right too         -> [float bits 4611686018427387904, float bits 4611686018427387904] @Some(3) steps
  -inf vs 1: the bottom is the min   -> [float bits 18442240474082181120, float bits 4607182418800017408] @Some(3) steps
  1 vs +inf: the top is the max      -> [float bits 4607182418800017408, float bits 9218868437227405312] @Some(3) steps
  +0 vs +0: same-sign zeros answer   -> [float bits 0, float bits 0] @Some(3) steps
  -0 vs -0: the negative pair too    -> [float bits 9223372036854775808, float bits 9223372036854775808] @Some(3) steps
  1.5 vs 1.5: equal finites          -> [float bits 4609434218613702656, float bits 4609434218613702656] @Some(3) steps
```

Every row is the authored expectation exactly (the smoke asserts it), and
every step count matches the module shape (2 ops + ret = 3; 3 ops + ret =
4), so the declared 0 cost offsets have their measured E2 half. Expected E1
least fuels, analytic and UNMEASURED: **3 / 4 / 3** per chain (tightness:
`fuel_out` one below). The stage witnesses run at fuels `ir_d4`/`ir_d5`
(sufficient, not least). A mismatch on the first big-box run is a finding to
report, not a knob to turn.

## The inertness argument (stated and verified)

(i) The dispatch edits touch SEVEN arms of two evaluators
(`ir_unop_eval`/`ir_binop_eval`), all previously the constant
`ir_float_fault`: kernel iota-reduction selects the opcode's arm, so every
application over a different opcode reduces exactly as before, and the two
untouched arms (`fsqrt`, `frem`) still reduce to `ir_float_fault` — their
new universal witnesses are exactly that fact, executed. (ii) No registered
module, witness, or battery fixture constructed
`IRUnOp.fneg/fabs/ffloor/fceil/ftrunc` or `IRBinOp.fmin/fmax` before this
wave (grep: the sole prior occurrences were the dispatch arms and the
alphabet declaration). (iii) The new def names collide with nothing (grep:
only the new definition sites; census additions are name references). (iv)
Registration positions of all pre-existing defs are unchanged: the residue
band appends at the end of `add_eval_ir_float`, its witnesses append after
`add_eval_ir_compare`, the cast refusals append at the end of
`add_eval_ir_cast`, and the synth stage appends after `add_eval_ir_w4_synth`
in the bundle list. (v) Every prior gate RUNNABLE on this box re-ran green
after the change (list below). (vi) The kernel-side confirmation is the
big-box rerun; since the residue band registers INSIDE `add_eval_ir` (every
EvalIr-bundle spec build), the FIRST failure mode to look for is a
registration error breaking every spec-building target at once; the second
is a refuted vector or refusal witness — the kernel RAN the operation and
disagreed — which is a finding to report, never a statement to weaken. The
vacuity firewall is untouched by construction: no new inductive, no new
relation.

## Verified here (2026-08-25, plan §6 environment)

`cargo check --locked -j 2 --workspace` green; `cargo check --locked -j 2 -p
clean-verify --all-targets` green; `cargo clippy --locked -j 2 -p
clean-verify --all-targets -- -D warnings` green; `cargo fmt -p clean-verify
--check` clean. `scripts/evalir_adequacy_grid.py` write + `--check` +
`--self-test` (9/9 arms, baseline 97 rows) green;
`scripts/evalir_coverage.py --check` green (**unchanged 6/28** — the
scoreboard derives from minted artifacts only) and its `--self-test` green.
Spec-free test re-runs, all green: the crystal_a3_semdiff spec-free block
**15 passed** (all SEVEN E2 instrument smokes W1/W2a/W2b/W2c/W3/W4/WFR, all
seven lane pins, and the coverage print with the `== 28` assert HELD — this
wave adds ops, not constructors); the 3 grid gate tests (eleven delta ids
pinned); `crystal_a1_lineage` **134 passed** (operand_audit 6/6 and the
fixture freshness closure accepting the three new `synthetic:` fixtures);
lib unit tests **60 passed** (`eval_ir_float_res_witnesses` 6,
`eval_ir_wfr_synth` 3, `ir_semdiff::` 51 including the new `Float`
encodings).

## What flips this file

On a big machine (spec registration is the 8.8 GB-class cost this box cannot
pay — CLAUDE.md "Machine limits"):

```bash
# 1. Re-shard (clean-verify::lib inputs moved) and re-run the suite:
scripts/verify_runner_pinned.sh shards plan
scripts/verify_runner_pinned.sh run
# Rows expected UNKNOWN until then: clean-verify__lib (7 shards),
# clean-verify__test__eval_ir (now including the 43 WITNESSES additions and
# the eleven-delta grid gate), clean-verify__test__crystal_a3_semdiff (now
# including crystal_a3_semdiff_wfr_measures_encoding_agreement),
# clean-verify__test__vacuity_firewall, clean-verify__test__crystal_a1_lineage,
# clean-verify__test__crystal_a2_mint* — and any other clean-verify row whose
# input digest covers the crate source. NOTE: like W3/W4 this wave changed
# add_eval_ir itself (the residue band registers inside add_eval_ir_float /
# add_eval_ir_ops / add_eval_ir_cast), so the FIRST failure mode is a
# registration error breaking every spec-building target at once; the second
# is a refuted witness (report, never tune).

# 2. Run the differential with the recorded command
#    (data/crystal_gap2_semdiff_2026-08-20.json `command`):
cargo test --offline -p clean-verify --test crystal_a3_semdiff -- --nocapture --test-threads=1
# then mint data/crystal_gap2_semdiff_<date>.json from that run's output.
# The residue rows enter the artifact as OPERATOR-level evidence inside the
# already-exercised unop/binop constructors; constructor coverage was
# complete at W4 and this wave must not change the artifact's 28-denominator
# claim shape. The W1-W5 mint-session instructions in those PENDING files
# stand unchanged.

# 3. Freshness gates for this wave's artifacts:
python3 scripts/evalir_adequacy_grid.py --check
python3 scripts/evalir_adequacy_grid.py --self-test
python3 scripts/evalir_coverage.py --check
```

When step 1's `eval_ir` and `clean-verify__lib` rows are GREEN, the 28
vectors, the 10 universal refusals, the duplication pin and the synth
witnesses are kernel-confirmed at that sha; when step 2's artifact is
minted, the battery's 28 residue rows become MEASURED agreement and the
GAP2/CRYSTAL_STATUS restatements (which quote only minted numbers —
benchmark-freshness discipline) ride that session, exactly as W5's plan
delta 5 already assigns.
