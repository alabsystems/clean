# EvalIR W3 (overflow value domain, +1) — PENDING (recorded state, not silence)

**Wave:** W3 of `docs/analysis/evalir-completion-plan-2026-08-24.md` §5 — the
first VALUE-DOMAIN wave: the `overflow` dispatch arm
(`eval_ir_machine.rs`, previously `IRConfig.halted (unmodelled
width_bounded)`) now has real two-result semantics, and only `fcmp` (plan W4)
remains tagged.
**Authored:** 2026-08-25, on the 8 GB authoring box (plan §6 environment).
**Status: AUTHORED + TYPE-CHECKED + E2-SMOKED here; the kernel half (E1) —
the new value-domain defs' registration, the 17 exact vectors, the stage
witnesses, the battery's value probes, and therefore every agreement row — is
UNKNOWN until a big machine runs it.** Per `docs/SUITE_STATE.md`, UNKNOWN is
the correct reading and is never rounded up.

## The design, with its trust-ir ground truth (pinned rev `a4e81b6`)

* **Two results, bound positionally.** `Inst::Overflow` binds
  `[result, InterpretValue::bool(overflow)]` to the node's two declared
  result ids (`interpret.rs:637-644`). Clean side: `ir_frame_bind2` /
  `ir_bind2` (`eval_ir_machine.rs`) — the node's `rs` multi-bound through the
  existing `ir_bind_params` (the `ir_ret_to` precedent), plus the advance an
  instruction needs and a return does not.
* **The plan's recommended design α landed WITHOUT the new inductive it
  sketched.** Plan W3 phrased α as "a paired-value `IRStepResult2`"; the
  landed form keeps α's substance (two results, positional multi-bind, the
  producer's node shape) but makes the evaluator CONFIG-level — the
  `ir_store_exec`/`ir_alloca_exec` pattern (`ir_overflow_exec` →
  `ir_overflow_vals` → `ir_overflow_ints` → `ir_bind2`) — so `IRStepResult`
  is unchanged, **no new inductive and no new relation exists**,
  `EVAL_IR_FAMILIES` is untouched, and the vacuity firewall carries no new
  big-box obligation beyond its standing run inside the `eval_ir` target.
  (Recorded as a plan delta; the brief's "prefer encodings that need none"
  is why.)
* **The value is the wrapping binop.** `eval_int_overflow` delegates to
  `eval_int_binop` Add/Sub/Mul and masks (`interpret.rs:5850-5879`);
  `ir_overflow_value` (`eval_ir_ops.rs`) is arm-for-arm the same
  `ir_wrap`/`ir_sub_wrap`/`ir_nat_mul` helpers `ir_binop_eval` uses.
* **The flag dispatches on the TYPE's signedness** (`InterpretInt.signed`,
  `interpret.rs:5872-5876`): `IRTy.int_` → `ir_overflow_flag_s`,
  `IRTy.uint_` → `ir_overflow_flag_u`, every other type (bool_ included —
  `expect_int_value` rejects Bool, `:5429-5434`) fails closed
  `type_error not_int`.
  - Unsigned (`unsigned_overflow`, `:6132-6145`): sum/product past the mask,
    borrow = strict lhs<rhs — phrased as exact ℕ comparisons
    (`ir_nat_leb (pow2 w) …`); the interpreter's extra u128-overflow guards
    are bounded-host artifacts, over ℕ the comparison IS the condition.
  - Signed (`signed_overflow`, `:6147-6157`: checked arithmetic escaping
    [-2^(w-1), 2^(w-1)-1]): add/sub use the classical two's-complement sign
    rules (equal to the bounds check at every width, add: same signs in,
    different sign out; sub: different signs in, result leaves the minuend's);
    mul compares the exact magnitude product against 2^(w-1)-1 / 2^(w-1)
    depending on the result's sign side. Kernel-side the equivalence is
    pinned by the width-4 exact vectors, battery-side by the i8 rows against
    the interpreter's own checked arithmetic.
* **Operands are wrapped to canonical residues once at entry**
  (`ir_overflow_ints`, the `ir_uint2`/`ir_int2_width_result` discipline) so a
  junk over-wide `int_` cannot leak a wrong flag; identity on every reachable
  value (InterpretInt.raw is always masked).
* **Junk-node arity split, recorded not smoothed:** a node declaring fewer
  than two results binds the prefix on the Clean side (`ir_bind_params`'s
  standing posture: arity is producer-side well-formedness) where the
  interpreter's `bind_results` faults `malformed_instruction`
  (`interpret.rs:5339-5361`). Producer nodes always declare both; recorded in
  `ir_frame_bind2`'s registered doc.

## What landed

* `crates/clean-verify/src/spec/core_spec/eval_ir_ops.rs` —
  `ir_overflow_value`, `ir_overflow_flag_u`, `ir_overflow_flag_s`,
  `ir_overflow_flag` + **17 width-4 exact vectors** (`ir_exact_ovf_*`:
  wrap/borrow/boundary on the unsigned side; the signed MIN edges
  -8-1, -8+(-1), -8×-1 with their values, and the one-inside boundaries
  -8+1, -8×1, -8-(-1)), each doc citing its interpreter function.
  `ir_width_fault`'s doc updated with the dated note (it previously named
  "Overflow's paired result"; true when written).
* `crates/clean-verify/src/spec/core_spec/eval_ir_machine.rs` —
  `ir_frame_bind2` + `ir_bind2` (transitions), new stage fn
  `add_eval_ir_overflow` (`ir_overflow_ints`/`ir_overflow_vals`/
  `ir_overflow_exec`) registered between control and dispatch, the dispatch
  arm swapped to `ir_overflow_exec s rs op t (ir_getd s a) (ir_getd s b)`,
  and the 28-arm census comment rewritten "exactly two → exactly ONE
  (fcmp)" with the dated correction inline.
* `crates/clean-verify/src/spec/core_spec/eval_ir_w3_synth.rs` — two
  synthetic micro-modules (`ir_w3_ou_module` u8 / `ir_w3_os_module` i8),
  each running ALL THREE OverflowOps on the same operands and returning all
  six bound results through the multi-value ret; 14 defs, 8 kernel witnesses
  incl. three fault edges (`ir_w3_ou_not_int` quantified over (b, y);
  `ir_w3_os_not_int` second-operand side quantified over (x, b);
  `ir_w3_ovf_bad_ty` quantified over EVERY machine/ids/operands at
  `IRTy.ptr_`). Registered as Full-bundle stage `add_eval_ir_w3_synth`
  (bundles.rs, after `add_eval_ir_w2c_synth`; reuses only `add_eval_ir`
  names). All `Eq.refl`, no new inductives.
* `crates/clean-verify/tests/fixtures/synth/synth_overflow_{u8,i8}.trust-ir.txt`
  — the authored E2 twins, `; synthetic:` self-declaring above the `fn` header (freshness-closure
  invariant re-run here: green, 17 passed).
* `crates/clean-verify/tests/crystal_a3_semdiff/w3_chains.rs` — **2 chains /
  8 rows**, `Synthetic`-labeled, E3 absent by construction, reusing the W2a
  table structs; **ZERO declared deltas** — every row is exact multi-value
  `Ret` agreement. Sigs functy 922/923 continue the 910-921 convention.
* Instrument: `RunResult::Many(Vec<RunResult>)`
  (`src/ir_semdiff/obligations.rs`) with the ret-payload cons-spine encoding
  (`src/ir_semdiff/wide.rs::wide_ret_values`, + 2 unit tests) and the E2
  multi-return mapping (`tests/crystal_a3_semdiff/wide_exec.rs::map_returns`,
  element faults propagate to a whole-list fault, never element-wise
  comparison). **This is the battery's first vocabulary for multi-value
  returns, so the W3 rows also put `ir_ret_to`'s positional multi-value
  return under differential measurement for the first time.**
* Gate additions in `crystal_a3_semdiff.rs`:
  `crystal_a3_semdiff_w3_measures_encoding_agreement` (spec-building, big box
  only), `crystal_a3_w3_e2_instrument_smoke` (E2-only, RUN here — below),
  `crystal_a3_w3_lane_exercises_the_overflow_constructor` (the +1 pin, which
  also pins all three operator mnemonics per fixture), the coverage print
  extended to the six-lane union, and the W2c gate's trailing note corrected
  (overflow now has its own lane).
* `tests/eval_ir/census.rs` — the 17 `ir_exact_ovf_*` names joined
  `WITNESSES`, so `eval_ir_witnesses_are_registered_and_axiom_free` gates
  them (registered + empty transitive axiom closure) on the big box.

## Plan deltas (record, not silence)

1. **α without `IRStepResult2`** — see the design section; the sketched new
   inductive was not needed and none was added (firewall untouched by
   construction).
2. **"Synthetic module(s)" landed as two modules split by SIGNEDNESS, not by
   operator.** The overflow flag is the one integer arithmetic where
   `int_` vs `uint_` changes the answer, so u8/i8 is the split that measures
   something; the three operators share each body (six-value ret), which
   keeps every row observing all six bound results and spreads polarity
   coverage across rows (per-op ledger in the stage's module doc).
3. **Width 8 everywhere, and one deliberately expensive row.** `ir_wrap`
   walks its dividend (the re-measured residue cost law), so battery rows
   were chosen to keep raw products small — except `-128 × -1` (raw product
   32640, seconds-class on E1), kept because it IS the plan's named signed
   MIN edge. Registration-time witnesses stay under ~800-step walks.
4. **The producer's real overflow bodies stay refused, and the refusal is
   inherited, not reopened:** the `no_overflow` shape (9 bodies,
   `mul.overflow usize`) is at the width the type lane deliberately leaves
   unresolved (`eval_ir_meta_tag.rs` module doc), so the synthetic lane is
   the honest measurement route.
5. **A dated historical record now reads stale and is left as-written:**
   `tests/fixtures/meta_tag_shl.lineage.json` ("exactly TWO arms … tagged
   unmodelled", "what_a_later_lane_would_also_owe: IRInst.overflow … an
   evaluator and a binder") is a committed lineage fixture from the
   meta-tag wave; it predicted exactly this wave's build items and stays
   inline per R6.

## The E2 half, MEASURED here (2026-08-25, `crystal_a3_w3_e2_instrument_smoke`, verbatim values/steps)

```
=== W3 E2 smoke: synth_overflow_u8 ===
  16 op 16: mul wraps at exactly 2^8 -> [int 32, bool false, int 0, bool false, int 0, bool true] @Some(4) steps
  0 op 1: sub borrows to 255         -> [int 1, bool false, int 255, bool true, int 0, bool false] @Some(4) steps
  240 op 32: add and mul overflow together -> [int 16, bool true, int 208, bool false, int 0, bool true] @Some(4) steps
  3 op 2: nothing overflows          -> [int 5, bool false, int 1, bool false, int 6, bool false] @Some(4) steps

=== W3 E2 smoke: synth_overflow_i8 ===
  96 op 64: add and mul escape the signed maximum -> [int 160, bool true, int 32, bool false, int 0, bool true] @Some(4) steps
  -128 op 1: only sub leaves the range -> [int 129, bool false, int 127, bool true, int 128, bool false] @Some(4) steps
  3 op -2: nothing overflows         -> [int 1, bool false, int 5, bool false, int 250, bool false] @Some(4) steps
  -128 op -1: the MIN * -1 asymmetry -> [int 127, bool true, int 129, bool false, int 128, bool true] @Some(4) steps
```

Every row is the authored expectation exactly — 48 result values, all three
(value, flag) pairs per row, both polarities of every operator in both
signedness lanes, values crossing as raw width-8 residues — and every step
count is 4 (three overflow nodes + ret), so the declared 0 cost offsets have
their measured E2 half. Expected E1 least fuels, analytic and UNMEASURED:
**4 on every row** (tightness: `fuel_out` at 3). The stage witnesses' fault
edges halt at the first step. A mismatch on the first big-box run is a
finding to report, not a knob to turn.

## The inertness argument (the arm was unreachable, stated and verified)

The dispatch change replaces the body of ONE arm of the `ir_exec` match.
(i) Kernel iota-reduction selects only the scrutinee constructor's arm, so
every application over a different constructor reduces exactly as before —
the three `ir_exec_*_irrelevant` theorems included (their scrutinees are
`switch`/`callindirect`). (ii) No registered module, witness, or battery
fixture constructed `IRInst.overflow` before this wave — verified by grep:
the sole source occurrence was the dispatch arm itself (the mint's
`ir_mint/shape.rs` row is a parser shape, not a constructed term; the only
other mention is the prose record of delta 5). (iii) The new def names
(`ir_bind2`, `ir_frame_bind2`, `ir_overflow_*`, `ir_exact_ovf_*`, `ir_w3_*`)
collide with nothing — grep over the spec sources shows exactly the three
new definition sites. (iv) Every prior gate RUNNABLE on this box re-ran
green after the change: all five E2 instrument smokes (W1/W2a/W2b/W2c/W3),
the five lane pins, the coverage print, `crystal_a1_lineage` freshness
(17 passed), and the 49 `ir_semdiff::` lib unit tests. (v) The kernel-side
confirmation of (i)-(ii) is the big-box rerun below — until then every
E1-touching row is UNKNOWN, and since the new arith/machine defs register
INSIDE `add_eval_ir` (every EvalIr-bundle spec build), the FIRST failure
mode to look for is a registration error breaking every spec-building
target at once.

## Verified here (2026-08-25, plan §6 environment)

`cargo check --locked -j 2 --workspace` green; `cargo check --locked -j 2 -p
clean-verify --tests` green; `cargo clippy --locked -j 2 -p clean-verify
--all-targets -- -D warnings` green; `cargo fmt -p clean-verify --check`
clean; `scripts/evalir_coverage.py --check` green (unchanged 6/28 — the
scoreboard derives from minted artifacts only).

## The exercised ladder after this wave (battery print, run here)

`crystal_a3_coverage_is_reported_over_the_full_irinst_surface`: 6/28 narrow,
15/28 narrow+W1, 20/28 +W2a, 24/28 +W2b, 26/28 +W2c, **27/28 +W3**.
Exercised is not measured; the fraction that counts is the artifact's. The
one still-unexercised constructor is `fcmp` (W4 — the float lane, the last
tagged arm of the dispatch).

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
# input digest covers the crate source. NOTE: unlike W2a-c this wave changed
# add_eval_ir itself (arith defs + exacts, machine binds + exec + dispatch),
# so the FIRST failure mode to look for is a registration error breaking
# every spec-building target at once; the second is a refuted ir_exact_ovf_*
# vector or ir_w3_* witness (the kernel RAN the semantics and disagreed —
# report, never tune).

# 2. Run the W3 differential and the narrow/W1/W2a/W2b/W2c gates with the
#    recorded command (data/crystal_gap2_semdiff_2026-08-20.json `command`):
cargo test --offline -p clean-verify --test crystal_a3_semdiff -- --nocapture --test-threads=1
# then mint data/crystal_gap2_semdiff_<date>.json from that run's output.
# A constructor enters the new artifact's `coverage.exercised` ONLY from rows
# that measured agreement — never from authored rows. W2a's recorded `undef`
# coverage-policy question (evalir_w2a.PENDING.md delta 2) still belongs to
# that mint session; overflow has eight agreement rows and no delta, so it
# enters normally.

# 3. Re-derive the coverage scoreboard from the committed artifacts:
python3 scripts/evalir_coverage.py            # writes data/evalir_coverage.json
python3 scripts/evalir_coverage.py --check
```

`data/evalir_coverage.json` stays **6/28** until step 3 runs over a minted
artifact recording the new rows (checked here: `--check` green, unchanged).
