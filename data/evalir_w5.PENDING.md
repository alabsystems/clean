# EvalIR W5 (the adequacy grid — kill "cannot see semantic depth") — PENDING (recorded state, not silence)

**Wave:** W5 of `docs/analysis/evalir-completion-plan-2026-08-24.md` §5 — the
§4(c) grid: every syntax field of every `IRInst` constructor classified
constructor-by-constructor, the seventeen remaining dropped-operand
irrelevance theorems authored, the `Alloca.align` erasure audit-pinned, and
the six measured W1-W4 executor divergences given their permanent rows.
**Authored:** 2026-08-25, on the 8 GB authoring box (plan §6 environment).
**Status: AUTHORED + TYPE-CHECKED + STRING-LEVEL-VERIFIED here; the kernel
half (E1) — the registration of the seventeen new `Eq.refl` theorems inside
`add_eval_ir` (every spec build), and the WITNESSES axiom-closure gate over
all twenty — is UNKNOWN until a big machine runs it.** Per
`docs/SUITE_STATE.md`, UNKNOWN is the correct reading and is never rounded up.

## The grid, and its totals by state (the wave's headline)

`data/evalir_adequacy_grid.json`, generated fail-closed by
`scripts/evalir_adequacy_grid.py` (same style as `evalir_coverage.py`:
deterministic output, content-derived provenance, `--check`, `--self-test`
with 9 mutation arms — all green here). **92 rows:**

| state | rows | what it means |
|---|---|---|
| `relevant-by-design` | **63** | the `ir_exec` dispatch arm READS the field — no irrelevance theorem is possible, the battery rows measure it |
| `irrelevance-proved-await-mint` | **20** | the dispatch BINDS AND DROPS the field and a kernel-checkable `Eq.refl` theorem states the step is identical at every value (3 pre-W5 precedents + 17 authored this wave) |
| `audit-pin` | **3** | the erased `align` slots of load/store/alloca — no `IRInst` slot exists, so the boundary is pinned, not theorem'd |
| `declared-delta` | **6** | the measured W1-W4 executor divergences — this grid is their permanent home |

Field surface: 83 field rows = every field of all 28 constructors (derived
from the `IRInst` telescopes; 63 + 20 = 83, checked by arithmetic in the
gate). The derivation is MECHANICAL: field list from `eval_ir_syntax.rs`,
read/drop verdict from word-boundary use of the arm's pattern variable in the
`eval_ir_machine.rs` dispatch RHS — so a new field cannot be silently
unclassified (script and gate both abort).

## What landed

* `crates/clean-verify/src/spec/core_spec/eval_ir_adequacy.rs` — NEW: the
  seventeen irrelevance theorems (`ir_exec_load_ty/load_vol/store_ty/
  store_vol/alloca_ty/gep_ty/gep_inbounds/ptrdata_ty/ptrmeta_pt/ptrmeta_mt/
  ptrparts_pt/ptrparts_mt/extractfield_ty/insertfield_ty/extractelement_ty/
  undef_ty/select_ty_irrelevant`), exactly the precedent pattern
  (`eval_ir_machine.rs:973-1016` pre-W5 numbering): `IRTy`-typed fields
  varied as two quantified binders (the `callind_conv` shape), `Bool`-typed
  fields stated at `Bool.true` vs `Bool.false` (the `switch_exh` shape), the
  proof term the dispatch arm's RHS verbatim. Registered from a new
  `add_eval_ir_adequacy` called at the END of `add_eval_ir_machine` (after
  dispatch), so every pre-existing def keeps its registration position (the
  W4 precedent). Three spec-free unit tests in the file verify, on this box:
  each statement's two sides differ in EXACTLY the claimed slot and the
  varied tokens never reach the proof term; the claimed rows are EXACTLY the
  dispatch's dropped-field surface (both directions); dispatch arity matches
  the telescopes.
* `crates/clean-verify/src/spec/core_spec/eval_ir_machine.rs` — the "drops
  exactly three operands" comment carries its dated correction (R6): the
  mechanical count is TWENTY; the three theorems there are the precedent and
  the seventeen live in `eval_ir_adequacy.rs`.
* `scripts/evalir_adequacy_grid.py` + `data/evalir_adequacy_grid.json` — the
  generator and the committed artifact (totals above). Every proved row must
  name a theorem whose `def <name> ` exists in its stated source; every
  audit-pin and delta row must anchor to live source text (verbatim
  substrings, the blind-slot-ledger row included) — a closed erasure or a
  renamed witness breaks the derivation instead of outliving it.
* `crates/clean-verify/tests/eval_ir/adequacy_grid.rs` — gate clause 5 of the
  `eval_ir` target, SPEC-FREE (runs here): re-derives the field surface with
  its OWN parsers (not the script's) and holds the committed JSON to it —
  full coverage (every field of every constructor exactly once), state
  matches the read/drop verdict, theorems present, erased set = exactly the
  three align rows, delta set = exactly the six ids, totals arithmetic, and
  the dispatch echo in the JSON matches the parsed dispatch.
* `crates/clean-verify/tests/crystal_a1_lineage/operand_audit.rs` — the
  audit-pin (plan §4(c) option (ii), adopted):
  `the_alignment_operand_reaches_the_mint_and_its_exec_erasure_is_pinned`
  pins that the mint READS the align slot fail-closed for load/store
  (`r_align` lanes + the unrecognised-trailing-operand refusals,
  `src/ir_mint/emitted_inst.rs`), that `alloca` has NO reader arm at all (the
  mnemonic falls through to the fail-closed `NoImage` refusal — checked as
  absence plus the fall-through anchor), that the three `IRInst` shapes and
  the three dispatch arms carry no align notion (verbatim pins), that the R8
  ledger row stands (`data/crystal_mint_blind_slots.json` slot `align`, kind
  `compared` — the row predates this wave; the grid rows cite it rather than
  duplicating it), and that the grid carries exactly 3 audit-pin rows.
* `crates/clean-verify/tests/eval_ir/census.rs` — all TWENTY theorem names
  joined `WITNESSES` (the three pre-W5 ones had never been gated there), so
  `eval_ir_witnesses_are_registered_and_axiom_free` holds each to registered
  + EMPTY transitive axiom closure on the big box.

## Plan deltas (record, not silence)

1. **The sketch's `unop.t`/`binop.t`(float arms)/`fcmp.t` rows are DEAD, per
   the W4 binding note.** Plan §4(c) listed them as retained-inert; the
   post-W4 dispatch PASSES `t` to all three evaluators (the width gates), so
   they derive as `relevant-by-design` — no theorem is possible or wanted.
   The grid is derived from the post-W4 dispatch, exactly as
   `evalir_w4.PENDING.md` delta 1 instructed.
2. **The plan's "~16 theorems" is 17.** The mechanical derivation over the
   dispatch counts 20 dropped fields; 3 had theorems, so the wave authors 17
   (the sketch had under-counted `ptrmetadata`/`ptrfromparts`'s paired type
   slots and `undef.t`, and over-counted the three float `t` rows above).
3. **`Alloca.align` landed as option (ii) audit-pin, per the plan's own
   recommendation** ("(i) only if a chained body's alignment ever becomes
   observable — in a cell-addressed model it cannot be, and that
   unobservability is itself the adequacy statement"). No `IRInst` arity
   change, no minter/censal ripple. The R8 ledger row already existed
   (blind-slots `align`, HALF-CLOSED 2026-08-20) — this wave cites it and
   adds the exec-side pin + grid rows rather than minting a duplicate row;
   R8's "the ledger count only shrinks" is respected by construction.
4. **The grid quantifies the three PRE-W5 theorems as
   `irrelevance-proved-await-mint` too**, with a per-row `since` field
   separating "operand-audit era, kernel-run GREEN in prior suite passes"
   from "W5 2026-08-25, first kernel run pending" — the whole crate's suite
   rows are UNKNOWN at this tree state either way, so one state with dated
   provenance is the honest encoding.
5. **Doc restatements ride the mint session.** Plan W5 also names GAP2 §8 and
   CRYSTAL_STATUS §0.6a rewrites and the new dated semdiff artifact; those
   quote the MEASURED fraction, which only the big-box mint can produce
   (benchmark-freshness discipline), so they belong to that session, not this
   authoring wave. The grid itself is complete and self-contained now.

## Verified here (2026-08-25, plan §6 environment)

`cargo check --locked -j 2 --workspace` green; `cargo check --locked -j 2 -p
clean-verify --all-targets` green; `cargo clippy --locked -j 2 -p
clean-verify --all-targets -- -D warnings` green; `cargo fmt -p clean-verify
--check` clean. `scripts/evalir_adequacy_grid.py` write + `--check` +
`--self-test` (9/9 mutation arms detected, baseline 92 rows) green;
`scripts/evalir_coverage.py --check` green (unchanged 6/28 — the scoreboard
derives from minted artifacts only) and its `--self-test` green. Spec-free
test re-runs, all green: the 3 new adequacy unit tests; the 3 grid gate
tests; `operand_audit` 6/6 (new pin included); `crystal_a1_lineage` freshness
17/17; all six E2 instrument smokes + all six lane pins + the coverage print
(28/28 exercised ladder unchanged) in one `crystal_a3_semdiff` run (13
passed); `ir_semdiff::` lib unit tests 50/50.

## The inertness argument (nothing pre-existing moved, stated and verified)

(i) The seventeen new defs register AFTER every pre-existing def of the
machine stage (appended at the end of `add_eval_ir_machine`), so registration
order for all pre-existing names is unchanged. (ii) The new names collide
with nothing (grep: only the new definition sites; census WITNESSES additions
are name references). (iii) No dispatch arm, evaluator, or registered module
was edited — the only `eval_ir_machine.rs` changes are a comment correction
and the added stage call. (iv) Every prior gate RUNNABLE on this box re-ran
green after the change (list above). (v) The kernel-side confirmation is the
big-box rerun below; since the new theorems register INSIDE `add_eval_ir`
(every EvalIr-bundle spec build), the FIRST failure mode to look for is a
registration error breaking every spec-building target at once; the second is
a REFUTED irrelevance theorem — the kernel found the dispatch reading a field
the grid says it drops — which is a finding to report (and a grid regen),
never a statement to weaken.

## What flips this file

On a big machine (spec registration is the 8.8 GB-class cost this box cannot
pay — CLAUDE.md "Machine limits"):

```bash
# 1. Re-shard (clean-verify::lib inputs moved) and re-run the suite:
scripts/verify_runner_pinned.sh shards plan
scripts/verify_runner_pinned.sh run
# Rows expected UNKNOWN until then: clean-verify__lib (7 shards),
# clean-verify__test__eval_ir (now including gate clause 5 and the 20-name
# WITNESSES additions), clean-verify__test__crystal_a3_semdiff,
# clean-verify__test__vacuity_firewall, clean-verify__test__crystal_a1_lineage
# (now including the align audit-pin), clean-verify__test__crystal_a2_mint* —
# and any other clean-verify row whose input digest covers the crate source.

# 2. The W1-W4 mint session commands stand unchanged (see those PENDING
#    files); this wave adds no battery rows, so the semdiff artifact mint is
#    untouched by W5 — the grid's "await-mint" rows flip when step 1's
#    eval_ir target goes GREEN (the theorems kernel-ran) rather than when the
#    semdiff artifact is minted.

# 3. Freshness gates for this wave's artifacts:
python3 scripts/evalir_adequacy_grid.py --check
python3 scripts/evalir_adequacy_grid.py --self-test
python3 scripts/evalir_coverage.py --check
```

When step 1's `eval_ir` and `clean-verify__lib` rows are GREEN, the grid's 20
`irrelevance-proved-await-mint` rows are kernel-confirmed at that sha; the
state name can then be tightened (a one-word script/gate change, done
together) in the same session that restates GAP2 §8 and CRYSTAL_STATUS §0.6a
from the minted numbers — plan delta 5 above.
