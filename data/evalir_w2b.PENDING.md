# EvalIR W2b (synthetic micro-modules, memory tranche, +4) — PENDING (recorded state, not silence)

**Wave:** W2b of `docs/analysis/evalir-completion-plan-2026-08-24.md` §5
(the synthetic lane's memory tranche: `alloca`, `ptrdata`, `ptrmetadata`,
`ptrfromparts`).
**Authored:** 2026-08-25, on the 8 GB authoring box (plan §6 environment).
**Status: AUTHORED + TYPE-CHECKED + E2-SMOKED here; the kernel half (E1) —
the stage witnesses, the battery's value/outcome probes, and therefore every
agreement row — is UNKNOWN until a big machine runs it.** Per
`docs/SUITE_STATE.md`, UNKNOWN is the correct reading and is never rounded up.

## What landed

* `crates/clean-verify/src/spec/core_spec/eval_ir_w2b_synth.rs` — four
  hand-authored micro-modules + kernel witnesses incl. the fault edges.
  Unlike W2a's, every module is a COMPOSITION, because a memory constructor
  is only observable through the heap (the file's module doc states this as
  the design rule): `ir_w2b_al_*` (alloca + condbr between the store/load
  round-trip — universally quantified over the stored value — and the
  fresh-cell uninitialized read, `ub uninit`; plus the nonbool-selector
  edge), `ir_w2b_pd_*` (thin ptr_data observed by dereferencing the
  PROJECTED pointer; value-level fat/null/not_ptr witnesses), `ir_w2b_pm_*`
  (str-fat rebuild + metadata projection, the length round-trip universally
  quantified over value AND length; value-level thin-arm and not_ptr
  witnesses), `ir_w2b_pp_*` (thin and fat rebuild arms each observed through
  a deref behind a condbr; value-level vtable/fnptr/bad-metadata/null-data
  witnesses — `ir_w2b_pp_null_data` quantifies over the WHOLE IRScalar
  metadata family, since the match decides on the data operand alone).
  Registered as Full-bundle stage `add_eval_ir_w2b_synth` (bundles.rs,
  directly after `add_eval_ir_w2a_synth`; reuses only `add_eval_ir` names so
  the battery registers the module lines standalone). 32 defs, all
  `Eq.refl`, no new inductives — the vacuity firewall's family list is
  untouched by construction.
* `crates/clean-verify/tests/fixtures/synth/synth_{alloca,ptrdata,
  ptrmetadata,ptrfromparts}.trust-ir.txt` — the authored E2 twins, each
  self-declaring `SYNTHETIC MODULE` in `; #synthetic:` directive lines
  (the `crystal_a1_lineage` freshness-closure invariant; its spec-free test
  re-run here: green).
* `crates/clean-verify/tests/crystal_a3_semdiff/w2b_chains.rs` — **4 chains
  / 14 inputs**, `Synthetic`-labeled, E3 absent by construction on every
  chain, reusing the W2a table structs verbatim; one non-`Ret` row (below).
* Gate additions in `crystal_a3_semdiff.rs`: the W2a gate/smoke bodies were
  factored into lane-parameterized `measure_synth_lane` /
  `synth_e2_smoke_lane` (helper def-name prefix `w2a_` → lane-neutral `sx_`;
  behavior otherwise unchanged), and the W2b lane runs through them:
  `crystal_a3_semdiff_w2b_measures_encoding_agreement` (spec-building, big
  box only), `crystal_a3_w2b_e2_instrument_smoke` (E2-only, RUN here —
  below), `crystal_a3_w2b_lane_exercises_the_four_w2b_constructors` (the +4
  pin), and `crystal_a3_coverage_is_reported_over_the_full_irinst_surface`
  extended to the four-lane union.
* `src/ir_semdiff/synth.rs` — `IrFaultName` gained `Uninit` and `NotPtr`
  (+ a term unit test); `src/ir_semdiff/wide.rs` gained `wide_unit()` (the
  thin rebuild's unit metadata argument; trust-ir spells the type `()`).

## Plan deltas (record, not silence)

1. **The uninitialized-read row agrees at CLASS but diverges by fault
   SITE — measured, and honest only for this module's shape.** Clean's
   `ir_load_value` faults `ub uninit` AT THE LOAD of the fresh cell; the
   pinned interpreter's plain (non-strict) load of uninitialized bytes
   yields inert `PartialBytes` poison and faults `undefined_behavior` only
   when the value is INSPECTED — for `synth_alloca`, at the `ret` signature
   check (`reject_partial`, trust-ir `a4e81b6` `interpret.rs:5402-5403`;
   smoke-confirmed here: `fault undefined_behavior`, no step count). The row
   is `UbAgree(Uninit)` because this module's only path from the poisoned
   load ends in an inspection. **Fragment residue, recorded not smoothed:**
   a program that loads uninitialized memory and only COPIES/STORES it
   onward is UB under Clean's semantics and defined under the
   interpreter's copy-propagates-poison discipline — a real divergence
   class no W2b row measures, left for the adequacy stream (§4(c)) to own.
2. **`ptrmetadata`'s battery rows measure the slice/str (integer-length)
   shape only; the vtable/fnptr metadata arms are kernel-witnessed, not
   battery-measured.** Clean's `IRScalar.fat_ d md` carries `md : Nat`, so
   `ir_ptrmeta_eval` on a vtable-built fat value returns `int_ md` — the
   metadata's pointer-ness is erased (stated exactly in the
   `ir_w2b_pp_vtable` witness doc), and E2 returns a `Ptr` value the
   differential's integer vocabulary cannot compare. Their E2-comparable
   observable is the DATA lane, which the `ptrfromparts` fat path measures
   whole-program. The plan's "thin/fat/vtable rebuild cases" therefore land
   as: thin + fat(str) in the battery, vtable/fnptr as `Eq.refl`
   value-level witnesses over `ir_ptrparts_at` (machine:523-557's arms).
3. **`ptrmetadata`'s THIN arm has no battery row.** It returns unit — and
   `RunResult::Unit` in this battery's vocabulary is the EMPTY return list
   (`strict_monads`), not `ret [unit_]`, so a ret-of-unit row would compare
   the wrong Clean term. Kernel witness `ir_w2b_pm_thin` pins the arm
   value-level instead; the constructor's whole-program measurement is the
   fat arm.
4. **The E2 fat shape is `fatptr<str>`, not `fatptr<slice ty.N>`.** Both
   have the same canonical metadata (`u64` at the pinned 64-bit target,
   `shape.rs::PointerMetadataShape::metadata_ty`); `str` needs no element
   TyId, so the synthetic module carries no type table. Note the canonical
   metadata type is **u64, not usize** — `validate_fat_pointer_value`
   requires the declared and carried metadata type to BE the canonical one,
   so the fixtures declare `u64` and the chain passes `iv_u64`.
5. **Store/load/condbr ride along in every module.** Memory observability
   forces the composition (delta 1's design rule); all three already carry
   W1 agreement rows, so each W2b chain's new information is its
   constructor's. The exercised-forms print counts them once in the union.
6. **`sigs` functy indices 915-918** continue W2a's 910-914 convention —
   arbitrary per-chain reconstituted tables, never shared across chains.

## The E2 half, MEASURED here (2026-08-25, `crystal_a3_w2b_e2_instrument_smoke`, verbatim values/steps)

```
=== W2b E2 smoke: synth_alloca ===
  store 7 then load                  -> int 7 @Some(5) steps
  store 0 then load                  -> int 0 @Some(5) steps
  store u32::MAX then load           -> int 4294967295 @Some(5) steps
  load the fresh cell uninitialized  -> fault undefined_behavior @None steps

=== W2b E2 smoke: synth_ptrdata ===
  round-trip 7 through the projected lane -> int 7 @Some(5) steps
  round-trip 0                       -> int 0 @Some(5) steps
  round-trip u32::MAX                -> int 4294967295 @Some(5) steps

=== W2b E2 smoke: synth_ptrmetadata ===
  length 0 round-trips               -> int 0 @Some(5) steps
  length 1 round-trips               -> int 1 @Some(5) steps
  length 2^32 exercises the full u64 lane -> int 4294967296 @Some(5) steps

=== W2b E2 smoke: synth_ptrfromparts ===
  thin rebuild derefs to 7           -> int 7 @Some(6) steps
  thin rebuild transports u32::MAX   -> int 4294967295 @Some(6) steps
  fat rebuild's data lane derefs to 7 -> int 7 @Some(7) steps
  fat rebuild's data lane transports u32::MAX -> int 4294967295 @Some(7) steps
```

Every step count equals the analytic per-path instruction count
(alloca+condbr+store+load+ret = 5; alloca+store+ptr_data+load+ret = 5;
alloca+store+ptr_from_parts+ptr_metadata+ret = 5;
alloca+store+condbr+ptr_from_parts+load+ret = 6, +1 for the fat path's
ptr_data), so the declared 0 cost offsets have their measured E2 half.
Expected E1 least fuels, analytic and UNMEASURED: alloca stored rows 5,
uninit row 3 (Clean faults at the load, the third instruction — the site
split of delta 1); ptrdata 5; ptrmetadata 5; ptrfromparts thin 6 / fat 7.
A mismatch on the first big-box run is a finding to report, not a knob to
turn.

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
# registration error in add_eval_ir_w2b_synth breaking every Full-spec
# target at once; the witnesses themselves are kernel-run at registration.

# 2. Run the W2b differential and the narrow/W1/W2a gates with the recorded
#    command (data/crystal_gap2_semdiff_2026-08-20.json `command` field):
cargo test --offline -p clean-verify --test crystal_a3_semdiff -- --nocapture --test-threads=1
# then mint data/crystal_gap2_semdiff_<date>.json from that run's output.
# A constructor enters the new artifact's `coverage.exercised` ONLY from rows
# that measured agreement — never from authored rows; W2a's recorded `undef`
# coverage-policy question (evalir_w2a.PENDING.md delta 2) is still open and
# belongs to that same mint session.

# 3. Re-derive the coverage scoreboard from the committed artifacts:
python3 scripts/evalir_coverage.py            # writes data/evalir_coverage.json
python3 scripts/evalir_coverage.py --check
```

`data/evalir_coverage.json` stays **6/28** until step 3 runs over a minted
artifact recording the new rows (checked here: `--check` green, unchanged).
The battery's EXERCISED print, measured here, is 6/28 narrow, 15/28
narrow+W1, 20/28 narrow+W1+W2a, **24/28 narrow+W1+W2a+W2b**
(`crystal_a3_coverage_is_reported_over_the_full_irinst_surface`, run on this
box 2026-08-25). Exercised is not measured; the fraction that counts is the
artifact's. The four still-unexercised constructors are `callindirect` and
`globaladdr` (W2c), `overflow` (W3), `fcmp` (W4).
