# EvalIR W2c (synthetic micro-modules, call+module tranche, +2) — PENDING (recorded state, not silence)

**Wave:** W2c of `docs/analysis/evalir-completion-plan-2026-08-24.md` §5
(the synthetic lane's call+module tranche: `callindirect`, `globaladdr`) —
**the FINAL synthetic tranche**: after it, every `IRInst` constructor except
`overflow` (plan W3) and `fcmp` (plan W4) has battery rows.
**Authored:** 2026-08-25, on the 8 GB authoring box (plan §6 environment).
**Status: AUTHORED + TYPE-CHECKED + E2-SMOKED here; the kernel half (E1) —
the stage witnesses, the battery's value/outcome probes, and therefore every
agreement row — is UNKNOWN until a big machine runs it.** Per
`docs/SUITE_STATE.md`, UNKNOWN is the correct reading and is never rounded up.

## What landed

* `crates/clean-verify/src/spec/core_spec/eval_ir_w2c_synth.rs` — two
  hand-authored micro-modules + kernel witnesses incl. the fault edges.
  `ir_w2c_ci_*` (callindirect: ONE caller body dispatching through a
  function-pointer ARGUMENT to TWO companion callees — one
  argument-independent `const 11`, one the identity — so value-driven
  dispatch is the two-point separation the rows measure, universally
  quantified over the payload on both paths; fault edges: null callee
  `ub null_deref`, integer callee `type_error not_fnptr` over both free
  values, dangling fnptr `stuck no_func`), `ir_w2c_ga_*` (globaladdr: one
  global `u32 = 7`; the initializer read, and a store-through-one-address /
  load-through-a-SECOND-globaladdr-of-the-same-global round-trip — the
  repeated-address-of-aliases property measured, quantified over the stored
  value; fault edges: nonbool selector, and the value-level
  `ir_globaladdr_eval` missing-global `type_error no_global`). Registered as
  Full-bundle stage `add_eval_ir_w2c_synth` (bundles.rs, directly after
  `add_eval_ir_w2b_synth`; reuses only `add_eval_ir` names so the battery
  registers the module lines standalone). 22 defs, all `Eq.refl`, no new
  inductives — the vacuity firewall's family list is untouched by
  construction.
* `crates/clean-verify/tests/fixtures/synth/synth_callindirect.trust-ir.txt`
  + `synth_callindirect_c11.trust-ir.txt` + `synth_callindirect_id.trust-ir.txt`
  + `synth_globaladdr.trust-ir.txt` — the authored E2 twins, each
  self-declaring `SYNTHETIC MODULE` in `; #synthetic:` directive lines
  (the `crystal_a1_lineage` freshness-closure invariant; its spec-free test
  re-run here: green, 17 passed).
* `crates/clean-verify/tests/crystal_a3_semdiff/w2c_chains.rs` — **2 chains
  / 9 inputs**, `Synthetic`-labeled, E3 absent by construction on every
  chain, reusing the W2a table structs verbatim; one DECLARED executor delta
  (below).
* Gate additions in `crystal_a3_semdiff.rs`: the W2c lane runs through the
  existing lane-parameterized `measure_synth_lane` / `synth_e2_smoke_lane`
  (no machinery change needed — the factoring W2b did was the last):
  `crystal_a3_semdiff_w2c_measures_encoding_agreement` (spec-building, big
  box only), `crystal_a3_w2c_e2_instrument_smoke` (E2-only, RUN here —
  below), `crystal_a3_w2c_lane_exercises_the_two_w2c_constructors` (the +2
  pin), and `crystal_a3_coverage_is_reported_over_the_full_irinst_surface`
  extended to the five-lane union.
* `src/ir_semdiff/synth.rs` — `IrFaultName` gained `NullDeref` (+ a term
  unit test); `src/ir_semdiff/wide.rs` gained `wide_fnptr` / `wide_nullptr`
  (+ a unit test). Both run here: 47 `ir_semdiff::` lib unit tests green.

## Plan deltas (record, not silence)

1. **The null-callee row diverges by fault CODE, not class.** The plan named
   a "null-callee UB row"; measured at trust-ir `a4e81b6`, the reference
   interpreter reports its own `invalid_function_pointer` code
   ("CallIndirect: null function pointer", `interpret.rs:1415-1421`) — NOT
   `undefined_behavior` — while Clean's `ir_callind_exec` pins
   `ub null_deref` (`ir_w2c_ci_on_null`). `invalid_function_pointer` is
   outside the two-class outcome map on purpose, so the row lands as a
   `SynthExpect::DeclaredDelta` (asserted to reproduce exactly, printed,
   never counted as agreement), not the plan's implied `UbAgree`.
2. **The plan's "fnptr table" landed as a fnptr ARGUMENT plus two companion
   callees.** A single callee cannot distinguish "the machine resolved the
   value" from "the machine returned the argument"; two can — same caller
   body, same payload, different fnptr, different answer, measured per row on
   both executors. The module contains no fnptr-PRODUCING instruction: a
   `const functy` / `reify_fn_pointer` lane would measure `const_`/`cast`
   again, not `callindirect`. The inert `sig`/`calling_conv` operands are
   spelled `ir_d9`/`ir_d0` on the Clean side against the E2 twin's
   `functy.920` — licensed by the existing kernel theorems
   `ir_exec_callind_sig_irrelevant` / `ir_exec_callind_conv_irrelevant`,
   which is exactly what those irrelevance theorems are for.
3. **The dangling-fnptr and non-fnptr-callee edges are kernel-witnessed, not
   battery rows.** Clean: `stuck no_func` (`ir_w2c_ci_no_func`) /
   `type_error not_fnptr` (`ir_w2c_ci_not_fnptr`). E2 reports
   `invalid_function_pointer` for the dangling id at the call, and rejects
   the integer-in-fnptr-slot input at the ENTRY signature check — different
   sites and codes with no shared row vocabulary; the same split family as
   delta 1, recorded in the stage docs.
4. **`globaladdr`'s global lives in the chain's `type_decls`, not the
   fixture file.** A trust-ir global is a module-level declaration
   (`global mut @SYNTH_G u32 = 7` in the composed module header); the
   fixture file carries the function only and says so in its directives.
   Clean twin: `IRGlobal.mk ir_d0 (IRConst.int_ ir_d7)` in
   `ir_w2c_ga_module`.
5. **Globals-or-low-na design rule (Clean side).** A Clean global's id IS
   its cell address (`ir_globals_mem`), and the battery passes `na = 0`, so
   the `globaladdr` module allocates nothing — an `alloca` at `na = 0` would
   collide with global 0's cell. Recorded in the stage's module doc as the
   rule for any future globals-carrying module.
6. **Materialization timing is an unobservable split, recorded.** Clean
   materializes global cells at `ir_init`; the interpreter lazily allocates
   on FIRST `global_addr` and caches the pointer (`global_pointer`,
   `a4e81b6`). No row observes allocation order, so no delta row exists; the
   note lives in the stage doc rather than being silently dropped.
7. **Three fixture files for one callindirect chain.** `build_wide_module`'s
   contract is one function per fixture entry (the W1 `has_loose_bvars`
   precedent), so the caller and each companion callee are separate
   `synth/`-prefixed files, composed with `func_ids: [0, 1, 2]`.
8. **`sigs` functy indices 919-921** continue W2a/W2b's 910-918 convention —
   arbitrary per-chain reconstituted tables, never shared across chains.

## The E2 half, MEASURED here (2026-08-25, `crystal_a3_w2c_e2_instrument_smoke`, verbatim values/steps)

```
=== W2c E2 smoke: synth_callindirect ===
  const11 callee ignores payload 7   -> int 11 @Some(4) steps
  const11 callee ignores payload 0   -> int 11 @Some(4) steps
  ident callee transports 7          -> int 7 @Some(3) steps
  ident callee transports u32::MAX   -> int 4294967295 @Some(3) steps
  null function pointer              -> fault invalid_function_pointer @None steps
      (declared delta 1 reproduces exactly)

=== W2c E2 smoke: synth_globaladdr ===
  false reads the initializer 7      -> int 7 @Some(4) steps
  store 42, load through the second address -> int 42 @Some(6) steps
  store 0, load through the second address -> int 0 @Some(6) steps
  store u32::MAX, load through the second address -> int 4294967295 @Some(6) steps
```

Every step count equals the analytic per-path instruction count
(call_indirect + callee const + callee ret + caller ret = 4;
call_indirect + callee ret + caller ret = 3;
global_addr + condbr + load + ret = 4;
global_addr + condbr + global_addr + store + load + ret = 6), so the declared
0 cost offsets have their measured E2 half — including that the interpreter
counts the indirect-call frame push/pop the same way Clean's machine steps do
on these bodies. Expected E1 least fuels, analytic and UNMEASURED: const11
rows 4, ident rows 3, null row 1; globaladdr initializer row 4, store rows 6.
A mismatch on the first big-box run is a finding to report, not a knob to
turn.

## The exercised ladder after this wave (battery print, run here)

`crystal_a3_coverage_is_reported_over_the_full_irinst_surface`: 6/28 narrow,
15/28 narrow+W1, 20/28 narrow+W1+W2a, 24/28 narrow+W1+W2a+W2b, **26/28
narrow+W1+W2a+W2b+W2c**. Exercised is not measured; the fraction that counts
is the artifact's. The two still-unexercised constructors are `overflow`
(W3 — the two-result value-domain build item) and `fcmp` (W4 — the float
lane). The synthetic tranches are COMPLETE.

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
# registration error in add_eval_ir_w2c_synth breaking every Full-spec
# target at once; the witnesses themselves are kernel-run at registration.

# 2. Run the W2c differential and the narrow/W1/W2a/W2b gates with the
#    recorded command (data/crystal_gap2_semdiff_2026-08-20.json `command`):
cargo test --offline -p clean-verify --test crystal_a3_semdiff -- --nocapture --test-threads=1
# then mint data/crystal_gap2_semdiff_<date>.json from that run's output.
# A constructor enters the new artifact's `coverage.exercised` ONLY from rows
# that measured agreement — never from authored rows. TWO coverage-policy
# questions now belong to that mint session, same class, decide both
# explicitly: W2a's `undef` (E1-only — every E2 comparison is a declared
# delta, evalir_w2a.PENDING.md delta 2) and nothing new from W2c
# (callindirect has four agreement rows besides its declared delta, so it
# enters normally).

# 3. Re-derive the coverage scoreboard from the committed artifacts:
python3 scripts/evalir_coverage.py            # writes data/evalir_coverage.json
python3 scripts/evalir_coverage.py --check
```

`data/evalir_coverage.json` stays **6/28** until step 3 runs over a minted
artifact recording the new rows (checked here: `--check` green, unchanged).
