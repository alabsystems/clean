# U2 stage 1 — obligations PENDING on this box (honest ledger)

Date: 2026-08-25 • Lane: U2 stage 1 (ElabCtx↔ProofState level-identity bridge)
Plan: `docs/analysis/u2-implementation-plan-2026-08-24.md` §3 stage 1.

This box (8 GB, no Mathlib corpus, no clean-verify spec binaries) cannot run:

1. **The 5-file Mathlib source-elab gate re-measurement** (stage-1
   verification item 5). Command, on the corpus box, per the armed ratchet's
   own recorded invocation:

   ```
   scripts/source_elab_gate.sh --jobs 3 --update
   ```

   The measured claim to make afterwards — and the only one — is
   per-declaration: each of the 19 named sub-class-A declarations (plan §1.2:
   `cast_heq_iff_heq`, `heq_cast_iff_heq`, `forall₂_true_iff`,
   `forall₃_true_iff`, `mem_dite`, `dite_mem`, `beq_eq_beq`,
   `Function.Injective.extend_comp`, `Symmetric.forall_existsUnique_iff`,
   `eq_mp_bijective`, `eq_mpr_bijective`, `cast_bijective`,
   `Subtype.mk_eq_mk`, `Subtype.coind_injective`, `not_lt_iff_not_le_or_ge`,
   and the four `Mathlib.Tactic.LE.LE.LT.*` rows) must LEAVE the
   `sort/universe mismatch` class in the new report's `per_error_class`.
   They are expected-pass CANDIDATES, not promised passes — clearing one
   face can reveal the next. The armed ratchet enforces the success floor
   (154/77/13/8/58 may only rise). Sub-class B (the three decl-close
   `Param` vs `Max` rejections) is stage 2, untouched here.

2. **The A/B wall-time profile on the corpus box** (stage-1 risk item:
   level canonicalization on the tactic path). The added per-check work is
   `MetaState::instantiate_levels` on ProofState kernel-check inputs — an
   O(1) no-op clone when the tactic recorded no level constraint, and a
   `has_level_param_quick`-guarded walk otherwise; no memoization was added
   because the ProofState's meta population is tactic-scale, not
   declaration-scale. Per the plan, a wall-time regression on the 5-file
   gate is a BLOCKER even with all verdicts green. Method: concurrent
   BEFORE/AFTER release binaries, 1 ms `sample(1)` windows, as in
   `docs/issues/2026-08-21-mathlib-source-frontier-logic-basic.md`.

3. **E1/kernel-obligation suite legs**: clean-verify spec test binaries are
   the 8.8 GB class and are banned on this box; those rows stay UNKNOWN here
   by policy — the pinned runner on the suite box owns them.

4. **`scripts/u2_battery.sh` green-through-the-gate**: the gate's provenance
   check requires its fixture inputs TRACKED and CLEAN, so with p41/p42
   uncommitted it refuses by design. Run it once after commit; until then
   the equivalent assertions were executed manually with the same binary
   (p41: 8 passed 0 failed; p42: non-zero exit with the pinned fragment
   `cannot assign rigid universe parameter u := 1`), and the committed-input
   battery (34 pass / 6 fail-pinned) is GREEN through the gate itself.

What WAS measured on this box before landing (see the stage-1 report):
stage-0 probes CONFIRM bridge-class (zero `[u2hist]` solver events on every
failing probe); all sub-class-A probe shapes flip FAIL→PASS; U2 battery
34/6 GREEN through the unmodified gate on the fixed binary; everyday
battery via `test_r100_everyday_battery_full` (63 snippets name-for-name);
`cargo test --locked --lib -p clean-elab` slices; workspace check; fmt;
clippy on the touched crate.
