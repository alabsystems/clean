# U2 stage 2 — obligations PENDING on this box (honest ledger)

Date: 2026-08-25 • Lane: U2 stage 2 (sub-class B — the decl-close
`Param` vs `Max` rejections)
Plan: `docs/analysis/u2-implementation-plan-2026-08-24.md` §3 stage 2.

Measured root cause (attributed on this box, builtin prelude, stage-0
discipline): `Unifier::infer_level_for_type`
(`crates/clean-elab/src/unify/unifier/mod.rs`) handled Sort/FVar/Const/App
and returned `None` for PI TYPES, so a Sort-typed metavariable assigned a
function type never had its level equation GENERATED at all —
`CLEAN_U2_HISTOGRAM=1` on every failing probe shows ZERO solver events for
the orphaned param (the plan's "no event means the equation was never
GENERATED" discriminator, confirmed). The param was then generalized at
declaration close and the mandatory kernel re-check refused with the
recorded face `expected Sort(Param(u_N)), got Sort(Max(Succ(..), Succ(..)))`.
Fix: the Pi arm (capability-adding only; the equation now reaches the
shared solver's existing arms 5/6/7/9).

This box (8 GB, no Mathlib corpus, no clean-verify spec binaries) cannot run:

1. **The 5-file Mathlib source-elab gate re-measurement** (stage-2
   verification). Command, on the corpus box, per the armed ratchet's own
   recorded invocation:

   ```
   scripts/source_elab_gate.sh --jobs 3 --update
   ```

   The measured claim to make afterwards — and the only one — is
   per-declaration: each of the 3 named sub-class-B declarations (plan
   §1.2, all in `Mathlib/Logic/Function/Basic.lean`):

   - `Function.hasUncurryBase` (instance; its builtin-prelude analog —
     section `Type*` variables + `⟨id⟩` over an `α → β` carrier —
     reproduced the face byte-for-byte at baseline and flips with the fix)
   - `Set.SeparatesPoints` (def)
   - `Pi.map_id` (theorem)

   must LEAVE the `sort/universe mismatch` class in the new report's
   `per_error_class`. They are expected-pass CANDIDATES, not promised
   passes — clearing one face can reveal the next (the second and third
   were NOT reproduced 1:1 on builtin prelude; their nearest analogs pass
   both before and after, so their faces may carry additional Mathlib-only
   ingredients on top of the Pi gap). Sub-class-A declarations still in
   the class after stage 1's re-run may also move — the Pi arm fires on
   any `?A : Sort ?u := <function type>` assignment — but no per-decl
   claim is made for them here. The armed ratchet enforces the success
   floor (154/77/13/8/58 may only rise).

2. **The A/B wall-time profile on the corpus box** (stage-1 perf
   discipline, inherited unchanged). The added per-assignment work is one
   cached-TypeChecker `infer_type` on the assigned Pi — the same cost
   class as the pre-existing App arm of `infer_level_for_type`, paid only
   when a Sort-typed meta is assigned a Pi. Per the plan, a wall-time
   regression on the 5-file gate is a BLOCKER even with all verdicts
   green. Method: concurrent BEFORE/AFTER release binaries, as in
   `docs/issues/2026-08-21-mathlib-source-frontier-logic-basic.md`.

3. **E1/kernel-obligation suite legs**: clean-verify spec test binaries
   are the 8.8 GB class and are banned on this box; those rows stay
   UNKNOWN here by policy — the pinned runner on the suite box owns them.

4. **`scripts/u2_battery.sh` green-through-the-gate at the final split**:
   the gate's provenance check requires its fixture inputs TRACKED and
   CLEAN, so with p43/p44 uncommitted it refuses by design. Run it once
   after commit (it re-mints `reports/u2-battery.json` with the derived
   35 pass / 7 fail split and the shipped binary's sha). Until then the
   equivalent assertions were executed manually with the same binary
   (p43: 9 passed 0 failed; p44: non-zero exit with the pinned fragment),
   and the committed-input battery (34 pass / 6 fail-pinned, p41/p42
   included) is GREEN through the unmodified gate on the fixed binary.
