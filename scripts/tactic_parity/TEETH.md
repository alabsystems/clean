# TEETH — recorded perturbations for the tactic family gates

Per docs/plans/TACTICS_TO_100_2026-07-29.md §7.3: **a gate with no recorded
perturbation-failure is not a gate.** This file names one specific mutation per
gate and the observation that must follow. The mutations are DESCRIBED here and
are to be DEMONSTRATED by the central verifier (this repo forbids gate authors
from running cargo; the demonstration requires a rebuild).

Both gates read per-declaration verdicts from `clean check --json`
(success_count / trust_failures / kernel_failures / proof_state_feedback) and
fail closed on: fixture/manifest drift, a probe count differing from the pinned
family denominator, any silently skipped declaration (decl_count mismatch), any
verdict that cannot be attributed to a declaration, a failing environment
canary (stub/builtin-prelude fallback), a failing `required` row, zero passing
probes, and any regression against the recorded baseline
(`data/tactic_family_baselines/<family>.json`).

## Demonstration procedure (both gates)

1. At HEAD, with a freshly built release binary: `scripts/tactic_parity/<fam>.sh`
   must print `<GATE>=measured …` (exit 0).
2. Record the ratchet: `scripts/tactic_parity/<fam>.sh --update-baseline` and
   commit `data/tactic_family_baselines/<fam>.json` (the update refuses to drop
   passing rows — ratchets only go down).
3. Apply the named mutation below, rebuild the release binary, re-run the gate.
   The gate must print `<GATE>=failed reason=…baseline regression…` naming the
   flipped rows, and exit 1.
4. Revert the mutation. Step 2's baseline is the permanent teeth record; update
   this file with the observed flip count and artifact paths once demonstrated.

## G-AUTO — named mutation: revert RC-A in `norm_num.rs`

**Mutation.** In `crates/clean-elab/src/tactic/norm_num.rs`, revert the RC-A
decide-routing import

```rust
use super::decide::eval_decide as decide;
```

back to the pre-fix

```rust
use super::smt::decide;
```

(the line carries a do-not-revert comment; this mutation is exactly the defect
fixed by commit `bf3a92a10`, plan §4 RC-A).

**Must observe.** ≥3 `g_auto` rows flip pass→fail, with the norm_num rows on
true ground goals — designated rows `p_auto_norm_num_01` ((2:Nat) ≤ 3),
`p_auto_norm_num_05` (¬(3 = 4)), `p_auto_norm_num_06` ((0:Nat) < 1) — failing
via `SmtFailed { tactic: "decide", detail: "found counterexample — goal is not
valid" }`, while the `p_auto_decide_*` controls on the identical goals keep
passing (the in-file control pattern from the plan's live reproduction,
`scratchpad/rc2_control.lean`, which measured 3 pass/3 fail before the fix and
6/0 after). With the baseline recorded, the gate exits 1 on the regression;
once the designated rows are promoted to `required` in the manifest (after the
first green run), the gate fails on this mutation even without a baseline.

**Status.** Described; not yet demonstrated at HEAD (requires a rebuild — the
central verifier runs the procedure above). The "before" direction is already
recorded in the plan: §4 RC-A's live differential and the brick-progress table
(3 pass/3 fail → 6 pass/0 fail at `6cae2dac3`).

## G-SIMP — named mutation: restore the hardcoded `u_simp` level

**Mutation.** In `crates/clean-elab/src/tactic/simp/expr.rs`, in the
`lemma_levels` construction (the RC-E.1 fix site — the long two-convention
comment block), replace the per-parameter resolution

```rust
.map(|param| resolve_lemma_level(&metas, param))
```

with the pre-fix hardcoded level

```rust
.map(|_| metas.instantiate_level(&Level::param(Name::from_string("u_simp"))))
```

(this is exactly the defect fixed by RC-E part 1, commit `7936e3c17`).

**Must observe.** ≥3 of the universe-polymorphic `simp only` rows
`p_simp_only_16` … `p_simp_only_25` (List lemmas: `reverse_reverse`,
`length_reverse`, `append_nil`, …) flip pass→fail as `NoProgress` — the RC-E
measured delta was 1/10 → 7/10 on exactly this probe class — while the
monomorphic rows `p_simp_only_01..15` are unaffected (the in-file control that
isolated RC-E). With the baseline recorded, the gate exits 1 on the regression.

**Status.** Described; not yet demonstrated at HEAD (requires a rebuild — the
central verifier runs the procedure above). The "before" direction is recorded
in the plan's brick-progress table (RC-E part 1: polymorphic `simp only`
1/10 → 7/10 on one binary, A/B under `import Init`).

## Meta-teeth already executable without a rebuild

These perturbations fail the gate TODAY with no Rust mutation, and demonstrate
the fail-closed integrity properties:

- Delete (or add) one probe from any fixture without touching MANIFEST.json →
  `…=failed reason=fixture-manifest-integrity` (declaration mismatch, and the
  denominator check refuses a probe count ≠ 131/127).
- Replace a fixture's `import Init` header with a blank line →
  `…=failed reason=fixture-manifest-integrity` (builtin-prelude fixtures are
  rejected by the gate script itself).
- Point `CLEAN_BIN` at a binary whose import path cannot resolve the Init
  `.olean`s → the per-file term-mode canary (`List.reverse_reverse`, absent
  from every builtin/stub prelude) fails and the gate exits 1.
