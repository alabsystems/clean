# HX-Seed Provenance

This file records who designed each HX-Seed target, when, with what
intent, and what the novelty argument is. Required by §Phase 1.5.4 of
the buildout plan.

## HX-Seed-0 — `twists_le_length`

| Field | Value |
|---|---|
| Designed on | 2026-05-22 |
| Designer | Andrew Yates (with Claude Opus 4.7 assistance) |
| Mini-domain | `Mathbot.HX.Seed.ChainBraid` (rope-like recursive structures with twist counting) |
| Difficulty class | `compose_2_lemmas` (induction motive + numeric inequality) |
| Mathlib equivalent | None found. ChainBraid is not isomorphic to `List`, `Nat`, `Tree`, or any other catalogued Mathlib inductive. |
| Novelty argument | The `twist` constructor takes two child braids and increments twist count by 1; the proof requires combining IH on both children and then a numeric bound. This shape is not directly memorized via standard Mathlib lemma names. |
| Canonical proof location | `~/mathbot-hx-private/Mathbot/HX/Seed/Proofs.lean` (gitignored, outside the public repo) |
| Canonical proof shape | Induction on `b`; `twist` case uses both IHs plus `mathverse` |
| Expected adversarial failure mode | Worker hallucinates a Mathlib lemma name (e.g. `Nat.le_add_right`) that doesn't apply to ChainBraid; worker writes `simp` and gives up; worker uses tactic combinators that don't elaborate. |
| Human baseline | 3-5 minutes for a Lean-fluent reader who knows the statement. |

## Phase 0 status

HX-Probe-0 and HX-Probe-1 are **early-signal targets**: they exist to
give Phase 0 a real go/no-go datapoint. Neither is under the
second-mathematician-review gate of §Phase 1.5.4. Both are marked
`not_scored` and will be retired or upgraded during Phase 1.5.

Round-5 review confirmed HX-Probe-0 falls to `mathverse` after one
`simp`; the model contribution was tactic selection, not composition.
HX-Probe-1 was added in response: its bound (`2^maxTwists - 1`) is
outside mathverse's decidable fragment and forces composition of
`Nat.pow_le_pow_right`, `Nat.le_max_left/right`, a power-arithmetic
helper, and final discharge.

## HX-Probe-1 — `twists_le_pow_maxTwists`

| Field | Value |
|---|---|
| Designed on | 2026-05-22 |
| Designer | Andrew Yates (with Claude Opus 4.7 assistance), in response to round-5 reviews from codex/claude calling HX-Probe-0 "shallow" |
| Mini-domain | Same `Mathbot.HX.Seed.ChainBraid` with a new `maxTwists` recursion (`max` at twist nodes instead of `+`) |
| Difficulty class | `compose_3_5_lemmas` (Nat.pow_le_pow_right + Nat.le_max_left/right + Nat.pow_succ + Nat-subtraction reasoning) |
| Mathlib equivalent | None — the function `maxTwists` and the bound `2^x - 1` together form a non-standard pairing |
| Novelty argument | `2^x - 1` puts the bound outside mathverse's decidable fragment. `max` requires case analysis. The natural proof uses a `< 2^x` strengthening before subtracting. |
| Canonical proof location | `~/mathbot-hx-private/Mathbot/HX/Seed/Proofs.lean` (gitignored, outside the public repo) |
| Canonical proof shape | (a) strengthen to `twists < 2^maxTwists`, (b) induction with IH chaining through `Nat.pow_le_pow_right` for the twist case, (c) `2^(n+1) = 2^n + 2^n` rewrite, (d) `mathverse` discharges the final linear inequality |
| Expected adversarial failure mode | Worker tries `mathverse` directly and fails; worker doesn't strengthen to `<` and gets stuck on Nat subtraction; worker tries `decide` on a non-decidable goal. |
| Human baseline | 10-15 minutes for a Lean-fluent reader. |
