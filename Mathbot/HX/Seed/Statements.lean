import Mathbot.HX.Seed.Definitions

/-!
# Mathbot HX-Seed: held-out theorem statements (Phase 0 — single seed)

These statements use the ChainBraid mini-domain defined in
`Mathbot.HX.Seed.Definitions`. Proofs are deliberately replaced by
`sorry` in the public repo. The canonical proofs live outside the
public tree at `~/mathbot-hx-private/Mathbot/HX/Seed/Proofs.lean`
and are NEVER mounted into the worker sandbox during bakeoff runs.

A `mathbot hx audit` step asserts that every theorem body in this
file is literally `sorry`. If the build ever passes a real body
through, the audit fails and the run is rejected.

## HX-Seed-0 — Phase 0 early-signal target

The single Phase 0 target: prove that the number of twist nodes in
any `ChainBraid` is bounded above by its total length. Standard
proof: induction on the braid structure, IH chained through the
twist case, finishing with linear arithmetic on Nat.

Expected difficulty: `compose_2_lemmas` (induction motive + numeric
inequality). Solvable by `induction b with | twist a b iha ihb =>
... | ... => ...` followed by `omega` or explicit Nat reasoning.
-/

set_option autoImplicit false

namespace Mathbot.HX.Seed

/-- **HX-Probe-0**: the twist count of any ChainBraid is at most its
    total length. This bound is tight (achieved when every node is a
    twist), but the proof requires induction with IH chaining
    through the twist case.

    **Probe note**: post-`simp` this falls to `omega`. The harder
    probe is `twists_le_pow_maxTwists` below. -/
theorem twists_le_length : ∀ b : ChainBraid, b.twists ≤ b.length := by
  sorry

/-- **HX-Probe-1**: omega-defeating variant. The twist count is at most
    `2 ^ maxTwists - 1`, which puts the bound outside omega's decidable
    fragment by virtue of `Nat.pow` and the truncating Nat subtraction.
    The proof requires:
    - Induction on the braid.
    - `Nat.pow_le_pow_*` lemma selection.
    - Case analysis on the `max` in `maxTwists`.
    - Reasoning about Nat subtraction (which truncates at zero). -/
theorem twists_le_pow_maxTwists :
    ∀ b : ChainBraid, b.twists ≤ 2 ^ b.maxTwists - 1 := by
  sorry

/-- **HX-Probe-2**: composition test. The custom `weight` function
    MULTIPLIES at twist nodes, so a `2^sides ≤ weight` bound forces
    the prover to combine `Nat.pow_add` (to split `2^(sides_a +
    sides_b)` into `2^sides_a * 2^sides_b`) with `Nat.mul_le_mul`
    (to chain the two induction hypotheses through the product).

    Per round-6 reviewer guidance:
    - codex r6 §3: unfamiliar local structure with no Nat-library-
      shaped goal, at least one composition not summarizable by a
      single canonical lemma name.
    - claude r6 §3: non-distributive custom invariant requiring
      step-by-step composition.
    - gemini r6 §3: novel local definition with zero pre-training
      representation; proof must depend entirely on local lemmas.

    Defeats `omega` (multiplication is not Presburger). Defeats
    pure `simp [pow_le_pow_right, le_max_left]`-style lemma chains
    (the goal has neither pow_le_pow nor max in it). -/
theorem pow_sides_le_weight : ∀ b : ChainBraid, 2 ^ b.sides ≤ b.weight := by
  sorry

end Mathbot.HX.Seed
