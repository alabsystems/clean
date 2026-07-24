/-!
# Mathbot HX-Seed: ChainBraid mini-domain

Custom recursive datatype designed for the held-out (HX) benchmark.
NOT a Mathlib type. Models that have not been trained on this file
must learn the structure and prove the lemmas from the definitions
alone.

The point of inventing a custom type is to make the benchmark resistant
to lemma-name memorization. A model that has memorized `Nat.le_trans`
or `List.length_append` will not have memorized
`Mathbot.HX.Seed.twists_le_length`.

## Provenance

- Designed: 2026-05-22
- Designer: Andrew Yates (with Claude Opus 4.7 assistance)
- Mini-domain: rope-like recursive structures with twist counting
- Novelty argument: ChainBraid is not isomorphic to any existing
  Mathlib inductive; the proof requires induction + IH chaining +
  numeric inequality over a custom-defined invariant.
-/

set_option autoImplicit false

namespace Mathbot.HX.Seed

/-- A `ChainBraid` is an abstract rope-like structure built from
    twists and one-sided extensions. It is intentionally distinct
    from Mathlib's existing tree types. -/
inductive ChainBraid where
  /-- The empty braid. -/
  | none : ChainBraid
  /-- Extend the braid by a one-sided left step. -/
  | left : ChainBraid → ChainBraid
  /-- Extend the braid by a one-sided right step. -/
  | right : ChainBraid → ChainBraid
  /-- Combine two braids with a fresh twist node. -/
  | twist : ChainBraid → ChainBraid → ChainBraid
  deriving Inhabited, Repr

/-- The number of nodes in the braid (including the twist nodes
    and one-sided extensions). -/
def ChainBraid.length : ChainBraid → Nat
  | .none => 0
  | .left b => length b + 1
  | .right b => length b + 1
  | .twist a b => length a + length b + 1

/-- The number of twist nodes in the braid. -/
def ChainBraid.twists : ChainBraid → Nat
  | .none => 0
  | .left b => twists b
  | .right b => twists b
  | .twist a b => twists a + twists b + 1

/-- The number of one-sided (left or right) extension nodes. -/
def ChainBraid.sides : ChainBraid → Nat
  | .none => 0
  | .left b => sides b + 1
  | .right b => sides b + 1
  | .twist a b => sides a + sides b

/-- The maximum twist count along any branch of the braid.

    Used by `HX-Probe-1`. Distinguished from `twists` (which sums all
    twists in the structure) by taking `max` at each twist node
    instead of `+`. This puts proof obligations involving `maxTwists`
    outside the linear-arithmetic fragment that `omega` decides. -/
def ChainBraid.maxTwists : ChainBraid → Nat
  | .none => 0
  | .left b => maxTwists b
  | .right b => maxTwists b
  | .twist a b => Nat.max (maxTwists a) (maxTwists b) + 1

/-- A custom multiplicative weight on the braid.

    Used by `HX-Probe-2`. Designed so that `weight` MULTIPLIES at
    twist nodes (rather than the additive `length`/`twists` or the
    max-based `maxTwists`). The bound `2^sides ≤ weight` then forces
    the prover to combine `Nat.pow_add` and `Nat.mul_le_mul` in the
    twist case — there is no nice Mathlib-canonical lemma that
    chains them, so the prover must compose the proof step by step
    rather than recalling a single named result. -/
def ChainBraid.weight : ChainBraid → Nat
  | .none => 1
  | .left b => weight b * 2
  | .right b => weight b * 2
  | .twist a b => weight a * weight b

end Mathbot.HX.Seed
