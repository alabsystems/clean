/- Copyright 2026 Andrew Yates. Apache-2.0.
   Checked byte data and ordinary logical transport. This module depends on
   the original data model, without changing or selecting a decoder policy. -/
import SemR

namespace SemR.DecodeCertificate

/-- A checked data value with an explicit equation to the independently
    expected bytes. An opaque constant of this type remains tied to its data
    by the proof field; opacity supplies no axiom or unverified assertion. -/
structure BoundBytes (expected : List Nat) where
  bytes : List Nat
  equation : bytes = expected

/-- Check a nominal input goal first, then transport to the complete expected
    byte goal. The predicate is supplied by the independent goal owner. -/
theorem from_bound {expected : List Nat} {predicate : List Nat → Prop}
    (input : BoundBytes expected) (proof : predicate input.bytes) :
    predicate expected := by
  rw [input.equation] at proof
  exact proof

/-- A producer may transport a checked concrete derivation to the input's
    nominal goal. Both directions retain the full explicit byte equation. -/
theorem to_bound {expected : List Nat} {predicate : List Nat → Prop}
    (input : BoundBytes expected) (proof : predicate expected) :
    predicate input.bytes := by
  rw [input.equation]
  exact proof

/-- A producer's chunk, link and terminal equations compose only when they
    agree with the independently expected head and suffix. -/
theorem suffix_exact
    {actual head tail expectedHead expectedTail expected : List Nat}
    (actualStep : actual = head ++ tail)
    (headExact : head = expectedHead) (tailExact : tail = expectedTail)
    (expectedStep : expected = expectedHead ++ expectedTail) :
    actual = expected := by
  rw [actualStep, headExact, tailExact, ← expectedStep]

/-- The producer's returned root must also equal its checked suffix chain. -/
theorem trans_exact {root chain expected : List Nat}
    (rootExact : root = chain) (chainExact : chain = expected) :
    root = expected := Eq.trans rootExact chainExact

/-- Independent producer and reader encodings meet through a checked complete
    byte equation. Neither encoding's name or hash can replace that premise. -/
theorem to_bound_from {actual expected : List Nat} {predicate : List Nat → Prop}
    (bytesExact : actual = expected) (input : BoundBytes expected)
    (proof : predicate actual) : predicate input.bytes := by
  rw [bytesExact] at proof
  exact to_bound input proof

end SemR.DecodeCertificate
