/- Copyright 2026 Andrew Yates. Apache-2.0.
   Canonical SemR byte-subject claims for Clean's independent reference entry.
   No new source evaluator, machine model or compiler admission theorem. -/
import U64AdditionAudit
namespace SemRU64AdditionConsumer
open SemR SemRU64Addition
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def Decodes (bytes : List Nat) (literal : Nat) : Prop :=
  decode bytes = .ok (module literal)

def Returns (bytes : List Nat) (literal : Nat) : Prop :=
  ∀ input depth : Nat, input < modulus 64 →
    runBlob bytes 0 [.int .u64 input] 3 depth =
      .ok (.ret [.int .u64 ((input + literal) % modulus 64)])

def NoBad (bytes : List Nat) : Prop :=
  ∀ m : Module, decode bytes = .ok m →
    ∀ (input depth : Nat) (initialState : Core), input < modulus 64 →
      start m 0 [.int .u64 input] depth = .ok initialState →
      ¬ BodyViolation m initialState

theorem original_decoded : Decodes originalBytes 7 := original_decodes

theorem original_returns : Returns originalBytes 7 := by
  intro input depth valid
  simp only [runBlob, original_decodes]
  exact congrArg Except.ok (original_return input depth valid)

theorem original_no_bad : NoBad originalBytes := by
  intro m decoded input depth initialState valid started
  rw [original_decodes] at decoded
  cases decoded
  exact original_no_body_violation input depth initialState valid started

end SemRU64AdditionConsumer
