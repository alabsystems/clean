-- p20 — CLASS I risk axis (a): the REFUSAL half. The most important probe in
-- the stage-I-1 set.
--
-- PROVES: a `[DecidableEq α]` local in scope is NOT grabbed for a
-- `Decidable (b = b)` goal at an unrelated carrier `β`. The candidate-side
-- match unifies the local's conclusion arguments against the goal's under a
-- pushed metavariable scope and ROLLS BACK on failure, so widening the
-- candidate set does not widen what is ACCEPTED.
--
-- The declaration must still fail, and must still fail with the pre-existing
-- `FailedToSynthesize { class_name: Decidable, … }`, i.e. the diagnostic is
-- unchanged too — a capability-adding change that silently reworded a refusal
-- would make every downstream classifier read differently.
--
-- CONTROL: p19 — the same shape WITH a matching local passes. So this failure
-- is the carrier mismatch and nothing else.
def wrongCarrier {α β : Type} [DecidableEq α] (b : β) : Bool :=
  if b = b then true else false
