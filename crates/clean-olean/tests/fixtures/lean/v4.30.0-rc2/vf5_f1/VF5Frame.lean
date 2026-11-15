import VF5Call

set_option linter.unusedVariables false

namespace VF5
open SemR

variable {m : Module}

/-- The parts of a machine state a frame-local step leaves alone (the memory
    among them: no frame-local instruction is a memory instruction). -/
def ctxOf (k : Core) : Func × FuncTy × Nat × List Caller × List Nat × Nat × List Cell × Nat × Mem :=
  (k.fn, k.sig, k.depth, k.stack, k.openFrames, k.nextFrame, k.cells, k.nextCell, k.mem)

theorem R_bind_eq_ok {α β : Type} {x : R α} {f : α → R β} {y : β} (h : (x >>= f) = .ok y) :
    ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | ok a => exact ⟨a, rfl, h⟩
  | stop o => exact nomatch h

theorem bindResults_ctx {k k' : Core} {node : Node} {vs : List Val}
    (h : bindResults k node vs = .ok k') : ctxOf k' = ctxOf k := by
  simp only [bindResults] at h
  split at h
  · exact nomatch h
  · cases h; rfl

theorem jump_ctx {pointerBits : Nat} {k k' : Core} {t : Nat} {vs : List Val}
    (h : jump pointerBits k t vs = .ok k') :
    ctxOf k' = ctxOf k := by
  simp only [jump] at h
  split at h
  · exact nomatch h
  · obtain ⟨env, _, h2⟩ := R_bind_eq_ok h
    cases h2; rfl

theorem ofR_cont {x : R Core} {k' : Core} (h : ofR x = .cont k') : x = .ok k' := by
  cases x with
  | ok a => cases h; rfl
  | stop o => exact nomatch h

theorem next_ctx (k : Core) : ctxOf (next k) = ctxOf k := rfl

/-- A frame-local step changes only the block, the position and the values. -/
theorem execNode_local_ctx {m : Module} {k k' : Core} {node : Node}
    (hloc : isLocal node.inst = true) (h : execNode m k node = .cont k') : ctxOf k' = ctxOf k := by
  cases hinst : node.inst <;> simp only [isLocal, hinst, Bool.false_eq_true] at hloc <;>
    simp only [execNode, binopStep, unopStep, overflowStep, icmpStep, constStep, copyStep, selectStep, extractFieldStep, insertFieldStep, bindSlotStep, loadSlotStep, closeFrameStep, assertStep, callStep, brStep, condBrStep, retStep, castStep, switchStep, asBool, assertOn, bindSlotAt, branchOn, callFn, callOn, callSig, callSigned, closeAt, enterFn, loadSlotAt, openedAt, pickOn, returnTo, selectOn, suspend, switchOn, switchable, hinst] at h <;> try (have h := ofR_cont h)
  case binop =>
    obtain ⟨_, _, h⟩ := R_bind_eq_ok h; obtain ⟨_, _, h⟩ := R_bind_eq_ok h
    obtain ⟨_, _, h⟩ := R_bind_eq_ok h; exact (bindResults_ctx h).trans (next_ctx k)
  case unop =>
    obtain ⟨_, _, h⟩ := R_bind_eq_ok h
    obtain ⟨_, _, h⟩ := R_bind_eq_ok h; exact (bindResults_ctx h).trans (next_ctx k)
  case overflow =>
    obtain ⟨_, _, h⟩ := R_bind_eq_ok h; obtain ⟨_, _, h⟩ := R_bind_eq_ok h
    obtain ⟨_, _, h⟩ := R_bind_eq_ok h; exact (bindResults_ctx h).trans (next_ctx k)
  case icmp =>
    obtain ⟨_, _, h⟩ := R_bind_eq_ok h; obtain ⟨_, _, h⟩ := R_bind_eq_ok h
    obtain ⟨_, _, h⟩ := R_bind_eq_ok h; exact (bindResults_ctx h).trans (next_ctx k)
  case const =>
    obtain ⟨_, _, h⟩ := R_bind_eq_ok h; exact (bindResults_ctx h).trans (next_ctx k)
  case copy =>
    obtain ⟨_, _, h⟩ := R_bind_eq_ok h; obtain ⟨_, _, h⟩ := R_bind_eq_ok h
    exact (bindResults_ctx h).trans (next_ctx k)
  case select =>
    obtain ⟨_, _, h⟩ := R_bind_eq_ok h; obtain ⟨_, _, h⟩ := R_bind_eq_ok h
    obtain ⟨_, _, h⟩ := R_bind_eq_ok h; obtain ⟨_, _, h⟩ := R_bind_eq_ok h
    obtain ⟨_, _, h⟩ := R_bind_eq_ok h; obtain ⟨_, _, h⟩ := R_bind_eq_ok h
    split at h
    · exact (bindResults_ctx h).trans (next_ctx k)
    · exact (bindResults_ctx h).trans (next_ctx k)
    · exact nomatch h
  case extractField =>
    obtain ⟨_, _, h⟩ := R_bind_eq_ok h; obtain ⟨_, _, h⟩ := R_bind_eq_ok h
    exact (bindResults_ctx h).trans (next_ctx k)
  case insertField =>
    obtain ⟨_, _, h⟩ := R_bind_eq_ok h; obtain ⟨_, _, h⟩ := R_bind_eq_ok h
    obtain ⟨_, _, h⟩ := R_bind_eq_ok h; exact (bindResults_ctx h).trans (next_ctx k)
  case nullPtr => exact (bindResults_ctx h).trans (next_ctx k)
  case unreachable => exact nomatch h
  case assert =>
    obtain ⟨_, _, h⟩ := R_bind_eq_ok h; obtain ⟨_, _, h⟩ := R_bind_eq_ok h
    split at h
    · cases h; rfl
    · obtain ⟨_, _, h⟩ := R_bind_eq_ok h; exact nomatch h
    · exact nomatch h
  case br =>
    obtain ⟨_, _, h⟩ := R_bind_eq_ok h; exact jump_ctx h
  case cast =>
    obtain ⟨_, _, h⟩ := R_bind_eq_ok h; obtain ⟨_, _, h⟩ := R_bind_eq_ok h
    exact (bindResults_ctx h).trans (next_ctx k)
  case switch =>
    obtain ⟨_, _, h⟩ := R_bind_eq_ok h; obtain ⟨_, _, h⟩ := R_bind_eq_ok h
    split at h
    · obtain ⟨_, _, h⟩ := R_bind_eq_ok h
      split at h
      · obtain ⟨_, _, h⟩ := R_bind_eq_ok h; exact jump_ctx h
      · obtain ⟨_, _, h⟩ := R_bind_eq_ok h; exact jump_ctx h
    · obtain ⟨_, _, h⟩ := R_bind_eq_ok h
      split at h
      · obtain ⟨_, _, h⟩ := R_bind_eq_ok h; exact jump_ctx h
      · obtain ⟨_, _, h⟩ := R_bind_eq_ok h; exact jump_ctx h
    · exact nomatch h
  case condBr =>
    obtain ⟨_, _, h⟩ := R_bind_eq_ok h; obtain ⟨_, _, h⟩ := R_bind_eq_ok h
    split at h
    · obtain ⟨_, _, h⟩ := R_bind_eq_ok h; exact jump_ctx h
    · obtain ⟨_, _, h⟩ := R_bind_eq_ok h; exact jump_ctx h
    · exact nomatch h

end VF5
