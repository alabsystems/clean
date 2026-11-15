/- Canonical Core wrapper ↔ actual generated function-step observation.
   One shared MiniRust import; no new evaluator or successful-execution premise.
   Whole-program Machine.new reachability and source/ABI/licensing stay open. -/
import TrustSem
import MiniRustU64Entry
noncomputable section
namespace TrustSemFunction
open SemR MiniRustU64Function MiniRustU64Execution MiniRustU64Return MiniRustU64Step
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- A raw generated step retains the COMPLETE machine, including memory,
    thread/frame/PC state, accesses and all unrelated fields at every leaf. -/
abbrev FunctionObservation := SOut (SRes MR_TerminationInfo Unit × MR_Machine)

def observe (fuel : Nat) (machine : MR_Machine) : FunctionObservation :=
  MRf.Machine.step fuel machine

/-- The EXISTING whole-program wrapper's projection. Continuing steps retain
    the whole machine. Termination still discards it, exactly as before. -/
def projectResult : SRes MR_TerminationInfo Unit × MR_Machine →
    List Unit × (Option MR_Machine ⊕ MR_TerminationInfo)
  | (.ok _, machine) => ([], .inl (some machine))
  | (.err termination, _) => ([], .inr termination)

def project (observation : FunctionObservation) :
    SOut (List Unit × (Option MR_Machine ⊕ MR_TerminationInfo)) :=
  observation.bind (fun result => .ok (projectResult result))

/-- Unconditional identity of the actual Core entry with the generated step
    plus its existing projection. No run/frame/call equality is assumed. -/
theorem core_step_observation (fuel : Nat) (program : MR_Program) (machine : MR_Machine) :
    TrustSem.miniRustStep fuel program (some machine) = project (observe fuel machine) := by
  unfold TrustSem.miniRustStep project observe
  apply congrArg (fun next => (MRf.Machine.step fuel machine).bind next)
  funext result
  rcases result with ⟨result, next⟩
  cases result <;> rfl

theorem program_step_observation (fuel : Nat) (program : MR_Program) (machine : MR_Machine) :
    (TrustSem.miniRust fuel program).step (some machine) = project (observe fuel machine) :=
  core_step_observation fuel program machine

theorem program_initial_state (fuel : Nat) (program : MR_Program) :
    (TrustSem.miniRust fuel program).init = none := rfl

theorem continued_machine_retained (machine : MR_Machine) :
    projectResult (.ok (), machine) = ([], .inl (some machine)) := rfl

theorem terminal_machine_discarded (termination : MR_TerminationInfo)
    (before after : MR_Machine) :
    projectResult (.err termination, before) = ([], .inr termination) ∧
      projectResult (.err termination, before) = projectResult (.err termination, after) :=
  ⟨rfl, rfl⟩

/-- Projection preserves the actual scheduler tree, including EVERY rejected
    nonzero index. It neither selects index0 nor asserts schedule availability. -/
theorem project_scheduler (result : SRes MR_TerminationInfo Unit × MR_Machine) :
    project (oneThreadChoice result) = oneThreadChoice (projectResult result) := by
  unfold project oneThreadChoice
  apply congrArg SOut.pick
  funext index
  cases index <;> rfl

theorem projected_scheduler_oracle (result : SRes MR_TerminationInfo Unit × MR_Machine)
    (δ π : List Nat → Nat) :
    SOut.runOracle δ π (project (oneThreadChoice result)) =
      match δ [] with | 0 => .ok (projectResult result) | _ + 1 => .reject := by
  rw [project_scheduler]
  exact oneThread_oracle _ δ π

/-- Actual Assign, PC advance and race reset/check, observed through the real
    Core wrapper. All initial world/base fields and every resulting byte/log
    are retained in the complete continued machine. -/
theorem core_assign (fuel : Nat) (program : MR_Program)
    (base : MR_Machine) (caller : MR_StackFrame)
    (literal : Nat) (action : MR_StackPopAction)
    (world : List MR_Allocation) (retAddr argAddr n : Nat)
    (retBytes : List MR_AbstractByte) (oldAccesses : List MR_Access)
    (retLength : retBytes.length = 8) (retAligned : retAddr % 8 = 0)
    (argAligned : argAddr % 8 = 0) (valid : n < modulus 64)
    (literalValid : literal < modulus 64) :
    TrustSem.miniRustStep (fuel + 50) program
      (some (active base caller
        (frame literal (ptr world.length (Int.ofNat retAddr))
          (ptr (world.length + 1) (Int.ofNat argAddr)) action 0)
        (cells world retAddr argAddr retBytes n oldAccesses))) =
    oneThreadChoice ([], .inl (some (active base caller
      (frame literal (ptr world.length (Int.ofNat retAddr))
        (ptr (world.length + 1) (Int.ofNat argAddr)) action 1)
      (cells world retAddr argAddr (u64bytes ((n + literal) % modulus 64)) n
        [⟨.Load, .None, Int.ofNat argAddr, 8⟩, ⟨.Store, .None, Int.ofNat retAddr, 8⟩])))) := by
  rw [core_step_observation]
  unfold observe
  rw [assign_step fuel base caller literal action world retAddr argAddr n retBytes oldAccesses
    retLength retAligned argAligned valid literalValid]
  exact project_scheduler _

/-- Actual Return includes result load, BOTH retired private allocations,
    caller store/jump and race tracking. The Core continuation preserves that
    full endpoint; no terminal-state strengthening or successful-call premise. -/
theorem core_return (fuel : Nat) (program : MR_Program)
    (base : MR_Machine) (caller : MR_StackFrame)
    (literal : Nat) (next : MR_BbName) (before after : List MR_Allocation)
    (callerAddr retAddr argAddr value n : Nat)
    (callerBytes : List MR_AbstractByte) (oldAccesses : List MR_Access)
    (callerLength : callerBytes.length = 8) (callerAligned : callerAddr % 8 = 0)
    (retAligned : retAddr % 8 = 0) (valid : value < modulus 64) :
    TrustSem.miniRustStep (fuel + 50) program
      (some (active base caller
        (frame literal
          (ptr (callerWorld before after callerAddr callerBytes).length (Int.ofNat retAddr))
          (ptr ((callerWorld before after callerAddr callerBytes).length + 1) (Int.ofNat argAddr))
          (.BackToCaller (some next) none (ptr before.length (Int.ofNat callerAddr))) 1)
        (cells (callerWorld before after callerAddr callerBytes)
          retAddr argAddr (u64bytes value) n oldAccesses))) =
    oneThreadChoice ([], .inl (some (single base [(caller.set_next_block next).set_next_stmt 0]
      (retiredCells (callerWorld before after callerAddr (u64bytes value))
        retAddr argAddr value n
        [⟨.Load, .None, Int.ofNat retAddr, 8⟩, ⟨.Store, .None, Int.ofNat callerAddr, 8⟩])))) := by
  rw [core_step_observation]
  unfold observe
  rw [return_step fuel base caller literal next before after callerAddr retAddr argAddr value n
    callerBytes oldAccesses callerLength callerAligned retAligned valid]
  exact project_scheduler _

end TrustSemFunction
