/- Checked claim controls for the actual Core/function observation boundary.
   Wrong claims are DEFINITIONS of propositions, never axioms or theorems.
   The reader must reject the original proof at each changed proposition. -/
import TrustSemFunction
noncomputable section
namespace TrustSemFunctionCheck
open SemR MiniRustU64Function MiniRustU64Execution MiniRustU64Return MiniRustU64Step
  TrustSemFunction
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def rightAssign : Prop :=
  ∀ (fuel : Nat) (program : MR_Program)
    (base : MR_Machine) (caller : MR_StackFrame)
    (literal : Nat) (action : MR_StackPopAction)
    (world : List MR_Allocation) (retAddr argAddr n : Nat)
    (retBytes : List MR_AbstractByte) (oldAccesses : List MR_Access)
    (retLength : retBytes.length = 8) (retAligned : retAddr % 8 = 0)
    (argAligned : argAddr % 8 = 0) (valid : n < modulus 64)
    (literalValid : literal < modulus 64),
    TrustSem.miniRustStep (fuel + 50) program
      (some (active base caller
        (frame literal (ptr world.length (Int.ofNat retAddr))
          (ptr (world.length + 1) (Int.ofNat argAddr)) action 0)
        (cells world retAddr argAddr retBytes n oldAccesses))) =
    oneThreadChoice ([], .inl (some (active base caller
      (frame literal (ptr world.length (Int.ofNat retAddr))
        (ptr (world.length + 1) (Int.ofNat argAddr)) action 1)
      (cells world retAddr argAddr (u64bytes ((n + literal) % modulus 64)) n
        [⟨.Load, .None, Int.ofNat argAddr, 8⟩, ⟨.Store, .None, Int.ofNat retAddr, 8⟩]))))

def wrongAssignPc : Prop :=
  ∀ (fuel : Nat) (program : MR_Program)
    (base : MR_Machine) (caller : MR_StackFrame)
    (literal : Nat) (action : MR_StackPopAction)
    (world : List MR_Allocation) (retAddr argAddr n : Nat)
    (retBytes : List MR_AbstractByte) (oldAccesses : List MR_Access)
    (retLength : retBytes.length = 8) (retAligned : retAddr % 8 = 0)
    (argAligned : argAddr % 8 = 0) (valid : n < modulus 64)
    (literalValid : literal < modulus 64),
    TrustSem.miniRustStep (fuel + 50) program
      (some (active base caller
        (frame literal (ptr world.length (Int.ofNat retAddr))
          (ptr (world.length + 1) (Int.ofNat argAddr)) action 0)
        (cells world retAddr argAddr retBytes n oldAccesses))) =
    oneThreadChoice ([], .inl (some (active base caller
      (frame literal (ptr world.length (Int.ofNat retAddr))
        (ptr (world.length + 1) (Int.ofNat argAddr)) action 0)
      (cells world retAddr argAddr (u64bytes ((n + literal) % modulus 64)) n
        [⟨.Load, .None, Int.ofNat argAddr, 8⟩, ⟨.Store, .None, Int.ofNat retAddr, 8⟩]))))

def rightReturn : Prop :=
  ∀ (fuel : Nat) (program : MR_Program)
    (base : MR_Machine) (caller : MR_StackFrame)
    (literal : Nat) (next : MR_BbName) (before after : List MR_Allocation)
    (callerAddr retAddr argAddr value n : Nat)
    (callerBytes : List MR_AbstractByte) (oldAccesses : List MR_Access)
    (callerLength : callerBytes.length = 8) (callerAligned : callerAddr % 8 = 0)
    (retAligned : retAddr % 8 = 0) (valid : value < modulus 64),
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
        [⟨.Load, .None, Int.ofNat retAddr, 8⟩, ⟨.Store, .None, Int.ofNat callerAddr, 8⟩]))))

def wrongReturnRetirement : Prop :=
  ∀ (fuel : Nat) (program : MR_Program)
    (base : MR_Machine) (caller : MR_StackFrame)
    (literal : Nat) (next : MR_BbName) (before after : List MR_Allocation)
    (callerAddr retAddr argAddr value n : Nat)
    (callerBytes : List MR_AbstractByte) (oldAccesses : List MR_Access)
    (callerLength : callerBytes.length = 8) (callerAligned : callerAddr % 8 = 0)
    (retAligned : retAddr % 8 = 0) (valid : value < modulus 64),
    TrustSem.miniRustStep (fuel + 50) program
      (some (active base caller
        (frame literal
          (ptr (callerWorld before after callerAddr callerBytes).length (Int.ofNat retAddr))
          (ptr ((callerWorld before after callerAddr callerBytes).length + 1) (Int.ofNat argAddr))
          (.BackToCaller (some next) none (ptr before.length (Int.ofNat callerAddr))) 1)
        (cells (callerWorld before after callerAddr callerBytes)
          retAddr argAddr (u64bytes value) n oldAccesses))) =
    oneThreadChoice ([], .inl (some (single base [(caller.set_next_block next).set_next_stmt 0]
      (cells (callerWorld before after callerAddr (u64bytes value))
        retAddr argAddr (u64bytes value) n
        [⟨.Load, .None, Int.ofNat retAddr, 8⟩, ⟨.Store, .None, Int.ofNat callerAddr, 8⟩]))))

def rightScheduler : Prop :=
  ∀ result : SRes MR_TerminationInfo Unit × MR_Machine,
    project (oneThreadChoice result) = oneThreadChoice (projectResult result)

def wrongScheduler : Prop :=
  ∀ result : SRes MR_TerminationInfo Unit × MR_Machine,
    project (oneThreadChoice result) = .predict (fun index =>
      match index with | 0 => .ok (projectResult result) | _ + 1 => .reject)

def rightTerminal : Prop :=
  ∀ (termination : MR_TerminationInfo) (before after : MR_Machine),
    projectResult (.err termination, before) = ([], .inr termination) ∧
      projectResult (.err termination, before) = projectResult (.err termination, after)

def wrongTerminal : Prop :=
  ∀ (termination : MR_TerminationInfo) (before after : MR_Machine),
    projectResult (.err termination, before) = ([], .inl (some before)) ∧
      projectResult (.err termination, before) = projectResult (.err termination, after)

/-- Concrete complete base data makes the universal profile's state premises
    inhabited; it is NOT a whole-program Machine.new reachability assertion. -/
def base : MR_Machine :=
  { prog := ⟨[(⟨0⟩, function 7)], ⟨0⟩, [], [], []⟩
    mem := ⟨⟨[], ()⟩, []⟩, intptrcast := ⟨[]⟩
    threads := [], active_thread := 0, synchronized_threads := []
    locks := [], global_ptrs := [], fn_ptrs := [], vtable_ptrs := []
    stdout := (), stderr := () }

def caller : MR_StackFrame := frame 7 (ptr 0 8192) (ptr 1 12288) .BottomOfStack 0

/-- An inhabited actual generated step under the Core wrapper, with the
    entire continued endpoint and invalid schedule branches retained. -/
theorem inhabited_assignment_observation :
    TrustSem.miniRustStep 50 base.prog
      (some (active base caller (frame 7 (ptr 0 8192) (ptr 1 12288) .BottomOfStack 0)
        (cells [] 8192 12288 (u64bytes 0) 1 []))) =
    oneThreadChoice ([], .inl (some (active base caller
      (frame 7 (ptr 0 8192) (ptr 1 12288) .BottomOfStack 1)
      (cells [] 8192 12288 (u64bytes 8) 1
        [⟨.Load, .None, 12288, 8⟩, ⟨.Store, .None, 8192, 8⟩])))) := by
  exact core_assign 0 base.prog base caller 7 .BottomOfStack [] 8192 12288 1
    (u64bytes 0) [] (u64bytes_length 0) (by decide) (by decide) (by decide) (by decide)

end TrustSemFunctionCheck
