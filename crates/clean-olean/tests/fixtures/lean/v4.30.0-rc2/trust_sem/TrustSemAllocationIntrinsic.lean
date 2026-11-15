/-
Original generated Allocate intrinsic at admissible size/alignment and full
finite-capacity memory. These are actual component calls, not a new evaluator.
The raw carrier proves the conditional claim is not vacuous; it is explicitly
not a Machine.new/WF/reachability witness or a current source-refinement claim.
-/
import TrustSemAllocationCapacityRejected

noncomputable section
namespace TrustSem.AllocationCapacity.Intrinsic

private theorem rejected_bind {α β : Type} {tree : SOut α}
    {f : α → SOut β} (h : AllRejected tree) : AllRejected (SOut.bind tree f) := by
  induction h with
  | reject => exact .reject
  | pick hk ih => exact .pick ih
  | predict hk ih => exact .predict ih

private theorem rejected_from_ok {α β : Type} {tree : SOut α} {a : α}
    {f : α → SOut β} (htree : tree = .ok a) (h : AllRejected (f a)) :
    AllRejected (SOut.bind tree f) := by
  rw [htree]
  exact h

theorem memory_wrapper_rejected :
    AllRejected (MRf.BasicMemory.Memory.allocate 5 fullMemory .Heap 1 1) := by
  dsimp only [MRf.BasicMemory.Memory.allocate]
  apply rejected_bind
  exact full_memory_all_rejected

theorem concurrent_wrapper_rejected (memory : MR_ConcurrentMemory)
    (hfull : memory.memory = fullMemory) :
    AllRejected (MRf.ConcurrentMemory.allocate 6 memory .Heap 1 1) := by
  dsimp only [MRf.ConcurrentMemory.allocate]
  apply rejected_bind
  rw [hfull]
  exact memory_wrapper_rejected

abbrev usizeType : MR_Type := .Int ⟨.Unsigned, 8⟩
abbrev arguments : List (MR_Value × MR_Type) := [(.Int 1, usizeType), (.Int 1, usizeType)]
abbrev resultType : MR_Type := .Ptr (.Raw .None)

theorem allocate_intrinsic_rejected (machine : MR_Machine)
    (hfull : machine.mem.memory = fullMemory) :
    AllRejected (MRf.Machine.eval_intrinsic 7 machine .Allocate arguments resultType) := by
  dsimp only [MRf.Machine.eval_intrinsic, resultType]
  have hlen : SInt.beq (SList.len arguments) 2 = true := rfl
  rw [hlen]
  dsimp only [SBool.not]
  have harg0 : SList.index_at arguments 0 = .ok (.Int 1, usizeType) := rfl
  apply rejected_from_ok harg0
  dsimp only []
  have hsize : SSize.from_bytes 1 = some 1 := rfl
  rw [hsize]
  have harg1 : SList.index_at arguments 1 = .ok (.Int 1, usizeType) := rfl
  apply rejected_from_ok harg1
  dsimp only []
  have halign : SAlign.from_bytes 1 = some 1 := rfl
  rw [halign]
  have hmeta : MRf.PtrType.meta_kind 6 (.Raw .None) = .ok .None := rfl
  apply rejected_from_ok hmeta
  dsimp only [SBool.not, MR_PointerMetaKind.beq]
  apply rejected_bind
  exact concurrent_wrapper_rejected machine.mem hfull

def IntrinsicRejectGoal : Prop :=
  ∀ machine : MR_Machine, machine.mem.memory = fullMemory →
    ∀ δ π : List Nat → Nat,
      SOut.runOracle δ π (MRf.Machine.eval_intrinsic 7 machine .Allocate arguments resultType) = .reject

theorem allocate_intrinsic_every_oracle_rejected : IntrinsicRejectGoal := by
  intro machine hfull δ π
  exact all_rejected_runOracle (allocate_intrinsic_rejected machine hfull) δ π

/-- A raw carrier inhabitation witness only. This does not assert program WF,
Machine.new reachability or the Machine.step premise. Intrinsic evaluation does
not inspect these unused program/thread fields before its allocation. -/
def carrierWitness : MR_Machine :=
  ⟨⟨[], ⟨0⟩, [], [], []⟩, ⟨fullMemory, []⟩, ⟨[]⟩, [], 0,
    [], [], [], [], [], (), ()⟩

theorem carrier_has_full_memory : carrierWitness.mem.memory = fullMemory := rfl

def IntrinsicAbortGoal : Prop :=
  ∀ machine : MR_Machine, machine.mem.memory = fullMemory →
    ∀ δ π : List Nat → Nat,
      SOut.runOracle δ π (MRf.Machine.eval_intrinsic 7 machine .Allocate arguments resultType) =
        .ok (.err .Abort, machine)

def IntrinsicFuelGoal : Prop :=
  ∀ machine : MR_Machine, machine.mem.memory = fullMemory →
    ∀ δ π : List Nat → Nat,
      SOut.runOracle δ π (MRf.Machine.eval_intrinsic 7 machine .Allocate arguments resultType) = .fuel

theorem intrinsic_abort_goal_false : ¬ IntrinsicAbortGoal := by
  intro h
  have wrong := h carrierWitness carrier_has_full_memory (fun _ => 0) (fun _ => 0)
  rw [allocate_intrinsic_every_oracle_rejected carrierWitness carrier_has_full_memory
    (fun _ => 0) (fun _ => 0)] at wrong
  cases wrong

theorem intrinsic_fuel_goal_false : ¬ IntrinsicFuelGoal := by
  intro h
  have wrong := h carrierWitness carrier_has_full_memory (fun _ => 0) (fun _ => 0)
  rw [allocate_intrinsic_every_oracle_rejected carrierWitness carrier_has_full_memory
    (fun _ => 0) (fun _ => 0)] at wrong
  cases wrong

theorem intrinsic_zero_fuel_still_fuel (machine : MR_Machine) (δ π : List Nat → Nat) :
    SOut.runOracle δ π (MRf.Machine.eval_intrinsic 0 machine .Allocate arguments resultType) = .fuel := rfl

end TrustSem.AllocationCapacity.Intrinsic

