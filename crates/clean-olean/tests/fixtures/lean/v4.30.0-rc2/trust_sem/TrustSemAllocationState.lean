/-
State-preservation obligations over the ORIGINAL generated BasicMemory allocator.
This imports the old generated model unchanged. It does not assert that the
repaired source fork has been imported, or that every Machine.step preserves a
whole-program invariant. Successful component transitions are stated with their
complete memory and provenance, rather than just a scalar return value.
-/
import TrustSemAllocationSearch

noncomputable section
namespace TrustSem.AllocationState

open TrustSem.AllocationSearch

def addressLimit : Int := 18446744073709551616

def AllocationLayout (allocation : MR_Allocation) : Prop :=
  0 < allocation.addr ∧ 0 < allocation.align ∧
    allocation.addr % allocation.align = 0 ∧
    allocation.addr + SList.len allocation.data < addressLimit

def LiveSeparated (left right : MR_Allocation) : Prop :=
  left.live = true → right.live = true →
    MRf.Allocation.overlaps 3 left right.addr (SList.len right.data) = .ok false

/-- A memory component invariant. Whole-machine reachability additionally needs
the program, threads, stacks, layouts and every other memory transition. -/
def MemoryLayout (memory : MR_BasicMemory) : Prop :=
  (∀ allocation, allocation ∈ memory.allocations → AllocationLayout allocation) ∧
    memory.allocations.Pairwise LiveSeparated

theorem empty_memory_layout : MemoryLayout ⟨[], ()⟩ := by
  constructor
  · intro allocation h
    cases h
  · exact List.Pairwise.nil

theorem original_memory_new : MRf.BasicMemory.new 1 = .ok ⟨[], ()⟩ := rfl

private theorem pairwise_append_fresh (allocations : List MR_Allocation)
    (fresh : MR_Allocation) (hpair : allocations.Pairwise LiveSeparated)
    (hsep : ∀ old, old ∈ allocations → LiveSeparated old fresh) :
    (allocations ++ [fresh]).Pairwise LiveSeparated := by
  induction allocations with
  | nil => exact List.Pairwise.cons (by simp) List.Pairwise.nil
  | cons first rest ih =>
    cases hpair with
    | cons hfirst hrest =>
      apply List.Pairwise.cons
      · intro allocation hmem
        rcases List.mem_append.mp hmem with hmem | hmem
        · exact hfirst allocation hmem
        · have heq : allocation = fresh := by simpa using hmem
          subst allocation
          exact hsep first (by simp)
      · exact ih hrest (fun old hmem => hsep old (by simp [hmem]))

theorem append_preserves_memory_layout (memory : MR_BasicMemory) (fresh : MR_Allocation)
    (hmem : MemoryLayout memory) (hfresh : AllocationLayout fresh)
    (hsep : ∀ old, old ∈ memory.allocations → LiveSeparated old fresh) :
    MemoryLayout ⟨memory.allocations ++ [fresh], ()⟩ := by
  constructor
  · intro allocation hmember
    rcases List.mem_append.mp hmember with hmember | hmember
    · exact hmem.1 allocation hmember
    · have heq : allocation = fresh := by simpa using hmember
      subst allocation
      exact hfresh
  · exact pairwise_append_fresh memory.allocations fresh hmem.2 hsep

theorem original_any_no_overlap (allocations : List MR_Allocation) (address size : Int)
    (hclear : ∀ allocation, allocation ∈ allocations → allocation.live = true →
      MRf.Allocation.overlaps 3 allocation address size = .ok false) :
    SList.anyS allocations
      (fun (allocation : MR_Allocation) (_ : Unit) =>
        match allocation.live with
        | true => SOut.bind (MRf.Allocation.overlaps 3 allocation address size)
          (fun overlaps => .ok (overlaps, ()))
        | false => .ok (false, ())) () = .ok (false, ()) := by
  induction allocations with
  | nil => rfl
  | cons first rest ih =>
    have hrest := ih (fun allocation hmember hlive =>
      hclear allocation (by simp [hmember]) hlive)
    dsimp only [SList.anyS]
    cases hlive : first.live with
    | false => simpa only [hlive, SOut.bind] using hrest
    | true =>
      dsimp only
      rw [hclear first (by simp) hlive]
      simpa only [SOut.bind] using hrest

private theorem bind_ok {α β : Type} (value : α) (next : α → SOut β) :
    (SOut.ok value).bind next = next value := rfl

private theorem bind_pick {α β : Type} (choice : Nat → SOut α) (next : α → SOut β) :
    (SOut.pick choice).bind next = .pick (fun i => (choice i).bind next) := rfl

private theorem runOracle_pick {α : Type} (δ π : List Nat → Nat) (choice : Nat → SOut α) :
    SOut.runOracle δ π (.pick choice) =
      SOut.runOracle (fun h => δ (δ [] :: h)) (fun h => π (δ [] :: h)) (choice (δ [])) := rfl

private theorem append_eq {α : Type} (left right : List α) :
    SList.appendL left right = left ++ right := by
  induction left with
  | nil => rfl
  | cons first rest ih => simpa only [SList.appendL, List.cons_append] using congrArg (List.cons first) ih

theorem original_allocation_exact_state (memory : MR_BasicMemory)
    (kind : MR_AllocationKind) (size alignment q address : Int)
    (data : List MR_AbstractByte) (δ π : List Nat → Nat)
    (hvalid : MRf.x86_64.Target.valid_size 3 size = .ok true)
    (hquot : SInt.div_ceil 1 alignment = .ok q)
    (hchosen : address = (q + Int.ofNat (δ [])) * alignment)
    (hpositive : 0 < address) (hbound : address < addressLimit)
    (haligned : SAlign.is_aligned alignment address = .ok true)
    (hend : SInt.in_bounds (address + size) .Unsigned 8 = .ok true)
    (hclear : ∀ allocation, allocation ∈ memory.allocations → allocation.live = true →
      MRf.Allocation.overlaps 3 allocation address size = .ok false)
    (hdata : SList.from_elem MR_AbstractByte.Uninit size = .ok data) :
    SOut.runOracle δ π (MRf.BasicMemory.allocate 4 memory kind size alignment () ()) =
      .ok (.ok ⟨address, some (⟨SList.len memory.allocations⟩, ())⟩,
        ⟨memory.allocations ++ [⟨data, address, alignment, kind, true, ()⟩], ()⟩) := by
  dsimp only [MRf.BasicMemory.allocate]
  rw [hvalid]
  simp only [bind_ok, SBool.not]
  simp only [show MRf.x86_64.PTR_SIZE 3 = .ok 8 from rfl, bind_ok]
  rw [show SInt.pow 2 (SSize.bits 8) = .ok addressLimit from rfl]
  simp only [bind_ok]
  unfold SPick.choose
  rw [hquot]
  simp only [bind_ok, bind_pick, runOracle_pick]
  rw [← hchosen]
  have hbounded : SInt.blt address addressLimit = true := decide_eq_true hbound
  have hpos : SInt.ble address 0 = false := decide_eq_false (by omega)
  rw [hbounded, hpos, haligned]
  simp only [bind_ok]
  rw [hend]
  simp only [bind_ok]
  have hnone := original_any_no_overlap memory.allocations address size hclear
  -- The independently compiled matches use distinct matcher declarations.
  unfold original_any_no_overlap.match_1 at hnone
  unfold SBool.beq.match_1
  rw [hnone]
  simp only [bind_ok]
  rw [hdata]
  simp only [bind_ok, SList.push, append_eq]
  cases memory
  rfl

private theorem repeat_length {α : Type} (value : α) (n : Nat) :
    SList.lenNat (SList.repeatNat value n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [SList.repeatNat, SList.lenNat, ih]

theorem original_fresh_data_length (size : Int) (data : List MR_AbstractByte)
    (hdata : SList.from_elem MR_AbstractByte.Uninit size = .ok data) :
    SList.len data = size := by
  cases size with
  | ofNat n =>
    dsimp only [SList.from_elem] at hdata
    cases hdata
    unfold SList.len
    rw [repeat_length]
  | negSucc n => cases hdata

theorem fitting_append_preserves_layout (memory : MR_BasicMemory) (data : List MR_AbstractByte)
    (kind : MR_AllocationKind) (size alignment address : Int)
    (hmem : MemoryLayout memory) (ha : 0 < alignment)
    (hfit : Fits memory.allocations size alignment addressLimit address)
    (hlen : SList.len data = size) :
    MemoryLayout ⟨memory.allocations ++ [⟨data, address, alignment, kind, true, ()⟩], ()⟩ := by
  apply append_preserves_memory_layout memory _ hmem
  · exact ⟨hfit.1, ha, hfit.2.1, by simpa only [hlen] using hfit.2.2.1⟩
  · intro old hmember hlive _
    change MRf.Allocation.overlaps 3 old address (SList.len data) = .ok false
    rw [hlen]
    exact hfit.2.2.2 old hmember hlive

/-- An actual original allocator transition, retaining its complete result and
component invariant. A fitting candidate is a premise for this success case;
this theorem does not assume that valid layouts always have free space. -/
theorem original_allocation_preserves_layout (memory : MR_BasicMemory)
    (kind : MR_AllocationKind) (size alignment q address : Int)
    (data : List MR_AbstractByte) (δ π : List Nat → Nat)
    (hmem : MemoryLayout memory) (ha : 0 < alignment)
    (hfit : Fits memory.allocations size alignment addressLimit address)
    (hvalid : MRf.x86_64.Target.valid_size 3 size = .ok true)
    (hquot : SInt.div_ceil 1 alignment = .ok q)
    (hchosen : address = (q + Int.ofNat (δ [])) * alignment)
    (haligned : SAlign.is_aligned alignment address = .ok true)
    (hend : SInt.in_bounds (address + size) .Unsigned 8 = .ok true)
    (hdata : SList.from_elem MR_AbstractByte.Uninit size = .ok data) :
    ∃ pointer updated,
      SOut.runOracle δ π (MRf.BasicMemory.allocate 4 memory kind size alignment () ()) =
        .ok (.ok pointer, updated) ∧ MemoryLayout updated := by
  have hlen := original_fresh_data_length size data hdata
  have hnonnegative := original_data_length_nonnegative ⟨data, address, alignment, kind, true, ()⟩
  change 0 ≤ SList.len data at hnonnegative
  rw [hlen] at hnonnegative
  have hbound : address < addressLimit := by have := hfit.2.2.1; omega
  refine ⟨⟨address, some (⟨SList.len memory.allocations⟩, ())⟩,
    ⟨memory.allocations ++ [⟨data, address, alignment, kind, true, ()⟩], ()⟩, ?_, ?_⟩
  · exact original_allocation_exact_state memory kind size alignment q address data δ π
      hvalid hquot hchosen hfit.1 hbound haligned hend hfit.2.2.2 hdata
  · exact fitting_append_preserves_layout memory data kind size alignment address hmem ha hfit hlen

def zeroReservation : MR_Allocation := ⟨[], 2, 1, .Stack, true, ()⟩
def initialMemory : MR_BasicMemory := ⟨[zeroReservation], ()⟩
def extendedMemory : MR_BasicMemory :=
  ⟨[zeroReservation, ⟨[.Uninit, .Uninit], 3, 1, .Heap, true, ()⟩], ()⟩

def OriginalAppendGoal : Prop :=
  SOut.runOracle (fun _ => 2) (fun _ => 0)
    (MRf.BasicMemory.allocate 4 initialMemory .Heap 2 1 () ()) =
      .ok (.ok ⟨3, some (⟨1⟩, ())⟩, extendedMemory)

theorem original_append_state : OriginalAppendGoal := by
  apply original_allocation_exact_state initialMemory .Heap 2 1 1 3
    [.Uninit, .Uninit] (fun _ => 2) (fun _ => 0)
    (by rfl) (by rfl) (by rfl) (by decide) (by decide) (by rfl) (by rfl)
  · intro allocation hmember _
    have heq : allocation = zeroReservation := by simpa only [initialMemory, List.mem_cons,
      List.not_mem_nil, or_false] using hmember
    subst allocation
    rfl
  · rfl

def ErasedPriorAllocationGoal : Prop :=
  SOut.runOracle (fun _ => 2) (fun _ => 0)
    (MRf.BasicMemory.allocate 4 initialMemory .Heap 2 1 () ()) =
      .ok (.ok ⟨3, some (⟨1⟩, ())⟩,
        ⟨[⟨[.Uninit, .Uninit], 3, 1, .Heap, true, ()⟩], ()⟩)

theorem erased_prior_allocation_goal_false : ¬ ErasedPriorAllocationGoal := by
  intro h
  have hactual := original_append_state
  unfold OriginalAppendGoal at hactual
  unfold ErasedPriorAllocationGoal at h
  rw [hactual] at h
  have hcount := congrArg
    (fun result : SOut (SRes MR_TerminationInfo MR_ThinPointer × MR_BasicMemory) =>
      match result with | .ok (_, memory) => memory.allocations.length | _ => 0) h
  change 2 = 1 at hcount
  cases hcount

end TrustSem.AllocationState
