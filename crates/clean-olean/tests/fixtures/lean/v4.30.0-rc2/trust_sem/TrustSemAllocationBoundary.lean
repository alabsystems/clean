/-
Allocation boundary of the original generated MiniRust BasicMemory instance.

These are proofs about MRf.BasicMemory.allocate, not a new evaluator or a proof
of the translator. The original generated MiniRust cohort is retained unchanged.
The raw request with alignment 2^64 has no first in-range aligned address. It is
not asserted to be an admissible Rust layout. Therefore a proof over arbitrary
raw records cannot replace the reachable-state/layout invariant needed by RM1.
The zero-oracle counterexample does not establish absence of every behavior.
-/
import MiniRust

noncomputable section
namespace TrustSem.AllocationBoundary

def emptyMemory : MR_BasicMemory := ⟨[], ()⟩

def UnitAlignmentGoal : Prop :=
  SOut.runOracle (fun _ => 0) (fun _ => 0)
    (MRf.BasicMemory.allocate 4 emptyMemory .Heap 0 1 () ()) =
  .ok (.ok ⟨1, some (⟨0⟩, ())⟩,
    ⟨[⟨[], 1, 1, .Heap, true, ()⟩], ()⟩)

/-- Original generated operation, including its complete updated memory. -/
theorem unit_alignment_allocates : UnitAlignmentGoal := rfl

/-- Deliberately false: the operation allocated address 1, not address 2. -/
def WrongAddressGoal : Prop :=
  SOut.runOracle (fun _ => 0) (fun _ => 0)
    (MRf.BasicMemory.allocate 4 emptyMemory .Heap 0 1 () ()) =
  .ok (.ok ⟨2, some (⟨0⟩, ())⟩,
    ⟨[⟨[], 1, 1, .Heap, true, ()⟩], ()⟩)

/-- Deliberately false: the returned pointer cannot erase the new allocation. -/
def WrongMemoryGoal : Prop :=
  SOut.runOracle (fun _ => 0) (fun _ => 0)
    (MRf.BasicMemory.allocate 4 emptyMemory .Heap 0 1 () ()) =
  .ok (.ok ⟨1, some (⟨0⟩, ())⟩, emptyMemory)

/-- The requested size is target-valid; it does not imply allocation room. -/
theorem zero_size_is_valid : MRf.x86_64.Target.valid_size 3 0 = .ok true := rfl

def AddressSpaceAlignmentGoal : Prop :=
  SOut.runOracle (fun _ => 0) (fun _ => 0)
    (MRf.BasicMemory.allocate 4 emptyMemory .Heap 0 18446744073709551616 () ()) =
    .reject

/-- Exact original computed refusal, distinct from fuel, UB and divergence. -/
theorem address_space_alignment_rejected_run : AddressSpaceAlignmentGoal := rfl

/-- The original operation cannot universally promise success on raw requests. -/
def RawZeroSizeAlwaysAllocates : Prop :=
  ∀ align : Int, ∃ pointer memory,
    SOut.runOracle (fun _ => 0) (fun _ => 0)
      (MRf.BasicMemory.allocate 4 emptyMemory .Heap 0 align () ()) =
      .ok (.ok pointer, memory)

theorem raw_zero_size_always_allocates_false : ¬ RawZeroSizeAlwaysAllocates := by
  intro h
  obtain ⟨pointer, memory, hp⟩ := h 18446744073709551616
  rw [show SOut.runOracle (fun _ => 0) (fun _ => 0)
    (MRf.BasicMemory.allocate 4 emptyMemory .Heap 0 18446744073709551616 () ()) = .reject
      from address_space_alignment_rejected_run] at hp
  cases hp

/-- Fuel is a disclosed interpreter outcome, never a rejected resolution. -/
theorem zero_fuel_remains_fuel (align : Int) :
    SOut.runOracle (fun _ => 0) (fun _ => 0)
      (MRf.BasicMemory.allocate 0 emptyMemory .Heap 0 align () ()) = .fuel := rfl

def ZeroFuelGoal : Prop :=
  ∀ align : Int, SOut.runOracle (fun _ => 0) (fun _ => 0)
    (MRf.BasicMemory.allocate 0 emptyMemory .Heap 0 align () ()) = .fuel

/-- Deliberately false: spending call-depth fuel does not reject a choice. -/
def FuelWasRejectedGoal : Prop :=
  ∀ align : Int, SOut.runOracle (fun _ => 0) (fun _ => 0)
    (MRf.BasicMemory.allocate 0 emptyMemory .Heap 0 align () ()) = .reject

/-- The address-domain part of the request invariant: the allocator's rounded
first address and one distribution index must name a positive in-range address.
For nonzero sizes and occupied memory, end bounds and nonoverlap are additionally
required. This definition alone is not a whole-machine invariant. -/
def ZeroSizeAddressRoom (align : Int) : Prop :=
  ∃ q : Int, SInt.div_ceil 1 align = .ok q ∧
    ∃ i : Nat, 0 < (q + Int.ofNat i) * align ∧
      (q + Int.ofNat i) * align < 18446744073709551616

theorem unit_alignment_has_room : ZeroSizeAddressRoom 1 :=
  ⟨1, rfl, 0, by decide, by decide⟩

theorem address_space_alignment_has_no_room :
    ¬ ZeroSizeAddressRoom 18446744073709551616 := by
  intro ⟨q, hq, i, _, hbound⟩
  have hquot : SInt.div_ceil 1 18446744073709551616 = .ok 1 := rfl
  rw [hquot] at hq
  cases hq
  have hi : 0 ≤ Int.ofNat i := Int.natCast_nonneg i
  omega

private theorem bind_ok {α β : Type} (a : α) (f : α → SOut β) :
    (SOut.ok a).bind f = f a := rfl

/-- A general fact about the same choice primitive used by the allocator. -/
theorem choose_no_candidates {σ : Type} (d : SIntDistribution)
    (pred : Int → σ → SOut (Bool × σ)) (s : σ) (q : Int)
    (hq : SInt.div_ceil d.start d.divisor = .ok q)
    (hb : ∀ i : Nat, SInt.blt ((q + Int.ofNat i) * d.divisor) d.«end» = false) :
    SPick.choose d pred s = .pick (fun _ => .reject) := by
  unfold SPick.choose
  rw [hq, bind_ok]
  exact congrArg SOut.pick (funext fun i => by rw [hb i])

/-- With alignment equal to the finite address limit, every candidate is out of
range regardless of the predicate or memory state. The required room invariant
must supply a candidate strictly below the limit. -/
theorem address_space_alignment_has_no_candidates {σ : Type}
    (pred : Int → σ → SOut (Bool × σ)) (s : σ) :
    SPick.choose ⟨1, 18446744073709551616, 18446744073709551616⟩ pred s =
      .pick (fun _ => .reject) := by
  apply choose_no_candidates _ _ _ 1 (by rfl)
  intro i
  apply decide_eq_false
  have hi : 0 ≤ Int.ofNat i := Int.natCast_nonneg i
  change ¬ ((1 + Int.ofNat i) * (18446744073709551616 : Int) < 18446744073709551616)
  omega

end TrustSem.AllocationBoundary
