/-
Finite-capacity behavior of the ORIGINAL generated allocator. This source does
not replace MiniRust, reinterpret fuel, or turn rejection into OOM. The source
allocator at current pin d821 has the identical basic.md body as old e866; the
full generated model epoch and Rust/source refinement remain separate premises.
-/
import SemRMiniRust

noncomputable section
namespace TrustSem.AllocationCapacity

def blockSize : Int := 9223372036854775807
def halfSpace : Int := 9223372036854775808
def addressLimit : Int := 18446744073709551616
def blockData : List MR_AbstractByte :=
  SList.repeatNat .Uninit 9223372036854775807

private theorem repeat_length {α : Type} (x : α) (n : Nat) :
    SList.lenNat (SList.repeatNat x n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [SList.repeatNat, SList.lenNat, ih]

theorem block_data_length : SList.len blockData = blockSize := by
  unfold SList.len blockData
  rw [repeat_length]
  rfl

def firstAllocation : MR_Allocation := ⟨blockData, 1, 1, .Heap, true, ()⟩
def secondAllocation : MR_Allocation := ⟨blockData, halfSpace, 1, .Heap, true, ()⟩
def emptyMemory : MR_BasicMemory := ⟨[], ()⟩
def firstMemory : MR_BasicMemory := ⟨[firstAllocation], ()⟩
def fullMemory : MR_BasicMemory := ⟨[firstAllocation, secondAllocation], ()⟩

theorem block_size_valid : MRf.x86_64.Target.valid_size 3 blockSize = .ok true := rfl
theorem requested_size_valid : MRf.x86_64.Target.valid_size 3 1 = .ok true := rfl

theorem first_allocation_size : MRf.Allocation.size 2 firstAllocation = .ok blockSize := by
  change SOut.bind (SOption.unwrap (SSize.from_bytes (SList.len blockData)))
    (fun n => SOut.ok n) = .ok blockSize
  rw [block_data_length]
  rfl

theorem second_allocation_size : MRf.Allocation.size 2 secondAllocation = .ok blockSize := by
  change SOut.bind (SOption.unwrap (SSize.from_bytes (SList.len blockData)))
    (fun n => SOut.ok n) = .ok blockSize
  rw [block_data_length]
  rfl

def FirstAllocationGoal : Prop :=
  SOut.runOracle (fun _ => 0) (fun _ => 0)
    (MRf.BasicMemory.allocate 4 emptyMemory .Heap blockSize 1 () ()) =
    .ok (.ok ⟨1, some (⟨0⟩, ())⟩, firstMemory)

theorem first_allocation_reachable : FirstAllocationGoal := rfl

theorem first_second_disjoint :
    MRf.Allocation.overlaps 3 firstAllocation halfSpace blockSize = .ok false := by
  dsimp only [MRf.Allocation.overlaps]
  rw [first_allocation_size]
  rfl

def SecondAllocationGoal : Prop :=
  SOut.runOracle (fun _ => 9223372036854775807) (fun _ => 0)
    (MRf.BasicMemory.allocate 4 firstMemory .Heap blockSize 1 () ()) =
    .ok (.ok ⟨halfSpace, some (⟨1⟩, ())⟩, fullMemory)

private theorem second_for_data (data fresh : List MR_AbstractByte)
    (hdata : SList.len data = blockSize)
    (hfresh : SList.from_elem MR_AbstractByte.Uninit blockSize = .ok fresh) :
  SOut.runOracle (fun _ => 9223372036854775807) (fun _ => 0)
    (MRf.BasicMemory.allocate 4 ⟨[⟨data, 1, 1, .Heap, true, ()⟩], ()⟩
      .Heap blockSize 1 () ()) =
    .ok (.ok ⟨halfSpace, some (⟨1⟩, ())⟩,
      ⟨[⟨data, 1, 1, .Heap, true, ()⟩,
        ⟨fresh, halfSpace, 1, .Heap, true, ()⟩], ()⟩) := by
  dsimp only [MRf.BasicMemory.allocate, SOut.bind, SBool.not,
    MRf.x86_64.PTR_SIZE, SPick.choose, SOut.runOracle, SList.anyS,
    MRf.x86_64.Target.valid_size, MRf.Allocation.overlaps, MRf.Allocation.size,
    SInt.pow, SSize.bits, SInt.div_ceil, SInt.blt, SInt.ble, SInt.in_bounds,
    SAlign.is_aligned, SOption.unwrap, SSize.from_bytes, SList.push]
  rw [hdata, hfresh]
  rfl

theorem second_allocation_reachable : SecondAllocationGoal :=
  second_for_data blockData blockData block_data_length rfl

theorem first_end_in_bounds :
    SInt.in_bounds (1 + blockSize) .Unsigned 8 = .ok true := rfl
theorem second_end_in_bounds :
    SInt.in_bounds (halfSpace + blockSize) .Unsigned 8 = .ok true := rfl

private theorem size_for_data (data : List MR_AbstractByte) (base : Int)
    (hdata : SList.len data = blockSize) :
    MRf.Allocation.size 2 ⟨data, base, 1, .Heap, true, ()⟩ = .ok blockSize := by
  change SOut.bind (SOption.unwrap (SSize.from_bytes (SList.len data)))
    (fun n => SOut.ok n) = .ok blockSize
  rw [hdata]
  rfl

private theorem overlaps_for_data (data : List MR_AbstractByte) (base addr size : Int)
    (hdata : SList.len data = blockSize) :
    MRf.Allocation.overlaps 3 ⟨data, base, 1, .Heap, true, ()⟩ addr size =
      (match SInt.ble (base + blockSize) addr with
      | true => .ok (SInt.beq base addr)
      | false => match SInt.ble (addr + size) base with
        | true => .ok (SInt.beq base addr)
        | false => .ok true) := by
  dsimp only [MRf.Allocation.overlaps]
  rw [size_for_data data base hdata]
  rfl

private theorem first_overlaps_inside_data (data : List MR_AbstractByte)
    (hdata : SList.len data = blockSize) (addr : Int)
    (hlo : 0 < addr) (hhi : addr < halfSpace) :
    MRf.Allocation.overlaps 3 ⟨data, 1, 1, .Heap, true, ()⟩ addr 1 = .ok true := by
  rw [overlaps_for_data data 1 addr 1 hdata]
  have hleft : SInt.ble (1 + blockSize) addr = false := by
    apply decide_eq_false
    change ¬ (1 + blockSize ≤ addr)
    unfold blockSize halfSpace at *
    omega
  have hright : SInt.ble (addr + 1) 1 = false := by
    apply decide_eq_false
    change ¬ (addr + 1 ≤ 1)
    omega
  rw [hleft, hright]

private theorem first_disjoint_after_data (data : List MR_AbstractByte)
    (hdata : SList.len data = blockSize) (addr : Int) (hlo : halfSpace ≤ addr) :
    MRf.Allocation.overlaps 3 ⟨data, 1, 1, .Heap, true, ()⟩ addr 1 = .ok false := by
  rw [overlaps_for_data data 1 addr 1 hdata]
  have hleft : SInt.ble (1 + blockSize) addr = true := by
    apply decide_eq_true
    change 1 + blockSize ≤ addr
    unfold blockSize halfSpace at *
    omega
  rw [hleft]
  have hne : SInt.beq 1 addr = false := by
    apply decide_eq_false
    change ¬ (1 = addr)
    unfold halfSpace at hlo
    omega
  rw [hne]

private theorem second_overlaps_inside_data (data : List MR_AbstractByte)
    (hdata : SList.len data = blockSize) (addr : Int)
    (hlo : halfSpace ≤ addr) (hhi : addr + 1 < addressLimit) :
    MRf.Allocation.overlaps 3 ⟨data, halfSpace, 1, .Heap, true, ()⟩ addr 1 = .ok true := by
  rw [overlaps_for_data data halfSpace addr 1 hdata]
  have hleft : SInt.ble (halfSpace + blockSize) addr = false := by
    apply decide_eq_false
    change ¬ (halfSpace + blockSize ≤ addr)
    unfold blockSize halfSpace addressLimit at *
    omega
  have hright : SInt.ble (addr + 1) halfSpace = false := by
    apply decide_eq_false
    change ¬ (addr + 1 ≤ halfSpace)
    omega
  rw [hleft, hright]

private theorem two_blocks_cover (data fresh : List MR_AbstractByte)
    (hdata : SList.len data = blockSize) (hfresh : SList.len fresh = blockSize) (addr : Int)
    (hlo : 0 < addr) (hhi : addr + 1 < addressLimit) :
    SList.anyS [⟨data, 1, 1, .Heap, true, ()⟩, ⟨fresh, halfSpace, 1, .Heap, true, ()⟩]
      (fun (a : MR_Allocation) (_ : Unit) => match a.live with
        | true => SOut.bind (MRf.Allocation.overlaps 3 a addr 1) (fun overlaps => .ok (overlaps, ()))
        | false => .ok (false, ())) () = .ok (true, ()) := by
  dsimp only [SList.anyS]
  by_cases hhalf : addr < halfSpace
  · rw [first_overlaps_inside_data data hdata addr hlo hhalf]
    rfl
  · have hafter : halfSpace ≤ addr := by omega
    rw [first_disjoint_after_data data hdata addr hafter,
      second_overlaps_inside_data fresh hfresh addr hafter hhi]
    rfl

theorem every_positive_in_bounds_address_overlaps (addr : Int)
    (hlo : 0 < addr) (hhi : addr + 1 < addressLimit) :
    SList.anyS fullMemory.allocations
      (fun (a : MR_Allocation) (_ : Unit) => match a.live with
        | true => SOut.bind (MRf.Allocation.overlaps 3 a addr 1) (fun overlaps => .ok (overlaps, ()))
        | false => .ok (false, ())) () = .ok (true, ()) :=
  two_blocks_cover blockData blockData block_data_length block_data_length addr hlo hhi

def WrongFirstAddressGoal : Prop :=
  SOut.runOracle (fun _ => 0) (fun _ => 0)
    (MRf.BasicMemory.allocate 4 emptyMemory .Heap blockSize 1 () ()) =
    .ok (.ok ⟨2, some (⟨0⟩, ())⟩, firstMemory)

theorem wrong_first_address_false : ¬ WrongFirstAddressGoal := by
  intro h
  have good := first_allocation_reachable
  unfold FirstAllocationGoal at good
  unfold WrongFirstAddressGoal at h
  rw [good] at h
  have address := congrArg
    (fun value : SOut (SRes MR_TerminationInfo MR_ThinPointer × MR_BasicMemory) =>
      match value with
      | .ok (.ok pointer, _) => pointer.addr
      | _ => 0) h
  change (1 : Int) = 2 at address
  omega

end TrustSem.AllocationCapacity

