import TrustSemAllocationCapacity
import TrustSem

noncomputable section
namespace TrustSem.AllocationCapacity

private theorem unsigned_bounds (addr : Int) :
    SInt.in_bounds addr .Unsigned 8 = .ok (SInt.beq addr (addr % addressLimit)) := by
  dsimp only [SInt.in_bounds, SInt.bring_in_bounds]
  have hsize : SInt.beq 8 0 = false := rfl
  rw [hsize]
  have hpow : SInt.pow 2 ((8 : Int) * 8) = .ok addressLimit := rfl
  rw [hpow]
  dsimp only [SOut.bind]
  have hrem : SInt.rem_euclid addr addressLimit = .ok (addr % addressLimit) :=
    SemR.rem_euclid_eq addr 18446744073709551616 (by decide)
  rw [hrem]

private theorem align_one (i : Nat) :
    SAlign.is_aligned 1 (1 + Int.ofNat i) = .ok true := by
  have haddr : 1 + Int.ofNat i = Int.ofNat (i + 1) := Int.add_comm _ _
  rw [haddr]
  unfold SAlign.is_aligned SInt.rem
  have hz : SInt.beq 1 0 = false := rfl
  rw [hz]
  simp only [SInt.isNeg, SInt.abs, SInt.ofSignedNat, Nat.mod_one]
  rfl

private theorem bind_ok {α β : Type} (a : α) (f : α → SOut β) :
    SOut.bind (.ok a) f = f a := rfl
/- Proof-only name for the ORIGINAL predicate. The checked conversion in the
allocation proof ties it to the generated operation. This does not define the
Rust OOM repair or replace the original allocator. -/
private def originalPredicate (memory : MR_BasicMemory) (addr : Int) : SOut (Bool × Unit) :=
  match SInt.ble addr 0 with
  | true => .ok (false, ())
  | false => SOut.bind (SAlign.is_aligned 1 addr) fun aligned =>
    match SBool.not aligned with
    | true => .ok (false, ())
    | false => SOut.bind (SInt.in_bounds (addr + 1) .Unsigned 8) fun bounded =>
      match SBool.not bounded with
      | true => .ok (false, ())
      | false => SOut.bind
        (SList.anyS memory.allocations
          (fun (a : MR_Allocation) (_ : Unit) => match a.live with
            | true => SOut.bind (MRf.Allocation.overlaps 3 a addr 1)
                (fun overlaps => .ok (overlaps, ()))
            | false => .ok (false, ())) ()) fun occupied =>
        match occupied with
        | (occupied, _) => match occupied with
          | true => .ok (false, ())
          | false => .ok (true, ())

private theorem predicate_rejects_of_cover (memory : MR_BasicMemory)
    (hcover : ∀ addr : Int, 0 < addr → addr + 1 < addressLimit →
      SList.anyS memory.allocations
        (fun (a : MR_Allocation) (_ : Unit) => match a.live with
          | true => SOut.bind (MRf.Allocation.overlaps 3 a addr 1) (fun overlaps => .ok (overlaps, ()))
          | false => .ok (false, ())) () = .ok (true, ()))
    (i : Nat) : originalPredicate memory (1 + Int.ofNat i) = .ok (false, ()) := by
  dsimp only [originalPredicate]
  have hi : 0 ≤ Int.ofNat i := Int.natCast_nonneg i
  have hpositive : 0 < 1 + Int.ofNat i := by omega
  have hnonzero : SInt.ble (1 + Int.ofNat i) 0 = false := by
    apply decide_eq_false
    change ¬ (1 + Int.ofNat i ≤ 0)
    omega
  rw [hnonzero, align_one i]
  simp only [bind_ok, SBool.not]
  rw [unsigned_bounds]
  simp only [bind_ok]
  cases hbnd : SInt.beq (1 + Int.ofNat i + 1)
      ((1 + Int.ofNat i + 1) % addressLimit) with
  | false => rfl
  | true =>
    have heq : 1 + Int.ofNat i + 1 = (1 + Int.ofNat i + 1) % addressLimit :=
      of_decide_eq_true hbnd
    have hmod := Int.emod_lt_of_pos (1 + Int.ofNat i + 1)
      (show 0 < addressLimit by decide)
    have hend : 1 + Int.ofNat i + 1 < addressLimit := by omega
    dsimp only [SBool.not]
    rw [hcover (1 + Int.ofNat i) hpositive hend] <;> rfl


/-- Proof predicate only: every branch of the ORIGINAL free tree rejects.
Fuel, panic, UB and successful outcomes have no constructor here. -/
inductive AllRejected {α : Type} : SOut α → Prop where
  | reject : AllRejected .reject
  | pick {k : Nat → SOut α} : (∀ i, AllRejected (k i)) → AllRejected (.pick k)
  | predict {k : Nat → SOut α} : (∀ i, AllRejected (k i)) → AllRejected (.predict k)

private theorem rejected_bind {α β : Type} {tree : SOut α}
    (f : α → SOut β) (h : AllRejected tree) : AllRejected (SOut.bind tree f) := by
  induction h with
  | reject => exact .reject
  | pick hk ih => exact .pick ih
  | predict hk ih => exact .predict ih

private theorem rejected_from_ok {α β : Type} {tree : SOut α} {a : α}
    {f : α → SOut β} (htree : tree = .ok a) (h : AllRejected (f a)) :
    AllRejected (SOut.bind tree f) := by
  rw [htree]
  exact h

private theorem choose_rejects (memory : MR_BasicMemory)
    (hcover : ∀ addr : Int, 0 < addr → addr + 1 < addressLimit →
      SList.anyS memory.allocations
        (fun (a : MR_Allocation) (_ : Unit) => match a.live with
          | true => SOut.bind (MRf.Allocation.overlaps 3 a addr 1) (fun overlaps => .ok (overlaps, ()))
          | false => .ok (false, ())) () = .ok (true, ())) :
    AllRejected (SPick.choose ⟨1, addressLimit, 1⟩
      (fun addr (_ : Unit) => originalPredicate memory addr) ()) := by
  dsimp only [SPick.choose]
  have hdiv : SInt.div_ceil 1 1 = .ok 1 := rfl
  rw [hdiv]
  simp only [bind_ok]
  apply AllRejected.pick
  intro i
  simp only [Int.mul_one]
  cases hchoice : SInt.blt (1 + Int.ofNat i) addressLimit with
  | false => exact .reject
  | true =>
    rw [predicate_rejects_of_cover memory hcover i]
    exact .reject

private theorem allocate_rejected_of_cover (memory : MR_BasicMemory)
    (hcover : ∀ addr : Int, 0 < addr → addr + 1 < addressLimit →
      SList.anyS memory.allocations
        (fun (a : MR_Allocation) (_ : Unit) => match a.live with
          | true => SOut.bind (MRf.Allocation.overlaps 3 a addr 1) (fun overlaps => .ok (overlaps, ()))
          | false => .ok (false, ())) () = .ok (true, ())) :
    AllRejected (MRf.BasicMemory.allocate 4 memory .Heap 1 1 () ()) := by
  dsimp only [MRf.BasicMemory.allocate]
  apply rejected_from_ok requested_size_valid
  dsimp only [SBool.not]
  have hptr : MRf.x86_64.PTR_SIZE 3 = .ok 8 := rfl
  apply rejected_from_ok hptr
  have hpow : SInt.pow 2 (SSize.bits 8) = .ok addressLimit := rfl
  apply rejected_from_ok hpow
  apply rejected_bind
  change AllRejected (SPick.choose ⟨1, addressLimit, 1⟩
    (fun addr (_ : Unit) => originalPredicate memory addr) ())
  exact choose_rejects memory hcover

theorem full_memory_all_rejected :
    AllRejected (MRf.BasicMemory.allocate 4 fullMemory .Heap 1 1 () ()) :=
  allocate_rejected_of_cover fullMemory every_positive_in_bounds_address_overlaps

theorem all_rejected_runOracle {α : Type} {tree : SOut α} (h : AllRejected tree)
    (δ π : List Nat → Nat) : SOut.runOracle δ π tree = .reject := by
  induction h generalizing δ π with
  | reject => rfl
  | pick hk ih =>
    exact ih (δ []) (fun history => δ (δ [] :: history)) (fun history => π (δ [] :: history))
  | predict hk ih =>
    exact ih (π []) (fun history => δ (π [] :: history)) (fun history => π (π [] :: history))

def RejectEveryOracleGoal : Prop :=
  ∀ δ π : List Nat → Nat,
    SOut.runOracle δ π (MRf.BasicMemory.allocate 4 fullMemory .Heap 1 1 () ()) = .reject

theorem full_memory_rejects_every_oracle : RejectEveryOracleGoal :=
  all_rejected_runOracle full_memory_all_rejected

def AbortEveryOracleGoal : Prop :=
  ∀ δ π : List Nat → Nat,
    SOut.runOracle δ π (MRf.BasicMemory.allocate 4 fullMemory .Heap 1 1 () ()) =
      .ok (.err .Abort, fullMemory)

def FuelEveryOracleGoal : Prop :=
  ∀ δ π : List Nat → Nat,
    SOut.runOracle δ π (MRf.BasicMemory.allocate 4 fullMemory .Heap 1 1 () ()) = .fuel

theorem abort_is_not_original_rejection : ¬ AbortEveryOracleGoal := by
  intro h
  have wrong := h (fun _ => 0) (fun _ => 0)
  rw [full_memory_rejects_every_oracle] at wrong
  cases wrong

theorem fuel_is_not_original_rejection : ¬ FuelEveryOracleGoal := by
  intro h
  have wrong := h (fun _ => 0) (fun _ => 0)
  rw [full_memory_rejects_every_oracle] at wrong
  cases wrong

theorem zero_fuel_still_fuel (δ π : List Nat → Nat) :
    SOut.runOracle δ π (MRf.BasicMemory.allocate 0 fullMemory .Heap 1 1 () ()) = .fuel := rfl

theorem all_rejected_dead {E S R : Type} (P : TrustSem.Prog E S R)
    {tree : SOut (List E × (S ⊕ R))} (h : AllRejected tree) : TrustSem.Dead P tree := by
  induction h with
  | reject => exact .reject
  | pick hk ih => exact .pick ih
  | predict hk ih => exact .predict ih

/-- Any continuation of this exact original exhausted allocation is dead in
TrustSem's existing sense. Reaching it in the whole Machine.step remains a
separate invariant/instance obligation; no such premise is invented here. -/
theorem exhausted_allocation_continuation_dead {E S R : Type} (P : TrustSem.Prog E S R)
    (continuation : (SRes MR_TerminationInfo MR_ThinPointer × MR_BasicMemory) →
      SOut (List E × (S ⊕ R))) :
    TrustSem.Dead P (SOut.bind
      (MRf.BasicMemory.allocate 4 fullMemory .Heap 1 1 () ()) continuation) :=
  all_rejected_dead P (rejected_bind continuation full_memory_all_rejected)

/-- A necessary exclusion invariant for the EXISTING live-step premise. This
does not assume the invariant is preserved or claim a whole-machine witness. -/
theorem miniRust_live_step_excludes_exhausted_call (fuel : Nat) (program : MR_Program)
    (live : ∀ state, ¬ TrustSem.Dead (TrustSem.miniRust fuel program)
      (TrustSem.miniRustStep fuel program state))
    (state : Option MR_Machine)
    (continuation : (SRes MR_TerminationInfo MR_ThinPointer × MR_BasicMemory) →
      SOut (List Unit × (Option MR_Machine ⊕ MR_TerminationInfo))) :
    TrustSem.miniRustStep fuel program state ≠ SOut.bind
      (MRf.BasicMemory.allocate 4 fullMemory .Heap 1 1 () ()) continuation := by
  intro equality
  have dead := exhausted_allocation_continuation_dead (TrustSem.miniRust fuel program) continuation
  rw [← equality] at dead
  exact live state dead

end TrustSem.AllocationCapacity


