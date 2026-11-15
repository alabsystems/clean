/-
Interval-skip obligations stated over the ORIGINAL generated Allocation.overlaps.
The scalar expression sourceNext is the repaired Rust search's arithmetic,
including the zero-sized reservation and defensive progress guards. These
lemmas do not claim that the Rust loop or its import has been refined to this
model, or that the whole Machine.step invariant is established.
-/
import MiniRust

noncomputable section
namespace TrustSem.AllocationSearch

def reservationEnd (base length : Int) : Int :=
  if length = 0 then base + 1 else base + length

def sourceNext (base length current : Int) : Int :=
  let finish := base + length
  let reserved := if finish ≤ base then base + 1 else finish
  if reserved ≤ current then current + 1 else reserved

def alignedNext (next alignment : Int) : Int :=
  if next % alignment = 0 then next else next + (alignment - next % alignment)

private theorem overlaps_shape (allocation : MR_Allocation) (length address size : Int)
    (hsize : MRf.Allocation.size 2 allocation = .ok length) :
    MRf.Allocation.overlaps 3 allocation address size =
      (match SInt.ble (allocation.addr + length) address with
      | true => .ok (SInt.beq allocation.addr address)
      | false => match SInt.ble (address + size) allocation.addr with
        | true => .ok (SInt.beq allocation.addr address)
        | false => .ok true) := by
  dsimp only [MRf.Allocation.overlaps]
  rw [hsize]
  rfl

theorem original_overlap_iff (allocation : MR_Allocation) (length address size : Int)
    (hsize : MRf.Allocation.size 2 allocation = .ok length) :
    MRf.Allocation.overlaps 3 allocation address size = .ok true ↔
      allocation.addr = address ∨
        (address < allocation.addr + length ∧ allocation.addr < address + size) := by
  rw [overlaps_shape allocation length address size hsize]
  by_cases hl : allocation.addr + length ≤ address
  · have hb : SInt.ble (allocation.addr + length) address = true := by
      apply decide_eq_true
      exact hl
    rw [hb]
    simp [SInt.beq]
    omega
  · have hb : SInt.ble (allocation.addr + length) address = false := by
      apply decide_eq_false
      exact hl
    rw [hb]
    by_cases hr : address + size ≤ allocation.addr
    · have hb : SInt.ble (address + size) allocation.addr = true := by
        apply decide_eq_true
        exact hr
      rw [hb]
      simp [SInt.beq]
      omega
    · have hb : SInt.ble (address + size) allocation.addr = false := by
        apply decide_eq_false
        exact hr
      rw [hb]
      simp
      omega

theorem overlapping_address_before_reservation (allocation : MR_Allocation)
    (length address size : Int) (hlen : 0 ≤ length)
    (hsize : MRf.Allocation.size 2 allocation = .ok length)
    (hoverlap : MRf.Allocation.overlaps 3 allocation address size = .ok true) :
    address < reservationEnd allocation.addr length := by
  have hov := (original_overlap_iff allocation length address size hsize).mp hoverlap
  unfold reservationEnd
  split <;> omega

theorem source_next_is_reservation_end (allocation : MR_Allocation)
    (length address size : Int) (hlen : 0 ≤ length)
    (hsize : MRf.Allocation.size 2 allocation = .ok length)
    (hoverlap : MRf.Allocation.overlaps 3 allocation address size = .ok true) :
    sourceNext allocation.addr length address = reservationEnd allocation.addr length := by
  have hbefore := overlapping_address_before_reservation allocation length address size
    hlen hsize hoverlap
  by_cases hz : length = 0
  · have hguard : ¬ allocation.addr + 1 ≤ address := by
      simp only [reservationEnd, hz, if_pos] at hbefore
      omega
    simp [sourceNext, reservationEnd, hz, hguard]
  · have hpos : 0 < length := by omega
    have hbase : ¬ allocation.addr + length ≤ allocation.addr := by omega
    have hguard : ¬ allocation.addr + length ≤ address := by
      simp only [reservationEnd, if_neg hz] at hbefore
      omega
    simp [sourceNext, reservationEnd, hz, hbase, hguard]

theorem skipped_addresses_still_overlap (allocation : MR_Allocation)
    (length current size address : Int) (hlen : 0 ≤ length) (hreq : 0 ≤ size)
    (hsize : MRf.Allocation.size 2 allocation = .ok length)
    (hoverlap : MRf.Allocation.overlaps 3 allocation current size = .ok true)
    (hlo : current ≤ address) (hhi : address < reservationEnd allocation.addr length) :
    MRf.Allocation.overlaps 3 allocation address size = .ok true := by
  apply (original_overlap_iff allocation length address size hsize).mpr
  have hov := (original_overlap_iff allocation length current size hsize).mp hoverlap
  unfold reservationEnd at hhi
  split at hhi <;> omega

theorem passed_reservation_never_overlaps (allocation : MR_Allocation)
    (length address size : Int) (hlen : 0 ≤ length)
    (hsize : MRf.Allocation.size 2 allocation = .ok length)
    (hafter : reservationEnd allocation.addr length ≤ address) :
    MRf.Allocation.overlaps 3 allocation address size = .ok false := by
  have hend : allocation.addr + length ≤ address := by
    unfold reservationEnd at hafter
    split at hafter <;> omega
  have hne : ¬ allocation.addr = address := by
    unfold reservationEnd at hafter
    split at hafter <;> omega
  rw [overlaps_shape allocation length address size hsize]
  simp [SInt.ble, SInt.beq, hend, hne]

theorem alignment_rounding_increases (next alignment : Int) (ha : 0 < alignment) :
    next ≤ alignedNext next alignment := by
  have hlo := Int.emod_nonneg next (Int.ne_of_gt ha)
  have hhi := Int.emod_lt_of_pos next ha
  unfold alignedNext
  split <;> omega

theorem alignment_rounding_is_aligned (next alignment : Int) :
    alignedNext next alignment % alignment = 0 := by
  unfold alignedNext
  split
  · assumption
  · apply Int.emod_eq_zero_of_dvd
    have hbase : alignment ∣ next - next % alignment := Int.dvd_self_sub_emod
    have hsum : next + (alignment - next % alignment) = (next - next % alignment) + alignment := by omega
    rw [hsum]
    exact Int.dvd_add hbase ⟨1, by omega⟩

theorem alignment_rounding_le_every_aligned (next alignment address : Int)
    (ha : 0 < alignment) (hlo : next ≤ address) (haligned : address % alignment = 0) :
    alignedNext next alignment ≤ address := by
  unfold alignedNext
  split
  · exact hlo
  next hrem =>
    have hnonneg := Int.emod_nonneg next (Int.ne_of_gt ha)
    have hpositive : 0 < address - (next - next % alignment) := by omega
    have hdvd : alignment ∣ address - (next - next % alignment) :=
      Int.dvd_sub (Int.dvd_of_emod_eq_zero haligned) Int.dvd_self_sub_emod
    have hstep := Int.le_of_dvd hpositive hdvd
    omega

/-- The source uses signed BigInt remainder, not Lean's Euclidean remainder.
The actual search keeps the rounded operand nonnegative and the alignment
positive; only on that stated domain do these two computations coincide. -/
theorem original_remainder_on_search_domain (next alignment : Int)
    (hn : 0 ≤ next) (ha : 0 < alignment) :
    SInt.rem next alignment = .ok (next % alignment) := by
  cases next with
  | ofNat n =>
    cases alignment with
    | ofNat a =>
      have hne : ¬ (Int.ofNat a = 0) := by omega
      simp only [SInt.rem, SInt.beq, hne, decide_false,
        SInt.isNeg, SInt.abs, SInt.ofSignedNat]
      rfl
    | negSucc a => omega
  | negSucc n => omega

theorem original_scalar_rounding (next alignment : Int) (hn : 0 ≤ next) (ha : 0 < alignment) :
    SOut.bind (SInt.rem next alignment)
      (fun remainder => .ok (if SInt.beq remainder 0 then next else next + (alignment - remainder))) =
      .ok (alignedNext next alignment) := by
  rw [original_remainder_on_search_domain next alignment hn ha]
  dsimp only [SOut.bind]
  unfold alignedNext SInt.beq
  by_cases h : next % alignment = 0 <;> simp [h]

theorem skipped_aligned_addresses_still_overlap (allocation : MR_Allocation)
    (length current size alignment address : Int) (hlen : 0 ≤ length) (hreq : 0 ≤ size)
    (hsize : MRf.Allocation.size 2 allocation = .ok length)
    (hoverlap : MRf.Allocation.overlaps 3 allocation current size = .ok true)
    (ha : 0 < alignment) (hlo : current ≤ address) (haligned : address % alignment = 0)
    (hhi : address < alignedNext (sourceNext allocation.addr length current) alignment) :
    MRf.Allocation.overlaps 3 allocation address size = .ok true := by
  rw [source_next_is_reservation_end allocation length current size hlen hsize hoverlap] at hhi
  apply skipped_addresses_still_overlap allocation length current size address hlen hreq hsize hoverlap hlo
  by_cases hbefore : address < reservationEnd allocation.addr length
  · exact hbefore
  · have hround := alignment_rounding_le_every_aligned
      (reservationEnd allocation.addr length) alignment address ha (by omega) haligned
    omega

theorem selected_allocation_cleared (allocation : MR_Allocation)
    (length current size alignment : Int) (hlen : 0 ≤ length)
    (hsize : MRf.Allocation.size 2 allocation = .ok length)
    (hoverlap : MRf.Allocation.overlaps 3 allocation current size = .ok true)
    (ha : 0 < alignment) :
    MRf.Allocation.overlaps 3 allocation
      (alignedNext (sourceNext allocation.addr length current) alignment) size = .ok false := by
  rw [source_next_is_reservation_end allocation length current size hlen hsize hoverlap]
  exact passed_reservation_never_overlaps allocation length _ size hlen hsize
    (alignment_rounding_increases _ alignment ha)

theorem original_size_is_data_length (allocation : MR_Allocation) :
    MRf.Allocation.size 2 allocation = .ok (SList.len allocation.data) := by
  have hn : SInt.blt (SList.len allocation.data) 0 = false := by
    apply decide_eq_false
    have hnonnegative : 0 ≤ SList.len allocation.data := Int.natCast_nonneg _
    omega
  dsimp only [MRf.Allocation.size]
  unfold SSize.from_bytes
  rw [hn]
  rfl

theorem original_data_length_nonnegative (allocation : MR_Allocation) :
    0 ≤ SList.len allocation.data := by
  exact Int.natCast_nonneg _

def allocationEnd (allocation : MR_Allocation) : Int :=
  reservationEnd allocation.addr (SList.len allocation.data)

/-- A mathematical ranking function, not another allocator/evaluator. Every
allocation potentially selectable at the current address is counted; crossing
one reservation removes it permanently even if other intervals overlap. -/
def remaining : List MR_Allocation → Int → Nat
  | [], _ => 0
  | allocation :: rest, address =>
    (if address < allocationEnd allocation then 1 else 0) + remaining rest address

theorem remaining_monotone (allocations : List MR_Allocation) (current next : Int)
    (hnext : current ≤ next) : remaining allocations next ≤ remaining allocations current := by
  induction allocations with
  | nil => exact Nat.le_refl _
  | cons allocation rest ih =>
    by_cases hc : current < allocationEnd allocation <;>
      by_cases hn : next < allocationEnd allocation <;>
      simp only [remaining, hc, hn, ite_true, ite_false, Nat.zero_add] <;> omega

theorem remaining_le_length (allocations : List MR_Allocation) (address : Int) :
    remaining allocations address ≤ allocations.length := by
  induction allocations with
  | nil => exact Nat.le_refl _
  | cons allocation rest ih =>
    by_cases h : address < allocationEnd allocation <;>
      simp only [remaining, List.length_cons, h, ite_true, ite_false, Nat.zero_add] <;> omega

theorem passing_member_decreases_remaining (allocations : List MR_Allocation)
    (selected : MR_Allocation) (current next : Int) (hmem : selected ∈ allocations)
    (hbefore : current < allocationEnd selected) (hafter : allocationEnd selected ≤ next)
    (hnext : current ≤ next) : remaining allocations next < remaining allocations current := by
  induction allocations with
  | nil => cases hmem
  | cons allocation rest ih =>
    cases List.mem_cons.mp hmem with
    | inl heq =>
      subst allocation
      have htail := remaining_monotone rest current next hnext
      have hn : ¬ next < allocationEnd selected := by omega
      simp only [remaining, hbefore, hn, ite_true, ite_false, Nat.zero_add]
      omega
    | inr htail =>
      have hstrict := ih htail
      by_cases hc : current < allocationEnd allocation <;>
        by_cases hn : next < allocationEnd allocation <;>
        simp only [remaining, hc, hn, ite_true, ite_false, Nat.zero_add] <;> omega

theorem actual_selected_skip_decreases_remaining (allocations : List MR_Allocation)
    (selected : MR_Allocation) (current size alignment : Int) (hmem : selected ∈ allocations)
    (hoverlap : MRf.Allocation.overlaps 3 selected current size = .ok true)
    (ha : 0 < alignment) :
    remaining allocations
      (alignedNext (sourceNext selected.addr (SList.len selected.data) current) alignment) <
      remaining allocations current := by
  have hsize := original_size_is_data_length selected
  have hlen := original_data_length_nonnegative selected
  have hbefore := overlapping_address_before_reservation selected _ current size hlen hsize hoverlap
  rw [source_next_is_reservation_end selected _ current size hlen hsize hoverlap]
  change current < allocationEnd selected at hbefore
  change remaining allocations (alignedNext (allocationEnd selected) alignment) < remaining allocations current
  have hafter := alignment_rounding_increases (allocationEnd selected) alignment ha
  apply passing_member_decreases_remaining allocations selected current _ hmem hbefore hafter
  omega

private theorem decreasing_rank_consumes_fuel (rank : Nat → Nat) (steps : Nat)
    (hsteps : ∀ i, i < steps → rank (i + 1) < rank i) : steps + rank steps ≤ rank 0 := by
  induction steps with
  | zero => simp
  | succ n ih =>
    have hprefix : ∀ i, i < n → rank (i + 1) < rank i := by
      intro i hi
      apply hsteps i
      omega
    have hprior := ih hprefix
    have hlast := hsteps n (by omega)
    omega

theorem skip_count_bounded_by_allocation_population (allocations : List MR_Allocation)
    (addresses : Nat → Int) (steps : Nat)
    (hsteps : ∀ i, i < steps →
      remaining allocations (addresses (i + 1)) < remaining allocations (addresses i)) :
    steps ≤ allocations.length := by
  have hbound := decreasing_rank_consumes_fuel (fun i => remaining allocations (addresses i)) steps hsteps
  dsimp only at hbound
  have hstart := remaining_le_length allocations (addresses 0)
  omega

theorem full_population_skips_leave_zero_rank (allocations : List MR_Allocation)
    (addresses : Nat → Int)
    (hsteps : ∀ i, i < allocations.length →
      remaining allocations (addresses (i + 1)) < remaining allocations (addresses i)) :
    remaining allocations (addresses allocations.length) = 0 := by
  have hbound := decreasing_rank_consumes_fuel
    (fun i => remaining allocations (addresses i)) allocations.length hsteps
  dsimp only at hbound
  have hstart := remaining_le_length allocations (addresses 0)
  omega

theorem zero_rank_clears_original_overlaps (allocations : List MR_Allocation) (address size : Int)
    (hzero : remaining allocations address = 0) :
    ∀ allocation, allocation ∈ allocations →
      MRf.Allocation.overlaps 3 allocation address size = .ok false := by
  induction allocations with
  | nil => intro allocation hmem; cases hmem
  | cons first rest ih =>
    have hnot : ¬ address < allocationEnd first := by
      intro h
      simp only [remaining, h, ite_true] at hzero
      omega
    have hrest : remaining rest address = 0 := by
      simp only [remaining, hnot, ite_false, Nat.zero_add] at hzero
      exact hzero
    intro allocation hmem
    cases List.mem_cons.mp hmem with
    | inl heq =>
      subst allocation
      have hafter : allocationEnd first ≤ address := by omega
      exact passed_reservation_never_overlaps first _ address size
        (original_data_length_nonnegative first) (original_size_is_data_length first) hafter
    | inr hmem => exact ih hrest allocation hmem

/-- The original fitting-domain constraints, with an arbitrary finite upper
address bound. This is a proposition over original overlap calls, not a host
search or a replacement for the source memory implementation. -/
def Fits (allocations : List MR_Allocation) (size alignment limit address : Int) : Prop :=
  0 < address ∧ address % alignment = 0 ∧ address + size < limit ∧
    ∀ allocation, allocation ∈ allocations → allocation.live = true →
      MRf.Allocation.overlaps 3 allocation address size = .ok false

def NoFitBefore (allocations : List MR_Allocation) (size alignment limit current : Int) : Prop :=
  ∀ address, Fits allocations size alignment limit address → current ≤ address

theorem initial_alignment_is_lower_bound (allocations : List MR_Allocation)
    (size alignment limit : Int) : NoFitBefore allocations size alignment limit alignment := by
  intro address hfit
  exact Int.le_of_dvd hfit.1 (Int.dvd_of_emod_eq_zero hfit.2.1)

theorem skip_preserves_every_fitting_address (allocations : List MR_Allocation)
    (selected : MR_Allocation) (current size alignment limit : Int)
    (hmem : selected ∈ allocations) (hlive : selected.live = true)
    (hoverlap : MRf.Allocation.overlaps 3 selected current size = .ok true)
    (hreq : 0 ≤ size) (ha : 0 < alignment)
    (hbefore : NoFitBefore allocations size alignment limit current) :
    NoFitBefore allocations size alignment limit
      (alignedNext (sourceNext selected.addr (SList.len selected.data) current) alignment) := by
  intro address hfit
  by_cases hnext : alignedNext (sourceNext selected.addr (SList.len selected.data) current) alignment ≤ address
  · exact hnext
  · have hovered := skipped_aligned_addresses_still_overlap selected _ current size alignment address
      (original_data_length_nonnegative selected) hreq (original_size_is_data_length selected)
      hoverlap ha (hbefore address hfit) hfit.2.1 (by omega)
    have hclear := hfit.2.2.2 selected hmem hlive
    rw [hovered] at hclear
    cases hclear

/-- Evidence obligations of one source skip. The Rust search is not assumed to
produce this evidence: its original-body refinement is a separate obligation. -/
def SkipStep (allocations : List MR_Allocation) (size alignment current next : Int) : Prop :=
  ∃ selected, selected ∈ allocations ∧ selected.live = true ∧
    MRf.Allocation.overlaps 3 selected current size = .ok true ∧
    next = alignedNext (sourceNext selected.addr (SList.len selected.data) current) alignment

theorem skip_step_decreases_rank (allocations : List MR_Allocation) (size alignment current next : Int)
    (ha : 0 < alignment) (hstep : SkipStep allocations size alignment current next) :
    remaining allocations next < remaining allocations current := by
  rcases hstep with ⟨selected, hmem, _, hoverlap, hnext⟩
  rw [hnext]
  exact actual_selected_skip_decreases_remaining allocations selected current size alignment hmem hoverlap ha

theorem trace_preserves_fitting_lower_bound (allocations : List MR_Allocation)
    (size alignment limit : Int) (addresses : Nat → Int) (steps : Nat)
    (hreq : 0 ≤ size) (ha : 0 < alignment) (hstart : addresses 0 = alignment)
    (hsteps : ∀ i, i < steps → SkipStep allocations size alignment (addresses i) (addresses (i + 1))) :
    ∀ i, i ≤ steps → NoFitBefore allocations size alignment limit (addresses i) := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [hstart]
    exact initial_alignment_is_lower_bound allocations size alignment limit
  | succ i ih =>
    intro hi
    have hprior := ih (by omega)
    rcases hsteps i (by omega) with ⟨selected, hmem, hlive, hoverlap, hnext⟩
    rw [hnext]
    exact skip_preserves_every_fitting_address allocations selected _ size alignment limit
      hmem hlive hoverlap hreq ha hprior

theorem trace_remains_positive_and_aligned (allocations : List MR_Allocation)
    (size alignment : Int) (addresses : Nat → Int) (steps : Nat)
    (ha : 0 < alignment) (hstart : addresses 0 = alignment)
    (hsteps : ∀ i, i < steps → SkipStep allocations size alignment (addresses i) (addresses (i + 1))) :
    ∀ i, i ≤ steps → 0 < addresses i ∧ addresses i % alignment = 0 := by
  intro i
  induction i with
  | zero => intro _; rw [hstart]; exact ⟨ha, by simp⟩
  | succ i ih =>
    intro hi
    have hprior := ih (by omega)
    rcases hsteps i (by omega) with ⟨selected, _, _, hoverlap, hnext⟩
    rw [hnext]
    have hbefore := overlapping_address_before_reservation selected _ (addresses i) size
      (original_data_length_nonnegative selected) (original_size_is_data_length selected) hoverlap
    rw [source_next_is_reservation_end selected _ (addresses i) size
      (original_data_length_nonnegative selected) (original_size_is_data_length selected) hoverlap]
    have hrounded := alignment_rounding_increases
      (reservationEnd selected.addr (SList.len selected.data)) alignment ha
    exact ⟨by omega, alignment_rounding_is_aligned _ alignment⟩

theorem completed_trace_fits_if_any_address_fits (allocations : List MR_Allocation)
    (size alignment limit : Int) (addresses : Nat → Int)
    (hreq : 0 ≤ size) (ha : 0 < alignment) (hstart : addresses 0 = alignment)
    (hsteps : ∀ i, i < allocations.length →
      SkipStep allocations size alignment (addresses i) (addresses (i + 1)))
    (hexists : ∃ address, Fits allocations size alignment limit address) :
    Fits allocations size alignment limit (addresses allocations.length) := by
  have hdrops : ∀ i, i < allocations.length →
      remaining allocations (addresses (i + 1)) < remaining allocations (addresses i) := by
    intro i hi
    exact skip_step_decreases_rank allocations size alignment _ _ ha (hsteps i hi)
  have hzero := full_population_skips_leave_zero_rank allocations addresses hdrops
  have hno := zero_rank_clears_original_overlaps allocations (addresses allocations.length) size hzero
  have hlower := trace_preserves_fitting_lower_bound allocations size alignment limit addresses
    allocations.length hreq ha hstart hsteps allocations.length (by omega)
  have hpositive := trace_remains_positive_and_aligned allocations size alignment addresses
    allocations.length ha hstart hsteps allocations.length (by omega)
  rcases hexists with ⟨address, hfit⟩
  have hle := hlower address hfit
  refine ⟨hpositive.1, hpositive.2, ?_, ?_⟩
  · have hlimit := hfit.2.2.1
    omega
  · intro allocation hmem _
    exact hno allocation hmem

def unfixedNext (base length current : Int) : Int :=
  if base + length ≤ current then current + 1 else base + length

def ClearedGoal : Prop :=
  ∀ allocation : MR_Allocation, ∀ current size alignment : Int,
    MRf.Allocation.overlaps 3 allocation current size = .ok true → 0 < alignment →
    MRf.Allocation.overlaps 3 allocation
      (alignedNext (sourceNext allocation.addr (SList.len allocation.data) current) alignment) size = .ok false

theorem actual_selected_cleared : ClearedGoal := by
  intro allocation current size alignment hoverlap ha
  exact selected_allocation_cleared allocation _ current size alignment
    (original_data_length_nonnegative allocation) (original_size_is_data_length allocation) hoverlap ha

def UnfixedClearedGoal : Prop :=
  ∀ allocation : MR_Allocation, ∀ current size alignment : Int,
    MRf.Allocation.overlaps 3 allocation current size = .ok true → 0 < alignment →
    MRf.Allocation.overlaps 3 allocation
      (alignedNext (unfixedNext allocation.addr (SList.len allocation.data) current) alignment) size = .ok false

def zeroReservationWitness : MR_Allocation := ⟨[], 2, 1, .Heap, true, ()⟩

theorem zero_reservation_ahead_overlaps :
    MRf.Allocation.overlaps 3 zeroReservationWitness 1 2 = .ok true := rfl

theorem unfixed_skip_lands_on_reserved_base :
    alignedNext (unfixedNext zeroReservationWitness.addr
      (SList.len zeroReservationWitness.data) 1) 1 = 2 := rfl

theorem unfixed_cleared_goal_false : ¬ UnfixedClearedGoal := by
  intro h
  have wrong := h zeroReservationWitness 1 2 1 zero_reservation_ahead_overlaps (by decide)
  change SOut.ok true = SOut.ok false at wrong
  cases wrong

end TrustSem.AllocationSearch
