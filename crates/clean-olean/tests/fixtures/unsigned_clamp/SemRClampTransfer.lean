/-
Exact counterexamples and normalized consequences of the original source proof.
The canonical decoder and runBlob execute the complete preserved wire inputs.
-/
import Lean
import UnsignedArtifact
set_option maxHeartbeats 8000000
set_option maxRecDepth 131072
open Lean Meta Elab Tactic in
elab "clampKernelRfl" : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType
  let some (_, _, rhs) := target.eq? | throwError "expected a closed equality"
  let proof ← mkEqRefl rhs
  let lemma ← withOptions (Elab.async.set · false) do
    mkAuxLemma [] target proof
  goal.assign (mkConst lemma)

namespace SemRClampTransfer
open SemR UnsignedArtifact

theorem width_zero_valid : 0 < 4294967296 := by decide
theorem width_high_valid : 65 < 4294967296 := by decide
theorem maximum_n_valid : 2 < 18446744073709551616 := by decide
theorem maximum_bound_valid : 1 < 18446744073709551616 := by decide

def widthZero : Except DErr Out := .ok (.ret [.int .u32 0])
def widthBound : Except DErr Out := .ok (.ret [.int .u32 64])
def widthAltered : Except DErr Out := .ok (.ret [.int .u32 65])
def maximumExpected : Except DErr Out := .ok (.ret [.int .u64 1])
def maximumAltered : Except DErr Out := .ok (.ret [.int .u64 2])

theorem source_width_zero : runBlob widthBlob 0 [.int .u32 0] 19 0 = widthZero := by
  simpa [widthZero] using width_correct 0 0 width_zero_valid
theorem source_width_high : runBlob widthBlob 0 [.int .u32 65] 19 0 = widthBound := by
  simpa [widthBound] using width_correct 65 0 width_high_valid
theorem source_maximum : runBlob maximumBlob 0 [.int .u64 2,.int .u64 1] 24 0 = maximumExpected := by
  simpa [maximumExpected] using maximum_correct 2 1 0 maximum_n_valid maximum_bound_valid

theorem width_zero_consequence : widthZero = widthZero := source_width_zero.symm.trans source_width_zero
theorem width_high_consequence : widthBound = widthBound := source_width_high.symm.trans source_width_high
theorem maximum_consequence : maximumExpected = maximumExpected := source_maximum.symm.trans source_maximum

theorem width_comparison_at : runBlob widthWrongComparisonBlob 0 [.int .u32 0] 19 0 = widthBound := by clampKernelRfl
def WrongWidthComparisonResult : Prop := widthBound = widthZero
theorem width_comparison_implies (h : WrongWidthComparison) : WrongWidthComparisonResult := by
  have at_input := h 0 0 width_zero_valid
  rw [width_comparison_at] at at_input
  simpa [WrongWidthComparisonResult, widthBound, widthZero] using at_input
theorem width_comparison_refuted : ¬ WrongWidthComparison := by
  intro h
  have bad := width_comparison_implies h
  simp [WrongWidthComparisonResult, widthBound, widthZero] at bad

theorem width_arms_at : runBlob widthWrongArmsBlob 0 [.int .u32 0] 19 0 = widthBound := by clampKernelRfl
def WrongWidthArmsResult : Prop := widthBound = widthZero
theorem width_arms_implies (h : WrongWidthArms) : WrongWidthArmsResult := by
  have at_input := h 0 0 width_zero_valid
  rw [width_arms_at] at at_input
  simpa [WrongWidthArmsResult, widthBound, widthZero] using at_input
theorem width_arms_refuted : ¬ WrongWidthArms := by
  intro h
  have bad := width_arms_implies h
  simp [WrongWidthArmsResult, widthBound, widthZero] at bad

theorem width_bound_at : runBlob widthWrongBoundBlob 0 [.int .u32 65] 19 0 = widthAltered := by clampKernelRfl
def WrongWidthBoundResult : Prop := widthAltered = widthBound
theorem width_bound_implies (h : WrongWidthBound) : WrongWidthBoundResult := by
  have at_input := h 65 0 width_high_valid
  rw [width_bound_at] at at_input
  simpa [WrongWidthBoundResult, widthAltered, widthBound] using at_input
theorem width_bound_refuted : ¬ WrongWidthBound := by
  intro h
  have bad := width_bound_implies h
  simp [WrongWidthBoundResult, widthAltered, widthBound] at bad

theorem maximum_comparison_at : runBlob maximumWrongComparisonBlob 0 [.int .u64 2,.int .u64 1] 24 0 = maximumAltered := by clampKernelRfl
def WrongMaximumComparisonResult : Prop := maximumAltered = maximumExpected
theorem maximum_comparison_implies (h : WrongMaximumComparison) : WrongMaximumComparisonResult := by
  have at_input := h 2 1 0 maximum_n_valid maximum_bound_valid
  rw [maximum_comparison_at] at at_input
  simpa [WrongMaximumComparisonResult, maximumAltered, maximumExpected] using at_input
theorem maximum_comparison_refuted : ¬ WrongMaximumComparison := by
  intro h
  have bad := maximum_comparison_implies h
  simp [WrongMaximumComparisonResult, maximumAltered, maximumExpected] at bad

theorem maximum_arms_at : runBlob maximumWrongArmsBlob 0 [.int .u64 2,.int .u64 1] 24 0 = maximumAltered := by clampKernelRfl
def WrongMaximumArmsResult : Prop := maximumAltered = maximumExpected
theorem maximum_arms_implies (h : WrongMaximumArms) : WrongMaximumArmsResult := by
  have at_input := h 2 1 0 maximum_n_valid maximum_bound_valid
  rw [maximum_arms_at] at at_input
  simpa [WrongMaximumArmsResult, maximumAltered, maximumExpected] using at_input
theorem maximum_arms_refuted : ¬ WrongMaximumArms := by
  intro h
  have bad := maximum_arms_implies h
  simp [WrongMaximumArmsResult, maximumAltered, maximumExpected] at bad

theorem maximum_bound_at : runBlob maximumWrongBoundBlob 0 [.int .u64 2,.int .u64 1] 24 0 = maximumAltered := by clampKernelRfl
def WrongMaximumBoundResult : Prop := maximumAltered = maximumExpected
theorem maximum_bound_implies (h : WrongMaximumBound) : WrongMaximumBoundResult := by
  have at_input := h 2 1 0 maximum_n_valid maximum_bound_valid
  rw [maximum_bound_at] at at_input
  simpa [WrongMaximumBoundResult, maximumAltered, maximumExpected] using at_input
theorem maximum_bound_refuted : ¬ WrongMaximumBound := by
  intro h
  have bad := maximum_bound_implies h
  simp [WrongMaximumBoundResult, maximumAltered, maximumExpected] at bad

end SemRClampTransfer
