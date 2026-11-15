/-
  Normalize transfer controls using already checked canonical executions.
  Every original universal bad claim implies its concrete witness target.
  No new evaluator, domain assumption, or execution rule is introduced.
-/
import UnsignedDivisionArtifact

namespace SemRDivisionTransfer
open SemR UnsignedDivisionArtifact

theorem valid_input : 1048576 < 18446744073709551616 := by decide

def expected : Except DErr Out := .ok (.ret [.int .u64 1])
def altered : Except DErr Out := .ok (.ret [.int .u64 1048576])
def zeroOutcome : Except DErr Out := .ok (.panic "attempt to divide by zero")

theorem source_at_witness :
    runBlob rawBlob 0 [.int .u64 1048576] 17 0 = expected := by
  simpa [expected] using raw_correct 1048576 0 valid_input

/-- A normalized consequence of the actual source proof, not an assumed result. -/
theorem source_consequence : expected = expected :=
  source_at_witness.symm.trans source_at_witness

def WrongDivisorResult : Prop := altered = expected
def WrongZeroResult : Prop := zeroOutcome = expected
def WrongResultResult : Prop := altered = expected
def WrongContractResult : Prop := expected = altered

theorem divisor_implies_result (h : WrongDivisor) : WrongDivisorResult := by
  have at_input := h 1048576 0 valid_input
  rw [divisor_witness] at at_input
  simpa [WrongDivisorResult, altered, expected] using at_input

theorem zero_implies_result (h : WrongZero) : WrongZeroResult := by
  have at_input := h 1048576 0 valid_input
  rw [zero_panics] at at_input
  simpa [WrongZeroResult, zeroOutcome, expected] using at_input

theorem result_implies_result (h : WrongResult) : WrongResultResult := by
  have at_input := h 1048576 0 valid_input
  rw [result_witness] at at_input
  simpa [WrongResultResult, altered, expected] using at_input

theorem contract_implies_result (h : WrongContract) : WrongContractResult := by
  have at_input := h 1048576 0 valid_input
  rw [source_at_witness] at at_input
  exact at_input

end SemRDivisionTransfer
