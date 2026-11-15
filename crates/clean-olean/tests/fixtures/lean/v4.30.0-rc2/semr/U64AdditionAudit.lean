/- Copyright 2026 Andrew Yates. Apache-2.0.
   Focused kernel/refusal audit of the new canonical scalar theorem. -/
import U64Addition
namespace SemRU64AdditionAudit
open SemR SemRU64Addition
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

-- A retained proof for the exact old subject cannot prove a different valid
-- module, an unrelated function/root, or a changed actual return operand.
example : True := by
  fail_if_success
    have wrong : runFunction (module 8) 0 [.int .u64 0] 3 0 = .ret [.int .u64 7] :=
      original_return 0 0 (by decide)
  trivial
example : True := by
  fail_if_success
    have wrong : runFunction (module 7) 1 [.int .u64 0] 3 0 = .ret [.int .u64 7] :=
      original_return 0 0 (by decide)
  trivial
example : True := by
  fail_if_success
    have wrong : runFunction (module 7) 0 [.int .u64 0] 3 0 = .ret [.int .u64 8] :=
      original_return 0 0 (by decide)
  trivial
example : True := by
  fail_if_success
    have wrong : runFunction (module 7) 0 [.int .u64 0] 2 0 = .ret [.int .u64 7] :=
      original_return 0 0 (by decide)
  trivial
example : True := by
  fail_if_success
    have wrong : decode (originalBytes ++ [0]) = .ok (module 7) := original_decodes
  trivial

/-- The full input domain is admitted, and a value one beyond it refuses. -/
theorem full64_last :
    runFunction (module 7) 0 [.int .u64 (modulus 64 - 1)] 3 0 = .ret [.int .u64 6] := by
  have h := original_return (modulus 64 - 1) 0 (by decide)
  exact h

theorem invalid_input_refuses :
    runFunction (module 7) 0 [.int .u64 (modulus 64)] 3 0 =
      .typeError "TypeError: integer value is out of range for the target width" := rfl

theorem future_version_refuses :
    decode ([84,82,85,83,84,95,73,82,71,0,0,0]) =
      .error (.unsupported "wire_version") := rfl

/-- The previous wire64 header remains supported and requires a payload. -/
theorem current_version_requires_payload :
    decode ([84,82,85,83,84,95,73,82,64,0,0,0]) =
      .error (.malformed "unexpected end of input") := rfl

theorem invalid_tag_refuses :
    inst 63 #[] [71] = .err (.malformed "invalid Inst tag") := rfl

theorem v63_closure_refuses :
    inst 63 #[] [70,0,0,0] = .err (.unsupported "inst.make_closure") := rfl

theorem pre63_closure_malformed :
    inst 62 #[] [70,0,0,0] = .err (.malformed "invalid Inst tag") := rfl

/-- info: 'SemRU64Addition.original_decodes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemRU64Addition.original_decodes
/-- info: 'SemRU64Addition.current_decodes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemRU64Addition.current_decodes

/-- info: 'SemRU64Addition.run_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemRU64Addition.run_exact
/-- info: 'SemRU64Addition.original_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemRU64Addition.original_return
/-- info: 'SemRU64Addition.no_body_violation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemRU64Addition.no_body_violation
/-- info: 'SemRU64Addition.original_no_body_violation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemRU64Addition.original_no_body_violation
/-- info: 'SemRU64Addition.minirust_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemRU64Addition.minirust_add
end SemRU64AdditionAudit
