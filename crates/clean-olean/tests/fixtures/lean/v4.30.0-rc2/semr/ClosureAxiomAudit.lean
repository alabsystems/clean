/- Copyright 2026 Andrew Yates. Apache-2.0.
   Mechanical Ax0 dependency guards for quoted nominal construction, capture projection and
   its operational/run proof chain. No new axiom or native evaluation may
   replace these kernel proofs. Main imports this audit on every oracle build. -/
import ClosureConstruction

/-- info: 'SemR.intTy_code_injective' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.intTy_code_injective

/-- info: 'SemR.ty_beq_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SemR.ty_beq_exact

/-- info: 'SemR.tyListEq_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SemR.tyListEq_exact

/-- info: 'SemR.makesClosure_contract' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SemR.makesClosure_contract

/-- info: 'SemR.bindResults_success' does not depend on any axioms -/
#guard_msgs in
#print axioms SemR.bindResults_success

/-- info: 'SemR.makeClosureOn_success' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.makeClosureOn_success

/-- info: 'SemR.makeClosureStep_success' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.makeClosureStep_success

/-- info: 'SemR.makeClosure_step_success' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.makeClosure_step_success

/-- info: 'SemR.makeClosure_step_preserves_memory' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.makeClosure_step_preserves_memory

/-- info: 'SemR.makeClosure_step_exact_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.makeClosure_step_exact_result

/-- info: 'SemR.construction_module_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.construction_module_entry

/-- info: 'SemR.construction_module_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.construction_module_return

/-- info: 'SemR.construction_pointer_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.construction_pointer_exact

/-- info: 'SemR.construction_pointer_relational' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.construction_pointer_relational

/-- info: 'SemR.construction_pointer_return' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.construction_pointer_return

/-- info: 'SemR.construction_nominal_identity' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.construction_nominal_identity

/-- info: 'SemR.construction_missing_definition' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.construction_missing_definition

/-- info: 'SemR.construction_missing_apparent' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.construction_missing_apparent

/-- info: 'SemR.construction_missing_target' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.construction_missing_target

/-- info: 'SemR.construction_missing_physical' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.construction_missing_physical

/-- info: 'SemR.construction_bad_prefix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.construction_bad_prefix

/-- info: 'SemR.construction_bad_return' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.construction_bad_return

/-- info: 'SemR.construction_vararg_apparent' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.construction_vararg_apparent

/-- info: 'SemR.construction_vararg_physical' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.construction_vararg_physical

/-- info: 'SemR.construction_wrong_capture_type' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.construction_wrong_capture_type

/-- info: 'SemR.construction_wrong_capture_arity' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.construction_wrong_capture_arity

/-- info: 'SemR.construction_poison_capture' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.construction_poison_capture

/-- info: 'SemR.construction_missing_operand' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.construction_missing_operand

/-- info: 'SemR.construction_wrong_result_arity' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.construction_wrong_result_arity

/-- info: 'SemR.construction_instruction_v63_refused' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.construction_instruction_v63_refused

/-- info: 'SemR.makesClosure_complete' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.makesClosure_complete

/-- info: 'SemR.makesClosure_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.makesClosure_sound

/-- info: 'SemR.makeClosure_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.makeClosure_sound

/-- info: 'SemR.step_complete' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.step_complete

/-- info: 'SemR.step_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.step_sound

/-- info: 'SemR.run_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.run_sound

/-- info: 'SemR.run_complete' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.run_complete


/-- info: 'SemR.evalExtract_closure_of_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SemR.evalExtract_closure_of_checked

/-- info: 'SemR.extractClosureStep_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SemR.extractClosureStep_exact

/-- info: 'SemR.extractClosure_step_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SemR.extractClosure_step_exact

/-- info: 'SemR.extractClosure_step_preserves_memory' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SemR.extractClosure_step_preserves_memory

/-- info: 'SemR.closure_direct_pointer_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.closure_direct_pointer_return

/-- info: 'SemR.closure_adapter_pointer_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.closure_adapter_pointer_return

/-- info: 'SemR.closure_direct_pointer_return_any_memory' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.closure_direct_pointer_return_any_memory

/-- info: 'SemR.closure_extract_null' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.closure_extract_null

/-- info: 'SemR.closure_extract_wrong_result_type' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.closure_extract_wrong_result_type

/-- info: 'SemR.closure_extract_wrong_value_kind' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.closure_extract_wrong_value_kind

/-- info: 'SemR.closure_extract_target_is_not_a_field' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.closure_extract_target_is_not_a_field

/-- info: 'SemR.closure_extract_wrong_nominal_argument' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.closure_extract_wrong_nominal_argument

/-- info: 'SemR.closure_extract_unwritten' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.closure_extract_unwritten

/-- info: 'SemR.closure_extract_poison_aggregate' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.closure_extract_poison_aggregate

/-- info: 'SemR.closure_extract_does_not_invoke_target' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.closure_extract_does_not_invoke_target

/-- info: 'SemR.closure_extract_scalar_is_not_an_environment' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.closure_extract_scalar_is_not_an_environment

/-- info: 'SemR.closure_extract_nominal_capture_type_is_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SemR.closure_extract_nominal_capture_type_is_exact

/-- info: 'SemR.closure_direct_pointer_wrong_offset_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemR.closure_direct_pointer_wrong_offset_refuted
