/- Parser controls for non-authoritative compiler bookkeeping.
   Copyright 2026 Andrew Yates. Apache-2.0. -/
import SemR

namespace SemRMetadataCheck
open SemR

theorem scalar_catalog : scalarMetadataType 38 #[] [5] = .ok () [] := rfl
theorem pointer_catalog_refuses :
    scalarMetadataType 38 #[] [13] = .err (.unsupported "types.non_scalar") := rfl
theorem compound_catalog_refuses :
    scalarMetadataType 38 #[] [255] = .err (.unsupported "ty.compound") := rfl
theorem invalid_catalog_tag :
    scalarMetadataType 38 #[] [254] = .err (.malformed "invalid Ty tag") := rfl
theorem catalog_length_refuses :
    counted scalarMetadataType 38 #[] [2,5] =
      .err (.malformed "declared count exceeds the input") := rfl
theorem pure_annotation : proofAnnotation 38 #[] [10] = .ok () [] := rfl
theorem invalid_annotation_tag :
    proofAnnotation 38 #[] [255] = .err (.malformed "invalid ProofAnnotation tag") := rfl
theorem text_formula : proofFormulaMetadata 38 #[[], []] [0,1,0,0] = .ok () [] := rfl
theorem empty_typed_formula : proofFormulaMetadata 41 #[[], []] [0,1,0,0,0] = .ok () [] := rfl
theorem scalar_param_binding :
    proofFormulaMetadata 41 #[[], []] [0,1,0,0,1,0,2,32,0,0] = .ok () [] := rfl
theorem scalar_result_binding :
    proofFormulaMetadata 41 #[[], []] [0,1,0,0,1,0,2,64,1,0] = .ok () [] := rfl
theorem bool_binding :
    proofFormulaMetadata 41 #[[], []] [0,1,0,0,1,0,0,0,0] = .ok () [] := rfl
theorem truncated_binding_refuses :
    proofFormulaMetadata 41 #[[], []] [0,1,0,0,1,0] =
      .err (.malformed "unexpected end of input") := rfl
theorem compound_binding_refuses :
    proofFormulaMetadata 41 #[[], []] [0,1,0,0,1,0,3] =
      .err (.unsupported "obligation.binding_sort") := rfl
theorem non_machine_width_refuses :
    proofFormulaMetadata 41 #[[], []] [0,1,0,0,1,0,2,0] =
      .err (.unsupported "obligation.binding_width") := rfl
theorem world_binding_refuses :
    proofFormulaMetadata 41 #[[], []] [0,1,0,0,1,0,0,3] =
      .err (.unsupported "obligation.binding_place") := rfl
theorem invalid_binding_sort :
    proofFormulaMetadata 41 #[[], []] [0,1,0,0,1,0,255] =
      .err (.malformed "invalid ClauseSort tag") := rfl
theorem invalid_binding_place :
    proofFormulaMetadata 41 #[[], []] [0,1,0,0,1,0,0,255] =
      .err (.malformed "invalid ClausePlace tag") := rfl
theorem assume_operand : inst 41 #[] [28,5,7] = .ok (.assume 5) [7] := rfl
theorem truncated_assume_operand :
    inst 41 #[] [28] = .err (.malformed "unexpected end of input") := rfl
theorem noncanonical_assume_operand :
    inst 41 #[] [28,128,0] = .err (.malformed "non-canonical varint encoding") := rfl
theorem invalid_formula_option :
    proofFormulaMetadata 38 #[[], []] [0,1,2] = .err (.malformed "invalid tag") := rfl
theorem truncated_formula_option :
    proofFormulaMetadata 38 #[[], []] [0,1,1] =
      .err (.malformed "unexpected end of input") := rfl

end SemRMetadataCheck
