-- SAT-COMP/ay incremental SAT witness merge soundness skeleton.
-- Partial witnesses from incremental/cube/refined solves may be merged into a
-- public SAT model only when frames, maps, defaults, projection evidence,
-- replay, archive digest, and original fingerprint evidence all agree.

def AyMIWMConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMIWMDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMIWMEquisat (left right : Prop) : Prop :=
  AyMIWMConj (left -> right) (right -> left)

def AyMIWMWitnessFrames
    (incrementalFrame cubeFrame refinementFrame : Prop) : Prop :=
  AyMIWMConj incrementalFrame (AyMIWMConj cubeFrame refinementFrame)

def AyMIWMVariableMap
    (partialVariableMap publicVariableMap mapAgreement : Prop) : Prop :=
  AyMIWMConj partialVariableMap
    (AyMIWMConj publicVariableMap mapAgreement)

def AyMIWMEliminatedDefaults
    (eliminatedVariables defaultAssignments defaultsComplete : Prop) : Prop :=
  AyMIWMConj eliminatedVariables
    (AyMIWMConj defaultAssignments defaultsComplete)

def AyMIWMProjectionReconstruction
    (projectionEvidence reconstructionEvidence mergeComplete : Prop) : Prop :=
  AyMIWMConj projectionEvidence
    (AyMIWMConj reconstructionEvidence mergeComplete)

def AyMIWMModelCheckerReplay (checkerAccepted replayTrace : Prop) : Prop :=
  AyMIWMConj checkerAccepted replayTrace

def AyMIWMArchiveDigest
    (archiveEntry witnessDigest digestAgreement : Prop) : Prop :=
  AyMIWMConj archiveEntry (AyMIWMConj witnessDigest digestAgreement)

def AyMIWMOriginalFingerprint
    (originalFingerprint mergedFingerprint fingerprintAgreement : Prop) :
    Prop :=
  AyMIWMConj originalFingerprint
    (AyMIWMConj mergedFingerprint fingerprintAgreement)

def AyMIWMMergeEvidence
    (framesOk mapOk defaultsOk projectionOk checkerOk digestOk fingerprintOk :
      Prop) : Prop :=
  AyMIWMConj framesOk
    (AyMIWMConj mapOk
      (AyMIWMConj defaultsOk
        (AyMIWMConj projectionOk
          (AyMIWMConj checkerOk
            (AyMIWMConj digestOk fingerprintOk)))))

def AyMIWMMergedSatPublication
    (mergeEvidence auditEntry publicSatModel : Prop) : Prop :=
  AyMIWMConj mergeEvidence (AyMIWMConj auditEntry publicSatModel)

def AyMIWMNoClaimDiagnostic (diagnostic publicClaim : Prop) : Prop :=
  AyMIWMConj diagnostic (publicClaim -> False)

def AyMIWMRecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMIWMConj reason recomputeRequest

theorem ay_miwm_conj_intro {left right : Prop} :
    left -> right -> AyMIWMConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_miwm_conj_left {left right : Prop} :
    AyMIWMConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_miwm_conj_right {left right : Prop} :
    AyMIWMConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_miwm_disj_left {left right : Prop} :
    left -> AyMIWMDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_miwm_disj_right {left right : Prop} :
    right -> AyMIWMDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_miwm_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMIWMEquisat left right :=
  fun hf hb => ay_miwm_conj_intro hf hb

theorem ay_miwm_equisat_forward {left right : Prop} :
    AyMIWMEquisat left right -> left -> right :=
  fun h => ay_miwm_conj_left h

theorem ay_miwm_equisat_backward {left right : Prop} :
    AyMIWMEquisat left right -> right -> left :=
  fun h => ay_miwm_conj_right h

theorem ay_miwm_witness_frames_intro
    {incrementalFrame cubeFrame refinementFrame : Prop} :
    incrementalFrame ->
    cubeFrame ->
    refinementFrame ->
    AyMIWMWitnessFrames incrementalFrame cubeFrame refinementFrame :=
  fun hincremental hcube hrefinement =>
    ay_miwm_conj_intro hincremental
      (ay_miwm_conj_intro hcube hrefinement)

theorem ay_miwm_witness_frames_incremental
    {incrementalFrame cubeFrame refinementFrame : Prop} :
    AyMIWMWitnessFrames incrementalFrame cubeFrame refinementFrame ->
    incrementalFrame :=
  fun h => ay_miwm_conj_left h

theorem ay_miwm_witness_frames_cube
    {incrementalFrame cubeFrame refinementFrame : Prop} :
    AyMIWMWitnessFrames incrementalFrame cubeFrame refinementFrame ->
    cubeFrame :=
  fun h => ay_miwm_conj_left (ay_miwm_conj_right h)

theorem ay_miwm_witness_frames_refinement
    {incrementalFrame cubeFrame refinementFrame : Prop} :
    AyMIWMWitnessFrames incrementalFrame cubeFrame refinementFrame ->
    refinementFrame :=
  fun h => ay_miwm_conj_right (ay_miwm_conj_right h)

theorem ay_miwm_variable_map_intro
    {partialVariableMap publicVariableMap mapAgreement : Prop} :
    partialVariableMap ->
    publicVariableMap ->
    mapAgreement ->
    AyMIWMVariableMap partialVariableMap publicVariableMap mapAgreement :=
  fun hpartial hpublic hagree =>
    ay_miwm_conj_intro hpartial (ay_miwm_conj_intro hpublic hagree)

theorem ay_miwm_variable_map_partial
    {partialVariableMap publicVariableMap mapAgreement : Prop} :
    AyMIWMVariableMap partialVariableMap publicVariableMap mapAgreement ->
    partialVariableMap :=
  fun h => ay_miwm_conj_left h

theorem ay_miwm_variable_map_public
    {partialVariableMap publicVariableMap mapAgreement : Prop} :
    AyMIWMVariableMap partialVariableMap publicVariableMap mapAgreement ->
    publicVariableMap :=
  fun h => ay_miwm_conj_left (ay_miwm_conj_right h)

theorem ay_miwm_variable_map_agreement
    {partialVariableMap publicVariableMap mapAgreement : Prop} :
    AyMIWMVariableMap partialVariableMap publicVariableMap mapAgreement ->
    mapAgreement :=
  fun h => ay_miwm_conj_right (ay_miwm_conj_right h)

theorem ay_miwm_eliminated_defaults_intro
    {eliminatedVariables defaultAssignments defaultsComplete : Prop} :
    eliminatedVariables ->
    defaultAssignments ->
    defaultsComplete ->
    AyMIWMEliminatedDefaults
      eliminatedVariables defaultAssignments defaultsComplete :=
  fun helim hdefaults hcomplete =>
    ay_miwm_conj_intro helim
      (ay_miwm_conj_intro hdefaults hcomplete)

theorem ay_miwm_eliminated_defaults_variables
    {eliminatedVariables defaultAssignments defaultsComplete : Prop} :
    AyMIWMEliminatedDefaults
      eliminatedVariables defaultAssignments defaultsComplete ->
    eliminatedVariables :=
  fun h => ay_miwm_conj_left h

theorem ay_miwm_eliminated_defaults_assignments
    {eliminatedVariables defaultAssignments defaultsComplete : Prop} :
    AyMIWMEliminatedDefaults
      eliminatedVariables defaultAssignments defaultsComplete ->
    defaultAssignments :=
  fun h => ay_miwm_conj_left (ay_miwm_conj_right h)

theorem ay_miwm_eliminated_defaults_complete
    {eliminatedVariables defaultAssignments defaultsComplete : Prop} :
    AyMIWMEliminatedDefaults
      eliminatedVariables defaultAssignments defaultsComplete ->
    defaultsComplete :=
  fun h => ay_miwm_conj_right (ay_miwm_conj_right h)

theorem ay_miwm_projection_reconstruction_intro
    {projectionEvidence reconstructionEvidence mergeComplete : Prop} :
    projectionEvidence ->
    reconstructionEvidence ->
    mergeComplete ->
    AyMIWMProjectionReconstruction
      projectionEvidence reconstructionEvidence mergeComplete :=
  fun hprojection hreconstruction hcomplete =>
    ay_miwm_conj_intro hprojection
      (ay_miwm_conj_intro hreconstruction hcomplete)

theorem ay_miwm_projection_reconstruction_projection
    {projectionEvidence reconstructionEvidence mergeComplete : Prop} :
    AyMIWMProjectionReconstruction
      projectionEvidence reconstructionEvidence mergeComplete ->
    projectionEvidence :=
  fun h => ay_miwm_conj_left h

theorem ay_miwm_projection_reconstruction_reconstruction
    {projectionEvidence reconstructionEvidence mergeComplete : Prop} :
    AyMIWMProjectionReconstruction
      projectionEvidence reconstructionEvidence mergeComplete ->
    reconstructionEvidence :=
  fun h => ay_miwm_conj_left (ay_miwm_conj_right h)

theorem ay_miwm_projection_reconstruction_complete
    {projectionEvidence reconstructionEvidence mergeComplete : Prop} :
    AyMIWMProjectionReconstruction
      projectionEvidence reconstructionEvidence mergeComplete ->
    mergeComplete :=
  fun h => ay_miwm_conj_right (ay_miwm_conj_right h)

theorem ay_miwm_model_checker_replay_intro
    {checkerAccepted replayTrace : Prop} :
    checkerAccepted ->
    replayTrace ->
    AyMIWMModelCheckerReplay checkerAccepted replayTrace :=
  fun haccepted htrace => ay_miwm_conj_intro haccepted htrace

theorem ay_miwm_model_checker_replay_accepted
    {checkerAccepted replayTrace : Prop} :
    AyMIWMModelCheckerReplay checkerAccepted replayTrace ->
    checkerAccepted :=
  fun h => ay_miwm_conj_left h

theorem ay_miwm_model_checker_replay_trace
    {checkerAccepted replayTrace : Prop} :
    AyMIWMModelCheckerReplay checkerAccepted replayTrace ->
    replayTrace :=
  fun h => ay_miwm_conj_right h

theorem ay_miwm_archive_digest_intro
    {archiveEntry witnessDigest digestAgreement : Prop} :
    archiveEntry ->
    witnessDigest ->
    digestAgreement ->
    AyMIWMArchiveDigest archiveEntry witnessDigest digestAgreement :=
  fun harchive hdigest hagree =>
    ay_miwm_conj_intro harchive (ay_miwm_conj_intro hdigest hagree)

theorem ay_miwm_archive_digest_entry
    {archiveEntry witnessDigest digestAgreement : Prop} :
    AyMIWMArchiveDigest archiveEntry witnessDigest digestAgreement ->
    archiveEntry :=
  fun h => ay_miwm_conj_left h

theorem ay_miwm_archive_digest_witness
    {archiveEntry witnessDigest digestAgreement : Prop} :
    AyMIWMArchiveDigest archiveEntry witnessDigest digestAgreement ->
    witnessDigest :=
  fun h => ay_miwm_conj_left (ay_miwm_conj_right h)

theorem ay_miwm_archive_digest_agreement
    {archiveEntry witnessDigest digestAgreement : Prop} :
    AyMIWMArchiveDigest archiveEntry witnessDigest digestAgreement ->
    digestAgreement :=
  fun h => ay_miwm_conj_right (ay_miwm_conj_right h)

theorem ay_miwm_original_fingerprint_intro
    {originalFingerprint mergedFingerprint fingerprintAgreement : Prop} :
    originalFingerprint ->
    mergedFingerprint ->
    fingerprintAgreement ->
    AyMIWMOriginalFingerprint
      originalFingerprint mergedFingerprint fingerprintAgreement :=
  fun horiginal hmerged hagree =>
    ay_miwm_conj_intro horiginal (ay_miwm_conj_intro hmerged hagree)

theorem ay_miwm_original_fingerprint_original
    {originalFingerprint mergedFingerprint fingerprintAgreement : Prop} :
    AyMIWMOriginalFingerprint
      originalFingerprint mergedFingerprint fingerprintAgreement ->
    originalFingerprint :=
  fun h => ay_miwm_conj_left h

theorem ay_miwm_original_fingerprint_merged
    {originalFingerprint mergedFingerprint fingerprintAgreement : Prop} :
    AyMIWMOriginalFingerprint
      originalFingerprint mergedFingerprint fingerprintAgreement ->
    mergedFingerprint :=
  fun h => ay_miwm_conj_left (ay_miwm_conj_right h)

theorem ay_miwm_original_fingerprint_agreement
    {originalFingerprint mergedFingerprint fingerprintAgreement : Prop} :
    AyMIWMOriginalFingerprint
      originalFingerprint mergedFingerprint fingerprintAgreement ->
    fingerprintAgreement :=
  fun h => ay_miwm_conj_right (ay_miwm_conj_right h)

theorem ay_miwm_merge_evidence_intro
    {framesOk mapOk defaultsOk projectionOk checkerOk digestOk fingerprintOk :
      Prop} :
    framesOk ->
    mapOk ->
    defaultsOk ->
    projectionOk ->
    checkerOk ->
    digestOk ->
    fingerprintOk ->
    AyMIWMMergeEvidence
      framesOk mapOk defaultsOk projectionOk checkerOk digestOk
      fingerprintOk :=
  fun hframes hmap hdefaults hprojection hchecker hdigest hfingerprint =>
    ay_miwm_conj_intro hframes
      (ay_miwm_conj_intro hmap
        (ay_miwm_conj_intro hdefaults
          (ay_miwm_conj_intro hprojection
            (ay_miwm_conj_intro hchecker
              (ay_miwm_conj_intro hdigest hfingerprint)))))

theorem ay_miwm_merge_evidence_frames
    {framesOk mapOk defaultsOk projectionOk checkerOk digestOk fingerprintOk :
      Prop} :
    AyMIWMMergeEvidence
      framesOk mapOk defaultsOk projectionOk checkerOk digestOk
      fingerprintOk ->
    framesOk :=
  fun h => ay_miwm_conj_left h

theorem ay_miwm_merge_evidence_map
    {framesOk mapOk defaultsOk projectionOk checkerOk digestOk fingerprintOk :
      Prop} :
    AyMIWMMergeEvidence
      framesOk mapOk defaultsOk projectionOk checkerOk digestOk
      fingerprintOk ->
    mapOk :=
  fun h => ay_miwm_conj_left (ay_miwm_conj_right h)

theorem ay_miwm_merge_evidence_defaults
    {framesOk mapOk defaultsOk projectionOk checkerOk digestOk fingerprintOk :
      Prop} :
    AyMIWMMergeEvidence
      framesOk mapOk defaultsOk projectionOk checkerOk digestOk
      fingerprintOk ->
    defaultsOk :=
  fun h => ay_miwm_conj_left (ay_miwm_conj_right (ay_miwm_conj_right h))

theorem ay_miwm_merge_evidence_projection
    {framesOk mapOk defaultsOk projectionOk checkerOk digestOk fingerprintOk :
      Prop} :
    AyMIWMMergeEvidence
      framesOk mapOk defaultsOk projectionOk checkerOk digestOk
      fingerprintOk ->
    projectionOk :=
  fun h =>
    ay_miwm_conj_left
      (ay_miwm_conj_right (ay_miwm_conj_right (ay_miwm_conj_right h)))

theorem ay_miwm_merge_evidence_checker
    {framesOk mapOk defaultsOk projectionOk checkerOk digestOk fingerprintOk :
      Prop} :
    AyMIWMMergeEvidence
      framesOk mapOk defaultsOk projectionOk checkerOk digestOk
      fingerprintOk ->
    checkerOk :=
  fun h =>
    ay_miwm_conj_left
      (ay_miwm_conj_right
        (ay_miwm_conj_right (ay_miwm_conj_right (ay_miwm_conj_right h))))

theorem ay_miwm_merge_evidence_digest
    {framesOk mapOk defaultsOk projectionOk checkerOk digestOk fingerprintOk :
      Prop} :
    AyMIWMMergeEvidence
      framesOk mapOk defaultsOk projectionOk checkerOk digestOk
      fingerprintOk ->
    digestOk :=
  fun h =>
    ay_miwm_conj_left
      (ay_miwm_conj_right
        (ay_miwm_conj_right
          (ay_miwm_conj_right (ay_miwm_conj_right (ay_miwm_conj_right h)))))

theorem ay_miwm_merge_evidence_fingerprint
    {framesOk mapOk defaultsOk projectionOk checkerOk digestOk fingerprintOk :
      Prop} :
    AyMIWMMergeEvidence
      framesOk mapOk defaultsOk projectionOk checkerOk digestOk
      fingerprintOk ->
    fingerprintOk :=
  fun h =>
    ay_miwm_conj_right
      (ay_miwm_conj_right
        (ay_miwm_conj_right
          (ay_miwm_conj_right (ay_miwm_conj_right (ay_miwm_conj_right h)))))

theorem ay_miwm_merged_sat_publication_intro
    {mergeEvidence auditEntry publicSatModel : Prop} :
    mergeEvidence ->
    auditEntry ->
    publicSatModel ->
    AyMIWMMergedSatPublication mergeEvidence auditEntry publicSatModel :=
  fun hevidence haudit hmodel =>
    ay_miwm_conj_intro hevidence (ay_miwm_conj_intro haudit hmodel)

theorem ay_miwm_merged_sat_publication_evidence
    {mergeEvidence auditEntry publicSatModel : Prop} :
    AyMIWMMergedSatPublication mergeEvidence auditEntry publicSatModel ->
    mergeEvidence :=
  fun h => ay_miwm_conj_left h

theorem ay_miwm_merged_sat_publication_audit
    {mergeEvidence auditEntry publicSatModel : Prop} :
    AyMIWMMergedSatPublication mergeEvidence auditEntry publicSatModel ->
    auditEntry :=
  fun h => ay_miwm_conj_left (ay_miwm_conj_right h)

theorem ay_miwm_merged_sat_publication_model
    {mergeEvidence auditEntry publicSatModel : Prop} :
    AyMIWMMergedSatPublication mergeEvidence auditEntry publicSatModel ->
    publicSatModel :=
  fun h => ay_miwm_conj_right (ay_miwm_conj_right h)

theorem ay_miwm_accepted_merge_validates_sat_publication
    {mergeEvidence auditEntry publicSatModel : Prop} :
    AyMIWMMergedSatPublication mergeEvidence auditEntry publicSatModel ->
    publicSatModel :=
  fun h => ay_miwm_merged_sat_publication_model h

theorem ay_miwm_publication_requires_frames
    {framesOk mapOk defaultsOk projectionOk checkerOk digestOk fingerprintOk
      auditEntry publicSatModel : Prop} :
    AyMIWMMergedSatPublication
      (AyMIWMMergeEvidence
        framesOk mapOk defaultsOk projectionOk checkerOk digestOk
        fingerprintOk)
      auditEntry
      publicSatModel ->
    framesOk :=
  fun h =>
    ay_miwm_merge_evidence_frames
      (ay_miwm_merged_sat_publication_evidence h)

theorem ay_miwm_publication_requires_map
    {framesOk mapOk defaultsOk projectionOk checkerOk digestOk fingerprintOk
      auditEntry publicSatModel : Prop} :
    AyMIWMMergedSatPublication
      (AyMIWMMergeEvidence
        framesOk mapOk defaultsOk projectionOk checkerOk digestOk
        fingerprintOk)
      auditEntry
      publicSatModel ->
    mapOk :=
  fun h =>
    ay_miwm_merge_evidence_map
      (ay_miwm_merged_sat_publication_evidence h)

theorem ay_miwm_publication_requires_defaults
    {framesOk mapOk defaultsOk projectionOk checkerOk digestOk fingerprintOk
      auditEntry publicSatModel : Prop} :
    AyMIWMMergedSatPublication
      (AyMIWMMergeEvidence
        framesOk mapOk defaultsOk projectionOk checkerOk digestOk
        fingerprintOk)
      auditEntry
      publicSatModel ->
    defaultsOk :=
  fun h =>
    ay_miwm_merge_evidence_defaults
      (ay_miwm_merged_sat_publication_evidence h)

theorem ay_miwm_publication_requires_projection
    {framesOk mapOk defaultsOk projectionOk checkerOk digestOk fingerprintOk
      auditEntry publicSatModel : Prop} :
    AyMIWMMergedSatPublication
      (AyMIWMMergeEvidence
        framesOk mapOk defaultsOk projectionOk checkerOk digestOk
        fingerprintOk)
      auditEntry
      publicSatModel ->
    projectionOk :=
  fun h =>
    ay_miwm_merge_evidence_projection
      (ay_miwm_merged_sat_publication_evidence h)

theorem ay_miwm_publication_requires_checker
    {framesOk mapOk defaultsOk projectionOk checkerOk digestOk fingerprintOk
      auditEntry publicSatModel : Prop} :
    AyMIWMMergedSatPublication
      (AyMIWMMergeEvidence
        framesOk mapOk defaultsOk projectionOk checkerOk digestOk
        fingerprintOk)
      auditEntry
      publicSatModel ->
    checkerOk :=
  fun h =>
    ay_miwm_merge_evidence_checker
      (ay_miwm_merged_sat_publication_evidence h)

theorem ay_miwm_publication_requires_digest
    {framesOk mapOk defaultsOk projectionOk checkerOk digestOk fingerprintOk
      auditEntry publicSatModel : Prop} :
    AyMIWMMergedSatPublication
      (AyMIWMMergeEvidence
        framesOk mapOk defaultsOk projectionOk checkerOk digestOk
        fingerprintOk)
      auditEntry
      publicSatModel ->
    digestOk :=
  fun h =>
    ay_miwm_merge_evidence_digest
      (ay_miwm_merged_sat_publication_evidence h)

theorem ay_miwm_publication_requires_fingerprint
    {framesOk mapOk defaultsOk projectionOk checkerOk digestOk fingerprintOk
      auditEntry publicSatModel : Prop} :
    AyMIWMMergedSatPublication
      (AyMIWMMergeEvidence
        framesOk mapOk defaultsOk projectionOk checkerOk digestOk
        fingerprintOk)
      auditEntry
      publicSatModel ->
    fingerprintOk :=
  fun h =>
    ay_miwm_merge_evidence_fingerprint
      (ay_miwm_merged_sat_publication_evidence h)

theorem ay_miwm_merged_sat_publication_sound_exact
    {mergeEvidence auditEntry publicSatModel : Prop} :
    AyMIWMEquisat
      (AyMIWMMergedSatPublication mergeEvidence auditEntry publicSatModel)
      (AyMIWMConj mergeEvidence (AyMIWMConj auditEntry publicSatModel)) :=
  ay_miwm_equisat_intro
    (fun h => h)
    (fun h => h)

theorem ay_miwm_no_claim_diagnostic_intro
    {diagnostic publicClaim : Prop} :
    diagnostic ->
    (publicClaim -> False) ->
    AyMIWMNoClaimDiagnostic diagnostic publicClaim :=
  fun hdiagnostic hblocks => ay_miwm_conj_intro hdiagnostic hblocks

theorem ay_miwm_no_claim_diagnostic_reason
    {diagnostic publicClaim : Prop} :
    AyMIWMNoClaimDiagnostic diagnostic publicClaim ->
    diagnostic :=
  fun h => ay_miwm_conj_left h

theorem ay_miwm_no_claim_diagnostic_blocks
    {diagnostic publicClaim : Prop} :
    AyMIWMNoClaimDiagnostic diagnostic publicClaim ->
    publicClaim ->
    False :=
  fun h => ay_miwm_conj_right h

theorem ay_miwm_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMIWMRecomputeObligation reason recomputeRequest :=
  fun hreason hrequest => ay_miwm_conj_intro hreason hrequest

theorem ay_miwm_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMIWMRecomputeObligation reason recomputeRequest ->
    reason :=
  fun h => ay_miwm_conj_left h

theorem ay_miwm_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMIWMRecomputeObligation reason recomputeRequest ->
    recomputeRequest :=
  fun h => ay_miwm_conj_right h

theorem ay_miwm_conflicting_assignments_recompute
    {conflictingAssignments recomputeRequest : Prop} :
    conflictingAssignments ->
    recomputeRequest ->
    AyMIWMRecomputeObligation conflictingAssignments recomputeRequest :=
  fun hconflict hrecompute =>
    ay_miwm_recompute_obligation_intro hconflict hrecompute

theorem ay_miwm_conflicting_assignments_no_claim
    {conflictingAssignments publicClaim : Prop} :
    conflictingAssignments ->
    (conflictingAssignments -> publicClaim -> False) ->
    AyMIWMNoClaimDiagnostic conflictingAssignments publicClaim :=
  fun hconflict hblocks =>
    ay_miwm_no_claim_diagnostic_intro hconflict (hblocks hconflict)

theorem ay_miwm_stale_frames_no_claim
    {staleFrames publicClaim : Prop} :
    staleFrames ->
    (staleFrames -> publicClaim -> False) ->
    AyMIWMNoClaimDiagnostic staleFrames publicClaim :=
  fun hstale hblocks =>
    ay_miwm_no_claim_diagnostic_intro hstale (hblocks hstale)

theorem ay_miwm_missing_defaults_no_claim
    {missingDefaults publicClaim : Prop} :
    missingDefaults ->
    (missingDefaults -> publicClaim -> False) ->
    AyMIWMNoClaimDiagnostic missingDefaults publicClaim :=
  fun hmissing hblocks =>
    ay_miwm_no_claim_diagnostic_intro hmissing (hblocks hmissing)

theorem ay_miwm_map_mismatch_no_claim
    {mapMismatch publicClaim : Prop} :
    mapMismatch ->
    (mapMismatch -> publicClaim -> False) ->
    AyMIWMNoClaimDiagnostic mapMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_miwm_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_miwm_checker_rejection_no_claim
    {checkerRejection publicClaim : Prop} :
    checkerRejection ->
    (checkerRejection -> publicClaim -> False) ->
    AyMIWMNoClaimDiagnostic checkerRejection publicClaim :=
  fun hreject hblocks =>
    ay_miwm_no_claim_diagnostic_intro hreject (hblocks hreject)

theorem ay_miwm_fingerprint_mismatch_no_claim
    {fingerprintMismatch publicClaim : Prop} :
    fingerprintMismatch ->
    (fingerprintMismatch -> publicClaim -> False) ->
    AyMIWMNoClaimDiagnostic fingerprintMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_miwm_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_miwm_diagnostic_blocks_public_claim
    {diagnostic publicClaim : Prop} :
    AyMIWMNoClaimDiagnostic diagnostic publicClaim ->
    publicClaim ->
    False :=
  fun h hclaim => ay_miwm_no_claim_diagnostic_blocks h hclaim

theorem ay_miwm_bad_merge_no_stale_sat_publication
    {conflictingAssignments staleFrames missingDefaults mapMismatch
      checkerRejection fingerprintMismatch publicClaim : Prop} :
    (conflictingAssignments -> publicClaim -> False) ->
    (staleFrames -> publicClaim -> False) ->
    (missingDefaults -> publicClaim -> False) ->
    (mapMismatch -> publicClaim -> False) ->
    (checkerRejection -> publicClaim -> False) ->
    (fingerprintMismatch -> publicClaim -> False) ->
    AyMIWMConj
      (conflictingAssignments ->
        AyMIWMNoClaimDiagnostic conflictingAssignments publicClaim)
      (AyMIWMConj
        (staleFrames ->
          AyMIWMNoClaimDiagnostic staleFrames publicClaim)
        (AyMIWMConj
          (missingDefaults ->
            AyMIWMNoClaimDiagnostic missingDefaults publicClaim)
          (AyMIWMConj
            (mapMismatch ->
              AyMIWMNoClaimDiagnostic mapMismatch publicClaim)
            (AyMIWMConj
              (checkerRejection ->
                AyMIWMNoClaimDiagnostic checkerRejection publicClaim)
              (fingerprintMismatch ->
                AyMIWMNoClaimDiagnostic
                  fingerprintMismatch publicClaim))))) :=
  fun hconflict hframes hdefaults hmap hchecker hfingerprint =>
    ay_miwm_conj_intro
      (fun h => ay_miwm_conflicting_assignments_no_claim h hconflict)
      (ay_miwm_conj_intro
        (fun h => ay_miwm_stale_frames_no_claim h hframes)
        (ay_miwm_conj_intro
          (fun h => ay_miwm_missing_defaults_no_claim h hdefaults)
          (ay_miwm_conj_intro
            (fun h => ay_miwm_map_mismatch_no_claim h hmap)
            (ay_miwm_conj_intro
              (fun h => ay_miwm_checker_rejection_no_claim h hchecker)
              (fun h =>
                ay_miwm_fingerprint_mismatch_no_claim h hfingerprint)))))
