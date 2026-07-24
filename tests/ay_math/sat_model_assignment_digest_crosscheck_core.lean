-- SAT-COMP/ay SAT model assignment digest crosscheck soundness skeleton.
-- A public SAT result is admissible only when assignment digest, original
-- variable map, eliminated/default reconstruction, witness frames, checker
-- replay, and stable original-instance fingerprint evidence all agree.

def AyMADCConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMADCDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMADCEquisat (left right : Prop) : Prop :=
  AyMADCConj (left -> right) (right -> left)

def AyMADCAssignmentDigest
    (assignmentArtifact digestValue digestAgreement : Prop) : Prop :=
  AyMADCConj assignmentArtifact
    (AyMADCConj digestValue digestAgreement)

def AyMADCOriginalVariableMap
    (solverVariableMap originalVariableMap mapAgreement : Prop) : Prop :=
  AyMADCConj solverVariableMap
    (AyMADCConj originalVariableMap mapAgreement)

def AyMADCEliminatedReconstruction
    (eliminatedVariables defaultValues reconstructionWitness : Prop) : Prop :=
  AyMADCConj eliminatedVariables
    (AyMADCConj defaultValues reconstructionWitness)

def AyMADCWitnessFrames
    (incrementalFrame cubeFrame refinementFrame : Prop) : Prop :=
  AyMADCConj incrementalFrame (AyMADCConj cubeFrame refinementFrame)

def AyMADCModelCheckerReplay (checkerAccepted replayTrace : Prop) : Prop :=
  AyMADCConj checkerAccepted replayTrace

def AyMADCOriginalInstanceFingerprint
    (originalFingerprint artifactFingerprint fingerprintStable : Prop) :
    Prop :=
  AyMADCConj originalFingerprint
    (AyMADCConj artifactFingerprint fingerprintStable)

def AyMADCProjectionReconstruction
    (projectedAssignment reconstructedAssignment originalModel : Prop) :
    Prop :=
  AyMADCConj projectedAssignment
    (AyMADCConj reconstructedAssignment originalModel)

def AyMADCCrosscheckEvidence
    (digestOk mapOk reconstructionOk framesOk replayOk fingerprintOk : Prop) :
    Prop :=
  AyMADCConj digestOk
    (AyMADCConj mapOk
      (AyMADCConj reconstructionOk
        (AyMADCConj framesOk
          (AyMADCConj replayOk fingerprintOk))))

def AyMADCAdmissibleSatResult
    (crosscheckEvidence auditEntry publicSatModel : Prop) : Prop :=
  AyMADCConj crosscheckEvidence (AyMADCConj auditEntry publicSatModel)

def AyMADCNoClaimDiagnostic (diagnostic publicClaim : Prop) : Prop :=
  AyMADCConj diagnostic (publicClaim -> False)

def AyMADCRecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMADCConj reason recomputeRequest

theorem ay_madc_conj_intro {left right : Prop} :
    left -> right -> AyMADCConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_madc_conj_left {left right : Prop} :
    AyMADCConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_madc_conj_right {left right : Prop} :
    AyMADCConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_madc_disj_left {left right : Prop} :
    left -> AyMADCDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_madc_disj_right {left right : Prop} :
    right -> AyMADCDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_madc_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMADCEquisat left right :=
  fun hf hb => ay_madc_conj_intro hf hb

theorem ay_madc_equisat_forward {left right : Prop} :
    AyMADCEquisat left right -> left -> right :=
  fun h => ay_madc_conj_left h

theorem ay_madc_equisat_backward {left right : Prop} :
    AyMADCEquisat left right -> right -> left :=
  fun h => ay_madc_conj_right h

theorem ay_madc_assignment_digest_intro
    {assignmentArtifact digestValue digestAgreement : Prop} :
    assignmentArtifact ->
    digestValue ->
    digestAgreement ->
    AyMADCAssignmentDigest
      assignmentArtifact digestValue digestAgreement :=
  fun hartifact hdigest hagree =>
    ay_madc_conj_intro hartifact
      (ay_madc_conj_intro hdigest hagree)

theorem ay_madc_assignment_digest_artifact
    {assignmentArtifact digestValue digestAgreement : Prop} :
    AyMADCAssignmentDigest
      assignmentArtifact digestValue digestAgreement ->
    assignmentArtifact :=
  fun h => ay_madc_conj_left h

theorem ay_madc_assignment_digest_value
    {assignmentArtifact digestValue digestAgreement : Prop} :
    AyMADCAssignmentDigest
      assignmentArtifact digestValue digestAgreement ->
    digestValue :=
  fun h => ay_madc_conj_left (ay_madc_conj_right h)

theorem ay_madc_assignment_digest_agreement
    {assignmentArtifact digestValue digestAgreement : Prop} :
    AyMADCAssignmentDigest
      assignmentArtifact digestValue digestAgreement ->
    digestAgreement :=
  fun h => ay_madc_conj_right (ay_madc_conj_right h)

theorem ay_madc_original_variable_map_intro
    {solverVariableMap originalVariableMap mapAgreement : Prop} :
    solverVariableMap ->
    originalVariableMap ->
    mapAgreement ->
    AyMADCOriginalVariableMap
      solverVariableMap originalVariableMap mapAgreement :=
  fun hsolver horiginal hagree =>
    ay_madc_conj_intro hsolver
      (ay_madc_conj_intro horiginal hagree)

theorem ay_madc_original_variable_map_solver
    {solverVariableMap originalVariableMap mapAgreement : Prop} :
    AyMADCOriginalVariableMap
      solverVariableMap originalVariableMap mapAgreement ->
    solverVariableMap :=
  fun h => ay_madc_conj_left h

theorem ay_madc_original_variable_map_original
    {solverVariableMap originalVariableMap mapAgreement : Prop} :
    AyMADCOriginalVariableMap
      solverVariableMap originalVariableMap mapAgreement ->
    originalVariableMap :=
  fun h => ay_madc_conj_left (ay_madc_conj_right h)

theorem ay_madc_original_variable_map_agreement
    {solverVariableMap originalVariableMap mapAgreement : Prop} :
    AyMADCOriginalVariableMap
      solverVariableMap originalVariableMap mapAgreement ->
    mapAgreement :=
  fun h => ay_madc_conj_right (ay_madc_conj_right h)

theorem ay_madc_eliminated_reconstruction_intro
    {eliminatedVariables defaultValues reconstructionWitness : Prop} :
    eliminatedVariables ->
    defaultValues ->
    reconstructionWitness ->
    AyMADCEliminatedReconstruction
      eliminatedVariables defaultValues reconstructionWitness :=
  fun helim hdefaults hreconstruct =>
    ay_madc_conj_intro helim
      (ay_madc_conj_intro hdefaults hreconstruct)

theorem ay_madc_eliminated_reconstruction_variables
    {eliminatedVariables defaultValues reconstructionWitness : Prop} :
    AyMADCEliminatedReconstruction
      eliminatedVariables defaultValues reconstructionWitness ->
    eliminatedVariables :=
  fun h => ay_madc_conj_left h

theorem ay_madc_eliminated_reconstruction_defaults
    {eliminatedVariables defaultValues reconstructionWitness : Prop} :
    AyMADCEliminatedReconstruction
      eliminatedVariables defaultValues reconstructionWitness ->
    defaultValues :=
  fun h => ay_madc_conj_left (ay_madc_conj_right h)

theorem ay_madc_eliminated_reconstruction_witness
    {eliminatedVariables defaultValues reconstructionWitness : Prop} :
    AyMADCEliminatedReconstruction
      eliminatedVariables defaultValues reconstructionWitness ->
    reconstructionWitness :=
  fun h => ay_madc_conj_right (ay_madc_conj_right h)

theorem ay_madc_witness_frames_intro
    {incrementalFrame cubeFrame refinementFrame : Prop} :
    incrementalFrame ->
    cubeFrame ->
    refinementFrame ->
    AyMADCWitnessFrames incrementalFrame cubeFrame refinementFrame :=
  fun hincremental hcube hrefinement =>
    ay_madc_conj_intro hincremental
      (ay_madc_conj_intro hcube hrefinement)

theorem ay_madc_witness_frames_incremental
    {incrementalFrame cubeFrame refinementFrame : Prop} :
    AyMADCWitnessFrames incrementalFrame cubeFrame refinementFrame ->
    incrementalFrame :=
  fun h => ay_madc_conj_left h

theorem ay_madc_witness_frames_cube
    {incrementalFrame cubeFrame refinementFrame : Prop} :
    AyMADCWitnessFrames incrementalFrame cubeFrame refinementFrame ->
    cubeFrame :=
  fun h => ay_madc_conj_left (ay_madc_conj_right h)

theorem ay_madc_witness_frames_refinement
    {incrementalFrame cubeFrame refinementFrame : Prop} :
    AyMADCWitnessFrames incrementalFrame cubeFrame refinementFrame ->
    refinementFrame :=
  fun h => ay_madc_conj_right (ay_madc_conj_right h)

theorem ay_madc_model_checker_replay_intro
    {checkerAccepted replayTrace : Prop} :
    checkerAccepted ->
    replayTrace ->
    AyMADCModelCheckerReplay checkerAccepted replayTrace :=
  fun haccepted htrace => ay_madc_conj_intro haccepted htrace

theorem ay_madc_model_checker_replay_accepted
    {checkerAccepted replayTrace : Prop} :
    AyMADCModelCheckerReplay checkerAccepted replayTrace ->
    checkerAccepted :=
  fun h => ay_madc_conj_left h

theorem ay_madc_model_checker_replay_trace
    {checkerAccepted replayTrace : Prop} :
    AyMADCModelCheckerReplay checkerAccepted replayTrace ->
    replayTrace :=
  fun h => ay_madc_conj_right h

theorem ay_madc_original_instance_fingerprint_intro
    {originalFingerprint artifactFingerprint fingerprintStable : Prop} :
    originalFingerprint ->
    artifactFingerprint ->
    fingerprintStable ->
    AyMADCOriginalInstanceFingerprint
      originalFingerprint artifactFingerprint fingerprintStable :=
  fun horiginal hartifact hstable =>
    ay_madc_conj_intro horiginal
      (ay_madc_conj_intro hartifact hstable)

theorem ay_madc_original_instance_fingerprint_original
    {originalFingerprint artifactFingerprint fingerprintStable : Prop} :
    AyMADCOriginalInstanceFingerprint
      originalFingerprint artifactFingerprint fingerprintStable ->
    originalFingerprint :=
  fun h => ay_madc_conj_left h

theorem ay_madc_original_instance_fingerprint_artifact
    {originalFingerprint artifactFingerprint fingerprintStable : Prop} :
    AyMADCOriginalInstanceFingerprint
      originalFingerprint artifactFingerprint fingerprintStable ->
    artifactFingerprint :=
  fun h => ay_madc_conj_left (ay_madc_conj_right h)

theorem ay_madc_original_instance_fingerprint_stable
    {originalFingerprint artifactFingerprint fingerprintStable : Prop} :
    AyMADCOriginalInstanceFingerprint
      originalFingerprint artifactFingerprint fingerprintStable ->
    fingerprintStable :=
  fun h => ay_madc_conj_right (ay_madc_conj_right h)

theorem ay_madc_projection_reconstruction_intro
    {projectedAssignment reconstructedAssignment originalModel : Prop} :
    projectedAssignment ->
    reconstructedAssignment ->
    originalModel ->
    AyMADCProjectionReconstruction
      projectedAssignment reconstructedAssignment originalModel :=
  fun hprojected hreconstructed horiginal =>
    ay_madc_conj_intro hprojected
      (ay_madc_conj_intro hreconstructed horiginal)

theorem ay_madc_projection_reconstruction_projected
    {projectedAssignment reconstructedAssignment originalModel : Prop} :
    AyMADCProjectionReconstruction
      projectedAssignment reconstructedAssignment originalModel ->
    projectedAssignment :=
  fun h => ay_madc_conj_left h

theorem ay_madc_projection_reconstruction_reconstructed
    {projectedAssignment reconstructedAssignment originalModel : Prop} :
    AyMADCProjectionReconstruction
      projectedAssignment reconstructedAssignment originalModel ->
    reconstructedAssignment :=
  fun h => ay_madc_conj_left (ay_madc_conj_right h)

theorem ay_madc_projection_reconstruction_original
    {projectedAssignment reconstructedAssignment originalModel : Prop} :
    AyMADCProjectionReconstruction
      projectedAssignment reconstructedAssignment originalModel ->
    originalModel :=
  fun h => ay_madc_conj_right (ay_madc_conj_right h)

theorem ay_madc_crosscheck_evidence_intro
    {digestOk mapOk reconstructionOk framesOk replayOk fingerprintOk : Prop} :
    digestOk ->
    mapOk ->
    reconstructionOk ->
    framesOk ->
    replayOk ->
    fingerprintOk ->
    AyMADCCrosscheckEvidence
      digestOk mapOk reconstructionOk framesOk replayOk fingerprintOk :=
  fun hdigest hmap hreconstruction hframes hreplay hfingerprint =>
    ay_madc_conj_intro hdigest
      (ay_madc_conj_intro hmap
        (ay_madc_conj_intro hreconstruction
          (ay_madc_conj_intro hframes
            (ay_madc_conj_intro hreplay hfingerprint))))

theorem ay_madc_crosscheck_evidence_digest
    {digestOk mapOk reconstructionOk framesOk replayOk fingerprintOk : Prop} :
    AyMADCCrosscheckEvidence
      digestOk mapOk reconstructionOk framesOk replayOk fingerprintOk ->
    digestOk :=
  fun h => ay_madc_conj_left h

theorem ay_madc_crosscheck_evidence_map
    {digestOk mapOk reconstructionOk framesOk replayOk fingerprintOk : Prop} :
    AyMADCCrosscheckEvidence
      digestOk mapOk reconstructionOk framesOk replayOk fingerprintOk ->
    mapOk :=
  fun h => ay_madc_conj_left (ay_madc_conj_right h)

theorem ay_madc_crosscheck_evidence_reconstruction
    {digestOk mapOk reconstructionOk framesOk replayOk fingerprintOk : Prop} :
    AyMADCCrosscheckEvidence
      digestOk mapOk reconstructionOk framesOk replayOk fingerprintOk ->
    reconstructionOk :=
  fun h => ay_madc_conj_left (ay_madc_conj_right (ay_madc_conj_right h))

theorem ay_madc_crosscheck_evidence_frames
    {digestOk mapOk reconstructionOk framesOk replayOk fingerprintOk : Prop} :
    AyMADCCrosscheckEvidence
      digestOk mapOk reconstructionOk framesOk replayOk fingerprintOk ->
    framesOk :=
  fun h =>
    ay_madc_conj_left
      (ay_madc_conj_right (ay_madc_conj_right (ay_madc_conj_right h)))

theorem ay_madc_crosscheck_evidence_replay
    {digestOk mapOk reconstructionOk framesOk replayOk fingerprintOk : Prop} :
    AyMADCCrosscheckEvidence
      digestOk mapOk reconstructionOk framesOk replayOk fingerprintOk ->
    replayOk :=
  fun h =>
    ay_madc_conj_left
      (ay_madc_conj_right
        (ay_madc_conj_right (ay_madc_conj_right (ay_madc_conj_right h))))

theorem ay_madc_crosscheck_evidence_fingerprint
    {digestOk mapOk reconstructionOk framesOk replayOk fingerprintOk : Prop} :
    AyMADCCrosscheckEvidence
      digestOk mapOk reconstructionOk framesOk replayOk fingerprintOk ->
    fingerprintOk :=
  fun h =>
    ay_madc_conj_right
      (ay_madc_conj_right
        (ay_madc_conj_right (ay_madc_conj_right (ay_madc_conj_right h))))

theorem ay_madc_admissible_sat_result_intro
    {crosscheckEvidence auditEntry publicSatModel : Prop} :
    crosscheckEvidence ->
    auditEntry ->
    publicSatModel ->
    AyMADCAdmissibleSatResult
      crosscheckEvidence auditEntry publicSatModel :=
  fun hevidence haudit hmodel =>
    ay_madc_conj_intro hevidence (ay_madc_conj_intro haudit hmodel)

theorem ay_madc_admissible_sat_result_evidence
    {crosscheckEvidence auditEntry publicSatModel : Prop} :
    AyMADCAdmissibleSatResult
      crosscheckEvidence auditEntry publicSatModel ->
    crosscheckEvidence :=
  fun h => ay_madc_conj_left h

theorem ay_madc_admissible_sat_result_audit
    {crosscheckEvidence auditEntry publicSatModel : Prop} :
    AyMADCAdmissibleSatResult
      crosscheckEvidence auditEntry publicSatModel ->
    auditEntry :=
  fun h => ay_madc_conj_left (ay_madc_conj_right h)

theorem ay_madc_admissible_sat_result_model
    {crosscheckEvidence auditEntry publicSatModel : Prop} :
    AyMADCAdmissibleSatResult
      crosscheckEvidence auditEntry publicSatModel ->
    publicSatModel :=
  fun h => ay_madc_conj_right (ay_madc_conj_right h)

theorem ay_madc_accepted_crosscheck_validates_sat_publication
    {crosscheckEvidence auditEntry publicSatModel : Prop} :
    AyMADCAdmissibleSatResult
      crosscheckEvidence auditEntry publicSatModel ->
    publicSatModel :=
  fun h => ay_madc_admissible_sat_result_model h

theorem ay_madc_model_projection_reconstruction_sound
    {projectedAssignment reconstructedAssignment originalModel : Prop} :
    AyMADCProjectionReconstruction
      projectedAssignment reconstructedAssignment originalModel ->
    originalModel :=
  fun h => ay_madc_projection_reconstruction_original h

theorem ay_madc_publication_requires_digest
    {digestOk mapOk reconstructionOk framesOk replayOk fingerprintOk
      auditEntry publicSatModel : Prop} :
    AyMADCAdmissibleSatResult
      (AyMADCCrosscheckEvidence
        digestOk mapOk reconstructionOk framesOk replayOk fingerprintOk)
      auditEntry
      publicSatModel ->
    digestOk :=
  fun h =>
    ay_madc_crosscheck_evidence_digest
      (ay_madc_admissible_sat_result_evidence h)

theorem ay_madc_publication_requires_map
    {digestOk mapOk reconstructionOk framesOk replayOk fingerprintOk
      auditEntry publicSatModel : Prop} :
    AyMADCAdmissibleSatResult
      (AyMADCCrosscheckEvidence
        digestOk mapOk reconstructionOk framesOk replayOk fingerprintOk)
      auditEntry
      publicSatModel ->
    mapOk :=
  fun h =>
    ay_madc_crosscheck_evidence_map
      (ay_madc_admissible_sat_result_evidence h)

theorem ay_madc_publication_requires_reconstruction
    {digestOk mapOk reconstructionOk framesOk replayOk fingerprintOk
      auditEntry publicSatModel : Prop} :
    AyMADCAdmissibleSatResult
      (AyMADCCrosscheckEvidence
        digestOk mapOk reconstructionOk framesOk replayOk fingerprintOk)
      auditEntry
      publicSatModel ->
    reconstructionOk :=
  fun h =>
    ay_madc_crosscheck_evidence_reconstruction
      (ay_madc_admissible_sat_result_evidence h)

theorem ay_madc_publication_requires_frames
    {digestOk mapOk reconstructionOk framesOk replayOk fingerprintOk
      auditEntry publicSatModel : Prop} :
    AyMADCAdmissibleSatResult
      (AyMADCCrosscheckEvidence
        digestOk mapOk reconstructionOk framesOk replayOk fingerprintOk)
      auditEntry
      publicSatModel ->
    framesOk :=
  fun h =>
    ay_madc_crosscheck_evidence_frames
      (ay_madc_admissible_sat_result_evidence h)

theorem ay_madc_publication_requires_replay
    {digestOk mapOk reconstructionOk framesOk replayOk fingerprintOk
      auditEntry publicSatModel : Prop} :
    AyMADCAdmissibleSatResult
      (AyMADCCrosscheckEvidence
        digestOk mapOk reconstructionOk framesOk replayOk fingerprintOk)
      auditEntry
      publicSatModel ->
    replayOk :=
  fun h =>
    ay_madc_crosscheck_evidence_replay
      (ay_madc_admissible_sat_result_evidence h)

theorem ay_madc_publication_requires_fingerprint
    {digestOk mapOk reconstructionOk framesOk replayOk fingerprintOk
      auditEntry publicSatModel : Prop} :
    AyMADCAdmissibleSatResult
      (AyMADCCrosscheckEvidence
        digestOk mapOk reconstructionOk framesOk replayOk fingerprintOk)
      auditEntry
      publicSatModel ->
    fingerprintOk :=
  fun h =>
    ay_madc_crosscheck_evidence_fingerprint
      (ay_madc_admissible_sat_result_evidence h)

theorem ay_madc_admissible_sat_result_sound_exact
    {crosscheckEvidence auditEntry publicSatModel : Prop} :
    AyMADCEquisat
      (AyMADCAdmissibleSatResult
        crosscheckEvidence auditEntry publicSatModel)
      (AyMADCConj crosscheckEvidence
        (AyMADCConj auditEntry publicSatModel)) :=
  ay_madc_equisat_intro
    (fun h => h)
    (fun h => h)

theorem ay_madc_no_claim_diagnostic_intro
    {diagnostic publicClaim : Prop} :
    diagnostic ->
    (publicClaim -> False) ->
    AyMADCNoClaimDiagnostic diagnostic publicClaim :=
  fun hdiagnostic hblocks => ay_madc_conj_intro hdiagnostic hblocks

theorem ay_madc_no_claim_diagnostic_reason
    {diagnostic publicClaim : Prop} :
    AyMADCNoClaimDiagnostic diagnostic publicClaim ->
    diagnostic :=
  fun h => ay_madc_conj_left h

theorem ay_madc_no_claim_diagnostic_blocks
    {diagnostic publicClaim : Prop} :
    AyMADCNoClaimDiagnostic diagnostic publicClaim ->
    publicClaim ->
    False :=
  fun h => ay_madc_conj_right h

theorem ay_madc_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMADCRecomputeObligation reason recomputeRequest :=
  fun hreason hrequest => ay_madc_conj_intro hreason hrequest

theorem ay_madc_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMADCRecomputeObligation reason recomputeRequest ->
    reason :=
  fun h => ay_madc_conj_left h

theorem ay_madc_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMADCRecomputeObligation reason recomputeRequest ->
    recomputeRequest :=
  fun h => ay_madc_conj_right h

theorem ay_madc_digest_mismatch_recompute
    {digestMismatch recomputeRequest : Prop} :
    digestMismatch ->
    recomputeRequest ->
    AyMADCRecomputeObligation digestMismatch recomputeRequest :=
  fun hmismatch hrecompute =>
    ay_madc_recompute_obligation_intro hmismatch hrecompute

theorem ay_madc_digest_mismatch_no_claim
    {digestMismatch publicClaim : Prop} :
    digestMismatch ->
    (digestMismatch -> publicClaim -> False) ->
    AyMADCNoClaimDiagnostic digestMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_madc_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_madc_partial_assignment_gap_no_claim
    {partialAssignmentGap publicClaim : Prop} :
    partialAssignmentGap ->
    (partialAssignmentGap -> publicClaim -> False) ->
    AyMADCNoClaimDiagnostic partialAssignmentGap publicClaim :=
  fun hgap hblocks =>
    ay_madc_no_claim_diagnostic_intro hgap (hblocks hgap)

theorem ay_madc_stale_witness_frames_no_claim
    {staleWitnessFrames publicClaim : Prop} :
    staleWitnessFrames ->
    (staleWitnessFrames -> publicClaim -> False) ->
    AyMADCNoClaimDiagnostic staleWitnessFrames publicClaim :=
  fun hstale hblocks =>
    ay_madc_no_claim_diagnostic_intro hstale (hblocks hstale)

theorem ay_madc_checker_rejection_no_claim
    {checkerRejection publicClaim : Prop} :
    checkerRejection ->
    (checkerRejection -> publicClaim -> False) ->
    AyMADCNoClaimDiagnostic checkerRejection publicClaim :=
  fun hreject hblocks =>
    ay_madc_no_claim_diagnostic_intro hreject (hblocks hreject)

theorem ay_madc_variable_map_drift_no_claim
    {variableMapDrift publicClaim : Prop} :
    variableMapDrift ->
    (variableMapDrift -> publicClaim -> False) ->
    AyMADCNoClaimDiagnostic variableMapDrift publicClaim :=
  fun hdrift hblocks =>
    ay_madc_no_claim_diagnostic_intro hdrift (hblocks hdrift)

theorem ay_madc_fingerprint_drift_no_claim
    {fingerprintDrift publicClaim : Prop} :
    fingerprintDrift ->
    (fingerprintDrift -> publicClaim -> False) ->
    AyMADCNoClaimDiagnostic fingerprintDrift publicClaim :=
  fun hdrift hblocks =>
    ay_madc_no_claim_diagnostic_intro hdrift (hblocks hdrift)

theorem ay_madc_diagnostic_blocks_public_claim
    {diagnostic publicClaim : Prop} :
    AyMADCNoClaimDiagnostic diagnostic publicClaim ->
    publicClaim ->
    False :=
  fun h hclaim => ay_madc_no_claim_diagnostic_blocks h hclaim

theorem ay_madc_bad_crosscheck_no_stale_sat_publication
    {digestMismatch partialAssignmentGap staleWitnessFrames checkerRejection
      variableMapDrift fingerprintDrift publicClaim : Prop} :
    (digestMismatch -> publicClaim -> False) ->
    (partialAssignmentGap -> publicClaim -> False) ->
    (staleWitnessFrames -> publicClaim -> False) ->
    (checkerRejection -> publicClaim -> False) ->
    (variableMapDrift -> publicClaim -> False) ->
    (fingerprintDrift -> publicClaim -> False) ->
    AyMADCConj
      (digestMismatch ->
        AyMADCNoClaimDiagnostic digestMismatch publicClaim)
      (AyMADCConj
        (partialAssignmentGap ->
          AyMADCNoClaimDiagnostic partialAssignmentGap publicClaim)
        (AyMADCConj
          (staleWitnessFrames ->
            AyMADCNoClaimDiagnostic staleWitnessFrames publicClaim)
          (AyMADCConj
            (checkerRejection ->
              AyMADCNoClaimDiagnostic checkerRejection publicClaim)
            (AyMADCConj
              (variableMapDrift ->
                AyMADCNoClaimDiagnostic variableMapDrift publicClaim)
              (fingerprintDrift ->
                AyMADCNoClaimDiagnostic
                  fingerprintDrift publicClaim))))) :=
  fun hdigest hgap hframes hchecker hmap hfingerprint =>
    ay_madc_conj_intro
      (fun h => ay_madc_digest_mismatch_no_claim h hdigest)
      (ay_madc_conj_intro
        (fun h => ay_madc_partial_assignment_gap_no_claim h hgap)
        (ay_madc_conj_intro
          (fun h => ay_madc_stale_witness_frames_no_claim h hframes)
          (ay_madc_conj_intro
            (fun h => ay_madc_checker_rejection_no_claim h hchecker)
            (ay_madc_conj_intro
              (fun h => ay_madc_variable_map_drift_no_claim h hmap)
              (fun h =>
                ay_madc_fingerprint_drift_no_claim h hfingerprint)))))
