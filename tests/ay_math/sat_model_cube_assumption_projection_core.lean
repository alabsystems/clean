-- SAT-COMP/ay cube/assumption model projection soundness skeleton.
-- A SAT model found under assumptions or cubing is publishable for the
-- original instance only when frames, cube literals, projection maps,
-- eliminated/default reconstruction, digest, replay, and fingerprint agree.

def AyMCAPConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMCAPDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMCAPEquisat (left right : Prop) : Prop :=
  AyMCAPConj (left -> right) (right -> left)

def AyMCAPAssumptionFrames
    (baseFrame assumptionFrame frameAgreement : Prop) : Prop :=
  AyMCAPConj baseFrame (AyMCAPConj assumptionFrame frameAgreement)

def AyMCAPCubeLiterals
    (cubeMembership cubeSatisfied cubeConsistent : Prop) : Prop :=
  AyMCAPConj cubeMembership (AyMCAPConj cubeSatisfied cubeConsistent)

def AyMCAPProjectionMap
    (solverProjection originalProjection projectionComplete : Prop) : Prop :=
  AyMCAPConj solverProjection
    (AyMCAPConj originalProjection projectionComplete)

def AyMCAPEliminatedReconstruction
    (eliminatedVariables defaultValues reconstructionWitness : Prop) : Prop :=
  AyMCAPConj eliminatedVariables
    (AyMCAPConj defaultValues reconstructionWitness)

def AyMCAPAssignmentDigest
    (assignmentArtifact digestValue digestAgreement : Prop) : Prop :=
  AyMCAPConj assignmentArtifact
    (AyMCAPConj digestValue digestAgreement)

def AyMCAPCheckerReplay (checkerAccepted replayTrace : Prop) : Prop :=
  AyMCAPConj checkerAccepted replayTrace

def AyMCAPOriginalFingerprint
    (originalFingerprint artifactFingerprint fingerprintStable : Prop) :
    Prop :=
  AyMCAPConj originalFingerprint
    (AyMCAPConj artifactFingerprint fingerprintStable)

def AyMCAPProjectionSoundness
    (assumptionModel projectedModel originalModel : Prop) : Prop :=
  AyMCAPConj assumptionModel (AyMCAPConj projectedModel originalModel)

def AyMCAPProjectionEvidence
    (framesOk cubeOk projectionOk reconstructionOk digestOk replayOk
      fingerprintOk : Prop) : Prop :=
  AyMCAPConj framesOk
    (AyMCAPConj cubeOk
      (AyMCAPConj projectionOk
        (AyMCAPConj reconstructionOk
          (AyMCAPConj digestOk
            (AyMCAPConj replayOk fingerprintOk)))))

def AyMCAPPublicSatResult
    (projectionEvidence auditEntry publicSatModel : Prop) : Prop :=
  AyMCAPConj projectionEvidence (AyMCAPConj auditEntry publicSatModel)

def AyMCAPNoClaimDiagnostic (diagnostic publicClaim : Prop) : Prop :=
  AyMCAPConj diagnostic (publicClaim -> False)

def AyMCAPRecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMCAPConj reason recomputeRequest

theorem ay_mcap_conj_intro {left right : Prop} :
    left -> right -> AyMCAPConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_mcap_conj_left {left right : Prop} :
    AyMCAPConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_mcap_conj_right {left right : Prop} :
    AyMCAPConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_mcap_disj_left {left right : Prop} :
    left -> AyMCAPDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_mcap_disj_right {left right : Prop} :
    right -> AyMCAPDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_mcap_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMCAPEquisat left right :=
  fun hf hb => ay_mcap_conj_intro hf hb

theorem ay_mcap_equisat_forward {left right : Prop} :
    AyMCAPEquisat left right -> left -> right :=
  fun h => ay_mcap_conj_left h

theorem ay_mcap_equisat_backward {left right : Prop} :
    AyMCAPEquisat left right -> right -> left :=
  fun h => ay_mcap_conj_right h

theorem ay_mcap_assumption_frames_intro
    {baseFrame assumptionFrame frameAgreement : Prop} :
    baseFrame ->
    assumptionFrame ->
    frameAgreement ->
    AyMCAPAssumptionFrames baseFrame assumptionFrame frameAgreement :=
  fun hbase hassumption hagree =>
    ay_mcap_conj_intro hbase (ay_mcap_conj_intro hassumption hagree)

theorem ay_mcap_assumption_frames_base
    {baseFrame assumptionFrame frameAgreement : Prop} :
    AyMCAPAssumptionFrames baseFrame assumptionFrame frameAgreement ->
    baseFrame :=
  fun h => ay_mcap_conj_left h

theorem ay_mcap_assumption_frames_assumption
    {baseFrame assumptionFrame frameAgreement : Prop} :
    AyMCAPAssumptionFrames baseFrame assumptionFrame frameAgreement ->
    assumptionFrame :=
  fun h => ay_mcap_conj_left (ay_mcap_conj_right h)

theorem ay_mcap_assumption_frames_agreement
    {baseFrame assumptionFrame frameAgreement : Prop} :
    AyMCAPAssumptionFrames baseFrame assumptionFrame frameAgreement ->
    frameAgreement :=
  fun h => ay_mcap_conj_right (ay_mcap_conj_right h)

theorem ay_mcap_cube_literals_intro
    {cubeMembership cubeSatisfied cubeConsistent : Prop} :
    cubeMembership ->
    cubeSatisfied ->
    cubeConsistent ->
    AyMCAPCubeLiterals cubeMembership cubeSatisfied cubeConsistent :=
  fun hmember hsatisfied hconsistent =>
    ay_mcap_conj_intro hmember
      (ay_mcap_conj_intro hsatisfied hconsistent)

theorem ay_mcap_cube_literals_membership
    {cubeMembership cubeSatisfied cubeConsistent : Prop} :
    AyMCAPCubeLiterals cubeMembership cubeSatisfied cubeConsistent ->
    cubeMembership :=
  fun h => ay_mcap_conj_left h

theorem ay_mcap_cube_literals_satisfied
    {cubeMembership cubeSatisfied cubeConsistent : Prop} :
    AyMCAPCubeLiterals cubeMembership cubeSatisfied cubeConsistent ->
    cubeSatisfied :=
  fun h => ay_mcap_conj_left (ay_mcap_conj_right h)

theorem ay_mcap_cube_literals_consistent
    {cubeMembership cubeSatisfied cubeConsistent : Prop} :
    AyMCAPCubeLiterals cubeMembership cubeSatisfied cubeConsistent ->
    cubeConsistent :=
  fun h => ay_mcap_conj_right (ay_mcap_conj_right h)

theorem ay_mcap_projection_map_intro
    {solverProjection originalProjection projectionComplete : Prop} :
    solverProjection ->
    originalProjection ->
    projectionComplete ->
    AyMCAPProjectionMap
      solverProjection originalProjection projectionComplete :=
  fun hsolver horiginal hcomplete =>
    ay_mcap_conj_intro hsolver
      (ay_mcap_conj_intro horiginal hcomplete)

theorem ay_mcap_projection_map_solver
    {solverProjection originalProjection projectionComplete : Prop} :
    AyMCAPProjectionMap
      solverProjection originalProjection projectionComplete ->
    solverProjection :=
  fun h => ay_mcap_conj_left h

theorem ay_mcap_projection_map_original
    {solverProjection originalProjection projectionComplete : Prop} :
    AyMCAPProjectionMap
      solverProjection originalProjection projectionComplete ->
    originalProjection :=
  fun h => ay_mcap_conj_left (ay_mcap_conj_right h)

theorem ay_mcap_projection_map_complete
    {solverProjection originalProjection projectionComplete : Prop} :
    AyMCAPProjectionMap
      solverProjection originalProjection projectionComplete ->
    projectionComplete :=
  fun h => ay_mcap_conj_right (ay_mcap_conj_right h)

theorem ay_mcap_eliminated_reconstruction_intro
    {eliminatedVariables defaultValues reconstructionWitness : Prop} :
    eliminatedVariables ->
    defaultValues ->
    reconstructionWitness ->
    AyMCAPEliminatedReconstruction
      eliminatedVariables defaultValues reconstructionWitness :=
  fun helim hdefaults hreconstruct =>
    ay_mcap_conj_intro helim
      (ay_mcap_conj_intro hdefaults hreconstruct)

theorem ay_mcap_eliminated_reconstruction_variables
    {eliminatedVariables defaultValues reconstructionWitness : Prop} :
    AyMCAPEliminatedReconstruction
      eliminatedVariables defaultValues reconstructionWitness ->
    eliminatedVariables :=
  fun h => ay_mcap_conj_left h

theorem ay_mcap_eliminated_reconstruction_defaults
    {eliminatedVariables defaultValues reconstructionWitness : Prop} :
    AyMCAPEliminatedReconstruction
      eliminatedVariables defaultValues reconstructionWitness ->
    defaultValues :=
  fun h => ay_mcap_conj_left (ay_mcap_conj_right h)

theorem ay_mcap_eliminated_reconstruction_witness
    {eliminatedVariables defaultValues reconstructionWitness : Prop} :
    AyMCAPEliminatedReconstruction
      eliminatedVariables defaultValues reconstructionWitness ->
    reconstructionWitness :=
  fun h => ay_mcap_conj_right (ay_mcap_conj_right h)

theorem ay_mcap_assignment_digest_intro
    {assignmentArtifact digestValue digestAgreement : Prop} :
    assignmentArtifact ->
    digestValue ->
    digestAgreement ->
    AyMCAPAssignmentDigest assignmentArtifact digestValue digestAgreement :=
  fun hartifact hdigest hagree =>
    ay_mcap_conj_intro hartifact (ay_mcap_conj_intro hdigest hagree)

theorem ay_mcap_assignment_digest_artifact
    {assignmentArtifact digestValue digestAgreement : Prop} :
    AyMCAPAssignmentDigest assignmentArtifact digestValue digestAgreement ->
    assignmentArtifact :=
  fun h => ay_mcap_conj_left h

theorem ay_mcap_assignment_digest_value
    {assignmentArtifact digestValue digestAgreement : Prop} :
    AyMCAPAssignmentDigest assignmentArtifact digestValue digestAgreement ->
    digestValue :=
  fun h => ay_mcap_conj_left (ay_mcap_conj_right h)

theorem ay_mcap_assignment_digest_agreement
    {assignmentArtifact digestValue digestAgreement : Prop} :
    AyMCAPAssignmentDigest assignmentArtifact digestValue digestAgreement ->
    digestAgreement :=
  fun h => ay_mcap_conj_right (ay_mcap_conj_right h)

theorem ay_mcap_checker_replay_intro
    {checkerAccepted replayTrace : Prop} :
    checkerAccepted ->
    replayTrace ->
    AyMCAPCheckerReplay checkerAccepted replayTrace :=
  fun haccepted htrace => ay_mcap_conj_intro haccepted htrace

theorem ay_mcap_checker_replay_accepted
    {checkerAccepted replayTrace : Prop} :
    AyMCAPCheckerReplay checkerAccepted replayTrace ->
    checkerAccepted :=
  fun h => ay_mcap_conj_left h

theorem ay_mcap_checker_replay_trace
    {checkerAccepted replayTrace : Prop} :
    AyMCAPCheckerReplay checkerAccepted replayTrace ->
    replayTrace :=
  fun h => ay_mcap_conj_right h

theorem ay_mcap_original_fingerprint_intro
    {originalFingerprint artifactFingerprint fingerprintStable : Prop} :
    originalFingerprint ->
    artifactFingerprint ->
    fingerprintStable ->
    AyMCAPOriginalFingerprint
      originalFingerprint artifactFingerprint fingerprintStable :=
  fun horiginal hartifact hstable =>
    ay_mcap_conj_intro horiginal
      (ay_mcap_conj_intro hartifact hstable)

theorem ay_mcap_original_fingerprint_original
    {originalFingerprint artifactFingerprint fingerprintStable : Prop} :
    AyMCAPOriginalFingerprint
      originalFingerprint artifactFingerprint fingerprintStable ->
    originalFingerprint :=
  fun h => ay_mcap_conj_left h

theorem ay_mcap_original_fingerprint_artifact
    {originalFingerprint artifactFingerprint fingerprintStable : Prop} :
    AyMCAPOriginalFingerprint
      originalFingerprint artifactFingerprint fingerprintStable ->
    artifactFingerprint :=
  fun h => ay_mcap_conj_left (ay_mcap_conj_right h)

theorem ay_mcap_original_fingerprint_stable
    {originalFingerprint artifactFingerprint fingerprintStable : Prop} :
    AyMCAPOriginalFingerprint
      originalFingerprint artifactFingerprint fingerprintStable ->
    fingerprintStable :=
  fun h => ay_mcap_conj_right (ay_mcap_conj_right h)

theorem ay_mcap_projection_soundness_intro
    {assumptionModel projectedModel originalModel : Prop} :
    assumptionModel ->
    projectedModel ->
    originalModel ->
    AyMCAPProjectionSoundness
      assumptionModel projectedModel originalModel :=
  fun hassumption hprojected horiginal =>
    ay_mcap_conj_intro hassumption
      (ay_mcap_conj_intro hprojected horiginal)

theorem ay_mcap_projection_soundness_assumption
    {assumptionModel projectedModel originalModel : Prop} :
    AyMCAPProjectionSoundness
      assumptionModel projectedModel originalModel ->
    assumptionModel :=
  fun h => ay_mcap_conj_left h

theorem ay_mcap_projection_soundness_projected
    {assumptionModel projectedModel originalModel : Prop} :
    AyMCAPProjectionSoundness
      assumptionModel projectedModel originalModel ->
    projectedModel :=
  fun h => ay_mcap_conj_left (ay_mcap_conj_right h)

theorem ay_mcap_projection_soundness_original
    {assumptionModel projectedModel originalModel : Prop} :
    AyMCAPProjectionSoundness
      assumptionModel projectedModel originalModel ->
    originalModel :=
  fun h => ay_mcap_conj_right (ay_mcap_conj_right h)

theorem ay_mcap_projection_evidence_intro
    {framesOk cubeOk projectionOk reconstructionOk digestOk replayOk
      fingerprintOk : Prop} :
    framesOk ->
    cubeOk ->
    projectionOk ->
    reconstructionOk ->
    digestOk ->
    replayOk ->
    fingerprintOk ->
    AyMCAPProjectionEvidence
      framesOk cubeOk projectionOk reconstructionOk digestOk replayOk
      fingerprintOk :=
  fun hframes hcube hprojection hreconstruction hdigest hreplay hfingerprint =>
    ay_mcap_conj_intro hframes
      (ay_mcap_conj_intro hcube
        (ay_mcap_conj_intro hprojection
          (ay_mcap_conj_intro hreconstruction
            (ay_mcap_conj_intro hdigest
              (ay_mcap_conj_intro hreplay hfingerprint)))))

theorem ay_mcap_projection_evidence_frames
    {framesOk cubeOk projectionOk reconstructionOk digestOk replayOk
      fingerprintOk : Prop} :
    AyMCAPProjectionEvidence
      framesOk cubeOk projectionOk reconstructionOk digestOk replayOk
      fingerprintOk ->
    framesOk :=
  fun h => ay_mcap_conj_left h

theorem ay_mcap_projection_evidence_cube
    {framesOk cubeOk projectionOk reconstructionOk digestOk replayOk
      fingerprintOk : Prop} :
    AyMCAPProjectionEvidence
      framesOk cubeOk projectionOk reconstructionOk digestOk replayOk
      fingerprintOk ->
    cubeOk :=
  fun h => ay_mcap_conj_left (ay_mcap_conj_right h)

theorem ay_mcap_projection_evidence_projection
    {framesOk cubeOk projectionOk reconstructionOk digestOk replayOk
      fingerprintOk : Prop} :
    AyMCAPProjectionEvidence
      framesOk cubeOk projectionOk reconstructionOk digestOk replayOk
      fingerprintOk ->
    projectionOk :=
  fun h => ay_mcap_conj_left (ay_mcap_conj_right (ay_mcap_conj_right h))

theorem ay_mcap_projection_evidence_reconstruction
    {framesOk cubeOk projectionOk reconstructionOk digestOk replayOk
      fingerprintOk : Prop} :
    AyMCAPProjectionEvidence
      framesOk cubeOk projectionOk reconstructionOk digestOk replayOk
      fingerprintOk ->
    reconstructionOk :=
  fun h =>
    ay_mcap_conj_left
      (ay_mcap_conj_right (ay_mcap_conj_right (ay_mcap_conj_right h)))

theorem ay_mcap_projection_evidence_digest
    {framesOk cubeOk projectionOk reconstructionOk digestOk replayOk
      fingerprintOk : Prop} :
    AyMCAPProjectionEvidence
      framesOk cubeOk projectionOk reconstructionOk digestOk replayOk
      fingerprintOk ->
    digestOk :=
  fun h =>
    ay_mcap_conj_left
      (ay_mcap_conj_right
        (ay_mcap_conj_right (ay_mcap_conj_right (ay_mcap_conj_right h))))

theorem ay_mcap_projection_evidence_replay
    {framesOk cubeOk projectionOk reconstructionOk digestOk replayOk
      fingerprintOk : Prop} :
    AyMCAPProjectionEvidence
      framesOk cubeOk projectionOk reconstructionOk digestOk replayOk
      fingerprintOk ->
    replayOk :=
  fun h =>
    ay_mcap_conj_left
      (ay_mcap_conj_right
        (ay_mcap_conj_right
          (ay_mcap_conj_right (ay_mcap_conj_right (ay_mcap_conj_right h)))))

theorem ay_mcap_projection_evidence_fingerprint
    {framesOk cubeOk projectionOk reconstructionOk digestOk replayOk
      fingerprintOk : Prop} :
    AyMCAPProjectionEvidence
      framesOk cubeOk projectionOk reconstructionOk digestOk replayOk
      fingerprintOk ->
    fingerprintOk :=
  fun h =>
    ay_mcap_conj_right
      (ay_mcap_conj_right
        (ay_mcap_conj_right
          (ay_mcap_conj_right (ay_mcap_conj_right (ay_mcap_conj_right h)))))

theorem ay_mcap_public_sat_result_intro
    {projectionEvidence auditEntry publicSatModel : Prop} :
    projectionEvidence ->
    auditEntry ->
    publicSatModel ->
    AyMCAPPublicSatResult projectionEvidence auditEntry publicSatModel :=
  fun hevidence haudit hmodel =>
    ay_mcap_conj_intro hevidence (ay_mcap_conj_intro haudit hmodel)

theorem ay_mcap_public_sat_result_evidence
    {projectionEvidence auditEntry publicSatModel : Prop} :
    AyMCAPPublicSatResult projectionEvidence auditEntry publicSatModel ->
    projectionEvidence :=
  fun h => ay_mcap_conj_left h

theorem ay_mcap_public_sat_result_audit
    {projectionEvidence auditEntry publicSatModel : Prop} :
    AyMCAPPublicSatResult projectionEvidence auditEntry publicSatModel ->
    auditEntry :=
  fun h => ay_mcap_conj_left (ay_mcap_conj_right h)

theorem ay_mcap_public_sat_result_model
    {projectionEvidence auditEntry publicSatModel : Prop} :
    AyMCAPPublicSatResult projectionEvidence auditEntry publicSatModel ->
    publicSatModel :=
  fun h => ay_mcap_conj_right (ay_mcap_conj_right h)

theorem ay_mcap_accepted_projection_validates_public_sat
    {projectionEvidence auditEntry publicSatModel : Prop} :
    AyMCAPPublicSatResult projectionEvidence auditEntry publicSatModel ->
    publicSatModel :=
  fun h => ay_mcap_public_sat_result_model h

theorem ay_mcap_projection_soundness_validates_original
    {assumptionModel projectedModel originalModel : Prop} :
    AyMCAPProjectionSoundness
      assumptionModel projectedModel originalModel ->
    originalModel :=
  fun h => ay_mcap_projection_soundness_original h

theorem ay_mcap_publication_requires_frames
    {framesOk cubeOk projectionOk reconstructionOk digestOk replayOk
      fingerprintOk auditEntry publicSatModel : Prop} :
    AyMCAPPublicSatResult
      (AyMCAPProjectionEvidence
        framesOk cubeOk projectionOk reconstructionOk digestOk replayOk
        fingerprintOk)
      auditEntry
      publicSatModel ->
    framesOk :=
  fun h =>
    ay_mcap_projection_evidence_frames
      (ay_mcap_public_sat_result_evidence h)

theorem ay_mcap_publication_requires_cube
    {framesOk cubeOk projectionOk reconstructionOk digestOk replayOk
      fingerprintOk auditEntry publicSatModel : Prop} :
    AyMCAPPublicSatResult
      (AyMCAPProjectionEvidence
        framesOk cubeOk projectionOk reconstructionOk digestOk replayOk
        fingerprintOk)
      auditEntry
      publicSatModel ->
    cubeOk :=
  fun h =>
    ay_mcap_projection_evidence_cube
      (ay_mcap_public_sat_result_evidence h)

theorem ay_mcap_publication_requires_projection
    {framesOk cubeOk projectionOk reconstructionOk digestOk replayOk
      fingerprintOk auditEntry publicSatModel : Prop} :
    AyMCAPPublicSatResult
      (AyMCAPProjectionEvidence
        framesOk cubeOk projectionOk reconstructionOk digestOk replayOk
        fingerprintOk)
      auditEntry
      publicSatModel ->
    projectionOk :=
  fun h =>
    ay_mcap_projection_evidence_projection
      (ay_mcap_public_sat_result_evidence h)

theorem ay_mcap_publication_requires_reconstruction
    {framesOk cubeOk projectionOk reconstructionOk digestOk replayOk
      fingerprintOk auditEntry publicSatModel : Prop} :
    AyMCAPPublicSatResult
      (AyMCAPProjectionEvidence
        framesOk cubeOk projectionOk reconstructionOk digestOk replayOk
        fingerprintOk)
      auditEntry
      publicSatModel ->
    reconstructionOk :=
  fun h =>
    ay_mcap_projection_evidence_reconstruction
      (ay_mcap_public_sat_result_evidence h)

theorem ay_mcap_publication_requires_digest
    {framesOk cubeOk projectionOk reconstructionOk digestOk replayOk
      fingerprintOk auditEntry publicSatModel : Prop} :
    AyMCAPPublicSatResult
      (AyMCAPProjectionEvidence
        framesOk cubeOk projectionOk reconstructionOk digestOk replayOk
        fingerprintOk)
      auditEntry
      publicSatModel ->
    digestOk :=
  fun h =>
    ay_mcap_projection_evidence_digest
      (ay_mcap_public_sat_result_evidence h)

theorem ay_mcap_publication_requires_replay
    {framesOk cubeOk projectionOk reconstructionOk digestOk replayOk
      fingerprintOk auditEntry publicSatModel : Prop} :
    AyMCAPPublicSatResult
      (AyMCAPProjectionEvidence
        framesOk cubeOk projectionOk reconstructionOk digestOk replayOk
        fingerprintOk)
      auditEntry
      publicSatModel ->
    replayOk :=
  fun h =>
    ay_mcap_projection_evidence_replay
      (ay_mcap_public_sat_result_evidence h)

theorem ay_mcap_publication_requires_fingerprint
    {framesOk cubeOk projectionOk reconstructionOk digestOk replayOk
      fingerprintOk auditEntry publicSatModel : Prop} :
    AyMCAPPublicSatResult
      (AyMCAPProjectionEvidence
        framesOk cubeOk projectionOk reconstructionOk digestOk replayOk
        fingerprintOk)
      auditEntry
      publicSatModel ->
    fingerprintOk :=
  fun h =>
    ay_mcap_projection_evidence_fingerprint
      (ay_mcap_public_sat_result_evidence h)

theorem ay_mcap_public_sat_result_sound_exact
    {projectionEvidence auditEntry publicSatModel : Prop} :
    AyMCAPEquisat
      (AyMCAPPublicSatResult projectionEvidence auditEntry publicSatModel)
      (AyMCAPConj projectionEvidence
        (AyMCAPConj auditEntry publicSatModel)) :=
  ay_mcap_equisat_intro
    (fun h => h)
    (fun h => h)

theorem ay_mcap_no_claim_diagnostic_intro
    {diagnostic publicClaim : Prop} :
    diagnostic ->
    (publicClaim -> False) ->
    AyMCAPNoClaimDiagnostic diagnostic publicClaim :=
  fun hdiagnostic hblocks => ay_mcap_conj_intro hdiagnostic hblocks

theorem ay_mcap_no_claim_diagnostic_reason
    {diagnostic publicClaim : Prop} :
    AyMCAPNoClaimDiagnostic diagnostic publicClaim ->
    diagnostic :=
  fun h => ay_mcap_conj_left h

theorem ay_mcap_no_claim_diagnostic_blocks
    {diagnostic publicClaim : Prop} :
    AyMCAPNoClaimDiagnostic diagnostic publicClaim ->
    publicClaim ->
    False :=
  fun h => ay_mcap_conj_right h

theorem ay_mcap_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMCAPRecomputeObligation reason recomputeRequest :=
  fun hreason hrequest => ay_mcap_conj_intro hreason hrequest

theorem ay_mcap_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMCAPRecomputeObligation reason recomputeRequest ->
    reason :=
  fun h => ay_mcap_conj_left h

theorem ay_mcap_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMCAPRecomputeObligation reason recomputeRequest ->
    recomputeRequest :=
  fun h => ay_mcap_conj_right h

theorem ay_mcap_conflicting_cube_assumptions_recompute
    {conflictingCubeAssumptions recomputeRequest : Prop} :
    conflictingCubeAssumptions ->
    recomputeRequest ->
    AyMCAPRecomputeObligation conflictingCubeAssumptions recomputeRequest :=
  fun hconflict hrecompute =>
    ay_mcap_recompute_obligation_intro hconflict hrecompute

theorem ay_mcap_conflicting_cube_assumptions_no_claim
    {conflictingCubeAssumptions publicClaim : Prop} :
    conflictingCubeAssumptions ->
    (conflictingCubeAssumptions -> publicClaim -> False) ->
    AyMCAPNoClaimDiagnostic conflictingCubeAssumptions publicClaim :=
  fun hconflict hblocks =>
    ay_mcap_no_claim_diagnostic_intro hconflict (hblocks hconflict)

theorem ay_mcap_missing_projection_no_claim
    {missingProjection publicClaim : Prop} :
    missingProjection ->
    (missingProjection -> publicClaim -> False) ->
    AyMCAPNoClaimDiagnostic missingProjection publicClaim :=
  fun hmissing hblocks =>
    ay_mcap_no_claim_diagnostic_intro hmissing (hblocks hmissing)

theorem ay_mcap_stale_frames_no_claim
    {staleFrames publicClaim : Prop} :
    staleFrames ->
    (staleFrames -> publicClaim -> False) ->
    AyMCAPNoClaimDiagnostic staleFrames publicClaim :=
  fun hstale hblocks =>
    ay_mcap_no_claim_diagnostic_intro hstale (hblocks hstale)

theorem ay_mcap_digest_mismatch_no_claim
    {digestMismatch publicClaim : Prop} :
    digestMismatch ->
    (digestMismatch -> publicClaim -> False) ->
    AyMCAPNoClaimDiagnostic digestMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_mcap_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mcap_checker_rejection_no_claim
    {checkerRejection publicClaim : Prop} :
    checkerRejection ->
    (checkerRejection -> publicClaim -> False) ->
    AyMCAPNoClaimDiagnostic checkerRejection publicClaim :=
  fun hreject hblocks =>
    ay_mcap_no_claim_diagnostic_intro hreject (hblocks hreject)

theorem ay_mcap_fingerprint_drift_no_claim
    {fingerprintDrift publicClaim : Prop} :
    fingerprintDrift ->
    (fingerprintDrift -> publicClaim -> False) ->
    AyMCAPNoClaimDiagnostic fingerprintDrift publicClaim :=
  fun hdrift hblocks =>
    ay_mcap_no_claim_diagnostic_intro hdrift (hblocks hdrift)

theorem ay_mcap_diagnostic_blocks_public_claim
    {diagnostic publicClaim : Prop} :
    AyMCAPNoClaimDiagnostic diagnostic publicClaim ->
    publicClaim ->
    False :=
  fun h hclaim => ay_mcap_no_claim_diagnostic_blocks h hclaim

theorem ay_mcap_bad_projection_no_stale_sat_publication
    {conflictingCubeAssumptions missingProjection staleFrames digestMismatch
      checkerRejection fingerprintDrift publicClaim : Prop} :
    (conflictingCubeAssumptions -> publicClaim -> False) ->
    (missingProjection -> publicClaim -> False) ->
    (staleFrames -> publicClaim -> False) ->
    (digestMismatch -> publicClaim -> False) ->
    (checkerRejection -> publicClaim -> False) ->
    (fingerprintDrift -> publicClaim -> False) ->
    AyMCAPConj
      (conflictingCubeAssumptions ->
        AyMCAPNoClaimDiagnostic conflictingCubeAssumptions publicClaim)
      (AyMCAPConj
        (missingProjection ->
          AyMCAPNoClaimDiagnostic missingProjection publicClaim)
        (AyMCAPConj
          (staleFrames ->
            AyMCAPNoClaimDiagnostic staleFrames publicClaim)
          (AyMCAPConj
            (digestMismatch ->
              AyMCAPNoClaimDiagnostic digestMismatch publicClaim)
            (AyMCAPConj
              (checkerRejection ->
                AyMCAPNoClaimDiagnostic checkerRejection publicClaim)
              (fingerprintDrift ->
                AyMCAPNoClaimDiagnostic
                  fingerprintDrift publicClaim))))) :=
  fun hconflict hprojection hframes hdigest hchecker hfingerprint =>
    ay_mcap_conj_intro
      (fun h => ay_mcap_conflicting_cube_assumptions_no_claim h hconflict)
      (ay_mcap_conj_intro
        (fun h => ay_mcap_missing_projection_no_claim h hprojection)
        (ay_mcap_conj_intro
          (fun h => ay_mcap_stale_frames_no_claim h hframes)
          (ay_mcap_conj_intro
            (fun h => ay_mcap_digest_mismatch_no_claim h hdigest)
            (ay_mcap_conj_intro
              (fun h => ay_mcap_checker_rejection_no_claim h hchecker)
              (fun h =>
                ay_mcap_fingerprint_drift_no_claim h hfingerprint)))))
