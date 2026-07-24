-- SAT-COMP/ay incremental assumption-release publication skeleton.
-- A model found after releasing assumptions or cubes is publishable for the
-- original instance only when release lineage, active frame, projection,
-- reconstruction, digest, checker replay, build, and fingerprint evidence agree.

def AyMIARConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMIARDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMIAREquisat (left right : Prop) : Prop :=
  AyMIARConj (left -> right) (right -> left)

def AyMIARReleaseLineage
    (parentFrame releasedFrame lineageAgreement : Prop) : Prop :=
  AyMIARConj parentFrame (AyMIARConj releasedFrame lineageAgreement)

def AyMIARActiveAssumptionFrame
    (activeFrame cubeFrame noActiveConflict : Prop) : Prop :=
  AyMIARConj activeFrame (AyMIARConj cubeFrame noActiveConflict)

def AyMIARProjectionMap
    (solverProjection originalProjection projectionAgreement : Prop) : Prop :=
  AyMIARConj solverProjection
    (AyMIARConj originalProjection projectionAgreement)

def AyMIAREliminatedDefaults
    (eliminatedVariables defaultValues defaultAgreement : Prop) : Prop :=
  AyMIARConj eliminatedVariables
    (AyMIARConj defaultValues defaultAgreement)

def AyMIARAssignmentDigest
    (releasedAssignment digestValue digestAgreement : Prop) : Prop :=
  AyMIARConj releasedAssignment
    (AyMIARConj digestValue digestAgreement)

def AyMIARCheckerReplay (checkerAccepted replayTrace : Prop) : Prop :=
  AyMIARConj checkerAccepted replayTrace

def AyMIARSolverBuild
    (solverBuild witnessBuild buildAgreement : Prop) : Prop :=
  AyMIARConj solverBuild (AyMIARConj witnessBuild buildAgreement)

def AyMIAROriginalFingerprint
    (originalFingerprint releasedFingerprint fingerprintAgreement : Prop) :
    Prop :=
  AyMIARConj originalFingerprint
    (AyMIARConj releasedFingerprint fingerprintAgreement)

def AyMIARReleaseEvidence
    (lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
      fingerprintOk : Prop) : Prop :=
  AyMIARConj lineageOk
    (AyMIARConj frameOk
      (AyMIARConj projectionOk
        (AyMIARConj defaultsOk
          (AyMIARConj digestOk
            (AyMIARConj replayOk
              (AyMIARConj buildOk fingerprintOk))))))

def AyMIARPublicSatResult
    (releaseEvidence releasedWitness publicSatClaim : Prop) : Prop :=
  AyMIARConj releaseEvidence
    (AyMIARConj releasedWitness publicSatClaim)

def AyMIARNoClaimDiagnostic (diagnostic publicSatClaim : Prop) : Prop :=
  AyMIARConj diagnostic (publicSatClaim -> False)

def AyMIARRecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMIARConj reason recomputeRequest

theorem ay_miar_conj_intro {left right : Prop} :
    left -> right -> AyMIARConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_miar_conj_left {left right : Prop} :
    AyMIARConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_miar_conj_right {left right : Prop} :
    AyMIARConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_miar_disj_left {left right : Prop} :
    left -> AyMIARDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_miar_disj_right {left right : Prop} :
    right -> AyMIARDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_miar_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMIAREquisat left right :=
  fun hf hb => ay_miar_conj_intro hf hb

theorem ay_miar_equisat_forward {left right : Prop} :
    AyMIAREquisat left right -> left -> right :=
  fun h => ay_miar_conj_left h

theorem ay_miar_equisat_backward {left right : Prop} :
    AyMIAREquisat left right -> right -> left :=
  fun h => ay_miar_conj_right h

theorem ay_miar_release_lineage_intro
    {parentFrame releasedFrame lineageAgreement : Prop} :
    parentFrame ->
    releasedFrame ->
    lineageAgreement ->
    AyMIARReleaseLineage parentFrame releasedFrame lineageAgreement :=
  fun hparent hreleased hagree =>
    ay_miar_conj_intro hparent
      (ay_miar_conj_intro hreleased hagree)

theorem ay_miar_release_lineage_parent
    {parentFrame releasedFrame lineageAgreement : Prop} :
    AyMIARReleaseLineage parentFrame releasedFrame lineageAgreement ->
    parentFrame :=
  fun h => ay_miar_conj_left h

theorem ay_miar_release_lineage_released
    {parentFrame releasedFrame lineageAgreement : Prop} :
    AyMIARReleaseLineage parentFrame releasedFrame lineageAgreement ->
    releasedFrame :=
  fun h => ay_miar_conj_left (ay_miar_conj_right h)

theorem ay_miar_release_lineage_agreement
    {parentFrame releasedFrame lineageAgreement : Prop} :
    AyMIARReleaseLineage parentFrame releasedFrame lineageAgreement ->
    lineageAgreement :=
  fun h => ay_miar_conj_right (ay_miar_conj_right h)

theorem ay_miar_active_assumption_frame_intro
    {activeFrame cubeFrame noActiveConflict : Prop} :
    activeFrame ->
    cubeFrame ->
    noActiveConflict ->
    AyMIARActiveAssumptionFrame activeFrame cubeFrame noActiveConflict :=
  fun hactive hcube hconflict =>
    ay_miar_conj_intro hactive
      (ay_miar_conj_intro hcube hconflict)

theorem ay_miar_active_assumption_frame_active
    {activeFrame cubeFrame noActiveConflict : Prop} :
    AyMIARActiveAssumptionFrame activeFrame cubeFrame noActiveConflict ->
    activeFrame :=
  fun h => ay_miar_conj_left h

theorem ay_miar_active_assumption_frame_cube
    {activeFrame cubeFrame noActiveConflict : Prop} :
    AyMIARActiveAssumptionFrame activeFrame cubeFrame noActiveConflict ->
    cubeFrame :=
  fun h => ay_miar_conj_left (ay_miar_conj_right h)

theorem ay_miar_active_assumption_frame_no_conflict
    {activeFrame cubeFrame noActiveConflict : Prop} :
    AyMIARActiveAssumptionFrame activeFrame cubeFrame noActiveConflict ->
    noActiveConflict :=
  fun h => ay_miar_conj_right (ay_miar_conj_right h)

theorem ay_miar_projection_map_intro
    {solverProjection originalProjection projectionAgreement : Prop} :
    solverProjection ->
    originalProjection ->
    projectionAgreement ->
    AyMIARProjectionMap
      solverProjection originalProjection projectionAgreement :=
  fun hsolver horiginal hagree =>
    ay_miar_conj_intro hsolver
      (ay_miar_conj_intro horiginal hagree)

theorem ay_miar_projection_map_solver
    {solverProjection originalProjection projectionAgreement : Prop} :
    AyMIARProjectionMap
      solverProjection originalProjection projectionAgreement ->
    solverProjection :=
  fun h => ay_miar_conj_left h

theorem ay_miar_projection_map_original
    {solverProjection originalProjection projectionAgreement : Prop} :
    AyMIARProjectionMap
      solverProjection originalProjection projectionAgreement ->
    originalProjection :=
  fun h => ay_miar_conj_left (ay_miar_conj_right h)

theorem ay_miar_projection_map_agreement
    {solverProjection originalProjection projectionAgreement : Prop} :
    AyMIARProjectionMap
      solverProjection originalProjection projectionAgreement ->
    projectionAgreement :=
  fun h => ay_miar_conj_right (ay_miar_conj_right h)

theorem ay_miar_eliminated_defaults_intro
    {eliminatedVariables defaultValues defaultAgreement : Prop} :
    eliminatedVariables ->
    defaultValues ->
    defaultAgreement ->
    AyMIAREliminatedDefaults
      eliminatedVariables defaultValues defaultAgreement :=
  fun helim hdefaults hagree =>
    ay_miar_conj_intro helim
      (ay_miar_conj_intro hdefaults hagree)

theorem ay_miar_eliminated_defaults_variables
    {eliminatedVariables defaultValues defaultAgreement : Prop} :
    AyMIAREliminatedDefaults
      eliminatedVariables defaultValues defaultAgreement ->
    eliminatedVariables :=
  fun h => ay_miar_conj_left h

theorem ay_miar_eliminated_defaults_values
    {eliminatedVariables defaultValues defaultAgreement : Prop} :
    AyMIAREliminatedDefaults
      eliminatedVariables defaultValues defaultAgreement ->
    defaultValues :=
  fun h => ay_miar_conj_left (ay_miar_conj_right h)

theorem ay_miar_eliminated_defaults_agreement
    {eliminatedVariables defaultValues defaultAgreement : Prop} :
    AyMIAREliminatedDefaults
      eliminatedVariables defaultValues defaultAgreement ->
    defaultAgreement :=
  fun h => ay_miar_conj_right (ay_miar_conj_right h)

theorem ay_miar_assignment_digest_intro
    {releasedAssignment digestValue digestAgreement : Prop} :
    releasedAssignment ->
    digestValue ->
    digestAgreement ->
    AyMIARAssignmentDigest
      releasedAssignment digestValue digestAgreement :=
  fun hassignment hdigest hagree =>
    ay_miar_conj_intro hassignment
      (ay_miar_conj_intro hdigest hagree)

theorem ay_miar_assignment_digest_assignment
    {releasedAssignment digestValue digestAgreement : Prop} :
    AyMIARAssignmentDigest
      releasedAssignment digestValue digestAgreement ->
    releasedAssignment :=
  fun h => ay_miar_conj_left h

theorem ay_miar_assignment_digest_value
    {releasedAssignment digestValue digestAgreement : Prop} :
    AyMIARAssignmentDigest
      releasedAssignment digestValue digestAgreement ->
    digestValue :=
  fun h => ay_miar_conj_left (ay_miar_conj_right h)

theorem ay_miar_assignment_digest_agreement
    {releasedAssignment digestValue digestAgreement : Prop} :
    AyMIARAssignmentDigest
      releasedAssignment digestValue digestAgreement ->
    digestAgreement :=
  fun h => ay_miar_conj_right (ay_miar_conj_right h)

theorem ay_miar_checker_replay_intro
    {checkerAccepted replayTrace : Prop} :
    checkerAccepted ->
    replayTrace ->
    AyMIARCheckerReplay checkerAccepted replayTrace :=
  fun haccepted htrace => ay_miar_conj_intro haccepted htrace

theorem ay_miar_checker_replay_accepted
    {checkerAccepted replayTrace : Prop} :
    AyMIARCheckerReplay checkerAccepted replayTrace -> checkerAccepted :=
  fun h => ay_miar_conj_left h

theorem ay_miar_checker_replay_trace
    {checkerAccepted replayTrace : Prop} :
    AyMIARCheckerReplay checkerAccepted replayTrace -> replayTrace :=
  fun h => ay_miar_conj_right h

theorem ay_miar_solver_build_intro
    {solverBuild witnessBuild buildAgreement : Prop} :
    solverBuild ->
    witnessBuild ->
    buildAgreement ->
    AyMIARSolverBuild solverBuild witnessBuild buildAgreement :=
  fun hsolver hwitness hagree =>
    ay_miar_conj_intro hsolver
      (ay_miar_conj_intro hwitness hagree)

theorem ay_miar_solver_build_solver
    {solverBuild witnessBuild buildAgreement : Prop} :
    AyMIARSolverBuild solverBuild witnessBuild buildAgreement ->
    solverBuild :=
  fun h => ay_miar_conj_left h

theorem ay_miar_solver_build_witness
    {solverBuild witnessBuild buildAgreement : Prop} :
    AyMIARSolverBuild solverBuild witnessBuild buildAgreement ->
    witnessBuild :=
  fun h => ay_miar_conj_left (ay_miar_conj_right h)

theorem ay_miar_solver_build_agreement
    {solverBuild witnessBuild buildAgreement : Prop} :
    AyMIARSolverBuild solverBuild witnessBuild buildAgreement ->
    buildAgreement :=
  fun h => ay_miar_conj_right (ay_miar_conj_right h)

theorem ay_miar_original_fingerprint_intro
    {originalFingerprint releasedFingerprint fingerprintAgreement : Prop} :
    originalFingerprint ->
    releasedFingerprint ->
    fingerprintAgreement ->
    AyMIAROriginalFingerprint
      originalFingerprint releasedFingerprint fingerprintAgreement :=
  fun horiginal hreleased hagree =>
    ay_miar_conj_intro horiginal
      (ay_miar_conj_intro hreleased hagree)

theorem ay_miar_original_fingerprint_original
    {originalFingerprint releasedFingerprint fingerprintAgreement : Prop} :
    AyMIAROriginalFingerprint
      originalFingerprint releasedFingerprint fingerprintAgreement ->
    originalFingerprint :=
  fun h => ay_miar_conj_left h

theorem ay_miar_original_fingerprint_released
    {originalFingerprint releasedFingerprint fingerprintAgreement : Prop} :
    AyMIAROriginalFingerprint
      originalFingerprint releasedFingerprint fingerprintAgreement ->
    releasedFingerprint :=
  fun h => ay_miar_conj_left (ay_miar_conj_right h)

theorem ay_miar_original_fingerprint_agreement
    {originalFingerprint releasedFingerprint fingerprintAgreement : Prop} :
    AyMIAROriginalFingerprint
      originalFingerprint releasedFingerprint fingerprintAgreement ->
    fingerprintAgreement :=
  fun h => ay_miar_conj_right (ay_miar_conj_right h)

theorem ay_miar_release_evidence_intro
    {lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    lineageOk ->
    frameOk ->
    projectionOk ->
    defaultsOk ->
    digestOk ->
    replayOk ->
    buildOk ->
    fingerprintOk ->
    AyMIARReleaseEvidence
      lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
      fingerprintOk :=
  fun hlineage hframe hprojection hdefaults hdigest hreplay hbuild
      hfingerprint =>
    ay_miar_conj_intro hlineage
      (ay_miar_conj_intro hframe
        (ay_miar_conj_intro hprojection
          (ay_miar_conj_intro hdefaults
            (ay_miar_conj_intro hdigest
              (ay_miar_conj_intro hreplay
                (ay_miar_conj_intro hbuild hfingerprint))))))

theorem ay_miar_release_evidence_lineage
    {lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMIARReleaseEvidence
      lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
      fingerprintOk ->
    lineageOk :=
  fun h => ay_miar_conj_left h

theorem ay_miar_release_evidence_frame
    {lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMIARReleaseEvidence
      lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
      fingerprintOk ->
    frameOk :=
  fun h => ay_miar_conj_left (ay_miar_conj_right h)

theorem ay_miar_release_evidence_projection
    {lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMIARReleaseEvidence
      lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
      fingerprintOk ->
    projectionOk :=
  fun h => ay_miar_conj_left
    (ay_miar_conj_right (ay_miar_conj_right h))

theorem ay_miar_release_evidence_defaults
    {lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMIARReleaseEvidence
      lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
      fingerprintOk ->
    defaultsOk :=
  fun h => ay_miar_conj_left
    (ay_miar_conj_right
      (ay_miar_conj_right (ay_miar_conj_right h)))

theorem ay_miar_release_evidence_digest
    {lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMIARReleaseEvidence
      lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
      fingerprintOk ->
    digestOk :=
  fun h => ay_miar_conj_left
    (ay_miar_conj_right
      (ay_miar_conj_right
        (ay_miar_conj_right (ay_miar_conj_right h))))

theorem ay_miar_release_evidence_replay
    {lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMIARReleaseEvidence
      lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
      fingerprintOk ->
    replayOk :=
  fun h => ay_miar_conj_left
    (ay_miar_conj_right
      (ay_miar_conj_right
        (ay_miar_conj_right
          (ay_miar_conj_right (ay_miar_conj_right h)))))

theorem ay_miar_release_evidence_build
    {lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMIARReleaseEvidence
      lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
      fingerprintOk ->
    buildOk :=
  fun h => ay_miar_conj_left
    (ay_miar_conj_right
      (ay_miar_conj_right
        (ay_miar_conj_right
          (ay_miar_conj_right
            (ay_miar_conj_right (ay_miar_conj_right h))))))

theorem ay_miar_release_evidence_fingerprint
    {lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMIARReleaseEvidence
      lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
      fingerprintOk ->
    fingerprintOk :=
  fun h => ay_miar_conj_right
    (ay_miar_conj_right
      (ay_miar_conj_right
        (ay_miar_conj_right
          (ay_miar_conj_right
            (ay_miar_conj_right (ay_miar_conj_right h))))))

theorem ay_miar_public_sat_result_intro
    {releaseEvidence releasedWitness publicSatClaim : Prop} :
    releaseEvidence ->
    releasedWitness ->
    publicSatClaim ->
    AyMIARPublicSatResult releaseEvidence releasedWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_miar_conj_intro hevidence
      (ay_miar_conj_intro hwitness hclaim)

theorem ay_miar_public_sat_result_evidence
    {releaseEvidence releasedWitness publicSatClaim : Prop} :
    AyMIARPublicSatResult releaseEvidence releasedWitness publicSatClaim ->
    releaseEvidence :=
  fun h => ay_miar_conj_left h

theorem ay_miar_public_sat_result_witness
    {releaseEvidence releasedWitness publicSatClaim : Prop} :
    AyMIARPublicSatResult releaseEvidence releasedWitness publicSatClaim ->
    releasedWitness :=
  fun h => ay_miar_conj_left (ay_miar_conj_right h)

theorem ay_miar_public_sat_result_claim
    {releaseEvidence releasedWitness publicSatClaim : Prop} :
    AyMIARPublicSatResult releaseEvidence releasedWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_miar_conj_right (ay_miar_conj_right h)

theorem ay_miar_accepted_release_validates_same_public_sat
    {lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
      fingerprintOk preReleaseSat releasedWitness publicSatClaim : Prop} :
    AyMIARReleaseEvidence
      lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
      fingerprintOk ->
    preReleaseSat ->
    releasedWitness ->
    (preReleaseSat -> publicSatClaim) ->
    AyMIARPublicSatResult
      (AyMIARReleaseEvidence
        lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
        fingerprintOk)
      releasedWitness
      publicSatClaim :=
  fun hevidence hpre hwitness lift =>
    ay_miar_public_sat_result_intro hevidence hwitness (lift hpre)

theorem ay_miar_release_equisat_preserves_public_claim
    {preReleaseModel releasedModel publicSatClaim : Prop} :
    AyMIAREquisat preReleaseModel releasedModel ->
    preReleaseModel ->
    (releasedModel -> publicSatClaim) ->
    publicSatClaim :=
  fun heq hpre publish => publish (ay_miar_equisat_forward heq hpre)

theorem ay_miar_publication_requires_lineage
    {lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
      fingerprintOk releasedWitness publicSatClaim : Prop} :
    AyMIARPublicSatResult
      (AyMIARReleaseEvidence
        lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
        fingerprintOk)
      releasedWitness
      publicSatClaim ->
    lineageOk :=
  fun h =>
    ay_miar_release_evidence_lineage
      (ay_miar_public_sat_result_evidence h)

theorem ay_miar_publication_requires_frame
    {lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
      fingerprintOk releasedWitness publicSatClaim : Prop} :
    AyMIARPublicSatResult
      (AyMIARReleaseEvidence
        lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
        fingerprintOk)
      releasedWitness
      publicSatClaim ->
    frameOk :=
  fun h =>
    ay_miar_release_evidence_frame
      (ay_miar_public_sat_result_evidence h)

theorem ay_miar_publication_requires_projection
    {lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
      fingerprintOk releasedWitness publicSatClaim : Prop} :
    AyMIARPublicSatResult
      (AyMIARReleaseEvidence
        lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
        fingerprintOk)
      releasedWitness
      publicSatClaim ->
    projectionOk :=
  fun h =>
    ay_miar_release_evidence_projection
      (ay_miar_public_sat_result_evidence h)

theorem ay_miar_publication_requires_defaults
    {lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
      fingerprintOk releasedWitness publicSatClaim : Prop} :
    AyMIARPublicSatResult
      (AyMIARReleaseEvidence
        lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
        fingerprintOk)
      releasedWitness
      publicSatClaim ->
    defaultsOk :=
  fun h =>
    ay_miar_release_evidence_defaults
      (ay_miar_public_sat_result_evidence h)

theorem ay_miar_publication_requires_digest
    {lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
      fingerprintOk releasedWitness publicSatClaim : Prop} :
    AyMIARPublicSatResult
      (AyMIARReleaseEvidence
        lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
        fingerprintOk)
      releasedWitness
      publicSatClaim ->
    digestOk :=
  fun h =>
    ay_miar_release_evidence_digest
      (ay_miar_public_sat_result_evidence h)

theorem ay_miar_publication_requires_replay
    {lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
      fingerprintOk releasedWitness publicSatClaim : Prop} :
    AyMIARPublicSatResult
      (AyMIARReleaseEvidence
        lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
        fingerprintOk)
      releasedWitness
      publicSatClaim ->
    replayOk :=
  fun h =>
    ay_miar_release_evidence_replay
      (ay_miar_public_sat_result_evidence h)

theorem ay_miar_publication_requires_build
    {lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
      fingerprintOk releasedWitness publicSatClaim : Prop} :
    AyMIARPublicSatResult
      (AyMIARReleaseEvidence
        lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
        fingerprintOk)
      releasedWitness
      publicSatClaim ->
    buildOk :=
  fun h =>
    ay_miar_release_evidence_build
      (ay_miar_public_sat_result_evidence h)

theorem ay_miar_publication_requires_fingerprint
    {lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
      fingerprintOk releasedWitness publicSatClaim : Prop} :
    AyMIARPublicSatResult
      (AyMIARReleaseEvidence
        lineageOk frameOk projectionOk defaultsOk digestOk replayOk buildOk
        fingerprintOk)
      releasedWitness
      publicSatClaim ->
    fingerprintOk :=
  fun h =>
    ay_miar_release_evidence_fingerprint
      (ay_miar_public_sat_result_evidence h)

theorem ay_miar_no_claim_diagnostic_intro
    {diagnostic publicSatClaim : Prop} :
    diagnostic ->
    (publicSatClaim -> False) ->
    AyMIARNoClaimDiagnostic diagnostic publicSatClaim :=
  fun hdiagnostic hblocks =>
    ay_miar_conj_intro hdiagnostic hblocks

theorem ay_miar_no_claim_diagnostic_reason
    {diagnostic publicSatClaim : Prop} :
    AyMIARNoClaimDiagnostic diagnostic publicSatClaim -> diagnostic :=
  fun h => ay_miar_conj_left h

theorem ay_miar_no_claim_diagnostic_blocks
    {diagnostic publicSatClaim : Prop} :
    AyMIARNoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h => ay_miar_conj_right h

theorem ay_miar_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMIARRecomputeObligation reason recomputeRequest :=
  fun hreason hrecompute => ay_miar_conj_intro hreason hrecompute

theorem ay_miar_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMIARRecomputeObligation reason recomputeRequest -> reason :=
  fun h => ay_miar_conj_left h

theorem ay_miar_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMIARRecomputeObligation reason recomputeRequest -> recomputeRequest :=
  fun h => ay_miar_conj_right h

theorem ay_miar_stale_release_lineage_no_claim
    {staleLineage publicSatClaim : Prop} :
    staleLineage ->
    (publicSatClaim -> False) ->
    AyMIARNoClaimDiagnostic staleLineage publicSatClaim :=
  fun hstale hblocks => ay_miar_no_claim_diagnostic_intro hstale hblocks

theorem ay_miar_active_assumption_conflict_no_claim
    {activeAssumptionConflict publicSatClaim : Prop} :
    activeAssumptionConflict ->
    (publicSatClaim -> False) ->
    AyMIARNoClaimDiagnostic activeAssumptionConflict publicSatClaim :=
  fun hconflict hblocks =>
    ay_miar_no_claim_diagnostic_intro hconflict hblocks

theorem ay_miar_missing_projection_recompute
    {missingProjection recomputeRequest : Prop} :
    missingProjection ->
    recomputeRequest ->
    AyMIARRecomputeObligation missingProjection recomputeRequest :=
  fun hmissing hrecompute =>
    ay_miar_recompute_obligation_intro hmissing hrecompute

theorem ay_miar_missing_projection_no_claim
    {missingProjection publicSatClaim : Prop} :
    missingProjection ->
    (publicSatClaim -> False) ->
    AyMIARNoClaimDiagnostic missingProjection publicSatClaim :=
  fun hmissing hblocks =>
    ay_miar_no_claim_diagnostic_intro hmissing hblocks

theorem ay_miar_default_conflict_no_claim
    {defaultConflict publicSatClaim : Prop} :
    defaultConflict ->
    (publicSatClaim -> False) ->
    AyMIARNoClaimDiagnostic defaultConflict publicSatClaim :=
  fun hconflict hblocks =>
    ay_miar_no_claim_diagnostic_intro hconflict hblocks

theorem ay_miar_digest_mismatch_no_claim
    {digestMismatch publicSatClaim : Prop} :
    digestMismatch ->
    (publicSatClaim -> False) ->
    AyMIARNoClaimDiagnostic digestMismatch publicSatClaim :=
  fun hmismatch hblocks =>
    ay_miar_no_claim_diagnostic_intro hmismatch hblocks

theorem ay_miar_checker_rejection_no_claim
    {checkerRejection publicSatClaim : Prop} :
    checkerRejection ->
    (publicSatClaim -> False) ->
    AyMIARNoClaimDiagnostic checkerRejection publicSatClaim :=
  fun hreject hblocks =>
    ay_miar_no_claim_diagnostic_intro hreject hblocks

theorem ay_miar_build_drift_no_claim
    {buildDrift publicSatClaim : Prop} :
    buildDrift ->
    (publicSatClaim -> False) ->
    AyMIARNoClaimDiagnostic buildDrift publicSatClaim :=
  fun hdrift hblocks => ay_miar_no_claim_diagnostic_intro hdrift hblocks

theorem ay_miar_fingerprint_drift_no_claim
    {fingerprintDrift publicSatClaim : Prop} :
    fingerprintDrift ->
    (publicSatClaim -> False) ->
    AyMIARNoClaimDiagnostic fingerprintDrift publicSatClaim :=
  fun hdrift hblocks => ay_miar_no_claim_diagnostic_intro hdrift hblocks

theorem ay_miar_diagnostic_blocks_public_claim
    {diagnostic publicSatClaim : Prop} :
    AyMIARNoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_miar_no_claim_diagnostic_blocks h hclaim

theorem ay_miar_bad_release_cannot_publish_sat
    {badRelease publicSatClaim : Prop} :
    AyMIARNoClaimDiagnostic badRelease publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_miar_diagnostic_blocks_public_claim h hclaim
