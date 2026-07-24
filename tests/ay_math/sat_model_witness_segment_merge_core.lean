-- SAT-COMP/ay witness segment merge soundness skeleton.
-- Segmented SAT witness artifacts merge into a public model only when segment
-- digests, intervals, overlap/disjointness, reconstruction, checker replay,
-- solver build, and original fingerprint evidence agree.

def AyMWSMConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMWSMDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMWSMEquisat (left right : Prop) : Prop :=
  AyMWSMConj (left -> right) (right -> left)

def AyMWSMSegmentDigests
    (segmentManifest segmentDigests digestAgreement : Prop) : Prop :=
  AyMWSMConj segmentManifest
    (AyMWSMConj segmentDigests digestAgreement)

def AyMWSMVariableIntervals
    (declaredIntervals coveredIntervals intervalAgreement : Prop) : Prop :=
  AyMWSMConj declaredIntervals
    (AyMWSMConj coveredIntervals intervalAgreement)

def AyMWSMOverlapEvidence
    (overlapChecked disjointSegments noOverlapConflict : Prop) : Prop :=
  AyMWSMConj overlapChecked
    (AyMWSMConj disjointSegments noOverlapConflict)

def AyMWSMProjectionDefaults
    (projectionMap defaultReconstruction reconstructionAgreement : Prop) :
    Prop :=
  AyMWSMConj projectionMap
    (AyMWSMConj defaultReconstruction reconstructionAgreement)

def AyMWSMAssignmentDigest
    (mergedAssignment mergedDigest digestAgreement : Prop) : Prop :=
  AyMWSMConj mergedAssignment
    (AyMWSMConj mergedDigest digestAgreement)

def AyMWSMCheckerReplay (checkerAccepted replayTrace : Prop) : Prop :=
  AyMWSMConj checkerAccepted replayTrace

def AyMWSMSolverBuild
    (solverBuild segmentBuild buildAgreement : Prop) : Prop :=
  AyMWSMConj solverBuild (AyMWSMConj segmentBuild buildAgreement)

def AyMWSMOriginalFingerprint
    (originalFingerprint mergedFingerprint fingerprintAgreement : Prop) :
    Prop :=
  AyMWSMConj originalFingerprint
    (AyMWSMConj mergedFingerprint fingerprintAgreement)

def AyMWSMMergeEvidence
    (segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
      buildOk fingerprintOk : Prop) : Prop :=
  AyMWSMConj segmentsOk
    (AyMWSMConj intervalsOk
      (AyMWSMConj overlapOk
        (AyMWSMConj reconstructionOk
          (AyMWSMConj digestOk
            (AyMWSMConj replayOk
              (AyMWSMConj buildOk fingerprintOk))))))

def AyMWSMPublicSatResult
    (mergeEvidence mergedWitness publicSatClaim : Prop) : Prop :=
  AyMWSMConj mergeEvidence (AyMWSMConj mergedWitness publicSatClaim)

def AyMWSMNoClaimDiagnostic (diagnostic publicSatClaim : Prop) : Prop :=
  AyMWSMConj diagnostic (publicSatClaim -> False)

def AyMWSMRecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMWSMConj reason recomputeRequest

theorem ay_mwsm_conj_intro {left right : Prop} :
    left -> right -> AyMWSMConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_mwsm_conj_left {left right : Prop} :
    AyMWSMConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_mwsm_conj_right {left right : Prop} :
    AyMWSMConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_mwsm_disj_left {left right : Prop} :
    left -> AyMWSMDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_mwsm_disj_right {left right : Prop} :
    right -> AyMWSMDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_mwsm_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMWSMEquisat left right :=
  fun hf hb => ay_mwsm_conj_intro hf hb

theorem ay_mwsm_equisat_forward {left right : Prop} :
    AyMWSMEquisat left right -> left -> right :=
  fun h => ay_mwsm_conj_left h

theorem ay_mwsm_equisat_backward {left right : Prop} :
    AyMWSMEquisat left right -> right -> left :=
  fun h => ay_mwsm_conj_right h

theorem ay_mwsm_segment_digests_intro
    {segmentManifest segmentDigests digestAgreement : Prop} :
    segmentManifest ->
    segmentDigests ->
    digestAgreement ->
    AyMWSMSegmentDigests
      segmentManifest segmentDigests digestAgreement :=
  fun hmanifest hdigests hagree =>
    ay_mwsm_conj_intro hmanifest
      (ay_mwsm_conj_intro hdigests hagree)

theorem ay_mwsm_segment_digests_manifest
    {segmentManifest segmentDigests digestAgreement : Prop} :
    AyMWSMSegmentDigests
      segmentManifest segmentDigests digestAgreement ->
    segmentManifest :=
  fun h => ay_mwsm_conj_left h

theorem ay_mwsm_segment_digests_digests
    {segmentManifest segmentDigests digestAgreement : Prop} :
    AyMWSMSegmentDigests
      segmentManifest segmentDigests digestAgreement ->
    segmentDigests :=
  fun h => ay_mwsm_conj_left (ay_mwsm_conj_right h)

theorem ay_mwsm_segment_digests_agreement
    {segmentManifest segmentDigests digestAgreement : Prop} :
    AyMWSMSegmentDigests
      segmentManifest segmentDigests digestAgreement ->
    digestAgreement :=
  fun h => ay_mwsm_conj_right (ay_mwsm_conj_right h)

theorem ay_mwsm_variable_intervals_intro
    {declaredIntervals coveredIntervals intervalAgreement : Prop} :
    declaredIntervals ->
    coveredIntervals ->
    intervalAgreement ->
    AyMWSMVariableIntervals
      declaredIntervals coveredIntervals intervalAgreement :=
  fun hdeclared hcovered hagree =>
    ay_mwsm_conj_intro hdeclared
      (ay_mwsm_conj_intro hcovered hagree)

theorem ay_mwsm_variable_intervals_declared
    {declaredIntervals coveredIntervals intervalAgreement : Prop} :
    AyMWSMVariableIntervals
      declaredIntervals coveredIntervals intervalAgreement ->
    declaredIntervals :=
  fun h => ay_mwsm_conj_left h

theorem ay_mwsm_variable_intervals_covered
    {declaredIntervals coveredIntervals intervalAgreement : Prop} :
    AyMWSMVariableIntervals
      declaredIntervals coveredIntervals intervalAgreement ->
    coveredIntervals :=
  fun h => ay_mwsm_conj_left (ay_mwsm_conj_right h)

theorem ay_mwsm_variable_intervals_agreement
    {declaredIntervals coveredIntervals intervalAgreement : Prop} :
    AyMWSMVariableIntervals
      declaredIntervals coveredIntervals intervalAgreement ->
    intervalAgreement :=
  fun h => ay_mwsm_conj_right (ay_mwsm_conj_right h)

theorem ay_mwsm_overlap_evidence_intro
    {overlapChecked disjointSegments noOverlapConflict : Prop} :
    overlapChecked ->
    disjointSegments ->
    noOverlapConflict ->
    AyMWSMOverlapEvidence
      overlapChecked disjointSegments noOverlapConflict :=
  fun hchecked hdisjoint hconflict =>
    ay_mwsm_conj_intro hchecked
      (ay_mwsm_conj_intro hdisjoint hconflict)

theorem ay_mwsm_overlap_evidence_checked
    {overlapChecked disjointSegments noOverlapConflict : Prop} :
    AyMWSMOverlapEvidence
      overlapChecked disjointSegments noOverlapConflict ->
    overlapChecked :=
  fun h => ay_mwsm_conj_left h

theorem ay_mwsm_overlap_evidence_disjoint
    {overlapChecked disjointSegments noOverlapConflict : Prop} :
    AyMWSMOverlapEvidence
      overlapChecked disjointSegments noOverlapConflict ->
    disjointSegments :=
  fun h => ay_mwsm_conj_left (ay_mwsm_conj_right h)

theorem ay_mwsm_overlap_evidence_no_conflict
    {overlapChecked disjointSegments noOverlapConflict : Prop} :
    AyMWSMOverlapEvidence
      overlapChecked disjointSegments noOverlapConflict ->
    noOverlapConflict :=
  fun h => ay_mwsm_conj_right (ay_mwsm_conj_right h)

theorem ay_mwsm_projection_defaults_intro
    {projectionMap defaultReconstruction reconstructionAgreement : Prop} :
    projectionMap ->
    defaultReconstruction ->
    reconstructionAgreement ->
    AyMWSMProjectionDefaults
      projectionMap defaultReconstruction reconstructionAgreement :=
  fun hprojection hdefaults hagree =>
    ay_mwsm_conj_intro hprojection
      (ay_mwsm_conj_intro hdefaults hagree)

theorem ay_mwsm_projection_defaults_map
    {projectionMap defaultReconstruction reconstructionAgreement : Prop} :
    AyMWSMProjectionDefaults
      projectionMap defaultReconstruction reconstructionAgreement ->
    projectionMap :=
  fun h => ay_mwsm_conj_left h

theorem ay_mwsm_projection_defaults_defaults
    {projectionMap defaultReconstruction reconstructionAgreement : Prop} :
    AyMWSMProjectionDefaults
      projectionMap defaultReconstruction reconstructionAgreement ->
    defaultReconstruction :=
  fun h => ay_mwsm_conj_left (ay_mwsm_conj_right h)

theorem ay_mwsm_projection_defaults_agreement
    {projectionMap defaultReconstruction reconstructionAgreement : Prop} :
    AyMWSMProjectionDefaults
      projectionMap defaultReconstruction reconstructionAgreement ->
    reconstructionAgreement :=
  fun h => ay_mwsm_conj_right (ay_mwsm_conj_right h)

theorem ay_mwsm_assignment_digest_intro
    {mergedAssignment mergedDigest digestAgreement : Prop} :
    mergedAssignment ->
    mergedDigest ->
    digestAgreement ->
    AyMWSMAssignmentDigest
      mergedAssignment mergedDigest digestAgreement :=
  fun hassignment hdigest hagree =>
    ay_mwsm_conj_intro hassignment
      (ay_mwsm_conj_intro hdigest hagree)

theorem ay_mwsm_assignment_digest_assignment
    {mergedAssignment mergedDigest digestAgreement : Prop} :
    AyMWSMAssignmentDigest
      mergedAssignment mergedDigest digestAgreement ->
    mergedAssignment :=
  fun h => ay_mwsm_conj_left h

theorem ay_mwsm_assignment_digest_digest
    {mergedAssignment mergedDigest digestAgreement : Prop} :
    AyMWSMAssignmentDigest
      mergedAssignment mergedDigest digestAgreement ->
    mergedDigest :=
  fun h => ay_mwsm_conj_left (ay_mwsm_conj_right h)

theorem ay_mwsm_assignment_digest_agreement
    {mergedAssignment mergedDigest digestAgreement : Prop} :
    AyMWSMAssignmentDigest
      mergedAssignment mergedDigest digestAgreement ->
    digestAgreement :=
  fun h => ay_mwsm_conj_right (ay_mwsm_conj_right h)

theorem ay_mwsm_checker_replay_intro
    {checkerAccepted replayTrace : Prop} :
    checkerAccepted ->
    replayTrace ->
    AyMWSMCheckerReplay checkerAccepted replayTrace :=
  fun haccepted htrace => ay_mwsm_conj_intro haccepted htrace

theorem ay_mwsm_checker_replay_accepted
    {checkerAccepted replayTrace : Prop} :
    AyMWSMCheckerReplay checkerAccepted replayTrace -> checkerAccepted :=
  fun h => ay_mwsm_conj_left h

theorem ay_mwsm_checker_replay_trace
    {checkerAccepted replayTrace : Prop} :
    AyMWSMCheckerReplay checkerAccepted replayTrace -> replayTrace :=
  fun h => ay_mwsm_conj_right h

theorem ay_mwsm_solver_build_intro
    {solverBuild segmentBuild buildAgreement : Prop} :
    solverBuild ->
    segmentBuild ->
    buildAgreement ->
    AyMWSMSolverBuild solverBuild segmentBuild buildAgreement :=
  fun hsolver hsegment hagree =>
    ay_mwsm_conj_intro hsolver
      (ay_mwsm_conj_intro hsegment hagree)

theorem ay_mwsm_solver_build_solver
    {solverBuild segmentBuild buildAgreement : Prop} :
    AyMWSMSolverBuild solverBuild segmentBuild buildAgreement -> solverBuild :=
  fun h => ay_mwsm_conj_left h

theorem ay_mwsm_solver_build_segment
    {solverBuild segmentBuild buildAgreement : Prop} :
    AyMWSMSolverBuild solverBuild segmentBuild buildAgreement ->
    segmentBuild :=
  fun h => ay_mwsm_conj_left (ay_mwsm_conj_right h)

theorem ay_mwsm_solver_build_agreement
    {solverBuild segmentBuild buildAgreement : Prop} :
    AyMWSMSolverBuild solverBuild segmentBuild buildAgreement ->
    buildAgreement :=
  fun h => ay_mwsm_conj_right (ay_mwsm_conj_right h)

theorem ay_mwsm_original_fingerprint_intro
    {originalFingerprint mergedFingerprint fingerprintAgreement : Prop} :
    originalFingerprint ->
    mergedFingerprint ->
    fingerprintAgreement ->
    AyMWSMOriginalFingerprint
      originalFingerprint mergedFingerprint fingerprintAgreement :=
  fun horiginal hmerged hagree =>
    ay_mwsm_conj_intro horiginal
      (ay_mwsm_conj_intro hmerged hagree)

theorem ay_mwsm_original_fingerprint_original
    {originalFingerprint mergedFingerprint fingerprintAgreement : Prop} :
    AyMWSMOriginalFingerprint
      originalFingerprint mergedFingerprint fingerprintAgreement ->
    originalFingerprint :=
  fun h => ay_mwsm_conj_left h

theorem ay_mwsm_original_fingerprint_merged
    {originalFingerprint mergedFingerprint fingerprintAgreement : Prop} :
    AyMWSMOriginalFingerprint
      originalFingerprint mergedFingerprint fingerprintAgreement ->
    mergedFingerprint :=
  fun h => ay_mwsm_conj_left (ay_mwsm_conj_right h)

theorem ay_mwsm_original_fingerprint_agreement
    {originalFingerprint mergedFingerprint fingerprintAgreement : Prop} :
    AyMWSMOriginalFingerprint
      originalFingerprint mergedFingerprint fingerprintAgreement ->
    fingerprintAgreement :=
  fun h => ay_mwsm_conj_right (ay_mwsm_conj_right h)

theorem ay_mwsm_merge_evidence_intro
    {segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
      buildOk fingerprintOk : Prop} :
    segmentsOk ->
    intervalsOk ->
    overlapOk ->
    reconstructionOk ->
    digestOk ->
    replayOk ->
    buildOk ->
    fingerprintOk ->
    AyMWSMMergeEvidence
      segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
      buildOk fingerprintOk :=
  fun hsegments hintervals hoverlap hreconstruction hdigest hreplay hbuild
      hfingerprint =>
    ay_mwsm_conj_intro hsegments
      (ay_mwsm_conj_intro hintervals
        (ay_mwsm_conj_intro hoverlap
          (ay_mwsm_conj_intro hreconstruction
            (ay_mwsm_conj_intro hdigest
              (ay_mwsm_conj_intro hreplay
                (ay_mwsm_conj_intro hbuild hfingerprint))))))

theorem ay_mwsm_merge_evidence_segments
    {segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
      buildOk fingerprintOk : Prop} :
    AyMWSMMergeEvidence
      segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
      buildOk fingerprintOk ->
    segmentsOk :=
  fun h => ay_mwsm_conj_left h

theorem ay_mwsm_merge_evidence_intervals
    {segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
      buildOk fingerprintOk : Prop} :
    AyMWSMMergeEvidence
      segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
      buildOk fingerprintOk ->
    intervalsOk :=
  fun h => ay_mwsm_conj_left (ay_mwsm_conj_right h)

theorem ay_mwsm_merge_evidence_overlap
    {segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
      buildOk fingerprintOk : Prop} :
    AyMWSMMergeEvidence
      segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
      buildOk fingerprintOk ->
    overlapOk :=
  fun h => ay_mwsm_conj_left
    (ay_mwsm_conj_right (ay_mwsm_conj_right h))

theorem ay_mwsm_merge_evidence_reconstruction
    {segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
      buildOk fingerprintOk : Prop} :
    AyMWSMMergeEvidence
      segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
      buildOk fingerprintOk ->
    reconstructionOk :=
  fun h => ay_mwsm_conj_left
    (ay_mwsm_conj_right
      (ay_mwsm_conj_right (ay_mwsm_conj_right h)))

theorem ay_mwsm_merge_evidence_digest
    {segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
      buildOk fingerprintOk : Prop} :
    AyMWSMMergeEvidence
      segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
      buildOk fingerprintOk ->
    digestOk :=
  fun h => ay_mwsm_conj_left
    (ay_mwsm_conj_right
      (ay_mwsm_conj_right
        (ay_mwsm_conj_right (ay_mwsm_conj_right h))))

theorem ay_mwsm_merge_evidence_replay
    {segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
      buildOk fingerprintOk : Prop} :
    AyMWSMMergeEvidence
      segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
      buildOk fingerprintOk ->
    replayOk :=
  fun h => ay_mwsm_conj_left
    (ay_mwsm_conj_right
      (ay_mwsm_conj_right
        (ay_mwsm_conj_right
          (ay_mwsm_conj_right (ay_mwsm_conj_right h)))))

theorem ay_mwsm_merge_evidence_build
    {segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
      buildOk fingerprintOk : Prop} :
    AyMWSMMergeEvidence
      segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
      buildOk fingerprintOk ->
    buildOk :=
  fun h => ay_mwsm_conj_left
    (ay_mwsm_conj_right
      (ay_mwsm_conj_right
        (ay_mwsm_conj_right
          (ay_mwsm_conj_right
            (ay_mwsm_conj_right (ay_mwsm_conj_right h))))))

theorem ay_mwsm_merge_evidence_fingerprint
    {segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
      buildOk fingerprintOk : Prop} :
    AyMWSMMergeEvidence
      segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
      buildOk fingerprintOk ->
    fingerprintOk :=
  fun h => ay_mwsm_conj_right
    (ay_mwsm_conj_right
      (ay_mwsm_conj_right
        (ay_mwsm_conj_right
          (ay_mwsm_conj_right
            (ay_mwsm_conj_right (ay_mwsm_conj_right h))))))

theorem ay_mwsm_public_sat_result_intro
    {mergeEvidence mergedWitness publicSatClaim : Prop} :
    mergeEvidence ->
    mergedWitness ->
    publicSatClaim ->
    AyMWSMPublicSatResult mergeEvidence mergedWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_mwsm_conj_intro hevidence
      (ay_mwsm_conj_intro hwitness hclaim)

theorem ay_mwsm_public_sat_result_evidence
    {mergeEvidence mergedWitness publicSatClaim : Prop} :
    AyMWSMPublicSatResult mergeEvidence mergedWitness publicSatClaim ->
    mergeEvidence :=
  fun h => ay_mwsm_conj_left h

theorem ay_mwsm_public_sat_result_witness
    {mergeEvidence mergedWitness publicSatClaim : Prop} :
    AyMWSMPublicSatResult mergeEvidence mergedWitness publicSatClaim ->
    mergedWitness :=
  fun h => ay_mwsm_conj_left (ay_mwsm_conj_right h)

theorem ay_mwsm_public_sat_result_claim
    {mergeEvidence mergedWitness publicSatClaim : Prop} :
    AyMWSMPublicSatResult mergeEvidence mergedWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_mwsm_conj_right (ay_mwsm_conj_right h)

theorem ay_mwsm_accepted_segment_merge_validates_same_public_sat
    {segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
      buildOk fingerprintOk segmentedPublicSat mergedWitness
      publicSatClaim : Prop} :
    AyMWSMMergeEvidence
      segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
      buildOk fingerprintOk ->
    segmentedPublicSat ->
    mergedWitness ->
    (segmentedPublicSat -> publicSatClaim) ->
    AyMWSMPublicSatResult
      (AyMWSMMergeEvidence
        segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
        buildOk fingerprintOk)
      mergedWitness
      publicSatClaim :=
  fun hevidence hsegmented hwitness lift =>
    ay_mwsm_public_sat_result_intro hevidence hwitness (lift hsegmented)

theorem ay_mwsm_segment_merge_preserves_public_claim
    {segmentedWitness mergedWitness publicSatClaim : Prop} :
    AyMWSMEquisat segmentedWitness mergedWitness ->
    segmentedWitness ->
    (mergedWitness -> publicSatClaim) ->
    publicSatClaim :=
  fun heq hsegmented publish =>
    publish (ay_mwsm_equisat_forward heq hsegmented)

theorem ay_mwsm_publication_requires_segments
    {segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
      buildOk fingerprintOk mergedWitness publicSatClaim : Prop} :
    AyMWSMPublicSatResult
      (AyMWSMMergeEvidence
        segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
        buildOk fingerprintOk)
      mergedWitness
      publicSatClaim ->
    segmentsOk :=
  fun h =>
    ay_mwsm_merge_evidence_segments
      (ay_mwsm_public_sat_result_evidence h)

theorem ay_mwsm_publication_requires_intervals
    {segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
      buildOk fingerprintOk mergedWitness publicSatClaim : Prop} :
    AyMWSMPublicSatResult
      (AyMWSMMergeEvidence
        segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
        buildOk fingerprintOk)
      mergedWitness
      publicSatClaim ->
    intervalsOk :=
  fun h =>
    ay_mwsm_merge_evidence_intervals
      (ay_mwsm_public_sat_result_evidence h)

theorem ay_mwsm_publication_requires_overlap
    {segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
      buildOk fingerprintOk mergedWitness publicSatClaim : Prop} :
    AyMWSMPublicSatResult
      (AyMWSMMergeEvidence
        segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
        buildOk fingerprintOk)
      mergedWitness
      publicSatClaim ->
    overlapOk :=
  fun h =>
    ay_mwsm_merge_evidence_overlap
      (ay_mwsm_public_sat_result_evidence h)

theorem ay_mwsm_publication_requires_reconstruction
    {segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
      buildOk fingerprintOk mergedWitness publicSatClaim : Prop} :
    AyMWSMPublicSatResult
      (AyMWSMMergeEvidence
        segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
        buildOk fingerprintOk)
      mergedWitness
      publicSatClaim ->
    reconstructionOk :=
  fun h =>
    ay_mwsm_merge_evidence_reconstruction
      (ay_mwsm_public_sat_result_evidence h)

theorem ay_mwsm_publication_requires_digest
    {segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
      buildOk fingerprintOk mergedWitness publicSatClaim : Prop} :
    AyMWSMPublicSatResult
      (AyMWSMMergeEvidence
        segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
        buildOk fingerprintOk)
      mergedWitness
      publicSatClaim ->
    digestOk :=
  fun h =>
    ay_mwsm_merge_evidence_digest
      (ay_mwsm_public_sat_result_evidence h)

theorem ay_mwsm_publication_requires_replay
    {segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
      buildOk fingerprintOk mergedWitness publicSatClaim : Prop} :
    AyMWSMPublicSatResult
      (AyMWSMMergeEvidence
        segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
        buildOk fingerprintOk)
      mergedWitness
      publicSatClaim ->
    replayOk :=
  fun h =>
    ay_mwsm_merge_evidence_replay
      (ay_mwsm_public_sat_result_evidence h)

theorem ay_mwsm_publication_requires_build
    {segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
      buildOk fingerprintOk mergedWitness publicSatClaim : Prop} :
    AyMWSMPublicSatResult
      (AyMWSMMergeEvidence
        segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
        buildOk fingerprintOk)
      mergedWitness
      publicSatClaim ->
    buildOk :=
  fun h =>
    ay_mwsm_merge_evidence_build
      (ay_mwsm_public_sat_result_evidence h)

theorem ay_mwsm_publication_requires_fingerprint
    {segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
      buildOk fingerprintOk mergedWitness publicSatClaim : Prop} :
    AyMWSMPublicSatResult
      (AyMWSMMergeEvidence
        segmentsOk intervalsOk overlapOk reconstructionOk digestOk replayOk
        buildOk fingerprintOk)
      mergedWitness
      publicSatClaim ->
    fingerprintOk :=
  fun h =>
    ay_mwsm_merge_evidence_fingerprint
      (ay_mwsm_public_sat_result_evidence h)

theorem ay_mwsm_no_claim_diagnostic_intro
    {diagnostic publicSatClaim : Prop} :
    diagnostic ->
    (publicSatClaim -> False) ->
    AyMWSMNoClaimDiagnostic diagnostic publicSatClaim :=
  fun hdiagnostic hblocks =>
    ay_mwsm_conj_intro hdiagnostic hblocks

theorem ay_mwsm_no_claim_diagnostic_reason
    {diagnostic publicSatClaim : Prop} :
    AyMWSMNoClaimDiagnostic diagnostic publicSatClaim -> diagnostic :=
  fun h => ay_mwsm_conj_left h

theorem ay_mwsm_no_claim_diagnostic_blocks
    {diagnostic publicSatClaim : Prop} :
    AyMWSMNoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h => ay_mwsm_conj_right h

theorem ay_mwsm_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMWSMRecomputeObligation reason recomputeRequest :=
  fun hreason hrecompute => ay_mwsm_conj_intro hreason hrecompute

theorem ay_mwsm_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMWSMRecomputeObligation reason recomputeRequest -> reason :=
  fun h => ay_mwsm_conj_left h

theorem ay_mwsm_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMWSMRecomputeObligation reason recomputeRequest -> recomputeRequest :=
  fun h => ay_mwsm_conj_right h

theorem ay_mwsm_missing_segment_recompute
    {missingSegment recomputeRequest : Prop} :
    missingSegment ->
    recomputeRequest ->
    AyMWSMRecomputeObligation missingSegment recomputeRequest :=
  fun hmissing hrecompute =>
    ay_mwsm_recompute_obligation_intro hmissing hrecompute

theorem ay_mwsm_missing_segment_no_claim
    {missingSegment publicSatClaim : Prop} :
    missingSegment ->
    (publicSatClaim -> False) ->
    AyMWSMNoClaimDiagnostic missingSegment publicSatClaim :=
  fun hmissing hblocks =>
    ay_mwsm_no_claim_diagnostic_intro hmissing hblocks

theorem ay_mwsm_overlapping_conflict_no_claim
    {overlappingConflict publicSatClaim : Prop} :
    overlappingConflict ->
    (publicSatClaim -> False) ->
    AyMWSMNoClaimDiagnostic overlappingConflict publicSatClaim :=
  fun hconflict hblocks =>
    ay_mwsm_no_claim_diagnostic_intro hconflict hblocks

theorem ay_mwsm_interval_gap_recompute
    {intervalGap recomputeRequest : Prop} :
    intervalGap ->
    recomputeRequest ->
    AyMWSMRecomputeObligation intervalGap recomputeRequest :=
  fun hgap hrecompute =>
    ay_mwsm_recompute_obligation_intro hgap hrecompute

theorem ay_mwsm_interval_gap_no_claim
    {intervalGap publicSatClaim : Prop} :
    intervalGap ->
    (publicSatClaim -> False) ->
    AyMWSMNoClaimDiagnostic intervalGap publicSatClaim :=
  fun hgap hblocks => ay_mwsm_no_claim_diagnostic_intro hgap hblocks

theorem ay_mwsm_map_drift_no_claim
    {mapDrift publicSatClaim : Prop} :
    mapDrift ->
    (publicSatClaim -> False) ->
    AyMWSMNoClaimDiagnostic mapDrift publicSatClaim :=
  fun hdrift hblocks => ay_mwsm_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mwsm_order_drift_no_claim
    {orderDrift publicSatClaim : Prop} :
    orderDrift ->
    (publicSatClaim -> False) ->
    AyMWSMNoClaimDiagnostic orderDrift publicSatClaim :=
  fun hdrift hblocks => ay_mwsm_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mwsm_digest_mismatch_no_claim
    {digestMismatch publicSatClaim : Prop} :
    digestMismatch ->
    (publicSatClaim -> False) ->
    AyMWSMNoClaimDiagnostic digestMismatch publicSatClaim :=
  fun hmismatch hblocks =>
    ay_mwsm_no_claim_diagnostic_intro hmismatch hblocks

theorem ay_mwsm_checker_rejection_no_claim
    {checkerRejection publicSatClaim : Prop} :
    checkerRejection ->
    (publicSatClaim -> False) ->
    AyMWSMNoClaimDiagnostic checkerRejection publicSatClaim :=
  fun hreject hblocks =>
    ay_mwsm_no_claim_diagnostic_intro hreject hblocks

theorem ay_mwsm_build_drift_no_claim
    {buildDrift publicSatClaim : Prop} :
    buildDrift ->
    (publicSatClaim -> False) ->
    AyMWSMNoClaimDiagnostic buildDrift publicSatClaim :=
  fun hdrift hblocks => ay_mwsm_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mwsm_fingerprint_drift_no_claim
    {fingerprintDrift publicSatClaim : Prop} :
    fingerprintDrift ->
    (publicSatClaim -> False) ->
    AyMWSMNoClaimDiagnostic fingerprintDrift publicSatClaim :=
  fun hdrift hblocks => ay_mwsm_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mwsm_diagnostic_blocks_public_claim
    {diagnostic publicSatClaim : Prop} :
    AyMWSMNoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_mwsm_no_claim_diagnostic_blocks h hclaim

theorem ay_mwsm_bad_segment_merge_cannot_publish_sat
    {badSegmentMerge publicSatClaim : Prop} :
    AyMWSMNoClaimDiagnostic badSegmentMerge publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_mwsm_diagnostic_blocks_public_claim h hclaim
