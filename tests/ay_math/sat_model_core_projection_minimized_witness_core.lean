-- SAT-COMP/ay core projection minimized witness soundness skeleton.
-- Projecting full models to original-formula variables and minimizing witness
-- output is admissible only under maps, projection/reconstruction, digest,
-- replay, transcript, fingerprint, and build evidence.

def AyMCPWConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMCPWDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMCPWEquisat (left right : Prop) : Prop :=
  AyMCPWConj (left -> right) (right -> left)

def AyMCPWCoreProjection
    (fullModel projectedModel minimizedWitness projectionAgreement : Prop) :
    Prop :=
  AyMCPWConj fullModel
    (AyMCPWConj projectedModel
      (AyMCPWConj minimizedWitness projectionAgreement))

def AyMCPWDimacsVariableMaps
    (solverMap dimacsMap mapAgreement : Prop) : Prop :=
  AyMCPWConj solverMap (AyMCPWConj dimacsMap mapAgreement)

def AyMCPWReconstructionEvidence
    (projectionEvidence reconstructionEvidence reconstructionAgreement : Prop) :
    Prop :=
  AyMCPWConj projectionEvidence
    (AyMCPWConj reconstructionEvidence reconstructionAgreement)

def AyMCPWAssignmentDigest
    (fullDigest projectedDigest digestAgreement : Prop) : Prop :=
  AyMCPWConj fullDigest (AyMCPWConj projectedDigest digestAgreement)

def AyMCPWClauseEvaluationReplay
    (clauseReplay projectedEvaluation evaluationAgreement : Prop) : Prop :=
  AyMCPWConj clauseReplay
    (AyMCPWConj projectedEvaluation evaluationAgreement)

def AyMCPWCheckerTranscript
    (checkerAccepted transcript replayAgreement : Prop) : Prop :=
  AyMCPWConj checkerAccepted (AyMCPWConj transcript replayAgreement)

def AyMCPWFormulaFingerprint
    (originalFingerprint projectedFingerprint fingerprintAgreement : Prop) :
    Prop :=
  AyMCPWConj originalFingerprint
    (AyMCPWConj projectedFingerprint fingerprintAgreement)

def AyMCPWBuildEvidence
    (solverBuild witnessBuild buildAgreement : Prop) : Prop :=
  AyMCPWConj solverBuild (AyMCPWConj witnessBuild buildAgreement)

def AyMCPWAcceptedEvidence
    (projectionOk mapsOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk buildOk : Prop) : Prop :=
  AyMCPWConj projectionOk
    (AyMCPWConj mapsOk
      (AyMCPWConj reconstructionOk
        (AyMCPWConj digestOk
          (AyMCPWConj clauseReplayOk
            (AyMCPWConj transcriptOk
              (AyMCPWConj fingerprintOk buildOk))))))

def AyMCPWPublicSatWitness
    (acceptedEvidence publicWitness publicSatClaim : Prop) : Prop :=
  AyMCPWConj acceptedEvidence
    (AyMCPWConj publicWitness publicSatClaim)

def AyMCPWNoClaimDiagnostic (diagnostic publicSatClaim : Prop) : Prop :=
  AyMCPWConj diagnostic (publicSatClaim -> False)

def AyMCPWRecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMCPWConj reason recomputeRequest

theorem ay_mcpw_conj_intro {left right : Prop} :
    left -> right -> AyMCPWConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_mcpw_conj_left {left right : Prop} :
    AyMCPWConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_mcpw_conj_right {left right : Prop} :
    AyMCPWConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_mcpw_disj_left {left right : Prop} :
    left -> AyMCPWDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_mcpw_disj_right {left right : Prop} :
    right -> AyMCPWDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_mcpw_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMCPWEquisat left right :=
  fun hf hb => ay_mcpw_conj_intro hf hb

theorem ay_mcpw_equisat_forward {left right : Prop} :
    AyMCPWEquisat left right -> left -> right :=
  fun h => ay_mcpw_conj_left h

theorem ay_mcpw_equisat_backward {left right : Prop} :
    AyMCPWEquisat left right -> right -> left :=
  fun h => ay_mcpw_conj_right h

theorem ay_mcpw_core_projection_intro
    {fullModel projectedModel minimizedWitness projectionAgreement : Prop} :
    fullModel ->
    projectedModel ->
    minimizedWitness ->
    projectionAgreement ->
    AyMCPWCoreProjection
      fullModel projectedModel minimizedWitness projectionAgreement :=
  fun hfull hprojected hminimized hagree =>
    ay_mcpw_conj_intro hfull
      (ay_mcpw_conj_intro hprojected
        (ay_mcpw_conj_intro hminimized hagree))

theorem ay_mcpw_core_projection_full
    {fullModel projectedModel minimizedWitness projectionAgreement : Prop} :
    AyMCPWCoreProjection
      fullModel projectedModel minimizedWitness projectionAgreement ->
    fullModel :=
  fun h => ay_mcpw_conj_left h

theorem ay_mcpw_core_projection_projected
    {fullModel projectedModel minimizedWitness projectionAgreement : Prop} :
    AyMCPWCoreProjection
      fullModel projectedModel minimizedWitness projectionAgreement ->
    projectedModel :=
  fun h => ay_mcpw_conj_left (ay_mcpw_conj_right h)

theorem ay_mcpw_core_projection_minimized
    {fullModel projectedModel minimizedWitness projectionAgreement : Prop} :
    AyMCPWCoreProjection
      fullModel projectedModel minimizedWitness projectionAgreement ->
    minimizedWitness :=
  fun h => ay_mcpw_conj_left
    (ay_mcpw_conj_right (ay_mcpw_conj_right h))

theorem ay_mcpw_core_projection_agreement
    {fullModel projectedModel minimizedWitness projectionAgreement : Prop} :
    AyMCPWCoreProjection
      fullModel projectedModel minimizedWitness projectionAgreement ->
    projectionAgreement :=
  fun h => ay_mcpw_conj_right
    (ay_mcpw_conj_right (ay_mcpw_conj_right h))

theorem ay_mcpw_dimacs_variable_maps_intro
    {solverMap dimacsMap mapAgreement : Prop} :
    solverMap ->
    dimacsMap ->
    mapAgreement ->
    AyMCPWDimacsVariableMaps solverMap dimacsMap mapAgreement :=
  fun hsolver hdimacs hagree =>
    ay_mcpw_conj_intro hsolver (ay_mcpw_conj_intro hdimacs hagree)

theorem ay_mcpw_dimacs_variable_maps_solver
    {solverMap dimacsMap mapAgreement : Prop} :
    AyMCPWDimacsVariableMaps solverMap dimacsMap mapAgreement ->
    solverMap :=
  fun h => ay_mcpw_conj_left h

theorem ay_mcpw_dimacs_variable_maps_dimacs
    {solverMap dimacsMap mapAgreement : Prop} :
    AyMCPWDimacsVariableMaps solverMap dimacsMap mapAgreement ->
    dimacsMap :=
  fun h => ay_mcpw_conj_left (ay_mcpw_conj_right h)

theorem ay_mcpw_dimacs_variable_maps_agreement
    {solverMap dimacsMap mapAgreement : Prop} :
    AyMCPWDimacsVariableMaps solverMap dimacsMap mapAgreement ->
    mapAgreement :=
  fun h => ay_mcpw_conj_right (ay_mcpw_conj_right h)

theorem ay_mcpw_reconstruction_evidence_intro
    {projectionEvidence reconstructionEvidence reconstructionAgreement : Prop} :
    projectionEvidence ->
    reconstructionEvidence ->
    reconstructionAgreement ->
    AyMCPWReconstructionEvidence
      projectionEvidence reconstructionEvidence reconstructionAgreement :=
  fun hprojection hreconstruction hagree =>
    ay_mcpw_conj_intro hprojection
      (ay_mcpw_conj_intro hreconstruction hagree)

theorem ay_mcpw_reconstruction_evidence_projection
    {projectionEvidence reconstructionEvidence reconstructionAgreement : Prop} :
    AyMCPWReconstructionEvidence
      projectionEvidence reconstructionEvidence reconstructionAgreement ->
    projectionEvidence :=
  fun h => ay_mcpw_conj_left h

theorem ay_mcpw_reconstruction_evidence_reconstruction
    {projectionEvidence reconstructionEvidence reconstructionAgreement : Prop} :
    AyMCPWReconstructionEvidence
      projectionEvidence reconstructionEvidence reconstructionAgreement ->
    reconstructionEvidence :=
  fun h => ay_mcpw_conj_left (ay_mcpw_conj_right h)

theorem ay_mcpw_reconstruction_evidence_agreement
    {projectionEvidence reconstructionEvidence reconstructionAgreement : Prop} :
    AyMCPWReconstructionEvidence
      projectionEvidence reconstructionEvidence reconstructionAgreement ->
    reconstructionAgreement :=
  fun h => ay_mcpw_conj_right (ay_mcpw_conj_right h)

theorem ay_mcpw_assignment_digest_intro
    {fullDigest projectedDigest digestAgreement : Prop} :
    fullDigest ->
    projectedDigest ->
    digestAgreement ->
    AyMCPWAssignmentDigest fullDigest projectedDigest digestAgreement :=
  fun hfull hprojected hagree =>
    ay_mcpw_conj_intro hfull (ay_mcpw_conj_intro hprojected hagree)

theorem ay_mcpw_assignment_digest_full
    {fullDigest projectedDigest digestAgreement : Prop} :
    AyMCPWAssignmentDigest fullDigest projectedDigest digestAgreement ->
    fullDigest :=
  fun h => ay_mcpw_conj_left h

theorem ay_mcpw_assignment_digest_projected
    {fullDigest projectedDigest digestAgreement : Prop} :
    AyMCPWAssignmentDigest fullDigest projectedDigest digestAgreement ->
    projectedDigest :=
  fun h => ay_mcpw_conj_left (ay_mcpw_conj_right h)

theorem ay_mcpw_assignment_digest_agreement
    {fullDigest projectedDigest digestAgreement : Prop} :
    AyMCPWAssignmentDigest fullDigest projectedDigest digestAgreement ->
    digestAgreement :=
  fun h => ay_mcpw_conj_right (ay_mcpw_conj_right h)

theorem ay_mcpw_clause_evaluation_replay_intro
    {clauseReplay projectedEvaluation evaluationAgreement : Prop} :
    clauseReplay ->
    projectedEvaluation ->
    evaluationAgreement ->
    AyMCPWClauseEvaluationReplay
      clauseReplay projectedEvaluation evaluationAgreement :=
  fun hreplay heval hagree =>
    ay_mcpw_conj_intro hreplay (ay_mcpw_conj_intro heval hagree)

theorem ay_mcpw_clause_evaluation_replay_trace
    {clauseReplay projectedEvaluation evaluationAgreement : Prop} :
    AyMCPWClauseEvaluationReplay
      clauseReplay projectedEvaluation evaluationAgreement ->
    clauseReplay :=
  fun h => ay_mcpw_conj_left h

theorem ay_mcpw_clause_evaluation_replay_evaluation
    {clauseReplay projectedEvaluation evaluationAgreement : Prop} :
    AyMCPWClauseEvaluationReplay
      clauseReplay projectedEvaluation evaluationAgreement ->
    projectedEvaluation :=
  fun h => ay_mcpw_conj_left (ay_mcpw_conj_right h)

theorem ay_mcpw_clause_evaluation_replay_agreement
    {clauseReplay projectedEvaluation evaluationAgreement : Prop} :
    AyMCPWClauseEvaluationReplay
      clauseReplay projectedEvaluation evaluationAgreement ->
    evaluationAgreement :=
  fun h => ay_mcpw_conj_right (ay_mcpw_conj_right h)

theorem ay_mcpw_checker_transcript_intro
    {checkerAccepted transcript replayAgreement : Prop} :
    checkerAccepted ->
    transcript ->
    replayAgreement ->
    AyMCPWCheckerTranscript checkerAccepted transcript replayAgreement :=
  fun haccepted htranscript hagree =>
    ay_mcpw_conj_intro haccepted
      (ay_mcpw_conj_intro htranscript hagree)

theorem ay_mcpw_checker_transcript_accepted
    {checkerAccepted transcript replayAgreement : Prop} :
    AyMCPWCheckerTranscript checkerAccepted transcript replayAgreement ->
    checkerAccepted :=
  fun h => ay_mcpw_conj_left h

theorem ay_mcpw_checker_transcript_transcript
    {checkerAccepted transcript replayAgreement : Prop} :
    AyMCPWCheckerTranscript checkerAccepted transcript replayAgreement ->
    transcript :=
  fun h => ay_mcpw_conj_left (ay_mcpw_conj_right h)

theorem ay_mcpw_checker_transcript_agreement
    {checkerAccepted transcript replayAgreement : Prop} :
    AyMCPWCheckerTranscript checkerAccepted transcript replayAgreement ->
    replayAgreement :=
  fun h => ay_mcpw_conj_right (ay_mcpw_conj_right h)

theorem ay_mcpw_formula_fingerprint_intro
    {originalFingerprint projectedFingerprint fingerprintAgreement : Prop} :
    originalFingerprint ->
    projectedFingerprint ->
    fingerprintAgreement ->
    AyMCPWFormulaFingerprint
      originalFingerprint projectedFingerprint fingerprintAgreement :=
  fun horiginal hprojected hagree =>
    ay_mcpw_conj_intro horiginal
      (ay_mcpw_conj_intro hprojected hagree)

theorem ay_mcpw_formula_fingerprint_original
    {originalFingerprint projectedFingerprint fingerprintAgreement : Prop} :
    AyMCPWFormulaFingerprint
      originalFingerprint projectedFingerprint fingerprintAgreement ->
    originalFingerprint :=
  fun h => ay_mcpw_conj_left h

theorem ay_mcpw_formula_fingerprint_projected
    {originalFingerprint projectedFingerprint fingerprintAgreement : Prop} :
    AyMCPWFormulaFingerprint
      originalFingerprint projectedFingerprint fingerprintAgreement ->
    projectedFingerprint :=
  fun h => ay_mcpw_conj_left (ay_mcpw_conj_right h)

theorem ay_mcpw_formula_fingerprint_agreement
    {originalFingerprint projectedFingerprint fingerprintAgreement : Prop} :
    AyMCPWFormulaFingerprint
      originalFingerprint projectedFingerprint fingerprintAgreement ->
    fingerprintAgreement :=
  fun h => ay_mcpw_conj_right (ay_mcpw_conj_right h)

theorem ay_mcpw_build_evidence_intro
    {solverBuild witnessBuild buildAgreement : Prop} :
    solverBuild ->
    witnessBuild ->
    buildAgreement ->
    AyMCPWBuildEvidence solverBuild witnessBuild buildAgreement :=
  fun hsolver hwitness hagree =>
    ay_mcpw_conj_intro hsolver (ay_mcpw_conj_intro hwitness hagree)

theorem ay_mcpw_build_evidence_solver
    {solverBuild witnessBuild buildAgreement : Prop} :
    AyMCPWBuildEvidence solverBuild witnessBuild buildAgreement ->
    solverBuild :=
  fun h => ay_mcpw_conj_left h

theorem ay_mcpw_build_evidence_witness
    {solverBuild witnessBuild buildAgreement : Prop} :
    AyMCPWBuildEvidence solverBuild witnessBuild buildAgreement ->
    witnessBuild :=
  fun h => ay_mcpw_conj_left (ay_mcpw_conj_right h)

theorem ay_mcpw_build_evidence_agreement
    {solverBuild witnessBuild buildAgreement : Prop} :
    AyMCPWBuildEvidence solverBuild witnessBuild buildAgreement ->
    buildAgreement :=
  fun h => ay_mcpw_conj_right (ay_mcpw_conj_right h)

theorem ay_mcpw_accepted_evidence_intro
    {projectionOk mapsOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk buildOk : Prop} :
    projectionOk ->
    mapsOk ->
    reconstructionOk ->
    digestOk ->
    clauseReplayOk ->
    transcriptOk ->
    fingerprintOk ->
    buildOk ->
    AyMCPWAcceptedEvidence
      projectionOk mapsOk reconstructionOk digestOk clauseReplayOk
      transcriptOk fingerprintOk buildOk :=
  fun hprojection hmaps hreconstruction hdigest hclause htranscript
      hfingerprint hbuild =>
    ay_mcpw_conj_intro hprojection
      (ay_mcpw_conj_intro hmaps
        (ay_mcpw_conj_intro hreconstruction
          (ay_mcpw_conj_intro hdigest
            (ay_mcpw_conj_intro hclause
              (ay_mcpw_conj_intro htranscript
                (ay_mcpw_conj_intro hfingerprint hbuild))))))

theorem ay_mcpw_accepted_evidence_projection
    {projectionOk mapsOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk buildOk : Prop} :
    AyMCPWAcceptedEvidence
      projectionOk mapsOk reconstructionOk digestOk clauseReplayOk
      transcriptOk fingerprintOk buildOk ->
    projectionOk :=
  fun h => ay_mcpw_conj_left h

theorem ay_mcpw_accepted_evidence_maps
    {projectionOk mapsOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk buildOk : Prop} :
    AyMCPWAcceptedEvidence
      projectionOk mapsOk reconstructionOk digestOk clauseReplayOk
      transcriptOk fingerprintOk buildOk ->
    mapsOk :=
  fun h => ay_mcpw_conj_left (ay_mcpw_conj_right h)

theorem ay_mcpw_accepted_evidence_reconstruction
    {projectionOk mapsOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk buildOk : Prop} :
    AyMCPWAcceptedEvidence
      projectionOk mapsOk reconstructionOk digestOk clauseReplayOk
      transcriptOk fingerprintOk buildOk ->
    reconstructionOk :=
  fun h => ay_mcpw_conj_left
    (ay_mcpw_conj_right (ay_mcpw_conj_right h))

theorem ay_mcpw_accepted_evidence_digest
    {projectionOk mapsOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk buildOk : Prop} :
    AyMCPWAcceptedEvidence
      projectionOk mapsOk reconstructionOk digestOk clauseReplayOk
      transcriptOk fingerprintOk buildOk ->
    digestOk :=
  fun h => ay_mcpw_conj_left
    (ay_mcpw_conj_right
      (ay_mcpw_conj_right (ay_mcpw_conj_right h)))

theorem ay_mcpw_accepted_evidence_clause_replay
    {projectionOk mapsOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk buildOk : Prop} :
    AyMCPWAcceptedEvidence
      projectionOk mapsOk reconstructionOk digestOk clauseReplayOk
      transcriptOk fingerprintOk buildOk ->
    clauseReplayOk :=
  fun h => ay_mcpw_conj_left
    (ay_mcpw_conj_right
      (ay_mcpw_conj_right
        (ay_mcpw_conj_right (ay_mcpw_conj_right h))))

theorem ay_mcpw_accepted_evidence_transcript
    {projectionOk mapsOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk buildOk : Prop} :
    AyMCPWAcceptedEvidence
      projectionOk mapsOk reconstructionOk digestOk clauseReplayOk
      transcriptOk fingerprintOk buildOk ->
    transcriptOk :=
  fun h => ay_mcpw_conj_left
    (ay_mcpw_conj_right
      (ay_mcpw_conj_right
        (ay_mcpw_conj_right
          (ay_mcpw_conj_right (ay_mcpw_conj_right h)))))

theorem ay_mcpw_accepted_evidence_fingerprint
    {projectionOk mapsOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk buildOk : Prop} :
    AyMCPWAcceptedEvidence
      projectionOk mapsOk reconstructionOk digestOk clauseReplayOk
      transcriptOk fingerprintOk buildOk ->
    fingerprintOk :=
  fun h => ay_mcpw_conj_left
    (ay_mcpw_conj_right
      (ay_mcpw_conj_right
        (ay_mcpw_conj_right
          (ay_mcpw_conj_right
            (ay_mcpw_conj_right (ay_mcpw_conj_right h))))))

theorem ay_mcpw_accepted_evidence_build
    {projectionOk mapsOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk buildOk : Prop} :
    AyMCPWAcceptedEvidence
      projectionOk mapsOk reconstructionOk digestOk clauseReplayOk
      transcriptOk fingerprintOk buildOk ->
    buildOk :=
  fun h => ay_mcpw_conj_right
    (ay_mcpw_conj_right
      (ay_mcpw_conj_right
        (ay_mcpw_conj_right
          (ay_mcpw_conj_right
            (ay_mcpw_conj_right (ay_mcpw_conj_right h))))))

theorem ay_mcpw_public_sat_witness_intro
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    acceptedEvidence ->
    publicWitness ->
    publicSatClaim ->
    AyMCPWPublicSatWitness acceptedEvidence publicWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_mcpw_conj_intro hevidence
      (ay_mcpw_conj_intro hwitness hclaim)

theorem ay_mcpw_public_sat_witness_evidence
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMCPWPublicSatWitness acceptedEvidence publicWitness publicSatClaim ->
    acceptedEvidence :=
  fun h => ay_mcpw_conj_left h

theorem ay_mcpw_public_sat_witness_witness
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMCPWPublicSatWitness acceptedEvidence publicWitness publicSatClaim ->
    publicWitness :=
  fun h => ay_mcpw_conj_left (ay_mcpw_conj_right h)

theorem ay_mcpw_public_sat_witness_claim
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMCPWPublicSatWitness acceptedEvidence publicWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_mcpw_conj_right (ay_mcpw_conj_right h)

theorem ay_mcpw_accepted_core_projection_publishes_sound_sat
    {projectionOk mapsOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk buildOk publicWitness publicSatClaim : Prop} :
    AyMCPWAcceptedEvidence
      projectionOk mapsOk reconstructionOk digestOk clauseReplayOk
      transcriptOk fingerprintOk buildOk ->
    publicWitness ->
    publicSatClaim ->
    AyMCPWPublicSatWitness
      (AyMCPWAcceptedEvidence
        projectionOk mapsOk reconstructionOk digestOk clauseReplayOk
        transcriptOk fingerprintOk buildOk)
      publicWitness
      publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_mcpw_public_sat_witness_intro hevidence hwitness hclaim

theorem ay_mcpw_public_sat_requires_accepted_evidence
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMCPWPublicSatWitness acceptedEvidence publicWitness publicSatClaim ->
    acceptedEvidence :=
  fun h => ay_mcpw_public_sat_witness_evidence h

theorem ay_mcpw_projection_minimization_preserves_truth
    {fullTruth projectedTruth : Prop} :
    AyMCPWEquisat fullTruth projectedTruth ->
    fullTruth ->
    projectedTruth :=
  fun heq hfull => ay_mcpw_equisat_forward heq hfull

theorem ay_mcpw_clause_replay_transports_truth
    {clauseReplay projectedEvaluation formulaTruth : Prop} :
    AyMCPWClauseEvaluationReplay
      clauseReplay projectedEvaluation formulaTruth ->
    formulaTruth :=
  fun h => ay_mcpw_clause_evaluation_replay_agreement h

theorem ay_mcpw_publication_requires_projection
    {projectionOk mapsOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk buildOk publicWitness publicSatClaim : Prop} :
    AyMCPWPublicSatWitness
      (AyMCPWAcceptedEvidence
        projectionOk mapsOk reconstructionOk digestOk clauseReplayOk
        transcriptOk fingerprintOk buildOk)
      publicWitness
      publicSatClaim ->
    projectionOk :=
  fun h =>
    ay_mcpw_accepted_evidence_projection
      (ay_mcpw_public_sat_witness_evidence h)

theorem ay_mcpw_publication_requires_maps
    {projectionOk mapsOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk buildOk publicWitness publicSatClaim : Prop} :
    AyMCPWPublicSatWitness
      (AyMCPWAcceptedEvidence
        projectionOk mapsOk reconstructionOk digestOk clauseReplayOk
        transcriptOk fingerprintOk buildOk)
      publicWitness
      publicSatClaim ->
    mapsOk :=
  fun h =>
    ay_mcpw_accepted_evidence_maps
      (ay_mcpw_public_sat_witness_evidence h)

theorem ay_mcpw_publication_requires_reconstruction
    {projectionOk mapsOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk buildOk publicWitness publicSatClaim : Prop} :
    AyMCPWPublicSatWitness
      (AyMCPWAcceptedEvidence
        projectionOk mapsOk reconstructionOk digestOk clauseReplayOk
        transcriptOk fingerprintOk buildOk)
      publicWitness
      publicSatClaim ->
    reconstructionOk :=
  fun h =>
    ay_mcpw_accepted_evidence_reconstruction
      (ay_mcpw_public_sat_witness_evidence h)

theorem ay_mcpw_publication_requires_digest
    {projectionOk mapsOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk buildOk publicWitness publicSatClaim : Prop} :
    AyMCPWPublicSatWitness
      (AyMCPWAcceptedEvidence
        projectionOk mapsOk reconstructionOk digestOk clauseReplayOk
        transcriptOk fingerprintOk buildOk)
      publicWitness
      publicSatClaim ->
    digestOk :=
  fun h =>
    ay_mcpw_accepted_evidence_digest
      (ay_mcpw_public_sat_witness_evidence h)

theorem ay_mcpw_publication_requires_clause_replay
    {projectionOk mapsOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk buildOk publicWitness publicSatClaim : Prop} :
    AyMCPWPublicSatWitness
      (AyMCPWAcceptedEvidence
        projectionOk mapsOk reconstructionOk digestOk clauseReplayOk
        transcriptOk fingerprintOk buildOk)
      publicWitness
      publicSatClaim ->
    clauseReplayOk :=
  fun h =>
    ay_mcpw_accepted_evidence_clause_replay
      (ay_mcpw_public_sat_witness_evidence h)

theorem ay_mcpw_publication_requires_transcript
    {projectionOk mapsOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk buildOk publicWitness publicSatClaim : Prop} :
    AyMCPWPublicSatWitness
      (AyMCPWAcceptedEvidence
        projectionOk mapsOk reconstructionOk digestOk clauseReplayOk
        transcriptOk fingerprintOk buildOk)
      publicWitness
      publicSatClaim ->
    transcriptOk :=
  fun h =>
    ay_mcpw_accepted_evidence_transcript
      (ay_mcpw_public_sat_witness_evidence h)

theorem ay_mcpw_publication_requires_fingerprint
    {projectionOk mapsOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk buildOk publicWitness publicSatClaim : Prop} :
    AyMCPWPublicSatWitness
      (AyMCPWAcceptedEvidence
        projectionOk mapsOk reconstructionOk digestOk clauseReplayOk
        transcriptOk fingerprintOk buildOk)
      publicWitness
      publicSatClaim ->
    fingerprintOk :=
  fun h =>
    ay_mcpw_accepted_evidence_fingerprint
      (ay_mcpw_public_sat_witness_evidence h)

theorem ay_mcpw_publication_requires_build
    {projectionOk mapsOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk buildOk publicWitness publicSatClaim : Prop} :
    AyMCPWPublicSatWitness
      (AyMCPWAcceptedEvidence
        projectionOk mapsOk reconstructionOk digestOk clauseReplayOk
        transcriptOk fingerprintOk buildOk)
      publicWitness
      publicSatClaim ->
    buildOk :=
  fun h =>
    ay_mcpw_accepted_evidence_build
      (ay_mcpw_public_sat_witness_evidence h)

theorem ay_mcpw_no_claim_diagnostic_intro
    {diagnostic publicSatClaim : Prop} :
    diagnostic ->
    (publicSatClaim -> False) ->
    AyMCPWNoClaimDiagnostic diagnostic publicSatClaim :=
  fun hdiagnostic hblocks =>
    ay_mcpw_conj_intro hdiagnostic hblocks

theorem ay_mcpw_no_claim_diagnostic_reason
    {diagnostic publicSatClaim : Prop} :
    AyMCPWNoClaimDiagnostic diagnostic publicSatClaim -> diagnostic :=
  fun h => ay_mcpw_conj_left h

theorem ay_mcpw_no_claim_diagnostic_blocks
    {diagnostic publicSatClaim : Prop} :
    AyMCPWNoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h => ay_mcpw_conj_right h

theorem ay_mcpw_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMCPWRecomputeObligation reason recomputeRequest :=
  fun hreason hrecompute => ay_mcpw_conj_intro hreason hrecompute

theorem ay_mcpw_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMCPWRecomputeObligation reason recomputeRequest -> reason :=
  fun h => ay_mcpw_conj_left h

theorem ay_mcpw_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMCPWRecomputeObligation reason recomputeRequest -> recomputeRequest :=
  fun h => ay_mcpw_conj_right h

theorem ay_mcpw_missing_map_recompute
    {missingMap recomputeRequest : Prop} :
    missingMap ->
    recomputeRequest ->
    AyMCPWRecomputeObligation missingMap recomputeRequest :=
  fun hmissing hrecompute =>
    ay_mcpw_recompute_obligation_intro hmissing hrecompute

theorem ay_mcpw_missing_map_no_claim
    {missingMap publicSatClaim : Prop} :
    missingMap ->
    (publicSatClaim -> False) ->
    AyMCPWNoClaimDiagnostic missingMap publicSatClaim :=
  fun hmissing hblocks =>
    ay_mcpw_no_claim_diagnostic_intro hmissing hblocks

theorem ay_mcpw_projection_mismatch_recompute
    {projectionMismatch recomputeRequest : Prop} :
    projectionMismatch ->
    recomputeRequest ->
    AyMCPWRecomputeObligation projectionMismatch recomputeRequest :=
  fun hmismatch hrecompute =>
    ay_mcpw_recompute_obligation_intro hmismatch hrecompute

theorem ay_mcpw_projection_mismatch_no_claim
    {projectionMismatch publicSatClaim : Prop} :
    projectionMismatch ->
    (publicSatClaim -> False) ->
    AyMCPWNoClaimDiagnostic projectionMismatch publicSatClaim :=
  fun hmismatch hblocks =>
    ay_mcpw_no_claim_diagnostic_intro hmismatch hblocks

theorem ay_mcpw_digest_drift_no_claim
    {digestDrift publicSatClaim : Prop} :
    digestDrift ->
    (publicSatClaim -> False) ->
    AyMCPWNoClaimDiagnostic digestDrift publicSatClaim :=
  fun hdrift hblocks => ay_mcpw_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mcpw_replay_failure_no_claim
    {replayFailure publicSatClaim : Prop} :
    replayFailure ->
    (publicSatClaim -> False) ->
    AyMCPWNoClaimDiagnostic replayFailure publicSatClaim :=
  fun hfailure hblocks =>
    ay_mcpw_no_claim_diagnostic_intro hfailure hblocks

theorem ay_mcpw_stale_fingerprint_no_claim
    {staleFingerprint publicSatClaim : Prop} :
    staleFingerprint ->
    (publicSatClaim -> False) ->
    AyMCPWNoClaimDiagnostic staleFingerprint publicSatClaim :=
  fun hstale hblocks => ay_mcpw_no_claim_diagnostic_intro hstale hblocks

theorem ay_mcpw_checker_rejection_no_claim
    {checkerRejection publicSatClaim : Prop} :
    checkerRejection ->
    (publicSatClaim -> False) ->
    AyMCPWNoClaimDiagnostic checkerRejection publicSatClaim :=
  fun hreject hblocks =>
    ay_mcpw_no_claim_diagnostic_intro hreject hblocks

theorem ay_mcpw_build_drift_no_claim
    {buildDrift publicSatClaim : Prop} :
    buildDrift ->
    (publicSatClaim -> False) ->
    AyMCPWNoClaimDiagnostic buildDrift publicSatClaim :=
  fun hdrift hblocks => ay_mcpw_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mcpw_diagnostic_blocks_public_claim
    {diagnostic publicSatClaim : Prop} :
    AyMCPWNoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_mcpw_no_claim_diagnostic_blocks h hclaim

theorem ay_mcpw_bad_core_projection_cannot_bless_sat
    {badProjection publicSatClaim : Prop} :
    AyMCPWNoClaimDiagnostic badProjection publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_mcpw_diagnostic_blocks_public_claim h hclaim
