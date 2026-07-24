-- SAT-COMP/ay incremental assignment digest emission soundness skeleton.
-- Incremental SAT witness chunks may be emitted only when chunk digests, final
-- digest, DIMACS maps, replay, transcript, fingerprint, and build evidence
-- agree.

def AyMIDEConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMIDEDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMIDEEquisat (left right : Prop) : Prop :=
  AyMIDEConj (left -> right) (right -> left)

def AyMIDEChunkDigests
    (chunkManifest chunkDigests chunkDigestAgreement : Prop) : Prop :=
  AyMIDEConj chunkManifest
    (AyMIDEConj chunkDigests chunkDigestAgreement)

def AyMIDEFinalAssignmentDigest
    (incrementalDigest finalDigest digestAgreement : Prop) : Prop :=
  AyMIDEConj incrementalDigest
    (AyMIDEConj finalDigest digestAgreement)

def AyMIDEDimacsVariableMaps
    (chunkVariableMap dimacsVariableMap mapAgreement : Prop) : Prop :=
  AyMIDEConj chunkVariableMap
    (AyMIDEConj dimacsVariableMap mapAgreement)

def AyMIDEClauseEvaluationReplay
    (clauseReplay finalEvaluation evaluationAgreement : Prop) : Prop :=
  AyMIDEConj clauseReplay
    (AyMIDEConj finalEvaluation evaluationAgreement)

def AyMIDECheckerTranscript
    (checkerAccepted transcript replayAgreement : Prop) : Prop :=
  AyMIDEConj checkerAccepted (AyMIDEConj transcript replayAgreement)

def AyMIDEFormulaFingerprint
    (originalFingerprint emittedFingerprint fingerprintAgreement : Prop) :
    Prop :=
  AyMIDEConj originalFingerprint
    (AyMIDEConj emittedFingerprint fingerprintAgreement)

def AyMIDEBuildEvidence
    (solverBuild emissionBuild buildAgreement : Prop) : Prop :=
  AyMIDEConj solverBuild (AyMIDEConj emissionBuild buildAgreement)

def AyMIDEAcceptedEvidence
    (chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
      buildOk : Prop) : Prop :=
  AyMIDEConj chunksOk
    (AyMIDEConj finalDigestOk
      (AyMIDEConj mapsOk
        (AyMIDEConj clauseReplayOk
          (AyMIDEConj transcriptOk
            (AyMIDEConj fingerprintOk buildOk)))))

def AyMIDEPublicSatWitness
    (acceptedEvidence publicWitness publicSatClaim : Prop) : Prop :=
  AyMIDEConj acceptedEvidence
    (AyMIDEConj publicWitness publicSatClaim)

def AyMIDENoClaimDiagnostic (diagnostic publicSatClaim : Prop) : Prop :=
  AyMIDEConj diagnostic (publicSatClaim -> False)

def AyMIDERecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMIDEConj reason recomputeRequest

theorem ay_mide_conj_intro {left right : Prop} :
    left -> right -> AyMIDEConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_mide_conj_left {left right : Prop} :
    AyMIDEConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_mide_conj_right {left right : Prop} :
    AyMIDEConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_mide_disj_left {left right : Prop} :
    left -> AyMIDEDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_mide_disj_right {left right : Prop} :
    right -> AyMIDEDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_mide_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMIDEEquisat left right :=
  fun hf hb => ay_mide_conj_intro hf hb

theorem ay_mide_equisat_forward {left right : Prop} :
    AyMIDEEquisat left right -> left -> right :=
  fun h => ay_mide_conj_left h

theorem ay_mide_equisat_backward {left right : Prop} :
    AyMIDEEquisat left right -> right -> left :=
  fun h => ay_mide_conj_right h

theorem ay_mide_chunk_digests_intro
    {chunkManifest chunkDigests chunkDigestAgreement : Prop} :
    chunkManifest ->
    chunkDigests ->
    chunkDigestAgreement ->
    AyMIDEChunkDigests
      chunkManifest chunkDigests chunkDigestAgreement :=
  fun hmanifest hdigests hagree =>
    ay_mide_conj_intro hmanifest
      (ay_mide_conj_intro hdigests hagree)

theorem ay_mide_chunk_digests_manifest
    {chunkManifest chunkDigests chunkDigestAgreement : Prop} :
    AyMIDEChunkDigests
      chunkManifest chunkDigests chunkDigestAgreement ->
    chunkManifest :=
  fun h => ay_mide_conj_left h

theorem ay_mide_chunk_digests_digests
    {chunkManifest chunkDigests chunkDigestAgreement : Prop} :
    AyMIDEChunkDigests
      chunkManifest chunkDigests chunkDigestAgreement ->
    chunkDigests :=
  fun h => ay_mide_conj_left (ay_mide_conj_right h)

theorem ay_mide_chunk_digests_agreement
    {chunkManifest chunkDigests chunkDigestAgreement : Prop} :
    AyMIDEChunkDigests
      chunkManifest chunkDigests chunkDigestAgreement ->
    chunkDigestAgreement :=
  fun h => ay_mide_conj_right (ay_mide_conj_right h)

theorem ay_mide_final_assignment_digest_intro
    {incrementalDigest finalDigest digestAgreement : Prop} :
    incrementalDigest ->
    finalDigest ->
    digestAgreement ->
    AyMIDEFinalAssignmentDigest
      incrementalDigest finalDigest digestAgreement :=
  fun hincremental hfinal hagree =>
    ay_mide_conj_intro hincremental
      (ay_mide_conj_intro hfinal hagree)

theorem ay_mide_final_assignment_digest_incremental
    {incrementalDigest finalDigest digestAgreement : Prop} :
    AyMIDEFinalAssignmentDigest
      incrementalDigest finalDigest digestAgreement ->
    incrementalDigest :=
  fun h => ay_mide_conj_left h

theorem ay_mide_final_assignment_digest_final
    {incrementalDigest finalDigest digestAgreement : Prop} :
    AyMIDEFinalAssignmentDigest
      incrementalDigest finalDigest digestAgreement ->
    finalDigest :=
  fun h => ay_mide_conj_left (ay_mide_conj_right h)

theorem ay_mide_final_assignment_digest_agreement
    {incrementalDigest finalDigest digestAgreement : Prop} :
    AyMIDEFinalAssignmentDigest
      incrementalDigest finalDigest digestAgreement ->
    digestAgreement :=
  fun h => ay_mide_conj_right (ay_mide_conj_right h)

theorem ay_mide_dimacs_variable_maps_intro
    {chunkVariableMap dimacsVariableMap mapAgreement : Prop} :
    chunkVariableMap ->
    dimacsVariableMap ->
    mapAgreement ->
    AyMIDEDimacsVariableMaps
      chunkVariableMap dimacsVariableMap mapAgreement :=
  fun hchunk hdimacs hagree =>
    ay_mide_conj_intro hchunk (ay_mide_conj_intro hdimacs hagree)

theorem ay_mide_dimacs_variable_maps_chunk
    {chunkVariableMap dimacsVariableMap mapAgreement : Prop} :
    AyMIDEDimacsVariableMaps
      chunkVariableMap dimacsVariableMap mapAgreement ->
    chunkVariableMap :=
  fun h => ay_mide_conj_left h

theorem ay_mide_dimacs_variable_maps_dimacs
    {chunkVariableMap dimacsVariableMap mapAgreement : Prop} :
    AyMIDEDimacsVariableMaps
      chunkVariableMap dimacsVariableMap mapAgreement ->
    dimacsVariableMap :=
  fun h => ay_mide_conj_left (ay_mide_conj_right h)

theorem ay_mide_dimacs_variable_maps_agreement
    {chunkVariableMap dimacsVariableMap mapAgreement : Prop} :
    AyMIDEDimacsVariableMaps
      chunkVariableMap dimacsVariableMap mapAgreement ->
    mapAgreement :=
  fun h => ay_mide_conj_right (ay_mide_conj_right h)

theorem ay_mide_clause_evaluation_replay_intro
    {clauseReplay finalEvaluation evaluationAgreement : Prop} :
    clauseReplay ->
    finalEvaluation ->
    evaluationAgreement ->
    AyMIDEClauseEvaluationReplay
      clauseReplay finalEvaluation evaluationAgreement :=
  fun hreplay hfinal hagree =>
    ay_mide_conj_intro hreplay (ay_mide_conj_intro hfinal hagree)

theorem ay_mide_clause_evaluation_replay_trace
    {clauseReplay finalEvaluation evaluationAgreement : Prop} :
    AyMIDEClauseEvaluationReplay
      clauseReplay finalEvaluation evaluationAgreement ->
    clauseReplay :=
  fun h => ay_mide_conj_left h

theorem ay_mide_clause_evaluation_replay_final
    {clauseReplay finalEvaluation evaluationAgreement : Prop} :
    AyMIDEClauseEvaluationReplay
      clauseReplay finalEvaluation evaluationAgreement ->
    finalEvaluation :=
  fun h => ay_mide_conj_left (ay_mide_conj_right h)

theorem ay_mide_clause_evaluation_replay_agreement
    {clauseReplay finalEvaluation evaluationAgreement : Prop} :
    AyMIDEClauseEvaluationReplay
      clauseReplay finalEvaluation evaluationAgreement ->
    evaluationAgreement :=
  fun h => ay_mide_conj_right (ay_mide_conj_right h)

theorem ay_mide_checker_transcript_intro
    {checkerAccepted transcript replayAgreement : Prop} :
    checkerAccepted ->
    transcript ->
    replayAgreement ->
    AyMIDECheckerTranscript checkerAccepted transcript replayAgreement :=
  fun haccepted htranscript hagree =>
    ay_mide_conj_intro haccepted
      (ay_mide_conj_intro htranscript hagree)

theorem ay_mide_checker_transcript_accepted
    {checkerAccepted transcript replayAgreement : Prop} :
    AyMIDECheckerTranscript checkerAccepted transcript replayAgreement ->
    checkerAccepted :=
  fun h => ay_mide_conj_left h

theorem ay_mide_checker_transcript_transcript
    {checkerAccepted transcript replayAgreement : Prop} :
    AyMIDECheckerTranscript checkerAccepted transcript replayAgreement ->
    transcript :=
  fun h => ay_mide_conj_left (ay_mide_conj_right h)

theorem ay_mide_checker_transcript_agreement
    {checkerAccepted transcript replayAgreement : Prop} :
    AyMIDECheckerTranscript checkerAccepted transcript replayAgreement ->
    replayAgreement :=
  fun h => ay_mide_conj_right (ay_mide_conj_right h)

theorem ay_mide_formula_fingerprint_intro
    {originalFingerprint emittedFingerprint fingerprintAgreement : Prop} :
    originalFingerprint ->
    emittedFingerprint ->
    fingerprintAgreement ->
    AyMIDEFormulaFingerprint
      originalFingerprint emittedFingerprint fingerprintAgreement :=
  fun horiginal hemitted hagree =>
    ay_mide_conj_intro horiginal
      (ay_mide_conj_intro hemitted hagree)

theorem ay_mide_formula_fingerprint_original
    {originalFingerprint emittedFingerprint fingerprintAgreement : Prop} :
    AyMIDEFormulaFingerprint
      originalFingerprint emittedFingerprint fingerprintAgreement ->
    originalFingerprint :=
  fun h => ay_mide_conj_left h

theorem ay_mide_formula_fingerprint_emitted
    {originalFingerprint emittedFingerprint fingerprintAgreement : Prop} :
    AyMIDEFormulaFingerprint
      originalFingerprint emittedFingerprint fingerprintAgreement ->
    emittedFingerprint :=
  fun h => ay_mide_conj_left (ay_mide_conj_right h)

theorem ay_mide_formula_fingerprint_agreement
    {originalFingerprint emittedFingerprint fingerprintAgreement : Prop} :
    AyMIDEFormulaFingerprint
      originalFingerprint emittedFingerprint fingerprintAgreement ->
    fingerprintAgreement :=
  fun h => ay_mide_conj_right (ay_mide_conj_right h)

theorem ay_mide_build_evidence_intro
    {solverBuild emissionBuild buildAgreement : Prop} :
    solverBuild ->
    emissionBuild ->
    buildAgreement ->
    AyMIDEBuildEvidence solverBuild emissionBuild buildAgreement :=
  fun hsolver hemission hagree =>
    ay_mide_conj_intro hsolver (ay_mide_conj_intro hemission hagree)

theorem ay_mide_build_evidence_solver
    {solverBuild emissionBuild buildAgreement : Prop} :
    AyMIDEBuildEvidence solverBuild emissionBuild buildAgreement ->
    solverBuild :=
  fun h => ay_mide_conj_left h

theorem ay_mide_build_evidence_emission
    {solverBuild emissionBuild buildAgreement : Prop} :
    AyMIDEBuildEvidence solverBuild emissionBuild buildAgreement ->
    emissionBuild :=
  fun h => ay_mide_conj_left (ay_mide_conj_right h)

theorem ay_mide_build_evidence_agreement
    {solverBuild emissionBuild buildAgreement : Prop} :
    AyMIDEBuildEvidence solverBuild emissionBuild buildAgreement ->
    buildAgreement :=
  fun h => ay_mide_conj_right (ay_mide_conj_right h)

theorem ay_mide_accepted_evidence_intro
    {chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
      buildOk : Prop} :
    chunksOk ->
    finalDigestOk ->
    mapsOk ->
    clauseReplayOk ->
    transcriptOk ->
    fingerprintOk ->
    buildOk ->
    AyMIDEAcceptedEvidence
      chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
      buildOk :=
  fun hchunks hfinal hmaps hclause htranscript hfingerprint hbuild =>
    ay_mide_conj_intro hchunks
      (ay_mide_conj_intro hfinal
        (ay_mide_conj_intro hmaps
          (ay_mide_conj_intro hclause
            (ay_mide_conj_intro htranscript
              (ay_mide_conj_intro hfingerprint hbuild)))))

theorem ay_mide_accepted_evidence_chunks
    {chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
      buildOk : Prop} :
    AyMIDEAcceptedEvidence
      chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
      buildOk ->
    chunksOk :=
  fun h => ay_mide_conj_left h

theorem ay_mide_accepted_evidence_final_digest
    {chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
      buildOk : Prop} :
    AyMIDEAcceptedEvidence
      chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
      buildOk ->
    finalDigestOk :=
  fun h => ay_mide_conj_left (ay_mide_conj_right h)

theorem ay_mide_accepted_evidence_maps
    {chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
      buildOk : Prop} :
    AyMIDEAcceptedEvidence
      chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
      buildOk ->
    mapsOk :=
  fun h => ay_mide_conj_left
    (ay_mide_conj_right (ay_mide_conj_right h))

theorem ay_mide_accepted_evidence_clause_replay
    {chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
      buildOk : Prop} :
    AyMIDEAcceptedEvidence
      chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
      buildOk ->
    clauseReplayOk :=
  fun h => ay_mide_conj_left
    (ay_mide_conj_right
      (ay_mide_conj_right (ay_mide_conj_right h)))

theorem ay_mide_accepted_evidence_transcript
    {chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
      buildOk : Prop} :
    AyMIDEAcceptedEvidence
      chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
      buildOk ->
    transcriptOk :=
  fun h => ay_mide_conj_left
    (ay_mide_conj_right
      (ay_mide_conj_right
        (ay_mide_conj_right (ay_mide_conj_right h))))

theorem ay_mide_accepted_evidence_fingerprint
    {chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
      buildOk : Prop} :
    AyMIDEAcceptedEvidence
      chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
      buildOk ->
    fingerprintOk :=
  fun h => ay_mide_conj_left
    (ay_mide_conj_right
      (ay_mide_conj_right
        (ay_mide_conj_right
          (ay_mide_conj_right (ay_mide_conj_right h)))))

theorem ay_mide_accepted_evidence_build
    {chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
      buildOk : Prop} :
    AyMIDEAcceptedEvidence
      chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
      buildOk ->
    buildOk :=
  fun h => ay_mide_conj_right
    (ay_mide_conj_right
      (ay_mide_conj_right
        (ay_mide_conj_right
          (ay_mide_conj_right (ay_mide_conj_right h)))))

theorem ay_mide_public_sat_witness_intro
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    acceptedEvidence ->
    publicWitness ->
    publicSatClaim ->
    AyMIDEPublicSatWitness acceptedEvidence publicWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_mide_conj_intro hevidence
      (ay_mide_conj_intro hwitness hclaim)

theorem ay_mide_public_sat_witness_evidence
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMIDEPublicSatWitness acceptedEvidence publicWitness publicSatClaim ->
    acceptedEvidence :=
  fun h => ay_mide_conj_left h

theorem ay_mide_public_sat_witness_witness
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMIDEPublicSatWitness acceptedEvidence publicWitness publicSatClaim ->
    publicWitness :=
  fun h => ay_mide_conj_left (ay_mide_conj_right h)

theorem ay_mide_public_sat_witness_claim
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMIDEPublicSatWitness acceptedEvidence publicWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_mide_conj_right (ay_mide_conj_right h)

theorem ay_mide_accepted_incremental_digest_publishes_sound_sat
    {chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
      buildOk publicWitness publicSatClaim : Prop} :
    AyMIDEAcceptedEvidence
      chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
      buildOk ->
    publicWitness ->
    publicSatClaim ->
    AyMIDEPublicSatWitness
      (AyMIDEAcceptedEvidence
        chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk
        fingerprintOk buildOk)
      publicWitness
      publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_mide_public_sat_witness_intro hevidence hwitness hclaim

theorem ay_mide_public_sat_requires_accepted_evidence
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMIDEPublicSatWitness acceptedEvidence publicWitness publicSatClaim ->
    acceptedEvidence :=
  fun h => ay_mide_public_sat_witness_evidence h

theorem ay_mide_incremental_chunks_preserve_truth
    {chunkTruth finalTruth : Prop} :
    AyMIDEEquisat chunkTruth finalTruth ->
    chunkTruth ->
    finalTruth :=
  fun heq hchunk => ay_mide_equisat_forward heq hchunk

theorem ay_mide_clause_replay_transports_truth
    {clauseReplay finalEvaluation formulaTruth : Prop} :
    AyMIDEClauseEvaluationReplay
      clauseReplay finalEvaluation formulaTruth ->
    formulaTruth :=
  fun h => ay_mide_clause_evaluation_replay_agreement h

theorem ay_mide_publication_requires_chunks
    {chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
      buildOk publicWitness publicSatClaim : Prop} :
    AyMIDEPublicSatWitness
      (AyMIDEAcceptedEvidence
        chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
        buildOk)
      publicWitness
      publicSatClaim ->
    chunksOk :=
  fun h =>
    ay_mide_accepted_evidence_chunks
      (ay_mide_public_sat_witness_evidence h)

theorem ay_mide_publication_requires_final_digest
    {chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
      buildOk publicWitness publicSatClaim : Prop} :
    AyMIDEPublicSatWitness
      (AyMIDEAcceptedEvidence
        chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
        buildOk)
      publicWitness
      publicSatClaim ->
    finalDigestOk :=
  fun h =>
    ay_mide_accepted_evidence_final_digest
      (ay_mide_public_sat_witness_evidence h)

theorem ay_mide_publication_requires_maps
    {chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
      buildOk publicWitness publicSatClaim : Prop} :
    AyMIDEPublicSatWitness
      (AyMIDEAcceptedEvidence
        chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
        buildOk)
      publicWitness
      publicSatClaim ->
    mapsOk :=
  fun h =>
    ay_mide_accepted_evidence_maps
      (ay_mide_public_sat_witness_evidence h)

theorem ay_mide_publication_requires_clause_replay
    {chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
      buildOk publicWitness publicSatClaim : Prop} :
    AyMIDEPublicSatWitness
      (AyMIDEAcceptedEvidence
        chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
        buildOk)
      publicWitness
      publicSatClaim ->
    clauseReplayOk :=
  fun h =>
    ay_mide_accepted_evidence_clause_replay
      (ay_mide_public_sat_witness_evidence h)

theorem ay_mide_publication_requires_transcript
    {chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
      buildOk publicWitness publicSatClaim : Prop} :
    AyMIDEPublicSatWitness
      (AyMIDEAcceptedEvidence
        chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
        buildOk)
      publicWitness
      publicSatClaim ->
    transcriptOk :=
  fun h =>
    ay_mide_accepted_evidence_transcript
      (ay_mide_public_sat_witness_evidence h)

theorem ay_mide_publication_requires_fingerprint
    {chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
      buildOk publicWitness publicSatClaim : Prop} :
    AyMIDEPublicSatWitness
      (AyMIDEAcceptedEvidence
        chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
        buildOk)
      publicWitness
      publicSatClaim ->
    fingerprintOk :=
  fun h =>
    ay_mide_accepted_evidence_fingerprint
      (ay_mide_public_sat_witness_evidence h)

theorem ay_mide_publication_requires_build
    {chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
      buildOk publicWitness publicSatClaim : Prop} :
    AyMIDEPublicSatWitness
      (AyMIDEAcceptedEvidence
        chunksOk finalDigestOk mapsOk clauseReplayOk transcriptOk fingerprintOk
        buildOk)
      publicWitness
      publicSatClaim ->
    buildOk :=
  fun h =>
    ay_mide_accepted_evidence_build
      (ay_mide_public_sat_witness_evidence h)

theorem ay_mide_no_claim_diagnostic_intro
    {diagnostic publicSatClaim : Prop} :
    diagnostic ->
    (publicSatClaim -> False) ->
    AyMIDENoClaimDiagnostic diagnostic publicSatClaim :=
  fun hdiagnostic hblocks =>
    ay_mide_conj_intro hdiagnostic hblocks

theorem ay_mide_no_claim_diagnostic_reason
    {diagnostic publicSatClaim : Prop} :
    AyMIDENoClaimDiagnostic diagnostic publicSatClaim -> diagnostic :=
  fun h => ay_mide_conj_left h

theorem ay_mide_no_claim_diagnostic_blocks
    {diagnostic publicSatClaim : Prop} :
    AyMIDENoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h => ay_mide_conj_right h

theorem ay_mide_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMIDERecomputeObligation reason recomputeRequest :=
  fun hreason hrecompute => ay_mide_conj_intro hreason hrecompute

theorem ay_mide_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMIDERecomputeObligation reason recomputeRequest -> reason :=
  fun h => ay_mide_conj_left h

theorem ay_mide_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMIDERecomputeObligation reason recomputeRequest -> recomputeRequest :=
  fun h => ay_mide_conj_right h

theorem ay_mide_missing_chunk_recompute
    {missingChunk recomputeRequest : Prop} :
    missingChunk ->
    recomputeRequest ->
    AyMIDERecomputeObligation missingChunk recomputeRequest :=
  fun hmissing hrecompute =>
    ay_mide_recompute_obligation_intro hmissing hrecompute

theorem ay_mide_missing_chunk_no_claim
    {missingChunk publicSatClaim : Prop} :
    missingChunk ->
    (publicSatClaim -> False) ->
    AyMIDENoClaimDiagnostic missingChunk publicSatClaim :=
  fun hmissing hblocks =>
    ay_mide_no_claim_diagnostic_intro hmissing hblocks

theorem ay_mide_digest_mismatch_no_claim
    {digestMismatch publicSatClaim : Prop} :
    digestMismatch ->
    (publicSatClaim -> False) ->
    AyMIDENoClaimDiagnostic digestMismatch publicSatClaim :=
  fun hmismatch hblocks =>
    ay_mide_no_claim_diagnostic_intro hmismatch hblocks

theorem ay_mide_map_mismatch_no_claim
    {mapMismatch publicSatClaim : Prop} :
    mapMismatch ->
    (publicSatClaim -> False) ->
    AyMIDENoClaimDiagnostic mapMismatch publicSatClaim :=
  fun hmismatch hblocks =>
    ay_mide_no_claim_diagnostic_intro hmismatch hblocks

theorem ay_mide_stale_fingerprint_no_claim
    {staleFingerprint publicSatClaim : Prop} :
    staleFingerprint ->
    (publicSatClaim -> False) ->
    AyMIDENoClaimDiagnostic staleFingerprint publicSatClaim :=
  fun hstale hblocks => ay_mide_no_claim_diagnostic_intro hstale hblocks

theorem ay_mide_checker_rejection_no_claim
    {checkerRejection publicSatClaim : Prop} :
    checkerRejection ->
    (publicSatClaim -> False) ->
    AyMIDENoClaimDiagnostic checkerRejection publicSatClaim :=
  fun hreject hblocks =>
    ay_mide_no_claim_diagnostic_intro hreject hblocks

theorem ay_mide_replay_failure_no_claim
    {replayFailure publicSatClaim : Prop} :
    replayFailure ->
    (publicSatClaim -> False) ->
    AyMIDENoClaimDiagnostic replayFailure publicSatClaim :=
  fun hfailure hblocks =>
    ay_mide_no_claim_diagnostic_intro hfailure hblocks

theorem ay_mide_diagnostic_blocks_public_claim
    {diagnostic publicSatClaim : Prop} :
    AyMIDENoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_mide_no_claim_diagnostic_blocks h hclaim

theorem ay_mide_bad_incremental_digest_cannot_bless_sat
    {badEmission publicSatClaim : Prop} :
    AyMIDENoClaimDiagnostic badEmission publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_mide_diagnostic_blocks_public_claim h hclaim
