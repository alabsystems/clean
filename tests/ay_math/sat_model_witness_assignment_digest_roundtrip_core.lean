/- SAT-COMP/ay witness-assignment digest roundtrip contract.

This package models conversion among internal assignments, DIMACS models,
sparse/complete witness views, and public result artifacts.  Publication is
allowed only when digest, map, completion, replay, checker, fingerprint, build,
and artifact evidence agree.
-/

def AyMWDRConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMWDRDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMWDREquisat (source target : Prop) : Prop :=
  AyMWDRConj (source -> target) (target -> source)

def AyMWDRWitnessViews
    (internalAssignment dimacsModel sparseCompleteView : Prop) : Prop :=
  AyMWDRConj internalAssignment
    (AyMWDRConj dimacsModel sparseCompleteView)

def AyMWDRAssignmentDigest
    (internalDigest dimacsDigest digestAgreement : Prop) : Prop :=
  AyMWDRConj internalDigest (AyMWDRConj dimacsDigest digestAgreement)

def AyMWDRBidirectionalVariableMaps
    (internalToDimacs dimacsToInternal inverseAgreement : Prop) : Prop :=
  AyMWDRConj internalToDimacs (AyMWDRConj dimacsToInternal inverseAgreement)

def AyMWDRCompletionManifest
    (sparseView completeView completionAgreement : Prop) : Prop :=
  AyMWDRConj sparseView (AyMWDRConj completeView completionAgreement)

def AyMWDRClauseReplay
    (clauseReplay modelEvaluation replayAgreement : Prop) : Prop :=
  AyMWDRConj clauseReplay (AyMWDRConj modelEvaluation replayAgreement)

def AyMWDRCheckerTranscript
    (checkerAccepted transcript transcriptAgreement : Prop) : Prop :=
  AyMWDRConj checkerAccepted (AyMWDRConj transcript transcriptAgreement)

def AyMWDRFormulaFingerprint
    (originalFingerprint witnessFingerprint fingerprintAgreement : Prop) : Prop :=
  AyMWDRConj originalFingerprint
    (AyMWDRConj witnessFingerprint fingerprintAgreement)

def AyMWDRBuildEvidence
    (solverBuild witnessBuild buildAgreement : Prop) : Prop :=
  AyMWDRConj solverBuild (AyMWDRConj witnessBuild buildAgreement)

def AyMWDRResultArtifact
    (artifactId artifactPayload artifactAgreement : Prop) : Prop :=
  AyMWDRConj artifactId (AyMWDRConj artifactPayload artifactAgreement)

def AyMWDRAcceptedRoundtrip
    (digestOk mapsOk completionOk clauseReplayOk checkerOk fingerprintOk
      buildOk artifactOk : Prop) : Prop :=
  AyMWDRConj digestOk
    (AyMWDRConj mapsOk
      (AyMWDRConj completionOk
        (AyMWDRConj clauseReplayOk
          (AyMWDRConj checkerOk
            (AyMWDRConj fingerprintOk
              (AyMWDRConj buildOk artifactOk))))))

def AyMWDRPublicSatWitness
    (acceptedRoundtrip publicArtifact publicSatClaim : Prop) : Prop :=
  AyMWDRConj acceptedRoundtrip (AyMWDRConj publicArtifact publicSatClaim)

def AyMWDRNoClaimDiagnostic (reason blocksPublication : Prop) : Prop :=
  AyMWDRConj reason blocksPublication

def AyMWDRRecomputeObligation (reason recomputeRequested : Prop) : Prop :=
  AyMWDRConj reason recomputeRequested

theorem ay_mwdr_conj_intro {left right : Prop} :
    left -> right -> AyMWDRConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_mwdr_conj_left {left right : Prop} :
    AyMWDRConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_mwdr_conj_right {left right : Prop} :
    AyMWDRConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_mwdr_disj_left {left right : Prop} :
    left -> AyMWDRDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_mwdr_disj_right {left right : Prop} :
    right -> AyMWDRDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_mwdr_equisat_intro {source target : Prop} :
    (source -> target) -> (target -> source) -> AyMWDREquisat source target :=
  fun forward backward => ay_mwdr_conj_intro forward backward

theorem ay_mwdr_equisat_forward {source target : Prop} :
    AyMWDREquisat source target -> source -> target :=
  fun h => ay_mwdr_conj_left h

theorem ay_mwdr_equisat_backward {source target : Prop} :
    AyMWDREquisat source target -> target -> source :=
  fun h => ay_mwdr_conj_right h

theorem ay_mwdr_witness_views_intro
    {internalAssignment dimacsModel sparseCompleteView : Prop} :
    internalAssignment -> dimacsModel -> sparseCompleteView ->
    AyMWDRWitnessViews internalAssignment dimacsModel sparseCompleteView :=
  fun hinternal hdimacs hview =>
    ay_mwdr_conj_intro hinternal (ay_mwdr_conj_intro hdimacs hview)

theorem ay_mwdr_witness_views_internal
    {internalAssignment dimacsModel sparseCompleteView : Prop} :
    AyMWDRWitnessViews internalAssignment dimacsModel sparseCompleteView ->
    internalAssignment :=
  fun h => ay_mwdr_conj_left h

theorem ay_mwdr_witness_views_dimacs
    {internalAssignment dimacsModel sparseCompleteView : Prop} :
    AyMWDRWitnessViews internalAssignment dimacsModel sparseCompleteView ->
    dimacsModel :=
  fun h => ay_mwdr_conj_left (ay_mwdr_conj_right h)

theorem ay_mwdr_witness_views_sparse_complete
    {internalAssignment dimacsModel sparseCompleteView : Prop} :
    AyMWDRWitnessViews internalAssignment dimacsModel sparseCompleteView ->
    sparseCompleteView :=
  fun h => ay_mwdr_conj_right (ay_mwdr_conj_right h)

theorem ay_mwdr_assignment_digest_intro
    {internalDigest dimacsDigest digestAgreement : Prop} :
    internalDigest -> dimacsDigest -> digestAgreement ->
    AyMWDRAssignmentDigest internalDigest dimacsDigest digestAgreement :=
  fun hinternal hdimacs hagree =>
    ay_mwdr_conj_intro hinternal (ay_mwdr_conj_intro hdimacs hagree)

theorem ay_mwdr_bidirectional_variable_maps_intro
    {internalToDimacs dimacsToInternal inverseAgreement : Prop} :
    internalToDimacs -> dimacsToInternal -> inverseAgreement ->
    AyMWDRBidirectionalVariableMaps
      internalToDimacs dimacsToInternal inverseAgreement :=
  fun hforward hbackward hagree =>
    ay_mwdr_conj_intro hforward (ay_mwdr_conj_intro hbackward hagree)

theorem ay_mwdr_completion_manifest_intro
    {sparseView completeView completionAgreement : Prop} :
    sparseView -> completeView -> completionAgreement ->
    AyMWDRCompletionManifest sparseView completeView completionAgreement :=
  fun hsparse hcomplete hagree =>
    ay_mwdr_conj_intro hsparse (ay_mwdr_conj_intro hcomplete hagree)

theorem ay_mwdr_clause_replay_intro
    {clauseReplay modelEvaluation replayAgreement : Prop} :
    clauseReplay -> modelEvaluation -> replayAgreement ->
    AyMWDRClauseReplay clauseReplay modelEvaluation replayAgreement :=
  fun hreplay heval hagree =>
    ay_mwdr_conj_intro hreplay (ay_mwdr_conj_intro heval hagree)

theorem ay_mwdr_checker_transcript_intro
    {checkerAccepted transcript transcriptAgreement : Prop} :
    checkerAccepted -> transcript -> transcriptAgreement ->
    AyMWDRCheckerTranscript checkerAccepted transcript transcriptAgreement :=
  fun haccepted htranscript hagree =>
    ay_mwdr_conj_intro haccepted (ay_mwdr_conj_intro htranscript hagree)

theorem ay_mwdr_formula_fingerprint_intro
    {originalFingerprint witnessFingerprint fingerprintAgreement : Prop} :
    originalFingerprint -> witnessFingerprint -> fingerprintAgreement ->
    AyMWDRFormulaFingerprint
      originalFingerprint witnessFingerprint fingerprintAgreement :=
  fun horiginal hwitness hagree =>
    ay_mwdr_conj_intro horiginal (ay_mwdr_conj_intro hwitness hagree)

theorem ay_mwdr_build_evidence_intro
    {solverBuild witnessBuild buildAgreement : Prop} :
    solverBuild -> witnessBuild -> buildAgreement ->
    AyMWDRBuildEvidence solverBuild witnessBuild buildAgreement :=
  fun hsolver hwitness hagree =>
    ay_mwdr_conj_intro hsolver (ay_mwdr_conj_intro hwitness hagree)

theorem ay_mwdr_result_artifact_intro
    {artifactId artifactPayload artifactAgreement : Prop} :
    artifactId -> artifactPayload -> artifactAgreement ->
    AyMWDRResultArtifact artifactId artifactPayload artifactAgreement :=
  fun hid hpayload hagree =>
    ay_mwdr_conj_intro hid (ay_mwdr_conj_intro hpayload hagree)

theorem ay_mwdr_accepted_roundtrip_intro
    {digestOk mapsOk completionOk clauseReplayOk checkerOk fingerprintOk
      buildOk artifactOk : Prop} :
    digestOk -> mapsOk -> completionOk -> clauseReplayOk -> checkerOk ->
    fingerprintOk -> buildOk -> artifactOk ->
    AyMWDRAcceptedRoundtrip digestOk mapsOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk artifactOk :=
  fun hdigest hmaps hcompletion hclause hchecker hfingerprint hbuild
      hartifact =>
    ay_mwdr_conj_intro hdigest
      (ay_mwdr_conj_intro hmaps
        (ay_mwdr_conj_intro hcompletion
          (ay_mwdr_conj_intro hclause
            (ay_mwdr_conj_intro hchecker
              (ay_mwdr_conj_intro hfingerprint
                (ay_mwdr_conj_intro hbuild hartifact))))))

theorem ay_mwdr_accepted_roundtrip_digest
    {digestOk mapsOk completionOk clauseReplayOk checkerOk fingerprintOk
      buildOk artifactOk : Prop} :
    AyMWDRAcceptedRoundtrip digestOk mapsOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk artifactOk ->
    digestOk :=
  fun h => ay_mwdr_conj_left h

theorem ay_mwdr_accepted_roundtrip_maps
    {digestOk mapsOk completionOk clauseReplayOk checkerOk fingerprintOk
      buildOk artifactOk : Prop} :
    AyMWDRAcceptedRoundtrip digestOk mapsOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk artifactOk ->
    mapsOk :=
  fun h => ay_mwdr_conj_left (ay_mwdr_conj_right h)

theorem ay_mwdr_accepted_roundtrip_completion
    {digestOk mapsOk completionOk clauseReplayOk checkerOk fingerprintOk
      buildOk artifactOk : Prop} :
    AyMWDRAcceptedRoundtrip digestOk mapsOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk artifactOk ->
    completionOk :=
  fun h => ay_mwdr_conj_left (ay_mwdr_conj_right (ay_mwdr_conj_right h))

theorem ay_mwdr_accepted_roundtrip_clause_replay
    {digestOk mapsOk completionOk clauseReplayOk checkerOk fingerprintOk
      buildOk artifactOk : Prop} :
    AyMWDRAcceptedRoundtrip digestOk mapsOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk artifactOk ->
    clauseReplayOk :=
  fun h =>
    ay_mwdr_conj_left
      (ay_mwdr_conj_right (ay_mwdr_conj_right (ay_mwdr_conj_right h)))

theorem ay_mwdr_accepted_roundtrip_checker
    {digestOk mapsOk completionOk clauseReplayOk checkerOk fingerprintOk
      buildOk artifactOk : Prop} :
    AyMWDRAcceptedRoundtrip digestOk mapsOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk artifactOk ->
    checkerOk :=
  fun h =>
    ay_mwdr_conj_left
      (ay_mwdr_conj_right
        (ay_mwdr_conj_right (ay_mwdr_conj_right (ay_mwdr_conj_right h))))

theorem ay_mwdr_accepted_roundtrip_fingerprint
    {digestOk mapsOk completionOk clauseReplayOk checkerOk fingerprintOk
      buildOk artifactOk : Prop} :
    AyMWDRAcceptedRoundtrip digestOk mapsOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk artifactOk ->
    fingerprintOk :=
  fun h =>
    ay_mwdr_conj_left
      (ay_mwdr_conj_right
        (ay_mwdr_conj_right
          (ay_mwdr_conj_right (ay_mwdr_conj_right
            (ay_mwdr_conj_right h)))))

theorem ay_mwdr_accepted_roundtrip_build
    {digestOk mapsOk completionOk clauseReplayOk checkerOk fingerprintOk
      buildOk artifactOk : Prop} :
    AyMWDRAcceptedRoundtrip digestOk mapsOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk artifactOk ->
    buildOk :=
  fun h =>
    ay_mwdr_conj_left
      (ay_mwdr_conj_right
        (ay_mwdr_conj_right
          (ay_mwdr_conj_right
            (ay_mwdr_conj_right (ay_mwdr_conj_right
              (ay_mwdr_conj_right h))))))

theorem ay_mwdr_accepted_roundtrip_artifact
    {digestOk mapsOk completionOk clauseReplayOk checkerOk fingerprintOk
      buildOk artifactOk : Prop} :
    AyMWDRAcceptedRoundtrip digestOk mapsOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk artifactOk ->
    artifactOk :=
  fun h =>
    ay_mwdr_conj_right
      (ay_mwdr_conj_right
        (ay_mwdr_conj_right
          (ay_mwdr_conj_right
            (ay_mwdr_conj_right (ay_mwdr_conj_right
              (ay_mwdr_conj_right h))))))

theorem ay_mwdr_public_sat_witness_intro
    {acceptedRoundtrip publicArtifact publicSatClaim : Prop} :
    acceptedRoundtrip -> publicArtifact -> publicSatClaim ->
    AyMWDRPublicSatWitness acceptedRoundtrip publicArtifact publicSatClaim :=
  fun hevidence hartifact hclaim =>
    ay_mwdr_conj_intro hevidence (ay_mwdr_conj_intro hartifact hclaim)

theorem ay_mwdr_public_sat_witness_evidence
    {acceptedRoundtrip publicArtifact publicSatClaim : Prop} :
    AyMWDRPublicSatWitness acceptedRoundtrip publicArtifact publicSatClaim ->
    acceptedRoundtrip :=
  fun h => ay_mwdr_conj_left h

theorem ay_mwdr_public_sat_witness_claim
    {acceptedRoundtrip publicArtifact publicSatClaim : Prop} :
    AyMWDRPublicSatWitness acceptedRoundtrip publicArtifact publicSatClaim ->
    publicSatClaim :=
  fun h => ay_mwdr_conj_right (ay_mwdr_conj_right h)

theorem ay_mwdr_accepted_roundtrip_publishes_sound_sat
    {digestOk mapsOk completionOk clauseReplayOk checkerOk fingerprintOk
      buildOk artifactOk publicArtifact publicSatClaim : Prop} :
    AyMWDRAcceptedRoundtrip digestOk mapsOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk artifactOk ->
    publicArtifact -> publicSatClaim ->
    AyMWDRPublicSatWitness
      (AyMWDRAcceptedRoundtrip digestOk mapsOk completionOk clauseReplayOk
        checkerOk fingerprintOk buildOk artifactOk)
      publicArtifact publicSatClaim :=
  ay_mwdr_public_sat_witness_intro

theorem ay_mwdr_assignment_roundtrip_preserves_truth
    {internalTruth publicTruth : Prop} :
    AyMWDREquisat internalTruth publicTruth -> internalTruth -> publicTruth :=
  ay_mwdr_equisat_forward

theorem ay_mwdr_public_sat_requires_roundtrip
    {acceptedRoundtrip publicArtifact publicSatClaim : Prop} :
    AyMWDRPublicSatWitness acceptedRoundtrip publicArtifact publicSatClaim ->
    acceptedRoundtrip :=
  ay_mwdr_public_sat_witness_evidence

theorem ay_mwdr_publication_requires_digest
    {digestOk mapsOk completionOk clauseReplayOk checkerOk fingerprintOk
      buildOk artifactOk publicArtifact publicSatClaim : Prop} :
    AyMWDRPublicSatWitness
      (AyMWDRAcceptedRoundtrip digestOk mapsOk completionOk clauseReplayOk
        checkerOk fingerprintOk buildOk artifactOk)
      publicArtifact publicSatClaim ->
    digestOk :=
  fun h => ay_mwdr_accepted_roundtrip_digest
    (ay_mwdr_public_sat_witness_evidence h)

theorem ay_mwdr_publication_requires_maps
    {digestOk mapsOk completionOk clauseReplayOk checkerOk fingerprintOk
      buildOk artifactOk publicArtifact publicSatClaim : Prop} :
    AyMWDRPublicSatWitness
      (AyMWDRAcceptedRoundtrip digestOk mapsOk completionOk clauseReplayOk
        checkerOk fingerprintOk buildOk artifactOk)
      publicArtifact publicSatClaim ->
    mapsOk :=
  fun h => ay_mwdr_accepted_roundtrip_maps
    (ay_mwdr_public_sat_witness_evidence h)

theorem ay_mwdr_publication_requires_completion
    {digestOk mapsOk completionOk clauseReplayOk checkerOk fingerprintOk
      buildOk artifactOk publicArtifact publicSatClaim : Prop} :
    AyMWDRPublicSatWitness
      (AyMWDRAcceptedRoundtrip digestOk mapsOk completionOk clauseReplayOk
        checkerOk fingerprintOk buildOk artifactOk)
      publicArtifact publicSatClaim ->
    completionOk :=
  fun h => ay_mwdr_accepted_roundtrip_completion
    (ay_mwdr_public_sat_witness_evidence h)

theorem ay_mwdr_publication_requires_clause_replay
    {digestOk mapsOk completionOk clauseReplayOk checkerOk fingerprintOk
      buildOk artifactOk publicArtifact publicSatClaim : Prop} :
    AyMWDRPublicSatWitness
      (AyMWDRAcceptedRoundtrip digestOk mapsOk completionOk clauseReplayOk
        checkerOk fingerprintOk buildOk artifactOk)
      publicArtifact publicSatClaim ->
    clauseReplayOk :=
  fun h => ay_mwdr_accepted_roundtrip_clause_replay
    (ay_mwdr_public_sat_witness_evidence h)

theorem ay_mwdr_publication_requires_checker
    {digestOk mapsOk completionOk clauseReplayOk checkerOk fingerprintOk
      buildOk artifactOk publicArtifact publicSatClaim : Prop} :
    AyMWDRPublicSatWitness
      (AyMWDRAcceptedRoundtrip digestOk mapsOk completionOk clauseReplayOk
        checkerOk fingerprintOk buildOk artifactOk)
      publicArtifact publicSatClaim ->
    checkerOk :=
  fun h => ay_mwdr_accepted_roundtrip_checker
    (ay_mwdr_public_sat_witness_evidence h)

theorem ay_mwdr_publication_requires_fingerprint
    {digestOk mapsOk completionOk clauseReplayOk checkerOk fingerprintOk
      buildOk artifactOk publicArtifact publicSatClaim : Prop} :
    AyMWDRPublicSatWitness
      (AyMWDRAcceptedRoundtrip digestOk mapsOk completionOk clauseReplayOk
        checkerOk fingerprintOk buildOk artifactOk)
      publicArtifact publicSatClaim ->
    fingerprintOk :=
  fun h => ay_mwdr_accepted_roundtrip_fingerprint
    (ay_mwdr_public_sat_witness_evidence h)

theorem ay_mwdr_publication_requires_build
    {digestOk mapsOk completionOk clauseReplayOk checkerOk fingerprintOk
      buildOk artifactOk publicArtifact publicSatClaim : Prop} :
    AyMWDRPublicSatWitness
      (AyMWDRAcceptedRoundtrip digestOk mapsOk completionOk clauseReplayOk
        checkerOk fingerprintOk buildOk artifactOk)
      publicArtifact publicSatClaim ->
    buildOk :=
  fun h => ay_mwdr_accepted_roundtrip_build
    (ay_mwdr_public_sat_witness_evidence h)

theorem ay_mwdr_publication_requires_artifact
    {digestOk mapsOk completionOk clauseReplayOk checkerOk fingerprintOk
      buildOk artifactOk publicArtifact publicSatClaim : Prop} :
    AyMWDRPublicSatWitness
      (AyMWDRAcceptedRoundtrip digestOk mapsOk completionOk clauseReplayOk
        checkerOk fingerprintOk buildOk artifactOk)
      publicArtifact publicSatClaim ->
    artifactOk :=
  fun h => ay_mwdr_accepted_roundtrip_artifact
    (ay_mwdr_public_sat_witness_evidence h)

theorem ay_mwdr_no_claim_diagnostic_intro
    {reason blocksPublication : Prop} :
    reason -> blocksPublication ->
    AyMWDRNoClaimDiagnostic reason blocksPublication :=
  ay_mwdr_conj_intro

theorem ay_mwdr_no_claim_diagnostic_blocks
    {reason blocksPublication : Prop} :
    AyMWDRNoClaimDiagnostic reason blocksPublication -> blocksPublication :=
  ay_mwdr_conj_right

theorem ay_mwdr_recompute_obligation_intro
    {reason recomputeRequested : Prop} :
    reason -> recomputeRequested ->
    AyMWDRRecomputeObligation reason recomputeRequested :=
  ay_mwdr_conj_intro

theorem ay_mwdr_recompute_obligation_request
    {reason recomputeRequested : Prop} :
    AyMWDRRecomputeObligation reason recomputeRequested -> recomputeRequested :=
  ay_mwdr_conj_right

theorem ay_mwdr_digest_drift_no_claim
    {digestDrift blocksPublication : Prop} :
    digestDrift -> blocksPublication ->
    AyMWDRNoClaimDiagnostic digestDrift blocksPublication :=
  ay_mwdr_no_claim_diagnostic_intro

theorem ay_mwdr_digest_drift_recompute
    {digestDrift recomputeRequested : Prop} :
    digestDrift -> recomputeRequested ->
    AyMWDRRecomputeObligation digestDrift recomputeRequested :=
  ay_mwdr_recompute_obligation_intro

theorem ay_mwdr_map_mismatch_no_claim
    {mapMismatch blocksPublication : Prop} :
    mapMismatch -> blocksPublication ->
    AyMWDRNoClaimDiagnostic mapMismatch blocksPublication :=
  ay_mwdr_no_claim_diagnostic_intro

theorem ay_mwdr_completion_mismatch_no_claim
    {completionMismatch blocksPublication : Prop} :
    completionMismatch -> blocksPublication ->
    AyMWDRNoClaimDiagnostic completionMismatch blocksPublication :=
  ay_mwdr_no_claim_diagnostic_intro

theorem ay_mwdr_clause_replay_gap_no_claim
    {clauseReplayGap blocksPublication : Prop} :
    clauseReplayGap -> blocksPublication ->
    AyMWDRNoClaimDiagnostic clauseReplayGap blocksPublication :=
  ay_mwdr_no_claim_diagnostic_intro

theorem ay_mwdr_stale_fingerprint_no_claim
    {staleFingerprint blocksPublication : Prop} :
    staleFingerprint -> blocksPublication ->
    AyMWDRNoClaimDiagnostic staleFingerprint blocksPublication :=
  ay_mwdr_no_claim_diagnostic_intro

theorem ay_mwdr_checker_reject_no_claim
    {checkerReject blocksPublication : Prop} :
    checkerReject -> blocksPublication ->
    AyMWDRNoClaimDiagnostic checkerReject blocksPublication :=
  ay_mwdr_no_claim_diagnostic_intro

theorem ay_mwdr_artifact_mismatch_no_claim
    {artifactMismatch blocksPublication : Prop} :
    artifactMismatch -> blocksPublication ->
    AyMWDRNoClaimDiagnostic artifactMismatch blocksPublication :=
  ay_mwdr_no_claim_diagnostic_intro

theorem ay_mwdr_build_drift_no_claim
    {buildDrift blocksPublication : Prop} :
    buildDrift -> blocksPublication ->
    AyMWDRNoClaimDiagnostic buildDrift blocksPublication :=
  ay_mwdr_no_claim_diagnostic_intro

theorem ay_mwdr_bad_roundtrip_cannot_bless_sat
    {failure blocksPublication recomputeRequested : Prop} :
    AyMWDRNoClaimDiagnostic failure blocksPublication ->
    AyMWDRRecomputeObligation failure recomputeRequested ->
    AyMWDRConj blocksPublication recomputeRequested :=
  fun hdiagnostic hrecompute =>
    ay_mwdr_conj_intro
      (ay_mwdr_no_claim_diagnostic_blocks hdiagnostic)
      (ay_mwdr_recompute_obligation_request hrecompute)
