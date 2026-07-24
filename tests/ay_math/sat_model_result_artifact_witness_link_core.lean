/- SAT-COMP/ay result-artifact to witness link contract.

This self-contained package models when a public SAT result artifact may be
linked to a validated model witness.  Every publication theorem is gated by
artifact digest, witness digest, maps, completion, replay, checker,
fingerprint, build, and archive evidence.
-/

def AyMRAWConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMRAWDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMRAWEquisat (source target : Prop) : Prop :=
  AyMRAWConj (source -> target) (target -> source)

def AyMRAWResultArtifactDigest
    (artifactId artifactDigest artifactAgreement : Prop) : Prop :=
  AyMRAWConj artifactId (AyMRAWConj artifactDigest artifactAgreement)

def AyMRAWWitnessAssignmentDigest
    (witnessArtifact assignmentDigest digestAgreement : Prop) : Prop :=
  AyMRAWConj witnessArtifact (AyMRAWConj assignmentDigest digestAgreement)

def AyMRAWDimacsMaps
    (solverToDimacs dimacsToSolver mapAgreement : Prop) : Prop :=
  AyMRAWConj solverToDimacs (AyMRAWConj dimacsToSolver mapAgreement)

def AyMRAWCompletionManifest
    (partialWitness completedWitness completionAgreement : Prop) : Prop :=
  AyMRAWConj partialWitness
    (AyMRAWConj completedWitness completionAgreement)

def AyMRAWClauseReplay
    (clauseReplay witnessEvaluation replayAgreement : Prop) : Prop :=
  AyMRAWConj clauseReplay (AyMRAWConj witnessEvaluation replayAgreement)

def AyMRAWCheckerTranscript
    (checkerAccepted transcript transcriptAgreement : Prop) : Prop :=
  AyMRAWConj checkerAccepted (AyMRAWConj transcript transcriptAgreement)

def AyMRAWFormulaFingerprint
    (originalFingerprint artifactFingerprint fingerprintAgreement : Prop) : Prop :=
  AyMRAWConj originalFingerprint
    (AyMRAWConj artifactFingerprint fingerprintAgreement)

def AyMRAWBuildEvidence
    (solverBuild artifactBuild buildAgreement : Prop) : Prop :=
  AyMRAWConj solverBuild (AyMRAWConj artifactBuild buildAgreement)

def AyMRAWArchiveManifest
    (archiveEntry archiveDigest archiveAgreement : Prop) : Prop :=
  AyMRAWConj archiveEntry (AyMRAWConj archiveDigest archiveAgreement)

def AyMRAWAcceptedLink
    (artifactOk witnessDigestOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop) : Prop :=
  AyMRAWConj artifactOk
    (AyMRAWConj witnessDigestOk
      (AyMRAWConj mapsOk
        (AyMRAWConj completionOk
          (AyMRAWConj clauseReplayOk
            (AyMRAWConj checkerOk
              (AyMRAWConj fingerprintOk
                (AyMRAWConj buildOk archiveOk)))))))

def AyMRAWPublicSatPublication
    (acceptedLink linkedWitness publicSatClaim : Prop) : Prop :=
  AyMRAWConj acceptedLink (AyMRAWConj linkedWitness publicSatClaim)

def AyMRAWNoClaimDiagnostic (reason blocksPublication : Prop) : Prop :=
  AyMRAWConj reason blocksPublication

def AyMRAWRecomputeObligation (reason recomputeRequested : Prop) : Prop :=
  AyMRAWConj reason recomputeRequested

theorem ay_mraw_conj_intro {left right : Prop} :
    left -> right -> AyMRAWConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_mraw_conj_left {left right : Prop} :
    AyMRAWConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_mraw_conj_right {left right : Prop} :
    AyMRAWConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_mraw_disj_left {left right : Prop} :
    left -> AyMRAWDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_mraw_disj_right {left right : Prop} :
    right -> AyMRAWDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_mraw_equisat_intro {source target : Prop} :
    (source -> target) -> (target -> source) -> AyMRAWEquisat source target :=
  fun forward backward => ay_mraw_conj_intro forward backward

theorem ay_mraw_equisat_forward {source target : Prop} :
    AyMRAWEquisat source target -> source -> target :=
  fun h => ay_mraw_conj_left h

theorem ay_mraw_equisat_backward {source target : Prop} :
    AyMRAWEquisat source target -> target -> source :=
  fun h => ay_mraw_conj_right h

theorem ay_mraw_result_artifact_digest_intro
    {artifactId artifactDigest artifactAgreement : Prop} :
    artifactId -> artifactDigest -> artifactAgreement ->
    AyMRAWResultArtifactDigest artifactId artifactDigest artifactAgreement :=
  fun hid hdigest hagree =>
    ay_mraw_conj_intro hid (ay_mraw_conj_intro hdigest hagree)

theorem ay_mraw_result_artifact_digest_id
    {artifactId artifactDigest artifactAgreement : Prop} :
    AyMRAWResultArtifactDigest artifactId artifactDigest artifactAgreement ->
    artifactId :=
  fun h => ay_mraw_conj_left h

theorem ay_mraw_result_artifact_digest_value
    {artifactId artifactDigest artifactAgreement : Prop} :
    AyMRAWResultArtifactDigest artifactId artifactDigest artifactAgreement ->
    artifactDigest :=
  fun h => ay_mraw_conj_left (ay_mraw_conj_right h)

theorem ay_mraw_result_artifact_digest_agreement
    {artifactId artifactDigest artifactAgreement : Prop} :
    AyMRAWResultArtifactDigest artifactId artifactDigest artifactAgreement ->
    artifactAgreement :=
  fun h => ay_mraw_conj_right (ay_mraw_conj_right h)

theorem ay_mraw_witness_assignment_digest_intro
    {witnessArtifact assignmentDigest digestAgreement : Prop} :
    witnessArtifact -> assignmentDigest -> digestAgreement ->
    AyMRAWWitnessAssignmentDigest
      witnessArtifact assignmentDigest digestAgreement :=
  fun hwitness hdigest hagree =>
    ay_mraw_conj_intro hwitness (ay_mraw_conj_intro hdigest hagree)

theorem ay_mraw_dimacs_maps_intro
    {solverToDimacs dimacsToSolver mapAgreement : Prop} :
    solverToDimacs -> dimacsToSolver -> mapAgreement ->
    AyMRAWDimacsMaps solverToDimacs dimacsToSolver mapAgreement :=
  fun hforward hbackward hagree =>
    ay_mraw_conj_intro hforward (ay_mraw_conj_intro hbackward hagree)

theorem ay_mraw_completion_manifest_intro
    {partialWitness completedWitness completionAgreement : Prop} :
    partialWitness -> completedWitness -> completionAgreement ->
    AyMRAWCompletionManifest
      partialWitness completedWitness completionAgreement :=
  fun hpartial hcompleted hagree =>
    ay_mraw_conj_intro hpartial (ay_mraw_conj_intro hcompleted hagree)

theorem ay_mraw_clause_replay_intro
    {clauseReplay witnessEvaluation replayAgreement : Prop} :
    clauseReplay -> witnessEvaluation -> replayAgreement ->
    AyMRAWClauseReplay clauseReplay witnessEvaluation replayAgreement :=
  fun hreplay heval hagree =>
    ay_mraw_conj_intro hreplay (ay_mraw_conj_intro heval hagree)

theorem ay_mraw_checker_transcript_intro
    {checkerAccepted transcript transcriptAgreement : Prop} :
    checkerAccepted -> transcript -> transcriptAgreement ->
    AyMRAWCheckerTranscript checkerAccepted transcript transcriptAgreement :=
  fun haccepted htranscript hagree =>
    ay_mraw_conj_intro haccepted (ay_mraw_conj_intro htranscript hagree)

theorem ay_mraw_formula_fingerprint_intro
    {originalFingerprint artifactFingerprint fingerprintAgreement : Prop} :
    originalFingerprint -> artifactFingerprint -> fingerprintAgreement ->
    AyMRAWFormulaFingerprint
      originalFingerprint artifactFingerprint fingerprintAgreement :=
  fun horiginal hartifact hagree =>
    ay_mraw_conj_intro horiginal (ay_mraw_conj_intro hartifact hagree)

theorem ay_mraw_build_evidence_intro
    {solverBuild artifactBuild buildAgreement : Prop} :
    solverBuild -> artifactBuild -> buildAgreement ->
    AyMRAWBuildEvidence solverBuild artifactBuild buildAgreement :=
  fun hsolver hartifact hagree =>
    ay_mraw_conj_intro hsolver (ay_mraw_conj_intro hartifact hagree)

theorem ay_mraw_archive_manifest_intro
    {archiveEntry archiveDigest archiveAgreement : Prop} :
    archiveEntry -> archiveDigest -> archiveAgreement ->
    AyMRAWArchiveManifest archiveEntry archiveDigest archiveAgreement :=
  fun hentry hdigest hagree =>
    ay_mraw_conj_intro hentry (ay_mraw_conj_intro hdigest hagree)

theorem ay_mraw_accepted_link_intro
    {artifactOk witnessDigestOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    artifactOk -> witnessDigestOk -> mapsOk -> completionOk ->
    clauseReplayOk -> checkerOk -> fingerprintOk -> buildOk -> archiveOk ->
    AyMRAWAcceptedLink artifactOk witnessDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk :=
  fun hartifact hwitness hmaps hcompletion hclause hchecker hfingerprint
      hbuild harchive =>
    ay_mraw_conj_intro hartifact
      (ay_mraw_conj_intro hwitness
        (ay_mraw_conj_intro hmaps
          (ay_mraw_conj_intro hcompletion
            (ay_mraw_conj_intro hclause
              (ay_mraw_conj_intro hchecker
                (ay_mraw_conj_intro hfingerprint
                  (ay_mraw_conj_intro hbuild harchive)))))))

theorem ay_mraw_accepted_link_artifact
    {artifactOk witnessDigestOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyMRAWAcceptedLink artifactOk witnessDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    artifactOk :=
  fun h => ay_mraw_conj_left h

theorem ay_mraw_accepted_link_witness_digest
    {artifactOk witnessDigestOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyMRAWAcceptedLink artifactOk witnessDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    witnessDigestOk :=
  fun h => ay_mraw_conj_left (ay_mraw_conj_right h)

theorem ay_mraw_accepted_link_maps
    {artifactOk witnessDigestOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyMRAWAcceptedLink artifactOk witnessDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    mapsOk :=
  fun h => ay_mraw_conj_left (ay_mraw_conj_right (ay_mraw_conj_right h))

theorem ay_mraw_accepted_link_completion
    {artifactOk witnessDigestOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyMRAWAcceptedLink artifactOk witnessDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    completionOk :=
  fun h =>
    ay_mraw_conj_left
      (ay_mraw_conj_right (ay_mraw_conj_right (ay_mraw_conj_right h)))

theorem ay_mraw_accepted_link_clause_replay
    {artifactOk witnessDigestOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyMRAWAcceptedLink artifactOk witnessDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    clauseReplayOk :=
  fun h =>
    ay_mraw_conj_left
      (ay_mraw_conj_right
        (ay_mraw_conj_right (ay_mraw_conj_right (ay_mraw_conj_right h))))

theorem ay_mraw_accepted_link_checker
    {artifactOk witnessDigestOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyMRAWAcceptedLink artifactOk witnessDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    checkerOk :=
  fun h =>
    ay_mraw_conj_left
      (ay_mraw_conj_right
        (ay_mraw_conj_right
          (ay_mraw_conj_right (ay_mraw_conj_right (ay_mraw_conj_right h)))))

theorem ay_mraw_accepted_link_fingerprint
    {artifactOk witnessDigestOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyMRAWAcceptedLink artifactOk witnessDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    fingerprintOk :=
  fun h =>
    ay_mraw_conj_left
      (ay_mraw_conj_right
        (ay_mraw_conj_right
          (ay_mraw_conj_right
            (ay_mraw_conj_right (ay_mraw_conj_right
              (ay_mraw_conj_right h))))))

theorem ay_mraw_accepted_link_build
    {artifactOk witnessDigestOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyMRAWAcceptedLink artifactOk witnessDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    buildOk :=
  fun h =>
    ay_mraw_conj_left
      (ay_mraw_conj_right
        (ay_mraw_conj_right
          (ay_mraw_conj_right
            (ay_mraw_conj_right
              (ay_mraw_conj_right (ay_mraw_conj_right
                (ay_mraw_conj_right h)))))))

theorem ay_mraw_accepted_link_archive
    {artifactOk witnessDigestOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyMRAWAcceptedLink artifactOk witnessDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    archiveOk :=
  fun h =>
    ay_mraw_conj_right
      (ay_mraw_conj_right
        (ay_mraw_conj_right
          (ay_mraw_conj_right
            (ay_mraw_conj_right
              (ay_mraw_conj_right (ay_mraw_conj_right
                (ay_mraw_conj_right h)))))))

theorem ay_mraw_public_sat_publication_intro
    {acceptedLink linkedWitness publicSatClaim : Prop} :
    acceptedLink -> linkedWitness -> publicSatClaim ->
    AyMRAWPublicSatPublication acceptedLink linkedWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_mraw_conj_intro hevidence (ay_mraw_conj_intro hwitness hclaim)

theorem ay_mraw_public_sat_publication_evidence
    {acceptedLink linkedWitness publicSatClaim : Prop} :
    AyMRAWPublicSatPublication acceptedLink linkedWitness publicSatClaim ->
    acceptedLink :=
  fun h => ay_mraw_conj_left h

theorem ay_mraw_public_sat_publication_claim
    {acceptedLink linkedWitness publicSatClaim : Prop} :
    AyMRAWPublicSatPublication acceptedLink linkedWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_mraw_conj_right (ay_mraw_conj_right h)

theorem ay_mraw_accepted_link_publishes_sound_sat
    {artifactOk witnessDigestOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk archiveOk linkedWitness publicSatClaim : Prop} :
    AyMRAWAcceptedLink artifactOk witnessDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    linkedWitness -> publicSatClaim ->
    AyMRAWPublicSatPublication
      (AyMRAWAcceptedLink artifactOk witnessDigestOk mapsOk completionOk
        clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      linkedWitness publicSatClaim :=
  ay_mraw_public_sat_publication_intro

theorem ay_mraw_artifact_witness_link_preserves_truth
    {witnessTruth artifactTruth : Prop} :
    AyMRAWEquisat witnessTruth artifactTruth -> witnessTruth -> artifactTruth :=
  ay_mraw_equisat_forward

theorem ay_mraw_public_sat_requires_accepted_link
    {acceptedLink linkedWitness publicSatClaim : Prop} :
    AyMRAWPublicSatPublication acceptedLink linkedWitness publicSatClaim ->
    acceptedLink :=
  ay_mraw_public_sat_publication_evidence

theorem ay_mraw_publication_requires_artifact
    {artifactOk witnessDigestOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk archiveOk linkedWitness publicSatClaim : Prop} :
    AyMRAWPublicSatPublication
      (AyMRAWAcceptedLink artifactOk witnessDigestOk mapsOk completionOk
        clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      linkedWitness publicSatClaim ->
    artifactOk :=
  fun h => ay_mraw_accepted_link_artifact
    (ay_mraw_public_sat_publication_evidence h)

theorem ay_mraw_publication_requires_witness_digest
    {artifactOk witnessDigestOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk archiveOk linkedWitness publicSatClaim : Prop} :
    AyMRAWPublicSatPublication
      (AyMRAWAcceptedLink artifactOk witnessDigestOk mapsOk completionOk
        clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      linkedWitness publicSatClaim ->
    witnessDigestOk :=
  fun h => ay_mraw_accepted_link_witness_digest
    (ay_mraw_public_sat_publication_evidence h)

theorem ay_mraw_publication_requires_maps
    {artifactOk witnessDigestOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk archiveOk linkedWitness publicSatClaim : Prop} :
    AyMRAWPublicSatPublication
      (AyMRAWAcceptedLink artifactOk witnessDigestOk mapsOk completionOk
        clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      linkedWitness publicSatClaim ->
    mapsOk :=
  fun h => ay_mraw_accepted_link_maps
    (ay_mraw_public_sat_publication_evidence h)

theorem ay_mraw_publication_requires_completion
    {artifactOk witnessDigestOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk archiveOk linkedWitness publicSatClaim : Prop} :
    AyMRAWPublicSatPublication
      (AyMRAWAcceptedLink artifactOk witnessDigestOk mapsOk completionOk
        clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      linkedWitness publicSatClaim ->
    completionOk :=
  fun h => ay_mraw_accepted_link_completion
    (ay_mraw_public_sat_publication_evidence h)

theorem ay_mraw_publication_requires_clause_replay
    {artifactOk witnessDigestOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk archiveOk linkedWitness publicSatClaim : Prop} :
    AyMRAWPublicSatPublication
      (AyMRAWAcceptedLink artifactOk witnessDigestOk mapsOk completionOk
        clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      linkedWitness publicSatClaim ->
    clauseReplayOk :=
  fun h => ay_mraw_accepted_link_clause_replay
    (ay_mraw_public_sat_publication_evidence h)

theorem ay_mraw_publication_requires_checker
    {artifactOk witnessDigestOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk archiveOk linkedWitness publicSatClaim : Prop} :
    AyMRAWPublicSatPublication
      (AyMRAWAcceptedLink artifactOk witnessDigestOk mapsOk completionOk
        clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      linkedWitness publicSatClaim ->
    checkerOk :=
  fun h => ay_mraw_accepted_link_checker
    (ay_mraw_public_sat_publication_evidence h)

theorem ay_mraw_publication_requires_fingerprint
    {artifactOk witnessDigestOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk archiveOk linkedWitness publicSatClaim : Prop} :
    AyMRAWPublicSatPublication
      (AyMRAWAcceptedLink artifactOk witnessDigestOk mapsOk completionOk
        clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      linkedWitness publicSatClaim ->
    fingerprintOk :=
  fun h => ay_mraw_accepted_link_fingerprint
    (ay_mraw_public_sat_publication_evidence h)

theorem ay_mraw_publication_requires_build
    {artifactOk witnessDigestOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk archiveOk linkedWitness publicSatClaim : Prop} :
    AyMRAWPublicSatPublication
      (AyMRAWAcceptedLink artifactOk witnessDigestOk mapsOk completionOk
        clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      linkedWitness publicSatClaim ->
    buildOk :=
  fun h => ay_mraw_accepted_link_build
    (ay_mraw_public_sat_publication_evidence h)

theorem ay_mraw_publication_requires_archive
    {artifactOk witnessDigestOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk archiveOk linkedWitness publicSatClaim : Prop} :
    AyMRAWPublicSatPublication
      (AyMRAWAcceptedLink artifactOk witnessDigestOk mapsOk completionOk
        clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      linkedWitness publicSatClaim ->
    archiveOk :=
  fun h => ay_mraw_accepted_link_archive
    (ay_mraw_public_sat_publication_evidence h)

theorem ay_mraw_no_claim_diagnostic_intro
    {reason blocksPublication : Prop} :
    reason -> blocksPublication ->
    AyMRAWNoClaimDiagnostic reason blocksPublication :=
  ay_mraw_conj_intro

theorem ay_mraw_no_claim_diagnostic_blocks
    {reason blocksPublication : Prop} :
    AyMRAWNoClaimDiagnostic reason blocksPublication -> blocksPublication :=
  ay_mraw_conj_right

theorem ay_mraw_recompute_obligation_intro
    {reason recomputeRequested : Prop} :
    reason -> recomputeRequested ->
    AyMRAWRecomputeObligation reason recomputeRequested :=
  ay_mraw_conj_intro

theorem ay_mraw_recompute_obligation_request
    {reason recomputeRequested : Prop} :
    AyMRAWRecomputeObligation reason recomputeRequested -> recomputeRequested :=
  ay_mraw_conj_right

theorem ay_mraw_artifact_drift_no_claim
    {artifactDrift blocksPublication : Prop} :
    artifactDrift -> blocksPublication ->
    AyMRAWNoClaimDiagnostic artifactDrift blocksPublication :=
  ay_mraw_no_claim_diagnostic_intro

theorem ay_mraw_artifact_drift_recompute
    {artifactDrift recomputeRequested : Prop} :
    artifactDrift -> recomputeRequested ->
    AyMRAWRecomputeObligation artifactDrift recomputeRequested :=
  ay_mraw_recompute_obligation_intro

theorem ay_mraw_witness_digest_drift_no_claim
    {witnessDigestDrift blocksPublication : Prop} :
    witnessDigestDrift -> blocksPublication ->
    AyMRAWNoClaimDiagnostic witnessDigestDrift blocksPublication :=
  ay_mraw_no_claim_diagnostic_intro

theorem ay_mraw_map_mismatch_no_claim
    {mapMismatch blocksPublication : Prop} :
    mapMismatch -> blocksPublication ->
    AyMRAWNoClaimDiagnostic mapMismatch blocksPublication :=
  ay_mraw_no_claim_diagnostic_intro

theorem ay_mraw_completion_mismatch_no_claim
    {completionMismatch blocksPublication : Prop} :
    completionMismatch -> blocksPublication ->
    AyMRAWNoClaimDiagnostic completionMismatch blocksPublication :=
  ay_mraw_no_claim_diagnostic_intro

theorem ay_mraw_clause_replay_gap_no_claim
    {clauseReplayGap blocksPublication : Prop} :
    clauseReplayGap -> blocksPublication ->
    AyMRAWNoClaimDiagnostic clauseReplayGap blocksPublication :=
  ay_mraw_no_claim_diagnostic_intro

theorem ay_mraw_stale_fingerprint_no_claim
    {staleFingerprint blocksPublication : Prop} :
    staleFingerprint -> blocksPublication ->
    AyMRAWNoClaimDiagnostic staleFingerprint blocksPublication :=
  ay_mraw_no_claim_diagnostic_intro

theorem ay_mraw_checker_reject_no_claim
    {checkerReject blocksPublication : Prop} :
    checkerReject -> blocksPublication ->
    AyMRAWNoClaimDiagnostic checkerReject blocksPublication :=
  ay_mraw_no_claim_diagnostic_intro

theorem ay_mraw_build_drift_no_claim
    {buildDrift blocksPublication : Prop} :
    buildDrift -> blocksPublication ->
    AyMRAWNoClaimDiagnostic buildDrift blocksPublication :=
  ay_mraw_no_claim_diagnostic_intro

theorem ay_mraw_archive_mismatch_no_claim
    {archiveMismatch blocksPublication : Prop} :
    archiveMismatch -> blocksPublication ->
    AyMRAWNoClaimDiagnostic archiveMismatch blocksPublication :=
  ay_mraw_no_claim_diagnostic_intro

theorem ay_mraw_bad_link_cannot_bless_sat
    {failure blocksPublication recomputeRequested : Prop} :
    AyMRAWNoClaimDiagnostic failure blocksPublication ->
    AyMRAWRecomputeObligation failure recomputeRequested ->
    AyMRAWConj blocksPublication recomputeRequested :=
  fun hdiagnostic hrecompute =>
    ay_mraw_conj_intro
      (ay_mraw_no_claim_diagnostic_blocks hdiagnostic)
      (ay_mraw_recompute_obligation_request hrecompute)
