/- SAT-COMP/ay solution-certificate index guard contract.

This self-contained package models the guard for indexing SAT solution
certificates.  A public SAT result may be blessed only when the certificate
index, witness digest, artifact digest, maps, completion, replay, checker,
fingerprint, build, and archive evidence all agree.
-/

def AyMSCIConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMSCIDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMSCIEquisat (source target : Prop) : Prop :=
  AyMSCIConj (source -> target) (target -> source)

def AyMSCICertificateIndex
    (indexEntry certificateEntry indexAgreement : Prop) : Prop :=
  AyMSCIConj indexEntry (AyMSCIConj certificateEntry indexAgreement)

def AyMSCIWitnessAssignmentDigest
    (witnessEntry assignmentDigest digestAgreement : Prop) : Prop :=
  AyMSCIConj witnessEntry (AyMSCIConj assignmentDigest digestAgreement)

def AyMSCIResultArtifactDigest
    (artifactEntry artifactDigest artifactAgreement : Prop) : Prop :=
  AyMSCIConj artifactEntry (AyMSCIConj artifactDigest artifactAgreement)

def AyMSCIDimacsMaps
    (solverToDimacs dimacsToSolver mapAgreement : Prop) : Prop :=
  AyMSCIConj solverToDimacs (AyMSCIConj dimacsToSolver mapAgreement)

def AyMSCICompletionManifest
    (partialWitness completedWitness completionAgreement : Prop) : Prop :=
  AyMSCIConj partialWitness
    (AyMSCIConj completedWitness completionAgreement)

def AyMSCIClauseReplay
    (clauseReplay witnessEvaluation replayAgreement : Prop) : Prop :=
  AyMSCIConj clauseReplay (AyMSCIConj witnessEvaluation replayAgreement)

def AyMSCICheckerTranscript
    (checkerAccepted transcript transcriptAgreement : Prop) : Prop :=
  AyMSCIConj checkerAccepted (AyMSCIConj transcript transcriptAgreement)

def AyMSCIFormulaFingerprint
    (originalFingerprint certificateFingerprint fingerprintAgreement : Prop) :
    Prop :=
  AyMSCIConj originalFingerprint
    (AyMSCIConj certificateFingerprint fingerprintAgreement)

def AyMSCIBuildEvidence
    (solverBuild certificateBuild buildAgreement : Prop) : Prop :=
  AyMSCIConj solverBuild (AyMSCIConj certificateBuild buildAgreement)

def AyMSCIArchiveManifest
    (archiveEntry archiveDigest archiveAgreement : Prop) : Prop :=
  AyMSCIConj archiveEntry (AyMSCIConj archiveDigest archiveAgreement)

def AyMSCIAcceptedIndex
    (indexOk witnessDigestOk artifactDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk : Prop) : Prop :=
  AyMSCIConj indexOk
    (AyMSCIConj witnessDigestOk
      (AyMSCIConj artifactDigestOk
        (AyMSCIConj mapsOk
          (AyMSCIConj completionOk
            (AyMSCIConj clauseReplayOk
              (AyMSCIConj checkerOk
                (AyMSCIConj fingerprintOk
                  (AyMSCIConj buildOk archiveOk))))))))

def AyMSCIPublicSatPublication
    (acceptedIndex certificateWitness publicSatClaim : Prop) : Prop :=
  AyMSCIConj acceptedIndex (AyMSCIConj certificateWitness publicSatClaim)

def AyMSCINoClaimDiagnostic (reason blocksPublication : Prop) : Prop :=
  AyMSCIConj reason blocksPublication

def AyMSCIRecomputeObligation (reason recomputeRequested : Prop) : Prop :=
  AyMSCIConj reason recomputeRequested

theorem ay_msci_conj_intro {left right : Prop} :
    left -> right -> AyMSCIConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_msci_conj_left {left right : Prop} :
    AyMSCIConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_msci_conj_right {left right : Prop} :
    AyMSCIConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_msci_disj_left {left right : Prop} :
    left -> AyMSCIDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_msci_disj_right {left right : Prop} :
    right -> AyMSCIDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_msci_equisat_intro {source target : Prop} :
    (source -> target) -> (target -> source) -> AyMSCIEquisat source target :=
  fun forward backward => ay_msci_conj_intro forward backward

theorem ay_msci_equisat_forward {source target : Prop} :
    AyMSCIEquisat source target -> source -> target :=
  fun h => ay_msci_conj_left h

theorem ay_msci_equisat_backward {source target : Prop} :
    AyMSCIEquisat source target -> target -> source :=
  fun h => ay_msci_conj_right h

theorem ay_msci_certificate_index_intro
    {indexEntry certificateEntry indexAgreement : Prop} :
    indexEntry -> certificateEntry -> indexAgreement ->
    AyMSCICertificateIndex indexEntry certificateEntry indexAgreement :=
  fun hindex hentry hagree =>
    ay_msci_conj_intro hindex (ay_msci_conj_intro hentry hagree)

theorem ay_msci_certificate_index_entry
    {indexEntry certificateEntry indexAgreement : Prop} :
    AyMSCICertificateIndex indexEntry certificateEntry indexAgreement ->
    indexEntry :=
  fun h => ay_msci_conj_left h

theorem ay_msci_certificate_index_certificate
    {indexEntry certificateEntry indexAgreement : Prop} :
    AyMSCICertificateIndex indexEntry certificateEntry indexAgreement ->
    certificateEntry :=
  fun h => ay_msci_conj_left (ay_msci_conj_right h)

theorem ay_msci_certificate_index_agreement
    {indexEntry certificateEntry indexAgreement : Prop} :
    AyMSCICertificateIndex indexEntry certificateEntry indexAgreement ->
    indexAgreement :=
  fun h => ay_msci_conj_right (ay_msci_conj_right h)

theorem ay_msci_witness_assignment_digest_intro
    {witnessEntry assignmentDigest digestAgreement : Prop} :
    witnessEntry -> assignmentDigest -> digestAgreement ->
    AyMSCIWitnessAssignmentDigest
      witnessEntry assignmentDigest digestAgreement :=
  fun hwitness hdigest hagree =>
    ay_msci_conj_intro hwitness (ay_msci_conj_intro hdigest hagree)

theorem ay_msci_result_artifact_digest_intro
    {artifactEntry artifactDigest artifactAgreement : Prop} :
    artifactEntry -> artifactDigest -> artifactAgreement ->
    AyMSCIResultArtifactDigest artifactEntry artifactDigest artifactAgreement :=
  fun hartifact hdigest hagree =>
    ay_msci_conj_intro hartifact (ay_msci_conj_intro hdigest hagree)

theorem ay_msci_dimacs_maps_intro
    {solverToDimacs dimacsToSolver mapAgreement : Prop} :
    solverToDimacs -> dimacsToSolver -> mapAgreement ->
    AyMSCIDimacsMaps solverToDimacs dimacsToSolver mapAgreement :=
  fun hforward hbackward hagree =>
    ay_msci_conj_intro hforward (ay_msci_conj_intro hbackward hagree)

theorem ay_msci_completion_manifest_intro
    {partialWitness completedWitness completionAgreement : Prop} :
    partialWitness -> completedWitness -> completionAgreement ->
    AyMSCICompletionManifest
      partialWitness completedWitness completionAgreement :=
  fun hpartial hcompleted hagree =>
    ay_msci_conj_intro hpartial (ay_msci_conj_intro hcompleted hagree)

theorem ay_msci_clause_replay_intro
    {clauseReplay witnessEvaluation replayAgreement : Prop} :
    clauseReplay -> witnessEvaluation -> replayAgreement ->
    AyMSCIClauseReplay clauseReplay witnessEvaluation replayAgreement :=
  fun hreplay heval hagree =>
    ay_msci_conj_intro hreplay (ay_msci_conj_intro heval hagree)

theorem ay_msci_checker_transcript_intro
    {checkerAccepted transcript transcriptAgreement : Prop} :
    checkerAccepted -> transcript -> transcriptAgreement ->
    AyMSCICheckerTranscript checkerAccepted transcript transcriptAgreement :=
  fun haccepted htranscript hagree =>
    ay_msci_conj_intro haccepted (ay_msci_conj_intro htranscript hagree)

theorem ay_msci_formula_fingerprint_intro
    {originalFingerprint certificateFingerprint fingerprintAgreement : Prop} :
    originalFingerprint -> certificateFingerprint -> fingerprintAgreement ->
    AyMSCIFormulaFingerprint
      originalFingerprint certificateFingerprint fingerprintAgreement :=
  fun horiginal hcertificate hagree =>
    ay_msci_conj_intro horiginal (ay_msci_conj_intro hcertificate hagree)

theorem ay_msci_build_evidence_intro
    {solverBuild certificateBuild buildAgreement : Prop} :
    solverBuild -> certificateBuild -> buildAgreement ->
    AyMSCIBuildEvidence solverBuild certificateBuild buildAgreement :=
  fun hsolver hcertificate hagree =>
    ay_msci_conj_intro hsolver (ay_msci_conj_intro hcertificate hagree)

theorem ay_msci_archive_manifest_intro
    {archiveEntry archiveDigest archiveAgreement : Prop} :
    archiveEntry -> archiveDigest -> archiveAgreement ->
    AyMSCIArchiveManifest archiveEntry archiveDigest archiveAgreement :=
  fun hentry hdigest hagree =>
    ay_msci_conj_intro hentry (ay_msci_conj_intro hdigest hagree)

theorem ay_msci_accepted_index_intro
    {indexOk witnessDigestOk artifactDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk : Prop} :
    indexOk -> witnessDigestOk -> artifactDigestOk -> mapsOk ->
    completionOk -> clauseReplayOk -> checkerOk -> fingerprintOk -> buildOk ->
    archiveOk ->
    AyMSCIAcceptedIndex indexOk witnessDigestOk artifactDigestOk mapsOk
      completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk :=
  fun hindex hwitness hartifact hmaps hcompletion hclause hchecker
      hfingerprint hbuild harchive =>
    ay_msci_conj_intro hindex
      (ay_msci_conj_intro hwitness
        (ay_msci_conj_intro hartifact
          (ay_msci_conj_intro hmaps
            (ay_msci_conj_intro hcompletion
              (ay_msci_conj_intro hclause
                (ay_msci_conj_intro hchecker
                  (ay_msci_conj_intro hfingerprint
                    (ay_msci_conj_intro hbuild harchive))))))))

theorem ay_msci_accepted_index_index
    {indexOk witnessDigestOk artifactDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk : Prop} :
    AyMSCIAcceptedIndex indexOk witnessDigestOk artifactDigestOk mapsOk
      completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    indexOk :=
  fun h => ay_msci_conj_left h

theorem ay_msci_accepted_index_witness_digest
    {indexOk witnessDigestOk artifactDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk : Prop} :
    AyMSCIAcceptedIndex indexOk witnessDigestOk artifactDigestOk mapsOk
      completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    witnessDigestOk :=
  fun h => ay_msci_conj_left (ay_msci_conj_right h)

theorem ay_msci_accepted_index_artifact_digest
    {indexOk witnessDigestOk artifactDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk : Prop} :
    AyMSCIAcceptedIndex indexOk witnessDigestOk artifactDigestOk mapsOk
      completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    artifactDigestOk :=
  fun h => ay_msci_conj_left (ay_msci_conj_right (ay_msci_conj_right h))

theorem ay_msci_accepted_index_maps
    {indexOk witnessDigestOk artifactDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk : Prop} :
    AyMSCIAcceptedIndex indexOk witnessDigestOk artifactDigestOk mapsOk
      completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    mapsOk :=
  fun h =>
    ay_msci_conj_left
      (ay_msci_conj_right (ay_msci_conj_right (ay_msci_conj_right h)))

theorem ay_msci_accepted_index_completion
    {indexOk witnessDigestOk artifactDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk : Prop} :
    AyMSCIAcceptedIndex indexOk witnessDigestOk artifactDigestOk mapsOk
      completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    completionOk :=
  fun h =>
    ay_msci_conj_left
      (ay_msci_conj_right
        (ay_msci_conj_right (ay_msci_conj_right (ay_msci_conj_right h))))

theorem ay_msci_accepted_index_clause_replay
    {indexOk witnessDigestOk artifactDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk : Prop} :
    AyMSCIAcceptedIndex indexOk witnessDigestOk artifactDigestOk mapsOk
      completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    clauseReplayOk :=
  fun h =>
    ay_msci_conj_left
      (ay_msci_conj_right
        (ay_msci_conj_right
          (ay_msci_conj_right (ay_msci_conj_right (ay_msci_conj_right h)))))

theorem ay_msci_accepted_index_checker
    {indexOk witnessDigestOk artifactDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk : Prop} :
    AyMSCIAcceptedIndex indexOk witnessDigestOk artifactDigestOk mapsOk
      completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    checkerOk :=
  fun h =>
    ay_msci_conj_left
      (ay_msci_conj_right
        (ay_msci_conj_right
          (ay_msci_conj_right
            (ay_msci_conj_right (ay_msci_conj_right
              (ay_msci_conj_right h))))))

theorem ay_msci_accepted_index_fingerprint
    {indexOk witnessDigestOk artifactDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk : Prop} :
    AyMSCIAcceptedIndex indexOk witnessDigestOk artifactDigestOk mapsOk
      completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    fingerprintOk :=
  fun h =>
    ay_msci_conj_left
      (ay_msci_conj_right
        (ay_msci_conj_right
          (ay_msci_conj_right
            (ay_msci_conj_right
              (ay_msci_conj_right (ay_msci_conj_right
                (ay_msci_conj_right h)))))))

theorem ay_msci_accepted_index_build
    {indexOk witnessDigestOk artifactDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk : Prop} :
    AyMSCIAcceptedIndex indexOk witnessDigestOk artifactDigestOk mapsOk
      completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    buildOk :=
  fun h =>
    ay_msci_conj_left
      (ay_msci_conj_right
        (ay_msci_conj_right
          (ay_msci_conj_right
            (ay_msci_conj_right
              (ay_msci_conj_right
                (ay_msci_conj_right (ay_msci_conj_right
                  (ay_msci_conj_right h))))))))

theorem ay_msci_accepted_index_archive
    {indexOk witnessDigestOk artifactDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk : Prop} :
    AyMSCIAcceptedIndex indexOk witnessDigestOk artifactDigestOk mapsOk
      completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    archiveOk :=
  fun h =>
    ay_msci_conj_right
      (ay_msci_conj_right
        (ay_msci_conj_right
          (ay_msci_conj_right
            (ay_msci_conj_right
              (ay_msci_conj_right
                (ay_msci_conj_right (ay_msci_conj_right
                  (ay_msci_conj_right h))))))))

theorem ay_msci_public_sat_publication_intro
    {acceptedIndex certificateWitness publicSatClaim : Prop} :
    acceptedIndex -> certificateWitness -> publicSatClaim ->
    AyMSCIPublicSatPublication acceptedIndex certificateWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_msci_conj_intro hevidence (ay_msci_conj_intro hwitness hclaim)

theorem ay_msci_public_sat_publication_evidence
    {acceptedIndex certificateWitness publicSatClaim : Prop} :
    AyMSCIPublicSatPublication acceptedIndex certificateWitness publicSatClaim ->
    acceptedIndex :=
  fun h => ay_msci_conj_left h

theorem ay_msci_public_sat_publication_claim
    {acceptedIndex certificateWitness publicSatClaim : Prop} :
    AyMSCIPublicSatPublication acceptedIndex certificateWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_msci_conj_right (ay_msci_conj_right h)

theorem ay_msci_accepted_certificate_index_publishes_sound_sat
    {indexOk witnessDigestOk artifactDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk
      certificateWitness publicSatClaim : Prop} :
    AyMSCIAcceptedIndex indexOk witnessDigestOk artifactDigestOk mapsOk
      completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    certificateWitness -> publicSatClaim ->
    AyMSCIPublicSatPublication
      (AyMSCIAcceptedIndex indexOk witnessDigestOk artifactDigestOk mapsOk
        completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      certificateWitness publicSatClaim :=
  ay_msci_public_sat_publication_intro

theorem ay_msci_certificate_index_preserves_truth
    {indexedTruth publicTruth : Prop} :
    AyMSCIEquisat indexedTruth publicTruth -> indexedTruth -> publicTruth :=
  ay_msci_equisat_forward

theorem ay_msci_public_sat_requires_accepted_index
    {acceptedIndex certificateWitness publicSatClaim : Prop} :
    AyMSCIPublicSatPublication acceptedIndex certificateWitness publicSatClaim ->
    acceptedIndex :=
  ay_msci_public_sat_publication_evidence

theorem ay_msci_publication_requires_index
    {indexOk witnessDigestOk artifactDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk
      certificateWitness publicSatClaim : Prop} :
    AyMSCIPublicSatPublication
      (AyMSCIAcceptedIndex indexOk witnessDigestOk artifactDigestOk mapsOk
        completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      certificateWitness publicSatClaim ->
    indexOk :=
  fun h => ay_msci_accepted_index_index
    (ay_msci_public_sat_publication_evidence h)

theorem ay_msci_publication_requires_witness_digest
    {indexOk witnessDigestOk artifactDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk
      certificateWitness publicSatClaim : Prop} :
    AyMSCIPublicSatPublication
      (AyMSCIAcceptedIndex indexOk witnessDigestOk artifactDigestOk mapsOk
        completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      certificateWitness publicSatClaim ->
    witnessDigestOk :=
  fun h => ay_msci_accepted_index_witness_digest
    (ay_msci_public_sat_publication_evidence h)

theorem ay_msci_publication_requires_artifact_digest
    {indexOk witnessDigestOk artifactDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk
      certificateWitness publicSatClaim : Prop} :
    AyMSCIPublicSatPublication
      (AyMSCIAcceptedIndex indexOk witnessDigestOk artifactDigestOk mapsOk
        completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      certificateWitness publicSatClaim ->
    artifactDigestOk :=
  fun h => ay_msci_accepted_index_artifact_digest
    (ay_msci_public_sat_publication_evidence h)

theorem ay_msci_publication_requires_maps
    {indexOk witnessDigestOk artifactDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk
      certificateWitness publicSatClaim : Prop} :
    AyMSCIPublicSatPublication
      (AyMSCIAcceptedIndex indexOk witnessDigestOk artifactDigestOk mapsOk
        completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      certificateWitness publicSatClaim ->
    mapsOk :=
  fun h => ay_msci_accepted_index_maps
    (ay_msci_public_sat_publication_evidence h)

theorem ay_msci_publication_requires_completion
    {indexOk witnessDigestOk artifactDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk
      certificateWitness publicSatClaim : Prop} :
    AyMSCIPublicSatPublication
      (AyMSCIAcceptedIndex indexOk witnessDigestOk artifactDigestOk mapsOk
        completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      certificateWitness publicSatClaim ->
    completionOk :=
  fun h => ay_msci_accepted_index_completion
    (ay_msci_public_sat_publication_evidence h)

theorem ay_msci_publication_requires_clause_replay
    {indexOk witnessDigestOk artifactDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk
      certificateWitness publicSatClaim : Prop} :
    AyMSCIPublicSatPublication
      (AyMSCIAcceptedIndex indexOk witnessDigestOk artifactDigestOk mapsOk
        completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      certificateWitness publicSatClaim ->
    clauseReplayOk :=
  fun h => ay_msci_accepted_index_clause_replay
    (ay_msci_public_sat_publication_evidence h)

theorem ay_msci_publication_requires_checker
    {indexOk witnessDigestOk artifactDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk
      certificateWitness publicSatClaim : Prop} :
    AyMSCIPublicSatPublication
      (AyMSCIAcceptedIndex indexOk witnessDigestOk artifactDigestOk mapsOk
        completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      certificateWitness publicSatClaim ->
    checkerOk :=
  fun h => ay_msci_accepted_index_checker
    (ay_msci_public_sat_publication_evidence h)

theorem ay_msci_publication_requires_fingerprint
    {indexOk witnessDigestOk artifactDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk
      certificateWitness publicSatClaim : Prop} :
    AyMSCIPublicSatPublication
      (AyMSCIAcceptedIndex indexOk witnessDigestOk artifactDigestOk mapsOk
        completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      certificateWitness publicSatClaim ->
    fingerprintOk :=
  fun h => ay_msci_accepted_index_fingerprint
    (ay_msci_public_sat_publication_evidence h)

theorem ay_msci_publication_requires_build
    {indexOk witnessDigestOk artifactDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk
      certificateWitness publicSatClaim : Prop} :
    AyMSCIPublicSatPublication
      (AyMSCIAcceptedIndex indexOk witnessDigestOk artifactDigestOk mapsOk
        completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      certificateWitness publicSatClaim ->
    buildOk :=
  fun h => ay_msci_accepted_index_build
    (ay_msci_public_sat_publication_evidence h)

theorem ay_msci_publication_requires_archive
    {indexOk witnessDigestOk artifactDigestOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk archiveOk
      certificateWitness publicSatClaim : Prop} :
    AyMSCIPublicSatPublication
      (AyMSCIAcceptedIndex indexOk witnessDigestOk artifactDigestOk mapsOk
        completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      certificateWitness publicSatClaim ->
    archiveOk :=
  fun h => ay_msci_accepted_index_archive
    (ay_msci_public_sat_publication_evidence h)

theorem ay_msci_no_claim_diagnostic_intro
    {reason blocksPublication : Prop} :
    reason -> blocksPublication ->
    AyMSCINoClaimDiagnostic reason blocksPublication :=
  ay_msci_conj_intro

theorem ay_msci_no_claim_diagnostic_blocks
    {reason blocksPublication : Prop} :
    AyMSCINoClaimDiagnostic reason blocksPublication -> blocksPublication :=
  ay_msci_conj_right

theorem ay_msci_recompute_obligation_intro
    {reason recomputeRequested : Prop} :
    reason -> recomputeRequested ->
    AyMSCIRecomputeObligation reason recomputeRequested :=
  ay_msci_conj_intro

theorem ay_msci_recompute_obligation_request
    {reason recomputeRequested : Prop} :
    AyMSCIRecomputeObligation reason recomputeRequested -> recomputeRequested :=
  ay_msci_conj_right

theorem ay_msci_index_drift_no_claim
    {indexDrift blocksPublication : Prop} :
    indexDrift -> blocksPublication ->
    AyMSCINoClaimDiagnostic indexDrift blocksPublication :=
  ay_msci_no_claim_diagnostic_intro

theorem ay_msci_index_drift_recompute
    {indexDrift recomputeRequested : Prop} :
    indexDrift -> recomputeRequested ->
    AyMSCIRecomputeObligation indexDrift recomputeRequested :=
  ay_msci_recompute_obligation_intro

theorem ay_msci_missing_certificate_entry_no_claim
    {missingCertificateEntry blocksPublication : Prop} :
    missingCertificateEntry -> blocksPublication ->
    AyMSCINoClaimDiagnostic missingCertificateEntry blocksPublication :=
  ay_msci_no_claim_diagnostic_intro

theorem ay_msci_witness_digest_drift_no_claim
    {witnessDigestDrift blocksPublication : Prop} :
    witnessDigestDrift -> blocksPublication ->
    AyMSCINoClaimDiagnostic witnessDigestDrift blocksPublication :=
  ay_msci_no_claim_diagnostic_intro

theorem ay_msci_artifact_digest_drift_no_claim
    {artifactDigestDrift blocksPublication : Prop} :
    artifactDigestDrift -> blocksPublication ->
    AyMSCINoClaimDiagnostic artifactDigestDrift blocksPublication :=
  ay_msci_no_claim_diagnostic_intro

theorem ay_msci_map_mismatch_no_claim
    {mapMismatch blocksPublication : Prop} :
    mapMismatch -> blocksPublication ->
    AyMSCINoClaimDiagnostic mapMismatch blocksPublication :=
  ay_msci_no_claim_diagnostic_intro

theorem ay_msci_completion_mismatch_no_claim
    {completionMismatch blocksPublication : Prop} :
    completionMismatch -> blocksPublication ->
    AyMSCINoClaimDiagnostic completionMismatch blocksPublication :=
  ay_msci_no_claim_diagnostic_intro

theorem ay_msci_clause_replay_gap_no_claim
    {clauseReplayGap blocksPublication : Prop} :
    clauseReplayGap -> blocksPublication ->
    AyMSCINoClaimDiagnostic clauseReplayGap blocksPublication :=
  ay_msci_no_claim_diagnostic_intro

theorem ay_msci_stale_fingerprint_no_claim
    {staleFingerprint blocksPublication : Prop} :
    staleFingerprint -> blocksPublication ->
    AyMSCINoClaimDiagnostic staleFingerprint blocksPublication :=
  ay_msci_no_claim_diagnostic_intro

theorem ay_msci_checker_reject_no_claim
    {checkerReject blocksPublication : Prop} :
    checkerReject -> blocksPublication ->
    AyMSCINoClaimDiagnostic checkerReject blocksPublication :=
  ay_msci_no_claim_diagnostic_intro

theorem ay_msci_build_drift_no_claim
    {buildDrift blocksPublication : Prop} :
    buildDrift -> blocksPublication ->
    AyMSCINoClaimDiagnostic buildDrift blocksPublication :=
  ay_msci_no_claim_diagnostic_intro

theorem ay_msci_archive_mismatch_no_claim
    {archiveMismatch blocksPublication : Prop} :
    archiveMismatch -> blocksPublication ->
    AyMSCINoClaimDiagnostic archiveMismatch blocksPublication :=
  ay_msci_no_claim_diagnostic_intro

theorem ay_msci_bad_index_guard_cannot_bless_sat
    {failure blocksPublication recomputeRequested : Prop} :
    AyMSCINoClaimDiagnostic failure blocksPublication ->
    AyMSCIRecomputeObligation failure recomputeRequested ->
    AyMSCIConj blocksPublication recomputeRequested :=
  fun hdiagnostic hrecompute =>
    ay_msci_conj_intro
      (ay_msci_no_claim_diagnostic_blocks hdiagnostic)
      (ay_msci_recompute_obligation_request hrecompute)
