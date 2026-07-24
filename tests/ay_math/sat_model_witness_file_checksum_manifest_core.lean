-- SAT-COMP/ay witness file checksum manifest soundness skeleton.
-- A public SAT witness file can bless publication only when path, checksum,
-- assignment digest, DIMACS map, replay, transcript, fingerprint, and build
-- evidence all agree.

def AyMWFCConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMWFCDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMWFCEquisat (left right : Prop) : Prop :=
  AyMWFCConj (left -> right) (right -> left)

def AyMWFCWitnessPath
    (declaredPath filePath pathAgreement : Prop) : Prop :=
  AyMWFCConj declaredPath (AyMWFCConj filePath pathAgreement)

def AyMWFCChecksumManifest
    (manifestEntry fileChecksum checksumAgreement : Prop) : Prop :=
  AyMWFCConj manifestEntry (AyMWFCConj fileChecksum checksumAgreement)

def AyMWFCAssignmentDigest
    (manifestDigest assignmentDigest digestAgreement : Prop) : Prop :=
  AyMWFCConj manifestDigest (AyMWFCConj assignmentDigest digestAgreement)

def AyMWFCDimacsVariableMap
    (dimacsMap originalMap mapAgreement : Prop) : Prop :=
  AyMWFCConj dimacsMap (AyMWFCConj originalMap mapAgreement)

def AyMWFCClauseEvaluationReplay
    (clauseReplay witnessEvaluation evaluationAgreement : Prop) : Prop :=
  AyMWFCConj clauseReplay
    (AyMWFCConj witnessEvaluation evaluationAgreement)

def AyMWFCCheckerTranscript
    (checkerAccepted transcript replayAgreement : Prop) : Prop :=
  AyMWFCConj checkerAccepted (AyMWFCConj transcript replayAgreement)

def AyMWFCOriginalFingerprint
    (originalFingerprint witnessFingerprint fingerprintAgreement : Prop) :
    Prop :=
  AyMWFCConj originalFingerprint
    (AyMWFCConj witnessFingerprint fingerprintAgreement)

def AyMWFCBuildEvidence
    (solverBuild witnessBuild buildAgreement : Prop) : Prop :=
  AyMWFCConj solverBuild (AyMWFCConj witnessBuild buildAgreement)

def AyMWFCAcceptedEvidence
    (pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
      fingerprintOk buildOk : Prop) : Prop :=
  AyMWFCConj pathOk
    (AyMWFCConj checksumOk
      (AyMWFCConj digestOk
        (AyMWFCConj mapOk
          (AyMWFCConj clauseReplayOk
            (AyMWFCConj transcriptOk
              (AyMWFCConj fingerprintOk buildOk))))))

def AyMWFCPublicSatWitness
    (acceptedEvidence publicWitnessFile publicSatClaim : Prop) : Prop :=
  AyMWFCConj acceptedEvidence
    (AyMWFCConj publicWitnessFile publicSatClaim)

def AyMWFCNoClaimDiagnostic (diagnostic publicSatClaim : Prop) : Prop :=
  AyMWFCConj diagnostic (publicSatClaim -> False)

def AyMWFCRecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMWFCConj reason recomputeRequest

theorem ay_mwfc_conj_intro {left right : Prop} :
    left -> right -> AyMWFCConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_mwfc_conj_left {left right : Prop} :
    AyMWFCConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_mwfc_conj_right {left right : Prop} :
    AyMWFCConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_mwfc_disj_left {left right : Prop} :
    left -> AyMWFCDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_mwfc_disj_right {left right : Prop} :
    right -> AyMWFCDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_mwfc_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMWFCEquisat left right :=
  fun hf hb => ay_mwfc_conj_intro hf hb

theorem ay_mwfc_equisat_forward {left right : Prop} :
    AyMWFCEquisat left right -> left -> right :=
  fun h => ay_mwfc_conj_left h

theorem ay_mwfc_equisat_backward {left right : Prop} :
    AyMWFCEquisat left right -> right -> left :=
  fun h => ay_mwfc_conj_right h

theorem ay_mwfc_witness_path_intro
    {declaredPath filePath pathAgreement : Prop} :
    declaredPath ->
    filePath ->
    pathAgreement ->
    AyMWFCWitnessPath declaredPath filePath pathAgreement :=
  fun hdeclared hfile hagree =>
    ay_mwfc_conj_intro hdeclared (ay_mwfc_conj_intro hfile hagree)

theorem ay_mwfc_witness_path_declared
    {declaredPath filePath pathAgreement : Prop} :
    AyMWFCWitnessPath declaredPath filePath pathAgreement ->
    declaredPath :=
  fun h => ay_mwfc_conj_left h

theorem ay_mwfc_witness_path_file
    {declaredPath filePath pathAgreement : Prop} :
    AyMWFCWitnessPath declaredPath filePath pathAgreement ->
    filePath :=
  fun h => ay_mwfc_conj_left (ay_mwfc_conj_right h)

theorem ay_mwfc_witness_path_agreement
    {declaredPath filePath pathAgreement : Prop} :
    AyMWFCWitnessPath declaredPath filePath pathAgreement ->
    pathAgreement :=
  fun h => ay_mwfc_conj_right (ay_mwfc_conj_right h)

theorem ay_mwfc_checksum_manifest_intro
    {manifestEntry fileChecksum checksumAgreement : Prop} :
    manifestEntry ->
    fileChecksum ->
    checksumAgreement ->
    AyMWFCChecksumManifest
      manifestEntry fileChecksum checksumAgreement :=
  fun hmanifest hchecksum hagree =>
    ay_mwfc_conj_intro hmanifest
      (ay_mwfc_conj_intro hchecksum hagree)

theorem ay_mwfc_checksum_manifest_entry
    {manifestEntry fileChecksum checksumAgreement : Prop} :
    AyMWFCChecksumManifest manifestEntry fileChecksum checksumAgreement ->
    manifestEntry :=
  fun h => ay_mwfc_conj_left h

theorem ay_mwfc_checksum_manifest_checksum
    {manifestEntry fileChecksum checksumAgreement : Prop} :
    AyMWFCChecksumManifest manifestEntry fileChecksum checksumAgreement ->
    fileChecksum :=
  fun h => ay_mwfc_conj_left (ay_mwfc_conj_right h)

theorem ay_mwfc_checksum_manifest_agreement
    {manifestEntry fileChecksum checksumAgreement : Prop} :
    AyMWFCChecksumManifest manifestEntry fileChecksum checksumAgreement ->
    checksumAgreement :=
  fun h => ay_mwfc_conj_right (ay_mwfc_conj_right h)

theorem ay_mwfc_assignment_digest_intro
    {manifestDigest assignmentDigest digestAgreement : Prop} :
    manifestDigest ->
    assignmentDigest ->
    digestAgreement ->
    AyMWFCAssignmentDigest
      manifestDigest assignmentDigest digestAgreement :=
  fun hmanifest hassignment hagree =>
    ay_mwfc_conj_intro hmanifest
      (ay_mwfc_conj_intro hassignment hagree)

theorem ay_mwfc_assignment_digest_manifest
    {manifestDigest assignmentDigest digestAgreement : Prop} :
    AyMWFCAssignmentDigest
      manifestDigest assignmentDigest digestAgreement ->
    manifestDigest :=
  fun h => ay_mwfc_conj_left h

theorem ay_mwfc_assignment_digest_assignment
    {manifestDigest assignmentDigest digestAgreement : Prop} :
    AyMWFCAssignmentDigest
      manifestDigest assignmentDigest digestAgreement ->
    assignmentDigest :=
  fun h => ay_mwfc_conj_left (ay_mwfc_conj_right h)

theorem ay_mwfc_assignment_digest_agreement
    {manifestDigest assignmentDigest digestAgreement : Prop} :
    AyMWFCAssignmentDigest
      manifestDigest assignmentDigest digestAgreement ->
    digestAgreement :=
  fun h => ay_mwfc_conj_right (ay_mwfc_conj_right h)

theorem ay_mwfc_dimacs_variable_map_intro
    {dimacsMap originalMap mapAgreement : Prop} :
    dimacsMap ->
    originalMap ->
    mapAgreement ->
    AyMWFCDimacsVariableMap dimacsMap originalMap mapAgreement :=
  fun hdimacs horiginal hagree =>
    ay_mwfc_conj_intro hdimacs (ay_mwfc_conj_intro horiginal hagree)

theorem ay_mwfc_dimacs_variable_map_dimacs
    {dimacsMap originalMap mapAgreement : Prop} :
    AyMWFCDimacsVariableMap dimacsMap originalMap mapAgreement ->
    dimacsMap :=
  fun h => ay_mwfc_conj_left h

theorem ay_mwfc_dimacs_variable_map_original
    {dimacsMap originalMap mapAgreement : Prop} :
    AyMWFCDimacsVariableMap dimacsMap originalMap mapAgreement ->
    originalMap :=
  fun h => ay_mwfc_conj_left (ay_mwfc_conj_right h)

theorem ay_mwfc_dimacs_variable_map_agreement
    {dimacsMap originalMap mapAgreement : Prop} :
    AyMWFCDimacsVariableMap dimacsMap originalMap mapAgreement ->
    mapAgreement :=
  fun h => ay_mwfc_conj_right (ay_mwfc_conj_right h)

theorem ay_mwfc_clause_evaluation_replay_intro
    {clauseReplay witnessEvaluation evaluationAgreement : Prop} :
    clauseReplay ->
    witnessEvaluation ->
    evaluationAgreement ->
    AyMWFCClauseEvaluationReplay
      clauseReplay witnessEvaluation evaluationAgreement :=
  fun hreplay heval hagree =>
    ay_mwfc_conj_intro hreplay (ay_mwfc_conj_intro heval hagree)

theorem ay_mwfc_clause_evaluation_replay_trace
    {clauseReplay witnessEvaluation evaluationAgreement : Prop} :
    AyMWFCClauseEvaluationReplay
      clauseReplay witnessEvaluation evaluationAgreement ->
    clauseReplay :=
  fun h => ay_mwfc_conj_left h

theorem ay_mwfc_clause_evaluation_replay_evaluation
    {clauseReplay witnessEvaluation evaluationAgreement : Prop} :
    AyMWFCClauseEvaluationReplay
      clauseReplay witnessEvaluation evaluationAgreement ->
    witnessEvaluation :=
  fun h => ay_mwfc_conj_left (ay_mwfc_conj_right h)

theorem ay_mwfc_clause_evaluation_replay_agreement
    {clauseReplay witnessEvaluation evaluationAgreement : Prop} :
    AyMWFCClauseEvaluationReplay
      clauseReplay witnessEvaluation evaluationAgreement ->
    evaluationAgreement :=
  fun h => ay_mwfc_conj_right (ay_mwfc_conj_right h)

theorem ay_mwfc_checker_transcript_intro
    {checkerAccepted transcript replayAgreement : Prop} :
    checkerAccepted ->
    transcript ->
    replayAgreement ->
    AyMWFCCheckerTranscript checkerAccepted transcript replayAgreement :=
  fun haccepted htranscript hagree =>
    ay_mwfc_conj_intro haccepted
      (ay_mwfc_conj_intro htranscript hagree)

theorem ay_mwfc_checker_transcript_accepted
    {checkerAccepted transcript replayAgreement : Prop} :
    AyMWFCCheckerTranscript checkerAccepted transcript replayAgreement ->
    checkerAccepted :=
  fun h => ay_mwfc_conj_left h

theorem ay_mwfc_checker_transcript_transcript
    {checkerAccepted transcript replayAgreement : Prop} :
    AyMWFCCheckerTranscript checkerAccepted transcript replayAgreement ->
    transcript :=
  fun h => ay_mwfc_conj_left (ay_mwfc_conj_right h)

theorem ay_mwfc_checker_transcript_agreement
    {checkerAccepted transcript replayAgreement : Prop} :
    AyMWFCCheckerTranscript checkerAccepted transcript replayAgreement ->
    replayAgreement :=
  fun h => ay_mwfc_conj_right (ay_mwfc_conj_right h)

theorem ay_mwfc_original_fingerprint_intro
    {originalFingerprint witnessFingerprint fingerprintAgreement : Prop} :
    originalFingerprint ->
    witnessFingerprint ->
    fingerprintAgreement ->
    AyMWFCOriginalFingerprint
      originalFingerprint witnessFingerprint fingerprintAgreement :=
  fun horiginal hwitness hagree =>
    ay_mwfc_conj_intro horiginal
      (ay_mwfc_conj_intro hwitness hagree)

theorem ay_mwfc_original_fingerprint_original
    {originalFingerprint witnessFingerprint fingerprintAgreement : Prop} :
    AyMWFCOriginalFingerprint
      originalFingerprint witnessFingerprint fingerprintAgreement ->
    originalFingerprint :=
  fun h => ay_mwfc_conj_left h

theorem ay_mwfc_original_fingerprint_witness
    {originalFingerprint witnessFingerprint fingerprintAgreement : Prop} :
    AyMWFCOriginalFingerprint
      originalFingerprint witnessFingerprint fingerprintAgreement ->
    witnessFingerprint :=
  fun h => ay_mwfc_conj_left (ay_mwfc_conj_right h)

theorem ay_mwfc_original_fingerprint_agreement
    {originalFingerprint witnessFingerprint fingerprintAgreement : Prop} :
    AyMWFCOriginalFingerprint
      originalFingerprint witnessFingerprint fingerprintAgreement ->
    fingerprintAgreement :=
  fun h => ay_mwfc_conj_right (ay_mwfc_conj_right h)

theorem ay_mwfc_build_evidence_intro
    {solverBuild witnessBuild buildAgreement : Prop} :
    solverBuild ->
    witnessBuild ->
    buildAgreement ->
    AyMWFCBuildEvidence solverBuild witnessBuild buildAgreement :=
  fun hsolver hwitness hagree =>
    ay_mwfc_conj_intro hsolver
      (ay_mwfc_conj_intro hwitness hagree)

theorem ay_mwfc_build_evidence_solver
    {solverBuild witnessBuild buildAgreement : Prop} :
    AyMWFCBuildEvidence solverBuild witnessBuild buildAgreement ->
    solverBuild :=
  fun h => ay_mwfc_conj_left h

theorem ay_mwfc_build_evidence_witness
    {solverBuild witnessBuild buildAgreement : Prop} :
    AyMWFCBuildEvidence solverBuild witnessBuild buildAgreement ->
    witnessBuild :=
  fun h => ay_mwfc_conj_left (ay_mwfc_conj_right h)

theorem ay_mwfc_build_evidence_agreement
    {solverBuild witnessBuild buildAgreement : Prop} :
    AyMWFCBuildEvidence solverBuild witnessBuild buildAgreement ->
    buildAgreement :=
  fun h => ay_mwfc_conj_right (ay_mwfc_conj_right h)

theorem ay_mwfc_accepted_evidence_intro
    {pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
      fingerprintOk buildOk : Prop} :
    pathOk ->
    checksumOk ->
    digestOk ->
    mapOk ->
    clauseReplayOk ->
    transcriptOk ->
    fingerprintOk ->
    buildOk ->
    AyMWFCAcceptedEvidence
      pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
      fingerprintOk buildOk :=
  fun hpath hchecksum hdigest hmap hclause htranscript hfingerprint
      hbuild =>
    ay_mwfc_conj_intro hpath
      (ay_mwfc_conj_intro hchecksum
        (ay_mwfc_conj_intro hdigest
          (ay_mwfc_conj_intro hmap
            (ay_mwfc_conj_intro hclause
              (ay_mwfc_conj_intro htranscript
                (ay_mwfc_conj_intro hfingerprint hbuild))))))

theorem ay_mwfc_accepted_evidence_path
    {pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
      fingerprintOk buildOk : Prop} :
    AyMWFCAcceptedEvidence
      pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
      fingerprintOk buildOk ->
    pathOk :=
  fun h => ay_mwfc_conj_left h

theorem ay_mwfc_accepted_evidence_checksum
    {pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
      fingerprintOk buildOk : Prop} :
    AyMWFCAcceptedEvidence
      pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
      fingerprintOk buildOk ->
    checksumOk :=
  fun h => ay_mwfc_conj_left (ay_mwfc_conj_right h)

theorem ay_mwfc_accepted_evidence_digest
    {pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
      fingerprintOk buildOk : Prop} :
    AyMWFCAcceptedEvidence
      pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
      fingerprintOk buildOk ->
    digestOk :=
  fun h => ay_mwfc_conj_left
    (ay_mwfc_conj_right (ay_mwfc_conj_right h))

theorem ay_mwfc_accepted_evidence_map
    {pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
      fingerprintOk buildOk : Prop} :
    AyMWFCAcceptedEvidence
      pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
      fingerprintOk buildOk ->
    mapOk :=
  fun h => ay_mwfc_conj_left
    (ay_mwfc_conj_right
      (ay_mwfc_conj_right (ay_mwfc_conj_right h)))

theorem ay_mwfc_accepted_evidence_clause_replay
    {pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
      fingerprintOk buildOk : Prop} :
    AyMWFCAcceptedEvidence
      pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
      fingerprintOk buildOk ->
    clauseReplayOk :=
  fun h => ay_mwfc_conj_left
    (ay_mwfc_conj_right
      (ay_mwfc_conj_right
        (ay_mwfc_conj_right (ay_mwfc_conj_right h))))

theorem ay_mwfc_accepted_evidence_transcript
    {pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
      fingerprintOk buildOk : Prop} :
    AyMWFCAcceptedEvidence
      pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
      fingerprintOk buildOk ->
    transcriptOk :=
  fun h => ay_mwfc_conj_left
    (ay_mwfc_conj_right
      (ay_mwfc_conj_right
        (ay_mwfc_conj_right
          (ay_mwfc_conj_right (ay_mwfc_conj_right h)))))

theorem ay_mwfc_accepted_evidence_fingerprint
    {pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
      fingerprintOk buildOk : Prop} :
    AyMWFCAcceptedEvidence
      pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
      fingerprintOk buildOk ->
    fingerprintOk :=
  fun h => ay_mwfc_conj_left
    (ay_mwfc_conj_right
      (ay_mwfc_conj_right
        (ay_mwfc_conj_right
          (ay_mwfc_conj_right
            (ay_mwfc_conj_right (ay_mwfc_conj_right h))))))

theorem ay_mwfc_accepted_evidence_build
    {pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
      fingerprintOk buildOk : Prop} :
    AyMWFCAcceptedEvidence
      pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
      fingerprintOk buildOk ->
    buildOk :=
  fun h => ay_mwfc_conj_right
    (ay_mwfc_conj_right
      (ay_mwfc_conj_right
        (ay_mwfc_conj_right
          (ay_mwfc_conj_right
            (ay_mwfc_conj_right (ay_mwfc_conj_right h))))))

theorem ay_mwfc_public_sat_witness_intro
    {acceptedEvidence publicWitnessFile publicSatClaim : Prop} :
    acceptedEvidence ->
    publicWitnessFile ->
    publicSatClaim ->
    AyMWFCPublicSatWitness
      acceptedEvidence publicWitnessFile publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_mwfc_conj_intro hevidence
      (ay_mwfc_conj_intro hwitness hclaim)

theorem ay_mwfc_public_sat_witness_evidence
    {acceptedEvidence publicWitnessFile publicSatClaim : Prop} :
    AyMWFCPublicSatWitness
      acceptedEvidence publicWitnessFile publicSatClaim ->
    acceptedEvidence :=
  fun h => ay_mwfc_conj_left h

theorem ay_mwfc_public_sat_witness_file
    {acceptedEvidence publicWitnessFile publicSatClaim : Prop} :
    AyMWFCPublicSatWitness
      acceptedEvidence publicWitnessFile publicSatClaim ->
    publicWitnessFile :=
  fun h => ay_mwfc_conj_left (ay_mwfc_conj_right h)

theorem ay_mwfc_public_sat_witness_claim
    {acceptedEvidence publicWitnessFile publicSatClaim : Prop} :
    AyMWFCPublicSatWitness
      acceptedEvidence publicWitnessFile publicSatClaim ->
    publicSatClaim :=
  fun h => ay_mwfc_conj_right (ay_mwfc_conj_right h)

theorem ay_mwfc_accepted_checksum_manifest_publishes_sound_sat
    {pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
      fingerprintOk buildOk publicWitnessFile publicSatClaim : Prop} :
    AyMWFCAcceptedEvidence
      pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
      fingerprintOk buildOk ->
    publicWitnessFile ->
    publicSatClaim ->
    AyMWFCPublicSatWitness
      (AyMWFCAcceptedEvidence
        pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
        fingerprintOk buildOk)
      publicWitnessFile
      publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_mwfc_public_sat_witness_intro hevidence hwitness hclaim

theorem ay_mwfc_public_sat_requires_accepted_evidence
    {acceptedEvidence publicWitnessFile publicSatClaim : Prop} :
    AyMWFCPublicSatWitness
      acceptedEvidence publicWitnessFile publicSatClaim ->
    acceptedEvidence :=
  fun h => ay_mwfc_public_sat_witness_evidence h

theorem ay_mwfc_clause_replay_transports_truth
    {clauseReplay witnessEvaluation formulaTruth : Prop} :
    AyMWFCClauseEvaluationReplay
      clauseReplay witnessEvaluation formulaTruth ->
    formulaTruth :=
  fun h => ay_mwfc_clause_evaluation_replay_agreement h

theorem ay_mwfc_stale_witness_file_cannot_bless_sat
    {staleWitnessFile publicSatClaim : Prop} :
    AyMWFCNoClaimDiagnostic staleWitnessFile publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim =>
    (h (publicSatClaim -> False) (fun _ hblocks => hblocks)) hclaim

theorem ay_mwfc_publication_requires_path
    {pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
      fingerprintOk buildOk publicWitnessFile publicSatClaim : Prop} :
    AyMWFCPublicSatWitness
      (AyMWFCAcceptedEvidence
        pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
        fingerprintOk buildOk)
      publicWitnessFile
      publicSatClaim ->
    pathOk :=
  fun h =>
    ay_mwfc_accepted_evidence_path
      (ay_mwfc_public_sat_witness_evidence h)

theorem ay_mwfc_publication_requires_checksum
    {pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
      fingerprintOk buildOk publicWitnessFile publicSatClaim : Prop} :
    AyMWFCPublicSatWitness
      (AyMWFCAcceptedEvidence
        pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
        fingerprintOk buildOk)
      publicWitnessFile
      publicSatClaim ->
    checksumOk :=
  fun h =>
    ay_mwfc_accepted_evidence_checksum
      (ay_mwfc_public_sat_witness_evidence h)

theorem ay_mwfc_publication_requires_digest
    {pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
      fingerprintOk buildOk publicWitnessFile publicSatClaim : Prop} :
    AyMWFCPublicSatWitness
      (AyMWFCAcceptedEvidence
        pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
        fingerprintOk buildOk)
      publicWitnessFile
      publicSatClaim ->
    digestOk :=
  fun h =>
    ay_mwfc_accepted_evidence_digest
      (ay_mwfc_public_sat_witness_evidence h)

theorem ay_mwfc_publication_requires_map
    {pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
      fingerprintOk buildOk publicWitnessFile publicSatClaim : Prop} :
    AyMWFCPublicSatWitness
      (AyMWFCAcceptedEvidence
        pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
        fingerprintOk buildOk)
      publicWitnessFile
      publicSatClaim ->
    mapOk :=
  fun h =>
    ay_mwfc_accepted_evidence_map
      (ay_mwfc_public_sat_witness_evidence h)

theorem ay_mwfc_publication_requires_clause_replay
    {pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
      fingerprintOk buildOk publicWitnessFile publicSatClaim : Prop} :
    AyMWFCPublicSatWitness
      (AyMWFCAcceptedEvidence
        pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
        fingerprintOk buildOk)
      publicWitnessFile
      publicSatClaim ->
    clauseReplayOk :=
  fun h =>
    ay_mwfc_accepted_evidence_clause_replay
      (ay_mwfc_public_sat_witness_evidence h)

theorem ay_mwfc_publication_requires_transcript
    {pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
      fingerprintOk buildOk publicWitnessFile publicSatClaim : Prop} :
    AyMWFCPublicSatWitness
      (AyMWFCAcceptedEvidence
        pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
        fingerprintOk buildOk)
      publicWitnessFile
      publicSatClaim ->
    transcriptOk :=
  fun h =>
    ay_mwfc_accepted_evidence_transcript
      (ay_mwfc_public_sat_witness_evidence h)

theorem ay_mwfc_publication_requires_fingerprint
    {pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
      fingerprintOk buildOk publicWitnessFile publicSatClaim : Prop} :
    AyMWFCPublicSatWitness
      (AyMWFCAcceptedEvidence
        pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
        fingerprintOk buildOk)
      publicWitnessFile
      publicSatClaim ->
    fingerprintOk :=
  fun h =>
    ay_mwfc_accepted_evidence_fingerprint
      (ay_mwfc_public_sat_witness_evidence h)

theorem ay_mwfc_publication_requires_build
    {pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
      fingerprintOk buildOk publicWitnessFile publicSatClaim : Prop} :
    AyMWFCPublicSatWitness
      (AyMWFCAcceptedEvidence
        pathOk checksumOk digestOk mapOk clauseReplayOk transcriptOk
        fingerprintOk buildOk)
      publicWitnessFile
      publicSatClaim ->
    buildOk :=
  fun h =>
    ay_mwfc_accepted_evidence_build
      (ay_mwfc_public_sat_witness_evidence h)

theorem ay_mwfc_no_claim_diagnostic_intro
    {diagnostic publicSatClaim : Prop} :
    diagnostic ->
    (publicSatClaim -> False) ->
    AyMWFCNoClaimDiagnostic diagnostic publicSatClaim :=
  fun hdiagnostic hblocks =>
    ay_mwfc_conj_intro hdiagnostic hblocks

theorem ay_mwfc_no_claim_diagnostic_reason
    {diagnostic publicSatClaim : Prop} :
    AyMWFCNoClaimDiagnostic diagnostic publicSatClaim -> diagnostic :=
  fun h => ay_mwfc_conj_left h

theorem ay_mwfc_no_claim_diagnostic_blocks
    {diagnostic publicSatClaim : Prop} :
    AyMWFCNoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h => ay_mwfc_conj_right h

theorem ay_mwfc_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMWFCRecomputeObligation reason recomputeRequest :=
  fun hreason hrecompute => ay_mwfc_conj_intro hreason hrecompute

theorem ay_mwfc_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMWFCRecomputeObligation reason recomputeRequest -> reason :=
  fun h => ay_mwfc_conj_left h

theorem ay_mwfc_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMWFCRecomputeObligation reason recomputeRequest -> recomputeRequest :=
  fun h => ay_mwfc_conj_right h

theorem ay_mwfc_stale_witness_file_no_claim
    {staleWitnessFile publicSatClaim : Prop} :
    staleWitnessFile ->
    (publicSatClaim -> False) ->
    AyMWFCNoClaimDiagnostic staleWitnessFile publicSatClaim :=
  fun hstale hblocks => ay_mwfc_no_claim_diagnostic_intro hstale hblocks

theorem ay_mwfc_checksum_mismatch_recompute
    {checksumMismatch recomputeRequest : Prop} :
    checksumMismatch ->
    recomputeRequest ->
    AyMWFCRecomputeObligation checksumMismatch recomputeRequest :=
  fun hmismatch hrecompute =>
    ay_mwfc_recompute_obligation_intro hmismatch hrecompute

theorem ay_mwfc_checksum_mismatch_no_claim
    {checksumMismatch publicSatClaim : Prop} :
    checksumMismatch ->
    (publicSatClaim -> False) ->
    AyMWFCNoClaimDiagnostic checksumMismatch publicSatClaim :=
  fun hmismatch hblocks =>
    ay_mwfc_no_claim_diagnostic_intro hmismatch hblocks

theorem ay_mwfc_path_drift_recompute
    {pathDrift recomputeRequest : Prop} :
    pathDrift ->
    recomputeRequest ->
    AyMWFCRecomputeObligation pathDrift recomputeRequest :=
  fun hdrift hrecompute =>
    ay_mwfc_recompute_obligation_intro hdrift hrecompute

theorem ay_mwfc_path_drift_no_claim
    {pathDrift publicSatClaim : Prop} :
    pathDrift ->
    (publicSatClaim -> False) ->
    AyMWFCNoClaimDiagnostic pathDrift publicSatClaim :=
  fun hdrift hblocks => ay_mwfc_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mwfc_map_mismatch_no_claim
    {mapMismatch publicSatClaim : Prop} :
    mapMismatch ->
    (publicSatClaim -> False) ->
    AyMWFCNoClaimDiagnostic mapMismatch publicSatClaim :=
  fun hmismatch hblocks =>
    ay_mwfc_no_claim_diagnostic_intro hmismatch hblocks

theorem ay_mwfc_checker_rejection_no_claim
    {checkerRejection publicSatClaim : Prop} :
    checkerRejection ->
    (publicSatClaim -> False) ->
    AyMWFCNoClaimDiagnostic checkerRejection publicSatClaim :=
  fun hreject hblocks =>
    ay_mwfc_no_claim_diagnostic_intro hreject hblocks

theorem ay_mwfc_fingerprint_drift_no_claim
    {fingerprintDrift publicSatClaim : Prop} :
    fingerprintDrift ->
    (publicSatClaim -> False) ->
    AyMWFCNoClaimDiagnostic fingerprintDrift publicSatClaim :=
  fun hdrift hblocks => ay_mwfc_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mwfc_digest_mismatch_no_claim
    {digestMismatch publicSatClaim : Prop} :
    digestMismatch ->
    (publicSatClaim -> False) ->
    AyMWFCNoClaimDiagnostic digestMismatch publicSatClaim :=
  fun hmismatch hblocks =>
    ay_mwfc_no_claim_diagnostic_intro hmismatch hblocks

theorem ay_mwfc_diagnostic_blocks_public_claim
    {diagnostic publicSatClaim : Prop} :
    AyMWFCNoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_mwfc_no_claim_diagnostic_blocks h hclaim

theorem ay_mwfc_bad_checksum_manifest_cannot_bless_sat
    {badManifest publicSatClaim : Prop} :
    AyMWFCNoClaimDiagnostic badManifest publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_mwfc_diagnostic_blocks_public_claim h hclaim
