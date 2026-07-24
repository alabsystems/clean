/- SAT-COMP/ay model-line parser manifest contract.

This self-contained package models parsing SAT-COMP model lines into
assignments.  Public SAT publication is allowed only when parser manifests,
tokenization digest, maps, assignment digest, completion, replay, checker,
fingerprint, build, and archive evidence all agree.
-/

def AyMMLPConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMMLPDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMMLPEquisat (source target : Prop) : Prop :=
  AyMMLPConj (source -> target) (target -> source)

def AyMMLPModelLineManifest
    (lineManifest parserVersion parserAgreement : Prop) : Prop :=
  AyMMLPConj lineManifest (AyMMLPConj parserVersion parserAgreement)

def AyMMLPTokenizationDigest
    (tokenStream tokenDigest tokenAgreement : Prop) : Prop :=
  AyMMLPConj tokenStream (AyMMLPConj tokenDigest tokenAgreement)

def AyMMLPDimacsMaps
    (parsedToDimacs dimacsToParsed mapAgreement : Prop) : Prop :=
  AyMMLPConj parsedToDimacs (AyMMLPConj dimacsToParsed mapAgreement)

def AyMMLPAssignmentDigest
    (parsedAssignment assignmentDigest digestAgreement : Prop) : Prop :=
  AyMMLPConj parsedAssignment (AyMMLPConj assignmentDigest digestAgreement)

def AyMMLPCompletionManifest
    (parsedWitness completedWitness completionAgreement : Prop) : Prop :=
  AyMMLPConj parsedWitness
    (AyMMLPConj completedWitness completionAgreement)

def AyMMLPClauseReplay
    (clauseReplay witnessEvaluation replayAgreement : Prop) : Prop :=
  AyMMLPConj clauseReplay (AyMMLPConj witnessEvaluation replayAgreement)

def AyMMLPCheckerTranscript
    (checkerAccepted transcript transcriptAgreement : Prop) : Prop :=
  AyMMLPConj checkerAccepted (AyMMLPConj transcript transcriptAgreement)

def AyMMLPFormulaFingerprint
    (originalFingerprint parserFingerprint fingerprintAgreement : Prop) : Prop :=
  AyMMLPConj originalFingerprint
    (AyMMLPConj parserFingerprint fingerprintAgreement)

def AyMMLPBuildEvidence
    (solverBuild parserBuild buildAgreement : Prop) : Prop :=
  AyMMLPConj solverBuild (AyMMLPConj parserBuild buildAgreement)

def AyMMLPArchiveManifest
    (archiveEntry archiveDigest archiveAgreement : Prop) : Prop :=
  AyMMLPConj archiveEntry (AyMMLPConj archiveDigest archiveAgreement)

def AyMMLPAcceptedParse
    (manifestOk tokenOk mapsOk assignmentDigestOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk archiveOk : Prop) : Prop :=
  AyMMLPConj manifestOk
    (AyMMLPConj tokenOk
      (AyMMLPConj mapsOk
        (AyMMLPConj assignmentDigestOk
          (AyMMLPConj completionOk
            (AyMMLPConj clauseReplayOk
              (AyMMLPConj checkerOk
                (AyMMLPConj fingerprintOk
                  (AyMMLPConj buildOk archiveOk))))))))

def AyMMLPPublicSatWitness
    (acceptedParse parsedWitness publicSatClaim : Prop) : Prop :=
  AyMMLPConj acceptedParse (AyMMLPConj parsedWitness publicSatClaim)

def AyMMLPNoClaimDiagnostic (reason blocksPublication : Prop) : Prop :=
  AyMMLPConj reason blocksPublication

def AyMMLPRecomputeObligation (reason recomputeRequested : Prop) : Prop :=
  AyMMLPConj reason recomputeRequested

theorem ay_mmlp_conj_intro {left right : Prop} :
    left -> right -> AyMMLPConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_mmlp_conj_left {left right : Prop} :
    AyMMLPConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_mmlp_conj_right {left right : Prop} :
    AyMMLPConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_mmlp_disj_left {left right : Prop} :
    left -> AyMMLPDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_mmlp_disj_right {left right : Prop} :
    right -> AyMMLPDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_mmlp_equisat_intro {source target : Prop} :
    (source -> target) -> (target -> source) -> AyMMLPEquisat source target :=
  fun forward backward => ay_mmlp_conj_intro forward backward

theorem ay_mmlp_equisat_forward {source target : Prop} :
    AyMMLPEquisat source target -> source -> target :=
  fun h => ay_mmlp_conj_left h

theorem ay_mmlp_equisat_backward {source target : Prop} :
    AyMMLPEquisat source target -> target -> source :=
  fun h => ay_mmlp_conj_right h

theorem ay_mmlp_model_line_manifest_intro
    {lineManifest parserVersion parserAgreement : Prop} :
    lineManifest -> parserVersion -> parserAgreement ->
    AyMMLPModelLineManifest lineManifest parserVersion parserAgreement :=
  fun hline hversion hagree =>
    ay_mmlp_conj_intro hline (ay_mmlp_conj_intro hversion hagree)

theorem ay_mmlp_model_line_manifest_line
    {lineManifest parserVersion parserAgreement : Prop} :
    AyMMLPModelLineManifest lineManifest parserVersion parserAgreement ->
    lineManifest :=
  fun h => ay_mmlp_conj_left h

theorem ay_mmlp_model_line_manifest_version
    {lineManifest parserVersion parserAgreement : Prop} :
    AyMMLPModelLineManifest lineManifest parserVersion parserAgreement ->
    parserVersion :=
  fun h => ay_mmlp_conj_left (ay_mmlp_conj_right h)

theorem ay_mmlp_model_line_manifest_agreement
    {lineManifest parserVersion parserAgreement : Prop} :
    AyMMLPModelLineManifest lineManifest parserVersion parserAgreement ->
    parserAgreement :=
  fun h => ay_mmlp_conj_right (ay_mmlp_conj_right h)

theorem ay_mmlp_tokenization_digest_intro
    {tokenStream tokenDigest tokenAgreement : Prop} :
    tokenStream -> tokenDigest -> tokenAgreement ->
    AyMMLPTokenizationDigest tokenStream tokenDigest tokenAgreement :=
  fun hstream hdigest hagree =>
    ay_mmlp_conj_intro hstream (ay_mmlp_conj_intro hdigest hagree)

theorem ay_mmlp_dimacs_maps_intro
    {parsedToDimacs dimacsToParsed mapAgreement : Prop} :
    parsedToDimacs -> dimacsToParsed -> mapAgreement ->
    AyMMLPDimacsMaps parsedToDimacs dimacsToParsed mapAgreement :=
  fun hforward hbackward hagree =>
    ay_mmlp_conj_intro hforward (ay_mmlp_conj_intro hbackward hagree)

theorem ay_mmlp_assignment_digest_intro
    {parsedAssignment assignmentDigest digestAgreement : Prop} :
    parsedAssignment -> assignmentDigest -> digestAgreement ->
    AyMMLPAssignmentDigest
      parsedAssignment assignmentDigest digestAgreement :=
  fun hparsed hdigest hagree =>
    ay_mmlp_conj_intro hparsed (ay_mmlp_conj_intro hdigest hagree)

theorem ay_mmlp_completion_manifest_intro
    {parsedWitness completedWitness completionAgreement : Prop} :
    parsedWitness -> completedWitness -> completionAgreement ->
    AyMMLPCompletionManifest
      parsedWitness completedWitness completionAgreement :=
  fun hparsed hcompleted hagree =>
    ay_mmlp_conj_intro hparsed (ay_mmlp_conj_intro hcompleted hagree)

theorem ay_mmlp_clause_replay_intro
    {clauseReplay witnessEvaluation replayAgreement : Prop} :
    clauseReplay -> witnessEvaluation -> replayAgreement ->
    AyMMLPClauseReplay clauseReplay witnessEvaluation replayAgreement :=
  fun hreplay heval hagree =>
    ay_mmlp_conj_intro hreplay (ay_mmlp_conj_intro heval hagree)

theorem ay_mmlp_checker_transcript_intro
    {checkerAccepted transcript transcriptAgreement : Prop} :
    checkerAccepted -> transcript -> transcriptAgreement ->
    AyMMLPCheckerTranscript checkerAccepted transcript transcriptAgreement :=
  fun haccepted htranscript hagree =>
    ay_mmlp_conj_intro haccepted (ay_mmlp_conj_intro htranscript hagree)

theorem ay_mmlp_formula_fingerprint_intro
    {originalFingerprint parserFingerprint fingerprintAgreement : Prop} :
    originalFingerprint -> parserFingerprint -> fingerprintAgreement ->
    AyMMLPFormulaFingerprint
      originalFingerprint parserFingerprint fingerprintAgreement :=
  fun horiginal hparser hagree =>
    ay_mmlp_conj_intro horiginal (ay_mmlp_conj_intro hparser hagree)

theorem ay_mmlp_build_evidence_intro
    {solverBuild parserBuild buildAgreement : Prop} :
    solverBuild -> parserBuild -> buildAgreement ->
    AyMMLPBuildEvidence solverBuild parserBuild buildAgreement :=
  fun hsolver hparser hagree =>
    ay_mmlp_conj_intro hsolver (ay_mmlp_conj_intro hparser hagree)

theorem ay_mmlp_archive_manifest_intro
    {archiveEntry archiveDigest archiveAgreement : Prop} :
    archiveEntry -> archiveDigest -> archiveAgreement ->
    AyMMLPArchiveManifest archiveEntry archiveDigest archiveAgreement :=
  fun hentry hdigest hagree =>
    ay_mmlp_conj_intro hentry (ay_mmlp_conj_intro hdigest hagree)

theorem ay_mmlp_accepted_parse_intro
    {manifestOk tokenOk mapsOk assignmentDigestOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk archiveOk : Prop} :
    manifestOk -> tokenOk -> mapsOk -> assignmentDigestOk -> completionOk ->
    clauseReplayOk -> checkerOk -> fingerprintOk -> buildOk -> archiveOk ->
    AyMMLPAcceptedParse manifestOk tokenOk mapsOk assignmentDigestOk
      completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk :=
  fun hmanifest htoken hmaps hdigest hcompletion hclause hchecker
      hfingerprint hbuild harchive =>
    ay_mmlp_conj_intro hmanifest
      (ay_mmlp_conj_intro htoken
        (ay_mmlp_conj_intro hmaps
          (ay_mmlp_conj_intro hdigest
            (ay_mmlp_conj_intro hcompletion
              (ay_mmlp_conj_intro hclause
                (ay_mmlp_conj_intro hchecker
                  (ay_mmlp_conj_intro hfingerprint
                    (ay_mmlp_conj_intro hbuild harchive))))))))

theorem ay_mmlp_accepted_parse_manifest
    {manifestOk tokenOk mapsOk assignmentDigestOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk archiveOk : Prop} :
    AyMMLPAcceptedParse manifestOk tokenOk mapsOk assignmentDigestOk
      completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    manifestOk :=
  fun h => ay_mmlp_conj_left h

theorem ay_mmlp_accepted_parse_token
    {manifestOk tokenOk mapsOk assignmentDigestOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk archiveOk : Prop} :
    AyMMLPAcceptedParse manifestOk tokenOk mapsOk assignmentDigestOk
      completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    tokenOk :=
  fun h => ay_mmlp_conj_left (ay_mmlp_conj_right h)

theorem ay_mmlp_accepted_parse_maps
    {manifestOk tokenOk mapsOk assignmentDigestOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk archiveOk : Prop} :
    AyMMLPAcceptedParse manifestOk tokenOk mapsOk assignmentDigestOk
      completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    mapsOk :=
  fun h => ay_mmlp_conj_left (ay_mmlp_conj_right (ay_mmlp_conj_right h))

theorem ay_mmlp_accepted_parse_assignment_digest
    {manifestOk tokenOk mapsOk assignmentDigestOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk archiveOk : Prop} :
    AyMMLPAcceptedParse manifestOk tokenOk mapsOk assignmentDigestOk
      completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    assignmentDigestOk :=
  fun h =>
    ay_mmlp_conj_left
      (ay_mmlp_conj_right (ay_mmlp_conj_right (ay_mmlp_conj_right h)))

theorem ay_mmlp_accepted_parse_completion
    {manifestOk tokenOk mapsOk assignmentDigestOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk archiveOk : Prop} :
    AyMMLPAcceptedParse manifestOk tokenOk mapsOk assignmentDigestOk
      completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    completionOk :=
  fun h =>
    ay_mmlp_conj_left
      (ay_mmlp_conj_right
        (ay_mmlp_conj_right (ay_mmlp_conj_right (ay_mmlp_conj_right h))))

theorem ay_mmlp_accepted_parse_clause_replay
    {manifestOk tokenOk mapsOk assignmentDigestOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk archiveOk : Prop} :
    AyMMLPAcceptedParse manifestOk tokenOk mapsOk assignmentDigestOk
      completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    clauseReplayOk :=
  fun h =>
    ay_mmlp_conj_left
      (ay_mmlp_conj_right
        (ay_mmlp_conj_right
          (ay_mmlp_conj_right (ay_mmlp_conj_right
            (ay_mmlp_conj_right h)))))

theorem ay_mmlp_accepted_parse_checker
    {manifestOk tokenOk mapsOk assignmentDigestOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk archiveOk : Prop} :
    AyMMLPAcceptedParse manifestOk tokenOk mapsOk assignmentDigestOk
      completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    checkerOk :=
  fun h =>
    ay_mmlp_conj_left
      (ay_mmlp_conj_right
        (ay_mmlp_conj_right
          (ay_mmlp_conj_right
            (ay_mmlp_conj_right (ay_mmlp_conj_right
              (ay_mmlp_conj_right h))))))

theorem ay_mmlp_accepted_parse_fingerprint
    {manifestOk tokenOk mapsOk assignmentDigestOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk archiveOk : Prop} :
    AyMMLPAcceptedParse manifestOk tokenOk mapsOk assignmentDigestOk
      completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    fingerprintOk :=
  fun h =>
    ay_mmlp_conj_left
      (ay_mmlp_conj_right
        (ay_mmlp_conj_right
          (ay_mmlp_conj_right
            (ay_mmlp_conj_right
              (ay_mmlp_conj_right (ay_mmlp_conj_right
                (ay_mmlp_conj_right h)))))))

theorem ay_mmlp_accepted_parse_build
    {manifestOk tokenOk mapsOk assignmentDigestOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk archiveOk : Prop} :
    AyMMLPAcceptedParse manifestOk tokenOk mapsOk assignmentDigestOk
      completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    buildOk :=
  fun h =>
    ay_mmlp_conj_left
      (ay_mmlp_conj_right
        (ay_mmlp_conj_right
          (ay_mmlp_conj_right
            (ay_mmlp_conj_right
              (ay_mmlp_conj_right
                (ay_mmlp_conj_right (ay_mmlp_conj_right
                  (ay_mmlp_conj_right h))))))))

theorem ay_mmlp_accepted_parse_archive
    {manifestOk tokenOk mapsOk assignmentDigestOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk archiveOk : Prop} :
    AyMMLPAcceptedParse manifestOk tokenOk mapsOk assignmentDigestOk
      completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    archiveOk :=
  fun h =>
    ay_mmlp_conj_right
      (ay_mmlp_conj_right
        (ay_mmlp_conj_right
          (ay_mmlp_conj_right
            (ay_mmlp_conj_right
              (ay_mmlp_conj_right
                (ay_mmlp_conj_right (ay_mmlp_conj_right
                  (ay_mmlp_conj_right h))))))))

theorem ay_mmlp_public_sat_witness_intro
    {acceptedParse parsedWitness publicSatClaim : Prop} :
    acceptedParse -> parsedWitness -> publicSatClaim ->
    AyMMLPPublicSatWitness acceptedParse parsedWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_mmlp_conj_intro hevidence (ay_mmlp_conj_intro hwitness hclaim)

theorem ay_mmlp_public_sat_witness_evidence
    {acceptedParse parsedWitness publicSatClaim : Prop} :
    AyMMLPPublicSatWitness acceptedParse parsedWitness publicSatClaim ->
    acceptedParse :=
  fun h => ay_mmlp_conj_left h

theorem ay_mmlp_public_sat_witness_claim
    {acceptedParse parsedWitness publicSatClaim : Prop} :
    AyMMLPPublicSatWitness acceptedParse parsedWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_mmlp_conj_right (ay_mmlp_conj_right h)

theorem ay_mmlp_accepted_parser_manifest_publishes_sound_sat
    {manifestOk tokenOk mapsOk assignmentDigestOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk archiveOk parsedWitness
      publicSatClaim : Prop} :
    AyMMLPAcceptedParse manifestOk tokenOk mapsOk assignmentDigestOk
      completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk ->
    parsedWitness -> publicSatClaim ->
    AyMMLPPublicSatWitness
      (AyMMLPAcceptedParse manifestOk tokenOk mapsOk assignmentDigestOk
        completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      parsedWitness publicSatClaim :=
  ay_mmlp_public_sat_witness_intro

theorem ay_mmlp_model_line_parse_preserves_truth
    {lineTruth assignmentTruth : Prop} :
    AyMMLPEquisat lineTruth assignmentTruth -> lineTruth -> assignmentTruth :=
  ay_mmlp_equisat_forward

theorem ay_mmlp_public_sat_requires_accepted_parse
    {acceptedParse parsedWitness publicSatClaim : Prop} :
    AyMMLPPublicSatWitness acceptedParse parsedWitness publicSatClaim ->
    acceptedParse :=
  ay_mmlp_public_sat_witness_evidence

theorem ay_mmlp_publication_requires_manifest
    {manifestOk tokenOk mapsOk assignmentDigestOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk archiveOk parsedWitness
      publicSatClaim : Prop} :
    AyMMLPPublicSatWitness
      (AyMMLPAcceptedParse manifestOk tokenOk mapsOk assignmentDigestOk
        completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      parsedWitness publicSatClaim ->
    manifestOk :=
  fun h => ay_mmlp_accepted_parse_manifest
    (ay_mmlp_public_sat_witness_evidence h)

theorem ay_mmlp_publication_requires_tokenization
    {manifestOk tokenOk mapsOk assignmentDigestOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk archiveOk parsedWitness
      publicSatClaim : Prop} :
    AyMMLPPublicSatWitness
      (AyMMLPAcceptedParse manifestOk tokenOk mapsOk assignmentDigestOk
        completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      parsedWitness publicSatClaim ->
    tokenOk :=
  fun h => ay_mmlp_accepted_parse_token
    (ay_mmlp_public_sat_witness_evidence h)

theorem ay_mmlp_publication_requires_maps
    {manifestOk tokenOk mapsOk assignmentDigestOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk archiveOk parsedWitness
      publicSatClaim : Prop} :
    AyMMLPPublicSatWitness
      (AyMMLPAcceptedParse manifestOk tokenOk mapsOk assignmentDigestOk
        completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      parsedWitness publicSatClaim ->
    mapsOk :=
  fun h => ay_mmlp_accepted_parse_maps
    (ay_mmlp_public_sat_witness_evidence h)

theorem ay_mmlp_publication_requires_assignment_digest
    {manifestOk tokenOk mapsOk assignmentDigestOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk archiveOk parsedWitness
      publicSatClaim : Prop} :
    AyMMLPPublicSatWitness
      (AyMMLPAcceptedParse manifestOk tokenOk mapsOk assignmentDigestOk
        completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      parsedWitness publicSatClaim ->
    assignmentDigestOk :=
  fun h => ay_mmlp_accepted_parse_assignment_digest
    (ay_mmlp_public_sat_witness_evidence h)

theorem ay_mmlp_publication_requires_completion
    {manifestOk tokenOk mapsOk assignmentDigestOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk archiveOk parsedWitness
      publicSatClaim : Prop} :
    AyMMLPPublicSatWitness
      (AyMMLPAcceptedParse manifestOk tokenOk mapsOk assignmentDigestOk
        completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      parsedWitness publicSatClaim ->
    completionOk :=
  fun h => ay_mmlp_accepted_parse_completion
    (ay_mmlp_public_sat_witness_evidence h)

theorem ay_mmlp_publication_requires_clause_replay
    {manifestOk tokenOk mapsOk assignmentDigestOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk archiveOk parsedWitness
      publicSatClaim : Prop} :
    AyMMLPPublicSatWitness
      (AyMMLPAcceptedParse manifestOk tokenOk mapsOk assignmentDigestOk
        completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      parsedWitness publicSatClaim ->
    clauseReplayOk :=
  fun h => ay_mmlp_accepted_parse_clause_replay
    (ay_mmlp_public_sat_witness_evidence h)

theorem ay_mmlp_publication_requires_checker
    {manifestOk tokenOk mapsOk assignmentDigestOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk archiveOk parsedWitness
      publicSatClaim : Prop} :
    AyMMLPPublicSatWitness
      (AyMMLPAcceptedParse manifestOk tokenOk mapsOk assignmentDigestOk
        completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      parsedWitness publicSatClaim ->
    checkerOk :=
  fun h => ay_mmlp_accepted_parse_checker
    (ay_mmlp_public_sat_witness_evidence h)

theorem ay_mmlp_publication_requires_fingerprint
    {manifestOk tokenOk mapsOk assignmentDigestOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk archiveOk parsedWitness
      publicSatClaim : Prop} :
    AyMMLPPublicSatWitness
      (AyMMLPAcceptedParse manifestOk tokenOk mapsOk assignmentDigestOk
        completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      parsedWitness publicSatClaim ->
    fingerprintOk :=
  fun h => ay_mmlp_accepted_parse_fingerprint
    (ay_mmlp_public_sat_witness_evidence h)

theorem ay_mmlp_publication_requires_build
    {manifestOk tokenOk mapsOk assignmentDigestOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk archiveOk parsedWitness
      publicSatClaim : Prop} :
    AyMMLPPublicSatWitness
      (AyMMLPAcceptedParse manifestOk tokenOk mapsOk assignmentDigestOk
        completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      parsedWitness publicSatClaim ->
    buildOk :=
  fun h => ay_mmlp_accepted_parse_build
    (ay_mmlp_public_sat_witness_evidence h)

theorem ay_mmlp_publication_requires_archive
    {manifestOk tokenOk mapsOk assignmentDigestOk completionOk clauseReplayOk
      checkerOk fingerprintOk buildOk archiveOk parsedWitness
      publicSatClaim : Prop} :
    AyMMLPPublicSatWitness
      (AyMMLPAcceptedParse manifestOk tokenOk mapsOk assignmentDigestOk
        completionOk clauseReplayOk checkerOk fingerprintOk buildOk archiveOk)
      parsedWitness publicSatClaim ->
    archiveOk :=
  fun h => ay_mmlp_accepted_parse_archive
    (ay_mmlp_public_sat_witness_evidence h)

theorem ay_mmlp_no_claim_diagnostic_intro
    {reason blocksPublication : Prop} :
    reason -> blocksPublication ->
    AyMMLPNoClaimDiagnostic reason blocksPublication :=
  ay_mmlp_conj_intro

theorem ay_mmlp_no_claim_diagnostic_blocks
    {reason blocksPublication : Prop} :
    AyMMLPNoClaimDiagnostic reason blocksPublication -> blocksPublication :=
  ay_mmlp_conj_right

theorem ay_mmlp_recompute_obligation_intro
    {reason recomputeRequested : Prop} :
    reason -> recomputeRequested ->
    AyMMLPRecomputeObligation reason recomputeRequested :=
  ay_mmlp_conj_intro

theorem ay_mmlp_recompute_obligation_request
    {reason recomputeRequested : Prop} :
    AyMMLPRecomputeObligation reason recomputeRequested -> recomputeRequested :=
  ay_mmlp_conj_right

theorem ay_mmlp_parser_drift_no_claim
    {parserDrift blocksPublication : Prop} :
    parserDrift -> blocksPublication ->
    AyMMLPNoClaimDiagnostic parserDrift blocksPublication :=
  ay_mmlp_no_claim_diagnostic_intro

theorem ay_mmlp_parser_drift_recompute
    {parserDrift recomputeRequested : Prop} :
    parserDrift -> recomputeRequested ->
    AyMMLPRecomputeObligation parserDrift recomputeRequested :=
  ay_mmlp_recompute_obligation_intro

theorem ay_mmlp_tokenization_mismatch_no_claim
    {tokenizationMismatch blocksPublication : Prop} :
    tokenizationMismatch -> blocksPublication ->
    AyMMLPNoClaimDiagnostic tokenizationMismatch blocksPublication :=
  ay_mmlp_no_claim_diagnostic_intro

theorem ay_mmlp_map_mismatch_no_claim
    {mapMismatch blocksPublication : Prop} :
    mapMismatch -> blocksPublication ->
    AyMMLPNoClaimDiagnostic mapMismatch blocksPublication :=
  ay_mmlp_no_claim_diagnostic_intro

theorem ay_mmlp_assignment_digest_drift_no_claim
    {assignmentDigestDrift blocksPublication : Prop} :
    assignmentDigestDrift -> blocksPublication ->
    AyMMLPNoClaimDiagnostic assignmentDigestDrift blocksPublication :=
  ay_mmlp_no_claim_diagnostic_intro

theorem ay_mmlp_completion_mismatch_no_claim
    {completionMismatch blocksPublication : Prop} :
    completionMismatch -> blocksPublication ->
    AyMMLPNoClaimDiagnostic completionMismatch blocksPublication :=
  ay_mmlp_no_claim_diagnostic_intro

theorem ay_mmlp_clause_replay_gap_no_claim
    {clauseReplayGap blocksPublication : Prop} :
    clauseReplayGap -> blocksPublication ->
    AyMMLPNoClaimDiagnostic clauseReplayGap blocksPublication :=
  ay_mmlp_no_claim_diagnostic_intro

theorem ay_mmlp_stale_fingerprint_no_claim
    {staleFingerprint blocksPublication : Prop} :
    staleFingerprint -> blocksPublication ->
    AyMMLPNoClaimDiagnostic staleFingerprint blocksPublication :=
  ay_mmlp_no_claim_diagnostic_intro

theorem ay_mmlp_checker_reject_no_claim
    {checkerReject blocksPublication : Prop} :
    checkerReject -> blocksPublication ->
    AyMMLPNoClaimDiagnostic checkerReject blocksPublication :=
  ay_mmlp_no_claim_diagnostic_intro

theorem ay_mmlp_build_drift_no_claim
    {buildDrift blocksPublication : Prop} :
    buildDrift -> blocksPublication ->
    AyMMLPNoClaimDiagnostic buildDrift blocksPublication :=
  ay_mmlp_no_claim_diagnostic_intro

theorem ay_mmlp_archive_mismatch_no_claim
    {archiveMismatch blocksPublication : Prop} :
    archiveMismatch -> blocksPublication ->
    AyMMLPNoClaimDiagnostic archiveMismatch blocksPublication :=
  ay_mmlp_no_claim_diagnostic_intro

theorem ay_mmlp_bad_parser_manifest_cannot_bless_sat
    {failure blocksPublication recomputeRequested : Prop} :
    AyMMLPNoClaimDiagnostic failure blocksPublication ->
    AyMMLPRecomputeObligation failure recomputeRequested ->
    AyMMLPConj blocksPublication recomputeRequested :=
  fun hdiagnostic hrecompute =>
    ay_mmlp_conj_intro
      (ay_mmlp_no_claim_diagnostic_blocks hdiagnostic)
      (ay_mmlp_recompute_obligation_request hrecompute)
