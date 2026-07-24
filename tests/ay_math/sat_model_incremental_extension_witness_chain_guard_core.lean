/- SAT-COMP/ay incremental extension witness-chain guard contract.

This self-contained package models publication after preprocessing or
inprocessing when eliminated variables are reconstructed by an incremental
extension-witness chain.
-/

def AyMIEWConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMIEWDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMIEWEquisat (source target : Prop) : Prop :=
  AyMIEWConj (source -> target) (target -> source)

def AyMIEWExtensionStep
    (eliminatedVariable stepWitness stepAgreement : Prop) : Prop :=
  AyMIEWConj eliminatedVariable (AyMIEWConj stepWitness stepAgreement)

def AyMIEWChainDigest
    (chainLedger chainDigest digestAgreement : Prop) : Prop :=
  AyMIEWConj chainLedger (AyMIEWConj chainDigest digestAgreement)

def AyMIEWProjectionManifest
    (preprocessedAssignment originalAssignment projectionAgreement : Prop) : Prop :=
  AyMIEWConj preprocessedAssignment
    (AyMIEWConj originalAssignment projectionAgreement)

def AyMIEWDimacsMap
    (internalToDimacs dimacsToInternal mapAgreement : Prop) : Prop :=
  AyMIEWConj internalToDimacs (AyMIEWConj dimacsToInternal mapAgreement)

def AyMIEWAssignmentDigest
    (internalDigest originalDigest digestAgreement : Prop) : Prop :=
  AyMIEWConj internalDigest (AyMIEWConj originalDigest digestAgreement)

def AyMIEWClauseReplay
    (clauseReplay originalEvaluation replayAgreement : Prop) : Prop :=
  AyMIEWConj clauseReplay (AyMIEWConj originalEvaluation replayAgreement)

def AyMIEWCheckerTranscript
    (checkerAccepted transcript transcriptAgreement : Prop) : Prop :=
  AyMIEWConj checkerAccepted (AyMIEWConj transcript transcriptAgreement)

def AyMIEWFormulaFingerprint
    (originalFingerprint chainFingerprint fingerprintAgreement : Prop) : Prop :=
  AyMIEWConj originalFingerprint
    (AyMIEWConj chainFingerprint fingerprintAgreement)

def AyMIEWBuildEvidence
    (solverBuild chainBuild buildAgreement : Prop) : Prop :=
  AyMIEWConj solverBuild (AyMIEWConj chainBuild buildAgreement)

def AyMIEWArchiveManifest
    (archiveEntry archiveDigest archiveAgreement : Prop) : Prop :=
  AyMIEWConj archiveEntry (AyMIEWConj archiveDigest archiveAgreement)

def AyMIEWAcceptedChain
    (stepOk chainOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop) : Prop :=
  AyMIEWConj stepOk
    (AyMIEWConj chainOk
      (AyMIEWConj projectionOk
        (AyMIEWConj mapOk
          (AyMIEWConj digestOk
            (AyMIEWConj replayOk
              (AyMIEWConj checkerOk
                (AyMIEWConj fingerprintOk
                  (AyMIEWConj buildOk archiveOk))))))))

def AyMIEWPublicSatWitness
    (acceptedChain originalWitness publicSatClaim : Prop) : Prop :=
  AyMIEWConj acceptedChain (AyMIEWConj originalWitness publicSatClaim)

def AyMIEWNoClaimDiagnostic (reason blocksPublication : Prop) : Prop :=
  AyMIEWConj reason blocksPublication

def AyMIEWRecomputeObligation (reason recomputeRequested : Prop) : Prop :=
  AyMIEWConj reason recomputeRequested

theorem ay_miew_conj_intro {left right : Prop} :
    left -> right -> AyMIEWConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_miew_conj_left {left right : Prop} :
    AyMIEWConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_miew_conj_right {left right : Prop} :
    AyMIEWConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_miew_disj_left {left right : Prop} :
    left -> AyMIEWDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_miew_disj_right {left right : Prop} :
    right -> AyMIEWDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_miew_equisat_intro {source target : Prop} :
    (source -> target) -> (target -> source) -> AyMIEWEquisat source target :=
  fun forward backward => ay_miew_conj_intro forward backward

theorem ay_miew_equisat_forward {source target : Prop} :
    AyMIEWEquisat source target -> source -> target :=
  fun h => ay_miew_conj_left h

theorem ay_miew_equisat_backward {source target : Prop} :
    AyMIEWEquisat source target -> target -> source :=
  fun h => ay_miew_conj_right h

theorem ay_miew_extension_step_intro
    {eliminatedVariable stepWitness stepAgreement : Prop} :
    eliminatedVariable -> stepWitness -> stepAgreement ->
    AyMIEWExtensionStep eliminatedVariable stepWitness stepAgreement :=
  fun helim hwitness hagree =>
    ay_miew_conj_intro helim (ay_miew_conj_intro hwitness hagree)

theorem ay_miew_extension_step_variable
    {eliminatedVariable stepWitness stepAgreement : Prop} :
    AyMIEWExtensionStep eliminatedVariable stepWitness stepAgreement ->
    eliminatedVariable :=
  fun h => ay_miew_conj_left h

theorem ay_miew_extension_step_witness
    {eliminatedVariable stepWitness stepAgreement : Prop} :
    AyMIEWExtensionStep eliminatedVariable stepWitness stepAgreement ->
    stepWitness :=
  fun h => ay_miew_conj_left (ay_miew_conj_right h)

theorem ay_miew_extension_step_agreement
    {eliminatedVariable stepWitness stepAgreement : Prop} :
    AyMIEWExtensionStep eliminatedVariable stepWitness stepAgreement ->
    stepAgreement :=
  fun h => ay_miew_conj_right (ay_miew_conj_right h)

theorem ay_miew_chain_digest_intro
    {chainLedger chainDigest digestAgreement : Prop} :
    chainLedger -> chainDigest -> digestAgreement ->
    AyMIEWChainDigest chainLedger chainDigest digestAgreement :=
  fun hledger hdigest hagree =>
    ay_miew_conj_intro hledger (ay_miew_conj_intro hdigest hagree)

theorem ay_miew_projection_manifest_intro
    {preprocessedAssignment originalAssignment projectionAgreement : Prop} :
    preprocessedAssignment -> originalAssignment -> projectionAgreement ->
    AyMIEWProjectionManifest
      preprocessedAssignment originalAssignment projectionAgreement :=
  fun hpre horiginal hagree =>
    ay_miew_conj_intro hpre (ay_miew_conj_intro horiginal hagree)

theorem ay_miew_dimacs_map_intro
    {internalToDimacs dimacsToInternal mapAgreement : Prop} :
    internalToDimacs -> dimacsToInternal -> mapAgreement ->
    AyMIEWDimacsMap internalToDimacs dimacsToInternal mapAgreement :=
  fun hforward hbackward hagree =>
    ay_miew_conj_intro hforward (ay_miew_conj_intro hbackward hagree)

theorem ay_miew_assignment_digest_intro
    {internalDigest originalDigest digestAgreement : Prop} :
    internalDigest -> originalDigest -> digestAgreement ->
    AyMIEWAssignmentDigest internalDigest originalDigest digestAgreement :=
  fun hinternal horiginal hagree =>
    ay_miew_conj_intro hinternal (ay_miew_conj_intro horiginal hagree)

theorem ay_miew_clause_replay_intro
    {clauseReplay originalEvaluation replayAgreement : Prop} :
    clauseReplay -> originalEvaluation -> replayAgreement ->
    AyMIEWClauseReplay clauseReplay originalEvaluation replayAgreement :=
  fun hreplay heval hagree =>
    ay_miew_conj_intro hreplay (ay_miew_conj_intro heval hagree)

theorem ay_miew_checker_transcript_intro
    {checkerAccepted transcript transcriptAgreement : Prop} :
    checkerAccepted -> transcript -> transcriptAgreement ->
    AyMIEWCheckerTranscript checkerAccepted transcript transcriptAgreement :=
  fun haccepted htranscript hagree =>
    ay_miew_conj_intro haccepted (ay_miew_conj_intro htranscript hagree)

theorem ay_miew_formula_fingerprint_intro
    {originalFingerprint chainFingerprint fingerprintAgreement : Prop} :
    originalFingerprint -> chainFingerprint -> fingerprintAgreement ->
    AyMIEWFormulaFingerprint
      originalFingerprint chainFingerprint fingerprintAgreement :=
  fun horiginal hchain hagree =>
    ay_miew_conj_intro horiginal (ay_miew_conj_intro hchain hagree)

theorem ay_miew_build_evidence_intro
    {solverBuild chainBuild buildAgreement : Prop} :
    solverBuild -> chainBuild -> buildAgreement ->
    AyMIEWBuildEvidence solverBuild chainBuild buildAgreement :=
  fun hsolver hchain hagree =>
    ay_miew_conj_intro hsolver (ay_miew_conj_intro hchain hagree)

theorem ay_miew_archive_manifest_intro
    {archiveEntry archiveDigest archiveAgreement : Prop} :
    archiveEntry -> archiveDigest -> archiveAgreement ->
    AyMIEWArchiveManifest archiveEntry archiveDigest archiveAgreement :=
  fun hentry hdigest hagree =>
    ay_miew_conj_intro hentry (ay_miew_conj_intro hdigest hagree)

theorem ay_miew_accepted_chain_intro
    {stepOk chainOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    stepOk -> chainOk -> projectionOk -> mapOk -> digestOk -> replayOk ->
    checkerOk -> fingerprintOk -> buildOk -> archiveOk ->
    AyMIEWAcceptedChain stepOk chainOk projectionOk mapOk digestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk :=
  fun hstep hchain hprojection hmap hdigest hreplay hchecker hfingerprint
      hbuild harchive =>
    ay_miew_conj_intro hstep
      (ay_miew_conj_intro hchain
        (ay_miew_conj_intro hprojection
          (ay_miew_conj_intro hmap
            (ay_miew_conj_intro hdigest
              (ay_miew_conj_intro hreplay
                (ay_miew_conj_intro hchecker
                  (ay_miew_conj_intro hfingerprint
                    (ay_miew_conj_intro hbuild harchive))))))))

theorem ay_miew_accepted_chain_step
    {stepOk chainOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyMIEWAcceptedChain stepOk chainOk projectionOk mapOk digestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk ->
    stepOk :=
  fun h => ay_miew_conj_left h

theorem ay_miew_accepted_chain_chain
    {stepOk chainOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyMIEWAcceptedChain stepOk chainOk projectionOk mapOk digestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk ->
    chainOk :=
  fun h => ay_miew_conj_left (ay_miew_conj_right h)

theorem ay_miew_accepted_chain_projection
    {stepOk chainOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyMIEWAcceptedChain stepOk chainOk projectionOk mapOk digestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk ->
    projectionOk :=
  fun h => ay_miew_conj_left (ay_miew_conj_right (ay_miew_conj_right h))

theorem ay_miew_accepted_chain_map
    {stepOk chainOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyMIEWAcceptedChain stepOk chainOk projectionOk mapOk digestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk ->
    mapOk :=
  fun h =>
    ay_miew_conj_left
      (ay_miew_conj_right (ay_miew_conj_right (ay_miew_conj_right h)))

theorem ay_miew_accepted_chain_digest
    {stepOk chainOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyMIEWAcceptedChain stepOk chainOk projectionOk mapOk digestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk ->
    digestOk :=
  fun h =>
    ay_miew_conj_left
      (ay_miew_conj_right
        (ay_miew_conj_right (ay_miew_conj_right (ay_miew_conj_right h))))

theorem ay_miew_accepted_chain_replay
    {stepOk chainOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyMIEWAcceptedChain stepOk chainOk projectionOk mapOk digestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk ->
    replayOk :=
  fun h =>
    ay_miew_conj_left
      (ay_miew_conj_right
        (ay_miew_conj_right
          (ay_miew_conj_right (ay_miew_conj_right
            (ay_miew_conj_right h)))))

theorem ay_miew_accepted_chain_checker
    {stepOk chainOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyMIEWAcceptedChain stepOk chainOk projectionOk mapOk digestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk ->
    checkerOk :=
  fun h =>
    ay_miew_conj_left
      (ay_miew_conj_right
        (ay_miew_conj_right
          (ay_miew_conj_right
            (ay_miew_conj_right (ay_miew_conj_right
              (ay_miew_conj_right h))))))

theorem ay_miew_accepted_chain_fingerprint
    {stepOk chainOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyMIEWAcceptedChain stepOk chainOk projectionOk mapOk digestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk ->
    fingerprintOk :=
  fun h =>
    ay_miew_conj_left
      (ay_miew_conj_right
        (ay_miew_conj_right
          (ay_miew_conj_right
            (ay_miew_conj_right
              (ay_miew_conj_right (ay_miew_conj_right
                (ay_miew_conj_right h)))))))

theorem ay_miew_accepted_chain_build
    {stepOk chainOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyMIEWAcceptedChain stepOk chainOk projectionOk mapOk digestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk ->
    buildOk :=
  fun h =>
    ay_miew_conj_left
      (ay_miew_conj_right
        (ay_miew_conj_right
          (ay_miew_conj_right
            (ay_miew_conj_right
              (ay_miew_conj_right
                (ay_miew_conj_right (ay_miew_conj_right
                  (ay_miew_conj_right h))))))))

theorem ay_miew_accepted_chain_archive
    {stepOk chainOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyMIEWAcceptedChain stepOk chainOk projectionOk mapOk digestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk ->
    archiveOk :=
  fun h =>
    ay_miew_conj_right
      (ay_miew_conj_right
        (ay_miew_conj_right
          (ay_miew_conj_right
            (ay_miew_conj_right
              (ay_miew_conj_right
                (ay_miew_conj_right (ay_miew_conj_right
                  (ay_miew_conj_right h))))))))

theorem ay_miew_public_sat_witness_intro
    {acceptedChain originalWitness publicSatClaim : Prop} :
    acceptedChain -> originalWitness -> publicSatClaim ->
    AyMIEWPublicSatWitness acceptedChain originalWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_miew_conj_intro hevidence (ay_miew_conj_intro hwitness hclaim)

theorem ay_miew_public_sat_witness_evidence
    {acceptedChain originalWitness publicSatClaim : Prop} :
    AyMIEWPublicSatWitness acceptedChain originalWitness publicSatClaim ->
    acceptedChain :=
  fun h => ay_miew_conj_left h

theorem ay_miew_public_sat_witness_claim
    {acceptedChain originalWitness publicSatClaim : Prop} :
    AyMIEWPublicSatWitness acceptedChain originalWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_miew_conj_right (ay_miew_conj_right h)

theorem ay_miew_accepted_witness_chain_publishes_sound_sat
    {stepOk chainOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyMIEWAcceptedChain stepOk chainOk projectionOk mapOk digestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk ->
    originalWitness -> publicSatClaim ->
    AyMIEWPublicSatWitness
      (AyMIEWAcceptedChain stepOk chainOk projectionOk mapOk digestOk replayOk
        checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim :=
  ay_miew_public_sat_witness_intro

theorem ay_miew_chain_reconstructs_original_assignment
    {preprocessedTruth originalTruth : Prop} :
    AyMIEWEquisat preprocessedTruth originalTruth ->
    preprocessedTruth -> originalTruth :=
  ay_miew_equisat_forward

theorem ay_miew_public_sat_requires_accepted_chain
    {acceptedChain originalWitness publicSatClaim : Prop} :
    AyMIEWPublicSatWitness acceptedChain originalWitness publicSatClaim ->
    acceptedChain :=
  ay_miew_public_sat_witness_evidence

theorem ay_miew_publication_requires_step
    {stepOk chainOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyMIEWPublicSatWitness
      (AyMIEWAcceptedChain stepOk chainOk projectionOk mapOk digestOk replayOk
        checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    stepOk :=
  fun h => ay_miew_accepted_chain_step
    (ay_miew_public_sat_witness_evidence h)

theorem ay_miew_publication_requires_chain
    {stepOk chainOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyMIEWPublicSatWitness
      (AyMIEWAcceptedChain stepOk chainOk projectionOk mapOk digestOk replayOk
        checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    chainOk :=
  fun h => ay_miew_accepted_chain_chain
    (ay_miew_public_sat_witness_evidence h)

theorem ay_miew_publication_requires_projection
    {stepOk chainOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyMIEWPublicSatWitness
      (AyMIEWAcceptedChain stepOk chainOk projectionOk mapOk digestOk replayOk
        checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    projectionOk :=
  fun h => ay_miew_accepted_chain_projection
    (ay_miew_public_sat_witness_evidence h)

theorem ay_miew_publication_requires_map
    {stepOk chainOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyMIEWPublicSatWitness
      (AyMIEWAcceptedChain stepOk chainOk projectionOk mapOk digestOk replayOk
        checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    mapOk :=
  fun h => ay_miew_accepted_chain_map
    (ay_miew_public_sat_witness_evidence h)

theorem ay_miew_publication_requires_digest
    {stepOk chainOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyMIEWPublicSatWitness
      (AyMIEWAcceptedChain stepOk chainOk projectionOk mapOk digestOk replayOk
        checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    digestOk :=
  fun h => ay_miew_accepted_chain_digest
    (ay_miew_public_sat_witness_evidence h)

theorem ay_miew_publication_requires_replay
    {stepOk chainOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyMIEWPublicSatWitness
      (AyMIEWAcceptedChain stepOk chainOk projectionOk mapOk digestOk replayOk
        checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    replayOk :=
  fun h => ay_miew_accepted_chain_replay
    (ay_miew_public_sat_witness_evidence h)

theorem ay_miew_publication_requires_checker
    {stepOk chainOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyMIEWPublicSatWitness
      (AyMIEWAcceptedChain stepOk chainOk projectionOk mapOk digestOk replayOk
        checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    checkerOk :=
  fun h => ay_miew_accepted_chain_checker
    (ay_miew_public_sat_witness_evidence h)

theorem ay_miew_publication_requires_fingerprint
    {stepOk chainOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyMIEWPublicSatWitness
      (AyMIEWAcceptedChain stepOk chainOk projectionOk mapOk digestOk replayOk
        checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    fingerprintOk :=
  fun h => ay_miew_accepted_chain_fingerprint
    (ay_miew_public_sat_witness_evidence h)

theorem ay_miew_publication_requires_build
    {stepOk chainOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyMIEWPublicSatWitness
      (AyMIEWAcceptedChain stepOk chainOk projectionOk mapOk digestOk replayOk
        checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    buildOk :=
  fun h => ay_miew_accepted_chain_build
    (ay_miew_public_sat_witness_evidence h)

theorem ay_miew_publication_requires_archive
    {stepOk chainOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyMIEWPublicSatWitness
      (AyMIEWAcceptedChain stepOk chainOk projectionOk mapOk digestOk replayOk
        checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    archiveOk :=
  fun h => ay_miew_accepted_chain_archive
    (ay_miew_public_sat_witness_evidence h)

theorem ay_miew_no_claim_diagnostic_intro
    {reason blocksPublication : Prop} :
    reason -> blocksPublication ->
    AyMIEWNoClaimDiagnostic reason blocksPublication :=
  ay_miew_conj_intro

theorem ay_miew_no_claim_diagnostic_blocks
    {reason blocksPublication : Prop} :
    AyMIEWNoClaimDiagnostic reason blocksPublication -> blocksPublication :=
  ay_miew_conj_right

theorem ay_miew_recompute_obligation_intro
    {reason recomputeRequested : Prop} :
    reason -> recomputeRequested ->
    AyMIEWRecomputeObligation reason recomputeRequested :=
  ay_miew_conj_intro

theorem ay_miew_recompute_obligation_request
    {reason recomputeRequested : Prop} :
    AyMIEWRecomputeObligation reason recomputeRequested -> recomputeRequested :=
  ay_miew_conj_right

theorem ay_miew_step_failure_no_claim
    {stepFailure blocksPublication : Prop} :
    stepFailure -> blocksPublication ->
    AyMIEWNoClaimDiagnostic stepFailure blocksPublication :=
  ay_miew_no_claim_diagnostic_intro

theorem ay_miew_step_failure_recompute
    {stepFailure recomputeRequested : Prop} :
    stepFailure -> recomputeRequested ->
    AyMIEWRecomputeObligation stepFailure recomputeRequested :=
  ay_miew_recompute_obligation_intro

theorem ay_miew_chain_failure_no_claim
    {chainFailure blocksPublication : Prop} :
    chainFailure -> blocksPublication ->
    AyMIEWNoClaimDiagnostic chainFailure blocksPublication :=
  ay_miew_no_claim_diagnostic_intro

theorem ay_miew_projection_failure_no_claim
    {projectionFailure blocksPublication : Prop} :
    projectionFailure -> blocksPublication ->
    AyMIEWNoClaimDiagnostic projectionFailure blocksPublication :=
  ay_miew_no_claim_diagnostic_intro

theorem ay_miew_map_failure_no_claim
    {mapFailure blocksPublication : Prop} :
    mapFailure -> blocksPublication ->
    AyMIEWNoClaimDiagnostic mapFailure blocksPublication :=
  ay_miew_no_claim_diagnostic_intro

theorem ay_miew_digest_failure_no_claim
    {digestFailure blocksPublication : Prop} :
    digestFailure -> blocksPublication ->
    AyMIEWNoClaimDiagnostic digestFailure blocksPublication :=
  ay_miew_no_claim_diagnostic_intro

theorem ay_miew_replay_failure_no_claim
    {replayFailure blocksPublication : Prop} :
    replayFailure -> blocksPublication ->
    AyMIEWNoClaimDiagnostic replayFailure blocksPublication :=
  ay_miew_no_claim_diagnostic_intro

theorem ay_miew_checker_failure_no_claim
    {checkerFailure blocksPublication : Prop} :
    checkerFailure -> blocksPublication ->
    AyMIEWNoClaimDiagnostic checkerFailure blocksPublication :=
  ay_miew_no_claim_diagnostic_intro

theorem ay_miew_fingerprint_failure_no_claim
    {fingerprintFailure blocksPublication : Prop} :
    fingerprintFailure -> blocksPublication ->
    AyMIEWNoClaimDiagnostic fingerprintFailure blocksPublication :=
  ay_miew_no_claim_diagnostic_intro

theorem ay_miew_build_failure_no_claim
    {buildFailure blocksPublication : Prop} :
    buildFailure -> blocksPublication ->
    AyMIEWNoClaimDiagnostic buildFailure blocksPublication :=
  ay_miew_no_claim_diagnostic_intro

theorem ay_miew_archive_failure_no_claim
    {archiveFailure blocksPublication : Prop} :
    archiveFailure -> blocksPublication ->
    AyMIEWNoClaimDiagnostic archiveFailure blocksPublication :=
  ay_miew_no_claim_diagnostic_intro

theorem ay_miew_bad_witness_chain_cannot_bless_sat
    {failure blocksPublication recomputeRequested : Prop} :
    AyMIEWNoClaimDiagnostic failure blocksPublication ->
    AyMIEWRecomputeObligation failure recomputeRequested ->
    AyMIEWConj blocksPublication recomputeRequested :=
  fun hdiagnostic hrecompute =>
    ay_miew_conj_intro
      (ay_miew_no_claim_diagnostic_blocks hdiagnostic)
      (ay_miew_recompute_obligation_request hrecompute)
