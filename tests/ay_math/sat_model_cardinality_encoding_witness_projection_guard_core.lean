/- SAT-COMP/ay cardinality-encoding witness projection guard contract.

This self-contained package models SAT model publication through cardinality
encodings.  Projection back to the original formula is accepted only when the
encoding manifest, auxiliary maps, extension witnesses, digest, replay,
checker, fingerprint, build, and archive evidence all agree.
-/

def AyCEWPConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyCEWPDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyCEWPEquisat (source target : Prop) : Prop :=
  AyCEWPConj (source -> target) (target -> source)

def AyCEWPEncodingManifest
    (cardinalityConstraint encodedClauses encodingAgreement : Prop) : Prop :=
  AyCEWPConj cardinalityConstraint
    (AyCEWPConj encodedClauses encodingAgreement)

def AyCEWPAuxiliaryVariableMap
    (auxiliaryVariables originalVariables mapAgreement : Prop) : Prop :=
  AyCEWPConj auxiliaryVariables
    (AyCEWPConj originalVariables mapAgreement)

def AyCEWPExtensionWitnessLedger
    (extensionWitness witnessLedger witnessAgreement : Prop) : Prop :=
  AyCEWPConj extensionWitness (AyCEWPConj witnessLedger witnessAgreement)

def AyCEWPAssignmentDigest
    (encodedDigest originalDigest digestAgreement : Prop) : Prop :=
  AyCEWPConj encodedDigest (AyCEWPConj originalDigest digestAgreement)

def AyCEWPClauseReplay
    (clauseReplay originalEvaluation replayAgreement : Prop) : Prop :=
  AyCEWPConj clauseReplay (AyCEWPConj originalEvaluation replayAgreement)

def AyCEWPCheckerTranscript
    (checkerAccepted transcript transcriptAgreement : Prop) : Prop :=
  AyCEWPConj checkerAccepted (AyCEWPConj transcript transcriptAgreement)

def AyCEWPFormulaFingerprint
    (originalFingerprint encodingFingerprint fingerprintAgreement : Prop) : Prop :=
  AyCEWPConj originalFingerprint
    (AyCEWPConj encodingFingerprint fingerprintAgreement)

def AyCEWPBuildEvidence
    (solverBuild encodingBuild buildAgreement : Prop) : Prop :=
  AyCEWPConj solverBuild (AyCEWPConj encodingBuild buildAgreement)

def AyCEWPArchiveManifest
    (archiveEntry archiveDigest archiveAgreement : Prop) : Prop :=
  AyCEWPConj archiveEntry (AyCEWPConj archiveDigest archiveAgreement)

def AyCEWPAcceptedProjection
    (encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop) : Prop :=
  AyCEWPConj encodingOk
    (AyCEWPConj mapOk
      (AyCEWPConj witnessOk
        (AyCEWPConj assignmentOk
          (AyCEWPConj replayOk
            (AyCEWPConj checkerOk
              (AyCEWPConj fingerprintOk
                (AyCEWPConj buildOk archiveOk)))))))

def AyCEWPPublicSatWitness
    (acceptedProjection originalWitness publicSatClaim : Prop) : Prop :=
  AyCEWPConj acceptedProjection (AyCEWPConj originalWitness publicSatClaim)

def AyCEWPNoClaimDiagnostic (reason blocksPublication : Prop) : Prop :=
  AyCEWPConj reason blocksPublication

def AyCEWPRecomputeObligation (reason recomputeRequested : Prop) : Prop :=
  AyCEWPConj reason recomputeRequested

theorem ay_cewp_conj_intro {left right : Prop} :
    left -> right -> AyCEWPConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_cewp_conj_left {left right : Prop} :
    AyCEWPConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_cewp_conj_right {left right : Prop} :
    AyCEWPConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_cewp_disj_left {left right : Prop} :
    left -> AyCEWPDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_cewp_disj_right {left right : Prop} :
    right -> AyCEWPDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_cewp_equisat_intro {source target : Prop} :
    (source -> target) -> (target -> source) -> AyCEWPEquisat source target :=
  fun forward backward => ay_cewp_conj_intro forward backward

theorem ay_cewp_equisat_forward {source target : Prop} :
    AyCEWPEquisat source target -> source -> target :=
  fun h => ay_cewp_conj_left h

theorem ay_cewp_equisat_backward {source target : Prop} :
    AyCEWPEquisat source target -> target -> source :=
  fun h => ay_cewp_conj_right h

theorem ay_cewp_encoding_manifest_intro
    {cardinalityConstraint encodedClauses encodingAgreement : Prop} :
    cardinalityConstraint -> encodedClauses -> encodingAgreement ->
    AyCEWPEncodingManifest
      cardinalityConstraint encodedClauses encodingAgreement :=
  fun hcard hencoded hagree =>
    ay_cewp_conj_intro hcard (ay_cewp_conj_intro hencoded hagree)

theorem ay_cewp_encoding_manifest_constraint
    {cardinalityConstraint encodedClauses encodingAgreement : Prop} :
    AyCEWPEncodingManifest
      cardinalityConstraint encodedClauses encodingAgreement ->
    cardinalityConstraint :=
  fun h => ay_cewp_conj_left h

theorem ay_cewp_encoding_manifest_encoded
    {cardinalityConstraint encodedClauses encodingAgreement : Prop} :
    AyCEWPEncodingManifest
      cardinalityConstraint encodedClauses encodingAgreement ->
    encodedClauses :=
  fun h => ay_cewp_conj_left (ay_cewp_conj_right h)

theorem ay_cewp_encoding_manifest_agreement
    {cardinalityConstraint encodedClauses encodingAgreement : Prop} :
    AyCEWPEncodingManifest
      cardinalityConstraint encodedClauses encodingAgreement ->
    encodingAgreement :=
  fun h => ay_cewp_conj_right (ay_cewp_conj_right h)

theorem ay_cewp_auxiliary_variable_map_intro
    {auxiliaryVariables originalVariables mapAgreement : Prop} :
    auxiliaryVariables -> originalVariables -> mapAgreement ->
    AyCEWPAuxiliaryVariableMap
      auxiliaryVariables originalVariables mapAgreement :=
  fun haux horiginal hagree =>
    ay_cewp_conj_intro haux (ay_cewp_conj_intro horiginal hagree)

theorem ay_cewp_extension_witness_ledger_intro
    {extensionWitness witnessLedger witnessAgreement : Prop} :
    extensionWitness -> witnessLedger -> witnessAgreement ->
    AyCEWPExtensionWitnessLedger
      extensionWitness witnessLedger witnessAgreement :=
  fun hwitness hledger hagree =>
    ay_cewp_conj_intro hwitness (ay_cewp_conj_intro hledger hagree)

theorem ay_cewp_assignment_digest_intro
    {encodedDigest originalDigest digestAgreement : Prop} :
    encodedDigest -> originalDigest -> digestAgreement ->
    AyCEWPAssignmentDigest encodedDigest originalDigest digestAgreement :=
  fun hencoded horiginal hagree =>
    ay_cewp_conj_intro hencoded (ay_cewp_conj_intro horiginal hagree)

theorem ay_cewp_clause_replay_intro
    {clauseReplay originalEvaluation replayAgreement : Prop} :
    clauseReplay -> originalEvaluation -> replayAgreement ->
    AyCEWPClauseReplay clauseReplay originalEvaluation replayAgreement :=
  fun hreplay heval hagree =>
    ay_cewp_conj_intro hreplay (ay_cewp_conj_intro heval hagree)

theorem ay_cewp_checker_transcript_intro
    {checkerAccepted transcript transcriptAgreement : Prop} :
    checkerAccepted -> transcript -> transcriptAgreement ->
    AyCEWPCheckerTranscript checkerAccepted transcript transcriptAgreement :=
  fun haccepted htranscript hagree =>
    ay_cewp_conj_intro haccepted (ay_cewp_conj_intro htranscript hagree)

theorem ay_cewp_formula_fingerprint_intro
    {originalFingerprint encodingFingerprint fingerprintAgreement : Prop} :
    originalFingerprint -> encodingFingerprint -> fingerprintAgreement ->
    AyCEWPFormulaFingerprint
      originalFingerprint encodingFingerprint fingerprintAgreement :=
  fun horiginal hencoding hagree =>
    ay_cewp_conj_intro horiginal (ay_cewp_conj_intro hencoding hagree)

theorem ay_cewp_build_evidence_intro
    {solverBuild encodingBuild buildAgreement : Prop} :
    solverBuild -> encodingBuild -> buildAgreement ->
    AyCEWPBuildEvidence solverBuild encodingBuild buildAgreement :=
  fun hsolver hencoding hagree =>
    ay_cewp_conj_intro hsolver (ay_cewp_conj_intro hencoding hagree)

theorem ay_cewp_archive_manifest_intro
    {archiveEntry archiveDigest archiveAgreement : Prop} :
    archiveEntry -> archiveDigest -> archiveAgreement ->
    AyCEWPArchiveManifest archiveEntry archiveDigest archiveAgreement :=
  fun hentry hdigest hagree =>
    ay_cewp_conj_intro hentry (ay_cewp_conj_intro hdigest hagree)

theorem ay_cewp_accepted_projection_intro
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    encodingOk -> mapOk -> witnessOk -> assignmentOk -> replayOk ->
    checkerOk -> fingerprintOk -> buildOk -> archiveOk ->
    AyCEWPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk :=
  fun hencoding hmap hwitness hassignment hreplay hchecker hfingerprint
      hbuild harchive =>
    ay_cewp_conj_intro hencoding
      (ay_cewp_conj_intro hmap
        (ay_cewp_conj_intro hwitness
          (ay_cewp_conj_intro hassignment
            (ay_cewp_conj_intro hreplay
              (ay_cewp_conj_intro hchecker
                (ay_cewp_conj_intro hfingerprint
                  (ay_cewp_conj_intro hbuild harchive)))))))

theorem ay_cewp_accepted_projection_encoding
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyCEWPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    encodingOk :=
  fun h => ay_cewp_conj_left h

theorem ay_cewp_accepted_projection_map
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyCEWPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    mapOk :=
  fun h => ay_cewp_conj_left (ay_cewp_conj_right h)

theorem ay_cewp_accepted_projection_witness
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyCEWPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    witnessOk :=
  fun h => ay_cewp_conj_left (ay_cewp_conj_right (ay_cewp_conj_right h))

theorem ay_cewp_accepted_projection_assignment
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyCEWPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    assignmentOk :=
  fun h =>
    ay_cewp_conj_left
      (ay_cewp_conj_right (ay_cewp_conj_right (ay_cewp_conj_right h)))

theorem ay_cewp_accepted_projection_replay
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyCEWPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    replayOk :=
  fun h =>
    ay_cewp_conj_left
      (ay_cewp_conj_right
        (ay_cewp_conj_right (ay_cewp_conj_right (ay_cewp_conj_right h))))

theorem ay_cewp_accepted_projection_checker
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyCEWPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    checkerOk :=
  fun h =>
    ay_cewp_conj_left
      (ay_cewp_conj_right
        (ay_cewp_conj_right
          (ay_cewp_conj_right (ay_cewp_conj_right (ay_cewp_conj_right h)))))

theorem ay_cewp_accepted_projection_fingerprint
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyCEWPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    fingerprintOk :=
  fun h =>
    ay_cewp_conj_left
      (ay_cewp_conj_right
        (ay_cewp_conj_right
          (ay_cewp_conj_right
            (ay_cewp_conj_right (ay_cewp_conj_right
              (ay_cewp_conj_right h))))))

theorem ay_cewp_accepted_projection_build
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyCEWPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    buildOk :=
  fun h =>
    ay_cewp_conj_left
      (ay_cewp_conj_right
        (ay_cewp_conj_right
          (ay_cewp_conj_right
            (ay_cewp_conj_right
              (ay_cewp_conj_right (ay_cewp_conj_right
                (ay_cewp_conj_right h)))))))

theorem ay_cewp_accepted_projection_archive
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyCEWPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    archiveOk :=
  fun h =>
    ay_cewp_conj_right
      (ay_cewp_conj_right
        (ay_cewp_conj_right
          (ay_cewp_conj_right
            (ay_cewp_conj_right
              (ay_cewp_conj_right (ay_cewp_conj_right
                (ay_cewp_conj_right h)))))))

theorem ay_cewp_public_sat_witness_intro
    {acceptedProjection originalWitness publicSatClaim : Prop} :
    acceptedProjection -> originalWitness -> publicSatClaim ->
    AyCEWPPublicSatWitness acceptedProjection originalWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_cewp_conj_intro hevidence (ay_cewp_conj_intro hwitness hclaim)

theorem ay_cewp_public_sat_witness_evidence
    {acceptedProjection originalWitness publicSatClaim : Prop} :
    AyCEWPPublicSatWitness acceptedProjection originalWitness publicSatClaim ->
    acceptedProjection :=
  fun h => ay_cewp_conj_left h

theorem ay_cewp_public_sat_witness_claim
    {acceptedProjection originalWitness publicSatClaim : Prop} :
    AyCEWPPublicSatWitness acceptedProjection originalWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_cewp_conj_right (ay_cewp_conj_right h)

theorem ay_cewp_accepted_projection_publishes_sound_sat
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyCEWPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    originalWitness -> publicSatClaim ->
    AyCEWPPublicSatWitness
      (AyCEWPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim :=
  ay_cewp_public_sat_witness_intro

theorem ay_cewp_projection_reconstructs_original_assignment
    {encodedTruth originalTruth : Prop} :
    AyCEWPEquisat encodedTruth originalTruth -> encodedTruth -> originalTruth :=
  ay_cewp_equisat_forward

theorem ay_cewp_public_sat_requires_accepted_projection
    {acceptedProjection originalWitness publicSatClaim : Prop} :
    AyCEWPPublicSatWitness acceptedProjection originalWitness publicSatClaim ->
    acceptedProjection :=
  ay_cewp_public_sat_witness_evidence

theorem ay_cewp_publication_requires_encoding
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyCEWPPublicSatWitness
      (AyCEWPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    encodingOk :=
  fun h => ay_cewp_accepted_projection_encoding
    (ay_cewp_public_sat_witness_evidence h)

theorem ay_cewp_publication_requires_map
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyCEWPPublicSatWitness
      (AyCEWPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    mapOk :=
  fun h => ay_cewp_accepted_projection_map
    (ay_cewp_public_sat_witness_evidence h)

theorem ay_cewp_publication_requires_witness
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyCEWPPublicSatWitness
      (AyCEWPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    witnessOk :=
  fun h => ay_cewp_accepted_projection_witness
    (ay_cewp_public_sat_witness_evidence h)

theorem ay_cewp_publication_requires_assignment
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyCEWPPublicSatWitness
      (AyCEWPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    assignmentOk :=
  fun h => ay_cewp_accepted_projection_assignment
    (ay_cewp_public_sat_witness_evidence h)

theorem ay_cewp_publication_requires_replay
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyCEWPPublicSatWitness
      (AyCEWPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    replayOk :=
  fun h => ay_cewp_accepted_projection_replay
    (ay_cewp_public_sat_witness_evidence h)

theorem ay_cewp_publication_requires_checker
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyCEWPPublicSatWitness
      (AyCEWPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    checkerOk :=
  fun h => ay_cewp_accepted_projection_checker
    (ay_cewp_public_sat_witness_evidence h)

theorem ay_cewp_publication_requires_fingerprint
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyCEWPPublicSatWitness
      (AyCEWPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    fingerprintOk :=
  fun h => ay_cewp_accepted_projection_fingerprint
    (ay_cewp_public_sat_witness_evidence h)

theorem ay_cewp_publication_requires_build
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyCEWPPublicSatWitness
      (AyCEWPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    buildOk :=
  fun h => ay_cewp_accepted_projection_build
    (ay_cewp_public_sat_witness_evidence h)

theorem ay_cewp_publication_requires_archive
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyCEWPPublicSatWitness
      (AyCEWPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    archiveOk :=
  fun h => ay_cewp_accepted_projection_archive
    (ay_cewp_public_sat_witness_evidence h)

theorem ay_cewp_no_claim_diagnostic_intro
    {reason blocksPublication : Prop} :
    reason -> blocksPublication ->
    AyCEWPNoClaimDiagnostic reason blocksPublication :=
  ay_cewp_conj_intro

theorem ay_cewp_no_claim_diagnostic_blocks
    {reason blocksPublication : Prop} :
    AyCEWPNoClaimDiagnostic reason blocksPublication -> blocksPublication :=
  ay_cewp_conj_right

theorem ay_cewp_recompute_obligation_intro
    {reason recomputeRequested : Prop} :
    reason -> recomputeRequested ->
    AyCEWPRecomputeObligation reason recomputeRequested :=
  ay_cewp_conj_intro

theorem ay_cewp_recompute_obligation_request
    {reason recomputeRequested : Prop} :
    AyCEWPRecomputeObligation reason recomputeRequested -> recomputeRequested :=
  ay_cewp_conj_right

theorem ay_cewp_encoding_failure_no_claim
    {encodingFailure blocksPublication : Prop} :
    encodingFailure -> blocksPublication ->
    AyCEWPNoClaimDiagnostic encodingFailure blocksPublication :=
  ay_cewp_no_claim_diagnostic_intro

theorem ay_cewp_encoding_failure_recompute
    {encodingFailure recomputeRequested : Prop} :
    encodingFailure -> recomputeRequested ->
    AyCEWPRecomputeObligation encodingFailure recomputeRequested :=
  ay_cewp_recompute_obligation_intro

theorem ay_cewp_map_failure_no_claim
    {mapFailure blocksPublication : Prop} :
    mapFailure -> blocksPublication ->
    AyCEWPNoClaimDiagnostic mapFailure blocksPublication :=
  ay_cewp_no_claim_diagnostic_intro

theorem ay_cewp_witness_failure_no_claim
    {witnessFailure blocksPublication : Prop} :
    witnessFailure -> blocksPublication ->
    AyCEWPNoClaimDiagnostic witnessFailure blocksPublication :=
  ay_cewp_no_claim_diagnostic_intro

theorem ay_cewp_assignment_failure_no_claim
    {assignmentFailure blocksPublication : Prop} :
    assignmentFailure -> blocksPublication ->
    AyCEWPNoClaimDiagnostic assignmentFailure blocksPublication :=
  ay_cewp_no_claim_diagnostic_intro

theorem ay_cewp_replay_failure_no_claim
    {replayFailure blocksPublication : Prop} :
    replayFailure -> blocksPublication ->
    AyCEWPNoClaimDiagnostic replayFailure blocksPublication :=
  ay_cewp_no_claim_diagnostic_intro

theorem ay_cewp_checker_failure_no_claim
    {checkerFailure blocksPublication : Prop} :
    checkerFailure -> blocksPublication ->
    AyCEWPNoClaimDiagnostic checkerFailure blocksPublication :=
  ay_cewp_no_claim_diagnostic_intro

theorem ay_cewp_fingerprint_failure_no_claim
    {fingerprintFailure blocksPublication : Prop} :
    fingerprintFailure -> blocksPublication ->
    AyCEWPNoClaimDiagnostic fingerprintFailure blocksPublication :=
  ay_cewp_no_claim_diagnostic_intro

theorem ay_cewp_build_failure_no_claim
    {buildFailure blocksPublication : Prop} :
    buildFailure -> blocksPublication ->
    AyCEWPNoClaimDiagnostic buildFailure blocksPublication :=
  ay_cewp_no_claim_diagnostic_intro

theorem ay_cewp_archive_failure_no_claim
    {archiveFailure blocksPublication : Prop} :
    archiveFailure -> blocksPublication ->
    AyCEWPNoClaimDiagnostic archiveFailure blocksPublication :=
  ay_cewp_no_claim_diagnostic_intro

theorem ay_cewp_bad_projection_cannot_bless_sat
    {failure blocksPublication recomputeRequested : Prop} :
    AyCEWPNoClaimDiagnostic failure blocksPublication ->
    AyCEWPRecomputeObligation failure recomputeRequested ->
    AyCEWPConj blocksPublication recomputeRequested :=
  fun hdiagnostic hrecompute =>
    ay_cewp_conj_intro
      (ay_cewp_no_claim_diagnostic_blocks hdiagnostic)
      (ay_cewp_recompute_obligation_request hrecompute)
