/- SAT-COMP/ay pseudo-Boolean encoding auxiliary projection guard contract.

This file is self-contained and propositional.  It models when a SAT witness
for a PB encoding may be projected through auxiliary variables back to a public
original-formula SAT assignment.
-/

def AyPEAPConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyPEAPDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyPEAPEquisat (source target : Prop) : Prop :=
  AyPEAPConj (source -> target) (target -> source)

def AyPEAPPBEncodingManifest
    (pbConstraint encodedClauses encodingAgreement : Prop) : Prop :=
  AyPEAPConj pbConstraint (AyPEAPConj encodedClauses encodingAgreement)

def AyPEAPAuxiliaryVariableMap
    (auxiliaryVariables originalVariables mapAgreement : Prop) : Prop :=
  AyPEAPConj auxiliaryVariables
    (AyPEAPConj originalVariables mapAgreement)

def AyPEAPExtensionWitnessLedger
    (extensionWitness witnessLedger witnessAgreement : Prop) : Prop :=
  AyPEAPConj extensionWitness (AyPEAPConj witnessLedger witnessAgreement)

def AyPEAPAssignmentDigest
    (encodedDigest originalDigest digestAgreement : Prop) : Prop :=
  AyPEAPConj encodedDigest (AyPEAPConj originalDigest digestAgreement)

def AyPEAPClauseReplay
    (clauseReplay originalEvaluation replayAgreement : Prop) : Prop :=
  AyPEAPConj clauseReplay (AyPEAPConj originalEvaluation replayAgreement)

def AyPEAPCheckerTranscript
    (checkerAccepted transcript transcriptAgreement : Prop) : Prop :=
  AyPEAPConj checkerAccepted (AyPEAPConj transcript transcriptAgreement)

def AyPEAPFormulaFingerprint
    (originalFingerprint encodingFingerprint fingerprintAgreement : Prop) : Prop :=
  AyPEAPConj originalFingerprint
    (AyPEAPConj encodingFingerprint fingerprintAgreement)

def AyPEAPBuildEvidence
    (solverBuild encodingBuild buildAgreement : Prop) : Prop :=
  AyPEAPConj solverBuild (AyPEAPConj encodingBuild buildAgreement)

def AyPEAPArchiveManifest
    (archiveEntry archiveDigest archiveAgreement : Prop) : Prop :=
  AyPEAPConj archiveEntry (AyPEAPConj archiveDigest archiveAgreement)

def AyPEAPAcceptedProjection
    (encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop) : Prop :=
  AyPEAPConj encodingOk
    (AyPEAPConj mapOk
      (AyPEAPConj witnessOk
        (AyPEAPConj assignmentOk
          (AyPEAPConj replayOk
            (AyPEAPConj checkerOk
              (AyPEAPConj fingerprintOk
                (AyPEAPConj buildOk archiveOk)))))))

def AyPEAPPublicSatWitness
    (acceptedProjection originalWitness publicSatClaim : Prop) : Prop :=
  AyPEAPConj acceptedProjection (AyPEAPConj originalWitness publicSatClaim)

def AyPEAPNoClaimDiagnostic (reason blocksPublication : Prop) : Prop :=
  AyPEAPConj reason blocksPublication

def AyPEAPRecomputeObligation (reason recomputeRequested : Prop) : Prop :=
  AyPEAPConj reason recomputeRequested

theorem ay_peap_conj_intro {left right : Prop} :
    left -> right -> AyPEAPConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_peap_conj_left {left right : Prop} :
    AyPEAPConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_peap_conj_right {left right : Prop} :
    AyPEAPConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_peap_disj_left {left right : Prop} :
    left -> AyPEAPDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_peap_disj_right {left right : Prop} :
    right -> AyPEAPDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_peap_equisat_intro {source target : Prop} :
    (source -> target) -> (target -> source) -> AyPEAPEquisat source target :=
  fun forward backward => ay_peap_conj_intro forward backward

theorem ay_peap_equisat_forward {source target : Prop} :
    AyPEAPEquisat source target -> source -> target :=
  fun h => ay_peap_conj_left h

theorem ay_peap_equisat_backward {source target : Prop} :
    AyPEAPEquisat source target -> target -> source :=
  fun h => ay_peap_conj_right h

theorem ay_peap_pb_encoding_manifest_intro
    {pbConstraint encodedClauses encodingAgreement : Prop} :
    pbConstraint -> encodedClauses -> encodingAgreement ->
    AyPEAPPBEncodingManifest pbConstraint encodedClauses encodingAgreement :=
  fun hpb hencoded hagree =>
    ay_peap_conj_intro hpb (ay_peap_conj_intro hencoded hagree)

theorem ay_peap_pb_encoding_manifest_constraint
    {pbConstraint encodedClauses encodingAgreement : Prop} :
    AyPEAPPBEncodingManifest pbConstraint encodedClauses encodingAgreement ->
    pbConstraint :=
  fun h => ay_peap_conj_left h

theorem ay_peap_pb_encoding_manifest_encoded
    {pbConstraint encodedClauses encodingAgreement : Prop} :
    AyPEAPPBEncodingManifest pbConstraint encodedClauses encodingAgreement ->
    encodedClauses :=
  fun h => ay_peap_conj_left (ay_peap_conj_right h)

theorem ay_peap_pb_encoding_manifest_agreement
    {pbConstraint encodedClauses encodingAgreement : Prop} :
    AyPEAPPBEncodingManifest pbConstraint encodedClauses encodingAgreement ->
    encodingAgreement :=
  fun h => ay_peap_conj_right (ay_peap_conj_right h)

theorem ay_peap_auxiliary_variable_map_intro
    {auxiliaryVariables originalVariables mapAgreement : Prop} :
    auxiliaryVariables -> originalVariables -> mapAgreement ->
    AyPEAPAuxiliaryVariableMap
      auxiliaryVariables originalVariables mapAgreement :=
  fun haux horiginal hagree =>
    ay_peap_conj_intro haux (ay_peap_conj_intro horiginal hagree)

theorem ay_peap_extension_witness_ledger_intro
    {extensionWitness witnessLedger witnessAgreement : Prop} :
    extensionWitness -> witnessLedger -> witnessAgreement ->
    AyPEAPExtensionWitnessLedger
      extensionWitness witnessLedger witnessAgreement :=
  fun hwitness hledger hagree =>
    ay_peap_conj_intro hwitness (ay_peap_conj_intro hledger hagree)

theorem ay_peap_assignment_digest_intro
    {encodedDigest originalDigest digestAgreement : Prop} :
    encodedDigest -> originalDigest -> digestAgreement ->
    AyPEAPAssignmentDigest encodedDigest originalDigest digestAgreement :=
  fun hencoded horiginal hagree =>
    ay_peap_conj_intro hencoded (ay_peap_conj_intro horiginal hagree)

theorem ay_peap_clause_replay_intro
    {clauseReplay originalEvaluation replayAgreement : Prop} :
    clauseReplay -> originalEvaluation -> replayAgreement ->
    AyPEAPClauseReplay clauseReplay originalEvaluation replayAgreement :=
  fun hreplay heval hagree =>
    ay_peap_conj_intro hreplay (ay_peap_conj_intro heval hagree)

theorem ay_peap_checker_transcript_intro
    {checkerAccepted transcript transcriptAgreement : Prop} :
    checkerAccepted -> transcript -> transcriptAgreement ->
    AyPEAPCheckerTranscript checkerAccepted transcript transcriptAgreement :=
  fun haccepted htranscript hagree =>
    ay_peap_conj_intro haccepted (ay_peap_conj_intro htranscript hagree)

theorem ay_peap_formula_fingerprint_intro
    {originalFingerprint encodingFingerprint fingerprintAgreement : Prop} :
    originalFingerprint -> encodingFingerprint -> fingerprintAgreement ->
    AyPEAPFormulaFingerprint
      originalFingerprint encodingFingerprint fingerprintAgreement :=
  fun horiginal hencoding hagree =>
    ay_peap_conj_intro horiginal (ay_peap_conj_intro hencoding hagree)

theorem ay_peap_build_evidence_intro
    {solverBuild encodingBuild buildAgreement : Prop} :
    solverBuild -> encodingBuild -> buildAgreement ->
    AyPEAPBuildEvidence solverBuild encodingBuild buildAgreement :=
  fun hsolver hencoding hagree =>
    ay_peap_conj_intro hsolver (ay_peap_conj_intro hencoding hagree)

theorem ay_peap_archive_manifest_intro
    {archiveEntry archiveDigest archiveAgreement : Prop} :
    archiveEntry -> archiveDigest -> archiveAgreement ->
    AyPEAPArchiveManifest archiveEntry archiveDigest archiveAgreement :=
  fun hentry hdigest hagree =>
    ay_peap_conj_intro hentry (ay_peap_conj_intro hdigest hagree)

theorem ay_peap_accepted_projection_intro
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    encodingOk -> mapOk -> witnessOk -> assignmentOk -> replayOk ->
    checkerOk -> fingerprintOk -> buildOk -> archiveOk ->
    AyPEAPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk :=
  fun hencoding hmap hwitness hassignment hreplay hchecker hfingerprint
      hbuild harchive =>
    ay_peap_conj_intro hencoding
      (ay_peap_conj_intro hmap
        (ay_peap_conj_intro hwitness
          (ay_peap_conj_intro hassignment
            (ay_peap_conj_intro hreplay
              (ay_peap_conj_intro hchecker
                (ay_peap_conj_intro hfingerprint
                  (ay_peap_conj_intro hbuild harchive)))))))

theorem ay_peap_accepted_projection_encoding
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyPEAPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    encodingOk :=
  fun h => ay_peap_conj_left h

theorem ay_peap_accepted_projection_map
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyPEAPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    mapOk :=
  fun h => ay_peap_conj_left (ay_peap_conj_right h)

theorem ay_peap_accepted_projection_witness
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyPEAPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    witnessOk :=
  fun h => ay_peap_conj_left (ay_peap_conj_right (ay_peap_conj_right h))

theorem ay_peap_accepted_projection_assignment
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyPEAPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    assignmentOk :=
  fun h =>
    ay_peap_conj_left
      (ay_peap_conj_right (ay_peap_conj_right (ay_peap_conj_right h)))

theorem ay_peap_accepted_projection_replay
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyPEAPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    replayOk :=
  fun h =>
    ay_peap_conj_left
      (ay_peap_conj_right
        (ay_peap_conj_right (ay_peap_conj_right (ay_peap_conj_right h))))

theorem ay_peap_accepted_projection_checker
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyPEAPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    checkerOk :=
  fun h =>
    ay_peap_conj_left
      (ay_peap_conj_right
        (ay_peap_conj_right
          (ay_peap_conj_right (ay_peap_conj_right (ay_peap_conj_right h)))))

theorem ay_peap_accepted_projection_fingerprint
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyPEAPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    fingerprintOk :=
  fun h =>
    ay_peap_conj_left
      (ay_peap_conj_right
        (ay_peap_conj_right
          (ay_peap_conj_right
            (ay_peap_conj_right (ay_peap_conj_right
              (ay_peap_conj_right h))))))

theorem ay_peap_accepted_projection_build
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyPEAPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    buildOk :=
  fun h =>
    ay_peap_conj_left
      (ay_peap_conj_right
        (ay_peap_conj_right
          (ay_peap_conj_right
            (ay_peap_conj_right
              (ay_peap_conj_right (ay_peap_conj_right
                (ay_peap_conj_right h)))))))

theorem ay_peap_accepted_projection_archive
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyPEAPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    archiveOk :=
  fun h =>
    ay_peap_conj_right
      (ay_peap_conj_right
        (ay_peap_conj_right
          (ay_peap_conj_right
            (ay_peap_conj_right
              (ay_peap_conj_right (ay_peap_conj_right
                (ay_peap_conj_right h)))))))

theorem ay_peap_public_sat_witness_intro
    {acceptedProjection originalWitness publicSatClaim : Prop} :
    acceptedProjection -> originalWitness -> publicSatClaim ->
    AyPEAPPublicSatWitness acceptedProjection originalWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_peap_conj_intro hevidence (ay_peap_conj_intro hwitness hclaim)

theorem ay_peap_public_sat_witness_evidence
    {acceptedProjection originalWitness publicSatClaim : Prop} :
    AyPEAPPublicSatWitness acceptedProjection originalWitness publicSatClaim ->
    acceptedProjection :=
  fun h => ay_peap_conj_left h

theorem ay_peap_public_sat_witness_claim
    {acceptedProjection originalWitness publicSatClaim : Prop} :
    AyPEAPPublicSatWitness acceptedProjection originalWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_peap_conj_right (ay_peap_conj_right h)

theorem ay_peap_accepted_projection_publishes_sound_sat
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyPEAPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    originalWitness -> publicSatClaim ->
    AyPEAPPublicSatWitness
      (AyPEAPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim :=
  ay_peap_public_sat_witness_intro

theorem ay_peap_projection_reconstructs_original_assignment
    {encodedTruth originalTruth : Prop} :
    AyPEAPEquisat encodedTruth originalTruth -> encodedTruth -> originalTruth :=
  ay_peap_equisat_forward

theorem ay_peap_public_sat_requires_accepted_projection
    {acceptedProjection originalWitness publicSatClaim : Prop} :
    AyPEAPPublicSatWitness acceptedProjection originalWitness publicSatClaim ->
    acceptedProjection :=
  ay_peap_public_sat_witness_evidence

theorem ay_peap_publication_requires_encoding
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyPEAPPublicSatWitness
      (AyPEAPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    encodingOk :=
  fun h => ay_peap_accepted_projection_encoding
    (ay_peap_public_sat_witness_evidence h)

theorem ay_peap_publication_requires_map
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyPEAPPublicSatWitness
      (AyPEAPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    mapOk :=
  fun h => ay_peap_accepted_projection_map
    (ay_peap_public_sat_witness_evidence h)

theorem ay_peap_publication_requires_witness
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyPEAPPublicSatWitness
      (AyPEAPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    witnessOk :=
  fun h => ay_peap_accepted_projection_witness
    (ay_peap_public_sat_witness_evidence h)

theorem ay_peap_publication_requires_assignment
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyPEAPPublicSatWitness
      (AyPEAPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    assignmentOk :=
  fun h => ay_peap_accepted_projection_assignment
    (ay_peap_public_sat_witness_evidence h)

theorem ay_peap_publication_requires_replay
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyPEAPPublicSatWitness
      (AyPEAPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    replayOk :=
  fun h => ay_peap_accepted_projection_replay
    (ay_peap_public_sat_witness_evidence h)

theorem ay_peap_publication_requires_checker
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyPEAPPublicSatWitness
      (AyPEAPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    checkerOk :=
  fun h => ay_peap_accepted_projection_checker
    (ay_peap_public_sat_witness_evidence h)

theorem ay_peap_publication_requires_fingerprint
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyPEAPPublicSatWitness
      (AyPEAPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    fingerprintOk :=
  fun h => ay_peap_accepted_projection_fingerprint
    (ay_peap_public_sat_witness_evidence h)

theorem ay_peap_publication_requires_build
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyPEAPPublicSatWitness
      (AyPEAPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    buildOk :=
  fun h => ay_peap_accepted_projection_build
    (ay_peap_public_sat_witness_evidence h)

theorem ay_peap_publication_requires_archive
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyPEAPPublicSatWitness
      (AyPEAPAcceptedProjection encodingOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    archiveOk :=
  fun h => ay_peap_accepted_projection_archive
    (ay_peap_public_sat_witness_evidence h)

theorem ay_peap_no_claim_diagnostic_intro
    {reason blocksPublication : Prop} :
    reason -> blocksPublication ->
    AyPEAPNoClaimDiagnostic reason blocksPublication :=
  ay_peap_conj_intro

theorem ay_peap_no_claim_diagnostic_blocks
    {reason blocksPublication : Prop} :
    AyPEAPNoClaimDiagnostic reason blocksPublication -> blocksPublication :=
  ay_peap_conj_right

theorem ay_peap_recompute_obligation_intro
    {reason recomputeRequested : Prop} :
    reason -> recomputeRequested ->
    AyPEAPRecomputeObligation reason recomputeRequested :=
  ay_peap_conj_intro

theorem ay_peap_recompute_obligation_request
    {reason recomputeRequested : Prop} :
    AyPEAPRecomputeObligation reason recomputeRequested -> recomputeRequested :=
  ay_peap_conj_right

theorem ay_peap_encoding_failure_no_claim
    {encodingFailure blocksPublication : Prop} :
    encodingFailure -> blocksPublication ->
    AyPEAPNoClaimDiagnostic encodingFailure blocksPublication :=
  ay_peap_no_claim_diagnostic_intro

theorem ay_peap_encoding_failure_recompute
    {encodingFailure recomputeRequested : Prop} :
    encodingFailure -> recomputeRequested ->
    AyPEAPRecomputeObligation encodingFailure recomputeRequested :=
  ay_peap_recompute_obligation_intro

theorem ay_peap_map_failure_no_claim
    {mapFailure blocksPublication : Prop} :
    mapFailure -> blocksPublication ->
    AyPEAPNoClaimDiagnostic mapFailure blocksPublication :=
  ay_peap_no_claim_diagnostic_intro

theorem ay_peap_witness_failure_no_claim
    {witnessFailure blocksPublication : Prop} :
    witnessFailure -> blocksPublication ->
    AyPEAPNoClaimDiagnostic witnessFailure blocksPublication :=
  ay_peap_no_claim_diagnostic_intro

theorem ay_peap_assignment_failure_no_claim
    {assignmentFailure blocksPublication : Prop} :
    assignmentFailure -> blocksPublication ->
    AyPEAPNoClaimDiagnostic assignmentFailure blocksPublication :=
  ay_peap_no_claim_diagnostic_intro

theorem ay_peap_replay_failure_no_claim
    {replayFailure blocksPublication : Prop} :
    replayFailure -> blocksPublication ->
    AyPEAPNoClaimDiagnostic replayFailure blocksPublication :=
  ay_peap_no_claim_diagnostic_intro

theorem ay_peap_checker_failure_no_claim
    {checkerFailure blocksPublication : Prop} :
    checkerFailure -> blocksPublication ->
    AyPEAPNoClaimDiagnostic checkerFailure blocksPublication :=
  ay_peap_no_claim_diagnostic_intro

theorem ay_peap_fingerprint_failure_no_claim
    {fingerprintFailure blocksPublication : Prop} :
    fingerprintFailure -> blocksPublication ->
    AyPEAPNoClaimDiagnostic fingerprintFailure blocksPublication :=
  ay_peap_no_claim_diagnostic_intro

theorem ay_peap_build_failure_no_claim
    {buildFailure blocksPublication : Prop} :
    buildFailure -> blocksPublication ->
    AyPEAPNoClaimDiagnostic buildFailure blocksPublication :=
  ay_peap_no_claim_diagnostic_intro

theorem ay_peap_archive_failure_no_claim
    {archiveFailure blocksPublication : Prop} :
    archiveFailure -> blocksPublication ->
    AyPEAPNoClaimDiagnostic archiveFailure blocksPublication :=
  ay_peap_no_claim_diagnostic_intro

theorem ay_peap_bad_projection_cannot_bless_sat
    {failure blocksPublication recomputeRequested : Prop} :
    AyPEAPNoClaimDiagnostic failure blocksPublication ->
    AyPEAPRecomputeObligation failure recomputeRequested ->
    AyPEAPConj blocksPublication recomputeRequested :=
  fun hdiagnostic hrecompute =>
    ay_peap_conj_intro
      (ay_peap_no_claim_diagnostic_blocks hdiagnostic)
      (ay_peap_recompute_obligation_request hrecompute)
