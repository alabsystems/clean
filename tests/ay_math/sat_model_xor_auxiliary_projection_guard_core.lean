/- SAT-COMP/ay XOR auxiliary projection guard contract.

This self-contained package models SAT model publication through XOR/Gaussian
elimination encodings.  Projection to the original formula is accepted only
when encoding, auxiliary map, extension, digest, replay, checker, fingerprint,
build, and archive evidence all agree.
-/

def AyXAPGConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyXAPGDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyXAPGEquisat (source target : Prop) : Prop :=
  AyXAPGConj (source -> target) (target -> source)

def AyXAPGXorEncodingManifest
    (xorSystem encodedClauses encodingAgreement : Prop) : Prop :=
  AyXAPGConj xorSystem (AyXAPGConj encodedClauses encodingAgreement)

def AyXAPGAuxiliaryVariableMap
    (auxiliaryVariables originalVariables mapAgreement : Prop) : Prop :=
  AyXAPGConj auxiliaryVariables
    (AyXAPGConj originalVariables mapAgreement)

def AyXAPGExtensionWitnessLedger
    (extensionWitness witnessLedger witnessAgreement : Prop) : Prop :=
  AyXAPGConj extensionWitness (AyXAPGConj witnessLedger witnessAgreement)

def AyXAPGAssignmentDigest
    (encodedDigest originalDigest digestAgreement : Prop) : Prop :=
  AyXAPGConj encodedDigest (AyXAPGConj originalDigest digestAgreement)

def AyXAPGClauseReplay
    (clauseReplay originalEvaluation replayAgreement : Prop) : Prop :=
  AyXAPGConj clauseReplay (AyXAPGConj originalEvaluation replayAgreement)

def AyXAPGCheckerTranscript
    (checkerAccepted transcript transcriptAgreement : Prop) : Prop :=
  AyXAPGConj checkerAccepted (AyXAPGConj transcript transcriptAgreement)

def AyXAPGFormulaFingerprint
    (originalFingerprint encodingFingerprint fingerprintAgreement : Prop) : Prop :=
  AyXAPGConj originalFingerprint
    (AyXAPGConj encodingFingerprint fingerprintAgreement)

def AyXAPGBuildEvidence
    (solverBuild encodingBuild buildAgreement : Prop) : Prop :=
  AyXAPGConj solverBuild (AyXAPGConj encodingBuild buildAgreement)

def AyXAPGArchiveManifest
    (archiveEntry archiveDigest archiveAgreement : Prop) : Prop :=
  AyXAPGConj archiveEntry (AyXAPGConj archiveDigest archiveAgreement)

def AyXAPGAcceptedProjection
    (encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop) : Prop :=
  AyXAPGConj encodingOk
    (AyXAPGConj mapOk
      (AyXAPGConj witnessOk
        (AyXAPGConj assignmentOk
          (AyXAPGConj replayOk
            (AyXAPGConj checkerOk
              (AyXAPGConj fingerprintOk
                (AyXAPGConj buildOk archiveOk)))))))

def AyXAPGPublicSatWitness
    (acceptedProjection originalWitness publicSatClaim : Prop) : Prop :=
  AyXAPGConj acceptedProjection (AyXAPGConj originalWitness publicSatClaim)

def AyXAPGNoClaimDiagnostic (reason blocksPublication : Prop) : Prop :=
  AyXAPGConj reason blocksPublication

def AyXAPGRecomputeObligation (reason recomputeRequested : Prop) : Prop :=
  AyXAPGConj reason recomputeRequested

theorem ay_xapg_conj_intro {left right : Prop} :
    left -> right -> AyXAPGConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_xapg_conj_left {left right : Prop} :
    AyXAPGConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_xapg_conj_right {left right : Prop} :
    AyXAPGConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_xapg_disj_left {left right : Prop} :
    left -> AyXAPGDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_xapg_disj_right {left right : Prop} :
    right -> AyXAPGDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_xapg_equisat_intro {source target : Prop} :
    (source -> target) -> (target -> source) -> AyXAPGEquisat source target :=
  fun forward backward => ay_xapg_conj_intro forward backward

theorem ay_xapg_equisat_forward {source target : Prop} :
    AyXAPGEquisat source target -> source -> target :=
  fun h => ay_xapg_conj_left h

theorem ay_xapg_equisat_backward {source target : Prop} :
    AyXAPGEquisat source target -> target -> source :=
  fun h => ay_xapg_conj_right h

theorem ay_xapg_xor_encoding_manifest_intro
    {xorSystem encodedClauses encodingAgreement : Prop} :
    xorSystem -> encodedClauses -> encodingAgreement ->
    AyXAPGXorEncodingManifest xorSystem encodedClauses encodingAgreement :=
  fun hxor hencoded hagree =>
    ay_xapg_conj_intro hxor (ay_xapg_conj_intro hencoded hagree)

theorem ay_xapg_xor_encoding_manifest_system
    {xorSystem encodedClauses encodingAgreement : Prop} :
    AyXAPGXorEncodingManifest xorSystem encodedClauses encodingAgreement ->
    xorSystem :=
  fun h => ay_xapg_conj_left h

theorem ay_xapg_xor_encoding_manifest_encoded
    {xorSystem encodedClauses encodingAgreement : Prop} :
    AyXAPGXorEncodingManifest xorSystem encodedClauses encodingAgreement ->
    encodedClauses :=
  fun h => ay_xapg_conj_left (ay_xapg_conj_right h)

theorem ay_xapg_xor_encoding_manifest_agreement
    {xorSystem encodedClauses encodingAgreement : Prop} :
    AyXAPGXorEncodingManifest xorSystem encodedClauses encodingAgreement ->
    encodingAgreement :=
  fun h => ay_xapg_conj_right (ay_xapg_conj_right h)

theorem ay_xapg_auxiliary_variable_map_intro
    {auxiliaryVariables originalVariables mapAgreement : Prop} :
    auxiliaryVariables -> originalVariables -> mapAgreement ->
    AyXAPGAuxiliaryVariableMap
      auxiliaryVariables originalVariables mapAgreement :=
  fun haux horiginal hagree =>
    ay_xapg_conj_intro haux (ay_xapg_conj_intro horiginal hagree)

theorem ay_xapg_extension_witness_ledger_intro
    {extensionWitness witnessLedger witnessAgreement : Prop} :
    extensionWitness -> witnessLedger -> witnessAgreement ->
    AyXAPGExtensionWitnessLedger
      extensionWitness witnessLedger witnessAgreement :=
  fun hwitness hledger hagree =>
    ay_xapg_conj_intro hwitness (ay_xapg_conj_intro hledger hagree)

theorem ay_xapg_assignment_digest_intro
    {encodedDigest originalDigest digestAgreement : Prop} :
    encodedDigest -> originalDigest -> digestAgreement ->
    AyXAPGAssignmentDigest encodedDigest originalDigest digestAgreement :=
  fun hencoded horiginal hagree =>
    ay_xapg_conj_intro hencoded (ay_xapg_conj_intro horiginal hagree)

theorem ay_xapg_clause_replay_intro
    {clauseReplay originalEvaluation replayAgreement : Prop} :
    clauseReplay -> originalEvaluation -> replayAgreement ->
    AyXAPGClauseReplay clauseReplay originalEvaluation replayAgreement :=
  fun hreplay heval hagree =>
    ay_xapg_conj_intro hreplay (ay_xapg_conj_intro heval hagree)

theorem ay_xapg_checker_transcript_intro
    {checkerAccepted transcript transcriptAgreement : Prop} :
    checkerAccepted -> transcript -> transcriptAgreement ->
    AyXAPGCheckerTranscript checkerAccepted transcript transcriptAgreement :=
  fun haccepted htranscript hagree =>
    ay_xapg_conj_intro haccepted (ay_xapg_conj_intro htranscript hagree)

theorem ay_xapg_formula_fingerprint_intro
    {originalFingerprint encodingFingerprint fingerprintAgreement : Prop} :
    originalFingerprint -> encodingFingerprint -> fingerprintAgreement ->
    AyXAPGFormulaFingerprint
      originalFingerprint encodingFingerprint fingerprintAgreement :=
  fun horiginal hencoding hagree =>
    ay_xapg_conj_intro horiginal (ay_xapg_conj_intro hencoding hagree)

theorem ay_xapg_build_evidence_intro
    {solverBuild encodingBuild buildAgreement : Prop} :
    solverBuild -> encodingBuild -> buildAgreement ->
    AyXAPGBuildEvidence solverBuild encodingBuild buildAgreement :=
  fun hsolver hencoding hagree =>
    ay_xapg_conj_intro hsolver (ay_xapg_conj_intro hencoding hagree)

theorem ay_xapg_archive_manifest_intro
    {archiveEntry archiveDigest archiveAgreement : Prop} :
    archiveEntry -> archiveDigest -> archiveAgreement ->
    AyXAPGArchiveManifest archiveEntry archiveDigest archiveAgreement :=
  fun hentry hdigest hagree =>
    ay_xapg_conj_intro hentry (ay_xapg_conj_intro hdigest hagree)

theorem ay_xapg_accepted_projection_intro
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    encodingOk -> mapOk -> witnessOk -> assignmentOk -> replayOk ->
    checkerOk -> fingerprintOk -> buildOk -> archiveOk ->
    AyXAPGAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk :=
  fun hencoding hmap hwitness hassignment hreplay hchecker hfingerprint
      hbuild harchive =>
    ay_xapg_conj_intro hencoding
      (ay_xapg_conj_intro hmap
        (ay_xapg_conj_intro hwitness
          (ay_xapg_conj_intro hassignment
            (ay_xapg_conj_intro hreplay
              (ay_xapg_conj_intro hchecker
                (ay_xapg_conj_intro hfingerprint
                  (ay_xapg_conj_intro hbuild harchive)))))))

theorem ay_xapg_accepted_projection_encoding
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyXAPGAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    encodingOk :=
  fun h => ay_xapg_conj_left h

theorem ay_xapg_accepted_projection_map
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyXAPGAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    mapOk :=
  fun h => ay_xapg_conj_left (ay_xapg_conj_right h)

theorem ay_xapg_accepted_projection_witness
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyXAPGAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    witnessOk :=
  fun h => ay_xapg_conj_left (ay_xapg_conj_right (ay_xapg_conj_right h))

theorem ay_xapg_accepted_projection_assignment
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyXAPGAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    assignmentOk :=
  fun h =>
    ay_xapg_conj_left
      (ay_xapg_conj_right (ay_xapg_conj_right (ay_xapg_conj_right h)))

theorem ay_xapg_accepted_projection_replay
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyXAPGAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    replayOk :=
  fun h =>
    ay_xapg_conj_left
      (ay_xapg_conj_right
        (ay_xapg_conj_right (ay_xapg_conj_right (ay_xapg_conj_right h))))

theorem ay_xapg_accepted_projection_checker
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyXAPGAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    checkerOk :=
  fun h =>
    ay_xapg_conj_left
      (ay_xapg_conj_right
        (ay_xapg_conj_right
          (ay_xapg_conj_right (ay_xapg_conj_right (ay_xapg_conj_right h)))))

theorem ay_xapg_accepted_projection_fingerprint
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyXAPGAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    fingerprintOk :=
  fun h =>
    ay_xapg_conj_left
      (ay_xapg_conj_right
        (ay_xapg_conj_right
          (ay_xapg_conj_right
            (ay_xapg_conj_right (ay_xapg_conj_right
              (ay_xapg_conj_right h))))))

theorem ay_xapg_accepted_projection_build
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyXAPGAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    buildOk :=
  fun h =>
    ay_xapg_conj_left
      (ay_xapg_conj_right
        (ay_xapg_conj_right
          (ay_xapg_conj_right
            (ay_xapg_conj_right
              (ay_xapg_conj_right (ay_xapg_conj_right
                (ay_xapg_conj_right h)))))))

theorem ay_xapg_accepted_projection_archive
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyXAPGAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    archiveOk :=
  fun h =>
    ay_xapg_conj_right
      (ay_xapg_conj_right
        (ay_xapg_conj_right
          (ay_xapg_conj_right
            (ay_xapg_conj_right
              (ay_xapg_conj_right (ay_xapg_conj_right
                (ay_xapg_conj_right h)))))))

theorem ay_xapg_public_sat_witness_intro
    {acceptedProjection originalWitness publicSatClaim : Prop} :
    acceptedProjection -> originalWitness -> publicSatClaim ->
    AyXAPGPublicSatWitness acceptedProjection originalWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_xapg_conj_intro hevidence (ay_xapg_conj_intro hwitness hclaim)

theorem ay_xapg_public_sat_witness_evidence
    {acceptedProjection originalWitness publicSatClaim : Prop} :
    AyXAPGPublicSatWitness acceptedProjection originalWitness publicSatClaim ->
    acceptedProjection :=
  fun h => ay_xapg_conj_left h

theorem ay_xapg_public_sat_witness_claim
    {acceptedProjection originalWitness publicSatClaim : Prop} :
    AyXAPGPublicSatWitness acceptedProjection originalWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_xapg_conj_right (ay_xapg_conj_right h)

theorem ay_xapg_accepted_projection_publishes_sound_sat
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyXAPGAcceptedProjection encodingOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    originalWitness -> publicSatClaim ->
    AyXAPGPublicSatWitness
      (AyXAPGAcceptedProjection encodingOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim :=
  ay_xapg_public_sat_witness_intro

theorem ay_xapg_projection_reconstructs_original_assignment
    {encodedTruth originalTruth : Prop} :
    AyXAPGEquisat encodedTruth originalTruth -> encodedTruth -> originalTruth :=
  ay_xapg_equisat_forward

theorem ay_xapg_public_sat_requires_accepted_projection
    {acceptedProjection originalWitness publicSatClaim : Prop} :
    AyXAPGPublicSatWitness acceptedProjection originalWitness publicSatClaim ->
    acceptedProjection :=
  ay_xapg_public_sat_witness_evidence

theorem ay_xapg_publication_requires_encoding
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyXAPGPublicSatWitness
      (AyXAPGAcceptedProjection encodingOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    encodingOk :=
  fun h => ay_xapg_accepted_projection_encoding
    (ay_xapg_public_sat_witness_evidence h)

theorem ay_xapg_publication_requires_map
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyXAPGPublicSatWitness
      (AyXAPGAcceptedProjection encodingOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    mapOk :=
  fun h => ay_xapg_accepted_projection_map
    (ay_xapg_public_sat_witness_evidence h)

theorem ay_xapg_publication_requires_witness
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyXAPGPublicSatWitness
      (AyXAPGAcceptedProjection encodingOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    witnessOk :=
  fun h => ay_xapg_accepted_projection_witness
    (ay_xapg_public_sat_witness_evidence h)

theorem ay_xapg_publication_requires_assignment
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyXAPGPublicSatWitness
      (AyXAPGAcceptedProjection encodingOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    assignmentOk :=
  fun h => ay_xapg_accepted_projection_assignment
    (ay_xapg_public_sat_witness_evidence h)

theorem ay_xapg_publication_requires_replay
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyXAPGPublicSatWitness
      (AyXAPGAcceptedProjection encodingOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    replayOk :=
  fun h => ay_xapg_accepted_projection_replay
    (ay_xapg_public_sat_witness_evidence h)

theorem ay_xapg_publication_requires_checker
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyXAPGPublicSatWitness
      (AyXAPGAcceptedProjection encodingOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    checkerOk :=
  fun h => ay_xapg_accepted_projection_checker
    (ay_xapg_public_sat_witness_evidence h)

theorem ay_xapg_publication_requires_fingerprint
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyXAPGPublicSatWitness
      (AyXAPGAcceptedProjection encodingOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    fingerprintOk :=
  fun h => ay_xapg_accepted_projection_fingerprint
    (ay_xapg_public_sat_witness_evidence h)

theorem ay_xapg_publication_requires_build
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyXAPGPublicSatWitness
      (AyXAPGAcceptedProjection encodingOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    buildOk :=
  fun h => ay_xapg_accepted_projection_build
    (ay_xapg_public_sat_witness_evidence h)

theorem ay_xapg_publication_requires_archive
    {encodingOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyXAPGPublicSatWitness
      (AyXAPGAcceptedProjection encodingOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    archiveOk :=
  fun h => ay_xapg_accepted_projection_archive
    (ay_xapg_public_sat_witness_evidence h)

theorem ay_xapg_no_claim_diagnostic_intro
    {reason blocksPublication : Prop} :
    reason -> blocksPublication ->
    AyXAPGNoClaimDiagnostic reason blocksPublication :=
  ay_xapg_conj_intro

theorem ay_xapg_no_claim_diagnostic_blocks
    {reason blocksPublication : Prop} :
    AyXAPGNoClaimDiagnostic reason blocksPublication -> blocksPublication :=
  ay_xapg_conj_right

theorem ay_xapg_recompute_obligation_intro
    {reason recomputeRequested : Prop} :
    reason -> recomputeRequested ->
    AyXAPGRecomputeObligation reason recomputeRequested :=
  ay_xapg_conj_intro

theorem ay_xapg_recompute_obligation_request
    {reason recomputeRequested : Prop} :
    AyXAPGRecomputeObligation reason recomputeRequested -> recomputeRequested :=
  ay_xapg_conj_right

theorem ay_xapg_encoding_failure_no_claim
    {encodingFailure blocksPublication : Prop} :
    encodingFailure -> blocksPublication ->
    AyXAPGNoClaimDiagnostic encodingFailure blocksPublication :=
  ay_xapg_no_claim_diagnostic_intro

theorem ay_xapg_encoding_failure_recompute
    {encodingFailure recomputeRequested : Prop} :
    encodingFailure -> recomputeRequested ->
    AyXAPGRecomputeObligation encodingFailure recomputeRequested :=
  ay_xapg_recompute_obligation_intro

theorem ay_xapg_map_failure_no_claim
    {mapFailure blocksPublication : Prop} :
    mapFailure -> blocksPublication ->
    AyXAPGNoClaimDiagnostic mapFailure blocksPublication :=
  ay_xapg_no_claim_diagnostic_intro

theorem ay_xapg_witness_failure_no_claim
    {witnessFailure blocksPublication : Prop} :
    witnessFailure -> blocksPublication ->
    AyXAPGNoClaimDiagnostic witnessFailure blocksPublication :=
  ay_xapg_no_claim_diagnostic_intro

theorem ay_xapg_assignment_failure_no_claim
    {assignmentFailure blocksPublication : Prop} :
    assignmentFailure -> blocksPublication ->
    AyXAPGNoClaimDiagnostic assignmentFailure blocksPublication :=
  ay_xapg_no_claim_diagnostic_intro

theorem ay_xapg_replay_failure_no_claim
    {replayFailure blocksPublication : Prop} :
    replayFailure -> blocksPublication ->
    AyXAPGNoClaimDiagnostic replayFailure blocksPublication :=
  ay_xapg_no_claim_diagnostic_intro

theorem ay_xapg_checker_failure_no_claim
    {checkerFailure blocksPublication : Prop} :
    checkerFailure -> blocksPublication ->
    AyXAPGNoClaimDiagnostic checkerFailure blocksPublication :=
  ay_xapg_no_claim_diagnostic_intro

theorem ay_xapg_fingerprint_failure_no_claim
    {fingerprintFailure blocksPublication : Prop} :
    fingerprintFailure -> blocksPublication ->
    AyXAPGNoClaimDiagnostic fingerprintFailure blocksPublication :=
  ay_xapg_no_claim_diagnostic_intro

theorem ay_xapg_build_failure_no_claim
    {buildFailure blocksPublication : Prop} :
    buildFailure -> blocksPublication ->
    AyXAPGNoClaimDiagnostic buildFailure blocksPublication :=
  ay_xapg_no_claim_diagnostic_intro

theorem ay_xapg_archive_failure_no_claim
    {archiveFailure blocksPublication : Prop} :
    archiveFailure -> blocksPublication ->
    AyXAPGNoClaimDiagnostic archiveFailure blocksPublication :=
  ay_xapg_no_claim_diagnostic_intro

theorem ay_xapg_bad_projection_cannot_bless_sat
    {failure blocksPublication recomputeRequested : Prop} :
    AyXAPGNoClaimDiagnostic failure blocksPublication ->
    AyXAPGRecomputeObligation failure recomputeRequested ->
    AyXAPGConj blocksPublication recomputeRequested :=
  fun hdiagnostic hrecompute =>
    ay_xapg_conj_intro
      (ay_xapg_no_claim_diagnostic_blocks hdiagnostic)
      (ay_xapg_recompute_obligation_request hrecompute)
