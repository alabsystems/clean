/- SAT-COMP/ay external extension-map stability guard contract.

This self-contained package models when an external extension map can be used
to reconstruct a public SAT assignment for the original formula.
-/

def AyEEMSConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyEEMSDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyEEMSEquisat (source target : Prop) : Prop :=
  AyEEMSConj (source -> target) (target -> source)

def AyEEMSExternalInternalMaps
    (externalToInternal internalToExternal mapAgreement : Prop) : Prop :=
  AyEEMSConj externalToInternal
    (AyEEMSConj internalToExternal mapAgreement)

def AyEEMSExtensionMapDigest
    (extensionMap extensionDigest digestAgreement : Prop) : Prop :=
  AyEEMSConj extensionMap (AyEEMSConj extensionDigest digestAgreement)

def AyEEMSReconstructionWitnessLedger
    (reconstructionWitness witnessLedger witnessAgreement : Prop) : Prop :=
  AyEEMSConj reconstructionWitness
    (AyEEMSConj witnessLedger witnessAgreement)

def AyEEMSAssignmentDigest
    (internalDigest originalDigest digestAgreement : Prop) : Prop :=
  AyEEMSConj internalDigest (AyEEMSConj originalDigest digestAgreement)

def AyEEMSClauseReplay
    (clauseReplay originalEvaluation replayAgreement : Prop) : Prop :=
  AyEEMSConj clauseReplay (AyEEMSConj originalEvaluation replayAgreement)

def AyEEMSCheckerTranscript
    (checkerAccepted transcript transcriptAgreement : Prop) : Prop :=
  AyEEMSConj checkerAccepted (AyEEMSConj transcript transcriptAgreement)

def AyEEMSFormulaFingerprint
    (originalFingerprint extensionFingerprint fingerprintAgreement : Prop) :
    Prop :=
  AyEEMSConj originalFingerprint
    (AyEEMSConj extensionFingerprint fingerprintAgreement)

def AyEEMSBuildEvidence
    (solverBuild extensionBuild buildAgreement : Prop) : Prop :=
  AyEEMSConj solverBuild (AyEEMSConj extensionBuild buildAgreement)

def AyEEMSArchiveManifest
    (archiveEntry archiveDigest archiveAgreement : Prop) : Prop :=
  AyEEMSConj archiveEntry (AyEEMSConj archiveDigest archiveAgreement)

def AyEEMSAcceptedStableMap
    (mapOk extensionDigestOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop) : Prop :=
  AyEEMSConj mapOk
    (AyEEMSConj extensionDigestOk
      (AyEEMSConj witnessOk
        (AyEEMSConj assignmentOk
          (AyEEMSConj replayOk
            (AyEEMSConj checkerOk
              (AyEEMSConj fingerprintOk
                (AyEEMSConj buildOk archiveOk)))))))

def AyEEMSPublicSatWitness
    (acceptedStableMap originalWitness publicSatClaim : Prop) : Prop :=
  AyEEMSConj acceptedStableMap (AyEEMSConj originalWitness publicSatClaim)

def AyEEMSNoClaimDiagnostic (reason blocksPublication : Prop) : Prop :=
  AyEEMSConj reason blocksPublication

def AyEEMSRecomputeObligation (reason recomputeRequested : Prop) : Prop :=
  AyEEMSConj reason recomputeRequested

theorem ay_eems_conj_intro {left right : Prop} :
    left -> right -> AyEEMSConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_eems_conj_left {left right : Prop} :
    AyEEMSConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_eems_conj_right {left right : Prop} :
    AyEEMSConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_eems_disj_left {left right : Prop} :
    left -> AyEEMSDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_eems_disj_right {left right : Prop} :
    right -> AyEEMSDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_eems_equisat_intro {source target : Prop} :
    (source -> target) -> (target -> source) -> AyEEMSEquisat source target :=
  fun forward backward => ay_eems_conj_intro forward backward

theorem ay_eems_equisat_forward {source target : Prop} :
    AyEEMSEquisat source target -> source -> target :=
  fun h => ay_eems_conj_left h

theorem ay_eems_equisat_backward {source target : Prop} :
    AyEEMSEquisat source target -> target -> source :=
  fun h => ay_eems_conj_right h

theorem ay_eems_external_internal_maps_intro
    {externalToInternal internalToExternal mapAgreement : Prop} :
    externalToInternal -> internalToExternal -> mapAgreement ->
    AyEEMSExternalInternalMaps
      externalToInternal internalToExternal mapAgreement :=
  fun hexternal hinternal hagree =>
    ay_eems_conj_intro hexternal (ay_eems_conj_intro hinternal hagree)

theorem ay_eems_external_internal_maps_external
    {externalToInternal internalToExternal mapAgreement : Prop} :
    AyEEMSExternalInternalMaps
      externalToInternal internalToExternal mapAgreement ->
    externalToInternal :=
  fun h => ay_eems_conj_left h

theorem ay_eems_external_internal_maps_internal
    {externalToInternal internalToExternal mapAgreement : Prop} :
    AyEEMSExternalInternalMaps
      externalToInternal internalToExternal mapAgreement ->
    internalToExternal :=
  fun h => ay_eems_conj_left (ay_eems_conj_right h)

theorem ay_eems_external_internal_maps_agreement
    {externalToInternal internalToExternal mapAgreement : Prop} :
    AyEEMSExternalInternalMaps
      externalToInternal internalToExternal mapAgreement ->
    mapAgreement :=
  fun h => ay_eems_conj_right (ay_eems_conj_right h)

theorem ay_eems_extension_map_digest_intro
    {extensionMap extensionDigest digestAgreement : Prop} :
    extensionMap -> extensionDigest -> digestAgreement ->
    AyEEMSExtensionMapDigest
      extensionMap extensionDigest digestAgreement :=
  fun hmap hdigest hagree =>
    ay_eems_conj_intro hmap (ay_eems_conj_intro hdigest hagree)

theorem ay_eems_reconstruction_witness_ledger_intro
    {reconstructionWitness witnessLedger witnessAgreement : Prop} :
    reconstructionWitness -> witnessLedger -> witnessAgreement ->
    AyEEMSReconstructionWitnessLedger
      reconstructionWitness witnessLedger witnessAgreement :=
  fun hwitness hledger hagree =>
    ay_eems_conj_intro hwitness (ay_eems_conj_intro hledger hagree)

theorem ay_eems_assignment_digest_intro
    {internalDigest originalDigest digestAgreement : Prop} :
    internalDigest -> originalDigest -> digestAgreement ->
    AyEEMSAssignmentDigest internalDigest originalDigest digestAgreement :=
  fun hinternal horiginal hagree =>
    ay_eems_conj_intro hinternal (ay_eems_conj_intro horiginal hagree)

theorem ay_eems_clause_replay_intro
    {clauseReplay originalEvaluation replayAgreement : Prop} :
    clauseReplay -> originalEvaluation -> replayAgreement ->
    AyEEMSClauseReplay clauseReplay originalEvaluation replayAgreement :=
  fun hreplay heval hagree =>
    ay_eems_conj_intro hreplay (ay_eems_conj_intro heval hagree)

theorem ay_eems_checker_transcript_intro
    {checkerAccepted transcript transcriptAgreement : Prop} :
    checkerAccepted -> transcript -> transcriptAgreement ->
    AyEEMSCheckerTranscript checkerAccepted transcript transcriptAgreement :=
  fun haccepted htranscript hagree =>
    ay_eems_conj_intro haccepted (ay_eems_conj_intro htranscript hagree)

theorem ay_eems_formula_fingerprint_intro
    {originalFingerprint extensionFingerprint fingerprintAgreement : Prop} :
    originalFingerprint -> extensionFingerprint -> fingerprintAgreement ->
    AyEEMSFormulaFingerprint
      originalFingerprint extensionFingerprint fingerprintAgreement :=
  fun horiginal hextension hagree =>
    ay_eems_conj_intro horiginal (ay_eems_conj_intro hextension hagree)

theorem ay_eems_build_evidence_intro
    {solverBuild extensionBuild buildAgreement : Prop} :
    solverBuild -> extensionBuild -> buildAgreement ->
    AyEEMSBuildEvidence solverBuild extensionBuild buildAgreement :=
  fun hsolver hextension hagree =>
    ay_eems_conj_intro hsolver (ay_eems_conj_intro hextension hagree)

theorem ay_eems_archive_manifest_intro
    {archiveEntry archiveDigest archiveAgreement : Prop} :
    archiveEntry -> archiveDigest -> archiveAgreement ->
    AyEEMSArchiveManifest archiveEntry archiveDigest archiveAgreement :=
  fun hentry hdigest hagree =>
    ay_eems_conj_intro hentry (ay_eems_conj_intro hdigest hagree)

theorem ay_eems_accepted_stable_map_intro
    {mapOk extensionDigestOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    mapOk -> extensionDigestOk -> witnessOk -> assignmentOk -> replayOk ->
    checkerOk -> fingerprintOk -> buildOk -> archiveOk ->
    AyEEMSAcceptedStableMap mapOk extensionDigestOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk :=
  fun hmap hdigest hwitness hassignment hreplay hchecker hfingerprint
      hbuild harchive =>
    ay_eems_conj_intro hmap
      (ay_eems_conj_intro hdigest
        (ay_eems_conj_intro hwitness
          (ay_eems_conj_intro hassignment
            (ay_eems_conj_intro hreplay
              (ay_eems_conj_intro hchecker
                (ay_eems_conj_intro hfingerprint
                  (ay_eems_conj_intro hbuild harchive)))))))

theorem ay_eems_accepted_stable_map_map
    {mapOk extensionDigestOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyEEMSAcceptedStableMap mapOk extensionDigestOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    mapOk :=
  fun h => ay_eems_conj_left h

theorem ay_eems_accepted_stable_map_extension_digest
    {mapOk extensionDigestOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyEEMSAcceptedStableMap mapOk extensionDigestOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    extensionDigestOk :=
  fun h => ay_eems_conj_left (ay_eems_conj_right h)

theorem ay_eems_accepted_stable_map_witness
    {mapOk extensionDigestOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyEEMSAcceptedStableMap mapOk extensionDigestOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    witnessOk :=
  fun h => ay_eems_conj_left (ay_eems_conj_right (ay_eems_conj_right h))

theorem ay_eems_accepted_stable_map_assignment
    {mapOk extensionDigestOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyEEMSAcceptedStableMap mapOk extensionDigestOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    assignmentOk :=
  fun h =>
    ay_eems_conj_left
      (ay_eems_conj_right (ay_eems_conj_right (ay_eems_conj_right h)))

theorem ay_eems_accepted_stable_map_replay
    {mapOk extensionDigestOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyEEMSAcceptedStableMap mapOk extensionDigestOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    replayOk :=
  fun h =>
    ay_eems_conj_left
      (ay_eems_conj_right
        (ay_eems_conj_right (ay_eems_conj_right (ay_eems_conj_right h))))

theorem ay_eems_accepted_stable_map_checker
    {mapOk extensionDigestOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyEEMSAcceptedStableMap mapOk extensionDigestOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    checkerOk :=
  fun h =>
    ay_eems_conj_left
      (ay_eems_conj_right
        (ay_eems_conj_right
          (ay_eems_conj_right (ay_eems_conj_right (ay_eems_conj_right h)))))

theorem ay_eems_accepted_stable_map_fingerprint
    {mapOk extensionDigestOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyEEMSAcceptedStableMap mapOk extensionDigestOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    fingerprintOk :=
  fun h =>
    ay_eems_conj_left
      (ay_eems_conj_right
        (ay_eems_conj_right
          (ay_eems_conj_right
            (ay_eems_conj_right (ay_eems_conj_right
              (ay_eems_conj_right h))))))

theorem ay_eems_accepted_stable_map_build
    {mapOk extensionDigestOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyEEMSAcceptedStableMap mapOk extensionDigestOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    buildOk :=
  fun h =>
    ay_eems_conj_left
      (ay_eems_conj_right
        (ay_eems_conj_right
          (ay_eems_conj_right
            (ay_eems_conj_right
              (ay_eems_conj_right (ay_eems_conj_right
                (ay_eems_conj_right h)))))))

theorem ay_eems_accepted_stable_map_archive
    {mapOk extensionDigestOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyEEMSAcceptedStableMap mapOk extensionDigestOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    archiveOk :=
  fun h =>
    ay_eems_conj_right
      (ay_eems_conj_right
        (ay_eems_conj_right
          (ay_eems_conj_right
            (ay_eems_conj_right
              (ay_eems_conj_right (ay_eems_conj_right
                (ay_eems_conj_right h)))))))

theorem ay_eems_public_sat_witness_intro
    {acceptedStableMap originalWitness publicSatClaim : Prop} :
    acceptedStableMap -> originalWitness -> publicSatClaim ->
    AyEEMSPublicSatWitness acceptedStableMap originalWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_eems_conj_intro hevidence (ay_eems_conj_intro hwitness hclaim)

theorem ay_eems_public_sat_witness_evidence
    {acceptedStableMap originalWitness publicSatClaim : Prop} :
    AyEEMSPublicSatWitness acceptedStableMap originalWitness publicSatClaim ->
    acceptedStableMap :=
  fun h => ay_eems_conj_left h

theorem ay_eems_public_sat_witness_claim
    {acceptedStableMap originalWitness publicSatClaim : Prop} :
    AyEEMSPublicSatWitness acceptedStableMap originalWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_eems_conj_right (ay_eems_conj_right h)

theorem ay_eems_accepted_stable_map_publishes_sound_sat
    {mapOk extensionDigestOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyEEMSAcceptedStableMap mapOk extensionDigestOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    originalWitness -> publicSatClaim ->
    AyEEMSPublicSatWitness
      (AyEEMSAcceptedStableMap mapOk extensionDigestOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim :=
  ay_eems_public_sat_witness_intro

theorem ay_eems_stable_map_reconstructs_original_assignment
    {internalTruth originalTruth : Prop} :
    AyEEMSEquisat internalTruth originalTruth -> internalTruth -> originalTruth :=
  ay_eems_equisat_forward

theorem ay_eems_public_sat_requires_accepted_stable_map
    {acceptedStableMap originalWitness publicSatClaim : Prop} :
    AyEEMSPublicSatWitness acceptedStableMap originalWitness publicSatClaim ->
    acceptedStableMap :=
  ay_eems_public_sat_witness_evidence

theorem ay_eems_publication_requires_map
    {mapOk extensionDigestOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyEEMSPublicSatWitness
      (AyEEMSAcceptedStableMap mapOk extensionDigestOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    mapOk :=
  fun h => ay_eems_accepted_stable_map_map
    (ay_eems_public_sat_witness_evidence h)

theorem ay_eems_publication_requires_extension_digest
    {mapOk extensionDigestOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyEEMSPublicSatWitness
      (AyEEMSAcceptedStableMap mapOk extensionDigestOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    extensionDigestOk :=
  fun h => ay_eems_accepted_stable_map_extension_digest
    (ay_eems_public_sat_witness_evidence h)

theorem ay_eems_publication_requires_witness
    {mapOk extensionDigestOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyEEMSPublicSatWitness
      (AyEEMSAcceptedStableMap mapOk extensionDigestOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    witnessOk :=
  fun h => ay_eems_accepted_stable_map_witness
    (ay_eems_public_sat_witness_evidence h)

theorem ay_eems_publication_requires_assignment
    {mapOk extensionDigestOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyEEMSPublicSatWitness
      (AyEEMSAcceptedStableMap mapOk extensionDigestOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    assignmentOk :=
  fun h => ay_eems_accepted_stable_map_assignment
    (ay_eems_public_sat_witness_evidence h)

theorem ay_eems_publication_requires_replay
    {mapOk extensionDigestOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyEEMSPublicSatWitness
      (AyEEMSAcceptedStableMap mapOk extensionDigestOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    replayOk :=
  fun h => ay_eems_accepted_stable_map_replay
    (ay_eems_public_sat_witness_evidence h)

theorem ay_eems_publication_requires_checker
    {mapOk extensionDigestOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyEEMSPublicSatWitness
      (AyEEMSAcceptedStableMap mapOk extensionDigestOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    checkerOk :=
  fun h => ay_eems_accepted_stable_map_checker
    (ay_eems_public_sat_witness_evidence h)

theorem ay_eems_publication_requires_fingerprint
    {mapOk extensionDigestOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyEEMSPublicSatWitness
      (AyEEMSAcceptedStableMap mapOk extensionDigestOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    fingerprintOk :=
  fun h => ay_eems_accepted_stable_map_fingerprint
    (ay_eems_public_sat_witness_evidence h)

theorem ay_eems_publication_requires_build
    {mapOk extensionDigestOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyEEMSPublicSatWitness
      (AyEEMSAcceptedStableMap mapOk extensionDigestOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    buildOk :=
  fun h => ay_eems_accepted_stable_map_build
    (ay_eems_public_sat_witness_evidence h)

theorem ay_eems_publication_requires_archive
    {mapOk extensionDigestOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyEEMSPublicSatWitness
      (AyEEMSAcceptedStableMap mapOk extensionDigestOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    archiveOk :=
  fun h => ay_eems_accepted_stable_map_archive
    (ay_eems_public_sat_witness_evidence h)

theorem ay_eems_no_claim_diagnostic_intro
    {reason blocksPublication : Prop} :
    reason -> blocksPublication ->
    AyEEMSNoClaimDiagnostic reason blocksPublication :=
  ay_eems_conj_intro

theorem ay_eems_no_claim_diagnostic_blocks
    {reason blocksPublication : Prop} :
    AyEEMSNoClaimDiagnostic reason blocksPublication -> blocksPublication :=
  ay_eems_conj_right

theorem ay_eems_recompute_obligation_intro
    {reason recomputeRequested : Prop} :
    reason -> recomputeRequested ->
    AyEEMSRecomputeObligation reason recomputeRequested :=
  ay_eems_conj_intro

theorem ay_eems_recompute_obligation_request
    {reason recomputeRequested : Prop} :
    AyEEMSRecomputeObligation reason recomputeRequested -> recomputeRequested :=
  ay_eems_conj_right

theorem ay_eems_map_failure_no_claim
    {mapFailure blocksPublication : Prop} :
    mapFailure -> blocksPublication ->
    AyEEMSNoClaimDiagnostic mapFailure blocksPublication :=
  ay_eems_no_claim_diagnostic_intro

theorem ay_eems_map_failure_recompute
    {mapFailure recomputeRequested : Prop} :
    mapFailure -> recomputeRequested ->
    AyEEMSRecomputeObligation mapFailure recomputeRequested :=
  ay_eems_recompute_obligation_intro

theorem ay_eems_digest_failure_no_claim
    {digestFailure blocksPublication : Prop} :
    digestFailure -> blocksPublication ->
    AyEEMSNoClaimDiagnostic digestFailure blocksPublication :=
  ay_eems_no_claim_diagnostic_intro

theorem ay_eems_witness_failure_no_claim
    {witnessFailure blocksPublication : Prop} :
    witnessFailure -> blocksPublication ->
    AyEEMSNoClaimDiagnostic witnessFailure blocksPublication :=
  ay_eems_no_claim_diagnostic_intro

theorem ay_eems_assignment_failure_no_claim
    {assignmentFailure blocksPublication : Prop} :
    assignmentFailure -> blocksPublication ->
    AyEEMSNoClaimDiagnostic assignmentFailure blocksPublication :=
  ay_eems_no_claim_diagnostic_intro

theorem ay_eems_replay_failure_no_claim
    {replayFailure blocksPublication : Prop} :
    replayFailure -> blocksPublication ->
    AyEEMSNoClaimDiagnostic replayFailure blocksPublication :=
  ay_eems_no_claim_diagnostic_intro

theorem ay_eems_checker_failure_no_claim
    {checkerFailure blocksPublication : Prop} :
    checkerFailure -> blocksPublication ->
    AyEEMSNoClaimDiagnostic checkerFailure blocksPublication :=
  ay_eems_no_claim_diagnostic_intro

theorem ay_eems_fingerprint_failure_no_claim
    {fingerprintFailure blocksPublication : Prop} :
    fingerprintFailure -> blocksPublication ->
    AyEEMSNoClaimDiagnostic fingerprintFailure blocksPublication :=
  ay_eems_no_claim_diagnostic_intro

theorem ay_eems_build_failure_no_claim
    {buildFailure blocksPublication : Prop} :
    buildFailure -> blocksPublication ->
    AyEEMSNoClaimDiagnostic buildFailure blocksPublication :=
  ay_eems_no_claim_diagnostic_intro

theorem ay_eems_archive_failure_no_claim
    {archiveFailure blocksPublication : Prop} :
    archiveFailure -> blocksPublication ->
    AyEEMSNoClaimDiagnostic archiveFailure blocksPublication :=
  ay_eems_no_claim_diagnostic_intro

theorem ay_eems_bad_stable_map_cannot_bless_sat
    {failure blocksPublication recomputeRequested : Prop} :
    AyEEMSNoClaimDiagnostic failure blocksPublication ->
    AyEEMSRecomputeObligation failure recomputeRequested ->
    AyEEMSConj blocksPublication recomputeRequested :=
  fun hdiagnostic hrecompute =>
    ay_eems_conj_intro
      (ay_eems_no_claim_diagnostic_blocks hdiagnostic)
      (ay_eems_recompute_obligation_request hrecompute)
