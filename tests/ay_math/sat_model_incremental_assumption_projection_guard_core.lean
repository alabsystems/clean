/- SAT-COMP/ay incremental assumption projection guard contract.

This self-contained package models SAT model publication under incremental
assumptions.  A projected witness may be published only when assumption,
projection, extension, digest, replay, checker, fingerprint, build, and archive
evidence all agree.
-/

def AyIAPGConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyIAPGDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyIAPGEquisat (source target : Prop) : Prop :=
  AyIAPGConj (source -> target) (target -> source)

def AyIAPGAssumptionManifest
    (incrementalFrame assumptionLiterals assumptionAgreement : Prop) : Prop :=
  AyIAPGConj incrementalFrame
    (AyIAPGConj assumptionLiterals assumptionAgreement)

def AyIAPGProjectionMap
    (assumptionToOriginal originalToAssumption mapAgreement : Prop) : Prop :=
  AyIAPGConj assumptionToOriginal
    (AyIAPGConj originalToAssumption mapAgreement)

def AyIAPGExtensionWitnessLedger
    (extensionWitness extensionLedger extensionAgreement : Prop) : Prop :=
  AyIAPGConj extensionWitness
    (AyIAPGConj extensionLedger extensionAgreement)

def AyIAPGAssignmentDigest
    (assumptionDigest originalDigest digestAgreement : Prop) : Prop :=
  AyIAPGConj assumptionDigest (AyIAPGConj originalDigest digestAgreement)

def AyIAPGClauseReplay
    (clauseReplay originalEvaluation replayAgreement : Prop) : Prop :=
  AyIAPGConj clauseReplay (AyIAPGConj originalEvaluation replayAgreement)

def AyIAPGCheckerTranscript
    (checkerAccepted transcript transcriptAgreement : Prop) : Prop :=
  AyIAPGConj checkerAccepted (AyIAPGConj transcript transcriptAgreement)

def AyIAPGFormulaFingerprint
    (originalFingerprint assumptionFingerprint fingerprintAgreement : Prop) :
    Prop :=
  AyIAPGConj originalFingerprint
    (AyIAPGConj assumptionFingerprint fingerprintAgreement)

def AyIAPGBuildEvidence
    (solverBuild assumptionBuild buildAgreement : Prop) : Prop :=
  AyIAPGConj solverBuild (AyIAPGConj assumptionBuild buildAgreement)

def AyIAPGArchiveManifest
    (archiveEntry archiveDigest archiveAgreement : Prop) : Prop :=
  AyIAPGConj archiveEntry (AyIAPGConj archiveDigest archiveAgreement)

def AyIAPGAcceptedProjection
    (assumptionOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop) : Prop :=
  AyIAPGConj assumptionOk
    (AyIAPGConj mapOk
      (AyIAPGConj witnessOk
        (AyIAPGConj assignmentOk
          (AyIAPGConj replayOk
            (AyIAPGConj checkerOk
              (AyIAPGConj fingerprintOk
                (AyIAPGConj buildOk archiveOk)))))))

def AyIAPGPublicSatWitness
    (acceptedProjection originalWitness publicSatClaim : Prop) : Prop :=
  AyIAPGConj acceptedProjection (AyIAPGConj originalWitness publicSatClaim)

def AyIAPGNoClaimDiagnostic (reason blocksPublication : Prop) : Prop :=
  AyIAPGConj reason blocksPublication

def AyIAPGRecomputeObligation (reason recomputeRequested : Prop) : Prop :=
  AyIAPGConj reason recomputeRequested

theorem ay_iapg_conj_intro {left right : Prop} :
    left -> right -> AyIAPGConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_iapg_conj_left {left right : Prop} :
    AyIAPGConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_iapg_conj_right {left right : Prop} :
    AyIAPGConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_iapg_disj_left {left right : Prop} :
    left -> AyIAPGDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_iapg_disj_right {left right : Prop} :
    right -> AyIAPGDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_iapg_equisat_intro {source target : Prop} :
    (source -> target) -> (target -> source) -> AyIAPGEquisat source target :=
  fun forward backward => ay_iapg_conj_intro forward backward

theorem ay_iapg_equisat_forward {source target : Prop} :
    AyIAPGEquisat source target -> source -> target :=
  fun h => ay_iapg_conj_left h

theorem ay_iapg_equisat_backward {source target : Prop} :
    AyIAPGEquisat source target -> target -> source :=
  fun h => ay_iapg_conj_right h

theorem ay_iapg_assumption_manifest_intro
    {incrementalFrame assumptionLiterals assumptionAgreement : Prop} :
    incrementalFrame -> assumptionLiterals -> assumptionAgreement ->
    AyIAPGAssumptionManifest
      incrementalFrame assumptionLiterals assumptionAgreement :=
  fun hframe hlits hagree =>
    ay_iapg_conj_intro hframe (ay_iapg_conj_intro hlits hagree)

theorem ay_iapg_assumption_manifest_frame
    {incrementalFrame assumptionLiterals assumptionAgreement : Prop} :
    AyIAPGAssumptionManifest
      incrementalFrame assumptionLiterals assumptionAgreement ->
    incrementalFrame :=
  fun h => ay_iapg_conj_left h

theorem ay_iapg_assumption_manifest_literals
    {incrementalFrame assumptionLiterals assumptionAgreement : Prop} :
    AyIAPGAssumptionManifest
      incrementalFrame assumptionLiterals assumptionAgreement ->
    assumptionLiterals :=
  fun h => ay_iapg_conj_left (ay_iapg_conj_right h)

theorem ay_iapg_assumption_manifest_agreement
    {incrementalFrame assumptionLiterals assumptionAgreement : Prop} :
    AyIAPGAssumptionManifest
      incrementalFrame assumptionLiterals assumptionAgreement ->
    assumptionAgreement :=
  fun h => ay_iapg_conj_right (ay_iapg_conj_right h)

theorem ay_iapg_projection_map_intro
    {assumptionToOriginal originalToAssumption mapAgreement : Prop} :
    assumptionToOriginal -> originalToAssumption -> mapAgreement ->
    AyIAPGProjectionMap assumptionToOriginal originalToAssumption mapAgreement :=
  fun hforward hbackward hagree =>
    ay_iapg_conj_intro hforward (ay_iapg_conj_intro hbackward hagree)

theorem ay_iapg_extension_witness_ledger_intro
    {extensionWitness extensionLedger extensionAgreement : Prop} :
    extensionWitness -> extensionLedger -> extensionAgreement ->
    AyIAPGExtensionWitnessLedger
      extensionWitness extensionLedger extensionAgreement :=
  fun hwitness hledger hagree =>
    ay_iapg_conj_intro hwitness (ay_iapg_conj_intro hledger hagree)

theorem ay_iapg_assignment_digest_intro
    {assumptionDigest originalDigest digestAgreement : Prop} :
    assumptionDigest -> originalDigest -> digestAgreement ->
    AyIAPGAssignmentDigest assumptionDigest originalDigest digestAgreement :=
  fun hassumption horiginal hagree =>
    ay_iapg_conj_intro hassumption (ay_iapg_conj_intro horiginal hagree)

theorem ay_iapg_clause_replay_intro
    {clauseReplay originalEvaluation replayAgreement : Prop} :
    clauseReplay -> originalEvaluation -> replayAgreement ->
    AyIAPGClauseReplay clauseReplay originalEvaluation replayAgreement :=
  fun hreplay heval hagree =>
    ay_iapg_conj_intro hreplay (ay_iapg_conj_intro heval hagree)

theorem ay_iapg_checker_transcript_intro
    {checkerAccepted transcript transcriptAgreement : Prop} :
    checkerAccepted -> transcript -> transcriptAgreement ->
    AyIAPGCheckerTranscript checkerAccepted transcript transcriptAgreement :=
  fun haccepted htranscript hagree =>
    ay_iapg_conj_intro haccepted (ay_iapg_conj_intro htranscript hagree)

theorem ay_iapg_formula_fingerprint_intro
    {originalFingerprint assumptionFingerprint fingerprintAgreement : Prop} :
    originalFingerprint -> assumptionFingerprint -> fingerprintAgreement ->
    AyIAPGFormulaFingerprint
      originalFingerprint assumptionFingerprint fingerprintAgreement :=
  fun horiginal hassumption hagree =>
    ay_iapg_conj_intro horiginal (ay_iapg_conj_intro hassumption hagree)

theorem ay_iapg_build_evidence_intro
    {solverBuild assumptionBuild buildAgreement : Prop} :
    solverBuild -> assumptionBuild -> buildAgreement ->
    AyIAPGBuildEvidence solverBuild assumptionBuild buildAgreement :=
  fun hsolver hassumption hagree =>
    ay_iapg_conj_intro hsolver (ay_iapg_conj_intro hassumption hagree)

theorem ay_iapg_archive_manifest_intro
    {archiveEntry archiveDigest archiveAgreement : Prop} :
    archiveEntry -> archiveDigest -> archiveAgreement ->
    AyIAPGArchiveManifest archiveEntry archiveDigest archiveAgreement :=
  fun hentry hdigest hagree =>
    ay_iapg_conj_intro hentry (ay_iapg_conj_intro hdigest hagree)

theorem ay_iapg_accepted_projection_intro
    {assumptionOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    assumptionOk -> mapOk -> witnessOk -> assignmentOk -> replayOk ->
    checkerOk -> fingerprintOk -> buildOk -> archiveOk ->
    AyIAPGAcceptedProjection assumptionOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk :=
  fun hassumption hmap hwitness hassignment hreplay hchecker hfingerprint
      hbuild harchive =>
    ay_iapg_conj_intro hassumption
      (ay_iapg_conj_intro hmap
        (ay_iapg_conj_intro hwitness
          (ay_iapg_conj_intro hassignment
            (ay_iapg_conj_intro hreplay
              (ay_iapg_conj_intro hchecker
                (ay_iapg_conj_intro hfingerprint
                  (ay_iapg_conj_intro hbuild harchive)))))))

theorem ay_iapg_accepted_projection_assumption
    {assumptionOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyIAPGAcceptedProjection assumptionOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    assumptionOk :=
  fun h => ay_iapg_conj_left h

theorem ay_iapg_accepted_projection_map
    {assumptionOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyIAPGAcceptedProjection assumptionOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    mapOk :=
  fun h => ay_iapg_conj_left (ay_iapg_conj_right h)

theorem ay_iapg_accepted_projection_witness
    {assumptionOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyIAPGAcceptedProjection assumptionOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    witnessOk :=
  fun h => ay_iapg_conj_left (ay_iapg_conj_right (ay_iapg_conj_right h))

theorem ay_iapg_accepted_projection_assignment
    {assumptionOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyIAPGAcceptedProjection assumptionOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    assignmentOk :=
  fun h =>
    ay_iapg_conj_left
      (ay_iapg_conj_right (ay_iapg_conj_right (ay_iapg_conj_right h)))

theorem ay_iapg_accepted_projection_replay
    {assumptionOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyIAPGAcceptedProjection assumptionOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    replayOk :=
  fun h =>
    ay_iapg_conj_left
      (ay_iapg_conj_right
        (ay_iapg_conj_right (ay_iapg_conj_right (ay_iapg_conj_right h))))

theorem ay_iapg_accepted_projection_checker
    {assumptionOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyIAPGAcceptedProjection assumptionOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    checkerOk :=
  fun h =>
    ay_iapg_conj_left
      (ay_iapg_conj_right
        (ay_iapg_conj_right
          (ay_iapg_conj_right (ay_iapg_conj_right (ay_iapg_conj_right h)))))

theorem ay_iapg_accepted_projection_fingerprint
    {assumptionOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyIAPGAcceptedProjection assumptionOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    fingerprintOk :=
  fun h =>
    ay_iapg_conj_left
      (ay_iapg_conj_right
        (ay_iapg_conj_right
          (ay_iapg_conj_right
            (ay_iapg_conj_right (ay_iapg_conj_right
              (ay_iapg_conj_right h))))))

theorem ay_iapg_accepted_projection_build
    {assumptionOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyIAPGAcceptedProjection assumptionOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    buildOk :=
  fun h =>
    ay_iapg_conj_left
      (ay_iapg_conj_right
        (ay_iapg_conj_right
          (ay_iapg_conj_right
            (ay_iapg_conj_right
              (ay_iapg_conj_right (ay_iapg_conj_right
                (ay_iapg_conj_right h)))))))

theorem ay_iapg_accepted_projection_archive
    {assumptionOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyIAPGAcceptedProjection assumptionOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    archiveOk :=
  fun h =>
    ay_iapg_conj_right
      (ay_iapg_conj_right
        (ay_iapg_conj_right
          (ay_iapg_conj_right
            (ay_iapg_conj_right
              (ay_iapg_conj_right (ay_iapg_conj_right
                (ay_iapg_conj_right h)))))))

theorem ay_iapg_public_sat_witness_intro
    {acceptedProjection originalWitness publicSatClaim : Prop} :
    acceptedProjection -> originalWitness -> publicSatClaim ->
    AyIAPGPublicSatWitness acceptedProjection originalWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_iapg_conj_intro hevidence (ay_iapg_conj_intro hwitness hclaim)

theorem ay_iapg_public_sat_witness_evidence
    {acceptedProjection originalWitness publicSatClaim : Prop} :
    AyIAPGPublicSatWitness acceptedProjection originalWitness publicSatClaim ->
    acceptedProjection :=
  fun h => ay_iapg_conj_left h

theorem ay_iapg_public_sat_witness_claim
    {acceptedProjection originalWitness publicSatClaim : Prop} :
    AyIAPGPublicSatWitness acceptedProjection originalWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_iapg_conj_right (ay_iapg_conj_right h)

theorem ay_iapg_accepted_projection_publishes_sound_sat
    {assumptionOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyIAPGAcceptedProjection assumptionOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    originalWitness -> publicSatClaim ->
    AyIAPGPublicSatWitness
      (AyIAPGAcceptedProjection assumptionOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim :=
  ay_iapg_public_sat_witness_intro

theorem ay_iapg_projection_reconstructs_assumed_original_assignment
    {assumptionTruth originalTruth : Prop} :
    AyIAPGEquisat assumptionTruth originalTruth -> assumptionTruth ->
    originalTruth :=
  ay_iapg_equisat_forward

theorem ay_iapg_public_sat_requires_accepted_projection
    {acceptedProjection originalWitness publicSatClaim : Prop} :
    AyIAPGPublicSatWitness acceptedProjection originalWitness publicSatClaim ->
    acceptedProjection :=
  ay_iapg_public_sat_witness_evidence

theorem ay_iapg_publication_requires_assumption
    {assumptionOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyIAPGPublicSatWitness
      (AyIAPGAcceptedProjection assumptionOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    assumptionOk :=
  fun h => ay_iapg_accepted_projection_assumption
    (ay_iapg_public_sat_witness_evidence h)

theorem ay_iapg_publication_requires_map
    {assumptionOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyIAPGPublicSatWitness
      (AyIAPGAcceptedProjection assumptionOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    mapOk :=
  fun h => ay_iapg_accepted_projection_map
    (ay_iapg_public_sat_witness_evidence h)

theorem ay_iapg_publication_requires_witness
    {assumptionOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyIAPGPublicSatWitness
      (AyIAPGAcceptedProjection assumptionOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    witnessOk :=
  fun h => ay_iapg_accepted_projection_witness
    (ay_iapg_public_sat_witness_evidence h)

theorem ay_iapg_publication_requires_assignment
    {assumptionOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyIAPGPublicSatWitness
      (AyIAPGAcceptedProjection assumptionOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    assignmentOk :=
  fun h => ay_iapg_accepted_projection_assignment
    (ay_iapg_public_sat_witness_evidence h)

theorem ay_iapg_publication_requires_replay
    {assumptionOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyIAPGPublicSatWitness
      (AyIAPGAcceptedProjection assumptionOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    replayOk :=
  fun h => ay_iapg_accepted_projection_replay
    (ay_iapg_public_sat_witness_evidence h)

theorem ay_iapg_publication_requires_checker
    {assumptionOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyIAPGPublicSatWitness
      (AyIAPGAcceptedProjection assumptionOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    checkerOk :=
  fun h => ay_iapg_accepted_projection_checker
    (ay_iapg_public_sat_witness_evidence h)

theorem ay_iapg_publication_requires_fingerprint
    {assumptionOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyIAPGPublicSatWitness
      (AyIAPGAcceptedProjection assumptionOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    fingerprintOk :=
  fun h => ay_iapg_accepted_projection_fingerprint
    (ay_iapg_public_sat_witness_evidence h)

theorem ay_iapg_publication_requires_build
    {assumptionOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyIAPGPublicSatWitness
      (AyIAPGAcceptedProjection assumptionOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    buildOk :=
  fun h => ay_iapg_accepted_projection_build
    (ay_iapg_public_sat_witness_evidence h)

theorem ay_iapg_publication_requires_archive
    {assumptionOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AyIAPGPublicSatWitness
      (AyIAPGAcceptedProjection assumptionOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    archiveOk :=
  fun h => ay_iapg_accepted_projection_archive
    (ay_iapg_public_sat_witness_evidence h)

theorem ay_iapg_no_claim_diagnostic_intro
    {reason blocksPublication : Prop} :
    reason -> blocksPublication ->
    AyIAPGNoClaimDiagnostic reason blocksPublication :=
  ay_iapg_conj_intro

theorem ay_iapg_no_claim_diagnostic_blocks
    {reason blocksPublication : Prop} :
    AyIAPGNoClaimDiagnostic reason blocksPublication -> blocksPublication :=
  ay_iapg_conj_right

theorem ay_iapg_recompute_obligation_intro
    {reason recomputeRequested : Prop} :
    reason -> recomputeRequested ->
    AyIAPGRecomputeObligation reason recomputeRequested :=
  ay_iapg_conj_intro

theorem ay_iapg_recompute_obligation_request
    {reason recomputeRequested : Prop} :
    AyIAPGRecomputeObligation reason recomputeRequested -> recomputeRequested :=
  ay_iapg_conj_right

theorem ay_iapg_assumption_failure_no_claim
    {assumptionFailure blocksPublication : Prop} :
    assumptionFailure -> blocksPublication ->
    AyIAPGNoClaimDiagnostic assumptionFailure blocksPublication :=
  ay_iapg_no_claim_diagnostic_intro

theorem ay_iapg_assumption_failure_recompute
    {assumptionFailure recomputeRequested : Prop} :
    assumptionFailure -> recomputeRequested ->
    AyIAPGRecomputeObligation assumptionFailure recomputeRequested :=
  ay_iapg_recompute_obligation_intro

theorem ay_iapg_map_failure_no_claim
    {mapFailure blocksPublication : Prop} :
    mapFailure -> blocksPublication ->
    AyIAPGNoClaimDiagnostic mapFailure blocksPublication :=
  ay_iapg_no_claim_diagnostic_intro

theorem ay_iapg_witness_failure_no_claim
    {witnessFailure blocksPublication : Prop} :
    witnessFailure -> blocksPublication ->
    AyIAPGNoClaimDiagnostic witnessFailure blocksPublication :=
  ay_iapg_no_claim_diagnostic_intro

theorem ay_iapg_assignment_failure_no_claim
    {assignmentFailure blocksPublication : Prop} :
    assignmentFailure -> blocksPublication ->
    AyIAPGNoClaimDiagnostic assignmentFailure blocksPublication :=
  ay_iapg_no_claim_diagnostic_intro

theorem ay_iapg_replay_failure_no_claim
    {replayFailure blocksPublication : Prop} :
    replayFailure -> blocksPublication ->
    AyIAPGNoClaimDiagnostic replayFailure blocksPublication :=
  ay_iapg_no_claim_diagnostic_intro

theorem ay_iapg_checker_failure_no_claim
    {checkerFailure blocksPublication : Prop} :
    checkerFailure -> blocksPublication ->
    AyIAPGNoClaimDiagnostic checkerFailure blocksPublication :=
  ay_iapg_no_claim_diagnostic_intro

theorem ay_iapg_fingerprint_failure_no_claim
    {fingerprintFailure blocksPublication : Prop} :
    fingerprintFailure -> blocksPublication ->
    AyIAPGNoClaimDiagnostic fingerprintFailure blocksPublication :=
  ay_iapg_no_claim_diagnostic_intro

theorem ay_iapg_build_failure_no_claim
    {buildFailure blocksPublication : Prop} :
    buildFailure -> blocksPublication ->
    AyIAPGNoClaimDiagnostic buildFailure blocksPublication :=
  ay_iapg_no_claim_diagnostic_intro

theorem ay_iapg_archive_failure_no_claim
    {archiveFailure blocksPublication : Prop} :
    archiveFailure -> blocksPublication ->
    AyIAPGNoClaimDiagnostic archiveFailure blocksPublication :=
  ay_iapg_no_claim_diagnostic_intro

theorem ay_iapg_bad_projection_cannot_bless_sat
    {failure blocksPublication recomputeRequested : Prop} :
    AyIAPGNoClaimDiagnostic failure blocksPublication ->
    AyIAPGRecomputeObligation failure recomputeRequested ->
    AyIAPGConj blocksPublication recomputeRequested :=
  fun hdiagnostic hrecompute =>
    ay_iapg_conj_intro
      (ay_iapg_no_claim_diagnostic_blocks hdiagnostic)
      (ay_iapg_recompute_obligation_request hrecompute)
