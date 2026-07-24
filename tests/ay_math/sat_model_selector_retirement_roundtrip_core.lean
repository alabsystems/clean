-- SAT-COMP/ay selector retirement roundtrip soundness skeleton.
-- Temporary preprocessing selectors must be retired before public witness
-- emission under accepted map, ledger, replay, digest, build, and fingerprint
-- evidence.

def AyMSRRConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMSRRDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMSRREquisat (left right : Prop) : Prop :=
  AyMSRRConj (left -> right) (right -> left)

def AyMSRRSelectorMap
    (temporarySelectors publicVariables selectorMapAgreement : Prop) : Prop :=
  AyMSRRConj temporarySelectors
    (AyMSRRConj publicVariables selectorMapAgreement)

def AyMSRRRetirementLedger
    (retirementEntries retiredSelectors ledgerAgreement : Prop) : Prop :=
  AyMSRRConj retirementEntries
    (AyMSRRConj retiredSelectors ledgerAgreement)

def AyMSRRAssignmentDigest
    (internalDigest publicDigest digestAgreement : Prop) : Prop :=
  AyMSRRConj internalDigest (AyMSRRConj publicDigest digestAgreement)

def AyMSRRClauseEvaluationReplay
    (clauseReplay publicEvaluation evaluationAgreement : Prop) : Prop :=
  AyMSRRConj clauseReplay
    (AyMSRRConj publicEvaluation evaluationAgreement)

def AyMSRRCheckerReplay (checkerAccepted replayTrace : Prop) : Prop :=
  AyMSRRConj checkerAccepted replayTrace

def AyMSRRSolverBuild
    (solverBuild retirementBuild buildAgreement : Prop) : Prop :=
  AyMSRRConj solverBuild (AyMSRRConj retirementBuild buildAgreement)

def AyMSRROriginalFingerprint
    (originalFingerprint retirementFingerprint fingerprintAgreement : Prop) :
    Prop :=
  AyMSRRConj originalFingerprint
    (AyMSRRConj retirementFingerprint fingerprintAgreement)

def AyMSRRAcceptedEvidence
    (selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop) : Prop :=
  AyMSRRConj selectorMapOk
    (AyMSRRConj ledgerOk
      (AyMSRRConj digestOk
        (AyMSRRConj clauseReplayOk
          (AyMSRRConj checkerOk
            (AyMSRRConj buildOk fingerprintOk)))))

def AyMSRRPublicSatWitness
    (acceptedEvidence publicWitness publicSatClaim : Prop) : Prop :=
  AyMSRRConj acceptedEvidence
    (AyMSRRConj publicWitness publicSatClaim)

def AyMSRRNoClaimDiagnostic (diagnostic publicSatClaim : Prop) : Prop :=
  AyMSRRConj diagnostic (publicSatClaim -> False)

def AyMSRRRecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMSRRConj reason recomputeRequest

theorem ay_msrr_conj_intro {left right : Prop} :
    left -> right -> AyMSRRConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_msrr_conj_left {left right : Prop} :
    AyMSRRConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_msrr_conj_right {left right : Prop} :
    AyMSRRConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_msrr_disj_left {left right : Prop} :
    left -> AyMSRRDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_msrr_disj_right {left right : Prop} :
    right -> AyMSRRDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_msrr_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMSRREquisat left right :=
  fun hf hb => ay_msrr_conj_intro hf hb

theorem ay_msrr_equisat_forward {left right : Prop} :
    AyMSRREquisat left right -> left -> right :=
  fun h => ay_msrr_conj_left h

theorem ay_msrr_equisat_backward {left right : Prop} :
    AyMSRREquisat left right -> right -> left :=
  fun h => ay_msrr_conj_right h

theorem ay_msrr_selector_map_intro
    {temporarySelectors publicVariables selectorMapAgreement : Prop} :
    temporarySelectors ->
    publicVariables ->
    selectorMapAgreement ->
    AyMSRRSelectorMap
      temporarySelectors publicVariables selectorMapAgreement :=
  fun htemporary hpublic hagree =>
    ay_msrr_conj_intro htemporary
      (ay_msrr_conj_intro hpublic hagree)

theorem ay_msrr_selector_map_temporary
    {temporarySelectors publicVariables selectorMapAgreement : Prop} :
    AyMSRRSelectorMap
      temporarySelectors publicVariables selectorMapAgreement ->
    temporarySelectors :=
  fun h => ay_msrr_conj_left h

theorem ay_msrr_selector_map_public
    {temporarySelectors publicVariables selectorMapAgreement : Prop} :
    AyMSRRSelectorMap
      temporarySelectors publicVariables selectorMapAgreement ->
    publicVariables :=
  fun h => ay_msrr_conj_left (ay_msrr_conj_right h)

theorem ay_msrr_selector_map_agreement
    {temporarySelectors publicVariables selectorMapAgreement : Prop} :
    AyMSRRSelectorMap
      temporarySelectors publicVariables selectorMapAgreement ->
    selectorMapAgreement :=
  fun h => ay_msrr_conj_right (ay_msrr_conj_right h)

theorem ay_msrr_retirement_ledger_intro
    {retirementEntries retiredSelectors ledgerAgreement : Prop} :
    retirementEntries ->
    retiredSelectors ->
    ledgerAgreement ->
    AyMSRRRetirementLedger
      retirementEntries retiredSelectors ledgerAgreement :=
  fun hentries hretired hagree =>
    ay_msrr_conj_intro hentries
      (ay_msrr_conj_intro hretired hagree)

theorem ay_msrr_retirement_ledger_entries
    {retirementEntries retiredSelectors ledgerAgreement : Prop} :
    AyMSRRRetirementLedger
      retirementEntries retiredSelectors ledgerAgreement ->
    retirementEntries :=
  fun h => ay_msrr_conj_left h

theorem ay_msrr_retirement_ledger_retired
    {retirementEntries retiredSelectors ledgerAgreement : Prop} :
    AyMSRRRetirementLedger
      retirementEntries retiredSelectors ledgerAgreement ->
    retiredSelectors :=
  fun h => ay_msrr_conj_left (ay_msrr_conj_right h)

theorem ay_msrr_retirement_ledger_agreement
    {retirementEntries retiredSelectors ledgerAgreement : Prop} :
    AyMSRRRetirementLedger
      retirementEntries retiredSelectors ledgerAgreement ->
    ledgerAgreement :=
  fun h => ay_msrr_conj_right (ay_msrr_conj_right h)

theorem ay_msrr_assignment_digest_intro
    {internalDigest publicDigest digestAgreement : Prop} :
    internalDigest ->
    publicDigest ->
    digestAgreement ->
    AyMSRRAssignmentDigest internalDigest publicDigest digestAgreement :=
  fun hinternal hpublic hagree =>
    ay_msrr_conj_intro hinternal
      (ay_msrr_conj_intro hpublic hagree)

theorem ay_msrr_assignment_digest_internal
    {internalDigest publicDigest digestAgreement : Prop} :
    AyMSRRAssignmentDigest internalDigest publicDigest digestAgreement ->
    internalDigest :=
  fun h => ay_msrr_conj_left h

theorem ay_msrr_assignment_digest_public
    {internalDigest publicDigest digestAgreement : Prop} :
    AyMSRRAssignmentDigest internalDigest publicDigest digestAgreement ->
    publicDigest :=
  fun h => ay_msrr_conj_left (ay_msrr_conj_right h)

theorem ay_msrr_assignment_digest_agreement
    {internalDigest publicDigest digestAgreement : Prop} :
    AyMSRRAssignmentDigest internalDigest publicDigest digestAgreement ->
    digestAgreement :=
  fun h => ay_msrr_conj_right (ay_msrr_conj_right h)

theorem ay_msrr_clause_evaluation_replay_intro
    {clauseReplay publicEvaluation evaluationAgreement : Prop} :
    clauseReplay ->
    publicEvaluation ->
    evaluationAgreement ->
    AyMSRRClauseEvaluationReplay
      clauseReplay publicEvaluation evaluationAgreement :=
  fun hreplay hevaluation hagree =>
    ay_msrr_conj_intro hreplay
      (ay_msrr_conj_intro hevaluation hagree)

theorem ay_msrr_clause_evaluation_replay_trace
    {clauseReplay publicEvaluation evaluationAgreement : Prop} :
    AyMSRRClauseEvaluationReplay
      clauseReplay publicEvaluation evaluationAgreement ->
    clauseReplay :=
  fun h => ay_msrr_conj_left h

theorem ay_msrr_clause_evaluation_replay_evaluation
    {clauseReplay publicEvaluation evaluationAgreement : Prop} :
    AyMSRRClauseEvaluationReplay
      clauseReplay publicEvaluation evaluationAgreement ->
    publicEvaluation :=
  fun h => ay_msrr_conj_left (ay_msrr_conj_right h)

theorem ay_msrr_clause_evaluation_replay_agreement
    {clauseReplay publicEvaluation evaluationAgreement : Prop} :
    AyMSRRClauseEvaluationReplay
      clauseReplay publicEvaluation evaluationAgreement ->
    evaluationAgreement :=
  fun h => ay_msrr_conj_right (ay_msrr_conj_right h)

theorem ay_msrr_checker_replay_intro
    {checkerAccepted replayTrace : Prop} :
    checkerAccepted ->
    replayTrace ->
    AyMSRRCheckerReplay checkerAccepted replayTrace :=
  fun haccepted htrace => ay_msrr_conj_intro haccepted htrace

theorem ay_msrr_checker_replay_accepted
    {checkerAccepted replayTrace : Prop} :
    AyMSRRCheckerReplay checkerAccepted replayTrace -> checkerAccepted :=
  fun h => ay_msrr_conj_left h

theorem ay_msrr_checker_replay_trace
    {checkerAccepted replayTrace : Prop} :
    AyMSRRCheckerReplay checkerAccepted replayTrace -> replayTrace :=
  fun h => ay_msrr_conj_right h

theorem ay_msrr_solver_build_intro
    {solverBuild retirementBuild buildAgreement : Prop} :
    solverBuild ->
    retirementBuild ->
    buildAgreement ->
    AyMSRRSolverBuild solverBuild retirementBuild buildAgreement :=
  fun hsolver hretirement hagree =>
    ay_msrr_conj_intro hsolver
      (ay_msrr_conj_intro hretirement hagree)

theorem ay_msrr_solver_build_solver
    {solverBuild retirementBuild buildAgreement : Prop} :
    AyMSRRSolverBuild solverBuild retirementBuild buildAgreement ->
    solverBuild :=
  fun h => ay_msrr_conj_left h

theorem ay_msrr_solver_build_retirement
    {solverBuild retirementBuild buildAgreement : Prop} :
    AyMSRRSolverBuild solverBuild retirementBuild buildAgreement ->
    retirementBuild :=
  fun h => ay_msrr_conj_left (ay_msrr_conj_right h)

theorem ay_msrr_solver_build_agreement
    {solverBuild retirementBuild buildAgreement : Prop} :
    AyMSRRSolverBuild solverBuild retirementBuild buildAgreement ->
    buildAgreement :=
  fun h => ay_msrr_conj_right (ay_msrr_conj_right h)

theorem ay_msrr_original_fingerprint_intro
    {originalFingerprint retirementFingerprint fingerprintAgreement : Prop} :
    originalFingerprint ->
    retirementFingerprint ->
    fingerprintAgreement ->
    AyMSRROriginalFingerprint
      originalFingerprint retirementFingerprint fingerprintAgreement :=
  fun horiginal hretirement hagree =>
    ay_msrr_conj_intro horiginal
      (ay_msrr_conj_intro hretirement hagree)

theorem ay_msrr_original_fingerprint_original
    {originalFingerprint retirementFingerprint fingerprintAgreement : Prop} :
    AyMSRROriginalFingerprint
      originalFingerprint retirementFingerprint fingerprintAgreement ->
    originalFingerprint :=
  fun h => ay_msrr_conj_left h

theorem ay_msrr_original_fingerprint_retirement
    {originalFingerprint retirementFingerprint fingerprintAgreement : Prop} :
    AyMSRROriginalFingerprint
      originalFingerprint retirementFingerprint fingerprintAgreement ->
    retirementFingerprint :=
  fun h => ay_msrr_conj_left (ay_msrr_conj_right h)

theorem ay_msrr_original_fingerprint_agreement
    {originalFingerprint retirementFingerprint fingerprintAgreement : Prop} :
    AyMSRROriginalFingerprint
      originalFingerprint retirementFingerprint fingerprintAgreement ->
    fingerprintAgreement :=
  fun h => ay_msrr_conj_right (ay_msrr_conj_right h)

theorem ay_msrr_accepted_evidence_intro
    {selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    selectorMapOk ->
    ledgerOk ->
    digestOk ->
    clauseReplayOk ->
    checkerOk ->
    buildOk ->
    fingerprintOk ->
    AyMSRRAcceptedEvidence
      selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk :=
  fun hselector hledger hdigest hclause hchecker hbuild hfingerprint =>
    ay_msrr_conj_intro hselector
      (ay_msrr_conj_intro hledger
        (ay_msrr_conj_intro hdigest
          (ay_msrr_conj_intro hclause
            (ay_msrr_conj_intro hchecker
              (ay_msrr_conj_intro hbuild hfingerprint)))))

theorem ay_msrr_accepted_evidence_selector_map
    {selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMSRRAcceptedEvidence
      selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    selectorMapOk :=
  fun h => ay_msrr_conj_left h

theorem ay_msrr_accepted_evidence_ledger
    {selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMSRRAcceptedEvidence
      selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    ledgerOk :=
  fun h => ay_msrr_conj_left (ay_msrr_conj_right h)

theorem ay_msrr_accepted_evidence_digest
    {selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMSRRAcceptedEvidence
      selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    digestOk :=
  fun h => ay_msrr_conj_left
    (ay_msrr_conj_right (ay_msrr_conj_right h))

theorem ay_msrr_accepted_evidence_clause_replay
    {selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMSRRAcceptedEvidence
      selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    clauseReplayOk :=
  fun h => ay_msrr_conj_left
    (ay_msrr_conj_right
      (ay_msrr_conj_right (ay_msrr_conj_right h)))

theorem ay_msrr_accepted_evidence_checker
    {selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMSRRAcceptedEvidence
      selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    checkerOk :=
  fun h => ay_msrr_conj_left
    (ay_msrr_conj_right
      (ay_msrr_conj_right
        (ay_msrr_conj_right (ay_msrr_conj_right h))))

theorem ay_msrr_accepted_evidence_build
    {selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMSRRAcceptedEvidence
      selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    buildOk :=
  fun h => ay_msrr_conj_left
    (ay_msrr_conj_right
      (ay_msrr_conj_right
        (ay_msrr_conj_right
          (ay_msrr_conj_right (ay_msrr_conj_right h)))))

theorem ay_msrr_accepted_evidence_fingerprint
    {selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMSRRAcceptedEvidence
      selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    fingerprintOk :=
  fun h => ay_msrr_conj_right
    (ay_msrr_conj_right
      (ay_msrr_conj_right
        (ay_msrr_conj_right
          (ay_msrr_conj_right (ay_msrr_conj_right h)))))

theorem ay_msrr_public_sat_witness_intro
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    acceptedEvidence ->
    publicWitness ->
    publicSatClaim ->
    AyMSRRPublicSatWitness acceptedEvidence publicWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_msrr_conj_intro hevidence
      (ay_msrr_conj_intro hwitness hclaim)

theorem ay_msrr_public_sat_witness_evidence
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMSRRPublicSatWitness acceptedEvidence publicWitness publicSatClaim ->
    acceptedEvidence :=
  fun h => ay_msrr_conj_left h

theorem ay_msrr_public_sat_witness_witness
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMSRRPublicSatWitness acceptedEvidence publicWitness publicSatClaim ->
    publicWitness :=
  fun h => ay_msrr_conj_left (ay_msrr_conj_right h)

theorem ay_msrr_public_sat_witness_claim
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMSRRPublicSatWitness acceptedEvidence publicWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_msrr_conj_right (ay_msrr_conj_right h)

theorem ay_msrr_accepted_selector_retirement_emits_sound_public_sat
    {selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMSRRAcceptedEvidence
      selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    publicWitness ->
    publicSatClaim ->
    AyMSRRPublicSatWitness
      (AyMSRRAcceptedEvidence
        selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_msrr_public_sat_witness_intro hevidence hwitness hclaim

theorem ay_msrr_public_sat_requires_accepted_evidence
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMSRRPublicSatWitness acceptedEvidence publicWitness publicSatClaim ->
    acceptedEvidence :=
  fun h => ay_msrr_public_sat_witness_evidence h

theorem ay_msrr_selector_internal_hints_preserve_truth
    {internalTruth publicTruth : Prop} :
    AyMSRREquisat internalTruth publicTruth ->
    internalTruth ->
    publicTruth :=
  fun heq hinternal => ay_msrr_equisat_forward heq hinternal

theorem ay_msrr_clause_replay_transports_truth
    {clauseReplay publicEvaluation formulaTruth : Prop} :
    AyMSRRClauseEvaluationReplay
      clauseReplay publicEvaluation formulaTruth ->
    formulaTruth :=
  fun h => ay_msrr_clause_evaluation_replay_agreement h

theorem ay_msrr_publication_requires_selector_map
    {selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMSRRPublicSatWitness
      (AyMSRRAcceptedEvidence
        selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    selectorMapOk :=
  fun h =>
    ay_msrr_accepted_evidence_selector_map
      (ay_msrr_public_sat_witness_evidence h)

theorem ay_msrr_publication_requires_ledger
    {selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMSRRPublicSatWitness
      (AyMSRRAcceptedEvidence
        selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    ledgerOk :=
  fun h =>
    ay_msrr_accepted_evidence_ledger
      (ay_msrr_public_sat_witness_evidence h)

theorem ay_msrr_publication_requires_digest
    {selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMSRRPublicSatWitness
      (AyMSRRAcceptedEvidence
        selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    digestOk :=
  fun h =>
    ay_msrr_accepted_evidence_digest
      (ay_msrr_public_sat_witness_evidence h)

theorem ay_msrr_publication_requires_clause_replay
    {selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMSRRPublicSatWitness
      (AyMSRRAcceptedEvidence
        selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    clauseReplayOk :=
  fun h =>
    ay_msrr_accepted_evidence_clause_replay
      (ay_msrr_public_sat_witness_evidence h)

theorem ay_msrr_publication_requires_checker
    {selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMSRRPublicSatWitness
      (AyMSRRAcceptedEvidence
        selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    checkerOk :=
  fun h =>
    ay_msrr_accepted_evidence_checker
      (ay_msrr_public_sat_witness_evidence h)

theorem ay_msrr_publication_requires_build
    {selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMSRRPublicSatWitness
      (AyMSRRAcceptedEvidence
        selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    buildOk :=
  fun h =>
    ay_msrr_accepted_evidence_build
      (ay_msrr_public_sat_witness_evidence h)

theorem ay_msrr_publication_requires_fingerprint
    {selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMSRRPublicSatWitness
      (AyMSRRAcceptedEvidence
        selectorMapOk ledgerOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    fingerprintOk :=
  fun h =>
    ay_msrr_accepted_evidence_fingerprint
      (ay_msrr_public_sat_witness_evidence h)

theorem ay_msrr_no_claim_diagnostic_intro
    {diagnostic publicSatClaim : Prop} :
    diagnostic ->
    (publicSatClaim -> False) ->
    AyMSRRNoClaimDiagnostic diagnostic publicSatClaim :=
  fun hdiagnostic hblocks =>
    ay_msrr_conj_intro hdiagnostic hblocks

theorem ay_msrr_no_claim_diagnostic_reason
    {diagnostic publicSatClaim : Prop} :
    AyMSRRNoClaimDiagnostic diagnostic publicSatClaim -> diagnostic :=
  fun h => ay_msrr_conj_left h

theorem ay_msrr_no_claim_diagnostic_blocks
    {diagnostic publicSatClaim : Prop} :
    AyMSRRNoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h => ay_msrr_conj_right h

theorem ay_msrr_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMSRRRecomputeObligation reason recomputeRequest :=
  fun hreason hrecompute => ay_msrr_conj_intro hreason hrecompute

theorem ay_msrr_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMSRRRecomputeObligation reason recomputeRequest -> reason :=
  fun h => ay_msrr_conj_left h

theorem ay_msrr_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMSRRRecomputeObligation reason recomputeRequest -> recomputeRequest :=
  fun h => ay_msrr_conj_right h

theorem ay_msrr_selector_leakage_recompute
    {selectorLeakage recomputeRequest : Prop} :
    selectorLeakage ->
    recomputeRequest ->
    AyMSRRRecomputeObligation selectorLeakage recomputeRequest :=
  fun hleak hrecompute =>
    ay_msrr_recompute_obligation_intro hleak hrecompute

theorem ay_msrr_selector_leakage_no_claim
    {selectorLeakage publicSatClaim : Prop} :
    selectorLeakage ->
    (publicSatClaim -> False) ->
    AyMSRRNoClaimDiagnostic selectorLeakage publicSatClaim :=
  fun hleak hblocks => ay_msrr_no_claim_diagnostic_intro hleak hblocks

theorem ay_msrr_retirement_drift_recompute
    {retirementDrift recomputeRequest : Prop} :
    retirementDrift ->
    recomputeRequest ->
    AyMSRRRecomputeObligation retirementDrift recomputeRequest :=
  fun hdrift hrecompute =>
    ay_msrr_recompute_obligation_intro hdrift hrecompute

theorem ay_msrr_retirement_drift_no_claim
    {retirementDrift publicSatClaim : Prop} :
    retirementDrift ->
    (publicSatClaim -> False) ->
    AyMSRRNoClaimDiagnostic retirementDrift publicSatClaim :=
  fun hdrift hblocks => ay_msrr_no_claim_diagnostic_intro hdrift hblocks

theorem ay_msrr_checker_rejection_no_claim
    {checkerRejection publicSatClaim : Prop} :
    checkerRejection ->
    (publicSatClaim -> False) ->
    AyMSRRNoClaimDiagnostic checkerRejection publicSatClaim :=
  fun hreject hblocks =>
    ay_msrr_no_claim_diagnostic_intro hreject hblocks

theorem ay_msrr_digest_mismatch_no_claim
    {digestMismatch publicSatClaim : Prop} :
    digestMismatch ->
    (publicSatClaim -> False) ->
    AyMSRRNoClaimDiagnostic digestMismatch publicSatClaim :=
  fun hmismatch hblocks =>
    ay_msrr_no_claim_diagnostic_intro hmismatch hblocks

theorem ay_msrr_build_drift_no_claim
    {buildDrift publicSatClaim : Prop} :
    buildDrift ->
    (publicSatClaim -> False) ->
    AyMSRRNoClaimDiagnostic buildDrift publicSatClaim :=
  fun hdrift hblocks => ay_msrr_no_claim_diagnostic_intro hdrift hblocks

theorem ay_msrr_fingerprint_mismatch_no_claim
    {fingerprintMismatch publicSatClaim : Prop} :
    fingerprintMismatch ->
    (publicSatClaim -> False) ->
    AyMSRRNoClaimDiagnostic fingerprintMismatch publicSatClaim :=
  fun hmismatch hblocks =>
    ay_msrr_no_claim_diagnostic_intro hmismatch hblocks

theorem ay_msrr_diagnostic_blocks_public_claim
    {diagnostic publicSatClaim : Prop} :
    AyMSRRNoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_msrr_no_claim_diagnostic_blocks h hclaim

theorem ay_msrr_bad_selector_retirement_cannot_emit_sat
    {badRetirement publicSatClaim : Prop} :
    AyMSRRNoClaimDiagnostic badRetirement publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_msrr_diagnostic_blocks_public_claim h hclaim
