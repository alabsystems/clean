-- SAT-COMP/ay assumption literal projection soundness skeleton.
-- Solver-internal assumptions and temporary selectors project to public DIMACS
-- assignments only when maps, selector retirement, replay, digest, build, and
-- original fingerprint evidence are accepted.

def AyMALPConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMALPDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMALPEquisat (left right : Prop) : Prop :=
  AyMALPConj (left -> right) (right -> left)

def AyMALPAssumptionMap
    (internalAssumptions dimacsAssumptions assumptionAgreement : Prop) : Prop :=
  AyMALPConj internalAssumptions
    (AyMALPConj dimacsAssumptions assumptionAgreement)

def AyMALPSelectorRetirement
    (temporarySelectors retiredSelectors retirementAgreement : Prop) : Prop :=
  AyMALPConj temporarySelectors
    (AyMALPConj retiredSelectors retirementAgreement)

def AyMALPAssignmentDigest
    (internalDigest publicDigest digestAgreement : Prop) : Prop :=
  AyMALPConj internalDigest (AyMALPConj publicDigest digestAgreement)

def AyMALPClauseEvaluationReplay
    (clauseReplay publicEvaluation evaluationAgreement : Prop) : Prop :=
  AyMALPConj clauseReplay
    (AyMALPConj publicEvaluation evaluationAgreement)

def AyMALPCheckerReplay (checkerAccepted replayTrace : Prop) : Prop :=
  AyMALPConj checkerAccepted replayTrace

def AyMALPSolverBuild
    (solverBuild projectionBuild buildAgreement : Prop) : Prop :=
  AyMALPConj solverBuild (AyMALPConj projectionBuild buildAgreement)

def AyMALPOriginalFingerprint
    (originalFingerprint projectionFingerprint fingerprintAgreement : Prop) :
    Prop :=
  AyMALPConj originalFingerprint
    (AyMALPConj projectionFingerprint fingerprintAgreement)

def AyMALPAcceptedEvidence
    (assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop) : Prop :=
  AyMALPConj assumptionMapOk
    (AyMALPConj selectorOk
      (AyMALPConj digestOk
        (AyMALPConj clauseReplayOk
          (AyMALPConj checkerOk
            (AyMALPConj buildOk fingerprintOk)))))

def AyMALPPublicSatWitness
    (acceptedEvidence publicWitness publicSatClaim : Prop) : Prop :=
  AyMALPConj acceptedEvidence
    (AyMALPConj publicWitness publicSatClaim)

def AyMALPNoClaimDiagnostic (diagnostic publicSatClaim : Prop) : Prop :=
  AyMALPConj diagnostic (publicSatClaim -> False)

def AyMALPRecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMALPConj reason recomputeRequest

theorem ay_malp_conj_intro {left right : Prop} :
    left -> right -> AyMALPConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_malp_conj_left {left right : Prop} :
    AyMALPConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_malp_conj_right {left right : Prop} :
    AyMALPConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_malp_disj_left {left right : Prop} :
    left -> AyMALPDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_malp_disj_right {left right : Prop} :
    right -> AyMALPDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_malp_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMALPEquisat left right :=
  fun hf hb => ay_malp_conj_intro hf hb

theorem ay_malp_equisat_forward {left right : Prop} :
    AyMALPEquisat left right -> left -> right :=
  fun h => ay_malp_conj_left h

theorem ay_malp_equisat_backward {left right : Prop} :
    AyMALPEquisat left right -> right -> left :=
  fun h => ay_malp_conj_right h

theorem ay_malp_assumption_map_intro
    {internalAssumptions dimacsAssumptions assumptionAgreement : Prop} :
    internalAssumptions ->
    dimacsAssumptions ->
    assumptionAgreement ->
    AyMALPAssumptionMap
      internalAssumptions dimacsAssumptions assumptionAgreement :=
  fun hinternal hdimacs hagree =>
    ay_malp_conj_intro hinternal
      (ay_malp_conj_intro hdimacs hagree)

theorem ay_malp_assumption_map_internal
    {internalAssumptions dimacsAssumptions assumptionAgreement : Prop} :
    AyMALPAssumptionMap
      internalAssumptions dimacsAssumptions assumptionAgreement ->
    internalAssumptions :=
  fun h => ay_malp_conj_left h

theorem ay_malp_assumption_map_dimacs
    {internalAssumptions dimacsAssumptions assumptionAgreement : Prop} :
    AyMALPAssumptionMap
      internalAssumptions dimacsAssumptions assumptionAgreement ->
    dimacsAssumptions :=
  fun h => ay_malp_conj_left (ay_malp_conj_right h)

theorem ay_malp_assumption_map_agreement
    {internalAssumptions dimacsAssumptions assumptionAgreement : Prop} :
    AyMALPAssumptionMap
      internalAssumptions dimacsAssumptions assumptionAgreement ->
    assumptionAgreement :=
  fun h => ay_malp_conj_right (ay_malp_conj_right h)

theorem ay_malp_selector_retirement_intro
    {temporarySelectors retiredSelectors retirementAgreement : Prop} :
    temporarySelectors ->
    retiredSelectors ->
    retirementAgreement ->
    AyMALPSelectorRetirement
      temporarySelectors retiredSelectors retirementAgreement :=
  fun htemporary hretired hagree =>
    ay_malp_conj_intro htemporary
      (ay_malp_conj_intro hretired hagree)

theorem ay_malp_selector_retirement_temporary
    {temporarySelectors retiredSelectors retirementAgreement : Prop} :
    AyMALPSelectorRetirement
      temporarySelectors retiredSelectors retirementAgreement ->
    temporarySelectors :=
  fun h => ay_malp_conj_left h

theorem ay_malp_selector_retirement_retired
    {temporarySelectors retiredSelectors retirementAgreement : Prop} :
    AyMALPSelectorRetirement
      temporarySelectors retiredSelectors retirementAgreement ->
    retiredSelectors :=
  fun h => ay_malp_conj_left (ay_malp_conj_right h)

theorem ay_malp_selector_retirement_agreement
    {temporarySelectors retiredSelectors retirementAgreement : Prop} :
    AyMALPSelectorRetirement
      temporarySelectors retiredSelectors retirementAgreement ->
    retirementAgreement :=
  fun h => ay_malp_conj_right (ay_malp_conj_right h)

theorem ay_malp_assignment_digest_intro
    {internalDigest publicDigest digestAgreement : Prop} :
    internalDigest ->
    publicDigest ->
    digestAgreement ->
    AyMALPAssignmentDigest internalDigest publicDigest digestAgreement :=
  fun hinternal hpublic hagree =>
    ay_malp_conj_intro hinternal
      (ay_malp_conj_intro hpublic hagree)

theorem ay_malp_assignment_digest_internal
    {internalDigest publicDigest digestAgreement : Prop} :
    AyMALPAssignmentDigest internalDigest publicDigest digestAgreement ->
    internalDigest :=
  fun h => ay_malp_conj_left h

theorem ay_malp_assignment_digest_public
    {internalDigest publicDigest digestAgreement : Prop} :
    AyMALPAssignmentDigest internalDigest publicDigest digestAgreement ->
    publicDigest :=
  fun h => ay_malp_conj_left (ay_malp_conj_right h)

theorem ay_malp_assignment_digest_agreement
    {internalDigest publicDigest digestAgreement : Prop} :
    AyMALPAssignmentDigest internalDigest publicDigest digestAgreement ->
    digestAgreement :=
  fun h => ay_malp_conj_right (ay_malp_conj_right h)

theorem ay_malp_clause_evaluation_replay_intro
    {clauseReplay publicEvaluation evaluationAgreement : Prop} :
    clauseReplay ->
    publicEvaluation ->
    evaluationAgreement ->
    AyMALPClauseEvaluationReplay
      clauseReplay publicEvaluation evaluationAgreement :=
  fun hreplay heval hagree =>
    ay_malp_conj_intro hreplay (ay_malp_conj_intro heval hagree)

theorem ay_malp_clause_evaluation_replay_trace
    {clauseReplay publicEvaluation evaluationAgreement : Prop} :
    AyMALPClauseEvaluationReplay
      clauseReplay publicEvaluation evaluationAgreement ->
    clauseReplay :=
  fun h => ay_malp_conj_left h

theorem ay_malp_clause_evaluation_replay_evaluation
    {clauseReplay publicEvaluation evaluationAgreement : Prop} :
    AyMALPClauseEvaluationReplay
      clauseReplay publicEvaluation evaluationAgreement ->
    publicEvaluation :=
  fun h => ay_malp_conj_left (ay_malp_conj_right h)

theorem ay_malp_clause_evaluation_replay_agreement
    {clauseReplay publicEvaluation evaluationAgreement : Prop} :
    AyMALPClauseEvaluationReplay
      clauseReplay publicEvaluation evaluationAgreement ->
    evaluationAgreement :=
  fun h => ay_malp_conj_right (ay_malp_conj_right h)

theorem ay_malp_checker_replay_intro
    {checkerAccepted replayTrace : Prop} :
    checkerAccepted ->
    replayTrace ->
    AyMALPCheckerReplay checkerAccepted replayTrace :=
  fun haccepted htrace => ay_malp_conj_intro haccepted htrace

theorem ay_malp_checker_replay_accepted
    {checkerAccepted replayTrace : Prop} :
    AyMALPCheckerReplay checkerAccepted replayTrace -> checkerAccepted :=
  fun h => ay_malp_conj_left h

theorem ay_malp_checker_replay_trace
    {checkerAccepted replayTrace : Prop} :
    AyMALPCheckerReplay checkerAccepted replayTrace -> replayTrace :=
  fun h => ay_malp_conj_right h

theorem ay_malp_solver_build_intro
    {solverBuild projectionBuild buildAgreement : Prop} :
    solverBuild ->
    projectionBuild ->
    buildAgreement ->
    AyMALPSolverBuild solverBuild projectionBuild buildAgreement :=
  fun hsolver hprojection hagree =>
    ay_malp_conj_intro hsolver
      (ay_malp_conj_intro hprojection hagree)

theorem ay_malp_solver_build_solver
    {solverBuild projectionBuild buildAgreement : Prop} :
    AyMALPSolverBuild solverBuild projectionBuild buildAgreement ->
    solverBuild :=
  fun h => ay_malp_conj_left h

theorem ay_malp_solver_build_projection
    {solverBuild projectionBuild buildAgreement : Prop} :
    AyMALPSolverBuild solverBuild projectionBuild buildAgreement ->
    projectionBuild :=
  fun h => ay_malp_conj_left (ay_malp_conj_right h)

theorem ay_malp_solver_build_agreement
    {solverBuild projectionBuild buildAgreement : Prop} :
    AyMALPSolverBuild solverBuild projectionBuild buildAgreement ->
    buildAgreement :=
  fun h => ay_malp_conj_right (ay_malp_conj_right h)

theorem ay_malp_original_fingerprint_intro
    {originalFingerprint projectionFingerprint fingerprintAgreement : Prop} :
    originalFingerprint ->
    projectionFingerprint ->
    fingerprintAgreement ->
    AyMALPOriginalFingerprint
      originalFingerprint projectionFingerprint fingerprintAgreement :=
  fun horiginal hprojection hagree =>
    ay_malp_conj_intro horiginal
      (ay_malp_conj_intro hprojection hagree)

theorem ay_malp_original_fingerprint_original
    {originalFingerprint projectionFingerprint fingerprintAgreement : Prop} :
    AyMALPOriginalFingerprint
      originalFingerprint projectionFingerprint fingerprintAgreement ->
    originalFingerprint :=
  fun h => ay_malp_conj_left h

theorem ay_malp_original_fingerprint_projection
    {originalFingerprint projectionFingerprint fingerprintAgreement : Prop} :
    AyMALPOriginalFingerprint
      originalFingerprint projectionFingerprint fingerprintAgreement ->
    projectionFingerprint :=
  fun h => ay_malp_conj_left (ay_malp_conj_right h)

theorem ay_malp_original_fingerprint_agreement
    {originalFingerprint projectionFingerprint fingerprintAgreement : Prop} :
    AyMALPOriginalFingerprint
      originalFingerprint projectionFingerprint fingerprintAgreement ->
    fingerprintAgreement :=
  fun h => ay_malp_conj_right (ay_malp_conj_right h)

theorem ay_malp_accepted_evidence_intro
    {assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    assumptionMapOk ->
    selectorOk ->
    digestOk ->
    clauseReplayOk ->
    checkerOk ->
    buildOk ->
    fingerprintOk ->
    AyMALPAcceptedEvidence
      assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk :=
  fun hassumption hselector hdigest hclause hchecker hbuild hfingerprint =>
    ay_malp_conj_intro hassumption
      (ay_malp_conj_intro hselector
        (ay_malp_conj_intro hdigest
          (ay_malp_conj_intro hclause
            (ay_malp_conj_intro hchecker
              (ay_malp_conj_intro hbuild hfingerprint)))))

theorem ay_malp_accepted_evidence_assumption_map
    {assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMALPAcceptedEvidence
      assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    assumptionMapOk :=
  fun h => ay_malp_conj_left h

theorem ay_malp_accepted_evidence_selector
    {assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMALPAcceptedEvidence
      assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    selectorOk :=
  fun h => ay_malp_conj_left (ay_malp_conj_right h)

theorem ay_malp_accepted_evidence_digest
    {assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMALPAcceptedEvidence
      assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    digestOk :=
  fun h => ay_malp_conj_left
    (ay_malp_conj_right (ay_malp_conj_right h))

theorem ay_malp_accepted_evidence_clause_replay
    {assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMALPAcceptedEvidence
      assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    clauseReplayOk :=
  fun h => ay_malp_conj_left
    (ay_malp_conj_right
      (ay_malp_conj_right (ay_malp_conj_right h)))

theorem ay_malp_accepted_evidence_checker
    {assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMALPAcceptedEvidence
      assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    checkerOk :=
  fun h => ay_malp_conj_left
    (ay_malp_conj_right
      (ay_malp_conj_right
        (ay_malp_conj_right (ay_malp_conj_right h))))

theorem ay_malp_accepted_evidence_build
    {assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMALPAcceptedEvidence
      assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    buildOk :=
  fun h => ay_malp_conj_left
    (ay_malp_conj_right
      (ay_malp_conj_right
        (ay_malp_conj_right
          (ay_malp_conj_right (ay_malp_conj_right h)))))

theorem ay_malp_accepted_evidence_fingerprint
    {assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMALPAcceptedEvidence
      assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    fingerprintOk :=
  fun h => ay_malp_conj_right
    (ay_malp_conj_right
      (ay_malp_conj_right
        (ay_malp_conj_right
          (ay_malp_conj_right (ay_malp_conj_right h)))))

theorem ay_malp_public_sat_witness_intro
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    acceptedEvidence ->
    publicWitness ->
    publicSatClaim ->
    AyMALPPublicSatWitness acceptedEvidence publicWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_malp_conj_intro hevidence
      (ay_malp_conj_intro hwitness hclaim)

theorem ay_malp_public_sat_witness_evidence
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMALPPublicSatWitness acceptedEvidence publicWitness publicSatClaim ->
    acceptedEvidence :=
  fun h => ay_malp_conj_left h

theorem ay_malp_public_sat_witness_witness
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMALPPublicSatWitness acceptedEvidence publicWitness publicSatClaim ->
    publicWitness :=
  fun h => ay_malp_conj_left (ay_malp_conj_right h)

theorem ay_malp_public_sat_witness_claim
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMALPPublicSatWitness acceptedEvidence publicWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_malp_conj_right (ay_malp_conj_right h)

theorem ay_malp_accepted_projection_emits_sound_public_sat
    {assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMALPAcceptedEvidence
      assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    publicWitness ->
    publicSatClaim ->
    AyMALPPublicSatWitness
      (AyMALPAcceptedEvidence
        assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_malp_public_sat_witness_intro hevidence hwitness hclaim

theorem ay_malp_public_sat_requires_accepted_evidence
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMALPPublicSatWitness acceptedEvidence publicWitness publicSatClaim ->
    acceptedEvidence :=
  fun h => ay_malp_public_sat_witness_evidence h

theorem ay_malp_internal_assumption_hints_preserve_truth
    {internalTruth publicTruth : Prop} :
    AyMALPEquisat internalTruth publicTruth ->
    internalTruth ->
    publicTruth :=
  fun heq hinternal => ay_malp_equisat_forward heq hinternal

theorem ay_malp_clause_replay_transports_truth
    {clauseReplay publicEvaluation formulaTruth : Prop} :
    AyMALPClauseEvaluationReplay
      clauseReplay publicEvaluation formulaTruth ->
    formulaTruth :=
  fun h => ay_malp_clause_evaluation_replay_agreement h

theorem ay_malp_publication_requires_assumption_map
    {assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMALPPublicSatWitness
      (AyMALPAcceptedEvidence
        assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    assumptionMapOk :=
  fun h =>
    ay_malp_accepted_evidence_assumption_map
      (ay_malp_public_sat_witness_evidence h)

theorem ay_malp_publication_requires_selector_retirement
    {assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMALPPublicSatWitness
      (AyMALPAcceptedEvidence
        assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    selectorOk :=
  fun h =>
    ay_malp_accepted_evidence_selector
      (ay_malp_public_sat_witness_evidence h)

theorem ay_malp_publication_requires_digest
    {assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMALPPublicSatWitness
      (AyMALPAcceptedEvidence
        assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    digestOk :=
  fun h =>
    ay_malp_accepted_evidence_digest
      (ay_malp_public_sat_witness_evidence h)

theorem ay_malp_publication_requires_clause_replay
    {assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMALPPublicSatWitness
      (AyMALPAcceptedEvidence
        assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    clauseReplayOk :=
  fun h =>
    ay_malp_accepted_evidence_clause_replay
      (ay_malp_public_sat_witness_evidence h)

theorem ay_malp_publication_requires_checker
    {assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMALPPublicSatWitness
      (AyMALPAcceptedEvidence
        assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    checkerOk :=
  fun h =>
    ay_malp_accepted_evidence_checker
      (ay_malp_public_sat_witness_evidence h)

theorem ay_malp_publication_requires_build
    {assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMALPPublicSatWitness
      (AyMALPAcceptedEvidence
        assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    buildOk :=
  fun h =>
    ay_malp_accepted_evidence_build
      (ay_malp_public_sat_witness_evidence h)

theorem ay_malp_publication_requires_fingerprint
    {assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMALPPublicSatWitness
      (AyMALPAcceptedEvidence
        assumptionMapOk selectorOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    fingerprintOk :=
  fun h =>
    ay_malp_accepted_evidence_fingerprint
      (ay_malp_public_sat_witness_evidence h)

theorem ay_malp_no_claim_diagnostic_intro
    {diagnostic publicSatClaim : Prop} :
    diagnostic ->
    (publicSatClaim -> False) ->
    AyMALPNoClaimDiagnostic diagnostic publicSatClaim :=
  fun hdiagnostic hblocks =>
    ay_malp_conj_intro hdiagnostic hblocks

theorem ay_malp_no_claim_diagnostic_reason
    {diagnostic publicSatClaim : Prop} :
    AyMALPNoClaimDiagnostic diagnostic publicSatClaim -> diagnostic :=
  fun h => ay_malp_conj_left h

theorem ay_malp_no_claim_diagnostic_blocks
    {diagnostic publicSatClaim : Prop} :
    AyMALPNoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h => ay_malp_conj_right h

theorem ay_malp_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMALPRecomputeObligation reason recomputeRequest :=
  fun hreason hrecompute => ay_malp_conj_intro hreason hrecompute

theorem ay_malp_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMALPRecomputeObligation reason recomputeRequest -> reason :=
  fun h => ay_malp_conj_left h

theorem ay_malp_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMALPRecomputeObligation reason recomputeRequest -> recomputeRequest :=
  fun h => ay_malp_conj_right h

theorem ay_malp_assumption_drift_recompute
    {assumptionDrift recomputeRequest : Prop} :
    assumptionDrift ->
    recomputeRequest ->
    AyMALPRecomputeObligation assumptionDrift recomputeRequest :=
  fun hdrift hrecompute =>
    ay_malp_recompute_obligation_intro hdrift hrecompute

theorem ay_malp_assumption_drift_no_claim
    {assumptionDrift publicSatClaim : Prop} :
    assumptionDrift ->
    (publicSatClaim -> False) ->
    AyMALPNoClaimDiagnostic assumptionDrift publicSatClaim :=
  fun hdrift hblocks => ay_malp_no_claim_diagnostic_intro hdrift hblocks

theorem ay_malp_selector_drift_recompute
    {selectorDrift recomputeRequest : Prop} :
    selectorDrift ->
    recomputeRequest ->
    AyMALPRecomputeObligation selectorDrift recomputeRequest :=
  fun hdrift hrecompute =>
    ay_malp_recompute_obligation_intro hdrift hrecompute

theorem ay_malp_selector_drift_no_claim
    {selectorDrift publicSatClaim : Prop} :
    selectorDrift ->
    (publicSatClaim -> False) ->
    AyMALPNoClaimDiagnostic selectorDrift publicSatClaim :=
  fun hdrift hblocks => ay_malp_no_claim_diagnostic_intro hdrift hblocks

theorem ay_malp_checker_rejection_no_claim
    {checkerRejection publicSatClaim : Prop} :
    checkerRejection ->
    (publicSatClaim -> False) ->
    AyMALPNoClaimDiagnostic checkerRejection publicSatClaim :=
  fun hreject hblocks =>
    ay_malp_no_claim_diagnostic_intro hreject hblocks

theorem ay_malp_digest_mismatch_no_claim
    {digestMismatch publicSatClaim : Prop} :
    digestMismatch ->
    (publicSatClaim -> False) ->
    AyMALPNoClaimDiagnostic digestMismatch publicSatClaim :=
  fun hmismatch hblocks =>
    ay_malp_no_claim_diagnostic_intro hmismatch hblocks

theorem ay_malp_build_drift_no_claim
    {buildDrift publicSatClaim : Prop} :
    buildDrift ->
    (publicSatClaim -> False) ->
    AyMALPNoClaimDiagnostic buildDrift publicSatClaim :=
  fun hdrift hblocks => ay_malp_no_claim_diagnostic_intro hdrift hblocks

theorem ay_malp_fingerprint_mismatch_no_claim
    {fingerprintMismatch publicSatClaim : Prop} :
    fingerprintMismatch ->
    (publicSatClaim -> False) ->
    AyMALPNoClaimDiagnostic fingerprintMismatch publicSatClaim :=
  fun hmismatch hblocks =>
    ay_malp_no_claim_diagnostic_intro hmismatch hblocks

theorem ay_malp_diagnostic_blocks_public_claim
    {diagnostic publicSatClaim : Prop} :
    AyMALPNoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_malp_no_claim_diagnostic_blocks h hclaim

theorem ay_malp_bad_assumption_projection_cannot_emit_sat
    {badProjection publicSatClaim : Prop} :
    AyMALPNoClaimDiagnostic badProjection publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_malp_diagnostic_blocks_public_claim h hclaim
