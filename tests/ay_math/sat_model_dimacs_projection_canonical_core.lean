-- SAT-COMP/ay canonical DIMACS projection soundness skeleton.
-- Solver-internal variable and order encodings project to public DIMACS
-- assignments only when maps, replay, digest, build, and fingerprint evidence
-- are accepted.

def AyMDPCConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMDPCDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMDPCEquisat (left right : Prop) : Prop :=
  AyMDPCConj (left -> right) (right -> left)

def AyMDPCVariableMap
    (internalVariables dimacsVariables variableMapAgreement : Prop) : Prop :=
  AyMDPCConj internalVariables
    (AyMDPCConj dimacsVariables variableMapAgreement)

def AyMDPCPolarityMap
    (internalPolarity dimacsPolarity polarityAgreement : Prop) : Prop :=
  AyMDPCConj internalPolarity
    (AyMDPCConj dimacsPolarity polarityAgreement)

def AyMDPCAssignmentDigest
    (internalDigest dimacsDigest digestAgreement : Prop) : Prop :=
  AyMDPCConj internalDigest (AyMDPCConj dimacsDigest digestAgreement)

def AyMDPCClauseEvaluationReplay
    (clauseReplay dimacsEvaluation evaluationAgreement : Prop) : Prop :=
  AyMDPCConj clauseReplay
    (AyMDPCConj dimacsEvaluation evaluationAgreement)

def AyMDPCCheckerReplay (checkerAccepted replayTrace : Prop) : Prop :=
  AyMDPCConj checkerAccepted replayTrace

def AyMDPCSolverBuild
    (solverBuild projectionBuild buildAgreement : Prop) : Prop :=
  AyMDPCConj solverBuild (AyMDPCConj projectionBuild buildAgreement)

def AyMDPCOriginalFingerprint
    (originalFingerprint projectionFingerprint fingerprintAgreement : Prop) :
    Prop :=
  AyMDPCConj originalFingerprint
    (AyMDPCConj projectionFingerprint fingerprintAgreement)

def AyMDPCAcceptedEvidence
    (variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop) : Prop :=
  AyMDPCConj variableMapOk
    (AyMDPCConj polarityMapOk
      (AyMDPCConj digestOk
        (AyMDPCConj clauseReplayOk
          (AyMDPCConj checkerOk
            (AyMDPCConj buildOk fingerprintOk)))))

def AyMDPCPublicSatWitness
    (acceptedEvidence publicDimacsWitness publicSatClaim : Prop) : Prop :=
  AyMDPCConj acceptedEvidence
    (AyMDPCConj publicDimacsWitness publicSatClaim)

def AyMDPCNoClaimDiagnostic (diagnostic publicSatClaim : Prop) : Prop :=
  AyMDPCConj diagnostic (publicSatClaim -> False)

def AyMDPCRecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMDPCConj reason recomputeRequest

theorem ay_mdpc_conj_intro {left right : Prop} :
    left -> right -> AyMDPCConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_mdpc_conj_left {left right : Prop} :
    AyMDPCConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_mdpc_conj_right {left right : Prop} :
    AyMDPCConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_mdpc_disj_left {left right : Prop} :
    left -> AyMDPCDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_mdpc_disj_right {left right : Prop} :
    right -> AyMDPCDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_mdpc_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMDPCEquisat left right :=
  fun hf hb => ay_mdpc_conj_intro hf hb

theorem ay_mdpc_equisat_forward {left right : Prop} :
    AyMDPCEquisat left right -> left -> right :=
  fun h => ay_mdpc_conj_left h

theorem ay_mdpc_equisat_backward {left right : Prop} :
    AyMDPCEquisat left right -> right -> left :=
  fun h => ay_mdpc_conj_right h

theorem ay_mdpc_variable_map_intro
    {internalVariables dimacsVariables variableMapAgreement : Prop} :
    internalVariables ->
    dimacsVariables ->
    variableMapAgreement ->
    AyMDPCVariableMap
      internalVariables dimacsVariables variableMapAgreement :=
  fun hinternal hdimacs hagree =>
    ay_mdpc_conj_intro hinternal
      (ay_mdpc_conj_intro hdimacs hagree)

theorem ay_mdpc_variable_map_internal
    {internalVariables dimacsVariables variableMapAgreement : Prop} :
    AyMDPCVariableMap
      internalVariables dimacsVariables variableMapAgreement ->
    internalVariables :=
  fun h => ay_mdpc_conj_left h

theorem ay_mdpc_variable_map_dimacs
    {internalVariables dimacsVariables variableMapAgreement : Prop} :
    AyMDPCVariableMap
      internalVariables dimacsVariables variableMapAgreement ->
    dimacsVariables :=
  fun h => ay_mdpc_conj_left (ay_mdpc_conj_right h)

theorem ay_mdpc_variable_map_agreement
    {internalVariables dimacsVariables variableMapAgreement : Prop} :
    AyMDPCVariableMap
      internalVariables dimacsVariables variableMapAgreement ->
    variableMapAgreement :=
  fun h => ay_mdpc_conj_right (ay_mdpc_conj_right h)

theorem ay_mdpc_polarity_map_intro
    {internalPolarity dimacsPolarity polarityAgreement : Prop} :
    internalPolarity ->
    dimacsPolarity ->
    polarityAgreement ->
    AyMDPCPolarityMap
      internalPolarity dimacsPolarity polarityAgreement :=
  fun hinternal hdimacs hagree =>
    ay_mdpc_conj_intro hinternal
      (ay_mdpc_conj_intro hdimacs hagree)

theorem ay_mdpc_polarity_map_internal
    {internalPolarity dimacsPolarity polarityAgreement : Prop} :
    AyMDPCPolarityMap
      internalPolarity dimacsPolarity polarityAgreement ->
    internalPolarity :=
  fun h => ay_mdpc_conj_left h

theorem ay_mdpc_polarity_map_dimacs
    {internalPolarity dimacsPolarity polarityAgreement : Prop} :
    AyMDPCPolarityMap
      internalPolarity dimacsPolarity polarityAgreement ->
    dimacsPolarity :=
  fun h => ay_mdpc_conj_left (ay_mdpc_conj_right h)

theorem ay_mdpc_polarity_map_agreement
    {internalPolarity dimacsPolarity polarityAgreement : Prop} :
    AyMDPCPolarityMap
      internalPolarity dimacsPolarity polarityAgreement ->
    polarityAgreement :=
  fun h => ay_mdpc_conj_right (ay_mdpc_conj_right h)

theorem ay_mdpc_assignment_digest_intro
    {internalDigest dimacsDigest digestAgreement : Prop} :
    internalDigest ->
    dimacsDigest ->
    digestAgreement ->
    AyMDPCAssignmentDigest internalDigest dimacsDigest digestAgreement :=
  fun hinternal hdimacs hagree =>
    ay_mdpc_conj_intro hinternal
      (ay_mdpc_conj_intro hdimacs hagree)

theorem ay_mdpc_assignment_digest_internal
    {internalDigest dimacsDigest digestAgreement : Prop} :
    AyMDPCAssignmentDigest internalDigest dimacsDigest digestAgreement ->
    internalDigest :=
  fun h => ay_mdpc_conj_left h

theorem ay_mdpc_assignment_digest_dimacs
    {internalDigest dimacsDigest digestAgreement : Prop} :
    AyMDPCAssignmentDigest internalDigest dimacsDigest digestAgreement ->
    dimacsDigest :=
  fun h => ay_mdpc_conj_left (ay_mdpc_conj_right h)

theorem ay_mdpc_assignment_digest_agreement
    {internalDigest dimacsDigest digestAgreement : Prop} :
    AyMDPCAssignmentDigest internalDigest dimacsDigest digestAgreement ->
    digestAgreement :=
  fun h => ay_mdpc_conj_right (ay_mdpc_conj_right h)

theorem ay_mdpc_clause_evaluation_replay_intro
    {clauseReplay dimacsEvaluation evaluationAgreement : Prop} :
    clauseReplay ->
    dimacsEvaluation ->
    evaluationAgreement ->
    AyMDPCClauseEvaluationReplay
      clauseReplay dimacsEvaluation evaluationAgreement :=
  fun hreplay heval hagree =>
    ay_mdpc_conj_intro hreplay (ay_mdpc_conj_intro heval hagree)

theorem ay_mdpc_clause_evaluation_replay_trace
    {clauseReplay dimacsEvaluation evaluationAgreement : Prop} :
    AyMDPCClauseEvaluationReplay
      clauseReplay dimacsEvaluation evaluationAgreement ->
    clauseReplay :=
  fun h => ay_mdpc_conj_left h

theorem ay_mdpc_clause_evaluation_replay_evaluation
    {clauseReplay dimacsEvaluation evaluationAgreement : Prop} :
    AyMDPCClauseEvaluationReplay
      clauseReplay dimacsEvaluation evaluationAgreement ->
    dimacsEvaluation :=
  fun h => ay_mdpc_conj_left (ay_mdpc_conj_right h)

theorem ay_mdpc_clause_evaluation_replay_agreement
    {clauseReplay dimacsEvaluation evaluationAgreement : Prop} :
    AyMDPCClauseEvaluationReplay
      clauseReplay dimacsEvaluation evaluationAgreement ->
    evaluationAgreement :=
  fun h => ay_mdpc_conj_right (ay_mdpc_conj_right h)

theorem ay_mdpc_checker_replay_intro
    {checkerAccepted replayTrace : Prop} :
    checkerAccepted ->
    replayTrace ->
    AyMDPCCheckerReplay checkerAccepted replayTrace :=
  fun haccepted htrace => ay_mdpc_conj_intro haccepted htrace

theorem ay_mdpc_checker_replay_accepted
    {checkerAccepted replayTrace : Prop} :
    AyMDPCCheckerReplay checkerAccepted replayTrace -> checkerAccepted :=
  fun h => ay_mdpc_conj_left h

theorem ay_mdpc_checker_replay_trace
    {checkerAccepted replayTrace : Prop} :
    AyMDPCCheckerReplay checkerAccepted replayTrace -> replayTrace :=
  fun h => ay_mdpc_conj_right h

theorem ay_mdpc_solver_build_intro
    {solverBuild projectionBuild buildAgreement : Prop} :
    solverBuild ->
    projectionBuild ->
    buildAgreement ->
    AyMDPCSolverBuild solverBuild projectionBuild buildAgreement :=
  fun hsolver hprojection hagree =>
    ay_mdpc_conj_intro hsolver
      (ay_mdpc_conj_intro hprojection hagree)

theorem ay_mdpc_solver_build_solver
    {solverBuild projectionBuild buildAgreement : Prop} :
    AyMDPCSolverBuild solverBuild projectionBuild buildAgreement ->
    solverBuild :=
  fun h => ay_mdpc_conj_left h

theorem ay_mdpc_solver_build_projection
    {solverBuild projectionBuild buildAgreement : Prop} :
    AyMDPCSolverBuild solverBuild projectionBuild buildAgreement ->
    projectionBuild :=
  fun h => ay_mdpc_conj_left (ay_mdpc_conj_right h)

theorem ay_mdpc_solver_build_agreement
    {solverBuild projectionBuild buildAgreement : Prop} :
    AyMDPCSolverBuild solverBuild projectionBuild buildAgreement ->
    buildAgreement :=
  fun h => ay_mdpc_conj_right (ay_mdpc_conj_right h)

theorem ay_mdpc_original_fingerprint_intro
    {originalFingerprint projectionFingerprint fingerprintAgreement : Prop} :
    originalFingerprint ->
    projectionFingerprint ->
    fingerprintAgreement ->
    AyMDPCOriginalFingerprint
      originalFingerprint projectionFingerprint fingerprintAgreement :=
  fun horiginal hprojection hagree =>
    ay_mdpc_conj_intro horiginal
      (ay_mdpc_conj_intro hprojection hagree)

theorem ay_mdpc_original_fingerprint_original
    {originalFingerprint projectionFingerprint fingerprintAgreement : Prop} :
    AyMDPCOriginalFingerprint
      originalFingerprint projectionFingerprint fingerprintAgreement ->
    originalFingerprint :=
  fun h => ay_mdpc_conj_left h

theorem ay_mdpc_original_fingerprint_projection
    {originalFingerprint projectionFingerprint fingerprintAgreement : Prop} :
    AyMDPCOriginalFingerprint
      originalFingerprint projectionFingerprint fingerprintAgreement ->
    projectionFingerprint :=
  fun h => ay_mdpc_conj_left (ay_mdpc_conj_right h)

theorem ay_mdpc_original_fingerprint_agreement
    {originalFingerprint projectionFingerprint fingerprintAgreement : Prop} :
    AyMDPCOriginalFingerprint
      originalFingerprint projectionFingerprint fingerprintAgreement ->
    fingerprintAgreement :=
  fun h => ay_mdpc_conj_right (ay_mdpc_conj_right h)

theorem ay_mdpc_accepted_evidence_intro
    {variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    variableMapOk ->
    polarityMapOk ->
    digestOk ->
    clauseReplayOk ->
    checkerOk ->
    buildOk ->
    fingerprintOk ->
    AyMDPCAcceptedEvidence
      variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk :=
  fun hvariable hpolarity hdigest hclause hchecker hbuild hfingerprint =>
    ay_mdpc_conj_intro hvariable
      (ay_mdpc_conj_intro hpolarity
        (ay_mdpc_conj_intro hdigest
          (ay_mdpc_conj_intro hclause
            (ay_mdpc_conj_intro hchecker
              (ay_mdpc_conj_intro hbuild hfingerprint)))))

theorem ay_mdpc_accepted_evidence_variable_map
    {variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMDPCAcceptedEvidence
      variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    variableMapOk :=
  fun h => ay_mdpc_conj_left h

theorem ay_mdpc_accepted_evidence_polarity_map
    {variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMDPCAcceptedEvidence
      variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    polarityMapOk :=
  fun h => ay_mdpc_conj_left (ay_mdpc_conj_right h)

theorem ay_mdpc_accepted_evidence_digest
    {variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMDPCAcceptedEvidence
      variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    digestOk :=
  fun h => ay_mdpc_conj_left
    (ay_mdpc_conj_right (ay_mdpc_conj_right h))

theorem ay_mdpc_accepted_evidence_clause_replay
    {variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMDPCAcceptedEvidence
      variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    clauseReplayOk :=
  fun h => ay_mdpc_conj_left
    (ay_mdpc_conj_right
      (ay_mdpc_conj_right (ay_mdpc_conj_right h)))

theorem ay_mdpc_accepted_evidence_checker
    {variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMDPCAcceptedEvidence
      variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    checkerOk :=
  fun h => ay_mdpc_conj_left
    (ay_mdpc_conj_right
      (ay_mdpc_conj_right
        (ay_mdpc_conj_right (ay_mdpc_conj_right h))))

theorem ay_mdpc_accepted_evidence_build
    {variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMDPCAcceptedEvidence
      variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    buildOk :=
  fun h => ay_mdpc_conj_left
    (ay_mdpc_conj_right
      (ay_mdpc_conj_right
        (ay_mdpc_conj_right
          (ay_mdpc_conj_right (ay_mdpc_conj_right h)))))

theorem ay_mdpc_accepted_evidence_fingerprint
    {variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMDPCAcceptedEvidence
      variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    fingerprintOk :=
  fun h => ay_mdpc_conj_right
    (ay_mdpc_conj_right
      (ay_mdpc_conj_right
        (ay_mdpc_conj_right
          (ay_mdpc_conj_right (ay_mdpc_conj_right h)))))

theorem ay_mdpc_public_sat_witness_intro
    {acceptedEvidence publicDimacsWitness publicSatClaim : Prop} :
    acceptedEvidence ->
    publicDimacsWitness ->
    publicSatClaim ->
    AyMDPCPublicSatWitness
      acceptedEvidence publicDimacsWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_mdpc_conj_intro hevidence
      (ay_mdpc_conj_intro hwitness hclaim)

theorem ay_mdpc_public_sat_witness_evidence
    {acceptedEvidence publicDimacsWitness publicSatClaim : Prop} :
    AyMDPCPublicSatWitness
      acceptedEvidence publicDimacsWitness publicSatClaim ->
    acceptedEvidence :=
  fun h => ay_mdpc_conj_left h

theorem ay_mdpc_public_sat_witness_witness
    {acceptedEvidence publicDimacsWitness publicSatClaim : Prop} :
    AyMDPCPublicSatWitness
      acceptedEvidence publicDimacsWitness publicSatClaim ->
    publicDimacsWitness :=
  fun h => ay_mdpc_conj_left (ay_mdpc_conj_right h)

theorem ay_mdpc_public_sat_witness_claim
    {acceptedEvidence publicDimacsWitness publicSatClaim : Prop} :
    AyMDPCPublicSatWitness
      acceptedEvidence publicDimacsWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_mdpc_conj_right (ay_mdpc_conj_right h)

theorem ay_mdpc_accepted_projection_emits_sound_public_sat
    {variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicDimacsWitness publicSatClaim : Prop} :
    AyMDPCAcceptedEvidence
      variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    publicDimacsWitness ->
    publicSatClaim ->
    AyMDPCPublicSatWitness
      (AyMDPCAcceptedEvidence
        variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicDimacsWitness
      publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_mdpc_public_sat_witness_intro hevidence hwitness hclaim

theorem ay_mdpc_public_sat_requires_accepted_evidence
    {acceptedEvidence publicDimacsWitness publicSatClaim : Prop} :
    AyMDPCPublicSatWitness
      acceptedEvidence publicDimacsWitness publicSatClaim ->
    acceptedEvidence :=
  fun h => ay_mdpc_public_sat_witness_evidence h

theorem ay_mdpc_internal_order_hints_preserve_truth
    {internalTruth dimacsTruth : Prop} :
    AyMDPCEquisat internalTruth dimacsTruth ->
    internalTruth ->
    dimacsTruth :=
  fun heq hinternal => ay_mdpc_equisat_forward heq hinternal

theorem ay_mdpc_clause_replay_transports_truth
    {clauseReplay dimacsEvaluation formulaTruth : Prop} :
    AyMDPCClauseEvaluationReplay
      clauseReplay dimacsEvaluation formulaTruth ->
    formulaTruth :=
  fun h => ay_mdpc_clause_evaluation_replay_agreement h

theorem ay_mdpc_publication_requires_variable_map
    {variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicDimacsWitness publicSatClaim : Prop} :
    AyMDPCPublicSatWitness
      (AyMDPCAcceptedEvidence
        variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicDimacsWitness
      publicSatClaim ->
    variableMapOk :=
  fun h =>
    ay_mdpc_accepted_evidence_variable_map
      (ay_mdpc_public_sat_witness_evidence h)

theorem ay_mdpc_publication_requires_polarity_map
    {variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicDimacsWitness publicSatClaim : Prop} :
    AyMDPCPublicSatWitness
      (AyMDPCAcceptedEvidence
        variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicDimacsWitness
      publicSatClaim ->
    polarityMapOk :=
  fun h =>
    ay_mdpc_accepted_evidence_polarity_map
      (ay_mdpc_public_sat_witness_evidence h)

theorem ay_mdpc_publication_requires_digest
    {variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicDimacsWitness publicSatClaim : Prop} :
    AyMDPCPublicSatWitness
      (AyMDPCAcceptedEvidence
        variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicDimacsWitness
      publicSatClaim ->
    digestOk :=
  fun h =>
    ay_mdpc_accepted_evidence_digest
      (ay_mdpc_public_sat_witness_evidence h)

theorem ay_mdpc_publication_requires_clause_replay
    {variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicDimacsWitness publicSatClaim : Prop} :
    AyMDPCPublicSatWitness
      (AyMDPCAcceptedEvidence
        variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicDimacsWitness
      publicSatClaim ->
    clauseReplayOk :=
  fun h =>
    ay_mdpc_accepted_evidence_clause_replay
      (ay_mdpc_public_sat_witness_evidence h)

theorem ay_mdpc_publication_requires_checker
    {variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicDimacsWitness publicSatClaim : Prop} :
    AyMDPCPublicSatWitness
      (AyMDPCAcceptedEvidence
        variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicDimacsWitness
      publicSatClaim ->
    checkerOk :=
  fun h =>
    ay_mdpc_accepted_evidence_checker
      (ay_mdpc_public_sat_witness_evidence h)

theorem ay_mdpc_publication_requires_build
    {variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicDimacsWitness publicSatClaim : Prop} :
    AyMDPCPublicSatWitness
      (AyMDPCAcceptedEvidence
        variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicDimacsWitness
      publicSatClaim ->
    buildOk :=
  fun h =>
    ay_mdpc_accepted_evidence_build
      (ay_mdpc_public_sat_witness_evidence h)

theorem ay_mdpc_publication_requires_fingerprint
    {variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicDimacsWitness publicSatClaim : Prop} :
    AyMDPCPublicSatWitness
      (AyMDPCAcceptedEvidence
        variableMapOk polarityMapOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicDimacsWitness
      publicSatClaim ->
    fingerprintOk :=
  fun h =>
    ay_mdpc_accepted_evidence_fingerprint
      (ay_mdpc_public_sat_witness_evidence h)

theorem ay_mdpc_no_claim_diagnostic_intro
    {diagnostic publicSatClaim : Prop} :
    diagnostic ->
    (publicSatClaim -> False) ->
    AyMDPCNoClaimDiagnostic diagnostic publicSatClaim :=
  fun hdiagnostic hblocks =>
    ay_mdpc_conj_intro hdiagnostic hblocks

theorem ay_mdpc_no_claim_diagnostic_reason
    {diagnostic publicSatClaim : Prop} :
    AyMDPCNoClaimDiagnostic diagnostic publicSatClaim -> diagnostic :=
  fun h => ay_mdpc_conj_left h

theorem ay_mdpc_no_claim_diagnostic_blocks
    {diagnostic publicSatClaim : Prop} :
    AyMDPCNoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h => ay_mdpc_conj_right h

theorem ay_mdpc_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMDPCRecomputeObligation reason recomputeRequest :=
  fun hreason hrecompute => ay_mdpc_conj_intro hreason hrecompute

theorem ay_mdpc_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMDPCRecomputeObligation reason recomputeRequest -> reason :=
  fun h => ay_mdpc_conj_left h

theorem ay_mdpc_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMDPCRecomputeObligation reason recomputeRequest -> recomputeRequest :=
  fun h => ay_mdpc_conj_right h

theorem ay_mdpc_map_drift_recompute
    {mapDrift recomputeRequest : Prop} :
    mapDrift ->
    recomputeRequest ->
    AyMDPCRecomputeObligation mapDrift recomputeRequest :=
  fun hdrift hrecompute =>
    ay_mdpc_recompute_obligation_intro hdrift hrecompute

theorem ay_mdpc_map_drift_no_claim
    {mapDrift publicSatClaim : Prop} :
    mapDrift ->
    (publicSatClaim -> False) ->
    AyMDPCNoClaimDiagnostic mapDrift publicSatClaim :=
  fun hdrift hblocks => ay_mdpc_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mdpc_polarity_drift_recompute
    {polarityDrift recomputeRequest : Prop} :
    polarityDrift ->
    recomputeRequest ->
    AyMDPCRecomputeObligation polarityDrift recomputeRequest :=
  fun hdrift hrecompute =>
    ay_mdpc_recompute_obligation_intro hdrift hrecompute

theorem ay_mdpc_polarity_drift_no_claim
    {polarityDrift publicSatClaim : Prop} :
    polarityDrift ->
    (publicSatClaim -> False) ->
    AyMDPCNoClaimDiagnostic polarityDrift publicSatClaim :=
  fun hdrift hblocks => ay_mdpc_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mdpc_checker_rejection_no_claim
    {checkerRejection publicSatClaim : Prop} :
    checkerRejection ->
    (publicSatClaim -> False) ->
    AyMDPCNoClaimDiagnostic checkerRejection publicSatClaim :=
  fun hreject hblocks =>
    ay_mdpc_no_claim_diagnostic_intro hreject hblocks

theorem ay_mdpc_digest_mismatch_no_claim
    {digestMismatch publicSatClaim : Prop} :
    digestMismatch ->
    (publicSatClaim -> False) ->
    AyMDPCNoClaimDiagnostic digestMismatch publicSatClaim :=
  fun hmismatch hblocks =>
    ay_mdpc_no_claim_diagnostic_intro hmismatch hblocks

theorem ay_mdpc_build_drift_no_claim
    {buildDrift publicSatClaim : Prop} :
    buildDrift ->
    (publicSatClaim -> False) ->
    AyMDPCNoClaimDiagnostic buildDrift publicSatClaim :=
  fun hdrift hblocks => ay_mdpc_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mdpc_fingerprint_mismatch_no_claim
    {fingerprintMismatch publicSatClaim : Prop} :
    fingerprintMismatch ->
    (publicSatClaim -> False) ->
    AyMDPCNoClaimDiagnostic fingerprintMismatch publicSatClaim :=
  fun hmismatch hblocks =>
    ay_mdpc_no_claim_diagnostic_intro hmismatch hblocks

theorem ay_mdpc_diagnostic_blocks_public_claim
    {diagnostic publicSatClaim : Prop} :
    AyMDPCNoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_mdpc_no_claim_diagnostic_blocks h hclaim

theorem ay_mdpc_bad_dimacs_projection_cannot_emit_sat
    {badProjection publicSatClaim : Prop} :
    AyMDPCNoClaimDiagnostic badProjection publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_mdpc_diagnostic_blocks_public_claim h hclaim
