-- SAT-COMP/ay polarity default roundtrip soundness skeleton.
-- Default polarity assignments and omitted polarity-default literals are sound
-- only under accepted default maps, coverage, replay, digest, build, and
-- fingerprint evidence.

def AyMPDRConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMPDRDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMPDREquisat (left right : Prop) : Prop :=
  AyMPDRConj (left -> right) (right -> left)

def AyMPDRPolarityDefaultMap
    (declaredDefaults omittedPolarityLiterals defaultAgreement : Prop) : Prop :=
  AyMPDRConj declaredDefaults
    (AyMPDRConj omittedPolarityLiterals defaultAgreement)

def AyMPDRCoverageLedger
    (coveredVariables defaultedVariables coverageAgreement : Prop) : Prop :=
  AyMPDRConj coveredVariables
    (AyMPDRConj defaultedVariables coverageAgreement)

def AyMPDRAssignmentDigest
    (explicitDigest defaultedDigest digestAgreement : Prop) : Prop :=
  AyMPDRConj explicitDigest (AyMPDRConj defaultedDigest digestAgreement)

def AyMPDRClauseEvaluationReplay
    (clauseReplay defaultedEvaluation evaluationAgreement : Prop) : Prop :=
  AyMPDRConj clauseReplay
    (AyMPDRConj defaultedEvaluation evaluationAgreement)

def AyMPDRCheckerReplay (checkerAccepted replayTrace : Prop) : Prop :=
  AyMPDRConj checkerAccepted replayTrace

def AyMPDRSolverBuild
    (solverBuild defaultBuild buildAgreement : Prop) : Prop :=
  AyMPDRConj solverBuild (AyMPDRConj defaultBuild buildAgreement)

def AyMPDROriginalFingerprint
    (originalFingerprint defaultFingerprint fingerprintAgreement : Prop) :
    Prop :=
  AyMPDRConj originalFingerprint
    (AyMPDRConj defaultFingerprint fingerprintAgreement)

def AyMPDRAcceptedEvidence
    (defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop) : Prop :=
  AyMPDRConj defaultMapOk
    (AyMPDRConj coverageOk
      (AyMPDRConj digestOk
        (AyMPDRConj clauseReplayOk
          (AyMPDRConj checkerOk
            (AyMPDRConj buildOk fingerprintOk)))))

def AyMPDRPublicSatWitness
    (acceptedEvidence publicWitness publicSatClaim : Prop) : Prop :=
  AyMPDRConj acceptedEvidence
    (AyMPDRConj publicWitness publicSatClaim)

def AyMPDRNoClaimDiagnostic (diagnostic publicSatClaim : Prop) : Prop :=
  AyMPDRConj diagnostic (publicSatClaim -> False)

def AyMPDRRecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMPDRConj reason recomputeRequest

theorem ay_mpdr_conj_intro {left right : Prop} :
    left -> right -> AyMPDRConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_mpdr_conj_left {left right : Prop} :
    AyMPDRConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_mpdr_conj_right {left right : Prop} :
    AyMPDRConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_mpdr_disj_left {left right : Prop} :
    left -> AyMPDRDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_mpdr_disj_right {left right : Prop} :
    right -> AyMPDRDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_mpdr_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMPDREquisat left right :=
  fun hf hb => ay_mpdr_conj_intro hf hb

theorem ay_mpdr_equisat_forward {left right : Prop} :
    AyMPDREquisat left right -> left -> right :=
  fun h => ay_mpdr_conj_left h

theorem ay_mpdr_equisat_backward {left right : Prop} :
    AyMPDREquisat left right -> right -> left :=
  fun h => ay_mpdr_conj_right h

theorem ay_mpdr_polarity_default_map_intro
    {declaredDefaults omittedPolarityLiterals defaultAgreement : Prop} :
    declaredDefaults ->
    omittedPolarityLiterals ->
    defaultAgreement ->
    AyMPDRPolarityDefaultMap
      declaredDefaults omittedPolarityLiterals defaultAgreement :=
  fun hdeclared homitted hagree =>
    ay_mpdr_conj_intro hdeclared
      (ay_mpdr_conj_intro homitted hagree)

theorem ay_mpdr_polarity_default_map_declared
    {declaredDefaults omittedPolarityLiterals defaultAgreement : Prop} :
    AyMPDRPolarityDefaultMap
      declaredDefaults omittedPolarityLiterals defaultAgreement ->
    declaredDefaults :=
  fun h => ay_mpdr_conj_left h

theorem ay_mpdr_polarity_default_map_omitted
    {declaredDefaults omittedPolarityLiterals defaultAgreement : Prop} :
    AyMPDRPolarityDefaultMap
      declaredDefaults omittedPolarityLiterals defaultAgreement ->
    omittedPolarityLiterals :=
  fun h => ay_mpdr_conj_left (ay_mpdr_conj_right h)

theorem ay_mpdr_polarity_default_map_agreement
    {declaredDefaults omittedPolarityLiterals defaultAgreement : Prop} :
    AyMPDRPolarityDefaultMap
      declaredDefaults omittedPolarityLiterals defaultAgreement ->
    defaultAgreement :=
  fun h => ay_mpdr_conj_right (ay_mpdr_conj_right h)

theorem ay_mpdr_coverage_ledger_intro
    {coveredVariables defaultedVariables coverageAgreement : Prop} :
    coveredVariables ->
    defaultedVariables ->
    coverageAgreement ->
    AyMPDRCoverageLedger
      coveredVariables defaultedVariables coverageAgreement :=
  fun hcovered hdefaulted hagree =>
    ay_mpdr_conj_intro hcovered
      (ay_mpdr_conj_intro hdefaulted hagree)

theorem ay_mpdr_coverage_ledger_covered
    {coveredVariables defaultedVariables coverageAgreement : Prop} :
    AyMPDRCoverageLedger
      coveredVariables defaultedVariables coverageAgreement ->
    coveredVariables :=
  fun h => ay_mpdr_conj_left h

theorem ay_mpdr_coverage_ledger_defaulted
    {coveredVariables defaultedVariables coverageAgreement : Prop} :
    AyMPDRCoverageLedger
      coveredVariables defaultedVariables coverageAgreement ->
    defaultedVariables :=
  fun h => ay_mpdr_conj_left (ay_mpdr_conj_right h)

theorem ay_mpdr_coverage_ledger_agreement
    {coveredVariables defaultedVariables coverageAgreement : Prop} :
    AyMPDRCoverageLedger
      coveredVariables defaultedVariables coverageAgreement ->
    coverageAgreement :=
  fun h => ay_mpdr_conj_right (ay_mpdr_conj_right h)

theorem ay_mpdr_assignment_digest_intro
    {explicitDigest defaultedDigest digestAgreement : Prop} :
    explicitDigest ->
    defaultedDigest ->
    digestAgreement ->
    AyMPDRAssignmentDigest explicitDigest defaultedDigest digestAgreement :=
  fun hexplicit hdefaulted hagree =>
    ay_mpdr_conj_intro hexplicit
      (ay_mpdr_conj_intro hdefaulted hagree)

theorem ay_mpdr_assignment_digest_explicit
    {explicitDigest defaultedDigest digestAgreement : Prop} :
    AyMPDRAssignmentDigest explicitDigest defaultedDigest digestAgreement ->
    explicitDigest :=
  fun h => ay_mpdr_conj_left h

theorem ay_mpdr_assignment_digest_defaulted
    {explicitDigest defaultedDigest digestAgreement : Prop} :
    AyMPDRAssignmentDigest explicitDigest defaultedDigest digestAgreement ->
    defaultedDigest :=
  fun h => ay_mpdr_conj_left (ay_mpdr_conj_right h)

theorem ay_mpdr_assignment_digest_agreement
    {explicitDigest defaultedDigest digestAgreement : Prop} :
    AyMPDRAssignmentDigest explicitDigest defaultedDigest digestAgreement ->
    digestAgreement :=
  fun h => ay_mpdr_conj_right (ay_mpdr_conj_right h)

theorem ay_mpdr_clause_evaluation_replay_intro
    {clauseReplay defaultedEvaluation evaluationAgreement : Prop} :
    clauseReplay ->
    defaultedEvaluation ->
    evaluationAgreement ->
    AyMPDRClauseEvaluationReplay
      clauseReplay defaultedEvaluation evaluationAgreement :=
  fun hreplay hevaluation hagree =>
    ay_mpdr_conj_intro hreplay
      (ay_mpdr_conj_intro hevaluation hagree)

theorem ay_mpdr_clause_evaluation_replay_trace
    {clauseReplay defaultedEvaluation evaluationAgreement : Prop} :
    AyMPDRClauseEvaluationReplay
      clauseReplay defaultedEvaluation evaluationAgreement ->
    clauseReplay :=
  fun h => ay_mpdr_conj_left h

theorem ay_mpdr_clause_evaluation_replay_evaluation
    {clauseReplay defaultedEvaluation evaluationAgreement : Prop} :
    AyMPDRClauseEvaluationReplay
      clauseReplay defaultedEvaluation evaluationAgreement ->
    defaultedEvaluation :=
  fun h => ay_mpdr_conj_left (ay_mpdr_conj_right h)

theorem ay_mpdr_clause_evaluation_replay_agreement
    {clauseReplay defaultedEvaluation evaluationAgreement : Prop} :
    AyMPDRClauseEvaluationReplay
      clauseReplay defaultedEvaluation evaluationAgreement ->
    evaluationAgreement :=
  fun h => ay_mpdr_conj_right (ay_mpdr_conj_right h)

theorem ay_mpdr_checker_replay_intro
    {checkerAccepted replayTrace : Prop} :
    checkerAccepted ->
    replayTrace ->
    AyMPDRCheckerReplay checkerAccepted replayTrace :=
  fun haccepted htrace => ay_mpdr_conj_intro haccepted htrace

theorem ay_mpdr_checker_replay_accepted
    {checkerAccepted replayTrace : Prop} :
    AyMPDRCheckerReplay checkerAccepted replayTrace -> checkerAccepted :=
  fun h => ay_mpdr_conj_left h

theorem ay_mpdr_checker_replay_trace
    {checkerAccepted replayTrace : Prop} :
    AyMPDRCheckerReplay checkerAccepted replayTrace -> replayTrace :=
  fun h => ay_mpdr_conj_right h

theorem ay_mpdr_solver_build_intro
    {solverBuild defaultBuild buildAgreement : Prop} :
    solverBuild ->
    defaultBuild ->
    buildAgreement ->
    AyMPDRSolverBuild solverBuild defaultBuild buildAgreement :=
  fun hsolver hdefault hagree =>
    ay_mpdr_conj_intro hsolver
      (ay_mpdr_conj_intro hdefault hagree)

theorem ay_mpdr_solver_build_solver
    {solverBuild defaultBuild buildAgreement : Prop} :
    AyMPDRSolverBuild solverBuild defaultBuild buildAgreement ->
    solverBuild :=
  fun h => ay_mpdr_conj_left h

theorem ay_mpdr_solver_build_default
    {solverBuild defaultBuild buildAgreement : Prop} :
    AyMPDRSolverBuild solverBuild defaultBuild buildAgreement ->
    defaultBuild :=
  fun h => ay_mpdr_conj_left (ay_mpdr_conj_right h)

theorem ay_mpdr_solver_build_agreement
    {solverBuild defaultBuild buildAgreement : Prop} :
    AyMPDRSolverBuild solverBuild defaultBuild buildAgreement ->
    buildAgreement :=
  fun h => ay_mpdr_conj_right (ay_mpdr_conj_right h)

theorem ay_mpdr_original_fingerprint_intro
    {originalFingerprint defaultFingerprint fingerprintAgreement : Prop} :
    originalFingerprint ->
    defaultFingerprint ->
    fingerprintAgreement ->
    AyMPDROriginalFingerprint
      originalFingerprint defaultFingerprint fingerprintAgreement :=
  fun horiginal hdefault hagree =>
    ay_mpdr_conj_intro horiginal
      (ay_mpdr_conj_intro hdefault hagree)

theorem ay_mpdr_original_fingerprint_original
    {originalFingerprint defaultFingerprint fingerprintAgreement : Prop} :
    AyMPDROriginalFingerprint
      originalFingerprint defaultFingerprint fingerprintAgreement ->
    originalFingerprint :=
  fun h => ay_mpdr_conj_left h

theorem ay_mpdr_original_fingerprint_default
    {originalFingerprint defaultFingerprint fingerprintAgreement : Prop} :
    AyMPDROriginalFingerprint
      originalFingerprint defaultFingerprint fingerprintAgreement ->
    defaultFingerprint :=
  fun h => ay_mpdr_conj_left (ay_mpdr_conj_right h)

theorem ay_mpdr_original_fingerprint_agreement
    {originalFingerprint defaultFingerprint fingerprintAgreement : Prop} :
    AyMPDROriginalFingerprint
      originalFingerprint defaultFingerprint fingerprintAgreement ->
    fingerprintAgreement :=
  fun h => ay_mpdr_conj_right (ay_mpdr_conj_right h)

theorem ay_mpdr_accepted_evidence_intro
    {defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    defaultMapOk ->
    coverageOk ->
    digestOk ->
    clauseReplayOk ->
    checkerOk ->
    buildOk ->
    fingerprintOk ->
    AyMPDRAcceptedEvidence
      defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk :=
  fun hdefault hcoverage hdigest hclause hchecker hbuild hfingerprint =>
    ay_mpdr_conj_intro hdefault
      (ay_mpdr_conj_intro hcoverage
        (ay_mpdr_conj_intro hdigest
          (ay_mpdr_conj_intro hclause
            (ay_mpdr_conj_intro hchecker
              (ay_mpdr_conj_intro hbuild hfingerprint)))))

theorem ay_mpdr_accepted_evidence_default_map
    {defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMPDRAcceptedEvidence
      defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    defaultMapOk :=
  fun h => ay_mpdr_conj_left h

theorem ay_mpdr_accepted_evidence_coverage
    {defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMPDRAcceptedEvidence
      defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    coverageOk :=
  fun h => ay_mpdr_conj_left (ay_mpdr_conj_right h)

theorem ay_mpdr_accepted_evidence_digest
    {defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMPDRAcceptedEvidence
      defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    digestOk :=
  fun h => ay_mpdr_conj_left
    (ay_mpdr_conj_right (ay_mpdr_conj_right h))

theorem ay_mpdr_accepted_evidence_clause_replay
    {defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMPDRAcceptedEvidence
      defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    clauseReplayOk :=
  fun h => ay_mpdr_conj_left
    (ay_mpdr_conj_right
      (ay_mpdr_conj_right (ay_mpdr_conj_right h)))

theorem ay_mpdr_accepted_evidence_checker
    {defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMPDRAcceptedEvidence
      defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    checkerOk :=
  fun h => ay_mpdr_conj_left
    (ay_mpdr_conj_right
      (ay_mpdr_conj_right
        (ay_mpdr_conj_right (ay_mpdr_conj_right h))))

theorem ay_mpdr_accepted_evidence_build
    {defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMPDRAcceptedEvidence
      defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    buildOk :=
  fun h => ay_mpdr_conj_left
    (ay_mpdr_conj_right
      (ay_mpdr_conj_right
        (ay_mpdr_conj_right
          (ay_mpdr_conj_right (ay_mpdr_conj_right h)))))

theorem ay_mpdr_accepted_evidence_fingerprint
    {defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMPDRAcceptedEvidence
      defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    fingerprintOk :=
  fun h => ay_mpdr_conj_right
    (ay_mpdr_conj_right
      (ay_mpdr_conj_right
        (ay_mpdr_conj_right
          (ay_mpdr_conj_right (ay_mpdr_conj_right h)))))

theorem ay_mpdr_public_sat_witness_intro
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    acceptedEvidence ->
    publicWitness ->
    publicSatClaim ->
    AyMPDRPublicSatWitness acceptedEvidence publicWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_mpdr_conj_intro hevidence
      (ay_mpdr_conj_intro hwitness hclaim)

theorem ay_mpdr_public_sat_witness_evidence
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMPDRPublicSatWitness acceptedEvidence publicWitness publicSatClaim ->
    acceptedEvidence :=
  fun h => ay_mpdr_conj_left h

theorem ay_mpdr_public_sat_witness_witness
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMPDRPublicSatWitness acceptedEvidence publicWitness publicSatClaim ->
    publicWitness :=
  fun h => ay_mpdr_conj_left (ay_mpdr_conj_right h)

theorem ay_mpdr_public_sat_witness_claim
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMPDRPublicSatWitness acceptedEvidence publicWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_mpdr_conj_right (ay_mpdr_conj_right h)

theorem ay_mpdr_accepted_polarity_defaults_emit_sound_public_sat
    {defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMPDRAcceptedEvidence
      defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    publicWitness ->
    publicSatClaim ->
    AyMPDRPublicSatWitness
      (AyMPDRAcceptedEvidence
        defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_mpdr_public_sat_witness_intro hevidence hwitness hclaim

theorem ay_mpdr_public_sat_requires_accepted_evidence
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMPDRPublicSatWitness acceptedEvidence publicWitness publicSatClaim ->
    acceptedEvidence :=
  fun h => ay_mpdr_public_sat_witness_evidence h

theorem ay_mpdr_default_polarity_hints_preserve_truth
    {explicitTruth defaultedTruth : Prop} :
    AyMPDREquisat explicitTruth defaultedTruth ->
    explicitTruth ->
    defaultedTruth :=
  fun heq hexplicit => ay_mpdr_equisat_forward heq hexplicit

theorem ay_mpdr_clause_replay_transports_truth
    {clauseReplay defaultedEvaluation formulaTruth : Prop} :
    AyMPDRClauseEvaluationReplay
      clauseReplay defaultedEvaluation formulaTruth ->
    formulaTruth :=
  fun h => ay_mpdr_clause_evaluation_replay_agreement h

theorem ay_mpdr_publication_requires_default_map
    {defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMPDRPublicSatWitness
      (AyMPDRAcceptedEvidence
        defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    defaultMapOk :=
  fun h =>
    ay_mpdr_accepted_evidence_default_map
      (ay_mpdr_public_sat_witness_evidence h)

theorem ay_mpdr_publication_requires_coverage
    {defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMPDRPublicSatWitness
      (AyMPDRAcceptedEvidence
        defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    coverageOk :=
  fun h =>
    ay_mpdr_accepted_evidence_coverage
      (ay_mpdr_public_sat_witness_evidence h)

theorem ay_mpdr_publication_requires_digest
    {defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMPDRPublicSatWitness
      (AyMPDRAcceptedEvidence
        defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    digestOk :=
  fun h =>
    ay_mpdr_accepted_evidence_digest
      (ay_mpdr_public_sat_witness_evidence h)

theorem ay_mpdr_publication_requires_clause_replay
    {defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMPDRPublicSatWitness
      (AyMPDRAcceptedEvidence
        defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    clauseReplayOk :=
  fun h =>
    ay_mpdr_accepted_evidence_clause_replay
      (ay_mpdr_public_sat_witness_evidence h)

theorem ay_mpdr_publication_requires_checker
    {defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMPDRPublicSatWitness
      (AyMPDRAcceptedEvidence
        defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    checkerOk :=
  fun h =>
    ay_mpdr_accepted_evidence_checker
      (ay_mpdr_public_sat_witness_evidence h)

theorem ay_mpdr_publication_requires_build
    {defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMPDRPublicSatWitness
      (AyMPDRAcceptedEvidence
        defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    buildOk :=
  fun h =>
    ay_mpdr_accepted_evidence_build
      (ay_mpdr_public_sat_witness_evidence h)

theorem ay_mpdr_publication_requires_fingerprint
    {defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMPDRPublicSatWitness
      (AyMPDRAcceptedEvidence
        defaultMapOk coverageOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    fingerprintOk :=
  fun h =>
    ay_mpdr_accepted_evidence_fingerprint
      (ay_mpdr_public_sat_witness_evidence h)

theorem ay_mpdr_no_claim_diagnostic_intro
    {diagnostic publicSatClaim : Prop} :
    diagnostic ->
    (publicSatClaim -> False) ->
    AyMPDRNoClaimDiagnostic diagnostic publicSatClaim :=
  fun hdiagnostic hblocks =>
    ay_mpdr_conj_intro hdiagnostic hblocks

theorem ay_mpdr_no_claim_diagnostic_reason
    {diagnostic publicSatClaim : Prop} :
    AyMPDRNoClaimDiagnostic diagnostic publicSatClaim -> diagnostic :=
  fun h => ay_mpdr_conj_left h

theorem ay_mpdr_no_claim_diagnostic_blocks
    {diagnostic publicSatClaim : Prop} :
    AyMPDRNoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h => ay_mpdr_conj_right h

theorem ay_mpdr_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMPDRRecomputeObligation reason recomputeRequest :=
  fun hreason hrecompute => ay_mpdr_conj_intro hreason hrecompute

theorem ay_mpdr_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMPDRRecomputeObligation reason recomputeRequest -> reason :=
  fun h => ay_mpdr_conj_left h

theorem ay_mpdr_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMPDRRecomputeObligation reason recomputeRequest -> recomputeRequest :=
  fun h => ay_mpdr_conj_right h

theorem ay_mpdr_polarity_default_drift_recompute
    {polarityDefaultDrift recomputeRequest : Prop} :
    polarityDefaultDrift ->
    recomputeRequest ->
    AyMPDRRecomputeObligation polarityDefaultDrift recomputeRequest :=
  fun hdrift hrecompute =>
    ay_mpdr_recompute_obligation_intro hdrift hrecompute

theorem ay_mpdr_polarity_default_drift_no_claim
    {polarityDefaultDrift publicSatClaim : Prop} :
    polarityDefaultDrift ->
    (publicSatClaim -> False) ->
    AyMPDRNoClaimDiagnostic polarityDefaultDrift publicSatClaim :=
  fun hdrift hblocks => ay_mpdr_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mpdr_coverage_drift_no_claim
    {coverageDrift publicSatClaim : Prop} :
    coverageDrift ->
    (publicSatClaim -> False) ->
    AyMPDRNoClaimDiagnostic coverageDrift publicSatClaim :=
  fun hdrift hblocks => ay_mpdr_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mpdr_checker_rejection_no_claim
    {checkerRejection publicSatClaim : Prop} :
    checkerRejection ->
    (publicSatClaim -> False) ->
    AyMPDRNoClaimDiagnostic checkerRejection publicSatClaim :=
  fun hreject hblocks =>
    ay_mpdr_no_claim_diagnostic_intro hreject hblocks

theorem ay_mpdr_digest_mismatch_no_claim
    {digestMismatch publicSatClaim : Prop} :
    digestMismatch ->
    (publicSatClaim -> False) ->
    AyMPDRNoClaimDiagnostic digestMismatch publicSatClaim :=
  fun hmismatch hblocks =>
    ay_mpdr_no_claim_diagnostic_intro hmismatch hblocks

theorem ay_mpdr_build_drift_no_claim
    {buildDrift publicSatClaim : Prop} :
    buildDrift ->
    (publicSatClaim -> False) ->
    AyMPDRNoClaimDiagnostic buildDrift publicSatClaim :=
  fun hdrift hblocks => ay_mpdr_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mpdr_fingerprint_mismatch_no_claim
    {fingerprintMismatch publicSatClaim : Prop} :
    fingerprintMismatch ->
    (publicSatClaim -> False) ->
    AyMPDRNoClaimDiagnostic fingerprintMismatch publicSatClaim :=
  fun hmismatch hblocks =>
    ay_mpdr_no_claim_diagnostic_intro hmismatch hblocks

theorem ay_mpdr_diagnostic_blocks_public_claim
    {diagnostic publicSatClaim : Prop} :
    AyMPDRNoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_mpdr_no_claim_diagnostic_blocks h hclaim

theorem ay_mpdr_bad_polarity_defaults_cannot_emit_sat
    {badPolarityDefaults publicSatClaim : Prop} :
    AyMPDRNoClaimDiagnostic badPolarityDefaults publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_mpdr_diagnostic_blocks_public_claim h hclaim
