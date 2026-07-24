-- SAT-COMP/ay witness minimization projection soundness skeleton.
-- Minimized public witnesses may omit redundant or default literals only under
-- accepted minimization, coverage, replay, digest, build, and fingerprint
-- evidence.

def AyMWMPConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMWMPDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMWMPEquisat (left right : Prop) : Prop :=
  AyMWMPConj (left -> right) (right -> left)

def AyMWMPMinimizationMap
    (fullWitness minimizedWitness minimizationAgreement : Prop) : Prop :=
  AyMWMPConj fullWitness
    (AyMWMPConj minimizedWitness minimizationAgreement)

def AyMWMPCoverageLedger
    (coveredLiterals omittedDefaults coverageAgreement : Prop) : Prop :=
  AyMWMPConj coveredLiterals
    (AyMWMPConj omittedDefaults coverageAgreement)

def AyMWMPAssignmentDigest
    (fullDigest minimizedDigest digestAgreement : Prop) : Prop :=
  AyMWMPConj fullDigest (AyMWMPConj minimizedDigest digestAgreement)

def AyMWMPClauseEvaluationReplay
    (clauseReplay minimizedEvaluation evaluationAgreement : Prop) : Prop :=
  AyMWMPConj clauseReplay
    (AyMWMPConj minimizedEvaluation evaluationAgreement)

def AyMWMPCheckerReplay (checkerAccepted replayTrace : Prop) : Prop :=
  AyMWMPConj checkerAccepted replayTrace

def AyMWMPSolverBuild
    (solverBuild minimizationBuild buildAgreement : Prop) : Prop :=
  AyMWMPConj solverBuild (AyMWMPConj minimizationBuild buildAgreement)

def AyMWMPOriginalFingerprint
    (originalFingerprint minimizationFingerprint fingerprintAgreement : Prop) :
    Prop :=
  AyMWMPConj originalFingerprint
    (AyMWMPConj minimizationFingerprint fingerprintAgreement)

def AyMWMPAcceptedEvidence
    (minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop) : Prop :=
  AyMWMPConj minimizationOk
    (AyMWMPConj coverageOk
      (AyMWMPConj digestOk
        (AyMWMPConj clauseReplayOk
          (AyMWMPConj checkerOk
            (AyMWMPConj buildOk fingerprintOk)))))

def AyMWMPPublicSatWitness
    (acceptedEvidence publicWitness publicSatClaim : Prop) : Prop :=
  AyMWMPConj acceptedEvidence
    (AyMWMPConj publicWitness publicSatClaim)

def AyMWMPNoClaimDiagnostic (diagnostic publicSatClaim : Prop) : Prop :=
  AyMWMPConj diagnostic (publicSatClaim -> False)

def AyMWMPRecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMWMPConj reason recomputeRequest

theorem ay_mwmp_conj_intro {left right : Prop} :
    left -> right -> AyMWMPConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_mwmp_conj_left {left right : Prop} :
    AyMWMPConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_mwmp_conj_right {left right : Prop} :
    AyMWMPConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_mwmp_disj_left {left right : Prop} :
    left -> AyMWMPDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_mwmp_disj_right {left right : Prop} :
    right -> AyMWMPDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_mwmp_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMWMPEquisat left right :=
  fun hf hb => ay_mwmp_conj_intro hf hb

theorem ay_mwmp_equisat_forward {left right : Prop} :
    AyMWMPEquisat left right -> left -> right :=
  fun h => ay_mwmp_conj_left h

theorem ay_mwmp_equisat_backward {left right : Prop} :
    AyMWMPEquisat left right -> right -> left :=
  fun h => ay_mwmp_conj_right h

theorem ay_mwmp_minimization_map_intro
    {fullWitness minimizedWitness minimizationAgreement : Prop} :
    fullWitness ->
    minimizedWitness ->
    minimizationAgreement ->
    AyMWMPMinimizationMap
      fullWitness minimizedWitness minimizationAgreement :=
  fun hfull hminimized hagree =>
    ay_mwmp_conj_intro hfull
      (ay_mwmp_conj_intro hminimized hagree)

theorem ay_mwmp_minimization_map_full
    {fullWitness minimizedWitness minimizationAgreement : Prop} :
    AyMWMPMinimizationMap
      fullWitness minimizedWitness minimizationAgreement ->
    fullWitness :=
  fun h => ay_mwmp_conj_left h

theorem ay_mwmp_minimization_map_minimized
    {fullWitness minimizedWitness minimizationAgreement : Prop} :
    AyMWMPMinimizationMap
      fullWitness minimizedWitness minimizationAgreement ->
    minimizedWitness :=
  fun h => ay_mwmp_conj_left (ay_mwmp_conj_right h)

theorem ay_mwmp_minimization_map_agreement
    {fullWitness minimizedWitness minimizationAgreement : Prop} :
    AyMWMPMinimizationMap
      fullWitness minimizedWitness minimizationAgreement ->
    minimizationAgreement :=
  fun h => ay_mwmp_conj_right (ay_mwmp_conj_right h)

theorem ay_mwmp_coverage_ledger_intro
    {coveredLiterals omittedDefaults coverageAgreement : Prop} :
    coveredLiterals ->
    omittedDefaults ->
    coverageAgreement ->
    AyMWMPCoverageLedger
      coveredLiterals omittedDefaults coverageAgreement :=
  fun hcovered homitted hagree =>
    ay_mwmp_conj_intro hcovered
      (ay_mwmp_conj_intro homitted hagree)

theorem ay_mwmp_coverage_ledger_covered
    {coveredLiterals omittedDefaults coverageAgreement : Prop} :
    AyMWMPCoverageLedger
      coveredLiterals omittedDefaults coverageAgreement ->
    coveredLiterals :=
  fun h => ay_mwmp_conj_left h

theorem ay_mwmp_coverage_ledger_omitted
    {coveredLiterals omittedDefaults coverageAgreement : Prop} :
    AyMWMPCoverageLedger
      coveredLiterals omittedDefaults coverageAgreement ->
    omittedDefaults :=
  fun h => ay_mwmp_conj_left (ay_mwmp_conj_right h)

theorem ay_mwmp_coverage_ledger_agreement
    {coveredLiterals omittedDefaults coverageAgreement : Prop} :
    AyMWMPCoverageLedger
      coveredLiterals omittedDefaults coverageAgreement ->
    coverageAgreement :=
  fun h => ay_mwmp_conj_right (ay_mwmp_conj_right h)

theorem ay_mwmp_assignment_digest_intro
    {fullDigest minimizedDigest digestAgreement : Prop} :
    fullDigest ->
    minimizedDigest ->
    digestAgreement ->
    AyMWMPAssignmentDigest fullDigest minimizedDigest digestAgreement :=
  fun hfull hminimized hagree =>
    ay_mwmp_conj_intro hfull
      (ay_mwmp_conj_intro hminimized hagree)

theorem ay_mwmp_assignment_digest_full
    {fullDigest minimizedDigest digestAgreement : Prop} :
    AyMWMPAssignmentDigest fullDigest minimizedDigest digestAgreement ->
    fullDigest :=
  fun h => ay_mwmp_conj_left h

theorem ay_mwmp_assignment_digest_minimized
    {fullDigest minimizedDigest digestAgreement : Prop} :
    AyMWMPAssignmentDigest fullDigest minimizedDigest digestAgreement ->
    minimizedDigest :=
  fun h => ay_mwmp_conj_left (ay_mwmp_conj_right h)

theorem ay_mwmp_assignment_digest_agreement
    {fullDigest minimizedDigest digestAgreement : Prop} :
    AyMWMPAssignmentDigest fullDigest minimizedDigest digestAgreement ->
    digestAgreement :=
  fun h => ay_mwmp_conj_right (ay_mwmp_conj_right h)

theorem ay_mwmp_clause_evaluation_replay_intro
    {clauseReplay minimizedEvaluation evaluationAgreement : Prop} :
    clauseReplay ->
    minimizedEvaluation ->
    evaluationAgreement ->
    AyMWMPClauseEvaluationReplay
      clauseReplay minimizedEvaluation evaluationAgreement :=
  fun hreplay hevaluation hagree =>
    ay_mwmp_conj_intro hreplay
      (ay_mwmp_conj_intro hevaluation hagree)

theorem ay_mwmp_clause_evaluation_replay_trace
    {clauseReplay minimizedEvaluation evaluationAgreement : Prop} :
    AyMWMPClauseEvaluationReplay
      clauseReplay minimizedEvaluation evaluationAgreement ->
    clauseReplay :=
  fun h => ay_mwmp_conj_left h

theorem ay_mwmp_clause_evaluation_replay_evaluation
    {clauseReplay minimizedEvaluation evaluationAgreement : Prop} :
    AyMWMPClauseEvaluationReplay
      clauseReplay minimizedEvaluation evaluationAgreement ->
    minimizedEvaluation :=
  fun h => ay_mwmp_conj_left (ay_mwmp_conj_right h)

theorem ay_mwmp_clause_evaluation_replay_agreement
    {clauseReplay minimizedEvaluation evaluationAgreement : Prop} :
    AyMWMPClauseEvaluationReplay
      clauseReplay minimizedEvaluation evaluationAgreement ->
    evaluationAgreement :=
  fun h => ay_mwmp_conj_right (ay_mwmp_conj_right h)

theorem ay_mwmp_checker_replay_intro
    {checkerAccepted replayTrace : Prop} :
    checkerAccepted ->
    replayTrace ->
    AyMWMPCheckerReplay checkerAccepted replayTrace :=
  fun haccepted htrace => ay_mwmp_conj_intro haccepted htrace

theorem ay_mwmp_checker_replay_accepted
    {checkerAccepted replayTrace : Prop} :
    AyMWMPCheckerReplay checkerAccepted replayTrace -> checkerAccepted :=
  fun h => ay_mwmp_conj_left h

theorem ay_mwmp_checker_replay_trace
    {checkerAccepted replayTrace : Prop} :
    AyMWMPCheckerReplay checkerAccepted replayTrace -> replayTrace :=
  fun h => ay_mwmp_conj_right h

theorem ay_mwmp_solver_build_intro
    {solverBuild minimizationBuild buildAgreement : Prop} :
    solverBuild ->
    minimizationBuild ->
    buildAgreement ->
    AyMWMPSolverBuild solverBuild minimizationBuild buildAgreement :=
  fun hsolver hminimization hagree =>
    ay_mwmp_conj_intro hsolver
      (ay_mwmp_conj_intro hminimization hagree)

theorem ay_mwmp_solver_build_solver
    {solverBuild minimizationBuild buildAgreement : Prop} :
    AyMWMPSolverBuild solverBuild minimizationBuild buildAgreement ->
    solverBuild :=
  fun h => ay_mwmp_conj_left h

theorem ay_mwmp_solver_build_minimization
    {solverBuild minimizationBuild buildAgreement : Prop} :
    AyMWMPSolverBuild solverBuild minimizationBuild buildAgreement ->
    minimizationBuild :=
  fun h => ay_mwmp_conj_left (ay_mwmp_conj_right h)

theorem ay_mwmp_solver_build_agreement
    {solverBuild minimizationBuild buildAgreement : Prop} :
    AyMWMPSolverBuild solverBuild minimizationBuild buildAgreement ->
    buildAgreement :=
  fun h => ay_mwmp_conj_right (ay_mwmp_conj_right h)

theorem ay_mwmp_original_fingerprint_intro
    {originalFingerprint minimizationFingerprint fingerprintAgreement : Prop} :
    originalFingerprint ->
    minimizationFingerprint ->
    fingerprintAgreement ->
    AyMWMPOriginalFingerprint
      originalFingerprint minimizationFingerprint fingerprintAgreement :=
  fun horiginal hminimization hagree =>
    ay_mwmp_conj_intro horiginal
      (ay_mwmp_conj_intro hminimization hagree)

theorem ay_mwmp_original_fingerprint_original
    {originalFingerprint minimizationFingerprint fingerprintAgreement : Prop} :
    AyMWMPOriginalFingerprint
      originalFingerprint minimizationFingerprint fingerprintAgreement ->
    originalFingerprint :=
  fun h => ay_mwmp_conj_left h

theorem ay_mwmp_original_fingerprint_minimization
    {originalFingerprint minimizationFingerprint fingerprintAgreement : Prop} :
    AyMWMPOriginalFingerprint
      originalFingerprint minimizationFingerprint fingerprintAgreement ->
    minimizationFingerprint :=
  fun h => ay_mwmp_conj_left (ay_mwmp_conj_right h)

theorem ay_mwmp_original_fingerprint_agreement
    {originalFingerprint minimizationFingerprint fingerprintAgreement : Prop} :
    AyMWMPOriginalFingerprint
      originalFingerprint minimizationFingerprint fingerprintAgreement ->
    fingerprintAgreement :=
  fun h => ay_mwmp_conj_right (ay_mwmp_conj_right h)

theorem ay_mwmp_accepted_evidence_intro
    {minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    minimizationOk ->
    coverageOk ->
    digestOk ->
    clauseReplayOk ->
    checkerOk ->
    buildOk ->
    fingerprintOk ->
    AyMWMPAcceptedEvidence
      minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk :=
  fun hminimization hcoverage hdigest hclause hchecker hbuild
      hfingerprint =>
    ay_mwmp_conj_intro hminimization
      (ay_mwmp_conj_intro hcoverage
        (ay_mwmp_conj_intro hdigest
          (ay_mwmp_conj_intro hclause
            (ay_mwmp_conj_intro hchecker
              (ay_mwmp_conj_intro hbuild hfingerprint)))))

theorem ay_mwmp_accepted_evidence_minimization
    {minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMWMPAcceptedEvidence
      minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    minimizationOk :=
  fun h => ay_mwmp_conj_left h

theorem ay_mwmp_accepted_evidence_coverage
    {minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMWMPAcceptedEvidence
      minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    coverageOk :=
  fun h => ay_mwmp_conj_left (ay_mwmp_conj_right h)

theorem ay_mwmp_accepted_evidence_digest
    {minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMWMPAcceptedEvidence
      minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    digestOk :=
  fun h => ay_mwmp_conj_left
    (ay_mwmp_conj_right (ay_mwmp_conj_right h))

theorem ay_mwmp_accepted_evidence_clause_replay
    {minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMWMPAcceptedEvidence
      minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    clauseReplayOk :=
  fun h => ay_mwmp_conj_left
    (ay_mwmp_conj_right
      (ay_mwmp_conj_right (ay_mwmp_conj_right h)))

theorem ay_mwmp_accepted_evidence_checker
    {minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMWMPAcceptedEvidence
      minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    checkerOk :=
  fun h => ay_mwmp_conj_left
    (ay_mwmp_conj_right
      (ay_mwmp_conj_right
        (ay_mwmp_conj_right (ay_mwmp_conj_right h))))

theorem ay_mwmp_accepted_evidence_build
    {minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMWMPAcceptedEvidence
      minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    buildOk :=
  fun h => ay_mwmp_conj_left
    (ay_mwmp_conj_right
      (ay_mwmp_conj_right
        (ay_mwmp_conj_right
          (ay_mwmp_conj_right (ay_mwmp_conj_right h)))))

theorem ay_mwmp_accepted_evidence_fingerprint
    {minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMWMPAcceptedEvidence
      minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    fingerprintOk :=
  fun h => ay_mwmp_conj_right
    (ay_mwmp_conj_right
      (ay_mwmp_conj_right
        (ay_mwmp_conj_right
          (ay_mwmp_conj_right (ay_mwmp_conj_right h)))))

theorem ay_mwmp_public_sat_witness_intro
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    acceptedEvidence ->
    publicWitness ->
    publicSatClaim ->
    AyMWMPPublicSatWitness acceptedEvidence publicWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_mwmp_conj_intro hevidence
      (ay_mwmp_conj_intro hwitness hclaim)

theorem ay_mwmp_public_sat_witness_evidence
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMWMPPublicSatWitness acceptedEvidence publicWitness publicSatClaim ->
    acceptedEvidence :=
  fun h => ay_mwmp_conj_left h

theorem ay_mwmp_public_sat_witness_witness
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMWMPPublicSatWitness acceptedEvidence publicWitness publicSatClaim ->
    publicWitness :=
  fun h => ay_mwmp_conj_left (ay_mwmp_conj_right h)

theorem ay_mwmp_public_sat_witness_claim
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMWMPPublicSatWitness acceptedEvidence publicWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_mwmp_conj_right (ay_mwmp_conj_right h)

theorem ay_mwmp_accepted_minimization_emits_sound_public_sat
    {minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMWMPAcceptedEvidence
      minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    publicWitness ->
    publicSatClaim ->
    AyMWMPPublicSatWitness
      (AyMWMPAcceptedEvidence
        minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_mwmp_public_sat_witness_intro hevidence hwitness hclaim

theorem ay_mwmp_public_sat_requires_accepted_evidence
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMWMPPublicSatWitness acceptedEvidence publicWitness publicSatClaim ->
    acceptedEvidence :=
  fun h => ay_mwmp_public_sat_witness_evidence h

theorem ay_mwmp_minimization_hints_preserve_truth
    {fullTruth minimizedTruth : Prop} :
    AyMWMPEquisat fullTruth minimizedTruth ->
    fullTruth ->
    minimizedTruth :=
  fun heq hfull => ay_mwmp_equisat_forward heq hfull

theorem ay_mwmp_clause_replay_transports_truth
    {clauseReplay minimizedEvaluation formulaTruth : Prop} :
    AyMWMPClauseEvaluationReplay
      clauseReplay minimizedEvaluation formulaTruth ->
    formulaTruth :=
  fun h => ay_mwmp_clause_evaluation_replay_agreement h

theorem ay_mwmp_publication_requires_minimization
    {minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMWMPPublicSatWitness
      (AyMWMPAcceptedEvidence
        minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    minimizationOk :=
  fun h =>
    ay_mwmp_accepted_evidence_minimization
      (ay_mwmp_public_sat_witness_evidence h)

theorem ay_mwmp_publication_requires_coverage
    {minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMWMPPublicSatWitness
      (AyMWMPAcceptedEvidence
        minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    coverageOk :=
  fun h =>
    ay_mwmp_accepted_evidence_coverage
      (ay_mwmp_public_sat_witness_evidence h)

theorem ay_mwmp_publication_requires_digest
    {minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMWMPPublicSatWitness
      (AyMWMPAcceptedEvidence
        minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    digestOk :=
  fun h =>
    ay_mwmp_accepted_evidence_digest
      (ay_mwmp_public_sat_witness_evidence h)

theorem ay_mwmp_publication_requires_clause_replay
    {minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMWMPPublicSatWitness
      (AyMWMPAcceptedEvidence
        minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    clauseReplayOk :=
  fun h =>
    ay_mwmp_accepted_evidence_clause_replay
      (ay_mwmp_public_sat_witness_evidence h)

theorem ay_mwmp_publication_requires_checker
    {minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMWMPPublicSatWitness
      (AyMWMPAcceptedEvidence
        minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    checkerOk :=
  fun h =>
    ay_mwmp_accepted_evidence_checker
      (ay_mwmp_public_sat_witness_evidence h)

theorem ay_mwmp_publication_requires_build
    {minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMWMPPublicSatWitness
      (AyMWMPAcceptedEvidence
        minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    buildOk :=
  fun h =>
    ay_mwmp_accepted_evidence_build
      (ay_mwmp_public_sat_witness_evidence h)

theorem ay_mwmp_publication_requires_fingerprint
    {minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMWMPPublicSatWitness
      (AyMWMPAcceptedEvidence
        minimizationOk coverageOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    fingerprintOk :=
  fun h =>
    ay_mwmp_accepted_evidence_fingerprint
      (ay_mwmp_public_sat_witness_evidence h)

theorem ay_mwmp_no_claim_diagnostic_intro
    {diagnostic publicSatClaim : Prop} :
    diagnostic ->
    (publicSatClaim -> False) ->
    AyMWMPNoClaimDiagnostic diagnostic publicSatClaim :=
  fun hdiagnostic hblocks =>
    ay_mwmp_conj_intro hdiagnostic hblocks

theorem ay_mwmp_no_claim_diagnostic_reason
    {diagnostic publicSatClaim : Prop} :
    AyMWMPNoClaimDiagnostic diagnostic publicSatClaim -> diagnostic :=
  fun h => ay_mwmp_conj_left h

theorem ay_mwmp_no_claim_diagnostic_blocks
    {diagnostic publicSatClaim : Prop} :
    AyMWMPNoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h => ay_mwmp_conj_right h

theorem ay_mwmp_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMWMPRecomputeObligation reason recomputeRequest :=
  fun hreason hrecompute => ay_mwmp_conj_intro hreason hrecompute

theorem ay_mwmp_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMWMPRecomputeObligation reason recomputeRequest -> reason :=
  fun h => ay_mwmp_conj_left h

theorem ay_mwmp_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMWMPRecomputeObligation reason recomputeRequest -> recomputeRequest :=
  fun h => ay_mwmp_conj_right h

theorem ay_mwmp_omitted_literal_coverage_drift_recompute
    {coverageDrift recomputeRequest : Prop} :
    coverageDrift ->
    recomputeRequest ->
    AyMWMPRecomputeObligation coverageDrift recomputeRequest :=
  fun hdrift hrecompute =>
    ay_mwmp_recompute_obligation_intro hdrift hrecompute

theorem ay_mwmp_omitted_literal_coverage_drift_no_claim
    {coverageDrift publicSatClaim : Prop} :
    coverageDrift ->
    (publicSatClaim -> False) ->
    AyMWMPNoClaimDiagnostic coverageDrift publicSatClaim :=
  fun hdrift hblocks => ay_mwmp_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mwmp_minimization_map_drift_no_claim
    {mapDrift publicSatClaim : Prop} :
    mapDrift ->
    (publicSatClaim -> False) ->
    AyMWMPNoClaimDiagnostic mapDrift publicSatClaim :=
  fun hdrift hblocks => ay_mwmp_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mwmp_checker_rejection_no_claim
    {checkerRejection publicSatClaim : Prop} :
    checkerRejection ->
    (publicSatClaim -> False) ->
    AyMWMPNoClaimDiagnostic checkerRejection publicSatClaim :=
  fun hreject hblocks =>
    ay_mwmp_no_claim_diagnostic_intro hreject hblocks

theorem ay_mwmp_digest_mismatch_no_claim
    {digestMismatch publicSatClaim : Prop} :
    digestMismatch ->
    (publicSatClaim -> False) ->
    AyMWMPNoClaimDiagnostic digestMismatch publicSatClaim :=
  fun hmismatch hblocks =>
    ay_mwmp_no_claim_diagnostic_intro hmismatch hblocks

theorem ay_mwmp_build_drift_no_claim
    {buildDrift publicSatClaim : Prop} :
    buildDrift ->
    (publicSatClaim -> False) ->
    AyMWMPNoClaimDiagnostic buildDrift publicSatClaim :=
  fun hdrift hblocks => ay_mwmp_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mwmp_fingerprint_mismatch_no_claim
    {fingerprintMismatch publicSatClaim : Prop} :
    fingerprintMismatch ->
    (publicSatClaim -> False) ->
    AyMWMPNoClaimDiagnostic fingerprintMismatch publicSatClaim :=
  fun hmismatch hblocks =>
    ay_mwmp_no_claim_diagnostic_intro hmismatch hblocks

theorem ay_mwmp_diagnostic_blocks_public_claim
    {diagnostic publicSatClaim : Prop} :
    AyMWMPNoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_mwmp_no_claim_diagnostic_blocks h hclaim

theorem ay_mwmp_bad_minimization_cannot_emit_sat
    {badMinimization publicSatClaim : Prop} :
    AyMWMPNoClaimDiagnostic badMinimization publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_mwmp_diagnostic_blocks_public_claim h hclaim
