-- SAT-COMP/ay partial assignment default-extension soundness skeleton.
-- Partial solver assignments may be completed with defaults only when coverage,
-- clause replay, digest, checker replay, solver build, and fingerprint evidence
-- are accepted.

def AyMPDEConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMPDEDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMPDEEquisat (left right : Prop) : Prop :=
  AyMPDEConj (left -> right) (right -> left)

def AyMPDECanonicalCoverage
    (originalVariables assignedVariables defaultedVariables coverageAgreement :
      Prop) : Prop :=
  AyMPDEConj originalVariables
    (AyMPDEConj assignedVariables
      (AyMPDEConj defaultedVariables coverageAgreement))

def AyMPDEDefaultExtension
    (partialAssignment defaultValues extendedAssignment defaultsConsistent :
      Prop) : Prop :=
  AyMPDEConj partialAssignment
    (AyMPDEConj defaultValues
      (AyMPDEConj extendedAssignment defaultsConsistent))

def AyMPDEClauseEvaluationReplay
    (clauseReplay extendedEvaluation evaluationAgreement : Prop) : Prop :=
  AyMPDEConj clauseReplay
    (AyMPDEConj extendedEvaluation evaluationAgreement)

def AyMPDEAssignmentDigest
    (partialDigest extendedDigest digestAgreement : Prop) : Prop :=
  AyMPDEConj partialDigest (AyMPDEConj extendedDigest digestAgreement)

def AyMPDECheckerReplay (checkerAccepted replayTrace : Prop) : Prop :=
  AyMPDEConj checkerAccepted replayTrace

def AyMPDESolverBuild
    (solverBuild witnessBuild buildAgreement : Prop) : Prop :=
  AyMPDEConj solverBuild (AyMPDEConj witnessBuild buildAgreement)

def AyMPDEOriginalFingerprint
    (originalFingerprint extensionFingerprint fingerprintAgreement : Prop) :
    Prop :=
  AyMPDEConj originalFingerprint
    (AyMPDEConj extensionFingerprint fingerprintAgreement)

def AyMPDEAcceptedEvidence
    (coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
      fingerprintOk : Prop) : Prop :=
  AyMPDEConj coverageOk
    (AyMPDEConj extensionOk
      (AyMPDEConj clauseReplayOk
        (AyMPDEConj digestOk
          (AyMPDEConj checkerOk
            (AyMPDEConj buildOk fingerprintOk)))))

def AyMPDEPublicSatWitness
    (acceptedEvidence publicWitness publicSatClaim : Prop) : Prop :=
  AyMPDEConj acceptedEvidence
    (AyMPDEConj publicWitness publicSatClaim)

def AyMPDENoClaimDiagnostic (diagnostic publicSatClaim : Prop) : Prop :=
  AyMPDEConj diagnostic (publicSatClaim -> False)

def AyMPDERecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMPDEConj reason recomputeRequest

theorem ay_mpde_conj_intro {left right : Prop} :
    left -> right -> AyMPDEConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_mpde_conj_left {left right : Prop} :
    AyMPDEConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_mpde_conj_right {left right : Prop} :
    AyMPDEConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_mpde_disj_left {left right : Prop} :
    left -> AyMPDEDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_mpde_disj_right {left right : Prop} :
    right -> AyMPDEDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_mpde_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMPDEEquisat left right :=
  fun hf hb => ay_mpde_conj_intro hf hb

theorem ay_mpde_equisat_forward {left right : Prop} :
    AyMPDEEquisat left right -> left -> right :=
  fun h => ay_mpde_conj_left h

theorem ay_mpde_equisat_backward {left right : Prop} :
    AyMPDEEquisat left right -> right -> left :=
  fun h => ay_mpde_conj_right h

theorem ay_mpde_canonical_coverage_intro
    {originalVariables assignedVariables defaultedVariables coverageAgreement :
      Prop} :
    originalVariables ->
    assignedVariables ->
    defaultedVariables ->
    coverageAgreement ->
    AyMPDECanonicalCoverage
      originalVariables assignedVariables defaultedVariables
      coverageAgreement :=
  fun horiginal hassigned hdefaulted hagree =>
    ay_mpde_conj_intro horiginal
      (ay_mpde_conj_intro hassigned
        (ay_mpde_conj_intro hdefaulted hagree))

theorem ay_mpde_canonical_coverage_original
    {originalVariables assignedVariables defaultedVariables coverageAgreement :
      Prop} :
    AyMPDECanonicalCoverage
      originalVariables assignedVariables defaultedVariables
      coverageAgreement ->
    originalVariables :=
  fun h => ay_mpde_conj_left h

theorem ay_mpde_canonical_coverage_assigned
    {originalVariables assignedVariables defaultedVariables coverageAgreement :
      Prop} :
    AyMPDECanonicalCoverage
      originalVariables assignedVariables defaultedVariables
      coverageAgreement ->
    assignedVariables :=
  fun h => ay_mpde_conj_left (ay_mpde_conj_right h)

theorem ay_mpde_canonical_coverage_defaulted
    {originalVariables assignedVariables defaultedVariables coverageAgreement :
      Prop} :
    AyMPDECanonicalCoverage
      originalVariables assignedVariables defaultedVariables
      coverageAgreement ->
    defaultedVariables :=
  fun h => ay_mpde_conj_left
    (ay_mpde_conj_right (ay_mpde_conj_right h))

theorem ay_mpde_canonical_coverage_agreement
    {originalVariables assignedVariables defaultedVariables coverageAgreement :
      Prop} :
    AyMPDECanonicalCoverage
      originalVariables assignedVariables defaultedVariables
      coverageAgreement ->
    coverageAgreement :=
  fun h => ay_mpde_conj_right
    (ay_mpde_conj_right (ay_mpde_conj_right h))

theorem ay_mpde_default_extension_intro
    {partialAssignment defaultValues extendedAssignment defaultsConsistent :
      Prop} :
    partialAssignment ->
    defaultValues ->
    extendedAssignment ->
    defaultsConsistent ->
    AyMPDEDefaultExtension
      partialAssignment defaultValues extendedAssignment defaultsConsistent :=
  fun hpartial hdefaults hextended hconsistent =>
    ay_mpde_conj_intro hpartial
      (ay_mpde_conj_intro hdefaults
        (ay_mpde_conj_intro hextended hconsistent))

theorem ay_mpde_default_extension_partial
    {partialAssignment defaultValues extendedAssignment defaultsConsistent :
      Prop} :
    AyMPDEDefaultExtension
      partialAssignment defaultValues extendedAssignment defaultsConsistent ->
    partialAssignment :=
  fun h => ay_mpde_conj_left h

theorem ay_mpde_default_extension_defaults
    {partialAssignment defaultValues extendedAssignment defaultsConsistent :
      Prop} :
    AyMPDEDefaultExtension
      partialAssignment defaultValues extendedAssignment defaultsConsistent ->
    defaultValues :=
  fun h => ay_mpde_conj_left (ay_mpde_conj_right h)

theorem ay_mpde_default_extension_extended
    {partialAssignment defaultValues extendedAssignment defaultsConsistent :
      Prop} :
    AyMPDEDefaultExtension
      partialAssignment defaultValues extendedAssignment defaultsConsistent ->
    extendedAssignment :=
  fun h => ay_mpde_conj_left
    (ay_mpde_conj_right (ay_mpde_conj_right h))

theorem ay_mpde_default_extension_consistent
    {partialAssignment defaultValues extendedAssignment defaultsConsistent :
      Prop} :
    AyMPDEDefaultExtension
      partialAssignment defaultValues extendedAssignment defaultsConsistent ->
    defaultsConsistent :=
  fun h => ay_mpde_conj_right
    (ay_mpde_conj_right (ay_mpde_conj_right h))

theorem ay_mpde_clause_evaluation_replay_intro
    {clauseReplay extendedEvaluation evaluationAgreement : Prop} :
    clauseReplay ->
    extendedEvaluation ->
    evaluationAgreement ->
    AyMPDEClauseEvaluationReplay
      clauseReplay extendedEvaluation evaluationAgreement :=
  fun hreplay heval hagree =>
    ay_mpde_conj_intro hreplay (ay_mpde_conj_intro heval hagree)

theorem ay_mpde_clause_evaluation_replay_trace
    {clauseReplay extendedEvaluation evaluationAgreement : Prop} :
    AyMPDEClauseEvaluationReplay
      clauseReplay extendedEvaluation evaluationAgreement ->
    clauseReplay :=
  fun h => ay_mpde_conj_left h

theorem ay_mpde_clause_evaluation_replay_evaluation
    {clauseReplay extendedEvaluation evaluationAgreement : Prop} :
    AyMPDEClauseEvaluationReplay
      clauseReplay extendedEvaluation evaluationAgreement ->
    extendedEvaluation :=
  fun h => ay_mpde_conj_left (ay_mpde_conj_right h)

theorem ay_mpde_clause_evaluation_replay_agreement
    {clauseReplay extendedEvaluation evaluationAgreement : Prop} :
    AyMPDEClauseEvaluationReplay
      clauseReplay extendedEvaluation evaluationAgreement ->
    evaluationAgreement :=
  fun h => ay_mpde_conj_right (ay_mpde_conj_right h)

theorem ay_mpde_assignment_digest_intro
    {partialDigest extendedDigest digestAgreement : Prop} :
    partialDigest ->
    extendedDigest ->
    digestAgreement ->
    AyMPDEAssignmentDigest partialDigest extendedDigest digestAgreement :=
  fun hpartial hextended hagree =>
    ay_mpde_conj_intro hpartial (ay_mpde_conj_intro hextended hagree)

theorem ay_mpde_assignment_digest_partial
    {partialDigest extendedDigest digestAgreement : Prop} :
    AyMPDEAssignmentDigest partialDigest extendedDigest digestAgreement ->
    partialDigest :=
  fun h => ay_mpde_conj_left h

theorem ay_mpde_assignment_digest_extended
    {partialDigest extendedDigest digestAgreement : Prop} :
    AyMPDEAssignmentDigest partialDigest extendedDigest digestAgreement ->
    extendedDigest :=
  fun h => ay_mpde_conj_left (ay_mpde_conj_right h)

theorem ay_mpde_assignment_digest_agreement
    {partialDigest extendedDigest digestAgreement : Prop} :
    AyMPDEAssignmentDigest partialDigest extendedDigest digestAgreement ->
    digestAgreement :=
  fun h => ay_mpde_conj_right (ay_mpde_conj_right h)

theorem ay_mpde_checker_replay_intro
    {checkerAccepted replayTrace : Prop} :
    checkerAccepted ->
    replayTrace ->
    AyMPDECheckerReplay checkerAccepted replayTrace :=
  fun haccepted htrace => ay_mpde_conj_intro haccepted htrace

theorem ay_mpde_checker_replay_accepted
    {checkerAccepted replayTrace : Prop} :
    AyMPDECheckerReplay checkerAccepted replayTrace -> checkerAccepted :=
  fun h => ay_mpde_conj_left h

theorem ay_mpde_checker_replay_trace
    {checkerAccepted replayTrace : Prop} :
    AyMPDECheckerReplay checkerAccepted replayTrace -> replayTrace :=
  fun h => ay_mpde_conj_right h

theorem ay_mpde_solver_build_intro
    {solverBuild witnessBuild buildAgreement : Prop} :
    solverBuild ->
    witnessBuild ->
    buildAgreement ->
    AyMPDESolverBuild solverBuild witnessBuild buildAgreement :=
  fun hsolver hwitness hagree =>
    ay_mpde_conj_intro hsolver
      (ay_mpde_conj_intro hwitness hagree)

theorem ay_mpde_solver_build_solver
    {solverBuild witnessBuild buildAgreement : Prop} :
    AyMPDESolverBuild solverBuild witnessBuild buildAgreement -> solverBuild :=
  fun h => ay_mpde_conj_left h

theorem ay_mpde_solver_build_witness
    {solverBuild witnessBuild buildAgreement : Prop} :
    AyMPDESolverBuild solverBuild witnessBuild buildAgreement ->
    witnessBuild :=
  fun h => ay_mpde_conj_left (ay_mpde_conj_right h)

theorem ay_mpde_solver_build_agreement
    {solverBuild witnessBuild buildAgreement : Prop} :
    AyMPDESolverBuild solverBuild witnessBuild buildAgreement ->
    buildAgreement :=
  fun h => ay_mpde_conj_right (ay_mpde_conj_right h)

theorem ay_mpde_original_fingerprint_intro
    {originalFingerprint extensionFingerprint fingerprintAgreement : Prop} :
    originalFingerprint ->
    extensionFingerprint ->
    fingerprintAgreement ->
    AyMPDEOriginalFingerprint
      originalFingerprint extensionFingerprint fingerprintAgreement :=
  fun horiginal hextension hagree =>
    ay_mpde_conj_intro horiginal
      (ay_mpde_conj_intro hextension hagree)

theorem ay_mpde_original_fingerprint_original
    {originalFingerprint extensionFingerprint fingerprintAgreement : Prop} :
    AyMPDEOriginalFingerprint
      originalFingerprint extensionFingerprint fingerprintAgreement ->
    originalFingerprint :=
  fun h => ay_mpde_conj_left h

theorem ay_mpde_original_fingerprint_extension
    {originalFingerprint extensionFingerprint fingerprintAgreement : Prop} :
    AyMPDEOriginalFingerprint
      originalFingerprint extensionFingerprint fingerprintAgreement ->
    extensionFingerprint :=
  fun h => ay_mpde_conj_left (ay_mpde_conj_right h)

theorem ay_mpde_original_fingerprint_agreement
    {originalFingerprint extensionFingerprint fingerprintAgreement : Prop} :
    AyMPDEOriginalFingerprint
      originalFingerprint extensionFingerprint fingerprintAgreement ->
    fingerprintAgreement :=
  fun h => ay_mpde_conj_right (ay_mpde_conj_right h)

theorem ay_mpde_accepted_evidence_intro
    {coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
      fingerprintOk : Prop} :
    coverageOk ->
    extensionOk ->
    clauseReplayOk ->
    digestOk ->
    checkerOk ->
    buildOk ->
    fingerprintOk ->
    AyMPDEAcceptedEvidence
      coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
      fingerprintOk :=
  fun hcoverage hextension hclause hdigest hchecker hbuild hfingerprint =>
    ay_mpde_conj_intro hcoverage
      (ay_mpde_conj_intro hextension
        (ay_mpde_conj_intro hclause
          (ay_mpde_conj_intro hdigest
            (ay_mpde_conj_intro hchecker
              (ay_mpde_conj_intro hbuild hfingerprint)))))

theorem ay_mpde_accepted_evidence_coverage
    {coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMPDEAcceptedEvidence
      coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
      fingerprintOk ->
    coverageOk :=
  fun h => ay_mpde_conj_left h

theorem ay_mpde_accepted_evidence_extension
    {coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMPDEAcceptedEvidence
      coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
      fingerprintOk ->
    extensionOk :=
  fun h => ay_mpde_conj_left (ay_mpde_conj_right h)

theorem ay_mpde_accepted_evidence_clause_replay
    {coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMPDEAcceptedEvidence
      coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
      fingerprintOk ->
    clauseReplayOk :=
  fun h => ay_mpde_conj_left
    (ay_mpde_conj_right (ay_mpde_conj_right h))

theorem ay_mpde_accepted_evidence_digest
    {coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMPDEAcceptedEvidence
      coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
      fingerprintOk ->
    digestOk :=
  fun h => ay_mpde_conj_left
    (ay_mpde_conj_right
      (ay_mpde_conj_right (ay_mpde_conj_right h)))

theorem ay_mpde_accepted_evidence_checker
    {coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMPDEAcceptedEvidence
      coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
      fingerprintOk ->
    checkerOk :=
  fun h => ay_mpde_conj_left
    (ay_mpde_conj_right
      (ay_mpde_conj_right
        (ay_mpde_conj_right (ay_mpde_conj_right h))))

theorem ay_mpde_accepted_evidence_build
    {coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMPDEAcceptedEvidence
      coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
      fingerprintOk ->
    buildOk :=
  fun h => ay_mpde_conj_left
    (ay_mpde_conj_right
      (ay_mpde_conj_right
        (ay_mpde_conj_right
          (ay_mpde_conj_right (ay_mpde_conj_right h)))))

theorem ay_mpde_accepted_evidence_fingerprint
    {coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMPDEAcceptedEvidence
      coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
      fingerprintOk ->
    fingerprintOk :=
  fun h => ay_mpde_conj_right
    (ay_mpde_conj_right
      (ay_mpde_conj_right
        (ay_mpde_conj_right
          (ay_mpde_conj_right (ay_mpde_conj_right h)))))

theorem ay_mpde_public_sat_witness_intro
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    acceptedEvidence ->
    publicWitness ->
    publicSatClaim ->
    AyMPDEPublicSatWitness
      acceptedEvidence publicWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_mpde_conj_intro hevidence
      (ay_mpde_conj_intro hwitness hclaim)

theorem ay_mpde_public_sat_witness_evidence
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMPDEPublicSatWitness
      acceptedEvidence publicWitness publicSatClaim ->
    acceptedEvidence :=
  fun h => ay_mpde_conj_left h

theorem ay_mpde_public_sat_witness_witness
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMPDEPublicSatWitness
      acceptedEvidence publicWitness publicSatClaim ->
    publicWitness :=
  fun h => ay_mpde_conj_left (ay_mpde_conj_right h)

theorem ay_mpde_public_sat_witness_claim
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMPDEPublicSatWitness
      acceptedEvidence publicWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_mpde_conj_right (ay_mpde_conj_right h)

theorem ay_mpde_accepted_default_extension_emits_sound_public_sat
    {coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMPDEAcceptedEvidence
      coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
      fingerprintOk ->
    publicWitness ->
    publicSatClaim ->
    AyMPDEPublicSatWitness
      (AyMPDEAcceptedEvidence
        coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_mpde_public_sat_witness_intro hevidence hwitness hclaim

theorem ay_mpde_public_sat_requires_accepted_evidence
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMPDEPublicSatWitness
      acceptedEvidence publicWitness publicSatClaim ->
    acceptedEvidence :=
  fun h => ay_mpde_public_sat_witness_evidence h

theorem ay_mpde_default_extension_hints_preserve_truth
    {partialTruth extendedTruth : Prop} :
    AyMPDEEquisat partialTruth extendedTruth ->
    partialTruth ->
    extendedTruth :=
  fun heq hpartial => ay_mpde_equisat_forward heq hpartial

theorem ay_mpde_clause_replay_transports_truth
    {clauseReplay extendedEvaluation formulaTruth : Prop} :
    AyMPDEClauseEvaluationReplay
      clauseReplay extendedEvaluation formulaTruth ->
    formulaTruth :=
  fun h => ay_mpde_clause_evaluation_replay_agreement h

theorem ay_mpde_publication_requires_coverage
    {coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMPDEPublicSatWitness
      (AyMPDEAcceptedEvidence
        coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    coverageOk :=
  fun h =>
    ay_mpde_accepted_evidence_coverage
      (ay_mpde_public_sat_witness_evidence h)

theorem ay_mpde_publication_requires_extension
    {coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMPDEPublicSatWitness
      (AyMPDEAcceptedEvidence
        coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    extensionOk :=
  fun h =>
    ay_mpde_accepted_evidence_extension
      (ay_mpde_public_sat_witness_evidence h)

theorem ay_mpde_publication_requires_clause_replay
    {coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMPDEPublicSatWitness
      (AyMPDEAcceptedEvidence
        coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    clauseReplayOk :=
  fun h =>
    ay_mpde_accepted_evidence_clause_replay
      (ay_mpde_public_sat_witness_evidence h)

theorem ay_mpde_publication_requires_digest
    {coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMPDEPublicSatWitness
      (AyMPDEAcceptedEvidence
        coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    digestOk :=
  fun h =>
    ay_mpde_accepted_evidence_digest
      (ay_mpde_public_sat_witness_evidence h)

theorem ay_mpde_publication_requires_checker
    {coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMPDEPublicSatWitness
      (AyMPDEAcceptedEvidence
        coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    checkerOk :=
  fun h =>
    ay_mpde_accepted_evidence_checker
      (ay_mpde_public_sat_witness_evidence h)

theorem ay_mpde_publication_requires_build
    {coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMPDEPublicSatWitness
      (AyMPDEAcceptedEvidence
        coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    buildOk :=
  fun h =>
    ay_mpde_accepted_evidence_build
      (ay_mpde_public_sat_witness_evidence h)

theorem ay_mpde_publication_requires_fingerprint
    {coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMPDEPublicSatWitness
      (AyMPDEAcceptedEvidence
        coverageOk extensionOk clauseReplayOk digestOk checkerOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    fingerprintOk :=
  fun h =>
    ay_mpde_accepted_evidence_fingerprint
      (ay_mpde_public_sat_witness_evidence h)

theorem ay_mpde_no_claim_diagnostic_intro
    {diagnostic publicSatClaim : Prop} :
    diagnostic ->
    (publicSatClaim -> False) ->
    AyMPDENoClaimDiagnostic diagnostic publicSatClaim :=
  fun hdiagnostic hblocks =>
    ay_mpde_conj_intro hdiagnostic hblocks

theorem ay_mpde_no_claim_diagnostic_reason
    {diagnostic publicSatClaim : Prop} :
    AyMPDENoClaimDiagnostic diagnostic publicSatClaim -> diagnostic :=
  fun h => ay_mpde_conj_left h

theorem ay_mpde_no_claim_diagnostic_blocks
    {diagnostic publicSatClaim : Prop} :
    AyMPDENoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h => ay_mpde_conj_right h

theorem ay_mpde_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMPDERecomputeObligation reason recomputeRequest :=
  fun hreason hrecompute => ay_mpde_conj_intro hreason hrecompute

theorem ay_mpde_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMPDERecomputeObligation reason recomputeRequest -> reason :=
  fun h => ay_mpde_conj_left h

theorem ay_mpde_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMPDERecomputeObligation reason recomputeRequest -> recomputeRequest :=
  fun h => ay_mpde_conj_right h

theorem ay_mpde_missing_coverage_recompute
    {missingCoverage recomputeRequest : Prop} :
    missingCoverage ->
    recomputeRequest ->
    AyMPDERecomputeObligation missingCoverage recomputeRequest :=
  fun hmissing hrecompute =>
    ay_mpde_recompute_obligation_intro hmissing hrecompute

theorem ay_mpde_missing_coverage_no_claim
    {missingCoverage publicSatClaim : Prop} :
    missingCoverage ->
    (publicSatClaim -> False) ->
    AyMPDENoClaimDiagnostic missingCoverage publicSatClaim :=
  fun hmissing hblocks =>
    ay_mpde_no_claim_diagnostic_intro hmissing hblocks

theorem ay_mpde_conflicting_defaults_recompute
    {conflictingDefaults recomputeRequest : Prop} :
    conflictingDefaults ->
    recomputeRequest ->
    AyMPDERecomputeObligation conflictingDefaults recomputeRequest :=
  fun hconflict hrecompute =>
    ay_mpde_recompute_obligation_intro hconflict hrecompute

theorem ay_mpde_conflicting_defaults_no_claim
    {conflictingDefaults publicSatClaim : Prop} :
    conflictingDefaults ->
    (publicSatClaim -> False) ->
    AyMPDENoClaimDiagnostic conflictingDefaults publicSatClaim :=
  fun hconflict hblocks =>
    ay_mpde_no_claim_diagnostic_intro hconflict hblocks

theorem ay_mpde_checker_rejection_no_claim
    {checkerRejection publicSatClaim : Prop} :
    checkerRejection ->
    (publicSatClaim -> False) ->
    AyMPDENoClaimDiagnostic checkerRejection publicSatClaim :=
  fun hreject hblocks =>
    ay_mpde_no_claim_diagnostic_intro hreject hblocks

theorem ay_mpde_digest_mismatch_no_claim
    {digestMismatch publicSatClaim : Prop} :
    digestMismatch ->
    (publicSatClaim -> False) ->
    AyMPDENoClaimDiagnostic digestMismatch publicSatClaim :=
  fun hmismatch hblocks =>
    ay_mpde_no_claim_diagnostic_intro hmismatch hblocks

theorem ay_mpde_build_drift_no_claim
    {buildDrift publicSatClaim : Prop} :
    buildDrift ->
    (publicSatClaim -> False) ->
    AyMPDENoClaimDiagnostic buildDrift publicSatClaim :=
  fun hdrift hblocks => ay_mpde_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mpde_fingerprint_mismatch_no_claim
    {fingerprintMismatch publicSatClaim : Prop} :
    fingerprintMismatch ->
    (publicSatClaim -> False) ->
    AyMPDENoClaimDiagnostic fingerprintMismatch publicSatClaim :=
  fun hmismatch hblocks =>
    ay_mpde_no_claim_diagnostic_intro hmismatch hblocks

theorem ay_mpde_diagnostic_blocks_public_claim
    {diagnostic publicSatClaim : Prop} :
    AyMPDENoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_mpde_no_claim_diagnostic_blocks h hclaim

theorem ay_mpde_bad_default_extension_cannot_emit_sat
    {badDefaultExtension publicSatClaim : Prop} :
    AyMPDENoClaimDiagnostic badDefaultExtension publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_mpde_diagnostic_blocks_public_claim h hclaim
