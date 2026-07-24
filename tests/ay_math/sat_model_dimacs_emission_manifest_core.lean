-- SAT-COMP/ay DIMACS emission manifest soundness skeleton.
-- Public DIMACS witness files may be emitted only under accepted manifest,
-- variable/polarity map, digest, replay, build, and original fingerprint
-- evidence.

def AyMDEMConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMDEMDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMDEMEquisat (left right : Prop) : Prop :=
  AyMDEMConj (left -> right) (right -> left)

def AyMDEMEmissionManifest
    (manifestEntry witnessPath manifestAgreement : Prop) : Prop :=
  AyMDEMConj manifestEntry (AyMDEMConj witnessPath manifestAgreement)

def AyMDEMVariablePolarityMap
    (variableMap polarityMap mapAgreement : Prop) : Prop :=
  AyMDEMConj variableMap (AyMDEMConj polarityMap mapAgreement)

def AyMDEMAssignmentDigest
    (manifestDigest witnessDigest digestAgreement : Prop) : Prop :=
  AyMDEMConj manifestDigest (AyMDEMConj witnessDigest digestAgreement)

def AyMDEMClauseEvaluationReplay
    (clauseReplay witnessEvaluation evaluationAgreement : Prop) : Prop :=
  AyMDEMConj clauseReplay
    (AyMDEMConj witnessEvaluation evaluationAgreement)

def AyMDEMCheckerReplay (checkerAccepted replayTrace : Prop) : Prop :=
  AyMDEMConj checkerAccepted replayTrace

def AyMDEMSolverBuild
    (solverBuild emissionBuild buildAgreement : Prop) : Prop :=
  AyMDEMConj solverBuild (AyMDEMConj emissionBuild buildAgreement)

def AyMDEMOriginalFingerprint
    (originalFingerprint emissionFingerprint fingerprintAgreement : Prop) :
    Prop :=
  AyMDEMConj originalFingerprint
    (AyMDEMConj emissionFingerprint fingerprintAgreement)

def AyMDEMAcceptedEvidence
    (manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop) : Prop :=
  AyMDEMConj manifestOk
    (AyMDEMConj mapOk
      (AyMDEMConj digestOk
        (AyMDEMConj clauseReplayOk
          (AyMDEMConj checkerOk
            (AyMDEMConj buildOk fingerprintOk)))))

def AyMDEMPublicSatWitness
    (acceptedEvidence publicWitnessFile publicSatClaim : Prop) : Prop :=
  AyMDEMConj acceptedEvidence
    (AyMDEMConj publicWitnessFile publicSatClaim)

def AyMDEMNoClaimDiagnostic (diagnostic publicSatClaim : Prop) : Prop :=
  AyMDEMConj diagnostic (publicSatClaim -> False)

def AyMDEMRecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMDEMConj reason recomputeRequest

theorem ay_mdem_conj_intro {left right : Prop} :
    left -> right -> AyMDEMConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_mdem_conj_left {left right : Prop} :
    AyMDEMConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_mdem_conj_right {left right : Prop} :
    AyMDEMConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_mdem_disj_left {left right : Prop} :
    left -> AyMDEMDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_mdem_disj_right {left right : Prop} :
    right -> AyMDEMDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_mdem_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMDEMEquisat left right :=
  fun hf hb => ay_mdem_conj_intro hf hb

theorem ay_mdem_equisat_forward {left right : Prop} :
    AyMDEMEquisat left right -> left -> right :=
  fun h => ay_mdem_conj_left h

theorem ay_mdem_equisat_backward {left right : Prop} :
    AyMDEMEquisat left right -> right -> left :=
  fun h => ay_mdem_conj_right h

theorem ay_mdem_emission_manifest_intro
    {manifestEntry witnessPath manifestAgreement : Prop} :
    manifestEntry ->
    witnessPath ->
    manifestAgreement ->
    AyMDEMEmissionManifest manifestEntry witnessPath manifestAgreement :=
  fun hmanifest hpath hagree =>
    ay_mdem_conj_intro hmanifest (ay_mdem_conj_intro hpath hagree)

theorem ay_mdem_emission_manifest_entry
    {manifestEntry witnessPath manifestAgreement : Prop} :
    AyMDEMEmissionManifest manifestEntry witnessPath manifestAgreement ->
    manifestEntry :=
  fun h => ay_mdem_conj_left h

theorem ay_mdem_emission_manifest_path
    {manifestEntry witnessPath manifestAgreement : Prop} :
    AyMDEMEmissionManifest manifestEntry witnessPath manifestAgreement ->
    witnessPath :=
  fun h => ay_mdem_conj_left (ay_mdem_conj_right h)

theorem ay_mdem_emission_manifest_agreement
    {manifestEntry witnessPath manifestAgreement : Prop} :
    AyMDEMEmissionManifest manifestEntry witnessPath manifestAgreement ->
    manifestAgreement :=
  fun h => ay_mdem_conj_right (ay_mdem_conj_right h)

theorem ay_mdem_variable_polarity_map_intro
    {variableMap polarityMap mapAgreement : Prop} :
    variableMap ->
    polarityMap ->
    mapAgreement ->
    AyMDEMVariablePolarityMap variableMap polarityMap mapAgreement :=
  fun hvar hpol hagree =>
    ay_mdem_conj_intro hvar (ay_mdem_conj_intro hpol hagree)

theorem ay_mdem_variable_polarity_map_variable
    {variableMap polarityMap mapAgreement : Prop} :
    AyMDEMVariablePolarityMap variableMap polarityMap mapAgreement ->
    variableMap :=
  fun h => ay_mdem_conj_left h

theorem ay_mdem_variable_polarity_map_polarity
    {variableMap polarityMap mapAgreement : Prop} :
    AyMDEMVariablePolarityMap variableMap polarityMap mapAgreement ->
    polarityMap :=
  fun h => ay_mdem_conj_left (ay_mdem_conj_right h)

theorem ay_mdem_variable_polarity_map_agreement
    {variableMap polarityMap mapAgreement : Prop} :
    AyMDEMVariablePolarityMap variableMap polarityMap mapAgreement ->
    mapAgreement :=
  fun h => ay_mdem_conj_right (ay_mdem_conj_right h)

theorem ay_mdem_assignment_digest_intro
    {manifestDigest witnessDigest digestAgreement : Prop} :
    manifestDigest ->
    witnessDigest ->
    digestAgreement ->
    AyMDEMAssignmentDigest manifestDigest witnessDigest digestAgreement :=
  fun hmanifest hwitness hagree =>
    ay_mdem_conj_intro hmanifest (ay_mdem_conj_intro hwitness hagree)

theorem ay_mdem_assignment_digest_manifest
    {manifestDigest witnessDigest digestAgreement : Prop} :
    AyMDEMAssignmentDigest manifestDigest witnessDigest digestAgreement ->
    manifestDigest :=
  fun h => ay_mdem_conj_left h

theorem ay_mdem_assignment_digest_witness
    {manifestDigest witnessDigest digestAgreement : Prop} :
    AyMDEMAssignmentDigest manifestDigest witnessDigest digestAgreement ->
    witnessDigest :=
  fun h => ay_mdem_conj_left (ay_mdem_conj_right h)

theorem ay_mdem_assignment_digest_agreement
    {manifestDigest witnessDigest digestAgreement : Prop} :
    AyMDEMAssignmentDigest manifestDigest witnessDigest digestAgreement ->
    digestAgreement :=
  fun h => ay_mdem_conj_right (ay_mdem_conj_right h)

theorem ay_mdem_clause_evaluation_replay_intro
    {clauseReplay witnessEvaluation evaluationAgreement : Prop} :
    clauseReplay ->
    witnessEvaluation ->
    evaluationAgreement ->
    AyMDEMClauseEvaluationReplay
      clauseReplay witnessEvaluation evaluationAgreement :=
  fun hreplay heval hagree =>
    ay_mdem_conj_intro hreplay (ay_mdem_conj_intro heval hagree)

theorem ay_mdem_clause_evaluation_replay_trace
    {clauseReplay witnessEvaluation evaluationAgreement : Prop} :
    AyMDEMClauseEvaluationReplay
      clauseReplay witnessEvaluation evaluationAgreement ->
    clauseReplay :=
  fun h => ay_mdem_conj_left h

theorem ay_mdem_clause_evaluation_replay_evaluation
    {clauseReplay witnessEvaluation evaluationAgreement : Prop} :
    AyMDEMClauseEvaluationReplay
      clauseReplay witnessEvaluation evaluationAgreement ->
    witnessEvaluation :=
  fun h => ay_mdem_conj_left (ay_mdem_conj_right h)

theorem ay_mdem_clause_evaluation_replay_agreement
    {clauseReplay witnessEvaluation evaluationAgreement : Prop} :
    AyMDEMClauseEvaluationReplay
      clauseReplay witnessEvaluation evaluationAgreement ->
    evaluationAgreement :=
  fun h => ay_mdem_conj_right (ay_mdem_conj_right h)

theorem ay_mdem_checker_replay_intro
    {checkerAccepted replayTrace : Prop} :
    checkerAccepted ->
    replayTrace ->
    AyMDEMCheckerReplay checkerAccepted replayTrace :=
  fun haccepted htrace => ay_mdem_conj_intro haccepted htrace

theorem ay_mdem_checker_replay_accepted
    {checkerAccepted replayTrace : Prop} :
    AyMDEMCheckerReplay checkerAccepted replayTrace -> checkerAccepted :=
  fun h => ay_mdem_conj_left h

theorem ay_mdem_checker_replay_trace
    {checkerAccepted replayTrace : Prop} :
    AyMDEMCheckerReplay checkerAccepted replayTrace -> replayTrace :=
  fun h => ay_mdem_conj_right h

theorem ay_mdem_solver_build_intro
    {solverBuild emissionBuild buildAgreement : Prop} :
    solverBuild ->
    emissionBuild ->
    buildAgreement ->
    AyMDEMSolverBuild solverBuild emissionBuild buildAgreement :=
  fun hsolver hemission hagree =>
    ay_mdem_conj_intro hsolver (ay_mdem_conj_intro hemission hagree)

theorem ay_mdem_solver_build_solver
    {solverBuild emissionBuild buildAgreement : Prop} :
    AyMDEMSolverBuild solverBuild emissionBuild buildAgreement ->
    solverBuild :=
  fun h => ay_mdem_conj_left h

theorem ay_mdem_solver_build_emission
    {solverBuild emissionBuild buildAgreement : Prop} :
    AyMDEMSolverBuild solverBuild emissionBuild buildAgreement ->
    emissionBuild :=
  fun h => ay_mdem_conj_left (ay_mdem_conj_right h)

theorem ay_mdem_solver_build_agreement
    {solverBuild emissionBuild buildAgreement : Prop} :
    AyMDEMSolverBuild solverBuild emissionBuild buildAgreement ->
    buildAgreement :=
  fun h => ay_mdem_conj_right (ay_mdem_conj_right h)

theorem ay_mdem_original_fingerprint_intro
    {originalFingerprint emissionFingerprint fingerprintAgreement : Prop} :
    originalFingerprint ->
    emissionFingerprint ->
    fingerprintAgreement ->
    AyMDEMOriginalFingerprint
      originalFingerprint emissionFingerprint fingerprintAgreement :=
  fun horiginal hemission hagree =>
    ay_mdem_conj_intro horiginal (ay_mdem_conj_intro hemission hagree)

theorem ay_mdem_original_fingerprint_original
    {originalFingerprint emissionFingerprint fingerprintAgreement : Prop} :
    AyMDEMOriginalFingerprint
      originalFingerprint emissionFingerprint fingerprintAgreement ->
    originalFingerprint :=
  fun h => ay_mdem_conj_left h

theorem ay_mdem_original_fingerprint_emission
    {originalFingerprint emissionFingerprint fingerprintAgreement : Prop} :
    AyMDEMOriginalFingerprint
      originalFingerprint emissionFingerprint fingerprintAgreement ->
    emissionFingerprint :=
  fun h => ay_mdem_conj_left (ay_mdem_conj_right h)

theorem ay_mdem_original_fingerprint_agreement
    {originalFingerprint emissionFingerprint fingerprintAgreement : Prop} :
    AyMDEMOriginalFingerprint
      originalFingerprint emissionFingerprint fingerprintAgreement ->
    fingerprintAgreement :=
  fun h => ay_mdem_conj_right (ay_mdem_conj_right h)

theorem ay_mdem_accepted_evidence_intro
    {manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    manifestOk ->
    mapOk ->
    digestOk ->
    clauseReplayOk ->
    checkerOk ->
    buildOk ->
    fingerprintOk ->
    AyMDEMAcceptedEvidence
      manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk :=
  fun hmanifest hmap hdigest hclause hchecker hbuild hfingerprint =>
    ay_mdem_conj_intro hmanifest
      (ay_mdem_conj_intro hmap
        (ay_mdem_conj_intro hdigest
          (ay_mdem_conj_intro hclause
            (ay_mdem_conj_intro hchecker
              (ay_mdem_conj_intro hbuild hfingerprint)))))

theorem ay_mdem_accepted_evidence_manifest
    {manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMDEMAcceptedEvidence
      manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    manifestOk :=
  fun h => ay_mdem_conj_left h

theorem ay_mdem_accepted_evidence_map
    {manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMDEMAcceptedEvidence
      manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    mapOk :=
  fun h => ay_mdem_conj_left (ay_mdem_conj_right h)

theorem ay_mdem_accepted_evidence_digest
    {manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMDEMAcceptedEvidence
      manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    digestOk :=
  fun h => ay_mdem_conj_left
    (ay_mdem_conj_right (ay_mdem_conj_right h))

theorem ay_mdem_accepted_evidence_clause_replay
    {manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMDEMAcceptedEvidence
      manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    clauseReplayOk :=
  fun h => ay_mdem_conj_left
    (ay_mdem_conj_right
      (ay_mdem_conj_right (ay_mdem_conj_right h)))

theorem ay_mdem_accepted_evidence_checker
    {manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMDEMAcceptedEvidence
      manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    checkerOk :=
  fun h => ay_mdem_conj_left
    (ay_mdem_conj_right
      (ay_mdem_conj_right
        (ay_mdem_conj_right (ay_mdem_conj_right h))))

theorem ay_mdem_accepted_evidence_build
    {manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMDEMAcceptedEvidence
      manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    buildOk :=
  fun h => ay_mdem_conj_left
    (ay_mdem_conj_right
      (ay_mdem_conj_right
        (ay_mdem_conj_right
          (ay_mdem_conj_right (ay_mdem_conj_right h)))))

theorem ay_mdem_accepted_evidence_fingerprint
    {manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk : Prop} :
    AyMDEMAcceptedEvidence
      manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    fingerprintOk :=
  fun h => ay_mdem_conj_right
    (ay_mdem_conj_right
      (ay_mdem_conj_right
        (ay_mdem_conj_right
          (ay_mdem_conj_right (ay_mdem_conj_right h)))))

theorem ay_mdem_public_sat_witness_intro
    {acceptedEvidence publicWitnessFile publicSatClaim : Prop} :
    acceptedEvidence ->
    publicWitnessFile ->
    publicSatClaim ->
    AyMDEMPublicSatWitness
      acceptedEvidence publicWitnessFile publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_mdem_conj_intro hevidence
      (ay_mdem_conj_intro hwitness hclaim)

theorem ay_mdem_public_sat_witness_evidence
    {acceptedEvidence publicWitnessFile publicSatClaim : Prop} :
    AyMDEMPublicSatWitness
      acceptedEvidence publicWitnessFile publicSatClaim ->
    acceptedEvidence :=
  fun h => ay_mdem_conj_left h

theorem ay_mdem_public_sat_witness_file
    {acceptedEvidence publicWitnessFile publicSatClaim : Prop} :
    AyMDEMPublicSatWitness
      acceptedEvidence publicWitnessFile publicSatClaim ->
    publicWitnessFile :=
  fun h => ay_mdem_conj_left (ay_mdem_conj_right h)

theorem ay_mdem_public_sat_witness_claim
    {acceptedEvidence publicWitnessFile publicSatClaim : Prop} :
    AyMDEMPublicSatWitness
      acceptedEvidence publicWitnessFile publicSatClaim ->
    publicSatClaim :=
  fun h => ay_mdem_conj_right (ay_mdem_conj_right h)

theorem ay_mdem_accepted_manifest_publishes_sound_sat
    {manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk fingerprintOk
      publicWitnessFile publicSatClaim : Prop} :
    AyMDEMAcceptedEvidence
      manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk
      fingerprintOk ->
    publicWitnessFile ->
    publicSatClaim ->
    AyMDEMPublicSatWitness
      (AyMDEMAcceptedEvidence
        manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitnessFile
      publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_mdem_public_sat_witness_intro hevidence hwitness hclaim

theorem ay_mdem_public_sat_requires_accepted_evidence
    {acceptedEvidence publicWitnessFile publicSatClaim : Prop} :
    AyMDEMPublicSatWitness
      acceptedEvidence publicWitnessFile publicSatClaim ->
    acceptedEvidence :=
  fun h => ay_mdem_public_sat_witness_evidence h

theorem ay_mdem_stale_witness_file_cannot_bless_sat
    {staleWitnessFile publicSatClaim : Prop} :
    AyMDEMNoClaimDiagnostic staleWitnessFile publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim =>
    (h (publicSatClaim -> False) (fun _ hblocks => hblocks)) hclaim

theorem ay_mdem_clause_replay_transports_truth
    {clauseReplay witnessEvaluation formulaTruth : Prop} :
    AyMDEMClauseEvaluationReplay
      clauseReplay witnessEvaluation formulaTruth ->
    formulaTruth :=
  fun h => ay_mdem_clause_evaluation_replay_agreement h

theorem ay_mdem_publication_requires_manifest
    {manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk fingerprintOk
      publicWitnessFile publicSatClaim : Prop} :
    AyMDEMPublicSatWitness
      (AyMDEMAcceptedEvidence
        manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitnessFile
      publicSatClaim ->
    manifestOk :=
  fun h =>
    ay_mdem_accepted_evidence_manifest
      (ay_mdem_public_sat_witness_evidence h)

theorem ay_mdem_publication_requires_map
    {manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk fingerprintOk
      publicWitnessFile publicSatClaim : Prop} :
    AyMDEMPublicSatWitness
      (AyMDEMAcceptedEvidence
        manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitnessFile
      publicSatClaim ->
    mapOk :=
  fun h =>
    ay_mdem_accepted_evidence_map
      (ay_mdem_public_sat_witness_evidence h)

theorem ay_mdem_publication_requires_digest
    {manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk fingerprintOk
      publicWitnessFile publicSatClaim : Prop} :
    AyMDEMPublicSatWitness
      (AyMDEMAcceptedEvidence
        manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitnessFile
      publicSatClaim ->
    digestOk :=
  fun h =>
    ay_mdem_accepted_evidence_digest
      (ay_mdem_public_sat_witness_evidence h)

theorem ay_mdem_publication_requires_clause_replay
    {manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk fingerprintOk
      publicWitnessFile publicSatClaim : Prop} :
    AyMDEMPublicSatWitness
      (AyMDEMAcceptedEvidence
        manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitnessFile
      publicSatClaim ->
    clauseReplayOk :=
  fun h =>
    ay_mdem_accepted_evidence_clause_replay
      (ay_mdem_public_sat_witness_evidence h)

theorem ay_mdem_publication_requires_checker
    {manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk fingerprintOk
      publicWitnessFile publicSatClaim : Prop} :
    AyMDEMPublicSatWitness
      (AyMDEMAcceptedEvidence
        manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitnessFile
      publicSatClaim ->
    checkerOk :=
  fun h =>
    ay_mdem_accepted_evidence_checker
      (ay_mdem_public_sat_witness_evidence h)

theorem ay_mdem_publication_requires_build
    {manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk fingerprintOk
      publicWitnessFile publicSatClaim : Prop} :
    AyMDEMPublicSatWitness
      (AyMDEMAcceptedEvidence
        manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitnessFile
      publicSatClaim ->
    buildOk :=
  fun h =>
    ay_mdem_accepted_evidence_build
      (ay_mdem_public_sat_witness_evidence h)

theorem ay_mdem_publication_requires_fingerprint
    {manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk fingerprintOk
      publicWitnessFile publicSatClaim : Prop} :
    AyMDEMPublicSatWitness
      (AyMDEMAcceptedEvidence
        manifestOk mapOk digestOk clauseReplayOk checkerOk buildOk
        fingerprintOk)
      publicWitnessFile
      publicSatClaim ->
    fingerprintOk :=
  fun h =>
    ay_mdem_accepted_evidence_fingerprint
      (ay_mdem_public_sat_witness_evidence h)

theorem ay_mdem_no_claim_diagnostic_intro
    {diagnostic publicSatClaim : Prop} :
    diagnostic ->
    (publicSatClaim -> False) ->
    AyMDEMNoClaimDiagnostic diagnostic publicSatClaim :=
  fun hdiagnostic hblocks =>
    ay_mdem_conj_intro hdiagnostic hblocks

theorem ay_mdem_no_claim_diagnostic_reason
    {diagnostic publicSatClaim : Prop} :
    AyMDEMNoClaimDiagnostic diagnostic publicSatClaim -> diagnostic :=
  fun h => ay_mdem_conj_left h

theorem ay_mdem_no_claim_diagnostic_blocks
    {diagnostic publicSatClaim : Prop} :
    AyMDEMNoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h => ay_mdem_conj_right h

theorem ay_mdem_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMDEMRecomputeObligation reason recomputeRequest :=
  fun hreason hrecompute => ay_mdem_conj_intro hreason hrecompute

theorem ay_mdem_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMDEMRecomputeObligation reason recomputeRequest -> reason :=
  fun h => ay_mdem_conj_left h

theorem ay_mdem_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMDEMRecomputeObligation reason recomputeRequest -> recomputeRequest :=
  fun h => ay_mdem_conj_right h

theorem ay_mdem_manifest_drift_recompute
    {manifestDrift recomputeRequest : Prop} :
    manifestDrift ->
    recomputeRequest ->
    AyMDEMRecomputeObligation manifestDrift recomputeRequest :=
  fun hdrift hrecompute =>
    ay_mdem_recompute_obligation_intro hdrift hrecompute

theorem ay_mdem_manifest_drift_no_claim
    {manifestDrift publicSatClaim : Prop} :
    manifestDrift ->
    (publicSatClaim -> False) ->
    AyMDEMNoClaimDiagnostic manifestDrift publicSatClaim :=
  fun hdrift hblocks => ay_mdem_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mdem_path_drift_recompute
    {pathDrift recomputeRequest : Prop} :
    pathDrift ->
    recomputeRequest ->
    AyMDEMRecomputeObligation pathDrift recomputeRequest :=
  fun hdrift hrecompute =>
    ay_mdem_recompute_obligation_intro hdrift hrecompute

theorem ay_mdem_path_drift_no_claim
    {pathDrift publicSatClaim : Prop} :
    pathDrift ->
    (publicSatClaim -> False) ->
    AyMDEMNoClaimDiagnostic pathDrift publicSatClaim :=
  fun hdrift hblocks => ay_mdem_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mdem_stale_witness_file_no_claim
    {staleWitnessFile publicSatClaim : Prop} :
    staleWitnessFile ->
    (publicSatClaim -> False) ->
    AyMDEMNoClaimDiagnostic staleWitnessFile publicSatClaim :=
  fun hstale hblocks => ay_mdem_no_claim_diagnostic_intro hstale hblocks

theorem ay_mdem_checker_rejection_no_claim
    {checkerRejection publicSatClaim : Prop} :
    checkerRejection ->
    (publicSatClaim -> False) ->
    AyMDEMNoClaimDiagnostic checkerRejection publicSatClaim :=
  fun hreject hblocks =>
    ay_mdem_no_claim_diagnostic_intro hreject hblocks

theorem ay_mdem_digest_mismatch_no_claim
    {digestMismatch publicSatClaim : Prop} :
    digestMismatch ->
    (publicSatClaim -> False) ->
    AyMDEMNoClaimDiagnostic digestMismatch publicSatClaim :=
  fun hmismatch hblocks =>
    ay_mdem_no_claim_diagnostic_intro hmismatch hblocks

theorem ay_mdem_build_drift_no_claim
    {buildDrift publicSatClaim : Prop} :
    buildDrift ->
    (publicSatClaim -> False) ->
    AyMDEMNoClaimDiagnostic buildDrift publicSatClaim :=
  fun hdrift hblocks => ay_mdem_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mdem_fingerprint_mismatch_no_claim
    {fingerprintMismatch publicSatClaim : Prop} :
    fingerprintMismatch ->
    (publicSatClaim -> False) ->
    AyMDEMNoClaimDiagnostic fingerprintMismatch publicSatClaim :=
  fun hmismatch hblocks =>
    ay_mdem_no_claim_diagnostic_intro hmismatch hblocks

theorem ay_mdem_diagnostic_blocks_public_claim
    {diagnostic publicSatClaim : Prop} :
    AyMDEMNoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_mdem_no_claim_diagnostic_blocks h hclaim

theorem ay_mdem_bad_emission_manifest_cannot_emit_sat
    {badEmission publicSatClaim : Prop} :
    AyMDEMNoClaimDiagnostic badEmission publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_mdem_diagnostic_blocks_public_claim h hclaim
