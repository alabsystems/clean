-- SAT-COMP/ay witness delta replay soundness skeleton.
-- Delta-compressed model updates reconstruct a public SAT witness only when the
-- base digest, delta operations, ordering, reconstruction, checker replay,
-- solver build, and original fingerprint evidence agree.

def AyMWDRConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMWDRDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMWDREquisat (left right : Prop) : Prop :=
  AyMWDRConj (left -> right) (right -> left)

def AyMWDRBaseWitnessDigest
    (baseWitness baseDigest baseDigestAgreement : Prop) : Prop :=
  AyMWDRConj baseWitness (AyMWDRConj baseDigest baseDigestAgreement)

def AyMWDRDeltaOperations
    (deltaLog deltaApplies deltaWellformed : Prop) : Prop :=
  AyMWDRConj deltaLog (AyMWDRConj deltaApplies deltaWellformed)

def AyMWDRVariableOrder
    (baseOrder deltaOrder orderAgreement : Prop) : Prop :=
  AyMWDRConj baseOrder (AyMWDRConj deltaOrder orderAgreement)

def AyMWDRProjectionDefaults
    (projectionMap defaultReconstruction reconstructionAgreement : Prop) :
    Prop :=
  AyMWDRConj projectionMap
    (AyMWDRConj defaultReconstruction reconstructionAgreement)

def AyMWDRAssignmentDigest
    (replayedAssignment replayDigest digestAgreement : Prop) : Prop :=
  AyMWDRConj replayedAssignment
    (AyMWDRConj replayDigest digestAgreement)

def AyMWDRCheckerReplay (checkerAccepted replayTrace : Prop) : Prop :=
  AyMWDRConj checkerAccepted replayTrace

def AyMWDRSolverBuild
    (solverBuild deltaBuild buildAgreement : Prop) : Prop :=
  AyMWDRConj solverBuild (AyMWDRConj deltaBuild buildAgreement)

def AyMWDROriginalFingerprint
    (originalFingerprint replayFingerprint fingerprintAgreement : Prop) :
    Prop :=
  AyMWDRConj originalFingerprint
    (AyMWDRConj replayFingerprint fingerprintAgreement)

def AyMWDRReplayEvidence
    (baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
      fingerprintOk : Prop) : Prop :=
  AyMWDRConj baseOk
    (AyMWDRConj deltaOk
      (AyMWDRConj orderOk
        (AyMWDRConj reconstructionOk
          (AyMWDRConj digestOk
            (AyMWDRConj replayOk
              (AyMWDRConj buildOk fingerprintOk))))))

def AyMWDRPublicSatResult
    (replayEvidence replayedWitness publicSatClaim : Prop) : Prop :=
  AyMWDRConj replayEvidence
    (AyMWDRConj replayedWitness publicSatClaim)

def AyMWDRNoClaimDiagnostic (diagnostic publicSatClaim : Prop) : Prop :=
  AyMWDRConj diagnostic (publicSatClaim -> False)

def AyMWDRRecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMWDRConj reason recomputeRequest

theorem ay_mwdr_conj_intro {left right : Prop} :
    left -> right -> AyMWDRConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_mwdr_conj_left {left right : Prop} :
    AyMWDRConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_mwdr_conj_right {left right : Prop} :
    AyMWDRConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_mwdr_disj_left {left right : Prop} :
    left -> AyMWDRDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_mwdr_disj_right {left right : Prop} :
    right -> AyMWDRDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_mwdr_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMWDREquisat left right :=
  fun hf hb => ay_mwdr_conj_intro hf hb

theorem ay_mwdr_equisat_forward {left right : Prop} :
    AyMWDREquisat left right -> left -> right :=
  fun h => ay_mwdr_conj_left h

theorem ay_mwdr_equisat_backward {left right : Prop} :
    AyMWDREquisat left right -> right -> left :=
  fun h => ay_mwdr_conj_right h

theorem ay_mwdr_base_witness_digest_intro
    {baseWitness baseDigest baseDigestAgreement : Prop} :
    baseWitness ->
    baseDigest ->
    baseDigestAgreement ->
    AyMWDRBaseWitnessDigest
      baseWitness baseDigest baseDigestAgreement :=
  fun hwitness hdigest hagree =>
    ay_mwdr_conj_intro hwitness
      (ay_mwdr_conj_intro hdigest hagree)

theorem ay_mwdr_base_witness_digest_witness
    {baseWitness baseDigest baseDigestAgreement : Prop} :
    AyMWDRBaseWitnessDigest
      baseWitness baseDigest baseDigestAgreement ->
    baseWitness :=
  fun h => ay_mwdr_conj_left h

theorem ay_mwdr_base_witness_digest_digest
    {baseWitness baseDigest baseDigestAgreement : Prop} :
    AyMWDRBaseWitnessDigest
      baseWitness baseDigest baseDigestAgreement ->
    baseDigest :=
  fun h => ay_mwdr_conj_left (ay_mwdr_conj_right h)

theorem ay_mwdr_base_witness_digest_agreement
    {baseWitness baseDigest baseDigestAgreement : Prop} :
    AyMWDRBaseWitnessDigest
      baseWitness baseDigest baseDigestAgreement ->
    baseDigestAgreement :=
  fun h => ay_mwdr_conj_right (ay_mwdr_conj_right h)

theorem ay_mwdr_delta_operations_intro
    {deltaLog deltaApplies deltaWellformed : Prop} :
    deltaLog ->
    deltaApplies ->
    deltaWellformed ->
    AyMWDRDeltaOperations deltaLog deltaApplies deltaWellformed :=
  fun hlog happlies hwellformed =>
    ay_mwdr_conj_intro hlog
      (ay_mwdr_conj_intro happlies hwellformed)

theorem ay_mwdr_delta_operations_log
    {deltaLog deltaApplies deltaWellformed : Prop} :
    AyMWDRDeltaOperations deltaLog deltaApplies deltaWellformed ->
    deltaLog :=
  fun h => ay_mwdr_conj_left h

theorem ay_mwdr_delta_operations_applies
    {deltaLog deltaApplies deltaWellformed : Prop} :
    AyMWDRDeltaOperations deltaLog deltaApplies deltaWellformed ->
    deltaApplies :=
  fun h => ay_mwdr_conj_left (ay_mwdr_conj_right h)

theorem ay_mwdr_delta_operations_wellformed
    {deltaLog deltaApplies deltaWellformed : Prop} :
    AyMWDRDeltaOperations deltaLog deltaApplies deltaWellformed ->
    deltaWellformed :=
  fun h => ay_mwdr_conj_right (ay_mwdr_conj_right h)

theorem ay_mwdr_variable_order_intro
    {baseOrder deltaOrder orderAgreement : Prop} :
    baseOrder ->
    deltaOrder ->
    orderAgreement ->
    AyMWDRVariableOrder baseOrder deltaOrder orderAgreement :=
  fun hbase hdelta hagree =>
    ay_mwdr_conj_intro hbase (ay_mwdr_conj_intro hdelta hagree)

theorem ay_mwdr_variable_order_base
    {baseOrder deltaOrder orderAgreement : Prop} :
    AyMWDRVariableOrder baseOrder deltaOrder orderAgreement ->
    baseOrder :=
  fun h => ay_mwdr_conj_left h

theorem ay_mwdr_variable_order_delta
    {baseOrder deltaOrder orderAgreement : Prop} :
    AyMWDRVariableOrder baseOrder deltaOrder orderAgreement ->
    deltaOrder :=
  fun h => ay_mwdr_conj_left (ay_mwdr_conj_right h)

theorem ay_mwdr_variable_order_agreement
    {baseOrder deltaOrder orderAgreement : Prop} :
    AyMWDRVariableOrder baseOrder deltaOrder orderAgreement ->
    orderAgreement :=
  fun h => ay_mwdr_conj_right (ay_mwdr_conj_right h)

theorem ay_mwdr_projection_defaults_intro
    {projectionMap defaultReconstruction reconstructionAgreement : Prop} :
    projectionMap ->
    defaultReconstruction ->
    reconstructionAgreement ->
    AyMWDRProjectionDefaults
      projectionMap defaultReconstruction reconstructionAgreement :=
  fun hprojection hdefaults hagree =>
    ay_mwdr_conj_intro hprojection
      (ay_mwdr_conj_intro hdefaults hagree)

theorem ay_mwdr_projection_defaults_map
    {projectionMap defaultReconstruction reconstructionAgreement : Prop} :
    AyMWDRProjectionDefaults
      projectionMap defaultReconstruction reconstructionAgreement ->
    projectionMap :=
  fun h => ay_mwdr_conj_left h

theorem ay_mwdr_projection_defaults_defaults
    {projectionMap defaultReconstruction reconstructionAgreement : Prop} :
    AyMWDRProjectionDefaults
      projectionMap defaultReconstruction reconstructionAgreement ->
    defaultReconstruction :=
  fun h => ay_mwdr_conj_left (ay_mwdr_conj_right h)

theorem ay_mwdr_projection_defaults_agreement
    {projectionMap defaultReconstruction reconstructionAgreement : Prop} :
    AyMWDRProjectionDefaults
      projectionMap defaultReconstruction reconstructionAgreement ->
    reconstructionAgreement :=
  fun h => ay_mwdr_conj_right (ay_mwdr_conj_right h)

theorem ay_mwdr_assignment_digest_intro
    {replayedAssignment replayDigest digestAgreement : Prop} :
    replayedAssignment ->
    replayDigest ->
    digestAgreement ->
    AyMWDRAssignmentDigest
      replayedAssignment replayDigest digestAgreement :=
  fun hassignment hdigest hagree =>
    ay_mwdr_conj_intro hassignment
      (ay_mwdr_conj_intro hdigest hagree)

theorem ay_mwdr_assignment_digest_assignment
    {replayedAssignment replayDigest digestAgreement : Prop} :
    AyMWDRAssignmentDigest
      replayedAssignment replayDigest digestAgreement ->
    replayedAssignment :=
  fun h => ay_mwdr_conj_left h

theorem ay_mwdr_assignment_digest_digest
    {replayedAssignment replayDigest digestAgreement : Prop} :
    AyMWDRAssignmentDigest
      replayedAssignment replayDigest digestAgreement ->
    replayDigest :=
  fun h => ay_mwdr_conj_left (ay_mwdr_conj_right h)

theorem ay_mwdr_assignment_digest_agreement
    {replayedAssignment replayDigest digestAgreement : Prop} :
    AyMWDRAssignmentDigest
      replayedAssignment replayDigest digestAgreement ->
    digestAgreement :=
  fun h => ay_mwdr_conj_right (ay_mwdr_conj_right h)

theorem ay_mwdr_checker_replay_intro
    {checkerAccepted replayTrace : Prop} :
    checkerAccepted ->
    replayTrace ->
    AyMWDRCheckerReplay checkerAccepted replayTrace :=
  fun haccepted htrace => ay_mwdr_conj_intro haccepted htrace

theorem ay_mwdr_checker_replay_accepted
    {checkerAccepted replayTrace : Prop} :
    AyMWDRCheckerReplay checkerAccepted replayTrace -> checkerAccepted :=
  fun h => ay_mwdr_conj_left h

theorem ay_mwdr_checker_replay_trace
    {checkerAccepted replayTrace : Prop} :
    AyMWDRCheckerReplay checkerAccepted replayTrace -> replayTrace :=
  fun h => ay_mwdr_conj_right h

theorem ay_mwdr_solver_build_intro
    {solverBuild deltaBuild buildAgreement : Prop} :
    solverBuild ->
    deltaBuild ->
    buildAgreement ->
    AyMWDRSolverBuild solverBuild deltaBuild buildAgreement :=
  fun hsolver hdelta hagree =>
    ay_mwdr_conj_intro hsolver
      (ay_mwdr_conj_intro hdelta hagree)

theorem ay_mwdr_solver_build_solver
    {solverBuild deltaBuild buildAgreement : Prop} :
    AyMWDRSolverBuild solverBuild deltaBuild buildAgreement -> solverBuild :=
  fun h => ay_mwdr_conj_left h

theorem ay_mwdr_solver_build_delta
    {solverBuild deltaBuild buildAgreement : Prop} :
    AyMWDRSolverBuild solverBuild deltaBuild buildAgreement -> deltaBuild :=
  fun h => ay_mwdr_conj_left (ay_mwdr_conj_right h)

theorem ay_mwdr_solver_build_agreement
    {solverBuild deltaBuild buildAgreement : Prop} :
    AyMWDRSolverBuild solverBuild deltaBuild buildAgreement ->
    buildAgreement :=
  fun h => ay_mwdr_conj_right (ay_mwdr_conj_right h)

theorem ay_mwdr_original_fingerprint_intro
    {originalFingerprint replayFingerprint fingerprintAgreement : Prop} :
    originalFingerprint ->
    replayFingerprint ->
    fingerprintAgreement ->
    AyMWDROriginalFingerprint
      originalFingerprint replayFingerprint fingerprintAgreement :=
  fun horiginal hreplay hagree =>
    ay_mwdr_conj_intro horiginal
      (ay_mwdr_conj_intro hreplay hagree)

theorem ay_mwdr_original_fingerprint_original
    {originalFingerprint replayFingerprint fingerprintAgreement : Prop} :
    AyMWDROriginalFingerprint
      originalFingerprint replayFingerprint fingerprintAgreement ->
    originalFingerprint :=
  fun h => ay_mwdr_conj_left h

theorem ay_mwdr_original_fingerprint_replay
    {originalFingerprint replayFingerprint fingerprintAgreement : Prop} :
    AyMWDROriginalFingerprint
      originalFingerprint replayFingerprint fingerprintAgreement ->
    replayFingerprint :=
  fun h => ay_mwdr_conj_left (ay_mwdr_conj_right h)

theorem ay_mwdr_original_fingerprint_agreement
    {originalFingerprint replayFingerprint fingerprintAgreement : Prop} :
    AyMWDROriginalFingerprint
      originalFingerprint replayFingerprint fingerprintAgreement ->
    fingerprintAgreement :=
  fun h => ay_mwdr_conj_right (ay_mwdr_conj_right h)

theorem ay_mwdr_replay_evidence_intro
    {baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    baseOk ->
    deltaOk ->
    orderOk ->
    reconstructionOk ->
    digestOk ->
    replayOk ->
    buildOk ->
    fingerprintOk ->
    AyMWDRReplayEvidence
      baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
      fingerprintOk :=
  fun hbase hdelta horder hreconstruction hdigest hreplay hbuild
      hfingerprint =>
    ay_mwdr_conj_intro hbase
      (ay_mwdr_conj_intro hdelta
        (ay_mwdr_conj_intro horder
          (ay_mwdr_conj_intro hreconstruction
            (ay_mwdr_conj_intro hdigest
              (ay_mwdr_conj_intro hreplay
                (ay_mwdr_conj_intro hbuild hfingerprint))))))

theorem ay_mwdr_replay_evidence_base
    {baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMWDRReplayEvidence
      baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
      fingerprintOk ->
    baseOk :=
  fun h => ay_mwdr_conj_left h

theorem ay_mwdr_replay_evidence_delta
    {baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMWDRReplayEvidence
      baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
      fingerprintOk ->
    deltaOk :=
  fun h => ay_mwdr_conj_left (ay_mwdr_conj_right h)

theorem ay_mwdr_replay_evidence_order
    {baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMWDRReplayEvidence
      baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
      fingerprintOk ->
    orderOk :=
  fun h => ay_mwdr_conj_left
    (ay_mwdr_conj_right (ay_mwdr_conj_right h))

theorem ay_mwdr_replay_evidence_reconstruction
    {baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMWDRReplayEvidence
      baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
      fingerprintOk ->
    reconstructionOk :=
  fun h => ay_mwdr_conj_left
    (ay_mwdr_conj_right
      (ay_mwdr_conj_right (ay_mwdr_conj_right h)))

theorem ay_mwdr_replay_evidence_digest
    {baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMWDRReplayEvidence
      baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
      fingerprintOk ->
    digestOk :=
  fun h => ay_mwdr_conj_left
    (ay_mwdr_conj_right
      (ay_mwdr_conj_right
        (ay_mwdr_conj_right (ay_mwdr_conj_right h))))

theorem ay_mwdr_replay_evidence_replay
    {baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMWDRReplayEvidence
      baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
      fingerprintOk ->
    replayOk :=
  fun h => ay_mwdr_conj_left
    (ay_mwdr_conj_right
      (ay_mwdr_conj_right
        (ay_mwdr_conj_right
          (ay_mwdr_conj_right (ay_mwdr_conj_right h)))))

theorem ay_mwdr_replay_evidence_build
    {baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMWDRReplayEvidence
      baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
      fingerprintOk ->
    buildOk :=
  fun h => ay_mwdr_conj_left
    (ay_mwdr_conj_right
      (ay_mwdr_conj_right
        (ay_mwdr_conj_right
          (ay_mwdr_conj_right
            (ay_mwdr_conj_right (ay_mwdr_conj_right h))))))

theorem ay_mwdr_replay_evidence_fingerprint
    {baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMWDRReplayEvidence
      baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
      fingerprintOk ->
    fingerprintOk :=
  fun h => ay_mwdr_conj_right
    (ay_mwdr_conj_right
      (ay_mwdr_conj_right
        (ay_mwdr_conj_right
          (ay_mwdr_conj_right
            (ay_mwdr_conj_right (ay_mwdr_conj_right h))))))

theorem ay_mwdr_public_sat_result_intro
    {replayEvidence replayedWitness publicSatClaim : Prop} :
    replayEvidence ->
    replayedWitness ->
    publicSatClaim ->
    AyMWDRPublicSatResult replayEvidence replayedWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_mwdr_conj_intro hevidence
      (ay_mwdr_conj_intro hwitness hclaim)

theorem ay_mwdr_public_sat_result_evidence
    {replayEvidence replayedWitness publicSatClaim : Prop} :
    AyMWDRPublicSatResult replayEvidence replayedWitness publicSatClaim ->
    replayEvidence :=
  fun h => ay_mwdr_conj_left h

theorem ay_mwdr_public_sat_result_witness
    {replayEvidence replayedWitness publicSatClaim : Prop} :
    AyMWDRPublicSatResult replayEvidence replayedWitness publicSatClaim ->
    replayedWitness :=
  fun h => ay_mwdr_conj_left (ay_mwdr_conj_right h)

theorem ay_mwdr_public_sat_result_claim
    {replayEvidence replayedWitness publicSatClaim : Prop} :
    AyMWDRPublicSatResult replayEvidence replayedWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_mwdr_conj_right (ay_mwdr_conj_right h)

theorem ay_mwdr_accepted_deltas_validate_same_public_sat
    {baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
      fingerprintOk basePublicSat replayedWitness publicSatClaim : Prop} :
    AyMWDRReplayEvidence
      baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
      fingerprintOk ->
    basePublicSat ->
    replayedWitness ->
    (basePublicSat -> publicSatClaim) ->
    AyMWDRPublicSatResult
      (AyMWDRReplayEvidence
        baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
        fingerprintOk)
      replayedWitness
      publicSatClaim :=
  fun hevidence hbase hwitness lift =>
    ay_mwdr_public_sat_result_intro hevidence hwitness (lift hbase)

theorem ay_mwdr_delta_replay_preserves_public_claim
    {baseWitness replayedWitness publicSatClaim : Prop} :
    AyMWDREquisat baseWitness replayedWitness ->
    baseWitness ->
    (replayedWitness -> publicSatClaim) ->
    publicSatClaim :=
  fun heq hbase publish => publish (ay_mwdr_equisat_forward heq hbase)

theorem ay_mwdr_publication_requires_base
    {baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
      fingerprintOk replayedWitness publicSatClaim : Prop} :
    AyMWDRPublicSatResult
      (AyMWDRReplayEvidence
        baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
        fingerprintOk)
      replayedWitness
      publicSatClaim ->
    baseOk :=
  fun h =>
    ay_mwdr_replay_evidence_base
      (ay_mwdr_public_sat_result_evidence h)

theorem ay_mwdr_publication_requires_delta
    {baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
      fingerprintOk replayedWitness publicSatClaim : Prop} :
    AyMWDRPublicSatResult
      (AyMWDRReplayEvidence
        baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
        fingerprintOk)
      replayedWitness
      publicSatClaim ->
    deltaOk :=
  fun h =>
    ay_mwdr_replay_evidence_delta
      (ay_mwdr_public_sat_result_evidence h)

theorem ay_mwdr_publication_requires_order
    {baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
      fingerprintOk replayedWitness publicSatClaim : Prop} :
    AyMWDRPublicSatResult
      (AyMWDRReplayEvidence
        baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
        fingerprintOk)
      replayedWitness
      publicSatClaim ->
    orderOk :=
  fun h =>
    ay_mwdr_replay_evidence_order
      (ay_mwdr_public_sat_result_evidence h)

theorem ay_mwdr_publication_requires_reconstruction
    {baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
      fingerprintOk replayedWitness publicSatClaim : Prop} :
    AyMWDRPublicSatResult
      (AyMWDRReplayEvidence
        baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
        fingerprintOk)
      replayedWitness
      publicSatClaim ->
    reconstructionOk :=
  fun h =>
    ay_mwdr_replay_evidence_reconstruction
      (ay_mwdr_public_sat_result_evidence h)

theorem ay_mwdr_publication_requires_digest
    {baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
      fingerprintOk replayedWitness publicSatClaim : Prop} :
    AyMWDRPublicSatResult
      (AyMWDRReplayEvidence
        baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
        fingerprintOk)
      replayedWitness
      publicSatClaim ->
    digestOk :=
  fun h =>
    ay_mwdr_replay_evidence_digest
      (ay_mwdr_public_sat_result_evidence h)

theorem ay_mwdr_publication_requires_replay
    {baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
      fingerprintOk replayedWitness publicSatClaim : Prop} :
    AyMWDRPublicSatResult
      (AyMWDRReplayEvidence
        baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
        fingerprintOk)
      replayedWitness
      publicSatClaim ->
    replayOk :=
  fun h =>
    ay_mwdr_replay_evidence_replay
      (ay_mwdr_public_sat_result_evidence h)

theorem ay_mwdr_publication_requires_build
    {baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
      fingerprintOk replayedWitness publicSatClaim : Prop} :
    AyMWDRPublicSatResult
      (AyMWDRReplayEvidence
        baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
        fingerprintOk)
      replayedWitness
      publicSatClaim ->
    buildOk :=
  fun h =>
    ay_mwdr_replay_evidence_build
      (ay_mwdr_public_sat_result_evidence h)

theorem ay_mwdr_publication_requires_fingerprint
    {baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
      fingerprintOk replayedWitness publicSatClaim : Prop} :
    AyMWDRPublicSatResult
      (AyMWDRReplayEvidence
        baseOk deltaOk orderOk reconstructionOk digestOk replayOk buildOk
        fingerprintOk)
      replayedWitness
      publicSatClaim ->
    fingerprintOk :=
  fun h =>
    ay_mwdr_replay_evidence_fingerprint
      (ay_mwdr_public_sat_result_evidence h)

theorem ay_mwdr_no_claim_diagnostic_intro
    {diagnostic publicSatClaim : Prop} :
    diagnostic ->
    (publicSatClaim -> False) ->
    AyMWDRNoClaimDiagnostic diagnostic publicSatClaim :=
  fun hdiagnostic hblocks =>
    ay_mwdr_conj_intro hdiagnostic hblocks

theorem ay_mwdr_no_claim_diagnostic_reason
    {diagnostic publicSatClaim : Prop} :
    AyMWDRNoClaimDiagnostic diagnostic publicSatClaim -> diagnostic :=
  fun h => ay_mwdr_conj_left h

theorem ay_mwdr_no_claim_diagnostic_blocks
    {diagnostic publicSatClaim : Prop} :
    AyMWDRNoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h => ay_mwdr_conj_right h

theorem ay_mwdr_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMWDRRecomputeObligation reason recomputeRequest :=
  fun hreason hrecompute => ay_mwdr_conj_intro hreason hrecompute

theorem ay_mwdr_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMWDRRecomputeObligation reason recomputeRequest -> reason :=
  fun h => ay_mwdr_conj_left h

theorem ay_mwdr_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMWDRRecomputeObligation reason recomputeRequest -> recomputeRequest :=
  fun h => ay_mwdr_conj_right h

theorem ay_mwdr_missing_base_recompute
    {missingBase recomputeRequest : Prop} :
    missingBase ->
    recomputeRequest ->
    AyMWDRRecomputeObligation missingBase recomputeRequest :=
  fun hmissing hrecompute =>
    ay_mwdr_recompute_obligation_intro hmissing hrecompute

theorem ay_mwdr_missing_base_no_claim
    {missingBase publicSatClaim : Prop} :
    missingBase ->
    (publicSatClaim -> False) ->
    AyMWDRNoClaimDiagnostic missingBase publicSatClaim :=
  fun hmissing hblocks =>
    ay_mwdr_no_claim_diagnostic_intro hmissing hblocks

theorem ay_mwdr_malformed_delta_no_claim
    {malformedDelta publicSatClaim : Prop} :
    malformedDelta ->
    (publicSatClaim -> False) ->
    AyMWDRNoClaimDiagnostic malformedDelta publicSatClaim :=
  fun hmalformed hblocks =>
    ay_mwdr_no_claim_diagnostic_intro hmalformed hblocks

theorem ay_mwdr_duplicate_assignment_no_claim
    {duplicateAssignment publicSatClaim : Prop} :
    duplicateAssignment ->
    (publicSatClaim -> False) ->
    AyMWDRNoClaimDiagnostic duplicateAssignment publicSatClaim :=
  fun hduplicate hblocks =>
    ay_mwdr_no_claim_diagnostic_intro hduplicate hblocks

theorem ay_mwdr_missing_variable_recompute
    {missingVariable recomputeRequest : Prop} :
    missingVariable ->
    recomputeRequest ->
    AyMWDRRecomputeObligation missingVariable recomputeRequest :=
  fun hmissing hrecompute =>
    ay_mwdr_recompute_obligation_intro hmissing hrecompute

theorem ay_mwdr_missing_variable_no_claim
    {missingVariable publicSatClaim : Prop} :
    missingVariable ->
    (publicSatClaim -> False) ->
    AyMWDRNoClaimDiagnostic missingVariable publicSatClaim :=
  fun hmissing hblocks =>
    ay_mwdr_no_claim_diagnostic_intro hmissing hblocks

theorem ay_mwdr_map_drift_no_claim
    {mapDrift publicSatClaim : Prop} :
    mapDrift ->
    (publicSatClaim -> False) ->
    AyMWDRNoClaimDiagnostic mapDrift publicSatClaim :=
  fun hdrift hblocks => ay_mwdr_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mwdr_order_drift_no_claim
    {orderDrift publicSatClaim : Prop} :
    orderDrift ->
    (publicSatClaim -> False) ->
    AyMWDRNoClaimDiagnostic orderDrift publicSatClaim :=
  fun hdrift hblocks => ay_mwdr_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mwdr_digest_mismatch_no_claim
    {digestMismatch publicSatClaim : Prop} :
    digestMismatch ->
    (publicSatClaim -> False) ->
    AyMWDRNoClaimDiagnostic digestMismatch publicSatClaim :=
  fun hmismatch hblocks =>
    ay_mwdr_no_claim_diagnostic_intro hmismatch hblocks

theorem ay_mwdr_checker_rejection_no_claim
    {checkerRejection publicSatClaim : Prop} :
    checkerRejection ->
    (publicSatClaim -> False) ->
    AyMWDRNoClaimDiagnostic checkerRejection publicSatClaim :=
  fun hreject hblocks =>
    ay_mwdr_no_claim_diagnostic_intro hreject hblocks

theorem ay_mwdr_build_drift_no_claim
    {buildDrift publicSatClaim : Prop} :
    buildDrift ->
    (publicSatClaim -> False) ->
    AyMWDRNoClaimDiagnostic buildDrift publicSatClaim :=
  fun hdrift hblocks => ay_mwdr_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mwdr_fingerprint_drift_no_claim
    {fingerprintDrift publicSatClaim : Prop} :
    fingerprintDrift ->
    (publicSatClaim -> False) ->
    AyMWDRNoClaimDiagnostic fingerprintDrift publicSatClaim :=
  fun hdrift hblocks => ay_mwdr_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mwdr_diagnostic_blocks_public_claim
    {diagnostic publicSatClaim : Prop} :
    AyMWDRNoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_mwdr_no_claim_diagnostic_blocks h hclaim

theorem ay_mwdr_bad_delta_replay_cannot_publish_sat
    {badDeltaReplay publicSatClaim : Prop} :
    AyMWDRNoClaimDiagnostic badDeltaReplay publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_mwdr_diagnostic_blocks_public_claim h hclaim
