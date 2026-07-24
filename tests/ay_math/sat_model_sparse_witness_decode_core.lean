-- SAT-COMP/ay sparse witness decoding soundness skeleton.
-- Sparse or compressed SAT witness artifacts decode to a public model only
-- when encoding, ordering, defaults, projection, digest, checker replay, build,
-- and original fingerprint evidence all agree.

def AyMSWDConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMSWDDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMSWDEquisat (left right : Prop) : Prop :=
  AyMSWDConj (left -> right) (right -> left)

def AyMSWDSparseEncoding
    (encodedWitness sparseIndex encodingWellformed : Prop) : Prop :=
  AyMSWDConj encodedWitness
    (AyMSWDConj sparseIndex encodingWellformed)

def AyMSWDVariableOrder
    (declaredOrder decodedOrder orderAgreement : Prop) : Prop :=
  AyMSWDConj declaredOrder (AyMSWDConj decodedOrder orderAgreement)

def AyMSWDDefaultReconstruction
    (defaultValues reconstructedValues defaultAgreement : Prop) : Prop :=
  AyMSWDConj defaultValues
    (AyMSWDConj reconstructedValues defaultAgreement)

def AyMSWDProjectionMap
    (solverProjection originalProjection projectionAgreement : Prop) : Prop :=
  AyMSWDConj solverProjection
    (AyMSWDConj originalProjection projectionAgreement)

def AyMSWDAssignmentDigest
    (sparseDigest decodedDigest digestAgreement : Prop) : Prop :=
  AyMSWDConj sparseDigest (AyMSWDConj decodedDigest digestAgreement)

def AyMSWDCheckerReplay (checkerAccepted replayTrace : Prop) : Prop :=
  AyMSWDConj checkerAccepted replayTrace

def AyMSWDSolverBuild
    (solverBuild witnessBuild buildAgreement : Prop) : Prop :=
  AyMSWDConj solverBuild (AyMSWDConj witnessBuild buildAgreement)

def AyMSWDOriginalFingerprint
    (originalFingerprint decodedFingerprint fingerprintAgreement : Prop) :
    Prop :=
  AyMSWDConj originalFingerprint
    (AyMSWDConj decodedFingerprint fingerprintAgreement)

def AyMSWDDecodeEvidence
    (encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
      fingerprintOk : Prop) : Prop :=
  AyMSWDConj encodingOk
    (AyMSWDConj orderOk
      (AyMSWDConj defaultsOk
        (AyMSWDConj projectionOk
          (AyMSWDConj digestOk
            (AyMSWDConj replayOk
              (AyMSWDConj buildOk fingerprintOk))))))

def AyMSWDPublicSatResult
    (decodeEvidence decodedWitness publicSatClaim : Prop) : Prop :=
  AyMSWDConj decodeEvidence
    (AyMSWDConj decodedWitness publicSatClaim)

def AyMSWDNoClaimDiagnostic (diagnostic publicSatClaim : Prop) : Prop :=
  AyMSWDConj diagnostic (publicSatClaim -> False)

def AyMSWDRecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMSWDConj reason recomputeRequest

theorem ay_mswd_conj_intro {left right : Prop} :
    left -> right -> AyMSWDConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_mswd_conj_left {left right : Prop} :
    AyMSWDConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_mswd_conj_right {left right : Prop} :
    AyMSWDConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_mswd_disj_left {left right : Prop} :
    left -> AyMSWDDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_mswd_disj_right {left right : Prop} :
    right -> AyMSWDDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_mswd_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMSWDEquisat left right :=
  fun hf hb => ay_mswd_conj_intro hf hb

theorem ay_mswd_equisat_forward {left right : Prop} :
    AyMSWDEquisat left right -> left -> right :=
  fun h => ay_mswd_conj_left h

theorem ay_mswd_equisat_backward {left right : Prop} :
    AyMSWDEquisat left right -> right -> left :=
  fun h => ay_mswd_conj_right h

theorem ay_mswd_sparse_encoding_intro
    {encodedWitness sparseIndex encodingWellformed : Prop} :
    encodedWitness ->
    sparseIndex ->
    encodingWellformed ->
    AyMSWDSparseEncoding
      encodedWitness sparseIndex encodingWellformed :=
  fun hencoded hindex hwellformed =>
    ay_mswd_conj_intro hencoded
      (ay_mswd_conj_intro hindex hwellformed)

theorem ay_mswd_sparse_encoding_witness
    {encodedWitness sparseIndex encodingWellformed : Prop} :
    AyMSWDSparseEncoding
      encodedWitness sparseIndex encodingWellformed ->
    encodedWitness :=
  fun h => ay_mswd_conj_left h

theorem ay_mswd_sparse_encoding_index
    {encodedWitness sparseIndex encodingWellformed : Prop} :
    AyMSWDSparseEncoding
      encodedWitness sparseIndex encodingWellformed ->
    sparseIndex :=
  fun h => ay_mswd_conj_left (ay_mswd_conj_right h)

theorem ay_mswd_sparse_encoding_wellformed
    {encodedWitness sparseIndex encodingWellformed : Prop} :
    AyMSWDSparseEncoding
      encodedWitness sparseIndex encodingWellformed ->
    encodingWellformed :=
  fun h => ay_mswd_conj_right (ay_mswd_conj_right h)

theorem ay_mswd_variable_order_intro
    {declaredOrder decodedOrder orderAgreement : Prop} :
    declaredOrder ->
    decodedOrder ->
    orderAgreement ->
    AyMSWDVariableOrder declaredOrder decodedOrder orderAgreement :=
  fun hdeclared hdecoded hagree =>
    ay_mswd_conj_intro hdeclared
      (ay_mswd_conj_intro hdecoded hagree)

theorem ay_mswd_variable_order_declared
    {declaredOrder decodedOrder orderAgreement : Prop} :
    AyMSWDVariableOrder declaredOrder decodedOrder orderAgreement ->
    declaredOrder :=
  fun h => ay_mswd_conj_left h

theorem ay_mswd_variable_order_decoded
    {declaredOrder decodedOrder orderAgreement : Prop} :
    AyMSWDVariableOrder declaredOrder decodedOrder orderAgreement ->
    decodedOrder :=
  fun h => ay_mswd_conj_left (ay_mswd_conj_right h)

theorem ay_mswd_variable_order_agreement
    {declaredOrder decodedOrder orderAgreement : Prop} :
    AyMSWDVariableOrder declaredOrder decodedOrder orderAgreement ->
    orderAgreement :=
  fun h => ay_mswd_conj_right (ay_mswd_conj_right h)

theorem ay_mswd_default_reconstruction_intro
    {defaultValues reconstructedValues defaultAgreement : Prop} :
    defaultValues ->
    reconstructedValues ->
    defaultAgreement ->
    AyMSWDDefaultReconstruction
      defaultValues reconstructedValues defaultAgreement :=
  fun hdefaults hvalues hagree =>
    ay_mswd_conj_intro hdefaults
      (ay_mswd_conj_intro hvalues hagree)

theorem ay_mswd_default_reconstruction_defaults
    {defaultValues reconstructedValues defaultAgreement : Prop} :
    AyMSWDDefaultReconstruction
      defaultValues reconstructedValues defaultAgreement ->
    defaultValues :=
  fun h => ay_mswd_conj_left h

theorem ay_mswd_default_reconstruction_values
    {defaultValues reconstructedValues defaultAgreement : Prop} :
    AyMSWDDefaultReconstruction
      defaultValues reconstructedValues defaultAgreement ->
    reconstructedValues :=
  fun h => ay_mswd_conj_left (ay_mswd_conj_right h)

theorem ay_mswd_default_reconstruction_agreement
    {defaultValues reconstructedValues defaultAgreement : Prop} :
    AyMSWDDefaultReconstruction
      defaultValues reconstructedValues defaultAgreement ->
    defaultAgreement :=
  fun h => ay_mswd_conj_right (ay_mswd_conj_right h)

theorem ay_mswd_projection_map_intro
    {solverProjection originalProjection projectionAgreement : Prop} :
    solverProjection ->
    originalProjection ->
    projectionAgreement ->
    AyMSWDProjectionMap
      solverProjection originalProjection projectionAgreement :=
  fun hsolver horiginal hagree =>
    ay_mswd_conj_intro hsolver
      (ay_mswd_conj_intro horiginal hagree)

theorem ay_mswd_projection_map_solver
    {solverProjection originalProjection projectionAgreement : Prop} :
    AyMSWDProjectionMap
      solverProjection originalProjection projectionAgreement ->
    solverProjection :=
  fun h => ay_mswd_conj_left h

theorem ay_mswd_projection_map_original
    {solverProjection originalProjection projectionAgreement : Prop} :
    AyMSWDProjectionMap
      solverProjection originalProjection projectionAgreement ->
    originalProjection :=
  fun h => ay_mswd_conj_left (ay_mswd_conj_right h)

theorem ay_mswd_projection_map_agreement
    {solverProjection originalProjection projectionAgreement : Prop} :
    AyMSWDProjectionMap
      solverProjection originalProjection projectionAgreement ->
    projectionAgreement :=
  fun h => ay_mswd_conj_right (ay_mswd_conj_right h)

theorem ay_mswd_assignment_digest_intro
    {sparseDigest decodedDigest digestAgreement : Prop} :
    sparseDigest ->
    decodedDigest ->
    digestAgreement ->
    AyMSWDAssignmentDigest sparseDigest decodedDigest digestAgreement :=
  fun hsparse hdecoded hagree =>
    ay_mswd_conj_intro hsparse
      (ay_mswd_conj_intro hdecoded hagree)

theorem ay_mswd_assignment_digest_sparse
    {sparseDigest decodedDigest digestAgreement : Prop} :
    AyMSWDAssignmentDigest sparseDigest decodedDigest digestAgreement ->
    sparseDigest :=
  fun h => ay_mswd_conj_left h

theorem ay_mswd_assignment_digest_decoded
    {sparseDigest decodedDigest digestAgreement : Prop} :
    AyMSWDAssignmentDigest sparseDigest decodedDigest digestAgreement ->
    decodedDigest :=
  fun h => ay_mswd_conj_left (ay_mswd_conj_right h)

theorem ay_mswd_assignment_digest_agreement
    {sparseDigest decodedDigest digestAgreement : Prop} :
    AyMSWDAssignmentDigest sparseDigest decodedDigest digestAgreement ->
    digestAgreement :=
  fun h => ay_mswd_conj_right (ay_mswd_conj_right h)

theorem ay_mswd_checker_replay_intro
    {checkerAccepted replayTrace : Prop} :
    checkerAccepted ->
    replayTrace ->
    AyMSWDCheckerReplay checkerAccepted replayTrace :=
  fun haccepted htrace => ay_mswd_conj_intro haccepted htrace

theorem ay_mswd_checker_replay_accepted
    {checkerAccepted replayTrace : Prop} :
    AyMSWDCheckerReplay checkerAccepted replayTrace -> checkerAccepted :=
  fun h => ay_mswd_conj_left h

theorem ay_mswd_checker_replay_trace
    {checkerAccepted replayTrace : Prop} :
    AyMSWDCheckerReplay checkerAccepted replayTrace -> replayTrace :=
  fun h => ay_mswd_conj_right h

theorem ay_mswd_solver_build_intro
    {solverBuild witnessBuild buildAgreement : Prop} :
    solverBuild ->
    witnessBuild ->
    buildAgreement ->
    AyMSWDSolverBuild solverBuild witnessBuild buildAgreement :=
  fun hsolver hwitness hagree =>
    ay_mswd_conj_intro hsolver
      (ay_mswd_conj_intro hwitness hagree)

theorem ay_mswd_solver_build_solver
    {solverBuild witnessBuild buildAgreement : Prop} :
    AyMSWDSolverBuild solverBuild witnessBuild buildAgreement -> solverBuild :=
  fun h => ay_mswd_conj_left h

theorem ay_mswd_solver_build_witness
    {solverBuild witnessBuild buildAgreement : Prop} :
    AyMSWDSolverBuild solverBuild witnessBuild buildAgreement ->
    witnessBuild :=
  fun h => ay_mswd_conj_left (ay_mswd_conj_right h)

theorem ay_mswd_solver_build_agreement
    {solverBuild witnessBuild buildAgreement : Prop} :
    AyMSWDSolverBuild solverBuild witnessBuild buildAgreement ->
    buildAgreement :=
  fun h => ay_mswd_conj_right (ay_mswd_conj_right h)

theorem ay_mswd_original_fingerprint_intro
    {originalFingerprint decodedFingerprint fingerprintAgreement : Prop} :
    originalFingerprint ->
    decodedFingerprint ->
    fingerprintAgreement ->
    AyMSWDOriginalFingerprint
      originalFingerprint decodedFingerprint fingerprintAgreement :=
  fun horiginal hdecoded hagree =>
    ay_mswd_conj_intro horiginal
      (ay_mswd_conj_intro hdecoded hagree)

theorem ay_mswd_original_fingerprint_original
    {originalFingerprint decodedFingerprint fingerprintAgreement : Prop} :
    AyMSWDOriginalFingerprint
      originalFingerprint decodedFingerprint fingerprintAgreement ->
    originalFingerprint :=
  fun h => ay_mswd_conj_left h

theorem ay_mswd_original_fingerprint_decoded
    {originalFingerprint decodedFingerprint fingerprintAgreement : Prop} :
    AyMSWDOriginalFingerprint
      originalFingerprint decodedFingerprint fingerprintAgreement ->
    decodedFingerprint :=
  fun h => ay_mswd_conj_left (ay_mswd_conj_right h)

theorem ay_mswd_original_fingerprint_agreement
    {originalFingerprint decodedFingerprint fingerprintAgreement : Prop} :
    AyMSWDOriginalFingerprint
      originalFingerprint decodedFingerprint fingerprintAgreement ->
    fingerprintAgreement :=
  fun h => ay_mswd_conj_right (ay_mswd_conj_right h)

theorem ay_mswd_decode_evidence_intro
    {encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    encodingOk ->
    orderOk ->
    defaultsOk ->
    projectionOk ->
    digestOk ->
    replayOk ->
    buildOk ->
    fingerprintOk ->
    AyMSWDDecodeEvidence
      encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
      fingerprintOk :=
  fun hencoding horder hdefaults hprojection hdigest hreplay hbuild
      hfingerprint =>
    ay_mswd_conj_intro hencoding
      (ay_mswd_conj_intro horder
        (ay_mswd_conj_intro hdefaults
          (ay_mswd_conj_intro hprojection
            (ay_mswd_conj_intro hdigest
              (ay_mswd_conj_intro hreplay
                (ay_mswd_conj_intro hbuild hfingerprint))))))

theorem ay_mswd_decode_evidence_encoding
    {encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMSWDDecodeEvidence
      encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
      fingerprintOk ->
    encodingOk :=
  fun h => ay_mswd_conj_left h

theorem ay_mswd_decode_evidence_order
    {encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMSWDDecodeEvidence
      encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
      fingerprintOk ->
    orderOk :=
  fun h => ay_mswd_conj_left (ay_mswd_conj_right h)

theorem ay_mswd_decode_evidence_defaults
    {encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMSWDDecodeEvidence
      encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
      fingerprintOk ->
    defaultsOk :=
  fun h => ay_mswd_conj_left
    (ay_mswd_conj_right (ay_mswd_conj_right h))

theorem ay_mswd_decode_evidence_projection
    {encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMSWDDecodeEvidence
      encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
      fingerprintOk ->
    projectionOk :=
  fun h => ay_mswd_conj_left
    (ay_mswd_conj_right
      (ay_mswd_conj_right (ay_mswd_conj_right h)))

theorem ay_mswd_decode_evidence_digest
    {encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMSWDDecodeEvidence
      encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
      fingerprintOk ->
    digestOk :=
  fun h => ay_mswd_conj_left
    (ay_mswd_conj_right
      (ay_mswd_conj_right
        (ay_mswd_conj_right (ay_mswd_conj_right h))))

theorem ay_mswd_decode_evidence_replay
    {encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMSWDDecodeEvidence
      encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
      fingerprintOk ->
    replayOk :=
  fun h => ay_mswd_conj_left
    (ay_mswd_conj_right
      (ay_mswd_conj_right
        (ay_mswd_conj_right
          (ay_mswd_conj_right (ay_mswd_conj_right h)))))

theorem ay_mswd_decode_evidence_build
    {encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMSWDDecodeEvidence
      encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
      fingerprintOk ->
    buildOk :=
  fun h => ay_mswd_conj_left
    (ay_mswd_conj_right
      (ay_mswd_conj_right
        (ay_mswd_conj_right
          (ay_mswd_conj_right
            (ay_mswd_conj_right (ay_mswd_conj_right h))))))

theorem ay_mswd_decode_evidence_fingerprint
    {encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMSWDDecodeEvidence
      encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
      fingerprintOk ->
    fingerprintOk :=
  fun h => ay_mswd_conj_right
    (ay_mswd_conj_right
      (ay_mswd_conj_right
        (ay_mswd_conj_right
          (ay_mswd_conj_right
            (ay_mswd_conj_right (ay_mswd_conj_right h))))))

theorem ay_mswd_public_sat_result_intro
    {decodeEvidence decodedWitness publicSatClaim : Prop} :
    decodeEvidence ->
    decodedWitness ->
    publicSatClaim ->
    AyMSWDPublicSatResult decodeEvidence decodedWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_mswd_conj_intro hevidence
      (ay_mswd_conj_intro hwitness hclaim)

theorem ay_mswd_public_sat_result_evidence
    {decodeEvidence decodedWitness publicSatClaim : Prop} :
    AyMSWDPublicSatResult decodeEvidence decodedWitness publicSatClaim ->
    decodeEvidence :=
  fun h => ay_mswd_conj_left h

theorem ay_mswd_public_sat_result_witness
    {decodeEvidence decodedWitness publicSatClaim : Prop} :
    AyMSWDPublicSatResult decodeEvidence decodedWitness publicSatClaim ->
    decodedWitness :=
  fun h => ay_mswd_conj_left (ay_mswd_conj_right h)

theorem ay_mswd_public_sat_result_claim
    {decodeEvidence decodedWitness publicSatClaim : Prop} :
    AyMSWDPublicSatResult decodeEvidence decodedWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_mswd_conj_right (ay_mswd_conj_right h)

theorem ay_mswd_accepted_decode_validates_same_public_sat
    {encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
      fingerprintOk sparseSat decodedWitness publicSatClaim : Prop} :
    AyMSWDDecodeEvidence
      encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
      fingerprintOk ->
    sparseSat ->
    decodedWitness ->
    (sparseSat -> publicSatClaim) ->
    AyMSWDPublicSatResult
      (AyMSWDDecodeEvidence
        encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
        fingerprintOk)
      decodedWitness
      publicSatClaim :=
  fun hevidence hsparse hwitness lift =>
    ay_mswd_public_sat_result_intro hevidence hwitness (lift hsparse)

theorem ay_mswd_decode_equisat_preserves_public_claim
    {sparseWitness decodedWitness publicSatClaim : Prop} :
    AyMSWDEquisat sparseWitness decodedWitness ->
    sparseWitness ->
    (decodedWitness -> publicSatClaim) ->
    publicSatClaim :=
  fun heq hsparse publish => publish (ay_mswd_equisat_forward heq hsparse)

theorem ay_mswd_publication_requires_encoding
    {encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
      fingerprintOk decodedWitness publicSatClaim : Prop} :
    AyMSWDPublicSatResult
      (AyMSWDDecodeEvidence
        encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
        fingerprintOk)
      decodedWitness
      publicSatClaim ->
    encodingOk :=
  fun h =>
    ay_mswd_decode_evidence_encoding
      (ay_mswd_public_sat_result_evidence h)

theorem ay_mswd_publication_requires_order
    {encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
      fingerprintOk decodedWitness publicSatClaim : Prop} :
    AyMSWDPublicSatResult
      (AyMSWDDecodeEvidence
        encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
        fingerprintOk)
      decodedWitness
      publicSatClaim ->
    orderOk :=
  fun h =>
    ay_mswd_decode_evidence_order
      (ay_mswd_public_sat_result_evidence h)

theorem ay_mswd_publication_requires_defaults
    {encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
      fingerprintOk decodedWitness publicSatClaim : Prop} :
    AyMSWDPublicSatResult
      (AyMSWDDecodeEvidence
        encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
        fingerprintOk)
      decodedWitness
      publicSatClaim ->
    defaultsOk :=
  fun h =>
    ay_mswd_decode_evidence_defaults
      (ay_mswd_public_sat_result_evidence h)

theorem ay_mswd_publication_requires_projection
    {encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
      fingerprintOk decodedWitness publicSatClaim : Prop} :
    AyMSWDPublicSatResult
      (AyMSWDDecodeEvidence
        encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
        fingerprintOk)
      decodedWitness
      publicSatClaim ->
    projectionOk :=
  fun h =>
    ay_mswd_decode_evidence_projection
      (ay_mswd_public_sat_result_evidence h)

theorem ay_mswd_publication_requires_digest
    {encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
      fingerprintOk decodedWitness publicSatClaim : Prop} :
    AyMSWDPublicSatResult
      (AyMSWDDecodeEvidence
        encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
        fingerprintOk)
      decodedWitness
      publicSatClaim ->
    digestOk :=
  fun h =>
    ay_mswd_decode_evidence_digest
      (ay_mswd_public_sat_result_evidence h)

theorem ay_mswd_publication_requires_replay
    {encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
      fingerprintOk decodedWitness publicSatClaim : Prop} :
    AyMSWDPublicSatResult
      (AyMSWDDecodeEvidence
        encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
        fingerprintOk)
      decodedWitness
      publicSatClaim ->
    replayOk :=
  fun h =>
    ay_mswd_decode_evidence_replay
      (ay_mswd_public_sat_result_evidence h)

theorem ay_mswd_publication_requires_build
    {encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
      fingerprintOk decodedWitness publicSatClaim : Prop} :
    AyMSWDPublicSatResult
      (AyMSWDDecodeEvidence
        encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
        fingerprintOk)
      decodedWitness
      publicSatClaim ->
    buildOk :=
  fun h =>
    ay_mswd_decode_evidence_build
      (ay_mswd_public_sat_result_evidence h)

theorem ay_mswd_publication_requires_fingerprint
    {encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
      fingerprintOk decodedWitness publicSatClaim : Prop} :
    AyMSWDPublicSatResult
      (AyMSWDDecodeEvidence
        encodingOk orderOk defaultsOk projectionOk digestOk replayOk buildOk
        fingerprintOk)
      decodedWitness
      publicSatClaim ->
    fingerprintOk :=
  fun h =>
    ay_mswd_decode_evidence_fingerprint
      (ay_mswd_public_sat_result_evidence h)

theorem ay_mswd_no_claim_diagnostic_intro
    {diagnostic publicSatClaim : Prop} :
    diagnostic ->
    (publicSatClaim -> False) ->
    AyMSWDNoClaimDiagnostic diagnostic publicSatClaim :=
  fun hdiagnostic hblocks =>
    ay_mswd_conj_intro hdiagnostic hblocks

theorem ay_mswd_no_claim_diagnostic_reason
    {diagnostic publicSatClaim : Prop} :
    AyMSWDNoClaimDiagnostic diagnostic publicSatClaim -> diagnostic :=
  fun h => ay_mswd_conj_left h

theorem ay_mswd_no_claim_diagnostic_blocks
    {diagnostic publicSatClaim : Prop} :
    AyMSWDNoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h => ay_mswd_conj_right h

theorem ay_mswd_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMSWDRecomputeObligation reason recomputeRequest :=
  fun hreason hrecompute => ay_mswd_conj_intro hreason hrecompute

theorem ay_mswd_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMSWDRecomputeObligation reason recomputeRequest -> reason :=
  fun h => ay_mswd_conj_left h

theorem ay_mswd_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMSWDRecomputeObligation reason recomputeRequest -> recomputeRequest :=
  fun h => ay_mswd_conj_right h

theorem ay_mswd_malformed_sparse_encoding_no_claim
    {malformedSparseEncoding publicSatClaim : Prop} :
    malformedSparseEncoding ->
    (publicSatClaim -> False) ->
    AyMSWDNoClaimDiagnostic malformedSparseEncoding publicSatClaim :=
  fun hmalformed hblocks =>
    ay_mswd_no_claim_diagnostic_intro hmalformed hblocks

theorem ay_mswd_missing_variable_recompute
    {missingVariable recomputeRequest : Prop} :
    missingVariable ->
    recomputeRequest ->
    AyMSWDRecomputeObligation missingVariable recomputeRequest :=
  fun hmissing hrecompute =>
    ay_mswd_recompute_obligation_intro hmissing hrecompute

theorem ay_mswd_missing_variable_no_claim
    {missingVariable publicSatClaim : Prop} :
    missingVariable ->
    (publicSatClaim -> False) ->
    AyMSWDNoClaimDiagnostic missingVariable publicSatClaim :=
  fun hmissing hblocks =>
    ay_mswd_no_claim_diagnostic_intro hmissing hblocks

theorem ay_mswd_default_conflict_no_claim
    {defaultConflict publicSatClaim : Prop} :
    defaultConflict ->
    (publicSatClaim -> False) ->
    AyMSWDNoClaimDiagnostic defaultConflict publicSatClaim :=
  fun hconflict hblocks =>
    ay_mswd_no_claim_diagnostic_intro hconflict hblocks

theorem ay_mswd_order_drift_no_claim
    {orderDrift publicSatClaim : Prop} :
    orderDrift ->
    (publicSatClaim -> False) ->
    AyMSWDNoClaimDiagnostic orderDrift publicSatClaim :=
  fun hdrift hblocks => ay_mswd_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mswd_map_drift_no_claim
    {mapDrift publicSatClaim : Prop} :
    mapDrift ->
    (publicSatClaim -> False) ->
    AyMSWDNoClaimDiagnostic mapDrift publicSatClaim :=
  fun hdrift hblocks => ay_mswd_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mswd_digest_mismatch_no_claim
    {digestMismatch publicSatClaim : Prop} :
    digestMismatch ->
    (publicSatClaim -> False) ->
    AyMSWDNoClaimDiagnostic digestMismatch publicSatClaim :=
  fun hmismatch hblocks =>
    ay_mswd_no_claim_diagnostic_intro hmismatch hblocks

theorem ay_mswd_checker_rejection_no_claim
    {checkerRejection publicSatClaim : Prop} :
    checkerRejection ->
    (publicSatClaim -> False) ->
    AyMSWDNoClaimDiagnostic checkerRejection publicSatClaim :=
  fun hreject hblocks =>
    ay_mswd_no_claim_diagnostic_intro hreject hblocks

theorem ay_mswd_build_drift_no_claim
    {buildDrift publicSatClaim : Prop} :
    buildDrift ->
    (publicSatClaim -> False) ->
    AyMSWDNoClaimDiagnostic buildDrift publicSatClaim :=
  fun hdrift hblocks => ay_mswd_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mswd_fingerprint_drift_no_claim
    {fingerprintDrift publicSatClaim : Prop} :
    fingerprintDrift ->
    (publicSatClaim -> False) ->
    AyMSWDNoClaimDiagnostic fingerprintDrift publicSatClaim :=
  fun hdrift hblocks => ay_mswd_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mswd_diagnostic_blocks_public_claim
    {diagnostic publicSatClaim : Prop} :
    AyMSWDNoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_mswd_no_claim_diagnostic_blocks h hclaim

theorem ay_mswd_bad_decode_cannot_publish_sat
    {badDecode publicSatClaim : Prop} :
    AyMSWDNoClaimDiagnostic badDecode publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_mswd_diagnostic_blocks_public_claim h hclaim
