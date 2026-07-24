/- SAT-COMP/ay DIMACS variable-order manifest contract.

This self-contained package models variable-order normalization evidence for
sequential-main SAT witnesses.  Public SAT output is permitted only when the
DIMACS order manifest, bidirectional maps, replay, checker, fingerprint, and
build evidence all agree.
-/

def AyMDVOConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMDVODisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMDVOEquisat (source target : Prop) : Prop :=
  AyMDVOConj (source -> target) (target -> source)

def AyMDVOVariableOrderManifest
    (solverOrder dimacsOrder normalizedOrder : Prop) : Prop :=
  AyMDVOConj solverOrder (AyMDVOConj dimacsOrder normalizedOrder)

def AyMDVOBidirectionalMaps
    (solverToDimacs dimacsToSolver inverseAgreement : Prop) : Prop :=
  AyMDVOConj solverToDimacs (AyMDVOConj dimacsToSolver inverseAgreement)

def AyMDVODigestEvidence
    (solverDigest dimacsDigest digestAgreement : Prop) : Prop :=
  AyMDVOConj solverDigest (AyMDVOConj dimacsDigest digestAgreement)

def AyMDVOClauseReplay
    (clauseReplay normalizedEvaluation replayAgreement : Prop) : Prop :=
  AyMDVOConj clauseReplay
    (AyMDVOConj normalizedEvaluation replayAgreement)

def AyMDVOCheckerTranscript
    (checkerAccepted transcript transcriptAgreement : Prop) : Prop :=
  AyMDVOConj checkerAccepted (AyMDVOConj transcript transcriptAgreement)

def AyMDVOFormulaFingerprint
    (originalFingerprint orderFingerprint fingerprintAgreement : Prop) : Prop :=
  AyMDVOConj originalFingerprint
    (AyMDVOConj orderFingerprint fingerprintAgreement)

def AyMDVOBuildEvidence
    (solverBuild manifestBuild buildAgreement : Prop) : Prop :=
  AyMDVOConj solverBuild (AyMDVOConj manifestBuild buildAgreement)

def AyMDVOAcceptedManifest
    (orderOk mapsOk digestOk clauseReplayOk checkerOk fingerprintOk
      buildOk : Prop) : Prop :=
  AyMDVOConj orderOk
    (AyMDVOConj mapsOk
      (AyMDVOConj digestOk
        (AyMDVOConj clauseReplayOk
          (AyMDVOConj checkerOk
            (AyMDVOConj fingerprintOk buildOk)))))

def AyMDVOPublicSatWitness
    (acceptedManifest publicWitness publicSatClaim : Prop) : Prop :=
  AyMDVOConj acceptedManifest (AyMDVOConj publicWitness publicSatClaim)

def AyMDVONoClaimDiagnostic (reason blocksPublication : Prop) : Prop :=
  AyMDVOConj reason blocksPublication

def AyMDVORecomputeObligation (reason recomputeRequested : Prop) : Prop :=
  AyMDVOConj reason recomputeRequested

theorem ay_mdvo_conj_intro {left right : Prop} :
    left -> right -> AyMDVOConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_mdvo_conj_left {left right : Prop} :
    AyMDVOConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_mdvo_conj_right {left right : Prop} :
    AyMDVOConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_mdvo_disj_left {left right : Prop} :
    left -> AyMDVODisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_mdvo_disj_right {left right : Prop} :
    right -> AyMDVODisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_mdvo_equisat_intro {source target : Prop} :
    (source -> target) -> (target -> source) -> AyMDVOEquisat source target :=
  fun forward backward => ay_mdvo_conj_intro forward backward

theorem ay_mdvo_equisat_forward {source target : Prop} :
    AyMDVOEquisat source target -> source -> target :=
  fun h => ay_mdvo_conj_left h

theorem ay_mdvo_equisat_backward {source target : Prop} :
    AyMDVOEquisat source target -> target -> source :=
  fun h => ay_mdvo_conj_right h

theorem ay_mdvo_variable_order_manifest_intro
    {solverOrder dimacsOrder normalizedOrder : Prop} :
    solverOrder -> dimacsOrder -> normalizedOrder ->
    AyMDVOVariableOrderManifest solverOrder dimacsOrder normalizedOrder :=
  fun hsolver hdimacs hnormalized =>
    ay_mdvo_conj_intro hsolver (ay_mdvo_conj_intro hdimacs hnormalized)

theorem ay_mdvo_variable_order_manifest_solver
    {solverOrder dimacsOrder normalizedOrder : Prop} :
    AyMDVOVariableOrderManifest solverOrder dimacsOrder normalizedOrder ->
    solverOrder :=
  fun h => ay_mdvo_conj_left h

theorem ay_mdvo_variable_order_manifest_dimacs
    {solverOrder dimacsOrder normalizedOrder : Prop} :
    AyMDVOVariableOrderManifest solverOrder dimacsOrder normalizedOrder ->
    dimacsOrder :=
  fun h => ay_mdvo_conj_left (ay_mdvo_conj_right h)

theorem ay_mdvo_variable_order_manifest_normalized
    {solverOrder dimacsOrder normalizedOrder : Prop} :
    AyMDVOVariableOrderManifest solverOrder dimacsOrder normalizedOrder ->
    normalizedOrder :=
  fun h => ay_mdvo_conj_right (ay_mdvo_conj_right h)

theorem ay_mdvo_bidirectional_maps_intro
    {solverToDimacs dimacsToSolver inverseAgreement : Prop} :
    solverToDimacs -> dimacsToSolver -> inverseAgreement ->
    AyMDVOBidirectionalMaps solverToDimacs dimacsToSolver inverseAgreement :=
  fun hforward hbackward hagree =>
    ay_mdvo_conj_intro hforward (ay_mdvo_conj_intro hbackward hagree)

theorem ay_mdvo_bidirectional_maps_forward
    {solverToDimacs dimacsToSolver inverseAgreement : Prop} :
    AyMDVOBidirectionalMaps solverToDimacs dimacsToSolver inverseAgreement ->
    solverToDimacs :=
  fun h => ay_mdvo_conj_left h

theorem ay_mdvo_bidirectional_maps_backward
    {solverToDimacs dimacsToSolver inverseAgreement : Prop} :
    AyMDVOBidirectionalMaps solverToDimacs dimacsToSolver inverseAgreement ->
    dimacsToSolver :=
  fun h => ay_mdvo_conj_left (ay_mdvo_conj_right h)

theorem ay_mdvo_bidirectional_maps_agreement
    {solverToDimacs dimacsToSolver inverseAgreement : Prop} :
    AyMDVOBidirectionalMaps solverToDimacs dimacsToSolver inverseAgreement ->
    inverseAgreement :=
  fun h => ay_mdvo_conj_right (ay_mdvo_conj_right h)

theorem ay_mdvo_digest_evidence_intro
    {solverDigest dimacsDigest digestAgreement : Prop} :
    solverDigest -> dimacsDigest -> digestAgreement ->
    AyMDVODigestEvidence solverDigest dimacsDigest digestAgreement :=
  fun hsolver hdimacs hagree =>
    ay_mdvo_conj_intro hsolver (ay_mdvo_conj_intro hdimacs hagree)

theorem ay_mdvo_clause_replay_intro
    {clauseReplay normalizedEvaluation replayAgreement : Prop} :
    clauseReplay -> normalizedEvaluation -> replayAgreement ->
    AyMDVOClauseReplay clauseReplay normalizedEvaluation replayAgreement :=
  fun hreplay heval hagree =>
    ay_mdvo_conj_intro hreplay (ay_mdvo_conj_intro heval hagree)

theorem ay_mdvo_checker_transcript_intro
    {checkerAccepted transcript transcriptAgreement : Prop} :
    checkerAccepted -> transcript -> transcriptAgreement ->
    AyMDVOCheckerTranscript checkerAccepted transcript transcriptAgreement :=
  fun haccepted htranscript hagree =>
    ay_mdvo_conj_intro haccepted (ay_mdvo_conj_intro htranscript hagree)

theorem ay_mdvo_formula_fingerprint_intro
    {originalFingerprint orderFingerprint fingerprintAgreement : Prop} :
    originalFingerprint -> orderFingerprint -> fingerprintAgreement ->
    AyMDVOFormulaFingerprint
      originalFingerprint orderFingerprint fingerprintAgreement :=
  fun horiginal horder hagree =>
    ay_mdvo_conj_intro horiginal (ay_mdvo_conj_intro horder hagree)

theorem ay_mdvo_build_evidence_intro
    {solverBuild manifestBuild buildAgreement : Prop} :
    solverBuild -> manifestBuild -> buildAgreement ->
    AyMDVOBuildEvidence solverBuild manifestBuild buildAgreement :=
  fun hsolver hmanifest hagree =>
    ay_mdvo_conj_intro hsolver (ay_mdvo_conj_intro hmanifest hagree)

theorem ay_mdvo_accepted_manifest_intro
    {orderOk mapsOk digestOk clauseReplayOk checkerOk fingerprintOk
      buildOk : Prop} :
    orderOk -> mapsOk -> digestOk -> clauseReplayOk -> checkerOk ->
    fingerprintOk -> buildOk ->
    AyMDVOAcceptedManifest orderOk mapsOk digestOk clauseReplayOk
      checkerOk fingerprintOk buildOk :=
  fun horder hmaps hdigest hclause hchecker hfingerprint hbuild =>
    ay_mdvo_conj_intro horder
      (ay_mdvo_conj_intro hmaps
        (ay_mdvo_conj_intro hdigest
          (ay_mdvo_conj_intro hclause
            (ay_mdvo_conj_intro hchecker
              (ay_mdvo_conj_intro hfingerprint hbuild)))))

theorem ay_mdvo_accepted_manifest_order
    {orderOk mapsOk digestOk clauseReplayOk checkerOk fingerprintOk
      buildOk : Prop} :
    AyMDVOAcceptedManifest orderOk mapsOk digestOk clauseReplayOk
      checkerOk fingerprintOk buildOk ->
    orderOk :=
  fun h => ay_mdvo_conj_left h

theorem ay_mdvo_accepted_manifest_maps
    {orderOk mapsOk digestOk clauseReplayOk checkerOk fingerprintOk
      buildOk : Prop} :
    AyMDVOAcceptedManifest orderOk mapsOk digestOk clauseReplayOk
      checkerOk fingerprintOk buildOk ->
    mapsOk :=
  fun h => ay_mdvo_conj_left (ay_mdvo_conj_right h)

theorem ay_mdvo_accepted_manifest_digest
    {orderOk mapsOk digestOk clauseReplayOk checkerOk fingerprintOk
      buildOk : Prop} :
    AyMDVOAcceptedManifest orderOk mapsOk digestOk clauseReplayOk
      checkerOk fingerprintOk buildOk ->
    digestOk :=
  fun h => ay_mdvo_conj_left (ay_mdvo_conj_right (ay_mdvo_conj_right h))

theorem ay_mdvo_accepted_manifest_clause_replay
    {orderOk mapsOk digestOk clauseReplayOk checkerOk fingerprintOk
      buildOk : Prop} :
    AyMDVOAcceptedManifest orderOk mapsOk digestOk clauseReplayOk
      checkerOk fingerprintOk buildOk ->
    clauseReplayOk :=
  fun h =>
    ay_mdvo_conj_left
      (ay_mdvo_conj_right (ay_mdvo_conj_right (ay_mdvo_conj_right h)))

theorem ay_mdvo_accepted_manifest_checker
    {orderOk mapsOk digestOk clauseReplayOk checkerOk fingerprintOk
      buildOk : Prop} :
    AyMDVOAcceptedManifest orderOk mapsOk digestOk clauseReplayOk
      checkerOk fingerprintOk buildOk ->
    checkerOk :=
  fun h =>
    ay_mdvo_conj_left
      (ay_mdvo_conj_right
        (ay_mdvo_conj_right (ay_mdvo_conj_right (ay_mdvo_conj_right h))))

theorem ay_mdvo_accepted_manifest_fingerprint
    {orderOk mapsOk digestOk clauseReplayOk checkerOk fingerprintOk
      buildOk : Prop} :
    AyMDVOAcceptedManifest orderOk mapsOk digestOk clauseReplayOk
      checkerOk fingerprintOk buildOk ->
    fingerprintOk :=
  fun h =>
    ay_mdvo_conj_left
      (ay_mdvo_conj_right
        (ay_mdvo_conj_right
          (ay_mdvo_conj_right (ay_mdvo_conj_right (ay_mdvo_conj_right h)))))

theorem ay_mdvo_accepted_manifest_build
    {orderOk mapsOk digestOk clauseReplayOk checkerOk fingerprintOk
      buildOk : Prop} :
    AyMDVOAcceptedManifest orderOk mapsOk digestOk clauseReplayOk
      checkerOk fingerprintOk buildOk ->
    buildOk :=
  fun h =>
    ay_mdvo_conj_right
      (ay_mdvo_conj_right
        (ay_mdvo_conj_right
          (ay_mdvo_conj_right (ay_mdvo_conj_right (ay_mdvo_conj_right h)))))

theorem ay_mdvo_public_sat_witness_intro
    {acceptedManifest publicWitness publicSatClaim : Prop} :
    acceptedManifest -> publicWitness -> publicSatClaim ->
    AyMDVOPublicSatWitness acceptedManifest publicWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_mdvo_conj_intro hevidence (ay_mdvo_conj_intro hwitness hclaim)

theorem ay_mdvo_public_sat_witness_evidence
    {acceptedManifest publicWitness publicSatClaim : Prop} :
    AyMDVOPublicSatWitness acceptedManifest publicWitness publicSatClaim ->
    acceptedManifest :=
  fun h => ay_mdvo_conj_left h

theorem ay_mdvo_public_sat_witness_claim
    {acceptedManifest publicWitness publicSatClaim : Prop} :
    AyMDVOPublicSatWitness acceptedManifest publicWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_mdvo_conj_right (ay_mdvo_conj_right h)

theorem ay_mdvo_accepted_order_manifest_publishes_sound_sat
    {orderOk mapsOk digestOk clauseReplayOk checkerOk fingerprintOk buildOk
      publicWitness publicSatClaim : Prop} :
    AyMDVOAcceptedManifest orderOk mapsOk digestOk clauseReplayOk
      checkerOk fingerprintOk buildOk ->
    publicWitness -> publicSatClaim ->
    AyMDVOPublicSatWitness
      (AyMDVOAcceptedManifest orderOk mapsOk digestOk clauseReplayOk
        checkerOk fingerprintOk buildOk)
      publicWitness publicSatClaim :=
  ay_mdvo_public_sat_witness_intro

theorem ay_mdvo_variable_order_normalization_preserves_truth
    {solverOrderTruth dimacsOrderTruth : Prop} :
    AyMDVOEquisat solverOrderTruth dimacsOrderTruth ->
    solverOrderTruth -> dimacsOrderTruth :=
  ay_mdvo_equisat_forward

theorem ay_mdvo_public_sat_requires_manifest
    {acceptedManifest publicWitness publicSatClaim : Prop} :
    AyMDVOPublicSatWitness acceptedManifest publicWitness publicSatClaim ->
    acceptedManifest :=
  ay_mdvo_public_sat_witness_evidence

theorem ay_mdvo_publication_requires_order
    {orderOk mapsOk digestOk clauseReplayOk checkerOk fingerprintOk buildOk
      publicWitness publicSatClaim : Prop} :
    AyMDVOPublicSatWitness
      (AyMDVOAcceptedManifest orderOk mapsOk digestOk clauseReplayOk
        checkerOk fingerprintOk buildOk)
      publicWitness publicSatClaim ->
    orderOk :=
  fun h => ay_mdvo_accepted_manifest_order
    (ay_mdvo_public_sat_witness_evidence h)

theorem ay_mdvo_publication_requires_maps
    {orderOk mapsOk digestOk clauseReplayOk checkerOk fingerprintOk buildOk
      publicWitness publicSatClaim : Prop} :
    AyMDVOPublicSatWitness
      (AyMDVOAcceptedManifest orderOk mapsOk digestOk clauseReplayOk
        checkerOk fingerprintOk buildOk)
      publicWitness publicSatClaim ->
    mapsOk :=
  fun h => ay_mdvo_accepted_manifest_maps
    (ay_mdvo_public_sat_witness_evidence h)

theorem ay_mdvo_publication_requires_digest
    {orderOk mapsOk digestOk clauseReplayOk checkerOk fingerprintOk buildOk
      publicWitness publicSatClaim : Prop} :
    AyMDVOPublicSatWitness
      (AyMDVOAcceptedManifest orderOk mapsOk digestOk clauseReplayOk
        checkerOk fingerprintOk buildOk)
      publicWitness publicSatClaim ->
    digestOk :=
  fun h => ay_mdvo_accepted_manifest_digest
    (ay_mdvo_public_sat_witness_evidence h)

theorem ay_mdvo_publication_requires_clause_replay
    {orderOk mapsOk digestOk clauseReplayOk checkerOk fingerprintOk buildOk
      publicWitness publicSatClaim : Prop} :
    AyMDVOPublicSatWitness
      (AyMDVOAcceptedManifest orderOk mapsOk digestOk clauseReplayOk
        checkerOk fingerprintOk buildOk)
      publicWitness publicSatClaim ->
    clauseReplayOk :=
  fun h => ay_mdvo_accepted_manifest_clause_replay
    (ay_mdvo_public_sat_witness_evidence h)

theorem ay_mdvo_publication_requires_checker
    {orderOk mapsOk digestOk clauseReplayOk checkerOk fingerprintOk buildOk
      publicWitness publicSatClaim : Prop} :
    AyMDVOPublicSatWitness
      (AyMDVOAcceptedManifest orderOk mapsOk digestOk clauseReplayOk
        checkerOk fingerprintOk buildOk)
      publicWitness publicSatClaim ->
    checkerOk :=
  fun h => ay_mdvo_accepted_manifest_checker
    (ay_mdvo_public_sat_witness_evidence h)

theorem ay_mdvo_publication_requires_fingerprint
    {orderOk mapsOk digestOk clauseReplayOk checkerOk fingerprintOk buildOk
      publicWitness publicSatClaim : Prop} :
    AyMDVOPublicSatWitness
      (AyMDVOAcceptedManifest orderOk mapsOk digestOk clauseReplayOk
        checkerOk fingerprintOk buildOk)
      publicWitness publicSatClaim ->
    fingerprintOk :=
  fun h => ay_mdvo_accepted_manifest_fingerprint
    (ay_mdvo_public_sat_witness_evidence h)

theorem ay_mdvo_publication_requires_build
    {orderOk mapsOk digestOk clauseReplayOk checkerOk fingerprintOk buildOk
      publicWitness publicSatClaim : Prop} :
    AyMDVOPublicSatWitness
      (AyMDVOAcceptedManifest orderOk mapsOk digestOk clauseReplayOk
        checkerOk fingerprintOk buildOk)
      publicWitness publicSatClaim ->
    buildOk :=
  fun h => ay_mdvo_accepted_manifest_build
    (ay_mdvo_public_sat_witness_evidence h)

theorem ay_mdvo_no_claim_diagnostic_intro
    {reason blocksPublication : Prop} :
    reason -> blocksPublication ->
    AyMDVONoClaimDiagnostic reason blocksPublication :=
  ay_mdvo_conj_intro

theorem ay_mdvo_no_claim_diagnostic_blocks
    {reason blocksPublication : Prop} :
    AyMDVONoClaimDiagnostic reason blocksPublication -> blocksPublication :=
  ay_mdvo_conj_right

theorem ay_mdvo_recompute_obligation_intro
    {reason recomputeRequested : Prop} :
    reason -> recomputeRequested ->
    AyMDVORecomputeObligation reason recomputeRequested :=
  ay_mdvo_conj_intro

theorem ay_mdvo_recompute_obligation_request
    {reason recomputeRequested : Prop} :
    AyMDVORecomputeObligation reason recomputeRequested -> recomputeRequested :=
  ay_mdvo_conj_right

theorem ay_mdvo_order_drift_no_claim
    {orderDrift blocksPublication : Prop} :
    orderDrift -> blocksPublication ->
    AyMDVONoClaimDiagnostic orderDrift blocksPublication :=
  ay_mdvo_no_claim_diagnostic_intro

theorem ay_mdvo_order_drift_recompute
    {orderDrift recomputeRequested : Prop} :
    orderDrift -> recomputeRequested ->
    AyMDVORecomputeObligation orderDrift recomputeRequested :=
  ay_mdvo_recompute_obligation_intro

theorem ay_mdvo_mapping_mismatch_no_claim
    {mappingMismatch blocksPublication : Prop} :
    mappingMismatch -> blocksPublication ->
    AyMDVONoClaimDiagnostic mappingMismatch blocksPublication :=
  ay_mdvo_no_claim_diagnostic_intro

theorem ay_mdvo_digest_drift_no_claim
    {digestDrift blocksPublication : Prop} :
    digestDrift -> blocksPublication ->
    AyMDVONoClaimDiagnostic digestDrift blocksPublication :=
  ay_mdvo_no_claim_diagnostic_intro

theorem ay_mdvo_stale_fingerprint_no_claim
    {staleFingerprint blocksPublication : Prop} :
    staleFingerprint -> blocksPublication ->
    AyMDVONoClaimDiagnostic staleFingerprint blocksPublication :=
  ay_mdvo_no_claim_diagnostic_intro

theorem ay_mdvo_clause_replay_gap_no_claim
    {clauseReplayGap blocksPublication : Prop} :
    clauseReplayGap -> blocksPublication ->
    AyMDVONoClaimDiagnostic clauseReplayGap blocksPublication :=
  ay_mdvo_no_claim_diagnostic_intro

theorem ay_mdvo_checker_reject_no_claim
    {checkerReject blocksPublication : Prop} :
    checkerReject -> blocksPublication ->
    AyMDVONoClaimDiagnostic checkerReject blocksPublication :=
  ay_mdvo_no_claim_diagnostic_intro

theorem ay_mdvo_build_drift_no_claim
    {buildDrift blocksPublication : Prop} :
    buildDrift -> blocksPublication ->
    AyMDVONoClaimDiagnostic buildDrift blocksPublication :=
  ay_mdvo_no_claim_diagnostic_intro

theorem ay_mdvo_bad_order_manifest_cannot_bless_sat
    {failure blocksPublication recomputeRequested : Prop} :
    AyMDVONoClaimDiagnostic failure blocksPublication ->
    AyMDVORecomputeObligation failure recomputeRequested ->
    AyMDVOConj blocksPublication recomputeRequested :=
  fun hdiagnostic hrecompute =>
    ay_mdvo_conj_intro
      (ay_mdvo_no_claim_diagnostic_blocks hdiagnostic)
      (ay_mdvo_recompute_obligation_request hrecompute)
