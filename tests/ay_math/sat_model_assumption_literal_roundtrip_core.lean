/- SAT-COMP/ay assumption-literal model roundtrip contract.

This self-contained package models SAT solving under assumptions and the
evidence needed to translate the resulting witness back to the original
assumption frame before public SAT publication.
-/

def AyMALRConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMALRDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMALREquisat (source target : Prop) : Prop :=
  AyMALRConj (source -> target) (target -> source)

def AyMALRAssumptionMap
    (solverAssumptions originalAssumptions assumptionAgreement : Prop) : Prop :=
  AyMALRConj solverAssumptions
    (AyMALRConj originalAssumptions assumptionAgreement)

def AyMALRDimacsMaps
    (solverToDimacs dimacsToSolver mapAgreement : Prop) : Prop :=
  AyMALRConj solverToDimacs (AyMALRConj dimacsToSolver mapAgreement)

def AyMALRAssignmentDigest
    (solverDigest dimacsDigest digestAgreement : Prop) : Prop :=
  AyMALRConj solverDigest (AyMALRConj dimacsDigest digestAgreement)

def AyMALRCompletionManifest
    (assumptionWitness completedWitness completionAgreement : Prop) : Prop :=
  AyMALRConj assumptionWitness
    (AyMALRConj completedWitness completionAgreement)

def AyMALRClauseReplay
    (clauseReplay witnessEvaluation replayAgreement : Prop) : Prop :=
  AyMALRConj clauseReplay (AyMALRConj witnessEvaluation replayAgreement)

def AyMALRCheckerTranscript
    (checkerAccepted transcript transcriptAgreement : Prop) : Prop :=
  AyMALRConj checkerAccepted (AyMALRConj transcript transcriptAgreement)

def AyMALRFormulaFingerprint
    (originalFingerprint assumptionFingerprint fingerprintAgreement : Prop) : Prop :=
  AyMALRConj originalFingerprint
    (AyMALRConj assumptionFingerprint fingerprintAgreement)

def AyMALRBuildEvidence
    (solverBuild assumptionBuild buildAgreement : Prop) : Prop :=
  AyMALRConj solverBuild (AyMALRConj assumptionBuild buildAgreement)

def AyMALRAcceptedRoundtrip
    (assumptionOk mapsOk digestOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk : Prop) : Prop :=
  AyMALRConj assumptionOk
    (AyMALRConj mapsOk
      (AyMALRConj digestOk
        (AyMALRConj completionOk
          (AyMALRConj clauseReplayOk
            (AyMALRConj checkerOk
              (AyMALRConj fingerprintOk buildOk))))))

def AyMALRPublicSatWitness
    (acceptedRoundtrip publicWitness publicSatClaim : Prop) : Prop :=
  AyMALRConj acceptedRoundtrip (AyMALRConj publicWitness publicSatClaim)

def AyMALRNoClaimDiagnostic (reason blocksPublication : Prop) : Prop :=
  AyMALRConj reason blocksPublication

def AyMALRRecomputeObligation (reason recomputeRequested : Prop) : Prop :=
  AyMALRConj reason recomputeRequested

theorem ay_malr_conj_intro {left right : Prop} :
    left -> right -> AyMALRConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_malr_conj_left {left right : Prop} :
    AyMALRConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_malr_conj_right {left right : Prop} :
    AyMALRConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_malr_disj_left {left right : Prop} :
    left -> AyMALRDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_malr_disj_right {left right : Prop} :
    right -> AyMALRDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_malr_equisat_intro {source target : Prop} :
    (source -> target) -> (target -> source) -> AyMALREquisat source target :=
  fun forward backward => ay_malr_conj_intro forward backward

theorem ay_malr_equisat_forward {source target : Prop} :
    AyMALREquisat source target -> source -> target :=
  fun h => ay_malr_conj_left h

theorem ay_malr_equisat_backward {source target : Prop} :
    AyMALREquisat source target -> target -> source :=
  fun h => ay_malr_conj_right h

theorem ay_malr_assumption_map_intro
    {solverAssumptions originalAssumptions assumptionAgreement : Prop} :
    solverAssumptions -> originalAssumptions -> assumptionAgreement ->
    AyMALRAssumptionMap
      solverAssumptions originalAssumptions assumptionAgreement :=
  fun hsolver horiginal hagree =>
    ay_malr_conj_intro hsolver (ay_malr_conj_intro horiginal hagree)

theorem ay_malr_assumption_map_solver
    {solverAssumptions originalAssumptions assumptionAgreement : Prop} :
    AyMALRAssumptionMap
      solverAssumptions originalAssumptions assumptionAgreement ->
    solverAssumptions :=
  fun h => ay_malr_conj_left h

theorem ay_malr_assumption_map_original
    {solverAssumptions originalAssumptions assumptionAgreement : Prop} :
    AyMALRAssumptionMap
      solverAssumptions originalAssumptions assumptionAgreement ->
    originalAssumptions :=
  fun h => ay_malr_conj_left (ay_malr_conj_right h)

theorem ay_malr_assumption_map_agreement
    {solverAssumptions originalAssumptions assumptionAgreement : Prop} :
    AyMALRAssumptionMap
      solverAssumptions originalAssumptions assumptionAgreement ->
    assumptionAgreement :=
  fun h => ay_malr_conj_right (ay_malr_conj_right h)

theorem ay_malr_dimacs_maps_intro
    {solverToDimacs dimacsToSolver mapAgreement : Prop} :
    solverToDimacs -> dimacsToSolver -> mapAgreement ->
    AyMALRDimacsMaps solverToDimacs dimacsToSolver mapAgreement :=
  fun hforward hbackward hagree =>
    ay_malr_conj_intro hforward (ay_malr_conj_intro hbackward hagree)

theorem ay_malr_assignment_digest_intro
    {solverDigest dimacsDigest digestAgreement : Prop} :
    solverDigest -> dimacsDigest -> digestAgreement ->
    AyMALRAssignmentDigest solverDigest dimacsDigest digestAgreement :=
  fun hsolver hdimacs hagree =>
    ay_malr_conj_intro hsolver (ay_malr_conj_intro hdimacs hagree)

theorem ay_malr_completion_manifest_intro
    {assumptionWitness completedWitness completionAgreement : Prop} :
    assumptionWitness -> completedWitness -> completionAgreement ->
    AyMALRCompletionManifest
      assumptionWitness completedWitness completionAgreement :=
  fun hwitness hcompleted hagree =>
    ay_malr_conj_intro hwitness (ay_malr_conj_intro hcompleted hagree)

theorem ay_malr_clause_replay_intro
    {clauseReplay witnessEvaluation replayAgreement : Prop} :
    clauseReplay -> witnessEvaluation -> replayAgreement ->
    AyMALRClauseReplay clauseReplay witnessEvaluation replayAgreement :=
  fun hreplay heval hagree =>
    ay_malr_conj_intro hreplay (ay_malr_conj_intro heval hagree)

theorem ay_malr_checker_transcript_intro
    {checkerAccepted transcript transcriptAgreement : Prop} :
    checkerAccepted -> transcript -> transcriptAgreement ->
    AyMALRCheckerTranscript checkerAccepted transcript transcriptAgreement :=
  fun haccepted htranscript hagree =>
    ay_malr_conj_intro haccepted (ay_malr_conj_intro htranscript hagree)

theorem ay_malr_formula_fingerprint_intro
    {originalFingerprint assumptionFingerprint fingerprintAgreement : Prop} :
    originalFingerprint -> assumptionFingerprint -> fingerprintAgreement ->
    AyMALRFormulaFingerprint
      originalFingerprint assumptionFingerprint fingerprintAgreement :=
  fun horiginal hassumption hagree =>
    ay_malr_conj_intro horiginal (ay_malr_conj_intro hassumption hagree)

theorem ay_malr_build_evidence_intro
    {solverBuild assumptionBuild buildAgreement : Prop} :
    solverBuild -> assumptionBuild -> buildAgreement ->
    AyMALRBuildEvidence solverBuild assumptionBuild buildAgreement :=
  fun hsolver hassumption hagree =>
    ay_malr_conj_intro hsolver (ay_malr_conj_intro hassumption hagree)

theorem ay_malr_accepted_roundtrip_intro
    {assumptionOk mapsOk digestOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk : Prop} :
    assumptionOk -> mapsOk -> digestOk -> completionOk -> clauseReplayOk ->
    checkerOk -> fingerprintOk -> buildOk ->
    AyMALRAcceptedRoundtrip assumptionOk mapsOk digestOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk :=
  fun hassumption hmaps hdigest hcompletion hclause hchecker hfingerprint
      hbuild =>
    ay_malr_conj_intro hassumption
      (ay_malr_conj_intro hmaps
        (ay_malr_conj_intro hdigest
          (ay_malr_conj_intro hcompletion
            (ay_malr_conj_intro hclause
              (ay_malr_conj_intro hchecker
                (ay_malr_conj_intro hfingerprint hbuild))))))

theorem ay_malr_accepted_roundtrip_assumption
    {assumptionOk mapsOk digestOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk : Prop} :
    AyMALRAcceptedRoundtrip assumptionOk mapsOk digestOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk ->
    assumptionOk :=
  fun h => ay_malr_conj_left h

theorem ay_malr_accepted_roundtrip_maps
    {assumptionOk mapsOk digestOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk : Prop} :
    AyMALRAcceptedRoundtrip assumptionOk mapsOk digestOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk ->
    mapsOk :=
  fun h => ay_malr_conj_left (ay_malr_conj_right h)

theorem ay_malr_accepted_roundtrip_digest
    {assumptionOk mapsOk digestOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk : Prop} :
    AyMALRAcceptedRoundtrip assumptionOk mapsOk digestOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk ->
    digestOk :=
  fun h => ay_malr_conj_left (ay_malr_conj_right (ay_malr_conj_right h))

theorem ay_malr_accepted_roundtrip_completion
    {assumptionOk mapsOk digestOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk : Prop} :
    AyMALRAcceptedRoundtrip assumptionOk mapsOk digestOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk ->
    completionOk :=
  fun h =>
    ay_malr_conj_left
      (ay_malr_conj_right (ay_malr_conj_right (ay_malr_conj_right h)))

theorem ay_malr_accepted_roundtrip_clause_replay
    {assumptionOk mapsOk digestOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk : Prop} :
    AyMALRAcceptedRoundtrip assumptionOk mapsOk digestOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk ->
    clauseReplayOk :=
  fun h =>
    ay_malr_conj_left
      (ay_malr_conj_right
        (ay_malr_conj_right (ay_malr_conj_right (ay_malr_conj_right h))))

theorem ay_malr_accepted_roundtrip_checker
    {assumptionOk mapsOk digestOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk : Prop} :
    AyMALRAcceptedRoundtrip assumptionOk mapsOk digestOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk ->
    checkerOk :=
  fun h =>
    ay_malr_conj_left
      (ay_malr_conj_right
        (ay_malr_conj_right
          (ay_malr_conj_right (ay_malr_conj_right (ay_malr_conj_right h)))))

theorem ay_malr_accepted_roundtrip_fingerprint
    {assumptionOk mapsOk digestOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk : Prop} :
    AyMALRAcceptedRoundtrip assumptionOk mapsOk digestOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk ->
    fingerprintOk :=
  fun h =>
    ay_malr_conj_left
      (ay_malr_conj_right
        (ay_malr_conj_right
          (ay_malr_conj_right
            (ay_malr_conj_right (ay_malr_conj_right
              (ay_malr_conj_right h))))))

theorem ay_malr_accepted_roundtrip_build
    {assumptionOk mapsOk digestOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk : Prop} :
    AyMALRAcceptedRoundtrip assumptionOk mapsOk digestOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk ->
    buildOk :=
  fun h =>
    ay_malr_conj_right
      (ay_malr_conj_right
        (ay_malr_conj_right
          (ay_malr_conj_right
            (ay_malr_conj_right (ay_malr_conj_right
              (ay_malr_conj_right h))))))

theorem ay_malr_public_sat_witness_intro
    {acceptedRoundtrip publicWitness publicSatClaim : Prop} :
    acceptedRoundtrip -> publicWitness -> publicSatClaim ->
    AyMALRPublicSatWitness acceptedRoundtrip publicWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_malr_conj_intro hevidence (ay_malr_conj_intro hwitness hclaim)

theorem ay_malr_public_sat_witness_evidence
    {acceptedRoundtrip publicWitness publicSatClaim : Prop} :
    AyMALRPublicSatWitness acceptedRoundtrip publicWitness publicSatClaim ->
    acceptedRoundtrip :=
  fun h => ay_malr_conj_left h

theorem ay_malr_public_sat_witness_claim
    {acceptedRoundtrip publicWitness publicSatClaim : Prop} :
    AyMALRPublicSatWitness acceptedRoundtrip publicWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_malr_conj_right (ay_malr_conj_right h)

theorem ay_malr_accepted_assumption_roundtrip_publishes_sound_sat
    {assumptionOk mapsOk digestOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk publicWitness publicSatClaim : Prop} :
    AyMALRAcceptedRoundtrip assumptionOk mapsOk digestOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk ->
    publicWitness -> publicSatClaim ->
    AyMALRPublicSatWitness
      (AyMALRAcceptedRoundtrip assumptionOk mapsOk digestOk completionOk
        clauseReplayOk checkerOk fingerprintOk buildOk)
      publicWitness publicSatClaim :=
  ay_malr_public_sat_witness_intro

theorem ay_malr_assumption_roundtrip_preserves_truth
    {assumptionTruth publicTruth : Prop} :
    AyMALREquisat assumptionTruth publicTruth -> assumptionTruth -> publicTruth :=
  ay_malr_equisat_forward

theorem ay_malr_public_sat_requires_roundtrip
    {acceptedRoundtrip publicWitness publicSatClaim : Prop} :
    AyMALRPublicSatWitness acceptedRoundtrip publicWitness publicSatClaim ->
    acceptedRoundtrip :=
  ay_malr_public_sat_witness_evidence

theorem ay_malr_publication_requires_assumptions
    {assumptionOk mapsOk digestOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk publicWitness publicSatClaim : Prop} :
    AyMALRPublicSatWitness
      (AyMALRAcceptedRoundtrip assumptionOk mapsOk digestOk completionOk
        clauseReplayOk checkerOk fingerprintOk buildOk)
      publicWitness publicSatClaim ->
    assumptionOk :=
  fun h => ay_malr_accepted_roundtrip_assumption
    (ay_malr_public_sat_witness_evidence h)

theorem ay_malr_publication_requires_maps
    {assumptionOk mapsOk digestOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk publicWitness publicSatClaim : Prop} :
    AyMALRPublicSatWitness
      (AyMALRAcceptedRoundtrip assumptionOk mapsOk digestOk completionOk
        clauseReplayOk checkerOk fingerprintOk buildOk)
      publicWitness publicSatClaim ->
    mapsOk :=
  fun h => ay_malr_accepted_roundtrip_maps
    (ay_malr_public_sat_witness_evidence h)

theorem ay_malr_publication_requires_digest
    {assumptionOk mapsOk digestOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk publicWitness publicSatClaim : Prop} :
    AyMALRPublicSatWitness
      (AyMALRAcceptedRoundtrip assumptionOk mapsOk digestOk completionOk
        clauseReplayOk checkerOk fingerprintOk buildOk)
      publicWitness publicSatClaim ->
    digestOk :=
  fun h => ay_malr_accepted_roundtrip_digest
    (ay_malr_public_sat_witness_evidence h)

theorem ay_malr_publication_requires_completion
    {assumptionOk mapsOk digestOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk publicWitness publicSatClaim : Prop} :
    AyMALRPublicSatWitness
      (AyMALRAcceptedRoundtrip assumptionOk mapsOk digestOk completionOk
        clauseReplayOk checkerOk fingerprintOk buildOk)
      publicWitness publicSatClaim ->
    completionOk :=
  fun h => ay_malr_accepted_roundtrip_completion
    (ay_malr_public_sat_witness_evidence h)

theorem ay_malr_publication_requires_clause_replay
    {assumptionOk mapsOk digestOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk publicWitness publicSatClaim : Prop} :
    AyMALRPublicSatWitness
      (AyMALRAcceptedRoundtrip assumptionOk mapsOk digestOk completionOk
        clauseReplayOk checkerOk fingerprintOk buildOk)
      publicWitness publicSatClaim ->
    clauseReplayOk :=
  fun h => ay_malr_accepted_roundtrip_clause_replay
    (ay_malr_public_sat_witness_evidence h)

theorem ay_malr_publication_requires_checker
    {assumptionOk mapsOk digestOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk publicWitness publicSatClaim : Prop} :
    AyMALRPublicSatWitness
      (AyMALRAcceptedRoundtrip assumptionOk mapsOk digestOk completionOk
        clauseReplayOk checkerOk fingerprintOk buildOk)
      publicWitness publicSatClaim ->
    checkerOk :=
  fun h => ay_malr_accepted_roundtrip_checker
    (ay_malr_public_sat_witness_evidence h)

theorem ay_malr_publication_requires_fingerprint
    {assumptionOk mapsOk digestOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk publicWitness publicSatClaim : Prop} :
    AyMALRPublicSatWitness
      (AyMALRAcceptedRoundtrip assumptionOk mapsOk digestOk completionOk
        clauseReplayOk checkerOk fingerprintOk buildOk)
      publicWitness publicSatClaim ->
    fingerprintOk :=
  fun h => ay_malr_accepted_roundtrip_fingerprint
    (ay_malr_public_sat_witness_evidence h)

theorem ay_malr_publication_requires_build
    {assumptionOk mapsOk digestOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk publicWitness publicSatClaim : Prop} :
    AyMALRPublicSatWitness
      (AyMALRAcceptedRoundtrip assumptionOk mapsOk digestOk completionOk
        clauseReplayOk checkerOk fingerprintOk buildOk)
      publicWitness publicSatClaim ->
    buildOk :=
  fun h => ay_malr_accepted_roundtrip_build
    (ay_malr_public_sat_witness_evidence h)

theorem ay_malr_no_claim_diagnostic_intro
    {reason blocksPublication : Prop} :
    reason -> blocksPublication ->
    AyMALRNoClaimDiagnostic reason blocksPublication :=
  ay_malr_conj_intro

theorem ay_malr_no_claim_diagnostic_blocks
    {reason blocksPublication : Prop} :
    AyMALRNoClaimDiagnostic reason blocksPublication -> blocksPublication :=
  ay_malr_conj_right

theorem ay_malr_recompute_obligation_intro
    {reason recomputeRequested : Prop} :
    reason -> recomputeRequested ->
    AyMALRRecomputeObligation reason recomputeRequested :=
  ay_malr_conj_intro

theorem ay_malr_recompute_obligation_request
    {reason recomputeRequested : Prop} :
    AyMALRRecomputeObligation reason recomputeRequested -> recomputeRequested :=
  ay_malr_conj_right

theorem ay_malr_assumption_map_drift_no_claim
    {assumptionMapDrift blocksPublication : Prop} :
    assumptionMapDrift -> blocksPublication ->
    AyMALRNoClaimDiagnostic assumptionMapDrift blocksPublication :=
  ay_malr_no_claim_diagnostic_intro

theorem ay_malr_assumption_map_drift_recompute
    {assumptionMapDrift recomputeRequested : Prop} :
    assumptionMapDrift -> recomputeRequested ->
    AyMALRRecomputeObligation assumptionMapDrift recomputeRequested :=
  ay_malr_recompute_obligation_intro

theorem ay_malr_missing_assumption_literal_no_claim
    {missingAssumptionLiteral blocksPublication : Prop} :
    missingAssumptionLiteral -> blocksPublication ->
    AyMALRNoClaimDiagnostic missingAssumptionLiteral blocksPublication :=
  ay_malr_no_claim_diagnostic_intro

theorem ay_malr_map_mismatch_no_claim
    {mapMismatch blocksPublication : Prop} :
    mapMismatch -> blocksPublication ->
    AyMALRNoClaimDiagnostic mapMismatch blocksPublication :=
  ay_malr_no_claim_diagnostic_intro

theorem ay_malr_digest_drift_no_claim
    {digestDrift blocksPublication : Prop} :
    digestDrift -> blocksPublication ->
    AyMALRNoClaimDiagnostic digestDrift blocksPublication :=
  ay_malr_no_claim_diagnostic_intro

theorem ay_malr_completion_mismatch_no_claim
    {completionMismatch blocksPublication : Prop} :
    completionMismatch -> blocksPublication ->
    AyMALRNoClaimDiagnostic completionMismatch blocksPublication :=
  ay_malr_no_claim_diagnostic_intro

theorem ay_malr_clause_replay_gap_no_claim
    {clauseReplayGap blocksPublication : Prop} :
    clauseReplayGap -> blocksPublication ->
    AyMALRNoClaimDiagnostic clauseReplayGap blocksPublication :=
  ay_malr_no_claim_diagnostic_intro

theorem ay_malr_stale_fingerprint_no_claim
    {staleFingerprint blocksPublication : Prop} :
    staleFingerprint -> blocksPublication ->
    AyMALRNoClaimDiagnostic staleFingerprint blocksPublication :=
  ay_malr_no_claim_diagnostic_intro

theorem ay_malr_checker_reject_no_claim
    {checkerReject blocksPublication : Prop} :
    checkerReject -> blocksPublication ->
    AyMALRNoClaimDiagnostic checkerReject blocksPublication :=
  ay_malr_no_claim_diagnostic_intro

theorem ay_malr_build_drift_no_claim
    {buildDrift blocksPublication : Prop} :
    buildDrift -> blocksPublication ->
    AyMALRNoClaimDiagnostic buildDrift blocksPublication :=
  ay_malr_no_claim_diagnostic_intro

theorem ay_malr_bad_assumption_roundtrip_cannot_bless_sat
    {failure blocksPublication recomputeRequested : Prop} :
    AyMALRNoClaimDiagnostic failure blocksPublication ->
    AyMALRRecomputeObligation failure recomputeRequested ->
    AyMALRConj blocksPublication recomputeRequested :=
  fun hdiagnostic hrecompute =>
    ay_malr_conj_intro
      (ay_malr_no_claim_diagnostic_blocks hdiagnostic)
      (ay_malr_recompute_obligation_request hrecompute)
