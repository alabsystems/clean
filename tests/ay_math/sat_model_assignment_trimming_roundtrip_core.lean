-- SAT-COMP/ay assignment trimming roundtrip soundness skeleton.
-- Trimming don't-care variables and normalizing assignment order is admissible
-- only under DIMACS map, replay, digest, checker transcript, fingerprint, and
-- reconstruction evidence.

def AyMATRConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMATRDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMATREquisat (left right : Prop) : Prop :=
  AyMATRConj (left -> right) (right -> left)

def AyMATRTrimmingRoundtrip
    (fullAssignment trimmedAssignment orderNormalized roundtripAgreement :
      Prop) : Prop :=
  AyMATRConj fullAssignment
    (AyMATRConj trimmedAssignment
      (AyMATRConj orderNormalized roundtripAgreement))

def AyMATRDimacsVariableMap
    (dimacsMap originalMap mapAgreement : Prop) : Prop :=
  AyMATRConj dimacsMap (AyMATRConj originalMap mapAgreement)

def AyMATRReconstructionEvidence
    (trimmedWitness reconstructedWitness reconstructionAgreement : Prop) :
    Prop :=
  AyMATRConj trimmedWitness
    (AyMATRConj reconstructedWitness reconstructionAgreement)

def AyMATRAssignmentDigest
    (fullDigest trimmedDigest digestAgreement : Prop) : Prop :=
  AyMATRConj fullDigest (AyMATRConj trimmedDigest digestAgreement)

def AyMATRClauseEvaluationReplay
    (clauseReplay trimmedEvaluation evaluationAgreement : Prop) : Prop :=
  AyMATRConj clauseReplay
    (AyMATRConj trimmedEvaluation evaluationAgreement)

def AyMATRCheckerTranscript
    (checkerAccepted transcript replayAgreement : Prop) : Prop :=
  AyMATRConj checkerAccepted (AyMATRConj transcript replayAgreement)

def AyMATRFormulaFingerprint
    (originalFingerprint trimmedFingerprint fingerprintAgreement : Prop) :
    Prop :=
  AyMATRConj originalFingerprint
    (AyMATRConj trimmedFingerprint fingerprintAgreement)

def AyMATRAcceptedEvidence
    (roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk : Prop) : Prop :=
  AyMATRConj roundtripOk
    (AyMATRConj mapOk
      (AyMATRConj reconstructionOk
        (AyMATRConj digestOk
          (AyMATRConj clauseReplayOk
            (AyMATRConj transcriptOk fingerprintOk)))))

def AyMATRPublicSatWitness
    (acceptedEvidence publicWitness publicSatClaim : Prop) : Prop :=
  AyMATRConj acceptedEvidence
    (AyMATRConj publicWitness publicSatClaim)

def AyMATRNoClaimDiagnostic (diagnostic publicSatClaim : Prop) : Prop :=
  AyMATRConj diagnostic (publicSatClaim -> False)

def AyMATRRecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMATRConj reason recomputeRequest

theorem ay_matr_conj_intro {left right : Prop} :
    left -> right -> AyMATRConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_matr_conj_left {left right : Prop} :
    AyMATRConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_matr_conj_right {left right : Prop} :
    AyMATRConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_matr_disj_left {left right : Prop} :
    left -> AyMATRDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_matr_disj_right {left right : Prop} :
    right -> AyMATRDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_matr_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMATREquisat left right :=
  fun hf hb => ay_matr_conj_intro hf hb

theorem ay_matr_equisat_forward {left right : Prop} :
    AyMATREquisat left right -> left -> right :=
  fun h => ay_matr_conj_left h

theorem ay_matr_equisat_backward {left right : Prop} :
    AyMATREquisat left right -> right -> left :=
  fun h => ay_matr_conj_right h

theorem ay_matr_trimming_roundtrip_intro
    {fullAssignment trimmedAssignment orderNormalized roundtripAgreement :
      Prop} :
    fullAssignment ->
    trimmedAssignment ->
    orderNormalized ->
    roundtripAgreement ->
    AyMATRTrimmingRoundtrip
      fullAssignment trimmedAssignment orderNormalized roundtripAgreement :=
  fun hfull htrimmed horder hagree =>
    ay_matr_conj_intro hfull
      (ay_matr_conj_intro htrimmed
        (ay_matr_conj_intro horder hagree))

theorem ay_matr_trimming_roundtrip_full
    {fullAssignment trimmedAssignment orderNormalized roundtripAgreement :
      Prop} :
    AyMATRTrimmingRoundtrip
      fullAssignment trimmedAssignment orderNormalized roundtripAgreement ->
    fullAssignment :=
  fun h => ay_matr_conj_left h

theorem ay_matr_trimming_roundtrip_trimmed
    {fullAssignment trimmedAssignment orderNormalized roundtripAgreement :
      Prop} :
    AyMATRTrimmingRoundtrip
      fullAssignment trimmedAssignment orderNormalized roundtripAgreement ->
    trimmedAssignment :=
  fun h => ay_matr_conj_left (ay_matr_conj_right h)

theorem ay_matr_trimming_roundtrip_order
    {fullAssignment trimmedAssignment orderNormalized roundtripAgreement :
      Prop} :
    AyMATRTrimmingRoundtrip
      fullAssignment trimmedAssignment orderNormalized roundtripAgreement ->
    orderNormalized :=
  fun h => ay_matr_conj_left
    (ay_matr_conj_right (ay_matr_conj_right h))

theorem ay_matr_trimming_roundtrip_agreement
    {fullAssignment trimmedAssignment orderNormalized roundtripAgreement :
      Prop} :
    AyMATRTrimmingRoundtrip
      fullAssignment trimmedAssignment orderNormalized roundtripAgreement ->
    roundtripAgreement :=
  fun h => ay_matr_conj_right
    (ay_matr_conj_right (ay_matr_conj_right h))

theorem ay_matr_dimacs_variable_map_intro
    {dimacsMap originalMap mapAgreement : Prop} :
    dimacsMap ->
    originalMap ->
    mapAgreement ->
    AyMATRDimacsVariableMap dimacsMap originalMap mapAgreement :=
  fun hdimacs horiginal hagree =>
    ay_matr_conj_intro hdimacs (ay_matr_conj_intro horiginal hagree)

theorem ay_matr_dimacs_variable_map_dimacs
    {dimacsMap originalMap mapAgreement : Prop} :
    AyMATRDimacsVariableMap dimacsMap originalMap mapAgreement ->
    dimacsMap :=
  fun h => ay_matr_conj_left h

theorem ay_matr_dimacs_variable_map_original
    {dimacsMap originalMap mapAgreement : Prop} :
    AyMATRDimacsVariableMap dimacsMap originalMap mapAgreement ->
    originalMap :=
  fun h => ay_matr_conj_left (ay_matr_conj_right h)

theorem ay_matr_dimacs_variable_map_agreement
    {dimacsMap originalMap mapAgreement : Prop} :
    AyMATRDimacsVariableMap dimacsMap originalMap mapAgreement ->
    mapAgreement :=
  fun h => ay_matr_conj_right (ay_matr_conj_right h)

theorem ay_matr_reconstruction_evidence_intro
    {trimmedWitness reconstructedWitness reconstructionAgreement : Prop} :
    trimmedWitness ->
    reconstructedWitness ->
    reconstructionAgreement ->
    AyMATRReconstructionEvidence
      trimmedWitness reconstructedWitness reconstructionAgreement :=
  fun htrimmed hreconstructed hagree =>
    ay_matr_conj_intro htrimmed
      (ay_matr_conj_intro hreconstructed hagree)

theorem ay_matr_reconstruction_evidence_trimmed
    {trimmedWitness reconstructedWitness reconstructionAgreement : Prop} :
    AyMATRReconstructionEvidence
      trimmedWitness reconstructedWitness reconstructionAgreement ->
    trimmedWitness :=
  fun h => ay_matr_conj_left h

theorem ay_matr_reconstruction_evidence_reconstructed
    {trimmedWitness reconstructedWitness reconstructionAgreement : Prop} :
    AyMATRReconstructionEvidence
      trimmedWitness reconstructedWitness reconstructionAgreement ->
    reconstructedWitness :=
  fun h => ay_matr_conj_left (ay_matr_conj_right h)

theorem ay_matr_reconstruction_evidence_agreement
    {trimmedWitness reconstructedWitness reconstructionAgreement : Prop} :
    AyMATRReconstructionEvidence
      trimmedWitness reconstructedWitness reconstructionAgreement ->
    reconstructionAgreement :=
  fun h => ay_matr_conj_right (ay_matr_conj_right h)

theorem ay_matr_assignment_digest_intro
    {fullDigest trimmedDigest digestAgreement : Prop} :
    fullDigest ->
    trimmedDigest ->
    digestAgreement ->
    AyMATRAssignmentDigest fullDigest trimmedDigest digestAgreement :=
  fun hfull htrimmed hagree =>
    ay_matr_conj_intro hfull (ay_matr_conj_intro htrimmed hagree)

theorem ay_matr_assignment_digest_full
    {fullDigest trimmedDigest digestAgreement : Prop} :
    AyMATRAssignmentDigest fullDigest trimmedDigest digestAgreement ->
    fullDigest :=
  fun h => ay_matr_conj_left h

theorem ay_matr_assignment_digest_trimmed
    {fullDigest trimmedDigest digestAgreement : Prop} :
    AyMATRAssignmentDigest fullDigest trimmedDigest digestAgreement ->
    trimmedDigest :=
  fun h => ay_matr_conj_left (ay_matr_conj_right h)

theorem ay_matr_assignment_digest_agreement
    {fullDigest trimmedDigest digestAgreement : Prop} :
    AyMATRAssignmentDigest fullDigest trimmedDigest digestAgreement ->
    digestAgreement :=
  fun h => ay_matr_conj_right (ay_matr_conj_right h)

theorem ay_matr_clause_evaluation_replay_intro
    {clauseReplay trimmedEvaluation evaluationAgreement : Prop} :
    clauseReplay ->
    trimmedEvaluation ->
    evaluationAgreement ->
    AyMATRClauseEvaluationReplay
      clauseReplay trimmedEvaluation evaluationAgreement :=
  fun hreplay heval hagree =>
    ay_matr_conj_intro hreplay (ay_matr_conj_intro heval hagree)

theorem ay_matr_clause_evaluation_replay_trace
    {clauseReplay trimmedEvaluation evaluationAgreement : Prop} :
    AyMATRClauseEvaluationReplay
      clauseReplay trimmedEvaluation evaluationAgreement ->
    clauseReplay :=
  fun h => ay_matr_conj_left h

theorem ay_matr_clause_evaluation_replay_evaluation
    {clauseReplay trimmedEvaluation evaluationAgreement : Prop} :
    AyMATRClauseEvaluationReplay
      clauseReplay trimmedEvaluation evaluationAgreement ->
    trimmedEvaluation :=
  fun h => ay_matr_conj_left (ay_matr_conj_right h)

theorem ay_matr_clause_evaluation_replay_agreement
    {clauseReplay trimmedEvaluation evaluationAgreement : Prop} :
    AyMATRClauseEvaluationReplay
      clauseReplay trimmedEvaluation evaluationAgreement ->
    evaluationAgreement :=
  fun h => ay_matr_conj_right (ay_matr_conj_right h)

theorem ay_matr_checker_transcript_intro
    {checkerAccepted transcript replayAgreement : Prop} :
    checkerAccepted ->
    transcript ->
    replayAgreement ->
    AyMATRCheckerTranscript checkerAccepted transcript replayAgreement :=
  fun haccepted htranscript hagree =>
    ay_matr_conj_intro haccepted
      (ay_matr_conj_intro htranscript hagree)

theorem ay_matr_checker_transcript_accepted
    {checkerAccepted transcript replayAgreement : Prop} :
    AyMATRCheckerTranscript checkerAccepted transcript replayAgreement ->
    checkerAccepted :=
  fun h => ay_matr_conj_left h

theorem ay_matr_checker_transcript_transcript
    {checkerAccepted transcript replayAgreement : Prop} :
    AyMATRCheckerTranscript checkerAccepted transcript replayAgreement ->
    transcript :=
  fun h => ay_matr_conj_left (ay_matr_conj_right h)

theorem ay_matr_checker_transcript_agreement
    {checkerAccepted transcript replayAgreement : Prop} :
    AyMATRCheckerTranscript checkerAccepted transcript replayAgreement ->
    replayAgreement :=
  fun h => ay_matr_conj_right (ay_matr_conj_right h)

theorem ay_matr_formula_fingerprint_intro
    {originalFingerprint trimmedFingerprint fingerprintAgreement : Prop} :
    originalFingerprint ->
    trimmedFingerprint ->
    fingerprintAgreement ->
    AyMATRFormulaFingerprint
      originalFingerprint trimmedFingerprint fingerprintAgreement :=
  fun horiginal htrimmed hagree =>
    ay_matr_conj_intro horiginal
      (ay_matr_conj_intro htrimmed hagree)

theorem ay_matr_formula_fingerprint_original
    {originalFingerprint trimmedFingerprint fingerprintAgreement : Prop} :
    AyMATRFormulaFingerprint
      originalFingerprint trimmedFingerprint fingerprintAgreement ->
    originalFingerprint :=
  fun h => ay_matr_conj_left h

theorem ay_matr_formula_fingerprint_trimmed
    {originalFingerprint trimmedFingerprint fingerprintAgreement : Prop} :
    AyMATRFormulaFingerprint
      originalFingerprint trimmedFingerprint fingerprintAgreement ->
    trimmedFingerprint :=
  fun h => ay_matr_conj_left (ay_matr_conj_right h)

theorem ay_matr_formula_fingerprint_agreement
    {originalFingerprint trimmedFingerprint fingerprintAgreement : Prop} :
    AyMATRFormulaFingerprint
      originalFingerprint trimmedFingerprint fingerprintAgreement ->
    fingerprintAgreement :=
  fun h => ay_matr_conj_right (ay_matr_conj_right h)

theorem ay_matr_accepted_evidence_intro
    {roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk : Prop} :
    roundtripOk ->
    mapOk ->
    reconstructionOk ->
    digestOk ->
    clauseReplayOk ->
    transcriptOk ->
    fingerprintOk ->
    AyMATRAcceptedEvidence
      roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk :=
  fun hroundtrip hmap hreconstruction hdigest hclause htranscript
      hfingerprint =>
    ay_matr_conj_intro hroundtrip
      (ay_matr_conj_intro hmap
        (ay_matr_conj_intro hreconstruction
          (ay_matr_conj_intro hdigest
            (ay_matr_conj_intro hclause
              (ay_matr_conj_intro htranscript hfingerprint)))))

theorem ay_matr_accepted_evidence_roundtrip
    {roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk : Prop} :
    AyMATRAcceptedEvidence
      roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk ->
    roundtripOk :=
  fun h => ay_matr_conj_left h

theorem ay_matr_accepted_evidence_map
    {roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk : Prop} :
    AyMATRAcceptedEvidence
      roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk ->
    mapOk :=
  fun h => ay_matr_conj_left (ay_matr_conj_right h)

theorem ay_matr_accepted_evidence_reconstruction
    {roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk : Prop} :
    AyMATRAcceptedEvidence
      roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk ->
    reconstructionOk :=
  fun h => ay_matr_conj_left
    (ay_matr_conj_right (ay_matr_conj_right h))

theorem ay_matr_accepted_evidence_digest
    {roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk : Prop} :
    AyMATRAcceptedEvidence
      roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk ->
    digestOk :=
  fun h => ay_matr_conj_left
    (ay_matr_conj_right
      (ay_matr_conj_right (ay_matr_conj_right h)))

theorem ay_matr_accepted_evidence_clause_replay
    {roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk : Prop} :
    AyMATRAcceptedEvidence
      roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk ->
    clauseReplayOk :=
  fun h => ay_matr_conj_left
    (ay_matr_conj_right
      (ay_matr_conj_right
        (ay_matr_conj_right (ay_matr_conj_right h))))

theorem ay_matr_accepted_evidence_transcript
    {roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk : Prop} :
    AyMATRAcceptedEvidence
      roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk ->
    transcriptOk :=
  fun h => ay_matr_conj_left
    (ay_matr_conj_right
      (ay_matr_conj_right
        (ay_matr_conj_right
          (ay_matr_conj_right (ay_matr_conj_right h)))))

theorem ay_matr_accepted_evidence_fingerprint
    {roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk : Prop} :
    AyMATRAcceptedEvidence
      roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk ->
    fingerprintOk :=
  fun h => ay_matr_conj_right
    (ay_matr_conj_right
      (ay_matr_conj_right
        (ay_matr_conj_right
          (ay_matr_conj_right (ay_matr_conj_right h)))))

theorem ay_matr_public_sat_witness_intro
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    acceptedEvidence ->
    publicWitness ->
    publicSatClaim ->
    AyMATRPublicSatWitness acceptedEvidence publicWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_matr_conj_intro hevidence
      (ay_matr_conj_intro hwitness hclaim)

theorem ay_matr_public_sat_witness_evidence
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMATRPublicSatWitness acceptedEvidence publicWitness publicSatClaim ->
    acceptedEvidence :=
  fun h => ay_matr_conj_left h

theorem ay_matr_public_sat_witness_witness
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMATRPublicSatWitness acceptedEvidence publicWitness publicSatClaim ->
    publicWitness :=
  fun h => ay_matr_conj_left (ay_matr_conj_right h)

theorem ay_matr_public_sat_witness_claim
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMATRPublicSatWitness acceptedEvidence publicWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_matr_conj_right (ay_matr_conj_right h)

theorem ay_matr_accepted_trimming_roundtrip_publishes_sound_sat
    {roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMATRAcceptedEvidence
      roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk ->
    publicWitness ->
    publicSatClaim ->
    AyMATRPublicSatWitness
      (AyMATRAcceptedEvidence
        roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
        fingerprintOk)
      publicWitness
      publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_matr_public_sat_witness_intro hevidence hwitness hclaim

theorem ay_matr_public_sat_requires_accepted_evidence
    {acceptedEvidence publicWitness publicSatClaim : Prop} :
    AyMATRPublicSatWitness acceptedEvidence publicWitness publicSatClaim ->
    acceptedEvidence :=
  fun h => ay_matr_public_sat_witness_evidence h

theorem ay_matr_trimming_hints_preserve_truth
    {fullTruth trimmedTruth : Prop} :
    AyMATREquisat fullTruth trimmedTruth ->
    fullTruth ->
    trimmedTruth :=
  fun heq hfull => ay_matr_equisat_forward heq hfull

theorem ay_matr_clause_replay_transports_truth
    {clauseReplay trimmedEvaluation formulaTruth : Prop} :
    AyMATRClauseEvaluationReplay
      clauseReplay trimmedEvaluation formulaTruth ->
    formulaTruth :=
  fun h => ay_matr_clause_evaluation_replay_agreement h

theorem ay_matr_publication_requires_roundtrip
    {roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMATRPublicSatWitness
      (AyMATRAcceptedEvidence
        roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    roundtripOk :=
  fun h =>
    ay_matr_accepted_evidence_roundtrip
      (ay_matr_public_sat_witness_evidence h)

theorem ay_matr_publication_requires_map
    {roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMATRPublicSatWitness
      (AyMATRAcceptedEvidence
        roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    mapOk :=
  fun h =>
    ay_matr_accepted_evidence_map
      (ay_matr_public_sat_witness_evidence h)

theorem ay_matr_publication_requires_reconstruction
    {roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMATRPublicSatWitness
      (AyMATRAcceptedEvidence
        roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    reconstructionOk :=
  fun h =>
    ay_matr_accepted_evidence_reconstruction
      (ay_matr_public_sat_witness_evidence h)

theorem ay_matr_publication_requires_digest
    {roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMATRPublicSatWitness
      (AyMATRAcceptedEvidence
        roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    digestOk :=
  fun h =>
    ay_matr_accepted_evidence_digest
      (ay_matr_public_sat_witness_evidence h)

theorem ay_matr_publication_requires_clause_replay
    {roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMATRPublicSatWitness
      (AyMATRAcceptedEvidence
        roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    clauseReplayOk :=
  fun h =>
    ay_matr_accepted_evidence_clause_replay
      (ay_matr_public_sat_witness_evidence h)

theorem ay_matr_publication_requires_transcript
    {roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMATRPublicSatWitness
      (AyMATRAcceptedEvidence
        roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    transcriptOk :=
  fun h =>
    ay_matr_accepted_evidence_transcript
      (ay_matr_public_sat_witness_evidence h)

theorem ay_matr_publication_requires_fingerprint
    {roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
      fingerprintOk publicWitness publicSatClaim : Prop} :
    AyMATRPublicSatWitness
      (AyMATRAcceptedEvidence
        roundtripOk mapOk reconstructionOk digestOk clauseReplayOk transcriptOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    fingerprintOk :=
  fun h =>
    ay_matr_accepted_evidence_fingerprint
      (ay_matr_public_sat_witness_evidence h)

theorem ay_matr_no_claim_diagnostic_intro
    {diagnostic publicSatClaim : Prop} :
    diagnostic ->
    (publicSatClaim -> False) ->
    AyMATRNoClaimDiagnostic diagnostic publicSatClaim :=
  fun hdiagnostic hblocks =>
    ay_matr_conj_intro hdiagnostic hblocks

theorem ay_matr_no_claim_diagnostic_reason
    {diagnostic publicSatClaim : Prop} :
    AyMATRNoClaimDiagnostic diagnostic publicSatClaim -> diagnostic :=
  fun h => ay_matr_conj_left h

theorem ay_matr_no_claim_diagnostic_blocks
    {diagnostic publicSatClaim : Prop} :
    AyMATRNoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h => ay_matr_conj_right h

theorem ay_matr_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMATRRecomputeObligation reason recomputeRequest :=
  fun hreason hrecompute => ay_matr_conj_intro hreason hrecompute

theorem ay_matr_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMATRRecomputeObligation reason recomputeRequest -> reason :=
  fun h => ay_matr_conj_left h

theorem ay_matr_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMATRRecomputeObligation reason recomputeRequest -> recomputeRequest :=
  fun h => ay_matr_conj_right h

theorem ay_matr_missing_variable_map_recompute
    {missingVariableMap recomputeRequest : Prop} :
    missingVariableMap ->
    recomputeRequest ->
    AyMATRRecomputeObligation missingVariableMap recomputeRequest :=
  fun hmissing hrecompute =>
    ay_matr_recompute_obligation_intro hmissing hrecompute

theorem ay_matr_missing_variable_map_no_claim
    {missingVariableMap publicSatClaim : Prop} :
    missingVariableMap ->
    (publicSatClaim -> False) ->
    AyMATRNoClaimDiagnostic missingVariableMap publicSatClaim :=
  fun hmissing hblocks =>
    ay_matr_no_claim_diagnostic_intro hmissing hblocks

theorem ay_matr_digest_mismatch_no_claim
    {digestMismatch publicSatClaim : Prop} :
    digestMismatch ->
    (publicSatClaim -> False) ->
    AyMATRNoClaimDiagnostic digestMismatch publicSatClaim :=
  fun hmismatch hblocks =>
    ay_matr_no_claim_diagnostic_intro hmismatch hblocks

theorem ay_matr_clause_replay_failure_no_claim
    {clauseReplayFailure publicSatClaim : Prop} :
    clauseReplayFailure ->
    (publicSatClaim -> False) ->
    AyMATRNoClaimDiagnostic clauseReplayFailure publicSatClaim :=
  fun hfailure hblocks =>
    ay_matr_no_claim_diagnostic_intro hfailure hblocks

theorem ay_matr_stale_fingerprint_no_claim
    {staleFingerprint publicSatClaim : Prop} :
    staleFingerprint ->
    (publicSatClaim -> False) ->
    AyMATRNoClaimDiagnostic staleFingerprint publicSatClaim :=
  fun hstale hblocks => ay_matr_no_claim_diagnostic_intro hstale hblocks

theorem ay_matr_checker_rejection_no_claim
    {checkerRejection publicSatClaim : Prop} :
    checkerRejection ->
    (publicSatClaim -> False) ->
    AyMATRNoClaimDiagnostic checkerRejection publicSatClaim :=
  fun hreject hblocks =>
    ay_matr_no_claim_diagnostic_intro hreject hblocks

theorem ay_matr_reconstruction_failure_no_claim
    {reconstructionFailure publicSatClaim : Prop} :
    reconstructionFailure ->
    (publicSatClaim -> False) ->
    AyMATRNoClaimDiagnostic reconstructionFailure publicSatClaim :=
  fun hfailure hblocks =>
    ay_matr_no_claim_diagnostic_intro hfailure hblocks

theorem ay_matr_diagnostic_blocks_public_claim
    {diagnostic publicSatClaim : Prop} :
    AyMATRNoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_matr_no_claim_diagnostic_blocks h hclaim

theorem ay_matr_bad_trimming_roundtrip_cannot_bless_sat
    {badRoundtrip publicSatClaim : Prop} :
    AyMATRNoClaimDiagnostic badRoundtrip publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_matr_diagnostic_blocks_public_claim h hclaim
