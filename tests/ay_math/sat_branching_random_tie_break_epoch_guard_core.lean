-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Random tie-break epoch guard skeleton for sequential-main SAT. Deterministic
-- or randomized tie-break metadata is a performance hint only when epoch,
-- seed, candidate set, heap, phase/trail, fallback, build, validator, and
-- audit evidence agree.

def ay_brtb_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_brtb_equisat (before : Prop) (after : Prop) : Prop :=
  ay_brtb_conj (before -> after) (after -> before)

def ay_brtb_tie_break_guard
    (tieBreakEpochLedger : Prop)
    (seedDigest : Prop)
    (candidateSetDigest : Prop)
    (activityHeapSnapshot : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) : Prop :=
  forall result : Prop,
    (tieBreakEpochLedger ->
      seedDigest ->
      candidateSetDigest ->
      activityHeapSnapshot ->
      phaseTrailSnapshot ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditEvidence ->
      result) ->
    result

def ay_brtb_guard_agreement
    (epochMatch : Prop)
    (seedMatch : Prop)
    (candidateSetMatch : Prop)
    (heapMatch : Prop)
    (phaseTrailMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_brtb_tie_break_guard epochMatch seedMatch candidateSetMatch heapMatch
    phaseTrailMatch fallbackMatch buildMatch validatorAccepts auditMatch

def ay_brtb_accepted_tie_break
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (tieBreakGuidance : Prop) : Prop :=
  ay_brtb_conj guardEvidence
    (ay_brtb_conj agreementEvidence tieBreakGuidance)

def ay_brtb_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_brtb_conj acceptedEvidence (ay_brtb_conj outcome formulaTruth)

def ay_brtb_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_brtb_conj diagnostic fallbackPublic

theorem ay_brtb_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_brtb_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_brtb_conj_left (left : Prop) (right : Prop) :
    ay_brtb_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_brtb_conj_right (left : Prop) (right : Prop) :
    ay_brtb_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_brtb_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_brtb_equisat before after :=
  fun forward backward =>
    ay_brtb_conj_intro (before -> after) (after -> before) forward backward

theorem ay_brtb_equisat_forward (before : Prop) (after : Prop) :
    ay_brtb_equisat before after -> before -> after :=
  fun eqsat =>
    ay_brtb_conj_left (before -> after) (after -> before) eqsat

theorem ay_brtb_equisat_backward (before : Prop) (after : Prop) :
    ay_brtb_equisat before after -> after -> before :=
  fun eqsat =>
    ay_brtb_conj_right (before -> after) (after -> before) eqsat

theorem ay_brtb_tie_break_guard_intro
    (tieBreakEpochLedger : Prop)
    (seedDigest : Prop)
    (candidateSetDigest : Prop)
    (activityHeapSnapshot : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    tieBreakEpochLedger ->
    seedDigest ->
    candidateSetDigest ->
    activityHeapSnapshot ->
    phaseTrailSnapshot ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditEvidence ->
    ay_brtb_tie_break_guard tieBreakEpochLedger seedDigest
      candidateSetDigest activityHeapSnapshot phaseTrailSnapshot
      fallbackBaseline buildEvidence validatorGate auditEvidence :=
  fun epochH seedH candidateH heapH phaseTrailH fallbackH buildH validatorH
      auditH result build =>
    build epochH seedH candidateH heapH phaseTrailH fallbackH buildH validatorH
      auditH

theorem ay_brtb_tie_break_guard_epoch
    (tieBreakEpochLedger : Prop)
    (seedDigest : Prop)
    (candidateSetDigest : Prop)
    (activityHeapSnapshot : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brtb_tie_break_guard tieBreakEpochLedger seedDigest
      candidateSetDigest activityHeapSnapshot phaseTrailSnapshot
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    tieBreakEpochLedger :=
  fun guard =>
    guard tieBreakEpochLedger
      (fun epochH _seedH _candidateH _heapH _phaseTrailH _fallbackH _buildH
          _validatorH _auditH => epochH)

theorem ay_brtb_tie_break_guard_seed
    (tieBreakEpochLedger : Prop)
    (seedDigest : Prop)
    (candidateSetDigest : Prop)
    (activityHeapSnapshot : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brtb_tie_break_guard tieBreakEpochLedger seedDigest
      candidateSetDigest activityHeapSnapshot phaseTrailSnapshot
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    seedDigest :=
  fun guard =>
    guard seedDigest
      (fun _epochH seedH _candidateH _heapH _phaseTrailH _fallbackH _buildH
          _validatorH _auditH => seedH)

theorem ay_brtb_tie_break_guard_candidate_set
    (tieBreakEpochLedger : Prop)
    (seedDigest : Prop)
    (candidateSetDigest : Prop)
    (activityHeapSnapshot : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brtb_tie_break_guard tieBreakEpochLedger seedDigest
      candidateSetDigest activityHeapSnapshot phaseTrailSnapshot
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    candidateSetDigest :=
  fun guard =>
    guard candidateSetDigest
      (fun _epochH _seedH candidateH _heapH _phaseTrailH _fallbackH _buildH
          _validatorH _auditH => candidateH)

theorem ay_brtb_tie_break_guard_heap
    (tieBreakEpochLedger : Prop)
    (seedDigest : Prop)
    (candidateSetDigest : Prop)
    (activityHeapSnapshot : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brtb_tie_break_guard tieBreakEpochLedger seedDigest
      candidateSetDigest activityHeapSnapshot phaseTrailSnapshot
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    activityHeapSnapshot :=
  fun guard =>
    guard activityHeapSnapshot
      (fun _epochH _seedH _candidateH heapH _phaseTrailH _fallbackH _buildH
          _validatorH _auditH => heapH)

theorem ay_brtb_tie_break_guard_phase_trail
    (tieBreakEpochLedger : Prop)
    (seedDigest : Prop)
    (candidateSetDigest : Prop)
    (activityHeapSnapshot : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brtb_tie_break_guard tieBreakEpochLedger seedDigest
      candidateSetDigest activityHeapSnapshot phaseTrailSnapshot
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    phaseTrailSnapshot :=
  fun guard =>
    guard phaseTrailSnapshot
      (fun _epochH _seedH _candidateH _heapH phaseTrailH _fallbackH _buildH
          _validatorH _auditH => phaseTrailH)

theorem ay_brtb_tie_break_guard_fallback
    (tieBreakEpochLedger : Prop)
    (seedDigest : Prop)
    (candidateSetDigest : Prop)
    (activityHeapSnapshot : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brtb_tie_break_guard tieBreakEpochLedger seedDigest
      candidateSetDigest activityHeapSnapshot phaseTrailSnapshot
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _epochH _seedH _candidateH _heapH _phaseTrailH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_brtb_tie_break_guard_build
    (tieBreakEpochLedger : Prop)
    (seedDigest : Prop)
    (candidateSetDigest : Prop)
    (activityHeapSnapshot : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brtb_tie_break_guard tieBreakEpochLedger seedDigest
      candidateSetDigest activityHeapSnapshot phaseTrailSnapshot
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _epochH _seedH _candidateH _heapH _phaseTrailH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_brtb_tie_break_guard_validator
    (tieBreakEpochLedger : Prop)
    (seedDigest : Prop)
    (candidateSetDigest : Prop)
    (activityHeapSnapshot : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brtb_tie_break_guard tieBreakEpochLedger seedDigest
      candidateSetDigest activityHeapSnapshot phaseTrailSnapshot
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _epochH _seedH _candidateH _heapH _phaseTrailH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_brtb_tie_break_guard_audit
    (tieBreakEpochLedger : Prop)
    (seedDigest : Prop)
    (candidateSetDigest : Prop)
    (activityHeapSnapshot : Prop)
    (phaseTrailSnapshot : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brtb_tie_break_guard tieBreakEpochLedger seedDigest
      candidateSetDigest activityHeapSnapshot phaseTrailSnapshot
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    auditEvidence :=
  fun guard =>
    guard auditEvidence
      (fun _epochH _seedH _candidateH _heapH _phaseTrailH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_brtb_guard_agreement_intro
    (epochMatch : Prop)
    (seedMatch : Prop)
    (candidateSetMatch : Prop)
    (heapMatch : Prop)
    (phaseTrailMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    epochMatch ->
    seedMatch ->
    candidateSetMatch ->
    heapMatch ->
    phaseTrailMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_brtb_guard_agreement epochMatch seedMatch candidateSetMatch heapMatch
      phaseTrailMatch fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_brtb_tie_break_guard_intro epochMatch seedMatch candidateSetMatch heapMatch
    phaseTrailMatch fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_brtb_accepted_tie_break_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (tieBreakGuidance : Prop) :
    guardEvidence ->
    agreementEvidence ->
    tieBreakGuidance ->
    ay_brtb_accepted_tie_break guardEvidence agreementEvidence
      tieBreakGuidance :=
  fun guardH agreementH guidanceH =>
    ay_brtb_conj_intro guardEvidence
      (ay_brtb_conj agreementEvidence tieBreakGuidance)
      guardH
      (ay_brtb_conj_intro agreementEvidence tieBreakGuidance
        agreementH guidanceH)

theorem ay_brtb_accepted_tie_break_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (tieBreakGuidance : Prop) :
    ay_brtb_accepted_tie_break guardEvidence agreementEvidence
      tieBreakGuidance ->
    guardEvidence :=
  fun accepted =>
    ay_brtb_conj_left guardEvidence
      (ay_brtb_conj agreementEvidence tieBreakGuidance)
      accepted

theorem ay_brtb_accepted_tie_break_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (tieBreakGuidance : Prop) :
    ay_brtb_accepted_tie_break guardEvidence agreementEvidence
      tieBreakGuidance ->
    agreementEvidence :=
  fun accepted =>
    ay_brtb_conj_left agreementEvidence tieBreakGuidance
      (ay_brtb_conj_right guardEvidence
        (ay_brtb_conj agreementEvidence tieBreakGuidance)
        accepted)

theorem ay_brtb_accepted_tie_break_guidance
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (tieBreakGuidance : Prop) :
    ay_brtb_accepted_tie_break guardEvidence agreementEvidence
      tieBreakGuidance ->
    tieBreakGuidance :=
  fun accepted =>
    ay_brtb_conj_right agreementEvidence tieBreakGuidance
      (ay_brtb_conj_right guardEvidence
        (ay_brtb_conj agreementEvidence tieBreakGuidance)
        accepted)

theorem ay_brtb_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_brtb_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_brtb_conj_intro acceptedEvidence
      (ay_brtb_conj outcome formulaTruth)
      acceptedH
      (ay_brtb_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_brtb_public_report_requires_guard
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_brtb_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun public =>
    ay_brtb_conj_left acceptedEvidence
      (ay_brtb_conj outcome formulaTruth)
      public

theorem ay_brtb_no_claim_intro
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_brtb_no_claim diagnostic fallbackPublic :=
  ay_brtb_conj_intro diagnostic fallbackPublic

theorem ay_brtb_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_brtb_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_brtb_conj_right diagnostic fallbackPublic noClaim

theorem ay_brtb_tie_break_epoch_drift_no_claim
    (tieBreakEpochDrift : Prop)
    (fallbackPublic : Prop) :
    tieBreakEpochDrift ->
    fallbackPublic ->
    ay_brtb_no_claim tieBreakEpochDrift fallbackPublic :=
  ay_brtb_no_claim_intro tieBreakEpochDrift fallbackPublic

theorem ay_brtb_seed_digest_mismatch_no_claim
    (seedDigestMismatch : Prop)
    (fallbackPublic : Prop) :
    seedDigestMismatch ->
    fallbackPublic ->
    ay_brtb_no_claim seedDigestMismatch fallbackPublic :=
  ay_brtb_no_claim_intro seedDigestMismatch fallbackPublic

theorem ay_brtb_candidate_set_mismatch_no_claim
    (candidateSetMismatch : Prop)
    (fallbackPublic : Prop) :
    candidateSetMismatch ->
    fallbackPublic ->
    ay_brtb_no_claim candidateSetMismatch fallbackPublic :=
  ay_brtb_no_claim_intro candidateSetMismatch fallbackPublic

theorem ay_brtb_heap_mismatch_no_claim
    (heapMismatch : Prop)
    (fallbackPublic : Prop) :
    heapMismatch -> fallbackPublic -> ay_brtb_no_claim heapMismatch fallbackPublic :=
  ay_brtb_no_claim_intro heapMismatch fallbackPublic

theorem ay_brtb_phase_trail_mismatch_no_claim
    (phaseTrailMismatch : Prop)
    (fallbackPublic : Prop) :
    phaseTrailMismatch ->
    fallbackPublic ->
    ay_brtb_no_claim phaseTrailMismatch fallbackPublic :=
  ay_brtb_no_claim_intro phaseTrailMismatch fallbackPublic

theorem ay_brtb_missing_fallback_no_claim
    (missingFallback : Prop)
    (fallbackPublic : Prop) :
    missingFallback ->
    fallbackPublic ->
    ay_brtb_no_claim missingFallback fallbackPublic :=
  ay_brtb_no_claim_intro missingFallback fallbackPublic

theorem ay_brtb_stale_build_no_claim
    (staleBuild : Prop)
    (fallbackPublic : Prop) :
    staleBuild -> fallbackPublic -> ay_brtb_no_claim staleBuild fallbackPublic :=
  ay_brtb_no_claim_intro staleBuild fallbackPublic

theorem ay_brtb_validator_rejection_no_claim
    (validatorRejection : Prop)
    (fallbackPublic : Prop) :
    validatorRejection ->
    fallbackPublic ->
    ay_brtb_no_claim validatorRejection fallbackPublic :=
  ay_brtb_no_claim_intro validatorRejection fallbackPublic

theorem ay_brtb_audit_contradiction_no_claim
    (auditContradiction : Prop)
    (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_brtb_no_claim auditContradiction fallbackPublic :=
  ay_brtb_no_claim_intro auditContradiction fallbackPublic

theorem ay_brtb_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (recomputedPublic : Prop) :
    ay_brtb_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> recomputedPublic) ->
    recomputedPublic :=
  fun noClaim recompute =>
    recompute (ay_brtb_no_claim_preserves_fallback diagnostic fallbackPublic noClaim)

theorem ay_brtb_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_brtb_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_brtb_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_brtb_accepted_tie_break_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (tieBreakGuidance : Prop)
    (satOutcome : Prop)
    (formulaTruth : Prop) :
    ay_brtb_accepted_tie_break guardEvidence agreementEvidence
      tieBreakGuidance ->
    satOutcome ->
    formulaTruth ->
    ay_brtb_public_report
      (ay_brtb_accepted_tie_break guardEvidence agreementEvidence
        tieBreakGuidance)
      satOutcome
      formulaTruth :=
  fun accepted satH truthH =>
    ay_brtb_public_report_intro
      (ay_brtb_accepted_tie_break guardEvidence agreementEvidence
        tieBreakGuidance)
      satOutcome
      formulaTruth
      accepted
      satH
      truthH

theorem ay_brtb_accepted_tie_break_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (tieBreakGuidance : Prop)
    (unsatOutcome : Prop)
    (formulaTruth : Prop) :
    ay_brtb_accepted_tie_break guardEvidence agreementEvidence
      tieBreakGuidance ->
    unsatOutcome ->
    formulaTruth ->
    ay_brtb_public_report
      (ay_brtb_accepted_tie_break guardEvidence agreementEvidence
        tieBreakGuidance)
      unsatOutcome
      formulaTruth :=
  ay_brtb_accepted_tie_break_guides_sat guardEvidence agreementEvidence
    tieBreakGuidance unsatOutcome formulaTruth

theorem ay_brtb_accepted_tie_break_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (tieBreakGuidance : Prop)
    (solverTruth : Prop)
    (publicTruth : Prop) :
    ay_brtb_accepted_tie_break guardEvidence agreementEvidence
      tieBreakGuidance ->
    ay_brtb_equisat solverTruth publicTruth ->
    solverTruth ->
    publicTruth :=
  fun _accepted outcome solverH =>
    ay_brtb_equisat_forward solverTruth publicTruth outcome solverH

theorem ay_brtb_tie_break_does_not_change_truth
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (tieBreakGuidance : Prop)
    (beforeTruth : Prop)
    (afterTruth : Prop) :
    ay_brtb_accepted_tie_break guardEvidence agreementEvidence
      tieBreakGuidance ->
    ay_brtb_equisat beforeTruth afterTruth ->
    ay_brtb_equisat afterTruth beforeTruth :=
  fun _accepted eqsat =>
    ay_brtb_equisat_intro afterTruth beforeTruth
      (ay_brtb_equisat_backward beforeTruth afterTruth eqsat)
      (ay_brtb_equisat_forward beforeTruth afterTruth eqsat)
