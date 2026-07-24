-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Activity heap rebuild replay guard skeleton for sequential-main SAT. Heap
-- rebuilding is modeled as performance guidance: public SAT/UNSAT claims still
-- require replay, fallback, build, validator, and audit evidence.

def ay_bahr_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bahr_equisat (before : Prop) (after : Prop) : Prop :=
  ay_bahr_conj (before -> after) (after -> before)

def ay_bahr_rebuild_guard
    (rankingSnapshot : Prop)
    (heapOrderReplay : Prop)
    (phaseTrailCompatible : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) : Prop :=
  forall result : Prop,
    (rankingSnapshot ->
      heapOrderReplay ->
      phaseTrailCompatible ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditEvidence ->
      result) ->
    result

def ay_bahr_guard_agreement
    (rankingMatch : Prop)
    (heapOrderMatch : Prop)
    (phaseTrailMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_bahr_rebuild_guard rankingMatch heapOrderMatch phaseTrailMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

def ay_bahr_accepted_rebuild
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (heapGuidance : Prop) : Prop :=
  ay_bahr_conj guardEvidence (ay_bahr_conj agreementEvidence heapGuidance)

def ay_bahr_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_bahr_conj acceptedEvidence (ay_bahr_conj outcome formulaTruth)

def ay_bahr_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_bahr_conj diagnostic fallbackPublic

theorem ay_bahr_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_bahr_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_bahr_conj_left (left : Prop) (right : Prop) :
    ay_bahr_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_bahr_conj_right (left : Prop) (right : Prop) :
    ay_bahr_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_bahr_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_bahr_equisat before after :=
  fun forward backward =>
    ay_bahr_conj_intro (before -> after) (after -> before) forward backward

theorem ay_bahr_equisat_forward (before : Prop) (after : Prop) :
    ay_bahr_equisat before after -> before -> after :=
  fun eqsat =>
    ay_bahr_conj_left (before -> after) (after -> before) eqsat

theorem ay_bahr_equisat_backward (before : Prop) (after : Prop) :
    ay_bahr_equisat before after -> after -> before :=
  fun eqsat =>
    ay_bahr_conj_right (before -> after) (after -> before) eqsat

theorem ay_bahr_rebuild_guard_intro
    (rankingSnapshot : Prop)
    (heapOrderReplay : Prop)
    (phaseTrailCompatible : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    rankingSnapshot ->
    heapOrderReplay ->
    phaseTrailCompatible ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditEvidence ->
    ay_bahr_rebuild_guard rankingSnapshot heapOrderReplay phaseTrailCompatible
      fallbackBaseline buildEvidence validatorGate auditEvidence :=
  fun rankingH heapH phaseTrailH fallbackH buildH validatorH auditH
      result build =>
    build rankingH heapH phaseTrailH fallbackH buildH validatorH auditH

theorem ay_bahr_rebuild_guard_ranking
    (rankingSnapshot : Prop)
    (heapOrderReplay : Prop)
    (phaseTrailCompatible : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bahr_rebuild_guard rankingSnapshot heapOrderReplay phaseTrailCompatible
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    rankingSnapshot :=
  fun guard =>
    guard rankingSnapshot
      (fun rankingH _heapH _phaseTrailH _fallbackH _buildH _validatorH
          _auditH => rankingH)

theorem ay_bahr_rebuild_guard_heap_order
    (rankingSnapshot : Prop)
    (heapOrderReplay : Prop)
    (phaseTrailCompatible : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bahr_rebuild_guard rankingSnapshot heapOrderReplay phaseTrailCompatible
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    heapOrderReplay :=
  fun guard =>
    guard heapOrderReplay
      (fun _rankingH heapH _phaseTrailH _fallbackH _buildH _validatorH
          _auditH => heapH)

theorem ay_bahr_rebuild_guard_phase_trail
    (rankingSnapshot : Prop)
    (heapOrderReplay : Prop)
    (phaseTrailCompatible : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bahr_rebuild_guard rankingSnapshot heapOrderReplay phaseTrailCompatible
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    phaseTrailCompatible :=
  fun guard =>
    guard phaseTrailCompatible
      (fun _rankingH _heapH phaseTrailH _fallbackH _buildH _validatorH
          _auditH => phaseTrailH)

theorem ay_bahr_rebuild_guard_fallback
    (rankingSnapshot : Prop)
    (heapOrderReplay : Prop)
    (phaseTrailCompatible : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bahr_rebuild_guard rankingSnapshot heapOrderReplay phaseTrailCompatible
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _rankingH _heapH _phaseTrailH fallbackH _buildH _validatorH
          _auditH => fallbackH)

theorem ay_bahr_rebuild_guard_build
    (rankingSnapshot : Prop)
    (heapOrderReplay : Prop)
    (phaseTrailCompatible : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bahr_rebuild_guard rankingSnapshot heapOrderReplay phaseTrailCompatible
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _rankingH _heapH _phaseTrailH _fallbackH buildH _validatorH
          _auditH => buildH)

theorem ay_bahr_rebuild_guard_validator
    (rankingSnapshot : Prop)
    (heapOrderReplay : Prop)
    (phaseTrailCompatible : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bahr_rebuild_guard rankingSnapshot heapOrderReplay phaseTrailCompatible
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _rankingH _heapH _phaseTrailH _fallbackH _buildH validatorH
          _auditH => validatorH)

theorem ay_bahr_rebuild_guard_audit
    (rankingSnapshot : Prop)
    (heapOrderReplay : Prop)
    (phaseTrailCompatible : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bahr_rebuild_guard rankingSnapshot heapOrderReplay phaseTrailCompatible
      fallbackBaseline buildEvidence validatorGate auditEvidence ->
    auditEvidence :=
  fun guard =>
    guard auditEvidence
      (fun _rankingH _heapH _phaseTrailH _fallbackH _buildH _validatorH
          auditH => auditH)

theorem ay_bahr_guard_agreement_intro
    (rankingMatch : Prop)
    (heapOrderMatch : Prop)
    (phaseTrailMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    rankingMatch ->
    heapOrderMatch ->
    phaseTrailMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_bahr_guard_agreement rankingMatch heapOrderMatch phaseTrailMatch
      fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_bahr_rebuild_guard_intro rankingMatch heapOrderMatch phaseTrailMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_bahr_accepted_rebuild_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (heapGuidance : Prop) :
    guardEvidence ->
    agreementEvidence ->
    heapGuidance ->
    ay_bahr_accepted_rebuild guardEvidence agreementEvidence heapGuidance :=
  fun guardH agreementH guidanceH =>
    ay_bahr_conj_intro guardEvidence
      (ay_bahr_conj agreementEvidence heapGuidance)
      guardH
      (ay_bahr_conj_intro agreementEvidence heapGuidance agreementH guidanceH)

theorem ay_bahr_accepted_rebuild_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (heapGuidance : Prop) :
    ay_bahr_accepted_rebuild guardEvidence agreementEvidence heapGuidance ->
    guardEvidence :=
  fun accepted =>
    ay_bahr_conj_left guardEvidence
      (ay_bahr_conj agreementEvidence heapGuidance)
      accepted

theorem ay_bahr_accepted_rebuild_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (heapGuidance : Prop) :
    ay_bahr_accepted_rebuild guardEvidence agreementEvidence heapGuidance ->
    agreementEvidence :=
  fun accepted =>
    ay_bahr_conj_left agreementEvidence heapGuidance
      (ay_bahr_conj_right guardEvidence
        (ay_bahr_conj agreementEvidence heapGuidance)
        accepted)

theorem ay_bahr_accepted_rebuild_guidance
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (heapGuidance : Prop) :
    ay_bahr_accepted_rebuild guardEvidence agreementEvidence heapGuidance ->
    heapGuidance :=
  fun accepted =>
    ay_bahr_conj_right agreementEvidence heapGuidance
      (ay_bahr_conj_right guardEvidence
        (ay_bahr_conj agreementEvidence heapGuidance)
        accepted)

theorem ay_bahr_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_bahr_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_bahr_conj_intro acceptedEvidence
      (ay_bahr_conj outcome formulaTruth)
      acceptedH
      (ay_bahr_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_bahr_public_report_requires_guard
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_bahr_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun public =>
    ay_bahr_conj_left acceptedEvidence
      (ay_bahr_conj outcome formulaTruth)
      public

theorem ay_bahr_no_claim_intro
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_bahr_no_claim diagnostic fallbackPublic :=
  ay_bahr_conj_intro diagnostic fallbackPublic

theorem ay_bahr_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_bahr_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_bahr_conj_right diagnostic fallbackPublic noClaim

theorem ay_bahr_ranking_drift_no_claim
    (rankingDrift : Prop)
    (fallbackPublic : Prop) :
    rankingDrift ->
    fallbackPublic ->
    ay_bahr_no_claim rankingDrift fallbackPublic :=
  ay_bahr_no_claim_intro rankingDrift fallbackPublic

theorem ay_bahr_heap_order_mismatch_no_claim
    (heapOrderMismatch : Prop)
    (fallbackPublic : Prop) :
    heapOrderMismatch ->
    fallbackPublic ->
    ay_bahr_no_claim heapOrderMismatch fallbackPublic :=
  ay_bahr_no_claim_intro heapOrderMismatch fallbackPublic

theorem ay_bahr_phase_mismatch_no_claim
    (phaseMismatch : Prop)
    (fallbackPublic : Prop) :
    phaseMismatch ->
    fallbackPublic ->
    ay_bahr_no_claim phaseMismatch fallbackPublic :=
  ay_bahr_no_claim_intro phaseMismatch fallbackPublic

theorem ay_bahr_stale_build_no_claim
    (staleBuild : Prop)
    (fallbackPublic : Prop) :
    staleBuild -> fallbackPublic -> ay_bahr_no_claim staleBuild fallbackPublic :=
  ay_bahr_no_claim_intro staleBuild fallbackPublic

theorem ay_bahr_audit_contradiction_no_claim
    (auditContradiction : Prop)
    (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_bahr_no_claim auditContradiction fallbackPublic :=
  ay_bahr_no_claim_intro auditContradiction fallbackPublic

theorem ay_bahr_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (recomputedPublic : Prop) :
    ay_bahr_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> recomputedPublic) ->
    recomputedPublic :=
  fun noClaim recompute =>
    recompute (ay_bahr_no_claim_preserves_fallback diagnostic fallbackPublic noClaim)

theorem ay_bahr_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_bahr_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_bahr_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_bahr_accepted_rebuild_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (heapGuidance : Prop)
    (satOutcome : Prop)
    (formulaTruth : Prop) :
    ay_bahr_accepted_rebuild guardEvidence agreementEvidence heapGuidance ->
    satOutcome ->
    formulaTruth ->
    ay_bahr_public_report
      (ay_bahr_accepted_rebuild guardEvidence agreementEvidence heapGuidance)
      satOutcome
      formulaTruth :=
  fun accepted satH truthH =>
    ay_bahr_public_report_intro
      (ay_bahr_accepted_rebuild guardEvidence agreementEvidence heapGuidance)
      satOutcome
      formulaTruth
      accepted
      satH
      truthH

theorem ay_bahr_accepted_rebuild_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (heapGuidance : Prop)
    (unsatOutcome : Prop)
    (formulaTruth : Prop) :
    ay_bahr_accepted_rebuild guardEvidence agreementEvidence heapGuidance ->
    unsatOutcome ->
    formulaTruth ->
    ay_bahr_public_report
      (ay_bahr_accepted_rebuild guardEvidence agreementEvidence heapGuidance)
      unsatOutcome
      formulaTruth :=
  ay_bahr_accepted_rebuild_guides_sat guardEvidence agreementEvidence
    heapGuidance unsatOutcome formulaTruth

theorem ay_bahr_accepted_rebuild_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (heapGuidance : Prop)
    (solverTruth : Prop)
    (publicTruth : Prop) :
    ay_bahr_accepted_rebuild guardEvidence agreementEvidence heapGuidance ->
    ay_bahr_equisat solverTruth publicTruth ->
    solverTruth ->
    publicTruth :=
  fun _accepted outcome solverH =>
    ay_bahr_equisat_forward solverTruth publicTruth outcome solverH

theorem ay_bahr_heap_rebuild_does_not_change_truth
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (heapGuidance : Prop)
    (beforeTruth : Prop)
    (afterTruth : Prop) :
    ay_bahr_accepted_rebuild guardEvidence agreementEvidence heapGuidance ->
    ay_bahr_equisat beforeTruth afterTruth ->
    ay_bahr_equisat afterTruth beforeTruth :=
  fun _accepted eqsat =>
    ay_bahr_equisat_intro afterTruth beforeTruth
      (ay_bahr_equisat_backward beforeTruth afterTruth eqsat)
      (ay_bahr_equisat_forward beforeTruth afterTruth eqsat)
