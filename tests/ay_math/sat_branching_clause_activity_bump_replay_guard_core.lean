-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Clause/activity bump replay guard skeleton for sequential-main SAT. Activity
-- bump replay is an admissible heuristic only when bumps, decay epochs, heap
-- ranking, phase/trail compatibility, fallback, build, validator, and audit
-- evidence agree.

def ay_bcab_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bcab_equisat (before : Prop) (after : Prop) : Prop :=
  ay_bcab_conj (before -> after) (after -> before)

def ay_bcab_replay_guard
    (activityBumps : Prop)
    (decayEpochs : Prop)
    (heapRanking : Prop)
    (phaseTrailCompatible : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) : Prop :=
  forall result : Prop,
    (activityBumps ->
      decayEpochs ->
      heapRanking ->
      phaseTrailCompatible ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditEvidence ->
      result) ->
    result

def ay_bcab_guard_agreement
    (bumpMatch : Prop)
    (decayMatch : Prop)
    (rankingMatch : Prop)
    (phaseTrailMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_bcab_replay_guard bumpMatch decayMatch rankingMatch phaseTrailMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

def ay_bcab_accepted_replay
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (bumpGuidance : Prop) : Prop :=
  ay_bcab_conj guardEvidence (ay_bcab_conj agreementEvidence bumpGuidance)

def ay_bcab_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_bcab_conj acceptedEvidence (ay_bcab_conj outcome formulaTruth)

def ay_bcab_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_bcab_conj diagnostic fallbackPublic

theorem ay_bcab_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_bcab_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_bcab_conj_left (left : Prop) (right : Prop) :
    ay_bcab_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_bcab_conj_right (left : Prop) (right : Prop) :
    ay_bcab_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_bcab_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_bcab_equisat before after :=
  fun forward backward =>
    ay_bcab_conj_intro (before -> after) (after -> before) forward backward

theorem ay_bcab_equisat_forward (before : Prop) (after : Prop) :
    ay_bcab_equisat before after -> before -> after :=
  fun eqsat =>
    ay_bcab_conj_left (before -> after) (after -> before) eqsat

theorem ay_bcab_equisat_backward (before : Prop) (after : Prop) :
    ay_bcab_equisat before after -> after -> before :=
  fun eqsat =>
    ay_bcab_conj_right (before -> after) (after -> before) eqsat

theorem ay_bcab_replay_guard_intro
    (activityBumps : Prop)
    (decayEpochs : Prop)
    (heapRanking : Prop)
    (phaseTrailCompatible : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    activityBumps ->
    decayEpochs ->
    heapRanking ->
    phaseTrailCompatible ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditEvidence ->
    ay_bcab_replay_guard activityBumps decayEpochs heapRanking
      phaseTrailCompatible fallbackBaseline buildEvidence validatorGate
      auditEvidence :=
  fun bumpH decayH rankingH phaseTrailH fallbackH buildH validatorH auditH
      result build =>
    build bumpH decayH rankingH phaseTrailH fallbackH buildH validatorH auditH

theorem ay_bcab_replay_guard_bumps
    (activityBumps : Prop)
    (decayEpochs : Prop)
    (heapRanking : Prop)
    (phaseTrailCompatible : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcab_replay_guard activityBumps decayEpochs heapRanking
      phaseTrailCompatible fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    activityBumps :=
  fun guard =>
    guard activityBumps
      (fun bumpH _decayH _rankingH _phaseTrailH _fallbackH _buildH
          _validatorH _auditH => bumpH)

theorem ay_bcab_replay_guard_decay
    (activityBumps : Prop)
    (decayEpochs : Prop)
    (heapRanking : Prop)
    (phaseTrailCompatible : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcab_replay_guard activityBumps decayEpochs heapRanking
      phaseTrailCompatible fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    decayEpochs :=
  fun guard =>
    guard decayEpochs
      (fun _bumpH decayH _rankingH _phaseTrailH _fallbackH _buildH
          _validatorH _auditH => decayH)

theorem ay_bcab_replay_guard_ranking
    (activityBumps : Prop)
    (decayEpochs : Prop)
    (heapRanking : Prop)
    (phaseTrailCompatible : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcab_replay_guard activityBumps decayEpochs heapRanking
      phaseTrailCompatible fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    heapRanking :=
  fun guard =>
    guard heapRanking
      (fun _bumpH _decayH rankingH _phaseTrailH _fallbackH _buildH
          _validatorH _auditH => rankingH)

theorem ay_bcab_replay_guard_phase_trail
    (activityBumps : Prop)
    (decayEpochs : Prop)
    (heapRanking : Prop)
    (phaseTrailCompatible : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcab_replay_guard activityBumps decayEpochs heapRanking
      phaseTrailCompatible fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    phaseTrailCompatible :=
  fun guard =>
    guard phaseTrailCompatible
      (fun _bumpH _decayH _rankingH phaseTrailH _fallbackH _buildH
          _validatorH _auditH => phaseTrailH)

theorem ay_bcab_replay_guard_fallback
    (activityBumps : Prop)
    (decayEpochs : Prop)
    (heapRanking : Prop)
    (phaseTrailCompatible : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcab_replay_guard activityBumps decayEpochs heapRanking
      phaseTrailCompatible fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _bumpH _decayH _rankingH _phaseTrailH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_bcab_replay_guard_build
    (activityBumps : Prop)
    (decayEpochs : Prop)
    (heapRanking : Prop)
    (phaseTrailCompatible : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcab_replay_guard activityBumps decayEpochs heapRanking
      phaseTrailCompatible fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _bumpH _decayH _rankingH _phaseTrailH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_bcab_replay_guard_validator
    (activityBumps : Prop)
    (decayEpochs : Prop)
    (heapRanking : Prop)
    (phaseTrailCompatible : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcab_replay_guard activityBumps decayEpochs heapRanking
      phaseTrailCompatible fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _bumpH _decayH _rankingH _phaseTrailH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_bcab_replay_guard_audit
    (activityBumps : Prop)
    (decayEpochs : Prop)
    (heapRanking : Prop)
    (phaseTrailCompatible : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_bcab_replay_guard activityBumps decayEpochs heapRanking
      phaseTrailCompatible fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    auditEvidence :=
  fun guard =>
    guard auditEvidence
      (fun _bumpH _decayH _rankingH _phaseTrailH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_bcab_guard_agreement_intro
    (bumpMatch : Prop)
    (decayMatch : Prop)
    (rankingMatch : Prop)
    (phaseTrailMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    bumpMatch ->
    decayMatch ->
    rankingMatch ->
    phaseTrailMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_bcab_guard_agreement bumpMatch decayMatch rankingMatch phaseTrailMatch
      fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_bcab_replay_guard_intro bumpMatch decayMatch rankingMatch phaseTrailMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_bcab_accepted_replay_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (bumpGuidance : Prop) :
    guardEvidence ->
    agreementEvidence ->
    bumpGuidance ->
    ay_bcab_accepted_replay guardEvidence agreementEvidence bumpGuidance :=
  fun guardH agreementH guidanceH =>
    ay_bcab_conj_intro guardEvidence
      (ay_bcab_conj agreementEvidence bumpGuidance)
      guardH
      (ay_bcab_conj_intro agreementEvidence bumpGuidance agreementH guidanceH)

theorem ay_bcab_accepted_replay_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (bumpGuidance : Prop) :
    ay_bcab_accepted_replay guardEvidence agreementEvidence bumpGuidance ->
    guardEvidence :=
  fun accepted =>
    ay_bcab_conj_left guardEvidence
      (ay_bcab_conj agreementEvidence bumpGuidance)
      accepted

theorem ay_bcab_accepted_replay_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (bumpGuidance : Prop) :
    ay_bcab_accepted_replay guardEvidence agreementEvidence bumpGuidance ->
    agreementEvidence :=
  fun accepted =>
    ay_bcab_conj_left agreementEvidence bumpGuidance
      (ay_bcab_conj_right guardEvidence
        (ay_bcab_conj agreementEvidence bumpGuidance)
        accepted)

theorem ay_bcab_accepted_replay_guidance
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (bumpGuidance : Prop) :
    ay_bcab_accepted_replay guardEvidence agreementEvidence bumpGuidance ->
    bumpGuidance :=
  fun accepted =>
    ay_bcab_conj_right agreementEvidence bumpGuidance
      (ay_bcab_conj_right guardEvidence
        (ay_bcab_conj agreementEvidence bumpGuidance)
        accepted)

theorem ay_bcab_public_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_bcab_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_bcab_conj_intro acceptedEvidence
      (ay_bcab_conj outcome formulaTruth)
      acceptedH
      (ay_bcab_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_bcab_public_report_requires_guard
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_bcab_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun public =>
    ay_bcab_conj_left acceptedEvidence
      (ay_bcab_conj outcome formulaTruth)
      public

theorem ay_bcab_no_claim_intro
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_bcab_no_claim diagnostic fallbackPublic :=
  ay_bcab_conj_intro diagnostic fallbackPublic

theorem ay_bcab_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_bcab_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim => ay_bcab_conj_right diagnostic fallbackPublic noClaim

theorem ay_bcab_bump_drift_no_claim
    (bumpDrift : Prop)
    (fallbackPublic : Prop) :
    bumpDrift -> fallbackPublic -> ay_bcab_no_claim bumpDrift fallbackPublic :=
  ay_bcab_no_claim_intro bumpDrift fallbackPublic

theorem ay_bcab_decay_mismatch_no_claim
    (decayMismatch : Prop)
    (fallbackPublic : Prop) :
    decayMismatch ->
    fallbackPublic ->
    ay_bcab_no_claim decayMismatch fallbackPublic :=
  ay_bcab_no_claim_intro decayMismatch fallbackPublic

theorem ay_bcab_ranking_drift_no_claim
    (rankingDrift : Prop)
    (fallbackPublic : Prop) :
    rankingDrift ->
    fallbackPublic ->
    ay_bcab_no_claim rankingDrift fallbackPublic :=
  ay_bcab_no_claim_intro rankingDrift fallbackPublic

theorem ay_bcab_stale_build_no_claim
    (staleBuild : Prop)
    (fallbackPublic : Prop) :
    staleBuild -> fallbackPublic -> ay_bcab_no_claim staleBuild fallbackPublic :=
  ay_bcab_no_claim_intro staleBuild fallbackPublic

theorem ay_bcab_audit_contradiction_no_claim
    (auditContradiction : Prop)
    (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_bcab_no_claim auditContradiction fallbackPublic :=
  ay_bcab_no_claim_intro auditContradiction fallbackPublic

theorem ay_bcab_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (recomputedPublic : Prop) :
    ay_bcab_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> recomputedPublic) ->
    recomputedPublic :=
  fun noClaim recompute =>
    recompute (ay_bcab_no_claim_preserves_fallback diagnostic fallbackPublic noClaim)

theorem ay_bcab_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_bcab_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_bcab_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_bcab_accepted_replay_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (bumpGuidance : Prop)
    (satOutcome : Prop)
    (formulaTruth : Prop) :
    ay_bcab_accepted_replay guardEvidence agreementEvidence bumpGuidance ->
    satOutcome ->
    formulaTruth ->
    ay_bcab_public_report
      (ay_bcab_accepted_replay guardEvidence agreementEvidence bumpGuidance)
      satOutcome
      formulaTruth :=
  fun accepted satH truthH =>
    ay_bcab_public_report_intro
      (ay_bcab_accepted_replay guardEvidence agreementEvidence bumpGuidance)
      satOutcome
      formulaTruth
      accepted
      satH
      truthH

theorem ay_bcab_accepted_replay_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (bumpGuidance : Prop)
    (unsatOutcome : Prop)
    (formulaTruth : Prop) :
    ay_bcab_accepted_replay guardEvidence agreementEvidence bumpGuidance ->
    unsatOutcome ->
    formulaTruth ->
    ay_bcab_public_report
      (ay_bcab_accepted_replay guardEvidence agreementEvidence bumpGuidance)
      unsatOutcome
      formulaTruth :=
  ay_bcab_accepted_replay_guides_sat guardEvidence agreementEvidence
    bumpGuidance unsatOutcome formulaTruth

theorem ay_bcab_accepted_replay_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (bumpGuidance : Prop)
    (solverTruth : Prop)
    (publicTruth : Prop) :
    ay_bcab_accepted_replay guardEvidence agreementEvidence bumpGuidance ->
    ay_bcab_equisat solverTruth publicTruth ->
    solverTruth ->
    publicTruth :=
  fun _accepted outcome solverH =>
    ay_bcab_equisat_forward solverTruth publicTruth outcome solverH

theorem ay_bcab_bump_replay_does_not_change_truth
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (bumpGuidance : Prop)
    (beforeTruth : Prop)
    (afterTruth : Prop) :
    ay_bcab_accepted_replay guardEvidence agreementEvidence bumpGuidance ->
    ay_bcab_equisat beforeTruth afterTruth ->
    ay_bcab_equisat afterTruth beforeTruth :=
  fun _accepted eqsat =>
    ay_bcab_equisat_intro afterTruth beforeTruth
      (ay_bcab_equisat_backward beforeTruth afterTruth eqsat)
      (ay_bcab_equisat_forward beforeTruth afterTruth eqsat)
