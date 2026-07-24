-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Restart/phase decay-window guard soundness skeleton for sequential-main SAT.
-- The package is intentionally propositional: it records which certificate
-- gates must agree before ay may treat phase saving, restart ledgers, and
-- decay-window activity rankings as performance guidance.

def ay_brpd_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_brpd_disj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_brpd_equisat (before : Prop) (after : Prop) : Prop :=
  ay_brpd_conj (before -> after) (after -> before)

def ay_brpd_decay_window_guard
    (phaseSaving : Prop)
    (decayWindowState : Prop)
    (restartLedger : Prop)
    (activityRankingReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) : Prop :=
  forall result : Prop,
    (phaseSaving ->
      decayWindowState ->
      restartLedger ->
      activityRankingReplay ->
      fallbackBaseline ->
      buildEvidence ->
      validatorGate ->
      auditEvidence ->
      result) ->
    result

def ay_brpd_guard_agreement
    (phaseMatch : Prop)
    (windowMatch : Prop)
    (restartMatch : Prop)
    (rankingMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) : Prop :=
  ay_brpd_decay_window_guard phaseMatch windowMatch restartMatch rankingMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

def ay_brpd_accepted_hint
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayWindowHint : Prop) : Prop :=
  ay_brpd_conj guardEvidence (ay_brpd_conj agreementEvidence decayWindowHint)

def ay_brpd_outcome (solverTruth : Prop) (publicTruth : Prop) : Prop :=
  ay_brpd_equisat solverTruth publicTruth

def ay_brpd_public_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) : Prop :=
  ay_brpd_conj acceptedEvidence (ay_brpd_conj outcome formulaTruth)

def ay_brpd_accepted_report
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop)
    (published : Prop) : Prop :=
  ay_brpd_conj
    (ay_brpd_public_report acceptedEvidence outcome formulaTruth)
    published

def ay_brpd_no_claim (diagnostic : Prop) (fallbackPublic : Prop) : Prop :=
  ay_brpd_conj diagnostic fallbackPublic

theorem ay_brpd_conj_intro (left : Prop) (right : Prop) :
    left -> right -> ay_brpd_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_brpd_conj_left (left : Prop) (right : Prop) :
    ay_brpd_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_brpd_conj_right (left : Prop) (right : Prop) :
    ay_brpd_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_brpd_disj_left (left : Prop) (right : Prop) :
    left -> ay_brpd_disj left right :=
  fun leftH result leftBuild _rightBuild => leftBuild leftH

theorem ay_brpd_disj_right (left : Prop) (right : Prop) :
    right -> ay_brpd_disj left right :=
  fun rightH result _leftBuild rightBuild => rightBuild rightH

theorem ay_brpd_equisat_intro (before : Prop) (after : Prop) :
    (before -> after) -> (after -> before) -> ay_brpd_equisat before after :=
  fun forward backward =>
    ay_brpd_conj_intro (before -> after) (after -> before) forward backward

theorem ay_brpd_equisat_forward (before : Prop) (after : Prop) :
    ay_brpd_equisat before after -> before -> after :=
  fun eqsat =>
    ay_brpd_conj_left (before -> after) (after -> before) eqsat

theorem ay_brpd_equisat_backward (before : Prop) (after : Prop) :
    ay_brpd_equisat before after -> after -> before :=
  fun eqsat =>
    ay_brpd_conj_right (before -> after) (after -> before) eqsat

theorem ay_brpd_decay_window_guard_intro
    (phaseSaving : Prop)
    (decayWindowState : Prop)
    (restartLedger : Prop)
    (activityRankingReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    phaseSaving ->
    decayWindowState ->
    restartLedger ->
    activityRankingReplay ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditEvidence ->
    ay_brpd_decay_window_guard phaseSaving decayWindowState restartLedger
      activityRankingReplay fallbackBaseline buildEvidence validatorGate
      auditEvidence :=
  fun phaseH windowH restartH rankingH fallbackH buildH validatorH auditH
      result build =>
    build phaseH windowH restartH rankingH fallbackH buildH validatorH auditH

theorem ay_brpd_decay_window_guard_phase
    (phaseSaving : Prop)
    (decayWindowState : Prop)
    (restartLedger : Prop)
    (activityRankingReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brpd_decay_window_guard phaseSaving decayWindowState restartLedger
      activityRankingReplay fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    phaseSaving :=
  fun guard =>
    guard phaseSaving
      (fun phaseH _windowH _restartH _rankingH _fallbackH _buildH
          _validatorH _auditH => phaseH)

theorem ay_brpd_decay_window_guard_window
    (phaseSaving : Prop)
    (decayWindowState : Prop)
    (restartLedger : Prop)
    (activityRankingReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brpd_decay_window_guard phaseSaving decayWindowState restartLedger
      activityRankingReplay fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    decayWindowState :=
  fun guard =>
    guard decayWindowState
      (fun _phaseH windowH _restartH _rankingH _fallbackH _buildH
          _validatorH _auditH => windowH)

theorem ay_brpd_decay_window_guard_restart
    (phaseSaving : Prop)
    (decayWindowState : Prop)
    (restartLedger : Prop)
    (activityRankingReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brpd_decay_window_guard phaseSaving decayWindowState restartLedger
      activityRankingReplay fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    restartLedger :=
  fun guard =>
    guard restartLedger
      (fun _phaseH _windowH restartH _rankingH _fallbackH _buildH
          _validatorH _auditH => restartH)

theorem ay_brpd_decay_window_guard_ranking
    (phaseSaving : Prop)
    (decayWindowState : Prop)
    (restartLedger : Prop)
    (activityRankingReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brpd_decay_window_guard phaseSaving decayWindowState restartLedger
      activityRankingReplay fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    activityRankingReplay :=
  fun guard =>
    guard activityRankingReplay
      (fun _phaseH _windowH _restartH rankingH _fallbackH _buildH
          _validatorH _auditH => rankingH)

theorem ay_brpd_decay_window_guard_fallback
    (phaseSaving : Prop)
    (decayWindowState : Prop)
    (restartLedger : Prop)
    (activityRankingReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brpd_decay_window_guard phaseSaving decayWindowState restartLedger
      activityRankingReplay fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _phaseH _windowH _restartH _rankingH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_brpd_decay_window_guard_build
    (phaseSaving : Prop)
    (decayWindowState : Prop)
    (restartLedger : Prop)
    (activityRankingReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brpd_decay_window_guard phaseSaving decayWindowState restartLedger
      activityRankingReplay fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _phaseH _windowH _restartH _rankingH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_brpd_decay_window_guard_validator
    (phaseSaving : Prop)
    (decayWindowState : Prop)
    (restartLedger : Prop)
    (activityRankingReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brpd_decay_window_guard phaseSaving decayWindowState restartLedger
      activityRankingReplay fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _phaseH _windowH _restartH _rankingH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_brpd_decay_window_guard_audit
    (phaseSaving : Prop)
    (decayWindowState : Prop)
    (restartLedger : Prop)
    (activityRankingReplay : Prop)
    (fallbackBaseline : Prop)
    (buildEvidence : Prop)
    (validatorGate : Prop)
    (auditEvidence : Prop) :
    ay_brpd_decay_window_guard phaseSaving decayWindowState restartLedger
      activityRankingReplay fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    auditEvidence :=
  fun guard =>
    guard auditEvidence
      (fun _phaseH _windowH _restartH _rankingH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_brpd_guard_agreement_intro
    (phaseMatch : Prop)
    (windowMatch : Prop)
    (restartMatch : Prop)
    (rankingMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    phaseMatch ->
    windowMatch ->
    restartMatch ->
    rankingMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_brpd_guard_agreement phaseMatch windowMatch restartMatch rankingMatch
      fallbackMatch buildMatch validatorAccepts auditMatch :=
  ay_brpd_decay_window_guard_intro phaseMatch windowMatch restartMatch
    rankingMatch fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_brpd_guard_agreement_phase
    (phaseMatch : Prop)
    (windowMatch : Prop)
    (restartMatch : Prop)
    (rankingMatch : Prop)
    (fallbackMatch : Prop)
    (buildMatch : Prop)
    (validatorAccepts : Prop)
    (auditMatch : Prop) :
    ay_brpd_guard_agreement phaseMatch windowMatch restartMatch rankingMatch
      fallbackMatch buildMatch validatorAccepts auditMatch ->
    phaseMatch :=
  ay_brpd_decay_window_guard_phase phaseMatch windowMatch restartMatch
    rankingMatch fallbackMatch buildMatch validatorAccepts auditMatch

theorem ay_brpd_accepted_hint_intro
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayWindowHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    decayWindowHint ->
    ay_brpd_accepted_hint guardEvidence agreementEvidence decayWindowHint :=
  fun guardH agreementH hintH =>
    ay_brpd_conj_intro guardEvidence
      (ay_brpd_conj agreementEvidence decayWindowHint)
      guardH
      (ay_brpd_conj_intro agreementEvidence decayWindowHint agreementH hintH)

theorem ay_brpd_accepted_hint_guard
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayWindowHint : Prop) :
    ay_brpd_accepted_hint guardEvidence agreementEvidence decayWindowHint ->
    guardEvidence :=
  fun accepted =>
    ay_brpd_conj_left guardEvidence
      (ay_brpd_conj agreementEvidence decayWindowHint)
      accepted

theorem ay_brpd_accepted_hint_agreement
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayWindowHint : Prop) :
    ay_brpd_accepted_hint guardEvidence agreementEvidence decayWindowHint ->
    agreementEvidence :=
  fun accepted =>
    ay_brpd_conj_left agreementEvidence decayWindowHint
      (ay_brpd_conj_right guardEvidence
        (ay_brpd_conj agreementEvidence decayWindowHint)
        accepted)

theorem ay_brpd_accepted_hint_guidance
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayWindowHint : Prop) :
    ay_brpd_accepted_hint guardEvidence agreementEvidence decayWindowHint ->
    decayWindowHint :=
  fun accepted =>
    ay_brpd_conj_right agreementEvidence decayWindowHint
      (ay_brpd_conj_right guardEvidence
        (ay_brpd_conj agreementEvidence decayWindowHint)
        accepted)

theorem ay_brpd_public_sat_report
    (acceptedEvidence : Prop)
    (satOutcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_brpd_public_report acceptedEvidence satOutcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_brpd_conj_intro acceptedEvidence
      (ay_brpd_conj satOutcome formulaTruth)
      acceptedH
      (ay_brpd_conj_intro satOutcome formulaTruth outcomeH truthH)

theorem ay_brpd_public_unsat_report
    (acceptedEvidence : Prop)
    (unsatOutcome : Prop)
    (formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_brpd_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_brpd_public_sat_report acceptedEvidence unsatOutcome formulaTruth

theorem ay_brpd_public_report_requires_guard
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop) :
    ay_brpd_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun public =>
    ay_brpd_conj_left acceptedEvidence
      (ay_brpd_conj outcome formulaTruth)
      public

theorem ay_brpd_accepted_report_intro
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop)
    (published : Prop) :
    ay_brpd_public_report acceptedEvidence outcome formulaTruth ->
    published ->
    ay_brpd_accepted_report acceptedEvidence outcome formulaTruth published :=
  fun publicH publishedH =>
    ay_brpd_conj_intro
      (ay_brpd_public_report acceptedEvidence outcome formulaTruth)
      published
      publicH
      publishedH

theorem ay_brpd_accepted_report_public
    (acceptedEvidence : Prop)
    (outcome : Prop)
    (formulaTruth : Prop)
    (published : Prop) :
    ay_brpd_accepted_report acceptedEvidence outcome formulaTruth published ->
    ay_brpd_public_report acceptedEvidence outcome formulaTruth :=
  fun accepted =>
    ay_brpd_conj_left
      (ay_brpd_public_report acceptedEvidence outcome formulaTruth)
      published
      accepted

theorem ay_brpd_no_claim_intro
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    diagnostic -> fallbackPublic -> ay_brpd_no_claim diagnostic fallbackPublic :=
  ay_brpd_conj_intro diagnostic fallbackPublic

theorem ay_brpd_no_claim_preserves_fallback
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_brpd_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_brpd_conj_right diagnostic fallbackPublic noClaim

theorem ay_brpd_window_drift_no_claim
    (windowDrift : Prop)
    (fallbackPublic : Prop) :
    windowDrift -> fallbackPublic -> ay_brpd_no_claim windowDrift fallbackPublic :=
  ay_brpd_no_claim_intro windowDrift fallbackPublic

theorem ay_brpd_phase_cache_mismatch_no_claim
    (phaseCacheMismatch : Prop)
    (fallbackPublic : Prop) :
    phaseCacheMismatch ->
    fallbackPublic ->
    ay_brpd_no_claim phaseCacheMismatch fallbackPublic :=
  ay_brpd_no_claim_intro phaseCacheMismatch fallbackPublic

theorem ay_brpd_missing_restart_ledger_no_claim
    (missingRestartLedger : Prop)
    (fallbackPublic : Prop) :
    missingRestartLedger ->
    fallbackPublic ->
    ay_brpd_no_claim missingRestartLedger fallbackPublic :=
  ay_brpd_no_claim_intro missingRestartLedger fallbackPublic

theorem ay_brpd_ranking_mismatch_no_claim
    (rankingMismatch : Prop)
    (fallbackPublic : Prop) :
    rankingMismatch ->
    fallbackPublic ->
    ay_brpd_no_claim rankingMismatch fallbackPublic :=
  ay_brpd_no_claim_intro rankingMismatch fallbackPublic

theorem ay_brpd_stale_build_no_claim
    (staleBuild : Prop)
    (fallbackPublic : Prop) :
    staleBuild -> fallbackPublic -> ay_brpd_no_claim staleBuild fallbackPublic :=
  ay_brpd_no_claim_intro staleBuild fallbackPublic

theorem ay_brpd_audit_contradiction_no_claim
    (auditContradiction : Prop)
    (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_brpd_no_claim auditContradiction fallbackPublic :=
  ay_brpd_no_claim_intro auditContradiction fallbackPublic

theorem ay_brpd_missing_fallback_no_claim
    (missingFallback : Prop)
    (fallbackPublic : Prop) :
    missingFallback ->
    fallbackPublic ->
    ay_brpd_no_claim missingFallback fallbackPublic :=
  ay_brpd_no_claim_intro missingFallback fallbackPublic

theorem ay_brpd_missing_validator_no_claim
    (missingValidator : Prop)
    (fallbackPublic : Prop) :
    missingValidator ->
    fallbackPublic ->
    ay_brpd_no_claim missingValidator fallbackPublic :=
  ay_brpd_no_claim_intro missingValidator fallbackPublic

theorem ay_brpd_recompute_preserves_public_soundness
    (diagnostic : Prop)
    (fallbackPublic : Prop)
    (recomputedPublic : Prop) :
    ay_brpd_no_claim diagnostic fallbackPublic ->
    (fallbackPublic -> recomputedPublic) ->
    recomputedPublic :=
  fun noClaim recompute =>
    recompute (ay_brpd_no_claim_preserves_fallback diagnostic fallbackPublic noClaim)

theorem ay_brpd_no_claim_cannot_bless_publication
    (diagnostic : Prop)
    (fallbackPublic : Prop) :
    ay_brpd_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_brpd_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_brpd_accepted_hint_guides_sat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayWindowHint : Prop)
    (satOutcome : Prop)
    (formulaTruth : Prop) :
    ay_brpd_accepted_hint guardEvidence agreementEvidence decayWindowHint ->
    satOutcome ->
    formulaTruth ->
    ay_brpd_public_report
      (ay_brpd_accepted_hint guardEvidence agreementEvidence decayWindowHint)
      satOutcome
      formulaTruth :=
  fun accepted satH truthH =>
    ay_brpd_public_sat_report
      (ay_brpd_accepted_hint guardEvidence agreementEvidence decayWindowHint)
      satOutcome
      formulaTruth
      accepted
      satH
      truthH

theorem ay_brpd_accepted_hint_guides_unsat
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayWindowHint : Prop)
    (unsatOutcome : Prop)
    (formulaTruth : Prop) :
    ay_brpd_accepted_hint guardEvidence agreementEvidence decayWindowHint ->
    unsatOutcome ->
    formulaTruth ->
    ay_brpd_public_report
      (ay_brpd_accepted_hint guardEvidence agreementEvidence decayWindowHint)
      unsatOutcome
      formulaTruth :=
  fun accepted unsatH truthH =>
    ay_brpd_public_unsat_report
      (ay_brpd_accepted_hint guardEvidence agreementEvidence decayWindowHint)
      unsatOutcome
      formulaTruth
      accepted
      unsatH
      truthH

theorem ay_brpd_accepted_hint_preserves_public_soundness
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayWindowHint : Prop)
    (solverTruth : Prop)
    (publicTruth : Prop) :
    ay_brpd_accepted_hint guardEvidence agreementEvidence decayWindowHint ->
    ay_brpd_outcome solverTruth publicTruth ->
    solverTruth ->
    publicTruth :=
  fun _accepted outcome solverH =>
    ay_brpd_equisat_forward solverTruth publicTruth outcome solverH

theorem ay_brpd_decay_window_hint_does_not_change_truth
    (guardEvidence : Prop)
    (agreementEvidence : Prop)
    (decayWindowHint : Prop)
    (beforeTruth : Prop)
    (afterTruth : Prop) :
    ay_brpd_accepted_hint guardEvidence agreementEvidence decayWindowHint ->
    ay_brpd_equisat beforeTruth afterTruth ->
    ay_brpd_equisat afterTruth beforeTruth :=
  fun _accepted eqsat =>
    ay_brpd_equisat_intro afterTruth beforeTruth
      (ay_brpd_equisat_backward beforeTruth afterTruth eqsat)
      (ay_brpd_equisat_forward beforeTruth afterTruth eqsat)
