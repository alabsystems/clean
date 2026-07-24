-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded activity-rescale replay guard soundness skeleton for ay SAT solving.
-- VSIDS/activity rescaling and tie-break choices are admissible performance
-- hints only when rescale logs, ranking replay, phase/restart compatibility,
-- fallback baselines, build evidence, validator gates, and audit evidence hold.

def ay_barx_conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_barx_disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_barx_equisat (before : Prop) (after : Prop) :=
  ay_barx_conj (before -> after) (after -> before)

def ay_barx_rescale_guard
    (rescaleLog : Prop) (rankingReplay : Prop)
    (phaseRestartCompatibility : Prop) (fallbackBaseline : Prop)
    (buildEvidence : Prop) (validatorGate : Prop) (auditEvidence : Prop) :=
  forall result : Prop,
    (rescaleLog -> rankingReplay -> phaseRestartCompatibility ->
      fallbackBaseline -> buildEvidence -> validatorGate -> auditEvidence ->
      result) ->
    result

def ay_barx_guard_agreement
    (rescaleMatch : Prop) (rankingMatch : Prop)
    (phaseRestartMatch : Prop) (fallbackMatch : Prop)
    (buildMatch : Prop) (validatorAccepts : Prop) (auditMatch : Prop) :=
  ay_barx_rescale_guard rescaleMatch rankingMatch phaseRestartMatch
    fallbackMatch buildMatch validatorAccepts auditMatch

def ay_barx_accepted_hint
    (guard : Prop) (agreement : Prop) (rescaleHint : Prop) :=
  ay_barx_conj guard (ay_barx_conj agreement rescaleHint)

def ay_barx_outcome (model : Prop) (conflict : Prop) :=
  ay_barx_disj model conflict

def ay_barx_public_report (acceptedEvidence : Prop)
    (outcome : Prop) (formula : Prop) :=
  ay_barx_conj acceptedEvidence (ay_barx_conj outcome formula)

def ay_barx_accepted_report (hintCert : Prop) (public : Prop) :=
  ay_barx_conj hintCert public

def ay_barx_no_claim (diagnostic : Prop) (fallbackPublic : Prop) :=
  ay_barx_conj fallbackPublic diagnostic

theorem ay_barx_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_barx_conj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_barx_conj_left
    (left : Prop) (right : Prop) :
    ay_barx_conj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_barx_conj_right
    (left : Prop) (right : Prop) :
    ay_barx_conj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_barx_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_barx_disj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_barx_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_barx_disj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_barx_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    ay_barx_equisat before after :=
  fun forward backward =>
    ay_barx_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_barx_equisat_forward
    (before : Prop) (after : Prop) :
    ay_barx_equisat before after -> before -> after :=
  fun equisat =>
    ay_barx_conj_left (before -> after) (after -> before) equisat

theorem ay_barx_equisat_backward
    (before : Prop) (after : Prop) :
    ay_barx_equisat before after -> after -> before :=
  fun equisat =>
    ay_barx_conj_right (before -> after) (after -> before) equisat

theorem ay_barx_rescale_guard_intro
    (rescaleLog : Prop) (rankingReplay : Prop)
    (phaseRestartCompatibility : Prop) (fallbackBaseline : Prop)
    (buildEvidence : Prop) (validatorGate : Prop) (auditEvidence : Prop) :
    rescaleLog ->
    rankingReplay ->
    phaseRestartCompatibility ->
    fallbackBaseline ->
    buildEvidence ->
    validatorGate ->
    auditEvidence ->
    ay_barx_rescale_guard rescaleLog rankingReplay
      phaseRestartCompatibility fallbackBaseline buildEvidence validatorGate
      auditEvidence :=
  fun rescaleH rankingH phaseRestartH fallbackH buildH validatorH auditH
      result build =>
    build rescaleH rankingH phaseRestartH fallbackH buildH validatorH auditH

theorem ay_barx_rescale_guard_log
    (rescaleLog : Prop) (rankingReplay : Prop)
    (phaseRestartCompatibility : Prop) (fallbackBaseline : Prop)
    (buildEvidence : Prop) (validatorGate : Prop) (auditEvidence : Prop) :
    ay_barx_rescale_guard rescaleLog rankingReplay
      phaseRestartCompatibility fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    rescaleLog :=
  fun guard =>
    guard rescaleLog
      (fun rescaleH _rankingH _phaseRestartH _fallbackH _buildH
          _validatorH _auditH => rescaleH)

theorem ay_barx_rescale_guard_ranking
    (rescaleLog : Prop) (rankingReplay : Prop)
    (phaseRestartCompatibility : Prop) (fallbackBaseline : Prop)
    (buildEvidence : Prop) (validatorGate : Prop) (auditEvidence : Prop) :
    ay_barx_rescale_guard rescaleLog rankingReplay
      phaseRestartCompatibility fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    rankingReplay :=
  fun guard =>
    guard rankingReplay
      (fun _rescaleH rankingH _phaseRestartH _fallbackH _buildH
          _validatorH _auditH => rankingH)

theorem ay_barx_rescale_guard_phase_restart
    (rescaleLog : Prop) (rankingReplay : Prop)
    (phaseRestartCompatibility : Prop) (fallbackBaseline : Prop)
    (buildEvidence : Prop) (validatorGate : Prop) (auditEvidence : Prop) :
    ay_barx_rescale_guard rescaleLog rankingReplay
      phaseRestartCompatibility fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    phaseRestartCompatibility :=
  fun guard =>
    guard phaseRestartCompatibility
      (fun _rescaleH _rankingH phaseRestartH _fallbackH _buildH
          _validatorH _auditH => phaseRestartH)

theorem ay_barx_rescale_guard_fallback
    (rescaleLog : Prop) (rankingReplay : Prop)
    (phaseRestartCompatibility : Prop) (fallbackBaseline : Prop)
    (buildEvidence : Prop) (validatorGate : Prop) (auditEvidence : Prop) :
    ay_barx_rescale_guard rescaleLog rankingReplay
      phaseRestartCompatibility fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _rescaleH _rankingH _phaseRestartH fallbackH _buildH
          _validatorH _auditH => fallbackH)

theorem ay_barx_rescale_guard_build
    (rescaleLog : Prop) (rankingReplay : Prop)
    (phaseRestartCompatibility : Prop) (fallbackBaseline : Prop)
    (buildEvidence : Prop) (validatorGate : Prop) (auditEvidence : Prop) :
    ay_barx_rescale_guard rescaleLog rankingReplay
      phaseRestartCompatibility fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    buildEvidence :=
  fun guard =>
    guard buildEvidence
      (fun _rescaleH _rankingH _phaseRestartH _fallbackH buildH
          _validatorH _auditH => buildH)

theorem ay_barx_rescale_guard_validator
    (rescaleLog : Prop) (rankingReplay : Prop)
    (phaseRestartCompatibility : Prop) (fallbackBaseline : Prop)
    (buildEvidence : Prop) (validatorGate : Prop) (auditEvidence : Prop) :
    ay_barx_rescale_guard rescaleLog rankingReplay
      phaseRestartCompatibility fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _rescaleH _rankingH _phaseRestartH _fallbackH _buildH
          validatorH _auditH => validatorH)

theorem ay_barx_rescale_guard_audit
    (rescaleLog : Prop) (rankingReplay : Prop)
    (phaseRestartCompatibility : Prop) (fallbackBaseline : Prop)
    (buildEvidence : Prop) (validatorGate : Prop) (auditEvidence : Prop) :
    ay_barx_rescale_guard rescaleLog rankingReplay
      phaseRestartCompatibility fallbackBaseline buildEvidence validatorGate
      auditEvidence ->
    auditEvidence :=
  fun guard =>
    guard auditEvidence
      (fun _rescaleH _rankingH _phaseRestartH _fallbackH _buildH
          _validatorH auditH => auditH)

theorem ay_barx_guard_agreement_intro
    (rescaleMatch : Prop) (rankingMatch : Prop)
    (phaseRestartMatch : Prop) (fallbackMatch : Prop)
    (buildMatch : Prop) (validatorAccepts : Prop) (auditMatch : Prop) :
    rescaleMatch ->
    rankingMatch ->
    phaseRestartMatch ->
    fallbackMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_barx_guard_agreement rescaleMatch rankingMatch phaseRestartMatch
      fallbackMatch buildMatch validatorAccepts auditMatch :=
  fun rescaleH rankingH phaseRestartH fallbackH buildH validatorH auditH =>
    ay_barx_rescale_guard_intro rescaleMatch rankingMatch phaseRestartMatch
      fallbackMatch buildMatch validatorAccepts auditMatch rescaleH rankingH
      phaseRestartH fallbackH buildH validatorH auditH

theorem ay_barx_guard_agreement_rescale
    (rescaleMatch : Prop) (rankingMatch : Prop)
    (phaseRestartMatch : Prop) (fallbackMatch : Prop)
    (buildMatch : Prop) (validatorAccepts : Prop) (auditMatch : Prop) :
    ay_barx_guard_agreement rescaleMatch rankingMatch phaseRestartMatch
      fallbackMatch buildMatch validatorAccepts auditMatch ->
    rescaleMatch :=
  fun agreement =>
    ay_barx_rescale_guard_log rescaleMatch rankingMatch phaseRestartMatch
      fallbackMatch buildMatch validatorAccepts auditMatch agreement

theorem ay_barx_accepted_hint_intro
    (guard : Prop) (agreement : Prop) (rescaleHint : Prop) :
    guard ->
    agreement ->
    rescaleHint ->
    ay_barx_accepted_hint guard agreement rescaleHint :=
  fun guardH agreementH hintH =>
    ay_barx_conj_intro guard (ay_barx_conj agreement rescaleHint)
      guardH
      (ay_barx_conj_intro agreement rescaleHint agreementH hintH)

theorem ay_barx_accepted_hint_guard
    (guard : Prop) (agreement : Prop) (rescaleHint : Prop) :
    ay_barx_accepted_hint guard agreement rescaleHint -> guard :=
  fun accepted =>
    ay_barx_conj_left guard (ay_barx_conj agreement rescaleHint) accepted

theorem ay_barx_accepted_hint_agreement
    (guard : Prop) (agreement : Prop) (rescaleHint : Prop) :
    ay_barx_accepted_hint guard agreement rescaleHint -> agreement :=
  fun accepted =>
    ay_barx_conj_left agreement rescaleHint
      (ay_barx_conj_right guard (ay_barx_conj agreement rescaleHint)
        accepted)

theorem ay_barx_accepted_hint_guidance
    (guard : Prop) (agreement : Prop) (rescaleHint : Prop) :
    ay_barx_accepted_hint guard agreement rescaleHint -> rescaleHint :=
  fun accepted =>
    ay_barx_conj_right agreement rescaleHint
      (ay_barx_conj_right guard (ay_barx_conj agreement rescaleHint)
        accepted)

theorem ay_barx_public_sat_report
    (acceptedEvidence : Prop) (model : Prop) (conflict : Prop)
    (formula : Prop) :
    acceptedEvidence ->
    model ->
    formula ->
    ay_barx_public_report acceptedEvidence
      (ay_barx_outcome model conflict) formula :=
  fun acceptedH modelH formulaH =>
    ay_barx_conj_intro acceptedEvidence
      (ay_barx_conj (ay_barx_outcome model conflict) formula)
      acceptedH
      (ay_barx_conj_intro (ay_barx_outcome model conflict) formula
        (ay_barx_disj_left model conflict modelH)
        formulaH)

theorem ay_barx_public_unsat_report
    (acceptedEvidence : Prop) (model : Prop) (conflict : Prop)
    (formula : Prop) :
    acceptedEvidence ->
    conflict ->
    formula ->
    ay_barx_public_report acceptedEvidence
      (ay_barx_outcome model conflict) formula :=
  fun acceptedH conflictH formulaH =>
    ay_barx_conj_intro acceptedEvidence
      (ay_barx_conj (ay_barx_outcome model conflict) formula)
      acceptedH
      (ay_barx_conj_intro (ay_barx_outcome model conflict) formula
        (ay_barx_disj_right model conflict conflictH)
        formulaH)

theorem ay_barx_public_report_requires_guard
    (acceptedEvidence : Prop) (outcome : Prop) (formula : Prop) :
    ay_barx_public_report acceptedEvidence outcome formula ->
    acceptedEvidence :=
  fun public =>
    ay_barx_conj_left acceptedEvidence
      (ay_barx_conj outcome formula) public

theorem ay_barx_accepted_report_intro
    (hintCert : Prop) (public : Prop) :
    hintCert ->
    public ->
    ay_barx_accepted_report hintCert public :=
  fun hintH publicH =>
    ay_barx_conj_intro hintCert public hintH publicH

theorem ay_barx_accepted_report_public
    (hintCert : Prop) (public : Prop) :
    ay_barx_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_barx_conj_right hintCert public accepted

theorem ay_barx_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    fallbackPublic ->
    diagnostic ->
    ay_barx_no_claim diagnostic fallbackPublic :=
  fun fallbackH diagnosticH =>
    ay_barx_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_barx_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_barx_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_barx_conj_left fallbackPublic diagnostic noClaim

theorem ay_barx_rescale_drift_no_claim
    (rescaleDrift : Prop) (fallbackPublic : Prop) :
    rescaleDrift ->
    fallbackPublic ->
    ay_barx_no_claim rescaleDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_barx_no_claim_intro rescaleDrift fallbackPublic fallbackH diagnosticH

theorem ay_barx_ranking_mismatch_no_claim
    (rankingMismatch : Prop) (fallbackPublic : Prop) :
    rankingMismatch ->
    fallbackPublic ->
    ay_barx_no_claim rankingMismatch fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_barx_no_claim_intro rankingMismatch fallbackPublic fallbackH diagnosticH

theorem ay_barx_missing_replay_no_claim
    (missingReplay : Prop) (fallbackPublic : Prop) :
    missingReplay ->
    fallbackPublic ->
    ay_barx_no_claim missingReplay fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_barx_no_claim_intro missingReplay fallbackPublic fallbackH diagnosticH

theorem ay_barx_phase_restart_drift_no_claim
    (phaseRestartDrift : Prop) (fallbackPublic : Prop) :
    phaseRestartDrift ->
    fallbackPublic ->
    ay_barx_no_claim phaseRestartDrift fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_barx_no_claim_intro phaseRestartDrift fallbackPublic
      fallbackH diagnosticH

theorem ay_barx_stale_build_no_claim
    (staleBuild : Prop) (fallbackPublic : Prop) :
    staleBuild ->
    fallbackPublic ->
    ay_barx_no_claim staleBuild fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_barx_no_claim_intro staleBuild fallbackPublic fallbackH diagnosticH

theorem ay_barx_missing_fallback_no_claim
    (missingFallback : Prop) (fallbackPublic : Prop) :
    missingFallback ->
    fallbackPublic ->
    ay_barx_no_claim missingFallback fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_barx_no_claim_intro missingFallback fallbackPublic fallbackH diagnosticH

theorem ay_barx_missing_validator_no_claim
    (missingValidator : Prop) (fallbackPublic : Prop) :
    missingValidator ->
    fallbackPublic ->
    ay_barx_no_claim missingValidator fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_barx_no_claim_intro missingValidator fallbackPublic
      fallbackH diagnosticH

theorem ay_barx_audit_contradiction_no_claim
    (auditContradiction : Prop) (fallbackPublic : Prop) :
    auditContradiction ->
    fallbackPublic ->
    ay_barx_no_claim auditContradiction fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_barx_no_claim_intro auditContradiction fallbackPublic
      fallbackH diagnosticH

theorem ay_barx_recompute_preserves_public_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_barx_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  fun noClaim =>
    ay_barx_no_claim_preserves_fallback diagnostic fallbackPublic noClaim

theorem ay_barx_no_claim_cannot_bless_publication
    (diagnostic : Prop) (fallbackPublic : Prop) :
    ay_barx_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  fun noClaim =>
    ay_barx_no_claim_preserves_fallback diagnostic fallbackPublic noClaim

theorem ay_barx_accepted_hint_guides_sat
    (guard : Prop) (agreement : Prop) (rescaleHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_barx_accepted_hint guard agreement rescaleHint ->
    model ->
    formula ->
    ay_barx_accepted_report
      (ay_barx_accepted_hint guard agreement rescaleHint)
      (ay_barx_public_report
        (ay_barx_accepted_hint guard agreement rescaleHint)
        (ay_barx_outcome model conflict) formula) :=
  fun accepted modelH formulaH =>
    ay_barx_accepted_report_intro
      (ay_barx_accepted_hint guard agreement rescaleHint)
      (ay_barx_public_report
        (ay_barx_accepted_hint guard agreement rescaleHint)
        (ay_barx_outcome model conflict) formula)
      accepted
      (ay_barx_public_sat_report
        (ay_barx_accepted_hint guard agreement rescaleHint)
        model conflict formula accepted modelH formulaH)

theorem ay_barx_accepted_hint_guides_unsat
    (guard : Prop) (agreement : Prop) (rescaleHint : Prop)
    (model : Prop) (conflict : Prop) (formula : Prop) :
    ay_barx_accepted_hint guard agreement rescaleHint ->
    conflict ->
    formula ->
    ay_barx_accepted_report
      (ay_barx_accepted_hint guard agreement rescaleHint)
      (ay_barx_public_report
        (ay_barx_accepted_hint guard agreement rescaleHint)
        (ay_barx_outcome model conflict) formula) :=
  fun accepted conflictH formulaH =>
    ay_barx_accepted_report_intro
      (ay_barx_accepted_hint guard agreement rescaleHint)
      (ay_barx_public_report
        (ay_barx_accepted_hint guard agreement rescaleHint)
        (ay_barx_outcome model conflict) formula)
      accepted
      (ay_barx_public_unsat_report
        (ay_barx_accepted_hint guard agreement rescaleHint)
        model conflict formula accepted conflictH formulaH)

theorem ay_barx_accepted_hint_preserves_public_soundness
    (hintCert : Prop) (public : Prop) :
    ay_barx_accepted_report hintCert public -> public :=
  fun accepted =>
    ay_barx_accepted_report_public hintCert public accepted

theorem ay_barx_rescale_hint_does_not_change_truth
    (beforeHint : Prop) (afterHint : Prop) :
    ay_barx_equisat beforeHint afterHint ->
    beforeHint ->
    afterHint :=
  fun equisat beforeH =>
    ay_barx_equisat_forward beforeHint afterHint equisat beforeH
