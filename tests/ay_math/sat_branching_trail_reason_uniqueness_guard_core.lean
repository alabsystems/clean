-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Trail reason-uniqueness guard for sequential main-track CDCL propagation.
-- Reason uniqueness is state-accounting only when trail, levels, reason
-- clauses, replay, fallback, build, validator, and audit evidence agree.

def ay_trug_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_trug_equisat (before : Prop) (after : Prop) : Prop :=
  ay_trug_conj (before -> after) (after -> before)

def ay_trug_guard
    (variableDomainDigest : Prop)
    (trailSnapshotDigest : Prop)
    (assignmentLevelMap : Prop)
    (reasonClauseLedger : Prop)
    (reasonUniquenessWitness : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (variableDomainDigest ->
      trailSnapshotDigest ->
      assignmentLevelMap ->
      reasonClauseLedger ->
      reasonUniquenessWitness ->
      propagationReplay ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_trug_agreement
    (originalFormulaTruth guardedStateTruth publicSoundness : Prop) : Prop :=
  ay_trug_conj
    (ay_trug_equisat originalFormulaTruth guardedStateTruth)
    publicSoundness

def ay_trug_accepted_reason_state
    (guardEvidence agreementEvidence stateAccounting : Prop) : Prop :=
  ay_trug_conj guardEvidence
    (ay_trug_conj agreementEvidence stateAccounting)

def ay_trug_public_report
    (acceptedEvidence outcome formulaTruth : Prop) : Prop :=
  ay_trug_conj acceptedEvidence
    (ay_trug_conj outcome formulaTruth)

def ay_trug_no_claim (diagnostic fallbackOrRecompute : Prop) : Prop :=
  ay_trug_conj diagnostic fallbackOrRecompute

theorem ay_trug_conj_intro (left right : Prop) :
    left -> right -> ay_trug_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_trug_conj_left (left right : Prop) :
    ay_trug_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_trug_conj_right (left right : Prop) :
    ay_trug_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_trug_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_trug_equisat before after :=
  fun forward backward =>
    ay_trug_conj_intro (before -> after) (after -> before) forward backward

theorem ay_trug_equisat_forward (before after : Prop) :
    ay_trug_equisat before after -> before -> after :=
  fun eqsat =>
    ay_trug_conj_left (before -> after) (after -> before) eqsat

theorem ay_trug_equisat_backward (before after : Prop) :
    ay_trug_equisat before after -> after -> before :=
  fun eqsat =>
    ay_trug_conj_right (before -> after) (after -> before) eqsat

theorem ay_trug_guard_intro
    (variableDomainDigest trailSnapshotDigest assignmentLevelMap
      reasonClauseLedger reasonUniquenessWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    variableDomainDigest ->
    trailSnapshotDigest ->
    assignmentLevelMap ->
    reasonClauseLedger ->
    reasonUniquenessWitness ->
    propagationReplay ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_trug_guard variableDomainDigest trailSnapshotDigest assignmentLevelMap
      reasonClauseLedger reasonUniquenessWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :=
  fun domainH trailH levelH reasonH uniqueH replayH fallbackH buildH
      validatorH auditH result make =>
    make domainH trailH levelH reasonH uniqueH replayH fallbackH buildH
      validatorH auditH

theorem ay_trug_guard_domain
    (variableDomainDigest trailSnapshotDigest assignmentLevelMap
      reasonClauseLedger reasonUniquenessWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_trug_guard variableDomainDigest trailSnapshotDigest assignmentLevelMap
      reasonClauseLedger reasonUniquenessWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    variableDomainDigest :=
  fun guard =>
    guard variableDomainDigest
      (fun domainH _trailH _levelH _reasonH _uniqueH _replayH _fallbackH
          _buildH _validatorH _auditH => domainH)

theorem ay_trug_guard_trail
    (variableDomainDigest trailSnapshotDigest assignmentLevelMap
      reasonClauseLedger reasonUniquenessWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_trug_guard variableDomainDigest trailSnapshotDigest assignmentLevelMap
      reasonClauseLedger reasonUniquenessWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    trailSnapshotDigest :=
  fun guard =>
    guard trailSnapshotDigest
      (fun _domainH trailH _levelH _reasonH _uniqueH _replayH _fallbackH
          _buildH _validatorH _auditH => trailH)

theorem ay_trug_guard_assignment_level
    (variableDomainDigest trailSnapshotDigest assignmentLevelMap
      reasonClauseLedger reasonUniquenessWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_trug_guard variableDomainDigest trailSnapshotDigest assignmentLevelMap
      reasonClauseLedger reasonUniquenessWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    assignmentLevelMap :=
  fun guard =>
    guard assignmentLevelMap
      (fun _domainH _trailH levelH _reasonH _uniqueH _replayH _fallbackH
          _buildH _validatorH _auditH => levelH)

theorem ay_trug_guard_reason
    (variableDomainDigest trailSnapshotDigest assignmentLevelMap
      reasonClauseLedger reasonUniquenessWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_trug_guard variableDomainDigest trailSnapshotDigest assignmentLevelMap
      reasonClauseLedger reasonUniquenessWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    reasonClauseLedger :=
  fun guard =>
    guard reasonClauseLedger
      (fun _domainH _trailH _levelH reasonH _uniqueH _replayH _fallbackH
          _buildH _validatorH _auditH => reasonH)

theorem ay_trug_guard_uniqueness
    (variableDomainDigest trailSnapshotDigest assignmentLevelMap
      reasonClauseLedger reasonUniquenessWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_trug_guard variableDomainDigest trailSnapshotDigest assignmentLevelMap
      reasonClauseLedger reasonUniquenessWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    reasonUniquenessWitness :=
  fun guard =>
    guard reasonUniquenessWitness
      (fun _domainH _trailH _levelH _reasonH uniqueH _replayH _fallbackH
          _buildH _validatorH _auditH => uniqueH)

theorem ay_trug_guard_replay
    (variableDomainDigest trailSnapshotDigest assignmentLevelMap
      reasonClauseLedger reasonUniquenessWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_trug_guard variableDomainDigest trailSnapshotDigest assignmentLevelMap
      reasonClauseLedger reasonUniquenessWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _domainH _trailH _levelH _reasonH _uniqueH replayH _fallbackH
          _buildH _validatorH _auditH => replayH)

theorem ay_trug_guard_fallback
    (variableDomainDigest trailSnapshotDigest assignmentLevelMap
      reasonClauseLedger reasonUniquenessWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_trug_guard variableDomainDigest trailSnapshotDigest assignmentLevelMap
      reasonClauseLedger reasonUniquenessWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _domainH _trailH _levelH _reasonH _uniqueH _replayH fallbackH
          _buildH _validatorH _auditH => fallbackH)

theorem ay_trug_guard_build
    (variableDomainDigest trailSnapshotDigest assignmentLevelMap
      reasonClauseLedger reasonUniquenessWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_trug_guard variableDomainDigest trailSnapshotDigest assignmentLevelMap
      reasonClauseLedger reasonUniquenessWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _domainH _trailH _levelH _reasonH _uniqueH _replayH _fallbackH
          buildH _validatorH _auditH => buildH)

theorem ay_trug_guard_validator
    (variableDomainDigest trailSnapshotDigest assignmentLevelMap
      reasonClauseLedger reasonUniquenessWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_trug_guard variableDomainDigest trailSnapshotDigest assignmentLevelMap
      reasonClauseLedger reasonUniquenessWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _domainH _trailH _levelH _reasonH _uniqueH _replayH _fallbackH
          _buildH validatorH _auditH => validatorH)

theorem ay_trug_guard_audit
    (variableDomainDigest trailSnapshotDigest assignmentLevelMap
      reasonClauseLedger reasonUniquenessWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_trug_guard variableDomainDigest trailSnapshotDigest assignmentLevelMap
      reasonClauseLedger reasonUniquenessWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _domainH _trailH _levelH _reasonH _uniqueH _replayH _fallbackH
          _buildH _validatorH auditH => auditH)

theorem ay_trug_agreement_intro
    (originalFormulaTruth guardedStateTruth publicSoundness : Prop) :
    ay_trug_equisat originalFormulaTruth guardedStateTruth ->
    publicSoundness ->
    ay_trug_agreement originalFormulaTruth guardedStateTruth publicSoundness :=
  fun eqsat sound =>
    ay_trug_conj_intro
      (ay_trug_equisat originalFormulaTruth guardedStateTruth)
      publicSoundness eqsat sound

theorem ay_trug_accepted_reason_state_intro
    (guardEvidence agreementEvidence stateAccounting : Prop) :
    guardEvidence ->
    agreementEvidence ->
    stateAccounting ->
    ay_trug_accepted_reason_state guardEvidence agreementEvidence
      stateAccounting :=
  fun guardH agreementH accountingH =>
    ay_trug_conj_intro guardEvidence
      (ay_trug_conj agreementEvidence stateAccounting) guardH
      (ay_trug_conj_intro agreementEvidence stateAccounting agreementH
        accountingH)

theorem ay_trug_accepted_guard
    (guardEvidence agreementEvidence stateAccounting : Prop) :
    ay_trug_accepted_reason_state guardEvidence agreementEvidence
      stateAccounting ->
    guardEvidence :=
  fun accepted =>
    ay_trug_conj_left guardEvidence
      (ay_trug_conj agreementEvidence stateAccounting) accepted

theorem ay_trug_accepted_agreement
    (guardEvidence agreementEvidence stateAccounting : Prop) :
    ay_trug_accepted_reason_state guardEvidence agreementEvidence
      stateAccounting ->
    agreementEvidence :=
  fun accepted =>
    ay_trug_conj_left agreementEvidence stateAccounting
      (ay_trug_conj_right guardEvidence
        (ay_trug_conj agreementEvidence stateAccounting) accepted)

theorem ay_trug_accepted_state_accounting
    (guardEvidence agreementEvidence stateAccounting : Prop) :
    ay_trug_accepted_reason_state guardEvidence agreementEvidence
      stateAccounting ->
    stateAccounting :=
  fun accepted =>
    ay_trug_conj_right agreementEvidence stateAccounting
      (ay_trug_conj_right guardEvidence
        (ay_trug_conj agreementEvidence stateAccounting) accepted)

theorem ay_trug_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_trug_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_trug_conj_intro acceptedEvidence (ay_trug_conj outcome formulaTruth)
      acceptedH (ay_trug_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_trug_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_trug_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_trug_conj_left acceptedEvidence (ay_trug_conj outcome formulaTruth)
      report

theorem ay_trug_public_report_outcome
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_trug_public_report acceptedEvidence outcome formulaTruth ->
    outcome :=
  fun report =>
    ay_trug_conj_left outcome formulaTruth
      (ay_trug_conj_right acceptedEvidence
        (ay_trug_conj outcome formulaTruth) report)

theorem ay_trug_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_trug_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_trug_conj_right outcome formulaTruth
      (ay_trug_conj_right acceptedEvidence
        (ay_trug_conj outcome formulaTruth) report)

theorem ay_trug_preserves_formula_truth
    (originalFormulaTruth guardedStateTruth : Prop) :
    ay_trug_equisat originalFormulaTruth guardedStateTruth ->
    originalFormulaTruth ->
    guardedStateTruth :=
  fun eqsat truth =>
    ay_trug_equisat_forward originalFormulaTruth guardedStateTruth eqsat truth

theorem ay_trug_reflects_formula_truth
    (originalFormulaTruth guardedStateTruth : Prop) :
    ay_trug_equisat originalFormulaTruth guardedStateTruth ->
    guardedStateTruth ->
    originalFormulaTruth :=
  fun eqsat truth =>
    ay_trug_equisat_backward originalFormulaTruth guardedStateTruth eqsat truth

theorem ay_trug_accepted_preserves_public_soundness
    (guardEvidence agreementEvidence stateAccounting publicSoundness : Prop) :
    ay_trug_accepted_reason_state guardEvidence agreementEvidence
      stateAccounting ->
    (agreementEvidence -> publicSoundness) ->
    publicSoundness :=
  fun accepted project =>
    project
      (ay_trug_accepted_agreement guardEvidence agreementEvidence
        stateAccounting accepted)

theorem ay_trug_no_claim_intro (diagnostic fallbackOrRecompute : Prop) :
    diagnostic ->
    fallbackOrRecompute ->
    ay_trug_no_claim diagnostic fallbackOrRecompute :=
  ay_trug_conj_intro diagnostic fallbackOrRecompute

theorem ay_trug_no_claim_recompute
    (diagnostic fallbackOrRecompute : Prop) :
    ay_trug_no_claim diagnostic fallbackOrRecompute ->
    fallbackOrRecompute :=
  ay_trug_conj_right diagnostic fallbackOrRecompute

theorem ay_trug_trail_mismatch_no_claim
    (trailMismatch fallbackOrRecompute : Prop) :
    trailMismatch ->
    fallbackOrRecompute ->
    ay_trug_no_claim trailMismatch fallbackOrRecompute :=
  ay_trug_no_claim_intro trailMismatch fallbackOrRecompute

theorem ay_trug_level_mismatch_no_claim
    (levelMismatch fallbackOrRecompute : Prop) :
    levelMismatch ->
    fallbackOrRecompute ->
    ay_trug_no_claim levelMismatch fallbackOrRecompute :=
  ay_trug_no_claim_intro levelMismatch fallbackOrRecompute

theorem ay_trug_reason_mismatch_no_claim
    (reasonMismatch fallbackOrRecompute : Prop) :
    reasonMismatch ->
    fallbackOrRecompute ->
    ay_trug_no_claim reasonMismatch fallbackOrRecompute :=
  ay_trug_no_claim_intro reasonMismatch fallbackOrRecompute

theorem ay_trug_uniqueness_mismatch_no_claim
    (uniquenessMismatch fallbackOrRecompute : Prop) :
    uniquenessMismatch ->
    fallbackOrRecompute ->
    ay_trug_no_claim uniquenessMismatch fallbackOrRecompute :=
  ay_trug_no_claim_intro uniquenessMismatch fallbackOrRecompute

theorem ay_trug_replay_mismatch_no_claim
    (replayMismatch fallbackOrRecompute : Prop) :
    replayMismatch ->
    fallbackOrRecompute ->
    ay_trug_no_claim replayMismatch fallbackOrRecompute :=
  ay_trug_no_claim_intro replayMismatch fallbackOrRecompute

theorem ay_trug_build_mismatch_no_claim
    (buildMismatch fallbackOrRecompute : Prop) :
    buildMismatch ->
    fallbackOrRecompute ->
    ay_trug_no_claim buildMismatch fallbackOrRecompute :=
  ay_trug_no_claim_intro buildMismatch fallbackOrRecompute

theorem ay_trug_validator_mismatch_no_claim
    (validatorMismatch fallbackOrRecompute : Prop) :
    validatorMismatch ->
    fallbackOrRecompute ->
    ay_trug_no_claim validatorMismatch fallbackOrRecompute :=
  ay_trug_no_claim_intro validatorMismatch fallbackOrRecompute

theorem ay_trug_audit_mismatch_no_claim
    (auditMismatch fallbackOrRecompute : Prop) :
    auditMismatch ->
    fallbackOrRecompute ->
    ay_trug_no_claim auditMismatch fallbackOrRecompute :=
  ay_trug_no_claim_intro auditMismatch fallbackOrRecompute

theorem ay_trug_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicSatOrUnsat : Prop) :
    ay_trug_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicSatOrUnsat -> fallbackPublic) ->
    publicSatOrUnsat ->
    fallbackPublic :=
  fun noClaim fallbackPublishes publication =>
    fallbackPublishes
      (ay_trug_no_claim_recompute failedGuard fallbackPublic noClaim)
      publication

theorem ay_trug_publication_requires_guard
    (guardEvidence agreementEvidence stateAccounting outcome formulaTruth :
      Prop) :
    ay_trug_public_report
      (ay_trug_accepted_reason_state guardEvidence agreementEvidence
        stateAccounting)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_trug_accepted_guard guardEvidence agreementEvidence stateAccounting
      (ay_trug_public_report_accepted
        (ay_trug_accepted_reason_state guardEvidence agreementEvidence
          stateAccounting)
        outcome formulaTruth report)

theorem ay_trug_publication_requires_validator
    (variableDomainDigest trailSnapshotDigest assignmentLevelMap
      reasonClauseLedger reasonUniquenessWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      agreementEvidence stateAccounting outcome formulaTruth : Prop) :
    ay_trug_public_report
      (ay_trug_accepted_reason_state
        (ay_trug_guard variableDomainDigest trailSnapshotDigest
          assignmentLevelMap reasonClauseLedger reasonUniquenessWitness
          propagationReplay fallbackBaseline solverBuildEvidence validatorGate
          auditTranscript)
        agreementEvidence stateAccounting)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_trug_guard_validator variableDomainDigest trailSnapshotDigest
      assignmentLevelMap reasonClauseLedger reasonUniquenessWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript
      (ay_trug_publication_requires_guard
        (ay_trug_guard variableDomainDigest trailSnapshotDigest
          assignmentLevelMap reasonClauseLedger reasonUniquenessWitness
          propagationReplay fallbackBaseline solverBuildEvidence validatorGate
          auditTranscript)
        agreementEvidence stateAccounting outcome formulaTruth report)

theorem ay_trug_publication_requires_audit
    (variableDomainDigest trailSnapshotDigest assignmentLevelMap
      reasonClauseLedger reasonUniquenessWitness propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      agreementEvidence stateAccounting outcome formulaTruth : Prop) :
    ay_trug_public_report
      (ay_trug_accepted_reason_state
        (ay_trug_guard variableDomainDigest trailSnapshotDigest
          assignmentLevelMap reasonClauseLedger reasonUniquenessWitness
          propagationReplay fallbackBaseline solverBuildEvidence validatorGate
          auditTranscript)
        agreementEvidence stateAccounting)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_trug_guard_audit variableDomainDigest trailSnapshotDigest
      assignmentLevelMap reasonClauseLedger reasonUniquenessWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript
      (ay_trug_publication_requires_guard
        (ay_trug_guard variableDomainDigest trailSnapshotDigest
          assignmentLevelMap reasonClauseLedger reasonUniquenessWitness
          propagationReplay fallbackBaseline solverBuildEvidence validatorGate
          auditTranscript)
        agreementEvidence stateAccounting outcome formulaTruth report)

theorem ay_trug_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_trug_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_trug_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_trug_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_trug_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_trug_public_report_intro acceptedEvidence unsatOutcome formulaTruth
