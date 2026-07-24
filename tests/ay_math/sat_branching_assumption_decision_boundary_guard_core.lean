-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Assumption/decision boundary guard for sequential main-track CDCL.
-- Boundary bookkeeping is state accounting only for the intended formula and
-- assumption scope when scope, trail, boundary, reason, replay, fallback,
-- build, validator, and audit evidence agree.

def ay_adbg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_adbg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_adbg_conj (before -> after) (after -> before)

def ay_adbg_guard
    (variableDomainDigest : Prop)
    (assumptionScopeManifest : Prop)
    (trailSnapshotDigest : Prop)
    (decisionBoundaryIndex : Prop)
    (reasonClauseLedger : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (variableDomainDigest ->
      assumptionScopeManifest ->
      trailSnapshotDigest ->
      decisionBoundaryIndex ->
      reasonClauseLedger ->
      propagationReplay ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_adbg_scoped_agreement
    (originalScopedTruth guardedScopedTruth publicSoundness : Prop) : Prop :=
  ay_adbg_conj
    (ay_adbg_equisat originalScopedTruth guardedScopedTruth)
    publicSoundness

def ay_adbg_accepted_boundary
    (guardEvidence agreementEvidence stateAccounting : Prop) : Prop :=
  ay_adbg_conj guardEvidence
    (ay_adbg_conj agreementEvidence stateAccounting)

def ay_adbg_public_report
    (acceptedEvidence outcome scopedFormulaTruth : Prop) : Prop :=
  ay_adbg_conj acceptedEvidence
    (ay_adbg_conj outcome scopedFormulaTruth)

def ay_adbg_no_claim (diagnostic fallbackOrRecompute : Prop) : Prop :=
  ay_adbg_conj diagnostic fallbackOrRecompute

theorem ay_adbg_conj_intro (left right : Prop) :
    left -> right -> ay_adbg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_adbg_conj_left (left right : Prop) :
    ay_adbg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_adbg_conj_right (left right : Prop) :
    ay_adbg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_adbg_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_adbg_equisat before after :=
  fun forward backward =>
    ay_adbg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_adbg_equisat_forward (before after : Prop) :
    ay_adbg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_adbg_conj_left (before -> after) (after -> before) eqsat

theorem ay_adbg_equisat_backward (before after : Prop) :
    ay_adbg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_adbg_conj_right (before -> after) (after -> before) eqsat

theorem ay_adbg_guard_intro
    (variableDomainDigest assumptionScopeManifest trailSnapshotDigest
      decisionBoundaryIndex reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    variableDomainDigest ->
    assumptionScopeManifest ->
    trailSnapshotDigest ->
    decisionBoundaryIndex ->
    reasonClauseLedger ->
    propagationReplay ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_adbg_guard variableDomainDigest assumptionScopeManifest
      trailSnapshotDigest decisionBoundaryIndex reasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript :=
  fun domainH scopeH trailH boundaryH reasonH replayH fallbackH buildH
      validatorH auditH result make =>
    make domainH scopeH trailH boundaryH reasonH replayH fallbackH buildH
      validatorH auditH

theorem ay_adbg_guard_domain
    (variableDomainDigest assumptionScopeManifest trailSnapshotDigest
      decisionBoundaryIndex reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_adbg_guard variableDomainDigest assumptionScopeManifest
      trailSnapshotDigest decisionBoundaryIndex reasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    variableDomainDigest :=
  fun guard =>
    guard variableDomainDigest
      (fun domainH _scopeH _trailH _boundaryH _reasonH _replayH _fallbackH
          _buildH _validatorH _auditH => domainH)

theorem ay_adbg_guard_scope
    (variableDomainDigest assumptionScopeManifest trailSnapshotDigest
      decisionBoundaryIndex reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_adbg_guard variableDomainDigest assumptionScopeManifest
      trailSnapshotDigest decisionBoundaryIndex reasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    assumptionScopeManifest :=
  fun guard =>
    guard assumptionScopeManifest
      (fun _domainH scopeH _trailH _boundaryH _reasonH _replayH _fallbackH
          _buildH _validatorH _auditH => scopeH)

theorem ay_adbg_guard_trail
    (variableDomainDigest assumptionScopeManifest trailSnapshotDigest
      decisionBoundaryIndex reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_adbg_guard variableDomainDigest assumptionScopeManifest
      trailSnapshotDigest decisionBoundaryIndex reasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    trailSnapshotDigest :=
  fun guard =>
    guard trailSnapshotDigest
      (fun _domainH _scopeH trailH _boundaryH _reasonH _replayH _fallbackH
          _buildH _validatorH _auditH => trailH)

theorem ay_adbg_guard_boundary
    (variableDomainDigest assumptionScopeManifest trailSnapshotDigest
      decisionBoundaryIndex reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_adbg_guard variableDomainDigest assumptionScopeManifest
      trailSnapshotDigest decisionBoundaryIndex reasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    decisionBoundaryIndex :=
  fun guard =>
    guard decisionBoundaryIndex
      (fun _domainH _scopeH _trailH boundaryH _reasonH _replayH _fallbackH
          _buildH _validatorH _auditH => boundaryH)

theorem ay_adbg_guard_reason
    (variableDomainDigest assumptionScopeManifest trailSnapshotDigest
      decisionBoundaryIndex reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_adbg_guard variableDomainDigest assumptionScopeManifest
      trailSnapshotDigest decisionBoundaryIndex reasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    reasonClauseLedger :=
  fun guard =>
    guard reasonClauseLedger
      (fun _domainH _scopeH _trailH _boundaryH reasonH _replayH _fallbackH
          _buildH _validatorH _auditH => reasonH)

theorem ay_adbg_guard_replay
    (variableDomainDigest assumptionScopeManifest trailSnapshotDigest
      decisionBoundaryIndex reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_adbg_guard variableDomainDigest assumptionScopeManifest
      trailSnapshotDigest decisionBoundaryIndex reasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _domainH _scopeH _trailH _boundaryH _reasonH replayH _fallbackH
          _buildH _validatorH _auditH => replayH)

theorem ay_adbg_guard_fallback
    (variableDomainDigest assumptionScopeManifest trailSnapshotDigest
      decisionBoundaryIndex reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_adbg_guard variableDomainDigest assumptionScopeManifest
      trailSnapshotDigest decisionBoundaryIndex reasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _domainH _scopeH _trailH _boundaryH _reasonH _replayH fallbackH
          _buildH _validatorH _auditH => fallbackH)

theorem ay_adbg_guard_build
    (variableDomainDigest assumptionScopeManifest trailSnapshotDigest
      decisionBoundaryIndex reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_adbg_guard variableDomainDigest assumptionScopeManifest
      trailSnapshotDigest decisionBoundaryIndex reasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _domainH _scopeH _trailH _boundaryH _reasonH _replayH _fallbackH
          buildH _validatorH _auditH => buildH)

theorem ay_adbg_guard_validator
    (variableDomainDigest assumptionScopeManifest trailSnapshotDigest
      decisionBoundaryIndex reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_adbg_guard variableDomainDigest assumptionScopeManifest
      trailSnapshotDigest decisionBoundaryIndex reasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _domainH _scopeH _trailH _boundaryH _reasonH _replayH _fallbackH
          _buildH validatorH _auditH => validatorH)

theorem ay_adbg_guard_audit
    (variableDomainDigest assumptionScopeManifest trailSnapshotDigest
      decisionBoundaryIndex reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_adbg_guard variableDomainDigest assumptionScopeManifest
      trailSnapshotDigest decisionBoundaryIndex reasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _domainH _scopeH _trailH _boundaryH _reasonH _replayH _fallbackH
          _buildH _validatorH auditH => auditH)

theorem ay_adbg_scoped_agreement_intro
    (originalScopedTruth guardedScopedTruth publicSoundness : Prop) :
    ay_adbg_equisat originalScopedTruth guardedScopedTruth ->
    publicSoundness ->
    ay_adbg_scoped_agreement originalScopedTruth guardedScopedTruth
      publicSoundness :=
  fun eqsat sound =>
    ay_adbg_conj_intro
      (ay_adbg_equisat originalScopedTruth guardedScopedTruth)
      publicSoundness eqsat sound

theorem ay_adbg_accepted_boundary_intro
    (guardEvidence agreementEvidence stateAccounting : Prop) :
    guardEvidence ->
    agreementEvidence ->
    stateAccounting ->
    ay_adbg_accepted_boundary guardEvidence agreementEvidence
      stateAccounting :=
  fun guardH agreementH accountingH =>
    ay_adbg_conj_intro guardEvidence
      (ay_adbg_conj agreementEvidence stateAccounting) guardH
      (ay_adbg_conj_intro agreementEvidence stateAccounting agreementH
        accountingH)

theorem ay_adbg_accepted_guard
    (guardEvidence agreementEvidence stateAccounting : Prop) :
    ay_adbg_accepted_boundary guardEvidence agreementEvidence
      stateAccounting ->
    guardEvidence :=
  fun accepted =>
    ay_adbg_conj_left guardEvidence
      (ay_adbg_conj agreementEvidence stateAccounting) accepted

theorem ay_adbg_accepted_agreement
    (guardEvidence agreementEvidence stateAccounting : Prop) :
    ay_adbg_accepted_boundary guardEvidence agreementEvidence
      stateAccounting ->
    agreementEvidence :=
  fun accepted =>
    ay_adbg_conj_left agreementEvidence stateAccounting
      (ay_adbg_conj_right guardEvidence
        (ay_adbg_conj agreementEvidence stateAccounting) accepted)

theorem ay_adbg_accepted_state_accounting
    (guardEvidence agreementEvidence stateAccounting : Prop) :
    ay_adbg_accepted_boundary guardEvidence agreementEvidence
      stateAccounting ->
    stateAccounting :=
  fun accepted =>
    ay_adbg_conj_right agreementEvidence stateAccounting
      (ay_adbg_conj_right guardEvidence
        (ay_adbg_conj agreementEvidence stateAccounting) accepted)

theorem ay_adbg_public_report_intro
    (acceptedEvidence outcome scopedFormulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    scopedFormulaTruth ->
    ay_adbg_public_report acceptedEvidence outcome scopedFormulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_adbg_conj_intro acceptedEvidence
      (ay_adbg_conj outcome scopedFormulaTruth)
      acceptedH (ay_adbg_conj_intro outcome scopedFormulaTruth outcomeH truthH)

theorem ay_adbg_public_report_accepted
    (acceptedEvidence outcome scopedFormulaTruth : Prop) :
    ay_adbg_public_report acceptedEvidence outcome scopedFormulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_adbg_conj_left acceptedEvidence
      (ay_adbg_conj outcome scopedFormulaTruth) report

theorem ay_adbg_public_report_outcome
    (acceptedEvidence outcome scopedFormulaTruth : Prop) :
    ay_adbg_public_report acceptedEvidence outcome scopedFormulaTruth ->
    outcome :=
  fun report =>
    ay_adbg_conj_left outcome scopedFormulaTruth
      (ay_adbg_conj_right acceptedEvidence
        (ay_adbg_conj outcome scopedFormulaTruth) report)

theorem ay_adbg_public_report_scope_truth
    (acceptedEvidence outcome scopedFormulaTruth : Prop) :
    ay_adbg_public_report acceptedEvidence outcome scopedFormulaTruth ->
    scopedFormulaTruth :=
  fun report =>
    ay_adbg_conj_right outcome scopedFormulaTruth
      (ay_adbg_conj_right acceptedEvidence
        (ay_adbg_conj outcome scopedFormulaTruth) report)

theorem ay_adbg_preserves_scoped_truth
    (originalScopedTruth guardedScopedTruth : Prop) :
    ay_adbg_equisat originalScopedTruth guardedScopedTruth ->
    originalScopedTruth ->
    guardedScopedTruth :=
  fun eqsat truth =>
    ay_adbg_equisat_forward originalScopedTruth guardedScopedTruth eqsat truth

theorem ay_adbg_reflects_scoped_truth
    (originalScopedTruth guardedScopedTruth : Prop) :
    ay_adbg_equisat originalScopedTruth guardedScopedTruth ->
    guardedScopedTruth ->
    originalScopedTruth :=
  fun eqsat truth =>
    ay_adbg_equisat_backward originalScopedTruth guardedScopedTruth eqsat truth

theorem ay_adbg_accepted_preserves_public_soundness
    (guardEvidence agreementEvidence stateAccounting publicSoundness : Prop) :
    ay_adbg_accepted_boundary guardEvidence agreementEvidence
      stateAccounting ->
    (agreementEvidence -> publicSoundness) ->
    publicSoundness :=
  fun accepted project =>
    project
      (ay_adbg_accepted_agreement guardEvidence agreementEvidence
        stateAccounting accepted)

theorem ay_adbg_no_claim_intro (diagnostic fallbackOrRecompute : Prop) :
    diagnostic ->
    fallbackOrRecompute ->
    ay_adbg_no_claim diagnostic fallbackOrRecompute :=
  ay_adbg_conj_intro diagnostic fallbackOrRecompute

theorem ay_adbg_no_claim_recompute
    (diagnostic fallbackOrRecompute : Prop) :
    ay_adbg_no_claim diagnostic fallbackOrRecompute ->
    fallbackOrRecompute :=
  ay_adbg_conj_right diagnostic fallbackOrRecompute

theorem ay_adbg_scope_mismatch_no_claim
    (scopeMismatch fallbackOrRecompute : Prop) :
    scopeMismatch ->
    fallbackOrRecompute ->
    ay_adbg_no_claim scopeMismatch fallbackOrRecompute :=
  ay_adbg_no_claim_intro scopeMismatch fallbackOrRecompute

theorem ay_adbg_trail_mismatch_no_claim
    (trailMismatch fallbackOrRecompute : Prop) :
    trailMismatch ->
    fallbackOrRecompute ->
    ay_adbg_no_claim trailMismatch fallbackOrRecompute :=
  ay_adbg_no_claim_intro trailMismatch fallbackOrRecompute

theorem ay_adbg_boundary_mismatch_no_claim
    (boundaryMismatch fallbackOrRecompute : Prop) :
    boundaryMismatch ->
    fallbackOrRecompute ->
    ay_adbg_no_claim boundaryMismatch fallbackOrRecompute :=
  ay_adbg_no_claim_intro boundaryMismatch fallbackOrRecompute

theorem ay_adbg_reason_mismatch_no_claim
    (reasonMismatch fallbackOrRecompute : Prop) :
    reasonMismatch ->
    fallbackOrRecompute ->
    ay_adbg_no_claim reasonMismatch fallbackOrRecompute :=
  ay_adbg_no_claim_intro reasonMismatch fallbackOrRecompute

theorem ay_adbg_replay_mismatch_no_claim
    (replayMismatch fallbackOrRecompute : Prop) :
    replayMismatch ->
    fallbackOrRecompute ->
    ay_adbg_no_claim replayMismatch fallbackOrRecompute :=
  ay_adbg_no_claim_intro replayMismatch fallbackOrRecompute

theorem ay_adbg_build_mismatch_no_claim
    (buildMismatch fallbackOrRecompute : Prop) :
    buildMismatch ->
    fallbackOrRecompute ->
    ay_adbg_no_claim buildMismatch fallbackOrRecompute :=
  ay_adbg_no_claim_intro buildMismatch fallbackOrRecompute

theorem ay_adbg_validator_mismatch_no_claim
    (validatorMismatch fallbackOrRecompute : Prop) :
    validatorMismatch ->
    fallbackOrRecompute ->
    ay_adbg_no_claim validatorMismatch fallbackOrRecompute :=
  ay_adbg_no_claim_intro validatorMismatch fallbackOrRecompute

theorem ay_adbg_audit_mismatch_no_claim
    (auditMismatch fallbackOrRecompute : Prop) :
    auditMismatch ->
    fallbackOrRecompute ->
    ay_adbg_no_claim auditMismatch fallbackOrRecompute :=
  ay_adbg_no_claim_intro auditMismatch fallbackOrRecompute

theorem ay_adbg_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicSatOrUnsat : Prop) :
    ay_adbg_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicSatOrUnsat -> fallbackPublic) ->
    publicSatOrUnsat ->
    fallbackPublic :=
  fun noClaim fallbackPublishes publication =>
    fallbackPublishes
      (ay_adbg_no_claim_recompute failedGuard fallbackPublic noClaim)
      publication

theorem ay_adbg_publication_requires_guard
    (guardEvidence agreementEvidence stateAccounting outcome scopedFormulaTruth :
      Prop) :
    ay_adbg_public_report
      (ay_adbg_accepted_boundary guardEvidence agreementEvidence
        stateAccounting)
      outcome scopedFormulaTruth ->
    guardEvidence :=
  fun report =>
    ay_adbg_accepted_guard guardEvidence agreementEvidence stateAccounting
      (ay_adbg_public_report_accepted
        (ay_adbg_accepted_boundary guardEvidence agreementEvidence
          stateAccounting)
        outcome scopedFormulaTruth report)

theorem ay_adbg_publication_requires_validator
    (variableDomainDigest assumptionScopeManifest trailSnapshotDigest
      decisionBoundaryIndex reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      agreementEvidence stateAccounting outcome scopedFormulaTruth : Prop) :
    ay_adbg_public_report
      (ay_adbg_accepted_boundary
        (ay_adbg_guard variableDomainDigest assumptionScopeManifest
          trailSnapshotDigest decisionBoundaryIndex reasonClauseLedger
          propagationReplay fallbackBaseline solverBuildEvidence validatorGate
          auditTranscript)
        agreementEvidence stateAccounting)
      outcome scopedFormulaTruth ->
    validatorGate :=
  fun report =>
    ay_adbg_guard_validator variableDomainDigest assumptionScopeManifest
      trailSnapshotDigest decisionBoundaryIndex reasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript
      (ay_adbg_publication_requires_guard
        (ay_adbg_guard variableDomainDigest assumptionScopeManifest
          trailSnapshotDigest decisionBoundaryIndex reasonClauseLedger
          propagationReplay fallbackBaseline solverBuildEvidence validatorGate
          auditTranscript)
        agreementEvidence stateAccounting outcome scopedFormulaTruth report)

theorem ay_adbg_publication_requires_audit
    (variableDomainDigest assumptionScopeManifest trailSnapshotDigest
      decisionBoundaryIndex reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      agreementEvidence stateAccounting outcome scopedFormulaTruth : Prop) :
    ay_adbg_public_report
      (ay_adbg_accepted_boundary
        (ay_adbg_guard variableDomainDigest assumptionScopeManifest
          trailSnapshotDigest decisionBoundaryIndex reasonClauseLedger
          propagationReplay fallbackBaseline solverBuildEvidence validatorGate
          auditTranscript)
        agreementEvidence stateAccounting)
      outcome scopedFormulaTruth ->
    auditTranscript :=
  fun report =>
    ay_adbg_guard_audit variableDomainDigest assumptionScopeManifest
      trailSnapshotDigest decisionBoundaryIndex reasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript
      (ay_adbg_publication_requires_guard
        (ay_adbg_guard variableDomainDigest assumptionScopeManifest
          trailSnapshotDigest decisionBoundaryIndex reasonClauseLedger
          propagationReplay fallbackBaseline solverBuildEvidence validatorGate
          auditTranscript)
        agreementEvidence stateAccounting outcome scopedFormulaTruth report)

theorem ay_adbg_accepted_public_report_for_sat
    (acceptedEvidence satOutcome scopedFormulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    scopedFormulaTruth ->
    ay_adbg_public_report acceptedEvidence satOutcome scopedFormulaTruth :=
  ay_adbg_public_report_intro acceptedEvidence satOutcome scopedFormulaTruth

theorem ay_adbg_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome scopedFormulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    scopedFormulaTruth ->
    ay_adbg_public_report acceptedEvidence unsatOutcome scopedFormulaTruth :=
  ay_adbg_public_report_intro acceptedEvidence unsatOutcome scopedFormulaTruth
