-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Decision-level gap guard for sequential main-track CDCL branching/restart.
-- Decision-level bookkeeping is search-control state accounting only when
-- trail, level map, contiguity, reason, replay, build, validator, and audit
-- evidence agree.

def ay_dlg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_dlg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_dlg_conj (before -> after) (after -> before)

def ay_dlg_guard
    (variableDomainDigest : Prop)
    (trailSnapshotDigest : Prop)
    (decisionLevelMap : Prop)
    (levelContiguityWitness : Prop)
    (reasonClauseLedger : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (variableDomainDigest ->
      trailSnapshotDigest ->
      decisionLevelMap ->
      levelContiguityWitness ->
      reasonClauseLedger ->
      propagationReplay ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_dlg_agreement
    (originalFormulaTruth guardedStateTruth publicSoundness : Prop) : Prop :=
  ay_dlg_conj
    (ay_dlg_equisat originalFormulaTruth guardedStateTruth)
    publicSoundness

def ay_dlg_accepted_level_state
    (guardEvidence agreementEvidence searchControlAccounting : Prop) : Prop :=
  ay_dlg_conj guardEvidence
    (ay_dlg_conj agreementEvidence searchControlAccounting)

def ay_dlg_public_report
    (acceptedEvidence outcome formulaTruth : Prop) : Prop :=
  ay_dlg_conj acceptedEvidence
    (ay_dlg_conj outcome formulaTruth)

def ay_dlg_no_claim (diagnostic fallbackOrRecompute : Prop) : Prop :=
  ay_dlg_conj diagnostic fallbackOrRecompute

theorem ay_dlg_conj_intro (left right : Prop) :
    left -> right -> ay_dlg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_dlg_conj_left (left right : Prop) :
    ay_dlg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_dlg_conj_right (left right : Prop) :
    ay_dlg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_dlg_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_dlg_equisat before after :=
  fun forward backward =>
    ay_dlg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_dlg_equisat_forward (before after : Prop) :
    ay_dlg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_dlg_conj_left (before -> after) (after -> before) eqsat

theorem ay_dlg_equisat_backward (before after : Prop) :
    ay_dlg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_dlg_conj_right (before -> after) (after -> before) eqsat

theorem ay_dlg_guard_intro
    (variableDomainDigest trailSnapshotDigest decisionLevelMap
      levelContiguityWitness reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    variableDomainDigest ->
    trailSnapshotDigest ->
    decisionLevelMap ->
    levelContiguityWitness ->
    reasonClauseLedger ->
    propagationReplay ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_dlg_guard variableDomainDigest trailSnapshotDigest decisionLevelMap
      levelContiguityWitness reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :=
  fun domainH trailH mapH contiguousH reasonH replayH fallbackH buildH
      validatorH auditH result make =>
    make domainH trailH mapH contiguousH reasonH replayH fallbackH buildH
      validatorH auditH

theorem ay_dlg_guard_domain
    (variableDomainDigest trailSnapshotDigest decisionLevelMap
      levelContiguityWitness reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_dlg_guard variableDomainDigest trailSnapshotDigest decisionLevelMap
      levelContiguityWitness reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    variableDomainDigest :=
  fun guard =>
    guard variableDomainDigest
      (fun domainH _trailH _mapH _contiguousH _reasonH _replayH _fallbackH
          _buildH _validatorH _auditH => domainH)

theorem ay_dlg_guard_trail
    (variableDomainDigest trailSnapshotDigest decisionLevelMap
      levelContiguityWitness reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_dlg_guard variableDomainDigest trailSnapshotDigest decisionLevelMap
      levelContiguityWitness reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    trailSnapshotDigest :=
  fun guard =>
    guard trailSnapshotDigest
      (fun _domainH trailH _mapH _contiguousH _reasonH _replayH _fallbackH
          _buildH _validatorH _auditH => trailH)

theorem ay_dlg_guard_level_map
    (variableDomainDigest trailSnapshotDigest decisionLevelMap
      levelContiguityWitness reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_dlg_guard variableDomainDigest trailSnapshotDigest decisionLevelMap
      levelContiguityWitness reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    decisionLevelMap :=
  fun guard =>
    guard decisionLevelMap
      (fun _domainH _trailH mapH _contiguousH _reasonH _replayH _fallbackH
          _buildH _validatorH _auditH => mapH)

theorem ay_dlg_guard_contiguity
    (variableDomainDigest trailSnapshotDigest decisionLevelMap
      levelContiguityWitness reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_dlg_guard variableDomainDigest trailSnapshotDigest decisionLevelMap
      levelContiguityWitness reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    levelContiguityWitness :=
  fun guard =>
    guard levelContiguityWitness
      (fun _domainH _trailH _mapH contiguousH _reasonH _replayH _fallbackH
          _buildH _validatorH _auditH => contiguousH)

theorem ay_dlg_guard_reason
    (variableDomainDigest trailSnapshotDigest decisionLevelMap
      levelContiguityWitness reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_dlg_guard variableDomainDigest trailSnapshotDigest decisionLevelMap
      levelContiguityWitness reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    reasonClauseLedger :=
  fun guard =>
    guard reasonClauseLedger
      (fun _domainH _trailH _mapH _contiguousH reasonH _replayH _fallbackH
          _buildH _validatorH _auditH => reasonH)

theorem ay_dlg_guard_replay
    (variableDomainDigest trailSnapshotDigest decisionLevelMap
      levelContiguityWitness reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_dlg_guard variableDomainDigest trailSnapshotDigest decisionLevelMap
      levelContiguityWitness reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _domainH _trailH _mapH _contiguousH _reasonH replayH _fallbackH
          _buildH _validatorH _auditH => replayH)

theorem ay_dlg_guard_fallback
    (variableDomainDigest trailSnapshotDigest decisionLevelMap
      levelContiguityWitness reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_dlg_guard variableDomainDigest trailSnapshotDigest decisionLevelMap
      levelContiguityWitness reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _domainH _trailH _mapH _contiguousH _reasonH _replayH fallbackH
          _buildH _validatorH _auditH => fallbackH)

theorem ay_dlg_guard_build
    (variableDomainDigest trailSnapshotDigest decisionLevelMap
      levelContiguityWitness reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_dlg_guard variableDomainDigest trailSnapshotDigest decisionLevelMap
      levelContiguityWitness reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _domainH _trailH _mapH _contiguousH _reasonH _replayH _fallbackH
          buildH _validatorH _auditH => buildH)

theorem ay_dlg_guard_validator
    (variableDomainDigest trailSnapshotDigest decisionLevelMap
      levelContiguityWitness reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_dlg_guard variableDomainDigest trailSnapshotDigest decisionLevelMap
      levelContiguityWitness reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _domainH _trailH _mapH _contiguousH _reasonH _replayH _fallbackH
          _buildH validatorH _auditH => validatorH)

theorem ay_dlg_guard_audit
    (variableDomainDigest trailSnapshotDigest decisionLevelMap
      levelContiguityWitness reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_dlg_guard variableDomainDigest trailSnapshotDigest decisionLevelMap
      levelContiguityWitness reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _domainH _trailH _mapH _contiguousH _reasonH _replayH _fallbackH
          _buildH _validatorH auditH => auditH)

theorem ay_dlg_agreement_intro
    (originalFormulaTruth guardedStateTruth publicSoundness : Prop) :
    ay_dlg_equisat originalFormulaTruth guardedStateTruth ->
    publicSoundness ->
    ay_dlg_agreement originalFormulaTruth guardedStateTruth publicSoundness :=
  fun eqsat sound =>
    ay_dlg_conj_intro
      (ay_dlg_equisat originalFormulaTruth guardedStateTruth)
      publicSoundness eqsat sound

theorem ay_dlg_accepted_level_state_intro
    (guardEvidence agreementEvidence searchControlAccounting : Prop) :
    guardEvidence ->
    agreementEvidence ->
    searchControlAccounting ->
    ay_dlg_accepted_level_state guardEvidence agreementEvidence
      searchControlAccounting :=
  fun guardH agreementH accountingH =>
    ay_dlg_conj_intro guardEvidence
      (ay_dlg_conj agreementEvidence searchControlAccounting) guardH
      (ay_dlg_conj_intro agreementEvidence searchControlAccounting agreementH
        accountingH)

theorem ay_dlg_accepted_guard
    (guardEvidence agreementEvidence searchControlAccounting : Prop) :
    ay_dlg_accepted_level_state guardEvidence agreementEvidence
      searchControlAccounting ->
    guardEvidence :=
  fun accepted =>
    ay_dlg_conj_left guardEvidence
      (ay_dlg_conj agreementEvidence searchControlAccounting) accepted

theorem ay_dlg_accepted_agreement
    (guardEvidence agreementEvidence searchControlAccounting : Prop) :
    ay_dlg_accepted_level_state guardEvidence agreementEvidence
      searchControlAccounting ->
    agreementEvidence :=
  fun accepted =>
    ay_dlg_conj_left agreementEvidence searchControlAccounting
      (ay_dlg_conj_right guardEvidence
        (ay_dlg_conj agreementEvidence searchControlAccounting) accepted)

theorem ay_dlg_accepted_search_control
    (guardEvidence agreementEvidence searchControlAccounting : Prop) :
    ay_dlg_accepted_level_state guardEvidence agreementEvidence
      searchControlAccounting ->
    searchControlAccounting :=
  fun accepted =>
    ay_dlg_conj_right agreementEvidence searchControlAccounting
      (ay_dlg_conj_right guardEvidence
        (ay_dlg_conj agreementEvidence searchControlAccounting) accepted)

theorem ay_dlg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_dlg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_dlg_conj_intro acceptedEvidence (ay_dlg_conj outcome formulaTruth)
      acceptedH (ay_dlg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_dlg_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_dlg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_dlg_conj_left acceptedEvidence (ay_dlg_conj outcome formulaTruth)
      report

theorem ay_dlg_public_report_outcome
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_dlg_public_report acceptedEvidence outcome formulaTruth ->
    outcome :=
  fun report =>
    ay_dlg_conj_left outcome formulaTruth
      (ay_dlg_conj_right acceptedEvidence
        (ay_dlg_conj outcome formulaTruth) report)

theorem ay_dlg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_dlg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_dlg_conj_right outcome formulaTruth
      (ay_dlg_conj_right acceptedEvidence
        (ay_dlg_conj outcome formulaTruth) report)

theorem ay_dlg_preserves_formula_truth
    (originalFormulaTruth guardedStateTruth : Prop) :
    ay_dlg_equisat originalFormulaTruth guardedStateTruth ->
    originalFormulaTruth ->
    guardedStateTruth :=
  fun eqsat truth =>
    ay_dlg_equisat_forward originalFormulaTruth guardedStateTruth eqsat truth

theorem ay_dlg_reflects_formula_truth
    (originalFormulaTruth guardedStateTruth : Prop) :
    ay_dlg_equisat originalFormulaTruth guardedStateTruth ->
    guardedStateTruth ->
    originalFormulaTruth :=
  fun eqsat truth =>
    ay_dlg_equisat_backward originalFormulaTruth guardedStateTruth eqsat truth

theorem ay_dlg_accepted_preserves_public_soundness
    (guardEvidence agreementEvidence searchControlAccounting publicSoundness :
      Prop) :
    ay_dlg_accepted_level_state guardEvidence agreementEvidence
      searchControlAccounting ->
    (agreementEvidence -> publicSoundness) ->
    publicSoundness :=
  fun accepted project =>
    project
      (ay_dlg_accepted_agreement guardEvidence agreementEvidence
        searchControlAccounting accepted)

theorem ay_dlg_no_claim_intro (diagnostic fallbackOrRecompute : Prop) :
    diagnostic ->
    fallbackOrRecompute ->
    ay_dlg_no_claim diagnostic fallbackOrRecompute :=
  ay_dlg_conj_intro diagnostic fallbackOrRecompute

theorem ay_dlg_no_claim_recompute
    (diagnostic fallbackOrRecompute : Prop) :
    ay_dlg_no_claim diagnostic fallbackOrRecompute ->
    fallbackOrRecompute :=
  ay_dlg_conj_right diagnostic fallbackOrRecompute

theorem ay_dlg_domain_mismatch_no_claim
    (domainMismatch fallbackOrRecompute : Prop) :
    domainMismatch ->
    fallbackOrRecompute ->
    ay_dlg_no_claim domainMismatch fallbackOrRecompute :=
  ay_dlg_no_claim_intro domainMismatch fallbackOrRecompute

theorem ay_dlg_trail_mismatch_no_claim
    (trailMismatch fallbackOrRecompute : Prop) :
    trailMismatch ->
    fallbackOrRecompute ->
    ay_dlg_no_claim trailMismatch fallbackOrRecompute :=
  ay_dlg_no_claim_intro trailMismatch fallbackOrRecompute

theorem ay_dlg_level_map_mismatch_no_claim
    (levelMapMismatch fallbackOrRecompute : Prop) :
    levelMapMismatch ->
    fallbackOrRecompute ->
    ay_dlg_no_claim levelMapMismatch fallbackOrRecompute :=
  ay_dlg_no_claim_intro levelMapMismatch fallbackOrRecompute

theorem ay_dlg_contiguity_mismatch_no_claim
    (contiguityMismatch fallbackOrRecompute : Prop) :
    contiguityMismatch ->
    fallbackOrRecompute ->
    ay_dlg_no_claim contiguityMismatch fallbackOrRecompute :=
  ay_dlg_no_claim_intro contiguityMismatch fallbackOrRecompute

theorem ay_dlg_reason_mismatch_no_claim
    (reasonMismatch fallbackOrRecompute : Prop) :
    reasonMismatch ->
    fallbackOrRecompute ->
    ay_dlg_no_claim reasonMismatch fallbackOrRecompute :=
  ay_dlg_no_claim_intro reasonMismatch fallbackOrRecompute

theorem ay_dlg_replay_mismatch_no_claim
    (replayMismatch fallbackOrRecompute : Prop) :
    replayMismatch ->
    fallbackOrRecompute ->
    ay_dlg_no_claim replayMismatch fallbackOrRecompute :=
  ay_dlg_no_claim_intro replayMismatch fallbackOrRecompute

theorem ay_dlg_build_mismatch_no_claim
    (buildMismatch fallbackOrRecompute : Prop) :
    buildMismatch ->
    fallbackOrRecompute ->
    ay_dlg_no_claim buildMismatch fallbackOrRecompute :=
  ay_dlg_no_claim_intro buildMismatch fallbackOrRecompute

theorem ay_dlg_validator_mismatch_no_claim
    (validatorMismatch fallbackOrRecompute : Prop) :
    validatorMismatch ->
    fallbackOrRecompute ->
    ay_dlg_no_claim validatorMismatch fallbackOrRecompute :=
  ay_dlg_no_claim_intro validatorMismatch fallbackOrRecompute

theorem ay_dlg_audit_mismatch_no_claim
    (auditMismatch fallbackOrRecompute : Prop) :
    auditMismatch ->
    fallbackOrRecompute ->
    ay_dlg_no_claim auditMismatch fallbackOrRecompute :=
  ay_dlg_no_claim_intro auditMismatch fallbackOrRecompute

theorem ay_dlg_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicSatOrUnsat : Prop) :
    ay_dlg_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicSatOrUnsat -> fallbackPublic) ->
    publicSatOrUnsat ->
    fallbackPublic :=
  fun noClaim fallbackPublishes publication =>
    fallbackPublishes
      (ay_dlg_no_claim_recompute failedGuard fallbackPublic noClaim)
      publication

theorem ay_dlg_publication_requires_guard
    (guardEvidence agreementEvidence searchControlAccounting outcome
      formulaTruth : Prop) :
    ay_dlg_public_report
      (ay_dlg_accepted_level_state guardEvidence agreementEvidence
        searchControlAccounting)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_dlg_accepted_guard guardEvidence agreementEvidence
      searchControlAccounting
      (ay_dlg_public_report_accepted
        (ay_dlg_accepted_level_state guardEvidence agreementEvidence
          searchControlAccounting)
        outcome formulaTruth report)

theorem ay_dlg_publication_requires_validator
    (variableDomainDigest trailSnapshotDigest decisionLevelMap
      levelContiguityWitness reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      agreementEvidence searchControlAccounting outcome formulaTruth : Prop) :
    ay_dlg_public_report
      (ay_dlg_accepted_level_state
        (ay_dlg_guard variableDomainDigest trailSnapshotDigest
          decisionLevelMap levelContiguityWitness reasonClauseLedger
          propagationReplay fallbackBaseline solverBuildEvidence validatorGate
          auditTranscript)
        agreementEvidence searchControlAccounting)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_dlg_guard_validator variableDomainDigest trailSnapshotDigest
      decisionLevelMap levelContiguityWitness reasonClauseLedger
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript
      (ay_dlg_publication_requires_guard
        (ay_dlg_guard variableDomainDigest trailSnapshotDigest
          decisionLevelMap levelContiguityWitness reasonClauseLedger
          propagationReplay fallbackBaseline solverBuildEvidence validatorGate
          auditTranscript)
        agreementEvidence searchControlAccounting outcome formulaTruth report)

theorem ay_dlg_publication_requires_audit
    (variableDomainDigest trailSnapshotDigest decisionLevelMap
      levelContiguityWitness reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      agreementEvidence searchControlAccounting outcome formulaTruth : Prop) :
    ay_dlg_public_report
      (ay_dlg_accepted_level_state
        (ay_dlg_guard variableDomainDigest trailSnapshotDigest
          decisionLevelMap levelContiguityWitness reasonClauseLedger
          propagationReplay fallbackBaseline solverBuildEvidence validatorGate
          auditTranscript)
        agreementEvidence searchControlAccounting)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_dlg_guard_audit variableDomainDigest trailSnapshotDigest decisionLevelMap
      levelContiguityWitness reasonClauseLedger propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      (ay_dlg_publication_requires_guard
        (ay_dlg_guard variableDomainDigest trailSnapshotDigest
          decisionLevelMap levelContiguityWitness reasonClauseLedger
          propagationReplay fallbackBaseline solverBuildEvidence validatorGate
          auditTranscript)
        agreementEvidence searchControlAccounting outcome formulaTruth report)

theorem ay_dlg_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_dlg_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_dlg_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_dlg_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_dlg_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_dlg_public_report_intro acceptedEvidence unsatOutcome formulaTruth
