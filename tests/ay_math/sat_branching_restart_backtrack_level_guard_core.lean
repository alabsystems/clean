-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Restart/backtrack-level guard for sequential main-track CDCL SAT.
-- Backtrack level selection is search-control only when trail, learned clause,
-- stack, replay, fallback, build, validator, and audit evidence agree.

def ay_rblg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_rblg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_rblg_conj (before -> after) (after -> before)

def ay_rblg_guard
    (variableDomainDigest : Prop)
    (trailSnapshotDigest : Prop)
    (learnedClauseDigest : Prop)
    (decisionStackDigest : Prop)
    (backtrackLevelWitness : Prop)
    (propagationReplay : Prop)
    (deterministicTiebreakManifest : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (variableDomainDigest ->
      trailSnapshotDigest ->
      learnedClauseDigest ->
      decisionStackDigest ->
      backtrackLevelWitness ->
      propagationReplay ->
      deterministicTiebreakManifest ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_rblg_agreement
    (originalFormulaTruth : Prop)
    (guardedRunTruth : Prop)
    (publicSoundness : Prop) : Prop :=
  ay_rblg_conj
    (ay_rblg_equisat originalFormulaTruth guardedRunTruth)
    publicSoundness

def ay_rblg_accepted_backtrack
    (guardEvidence agreementEvidence searchControlHint : Prop) : Prop :=
  ay_rblg_conj guardEvidence
    (ay_rblg_conj agreementEvidence searchControlHint)

def ay_rblg_public_report
    (acceptedEvidence outcome formulaTruth : Prop) : Prop :=
  ay_rblg_conj acceptedEvidence
    (ay_rblg_conj outcome formulaTruth)

def ay_rblg_no_claim (diagnostic fallbackOrRecompute : Prop) : Prop :=
  ay_rblg_conj diagnostic fallbackOrRecompute

theorem ay_rblg_conj_intro (left right : Prop) :
    left -> right -> ay_rblg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_rblg_conj_left (left right : Prop) :
    ay_rblg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_rblg_conj_right (left right : Prop) :
    ay_rblg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_rblg_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_rblg_equisat before after :=
  fun forward backward =>
    ay_rblg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_rblg_equisat_forward (before after : Prop) :
    ay_rblg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_rblg_conj_left (before -> after) (after -> before) eqsat

theorem ay_rblg_equisat_backward (before after : Prop) :
    ay_rblg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_rblg_conj_right (before -> after) (after -> before) eqsat

theorem ay_rblg_guard_intro
    (variableDomainDigest trailSnapshotDigest learnedClauseDigest
      decisionStackDigest backtrackLevelWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    variableDomainDigest ->
    trailSnapshotDigest ->
    learnedClauseDigest ->
    decisionStackDigest ->
    backtrackLevelWitness ->
    propagationReplay ->
    deterministicTiebreakManifest ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_rblg_guard variableDomainDigest trailSnapshotDigest learnedClauseDigest
      decisionStackDigest backtrackLevelWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript :=
  fun domainH trailH clauseH stackH levelH replayH tieH fallbackH buildH
      validatorH auditH result make =>
    make domainH trailH clauseH stackH levelH replayH tieH fallbackH buildH
      validatorH auditH

theorem ay_rblg_guard_domain
    (variableDomainDigest trailSnapshotDigest learnedClauseDigest
      decisionStackDigest backtrackLevelWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_rblg_guard variableDomainDigest trailSnapshotDigest learnedClauseDigest
      decisionStackDigest backtrackLevelWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    variableDomainDigest :=
  fun guard =>
    guard variableDomainDigest
      (fun domainH _trailH _clauseH _stackH _levelH _replayH _tieH
          _fallbackH _buildH _validatorH _auditH => domainH)

theorem ay_rblg_guard_trail
    (variableDomainDigest trailSnapshotDigest learnedClauseDigest
      decisionStackDigest backtrackLevelWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_rblg_guard variableDomainDigest trailSnapshotDigest learnedClauseDigest
      decisionStackDigest backtrackLevelWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    trailSnapshotDigest :=
  fun guard =>
    guard trailSnapshotDigest
      (fun _domainH trailH _clauseH _stackH _levelH _replayH _tieH
          _fallbackH _buildH _validatorH _auditH => trailH)

theorem ay_rblg_guard_learned_clause
    (variableDomainDigest trailSnapshotDigest learnedClauseDigest
      decisionStackDigest backtrackLevelWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_rblg_guard variableDomainDigest trailSnapshotDigest learnedClauseDigest
      decisionStackDigest backtrackLevelWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    learnedClauseDigest :=
  fun guard =>
    guard learnedClauseDigest
      (fun _domainH _trailH clauseH _stackH _levelH _replayH _tieH
          _fallbackH _buildH _validatorH _auditH => clauseH)

theorem ay_rblg_guard_stack
    (variableDomainDigest trailSnapshotDigest learnedClauseDigest
      decisionStackDigest backtrackLevelWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_rblg_guard variableDomainDigest trailSnapshotDigest learnedClauseDigest
      decisionStackDigest backtrackLevelWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    decisionStackDigest :=
  fun guard =>
    guard decisionStackDigest
      (fun _domainH _trailH _clauseH stackH _levelH _replayH _tieH
          _fallbackH _buildH _validatorH _auditH => stackH)

theorem ay_rblg_guard_level
    (variableDomainDigest trailSnapshotDigest learnedClauseDigest
      decisionStackDigest backtrackLevelWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_rblg_guard variableDomainDigest trailSnapshotDigest learnedClauseDigest
      decisionStackDigest backtrackLevelWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    backtrackLevelWitness :=
  fun guard =>
    guard backtrackLevelWitness
      (fun _domainH _trailH _clauseH _stackH levelH _replayH _tieH
          _fallbackH _buildH _validatorH _auditH => levelH)

theorem ay_rblg_guard_replay
    (variableDomainDigest trailSnapshotDigest learnedClauseDigest
      decisionStackDigest backtrackLevelWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_rblg_guard variableDomainDigest trailSnapshotDigest learnedClauseDigest
      decisionStackDigest backtrackLevelWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _domainH _trailH _clauseH _stackH _levelH replayH _tieH
          _fallbackH _buildH _validatorH _auditH => replayH)

theorem ay_rblg_guard_tiebreak
    (variableDomainDigest trailSnapshotDigest learnedClauseDigest
      decisionStackDigest backtrackLevelWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_rblg_guard variableDomainDigest trailSnapshotDigest learnedClauseDigest
      decisionStackDigest backtrackLevelWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    deterministicTiebreakManifest :=
  fun guard =>
    guard deterministicTiebreakManifest
      (fun _domainH _trailH _clauseH _stackH _levelH _replayH tieH
          _fallbackH _buildH _validatorH _auditH => tieH)

theorem ay_rblg_guard_fallback
    (variableDomainDigest trailSnapshotDigest learnedClauseDigest
      decisionStackDigest backtrackLevelWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_rblg_guard variableDomainDigest trailSnapshotDigest learnedClauseDigest
      decisionStackDigest backtrackLevelWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _domainH _trailH _clauseH _stackH _levelH _replayH _tieH
          fallbackH _buildH _validatorH _auditH => fallbackH)

theorem ay_rblg_guard_build
    (variableDomainDigest trailSnapshotDigest learnedClauseDigest
      decisionStackDigest backtrackLevelWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_rblg_guard variableDomainDigest trailSnapshotDigest learnedClauseDigest
      decisionStackDigest backtrackLevelWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _domainH _trailH _clauseH _stackH _levelH _replayH _tieH
          _fallbackH buildH _validatorH _auditH => buildH)

theorem ay_rblg_guard_validator
    (variableDomainDigest trailSnapshotDigest learnedClauseDigest
      decisionStackDigest backtrackLevelWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_rblg_guard variableDomainDigest trailSnapshotDigest learnedClauseDigest
      decisionStackDigest backtrackLevelWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _domainH _trailH _clauseH _stackH _levelH _replayH _tieH
          _fallbackH _buildH validatorH _auditH => validatorH)

theorem ay_rblg_guard_audit
    (variableDomainDigest trailSnapshotDigest learnedClauseDigest
      decisionStackDigest backtrackLevelWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript : Prop) :
    ay_rblg_guard variableDomainDigest trailSnapshotDigest learnedClauseDigest
      decisionStackDigest backtrackLevelWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _domainH _trailH _clauseH _stackH _levelH _replayH _tieH
          _fallbackH _buildH _validatorH auditH => auditH)

theorem ay_rblg_agreement_intro
    (originalFormulaTruth guardedRunTruth publicSoundness : Prop) :
    ay_rblg_equisat originalFormulaTruth guardedRunTruth ->
    publicSoundness ->
    ay_rblg_agreement originalFormulaTruth guardedRunTruth publicSoundness :=
  fun eqsat sound =>
    ay_rblg_conj_intro
      (ay_rblg_equisat originalFormulaTruth guardedRunTruth)
      publicSoundness eqsat sound

theorem ay_rblg_accepted_backtrack_intro
    (guardEvidence agreementEvidence searchControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    searchControlHint ->
    ay_rblg_accepted_backtrack guardEvidence agreementEvidence searchControlHint :=
  fun guardH agreementH hintH =>
    ay_rblg_conj_intro guardEvidence
      (ay_rblg_conj agreementEvidence searchControlHint) guardH
      (ay_rblg_conj_intro agreementEvidence searchControlHint agreementH hintH)

theorem ay_rblg_accepted_guard
    (guardEvidence agreementEvidence searchControlHint : Prop) :
    ay_rblg_accepted_backtrack guardEvidence agreementEvidence searchControlHint ->
    guardEvidence :=
  fun accepted =>
    ay_rblg_conj_left guardEvidence
      (ay_rblg_conj agreementEvidence searchControlHint) accepted

theorem ay_rblg_accepted_agreement
    (guardEvidence agreementEvidence searchControlHint : Prop) :
    ay_rblg_accepted_backtrack guardEvidence agreementEvidence searchControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_rblg_conj_left agreementEvidence searchControlHint
      (ay_rblg_conj_right guardEvidence
        (ay_rblg_conj agreementEvidence searchControlHint) accepted)

theorem ay_rblg_accepted_search_control
    (guardEvidence agreementEvidence searchControlHint : Prop) :
    ay_rblg_accepted_backtrack guardEvidence agreementEvidence searchControlHint ->
    searchControlHint :=
  fun accepted =>
    ay_rblg_conj_right agreementEvidence searchControlHint
      (ay_rblg_conj_right guardEvidence
        (ay_rblg_conj agreementEvidence searchControlHint) accepted)

theorem ay_rblg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_rblg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_rblg_conj_intro acceptedEvidence (ay_rblg_conj outcome formulaTruth)
      acceptedH (ay_rblg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_rblg_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_rblg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_rblg_conj_left acceptedEvidence (ay_rblg_conj outcome formulaTruth)
      report

theorem ay_rblg_public_report_outcome
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_rblg_public_report acceptedEvidence outcome formulaTruth ->
    outcome :=
  fun report =>
    ay_rblg_conj_left outcome formulaTruth
      (ay_rblg_conj_right acceptedEvidence
        (ay_rblg_conj outcome formulaTruth) report)

theorem ay_rblg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_rblg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_rblg_conj_right outcome formulaTruth
      (ay_rblg_conj_right acceptedEvidence
        (ay_rblg_conj outcome formulaTruth) report)

theorem ay_rblg_preserves_formula_truth
    (originalFormulaTruth guardedRunTruth : Prop) :
    ay_rblg_equisat originalFormulaTruth guardedRunTruth ->
    originalFormulaTruth ->
    guardedRunTruth :=
  fun eqsat truth =>
    ay_rblg_equisat_forward originalFormulaTruth guardedRunTruth eqsat truth

theorem ay_rblg_reflects_formula_truth
    (originalFormulaTruth guardedRunTruth : Prop) :
    ay_rblg_equisat originalFormulaTruth guardedRunTruth ->
    guardedRunTruth ->
    originalFormulaTruth :=
  fun eqsat truth =>
    ay_rblg_equisat_backward originalFormulaTruth guardedRunTruth eqsat truth

theorem ay_rblg_accepted_preserves_public_soundness
    (guardEvidence agreementEvidence searchControlHint publicSoundness : Prop) :
    ay_rblg_accepted_backtrack guardEvidence agreementEvidence searchControlHint ->
    (agreementEvidence -> publicSoundness) ->
    publicSoundness :=
  fun accepted project =>
    project
      (ay_rblg_accepted_agreement guardEvidence agreementEvidence
        searchControlHint accepted)

theorem ay_rblg_no_claim_intro (diagnostic fallbackOrRecompute : Prop) :
    diagnostic ->
    fallbackOrRecompute ->
    ay_rblg_no_claim diagnostic fallbackOrRecompute :=
  ay_rblg_conj_intro diagnostic fallbackOrRecompute

theorem ay_rblg_no_claim_recompute
    (diagnostic fallbackOrRecompute : Prop) :
    ay_rblg_no_claim diagnostic fallbackOrRecompute ->
    fallbackOrRecompute :=
  ay_rblg_conj_right diagnostic fallbackOrRecompute

theorem ay_rblg_domain_mismatch_no_claim
    (domainMismatch fallbackOrRecompute : Prop) :
    domainMismatch ->
    fallbackOrRecompute ->
    ay_rblg_no_claim domainMismatch fallbackOrRecompute :=
  ay_rblg_no_claim_intro domainMismatch fallbackOrRecompute

theorem ay_rblg_trail_mismatch_no_claim
    (trailMismatch fallbackOrRecompute : Prop) :
    trailMismatch ->
    fallbackOrRecompute ->
    ay_rblg_no_claim trailMismatch fallbackOrRecompute :=
  ay_rblg_no_claim_intro trailMismatch fallbackOrRecompute

theorem ay_rblg_learned_clause_mismatch_no_claim
    (clauseMismatch fallbackOrRecompute : Prop) :
    clauseMismatch ->
    fallbackOrRecompute ->
    ay_rblg_no_claim clauseMismatch fallbackOrRecompute :=
  ay_rblg_no_claim_intro clauseMismatch fallbackOrRecompute

theorem ay_rblg_stack_mismatch_no_claim
    (stackMismatch fallbackOrRecompute : Prop) :
    stackMismatch ->
    fallbackOrRecompute ->
    ay_rblg_no_claim stackMismatch fallbackOrRecompute :=
  ay_rblg_no_claim_intro stackMismatch fallbackOrRecompute

theorem ay_rblg_level_mismatch_no_claim
    (levelMismatch fallbackOrRecompute : Prop) :
    levelMismatch ->
    fallbackOrRecompute ->
    ay_rblg_no_claim levelMismatch fallbackOrRecompute :=
  ay_rblg_no_claim_intro levelMismatch fallbackOrRecompute

theorem ay_rblg_replay_mismatch_no_claim
    (replayMismatch fallbackOrRecompute : Prop) :
    replayMismatch ->
    fallbackOrRecompute ->
    ay_rblg_no_claim replayMismatch fallbackOrRecompute :=
  ay_rblg_no_claim_intro replayMismatch fallbackOrRecompute

theorem ay_rblg_tiebreak_mismatch_no_claim
    (tiebreakMismatch fallbackOrRecompute : Prop) :
    tiebreakMismatch ->
    fallbackOrRecompute ->
    ay_rblg_no_claim tiebreakMismatch fallbackOrRecompute :=
  ay_rblg_no_claim_intro tiebreakMismatch fallbackOrRecompute

theorem ay_rblg_build_mismatch_no_claim
    (buildMismatch fallbackOrRecompute : Prop) :
    buildMismatch ->
    fallbackOrRecompute ->
    ay_rblg_no_claim buildMismatch fallbackOrRecompute :=
  ay_rblg_no_claim_intro buildMismatch fallbackOrRecompute

theorem ay_rblg_validator_mismatch_no_claim
    (validatorMismatch fallbackOrRecompute : Prop) :
    validatorMismatch ->
    fallbackOrRecompute ->
    ay_rblg_no_claim validatorMismatch fallbackOrRecompute :=
  ay_rblg_no_claim_intro validatorMismatch fallbackOrRecompute

theorem ay_rblg_audit_mismatch_no_claim
    (auditMismatch fallbackOrRecompute : Prop) :
    auditMismatch ->
    fallbackOrRecompute ->
    ay_rblg_no_claim auditMismatch fallbackOrRecompute :=
  ay_rblg_no_claim_intro auditMismatch fallbackOrRecompute

theorem ay_rblg_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicSatOrUnsat : Prop) :
    ay_rblg_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicSatOrUnsat -> fallbackPublic) ->
    publicSatOrUnsat ->
    fallbackPublic :=
  fun noClaim fallbackPublishes publication =>
    fallbackPublishes
      (ay_rblg_no_claim_recompute failedGuard fallbackPublic noClaim)
      publication

theorem ay_rblg_publication_requires_guard
    (guardEvidence agreementEvidence searchControlHint outcome formulaTruth :
      Prop) :
    ay_rblg_public_report
      (ay_rblg_accepted_backtrack guardEvidence agreementEvidence
        searchControlHint)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_rblg_accepted_guard guardEvidence agreementEvidence searchControlHint
      (ay_rblg_public_report_accepted
        (ay_rblg_accepted_backtrack guardEvidence agreementEvidence
          searchControlHint)
        outcome formulaTruth report)

theorem ay_rblg_publication_requires_validator
    (variableDomainDigest trailSnapshotDigest learnedClauseDigest
      decisionStackDigest backtrackLevelWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript agreementEvidence searchControlHint outcome
      formulaTruth : Prop) :
    ay_rblg_public_report
      (ay_rblg_accepted_backtrack
        (ay_rblg_guard variableDomainDigest trailSnapshotDigest
          learnedClauseDigest decisionStackDigest backtrackLevelWitness
          propagationReplay deterministicTiebreakManifest fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence searchControlHint)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_rblg_guard_validator variableDomainDigest trailSnapshotDigest
      learnedClauseDigest decisionStackDigest backtrackLevelWitness
      propagationReplay deterministicTiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript
      (ay_rblg_publication_requires_guard
        (ay_rblg_guard variableDomainDigest trailSnapshotDigest
          learnedClauseDigest decisionStackDigest backtrackLevelWitness
          propagationReplay deterministicTiebreakManifest fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence searchControlHint outcome formulaTruth report)

theorem ay_rblg_publication_requires_audit
    (variableDomainDigest trailSnapshotDigest learnedClauseDigest
      decisionStackDigest backtrackLevelWitness propagationReplay
      deterministicTiebreakManifest fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript agreementEvidence searchControlHint outcome
      formulaTruth : Prop) :
    ay_rblg_public_report
      (ay_rblg_accepted_backtrack
        (ay_rblg_guard variableDomainDigest trailSnapshotDigest
          learnedClauseDigest decisionStackDigest backtrackLevelWitness
          propagationReplay deterministicTiebreakManifest fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence searchControlHint)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_rblg_guard_audit variableDomainDigest trailSnapshotDigest
      learnedClauseDigest decisionStackDigest backtrackLevelWitness
      propagationReplay deterministicTiebreakManifest fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript
      (ay_rblg_publication_requires_guard
        (ay_rblg_guard variableDomainDigest trailSnapshotDigest
          learnedClauseDigest decisionStackDigest backtrackLevelWitness
          propagationReplay deterministicTiebreakManifest fallbackBaseline
          solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence searchControlHint outcome formulaTruth report)

theorem ay_rblg_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_rblg_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_rblg_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_rblg_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_rblg_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_rblg_public_report_intro acceptedEvidence unsatOutcome formulaTruth
