-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Branching candidate-legality guard for sequential main-track CDCL.
-- Candidate selection is search-control only when the variable domain, trail,
-- unassigned witness, selection ledger, heuristic, tiebreak, replay, fallback,
-- build, validator, and audit evidence agree.

def ay_clg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_clg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_clg_conj (before -> after) (after -> before)

def ay_clg_guard
    (variableDomainDigest : Prop)
    (assignmentTrailDigest : Prop)
    (unassignedVariableWitness : Prop)
    (candidateSelectionLedger : Prop)
    (decisionHeuristicDigest : Prop)
    (tiebreakManifest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (variableDomainDigest ->
      assignmentTrailDigest ->
      unassignedVariableWitness ->
      candidateSelectionLedger ->
      decisionHeuristicDigest ->
      tiebreakManifest ->
      propagationReplay ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_clg_agreement
    (originalFormulaTruth branchedRunTruth publicSoundness : Prop) : Prop :=
  ay_clg_conj
    (ay_clg_equisat originalFormulaTruth branchedRunTruth)
    publicSoundness

def ay_clg_accepted_candidate
    (guardEvidence agreementEvidence searchControlOnly : Prop) : Prop :=
  ay_clg_conj guardEvidence
    (ay_clg_conj agreementEvidence searchControlOnly)

def ay_clg_public_report
    (acceptedEvidence outcome formulaTruth : Prop) : Prop :=
  ay_clg_conj acceptedEvidence
    (ay_clg_conj outcome formulaTruth)

def ay_clg_no_claim (diagnostic fallbackOrRecompute : Prop) : Prop :=
  ay_clg_conj diagnostic fallbackOrRecompute

theorem ay_clg_conj_intro (left right : Prop) :
    left -> right -> ay_clg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_clg_conj_left (left right : Prop) :
    ay_clg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_clg_conj_right (left right : Prop) :
    ay_clg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_clg_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_clg_equisat before after :=
  fun forward backward =>
    ay_clg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_clg_equisat_forward (before after : Prop) :
    ay_clg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_clg_conj_left (before -> after) (after -> before) eqsat

theorem ay_clg_equisat_backward (before after : Prop) :
    ay_clg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_clg_conj_right (before -> after) (after -> before) eqsat

theorem ay_clg_guard_intro
    (variableDomainDigest assignmentTrailDigest unassignedVariableWitness
      candidateSelectionLedger decisionHeuristicDigest tiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    variableDomainDigest ->
    assignmentTrailDigest ->
    unassignedVariableWitness ->
    candidateSelectionLedger ->
    decisionHeuristicDigest ->
    tiebreakManifest ->
    propagationReplay ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_clg_guard variableDomainDigest assignmentTrailDigest
      unassignedVariableWitness candidateSelectionLedger decisionHeuristicDigest
      tiebreakManifest propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript :=
  fun domainH trailH unassignedH candidateH heuristicH tiebreakH replayH
      fallbackH buildH validatorH auditH result make =>
    make domainH trailH unassignedH candidateH heuristicH tiebreakH replayH
      fallbackH buildH validatorH auditH

theorem ay_clg_guard_domain
    (variableDomainDigest assignmentTrailDigest unassignedVariableWitness
      candidateSelectionLedger decisionHeuristicDigest tiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_clg_guard variableDomainDigest assignmentTrailDigest
      unassignedVariableWitness candidateSelectionLedger decisionHeuristicDigest
      tiebreakManifest propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    variableDomainDigest :=
  fun guard =>
    guard variableDomainDigest
      (fun domainH _trailH _unassignedH _candidateH _heuristicH _tiebreakH
          _replayH _fallbackH _buildH _validatorH _auditH => domainH)

theorem ay_clg_guard_trail
    (variableDomainDigest assignmentTrailDigest unassignedVariableWitness
      candidateSelectionLedger decisionHeuristicDigest tiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_clg_guard variableDomainDigest assignmentTrailDigest
      unassignedVariableWitness candidateSelectionLedger decisionHeuristicDigest
      tiebreakManifest propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    assignmentTrailDigest :=
  fun guard =>
    guard assignmentTrailDigest
      (fun _domainH trailH _unassignedH _candidateH _heuristicH _tiebreakH
          _replayH _fallbackH _buildH _validatorH _auditH => trailH)

theorem ay_clg_guard_unassigned
    (variableDomainDigest assignmentTrailDigest unassignedVariableWitness
      candidateSelectionLedger decisionHeuristicDigest tiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_clg_guard variableDomainDigest assignmentTrailDigest
      unassignedVariableWitness candidateSelectionLedger decisionHeuristicDigest
      tiebreakManifest propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    unassignedVariableWitness :=
  fun guard =>
    guard unassignedVariableWitness
      (fun _domainH _trailH unassignedH _candidateH _heuristicH _tiebreakH
          _replayH _fallbackH _buildH _validatorH _auditH => unassignedH)

theorem ay_clg_guard_candidate
    (variableDomainDigest assignmentTrailDigest unassignedVariableWitness
      candidateSelectionLedger decisionHeuristicDigest tiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_clg_guard variableDomainDigest assignmentTrailDigest
      unassignedVariableWitness candidateSelectionLedger decisionHeuristicDigest
      tiebreakManifest propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    candidateSelectionLedger :=
  fun guard =>
    guard candidateSelectionLedger
      (fun _domainH _trailH _unassignedH candidateH _heuristicH _tiebreakH
          _replayH _fallbackH _buildH _validatorH _auditH => candidateH)

theorem ay_clg_guard_heuristic
    (variableDomainDigest assignmentTrailDigest unassignedVariableWitness
      candidateSelectionLedger decisionHeuristicDigest tiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_clg_guard variableDomainDigest assignmentTrailDigest
      unassignedVariableWitness candidateSelectionLedger decisionHeuristicDigest
      tiebreakManifest propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    decisionHeuristicDigest :=
  fun guard =>
    guard decisionHeuristicDigest
      (fun _domainH _trailH _unassignedH _candidateH heuristicH _tiebreakH
          _replayH _fallbackH _buildH _validatorH _auditH => heuristicH)

theorem ay_clg_guard_tiebreak
    (variableDomainDigest assignmentTrailDigest unassignedVariableWitness
      candidateSelectionLedger decisionHeuristicDigest tiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_clg_guard variableDomainDigest assignmentTrailDigest
      unassignedVariableWitness candidateSelectionLedger decisionHeuristicDigest
      tiebreakManifest propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    tiebreakManifest :=
  fun guard =>
    guard tiebreakManifest
      (fun _domainH _trailH _unassignedH _candidateH _heuristicH tiebreakH
          _replayH _fallbackH _buildH _validatorH _auditH => tiebreakH)

theorem ay_clg_guard_replay
    (variableDomainDigest assignmentTrailDigest unassignedVariableWitness
      candidateSelectionLedger decisionHeuristicDigest tiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_clg_guard variableDomainDigest assignmentTrailDigest
      unassignedVariableWitness candidateSelectionLedger decisionHeuristicDigest
      tiebreakManifest propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _domainH _trailH _unassignedH _candidateH _heuristicH _tiebreakH
          replayH _fallbackH _buildH _validatorH _auditH => replayH)

theorem ay_clg_guard_fallback
    (variableDomainDigest assignmentTrailDigest unassignedVariableWitness
      candidateSelectionLedger decisionHeuristicDigest tiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_clg_guard variableDomainDigest assignmentTrailDigest
      unassignedVariableWitness candidateSelectionLedger decisionHeuristicDigest
      tiebreakManifest propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _domainH _trailH _unassignedH _candidateH _heuristicH _tiebreakH
          _replayH fallbackH _buildH _validatorH _auditH => fallbackH)

theorem ay_clg_guard_build
    (variableDomainDigest assignmentTrailDigest unassignedVariableWitness
      candidateSelectionLedger decisionHeuristicDigest tiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_clg_guard variableDomainDigest assignmentTrailDigest
      unassignedVariableWitness candidateSelectionLedger decisionHeuristicDigest
      tiebreakManifest propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _domainH _trailH _unassignedH _candidateH _heuristicH _tiebreakH
          _replayH _fallbackH buildH _validatorH _auditH => buildH)

theorem ay_clg_guard_validator
    (variableDomainDigest assignmentTrailDigest unassignedVariableWitness
      candidateSelectionLedger decisionHeuristicDigest tiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_clg_guard variableDomainDigest assignmentTrailDigest
      unassignedVariableWitness candidateSelectionLedger decisionHeuristicDigest
      tiebreakManifest propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _domainH _trailH _unassignedH _candidateH _heuristicH _tiebreakH
          _replayH _fallbackH _buildH validatorH _auditH => validatorH)

theorem ay_clg_guard_audit
    (variableDomainDigest assignmentTrailDigest unassignedVariableWitness
      candidateSelectionLedger decisionHeuristicDigest tiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) :
    ay_clg_guard variableDomainDigest assignmentTrailDigest
      unassignedVariableWitness candidateSelectionLedger decisionHeuristicDigest
      tiebreakManifest propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _domainH _trailH _unassignedH _candidateH _heuristicH _tiebreakH
          _replayH _fallbackH _buildH _validatorH auditH => auditH)

theorem ay_clg_agreement_intro
    (originalFormulaTruth branchedRunTruth publicSoundness : Prop) :
    ay_clg_equisat originalFormulaTruth branchedRunTruth ->
    publicSoundness ->
    ay_clg_agreement originalFormulaTruth branchedRunTruth publicSoundness :=
  fun eqsat sound =>
    ay_clg_conj_intro
      (ay_clg_equisat originalFormulaTruth branchedRunTruth)
      publicSoundness eqsat sound

theorem ay_clg_accepted_candidate_intro
    (guardEvidence agreementEvidence searchControlOnly : Prop) :
    guardEvidence ->
    agreementEvidence ->
    searchControlOnly ->
    ay_clg_accepted_candidate guardEvidence agreementEvidence
      searchControlOnly :=
  fun guardH agreementH searchH =>
    ay_clg_conj_intro guardEvidence
      (ay_clg_conj agreementEvidence searchControlOnly) guardH
      (ay_clg_conj_intro agreementEvidence searchControlOnly agreementH
        searchH)

theorem ay_clg_accepted_guard
    (guardEvidence agreementEvidence searchControlOnly : Prop) :
    ay_clg_accepted_candidate guardEvidence agreementEvidence
      searchControlOnly ->
    guardEvidence :=
  fun accepted =>
    ay_clg_conj_left guardEvidence
      (ay_clg_conj agreementEvidence searchControlOnly) accepted

theorem ay_clg_accepted_agreement
    (guardEvidence agreementEvidence searchControlOnly : Prop) :
    ay_clg_accepted_candidate guardEvidence agreementEvidence
      searchControlOnly ->
    agreementEvidence :=
  fun accepted =>
    ay_clg_conj_left agreementEvidence searchControlOnly
      (ay_clg_conj_right guardEvidence
        (ay_clg_conj agreementEvidence searchControlOnly) accepted)

theorem ay_clg_accepted_search_control
    (guardEvidence agreementEvidence searchControlOnly : Prop) :
    ay_clg_accepted_candidate guardEvidence agreementEvidence
      searchControlOnly ->
    searchControlOnly :=
  fun accepted =>
    ay_clg_conj_right agreementEvidence searchControlOnly
      (ay_clg_conj_right guardEvidence
        (ay_clg_conj agreementEvidence searchControlOnly) accepted)

theorem ay_clg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_clg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_clg_conj_intro acceptedEvidence (ay_clg_conj outcome formulaTruth)
      acceptedH (ay_clg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_clg_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_clg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_clg_conj_left acceptedEvidence (ay_clg_conj outcome formulaTruth)
      report

theorem ay_clg_public_report_outcome
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_clg_public_report acceptedEvidence outcome formulaTruth ->
    outcome :=
  fun report =>
    ay_clg_conj_left outcome formulaTruth
      (ay_clg_conj_right acceptedEvidence
        (ay_clg_conj outcome formulaTruth) report)

theorem ay_clg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_clg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_clg_conj_right outcome formulaTruth
      (ay_clg_conj_right acceptedEvidence
        (ay_clg_conj outcome formulaTruth) report)

theorem ay_clg_preserves_formula_truth
    (originalFormulaTruth branchedRunTruth : Prop) :
    ay_clg_equisat originalFormulaTruth branchedRunTruth ->
    originalFormulaTruth ->
    branchedRunTruth :=
  fun eqsat truth =>
    ay_clg_equisat_forward originalFormulaTruth branchedRunTruth eqsat truth

theorem ay_clg_reflects_formula_truth
    (originalFormulaTruth branchedRunTruth : Prop) :
    ay_clg_equisat originalFormulaTruth branchedRunTruth ->
    branchedRunTruth ->
    originalFormulaTruth :=
  fun eqsat truth =>
    ay_clg_equisat_backward originalFormulaTruth branchedRunTruth eqsat truth

theorem ay_clg_accepted_preserves_public_soundness
    (guardEvidence agreementEvidence searchControlOnly publicSoundness : Prop) :
    ay_clg_accepted_candidate guardEvidence agreementEvidence
      searchControlOnly ->
    (agreementEvidence -> publicSoundness) ->
    publicSoundness :=
  fun accepted project =>
    project
      (ay_clg_accepted_agreement guardEvidence agreementEvidence
        searchControlOnly accepted)

theorem ay_clg_no_claim_intro (diagnostic fallbackOrRecompute : Prop) :
    diagnostic ->
    fallbackOrRecompute ->
    ay_clg_no_claim diagnostic fallbackOrRecompute :=
  ay_clg_conj_intro diagnostic fallbackOrRecompute

theorem ay_clg_no_claim_recompute
    (diagnostic fallbackOrRecompute : Prop) :
    ay_clg_no_claim diagnostic fallbackOrRecompute ->
    fallbackOrRecompute :=
  ay_clg_conj_right diagnostic fallbackOrRecompute

theorem ay_clg_domain_mismatch_no_claim
    (domainMismatch fallbackOrRecompute : Prop) :
    domainMismatch ->
    fallbackOrRecompute ->
    ay_clg_no_claim domainMismatch fallbackOrRecompute :=
  ay_clg_no_claim_intro domainMismatch fallbackOrRecompute

theorem ay_clg_trail_mismatch_no_claim
    (trailMismatch fallbackOrRecompute : Prop) :
    trailMismatch ->
    fallbackOrRecompute ->
    ay_clg_no_claim trailMismatch fallbackOrRecompute :=
  ay_clg_no_claim_intro trailMismatch fallbackOrRecompute

theorem ay_clg_assigned_mismatch_no_claim
    (assignedMismatch fallbackOrRecompute : Prop) :
    assignedMismatch ->
    fallbackOrRecompute ->
    ay_clg_no_claim assignedMismatch fallbackOrRecompute :=
  ay_clg_no_claim_intro assignedMismatch fallbackOrRecompute

theorem ay_clg_candidate_mismatch_no_claim
    (candidateMismatch fallbackOrRecompute : Prop) :
    candidateMismatch ->
    fallbackOrRecompute ->
    ay_clg_no_claim candidateMismatch fallbackOrRecompute :=
  ay_clg_no_claim_intro candidateMismatch fallbackOrRecompute

theorem ay_clg_heuristic_mismatch_no_claim
    (heuristicMismatch fallbackOrRecompute : Prop) :
    heuristicMismatch ->
    fallbackOrRecompute ->
    ay_clg_no_claim heuristicMismatch fallbackOrRecompute :=
  ay_clg_no_claim_intro heuristicMismatch fallbackOrRecompute

theorem ay_clg_tiebreak_mismatch_no_claim
    (tiebreakMismatch fallbackOrRecompute : Prop) :
    tiebreakMismatch ->
    fallbackOrRecompute ->
    ay_clg_no_claim tiebreakMismatch fallbackOrRecompute :=
  ay_clg_no_claim_intro tiebreakMismatch fallbackOrRecompute

theorem ay_clg_replay_mismatch_no_claim
    (replayMismatch fallbackOrRecompute : Prop) :
    replayMismatch ->
    fallbackOrRecompute ->
    ay_clg_no_claim replayMismatch fallbackOrRecompute :=
  ay_clg_no_claim_intro replayMismatch fallbackOrRecompute

theorem ay_clg_build_mismatch_no_claim
    (buildMismatch fallbackOrRecompute : Prop) :
    buildMismatch ->
    fallbackOrRecompute ->
    ay_clg_no_claim buildMismatch fallbackOrRecompute :=
  ay_clg_no_claim_intro buildMismatch fallbackOrRecompute

theorem ay_clg_validator_mismatch_no_claim
    (validatorMismatch fallbackOrRecompute : Prop) :
    validatorMismatch ->
    fallbackOrRecompute ->
    ay_clg_no_claim validatorMismatch fallbackOrRecompute :=
  ay_clg_no_claim_intro validatorMismatch fallbackOrRecompute

theorem ay_clg_audit_mismatch_no_claim
    (auditMismatch fallbackOrRecompute : Prop) :
    auditMismatch ->
    fallbackOrRecompute ->
    ay_clg_no_claim auditMismatch fallbackOrRecompute :=
  ay_clg_no_claim_intro auditMismatch fallbackOrRecompute

theorem ay_clg_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicSatOrUnsat : Prop) :
    ay_clg_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicSatOrUnsat -> fallbackPublic) ->
    publicSatOrUnsat ->
    fallbackPublic :=
  fun noClaim fallbackPublishes publication =>
    fallbackPublishes
      (ay_clg_no_claim_recompute failedGuard fallbackPublic noClaim)
      publication

theorem ay_clg_publication_requires_guard
    (guardEvidence agreementEvidence searchControlOnly outcome formulaTruth :
      Prop) :
    ay_clg_public_report
      (ay_clg_accepted_candidate guardEvidence agreementEvidence
        searchControlOnly)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_clg_accepted_guard guardEvidence agreementEvidence searchControlOnly
      (ay_clg_public_report_accepted
        (ay_clg_accepted_candidate guardEvidence agreementEvidence
          searchControlOnly)
        outcome formulaTruth report)

theorem ay_clg_publication_requires_validator
    (variableDomainDigest assignmentTrailDigest unassignedVariableWitness
      candidateSelectionLedger decisionHeuristicDigest tiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript agreementEvidence searchControlOnly outcome formulaTruth :
      Prop) :
    ay_clg_public_report
      (ay_clg_accepted_candidate
        (ay_clg_guard variableDomainDigest assignmentTrailDigest
          unassignedVariableWitness candidateSelectionLedger
          decisionHeuristicDigest tiebreakManifest propagationReplay
          fallbackBaseline solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence searchControlOnly)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_clg_guard_validator variableDomainDigest assignmentTrailDigest
      unassignedVariableWitness candidateSelectionLedger decisionHeuristicDigest
      tiebreakManifest propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript
      (ay_clg_publication_requires_guard
        (ay_clg_guard variableDomainDigest assignmentTrailDigest
          unassignedVariableWitness candidateSelectionLedger
          decisionHeuristicDigest tiebreakManifest propagationReplay
          fallbackBaseline solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence searchControlOnly outcome formulaTruth report)

theorem ay_clg_publication_requires_audit
    (variableDomainDigest assignmentTrailDigest unassignedVariableWitness
      candidateSelectionLedger decisionHeuristicDigest tiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript agreementEvidence searchControlOnly outcome formulaTruth :
      Prop) :
    ay_clg_public_report
      (ay_clg_accepted_candidate
        (ay_clg_guard variableDomainDigest assignmentTrailDigest
          unassignedVariableWitness candidateSelectionLedger
          decisionHeuristicDigest tiebreakManifest propagationReplay
          fallbackBaseline solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence searchControlOnly)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_clg_guard_audit variableDomainDigest assignmentTrailDigest
      unassignedVariableWitness candidateSelectionLedger decisionHeuristicDigest
      tiebreakManifest propagationReplay fallbackBaseline solverBuildEvidence
      validatorGate auditTranscript
      (ay_clg_publication_requires_guard
        (ay_clg_guard variableDomainDigest assignmentTrailDigest
          unassignedVariableWitness candidateSelectionLedger
          decisionHeuristicDigest tiebreakManifest propagationReplay
          fallbackBaseline solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence searchControlOnly outcome formulaTruth report)

theorem ay_clg_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_clg_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_clg_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_clg_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_clg_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_clg_public_report_intro acceptedEvidence unsatOutcome formulaTruth
