-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Heap-property guard for ay branching priority queues.
-- Heap maintenance is heuristic data-structure maintenance only; public
-- SAT/UNSAT soundness must come from accepted evidence tied to the same
-- domain, activity, queue, update, replay, build, validator, and audit context.

def ay_pqhg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pqhg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_pqhg_conj (before -> after) (after -> before)

def ay_pqhg_guard
    (variableDomainDigest : Prop)
    (activityVectorDigest : Prop)
    (priorityQueueDigest : Prop)
    (heapPropertyWitness : Prop)
    (updateRebuildLedger : Prop)
    (candidateLegalityWitness : Prop)
    (tiebreakManifest : Prop)
    (propagationReplayEvidence : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (variableDomainDigest ->
      activityVectorDigest ->
      priorityQueueDigest ->
      heapPropertyWitness ->
      updateRebuildLedger ->
      candidateLegalityWitness ->
      tiebreakManifest ->
      propagationReplayEvidence ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_pqhg_agreement
    (originalFormulaTruth heapGuidedRunTruth publicSoundness : Prop) : Prop :=
  ay_pqhg_conj
    (ay_pqhg_equisat originalFormulaTruth heapGuidedRunTruth)
    publicSoundness

def ay_pqhg_accepted_heap_property
    (guardEvidence agreementEvidence maintenanceOnly : Prop) : Prop :=
  ay_pqhg_conj guardEvidence
    (ay_pqhg_conj agreementEvidence maintenanceOnly)

def ay_pqhg_public_report
    (acceptedEvidence outcome formulaTruth : Prop) : Prop :=
  ay_pqhg_conj acceptedEvidence
    (ay_pqhg_conj outcome formulaTruth)

def ay_pqhg_no_claim (diagnostic fallbackOrRecompute : Prop) : Prop :=
  ay_pqhg_conj diagnostic fallbackOrRecompute

theorem ay_pqhg_conj_intro (left right : Prop) :
    left -> right -> ay_pqhg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_pqhg_conj_left (left right : Prop) :
    ay_pqhg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_pqhg_conj_right (left right : Prop) :
    ay_pqhg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_pqhg_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_pqhg_equisat before after :=
  fun forward backward =>
    ay_pqhg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_pqhg_equisat_forward (before after : Prop) :
    ay_pqhg_equisat before after -> before -> after :=
  fun eqsat =>
    ay_pqhg_conj_left (before -> after) (after -> before) eqsat

theorem ay_pqhg_equisat_backward (before after : Prop) :
    ay_pqhg_equisat before after -> after -> before :=
  fun eqsat =>
    ay_pqhg_conj_right (before -> after) (after -> before) eqsat

theorem ay_pqhg_guard_intro
    (variableDomainDigest activityVectorDigest priorityQueueDigest
      heapPropertyWitness updateRebuildLedger candidateLegalityWitness
      tiebreakManifest propagationReplayEvidence fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    variableDomainDigest ->
    activityVectorDigest ->
    priorityQueueDigest ->
    heapPropertyWitness ->
    updateRebuildLedger ->
    candidateLegalityWitness ->
    tiebreakManifest ->
    propagationReplayEvidence ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_pqhg_guard variableDomainDigest activityVectorDigest priorityQueueDigest
      heapPropertyWitness updateRebuildLedger candidateLegalityWitness
      tiebreakManifest propagationReplayEvidence fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript :=
  fun domainH activityH queueH heapH updateH candidateH tieH replayH
      fallbackH buildH validatorH auditH result make =>
    make domainH activityH queueH heapH updateH candidateH tieH replayH
      fallbackH buildH validatorH auditH

theorem ay_pqhg_guard_domain
    (variableDomainDigest activityVectorDigest priorityQueueDigest
      heapPropertyWitness updateRebuildLedger candidateLegalityWitness
      tiebreakManifest propagationReplayEvidence fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqhg_guard variableDomainDigest activityVectorDigest priorityQueueDigest
      heapPropertyWitness updateRebuildLedger candidateLegalityWitness
      tiebreakManifest propagationReplayEvidence fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    variableDomainDigest :=
  fun guard =>
    guard variableDomainDigest
      (fun domainH _activityH _queueH _heapH _updateH _candidateH _tieH
          _replayH _fallbackH _buildH _validatorH _auditH => domainH)

theorem ay_pqhg_guard_activity
    (variableDomainDigest activityVectorDigest priorityQueueDigest
      heapPropertyWitness updateRebuildLedger candidateLegalityWitness
      tiebreakManifest propagationReplayEvidence fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqhg_guard variableDomainDigest activityVectorDigest priorityQueueDigest
      heapPropertyWitness updateRebuildLedger candidateLegalityWitness
      tiebreakManifest propagationReplayEvidence fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    activityVectorDigest :=
  fun guard =>
    guard activityVectorDigest
      (fun _domainH activityH _queueH _heapH _updateH _candidateH _tieH
          _replayH _fallbackH _buildH _validatorH _auditH => activityH)

theorem ay_pqhg_guard_queue
    (variableDomainDigest activityVectorDigest priorityQueueDigest
      heapPropertyWitness updateRebuildLedger candidateLegalityWitness
      tiebreakManifest propagationReplayEvidence fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqhg_guard variableDomainDigest activityVectorDigest priorityQueueDigest
      heapPropertyWitness updateRebuildLedger candidateLegalityWitness
      tiebreakManifest propagationReplayEvidence fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    priorityQueueDigest :=
  fun guard =>
    guard priorityQueueDigest
      (fun _domainH _activityH queueH _heapH _updateH _candidateH _tieH
          _replayH _fallbackH _buildH _validatorH _auditH => queueH)

theorem ay_pqhg_guard_heap_property
    (variableDomainDigest activityVectorDigest priorityQueueDigest
      heapPropertyWitness updateRebuildLedger candidateLegalityWitness
      tiebreakManifest propagationReplayEvidence fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqhg_guard variableDomainDigest activityVectorDigest priorityQueueDigest
      heapPropertyWitness updateRebuildLedger candidateLegalityWitness
      tiebreakManifest propagationReplayEvidence fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    heapPropertyWitness :=
  fun guard =>
    guard heapPropertyWitness
      (fun _domainH _activityH _queueH heapH _updateH _candidateH _tieH
          _replayH _fallbackH _buildH _validatorH _auditH => heapH)

theorem ay_pqhg_guard_update_rebuild
    (variableDomainDigest activityVectorDigest priorityQueueDigest
      heapPropertyWitness updateRebuildLedger candidateLegalityWitness
      tiebreakManifest propagationReplayEvidence fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqhg_guard variableDomainDigest activityVectorDigest priorityQueueDigest
      heapPropertyWitness updateRebuildLedger candidateLegalityWitness
      tiebreakManifest propagationReplayEvidence fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    updateRebuildLedger :=
  fun guard =>
    guard updateRebuildLedger
      (fun _domainH _activityH _queueH _heapH updateH _candidateH _tieH
          _replayH _fallbackH _buildH _validatorH _auditH => updateH)

theorem ay_pqhg_guard_candidate
    (variableDomainDigest activityVectorDigest priorityQueueDigest
      heapPropertyWitness updateRebuildLedger candidateLegalityWitness
      tiebreakManifest propagationReplayEvidence fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqhg_guard variableDomainDigest activityVectorDigest priorityQueueDigest
      heapPropertyWitness updateRebuildLedger candidateLegalityWitness
      tiebreakManifest propagationReplayEvidence fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    candidateLegalityWitness :=
  fun guard =>
    guard candidateLegalityWitness
      (fun _domainH _activityH _queueH _heapH _updateH candidateH _tieH
          _replayH _fallbackH _buildH _validatorH _auditH => candidateH)

theorem ay_pqhg_guard_tiebreak
    (variableDomainDigest activityVectorDigest priorityQueueDigest
      heapPropertyWitness updateRebuildLedger candidateLegalityWitness
      tiebreakManifest propagationReplayEvidence fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqhg_guard variableDomainDigest activityVectorDigest priorityQueueDigest
      heapPropertyWitness updateRebuildLedger candidateLegalityWitness
      tiebreakManifest propagationReplayEvidence fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    tiebreakManifest :=
  fun guard =>
    guard tiebreakManifest
      (fun _domainH _activityH _queueH _heapH _updateH _candidateH tieH
          _replayH _fallbackH _buildH _validatorH _auditH => tieH)

theorem ay_pqhg_guard_replay
    (variableDomainDigest activityVectorDigest priorityQueueDigest
      heapPropertyWitness updateRebuildLedger candidateLegalityWitness
      tiebreakManifest propagationReplayEvidence fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqhg_guard variableDomainDigest activityVectorDigest priorityQueueDigest
      heapPropertyWitness updateRebuildLedger candidateLegalityWitness
      tiebreakManifest propagationReplayEvidence fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    propagationReplayEvidence :=
  fun guard =>
    guard propagationReplayEvidence
      (fun _domainH _activityH _queueH _heapH _updateH _candidateH _tieH
          replayH _fallbackH _buildH _validatorH _auditH => replayH)

theorem ay_pqhg_guard_fallback
    (variableDomainDigest activityVectorDigest priorityQueueDigest
      heapPropertyWitness updateRebuildLedger candidateLegalityWitness
      tiebreakManifest propagationReplayEvidence fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqhg_guard variableDomainDigest activityVectorDigest priorityQueueDigest
      heapPropertyWitness updateRebuildLedger candidateLegalityWitness
      tiebreakManifest propagationReplayEvidence fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _domainH _activityH _queueH _heapH _updateH _candidateH _tieH
          _replayH fallbackH _buildH _validatorH _auditH => fallbackH)

theorem ay_pqhg_guard_build
    (variableDomainDigest activityVectorDigest priorityQueueDigest
      heapPropertyWitness updateRebuildLedger candidateLegalityWitness
      tiebreakManifest propagationReplayEvidence fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqhg_guard variableDomainDigest activityVectorDigest priorityQueueDigest
      heapPropertyWitness updateRebuildLedger candidateLegalityWitness
      tiebreakManifest propagationReplayEvidence fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _domainH _activityH _queueH _heapH _updateH _candidateH _tieH
          _replayH _fallbackH buildH _validatorH _auditH => buildH)

theorem ay_pqhg_guard_validator
    (variableDomainDigest activityVectorDigest priorityQueueDigest
      heapPropertyWitness updateRebuildLedger candidateLegalityWitness
      tiebreakManifest propagationReplayEvidence fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqhg_guard variableDomainDigest activityVectorDigest priorityQueueDigest
      heapPropertyWitness updateRebuildLedger candidateLegalityWitness
      tiebreakManifest propagationReplayEvidence fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _domainH _activityH _queueH _heapH _updateH _candidateH _tieH
          _replayH _fallbackH _buildH validatorH _auditH => validatorH)

theorem ay_pqhg_guard_audit
    (variableDomainDigest activityVectorDigest priorityQueueDigest
      heapPropertyWitness updateRebuildLedger candidateLegalityWitness
      tiebreakManifest propagationReplayEvidence fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) :
    ay_pqhg_guard variableDomainDigest activityVectorDigest priorityQueueDigest
      heapPropertyWitness updateRebuildLedger candidateLegalityWitness
      tiebreakManifest propagationReplayEvidence fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _domainH _activityH _queueH _heapH _updateH _candidateH _tieH
          _replayH _fallbackH _buildH _validatorH auditH => auditH)

theorem ay_pqhg_agreement_intro
    (originalFormulaTruth heapGuidedRunTruth publicSoundness : Prop) :
    ay_pqhg_equisat originalFormulaTruth heapGuidedRunTruth ->
    publicSoundness ->
    ay_pqhg_agreement originalFormulaTruth heapGuidedRunTruth publicSoundness :=
  fun eqsat sound =>
    ay_pqhg_conj_intro
      (ay_pqhg_equisat originalFormulaTruth heapGuidedRunTruth)
      publicSoundness eqsat sound

theorem ay_pqhg_accepted_heap_property_intro
    (guardEvidence agreementEvidence maintenanceOnly : Prop) :
    guardEvidence ->
    agreementEvidence ->
    maintenanceOnly ->
    ay_pqhg_accepted_heap_property guardEvidence agreementEvidence
      maintenanceOnly :=
  fun guardH agreementH maintenanceH =>
    ay_pqhg_conj_intro guardEvidence
      (ay_pqhg_conj agreementEvidence maintenanceOnly) guardH
      (ay_pqhg_conj_intro agreementEvidence maintenanceOnly agreementH
        maintenanceH)

theorem ay_pqhg_accepted_guard
    (guardEvidence agreementEvidence maintenanceOnly : Prop) :
    ay_pqhg_accepted_heap_property guardEvidence agreementEvidence
      maintenanceOnly ->
    guardEvidence :=
  fun accepted =>
    ay_pqhg_conj_left guardEvidence
      (ay_pqhg_conj agreementEvidence maintenanceOnly) accepted

theorem ay_pqhg_accepted_agreement
    (guardEvidence agreementEvidence maintenanceOnly : Prop) :
    ay_pqhg_accepted_heap_property guardEvidence agreementEvidence
      maintenanceOnly ->
    agreementEvidence :=
  fun accepted =>
    ay_pqhg_conj_left agreementEvidence maintenanceOnly
      (ay_pqhg_conj_right guardEvidence
        (ay_pqhg_conj agreementEvidence maintenanceOnly) accepted)

theorem ay_pqhg_accepted_maintenance_only
    (guardEvidence agreementEvidence maintenanceOnly : Prop) :
    ay_pqhg_accepted_heap_property guardEvidence agreementEvidence
      maintenanceOnly ->
    maintenanceOnly :=
  fun accepted =>
    ay_pqhg_conj_right agreementEvidence maintenanceOnly
      (ay_pqhg_conj_right guardEvidence
        (ay_pqhg_conj agreementEvidence maintenanceOnly) accepted)

theorem ay_pqhg_heap_property_cannot_justify_publication
    (heapPropertyWitness fallbackOrRecompute : Prop) :
    heapPropertyWitness ->
    fallbackOrRecompute ->
    ay_pqhg_no_claim heapPropertyWitness fallbackOrRecompute :=
  fun _heap fallback =>
    ay_pqhg_conj_intro heapPropertyWitness fallbackOrRecompute _heap fallback

theorem ay_pqhg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_pqhg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_pqhg_conj_intro acceptedEvidence (ay_pqhg_conj outcome formulaTruth)
      acceptedH (ay_pqhg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_pqhg_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_pqhg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_pqhg_conj_left acceptedEvidence (ay_pqhg_conj outcome formulaTruth)
      report

theorem ay_pqhg_public_report_outcome
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_pqhg_public_report acceptedEvidence outcome formulaTruth ->
    outcome :=
  fun report =>
    ay_pqhg_conj_left outcome formulaTruth
      (ay_pqhg_conj_right acceptedEvidence
        (ay_pqhg_conj outcome formulaTruth) report)

theorem ay_pqhg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_pqhg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_pqhg_conj_right outcome formulaTruth
      (ay_pqhg_conj_right acceptedEvidence
        (ay_pqhg_conj outcome formulaTruth) report)

theorem ay_pqhg_preserves_formula_truth
    (originalFormulaTruth heapGuidedRunTruth : Prop) :
    ay_pqhg_equisat originalFormulaTruth heapGuidedRunTruth ->
    originalFormulaTruth ->
    heapGuidedRunTruth :=
  fun eqsat truth =>
    ay_pqhg_equisat_forward originalFormulaTruth heapGuidedRunTruth eqsat truth

theorem ay_pqhg_reflects_formula_truth
    (originalFormulaTruth heapGuidedRunTruth : Prop) :
    ay_pqhg_equisat originalFormulaTruth heapGuidedRunTruth ->
    heapGuidedRunTruth ->
    originalFormulaTruth :=
  fun eqsat truth =>
    ay_pqhg_equisat_backward originalFormulaTruth heapGuidedRunTruth eqsat truth

theorem ay_pqhg_accepted_preserves_public_soundness
    (guardEvidence agreementEvidence maintenanceOnly publicSoundness : Prop) :
    ay_pqhg_accepted_heap_property guardEvidence agreementEvidence
      maintenanceOnly ->
    (agreementEvidence -> publicSoundness) ->
    publicSoundness :=
  fun accepted project =>
    project
      (ay_pqhg_accepted_agreement guardEvidence agreementEvidence
        maintenanceOnly accepted)

theorem ay_pqhg_no_claim_intro (diagnostic fallbackOrRecompute : Prop) :
    diagnostic ->
    fallbackOrRecompute ->
    ay_pqhg_no_claim diagnostic fallbackOrRecompute :=
  ay_pqhg_conj_intro diagnostic fallbackOrRecompute

theorem ay_pqhg_no_claim_recompute
    (diagnostic fallbackOrRecompute : Prop) :
    ay_pqhg_no_claim diagnostic fallbackOrRecompute ->
    fallbackOrRecompute :=
  ay_pqhg_conj_right diagnostic fallbackOrRecompute

theorem ay_pqhg_heap_mismatch_no_claim
    (heapMismatch fallbackOrRecompute : Prop) :
    heapMismatch ->
    fallbackOrRecompute ->
    ay_pqhg_no_claim heapMismatch fallbackOrRecompute :=
  ay_pqhg_no_claim_intro heapMismatch fallbackOrRecompute

theorem ay_pqhg_update_mismatch_no_claim
    (updateMismatch fallbackOrRecompute : Prop) :
    updateMismatch ->
    fallbackOrRecompute ->
    ay_pqhg_no_claim updateMismatch fallbackOrRecompute :=
  ay_pqhg_no_claim_intro updateMismatch fallbackOrRecompute

theorem ay_pqhg_candidate_mismatch_no_claim
    (candidateMismatch fallbackOrRecompute : Prop) :
    candidateMismatch ->
    fallbackOrRecompute ->
    ay_pqhg_no_claim candidateMismatch fallbackOrRecompute :=
  ay_pqhg_no_claim_intro candidateMismatch fallbackOrRecompute

theorem ay_pqhg_replay_mismatch_no_claim
    (replayMismatch fallbackOrRecompute : Prop) :
    replayMismatch ->
    fallbackOrRecompute ->
    ay_pqhg_no_claim replayMismatch fallbackOrRecompute :=
  ay_pqhg_no_claim_intro replayMismatch fallbackOrRecompute

theorem ay_pqhg_build_mismatch_no_claim
    (buildMismatch fallbackOrRecompute : Prop) :
    buildMismatch ->
    fallbackOrRecompute ->
    ay_pqhg_no_claim buildMismatch fallbackOrRecompute :=
  ay_pqhg_no_claim_intro buildMismatch fallbackOrRecompute

theorem ay_pqhg_validator_mismatch_no_claim
    (validatorMismatch fallbackOrRecompute : Prop) :
    validatorMismatch ->
    fallbackOrRecompute ->
    ay_pqhg_no_claim validatorMismatch fallbackOrRecompute :=
  ay_pqhg_no_claim_intro validatorMismatch fallbackOrRecompute

theorem ay_pqhg_activity_mismatch_no_claim
    (activityMismatch fallbackOrRecompute : Prop) :
    activityMismatch ->
    fallbackOrRecompute ->
    ay_pqhg_no_claim activityMismatch fallbackOrRecompute :=
  ay_pqhg_no_claim_intro activityMismatch fallbackOrRecompute

theorem ay_pqhg_queue_mismatch_no_claim
    (queueMismatch fallbackOrRecompute : Prop) :
    queueMismatch ->
    fallbackOrRecompute ->
    ay_pqhg_no_claim queueMismatch fallbackOrRecompute :=
  ay_pqhg_no_claim_intro queueMismatch fallbackOrRecompute

theorem ay_pqhg_tiebreak_mismatch_no_claim
    (tiebreakMismatch fallbackOrRecompute : Prop) :
    tiebreakMismatch ->
    fallbackOrRecompute ->
    ay_pqhg_no_claim tiebreakMismatch fallbackOrRecompute :=
  ay_pqhg_no_claim_intro tiebreakMismatch fallbackOrRecompute

theorem ay_pqhg_audit_mismatch_no_claim
    (auditMismatch fallbackOrRecompute : Prop) :
    auditMismatch ->
    fallbackOrRecompute ->
    ay_pqhg_no_claim auditMismatch fallbackOrRecompute :=
  ay_pqhg_no_claim_intro auditMismatch fallbackOrRecompute

theorem ay_pqhg_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicSatOrUnsat : Prop) :
    ay_pqhg_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicSatOrUnsat -> fallbackPublic) ->
    publicSatOrUnsat ->
    fallbackPublic :=
  fun noClaim fallbackPublishes publication =>
    fallbackPublishes
      (ay_pqhg_no_claim_recompute failedGuard fallbackPublic noClaim)
      publication

theorem ay_pqhg_publication_requires_guard
    (guardEvidence agreementEvidence maintenanceOnly outcome formulaTruth :
      Prop) :
    ay_pqhg_public_report
      (ay_pqhg_accepted_heap_property guardEvidence agreementEvidence
        maintenanceOnly)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_pqhg_accepted_guard guardEvidence agreementEvidence maintenanceOnly
      (ay_pqhg_public_report_accepted
        (ay_pqhg_accepted_heap_property guardEvidence agreementEvidence
          maintenanceOnly)
        outcome formulaTruth report)

theorem ay_pqhg_publication_requires_validator
    (variableDomainDigest activityVectorDigest priorityQueueDigest
      heapPropertyWitness updateRebuildLedger candidateLegalityWitness
      tiebreakManifest propagationReplayEvidence fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript agreementEvidence
      maintenanceOnly outcome formulaTruth : Prop) :
    ay_pqhg_public_report
      (ay_pqhg_accepted_heap_property
        (ay_pqhg_guard variableDomainDigest activityVectorDigest
          priorityQueueDigest heapPropertyWitness updateRebuildLedger
          candidateLegalityWitness tiebreakManifest propagationReplayEvidence
          fallbackBaseline solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence maintenanceOnly)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_pqhg_guard_validator variableDomainDigest activityVectorDigest
      priorityQueueDigest heapPropertyWitness updateRebuildLedger
      candidateLegalityWitness tiebreakManifest propagationReplayEvidence
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      (ay_pqhg_publication_requires_guard
        (ay_pqhg_guard variableDomainDigest activityVectorDigest
          priorityQueueDigest heapPropertyWitness updateRebuildLedger
          candidateLegalityWitness tiebreakManifest propagationReplayEvidence
          fallbackBaseline solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence maintenanceOnly outcome formulaTruth report)

theorem ay_pqhg_publication_requires_audit
    (variableDomainDigest activityVectorDigest priorityQueueDigest
      heapPropertyWitness updateRebuildLedger candidateLegalityWitness
      tiebreakManifest propagationReplayEvidence fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript agreementEvidence
      maintenanceOnly outcome formulaTruth : Prop) :
    ay_pqhg_public_report
      (ay_pqhg_accepted_heap_property
        (ay_pqhg_guard variableDomainDigest activityVectorDigest
          priorityQueueDigest heapPropertyWitness updateRebuildLedger
          candidateLegalityWitness tiebreakManifest propagationReplayEvidence
          fallbackBaseline solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence maintenanceOnly)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_pqhg_guard_audit variableDomainDigest activityVectorDigest
      priorityQueueDigest heapPropertyWitness updateRebuildLedger
      candidateLegalityWitness tiebreakManifest propagationReplayEvidence
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      (ay_pqhg_publication_requires_guard
        (ay_pqhg_guard variableDomainDigest activityVectorDigest
          priorityQueueDigest heapPropertyWitness updateRebuildLedger
          candidateLegalityWitness tiebreakManifest propagationReplayEvidence
          fallbackBaseline solverBuildEvidence validatorGate auditTranscript)
        agreementEvidence maintenanceOnly outcome formulaTruth report)

theorem ay_pqhg_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_pqhg_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_pqhg_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_pqhg_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_pqhg_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_pqhg_public_report_intro acceptedEvidence unsatOutcome formulaTruth
