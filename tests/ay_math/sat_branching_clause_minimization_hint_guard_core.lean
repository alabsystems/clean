-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Clause-minimization hint guard for sequential-main SAT-COMP branching and
-- restart heuristics. Minimization hints are search-control only unless
-- replayed as proof evidence, and require digest, deletion, reason, activity,
-- tiebreak, replay, fallback, build, validator, and audit evidence.

def ay_cmig_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_cmig_equisat (before : Prop) (after : Prop) : Prop :=
  ay_cmig_conj (before -> after) (after -> before)

def ay_cmig_guard
    (learntClauseDigest : Prop)
    (minimizationDeletionLedger : Prop)
    (reasonChainWitness : Prop)
    (activityUpdateLedger : Prop)
    (deterministicTiebreakManifest : Prop)
    (propagationReplay : Prop)
    (fallbackBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (learntClauseDigest ->
      minimizationDeletionLedger ->
      reasonChainWitness ->
      activityUpdateLedger ->
      deterministicTiebreakManifest ->
      propagationReplay ->
      fallbackBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      auditTranscript ->
      result) ->
    result

def ay_cmig_agreement
    (digestMatch deletionMatch reasonMatch activityMatch tiebreakMatch
      replayMatch baselineMatch buildMatch validatorAccepts auditMatch :
      Prop) : Prop :=
  ay_cmig_guard digestMatch deletionMatch reasonMatch activityMatch
    tiebreakMatch replayMatch baselineMatch buildMatch validatorAccepts
    auditMatch

def ay_cmig_accepted_hint
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) : Prop :=
  ay_cmig_conj guardEvidence
    (ay_cmig_conj agreementEvidence
      (ay_cmig_conj deterministicBranchOrder searchControlHint))

def ay_cmig_proof_replayed_hint
    (acceptedHint proofReplayEvidence proofSoundness : Prop) : Prop :=
  ay_cmig_conj acceptedHint (ay_cmig_conj proofReplayEvidence proofSoundness)

def ay_cmig_public_report
    (acceptedEvidence outcome formulaTruth : Prop) : Prop :=
  ay_cmig_conj acceptedEvidence (ay_cmig_conj outcome formulaTruth)

def ay_cmig_no_claim (diagnostic fallbackPublic : Prop) : Prop :=
  ay_cmig_conj diagnostic fallbackPublic

theorem ay_cmig_conj_intro (left right : Prop) :
    left -> right -> ay_cmig_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_cmig_conj_left (left right : Prop) :
    ay_cmig_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_cmig_conj_right (left right : Prop) :
    ay_cmig_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_cmig_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_cmig_equisat before after :=
  fun forward backward =>
    ay_cmig_conj_intro (before -> after) (after -> before) forward backward

theorem ay_cmig_equisat_forward (before after : Prop) :
    ay_cmig_equisat before after -> before -> after :=
  fun eqsat =>
    ay_cmig_conj_left (before -> after) (after -> before) eqsat

theorem ay_cmig_equisat_backward (before after : Prop) :
    ay_cmig_equisat before after -> after -> before :=
  fun eqsat =>
    ay_cmig_conj_right (before -> after) (after -> before) eqsat

theorem ay_cmig_guard_intro
    (learntClauseDigest minimizationDeletionLedger reasonChainWitness
      activityUpdateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    learntClauseDigest ->
    minimizationDeletionLedger ->
    reasonChainWitness ->
    activityUpdateLedger ->
    deterministicTiebreakManifest ->
    propagationReplay ->
    fallbackBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    auditTranscript ->
    ay_cmig_guard learntClauseDigest minimizationDeletionLedger
      reasonChainWitness activityUpdateLedger deterministicTiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript :=
  fun digestH deletionH reasonH activityH tiebreakH replayH baselineH buildH
      validatorH auditH result make =>
    make digestH deletionH reasonH activityH tiebreakH replayH baselineH
      buildH validatorH auditH

theorem ay_cmig_guard_digest
    (learntClauseDigest minimizationDeletionLedger reasonChainWitness
      activityUpdateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_cmig_guard learntClauseDigest minimizationDeletionLedger
      reasonChainWitness activityUpdateLedger deterministicTiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    learntClauseDigest :=
  fun guard =>
    guard learntClauseDigest
      (fun digestH _deletionH _reasonH _activityH _tiebreakH _replayH
          _baselineH _buildH _validatorH _auditH => digestH)

theorem ay_cmig_guard_deletion
    (learntClauseDigest minimizationDeletionLedger reasonChainWitness
      activityUpdateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_cmig_guard learntClauseDigest minimizationDeletionLedger
      reasonChainWitness activityUpdateLedger deterministicTiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    minimizationDeletionLedger :=
  fun guard =>
    guard minimizationDeletionLedger
      (fun _digestH deletionH _reasonH _activityH _tiebreakH _replayH
          _baselineH _buildH _validatorH _auditH => deletionH)

theorem ay_cmig_guard_reason
    (learntClauseDigest minimizationDeletionLedger reasonChainWitness
      activityUpdateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_cmig_guard learntClauseDigest minimizationDeletionLedger
      reasonChainWitness activityUpdateLedger deterministicTiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    reasonChainWitness :=
  fun guard =>
    guard reasonChainWitness
      (fun _digestH _deletionH reasonH _activityH _tiebreakH _replayH
          _baselineH _buildH _validatorH _auditH => reasonH)

theorem ay_cmig_guard_activity
    (learntClauseDigest minimizationDeletionLedger reasonChainWitness
      activityUpdateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_cmig_guard learntClauseDigest minimizationDeletionLedger
      reasonChainWitness activityUpdateLedger deterministicTiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    activityUpdateLedger :=
  fun guard =>
    guard activityUpdateLedger
      (fun _digestH _deletionH _reasonH activityH _tiebreakH _replayH
          _baselineH _buildH _validatorH _auditH => activityH)

theorem ay_cmig_guard_tiebreak
    (learntClauseDigest minimizationDeletionLedger reasonChainWitness
      activityUpdateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_cmig_guard learntClauseDigest minimizationDeletionLedger
      reasonChainWitness activityUpdateLedger deterministicTiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    deterministicTiebreakManifest :=
  fun guard =>
    guard deterministicTiebreakManifest
      (fun _digestH _deletionH _reasonH _activityH tiebreakH _replayH
          _baselineH _buildH _validatorH _auditH => tiebreakH)

theorem ay_cmig_guard_replay
    (learntClauseDigest minimizationDeletionLedger reasonChainWitness
      activityUpdateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_cmig_guard learntClauseDigest minimizationDeletionLedger
      reasonChainWitness activityUpdateLedger deterministicTiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    propagationReplay :=
  fun guard =>
    guard propagationReplay
      (fun _digestH _deletionH _reasonH _activityH _tiebreakH replayH
          _baselineH _buildH _validatorH _auditH => replayH)

theorem ay_cmig_guard_baseline
    (learntClauseDigest minimizationDeletionLedger reasonChainWitness
      activityUpdateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_cmig_guard learntClauseDigest minimizationDeletionLedger
      reasonChainWitness activityUpdateLedger deterministicTiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    fallbackBaseline :=
  fun guard =>
    guard fallbackBaseline
      (fun _digestH _deletionH _reasonH _activityH _tiebreakH _replayH
          baselineH _buildH _validatorH _auditH => baselineH)

theorem ay_cmig_guard_build
    (learntClauseDigest minimizationDeletionLedger reasonChainWitness
      activityUpdateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_cmig_guard learntClauseDigest minimizationDeletionLedger
      reasonChainWitness activityUpdateLedger deterministicTiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _digestH _deletionH _reasonH _activityH _tiebreakH _replayH
          _baselineH buildH _validatorH _auditH => buildH)

theorem ay_cmig_guard_validator
    (learntClauseDigest minimizationDeletionLedger reasonChainWitness
      activityUpdateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_cmig_guard learntClauseDigest minimizationDeletionLedger
      reasonChainWitness activityUpdateLedger deterministicTiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _digestH _deletionH _reasonH _activityH _tiebreakH _replayH
          _baselineH _buildH validatorH _auditH => validatorH)

theorem ay_cmig_guard_audit
    (learntClauseDigest minimizationDeletionLedger reasonChainWitness
      activityUpdateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript :
      Prop) :
    ay_cmig_guard learntClauseDigest minimizationDeletionLedger
      reasonChainWitness activityUpdateLedger deterministicTiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _digestH _deletionH _reasonH _activityH _tiebreakH _replayH
          _baselineH _buildH _validatorH auditH => auditH)

theorem ay_cmig_agreement_intro
    (digestMatch deletionMatch reasonMatch activityMatch tiebreakMatch
      replayMatch baselineMatch buildMatch validatorAccepts auditMatch :
      Prop) :
    digestMatch ->
    deletionMatch ->
    reasonMatch ->
    activityMatch ->
    tiebreakMatch ->
    replayMatch ->
    baselineMatch ->
    buildMatch ->
    validatorAccepts ->
    auditMatch ->
    ay_cmig_agreement digestMatch deletionMatch reasonMatch activityMatch
      tiebreakMatch replayMatch baselineMatch buildMatch validatorAccepts
      auditMatch :=
  ay_cmig_guard_intro digestMatch deletionMatch reasonMatch activityMatch
    tiebreakMatch replayMatch baselineMatch buildMatch validatorAccepts
    auditMatch

theorem ay_cmig_accepted_hint_intro
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    guardEvidence ->
    agreementEvidence ->
    deterministicBranchOrder ->
    searchControlHint ->
    ay_cmig_accepted_hint guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint :=
  fun guardH agreementH orderH hintH =>
    ay_cmig_conj_intro guardEvidence
      (ay_cmig_conj agreementEvidence
        (ay_cmig_conj deterministicBranchOrder searchControlHint))
      guardH
      (ay_cmig_conj_intro agreementEvidence
        (ay_cmig_conj deterministicBranchOrder searchControlHint)
        agreementH
        (ay_cmig_conj_intro deterministicBranchOrder searchControlHint
          orderH hintH))

theorem ay_cmig_accepted_guard
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_cmig_accepted_hint guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint ->
    guardEvidence :=
  ay_cmig_conj_left guardEvidence
    (ay_cmig_conj agreementEvidence
      (ay_cmig_conj deterministicBranchOrder searchControlHint))

theorem ay_cmig_accepted_agreement
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_cmig_accepted_hint guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint ->
    agreementEvidence :=
  fun accepted =>
    ay_cmig_conj_left agreementEvidence
      (ay_cmig_conj deterministicBranchOrder searchControlHint)
      (ay_cmig_conj_right guardEvidence
        (ay_cmig_conj agreementEvidence
          (ay_cmig_conj deterministicBranchOrder searchControlHint))
        accepted)

theorem ay_cmig_accepted_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_cmig_accepted_hint guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint ->
    deterministicBranchOrder :=
  fun accepted =>
    ay_cmig_conj_left deterministicBranchOrder searchControlHint
      (ay_cmig_conj_right agreementEvidence
        (ay_cmig_conj deterministicBranchOrder searchControlHint)
        (ay_cmig_conj_right guardEvidence
          (ay_cmig_conj agreementEvidence
            (ay_cmig_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_cmig_accepted_search_control
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_cmig_accepted_hint guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint ->
    searchControlHint :=
  fun accepted =>
    ay_cmig_conj_right deterministicBranchOrder searchControlHint
      (ay_cmig_conj_right agreementEvidence
        (ay_cmig_conj deterministicBranchOrder searchControlHint)
        (ay_cmig_conj_right guardEvidence
          (ay_cmig_conj agreementEvidence
            (ay_cmig_conj deterministicBranchOrder searchControlHint))
          accepted))

theorem ay_cmig_proof_replayed_hint_intro
    (acceptedHint proofReplayEvidence proofSoundness : Prop) :
    acceptedHint ->
    proofReplayEvidence ->
    proofSoundness ->
    ay_cmig_proof_replayed_hint acceptedHint proofReplayEvidence
      proofSoundness :=
  fun acceptedH replayH soundH =>
    ay_cmig_conj_intro acceptedHint
      (ay_cmig_conj proofReplayEvidence proofSoundness)
      acceptedH
      (ay_cmig_conj_intro proofReplayEvidence proofSoundness replayH soundH)

theorem ay_cmig_proof_replayed_soundness
    (acceptedHint proofReplayEvidence proofSoundness : Prop) :
    ay_cmig_proof_replayed_hint acceptedHint proofReplayEvidence
      proofSoundness ->
    proofSoundness :=
  fun replayed =>
    ay_cmig_conj_right proofReplayEvidence proofSoundness
      (ay_cmig_conj_right acceptedHint
        (ay_cmig_conj proofReplayEvidence proofSoundness) replayed)

theorem ay_cmig_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_cmig_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_cmig_conj_intro acceptedEvidence (ay_cmig_conj outcome formulaTruth)
      acceptedH (ay_cmig_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_cmig_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_cmig_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  ay_cmig_conj_left acceptedEvidence (ay_cmig_conj outcome formulaTruth)

theorem ay_cmig_public_report_outcome
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_cmig_public_report acceptedEvidence outcome formulaTruth ->
    outcome :=
  fun report =>
    ay_cmig_conj_left outcome formulaTruth
      (ay_cmig_conj_right acceptedEvidence
        (ay_cmig_conj outcome formulaTruth) report)

theorem ay_cmig_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_cmig_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_cmig_conj_right outcome formulaTruth
      (ay_cmig_conj_right acceptedEvidence
        (ay_cmig_conj outcome formulaTruth) report)

theorem ay_cmig_no_claim_intro (diagnostic fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    ay_cmig_no_claim diagnostic fallbackPublic :=
  ay_cmig_conj_intro diagnostic fallbackPublic

theorem ay_cmig_no_claim_diagnostic (diagnostic fallbackPublic : Prop) :
    ay_cmig_no_claim diagnostic fallbackPublic -> diagnostic :=
  ay_cmig_conj_left diagnostic fallbackPublic

theorem ay_cmig_no_claim_preserves_fallback
    (diagnostic fallbackPublic : Prop) :
    ay_cmig_no_claim diagnostic fallbackPublic -> fallbackPublic :=
  ay_cmig_conj_right diagnostic fallbackPublic

theorem ay_cmig_hint_preserves_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_cmig_equisat beforeFormula afterFormula ->
    beforeFormula ->
    afterFormula :=
  ay_cmig_equisat_forward beforeFormula afterFormula

theorem ay_cmig_hint_reflects_formula_truth
    (beforeFormula afterFormula : Prop) :
    ay_cmig_equisat beforeFormula afterFormula ->
    afterFormula ->
    beforeFormula :=
  ay_cmig_equisat_backward beforeFormula afterFormula

theorem ay_cmig_accepted_preserves_public_soundness
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_cmig_public_report acceptedEvidence outcome formulaTruth ->
    ay_cmig_conj outcome formulaTruth :=
  fun report =>
    ay_cmig_conj_right acceptedEvidence (ay_cmig_conj outcome formulaTruth)
      report

theorem ay_cmig_accepted_guides_search_order
    (guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint : Prop) :
    ay_cmig_accepted_hint guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint ->
    ay_cmig_conj deterministicBranchOrder searchControlHint :=
  fun accepted =>
    ay_cmig_conj_right agreementEvidence
      (ay_cmig_conj deterministicBranchOrder searchControlHint)
      (ay_cmig_conj_right guardEvidence
        (ay_cmig_conj agreementEvidence
          (ay_cmig_conj deterministicBranchOrder searchControlHint))
        accepted)

theorem ay_cmig_digest_mismatch_no_claim
    (digestMismatch fallbackPublic : Prop) :
    digestMismatch ->
    fallbackPublic ->
    ay_cmig_no_claim digestMismatch fallbackPublic :=
  ay_cmig_no_claim_intro digestMismatch fallbackPublic

theorem ay_cmig_deletion_mismatch_no_claim
    (deletionMismatch fallbackPublic : Prop) :
    deletionMismatch ->
    fallbackPublic ->
    ay_cmig_no_claim deletionMismatch fallbackPublic :=
  ay_cmig_no_claim_intro deletionMismatch fallbackPublic

theorem ay_cmig_reason_mismatch_no_claim
    (reasonMismatch fallbackPublic : Prop) :
    reasonMismatch ->
    fallbackPublic ->
    ay_cmig_no_claim reasonMismatch fallbackPublic :=
  ay_cmig_no_claim_intro reasonMismatch fallbackPublic

theorem ay_cmig_activity_mismatch_no_claim
    (activityMismatch fallbackPublic : Prop) :
    activityMismatch ->
    fallbackPublic ->
    ay_cmig_no_claim activityMismatch fallbackPublic :=
  ay_cmig_no_claim_intro activityMismatch fallbackPublic

theorem ay_cmig_tiebreak_mismatch_no_claim
    (tiebreakMismatch fallbackPublic : Prop) :
    tiebreakMismatch ->
    fallbackPublic ->
    ay_cmig_no_claim tiebreakMismatch fallbackPublic :=
  ay_cmig_no_claim_intro tiebreakMismatch fallbackPublic

theorem ay_cmig_replay_mismatch_no_claim
    (replayMismatch fallbackPublic : Prop) :
    replayMismatch ->
    fallbackPublic ->
    ay_cmig_no_claim replayMismatch fallbackPublic :=
  ay_cmig_no_claim_intro replayMismatch fallbackPublic

theorem ay_cmig_baseline_mismatch_no_claim
    (baselineMismatch fallbackPublic : Prop) :
    baselineMismatch ->
    fallbackPublic ->
    ay_cmig_no_claim baselineMismatch fallbackPublic :=
  ay_cmig_no_claim_intro baselineMismatch fallbackPublic

theorem ay_cmig_build_mismatch_no_claim
    (buildMismatch fallbackPublic : Prop) :
    buildMismatch ->
    fallbackPublic ->
    ay_cmig_no_claim buildMismatch fallbackPublic :=
  ay_cmig_no_claim_intro buildMismatch fallbackPublic

theorem ay_cmig_validator_rejection_no_claim
    (validatorRejects fallbackPublic : Prop) :
    validatorRejects ->
    fallbackPublic ->
    ay_cmig_no_claim validatorRejects fallbackPublic :=
  ay_cmig_no_claim_intro validatorRejects fallbackPublic

theorem ay_cmig_audit_mismatch_no_claim
    (auditMismatch fallbackPublic : Prop) :
    auditMismatch ->
    fallbackPublic ->
    ay_cmig_no_claim auditMismatch fallbackPublic :=
  ay_cmig_no_claim_intro auditMismatch fallbackPublic

theorem ay_cmig_recompute_preserves_public_soundness
    (diagnostic fallbackPublic : Prop) :
    ay_cmig_no_claim diagnostic fallbackPublic ->
    fallbackPublic :=
  ay_cmig_no_claim_preserves_fallback diagnostic fallbackPublic

theorem ay_cmig_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicationBlessed : Prop) :
    ay_cmig_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicationBlessed) ->
    publicationBlessed :=
  fun noClaim fallbackPublishes =>
    fallbackPublishes
      (ay_cmig_no_claim_preserves_fallback failedGuard fallbackPublic noClaim)

theorem ay_cmig_publication_requires_accepted_guard
    (guardEvidence agreementEvidence deterministicBranchOrder searchControlHint
      outcome formulaTruth : Prop) :
    ay_cmig_public_report
      (ay_cmig_accepted_hint guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_cmig_accepted_guard guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint
      (ay_cmig_public_report_accepted
        (ay_cmig_accepted_hint guardEvidence agreementEvidence
          deterministicBranchOrder searchControlHint)
        outcome formulaTruth report)

theorem ay_cmig_publication_requires_validator
    (learntClauseDigest minimizationDeletionLedger reasonChainWitness
      activityUpdateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      agreementEvidence deterministicBranchOrder searchControlHint outcome
      formulaTruth : Prop) :
    ay_cmig_public_report
      (ay_cmig_accepted_hint
        (ay_cmig_guard learntClauseDigest minimizationDeletionLedger
          reasonChainWitness activityUpdateLedger deterministicTiebreakManifest
          propagationReplay fallbackBaseline solverBuildEvidence validatorGate
          auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_cmig_guard_validator learntClauseDigest minimizationDeletionLedger
      reasonChainWitness activityUpdateLedger deterministicTiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript
      (ay_cmig_publication_requires_accepted_guard
        (ay_cmig_guard learntClauseDigest minimizationDeletionLedger
          reasonChainWitness activityUpdateLedger deterministicTiebreakManifest
          propagationReplay fallbackBaseline solverBuildEvidence validatorGate
          auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint outcome
        formulaTruth report)

theorem ay_cmig_publication_requires_audit
    (learntClauseDigest minimizationDeletionLedger reasonChainWitness
      activityUpdateLedger deterministicTiebreakManifest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      agreementEvidence deterministicBranchOrder searchControlHint outcome
      formulaTruth : Prop) :
    ay_cmig_public_report
      (ay_cmig_accepted_hint
        (ay_cmig_guard learntClauseDigest minimizationDeletionLedger
          reasonChainWitness activityUpdateLedger deterministicTiebreakManifest
          propagationReplay fallbackBaseline solverBuildEvidence validatorGate
          auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_cmig_guard_audit learntClauseDigest minimizationDeletionLedger
      reasonChainWitness activityUpdateLedger deterministicTiebreakManifest
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript
      (ay_cmig_publication_requires_accepted_guard
        (ay_cmig_guard learntClauseDigest minimizationDeletionLedger
          reasonChainWitness activityUpdateLedger deterministicTiebreakManifest
          propagationReplay fallbackBaseline solverBuildEvidence validatorGate
          auditTranscript)
        agreementEvidence deterministicBranchOrder searchControlHint outcome
        formulaTruth report)

theorem ay_cmig_minimization_hint_is_search_control_only
    (beforeFormula afterFormula guardEvidence agreementEvidence
      deterministicBranchOrder searchControlHint : Prop) :
    ay_cmig_equisat beforeFormula afterFormula ->
    ay_cmig_accepted_hint guardEvidence agreementEvidence deterministicBranchOrder
      searchControlHint ->
    ay_cmig_conj (beforeFormula -> afterFormula)
      (ay_cmig_conj deterministicBranchOrder searchControlHint) :=
  fun eqsat accepted =>
    ay_cmig_conj_intro (beforeFormula -> afterFormula)
      (ay_cmig_conj deterministicBranchOrder searchControlHint)
      (ay_cmig_equisat_forward beforeFormula afterFormula eqsat)
      (ay_cmig_accepted_guides_search_order guardEvidence agreementEvidence
        deterministicBranchOrder searchControlHint accepted)

theorem ay_cmig_hint_becomes_proof_only_after_replay
    (acceptedHint proofReplayEvidence proofSoundness : Prop) :
    ay_cmig_proof_replayed_hint acceptedHint proofReplayEvidence
      proofSoundness ->
    ay_cmig_conj proofReplayEvidence proofSoundness :=
  fun replayed =>
    ay_cmig_conj_right acceptedHint
      (ay_cmig_conj proofReplayEvidence proofSoundness) replayed

theorem ay_cmig_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_cmig_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_cmig_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_cmig_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_cmig_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_cmig_public_report_intro acceptedEvidence unsatOutcome formulaTruth
