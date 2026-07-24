-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Seeded tie-break reproducibility guard for ay branching.
-- Seeded/randomized tie-breaks are heuristic reproducibility evidence only;
-- public SAT/UNSAT soundness must come from accepted checking evidence.

def ay_stg_conj (left : Prop) (right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_stg_equisat (before : Prop) (after : Prop) : Prop :=
  ay_stg_conj (before -> after) (after -> before)

def ay_stg_guard
    (benchmarkFingerprint : Prop)
    (seedManifest : Prop)
    (prngVersionDigest : Prop)
    (variableDomainDigest : Prop)
    (candidateSetDigest : Prop)
    (scoreVectorDigest : Prop)
    (tiebreakDecisionLedger : Prop)
    (decisionOrderReplayTranscript : Prop)
    (fallbackDeterministicBaseline : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (archiveManifest : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (benchmarkFingerprint ->
      seedManifest ->
      prngVersionDigest ->
      variableDomainDigest ->
      candidateSetDigest ->
      scoreVectorDigest ->
      tiebreakDecisionLedger ->
      decisionOrderReplayTranscript ->
      fallbackDeterministicBaseline ->
      solverBuildEvidence ->
      validatorGate ->
      archiveManifest ->
      auditTranscript ->
      result) ->
    result

def ay_stg_agreement
    (originalFormulaTruth seededRunTruth publicSoundness : Prop) : Prop :=
  ay_stg_conj
    (ay_stg_equisat originalFormulaTruth seededRunTruth)
    publicSoundness

def ay_stg_accepted_tiebreak
    (guardEvidence agreementEvidence reproducibilityOnly : Prop) : Prop :=
  ay_stg_conj guardEvidence
    (ay_stg_conj agreementEvidence reproducibilityOnly)

def ay_stg_public_report
    (acceptedEvidence outcome formulaTruth : Prop) : Prop :=
  ay_stg_conj acceptedEvidence
    (ay_stg_conj outcome formulaTruth)

def ay_stg_no_claim (diagnostic fallbackOrRecompute : Prop) : Prop :=
  ay_stg_conj diagnostic fallbackOrRecompute

theorem ay_stg_conj_intro (left right : Prop) :
    left -> right -> ay_stg_conj left right :=
  fun leftH rightH result build => build leftH rightH

theorem ay_stg_conj_left (left right : Prop) :
    ay_stg_conj left right -> left :=
  fun both => both left (fun leftH _rightH => leftH)

theorem ay_stg_conj_right (left right : Prop) :
    ay_stg_conj left right -> right :=
  fun both => both right (fun _leftH rightH => rightH)

theorem ay_stg_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_stg_equisat before after :=
  fun forward backward =>
    ay_stg_conj_intro (before -> after) (after -> before) forward backward

theorem ay_stg_equisat_forward (before after : Prop) :
    ay_stg_equisat before after -> before -> after :=
  fun eqsat => ay_stg_conj_left (before -> after) (after -> before) eqsat

theorem ay_stg_equisat_backward (before after : Prop) :
    ay_stg_equisat before after -> after -> before :=
  fun eqsat => ay_stg_conj_right (before -> after) (after -> before) eqsat

theorem ay_stg_guard_intro
    (benchmarkFingerprint seedManifest prngVersionDigest variableDomainDigest
      candidateSetDigest scoreVectorDigest tiebreakDecisionLedger
      decisionOrderReplayTranscript fallbackDeterministicBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript :
      Prop) :
    benchmarkFingerprint ->
    seedManifest ->
    prngVersionDigest ->
    variableDomainDigest ->
    candidateSetDigest ->
    scoreVectorDigest ->
    tiebreakDecisionLedger ->
    decisionOrderReplayTranscript ->
    fallbackDeterministicBaseline ->
    solverBuildEvidence ->
    validatorGate ->
    archiveManifest ->
    auditTranscript ->
    ay_stg_guard benchmarkFingerprint seedManifest prngVersionDigest
      variableDomainDigest candidateSetDigest scoreVectorDigest
      tiebreakDecisionLedger decisionOrderReplayTranscript
      fallbackDeterministicBaseline solverBuildEvidence validatorGate
      archiveManifest auditTranscript :=
  fun benchH seedH prngH domainH candidateH scoreH ledgerH replayH fallbackH
      buildH validatorH archiveH auditH result make =>
    make benchH seedH prngH domainH candidateH scoreH ledgerH replayH fallbackH
      buildH validatorH archiveH auditH

theorem ay_stg_guard_benchmark
    (benchmarkFingerprint seedManifest prngVersionDigest variableDomainDigest
      candidateSetDigest scoreVectorDigest tiebreakDecisionLedger
      decisionOrderReplayTranscript fallbackDeterministicBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript :
      Prop) :
    ay_stg_guard benchmarkFingerprint seedManifest prngVersionDigest
      variableDomainDigest candidateSetDigest scoreVectorDigest
      tiebreakDecisionLedger decisionOrderReplayTranscript
      fallbackDeterministicBaseline solverBuildEvidence validatorGate
      archiveManifest auditTranscript ->
    benchmarkFingerprint :=
  fun guard =>
    guard benchmarkFingerprint
      (fun benchH _seedH _prngH _domainH _candidateH _scoreH _ledgerH
          _replayH _fallbackH _buildH _validatorH _archiveH _auditH => benchH)

theorem ay_stg_guard_seed
    (benchmarkFingerprint seedManifest prngVersionDigest variableDomainDigest
      candidateSetDigest scoreVectorDigest tiebreakDecisionLedger
      decisionOrderReplayTranscript fallbackDeterministicBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript :
      Prop) :
    ay_stg_guard benchmarkFingerprint seedManifest prngVersionDigest
      variableDomainDigest candidateSetDigest scoreVectorDigest
      tiebreakDecisionLedger decisionOrderReplayTranscript
      fallbackDeterministicBaseline solverBuildEvidence validatorGate
      archiveManifest auditTranscript ->
    seedManifest :=
  fun guard =>
    guard seedManifest
      (fun _benchH seedH _prngH _domainH _candidateH _scoreH _ledgerH
          _replayH _fallbackH _buildH _validatorH _archiveH _auditH => seedH)

theorem ay_stg_guard_prng
    (benchmarkFingerprint seedManifest prngVersionDigest variableDomainDigest
      candidateSetDigest scoreVectorDigest tiebreakDecisionLedger
      decisionOrderReplayTranscript fallbackDeterministicBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript :
      Prop) :
    ay_stg_guard benchmarkFingerprint seedManifest prngVersionDigest
      variableDomainDigest candidateSetDigest scoreVectorDigest
      tiebreakDecisionLedger decisionOrderReplayTranscript
      fallbackDeterministicBaseline solverBuildEvidence validatorGate
      archiveManifest auditTranscript ->
    prngVersionDigest :=
  fun guard =>
    guard prngVersionDigest
      (fun _benchH _seedH prngH _domainH _candidateH _scoreH _ledgerH
          _replayH _fallbackH _buildH _validatorH _archiveH _auditH => prngH)

theorem ay_stg_guard_domain
    (benchmarkFingerprint seedManifest prngVersionDigest variableDomainDigest
      candidateSetDigest scoreVectorDigest tiebreakDecisionLedger
      decisionOrderReplayTranscript fallbackDeterministicBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript :
      Prop) :
    ay_stg_guard benchmarkFingerprint seedManifest prngVersionDigest
      variableDomainDigest candidateSetDigest scoreVectorDigest
      tiebreakDecisionLedger decisionOrderReplayTranscript
      fallbackDeterministicBaseline solverBuildEvidence validatorGate
      archiveManifest auditTranscript ->
    variableDomainDigest :=
  fun guard =>
    guard variableDomainDigest
      (fun _benchH _seedH _prngH domainH _candidateH _scoreH _ledgerH
          _replayH _fallbackH _buildH _validatorH _archiveH _auditH => domainH)

theorem ay_stg_guard_candidate
    (benchmarkFingerprint seedManifest prngVersionDigest variableDomainDigest
      candidateSetDigest scoreVectorDigest tiebreakDecisionLedger
      decisionOrderReplayTranscript fallbackDeterministicBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript :
      Prop) :
    ay_stg_guard benchmarkFingerprint seedManifest prngVersionDigest
      variableDomainDigest candidateSetDigest scoreVectorDigest
      tiebreakDecisionLedger decisionOrderReplayTranscript
      fallbackDeterministicBaseline solverBuildEvidence validatorGate
      archiveManifest auditTranscript ->
    candidateSetDigest :=
  fun guard =>
    guard candidateSetDigest
      (fun _benchH _seedH _prngH _domainH candidateH _scoreH _ledgerH
          _replayH _fallbackH _buildH _validatorH _archiveH _auditH =>
        candidateH)

theorem ay_stg_guard_score
    (benchmarkFingerprint seedManifest prngVersionDigest variableDomainDigest
      candidateSetDigest scoreVectorDigest tiebreakDecisionLedger
      decisionOrderReplayTranscript fallbackDeterministicBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript :
      Prop) :
    ay_stg_guard benchmarkFingerprint seedManifest prngVersionDigest
      variableDomainDigest candidateSetDigest scoreVectorDigest
      tiebreakDecisionLedger decisionOrderReplayTranscript
      fallbackDeterministicBaseline solverBuildEvidence validatorGate
      archiveManifest auditTranscript ->
    scoreVectorDigest :=
  fun guard =>
    guard scoreVectorDigest
      (fun _benchH _seedH _prngH _domainH _candidateH scoreH _ledgerH
          _replayH _fallbackH _buildH _validatorH _archiveH _auditH => scoreH)

theorem ay_stg_guard_ledger
    (benchmarkFingerprint seedManifest prngVersionDigest variableDomainDigest
      candidateSetDigest scoreVectorDigest tiebreakDecisionLedger
      decisionOrderReplayTranscript fallbackDeterministicBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript :
      Prop) :
    ay_stg_guard benchmarkFingerprint seedManifest prngVersionDigest
      variableDomainDigest candidateSetDigest scoreVectorDigest
      tiebreakDecisionLedger decisionOrderReplayTranscript
      fallbackDeterministicBaseline solverBuildEvidence validatorGate
      archiveManifest auditTranscript ->
    tiebreakDecisionLedger :=
  fun guard =>
    guard tiebreakDecisionLedger
      (fun _benchH _seedH _prngH _domainH _candidateH _scoreH ledgerH
          _replayH _fallbackH _buildH _validatorH _archiveH _auditH => ledgerH)

theorem ay_stg_guard_replay
    (benchmarkFingerprint seedManifest prngVersionDigest variableDomainDigest
      candidateSetDigest scoreVectorDigest tiebreakDecisionLedger
      decisionOrderReplayTranscript fallbackDeterministicBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript :
      Prop) :
    ay_stg_guard benchmarkFingerprint seedManifest prngVersionDigest
      variableDomainDigest candidateSetDigest scoreVectorDigest
      tiebreakDecisionLedger decisionOrderReplayTranscript
      fallbackDeterministicBaseline solverBuildEvidence validatorGate
      archiveManifest auditTranscript ->
    decisionOrderReplayTranscript :=
  fun guard =>
    guard decisionOrderReplayTranscript
      (fun _benchH _seedH _prngH _domainH _candidateH _scoreH _ledgerH
          replayH _fallbackH _buildH _validatorH _archiveH _auditH => replayH)

theorem ay_stg_guard_fallback
    (benchmarkFingerprint seedManifest prngVersionDigest variableDomainDigest
      candidateSetDigest scoreVectorDigest tiebreakDecisionLedger
      decisionOrderReplayTranscript fallbackDeterministicBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript :
      Prop) :
    ay_stg_guard benchmarkFingerprint seedManifest prngVersionDigest
      variableDomainDigest candidateSetDigest scoreVectorDigest
      tiebreakDecisionLedger decisionOrderReplayTranscript
      fallbackDeterministicBaseline solverBuildEvidence validatorGate
      archiveManifest auditTranscript ->
    fallbackDeterministicBaseline :=
  fun guard =>
    guard fallbackDeterministicBaseline
      (fun _benchH _seedH _prngH _domainH _candidateH _scoreH _ledgerH
          _replayH fallbackH _buildH _validatorH _archiveH _auditH => fallbackH)

theorem ay_stg_guard_build
    (benchmarkFingerprint seedManifest prngVersionDigest variableDomainDigest
      candidateSetDigest scoreVectorDigest tiebreakDecisionLedger
      decisionOrderReplayTranscript fallbackDeterministicBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript :
      Prop) :
    ay_stg_guard benchmarkFingerprint seedManifest prngVersionDigest
      variableDomainDigest candidateSetDigest scoreVectorDigest
      tiebreakDecisionLedger decisionOrderReplayTranscript
      fallbackDeterministicBaseline solverBuildEvidence validatorGate
      archiveManifest auditTranscript ->
    solverBuildEvidence :=
  fun guard =>
    guard solverBuildEvidence
      (fun _benchH _seedH _prngH _domainH _candidateH _scoreH _ledgerH
          _replayH _fallbackH buildH _validatorH _archiveH _auditH => buildH)

theorem ay_stg_guard_validator
    (benchmarkFingerprint seedManifest prngVersionDigest variableDomainDigest
      candidateSetDigest scoreVectorDigest tiebreakDecisionLedger
      decisionOrderReplayTranscript fallbackDeterministicBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript :
      Prop) :
    ay_stg_guard benchmarkFingerprint seedManifest prngVersionDigest
      variableDomainDigest candidateSetDigest scoreVectorDigest
      tiebreakDecisionLedger decisionOrderReplayTranscript
      fallbackDeterministicBaseline solverBuildEvidence validatorGate
      archiveManifest auditTranscript ->
    validatorGate :=
  fun guard =>
    guard validatorGate
      (fun _benchH _seedH _prngH _domainH _candidateH _scoreH _ledgerH
          _replayH _fallbackH _buildH validatorH _archiveH _auditH =>
        validatorH)

theorem ay_stg_guard_archive
    (benchmarkFingerprint seedManifest prngVersionDigest variableDomainDigest
      candidateSetDigest scoreVectorDigest tiebreakDecisionLedger
      decisionOrderReplayTranscript fallbackDeterministicBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript :
      Prop) :
    ay_stg_guard benchmarkFingerprint seedManifest prngVersionDigest
      variableDomainDigest candidateSetDigest scoreVectorDigest
      tiebreakDecisionLedger decisionOrderReplayTranscript
      fallbackDeterministicBaseline solverBuildEvidence validatorGate
      archiveManifest auditTranscript ->
    archiveManifest :=
  fun guard =>
    guard archiveManifest
      (fun _benchH _seedH _prngH _domainH _candidateH _scoreH _ledgerH
          _replayH _fallbackH _buildH _validatorH archiveH _auditH => archiveH)

theorem ay_stg_guard_audit
    (benchmarkFingerprint seedManifest prngVersionDigest variableDomainDigest
      candidateSetDigest scoreVectorDigest tiebreakDecisionLedger
      decisionOrderReplayTranscript fallbackDeterministicBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript :
      Prop) :
    ay_stg_guard benchmarkFingerprint seedManifest prngVersionDigest
      variableDomainDigest candidateSetDigest scoreVectorDigest
      tiebreakDecisionLedger decisionOrderReplayTranscript
      fallbackDeterministicBaseline solverBuildEvidence validatorGate
      archiveManifest auditTranscript ->
    auditTranscript :=
  fun guard =>
    guard auditTranscript
      (fun _benchH _seedH _prngH _domainH _candidateH _scoreH _ledgerH
          _replayH _fallbackH _buildH _validatorH _archiveH auditH => auditH)

theorem ay_stg_agreement_intro
    (originalFormulaTruth seededRunTruth publicSoundness : Prop) :
    ay_stg_equisat originalFormulaTruth seededRunTruth ->
    publicSoundness ->
    ay_stg_agreement originalFormulaTruth seededRunTruth publicSoundness :=
  fun eqsat sound =>
    ay_stg_conj_intro
      (ay_stg_equisat originalFormulaTruth seededRunTruth)
      publicSoundness eqsat sound

theorem ay_stg_accepted_tiebreak_intro
    (guardEvidence agreementEvidence reproducibilityOnly : Prop) :
    guardEvidence ->
    agreementEvidence ->
    reproducibilityOnly ->
    ay_stg_accepted_tiebreak guardEvidence agreementEvidence
      reproducibilityOnly :=
  fun guardH agreementH reproducibleH =>
    ay_stg_conj_intro guardEvidence
      (ay_stg_conj agreementEvidence reproducibilityOnly) guardH
      (ay_stg_conj_intro agreementEvidence reproducibilityOnly agreementH
        reproducibleH)

theorem ay_stg_accepted_guard
    (guardEvidence agreementEvidence reproducibilityOnly : Prop) :
    ay_stg_accepted_tiebreak guardEvidence agreementEvidence
      reproducibilityOnly ->
    guardEvidence :=
  fun accepted =>
    ay_stg_conj_left guardEvidence
      (ay_stg_conj agreementEvidence reproducibilityOnly) accepted

theorem ay_stg_accepted_agreement
    (guardEvidence agreementEvidence reproducibilityOnly : Prop) :
    ay_stg_accepted_tiebreak guardEvidence agreementEvidence
      reproducibilityOnly ->
    agreementEvidence :=
  fun accepted =>
    ay_stg_conj_left agreementEvidence reproducibilityOnly
      (ay_stg_conj_right guardEvidence
        (ay_stg_conj agreementEvidence reproducibilityOnly) accepted)

theorem ay_stg_accepted_reproducibility_only
    (guardEvidence agreementEvidence reproducibilityOnly : Prop) :
    ay_stg_accepted_tiebreak guardEvidence agreementEvidence
      reproducibilityOnly ->
    reproducibilityOnly :=
  fun accepted =>
    ay_stg_conj_right agreementEvidence reproducibilityOnly
      (ay_stg_conj_right guardEvidence
        (ay_stg_conj agreementEvidence reproducibilityOnly) accepted)

theorem ay_stg_seeded_path_cannot_justify_publication
    (seededEvidence fallbackOrRecompute : Prop) :
    seededEvidence ->
    fallbackOrRecompute ->
    ay_stg_no_claim seededEvidence fallbackOrRecompute :=
  ay_stg_conj_intro seededEvidence fallbackOrRecompute

theorem ay_stg_public_report_intro
    (acceptedEvidence outcome formulaTruth : Prop) :
    acceptedEvidence ->
    outcome ->
    formulaTruth ->
    ay_stg_public_report acceptedEvidence outcome formulaTruth :=
  fun acceptedH outcomeH truthH =>
    ay_stg_conj_intro acceptedEvidence (ay_stg_conj outcome formulaTruth)
      acceptedH (ay_stg_conj_intro outcome formulaTruth outcomeH truthH)

theorem ay_stg_public_report_accepted
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_stg_public_report acceptedEvidence outcome formulaTruth ->
    acceptedEvidence :=
  fun report =>
    ay_stg_conj_left acceptedEvidence (ay_stg_conj outcome formulaTruth)
      report

theorem ay_stg_public_report_outcome
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_stg_public_report acceptedEvidence outcome formulaTruth ->
    outcome :=
  fun report =>
    ay_stg_conj_left outcome formulaTruth
      (ay_stg_conj_right acceptedEvidence
        (ay_stg_conj outcome formulaTruth) report)

theorem ay_stg_public_report_truth
    (acceptedEvidence outcome formulaTruth : Prop) :
    ay_stg_public_report acceptedEvidence outcome formulaTruth ->
    formulaTruth :=
  fun report =>
    ay_stg_conj_right outcome formulaTruth
      (ay_stg_conj_right acceptedEvidence
        (ay_stg_conj outcome formulaTruth) report)

theorem ay_stg_preserves_formula_truth
    (originalFormulaTruth seededRunTruth : Prop) :
    ay_stg_equisat originalFormulaTruth seededRunTruth ->
    originalFormulaTruth ->
    seededRunTruth :=
  fun eqsat truth =>
    ay_stg_equisat_forward originalFormulaTruth seededRunTruth eqsat truth

theorem ay_stg_reflects_formula_truth
    (originalFormulaTruth seededRunTruth : Prop) :
    ay_stg_equisat originalFormulaTruth seededRunTruth ->
    seededRunTruth ->
    originalFormulaTruth :=
  fun eqsat truth =>
    ay_stg_equisat_backward originalFormulaTruth seededRunTruth eqsat truth

theorem ay_stg_accepted_preserves_public_soundness
    (guardEvidence agreementEvidence reproducibilityOnly publicSoundness : Prop) :
    ay_stg_accepted_tiebreak guardEvidence agreementEvidence
      reproducibilityOnly ->
    (agreementEvidence -> publicSoundness) ->
    publicSoundness :=
  fun accepted project =>
    project
      (ay_stg_accepted_agreement guardEvidence agreementEvidence
        reproducibilityOnly accepted)

theorem ay_stg_no_claim_intro (diagnostic fallbackOrRecompute : Prop) :
    diagnostic ->
    fallbackOrRecompute ->
    ay_stg_no_claim diagnostic fallbackOrRecompute :=
  ay_stg_conj_intro diagnostic fallbackOrRecompute

theorem ay_stg_no_claim_recompute
    (diagnostic fallbackOrRecompute : Prop) :
    ay_stg_no_claim diagnostic fallbackOrRecompute ->
    fallbackOrRecompute :=
  ay_stg_conj_right diagnostic fallbackOrRecompute

theorem ay_stg_seed_mismatch_no_claim
    (seedMismatch fallbackOrRecompute : Prop) :
    seedMismatch ->
    fallbackOrRecompute ->
    ay_stg_no_claim seedMismatch fallbackOrRecompute :=
  ay_stg_no_claim_intro seedMismatch fallbackOrRecompute

theorem ay_stg_prng_mismatch_no_claim
    (prngMismatch fallbackOrRecompute : Prop) :
    prngMismatch ->
    fallbackOrRecompute ->
    ay_stg_no_claim prngMismatch fallbackOrRecompute :=
  ay_stg_no_claim_intro prngMismatch fallbackOrRecompute

theorem ay_stg_domain_mismatch_no_claim
    (domainMismatch fallbackOrRecompute : Prop) :
    domainMismatch ->
    fallbackOrRecompute ->
    ay_stg_no_claim domainMismatch fallbackOrRecompute :=
  ay_stg_no_claim_intro domainMismatch fallbackOrRecompute

theorem ay_stg_candidate_mismatch_no_claim
    (candidateMismatch fallbackOrRecompute : Prop) :
    candidateMismatch ->
    fallbackOrRecompute ->
    ay_stg_no_claim candidateMismatch fallbackOrRecompute :=
  ay_stg_no_claim_intro candidateMismatch fallbackOrRecompute

theorem ay_stg_score_mismatch_no_claim
    (scoreMismatch fallbackOrRecompute : Prop) :
    scoreMismatch ->
    fallbackOrRecompute ->
    ay_stg_no_claim scoreMismatch fallbackOrRecompute :=
  ay_stg_no_claim_intro scoreMismatch fallbackOrRecompute

theorem ay_stg_ledger_mismatch_no_claim
    (ledgerMismatch fallbackOrRecompute : Prop) :
    ledgerMismatch ->
    fallbackOrRecompute ->
    ay_stg_no_claim ledgerMismatch fallbackOrRecompute :=
  ay_stg_no_claim_intro ledgerMismatch fallbackOrRecompute

theorem ay_stg_replay_mismatch_no_claim
    (replayMismatch fallbackOrRecompute : Prop) :
    replayMismatch ->
    fallbackOrRecompute ->
    ay_stg_no_claim replayMismatch fallbackOrRecompute :=
  ay_stg_no_claim_intro replayMismatch fallbackOrRecompute

theorem ay_stg_build_mismatch_no_claim
    (buildMismatch fallbackOrRecompute : Prop) :
    buildMismatch ->
    fallbackOrRecompute ->
    ay_stg_no_claim buildMismatch fallbackOrRecompute :=
  ay_stg_no_claim_intro buildMismatch fallbackOrRecompute

theorem ay_stg_validator_mismatch_no_claim
    (validatorMismatch fallbackOrRecompute : Prop) :
    validatorMismatch ->
    fallbackOrRecompute ->
    ay_stg_no_claim validatorMismatch fallbackOrRecompute :=
  ay_stg_no_claim_intro validatorMismatch fallbackOrRecompute

theorem ay_stg_archive_mismatch_no_claim
    (archiveMismatch fallbackOrRecompute : Prop) :
    archiveMismatch ->
    fallbackOrRecompute ->
    ay_stg_no_claim archiveMismatch fallbackOrRecompute :=
  ay_stg_no_claim_intro archiveMismatch fallbackOrRecompute

theorem ay_stg_audit_mismatch_no_claim
    (auditMismatch fallbackOrRecompute : Prop) :
    auditMismatch ->
    fallbackOrRecompute ->
    ay_stg_no_claim auditMismatch fallbackOrRecompute :=
  ay_stg_no_claim_intro auditMismatch fallbackOrRecompute

theorem ay_stg_failed_guard_cannot_bless_publication
    (failedGuard fallbackPublic publicSatOrUnsat : Prop) :
    ay_stg_no_claim failedGuard fallbackPublic ->
    (fallbackPublic -> publicSatOrUnsat -> fallbackPublic) ->
    publicSatOrUnsat ->
    fallbackPublic :=
  fun noClaim fallbackPublishes publication =>
    fallbackPublishes
      (ay_stg_no_claim_recompute failedGuard fallbackPublic noClaim)
      publication

theorem ay_stg_publication_requires_guard
    (guardEvidence agreementEvidence reproducibilityOnly outcome formulaTruth :
      Prop) :
    ay_stg_public_report
      (ay_stg_accepted_tiebreak guardEvidence agreementEvidence
        reproducibilityOnly)
      outcome formulaTruth ->
    guardEvidence :=
  fun report =>
    ay_stg_accepted_guard guardEvidence agreementEvidence reproducibilityOnly
      (ay_stg_public_report_accepted
        (ay_stg_accepted_tiebreak guardEvidence agreementEvidence
          reproducibilityOnly)
        outcome formulaTruth report)

theorem ay_stg_publication_requires_validator
    (benchmarkFingerprint seedManifest prngVersionDigest variableDomainDigest
      candidateSetDigest scoreVectorDigest tiebreakDecisionLedger
      decisionOrderReplayTranscript fallbackDeterministicBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript
      agreementEvidence reproducibilityOnly outcome formulaTruth : Prop) :
    ay_stg_public_report
      (ay_stg_accepted_tiebreak
        (ay_stg_guard benchmarkFingerprint seedManifest prngVersionDigest
          variableDomainDigest candidateSetDigest scoreVectorDigest
          tiebreakDecisionLedger decisionOrderReplayTranscript
          fallbackDeterministicBaseline solverBuildEvidence validatorGate
          archiveManifest auditTranscript)
        agreementEvidence reproducibilityOnly)
      outcome formulaTruth ->
    validatorGate :=
  fun report =>
    ay_stg_guard_validator benchmarkFingerprint seedManifest prngVersionDigest
      variableDomainDigest candidateSetDigest scoreVectorDigest
      tiebreakDecisionLedger decisionOrderReplayTranscript
      fallbackDeterministicBaseline solverBuildEvidence validatorGate
      archiveManifest auditTranscript
      (ay_stg_publication_requires_guard
        (ay_stg_guard benchmarkFingerprint seedManifest prngVersionDigest
          variableDomainDigest candidateSetDigest scoreVectorDigest
          tiebreakDecisionLedger decisionOrderReplayTranscript
          fallbackDeterministicBaseline solverBuildEvidence validatorGate
          archiveManifest auditTranscript)
        agreementEvidence reproducibilityOnly outcome formulaTruth report)

theorem ay_stg_publication_requires_archive
    (benchmarkFingerprint seedManifest prngVersionDigest variableDomainDigest
      candidateSetDigest scoreVectorDigest tiebreakDecisionLedger
      decisionOrderReplayTranscript fallbackDeterministicBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript
      agreementEvidence reproducibilityOnly outcome formulaTruth : Prop) :
    ay_stg_public_report
      (ay_stg_accepted_tiebreak
        (ay_stg_guard benchmarkFingerprint seedManifest prngVersionDigest
          variableDomainDigest candidateSetDigest scoreVectorDigest
          tiebreakDecisionLedger decisionOrderReplayTranscript
          fallbackDeterministicBaseline solverBuildEvidence validatorGate
          archiveManifest auditTranscript)
        agreementEvidence reproducibilityOnly)
      outcome formulaTruth ->
    archiveManifest :=
  fun report =>
    ay_stg_guard_archive benchmarkFingerprint seedManifest prngVersionDigest
      variableDomainDigest candidateSetDigest scoreVectorDigest
      tiebreakDecisionLedger decisionOrderReplayTranscript
      fallbackDeterministicBaseline solverBuildEvidence validatorGate
      archiveManifest auditTranscript
      (ay_stg_publication_requires_guard
        (ay_stg_guard benchmarkFingerprint seedManifest prngVersionDigest
          variableDomainDigest candidateSetDigest scoreVectorDigest
          tiebreakDecisionLedger decisionOrderReplayTranscript
          fallbackDeterministicBaseline solverBuildEvidence validatorGate
          archiveManifest auditTranscript)
        agreementEvidence reproducibilityOnly outcome formulaTruth report)

theorem ay_stg_publication_requires_audit
    (benchmarkFingerprint seedManifest prngVersionDigest variableDomainDigest
      candidateSetDigest scoreVectorDigest tiebreakDecisionLedger
      decisionOrderReplayTranscript fallbackDeterministicBaseline
      solverBuildEvidence validatorGate archiveManifest auditTranscript
      agreementEvidence reproducibilityOnly outcome formulaTruth : Prop) :
    ay_stg_public_report
      (ay_stg_accepted_tiebreak
        (ay_stg_guard benchmarkFingerprint seedManifest prngVersionDigest
          variableDomainDigest candidateSetDigest scoreVectorDigest
          tiebreakDecisionLedger decisionOrderReplayTranscript
          fallbackDeterministicBaseline solverBuildEvidence validatorGate
          archiveManifest auditTranscript)
        agreementEvidence reproducibilityOnly)
      outcome formulaTruth ->
    auditTranscript :=
  fun report =>
    ay_stg_guard_audit benchmarkFingerprint seedManifest prngVersionDigest
      variableDomainDigest candidateSetDigest scoreVectorDigest
      tiebreakDecisionLedger decisionOrderReplayTranscript
      fallbackDeterministicBaseline solverBuildEvidence validatorGate
      archiveManifest auditTranscript
      (ay_stg_publication_requires_guard
        (ay_stg_guard benchmarkFingerprint seedManifest prngVersionDigest
          variableDomainDigest candidateSetDigest scoreVectorDigest
          tiebreakDecisionLedger decisionOrderReplayTranscript
          fallbackDeterministicBaseline solverBuildEvidence validatorGate
          archiveManifest auditTranscript)
        agreementEvidence reproducibilityOnly outcome formulaTruth report)

theorem ay_stg_accepted_public_report_for_sat
    (acceptedEvidence satOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    satOutcome ->
    formulaTruth ->
    ay_stg_public_report acceptedEvidence satOutcome formulaTruth :=
  ay_stg_public_report_intro acceptedEvidence satOutcome formulaTruth

theorem ay_stg_accepted_public_report_for_unsat
    (acceptedEvidence unsatOutcome formulaTruth : Prop) :
    acceptedEvidence ->
    unsatOutcome ->
    formulaTruth ->
    ay_stg_public_report acceptedEvidence unsatOutcome formulaTruth :=
  ay_stg_public_report_intro acceptedEvidence unsatOutcome formulaTruth
