-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Clause-vivification replay guard soundness.
-- The propositions stand for formula digests, candidate-clause ledgers,
-- temporary-assumption trails, propagation-conflict replay, literal-removal
-- witnesses, model/proof reconstruction, fallback/build/validator gates, audit
-- transcripts, diagnostics, and public SAT/UNSAT reports.

def ay_cvrg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_cvrg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_cvrg_Equisat (original : Prop) (vivified : Prop) :=
  ay_cvrg_Conj (original -> vivified) (vivified -> original)

def ay_cvrg_Sat (cnf : Prop) (model : Prop) :=
  ay_cvrg_Conj cnf model

def ay_cvrg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_cvrg_OriginalFormulaDigest
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop) :=
  ay_cvrg_Conj formulaManifest (formulaDigest -> formulaDigestAccepted)

def ay_cvrg_CandidateClauseLedger
    (candidateLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop) :=
  ay_cvrg_Conj candidateCoverage (candidateLedger -> candidateAccepted)

def ay_cvrg_TemporaryAssumptionTrail
    (assumptionTrail : Prop) (trailAccepted : Prop)
    (trailDigest : Prop) :=
  ay_cvrg_Conj trailDigest (assumptionTrail -> trailAccepted)

def ay_cvrg_PropagationConflictReplay
    (propagationConflictReplay : Prop) (replayAccepted : Prop)
    (conflictCoverage : Prop) :=
  ay_cvrg_Conj conflictCoverage (propagationConflictReplay -> replayAccepted)

def ay_cvrg_LiteralRemovalWitness
    (literalRemovalWitness : Prop) (literalRemovalAccepted : Prop)
    (removedLiteralCoverage : Prop) :=
  ay_cvrg_Conj removedLiteralCoverage
    (literalRemovalWitness -> literalRemovalAccepted)

def ay_cvrg_ModelLiftWitness
    (vivifiedCnf : Prop) (originalCnf : Prop)
    (vivifiedModel : Prop) (originalModel : Prop) :=
  ay_cvrg_Sat vivifiedCnf vivifiedModel ->
    ay_cvrg_Sat originalCnf originalModel

def ay_cvrg_UnsatProofReplayWitness
    (originalCnf : Prop) (vivifiedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_cvrg_Replay vivifiedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_cvrg_ReconstructionWitnesses
    (vivifiedCnf : Prop) (originalCnf : Prop)
    (vivifiedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_cvrg_Conj
    (ay_cvrg_ModelLiftWitness
      vivifiedCnf originalCnf vivifiedModel originalModel)
    (ay_cvrg_UnsatProofReplayWitness
      originalCnf vivifiedCnf certificate conflict)

def ay_cvrg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_cvrg_Conj baselineSolver baselineAvailable

def ay_cvrg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_cvrg_Conj binaryFingerprint buildReproducible

def ay_cvrg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_cvrg_Conj validatorAccepted validatorVersion

def ay_cvrg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_cvrg_Conj auditAppended auditAppendOnly

def ay_cvrg_AcceptedClauseVivificationReplayGuard
    (originalCnf : Prop) (vivifiedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (candidateLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop)
    (assumptionTrail : Prop) (trailAccepted : Prop)
    (trailDigest : Prop)
    (propagationConflictReplay : Prop) (replayAccepted : Prop)
    (conflictCoverage : Prop)
    (literalRemovalWitness : Prop) (literalRemovalAccepted : Prop)
    (removedLiteralCoverage : Prop)
    (vivifiedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_cvrg_OriginalFormulaDigest
       formulaDigest formulaDigestAccepted formulaManifest ->
     ay_cvrg_CandidateClauseLedger
       candidateLedger candidateAccepted candidateCoverage ->
     ay_cvrg_TemporaryAssumptionTrail
       assumptionTrail trailAccepted trailDigest ->
     ay_cvrg_PropagationConflictReplay
       propagationConflictReplay replayAccepted conflictCoverage ->
     ay_cvrg_LiteralRemovalWitness
       literalRemovalWitness literalRemovalAccepted removedLiteralCoverage ->
     ay_cvrg_ReconstructionWitnesses
       vivifiedCnf originalCnf vivifiedModel originalModel certificate conflict ->
     ay_cvrg_Equisat originalCnf vivifiedCnf ->
     ay_cvrg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_cvrg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_cvrg_ValidatorGate validatorAccepted validatorVersion ->
     ay_cvrg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_cvrg_VivificationGuardFailure
    (digestMismatch : Prop) (candidateMismatch : Prop)
    (trailMismatch : Prop) (replayMismatch : Prop)
    (removalMismatch : Prop) (liftMismatch : Prop)
    (proofMismatch : Prop) (baselineMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (auditMismatch : Prop) :=
  forall result : Prop,
    (digestMismatch -> result) ->
    (candidateMismatch -> result) ->
    (trailMismatch -> result) ->
    (replayMismatch -> result) ->
    (removalMismatch -> result) ->
    (liftMismatch -> result) ->
    (proofMismatch -> result) ->
    (baselineMismatch -> result) ->
    (buildMismatch -> result) ->
    (validatorMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_cvrg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_cvrg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_cvrg_Conj currentCnf recompute

def ay_cvrg_DiagnosticVivificationGuard
    (currentCnf : Prop)
    (digestMismatch : Prop) (candidateMismatch : Prop)
    (trailMismatch : Prop) (replayMismatch : Prop)
    (removalMismatch : Prop) (liftMismatch : Prop)
    (proofMismatch : Prop) (baselineMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_cvrg_Conj
    (ay_cvrg_VivificationGuardFailure
      digestMismatch candidateMismatch trailMismatch replayMismatch
      removalMismatch liftMismatch proofMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch)
    (ay_cvrg_Conj
      (ay_cvrg_RecomputeObligation currentCnf recompute)
      (ay_cvrg_NoSemanticClaim diagnostic))

def ay_cvrg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_cvrg_Conj exitCode claim

def ay_cvrg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_cvrg_Disj
    (ay_cvrg_ExitCodeSound exitCode (ay_cvrg_Sat originalCnf model))
    (ay_cvrg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_cvrg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_cvrg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_cvrg_conj_left
    (left : Prop) (right : Prop) :
    ay_cvrg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_cvrg_conj_right
    (left : Prop) (right : Prop) :
    ay_cvrg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_cvrg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_cvrg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_cvrg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_cvrg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_cvrg_equisat_forward
    (original : Prop) (vivified : Prop) :
    ay_cvrg_Equisat original vivified -> original -> vivified := by
  intro eqsat
  exact ay_cvrg_conj_left (original -> vivified) (vivified -> original) eqsat

theorem ay_cvrg_equisat_backward
    (original : Prop) (vivified : Prop) :
    ay_cvrg_Equisat original vivified -> vivified -> original := by
  intro eqsat
  exact ay_cvrg_conj_right (original -> vivified) (vivified -> original) eqsat

theorem ay_cvrg_original_formula_digest_applies
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop) :
    ay_cvrg_OriginalFormulaDigest
      formulaDigest formulaDigestAccepted formulaManifest ->
    formulaDigest -> formulaDigestAccepted := by
  intro digest
  exact ay_cvrg_conj_right
    formulaManifest (formulaDigest -> formulaDigestAccepted) digest

theorem ay_cvrg_candidate_clause_ledger_applies
    (candidateLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop) :
    ay_cvrg_CandidateClauseLedger
      candidateLedger candidateAccepted candidateCoverage ->
    candidateLedger -> candidateAccepted := by
  intro ledger
  exact ay_cvrg_conj_right
    candidateCoverage (candidateLedger -> candidateAccepted) ledger

theorem ay_cvrg_temporary_assumption_trail_applies
    (assumptionTrail : Prop) (trailAccepted : Prop)
    (trailDigest : Prop) :
    ay_cvrg_TemporaryAssumptionTrail
      assumptionTrail trailAccepted trailDigest ->
    assumptionTrail -> trailAccepted := by
  intro trail
  exact ay_cvrg_conj_right
    trailDigest (assumptionTrail -> trailAccepted) trail

theorem ay_cvrg_propagation_conflict_replay_applies
    (propagationConflictReplay : Prop) (replayAccepted : Prop)
    (conflictCoverage : Prop) :
    ay_cvrg_PropagationConflictReplay
      propagationConflictReplay replayAccepted conflictCoverage ->
    propagationConflictReplay -> replayAccepted := by
  intro replay
  exact ay_cvrg_conj_right
    conflictCoverage (propagationConflictReplay -> replayAccepted) replay

theorem ay_cvrg_literal_removal_witness_applies
    (literalRemovalWitness : Prop) (literalRemovalAccepted : Prop)
    (removedLiteralCoverage : Prop) :
    ay_cvrg_LiteralRemovalWitness
      literalRemovalWitness literalRemovalAccepted removedLiteralCoverage ->
    literalRemovalWitness -> literalRemovalAccepted := by
  intro witness
  exact ay_cvrg_conj_right
    removedLiteralCoverage
    (literalRemovalWitness -> literalRemovalAccepted) witness

theorem ay_cvrg_model_lift
    (vivifiedCnf : Prop) (originalCnf : Prop)
    (vivifiedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_cvrg_ReconstructionWitnesses
      vivifiedCnf originalCnf vivifiedModel originalModel certificate conflict ->
    ay_cvrg_Sat vivifiedCnf vivifiedModel ->
    ay_cvrg_Sat originalCnf originalModel := by
  intro witnesses
  exact ay_cvrg_conj_left
    (ay_cvrg_ModelLiftWitness
      vivifiedCnf originalCnf vivifiedModel originalModel)
    (ay_cvrg_UnsatProofReplayWitness
      originalCnf vivifiedCnf certificate conflict)
    witnesses

theorem ay_cvrg_unsat_proof_replay
    (vivifiedCnf : Prop) (originalCnf : Prop)
    (vivifiedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_cvrg_ReconstructionWitnesses
      vivifiedCnf originalCnf vivifiedModel originalModel certificate conflict ->
    ay_cvrg_Replay vivifiedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses
  exact ay_cvrg_conj_right
    (ay_cvrg_ModelLiftWitness
      vivifiedCnf originalCnf vivifiedModel originalModel)
    (ay_cvrg_UnsatProofReplayWitness
      originalCnf vivifiedCnf certificate conflict)
    witnesses

theorem ay_cvrg_accepted_equisat
    (originalCnf : Prop) (vivifiedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (candidateLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop)
    (assumptionTrail : Prop) (trailAccepted : Prop)
    (trailDigest : Prop)
    (propagationConflictReplay : Prop) (replayAccepted : Prop)
    (conflictCoverage : Prop)
    (literalRemovalWitness : Prop) (literalRemovalAccepted : Prop)
    (removedLiteralCoverage : Prop)
    (vivifiedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_cvrg_AcceptedClauseVivificationReplayGuard
      originalCnf vivifiedCnf
      formulaDigest formulaDigestAccepted formulaManifest
      candidateLedger candidateAccepted candidateCoverage
      assumptionTrail trailAccepted trailDigest
      propagationConflictReplay replayAccepted conflictCoverage
      literalRemovalWitness literalRemovalAccepted removedLiteralCoverage
      vivifiedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_cvrg_Equisat originalCnf vivifiedCnf := by
  intro accepted
  exact accepted (ay_cvrg_Equisat originalCnf vivifiedCnf)
    (fun _digestOk _candidateOk _trailOk _replayOk _removalOk
      _reconstruct eqsat _fallback _build _validator _audit => eqsat)

theorem ay_cvrg_accepted_reconstruction
    (originalCnf : Prop) (vivifiedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (candidateLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop)
    (assumptionTrail : Prop) (trailAccepted : Prop)
    (trailDigest : Prop)
    (propagationConflictReplay : Prop) (replayAccepted : Prop)
    (conflictCoverage : Prop)
    (literalRemovalWitness : Prop) (literalRemovalAccepted : Prop)
    (removedLiteralCoverage : Prop)
    (vivifiedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_cvrg_AcceptedClauseVivificationReplayGuard
      originalCnf vivifiedCnf
      formulaDigest formulaDigestAccepted formulaManifest
      candidateLedger candidateAccepted candidateCoverage
      assumptionTrail trailAccepted trailDigest
      propagationConflictReplay replayAccepted conflictCoverage
      literalRemovalWitness literalRemovalAccepted removedLiteralCoverage
      vivifiedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_cvrg_ReconstructionWitnesses
      vivifiedCnf originalCnf vivifiedModel originalModel certificate conflict := by
  intro accepted
  exact accepted
    (ay_cvrg_ReconstructionWitnesses
      vivifiedCnf originalCnf vivifiedModel originalModel certificate conflict)
    (fun _digestOk _candidateOk _trailOk _replayOk _removalOk reconstruct
      _eqsat _fallback _build _validator _audit => reconstruct)

theorem ay_cvrg_sat_pullback
    (originalCnf : Prop) (vivifiedCnf : Prop)
    (vivifiedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_cvrg_ReconstructionWitnesses
      vivifiedCnf originalCnf vivifiedModel originalModel certificate conflict ->
    ay_cvrg_Sat vivifiedCnf vivifiedModel ->
    ay_cvrg_Sat originalCnf originalModel := by
  intro witnesses satVivified
  exact ay_cvrg_model_lift
    vivifiedCnf originalCnf vivifiedModel originalModel
    certificate conflict witnesses satVivified

theorem ay_cvrg_unsat_pushback
    (originalCnf : Prop) (vivifiedCnf : Prop)
    (vivifiedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_cvrg_ReconstructionWitnesses
      vivifiedCnf originalCnf vivifiedModel originalModel certificate conflict ->
    ay_cvrg_Replay vivifiedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses replay
  exact ay_cvrg_unsat_proof_replay
    vivifiedCnf originalCnf vivifiedModel originalModel
    certificate conflict witnesses replay

theorem ay_cvrg_public_sat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_cvrg_ExitCodeSound exitCode (ay_cvrg_Sat originalCnf originalModel) ->
    ay_cvrg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro satSound
  exact ay_cvrg_disj_left
    (ay_cvrg_ExitCodeSound exitCode (ay_cvrg_Sat originalCnf originalModel))
    (ay_cvrg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    satSound

theorem ay_cvrg_public_unsat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_cvrg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_cvrg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro unsatSound
  exact ay_cvrg_disj_right
    (ay_cvrg_ExitCodeSound exitCode (ay_cvrg_Sat originalCnf originalModel))
    (ay_cvrg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    unsatSound

theorem ay_cvrg_failure_digest
    (digestMismatch candidateMismatch trailMismatch replayMismatch : Prop)
    (removalMismatch liftMismatch proofMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    digestMismatch ->
    ay_cvrg_VivificationGuardFailure
      digestMismatch candidateMismatch trailMismatch replayMismatch
      removalMismatch liftMismatch proofMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result digest_case _candidate_case _trail_case _replay_case
    _removal_case _lift_case _proof_case _baseline_case
    _build_case _validator_case _audit_case
  exact digest_case h

theorem ay_cvrg_failure_candidate
    (digestMismatch candidateMismatch trailMismatch replayMismatch : Prop)
    (removalMismatch liftMismatch proofMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    candidateMismatch ->
    ay_cvrg_VivificationGuardFailure
      digestMismatch candidateMismatch trailMismatch replayMismatch
      removalMismatch liftMismatch proofMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result _digest_case candidate_case _trail_case _replay_case
    _removal_case _lift_case _proof_case _baseline_case
    _build_case _validator_case _audit_case
  exact candidate_case h

theorem ay_cvrg_failure_trail
    (digestMismatch candidateMismatch trailMismatch replayMismatch : Prop)
    (removalMismatch liftMismatch proofMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    trailMismatch ->
    ay_cvrg_VivificationGuardFailure
      digestMismatch candidateMismatch trailMismatch replayMismatch
      removalMismatch liftMismatch proofMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result _digest_case _candidate_case trail_case _replay_case
    _removal_case _lift_case _proof_case _baseline_case
    _build_case _validator_case _audit_case
  exact trail_case h

theorem ay_cvrg_failure_replay
    (digestMismatch candidateMismatch trailMismatch replayMismatch : Prop)
    (removalMismatch liftMismatch proofMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    replayMismatch ->
    ay_cvrg_VivificationGuardFailure
      digestMismatch candidateMismatch trailMismatch replayMismatch
      removalMismatch liftMismatch proofMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result _digest_case _candidate_case _trail_case replay_case
    _removal_case _lift_case _proof_case _baseline_case
    _build_case _validator_case _audit_case
  exact replay_case h

theorem ay_cvrg_failure_removal
    (digestMismatch candidateMismatch trailMismatch replayMismatch : Prop)
    (removalMismatch liftMismatch proofMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    removalMismatch ->
    ay_cvrg_VivificationGuardFailure
      digestMismatch candidateMismatch trailMismatch replayMismatch
      removalMismatch liftMismatch proofMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result _digest_case _candidate_case _trail_case _replay_case
    removal_case _lift_case _proof_case _baseline_case
    _build_case _validator_case _audit_case
  exact removal_case h

theorem ay_cvrg_failure_lift
    (digestMismatch candidateMismatch trailMismatch replayMismatch : Prop)
    (removalMismatch liftMismatch proofMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    liftMismatch ->
    ay_cvrg_VivificationGuardFailure
      digestMismatch candidateMismatch trailMismatch replayMismatch
      removalMismatch liftMismatch proofMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result _digest_case _candidate_case _trail_case _replay_case
    _removal_case lift_case _proof_case _baseline_case
    _build_case _validator_case _audit_case
  exact lift_case h

theorem ay_cvrg_failure_proof
    (digestMismatch candidateMismatch trailMismatch replayMismatch : Prop)
    (removalMismatch liftMismatch proofMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    proofMismatch ->
    ay_cvrg_VivificationGuardFailure
      digestMismatch candidateMismatch trailMismatch replayMismatch
      removalMismatch liftMismatch proofMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result _digest_case _candidate_case _trail_case _replay_case
    _removal_case _lift_case proof_case _baseline_case
    _build_case _validator_case _audit_case
  exact proof_case h

theorem ay_cvrg_failure_baseline
    (digestMismatch candidateMismatch trailMismatch replayMismatch : Prop)
    (removalMismatch liftMismatch proofMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    baselineMismatch ->
    ay_cvrg_VivificationGuardFailure
      digestMismatch candidateMismatch trailMismatch replayMismatch
      removalMismatch liftMismatch proofMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result _digest_case _candidate_case _trail_case _replay_case
    _removal_case _lift_case _proof_case baseline_case
    _build_case _validator_case _audit_case
  exact baseline_case h

theorem ay_cvrg_failure_build
    (digestMismatch candidateMismatch trailMismatch replayMismatch : Prop)
    (removalMismatch liftMismatch proofMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    buildMismatch ->
    ay_cvrg_VivificationGuardFailure
      digestMismatch candidateMismatch trailMismatch replayMismatch
      removalMismatch liftMismatch proofMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result _digest_case _candidate_case _trail_case _replay_case
    _removal_case _lift_case _proof_case _baseline_case
    build_case _validator_case _audit_case
  exact build_case h

theorem ay_cvrg_failure_validator
    (digestMismatch candidateMismatch trailMismatch replayMismatch : Prop)
    (removalMismatch liftMismatch proofMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    validatorMismatch ->
    ay_cvrg_VivificationGuardFailure
      digestMismatch candidateMismatch trailMismatch replayMismatch
      removalMismatch liftMismatch proofMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result _digest_case _candidate_case _trail_case _replay_case
    _removal_case _lift_case _proof_case _baseline_case
    _build_case validator_case _audit_case
  exact validator_case h

theorem ay_cvrg_failure_audit
    (digestMismatch candidateMismatch trailMismatch replayMismatch : Prop)
    (removalMismatch liftMismatch proofMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    auditMismatch ->
    ay_cvrg_VivificationGuardFailure
      digestMismatch candidateMismatch trailMismatch replayMismatch
      removalMismatch liftMismatch proofMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result _digest_case _candidate_case _trail_case _replay_case
    _removal_case _lift_case _proof_case _baseline_case
    _build_case _validator_case audit_case
  exact audit_case h

theorem ay_cvrg_diagnostic_no_claim
    (currentCnf : Prop)
    (digestMismatch candidateMismatch trailMismatch replayMismatch : Prop)
    (removalMismatch liftMismatch proofMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_cvrg_DiagnosticVivificationGuard
      currentCnf digestMismatch candidateMismatch trailMismatch replayMismatch
      removalMismatch liftMismatch proofMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch
      recompute diagnostic ->
    ay_cvrg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard
  exact ay_cvrg_conj_right
    (ay_cvrg_RecomputeObligation currentCnf recompute)
    (ay_cvrg_NoSemanticClaim diagnostic)
    (ay_cvrg_conj_right
      (ay_cvrg_VivificationGuardFailure
        digestMismatch candidateMismatch trailMismatch replayMismatch
        removalMismatch liftMismatch proofMismatch baselineMismatch
        buildMismatch validatorMismatch auditMismatch)
      (ay_cvrg_Conj
        (ay_cvrg_RecomputeObligation currentCnf recompute)
        (ay_cvrg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_cvrg_diagnostic_recompute
    (currentCnf : Prop)
    (digestMismatch candidateMismatch trailMismatch replayMismatch : Prop)
    (removalMismatch liftMismatch proofMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_cvrg_DiagnosticVivificationGuard
      currentCnf digestMismatch candidateMismatch trailMismatch replayMismatch
      removalMismatch liftMismatch proofMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch
      recompute diagnostic ->
    ay_cvrg_RecomputeObligation currentCnf recompute := by
  intro diagnosticGuard
  exact ay_cvrg_conj_left
    (ay_cvrg_RecomputeObligation currentCnf recompute)
    (ay_cvrg_NoSemanticClaim diagnostic)
    (ay_cvrg_conj_right
      (ay_cvrg_VivificationGuardFailure
        digestMismatch candidateMismatch trailMismatch replayMismatch
        removalMismatch liftMismatch proofMismatch baselineMismatch
        buildMismatch validatorMismatch auditMismatch)
      (ay_cvrg_Conj
        (ay_cvrg_RecomputeObligation currentCnf recompute)
        (ay_cvrg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_cvrg_failed_vivification_cannot_bless_public_result
    (currentCnf : Prop)
    (digestMismatch candidateMismatch trailMismatch replayMismatch : Prop)
    (removalMismatch liftMismatch proofMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_cvrg_DiagnosticVivificationGuard
      currentCnf digestMismatch candidateMismatch trailMismatch replayMismatch
      removalMismatch liftMismatch proofMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch
      recompute diagnostic ->
    ay_cvrg_PublicResult originalCnf model certificate conflict exitCode ->
    ay_cvrg_Conj
      (ay_cvrg_NoSemanticClaim diagnostic)
      (ay_cvrg_RecomputeObligation currentCnf recompute) := by
  intro diagnosticGuard _publicResult
  exact ay_cvrg_conj_intro
    (ay_cvrg_NoSemanticClaim diagnostic)
    (ay_cvrg_RecomputeObligation currentCnf recompute)
    (ay_cvrg_diagnostic_no_claim
      currentCnf digestMismatch candidateMismatch trailMismatch replayMismatch
      removalMismatch liftMismatch proofMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch
      recompute diagnostic diagnosticGuard)
    (ay_cvrg_diagnostic_recompute
      currentCnf digestMismatch candidateMismatch trailMismatch replayMismatch
      removalMismatch liftMismatch proofMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch
      recompute diagnostic diagnosticGuard)

theorem ay_cvrg_failed_vivification_cannot_bless_public_sat
    (currentCnf : Prop)
    (digestMismatch candidateMismatch trailMismatch replayMismatch : Prop)
    (removalMismatch liftMismatch proofMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop) (exitCode : Prop) :
    ay_cvrg_DiagnosticVivificationGuard
      currentCnf digestMismatch candidateMismatch trailMismatch replayMismatch
      removalMismatch liftMismatch proofMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch
      recompute diagnostic ->
    ay_cvrg_ExitCodeSound exitCode (ay_cvrg_Sat originalCnf model) ->
    ay_cvrg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _satClaim
  exact ay_cvrg_diagnostic_no_claim
    currentCnf digestMismatch candidateMismatch trailMismatch replayMismatch
    removalMismatch liftMismatch proofMismatch baselineMismatch
    buildMismatch validatorMismatch auditMismatch
    recompute diagnostic diagnosticGuard

theorem ay_cvrg_failed_vivification_cannot_bless_public_unsat
    (currentCnf : Prop)
    (digestMismatch candidateMismatch trailMismatch replayMismatch : Prop)
    (removalMismatch liftMismatch proofMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (certificate : Prop) (conflict : Prop)
    (exitCode : Prop) :
    ay_cvrg_DiagnosticVivificationGuard
      currentCnf digestMismatch candidateMismatch trailMismatch replayMismatch
      removalMismatch liftMismatch proofMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch
      recompute diagnostic ->
    ay_cvrg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_cvrg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _unsatClaim
  exact ay_cvrg_diagnostic_no_claim
    currentCnf digestMismatch candidateMismatch trailMismatch replayMismatch
    removalMismatch liftMismatch proofMismatch baselineMismatch
    buildMismatch validatorMismatch auditMismatch
    recompute diagnostic diagnosticGuard
