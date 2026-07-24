-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Failed-literal-probing preprocessing guard soundness.
-- The propositions stand for original/preprocessed formula digests, probe
-- ledgers, unit-propagation replay, conflict witnesses, implied-assignment
-- ledgers, checker replay, model/proof reconstruction, fallback/build/
-- validator gates, audit transcripts, diagnostics, and public SAT/UNSAT
-- reports.

def ay_flpg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_flpg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_flpg_Equisat (original : Prop) (preprocessed : Prop) :=
  ay_flpg_Conj (original -> preprocessed) (preprocessed -> original)

def ay_flpg_Sat (cnf : Prop) (model : Prop) :=
  ay_flpg_Conj cnf model

def ay_flpg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_flpg_OriginalFormulaDigest
    (originalDigest : Prop) (originalDigestAccepted : Prop)
    (originalManifest : Prop) :=
  ay_flpg_Conj originalManifest (originalDigest -> originalDigestAccepted)

def ay_flpg_PreprocessedFormulaDigest
    (preprocessedDigest : Prop) (preprocessedDigestAccepted : Prop)
    (preprocessedManifest : Prop) :=
  ay_flpg_Conj preprocessedManifest
    (preprocessedDigest -> preprocessedDigestAccepted)

def ay_flpg_ProbeLiteralLedger
    (probeLiteralLedger : Prop) (probeAccepted : Prop)
    (probeCoverage : Prop) :=
  ay_flpg_Conj probeCoverage (probeLiteralLedger -> probeAccepted)

def ay_flpg_UnitPropagationReplay
    (unitPropagationReplay : Prop) (unitReplayAccepted : Prop)
    (unitReplayCoverage : Prop) :=
  ay_flpg_Conj unitReplayCoverage
    (unitPropagationReplay -> unitReplayAccepted)

def ay_flpg_ConflictWitness
    (conflictWitness : Prop) (conflictAccepted : Prop)
    (conflictCoverage : Prop) :=
  ay_flpg_Conj conflictCoverage (conflictWitness -> conflictAccepted)

def ay_flpg_ImpliedAssignmentLedger
    (impliedAssignmentLedger : Prop) (impliedAccepted : Prop)
    (impliedCoverage : Prop) :=
  ay_flpg_Conj impliedCoverage (impliedAssignmentLedger -> impliedAccepted)

def ay_flpg_CheckerReplay
    (checkerReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_flpg_Conj checkerReplayCertificate checkerAccepted

def ay_flpg_ModelReconstructionWitness
    (preprocessedCnf : Prop) (originalCnf : Prop)
    (preprocessedModel : Prop) (originalModel : Prop) :=
  ay_flpg_Sat preprocessedCnf preprocessedModel ->
    ay_flpg_Sat originalCnf originalModel

def ay_flpg_UnsatProofReconstructionWitness
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_flpg_Replay preprocessedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_flpg_ReconstructionWitnesses
    (preprocessedCnf : Prop) (originalCnf : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_flpg_Conj
    (ay_flpg_ModelReconstructionWitness
      preprocessedCnf originalCnf preprocessedModel originalModel)
    (ay_flpg_UnsatProofReconstructionWitness
      originalCnf preprocessedCnf certificate conflict)

def ay_flpg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_flpg_Conj baselineSolver baselineAvailable

def ay_flpg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_flpg_Conj binaryFingerprint buildReproducible

def ay_flpg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_flpg_Conj validatorAccepted validatorVersion

def ay_flpg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_flpg_Conj auditAppended auditAppendOnly

def ay_flpg_AcceptedFailedLiteralProbeGuard
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (originalDigest : Prop) (originalDigestAccepted : Prop)
    (originalManifest : Prop)
    (preprocessedDigest : Prop) (preprocessedDigestAccepted : Prop)
    (preprocessedManifest : Prop)
    (probeLiteralLedger : Prop) (probeAccepted : Prop)
    (probeCoverage : Prop)
    (unitPropagationReplay : Prop) (unitReplayAccepted : Prop)
    (unitReplayCoverage : Prop)
    (conflictWitness : Prop) (conflictAccepted : Prop)
    (conflictCoverage : Prop)
    (impliedAssignmentLedger : Prop) (impliedAccepted : Prop)
    (impliedCoverage : Prop)
    (checkerReplayCertificate : Prop) (checkerAccepted : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_flpg_OriginalFormulaDigest
       originalDigest originalDigestAccepted originalManifest ->
     ay_flpg_PreprocessedFormulaDigest
       preprocessedDigest preprocessedDigestAccepted preprocessedManifest ->
     ay_flpg_ProbeLiteralLedger
       probeLiteralLedger probeAccepted probeCoverage ->
     ay_flpg_UnitPropagationReplay
       unitPropagationReplay unitReplayAccepted unitReplayCoverage ->
     ay_flpg_ConflictWitness
       conflictWitness conflictAccepted conflictCoverage ->
     ay_flpg_ImpliedAssignmentLedger
       impliedAssignmentLedger impliedAccepted impliedCoverage ->
     ay_flpg_CheckerReplay checkerReplayCertificate checkerAccepted ->
     ay_flpg_ReconstructionWitnesses
       preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict ->
     ay_flpg_Equisat originalCnf preprocessedCnf ->
     ay_flpg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_flpg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_flpg_ValidatorGate validatorAccepted validatorVersion ->
     ay_flpg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_flpg_FailedProbeGuardFailure
    (digestMismatch : Prop) (probeMismatch : Prop)
    (replayMismatch : Prop) (conflictMismatch : Prop)
    (reconstructionMismatch : Prop) (checkerMismatch : Prop)
    (baselineMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (digestMismatch -> result) ->
    (probeMismatch -> result) ->
    (replayMismatch -> result) ->
    (conflictMismatch -> result) ->
    (reconstructionMismatch -> result) ->
    (checkerMismatch -> result) ->
    (baselineMismatch -> result) ->
    (buildMismatch -> result) ->
    (validatorMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_flpg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_flpg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_flpg_Conj currentCnf recompute

def ay_flpg_DiagnosticFailedProbeGuard
    (currentCnf : Prop)
    (digestMismatch : Prop) (probeMismatch : Prop)
    (replayMismatch : Prop) (conflictMismatch : Prop)
    (reconstructionMismatch : Prop) (checkerMismatch : Prop)
    (baselineMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_flpg_Conj
    (ay_flpg_FailedProbeGuardFailure
      digestMismatch probeMismatch replayMismatch conflictMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch)
    (ay_flpg_Conj
      (ay_flpg_RecomputeObligation currentCnf recompute)
      (ay_flpg_NoSemanticClaim diagnostic))

def ay_flpg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_flpg_Conj exitCode claim

def ay_flpg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_flpg_Disj
    (ay_flpg_ExitCodeSound exitCode (ay_flpg_Sat originalCnf model))
    (ay_flpg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_flpg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_flpg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_flpg_conj_left
    (left : Prop) (right : Prop) :
    ay_flpg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_flpg_conj_right
    (left : Prop) (right : Prop) :
    ay_flpg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_flpg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_flpg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_flpg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_flpg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_flpg_equisat_forward
    (original : Prop) (preprocessed : Prop) :
    ay_flpg_Equisat original preprocessed -> original -> preprocessed := by
  intro eqsat
  exact ay_flpg_conj_left (original -> preprocessed) (preprocessed -> original) eqsat

theorem ay_flpg_equisat_backward
    (original : Prop) (preprocessed : Prop) :
    ay_flpg_Equisat original preprocessed -> preprocessed -> original := by
  intro eqsat
  exact ay_flpg_conj_right (original -> preprocessed) (preprocessed -> original) eqsat

theorem ay_flpg_original_formula_digest_applies
    (originalDigest : Prop) (originalDigestAccepted : Prop)
    (originalManifest : Prop) :
    ay_flpg_OriginalFormulaDigest
      originalDigest originalDigestAccepted originalManifest ->
    originalDigest -> originalDigestAccepted := by
  intro digest
  exact ay_flpg_conj_right
    originalManifest (originalDigest -> originalDigestAccepted) digest

theorem ay_flpg_preprocessed_formula_digest_applies
    (preprocessedDigest : Prop) (preprocessedDigestAccepted : Prop)
    (preprocessedManifest : Prop) :
    ay_flpg_PreprocessedFormulaDigest
      preprocessedDigest preprocessedDigestAccepted preprocessedManifest ->
    preprocessedDigest -> preprocessedDigestAccepted := by
  intro digest
  exact ay_flpg_conj_right
    preprocessedManifest
    (preprocessedDigest -> preprocessedDigestAccepted)
    digest

theorem ay_flpg_probe_literal_ledger_applies
    (probeLiteralLedger : Prop) (probeAccepted : Prop)
    (probeCoverage : Prop) :
    ay_flpg_ProbeLiteralLedger
      probeLiteralLedger probeAccepted probeCoverage ->
    probeLiteralLedger -> probeAccepted := by
  intro ledger
  exact ay_flpg_conj_right
    probeCoverage (probeLiteralLedger -> probeAccepted) ledger

theorem ay_flpg_unit_propagation_replay_applies
    (unitPropagationReplay : Prop) (unitReplayAccepted : Prop)
    (unitReplayCoverage : Prop) :
    ay_flpg_UnitPropagationReplay
      unitPropagationReplay unitReplayAccepted unitReplayCoverage ->
    unitPropagationReplay -> unitReplayAccepted := by
  intro replay
  exact ay_flpg_conj_right
    unitReplayCoverage (unitPropagationReplay -> unitReplayAccepted) replay

theorem ay_flpg_conflict_witness_applies
    (conflictWitness : Prop) (conflictAccepted : Prop)
    (conflictCoverage : Prop) :
    ay_flpg_ConflictWitness conflictWitness conflictAccepted conflictCoverage ->
    conflictWitness -> conflictAccepted := by
  intro witness
  exact ay_flpg_conj_right
    conflictCoverage (conflictWitness -> conflictAccepted) witness

theorem ay_flpg_implied_assignment_ledger_applies
    (impliedAssignmentLedger : Prop) (impliedAccepted : Prop)
    (impliedCoverage : Prop) :
    ay_flpg_ImpliedAssignmentLedger
      impliedAssignmentLedger impliedAccepted impliedCoverage ->
    impliedAssignmentLedger -> impliedAccepted := by
  intro ledger
  exact ay_flpg_conj_right
    impliedCoverage (impliedAssignmentLedger -> impliedAccepted) ledger

theorem ay_flpg_checker_replay_certificate
    (checkerReplayCertificate : Prop) (checkerAccepted : Prop) :
    ay_flpg_CheckerReplay checkerReplayCertificate checkerAccepted ->
    checkerReplayCertificate := by
  intro replay
  exact ay_flpg_conj_left checkerReplayCertificate checkerAccepted replay

theorem ay_flpg_model_reconstruction
    (preprocessedCnf : Prop) (originalCnf : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_flpg_ReconstructionWitnesses
      preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict ->
    ay_flpg_Sat preprocessedCnf preprocessedModel ->
    ay_flpg_Sat originalCnf originalModel := by
  intro witnesses
  exact ay_flpg_conj_left
    (ay_flpg_ModelReconstructionWitness
      preprocessedCnf originalCnf preprocessedModel originalModel)
    (ay_flpg_UnsatProofReconstructionWitness
      originalCnf preprocessedCnf certificate conflict)
    witnesses

theorem ay_flpg_unsat_proof_reconstruction
    (preprocessedCnf : Prop) (originalCnf : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_flpg_ReconstructionWitnesses
      preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict ->
    ay_flpg_Replay preprocessedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses
  exact ay_flpg_conj_right
    (ay_flpg_ModelReconstructionWitness
      preprocessedCnf originalCnf preprocessedModel originalModel)
    (ay_flpg_UnsatProofReconstructionWitness
      originalCnf preprocessedCnf certificate conflict)
    witnesses

theorem ay_flpg_accepted_equisat
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (originalDigest : Prop) (originalDigestAccepted : Prop)
    (originalManifest : Prop)
    (preprocessedDigest : Prop) (preprocessedDigestAccepted : Prop)
    (preprocessedManifest : Prop)
    (probeLiteralLedger : Prop) (probeAccepted : Prop)
    (probeCoverage : Prop)
    (unitPropagationReplay : Prop) (unitReplayAccepted : Prop)
    (unitReplayCoverage : Prop)
    (conflictWitness : Prop) (conflictAccepted : Prop)
    (conflictCoverage : Prop)
    (impliedAssignmentLedger : Prop) (impliedAccepted : Prop)
    (impliedCoverage : Prop)
    (checkerReplayCertificate : Prop) (checkerAccepted : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_flpg_AcceptedFailedLiteralProbeGuard
      originalCnf preprocessedCnf
      originalDigest originalDigestAccepted originalManifest
      preprocessedDigest preprocessedDigestAccepted preprocessedManifest
      probeLiteralLedger probeAccepted probeCoverage
      unitPropagationReplay unitReplayAccepted unitReplayCoverage
      conflictWitness conflictAccepted conflictCoverage
      impliedAssignmentLedger impliedAccepted impliedCoverage
      checkerReplayCertificate checkerAccepted
      preprocessedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_flpg_Equisat originalCnf preprocessedCnf := by
  intro accepted
  exact accepted (ay_flpg_Equisat originalCnf preprocessedCnf)
    (fun _origDigest _prepDigest _probe _unitReplay _conflictWitness
      _implied _checker _reconstruct eqsat _fallback _build _validator
      _audit => eqsat)

theorem ay_flpg_accepted_reconstruction
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (originalDigest : Prop) (originalDigestAccepted : Prop)
    (originalManifest : Prop)
    (preprocessedDigest : Prop) (preprocessedDigestAccepted : Prop)
    (preprocessedManifest : Prop)
    (probeLiteralLedger : Prop) (probeAccepted : Prop)
    (probeCoverage : Prop)
    (unitPropagationReplay : Prop) (unitReplayAccepted : Prop)
    (unitReplayCoverage : Prop)
    (conflictWitness : Prop) (conflictAccepted : Prop)
    (conflictCoverage : Prop)
    (impliedAssignmentLedger : Prop) (impliedAccepted : Prop)
    (impliedCoverage : Prop)
    (checkerReplayCertificate : Prop) (checkerAccepted : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_flpg_AcceptedFailedLiteralProbeGuard
      originalCnf preprocessedCnf
      originalDigest originalDigestAccepted originalManifest
      preprocessedDigest preprocessedDigestAccepted preprocessedManifest
      probeLiteralLedger probeAccepted probeCoverage
      unitPropagationReplay unitReplayAccepted unitReplayCoverage
      conflictWitness conflictAccepted conflictCoverage
      impliedAssignmentLedger impliedAccepted impliedCoverage
      checkerReplayCertificate checkerAccepted
      preprocessedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_flpg_ReconstructionWitnesses
      preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict := by
  intro accepted
  exact accepted
    (ay_flpg_ReconstructionWitnesses
      preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict)
    (fun _origDigest _prepDigest _probe _unitReplay _conflictWitness
      _implied _checker reconstruct _eqsat _fallback _build _validator
      _audit => reconstruct)

theorem ay_flpg_sat_pullback
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_flpg_ReconstructionWitnesses
      preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict ->
    ay_flpg_Sat preprocessedCnf preprocessedModel ->
    ay_flpg_Sat originalCnf originalModel := by
  intro witnesses satPreprocessed
  exact ay_flpg_model_reconstruction
    preprocessedCnf originalCnf preprocessedModel originalModel
    certificate conflict witnesses satPreprocessed

theorem ay_flpg_unsat_pushback
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_flpg_ReconstructionWitnesses
      preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict ->
    ay_flpg_Replay preprocessedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses replay
  exact ay_flpg_unsat_proof_reconstruction
    preprocessedCnf originalCnf preprocessedModel originalModel
    certificate conflict witnesses replay

theorem ay_flpg_public_sat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_flpg_ExitCodeSound exitCode (ay_flpg_Sat originalCnf originalModel) ->
    ay_flpg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro satSound
  exact ay_flpg_disj_left
    (ay_flpg_ExitCodeSound exitCode (ay_flpg_Sat originalCnf originalModel))
    (ay_flpg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    satSound

theorem ay_flpg_public_unsat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_flpg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_flpg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro unsatSound
  exact ay_flpg_disj_right
    (ay_flpg_ExitCodeSound exitCode (ay_flpg_Sat originalCnf originalModel))
    (ay_flpg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    unsatSound

theorem ay_flpg_failure_digest
    (digestMismatch probeMismatch replayMismatch conflictMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    digestMismatch ->
    ay_flpg_FailedProbeGuardFailure
      digestMismatch probeMismatch replayMismatch conflictMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result digest_case _probe_case _replay_case _conflict_case
    _reconstruction_case _checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact digest_case h

theorem ay_flpg_failure_probe
    (digestMismatch probeMismatch replayMismatch conflictMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    probeMismatch ->
    ay_flpg_FailedProbeGuardFailure
      digestMismatch probeMismatch replayMismatch conflictMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case probe_case _replay_case _conflict_case
    _reconstruction_case _checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact probe_case h

theorem ay_flpg_failure_replay
    (digestMismatch probeMismatch replayMismatch conflictMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    replayMismatch ->
    ay_flpg_FailedProbeGuardFailure
      digestMismatch probeMismatch replayMismatch conflictMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _probe_case replay_case _conflict_case
    _reconstruction_case _checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact replay_case h

theorem ay_flpg_failure_conflict
    (digestMismatch probeMismatch replayMismatch conflictMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    conflictMismatch ->
    ay_flpg_FailedProbeGuardFailure
      digestMismatch probeMismatch replayMismatch conflictMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _probe_case _replay_case conflict_case
    _reconstruction_case _checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact conflict_case h

theorem ay_flpg_failure_reconstruction
    (digestMismatch probeMismatch replayMismatch conflictMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    reconstructionMismatch ->
    ay_flpg_FailedProbeGuardFailure
      digestMismatch probeMismatch replayMismatch conflictMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _probe_case _replay_case _conflict_case
    reconstruction_case _checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case h

theorem ay_flpg_failure_checker
    (digestMismatch probeMismatch replayMismatch conflictMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    checkerMismatch ->
    ay_flpg_FailedProbeGuardFailure
      digestMismatch probeMismatch replayMismatch conflictMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _probe_case _replay_case _conflict_case
    _reconstruction_case checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact checker_case h

theorem ay_flpg_failure_baseline
    (digestMismatch probeMismatch replayMismatch conflictMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    baselineMismatch ->
    ay_flpg_FailedProbeGuardFailure
      digestMismatch probeMismatch replayMismatch conflictMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _probe_case _replay_case _conflict_case
    _reconstruction_case _checker_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case h

theorem ay_flpg_failure_build
    (digestMismatch probeMismatch replayMismatch conflictMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    buildMismatch ->
    ay_flpg_FailedProbeGuardFailure
      digestMismatch probeMismatch replayMismatch conflictMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _probe_case _replay_case _conflict_case
    _reconstruction_case _checker_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case h

theorem ay_flpg_failure_validator
    (digestMismatch probeMismatch replayMismatch conflictMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    validatorMismatch ->
    ay_flpg_FailedProbeGuardFailure
      digestMismatch probeMismatch replayMismatch conflictMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _probe_case _replay_case _conflict_case
    _reconstruction_case _checker_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case h

theorem ay_flpg_failure_audit
    (digestMismatch probeMismatch replayMismatch conflictMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    auditMismatch ->
    ay_flpg_FailedProbeGuardFailure
      digestMismatch probeMismatch replayMismatch conflictMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _probe_case _replay_case _conflict_case
    _reconstruction_case _checker_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case h

theorem ay_flpg_diagnostic_no_claim
    (currentCnf : Prop)
    (digestMismatch probeMismatch replayMismatch conflictMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_flpg_DiagnosticFailedProbeGuard
      currentCnf digestMismatch probeMismatch replayMismatch conflictMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_flpg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard
  exact ay_flpg_conj_right
    (ay_flpg_RecomputeObligation currentCnf recompute)
    (ay_flpg_NoSemanticClaim diagnostic)
    (ay_flpg_conj_right
      (ay_flpg_FailedProbeGuardFailure
        digestMismatch probeMismatch replayMismatch conflictMismatch
        reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
        validatorMismatch auditMismatch)
      (ay_flpg_Conj
        (ay_flpg_RecomputeObligation currentCnf recompute)
        (ay_flpg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_flpg_diagnostic_recompute
    (currentCnf : Prop)
    (digestMismatch probeMismatch replayMismatch conflictMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_flpg_DiagnosticFailedProbeGuard
      currentCnf digestMismatch probeMismatch replayMismatch conflictMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_flpg_RecomputeObligation currentCnf recompute := by
  intro diagnosticGuard
  exact ay_flpg_conj_left
    (ay_flpg_RecomputeObligation currentCnf recompute)
    (ay_flpg_NoSemanticClaim diagnostic)
    (ay_flpg_conj_right
      (ay_flpg_FailedProbeGuardFailure
        digestMismatch probeMismatch replayMismatch conflictMismatch
        reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
        validatorMismatch auditMismatch)
      (ay_flpg_Conj
        (ay_flpg_RecomputeObligation currentCnf recompute)
        (ay_flpg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_flpg_failed_guard_cannot_bless_public_result
    (currentCnf : Prop)
    (digestMismatch probeMismatch replayMismatch conflictMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_flpg_DiagnosticFailedProbeGuard
      currentCnf digestMismatch probeMismatch replayMismatch conflictMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_flpg_PublicResult originalCnf model certificate conflict exitCode ->
    ay_flpg_Conj
      (ay_flpg_NoSemanticClaim diagnostic)
      (ay_flpg_RecomputeObligation currentCnf recompute) := by
  intro diagnosticGuard _publicResult
  exact ay_flpg_conj_intro
    (ay_flpg_NoSemanticClaim diagnostic)
    (ay_flpg_RecomputeObligation currentCnf recompute)
    (ay_flpg_diagnostic_no_claim
      currentCnf digestMismatch probeMismatch replayMismatch conflictMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic diagnosticGuard)
    (ay_flpg_diagnostic_recompute
      currentCnf digestMismatch probeMismatch replayMismatch conflictMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic diagnosticGuard)

theorem ay_flpg_failed_guard_cannot_bless_public_sat
    (currentCnf : Prop)
    (digestMismatch probeMismatch replayMismatch conflictMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop) (exitCode : Prop) :
    ay_flpg_DiagnosticFailedProbeGuard
      currentCnf digestMismatch probeMismatch replayMismatch conflictMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_flpg_ExitCodeSound exitCode (ay_flpg_Sat originalCnf model) ->
    ay_flpg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _satClaim
  exact ay_flpg_diagnostic_no_claim
    currentCnf digestMismatch probeMismatch replayMismatch conflictMismatch
    reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
    validatorMismatch auditMismatch recompute diagnostic diagnosticGuard

theorem ay_flpg_failed_guard_cannot_bless_public_unsat
    (currentCnf : Prop)
    (digestMismatch probeMismatch replayMismatch conflictMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (certificate : Prop) (conflict : Prop)
    (exitCode : Prop) :
    ay_flpg_DiagnosticFailedProbeGuard
      currentCnf digestMismatch probeMismatch replayMismatch conflictMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_flpg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_flpg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _unsatClaim
  exact ay_flpg_diagnostic_no_claim
    currentCnf digestMismatch probeMismatch replayMismatch conflictMismatch
    reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
    validatorMismatch auditMismatch recompute diagnostic diagnosticGuard
