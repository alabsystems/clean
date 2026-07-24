-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Autarky-elimination preprocessing guard soundness.
-- The propositions stand for formula digests, autarky assignment ledgers,
-- touched-clause ledgers, untouched-clause preservation, deletion ledgers,
-- model/proof reconstruction, fallback/build/validator gates, audit
-- transcripts, diagnostics, and public SAT/UNSAT reports.

def ay_autg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_autg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_autg_Equisat (original : Prop) (reduced : Prop) :=
  ay_autg_Conj (original -> reduced) (reduced -> original)

def ay_autg_Sat (cnf : Prop) (model : Prop) :=
  ay_autg_Conj cnf model

def ay_autg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_autg_OriginalFormulaDigest
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop) :=
  ay_autg_Conj formulaManifest (formulaDigest -> formulaDigestAccepted)

def ay_autg_AutarkyAssignmentLedger
    (assignmentLedger : Prop) (assignmentAccepted : Prop)
    (assignmentCoverage : Prop) :=
  ay_autg_Conj assignmentCoverage (assignmentLedger -> assignmentAccepted)

def ay_autg_TouchedClauseLedger
    (touchedClauseLedger : Prop) (touchedAccepted : Prop)
    (touchedCoverage : Prop) :=
  ay_autg_Conj touchedCoverage (touchedClauseLedger -> touchedAccepted)

def ay_autg_UntouchedClausePreservationWitness
    (untouchedPreservationWitness : Prop) (untouchedAccepted : Prop)
    (untouchedCoverage : Prop) :=
  ay_autg_Conj untouchedCoverage
    (untouchedPreservationWitness -> untouchedAccepted)

def ay_autg_DeletionLedger
    (deletionLedger : Prop) (deletionAccepted : Prop)
    (deletionCoverage : Prop) :=
  ay_autg_Conj deletionCoverage (deletionLedger -> deletionAccepted)

def ay_autg_ModelReconstructionWitness
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :=
  ay_autg_Sat reducedCnf reducedModel ->
    ay_autg_Sat originalCnf originalModel

def ay_autg_UnsatProofReconstructionWitness
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_autg_Replay reducedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_autg_ReconstructionWitnesses
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_autg_Conj
    (ay_autg_ModelReconstructionWitness
      reducedCnf originalCnf reducedModel originalModel)
    (ay_autg_UnsatProofReconstructionWitness
      originalCnf reducedCnf certificate conflict)

def ay_autg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_autg_Conj baselineSolver baselineAvailable

def ay_autg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_autg_Conj binaryFingerprint buildReproducible

def ay_autg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_autg_Conj validatorAccepted validatorVersion

def ay_autg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_autg_Conj auditAppended auditAppendOnly

def ay_autg_AcceptedAutarkyEliminationGuard
    (originalCnf : Prop) (reducedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (assignmentLedger : Prop) (assignmentAccepted : Prop)
    (assignmentCoverage : Prop)
    (touchedClauseLedger : Prop) (touchedAccepted : Prop)
    (touchedCoverage : Prop)
    (untouchedPreservationWitness : Prop) (untouchedAccepted : Prop)
    (untouchedCoverage : Prop)
    (deletionLedger : Prop) (deletionAccepted : Prop)
    (deletionCoverage : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_autg_OriginalFormulaDigest
       formulaDigest formulaDigestAccepted formulaManifest ->
     ay_autg_AutarkyAssignmentLedger
       assignmentLedger assignmentAccepted assignmentCoverage ->
     ay_autg_TouchedClauseLedger
       touchedClauseLedger touchedAccepted touchedCoverage ->
     ay_autg_UntouchedClausePreservationWitness
       untouchedPreservationWitness untouchedAccepted untouchedCoverage ->
     ay_autg_DeletionLedger
       deletionLedger deletionAccepted deletionCoverage ->
     ay_autg_ReconstructionWitnesses
       reducedCnf originalCnf reducedModel originalModel certificate conflict ->
     ay_autg_Equisat originalCnf reducedCnf ->
     ay_autg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_autg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_autg_ValidatorGate validatorAccepted validatorVersion ->
     ay_autg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_autg_AutarkyGuardFailure
    (digestMismatch : Prop) (autarkyMismatch : Prop)
    (touchedMismatch : Prop) (untouchedMismatch : Prop)
    (deletionMismatch : Prop) (reconstructionMismatch : Prop)
    (baselineMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (digestMismatch -> result) ->
    (autarkyMismatch -> result) ->
    (touchedMismatch -> result) ->
    (untouchedMismatch -> result) ->
    (deletionMismatch -> result) ->
    (reconstructionMismatch -> result) ->
    (baselineMismatch -> result) ->
    (buildMismatch -> result) ->
    (validatorMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_autg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_autg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_autg_Conj currentCnf recompute

def ay_autg_DiagnosticAutarkyGuard
    (currentCnf : Prop)
    (digestMismatch : Prop) (autarkyMismatch : Prop)
    (touchedMismatch : Prop) (untouchedMismatch : Prop)
    (deletionMismatch : Prop) (reconstructionMismatch : Prop)
    (baselineMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_autg_Conj
    (ay_autg_AutarkyGuardFailure
      digestMismatch autarkyMismatch touchedMismatch untouchedMismatch
      deletionMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch)
    (ay_autg_Conj
      (ay_autg_RecomputeObligation currentCnf recompute)
      (ay_autg_NoSemanticClaim diagnostic))

def ay_autg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_autg_Conj exitCode claim

def ay_autg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_autg_Disj
    (ay_autg_ExitCodeSound exitCode (ay_autg_Sat originalCnf model))
    (ay_autg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_autg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_autg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_autg_conj_left
    (left : Prop) (right : Prop) :
    ay_autg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_autg_conj_right
    (left : Prop) (right : Prop) :
    ay_autg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_autg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_autg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_autg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_autg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_autg_equisat_forward
    (original : Prop) (reduced : Prop) :
    ay_autg_Equisat original reduced -> original -> reduced := by
  intro eqsat
  exact ay_autg_conj_left (original -> reduced) (reduced -> original) eqsat

theorem ay_autg_equisat_backward
    (original : Prop) (reduced : Prop) :
    ay_autg_Equisat original reduced -> reduced -> original := by
  intro eqsat
  exact ay_autg_conj_right (original -> reduced) (reduced -> original) eqsat

theorem ay_autg_original_formula_digest_applies
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop) :
    ay_autg_OriginalFormulaDigest
      formulaDigest formulaDigestAccepted formulaManifest ->
    formulaDigest -> formulaDigestAccepted := by
  intro digest
  exact ay_autg_conj_right
    formulaManifest (formulaDigest -> formulaDigestAccepted) digest

theorem ay_autg_autarky_assignment_ledger_applies
    (assignmentLedger : Prop) (assignmentAccepted : Prop)
    (assignmentCoverage : Prop) :
    ay_autg_AutarkyAssignmentLedger
      assignmentLedger assignmentAccepted assignmentCoverage ->
    assignmentLedger -> assignmentAccepted := by
  intro ledger
  exact ay_autg_conj_right
    assignmentCoverage (assignmentLedger -> assignmentAccepted) ledger

theorem ay_autg_touched_clause_ledger_applies
    (touchedClauseLedger : Prop) (touchedAccepted : Prop)
    (touchedCoverage : Prop) :
    ay_autg_TouchedClauseLedger
      touchedClauseLedger touchedAccepted touchedCoverage ->
    touchedClauseLedger -> touchedAccepted := by
  intro ledger
  exact ay_autg_conj_right
    touchedCoverage (touchedClauseLedger -> touchedAccepted) ledger

theorem ay_autg_untouched_clause_preservation_applies
    (untouchedPreservationWitness : Prop) (untouchedAccepted : Prop)
    (untouchedCoverage : Prop) :
    ay_autg_UntouchedClausePreservationWitness
      untouchedPreservationWitness untouchedAccepted untouchedCoverage ->
    untouchedPreservationWitness -> untouchedAccepted := by
  intro witness
  exact ay_autg_conj_right
    untouchedCoverage
    (untouchedPreservationWitness -> untouchedAccepted) witness

theorem ay_autg_deletion_ledger_applies
    (deletionLedger : Prop) (deletionAccepted : Prop)
    (deletionCoverage : Prop) :
    ay_autg_DeletionLedger deletionLedger deletionAccepted deletionCoverage ->
    deletionLedger -> deletionAccepted := by
  intro ledger
  exact ay_autg_conj_right
    deletionCoverage (deletionLedger -> deletionAccepted) ledger

theorem ay_autg_model_reconstruction
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_autg_ReconstructionWitnesses
      reducedCnf originalCnf reducedModel originalModel certificate conflict ->
    ay_autg_Sat reducedCnf reducedModel ->
    ay_autg_Sat originalCnf originalModel := by
  intro witnesses
  exact ay_autg_conj_left
    (ay_autg_ModelReconstructionWitness
      reducedCnf originalCnf reducedModel originalModel)
    (ay_autg_UnsatProofReconstructionWitness
      originalCnf reducedCnf certificate conflict)
    witnesses

theorem ay_autg_unsat_proof_reconstruction
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_autg_ReconstructionWitnesses
      reducedCnf originalCnf reducedModel originalModel certificate conflict ->
    ay_autg_Replay reducedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses
  exact ay_autg_conj_right
    (ay_autg_ModelReconstructionWitness
      reducedCnf originalCnf reducedModel originalModel)
    (ay_autg_UnsatProofReconstructionWitness
      originalCnf reducedCnf certificate conflict)
    witnesses

theorem ay_autg_accepted_equisat
    (originalCnf : Prop) (reducedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (assignmentLedger : Prop) (assignmentAccepted : Prop)
    (assignmentCoverage : Prop)
    (touchedClauseLedger : Prop) (touchedAccepted : Prop)
    (touchedCoverage : Prop)
    (untouchedPreservationWitness : Prop) (untouchedAccepted : Prop)
    (untouchedCoverage : Prop)
    (deletionLedger : Prop) (deletionAccepted : Prop)
    (deletionCoverage : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_autg_AcceptedAutarkyEliminationGuard
      originalCnf reducedCnf
      formulaDigest formulaDigestAccepted formulaManifest
      assignmentLedger assignmentAccepted assignmentCoverage
      touchedClauseLedger touchedAccepted touchedCoverage
      untouchedPreservationWitness untouchedAccepted untouchedCoverage
      deletionLedger deletionAccepted deletionCoverage
      reducedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_autg_Equisat originalCnf reducedCnf := by
  intro accepted
  exact accepted (ay_autg_Equisat originalCnf reducedCnf)
    (fun _digestOk _assignmentOk _touchedOk _untouchedOk _deletionOk
      _reconstruct eqsat _fallback _build _validator _audit => eqsat)

theorem ay_autg_accepted_reconstruction
    (originalCnf : Prop) (reducedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (assignmentLedger : Prop) (assignmentAccepted : Prop)
    (assignmentCoverage : Prop)
    (touchedClauseLedger : Prop) (touchedAccepted : Prop)
    (touchedCoverage : Prop)
    (untouchedPreservationWitness : Prop) (untouchedAccepted : Prop)
    (untouchedCoverage : Prop)
    (deletionLedger : Prop) (deletionAccepted : Prop)
    (deletionCoverage : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_autg_AcceptedAutarkyEliminationGuard
      originalCnf reducedCnf
      formulaDigest formulaDigestAccepted formulaManifest
      assignmentLedger assignmentAccepted assignmentCoverage
      touchedClauseLedger touchedAccepted touchedCoverage
      untouchedPreservationWitness untouchedAccepted untouchedCoverage
      deletionLedger deletionAccepted deletionCoverage
      reducedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_autg_ReconstructionWitnesses
      reducedCnf originalCnf reducedModel originalModel certificate conflict := by
  intro accepted
  exact accepted
    (ay_autg_ReconstructionWitnesses
      reducedCnf originalCnf reducedModel originalModel certificate conflict)
    (fun _digestOk _assignmentOk _touchedOk _untouchedOk _deletionOk
      reconstruct _eqsat _fallback _build _validator _audit => reconstruct)

theorem ay_autg_sat_pullback
    (originalCnf : Prop) (reducedCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_autg_ReconstructionWitnesses
      reducedCnf originalCnf reducedModel originalModel certificate conflict ->
    ay_autg_Sat reducedCnf reducedModel ->
    ay_autg_Sat originalCnf originalModel := by
  intro witnesses satReduced
  exact ay_autg_model_reconstruction
    reducedCnf originalCnf reducedModel originalModel
    certificate conflict witnesses satReduced

theorem ay_autg_unsat_pushback
    (originalCnf : Prop) (reducedCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_autg_ReconstructionWitnesses
      reducedCnf originalCnf reducedModel originalModel certificate conflict ->
    ay_autg_Replay reducedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses replay
  exact ay_autg_unsat_proof_reconstruction
    reducedCnf originalCnf reducedModel originalModel
    certificate conflict witnesses replay

theorem ay_autg_public_sat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_autg_ExitCodeSound exitCode (ay_autg_Sat originalCnf originalModel) ->
    ay_autg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro satSound
  exact ay_autg_disj_left
    (ay_autg_ExitCodeSound exitCode (ay_autg_Sat originalCnf originalModel))
    (ay_autg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    satSound

theorem ay_autg_public_unsat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_autg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_autg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro unsatSound
  exact ay_autg_disj_right
    (ay_autg_ExitCodeSound exitCode (ay_autg_Sat originalCnf originalModel))
    (ay_autg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    unsatSound

theorem ay_autg_failure_digest
    (digestMismatch autarkyMismatch touchedMismatch untouchedMismatch : Prop)
    (deletionMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    digestMismatch ->
    ay_autg_AutarkyGuardFailure
      digestMismatch autarkyMismatch touchedMismatch untouchedMismatch
      deletionMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result digest_case _autarky_case _touched_case _untouched_case
    _deletion_case _reconstruction_case _baseline_case _build_case
    _validator_case _audit_case
  exact digest_case h

theorem ay_autg_failure_autarky
    (digestMismatch autarkyMismatch touchedMismatch untouchedMismatch : Prop)
    (deletionMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    autarkyMismatch ->
    ay_autg_AutarkyGuardFailure
      digestMismatch autarkyMismatch touchedMismatch untouchedMismatch
      deletionMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case autarky_case _touched_case _untouched_case
    _deletion_case _reconstruction_case _baseline_case _build_case
    _validator_case _audit_case
  exact autarky_case h

theorem ay_autg_failure_touched
    (digestMismatch autarkyMismatch touchedMismatch untouchedMismatch : Prop)
    (deletionMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    touchedMismatch ->
    ay_autg_AutarkyGuardFailure
      digestMismatch autarkyMismatch touchedMismatch untouchedMismatch
      deletionMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _autarky_case touched_case _untouched_case
    _deletion_case _reconstruction_case _baseline_case _build_case
    _validator_case _audit_case
  exact touched_case h

theorem ay_autg_failure_untouched
    (digestMismatch autarkyMismatch touchedMismatch untouchedMismatch : Prop)
    (deletionMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    untouchedMismatch ->
    ay_autg_AutarkyGuardFailure
      digestMismatch autarkyMismatch touchedMismatch untouchedMismatch
      deletionMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _autarky_case _touched_case untouched_case
    _deletion_case _reconstruction_case _baseline_case _build_case
    _validator_case _audit_case
  exact untouched_case h

theorem ay_autg_failure_deletion
    (digestMismatch autarkyMismatch touchedMismatch untouchedMismatch : Prop)
    (deletionMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    deletionMismatch ->
    ay_autg_AutarkyGuardFailure
      digestMismatch autarkyMismatch touchedMismatch untouchedMismatch
      deletionMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _autarky_case _touched_case _untouched_case
    deletion_case _reconstruction_case _baseline_case _build_case
    _validator_case _audit_case
  exact deletion_case h

theorem ay_autg_failure_reconstruction
    (digestMismatch autarkyMismatch touchedMismatch untouchedMismatch : Prop)
    (deletionMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    reconstructionMismatch ->
    ay_autg_AutarkyGuardFailure
      digestMismatch autarkyMismatch touchedMismatch untouchedMismatch
      deletionMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _autarky_case _touched_case _untouched_case
    _deletion_case reconstruction_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case h

theorem ay_autg_failure_baseline
    (digestMismatch autarkyMismatch touchedMismatch untouchedMismatch : Prop)
    (deletionMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    baselineMismatch ->
    ay_autg_AutarkyGuardFailure
      digestMismatch autarkyMismatch touchedMismatch untouchedMismatch
      deletionMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _autarky_case _touched_case _untouched_case
    _deletion_case _reconstruction_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case h

theorem ay_autg_failure_build
    (digestMismatch autarkyMismatch touchedMismatch untouchedMismatch : Prop)
    (deletionMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    buildMismatch ->
    ay_autg_AutarkyGuardFailure
      digestMismatch autarkyMismatch touchedMismatch untouchedMismatch
      deletionMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _autarky_case _touched_case _untouched_case
    _deletion_case _reconstruction_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case h

theorem ay_autg_failure_validator
    (digestMismatch autarkyMismatch touchedMismatch untouchedMismatch : Prop)
    (deletionMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    validatorMismatch ->
    ay_autg_AutarkyGuardFailure
      digestMismatch autarkyMismatch touchedMismatch untouchedMismatch
      deletionMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _autarky_case _touched_case _untouched_case
    _deletion_case _reconstruction_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case h

theorem ay_autg_failure_audit
    (digestMismatch autarkyMismatch touchedMismatch untouchedMismatch : Prop)
    (deletionMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    auditMismatch ->
    ay_autg_AutarkyGuardFailure
      digestMismatch autarkyMismatch touchedMismatch untouchedMismatch
      deletionMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _autarky_case _touched_case _untouched_case
    _deletion_case _reconstruction_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case h

theorem ay_autg_diagnostic_no_claim
    (currentCnf : Prop)
    (digestMismatch autarkyMismatch touchedMismatch untouchedMismatch : Prop)
    (deletionMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_autg_DiagnosticAutarkyGuard
      currentCnf digestMismatch autarkyMismatch touchedMismatch untouchedMismatch
      deletionMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_autg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard
  exact ay_autg_conj_right
    (ay_autg_RecomputeObligation currentCnf recompute)
    (ay_autg_NoSemanticClaim diagnostic)
    (ay_autg_conj_right
      (ay_autg_AutarkyGuardFailure
        digestMismatch autarkyMismatch touchedMismatch untouchedMismatch
        deletionMismatch reconstructionMismatch baselineMismatch buildMismatch
        validatorMismatch auditMismatch)
      (ay_autg_Conj
        (ay_autg_RecomputeObligation currentCnf recompute)
        (ay_autg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_autg_diagnostic_recompute
    (currentCnf : Prop)
    (digestMismatch autarkyMismatch touchedMismatch untouchedMismatch : Prop)
    (deletionMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_autg_DiagnosticAutarkyGuard
      currentCnf digestMismatch autarkyMismatch touchedMismatch untouchedMismatch
      deletionMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_autg_RecomputeObligation currentCnf recompute := by
  intro diagnosticGuard
  exact ay_autg_conj_left
    (ay_autg_RecomputeObligation currentCnf recompute)
    (ay_autg_NoSemanticClaim diagnostic)
    (ay_autg_conj_right
      (ay_autg_AutarkyGuardFailure
        digestMismatch autarkyMismatch touchedMismatch untouchedMismatch
        deletionMismatch reconstructionMismatch baselineMismatch buildMismatch
        validatorMismatch auditMismatch)
      (ay_autg_Conj
        (ay_autg_RecomputeObligation currentCnf recompute)
        (ay_autg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_autg_failed_autarky_cannot_bless_public_result
    (currentCnf : Prop)
    (digestMismatch autarkyMismatch touchedMismatch untouchedMismatch : Prop)
    (deletionMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_autg_DiagnosticAutarkyGuard
      currentCnf digestMismatch autarkyMismatch touchedMismatch untouchedMismatch
      deletionMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_autg_PublicResult originalCnf model certificate conflict exitCode ->
    ay_autg_Conj
      (ay_autg_NoSemanticClaim diagnostic)
      (ay_autg_RecomputeObligation currentCnf recompute) := by
  intro diagnosticGuard _publicResult
  exact ay_autg_conj_intro
    (ay_autg_NoSemanticClaim diagnostic)
    (ay_autg_RecomputeObligation currentCnf recompute)
    (ay_autg_diagnostic_no_claim
      currentCnf digestMismatch autarkyMismatch touchedMismatch untouchedMismatch
      deletionMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic diagnosticGuard)
    (ay_autg_diagnostic_recompute
      currentCnf digestMismatch autarkyMismatch touchedMismatch untouchedMismatch
      deletionMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic diagnosticGuard)

theorem ay_autg_failed_autarky_cannot_bless_public_sat
    (currentCnf : Prop)
    (digestMismatch autarkyMismatch touchedMismatch untouchedMismatch : Prop)
    (deletionMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop) (exitCode : Prop) :
    ay_autg_DiagnosticAutarkyGuard
      currentCnf digestMismatch autarkyMismatch touchedMismatch untouchedMismatch
      deletionMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_autg_ExitCodeSound exitCode (ay_autg_Sat originalCnf model) ->
    ay_autg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _satClaim
  exact ay_autg_diagnostic_no_claim
    currentCnf digestMismatch autarkyMismatch touchedMismatch untouchedMismatch
    deletionMismatch reconstructionMismatch baselineMismatch buildMismatch
    validatorMismatch auditMismatch recompute diagnostic diagnosticGuard

theorem ay_autg_failed_autarky_cannot_bless_public_unsat
    (currentCnf : Prop)
    (digestMismatch autarkyMismatch touchedMismatch untouchedMismatch : Prop)
    (deletionMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (certificate : Prop) (conflict : Prop)
    (exitCode : Prop) :
    ay_autg_DiagnosticAutarkyGuard
      currentCnf digestMismatch autarkyMismatch touchedMismatch untouchedMismatch
      deletionMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_autg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_autg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _unsatClaim
  exact ay_autg_diagnostic_no_claim
    currentCnf digestMismatch autarkyMismatch touchedMismatch untouchedMismatch
    deletionMismatch reconstructionMismatch baselineMismatch buildMismatch
    validatorMismatch auditMismatch recompute diagnostic diagnosticGuard
