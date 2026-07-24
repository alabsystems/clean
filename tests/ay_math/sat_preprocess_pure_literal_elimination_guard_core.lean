-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Pure-literal-elimination preprocessing guard soundness.
-- The propositions stand for original formula fingerprints, literal occurrence
-- digests, pure-literal ledgers, assigned-literal witnesses, simplified
-- formula digests, deleted-clause ledgers, model extension, UNSAT/equisat
-- replay evidence, build/validator gates, fallback no-claim paths, audit
-- transcripts, and public SAT/UNSAT reports.

def ay_pleg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pleg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pleg_Equisat (original : Prop) (simplified : Prop) :=
  ay_pleg_Conj (original -> simplified) (simplified -> original)

def ay_pleg_Sat (cnf : Prop) (model : Prop) :=
  ay_pleg_Conj cnf model

def ay_pleg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pleg_OriginalFormulaFingerprint
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop) :=
  ay_pleg_Conj fingerprintManifest (fingerprint -> fingerprintAccepted)

def ay_pleg_LiteralOccurrenceDigest
    (occurrenceDigest : Prop) (occurrenceDigestAccepted : Prop)
    (occurrenceDigestManifest : Prop) :=
  ay_pleg_Conj occurrenceDigestManifest
    (occurrenceDigest -> occurrenceDigestAccepted)

def ay_pleg_PureLiteralLedger
    (pureLiteralLedger : Prop) (pureLiteralAccepted : Prop)
    (pureLiteralCoverage : Prop) :=
  ay_pleg_Conj pureLiteralCoverage
    (pureLiteralLedger -> pureLiteralAccepted)

def ay_pleg_AssignedLiteralWitness
    (assignedLiteralWitness : Prop) (assignmentAccepted : Prop)
    (assignmentCoverage : Prop) :=
  ay_pleg_Conj assignmentCoverage
    (assignedLiteralWitness -> assignmentAccepted)

def ay_pleg_SimplifiedFormulaDigest
    (simplifiedFormulaDigest : Prop) (simplifiedDigestAccepted : Prop)
    (simplifiedDigestManifest : Prop) :=
  ay_pleg_Conj simplifiedDigestManifest
    (simplifiedFormulaDigest -> simplifiedDigestAccepted)

def ay_pleg_DeletedClauseLedger
    (deletedClauseLedger : Prop) (deletionAccepted : Prop)
    (deletionCoverage : Prop) :=
  ay_pleg_Conj deletionCoverage (deletedClauseLedger -> deletionAccepted)

def ay_pleg_ValidatorGate
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop) :=
  ay_pleg_Conj checkerAccepted
    (ay_pleg_Conj validatorAccepted validatorVersion)

def ay_pleg_ModelExtensionWitness
    (simplifiedCnf : Prop) (originalCnf : Prop)
    (simplifiedModel : Prop) (originalModel : Prop) :=
  ay_pleg_Sat simplifiedCnf simplifiedModel ->
    ay_pleg_Sat originalCnf originalModel

def ay_pleg_UnsatEquisatReplayWitness
    (originalCnf : Prop) (simplifiedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pleg_Replay simplifiedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pleg_ReconstructionEvidence
    (simplifiedCnf : Prop) (originalCnf : Prop)
    (simplifiedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pleg_Conj
    (ay_pleg_ModelExtensionWitness
      simplifiedCnf originalCnf simplifiedModel originalModel)
    (ay_pleg_UnsatEquisatReplayWitness
      originalCnf simplifiedCnf certificate conflict)

def ay_pleg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_pleg_Conj binaryFingerprint buildReproducible

def ay_pleg_FallbackNoClaimPath
    (baselineAvailable : Prop) (noClaimPath : Prop) :=
  ay_pleg_Conj baselineAvailable noClaimPath

def ay_pleg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_pleg_Conj auditAppended auditAppendOnly

def ay_pleg_AcceptedPureLiteralEliminationGuard
    (originalCnf : Prop) (simplifiedCnf : Prop)
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop)
    (occurrenceDigest : Prop) (occurrenceDigestAccepted : Prop)
    (occurrenceDigestManifest : Prop)
    (pureLiteralLedger : Prop) (pureLiteralAccepted : Prop)
    (pureLiteralCoverage : Prop)
    (assignedLiteralWitness : Prop) (assignmentAccepted : Prop)
    (assignmentCoverage : Prop)
    (simplifiedFormulaDigest : Prop) (simplifiedDigestAccepted : Prop)
    (simplifiedDigestManifest : Prop)
    (deletedClauseLedger : Prop) (deletionAccepted : Prop)
    (deletionCoverage : Prop)
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop)
    (simplifiedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (baselineAvailable : Prop) (noClaimPath : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_pleg_OriginalFormulaFingerprint
       fingerprint fingerprintAccepted fingerprintManifest ->
     ay_pleg_LiteralOccurrenceDigest
       occurrenceDigest occurrenceDigestAccepted occurrenceDigestManifest ->
     ay_pleg_PureLiteralLedger
       pureLiteralLedger pureLiteralAccepted pureLiteralCoverage ->
     ay_pleg_AssignedLiteralWitness
       assignedLiteralWitness assignmentAccepted assignmentCoverage ->
     ay_pleg_SimplifiedFormulaDigest
       simplifiedFormulaDigest simplifiedDigestAccepted simplifiedDigestManifest ->
     ay_pleg_DeletedClauseLedger
       deletedClauseLedger deletionAccepted deletionCoverage ->
     ay_pleg_ReconstructionEvidence
       simplifiedCnf originalCnf simplifiedModel originalModel certificate conflict ->
     ay_pleg_Equisat originalCnf simplifiedCnf ->
     ay_pleg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_pleg_ValidatorGate checkerAccepted validatorAccepted validatorVersion ->
     ay_pleg_FallbackNoClaimPath baselineAvailable noClaimPath ->
     ay_pleg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_pleg_PureLiteralGuardFailure
    (occurrenceMismatch : Prop) (pureLedgerMismatch : Prop)
    (assignmentMismatch : Prop) (simplificationMismatch : Prop)
    (deletionMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (occurrenceMismatch -> result) ->
    (pureLedgerMismatch -> result) ->
    (assignmentMismatch -> result) ->
    (simplificationMismatch -> result) ->
    (deletionMismatch -> result) ->
    (modelMismatch -> result) ->
    (replayMismatch -> result) ->
    (buildMismatch -> result) ->
    (validatorMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_pleg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pleg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pleg_Conj currentCnf recompute

def ay_pleg_DiagnosticPureLiteralGuard
    (currentCnf : Prop)
    (occurrenceMismatch : Prop) (pureLedgerMismatch : Prop)
    (assignmentMismatch : Prop) (simplificationMismatch : Prop)
    (deletionMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pleg_Conj
    (ay_pleg_PureLiteralGuardFailure
      occurrenceMismatch pureLedgerMismatch assignmentMismatch simplificationMismatch
      deletionMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch)
    (ay_pleg_Conj
      (ay_pleg_RecomputeObligation currentCnf recompute)
      (ay_pleg_NoSemanticClaim diagnostic))

def ay_pleg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pleg_Conj exitCode claim

def ay_pleg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pleg_Disj
    (ay_pleg_ExitCodeSound exitCode (ay_pleg_Sat originalCnf model))
    (ay_pleg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_pleg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pleg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pleg_conj_left
    (left : Prop) (right : Prop) :
    ay_pleg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pleg_conj_right
    (left : Prop) (right : Prop) :
    ay_pleg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pleg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pleg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pleg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pleg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pleg_equisat_forward
    (original : Prop) (simplified : Prop) :
    ay_pleg_Equisat original simplified -> original -> simplified := by
  intro eqsat
  exact ay_pleg_conj_left (original -> simplified) (simplified -> original) eqsat

theorem ay_pleg_equisat_backward
    (original : Prop) (simplified : Prop) :
    ay_pleg_Equisat original simplified -> simplified -> original := by
  intro eqsat
  exact ay_pleg_conj_right (original -> simplified) (simplified -> original) eqsat

theorem ay_pleg_occurrence_digest_applies
    (occurrenceDigest : Prop) (occurrenceDigestAccepted : Prop)
    (occurrenceDigestManifest : Prop) :
    ay_pleg_LiteralOccurrenceDigest
      occurrenceDigest occurrenceDigestAccepted occurrenceDigestManifest ->
    occurrenceDigest -> occurrenceDigestAccepted := by
  intro digest
  exact ay_pleg_conj_right
    occurrenceDigestManifest (occurrenceDigest -> occurrenceDigestAccepted)
    digest

theorem ay_pleg_pure_literal_ledger_applies
    (pureLiteralLedger : Prop) (pureLiteralAccepted : Prop)
    (pureLiteralCoverage : Prop) :
    ay_pleg_PureLiteralLedger
      pureLiteralLedger pureLiteralAccepted pureLiteralCoverage ->
    pureLiteralLedger -> pureLiteralAccepted := by
  intro ledger
  exact ay_pleg_conj_right
    pureLiteralCoverage (pureLiteralLedger -> pureLiteralAccepted) ledger

theorem ay_pleg_assigned_literal_witness_applies
    (assignedLiteralWitness : Prop) (assignmentAccepted : Prop)
    (assignmentCoverage : Prop) :
    ay_pleg_AssignedLiteralWitness
      assignedLiteralWitness assignmentAccepted assignmentCoverage ->
    assignedLiteralWitness -> assignmentAccepted := by
  intro witness
  exact ay_pleg_conj_right
    assignmentCoverage (assignedLiteralWitness -> assignmentAccepted) witness

theorem ay_pleg_simplification_digest_applies
    (simplifiedFormulaDigest : Prop) (simplifiedDigestAccepted : Prop)
    (simplifiedDigestManifest : Prop) :
    ay_pleg_SimplifiedFormulaDigest
      simplifiedFormulaDigest simplifiedDigestAccepted simplifiedDigestManifest ->
    simplifiedFormulaDigest -> simplifiedDigestAccepted := by
  intro digest
  exact ay_pleg_conj_right
    simplifiedDigestManifest
    (simplifiedFormulaDigest -> simplifiedDigestAccepted)
    digest

theorem ay_pleg_deleted_clause_ledger_applies
    (deletedClauseLedger : Prop) (deletionAccepted : Prop)
    (deletionCoverage : Prop) :
    ay_pleg_DeletedClauseLedger
      deletedClauseLedger deletionAccepted deletionCoverage ->
    deletedClauseLedger -> deletionAccepted := by
  intro ledger
  exact ay_pleg_conj_right
    deletionCoverage (deletedClauseLedger -> deletionAccepted) ledger

theorem ay_pleg_model_extension
    (simplifiedCnf : Prop) (originalCnf : Prop)
    (simplifiedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pleg_ReconstructionEvidence
      simplifiedCnf originalCnf simplifiedModel originalModel certificate conflict ->
    ay_pleg_Sat simplifiedCnf simplifiedModel ->
    ay_pleg_Sat originalCnf originalModel := by
  intro witnesses
  exact ay_pleg_conj_left
    (ay_pleg_ModelExtensionWitness
      simplifiedCnf originalCnf simplifiedModel originalModel)
    (ay_pleg_UnsatEquisatReplayWitness
      originalCnf simplifiedCnf certificate conflict)
    witnesses

theorem ay_pleg_unsat_replay
    (simplifiedCnf : Prop) (originalCnf : Prop)
    (simplifiedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pleg_ReconstructionEvidence
      simplifiedCnf originalCnf simplifiedModel originalModel certificate conflict ->
    ay_pleg_Replay simplifiedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses
  exact ay_pleg_conj_right
    (ay_pleg_ModelExtensionWitness
      simplifiedCnf originalCnf simplifiedModel originalModel)
    (ay_pleg_UnsatEquisatReplayWitness
      originalCnf simplifiedCnf certificate conflict)
    witnesses

theorem ay_pleg_accepted_equisat
    (originalCnf : Prop) (simplifiedCnf : Prop)
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop)
    (occurrenceDigest : Prop) (occurrenceDigestAccepted : Prop)
    (occurrenceDigestManifest : Prop)
    (pureLiteralLedger : Prop) (pureLiteralAccepted : Prop)
    (pureLiteralCoverage : Prop)
    (assignedLiteralWitness : Prop) (assignmentAccepted : Prop)
    (assignmentCoverage : Prop)
    (simplifiedFormulaDigest : Prop) (simplifiedDigestAccepted : Prop)
    (simplifiedDigestManifest : Prop)
    (deletedClauseLedger : Prop) (deletionAccepted : Prop)
    (deletionCoverage : Prop)
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop)
    (simplifiedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (baselineAvailable : Prop) (noClaimPath : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pleg_AcceptedPureLiteralEliminationGuard
      originalCnf simplifiedCnf
      fingerprint fingerprintAccepted fingerprintManifest
      occurrenceDigest occurrenceDigestAccepted occurrenceDigestManifest
      pureLiteralLedger pureLiteralAccepted pureLiteralCoverage
      assignedLiteralWitness assignmentAccepted assignmentCoverage
      simplifiedFormulaDigest simplifiedDigestAccepted simplifiedDigestManifest
      deletedClauseLedger deletionAccepted deletionCoverage
      checkerAccepted validatorAccepted validatorVersion
      simplifiedModel originalModel certificate conflict
      binaryFingerprint buildReproducible
      baselineAvailable noClaimPath auditAppended auditAppendOnly ->
    ay_pleg_Equisat originalCnf simplifiedCnf := by
  intro accepted
  exact accepted (ay_pleg_Equisat originalCnf simplifiedCnf)
    (fun _fingerprint _occurrence _pure _assignment _simplified _deleted
      _reconstruct eqsat _build _validator _fallback _audit => eqsat)

theorem ay_pleg_accepted_reconstruction
    (originalCnf : Prop) (simplifiedCnf : Prop)
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop)
    (occurrenceDigest : Prop) (occurrenceDigestAccepted : Prop)
    (occurrenceDigestManifest : Prop)
    (pureLiteralLedger : Prop) (pureLiteralAccepted : Prop)
    (pureLiteralCoverage : Prop)
    (assignedLiteralWitness : Prop) (assignmentAccepted : Prop)
    (assignmentCoverage : Prop)
    (simplifiedFormulaDigest : Prop) (simplifiedDigestAccepted : Prop)
    (simplifiedDigestManifest : Prop)
    (deletedClauseLedger : Prop) (deletionAccepted : Prop)
    (deletionCoverage : Prop)
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop)
    (simplifiedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (baselineAvailable : Prop) (noClaimPath : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pleg_AcceptedPureLiteralEliminationGuard
      originalCnf simplifiedCnf
      fingerprint fingerprintAccepted fingerprintManifest
      occurrenceDigest occurrenceDigestAccepted occurrenceDigestManifest
      pureLiteralLedger pureLiteralAccepted pureLiteralCoverage
      assignedLiteralWitness assignmentAccepted assignmentCoverage
      simplifiedFormulaDigest simplifiedDigestAccepted simplifiedDigestManifest
      deletedClauseLedger deletionAccepted deletionCoverage
      checkerAccepted validatorAccepted validatorVersion
      simplifiedModel originalModel certificate conflict
      binaryFingerprint buildReproducible
      baselineAvailable noClaimPath auditAppended auditAppendOnly ->
    ay_pleg_ReconstructionEvidence
      simplifiedCnf originalCnf simplifiedModel originalModel certificate conflict := by
  intro accepted
  exact accepted
    (ay_pleg_ReconstructionEvidence
      simplifiedCnf originalCnf simplifiedModel originalModel certificate conflict)
    (fun _fingerprint _occurrence _pure _assignment _simplified _deleted
      reconstruct _eqsat _build _validator _fallback _audit => reconstruct)

theorem ay_pleg_sat_pullback
    (originalCnf : Prop) (simplifiedCnf : Prop)
    (simplifiedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pleg_ReconstructionEvidence
      simplifiedCnf originalCnf simplifiedModel originalModel certificate conflict ->
    ay_pleg_Sat simplifiedCnf simplifiedModel ->
    ay_pleg_Sat originalCnf originalModel := by
  intro witnesses satSimplified
  exact ay_pleg_model_extension
    simplifiedCnf originalCnf simplifiedModel originalModel
    certificate conflict witnesses satSimplified

theorem ay_pleg_unsat_pushback
    (originalCnf : Prop) (simplifiedCnf : Prop)
    (simplifiedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pleg_ReconstructionEvidence
      simplifiedCnf originalCnf simplifiedModel originalModel certificate conflict ->
    ay_pleg_Replay simplifiedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses replay
  exact ay_pleg_unsat_replay
    simplifiedCnf originalCnf simplifiedModel originalModel
    certificate conflict witnesses replay

theorem ay_pleg_public_sat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_pleg_ExitCodeSound exitCode (ay_pleg_Sat originalCnf originalModel) ->
    ay_pleg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro satSound
  exact ay_pleg_disj_left
    (ay_pleg_ExitCodeSound exitCode (ay_pleg_Sat originalCnf originalModel))
    (ay_pleg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    satSound

theorem ay_pleg_public_unsat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_pleg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_pleg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro unsatSound
  exact ay_pleg_disj_right
    (ay_pleg_ExitCodeSound exitCode (ay_pleg_Sat originalCnf originalModel))
    (ay_pleg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    unsatSound

theorem ay_pleg_failure_occurrence
    (occurrenceMismatch pureLedgerMismatch assignmentMismatch simplificationMismatch : Prop)
    (deletionMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    occurrenceMismatch ->
    ay_pleg_PureLiteralGuardFailure
      occurrenceMismatch pureLedgerMismatch assignmentMismatch simplificationMismatch
      deletionMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result occurrence_case _pure_case _assignment_case _simplification_case
    _deletion_case _model_case _replay_case _build_case _validator_case
    _audit_case
  exact occurrence_case h

theorem ay_pleg_failure_pure_ledger
    (occurrenceMismatch pureLedgerMismatch assignmentMismatch simplificationMismatch : Prop)
    (deletionMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    pureLedgerMismatch ->
    ay_pleg_PureLiteralGuardFailure
      occurrenceMismatch pureLedgerMismatch assignmentMismatch simplificationMismatch
      deletionMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _occurrence_case pure_case _assignment_case _simplification_case
    _deletion_case _model_case _replay_case _build_case _validator_case
    _audit_case
  exact pure_case h

theorem ay_pleg_failure_assignment
    (occurrenceMismatch pureLedgerMismatch assignmentMismatch simplificationMismatch : Prop)
    (deletionMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    assignmentMismatch ->
    ay_pleg_PureLiteralGuardFailure
      occurrenceMismatch pureLedgerMismatch assignmentMismatch simplificationMismatch
      deletionMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _occurrence_case _pure_case assignment_case _simplification_case
    _deletion_case _model_case _replay_case _build_case _validator_case
    _audit_case
  exact assignment_case h

theorem ay_pleg_failure_simplification
    (occurrenceMismatch pureLedgerMismatch assignmentMismatch simplificationMismatch : Prop)
    (deletionMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    simplificationMismatch ->
    ay_pleg_PureLiteralGuardFailure
      occurrenceMismatch pureLedgerMismatch assignmentMismatch simplificationMismatch
      deletionMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _occurrence_case _pure_case _assignment_case simplification_case
    _deletion_case _model_case _replay_case _build_case _validator_case
    _audit_case
  exact simplification_case h

theorem ay_pleg_failure_deletion
    (occurrenceMismatch pureLedgerMismatch assignmentMismatch simplificationMismatch : Prop)
    (deletionMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    deletionMismatch ->
    ay_pleg_PureLiteralGuardFailure
      occurrenceMismatch pureLedgerMismatch assignmentMismatch simplificationMismatch
      deletionMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _occurrence_case _pure_case _assignment_case _simplification_case
    deletion_case _model_case _replay_case _build_case _validator_case
    _audit_case
  exact deletion_case h

theorem ay_pleg_failure_model
    (occurrenceMismatch pureLedgerMismatch assignmentMismatch simplificationMismatch : Prop)
    (deletionMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    modelMismatch ->
    ay_pleg_PureLiteralGuardFailure
      occurrenceMismatch pureLedgerMismatch assignmentMismatch simplificationMismatch
      deletionMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _occurrence_case _pure_case _assignment_case _simplification_case
    _deletion_case model_case _replay_case _build_case _validator_case
    _audit_case
  exact model_case h

theorem ay_pleg_failure_replay
    (occurrenceMismatch pureLedgerMismatch assignmentMismatch simplificationMismatch : Prop)
    (deletionMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    replayMismatch ->
    ay_pleg_PureLiteralGuardFailure
      occurrenceMismatch pureLedgerMismatch assignmentMismatch simplificationMismatch
      deletionMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _occurrence_case _pure_case _assignment_case _simplification_case
    _deletion_case _model_case replay_case _build_case _validator_case
    _audit_case
  exact replay_case h

theorem ay_pleg_failure_build
    (occurrenceMismatch pureLedgerMismatch assignmentMismatch simplificationMismatch : Prop)
    (deletionMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    buildMismatch ->
    ay_pleg_PureLiteralGuardFailure
      occurrenceMismatch pureLedgerMismatch assignmentMismatch simplificationMismatch
      deletionMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _occurrence_case _pure_case _assignment_case _simplification_case
    _deletion_case _model_case _replay_case build_case _validator_case
    _audit_case
  exact build_case h

theorem ay_pleg_failure_validator
    (occurrenceMismatch pureLedgerMismatch assignmentMismatch simplificationMismatch : Prop)
    (deletionMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    validatorMismatch ->
    ay_pleg_PureLiteralGuardFailure
      occurrenceMismatch pureLedgerMismatch assignmentMismatch simplificationMismatch
      deletionMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _occurrence_case _pure_case _assignment_case _simplification_case
    _deletion_case _model_case _replay_case _build_case validator_case
    _audit_case
  exact validator_case h

theorem ay_pleg_failure_audit
    (occurrenceMismatch pureLedgerMismatch assignmentMismatch simplificationMismatch : Prop)
    (deletionMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    auditMismatch ->
    ay_pleg_PureLiteralGuardFailure
      occurrenceMismatch pureLedgerMismatch assignmentMismatch simplificationMismatch
      deletionMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _occurrence_case _pure_case _assignment_case _simplification_case
    _deletion_case _model_case _replay_case _build_case _validator_case
    audit_case
  exact audit_case h

theorem ay_pleg_diagnostic_no_claim
    (currentCnf : Prop)
    (occurrenceMismatch pureLedgerMismatch assignmentMismatch simplificationMismatch : Prop)
    (deletionMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pleg_DiagnosticPureLiteralGuard
      currentCnf occurrenceMismatch pureLedgerMismatch assignmentMismatch
      simplificationMismatch deletionMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch recompute diagnostic ->
    ay_pleg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard
  exact ay_pleg_conj_right
    (ay_pleg_RecomputeObligation currentCnf recompute)
    (ay_pleg_NoSemanticClaim diagnostic)
    (ay_pleg_conj_right
      (ay_pleg_PureLiteralGuardFailure
        occurrenceMismatch pureLedgerMismatch assignmentMismatch simplificationMismatch
        deletionMismatch modelMismatch replayMismatch buildMismatch
        validatorMismatch auditMismatch)
      (ay_pleg_Conj
        (ay_pleg_RecomputeObligation currentCnf recompute)
        (ay_pleg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_pleg_diagnostic_recompute
    (currentCnf : Prop)
    (occurrenceMismatch pureLedgerMismatch assignmentMismatch simplificationMismatch : Prop)
    (deletionMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pleg_DiagnosticPureLiteralGuard
      currentCnf occurrenceMismatch pureLedgerMismatch assignmentMismatch
      simplificationMismatch deletionMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch recompute diagnostic ->
    ay_pleg_RecomputeObligation currentCnf recompute := by
  intro diagnosticGuard
  exact ay_pleg_conj_left
    (ay_pleg_RecomputeObligation currentCnf recompute)
    (ay_pleg_NoSemanticClaim diagnostic)
    (ay_pleg_conj_right
      (ay_pleg_PureLiteralGuardFailure
        occurrenceMismatch pureLedgerMismatch assignmentMismatch simplificationMismatch
        deletionMismatch modelMismatch replayMismatch buildMismatch
        validatorMismatch auditMismatch)
      (ay_pleg_Conj
        (ay_pleg_RecomputeObligation currentCnf recompute)
        (ay_pleg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_pleg_failed_guard_cannot_bless_public_result
    (currentCnf : Prop)
    (occurrenceMismatch pureLedgerMismatch assignmentMismatch simplificationMismatch : Prop)
    (deletionMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_pleg_DiagnosticPureLiteralGuard
      currentCnf occurrenceMismatch pureLedgerMismatch assignmentMismatch
      simplificationMismatch deletionMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch recompute diagnostic ->
    ay_pleg_PublicResult originalCnf model certificate conflict exitCode ->
    ay_pleg_Conj
      (ay_pleg_NoSemanticClaim diagnostic)
      (ay_pleg_RecomputeObligation currentCnf recompute) := by
  intro diagnosticGuard _publicResult
  exact ay_pleg_conj_intro
    (ay_pleg_NoSemanticClaim diagnostic)
    (ay_pleg_RecomputeObligation currentCnf recompute)
    (ay_pleg_diagnostic_no_claim
      currentCnf occurrenceMismatch pureLedgerMismatch assignmentMismatch
      simplificationMismatch deletionMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch recompute diagnostic
      diagnosticGuard)
    (ay_pleg_diagnostic_recompute
      currentCnf occurrenceMismatch pureLedgerMismatch assignmentMismatch
      simplificationMismatch deletionMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch recompute diagnostic
      diagnosticGuard)

theorem ay_pleg_failed_guard_cannot_bless_public_sat
    (currentCnf : Prop)
    (occurrenceMismatch pureLedgerMismatch assignmentMismatch simplificationMismatch : Prop)
    (deletionMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop) (exitCode : Prop) :
    ay_pleg_DiagnosticPureLiteralGuard
      currentCnf occurrenceMismatch pureLedgerMismatch assignmentMismatch
      simplificationMismatch deletionMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch recompute diagnostic ->
    ay_pleg_ExitCodeSound exitCode (ay_pleg_Sat originalCnf model) ->
    ay_pleg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _satClaim
  exact ay_pleg_diagnostic_no_claim
    currentCnf occurrenceMismatch pureLedgerMismatch assignmentMismatch
    simplificationMismatch deletionMismatch modelMismatch replayMismatch
    buildMismatch validatorMismatch auditMismatch recompute diagnostic
    diagnosticGuard

theorem ay_pleg_failed_guard_cannot_bless_public_unsat
    (currentCnf : Prop)
    (occurrenceMismatch pureLedgerMismatch assignmentMismatch simplificationMismatch : Prop)
    (deletionMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (certificate : Prop) (conflict : Prop)
    (exitCode : Prop) :
    ay_pleg_DiagnosticPureLiteralGuard
      currentCnf occurrenceMismatch pureLedgerMismatch assignmentMismatch
      simplificationMismatch deletionMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch recompute diagnostic ->
    ay_pleg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_pleg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _unsatClaim
  exact ay_pleg_diagnostic_no_claim
    currentCnf occurrenceMismatch pureLedgerMismatch assignmentMismatch
    simplificationMismatch deletionMismatch modelMismatch replayMismatch
    buildMismatch validatorMismatch auditMismatch recompute diagnostic
    diagnosticGuard
