-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Clause-database delta guard soundness.
-- The propositions stand for before/after clause DB digests, add/delete delta ledgers, clause-id remap
-- witnesses, reconstruction witnesses, fingerprint agreement, checker replay,
-- fallback/build/validator gates, audit transcripts, diagnostics, and public
-- SAT/UNSAT reports.

def ay_cddg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_cddg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_cddg_Equisat (before : Prop) (after : Prop) :=
  ay_cddg_Conj (before -> after) (after -> before)

def ay_cddg_Sat (cnf : Prop) (model : Prop) :=
  ay_cddg_Conj cnf model

def ay_cddg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_cddg_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_cddg_Conj (leftId -> rightId) (rightId -> leftId)

def ay_cddg_BeforeAfterClauseDbDigest
    (clauseDbDelta : Prop) (clauseDbDeltaAccepted : Prop)
    (clauseDbDeltaManifest : Prop) :=
  ay_cddg_Conj clauseDbDeltaManifest (clauseDbDelta -> clauseDbDeltaAccepted)

def ay_cddg_AddDeleteDeltaLedger
    (addDeleteDelta : Prop) (deltaAccepted : Prop)
    (addDeleteDeltaWitness : Prop) :=
  ay_cddg_Conj addDeleteDeltaWitness (addDeleteDelta -> deltaAccepted)

def ay_cddg_ClauseIdRemapWitness
    (clauseIdRemap : Prop) (clauseIdRemapAccepted : Prop)
    (clauseIdRemapManifest : Prop) :=
  ay_cddg_Conj clauseIdRemapManifest (clauseIdRemap -> clauseIdRemapAccepted)

def ay_cddg_DeltaReplayCoverage
    (deltaReplayCoverage : Prop) (deltaReplayCoverageAccepted : Prop)
    (deltaReplayCoverageDigest : Prop) :=
  ay_cddg_Conj deltaReplayCoverageDigest (deltaReplayCoverage -> deltaReplayCoverageAccepted)

def ay_cddg_ModelProjectionReconstruction
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :=
  ay_cddg_Sat replayedCnf replayedModel ->
    ay_cddg_Sat originalCnf originalModel

def ay_cddg_ProofReconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_cddg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_cddg_ReconstructionWitnesses
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_cddg_Conj
    (ay_cddg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_cddg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)

def ay_cddg_FingerprintAgreement
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_cddg_Conj fingerprintWitness
    (ay_cddg_IdMatch originalFingerprint replayedFingerprint)

def ay_cddg_CheckerReplay
    (deltaReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_cddg_Conj deltaReplayCertificate checkerAccepted

def ay_cddg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_cddg_Conj baselineSolver baselineAvailable

def ay_cddg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_cddg_Conj binaryFingerprint buildReproducible

def ay_cddg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_cddg_Conj validatorAccepted validatorVersion

def ay_cddg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_cddg_Conj auditAppended auditAppendOnly

def ay_cddg_AcceptedClauseDatabaseDeltaGuard
    (originalCnf : Prop) (replayedCnf : Prop)
    (clauseDbDelta : Prop) (clauseDbDeltaAccepted : Prop) (clauseDbDeltaManifest : Prop)
    (addDeleteDelta : Prop) (deltaAccepted : Prop) (addDeleteDeltaWitness : Prop)
    (clauseIdRemap : Prop) (clauseIdRemapAccepted : Prop) (clauseIdRemapManifest : Prop)
    (deltaReplayCoverage : Prop) (deltaReplayCoverageAccepted : Prop)
    (deltaReplayCoverageDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (deltaReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_cddg_BeforeAfterClauseDbDigest
       clauseDbDelta clauseDbDeltaAccepted clauseDbDeltaManifest ->
     ay_cddg_AddDeleteDeltaLedger
       addDeleteDelta deltaAccepted addDeleteDeltaWitness ->
     ay_cddg_ClauseIdRemapWitness
       clauseIdRemap clauseIdRemapAccepted clauseIdRemapManifest ->
     ay_cddg_DeltaReplayCoverage
       deltaReplayCoverage deltaReplayCoverageAccepted deltaReplayCoverageDigest ->
     ay_cddg_ReconstructionWitnesses
       replayedCnf originalCnf replayedModel originalModel
       certificate conflict ->
     ay_cddg_Equisat originalCnf replayedCnf ->
     ay_cddg_FingerprintAgreement
       originalFingerprint replayedFingerprint fingerprintWitness ->
     ay_cddg_CheckerReplay deltaReplayCertificate checkerAccepted ->
     ay_cddg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_cddg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_cddg_ValidatorGate validatorAccepted validatorVersion ->
     ay_cddg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_cddg_ClauseDatabaseDeltaGuardFailure
    (staleBeforeAfterClauseDbDigest : Prop) (deltaLedgerMismatch : Prop)
    (clauseIdRemapMismatch : Prop)
    (deltaReplayCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (staleBeforeAfterClauseDbDigest -> result) ->
    (deltaLedgerMismatch -> result) ->
    (clauseIdRemapMismatch -> result) ->
    (deltaReplayCoverageGap -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (missingBaseline -> result) ->
    (buildDrift -> result) ->
    (validatorFailure -> result) ->
    (auditContradiction -> result) ->
    result

def ay_cddg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_cddg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_cddg_Conj currentCnf recompute

def ay_cddg_DiagnosticClauseDatabaseDeltaGuard
    (currentCnf : Prop)
    (staleBeforeAfterClauseDbDigest : Prop) (deltaLedgerMismatch : Prop)
    (clauseIdRemapMismatch : Prop)
    (deltaReplayCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_cddg_Conj
    (ay_cddg_ClauseDatabaseDeltaGuardFailure
      staleBeforeAfterClauseDbDigest deltaLedgerMismatch clauseIdRemapMismatch deltaReplayCoverageGap
      reconstructionGap staleFingerprint uncheckedReplay missingBaseline
      buildDrift validatorFailure
      auditContradiction)
    (ay_cddg_Conj
      (ay_cddg_RecomputeObligation currentCnf recompute)
      (ay_cddg_NoSemanticClaim diagnostic))

def ay_cddg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_cddg_Conj exitCode claim

def ay_cddg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_cddg_Disj
    (ay_cddg_ExitCodeSound exitCode (ay_cddg_Sat originalCnf model))
    (ay_cddg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_cddg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_cddg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_cddg_conj_left
    (left : Prop) (right : Prop) :
    ay_cddg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_cddg_conj_right
    (left : Prop) (right : Prop) :
    ay_cddg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_cddg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_cddg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_cddg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_cddg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_cddg_equisat_forward
    (before : Prop) (after : Prop) :
    ay_cddg_Equisat before after ->
    before -> after := by
  intro eqsat
  exact ay_cddg_conj_left (before -> after) (after -> before) eqsat

theorem ay_cddg_equisat_backward
    (before : Prop) (after : Prop) :
    ay_cddg_Equisat before after ->
    after -> before := by
  intro eqsat
  exact ay_cddg_conj_right (before -> after) (after -> before) eqsat

theorem ay_cddg_before_after_clause_db_digest_applies
    (clauseDbDelta : Prop) (clauseDbDeltaAccepted : Prop)
    (clauseDbDeltaManifest : Prop) :
    ay_cddg_BeforeAfterClauseDbDigest
      clauseDbDelta clauseDbDeltaAccepted clauseDbDeltaManifest ->
    clauseDbDelta -> clauseDbDeltaAccepted := by
  intro digest
  exact ay_cddg_conj_right clauseDbDeltaManifest
    (clauseDbDelta -> clauseDbDeltaAccepted) digest

theorem ay_cddg_add_delete_delta_ledger_applies
    (addDeleteDelta : Prop) (deltaAccepted : Prop)
    (addDeleteDeltaWitness : Prop) :
    ay_cddg_AddDeleteDeltaLedger
      addDeleteDelta deltaAccepted addDeleteDeltaWitness ->
    addDeleteDelta -> deltaAccepted := by
  intro digest
  exact ay_cddg_conj_right addDeleteDeltaWitness
    (addDeleteDelta -> deltaAccepted) digest

theorem ay_cddg_clause_id_remap_witness_applies
    (clauseIdRemap : Prop) (clauseIdRemapAccepted : Prop)
    (clauseIdRemapManifest : Prop) :
    ay_cddg_ClauseIdRemapWitness
      clauseIdRemap clauseIdRemapAccepted clauseIdRemapManifest ->
    clauseIdRemap -> clauseIdRemapAccepted := by
  intro ledger
  exact ay_cddg_conj_right clauseIdRemapManifest
    (clauseIdRemap -> clauseIdRemapAccepted) ledger

theorem ay_cddg_delta_replay_coverage_applies
    (deltaReplayCoverage : Prop) (deltaReplayCoverageAccepted : Prop)
    (deltaReplayCoverageDigest : Prop) :
    ay_cddg_DeltaReplayCoverage
      deltaReplayCoverage deltaReplayCoverageAccepted deltaReplayCoverageDigest ->
    deltaReplayCoverage -> deltaReplayCoverageAccepted := by
  intro coverage
  exact ay_cddg_conj_right deltaReplayCoverageDigest
    (deltaReplayCoverage -> deltaReplayCoverageAccepted) coverage

theorem ay_cddg_model_projection_reconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_cddg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_cddg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel := by
  intro witnesses
  exact ay_cddg_conj_left
    (ay_cddg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_cddg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_cddg_proof_reconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_cddg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_cddg_ProofReconstruction
      originalCnf replayedCnf certificate conflict := by
  intro witnesses
  exact ay_cddg_conj_right
    (ay_cddg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_cddg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_cddg_accepted_equisat
    (originalCnf : Prop) (replayedCnf : Prop)
    (clauseDbDelta : Prop) (clauseDbDeltaAccepted : Prop) (clauseDbDeltaManifest : Prop)
    (addDeleteDelta : Prop) (deltaAccepted : Prop) (addDeleteDeltaWitness : Prop)
    (clauseIdRemap : Prop) (clauseIdRemapAccepted : Prop) (clauseIdRemapManifest : Prop)
    (deltaReplayCoverage : Prop) (deltaReplayCoverageAccepted : Prop)
    (deltaReplayCoverageDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (deltaReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_cddg_AcceptedClauseDatabaseDeltaGuard
      originalCnf replayedCnf
      clauseDbDelta clauseDbDeltaAccepted clauseDbDeltaManifest
      addDeleteDelta deltaAccepted addDeleteDeltaWitness
      clauseIdRemap clauseIdRemapAccepted clauseIdRemapManifest
      deltaReplayCoverage deltaReplayCoverageAccepted deltaReplayCoverageDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      deltaReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_cddg_Equisat originalCnf replayedCnf := by
  intro accepted
  exact accepted (ay_cddg_Equisat originalCnf replayedCnf)
    (fun _manifest _schema _auxiliary _coverage _reconstruct eqsat _coverage _checker
      _fallback _build _validator _audit => eqsat)

theorem ay_cddg_accepted_replay_preserving
    (originalCnf : Prop) (replayedCnf : Prop)
    (clauseDbDelta : Prop) (clauseDbDeltaAccepted : Prop) (clauseDbDeltaManifest : Prop)
    (addDeleteDelta : Prop) (deltaAccepted : Prop) (addDeleteDeltaWitness : Prop)
    (clauseIdRemap : Prop) (clauseIdRemapAccepted : Prop) (clauseIdRemapManifest : Prop)
    (deltaReplayCoverage : Prop) (deltaReplayCoverageAccepted : Prop)
    (deltaReplayCoverageDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (deltaReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_cddg_AcceptedClauseDatabaseDeltaGuard
      originalCnf replayedCnf
      clauseDbDelta clauseDbDeltaAccepted clauseDbDeltaManifest
      addDeleteDelta deltaAccepted addDeleteDeltaWitness
      clauseIdRemap clauseIdRemapAccepted clauseIdRemapManifest
      deltaReplayCoverage deltaReplayCoverageAccepted deltaReplayCoverageDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      deltaReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    originalCnf -> replayedCnf := by
  intro accepted
  exact ay_cddg_equisat_forward originalCnf replayedCnf
    (ay_cddg_accepted_equisat
      originalCnf replayedCnf
      clauseDbDelta clauseDbDeltaAccepted clauseDbDeltaManifest
      addDeleteDelta deltaAccepted addDeleteDeltaWitness
      clauseIdRemap clauseIdRemapAccepted clauseIdRemapManifest
      deltaReplayCoverage deltaReplayCoverageAccepted deltaReplayCoverageDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      deltaReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly
      accepted)

theorem ay_cddg_accepted_checker_replay
    (originalCnf : Prop) (replayedCnf : Prop)
    (clauseDbDelta : Prop) (clauseDbDeltaAccepted : Prop) (clauseDbDeltaManifest : Prop)
    (addDeleteDelta : Prop) (deltaAccepted : Prop) (addDeleteDeltaWitness : Prop)
    (clauseIdRemap : Prop) (clauseIdRemapAccepted : Prop) (clauseIdRemapManifest : Prop)
    (deltaReplayCoverage : Prop) (deltaReplayCoverageAccepted : Prop)
    (deltaReplayCoverageDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (deltaReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_cddg_AcceptedClauseDatabaseDeltaGuard
      originalCnf replayedCnf
      clauseDbDelta clauseDbDeltaAccepted clauseDbDeltaManifest
      addDeleteDelta deltaAccepted addDeleteDeltaWitness
      clauseIdRemap clauseIdRemapAccepted clauseIdRemapManifest
      deltaReplayCoverage deltaReplayCoverageAccepted deltaReplayCoverageDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      deltaReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_cddg_CheckerReplay deltaReplayCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_cddg_CheckerReplay deltaReplayCertificate checkerAccepted)
    (fun _manifest _schema _auxiliary _coverage _reconstruct _eqsat _coverage checker
      _fallback _build _validator _audit => checker)

theorem ay_cddg_accepted_audit_transcript
    (originalCnf : Prop) (replayedCnf : Prop)
    (clauseDbDelta : Prop) (clauseDbDeltaAccepted : Prop) (clauseDbDeltaManifest : Prop)
    (addDeleteDelta : Prop) (deltaAccepted : Prop) (addDeleteDeltaWitness : Prop)
    (clauseIdRemap : Prop) (clauseIdRemapAccepted : Prop) (clauseIdRemapManifest : Prop)
    (deltaReplayCoverage : Prop) (deltaReplayCoverageAccepted : Prop)
    (deltaReplayCoverageDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (deltaReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_cddg_AcceptedClauseDatabaseDeltaGuard
      originalCnf replayedCnf
      clauseDbDelta clauseDbDeltaAccepted clauseDbDeltaManifest
      addDeleteDelta deltaAccepted addDeleteDeltaWitness
      clauseIdRemap clauseIdRemapAccepted clauseIdRemapManifest
      deltaReplayCoverage deltaReplayCoverageAccepted deltaReplayCoverageDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      deltaReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_cddg_AuditTranscript auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_cddg_AuditTranscript auditAppended auditAppendOnly)
    (fun _manifest _schema _auxiliary _coverage _reconstruct _eqsat _coverage _checker
      _fallback _build _validator audit => audit)

theorem ay_cddg_sat_pullback
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :
    ay_cddg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel ->
    ay_cddg_Sat replayedCnf replayedModel ->
    ay_cddg_Sat originalCnf originalModel := by
  intro reconstruct replayedSat
  exact reconstruct replayedSat

theorem ay_cddg_unsat_pushback
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_cddg_ProofReconstruction
      originalCnf replayedCnf certificate conflict ->
    ay_cddg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruct replayedReplay
  exact reconstruct replayedReplay

theorem ay_cddg_public_sat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (clauseDbDelta : Prop) (clauseDbDeltaAccepted : Prop) (clauseDbDeltaManifest : Prop)
    (addDeleteDelta : Prop) (deltaAccepted : Prop) (addDeleteDeltaWitness : Prop)
    (clauseIdRemap : Prop) (clauseIdRemapAccepted : Prop) (clauseIdRemapManifest : Prop)
    (deltaReplayCoverage : Prop) (deltaReplayCoverageAccepted : Prop)
    (deltaReplayCoverageDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (deltaReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_cddg_AcceptedClauseDatabaseDeltaGuard
      originalCnf replayedCnf
      clauseDbDelta clauseDbDeltaAccepted clauseDbDeltaManifest
      addDeleteDelta deltaAccepted addDeleteDeltaWitness
      clauseIdRemap clauseIdRemapAccepted clauseIdRemapManifest
      deltaReplayCoverage deltaReplayCoverageAccepted deltaReplayCoverageDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      deltaReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_cddg_Sat replayedCnf replayedModel ->
    exitCode ->
    ay_cddg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedSat hexit
  exact accepted
    (ay_cddg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _manifest _schema _auxiliary _coverage reconstruct _eqsat _coverage _checker
      _fallback _build _validator _audit =>
      ay_cddg_disj_left
        (ay_cddg_ExitCodeSound exitCode
          (ay_cddg_Sat originalCnf originalModel))
        (ay_cddg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_cddg_conj_intro exitCode
          (ay_cddg_Sat originalCnf originalModel)
          hexit
          ((ay_cddg_model_projection_reconstruction
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedSat)))

theorem ay_cddg_public_unsat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (clauseDbDelta : Prop) (clauseDbDeltaAccepted : Prop) (clauseDbDeltaManifest : Prop)
    (addDeleteDelta : Prop) (deltaAccepted : Prop) (addDeleteDeltaWitness : Prop)
    (clauseIdRemap : Prop) (clauseIdRemapAccepted : Prop) (clauseIdRemapManifest : Prop)
    (deltaReplayCoverage : Prop) (deltaReplayCoverageAccepted : Prop)
    (deltaReplayCoverageDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (deltaReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_cddg_AcceptedClauseDatabaseDeltaGuard
      originalCnf replayedCnf
      clauseDbDelta clauseDbDeltaAccepted clauseDbDeltaManifest
      addDeleteDelta deltaAccepted addDeleteDeltaWitness
      clauseIdRemap clauseIdRemapAccepted clauseIdRemapManifest
      deltaReplayCoverage deltaReplayCoverageAccepted deltaReplayCoverageDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      deltaReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_cddg_Replay replayedCnf certificate conflict ->
    exitCode ->
    ay_cddg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedReplay hexit
  exact accepted
    (ay_cddg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _manifest _schema _auxiliary _coverage reconstruct _eqsat _coverage _checker
      _fallback _build _validator _audit =>
      ay_cddg_disj_right
        (ay_cddg_ExitCodeSound exitCode
          (ay_cddg_Sat originalCnf originalModel))
        (ay_cddg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_cddg_conj_intro exitCode
          (certificate -> originalCnf -> conflict)
          hexit
          ((ay_cddg_proof_reconstruction
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedReplay)))

theorem ay_cddg_failure_stale_before_after_clause_db_digest
    (staleBeforeAfterClauseDbDigest : Prop) (deltaLedgerMismatch : Prop)
    (clauseIdRemapMismatch : Prop)
    (deltaReplayCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleBeforeAfterClauseDbDigest ->
    ay_cddg_ClauseDatabaseDeltaGuardFailure
      staleBeforeAfterClauseDbDigest deltaLedgerMismatch clauseIdRemapMismatch deltaReplayCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result constraint_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact constraint_case failure

theorem ay_cddg_failure_add_delete_delta_ledger
    (staleBeforeAfterClauseDbDigest : Prop) (deltaLedgerMismatch : Prop)
    (clauseIdRemapMismatch : Prop)
    (deltaReplayCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    deltaLedgerMismatch ->
    ay_cddg_ClauseDatabaseDeltaGuardFailure
      staleBeforeAfterClauseDbDigest deltaLedgerMismatch clauseIdRemapMismatch deltaReplayCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case schema_case _auxiliary_case _coverage_case
    _reconstruction_case _coverage_case _schema_case _baseline_case
    _build_case _validator_case _audit_case
  exact schema_case failure

theorem ay_cddg_failure_clause_id_remap_witness
    (staleBeforeAfterClauseDbDigest : Prop) (deltaLedgerMismatch : Prop)
    (clauseIdRemapMismatch : Prop)
    (deltaReplayCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    clauseIdRemapMismatch ->
    ay_cddg_ClauseDatabaseDeltaGuardFailure
      staleBeforeAfterClauseDbDigest deltaLedgerMismatch clauseIdRemapMismatch deltaReplayCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact auxiliary_case failure

theorem ay_cddg_failure_delta_replay_coverage
    (staleBeforeAfterClauseDbDigest : Prop) (deltaLedgerMismatch : Prop)
    (clauseIdRemapMismatch : Prop)
    (deltaReplayCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    deltaReplayCoverageGap ->
    ay_cddg_ClauseDatabaseDeltaGuardFailure
      staleBeforeAfterClauseDbDigest deltaLedgerMismatch clauseIdRemapMismatch deltaReplayCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case auxiliary_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact auxiliary_case failure

theorem ay_cddg_failure_reconstruction
    (staleBeforeAfterClauseDbDigest : Prop) (deltaLedgerMismatch : Prop)
    (clauseIdRemapMismatch : Prop)
    (deltaReplayCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_cddg_ClauseDatabaseDeltaGuardFailure
      staleBeforeAfterClauseDbDigest deltaLedgerMismatch clauseIdRemapMismatch deltaReplayCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case failure

theorem ay_cddg_failure_stale_fingerprint
    (staleBeforeAfterClauseDbDigest : Prop) (deltaLedgerMismatch : Prop)
    (clauseIdRemapMismatch : Prop)
    (deltaReplayCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_cddg_ClauseDatabaseDeltaGuardFailure
      staleBeforeAfterClauseDbDigest deltaLedgerMismatch clauseIdRemapMismatch deltaReplayCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    fingerprint_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact fingerprint_case failure

theorem ay_cddg_failure_unchecked_replay
    (staleBeforeAfterClauseDbDigest : Prop) (deltaLedgerMismatch : Prop)
    (clauseIdRemapMismatch : Prop)
    (deltaReplayCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_cddg_ClauseDatabaseDeltaGuardFailure
      staleBeforeAfterClauseDbDigest deltaLedgerMismatch clauseIdRemapMismatch deltaReplayCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact schema_case failure

theorem ay_cddg_failure_missing_baseline
    (staleBeforeAfterClauseDbDigest : Prop) (deltaLedgerMismatch : Prop)
    (clauseIdRemapMismatch : Prop)
    (deltaReplayCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingBaseline ->
    ay_cddg_ClauseDatabaseDeltaGuardFailure
      staleBeforeAfterClauseDbDigest deltaLedgerMismatch clauseIdRemapMismatch deltaReplayCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case failure

theorem ay_cddg_failure_build
    (staleBeforeAfterClauseDbDigest : Prop) (deltaLedgerMismatch : Prop)
    (clauseIdRemapMismatch : Prop)
    (deltaReplayCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_cddg_ClauseDatabaseDeltaGuardFailure
      staleBeforeAfterClauseDbDigest deltaLedgerMismatch clauseIdRemapMismatch deltaReplayCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case failure

theorem ay_cddg_failure_validator
    (staleBeforeAfterClauseDbDigest : Prop) (deltaLedgerMismatch : Prop)
    (clauseIdRemapMismatch : Prop)
    (deltaReplayCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    validatorFailure ->
    ay_cddg_ClauseDatabaseDeltaGuardFailure
      staleBeforeAfterClauseDbDigest deltaLedgerMismatch clauseIdRemapMismatch deltaReplayCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case failure

theorem ay_cddg_failure_audit
    (staleBeforeAfterClauseDbDigest : Prop) (deltaLedgerMismatch : Prop)
    (clauseIdRemapMismatch : Prop)
    (deltaReplayCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_cddg_ClauseDatabaseDeltaGuardFailure
      staleBeforeAfterClauseDbDigest deltaLedgerMismatch clauseIdRemapMismatch deltaReplayCoverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case failure

theorem ay_cddg_diagnostic_no_claim
    (currentCnf : Prop)
    (staleBeforeAfterClauseDbDigest : Prop) (deltaLedgerMismatch : Prop)
    (clauseIdRemapMismatch : Prop)
    (deltaReplayCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_cddg_DiagnosticClauseDatabaseDeltaGuard
      currentCnf staleBeforeAfterClauseDbDigest deltaLedgerMismatch clauseIdRemapMismatch deltaReplayCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_cddg_NoSemanticClaim diagnostic := by
  intro diagnosticBundle
  exact ay_cddg_conj_right
    (ay_cddg_RecomputeObligation currentCnf recompute)
    (ay_cddg_NoSemanticClaim diagnostic)
    (ay_cddg_conj_right
      (ay_cddg_ClauseDatabaseDeltaGuardFailure
        staleBeforeAfterClauseDbDigest deltaLedgerMismatch clauseIdRemapMismatch deltaReplayCoverageGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_cddg_Conj
        (ay_cddg_RecomputeObligation currentCnf recompute)
        (ay_cddg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_cddg_diagnostic_recompute
    (currentCnf : Prop)
    (staleBeforeAfterClauseDbDigest : Prop) (deltaLedgerMismatch : Prop)
    (clauseIdRemapMismatch : Prop)
    (deltaReplayCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_cddg_DiagnosticClauseDatabaseDeltaGuard
      currentCnf staleBeforeAfterClauseDbDigest deltaLedgerMismatch clauseIdRemapMismatch deltaReplayCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_cddg_RecomputeObligation currentCnf recompute := by
  intro diagnosticBundle
  exact ay_cddg_conj_left
    (ay_cddg_RecomputeObligation currentCnf recompute)
    (ay_cddg_NoSemanticClaim diagnostic)
    (ay_cddg_conj_right
      (ay_cddg_ClauseDatabaseDeltaGuardFailure
        staleBeforeAfterClauseDbDigest deltaLedgerMismatch clauseIdRemapMismatch deltaReplayCoverageGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_cddg_Conj
        (ay_cddg_RecomputeObligation currentCnf recompute)
        (ay_cddg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_cddg_unchecked_delta_cannot_bless_public_result
    (currentCnf : Prop)
    (staleBeforeAfterClauseDbDigest : Prop) (deltaLedgerMismatch : Prop)
    (clauseIdRemapMismatch : Prop)
    (deltaReplayCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_cddg_DiagnosticClauseDatabaseDeltaGuard
      currentCnf staleBeforeAfterClauseDbDigest deltaLedgerMismatch clauseIdRemapMismatch deltaReplayCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_cddg_Conj
      (ay_cddg_NoSemanticClaim diagnostic)
      (ay_cddg_RecomputeObligation currentCnf recompute) := by
  intro _unchecked diagnosticBundle
  exact ay_cddg_conj_intro
    (ay_cddg_NoSemanticClaim diagnostic)
    (ay_cddg_RecomputeObligation currentCnf recompute)
    (ay_cddg_diagnostic_no_claim
      currentCnf staleBeforeAfterClauseDbDigest deltaLedgerMismatch clauseIdRemapMismatch deltaReplayCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
    (ay_cddg_diagnostic_recompute
      currentCnf staleBeforeAfterClauseDbDigest deltaLedgerMismatch clauseIdRemapMismatch deltaReplayCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)

theorem ay_cddg_unchecked_delta_cannot_bless_public_sat
    (currentCnf : Prop)
    (staleBeforeAfterClauseDbDigest : Prop) (deltaLedgerMismatch : Prop)
    (clauseIdRemapMismatch : Prop)
    (deltaReplayCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_cddg_DiagnosticClauseDatabaseDeltaGuard
      currentCnf staleBeforeAfterClauseDbDigest deltaLedgerMismatch clauseIdRemapMismatch deltaReplayCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_cddg_NoSemanticClaim diagnostic := by
  intro _unchecked diagnosticBundle
  exact ay_cddg_diagnostic_no_claim
    currentCnf staleBeforeAfterClauseDbDigest deltaLedgerMismatch clauseIdRemapMismatch deltaReplayCoverageGap reconstructionGap
    staleFingerprint uncheckedReplay missingBaseline buildDrift
    validatorFailure auditContradiction recompute diagnostic diagnosticBundle

theorem ay_cddg_unchecked_delta_cannot_bless_public_unsat
    (currentCnf : Prop)
    (staleBeforeAfterClauseDbDigest : Prop) (deltaLedgerMismatch : Prop)
    (clauseIdRemapMismatch : Prop)
    (deltaReplayCoverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_cddg_DiagnosticClauseDatabaseDeltaGuard
      currentCnf staleBeforeAfterClauseDbDigest deltaLedgerMismatch clauseIdRemapMismatch deltaReplayCoverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_cddg_RecomputeObligation currentCnf recompute := by
  intro _unchecked diagnosticBundle
  exact ay_cddg_diagnostic_recompute
    currentCnf staleBeforeAfterClauseDbDigest deltaLedgerMismatch clauseIdRemapMismatch deltaReplayCoverageGap reconstructionGap
    staleFingerprint uncheckedReplay missingBaseline buildDrift
    validatorFailure auditContradiction recompute diagnostic diagnosticBundle
