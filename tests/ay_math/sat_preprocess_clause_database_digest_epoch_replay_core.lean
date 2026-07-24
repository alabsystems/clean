-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Clause-database digest epoch replay soundness for preprocessing. The
-- propositions stand for database epoch ledgers, clause digest manifests,
-- transform witness ledgers, affected-clause coverage, formula
-- fingerprints, checker replay, fallback baseline, build evidence, validator
-- gates, audit evidence, diagnostics, and public SAT/UNSAT reports.

def ay_pcde_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pcde_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pcde_Equisat (before : Prop) (after : Prop) :=
  ay_pcde_Conj (before -> after) (after -> before)

def ay_pcde_Sat (cnf : Prop) (model : Prop) :=
  ay_pcde_Conj cnf model

def ay_pcde_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pcde_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pcde_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pcde_DatabaseEpochLedger
    (databaseEpoch : Prop) (databaseLedger : Prop)
    (epochWitness : Prop) :=
  ay_pcde_Conj epochWitness
    (databaseEpoch -> databaseLedger)

def ay_pcde_ClauseDigestManifest
    (clauseDigest : Prop) (digestManifest : Prop)
    (digestWitness : Prop) :=
  ay_pcde_Conj digestWitness
    (ay_pcde_Conj clauseDigest digestManifest)

def ay_pcde_TransformWitnessLedger
    (affectedClause : Prop) (transformWitness : Prop)
    (transformLedger : Prop) :=
  ay_pcde_Conj transformLedger (affectedClause -> transformWitness)

def ay_pcde_AffectedClauseCoverage
    (coveredClause : Prop) (databaseLedger : Prop)
    (coverageWitness : Prop) :=
  ay_pcde_Conj coverageWitness
    (databaseLedger -> coveredClause)

def ay_pcde_ModelReconstruction
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :=
  ay_pcde_Sat reducedCnf reducedModel ->
    ay_pcde_Sat originalCnf originalModel

def ay_pcde_ProofReconstruction
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pcde_Replay reducedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pcde_FingerprintAgreement
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pcde_Conj fingerprintWitness
    (ay_pcde_IdMatch originalFingerprint reducedFingerprint)

def ay_pcde_CheckerReplay
    (digestCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pcde_Conj digestCertificate checkerAccepted

def ay_pcde_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_pcde_Conj baselineSolver baselineAvailable

def ay_pcde_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_pcde_Conj binaryFingerprint buildReproducible

def ay_pcde_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_pcde_Conj validatorAccepted validatorVersion

def ay_pcde_AuditEvidence
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_pcde_Conj auditAppended auditAppendOnly

def ay_pcde_AcceptedClauseDatabaseDigestEpochReplay
    (originalCnf : Prop) (reducedCnf : Prop)
    (databaseEpoch : Prop) (databaseLedger : Prop)
    (epochWitness : Prop)
    (clauseDigest : Prop) (digestManifest : Prop)
    (digestWitness : Prop)
    (affectedClause : Prop) (transformWitness : Prop)
    (transformLedger : Prop)
    (coveredClause : Prop) (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (digestCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_pcde_DatabaseEpochLedger
       databaseEpoch databaseLedger epochWitness ->
     ay_pcde_ClauseDigestManifest
       clauseDigest digestManifest digestWitness ->
     ay_pcde_TransformWitnessLedger
       affectedClause transformWitness transformLedger ->
     ay_pcde_AffectedClauseCoverage
       coveredClause databaseLedger coverageWitness ->
     ay_pcde_Equisat originalCnf reducedCnf ->
     ay_pcde_ModelReconstruction
       reducedCnf originalCnf reducedModel originalModel ->
     ay_pcde_ProofReconstruction
       originalCnf reducedCnf certificate conflict ->
     ay_pcde_FingerprintAgreement
       originalFingerprint reducedFingerprint fingerprintWitness ->
     ay_pcde_CheckerReplay
       digestCertificate checkerAccepted ->
     ay_pcde_FallbackBaseline baselineSolver baselineAvailable ->
     ay_pcde_BuildEvidence binaryFingerprint buildReproducible ->
     ay_pcde_ValidatorGate validatorAccepted validatorVersion ->
     ay_pcde_AuditEvidence auditAppended auditAppendOnly ->
     result) -> result

def ay_pcde_ClauseDatabaseDigestEpochFailure
    (epochDrift : Prop) (digestManifestMismatch : Prop)
    (transformWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (epochDrift -> result) ->
    (digestManifestMismatch -> result) ->
    (transformWitnessMismatch -> result) ->
    (coverageGap -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (buildDrift -> result) ->
    (auditContradiction -> result) ->
    result

def ay_pcde_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pcde_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pcde_Conj currentCnf recompute

def ay_pcde_DiagnosticClauseDatabaseDigestEpochReplay
    (currentCnf : Prop)
    (epochDrift : Prop) (digestManifestMismatch : Prop)
    (transformWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pcde_Conj
    (ay_pcde_ClauseDatabaseDigestEpochFailure
      epochDrift digestManifestMismatch transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction)
    (ay_pcde_Conj
      (ay_pcde_RecomputeObligation currentCnf recompute)
      (ay_pcde_NoSemanticClaim diagnostic))

def ay_pcde_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pcde_Conj exitCode claim

def ay_pcde_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pcde_Disj
    (ay_pcde_ExitCodeSound exitCode (ay_pcde_Sat originalCnf model))
    (ay_pcde_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_pcde_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pcde_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pcde_conj_left
    (left : Prop) (right : Prop) :
    ay_pcde_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pcde_conj_right
    (left : Prop) (right : Prop) :
    ay_pcde_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pcde_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pcde_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pcde_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pcde_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pcde_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pcde_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pcde_conj_left (before -> after) (after -> before) eq

theorem ay_pcde_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pcde_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pcde_conj_right (before -> after) (after -> before) eq

theorem ay_pcde_database_epoch_ledger_applies
    (databaseEpoch : Prop) (databaseLedger : Prop)
    (epochWitness : Prop) :
    ay_pcde_DatabaseEpochLedger
      databaseEpoch databaseLedger epochWitness ->
    databaseEpoch ->
    databaseLedger := by
  intro accepted raw
  exact
    (ay_pcde_conj_right epochWitness
      (databaseEpoch -> databaseLedger) accepted) raw

theorem ay_pcde_clause_digest_manifest_digest
    (clauseDigest : Prop) (digestManifest : Prop)
    (digestWitness : Prop) :
    ay_pcde_ClauseDigestManifest
      clauseDigest digestManifest digestWitness ->
    clauseDigest := by
  intro accepted
  exact accepted clauseDigest
    (fun _ledger pair =>
      pair clauseDigest
        (fun duplicate _tautology => duplicate))

theorem ay_pcde_clause_digest_manifest_manifest
    (clauseDigest : Prop) (digestManifest : Prop)
    (digestWitness : Prop) :
    ay_pcde_ClauseDigestManifest
      clauseDigest digestManifest digestWitness ->
    digestManifest := by
  intro accepted
  exact accepted digestManifest
    (fun _ledger pair =>
      pair digestManifest
        (fun _duplicate tautology => tautology))

theorem ay_pcde_transform_witness_ledger
    (affectedClause : Prop) (transformWitness : Prop)
    (transformLedger : Prop) :
    ay_pcde_TransformWitnessLedger
      affectedClause transformWitness transformLedger ->
    affectedClause ->
    transformWitness := by
  intro accepted original
  exact
    (ay_pcde_conj_right transformLedger
      (affectedClause -> transformWitness) accepted) original

theorem ay_pcde_affected_clause_coverage
    (coveredClause : Prop) (databaseLedger : Prop)
    (coverageWitness : Prop) :
    ay_pcde_AffectedClauseCoverage
      coveredClause databaseLedger coverageWitness ->
    databaseLedger ->
    coveredClause := by
  intro accepted canonical
  exact
    (ay_pcde_conj_right coverageWitness
      (databaseLedger -> coveredClause) accepted) canonical

theorem ay_pcde_accepted_equisat
    (originalCnf : Prop) (reducedCnf : Prop)
    (databaseEpoch : Prop) (databaseLedger : Prop)
    (epochWitness : Prop)
    (clauseDigest : Prop) (digestManifest : Prop)
    (digestWitness : Prop)
    (affectedClause : Prop) (transformWitness : Prop)
    (transformLedger : Prop)
    (coveredClause : Prop) (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (digestCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pcde_AcceptedClauseDatabaseDigestEpochReplay
      originalCnf reducedCnf databaseEpoch databaseLedger
      epochWitness clauseDigest digestManifest
      digestWitness affectedClause transformWitness transformLedger
      coveredClause coverageWitness reducedModel originalModel
      certificate conflict originalFingerprint reducedFingerprint
      fingerprintWitness digestCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pcde_Equisat originalCnf reducedCnf := by
  intro accepted
  exact accepted (ay_pcde_Equisat originalCnf reducedCnf)
    (fun _order _accounting _coverage _ledger eq _model _proof
      _fingerprint _checker _fallback _build _validator _audit => eq)

theorem ay_pcde_accepted_checker_replay
    (originalCnf : Prop) (reducedCnf : Prop)
    (databaseEpoch : Prop) (databaseLedger : Prop)
    (epochWitness : Prop)
    (clauseDigest : Prop) (digestManifest : Prop)
    (digestWitness : Prop)
    (affectedClause : Prop) (transformWitness : Prop)
    (transformLedger : Prop)
    (coveredClause : Prop) (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (digestCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pcde_AcceptedClauseDatabaseDigestEpochReplay
      originalCnf reducedCnf databaseEpoch databaseLedger
      epochWitness clauseDigest digestManifest
      digestWitness affectedClause transformWitness transformLedger
      coveredClause coverageWitness reducedModel originalModel
      certificate conflict originalFingerprint reducedFingerprint
      fingerprintWitness digestCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pcde_CheckerReplay digestCertificate checkerAccepted := by
  intro accepted
  exact accepted
    (ay_pcde_CheckerReplay digestCertificate checkerAccepted)
    (fun _order _accounting _coverage _ledger _eq _model _proof
      _fingerprint checker _fallback _build _validator _audit => checker)

theorem ay_pcde_accepted_audit_evidence
    (originalCnf : Prop) (reducedCnf : Prop)
    (databaseEpoch : Prop) (databaseLedger : Prop)
    (epochWitness : Prop)
    (clauseDigest : Prop) (digestManifest : Prop)
    (digestWitness : Prop)
    (affectedClause : Prop) (transformWitness : Prop)
    (transformLedger : Prop)
    (coveredClause : Prop) (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (digestCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pcde_AcceptedClauseDatabaseDigestEpochReplay
      originalCnf reducedCnf databaseEpoch databaseLedger
      epochWitness clauseDigest digestManifest
      digestWitness affectedClause transformWitness transformLedger
      coveredClause coverageWitness reducedModel originalModel
      certificate conflict originalFingerprint reducedFingerprint
      fingerprintWitness digestCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pcde_AuditEvidence auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_pcde_AuditEvidence auditAppended auditAppendOnly)
    (fun _order _accounting _coverage _ledger _eq _model _proof
      _fingerprint _checker _fallback _build _validator audit => audit)

theorem ay_pcde_sat_pullback
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :
    ay_pcde_ModelReconstruction
      reducedCnf originalCnf reducedModel originalModel ->
    ay_pcde_Sat reducedCnf reducedModel ->
    ay_pcde_Sat originalCnf originalModel := by
  intro reconstruct canonicalSat
  exact reconstruct canonicalSat

theorem ay_pcde_unsat_pushback
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pcde_ProofReconstruction
      originalCnf reducedCnf certificate conflict ->
    ay_pcde_Replay reducedCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro reconstruct replay cert original
  exact reconstruct replay cert original

theorem ay_pcde_public_sat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    ay_pcde_Sat originalCnf model ->
    ay_pcde_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit sat
  exact ay_pcde_disj_left
    (ay_pcde_ExitCodeSound exitCode (ay_pcde_Sat originalCnf model))
    (ay_pcde_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pcde_conj_intro exitCode
      (ay_pcde_Sat originalCnf model) exit sat)

theorem ay_pcde_public_unsat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    (certificate -> originalCnf -> conflict) ->
    ay_pcde_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit replay
  exact ay_pcde_disj_right
    (ay_pcde_ExitCodeSound exitCode (ay_pcde_Sat originalCnf model))
    (ay_pcde_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pcde_conj_intro exitCode
      (certificate -> originalCnf -> conflict) exit replay)

theorem ay_pcde_failure_epoch_drift
    (epochDrift : Prop) (digestManifestMismatch : Prop)
    (transformWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    epochDrift ->
    ay_pcde_ClauseDatabaseDigestEpochFailure
      epochDrift digestManifestMismatch transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hEpoch h

theorem ay_pcde_failure_digest_manifest_mismatch
    (epochDrift : Prop) (digestManifestMismatch : Prop)
    (transformWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    digestManifestMismatch ->
    ay_pcde_ClauseDatabaseDigestEpochFailure
      epochDrift digestManifestMismatch transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hStaleCandidate h

theorem ay_pcde_failure_transform_witness_mismatch
    (epochDrift : Prop) (digestManifestMismatch : Prop)
    (transformWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    transformWitnessMismatch ->
    ay_pcde_ClauseDatabaseDigestEpochFailure
      epochDrift digestManifestMismatch transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hWitness h

theorem ay_pcde_failure_coverage_gap
    (epochDrift : Prop) (digestManifestMismatch : Prop)
    (transformWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    coverageGap ->
    ay_pcde_ClauseDatabaseDigestEpochFailure
      epochDrift digestManifestMismatch transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hCoverage h

theorem ay_pcde_failure_reconstruction_gap
    (epochDrift : Prop) (digestManifestMismatch : Prop)
    (transformWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_pcde_ClauseDatabaseDigestEpochFailure
      epochDrift digestManifestMismatch transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hReconstruction h

theorem ay_pcde_failure_stale_fingerprint
    (epochDrift : Prop) (digestManifestMismatch : Prop)
    (transformWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_pcde_ClauseDatabaseDigestEpochFailure
      epochDrift digestManifestMismatch transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hStaleFingerprint h

theorem ay_pcde_failure_unchecked_replay
    (epochDrift : Prop) (digestManifestMismatch : Prop)
    (transformWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_pcde_ClauseDatabaseDigestEpochFailure
      epochDrift digestManifestMismatch transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hUnchecked h

theorem ay_pcde_failure_build_drift
    (epochDrift : Prop) (digestManifestMismatch : Prop)
    (transformWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_pcde_ClauseDatabaseDigestEpochFailure
      epochDrift digestManifestMismatch transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hBuild h

theorem ay_pcde_failure_audit_contradiction
    (epochDrift : Prop) (digestManifestMismatch : Prop)
    (transformWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_pcde_ClauseDatabaseDigestEpochFailure
      epochDrift digestManifestMismatch transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hEpoch hStaleCandidate hWitness hCoverage hReconstruction
    hStaleFingerprint hUnchecked hBuild hAudit
  exact hAudit h

theorem ay_pcde_diagnostic_no_claim
    (currentCnf : Prop)
    (epochDrift : Prop) (digestManifestMismatch : Prop)
    (transformWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pcde_DiagnosticClauseDatabaseDigestEpochReplay
      currentCnf epochDrift digestManifestMismatch transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic ->
    ay_pcde_NoSemanticClaim diagnostic := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pcde_NoSemanticClaim diagnostic)
    (fun _failure tail =>
      tail (ay_pcde_NoSemanticClaim diagnostic)
        (fun _recompute noClaim => noClaim))

theorem ay_pcde_diagnostic_recompute
    (currentCnf : Prop)
    (epochDrift : Prop) (digestManifestMismatch : Prop)
    (transformWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pcde_DiagnosticClauseDatabaseDigestEpochReplay
      currentCnf epochDrift digestManifestMismatch transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic ->
    ay_pcde_RecomputeObligation currentCnf recompute := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pcde_RecomputeObligation currentCnf recompute)
    (fun _failure tail =>
      tail (ay_pcde_RecomputeObligation currentCnf recompute)
        (fun recomputeObligation _noClaim => recomputeObligation))

theorem ay_pcde_unchecked_replay_cannot_bless_public_result
    (currentCnf : Prop)
    (epochDrift : Prop) (digestManifestMismatch : Prop)
    (transformWitnessMismatch : Prop) (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_pcde_RecomputeObligation currentCnf recompute ->
    ay_pcde_NoSemanticClaim diagnostic ->
    ay_pcde_DiagnosticClauseDatabaseDigestEpochReplay
      currentCnf epochDrift digestManifestMismatch transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic := by
  intro unchecked recomputeObligation noClaim
  exact ay_pcde_conj_intro
    (ay_pcde_ClauseDatabaseDigestEpochFailure
      epochDrift digestManifestMismatch transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction)
    (ay_pcde_Conj
      (ay_pcde_RecomputeObligation currentCnf recompute)
      (ay_pcde_NoSemanticClaim diagnostic))
    (ay_pcde_failure_unchecked_replay
      epochDrift digestManifestMismatch transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction unchecked)
    (ay_pcde_conj_intro
      (ay_pcde_RecomputeObligation currentCnf recompute)
      (ay_pcde_NoSemanticClaim diagnostic)
      recomputeObligation noClaim)
