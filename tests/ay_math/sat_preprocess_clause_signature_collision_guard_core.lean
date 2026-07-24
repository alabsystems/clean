-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Clause-signature collision guard soundness.
-- The propositions stand for formula/database/cache digests, candidate pair
-- ledgers, exact-clause comparison witnesses, collision diagnostics,
-- deletion/strengthening ledgers, checker replay, reconstruction witnesses,
-- fallback/build/validator gates, audit transcripts, diagnostics, and public
-- SAT/UNSAT reports.

def ay_cscg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_cscg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_cscg_Equisat (original : Prop) (preprocessed : Prop) :=
  ay_cscg_Conj (original -> preprocessed) (preprocessed -> original)

def ay_cscg_Sat (cnf : Prop) (model : Prop) :=
  ay_cscg_Conj cnf model

def ay_cscg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_cscg_FormulaDigest
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop) :=
  ay_cscg_Conj formulaManifest (formulaDigest -> formulaDigestAccepted)

def ay_cscg_ClauseDatabaseDigest
    (databaseDigest : Prop) (databaseDigestAccepted : Prop)
    (databaseManifest : Prop) :=
  ay_cscg_Conj databaseManifest (databaseDigest -> databaseDigestAccepted)

def ay_cscg_SignatureCacheDigest
    (cacheDigest : Prop) (cacheDigestAccepted : Prop)
    (cacheManifest : Prop) :=
  ay_cscg_Conj cacheManifest (cacheDigest -> cacheDigestAccepted)

def ay_cscg_CandidatePairLedger
    (candidatePairLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop) :=
  ay_cscg_Conj candidateCoverage
    (candidatePairLedger -> candidateAccepted)

def ay_cscg_ExactClauseComparisonWitness
    (exactComparisonWitness : Prop) (exactComparisonAccepted : Prop)
    (exactComparisonCoverage : Prop) :=
  ay_cscg_Conj exactComparisonCoverage
    (exactComparisonWitness -> exactComparisonAccepted)

def ay_cscg_CollisionDiagnosticLedger
    (collisionDiagnosticLedger : Prop) (collisionAccepted : Prop)
    (collisionCoverage : Prop) :=
  ay_cscg_Conj collisionCoverage
    (collisionDiagnosticLedger -> collisionAccepted)

def ay_cscg_DeletionStrengtheningLedger
    (deletionStrengtheningLedger : Prop) (ledgerAccepted : Prop)
    (ledgerCoverage : Prop) :=
  ay_cscg_Conj ledgerCoverage
    (deletionStrengtheningLedger -> ledgerAccepted)

def ay_cscg_CheckerReplay
    (checkerReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_cscg_Conj checkerReplayCertificate checkerAccepted

def ay_cscg_ModelReconstructionWitness
    (preprocessedCnf : Prop) (originalCnf : Prop)
    (preprocessedModel : Prop) (originalModel : Prop) :=
  ay_cscg_Sat preprocessedCnf preprocessedModel ->
    ay_cscg_Sat originalCnf originalModel

def ay_cscg_UnsatProofReconstructionWitness
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_cscg_Replay preprocessedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_cscg_ReconstructionWitnesses
    (preprocessedCnf : Prop) (originalCnf : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_cscg_Conj
    (ay_cscg_ModelReconstructionWitness
      preprocessedCnf originalCnf preprocessedModel originalModel)
    (ay_cscg_UnsatProofReconstructionWitness
      originalCnf preprocessedCnf certificate conflict)

def ay_cscg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_cscg_Conj baselineSolver baselineAvailable

def ay_cscg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_cscg_Conj binaryFingerprint buildReproducible

def ay_cscg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_cscg_Conj validatorAccepted validatorVersion

def ay_cscg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_cscg_Conj auditAppended auditAppendOnly

def ay_cscg_AcceptedClauseSignatureCollisionGuard
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (databaseDigest : Prop) (databaseDigestAccepted : Prop)
    (databaseManifest : Prop)
    (cacheDigest : Prop) (cacheDigestAccepted : Prop)
    (cacheManifest : Prop)
    (candidatePairLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop)
    (exactComparisonWitness : Prop) (exactComparisonAccepted : Prop)
    (exactComparisonCoverage : Prop)
    (collisionDiagnosticLedger : Prop) (collisionAccepted : Prop)
    (collisionCoverage : Prop)
    (deletionStrengtheningLedger : Prop) (ledgerAccepted : Prop)
    (ledgerCoverage : Prop)
    (checkerReplayCertificate : Prop) (checkerAccepted : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_cscg_FormulaDigest
       formulaDigest formulaDigestAccepted formulaManifest ->
     ay_cscg_ClauseDatabaseDigest
       databaseDigest databaseDigestAccepted databaseManifest ->
     ay_cscg_SignatureCacheDigest
       cacheDigest cacheDigestAccepted cacheManifest ->
     ay_cscg_CandidatePairLedger
       candidatePairLedger candidateAccepted candidateCoverage ->
     ay_cscg_ExactClauseComparisonWitness
       exactComparisonWitness exactComparisonAccepted exactComparisonCoverage ->
     ay_cscg_CollisionDiagnosticLedger
       collisionDiagnosticLedger collisionAccepted collisionCoverage ->
     ay_cscg_DeletionStrengtheningLedger
       deletionStrengtheningLedger ledgerAccepted ledgerCoverage ->
     ay_cscg_CheckerReplay checkerReplayCertificate checkerAccepted ->
     ay_cscg_ReconstructionWitnesses
       preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict ->
     ay_cscg_Equisat originalCnf preprocessedCnf ->
     ay_cscg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_cscg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_cscg_ValidatorGate validatorAccepted validatorVersion ->
     ay_cscg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_cscg_ClauseSignatureCollisionGuardFailure
    (collisionMismatch : Prop) (candidateMismatch : Prop)
    (exactComparisonMismatch : Prop) (ledgerMismatch : Prop)
    (reconstructionMismatch : Prop) (checkerMismatch : Prop)
    (baselineMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (collisionMismatch -> result) ->
    (candidateMismatch -> result) ->
    (exactComparisonMismatch -> result) ->
    (ledgerMismatch -> result) ->
    (reconstructionMismatch -> result) ->
    (checkerMismatch -> result) ->
    (baselineMismatch -> result) ->
    (buildMismatch -> result) ->
    (validatorMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_cscg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_cscg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_cscg_Conj currentCnf recompute

def ay_cscg_DiagnosticClauseSignatureCollisionGuard
    (currentCnf : Prop)
    (collisionMismatch : Prop) (candidateMismatch : Prop)
    (exactComparisonMismatch : Prop) (ledgerMismatch : Prop)
    (reconstructionMismatch : Prop) (checkerMismatch : Prop)
    (baselineMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_cscg_Conj
    (ay_cscg_ClauseSignatureCollisionGuardFailure
      collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch)
    (ay_cscg_Conj
      (ay_cscg_RecomputeObligation currentCnf recompute)
      (ay_cscg_NoSemanticClaim diagnostic))

def ay_cscg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_cscg_Conj exitCode claim

def ay_cscg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_cscg_Disj
    (ay_cscg_ExitCodeSound exitCode (ay_cscg_Sat originalCnf model))
    (ay_cscg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_cscg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_cscg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_cscg_conj_left
    (left : Prop) (right : Prop) :
    ay_cscg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_cscg_conj_right
    (left : Prop) (right : Prop) :
    ay_cscg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_cscg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_cscg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_cscg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_cscg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_cscg_equisat_forward
    (original : Prop) (preprocessed : Prop) :
    ay_cscg_Equisat original preprocessed -> original -> preprocessed := by
  intro eqsat
  exact ay_cscg_conj_left (original -> preprocessed) (preprocessed -> original) eqsat

theorem ay_cscg_equisat_backward
    (original : Prop) (preprocessed : Prop) :
    ay_cscg_Equisat original preprocessed -> preprocessed -> original := by
  intro eqsat
  exact ay_cscg_conj_right (original -> preprocessed) (preprocessed -> original) eqsat

theorem ay_cscg_candidate_pair_ledger_applies
    (candidatePairLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop) :
    ay_cscg_CandidatePairLedger
      candidatePairLedger candidateAccepted candidateCoverage ->
    candidatePairLedger -> candidateAccepted := by
  intro ledger
  exact ay_cscg_conj_right
    candidateCoverage (candidatePairLedger -> candidateAccepted) ledger

theorem ay_cscg_exact_clause_comparison_applies
    (exactComparisonWitness : Prop) (exactComparisonAccepted : Prop)
    (exactComparisonCoverage : Prop) :
    ay_cscg_ExactClauseComparisonWitness
      exactComparisonWitness exactComparisonAccepted exactComparisonCoverage ->
    exactComparisonWitness -> exactComparisonAccepted := by
  intro witness
  exact ay_cscg_conj_right
    exactComparisonCoverage
    (exactComparisonWitness -> exactComparisonAccepted)
    witness

theorem ay_cscg_collision_diagnostic_applies
    (collisionDiagnosticLedger : Prop) (collisionAccepted : Prop)
    (collisionCoverage : Prop) :
    ay_cscg_CollisionDiagnosticLedger
      collisionDiagnosticLedger collisionAccepted collisionCoverage ->
    collisionDiagnosticLedger -> collisionAccepted := by
  intro ledger
  exact ay_cscg_conj_right
    collisionCoverage (collisionDiagnosticLedger -> collisionAccepted) ledger

theorem ay_cscg_deletion_strengthening_ledger_applies
    (deletionStrengtheningLedger : Prop) (ledgerAccepted : Prop)
    (ledgerCoverage : Prop) :
    ay_cscg_DeletionStrengtheningLedger
      deletionStrengtheningLedger ledgerAccepted ledgerCoverage ->
    deletionStrengtheningLedger -> ledgerAccepted := by
  intro ledger
  exact ay_cscg_conj_right
    ledgerCoverage (deletionStrengtheningLedger -> ledgerAccepted) ledger

theorem ay_cscg_checker_replay_certificate
    (checkerReplayCertificate : Prop) (checkerAccepted : Prop) :
    ay_cscg_CheckerReplay checkerReplayCertificate checkerAccepted ->
    checkerReplayCertificate := by
  intro replay
  exact ay_cscg_conj_left checkerReplayCertificate checkerAccepted replay

theorem ay_cscg_model_reconstruction
    (preprocessedCnf : Prop) (originalCnf : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_cscg_ReconstructionWitnesses
      preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict ->
    ay_cscg_Sat preprocessedCnf preprocessedModel ->
    ay_cscg_Sat originalCnf originalModel := by
  intro witnesses
  exact ay_cscg_conj_left
    (ay_cscg_ModelReconstructionWitness
      preprocessedCnf originalCnf preprocessedModel originalModel)
    (ay_cscg_UnsatProofReconstructionWitness
      originalCnf preprocessedCnf certificate conflict)
    witnesses

theorem ay_cscg_unsat_proof_reconstruction
    (preprocessedCnf : Prop) (originalCnf : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_cscg_ReconstructionWitnesses
      preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict ->
    ay_cscg_Replay preprocessedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses
  exact ay_cscg_conj_right
    (ay_cscg_ModelReconstructionWitness
      preprocessedCnf originalCnf preprocessedModel originalModel)
    (ay_cscg_UnsatProofReconstructionWitness
      originalCnf preprocessedCnf certificate conflict)
    witnesses

theorem ay_cscg_accepted_equisat
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (databaseDigest : Prop) (databaseDigestAccepted : Prop)
    (databaseManifest : Prop)
    (cacheDigest : Prop) (cacheDigestAccepted : Prop)
    (cacheManifest : Prop)
    (candidatePairLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop)
    (exactComparisonWitness : Prop) (exactComparisonAccepted : Prop)
    (exactComparisonCoverage : Prop)
    (collisionDiagnosticLedger : Prop) (collisionAccepted : Prop)
    (collisionCoverage : Prop)
    (deletionStrengtheningLedger : Prop) (ledgerAccepted : Prop)
    (ledgerCoverage : Prop)
    (checkerReplayCertificate : Prop) (checkerAccepted : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_cscg_AcceptedClauseSignatureCollisionGuard
      originalCnf preprocessedCnf
      formulaDigest formulaDigestAccepted formulaManifest
      databaseDigest databaseDigestAccepted databaseManifest
      cacheDigest cacheDigestAccepted cacheManifest
      candidatePairLedger candidateAccepted candidateCoverage
      exactComparisonWitness exactComparisonAccepted exactComparisonCoverage
      collisionDiagnosticLedger collisionAccepted collisionCoverage
      deletionStrengtheningLedger ledgerAccepted ledgerCoverage
      checkerReplayCertificate checkerAccepted
      preprocessedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_cscg_Equisat originalCnf preprocessedCnf := by
  intro accepted
  exact accepted (ay_cscg_Equisat originalCnf preprocessedCnf)
    (fun _formula _database _cache _candidate _exact _collision _ledger
      _checker _reconstruct eqsat _fallback _build _validator _audit => eqsat)

theorem ay_cscg_accepted_reconstruction
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (databaseDigest : Prop) (databaseDigestAccepted : Prop)
    (databaseManifest : Prop)
    (cacheDigest : Prop) (cacheDigestAccepted : Prop)
    (cacheManifest : Prop)
    (candidatePairLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop)
    (exactComparisonWitness : Prop) (exactComparisonAccepted : Prop)
    (exactComparisonCoverage : Prop)
    (collisionDiagnosticLedger : Prop) (collisionAccepted : Prop)
    (collisionCoverage : Prop)
    (deletionStrengtheningLedger : Prop) (ledgerAccepted : Prop)
    (ledgerCoverage : Prop)
    (checkerReplayCertificate : Prop) (checkerAccepted : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_cscg_AcceptedClauseSignatureCollisionGuard
      originalCnf preprocessedCnf
      formulaDigest formulaDigestAccepted formulaManifest
      databaseDigest databaseDigestAccepted databaseManifest
      cacheDigest cacheDigestAccepted cacheManifest
      candidatePairLedger candidateAccepted candidateCoverage
      exactComparisonWitness exactComparisonAccepted exactComparisonCoverage
      collisionDiagnosticLedger collisionAccepted collisionCoverage
      deletionStrengtheningLedger ledgerAccepted ledgerCoverage
      checkerReplayCertificate checkerAccepted
      preprocessedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_cscg_ReconstructionWitnesses
      preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict := by
  intro accepted
  exact accepted
    (ay_cscg_ReconstructionWitnesses
      preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict)
    (fun _formula _database _cache _candidate _exact _collision _ledger
      _checker reconstruct _eqsat _fallback _build _validator _audit =>
      reconstruct)

theorem ay_cscg_collision_requires_exact_evidence
    (exactComparisonWitness : Prop) (exactComparisonAccepted : Prop)
    (exactComparisonCoverage : Prop)
    (deletionStrengtheningLedger : Prop) (ledgerAccepted : Prop)
    (ledgerCoverage : Prop) :
    ay_cscg_ExactClauseComparisonWitness
      exactComparisonWitness exactComparisonAccepted exactComparisonCoverage ->
    ay_cscg_DeletionStrengtheningLedger
      deletionStrengtheningLedger ledgerAccepted ledgerCoverage ->
    exactComparisonWitness -> deletionStrengtheningLedger ->
    ay_cscg_Conj exactComparisonAccepted ledgerAccepted := by
  intro exactOk ledgerOk exactWitness ledger
  exact ay_cscg_conj_intro exactComparisonAccepted ledgerAccepted
    (ay_cscg_exact_clause_comparison_applies
      exactComparisonWitness exactComparisonAccepted exactComparisonCoverage
      exactOk exactWitness)
    (ay_cscg_deletion_strengthening_ledger_applies
      deletionStrengtheningLedger ledgerAccepted ledgerCoverage ledgerOk ledger)

theorem ay_cscg_sat_pullback
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_cscg_ReconstructionWitnesses
      preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict ->
    ay_cscg_Sat preprocessedCnf preprocessedModel ->
    ay_cscg_Sat originalCnf originalModel := by
  intro witnesses satPreprocessed
  exact ay_cscg_model_reconstruction
    preprocessedCnf originalCnf preprocessedModel originalModel
    certificate conflict witnesses satPreprocessed

theorem ay_cscg_unsat_pushback
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_cscg_ReconstructionWitnesses
      preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict ->
    ay_cscg_Replay preprocessedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses replay
  exact ay_cscg_unsat_proof_reconstruction
    preprocessedCnf originalCnf preprocessedModel originalModel
    certificate conflict witnesses replay

theorem ay_cscg_public_sat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_cscg_ExitCodeSound exitCode (ay_cscg_Sat originalCnf originalModel) ->
    ay_cscg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro satSound
  exact ay_cscg_disj_left
    (ay_cscg_ExitCodeSound exitCode (ay_cscg_Sat originalCnf originalModel))
    (ay_cscg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    satSound

theorem ay_cscg_public_unsat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_cscg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_cscg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro unsatSound
  exact ay_cscg_disj_right
    (ay_cscg_ExitCodeSound exitCode (ay_cscg_Sat originalCnf originalModel))
    (ay_cscg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    unsatSound

theorem ay_cscg_failure_collision
    (collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    collisionMismatch ->
    ay_cscg_ClauseSignatureCollisionGuardFailure
      collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result collision_case _candidate_case _exact_case _ledger_case
    _reconstruction_case _checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact collision_case h

theorem ay_cscg_failure_candidate
    (collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    candidateMismatch ->
    ay_cscg_ClauseSignatureCollisionGuardFailure
      collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _collision_case candidate_case _exact_case _ledger_case
    _reconstruction_case _checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact candidate_case h

theorem ay_cscg_failure_exact_comparison
    (collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    exactComparisonMismatch ->
    ay_cscg_ClauseSignatureCollisionGuardFailure
      collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _collision_case _candidate_case exact_case _ledger_case
    _reconstruction_case _checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact exact_case h

theorem ay_cscg_failure_ledger
    (collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    ledgerMismatch ->
    ay_cscg_ClauseSignatureCollisionGuardFailure
      collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _collision_case _candidate_case _exact_case ledger_case
    _reconstruction_case _checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact ledger_case h

theorem ay_cscg_failure_reconstruction
    (collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    reconstructionMismatch ->
    ay_cscg_ClauseSignatureCollisionGuardFailure
      collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _collision_case _candidate_case _exact_case _ledger_case
    reconstruction_case _checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case h

theorem ay_cscg_failure_checker
    (collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    checkerMismatch ->
    ay_cscg_ClauseSignatureCollisionGuardFailure
      collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _collision_case _candidate_case _exact_case _ledger_case
    _reconstruction_case checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact checker_case h

theorem ay_cscg_failure_baseline
    (collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    baselineMismatch ->
    ay_cscg_ClauseSignatureCollisionGuardFailure
      collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _collision_case _candidate_case _exact_case _ledger_case
    _reconstruction_case _checker_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case h

theorem ay_cscg_failure_build
    (collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    buildMismatch ->
    ay_cscg_ClauseSignatureCollisionGuardFailure
      collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _collision_case _candidate_case _exact_case _ledger_case
    _reconstruction_case _checker_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case h

theorem ay_cscg_failure_validator
    (collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    validatorMismatch ->
    ay_cscg_ClauseSignatureCollisionGuardFailure
      collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _collision_case _candidate_case _exact_case _ledger_case
    _reconstruction_case _checker_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case h

theorem ay_cscg_failure_audit
    (collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    auditMismatch ->
    ay_cscg_ClauseSignatureCollisionGuardFailure
      collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _collision_case _candidate_case _exact_case _ledger_case
    _reconstruction_case _checker_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case h

theorem ay_cscg_diagnostic_no_claim
    (currentCnf : Prop)
    (collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_cscg_DiagnosticClauseSignatureCollisionGuard
      currentCnf collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_cscg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard
  exact ay_cscg_conj_right
    (ay_cscg_RecomputeObligation currentCnf recompute)
    (ay_cscg_NoSemanticClaim diagnostic)
    (ay_cscg_conj_right
      (ay_cscg_ClauseSignatureCollisionGuardFailure
        collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch
        reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
        validatorMismatch auditMismatch)
      (ay_cscg_Conj
        (ay_cscg_RecomputeObligation currentCnf recompute)
        (ay_cscg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_cscg_diagnostic_recompute
    (currentCnf : Prop)
    (collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_cscg_DiagnosticClauseSignatureCollisionGuard
      currentCnf collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_cscg_RecomputeObligation currentCnf recompute := by
  intro diagnosticGuard
  exact ay_cscg_conj_left
    (ay_cscg_RecomputeObligation currentCnf recompute)
    (ay_cscg_NoSemanticClaim diagnostic)
    (ay_cscg_conj_right
      (ay_cscg_ClauseSignatureCollisionGuardFailure
        collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch
        reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
        validatorMismatch auditMismatch)
      (ay_cscg_Conj
        (ay_cscg_RecomputeObligation currentCnf recompute)
        (ay_cscg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_cscg_failed_guard_cannot_bless_public_result
    (currentCnf : Prop)
    (collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_cscg_DiagnosticClauseSignatureCollisionGuard
      currentCnf collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_cscg_PublicResult originalCnf model certificate conflict exitCode ->
    ay_cscg_Conj
      (ay_cscg_NoSemanticClaim diagnostic)
      (ay_cscg_RecomputeObligation currentCnf recompute) := by
  intro diagnosticGuard _publicResult
  exact ay_cscg_conj_intro
    (ay_cscg_NoSemanticClaim diagnostic)
    (ay_cscg_RecomputeObligation currentCnf recompute)
    (ay_cscg_diagnostic_no_claim
      currentCnf collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic diagnosticGuard)
    (ay_cscg_diagnostic_recompute
      currentCnf collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic diagnosticGuard)

theorem ay_cscg_failed_guard_cannot_bless_public_sat
    (currentCnf : Prop)
    (collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop) (exitCode : Prop) :
    ay_cscg_DiagnosticClauseSignatureCollisionGuard
      currentCnf collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_cscg_ExitCodeSound exitCode (ay_cscg_Sat originalCnf model) ->
    ay_cscg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _satClaim
  exact ay_cscg_diagnostic_no_claim
    currentCnf collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch
    reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
    validatorMismatch auditMismatch recompute diagnostic diagnosticGuard

theorem ay_cscg_failed_guard_cannot_bless_public_unsat
    (currentCnf : Prop)
    (collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (certificate : Prop) (conflict : Prop)
    (exitCode : Prop) :
    ay_cscg_DiagnosticClauseSignatureCollisionGuard
      currentCnf collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_cscg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_cscg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _unsatClaim
  exact ay_cscg_diagnostic_no_claim
    currentCnf collisionMismatch candidateMismatch exactComparisonMismatch ledgerMismatch
    reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
    validatorMismatch auditMismatch recompute diagnostic diagnosticGuard
