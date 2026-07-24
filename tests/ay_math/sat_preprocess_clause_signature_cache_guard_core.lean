-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Clause-signature cache guard soundness.
-- The propositions stand for formula/database/cache digests, signature
-- recomputation witnesses, subsumption candidate ledgers, deletion/
-- strengthening ledgers, checker replay, reconstruction witnesses, fallback/
-- build/validator gates, audit transcripts, diagnostics, and public results.

def ay_csig_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_csig_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_csig_Equisat (original : Prop) (accelerated : Prop) :=
  ay_csig_Conj (original -> accelerated) (accelerated -> original)

def ay_csig_Sat (cnf : Prop) (model : Prop) :=
  ay_csig_Conj cnf model

def ay_csig_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_csig_FormulaDigest
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop) :=
  ay_csig_Conj formulaManifest (formulaDigest -> formulaDigestAccepted)

def ay_csig_ClauseDatabaseDigest
    (clauseDatabaseDigest : Prop) (databaseDigestAccepted : Prop)
    (databaseManifest : Prop) :=
  ay_csig_Conj databaseManifest
    (clauseDatabaseDigest -> databaseDigestAccepted)

def ay_csig_ClauseSignatureCacheDigest
    (cacheDigest : Prop) (cacheDigestAccepted : Prop)
    (cacheManifest : Prop) :=
  ay_csig_Conj cacheManifest (cacheDigest -> cacheDigestAccepted)

def ay_csig_SignatureRecomputationWitness
    (recomputationWitness : Prop) (recomputationAccepted : Prop)
    (recomputationCoverage : Prop) :=
  ay_csig_Conj recomputationCoverage
    (recomputationWitness -> recomputationAccepted)

def ay_csig_SubsumptionCandidateLedger
    (candidateLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop) :=
  ay_csig_Conj candidateCoverage (candidateLedger -> candidateAccepted)

def ay_csig_DeletionStrengtheningLedger
    (deletionStrengtheningLedger : Prop) (ledgerAccepted : Prop)
    (ledgerCoverage : Prop) :=
  ay_csig_Conj ledgerCoverage
    (deletionStrengtheningLedger -> ledgerAccepted)

def ay_csig_CheckerReplay
    (checkerReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_csig_Conj checkerReplayCertificate checkerAccepted

def ay_csig_ModelReconstructionWitness
    (acceleratedCnf : Prop) (originalCnf : Prop)
    (acceleratedModel : Prop) (originalModel : Prop) :=
  ay_csig_Sat acceleratedCnf acceleratedModel ->
    ay_csig_Sat originalCnf originalModel

def ay_csig_UnsatProofReconstructionWitness
    (originalCnf : Prop) (acceleratedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_csig_Replay acceleratedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_csig_ReconstructionWitnesses
    (acceleratedCnf : Prop) (originalCnf : Prop)
    (acceleratedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_csig_Conj
    (ay_csig_ModelReconstructionWitness
      acceleratedCnf originalCnf acceleratedModel originalModel)
    (ay_csig_UnsatProofReconstructionWitness
      originalCnf acceleratedCnf certificate conflict)

def ay_csig_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_csig_Conj baselineSolver baselineAvailable

def ay_csig_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_csig_Conj binaryFingerprint buildReproducible

def ay_csig_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_csig_Conj validatorAccepted validatorVersion

def ay_csig_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_csig_Conj auditAppended auditAppendOnly

def ay_csig_AcceptedClauseSignatureCacheGuard
    (originalCnf : Prop) (acceleratedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (clauseDatabaseDigest : Prop) (databaseDigestAccepted : Prop)
    (databaseManifest : Prop)
    (cacheDigest : Prop) (cacheDigestAccepted : Prop)
    (cacheManifest : Prop)
    (recomputationWitness : Prop) (recomputationAccepted : Prop)
    (recomputationCoverage : Prop)
    (candidateLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop)
    (deletionStrengtheningLedger : Prop) (ledgerAccepted : Prop)
    (ledgerCoverage : Prop)
    (checkerReplayCertificate : Prop) (checkerAccepted : Prop)
    (acceleratedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_csig_FormulaDigest
       formulaDigest formulaDigestAccepted formulaManifest ->
     ay_csig_ClauseDatabaseDigest
       clauseDatabaseDigest databaseDigestAccepted databaseManifest ->
     ay_csig_ClauseSignatureCacheDigest
       cacheDigest cacheDigestAccepted cacheManifest ->
     ay_csig_SignatureRecomputationWitness
       recomputationWitness recomputationAccepted recomputationCoverage ->
     ay_csig_SubsumptionCandidateLedger
       candidateLedger candidateAccepted candidateCoverage ->
     ay_csig_DeletionStrengtheningLedger
       deletionStrengtheningLedger ledgerAccepted ledgerCoverage ->
     ay_csig_CheckerReplay checkerReplayCertificate checkerAccepted ->
     ay_csig_ReconstructionWitnesses
       acceleratedCnf originalCnf acceleratedModel originalModel certificate conflict ->
     ay_csig_Equisat originalCnf acceleratedCnf ->
     ay_csig_FallbackBaseline baselineSolver baselineAvailable ->
     ay_csig_BuildEvidence binaryFingerprint buildReproducible ->
     ay_csig_ValidatorGate validatorAccepted validatorVersion ->
     ay_csig_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_csig_ClauseSignatureCacheGuardFailure
    (cacheMismatch : Prop) (recomputationMismatch : Prop)
    (candidateMismatch : Prop) (ledgerMismatch : Prop)
    (reconstructionMismatch : Prop) (checkerMismatch : Prop)
    (baselineMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (cacheMismatch -> result) ->
    (recomputationMismatch -> result) ->
    (candidateMismatch -> result) ->
    (ledgerMismatch -> result) ->
    (reconstructionMismatch -> result) ->
    (checkerMismatch -> result) ->
    (baselineMismatch -> result) ->
    (buildMismatch -> result) ->
    (validatorMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_csig_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_csig_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_csig_Conj currentCnf recompute

def ay_csig_DiagnosticClauseSignatureCacheGuard
    (currentCnf : Prop)
    (cacheMismatch : Prop) (recomputationMismatch : Prop)
    (candidateMismatch : Prop) (ledgerMismatch : Prop)
    (reconstructionMismatch : Prop) (checkerMismatch : Prop)
    (baselineMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_csig_Conj
    (ay_csig_ClauseSignatureCacheGuardFailure
      cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch)
    (ay_csig_Conj
      (ay_csig_RecomputeObligation currentCnf recompute)
      (ay_csig_NoSemanticClaim diagnostic))

def ay_csig_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_csig_Conj exitCode claim

def ay_csig_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_csig_Disj
    (ay_csig_ExitCodeSound exitCode (ay_csig_Sat originalCnf model))
    (ay_csig_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_csig_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_csig_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_csig_conj_left
    (left : Prop) (right : Prop) :
    ay_csig_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_csig_conj_right
    (left : Prop) (right : Prop) :
    ay_csig_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_csig_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_csig_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_csig_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_csig_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_csig_equisat_forward
    (original : Prop) (accelerated : Prop) :
    ay_csig_Equisat original accelerated -> original -> accelerated := by
  intro eqsat
  exact ay_csig_conj_left (original -> accelerated) (accelerated -> original) eqsat

theorem ay_csig_equisat_backward
    (original : Prop) (accelerated : Prop) :
    ay_csig_Equisat original accelerated -> accelerated -> original := by
  intro eqsat
  exact ay_csig_conj_right (original -> accelerated) (accelerated -> original) eqsat

theorem ay_csig_cache_digest_applies
    (cacheDigest : Prop) (cacheDigestAccepted : Prop)
    (cacheManifest : Prop) :
    ay_csig_ClauseSignatureCacheDigest
      cacheDigest cacheDigestAccepted cacheManifest ->
    cacheDigest -> cacheDigestAccepted := by
  intro digest
  exact ay_csig_conj_right
    cacheManifest (cacheDigest -> cacheDigestAccepted) digest

theorem ay_csig_signature_recomputation_applies
    (recomputationWitness : Prop) (recomputationAccepted : Prop)
    (recomputationCoverage : Prop) :
    ay_csig_SignatureRecomputationWitness
      recomputationWitness recomputationAccepted recomputationCoverage ->
    recomputationWitness -> recomputationAccepted := by
  intro witness
  exact ay_csig_conj_right
    recomputationCoverage (recomputationWitness -> recomputationAccepted) witness

theorem ay_csig_subsumption_candidate_ledger_applies
    (candidateLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop) :
    ay_csig_SubsumptionCandidateLedger
      candidateLedger candidateAccepted candidateCoverage ->
    candidateLedger -> candidateAccepted := by
  intro ledger
  exact ay_csig_conj_right
    candidateCoverage (candidateLedger -> candidateAccepted) ledger

theorem ay_csig_deletion_strengthening_ledger_applies
    (deletionStrengtheningLedger : Prop) (ledgerAccepted : Prop)
    (ledgerCoverage : Prop) :
    ay_csig_DeletionStrengtheningLedger
      deletionStrengtheningLedger ledgerAccepted ledgerCoverage ->
    deletionStrengtheningLedger -> ledgerAccepted := by
  intro ledger
  exact ay_csig_conj_right
    ledgerCoverage (deletionStrengtheningLedger -> ledgerAccepted) ledger

theorem ay_csig_checker_replay_certificate
    (checkerReplayCertificate : Prop) (checkerAccepted : Prop) :
    ay_csig_CheckerReplay checkerReplayCertificate checkerAccepted ->
    checkerReplayCertificate := by
  intro replay
  exact ay_csig_conj_left checkerReplayCertificate checkerAccepted replay

theorem ay_csig_model_reconstruction
    (acceleratedCnf : Prop) (originalCnf : Prop)
    (acceleratedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_csig_ReconstructionWitnesses
      acceleratedCnf originalCnf acceleratedModel originalModel certificate conflict ->
    ay_csig_Sat acceleratedCnf acceleratedModel ->
    ay_csig_Sat originalCnf originalModel := by
  intro witnesses
  exact ay_csig_conj_left
    (ay_csig_ModelReconstructionWitness
      acceleratedCnf originalCnf acceleratedModel originalModel)
    (ay_csig_UnsatProofReconstructionWitness
      originalCnf acceleratedCnf certificate conflict)
    witnesses

theorem ay_csig_unsat_proof_reconstruction
    (acceleratedCnf : Prop) (originalCnf : Prop)
    (acceleratedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_csig_ReconstructionWitnesses
      acceleratedCnf originalCnf acceleratedModel originalModel certificate conflict ->
    ay_csig_Replay acceleratedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses
  exact ay_csig_conj_right
    (ay_csig_ModelReconstructionWitness
      acceleratedCnf originalCnf acceleratedModel originalModel)
    (ay_csig_UnsatProofReconstructionWitness
      originalCnf acceleratedCnf certificate conflict)
    witnesses

theorem ay_csig_accepted_equisat
    (originalCnf : Prop) (acceleratedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (clauseDatabaseDigest : Prop) (databaseDigestAccepted : Prop)
    (databaseManifest : Prop)
    (cacheDigest : Prop) (cacheDigestAccepted : Prop)
    (cacheManifest : Prop)
    (recomputationWitness : Prop) (recomputationAccepted : Prop)
    (recomputationCoverage : Prop)
    (candidateLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop)
    (deletionStrengtheningLedger : Prop) (ledgerAccepted : Prop)
    (ledgerCoverage : Prop)
    (checkerReplayCertificate : Prop) (checkerAccepted : Prop)
    (acceleratedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_csig_AcceptedClauseSignatureCacheGuard
      originalCnf acceleratedCnf
      formulaDigest formulaDigestAccepted formulaManifest
      clauseDatabaseDigest databaseDigestAccepted databaseManifest
      cacheDigest cacheDigestAccepted cacheManifest
      recomputationWitness recomputationAccepted recomputationCoverage
      candidateLedger candidateAccepted candidateCoverage
      deletionStrengtheningLedger ledgerAccepted ledgerCoverage
      checkerReplayCertificate checkerAccepted
      acceleratedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_csig_Equisat originalCnf acceleratedCnf := by
  intro accepted
  exact accepted (ay_csig_Equisat originalCnf acceleratedCnf)
    (fun _formula _database _cache _recompute _candidate _ledger _checker
      _reconstruct eqsat _fallback _build _validator _audit => eqsat)

theorem ay_csig_accepted_reconstruction
    (originalCnf : Prop) (acceleratedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (clauseDatabaseDigest : Prop) (databaseDigestAccepted : Prop)
    (databaseManifest : Prop)
    (cacheDigest : Prop) (cacheDigestAccepted : Prop)
    (cacheManifest : Prop)
    (recomputationWitness : Prop) (recomputationAccepted : Prop)
    (recomputationCoverage : Prop)
    (candidateLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop)
    (deletionStrengtheningLedger : Prop) (ledgerAccepted : Prop)
    (ledgerCoverage : Prop)
    (checkerReplayCertificate : Prop) (checkerAccepted : Prop)
    (acceleratedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_csig_AcceptedClauseSignatureCacheGuard
      originalCnf acceleratedCnf
      formulaDigest formulaDigestAccepted formulaManifest
      clauseDatabaseDigest databaseDigestAccepted databaseManifest
      cacheDigest cacheDigestAccepted cacheManifest
      recomputationWitness recomputationAccepted recomputationCoverage
      candidateLedger candidateAccepted candidateCoverage
      deletionStrengtheningLedger ledgerAccepted ledgerCoverage
      checkerReplayCertificate checkerAccepted
      acceleratedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_csig_ReconstructionWitnesses
      acceleratedCnf originalCnf acceleratedModel originalModel certificate conflict := by
  intro accepted
  exact accepted
    (ay_csig_ReconstructionWitnesses
      acceleratedCnf originalCnf acceleratedModel originalModel certificate conflict)
    (fun _formula _database _cache _recompute _candidate _ledger _checker
      reconstruct _eqsat _fallback _build _validator _audit => reconstruct)

theorem ay_csig_cache_is_acceleration_only
    (originalCnf : Prop) (acceleratedCnf : Prop) :
    ay_csig_Equisat originalCnf acceleratedCnf ->
    originalCnf -> acceleratedCnf := by
  intro eqsat
  exact ay_csig_equisat_forward originalCnf acceleratedCnf eqsat

theorem ay_csig_sat_pullback
    (originalCnf : Prop) (acceleratedCnf : Prop)
    (acceleratedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_csig_ReconstructionWitnesses
      acceleratedCnf originalCnf acceleratedModel originalModel certificate conflict ->
    ay_csig_Sat acceleratedCnf acceleratedModel ->
    ay_csig_Sat originalCnf originalModel := by
  intro witnesses satAccelerated
  exact ay_csig_model_reconstruction
    acceleratedCnf originalCnf acceleratedModel originalModel
    certificate conflict witnesses satAccelerated

theorem ay_csig_unsat_pushback
    (originalCnf : Prop) (acceleratedCnf : Prop)
    (acceleratedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_csig_ReconstructionWitnesses
      acceleratedCnf originalCnf acceleratedModel originalModel certificate conflict ->
    ay_csig_Replay acceleratedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses replay
  exact ay_csig_unsat_proof_reconstruction
    acceleratedCnf originalCnf acceleratedModel originalModel
    certificate conflict witnesses replay

theorem ay_csig_public_sat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_csig_ExitCodeSound exitCode (ay_csig_Sat originalCnf originalModel) ->
    ay_csig_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro satSound
  exact ay_csig_disj_left
    (ay_csig_ExitCodeSound exitCode (ay_csig_Sat originalCnf originalModel))
    (ay_csig_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    satSound

theorem ay_csig_public_unsat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_csig_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_csig_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro unsatSound
  exact ay_csig_disj_right
    (ay_csig_ExitCodeSound exitCode (ay_csig_Sat originalCnf originalModel))
    (ay_csig_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    unsatSound

theorem ay_csig_failure_cache
    (cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    cacheMismatch ->
    ay_csig_ClauseSignatureCacheGuardFailure
      cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result cache_case _recompute_case _candidate_case _ledger_case
    _reconstruction_case _checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact cache_case h

theorem ay_csig_failure_recomputation
    (cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    recomputationMismatch ->
    ay_csig_ClauseSignatureCacheGuardFailure
      cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _cache_case recompute_case _candidate_case _ledger_case
    _reconstruction_case _checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact recompute_case h

theorem ay_csig_failure_candidate
    (cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    candidateMismatch ->
    ay_csig_ClauseSignatureCacheGuardFailure
      cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _cache_case _recompute_case candidate_case _ledger_case
    _reconstruction_case _checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact candidate_case h

theorem ay_csig_failure_ledger
    (cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    ledgerMismatch ->
    ay_csig_ClauseSignatureCacheGuardFailure
      cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _cache_case _recompute_case _candidate_case ledger_case
    _reconstruction_case _checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact ledger_case h

theorem ay_csig_failure_reconstruction
    (cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    reconstructionMismatch ->
    ay_csig_ClauseSignatureCacheGuardFailure
      cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _cache_case _recompute_case _candidate_case _ledger_case
    reconstruction_case _checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case h

theorem ay_csig_failure_checker
    (cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    checkerMismatch ->
    ay_csig_ClauseSignatureCacheGuardFailure
      cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _cache_case _recompute_case _candidate_case _ledger_case
    _reconstruction_case checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact checker_case h

theorem ay_csig_failure_baseline
    (cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    baselineMismatch ->
    ay_csig_ClauseSignatureCacheGuardFailure
      cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _cache_case _recompute_case _candidate_case _ledger_case
    _reconstruction_case _checker_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case h

theorem ay_csig_failure_build
    (cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    buildMismatch ->
    ay_csig_ClauseSignatureCacheGuardFailure
      cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _cache_case _recompute_case _candidate_case _ledger_case
    _reconstruction_case _checker_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case h

theorem ay_csig_failure_validator
    (cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    validatorMismatch ->
    ay_csig_ClauseSignatureCacheGuardFailure
      cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _cache_case _recompute_case _candidate_case _ledger_case
    _reconstruction_case _checker_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case h

theorem ay_csig_failure_audit
    (cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    auditMismatch ->
    ay_csig_ClauseSignatureCacheGuardFailure
      cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _cache_case _recompute_case _candidate_case _ledger_case
    _reconstruction_case _checker_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case h

theorem ay_csig_diagnostic_no_claim
    (currentCnf : Prop)
    (cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_csig_DiagnosticClauseSignatureCacheGuard
      currentCnf cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_csig_NoSemanticClaim diagnostic := by
  intro diagnosticGuard
  exact ay_csig_conj_right
    (ay_csig_RecomputeObligation currentCnf recompute)
    (ay_csig_NoSemanticClaim diagnostic)
    (ay_csig_conj_right
      (ay_csig_ClauseSignatureCacheGuardFailure
        cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch
        reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
        validatorMismatch auditMismatch)
      (ay_csig_Conj
        (ay_csig_RecomputeObligation currentCnf recompute)
        (ay_csig_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_csig_diagnostic_recompute
    (currentCnf : Prop)
    (cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_csig_DiagnosticClauseSignatureCacheGuard
      currentCnf cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_csig_RecomputeObligation currentCnf recompute := by
  intro diagnosticGuard
  exact ay_csig_conj_left
    (ay_csig_RecomputeObligation currentCnf recompute)
    (ay_csig_NoSemanticClaim diagnostic)
    (ay_csig_conj_right
      (ay_csig_ClauseSignatureCacheGuardFailure
        cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch
        reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
        validatorMismatch auditMismatch)
      (ay_csig_Conj
        (ay_csig_RecomputeObligation currentCnf recompute)
        (ay_csig_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_csig_failed_guard_cannot_bless_public_result
    (currentCnf : Prop)
    (cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_csig_DiagnosticClauseSignatureCacheGuard
      currentCnf cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_csig_PublicResult originalCnf model certificate conflict exitCode ->
    ay_csig_Conj
      (ay_csig_NoSemanticClaim diagnostic)
      (ay_csig_RecomputeObligation currentCnf recompute) := by
  intro diagnosticGuard _publicResult
  exact ay_csig_conj_intro
    (ay_csig_NoSemanticClaim diagnostic)
    (ay_csig_RecomputeObligation currentCnf recompute)
    (ay_csig_diagnostic_no_claim
      currentCnf cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic diagnosticGuard)
    (ay_csig_diagnostic_recompute
      currentCnf cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic diagnosticGuard)

theorem ay_csig_failed_guard_cannot_bless_public_sat
    (currentCnf : Prop)
    (cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop) (exitCode : Prop) :
    ay_csig_DiagnosticClauseSignatureCacheGuard
      currentCnf cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_csig_ExitCodeSound exitCode (ay_csig_Sat originalCnf model) ->
    ay_csig_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _satClaim
  exact ay_csig_diagnostic_no_claim
    currentCnf cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch
    reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
    validatorMismatch auditMismatch recompute diagnostic diagnosticGuard

theorem ay_csig_failed_guard_cannot_bless_public_unsat
    (currentCnf : Prop)
    (cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (certificate : Prop) (conflict : Prop)
    (exitCode : Prop) :
    ay_csig_DiagnosticClauseSignatureCacheGuard
      currentCnf cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_csig_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_csig_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _unsatClaim
  exact ay_csig_diagnostic_no_claim
    currentCnf cacheMismatch recomputationMismatch candidateMismatch ledgerMismatch
    reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
    validatorMismatch auditMismatch recompute diagnostic diagnosticGuard
