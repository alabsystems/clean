-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Binary-clause subsumption preprocessing guard soundness.
-- The propositions stand for formula digests, binary clause ledgers,
-- subsumption candidate ledgers, exact subsumption witnesses, deletion/
-- strengthening ledgers, checker replay, reconstruction witnesses, fallback/
-- build/validator gates, audit transcripts, diagnostics, and public results.

def ay_bsg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bsg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_bsg_Equisat (original : Prop) (preprocessed : Prop) :=
  ay_bsg_Conj (original -> preprocessed) (preprocessed -> original)

def ay_bsg_Sat (cnf : Prop) (model : Prop) :=
  ay_bsg_Conj cnf model

def ay_bsg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_bsg_FormulaDigest
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop) :=
  ay_bsg_Conj formulaManifest (formulaDigest -> formulaDigestAccepted)

def ay_bsg_BinaryClauseLedger
    (binaryClauseLedger : Prop) (binaryAccepted : Prop)
    (binaryCoverage : Prop) :=
  ay_bsg_Conj binaryCoverage (binaryClauseLedger -> binaryAccepted)

def ay_bsg_SubsumptionCandidateLedger
    (candidateLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop) :=
  ay_bsg_Conj candidateCoverage (candidateLedger -> candidateAccepted)

def ay_bsg_ExactSubsumptionWitness
    (exactSubsumptionWitness : Prop) (exactAccepted : Prop)
    (exactCoverage : Prop) :=
  ay_bsg_Conj exactCoverage (exactSubsumptionWitness -> exactAccepted)

def ay_bsg_DeletionStrengtheningLedger
    (deletionStrengtheningLedger : Prop) (ledgerAccepted : Prop)
    (ledgerCoverage : Prop) :=
  ay_bsg_Conj ledgerCoverage
    (deletionStrengtheningLedger -> ledgerAccepted)

def ay_bsg_CheckerReplay
    (checkerReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_bsg_Conj checkerReplayCertificate checkerAccepted

def ay_bsg_ModelReconstructionWitness
    (preprocessedCnf : Prop) (originalCnf : Prop)
    (preprocessedModel : Prop) (originalModel : Prop) :=
  ay_bsg_Sat preprocessedCnf preprocessedModel ->
    ay_bsg_Sat originalCnf originalModel

def ay_bsg_UnsatProofReconstructionWitness
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_bsg_Replay preprocessedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_bsg_ReconstructionWitnesses
    (preprocessedCnf : Prop) (originalCnf : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_bsg_Conj
    (ay_bsg_ModelReconstructionWitness
      preprocessedCnf originalCnf preprocessedModel originalModel)
    (ay_bsg_UnsatProofReconstructionWitness
      originalCnf preprocessedCnf certificate conflict)

def ay_bsg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_bsg_Conj baselineSolver baselineAvailable

def ay_bsg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_bsg_Conj binaryFingerprint buildReproducible

def ay_bsg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_bsg_Conj validatorAccepted validatorVersion

def ay_bsg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_bsg_Conj auditAppended auditAppendOnly

def ay_bsg_AcceptedBinarySubsumptionGuard
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (binaryClauseLedger : Prop) (binaryAccepted : Prop)
    (binaryCoverage : Prop)
    (candidateLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop)
    (exactSubsumptionWitness : Prop) (exactAccepted : Prop)
    (exactCoverage : Prop)
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
    (ay_bsg_FormulaDigest
       formulaDigest formulaDigestAccepted formulaManifest ->
     ay_bsg_BinaryClauseLedger
       binaryClauseLedger binaryAccepted binaryCoverage ->
     ay_bsg_SubsumptionCandidateLedger
       candidateLedger candidateAccepted candidateCoverage ->
     ay_bsg_ExactSubsumptionWitness
       exactSubsumptionWitness exactAccepted exactCoverage ->
     ay_bsg_DeletionStrengtheningLedger
       deletionStrengtheningLedger ledgerAccepted ledgerCoverage ->
     ay_bsg_CheckerReplay checkerReplayCertificate checkerAccepted ->
     ay_bsg_ReconstructionWitnesses
       preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict ->
     ay_bsg_Equisat originalCnf preprocessedCnf ->
     ay_bsg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_bsg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_bsg_ValidatorGate validatorAccepted validatorVersion ->
     ay_bsg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_bsg_BinarySubsumptionGuardFailure
    (binaryMismatch : Prop) (candidateMismatch : Prop)
    (exactMismatch : Prop) (deletionMismatch : Prop)
    (reconstructionMismatch : Prop) (checkerMismatch : Prop)
    (baselineMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (binaryMismatch -> result) ->
    (candidateMismatch -> result) ->
    (exactMismatch -> result) ->
    (deletionMismatch -> result) ->
    (reconstructionMismatch -> result) ->
    (checkerMismatch -> result) ->
    (baselineMismatch -> result) ->
    (buildMismatch -> result) ->
    (validatorMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_bsg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_bsg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_bsg_Conj currentCnf recompute

def ay_bsg_DiagnosticBinarySubsumptionGuard
    (currentCnf : Prop)
    (binaryMismatch : Prop) (candidateMismatch : Prop)
    (exactMismatch : Prop) (deletionMismatch : Prop)
    (reconstructionMismatch : Prop) (checkerMismatch : Prop)
    (baselineMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_bsg_Conj
    (ay_bsg_BinarySubsumptionGuardFailure
      binaryMismatch candidateMismatch exactMismatch deletionMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch)
    (ay_bsg_Conj
      (ay_bsg_RecomputeObligation currentCnf recompute)
      (ay_bsg_NoSemanticClaim diagnostic))

def ay_bsg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_bsg_Conj exitCode claim

def ay_bsg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_bsg_Disj
    (ay_bsg_ExitCodeSound exitCode (ay_bsg_Sat originalCnf model))
    (ay_bsg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_bsg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_bsg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_bsg_conj_left
    (left : Prop) (right : Prop) :
    ay_bsg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_bsg_conj_right
    (left : Prop) (right : Prop) :
    ay_bsg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_bsg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_bsg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_bsg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_bsg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_bsg_equisat_forward
    (original : Prop) (preprocessed : Prop) :
    ay_bsg_Equisat original preprocessed -> original -> preprocessed := by
  intro eqsat
  exact ay_bsg_conj_left (original -> preprocessed) (preprocessed -> original) eqsat

theorem ay_bsg_equisat_backward
    (original : Prop) (preprocessed : Prop) :
    ay_bsg_Equisat original preprocessed -> preprocessed -> original := by
  intro eqsat
  exact ay_bsg_conj_right (original -> preprocessed) (preprocessed -> original) eqsat

theorem ay_bsg_binary_clause_ledger_applies
    (binaryClauseLedger : Prop) (binaryAccepted : Prop)
    (binaryCoverage : Prop) :
    ay_bsg_BinaryClauseLedger
      binaryClauseLedger binaryAccepted binaryCoverage ->
    binaryClauseLedger -> binaryAccepted := by
  intro ledger
  exact ay_bsg_conj_right
    binaryCoverage (binaryClauseLedger -> binaryAccepted) ledger

theorem ay_bsg_subsumption_candidate_ledger_applies
    (candidateLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop) :
    ay_bsg_SubsumptionCandidateLedger
      candidateLedger candidateAccepted candidateCoverage ->
    candidateLedger -> candidateAccepted := by
  intro ledger
  exact ay_bsg_conj_right
    candidateCoverage (candidateLedger -> candidateAccepted) ledger

theorem ay_bsg_exact_subsumption_witness_applies
    (exactSubsumptionWitness : Prop) (exactAccepted : Prop)
    (exactCoverage : Prop) :
    ay_bsg_ExactSubsumptionWitness
      exactSubsumptionWitness exactAccepted exactCoverage ->
    exactSubsumptionWitness -> exactAccepted := by
  intro witness
  exact ay_bsg_conj_right
    exactCoverage (exactSubsumptionWitness -> exactAccepted) witness

theorem ay_bsg_deletion_strengthening_ledger_applies
    (deletionStrengtheningLedger : Prop) (ledgerAccepted : Prop)
    (ledgerCoverage : Prop) :
    ay_bsg_DeletionStrengtheningLedger
      deletionStrengtheningLedger ledgerAccepted ledgerCoverage ->
    deletionStrengtheningLedger -> ledgerAccepted := by
  intro ledger
  exact ay_bsg_conj_right
    ledgerCoverage (deletionStrengtheningLedger -> ledgerAccepted) ledger

theorem ay_bsg_checker_replay_certificate
    (checkerReplayCertificate : Prop) (checkerAccepted : Prop) :
    ay_bsg_CheckerReplay checkerReplayCertificate checkerAccepted ->
    checkerReplayCertificate := by
  intro replay
  exact ay_bsg_conj_left checkerReplayCertificate checkerAccepted replay

theorem ay_bsg_model_reconstruction
    (preprocessedCnf : Prop) (originalCnf : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_bsg_ReconstructionWitnesses
      preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict ->
    ay_bsg_Sat preprocessedCnf preprocessedModel ->
    ay_bsg_Sat originalCnf originalModel := by
  intro witnesses
  exact ay_bsg_conj_left
    (ay_bsg_ModelReconstructionWitness
      preprocessedCnf originalCnf preprocessedModel originalModel)
    (ay_bsg_UnsatProofReconstructionWitness
      originalCnf preprocessedCnf certificate conflict)
    witnesses

theorem ay_bsg_unsat_proof_reconstruction
    (preprocessedCnf : Prop) (originalCnf : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_bsg_ReconstructionWitnesses
      preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict ->
    ay_bsg_Replay preprocessedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses
  exact ay_bsg_conj_right
    (ay_bsg_ModelReconstructionWitness
      preprocessedCnf originalCnf preprocessedModel originalModel)
    (ay_bsg_UnsatProofReconstructionWitness
      originalCnf preprocessedCnf certificate conflict)
    witnesses

theorem ay_bsg_accepted_equisat
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (binaryClauseLedger : Prop) (binaryAccepted : Prop)
    (binaryCoverage : Prop)
    (candidateLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop)
    (exactSubsumptionWitness : Prop) (exactAccepted : Prop)
    (exactCoverage : Prop)
    (deletionStrengtheningLedger : Prop) (ledgerAccepted : Prop)
    (ledgerCoverage : Prop)
    (checkerReplayCertificate : Prop) (checkerAccepted : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_bsg_AcceptedBinarySubsumptionGuard
      originalCnf preprocessedCnf
      formulaDigest formulaDigestAccepted formulaManifest
      binaryClauseLedger binaryAccepted binaryCoverage
      candidateLedger candidateAccepted candidateCoverage
      exactSubsumptionWitness exactAccepted exactCoverage
      deletionStrengtheningLedger ledgerAccepted ledgerCoverage
      checkerReplayCertificate checkerAccepted
      preprocessedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_bsg_Equisat originalCnf preprocessedCnf := by
  intro accepted
  exact accepted (ay_bsg_Equisat originalCnf preprocessedCnf)
    (fun _formula _binary _candidate _exact _ledger _checker _reconstruct
      eqsat _fallback _build _validator _audit => eqsat)

theorem ay_bsg_accepted_reconstruction
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (binaryClauseLedger : Prop) (binaryAccepted : Prop)
    (binaryCoverage : Prop)
    (candidateLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop)
    (exactSubsumptionWitness : Prop) (exactAccepted : Prop)
    (exactCoverage : Prop)
    (deletionStrengtheningLedger : Prop) (ledgerAccepted : Prop)
    (ledgerCoverage : Prop)
    (checkerReplayCertificate : Prop) (checkerAccepted : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_bsg_AcceptedBinarySubsumptionGuard
      originalCnf preprocessedCnf
      formulaDigest formulaDigestAccepted formulaManifest
      binaryClauseLedger binaryAccepted binaryCoverage
      candidateLedger candidateAccepted candidateCoverage
      exactSubsumptionWitness exactAccepted exactCoverage
      deletionStrengtheningLedger ledgerAccepted ledgerCoverage
      checkerReplayCertificate checkerAccepted
      preprocessedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_bsg_ReconstructionWitnesses
      preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict := by
  intro accepted
  exact accepted
    (ay_bsg_ReconstructionWitnesses
      preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict)
    (fun _formula _binary _candidate _exact _ledger _checker reconstruct
      _eqsat _fallback _build _validator _audit => reconstruct)

theorem ay_bsg_binary_subsumption_requires_exact_evidence
    (exactSubsumptionWitness : Prop) (exactAccepted : Prop)
    (exactCoverage : Prop)
    (deletionStrengtheningLedger : Prop) (ledgerAccepted : Prop)
    (ledgerCoverage : Prop) :
    ay_bsg_ExactSubsumptionWitness
      exactSubsumptionWitness exactAccepted exactCoverage ->
    ay_bsg_DeletionStrengtheningLedger
      deletionStrengtheningLedger ledgerAccepted ledgerCoverage ->
    exactSubsumptionWitness -> deletionStrengtheningLedger ->
    ay_bsg_Conj exactAccepted ledgerAccepted := by
  intro exactOk ledgerOk exactWitness ledger
  exact ay_bsg_conj_intro exactAccepted ledgerAccepted
    (ay_bsg_exact_subsumption_witness_applies
      exactSubsumptionWitness exactAccepted exactCoverage exactOk exactWitness)
    (ay_bsg_deletion_strengthening_ledger_applies
      deletionStrengtheningLedger ledgerAccepted ledgerCoverage ledgerOk ledger)

theorem ay_bsg_sat_pullback
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_bsg_ReconstructionWitnesses
      preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict ->
    ay_bsg_Sat preprocessedCnf preprocessedModel ->
    ay_bsg_Sat originalCnf originalModel := by
  intro witnesses satPreprocessed
  exact ay_bsg_model_reconstruction
    preprocessedCnf originalCnf preprocessedModel originalModel
    certificate conflict witnesses satPreprocessed

theorem ay_bsg_unsat_pushback
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_bsg_ReconstructionWitnesses
      preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict ->
    ay_bsg_Replay preprocessedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses replay
  exact ay_bsg_unsat_proof_reconstruction
    preprocessedCnf originalCnf preprocessedModel originalModel
    certificate conflict witnesses replay

theorem ay_bsg_public_sat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_bsg_ExitCodeSound exitCode (ay_bsg_Sat originalCnf originalModel) ->
    ay_bsg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro satSound
  exact ay_bsg_disj_left
    (ay_bsg_ExitCodeSound exitCode (ay_bsg_Sat originalCnf originalModel))
    (ay_bsg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    satSound

theorem ay_bsg_public_unsat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_bsg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_bsg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro unsatSound
  exact ay_bsg_disj_right
    (ay_bsg_ExitCodeSound exitCode (ay_bsg_Sat originalCnf originalModel))
    (ay_bsg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    unsatSound

theorem ay_bsg_failure_binary
    (binaryMismatch candidateMismatch exactMismatch deletionMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    binaryMismatch ->
    ay_bsg_BinarySubsumptionGuardFailure
      binaryMismatch candidateMismatch exactMismatch deletionMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result binary_case _candidate_case _exact_case _deletion_case
    _reconstruction_case _checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact binary_case h

theorem ay_bsg_failure_candidate
    (binaryMismatch candidateMismatch exactMismatch deletionMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    candidateMismatch ->
    ay_bsg_BinarySubsumptionGuardFailure
      binaryMismatch candidateMismatch exactMismatch deletionMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _binary_case candidate_case _exact_case _deletion_case
    _reconstruction_case _checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact candidate_case h

theorem ay_bsg_failure_exact
    (binaryMismatch candidateMismatch exactMismatch deletionMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    exactMismatch ->
    ay_bsg_BinarySubsumptionGuardFailure
      binaryMismatch candidateMismatch exactMismatch deletionMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _binary_case _candidate_case exact_case _deletion_case
    _reconstruction_case _checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact exact_case h

theorem ay_bsg_failure_deletion
    (binaryMismatch candidateMismatch exactMismatch deletionMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    deletionMismatch ->
    ay_bsg_BinarySubsumptionGuardFailure
      binaryMismatch candidateMismatch exactMismatch deletionMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _binary_case _candidate_case _exact_case deletion_case
    _reconstruction_case _checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact deletion_case h

theorem ay_bsg_failure_reconstruction
    (binaryMismatch candidateMismatch exactMismatch deletionMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    reconstructionMismatch ->
    ay_bsg_BinarySubsumptionGuardFailure
      binaryMismatch candidateMismatch exactMismatch deletionMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _binary_case _candidate_case _exact_case _deletion_case
    reconstruction_case _checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case h

theorem ay_bsg_failure_checker
    (binaryMismatch candidateMismatch exactMismatch deletionMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    checkerMismatch ->
    ay_bsg_BinarySubsumptionGuardFailure
      binaryMismatch candidateMismatch exactMismatch deletionMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _binary_case _candidate_case _exact_case _deletion_case
    _reconstruction_case checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact checker_case h

theorem ay_bsg_failure_baseline
    (binaryMismatch candidateMismatch exactMismatch deletionMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    baselineMismatch ->
    ay_bsg_BinarySubsumptionGuardFailure
      binaryMismatch candidateMismatch exactMismatch deletionMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _binary_case _candidate_case _exact_case _deletion_case
    _reconstruction_case _checker_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case h

theorem ay_bsg_failure_build
    (binaryMismatch candidateMismatch exactMismatch deletionMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    buildMismatch ->
    ay_bsg_BinarySubsumptionGuardFailure
      binaryMismatch candidateMismatch exactMismatch deletionMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _binary_case _candidate_case _exact_case _deletion_case
    _reconstruction_case _checker_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case h

theorem ay_bsg_failure_validator
    (binaryMismatch candidateMismatch exactMismatch deletionMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    validatorMismatch ->
    ay_bsg_BinarySubsumptionGuardFailure
      binaryMismatch candidateMismatch exactMismatch deletionMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _binary_case _candidate_case _exact_case _deletion_case
    _reconstruction_case _checker_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case h

theorem ay_bsg_failure_audit
    (binaryMismatch candidateMismatch exactMismatch deletionMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    auditMismatch ->
    ay_bsg_BinarySubsumptionGuardFailure
      binaryMismatch candidateMismatch exactMismatch deletionMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _binary_case _candidate_case _exact_case _deletion_case
    _reconstruction_case _checker_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case h

theorem ay_bsg_diagnostic_no_claim
    (currentCnf : Prop)
    (binaryMismatch candidateMismatch exactMismatch deletionMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_bsg_DiagnosticBinarySubsumptionGuard
      currentCnf binaryMismatch candidateMismatch exactMismatch deletionMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_bsg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard
  exact ay_bsg_conj_right
    (ay_bsg_RecomputeObligation currentCnf recompute)
    (ay_bsg_NoSemanticClaim diagnostic)
    (ay_bsg_conj_right
      (ay_bsg_BinarySubsumptionGuardFailure
        binaryMismatch candidateMismatch exactMismatch deletionMismatch
        reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
        validatorMismatch auditMismatch)
      (ay_bsg_Conj
        (ay_bsg_RecomputeObligation currentCnf recompute)
        (ay_bsg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_bsg_diagnostic_recompute
    (currentCnf : Prop)
    (binaryMismatch candidateMismatch exactMismatch deletionMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_bsg_DiagnosticBinarySubsumptionGuard
      currentCnf binaryMismatch candidateMismatch exactMismatch deletionMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_bsg_RecomputeObligation currentCnf recompute := by
  intro diagnosticGuard
  exact ay_bsg_conj_left
    (ay_bsg_RecomputeObligation currentCnf recompute)
    (ay_bsg_NoSemanticClaim diagnostic)
    (ay_bsg_conj_right
      (ay_bsg_BinarySubsumptionGuardFailure
        binaryMismatch candidateMismatch exactMismatch deletionMismatch
        reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
        validatorMismatch auditMismatch)
      (ay_bsg_Conj
        (ay_bsg_RecomputeObligation currentCnf recompute)
        (ay_bsg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_bsg_failed_guard_cannot_bless_public_result
    (currentCnf : Prop)
    (binaryMismatch candidateMismatch exactMismatch deletionMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_bsg_DiagnosticBinarySubsumptionGuard
      currentCnf binaryMismatch candidateMismatch exactMismatch deletionMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_bsg_PublicResult originalCnf model certificate conflict exitCode ->
    ay_bsg_Conj
      (ay_bsg_NoSemanticClaim diagnostic)
      (ay_bsg_RecomputeObligation currentCnf recompute) := by
  intro diagnosticGuard _publicResult
  exact ay_bsg_conj_intro
    (ay_bsg_NoSemanticClaim diagnostic)
    (ay_bsg_RecomputeObligation currentCnf recompute)
    (ay_bsg_diagnostic_no_claim
      currentCnf binaryMismatch candidateMismatch exactMismatch deletionMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic diagnosticGuard)
    (ay_bsg_diagnostic_recompute
      currentCnf binaryMismatch candidateMismatch exactMismatch deletionMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic diagnosticGuard)

theorem ay_bsg_failed_guard_cannot_bless_public_sat
    (currentCnf : Prop)
    (binaryMismatch candidateMismatch exactMismatch deletionMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop) (exitCode : Prop) :
    ay_bsg_DiagnosticBinarySubsumptionGuard
      currentCnf binaryMismatch candidateMismatch exactMismatch deletionMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_bsg_ExitCodeSound exitCode (ay_bsg_Sat originalCnf model) ->
    ay_bsg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _satClaim
  exact ay_bsg_diagnostic_no_claim
    currentCnf binaryMismatch candidateMismatch exactMismatch deletionMismatch
    reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
    validatorMismatch auditMismatch recompute diagnostic diagnosticGuard

theorem ay_bsg_failed_guard_cannot_bless_public_unsat
    (currentCnf : Prop)
    (binaryMismatch candidateMismatch exactMismatch deletionMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (certificate : Prop) (conflict : Prop)
    (exitCode : Prop) :
    ay_bsg_DiagnosticBinarySubsumptionGuard
      currentCnf binaryMismatch candidateMismatch exactMismatch deletionMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_bsg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_bsg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _unsatClaim
  exact ay_bsg_diagnostic_no_claim
    currentCnf binaryMismatch candidateMismatch exactMismatch deletionMismatch
    reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
    validatorMismatch auditMismatch recompute diagnostic diagnosticGuard
