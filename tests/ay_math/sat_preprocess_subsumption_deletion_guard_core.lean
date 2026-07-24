-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Subsumption-deletion preprocessing guard soundness.
-- The propositions stand for original/preprocessed formula digests,
-- subsumption-pair ledgers, deleted-clause ledgers, redundancy witnesses,
-- checker replay, model/proof reconstruction, fallback/build/validator gates,
-- audit transcripts, diagnostics, and public SAT/UNSAT reports.

def ay_sdg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_sdg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_sdg_Equisat (original : Prop) (preprocessed : Prop) :=
  ay_sdg_Conj (original -> preprocessed) (preprocessed -> original)

def ay_sdg_Sat (cnf : Prop) (model : Prop) :=
  ay_sdg_Conj cnf model

def ay_sdg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_sdg_OriginalFormulaDigest
    (originalDigest : Prop) (originalDigestAccepted : Prop)
    (originalManifest : Prop) :=
  ay_sdg_Conj originalManifest (originalDigest -> originalDigestAccepted)

def ay_sdg_PreprocessedFormulaDigest
    (preprocessedDigest : Prop) (preprocessedDigestAccepted : Prop)
    (preprocessedManifest : Prop) :=
  ay_sdg_Conj preprocessedManifest
    (preprocessedDigest -> preprocessedDigestAccepted)

def ay_sdg_SubsumptionPairLedger
    (pairLedger : Prop) (pairAccepted : Prop) (pairCoverage : Prop) :=
  ay_sdg_Conj pairCoverage (pairLedger -> pairAccepted)

def ay_sdg_DeletedClauseLedger
    (deletedClauseLedger : Prop) (deletionAccepted : Prop)
    (deletionCoverage : Prop) :=
  ay_sdg_Conj deletionCoverage (deletedClauseLedger -> deletionAccepted)

def ay_sdg_RedundancyWitness
    (redundancyWitness : Prop) (redundancyAccepted : Prop)
    (redundancyCoverage : Prop) :=
  ay_sdg_Conj redundancyCoverage
    (redundancyWitness -> redundancyAccepted)

def ay_sdg_CheckerReplay
    (checkerReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_sdg_Conj checkerReplayCertificate checkerAccepted

def ay_sdg_ModelReconstructionWitness
    (preprocessedCnf : Prop) (originalCnf : Prop)
    (preprocessedModel : Prop) (originalModel : Prop) :=
  ay_sdg_Sat preprocessedCnf preprocessedModel ->
    ay_sdg_Sat originalCnf originalModel

def ay_sdg_UnsatProofReconstructionWitness
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_sdg_Replay preprocessedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_sdg_ReconstructionWitnesses
    (preprocessedCnf : Prop) (originalCnf : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_sdg_Conj
    (ay_sdg_ModelReconstructionWitness
      preprocessedCnf originalCnf preprocessedModel originalModel)
    (ay_sdg_UnsatProofReconstructionWitness
      originalCnf preprocessedCnf certificate conflict)

def ay_sdg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_sdg_Conj baselineSolver baselineAvailable

def ay_sdg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_sdg_Conj binaryFingerprint buildReproducible

def ay_sdg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_sdg_Conj validatorAccepted validatorVersion

def ay_sdg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_sdg_Conj auditAppended auditAppendOnly

def ay_sdg_AcceptedSubsumptionDeletionGuard
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (originalDigest : Prop) (originalDigestAccepted : Prop)
    (originalManifest : Prop)
    (preprocessedDigest : Prop) (preprocessedDigestAccepted : Prop)
    (preprocessedManifest : Prop)
    (pairLedger : Prop) (pairAccepted : Prop) (pairCoverage : Prop)
    (deletedClauseLedger : Prop) (deletionAccepted : Prop)
    (deletionCoverage : Prop)
    (redundancyWitness : Prop) (redundancyAccepted : Prop)
    (redundancyCoverage : Prop)
    (checkerReplayCertificate : Prop) (checkerAccepted : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_sdg_OriginalFormulaDigest
       originalDigest originalDigestAccepted originalManifest ->
     ay_sdg_PreprocessedFormulaDigest
       preprocessedDigest preprocessedDigestAccepted preprocessedManifest ->
     ay_sdg_SubsumptionPairLedger pairLedger pairAccepted pairCoverage ->
     ay_sdg_DeletedClauseLedger
       deletedClauseLedger deletionAccepted deletionCoverage ->
     ay_sdg_RedundancyWitness
       redundancyWitness redundancyAccepted redundancyCoverage ->
     ay_sdg_CheckerReplay checkerReplayCertificate checkerAccepted ->
     ay_sdg_ReconstructionWitnesses
       preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict ->
     ay_sdg_Equisat originalCnf preprocessedCnf ->
     ay_sdg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_sdg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_sdg_ValidatorGate validatorAccepted validatorVersion ->
     ay_sdg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_sdg_SubsumptionDeletionGuardFailure
    (digestMismatch : Prop) (pairMismatch : Prop)
    (deletionMismatch : Prop) (redundancyMismatch : Prop)
    (reconstructionMismatch : Prop) (checkerMismatch : Prop)
    (baselineMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (digestMismatch -> result) ->
    (pairMismatch -> result) ->
    (deletionMismatch -> result) ->
    (redundancyMismatch -> result) ->
    (reconstructionMismatch -> result) ->
    (checkerMismatch -> result) ->
    (baselineMismatch -> result) ->
    (buildMismatch -> result) ->
    (validatorMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_sdg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_sdg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_sdg_Conj currentCnf recompute

def ay_sdg_DiagnosticSubsumptionDeletionGuard
    (currentCnf : Prop)
    (digestMismatch : Prop) (pairMismatch : Prop)
    (deletionMismatch : Prop) (redundancyMismatch : Prop)
    (reconstructionMismatch : Prop) (checkerMismatch : Prop)
    (baselineMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_sdg_Conj
    (ay_sdg_SubsumptionDeletionGuardFailure
      digestMismatch pairMismatch deletionMismatch redundancyMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch)
    (ay_sdg_Conj
      (ay_sdg_RecomputeObligation currentCnf recompute)
      (ay_sdg_NoSemanticClaim diagnostic))

def ay_sdg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_sdg_Conj exitCode claim

def ay_sdg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_sdg_Disj
    (ay_sdg_ExitCodeSound exitCode (ay_sdg_Sat originalCnf model))
    (ay_sdg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_sdg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_sdg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_sdg_conj_left
    (left : Prop) (right : Prop) :
    ay_sdg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_sdg_conj_right
    (left : Prop) (right : Prop) :
    ay_sdg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_sdg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_sdg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_sdg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_sdg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_sdg_equisat_forward
    (original : Prop) (preprocessed : Prop) :
    ay_sdg_Equisat original preprocessed -> original -> preprocessed := by
  intro eqsat
  exact ay_sdg_conj_left (original -> preprocessed) (preprocessed -> original) eqsat

theorem ay_sdg_equisat_backward
    (original : Prop) (preprocessed : Prop) :
    ay_sdg_Equisat original preprocessed -> preprocessed -> original := by
  intro eqsat
  exact ay_sdg_conj_right (original -> preprocessed) (preprocessed -> original) eqsat

theorem ay_sdg_original_formula_digest_applies
    (originalDigest : Prop) (originalDigestAccepted : Prop)
    (originalManifest : Prop) :
    ay_sdg_OriginalFormulaDigest
      originalDigest originalDigestAccepted originalManifest ->
    originalDigest -> originalDigestAccepted := by
  intro digest
  exact ay_sdg_conj_right
    originalManifest (originalDigest -> originalDigestAccepted) digest

theorem ay_sdg_preprocessed_formula_digest_applies
    (preprocessedDigest : Prop) (preprocessedDigestAccepted : Prop)
    (preprocessedManifest : Prop) :
    ay_sdg_PreprocessedFormulaDigest
      preprocessedDigest preprocessedDigestAccepted preprocessedManifest ->
    preprocessedDigest -> preprocessedDigestAccepted := by
  intro digest
  exact ay_sdg_conj_right
    preprocessedManifest
    (preprocessedDigest -> preprocessedDigestAccepted)
    digest

theorem ay_sdg_subsumption_pair_ledger_applies
    (pairLedger : Prop) (pairAccepted : Prop) (pairCoverage : Prop) :
    ay_sdg_SubsumptionPairLedger pairLedger pairAccepted pairCoverage ->
    pairLedger -> pairAccepted := by
  intro ledger
  exact ay_sdg_conj_right pairCoverage (pairLedger -> pairAccepted) ledger

theorem ay_sdg_deleted_clause_ledger_applies
    (deletedClauseLedger : Prop) (deletionAccepted : Prop)
    (deletionCoverage : Prop) :
    ay_sdg_DeletedClauseLedger
      deletedClauseLedger deletionAccepted deletionCoverage ->
    deletedClauseLedger -> deletionAccepted := by
  intro ledger
  exact ay_sdg_conj_right
    deletionCoverage (deletedClauseLedger -> deletionAccepted) ledger

theorem ay_sdg_redundancy_witness_applies
    (redundancyWitness : Prop) (redundancyAccepted : Prop)
    (redundancyCoverage : Prop) :
    ay_sdg_RedundancyWitness
      redundancyWitness redundancyAccepted redundancyCoverage ->
    redundancyWitness -> redundancyAccepted := by
  intro witness
  exact ay_sdg_conj_right
    redundancyCoverage (redundancyWitness -> redundancyAccepted) witness

theorem ay_sdg_checker_replay_certificate
    (checkerReplayCertificate : Prop) (checkerAccepted : Prop) :
    ay_sdg_CheckerReplay checkerReplayCertificate checkerAccepted ->
    checkerReplayCertificate := by
  intro replay
  exact ay_sdg_conj_left checkerReplayCertificate checkerAccepted replay

theorem ay_sdg_model_reconstruction
    (preprocessedCnf : Prop) (originalCnf : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_sdg_ReconstructionWitnesses
      preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict ->
    ay_sdg_Sat preprocessedCnf preprocessedModel ->
    ay_sdg_Sat originalCnf originalModel := by
  intro witnesses
  exact ay_sdg_conj_left
    (ay_sdg_ModelReconstructionWitness
      preprocessedCnf originalCnf preprocessedModel originalModel)
    (ay_sdg_UnsatProofReconstructionWitness
      originalCnf preprocessedCnf certificate conflict)
    witnesses

theorem ay_sdg_unsat_proof_reconstruction
    (preprocessedCnf : Prop) (originalCnf : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_sdg_ReconstructionWitnesses
      preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict ->
    ay_sdg_Replay preprocessedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses
  exact ay_sdg_conj_right
    (ay_sdg_ModelReconstructionWitness
      preprocessedCnf originalCnf preprocessedModel originalModel)
    (ay_sdg_UnsatProofReconstructionWitness
      originalCnf preprocessedCnf certificate conflict)
    witnesses

theorem ay_sdg_accepted_equisat
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (originalDigest : Prop) (originalDigestAccepted : Prop)
    (originalManifest : Prop)
    (preprocessedDigest : Prop) (preprocessedDigestAccepted : Prop)
    (preprocessedManifest : Prop)
    (pairLedger : Prop) (pairAccepted : Prop) (pairCoverage : Prop)
    (deletedClauseLedger : Prop) (deletionAccepted : Prop)
    (deletionCoverage : Prop)
    (redundancyWitness : Prop) (redundancyAccepted : Prop)
    (redundancyCoverage : Prop)
    (checkerReplayCertificate : Prop) (checkerAccepted : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_sdg_AcceptedSubsumptionDeletionGuard
      originalCnf preprocessedCnf
      originalDigest originalDigestAccepted originalManifest
      preprocessedDigest preprocessedDigestAccepted preprocessedManifest
      pairLedger pairAccepted pairCoverage
      deletedClauseLedger deletionAccepted deletionCoverage
      redundancyWitness redundancyAccepted redundancyCoverage
      checkerReplayCertificate checkerAccepted
      preprocessedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_sdg_Equisat originalCnf preprocessedCnf := by
  intro accepted
  exact accepted (ay_sdg_Equisat originalCnf preprocessedCnf)
    (fun _origDigest _prepDigest _pairs _deletions _redundancy _checker
      _reconstruct eqsat _fallback _build _validator _audit => eqsat)

theorem ay_sdg_accepted_reconstruction
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (originalDigest : Prop) (originalDigestAccepted : Prop)
    (originalManifest : Prop)
    (preprocessedDigest : Prop) (preprocessedDigestAccepted : Prop)
    (preprocessedManifest : Prop)
    (pairLedger : Prop) (pairAccepted : Prop) (pairCoverage : Prop)
    (deletedClauseLedger : Prop) (deletionAccepted : Prop)
    (deletionCoverage : Prop)
    (redundancyWitness : Prop) (redundancyAccepted : Prop)
    (redundancyCoverage : Prop)
    (checkerReplayCertificate : Prop) (checkerAccepted : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_sdg_AcceptedSubsumptionDeletionGuard
      originalCnf preprocessedCnf
      originalDigest originalDigestAccepted originalManifest
      preprocessedDigest preprocessedDigestAccepted preprocessedManifest
      pairLedger pairAccepted pairCoverage
      deletedClauseLedger deletionAccepted deletionCoverage
      redundancyWitness redundancyAccepted redundancyCoverage
      checkerReplayCertificate checkerAccepted
      preprocessedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_sdg_ReconstructionWitnesses
      preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict := by
  intro accepted
  exact accepted
    (ay_sdg_ReconstructionWitnesses
      preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict)
    (fun _origDigest _prepDigest _pairs _deletions _redundancy _checker
      reconstruct _eqsat _fallback _build _validator _audit => reconstruct)

theorem ay_sdg_sat_pullback
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_sdg_ReconstructionWitnesses
      preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict ->
    ay_sdg_Sat preprocessedCnf preprocessedModel ->
    ay_sdg_Sat originalCnf originalModel := by
  intro witnesses satPreprocessed
  exact ay_sdg_model_reconstruction
    preprocessedCnf originalCnf preprocessedModel originalModel
    certificate conflict witnesses satPreprocessed

theorem ay_sdg_unsat_pushback
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_sdg_ReconstructionWitnesses
      preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict ->
    ay_sdg_Replay preprocessedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses replay
  exact ay_sdg_unsat_proof_reconstruction
    preprocessedCnf originalCnf preprocessedModel originalModel
    certificate conflict witnesses replay

theorem ay_sdg_public_sat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_sdg_ExitCodeSound exitCode (ay_sdg_Sat originalCnf originalModel) ->
    ay_sdg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro satSound
  exact ay_sdg_disj_left
    (ay_sdg_ExitCodeSound exitCode (ay_sdg_Sat originalCnf originalModel))
    (ay_sdg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    satSound

theorem ay_sdg_public_unsat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_sdg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_sdg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro unsatSound
  exact ay_sdg_disj_right
    (ay_sdg_ExitCodeSound exitCode (ay_sdg_Sat originalCnf originalModel))
    (ay_sdg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    unsatSound

theorem ay_sdg_failure_digest
    (digestMismatch pairMismatch deletionMismatch redundancyMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    digestMismatch ->
    ay_sdg_SubsumptionDeletionGuardFailure
      digestMismatch pairMismatch deletionMismatch redundancyMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result digest_case _pair_case _deletion_case _redundancy_case
    _reconstruction_case _checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact digest_case h

theorem ay_sdg_failure_pair
    (digestMismatch pairMismatch deletionMismatch redundancyMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    pairMismatch ->
    ay_sdg_SubsumptionDeletionGuardFailure
      digestMismatch pairMismatch deletionMismatch redundancyMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case pair_case _deletion_case _redundancy_case
    _reconstruction_case _checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact pair_case h

theorem ay_sdg_failure_deletion
    (digestMismatch pairMismatch deletionMismatch redundancyMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    deletionMismatch ->
    ay_sdg_SubsumptionDeletionGuardFailure
      digestMismatch pairMismatch deletionMismatch redundancyMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _pair_case deletion_case _redundancy_case
    _reconstruction_case _checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact deletion_case h

theorem ay_sdg_failure_redundancy
    (digestMismatch pairMismatch deletionMismatch redundancyMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    redundancyMismatch ->
    ay_sdg_SubsumptionDeletionGuardFailure
      digestMismatch pairMismatch deletionMismatch redundancyMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _pair_case _deletion_case redundancy_case
    _reconstruction_case _checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact redundancy_case h

theorem ay_sdg_failure_reconstruction
    (digestMismatch pairMismatch deletionMismatch redundancyMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    reconstructionMismatch ->
    ay_sdg_SubsumptionDeletionGuardFailure
      digestMismatch pairMismatch deletionMismatch redundancyMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _pair_case _deletion_case _redundancy_case
    reconstruction_case _checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case h

theorem ay_sdg_failure_checker
    (digestMismatch pairMismatch deletionMismatch redundancyMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    checkerMismatch ->
    ay_sdg_SubsumptionDeletionGuardFailure
      digestMismatch pairMismatch deletionMismatch redundancyMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _pair_case _deletion_case _redundancy_case
    _reconstruction_case checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact checker_case h

theorem ay_sdg_failure_baseline
    (digestMismatch pairMismatch deletionMismatch redundancyMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    baselineMismatch ->
    ay_sdg_SubsumptionDeletionGuardFailure
      digestMismatch pairMismatch deletionMismatch redundancyMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _pair_case _deletion_case _redundancy_case
    _reconstruction_case _checker_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case h

theorem ay_sdg_failure_build
    (digestMismatch pairMismatch deletionMismatch redundancyMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    buildMismatch ->
    ay_sdg_SubsumptionDeletionGuardFailure
      digestMismatch pairMismatch deletionMismatch redundancyMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _pair_case _deletion_case _redundancy_case
    _reconstruction_case _checker_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case h

theorem ay_sdg_failure_validator
    (digestMismatch pairMismatch deletionMismatch redundancyMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    validatorMismatch ->
    ay_sdg_SubsumptionDeletionGuardFailure
      digestMismatch pairMismatch deletionMismatch redundancyMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _pair_case _deletion_case _redundancy_case
    _reconstruction_case _checker_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case h

theorem ay_sdg_failure_audit
    (digestMismatch pairMismatch deletionMismatch redundancyMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    auditMismatch ->
    ay_sdg_SubsumptionDeletionGuardFailure
      digestMismatch pairMismatch deletionMismatch redundancyMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _pair_case _deletion_case _redundancy_case
    _reconstruction_case _checker_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case h

theorem ay_sdg_diagnostic_no_claim
    (currentCnf : Prop)
    (digestMismatch pairMismatch deletionMismatch redundancyMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_sdg_DiagnosticSubsumptionDeletionGuard
      currentCnf digestMismatch pairMismatch deletionMismatch redundancyMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_sdg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard
  exact ay_sdg_conj_right
    (ay_sdg_RecomputeObligation currentCnf recompute)
    (ay_sdg_NoSemanticClaim diagnostic)
    (ay_sdg_conj_right
      (ay_sdg_SubsumptionDeletionGuardFailure
        digestMismatch pairMismatch deletionMismatch redundancyMismatch
        reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
        validatorMismatch auditMismatch)
      (ay_sdg_Conj
        (ay_sdg_RecomputeObligation currentCnf recompute)
        (ay_sdg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_sdg_diagnostic_recompute
    (currentCnf : Prop)
    (digestMismatch pairMismatch deletionMismatch redundancyMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_sdg_DiagnosticSubsumptionDeletionGuard
      currentCnf digestMismatch pairMismatch deletionMismatch redundancyMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_sdg_RecomputeObligation currentCnf recompute := by
  intro diagnosticGuard
  exact ay_sdg_conj_left
    (ay_sdg_RecomputeObligation currentCnf recompute)
    (ay_sdg_NoSemanticClaim diagnostic)
    (ay_sdg_conj_right
      (ay_sdg_SubsumptionDeletionGuardFailure
        digestMismatch pairMismatch deletionMismatch redundancyMismatch
        reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
        validatorMismatch auditMismatch)
      (ay_sdg_Conj
        (ay_sdg_RecomputeObligation currentCnf recompute)
        (ay_sdg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_sdg_failed_guard_cannot_bless_public_result
    (currentCnf : Prop)
    (digestMismatch pairMismatch deletionMismatch redundancyMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_sdg_DiagnosticSubsumptionDeletionGuard
      currentCnf digestMismatch pairMismatch deletionMismatch redundancyMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_sdg_PublicResult originalCnf model certificate conflict exitCode ->
    ay_sdg_Conj
      (ay_sdg_NoSemanticClaim diagnostic)
      (ay_sdg_RecomputeObligation currentCnf recompute) := by
  intro diagnosticGuard _publicResult
  exact ay_sdg_conj_intro
    (ay_sdg_NoSemanticClaim diagnostic)
    (ay_sdg_RecomputeObligation currentCnf recompute)
    (ay_sdg_diagnostic_no_claim
      currentCnf digestMismatch pairMismatch deletionMismatch redundancyMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic diagnosticGuard)
    (ay_sdg_diagnostic_recompute
      currentCnf digestMismatch pairMismatch deletionMismatch redundancyMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic diagnosticGuard)

theorem ay_sdg_failed_guard_cannot_bless_public_sat
    (currentCnf : Prop)
    (digestMismatch pairMismatch deletionMismatch redundancyMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop) (exitCode : Prop) :
    ay_sdg_DiagnosticSubsumptionDeletionGuard
      currentCnf digestMismatch pairMismatch deletionMismatch redundancyMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_sdg_ExitCodeSound exitCode (ay_sdg_Sat originalCnf model) ->
    ay_sdg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _satClaim
  exact ay_sdg_diagnostic_no_claim
    currentCnf digestMismatch pairMismatch deletionMismatch redundancyMismatch
    reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
    validatorMismatch auditMismatch recompute diagnostic diagnosticGuard

theorem ay_sdg_failed_guard_cannot_bless_public_unsat
    (currentCnf : Prop)
    (digestMismatch pairMismatch deletionMismatch redundancyMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (certificate : Prop) (conflict : Prop)
    (exitCode : Prop) :
    ay_sdg_DiagnosticSubsumptionDeletionGuard
      currentCnf digestMismatch pairMismatch deletionMismatch redundancyMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_sdg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_sdg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _unsatClaim
  exact ay_sdg_diagnostic_no_claim
    currentCnf digestMismatch pairMismatch deletionMismatch redundancyMismatch
    reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
    validatorMismatch auditMismatch recompute diagnostic diagnosticGuard
