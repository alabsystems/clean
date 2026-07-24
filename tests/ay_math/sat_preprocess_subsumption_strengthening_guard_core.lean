-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Subsumption/strengthening guard soundness.
-- The propositions stand for clause digests, literal-deletion ledgers,
-- subsumption and exclusion witnesses, propagation replay, model/proof
-- reconstruction, fallback/build/validator gates, audit transcripts,
-- diagnostics, and public SAT/UNSAT reports.

def ay_ssgg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_ssgg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_ssgg_Equisat (original : Prop) (strengthened : Prop) :=
  ay_ssgg_Conj (original -> strengthened) (strengthened -> original)

def ay_ssgg_Sat (cnf : Prop) (model : Prop) :=
  ay_ssgg_Conj cnf model

def ay_ssgg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_ssgg_OriginalClauseDigest
    (originalDigest : Prop) (originalDigestAccepted : Prop)
    (originalClauseManifest : Prop) :=
  ay_ssgg_Conj originalClauseManifest (originalDigest -> originalDigestAccepted)

def ay_ssgg_StrengthenedClauseDigest
    (strengthenedDigest : Prop) (strengthenedDigestAccepted : Prop)
    (strengthenedClauseManifest : Prop) :=
  ay_ssgg_Conj strengthenedClauseManifest
    (strengthenedDigest -> strengthenedDigestAccepted)

def ay_ssgg_LiteralDeletionLedger
    (literalDeletionLedger : Prop) (literalDeletionAccepted : Prop)
    (deletedLiteralCoverage : Prop) :=
  ay_ssgg_Conj deletedLiteralCoverage
    (literalDeletionLedger -> literalDeletionAccepted)

def ay_ssgg_SubsumptionWitness
    (subsumptionWitness : Prop) (subsumptionAccepted : Prop)
    (subsumingClauseCoverage : Prop) :=
  ay_ssgg_Conj subsumingClauseCoverage
    (subsumptionWitness -> subsumptionAccepted)

def ay_ssgg_BlockedDeletionExclusionWitness
    (blockedDeletionExcluded : Prop) (exclusionAccepted : Prop)
    (exclusionLedger : Prop) :=
  ay_ssgg_Conj exclusionLedger (blockedDeletionExcluded -> exclusionAccepted)

def ay_ssgg_PropagationReplay
    (propagationTrace : Prop) (propagationAccepted : Prop)
    (propagationCoverage : Prop) :=
  ay_ssgg_Conj propagationCoverage (propagationTrace -> propagationAccepted)

def ay_ssgg_ModelLiftWitness
    (strengthenedCnf : Prop) (originalCnf : Prop)
    (strengthenedModel : Prop) (originalModel : Prop) :=
  ay_ssgg_Sat strengthenedCnf strengthenedModel ->
    ay_ssgg_Sat originalCnf originalModel

def ay_ssgg_UnsatProofReplayWitness
    (originalCnf : Prop) (strengthenedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_ssgg_Replay strengthenedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_ssgg_ReconstructionWitnesses
    (strengthenedCnf : Prop) (originalCnf : Prop)
    (strengthenedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_ssgg_Conj
    (ay_ssgg_ModelLiftWitness
      strengthenedCnf originalCnf strengthenedModel originalModel)
    (ay_ssgg_UnsatProofReplayWitness
      originalCnf strengthenedCnf certificate conflict)

def ay_ssgg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_ssgg_Conj baselineSolver baselineAvailable

def ay_ssgg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_ssgg_Conj binaryFingerprint buildReproducible

def ay_ssgg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_ssgg_Conj validatorAccepted validatorVersion

def ay_ssgg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_ssgg_Conj auditAppended auditAppendOnly

def ay_ssgg_AcceptedSubsumptionStrengtheningGuard
    (originalCnf : Prop) (strengthenedCnf : Prop)
    (originalDigest : Prop) (originalDigestAccepted : Prop)
    (originalClauseManifest : Prop)
    (strengthenedDigest : Prop) (strengthenedDigestAccepted : Prop)
    (strengthenedClauseManifest : Prop)
    (literalDeletionLedger : Prop) (literalDeletionAccepted : Prop)
    (deletedLiteralCoverage : Prop)
    (subsumptionWitness : Prop) (subsumptionAccepted : Prop)
    (subsumingClauseCoverage : Prop)
    (blockedDeletionExcluded : Prop) (exclusionAccepted : Prop)
    (exclusionLedger : Prop)
    (propagationTrace : Prop) (propagationAccepted : Prop)
    (propagationCoverage : Prop)
    (strengthenedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_ssgg_OriginalClauseDigest
       originalDigest originalDigestAccepted originalClauseManifest ->
     ay_ssgg_StrengthenedClauseDigest
       strengthenedDigest strengthenedDigestAccepted strengthenedClauseManifest ->
     ay_ssgg_LiteralDeletionLedger
       literalDeletionLedger literalDeletionAccepted deletedLiteralCoverage ->
     ay_ssgg_SubsumptionWitness
       subsumptionWitness subsumptionAccepted subsumingClauseCoverage ->
     ay_ssgg_BlockedDeletionExclusionWitness
       blockedDeletionExcluded exclusionAccepted exclusionLedger ->
     ay_ssgg_PropagationReplay
       propagationTrace propagationAccepted propagationCoverage ->
     ay_ssgg_ReconstructionWitnesses
       strengthenedCnf originalCnf strengthenedModel originalModel
       certificate conflict ->
     ay_ssgg_Equisat originalCnf strengthenedCnf ->
     ay_ssgg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_ssgg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_ssgg_ValidatorGate validatorAccepted validatorVersion ->
     ay_ssgg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_ssgg_StrengtheningGuardFailure
    (digestMismatch : Prop) (ledgerMismatch : Prop)
    (witnessMismatch : Prop) (replayMismatch : Prop)
    (reconstructionGap : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (digestMismatch -> result) ->
    (ledgerMismatch -> result) ->
    (witnessMismatch -> result) ->
    (replayMismatch -> result) ->
    (reconstructionGap -> result) ->
    (missingBaseline -> result) ->
    (buildDrift -> result) ->
    (validatorFailure -> result) ->
    (auditContradiction -> result) ->
    result

def ay_ssgg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_ssgg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_ssgg_Conj currentCnf recompute

def ay_ssgg_DiagnosticStrengtheningGuard
    (currentCnf : Prop)
    (digestMismatch : Prop) (ledgerMismatch : Prop)
    (witnessMismatch : Prop) (replayMismatch : Prop)
    (reconstructionGap : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_ssgg_Conj
    (ay_ssgg_StrengtheningGuardFailure
      digestMismatch ledgerMismatch witnessMismatch replayMismatch
      reconstructionGap missingBaseline buildDrift validatorFailure
      auditContradiction)
    (ay_ssgg_Conj
      (ay_ssgg_RecomputeObligation currentCnf recompute)
      (ay_ssgg_NoSemanticClaim diagnostic))

def ay_ssgg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_ssgg_Conj exitCode claim

def ay_ssgg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_ssgg_Disj
    (ay_ssgg_ExitCodeSound exitCode (ay_ssgg_Sat originalCnf model))
    (ay_ssgg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_ssgg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_ssgg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_ssgg_conj_left
    (left : Prop) (right : Prop) :
    ay_ssgg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_ssgg_conj_right
    (left : Prop) (right : Prop) :
    ay_ssgg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_ssgg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_ssgg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_ssgg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_ssgg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_ssgg_equisat_forward
    (original : Prop) (strengthened : Prop) :
    ay_ssgg_Equisat original strengthened -> original -> strengthened := by
  intro eqsat
  exact ay_ssgg_conj_left (original -> strengthened) (strengthened -> original) eqsat

theorem ay_ssgg_equisat_backward
    (original : Prop) (strengthened : Prop) :
    ay_ssgg_Equisat original strengthened -> strengthened -> original := by
  intro eqsat
  exact ay_ssgg_conj_right (original -> strengthened) (strengthened -> original) eqsat

theorem ay_ssgg_original_clause_digest_applies
    (originalDigest : Prop) (originalDigestAccepted : Prop)
    (originalClauseManifest : Prop) :
    ay_ssgg_OriginalClauseDigest
      originalDigest originalDigestAccepted originalClauseManifest ->
    originalDigest -> originalDigestAccepted := by
  intro digest
  exact ay_ssgg_conj_right
    originalClauseManifest (originalDigest -> originalDigestAccepted) digest

theorem ay_ssgg_strengthened_clause_digest_applies
    (strengthenedDigest : Prop) (strengthenedDigestAccepted : Prop)
    (strengthenedClauseManifest : Prop) :
    ay_ssgg_StrengthenedClauseDigest
      strengthenedDigest strengthenedDigestAccepted strengthenedClauseManifest ->
    strengthenedDigest -> strengthenedDigestAccepted := by
  intro digest
  exact ay_ssgg_conj_right
    strengthenedClauseManifest
    (strengthenedDigest -> strengthenedDigestAccepted) digest

theorem ay_ssgg_literal_deletion_ledger_applies
    (literalDeletionLedger : Prop) (literalDeletionAccepted : Prop)
    (deletedLiteralCoverage : Prop) :
    ay_ssgg_LiteralDeletionLedger
      literalDeletionLedger literalDeletionAccepted deletedLiteralCoverage ->
    literalDeletionLedger -> literalDeletionAccepted := by
  intro ledger
  exact ay_ssgg_conj_right
    deletedLiteralCoverage
    (literalDeletionLedger -> literalDeletionAccepted) ledger

theorem ay_ssgg_subsumption_witness_applies
    (subsumptionWitness : Prop) (subsumptionAccepted : Prop)
    (subsumingClauseCoverage : Prop) :
    ay_ssgg_SubsumptionWitness
      subsumptionWitness subsumptionAccepted subsumingClauseCoverage ->
    subsumptionWitness -> subsumptionAccepted := by
  intro witness
  exact ay_ssgg_conj_right
    subsumingClauseCoverage
    (subsumptionWitness -> subsumptionAccepted) witness

theorem ay_ssgg_blocked_deletion_exclusion_applies
    (blockedDeletionExcluded : Prop) (exclusionAccepted : Prop)
    (exclusionLedger : Prop) :
    ay_ssgg_BlockedDeletionExclusionWitness
      blockedDeletionExcluded exclusionAccepted exclusionLedger ->
    blockedDeletionExcluded -> exclusionAccepted := by
  intro witness
  exact ay_ssgg_conj_right
    exclusionLedger (blockedDeletionExcluded -> exclusionAccepted) witness

theorem ay_ssgg_propagation_replay_applies
    (propagationTrace : Prop) (propagationAccepted : Prop)
    (propagationCoverage : Prop) :
    ay_ssgg_PropagationReplay
      propagationTrace propagationAccepted propagationCoverage ->
    propagationTrace -> propagationAccepted := by
  intro replay
  exact ay_ssgg_conj_right
    propagationCoverage (propagationTrace -> propagationAccepted) replay

theorem ay_ssgg_model_lift
    (strengthenedCnf : Prop) (originalCnf : Prop)
    (strengthenedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_ssgg_ReconstructionWitnesses
      strengthenedCnf originalCnf strengthenedModel originalModel
      certificate conflict ->
    ay_ssgg_Sat strengthenedCnf strengthenedModel ->
    ay_ssgg_Sat originalCnf originalModel := by
  intro witnesses
  exact ay_ssgg_conj_left
    (ay_ssgg_ModelLiftWitness
      strengthenedCnf originalCnf strengthenedModel originalModel)
    (ay_ssgg_UnsatProofReplayWitness
      originalCnf strengthenedCnf certificate conflict)
    witnesses

theorem ay_ssgg_unsat_proof_replay
    (strengthenedCnf : Prop) (originalCnf : Prop)
    (strengthenedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_ssgg_ReconstructionWitnesses
      strengthenedCnf originalCnf strengthenedModel originalModel
      certificate conflict ->
    ay_ssgg_Replay strengthenedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses
  exact ay_ssgg_conj_right
    (ay_ssgg_ModelLiftWitness
      strengthenedCnf originalCnf strengthenedModel originalModel)
    (ay_ssgg_UnsatProofReplayWitness
      originalCnf strengthenedCnf certificate conflict)
    witnesses

theorem ay_ssgg_accepted_equisat
    (originalCnf : Prop) (strengthenedCnf : Prop)
    (originalDigest : Prop) (originalDigestAccepted : Prop)
    (originalClauseManifest : Prop)
    (strengthenedDigest : Prop) (strengthenedDigestAccepted : Prop)
    (strengthenedClauseManifest : Prop)
    (literalDeletionLedger : Prop) (literalDeletionAccepted : Prop)
    (deletedLiteralCoverage : Prop)
    (subsumptionWitness : Prop) (subsumptionAccepted : Prop)
    (subsumingClauseCoverage : Prop)
    (blockedDeletionExcluded : Prop) (exclusionAccepted : Prop)
    (exclusionLedger : Prop)
    (propagationTrace : Prop) (propagationAccepted : Prop)
    (propagationCoverage : Prop)
    (strengthenedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_ssgg_AcceptedSubsumptionStrengtheningGuard
      originalCnf strengthenedCnf
      originalDigest originalDigestAccepted originalClauseManifest
      strengthenedDigest strengthenedDigestAccepted strengthenedClauseManifest
      literalDeletionLedger literalDeletionAccepted deletedLiteralCoverage
      subsumptionWitness subsumptionAccepted subsumingClauseCoverage
      blockedDeletionExcluded exclusionAccepted exclusionLedger
      propagationTrace propagationAccepted propagationCoverage
      strengthenedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_ssgg_Equisat originalCnf strengthenedCnf := by
  intro accepted
  exact accepted (ay_ssgg_Equisat originalCnf strengthenedCnf)
    (fun _originalDigestOk _strengthenedDigestOk _literalLedgerOk
      _subsumptionOk _exclusionOk _propagationOk _reconstruct eqsat
      _fallback _build _validator _audit => eqsat)

theorem ay_ssgg_accepted_reconstruction
    (originalCnf : Prop) (strengthenedCnf : Prop)
    (originalDigest : Prop) (originalDigestAccepted : Prop)
    (originalClauseManifest : Prop)
    (strengthenedDigest : Prop) (strengthenedDigestAccepted : Prop)
    (strengthenedClauseManifest : Prop)
    (literalDeletionLedger : Prop) (literalDeletionAccepted : Prop)
    (deletedLiteralCoverage : Prop)
    (subsumptionWitness : Prop) (subsumptionAccepted : Prop)
    (subsumingClauseCoverage : Prop)
    (blockedDeletionExcluded : Prop) (exclusionAccepted : Prop)
    (exclusionLedger : Prop)
    (propagationTrace : Prop) (propagationAccepted : Prop)
    (propagationCoverage : Prop)
    (strengthenedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_ssgg_AcceptedSubsumptionStrengtheningGuard
      originalCnf strengthenedCnf
      originalDigest originalDigestAccepted originalClauseManifest
      strengthenedDigest strengthenedDigestAccepted strengthenedClauseManifest
      literalDeletionLedger literalDeletionAccepted deletedLiteralCoverage
      subsumptionWitness subsumptionAccepted subsumingClauseCoverage
      blockedDeletionExcluded exclusionAccepted exclusionLedger
      propagationTrace propagationAccepted propagationCoverage
      strengthenedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_ssgg_ReconstructionWitnesses
      strengthenedCnf originalCnf strengthenedModel originalModel
      certificate conflict := by
  intro accepted
  exact accepted
    (ay_ssgg_ReconstructionWitnesses
      strengthenedCnf originalCnf strengthenedModel originalModel
      certificate conflict)
    (fun _originalDigestOk _strengthenedDigestOk _literalLedgerOk
      _subsumptionOk _exclusionOk _propagationOk reconstruct _eqsat
      _fallback _build _validator _audit => reconstruct)

theorem ay_ssgg_sat_pullback
    (originalCnf : Prop) (strengthenedCnf : Prop)
    (strengthenedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_ssgg_ReconstructionWitnesses
      strengthenedCnf originalCnf strengthenedModel originalModel
      certificate conflict ->
    ay_ssgg_Sat strengthenedCnf strengthenedModel ->
    ay_ssgg_Sat originalCnf originalModel := by
  intro witnesses satStrengthened
  exact ay_ssgg_model_lift
    strengthenedCnf originalCnf strengthenedModel originalModel
    certificate conflict witnesses satStrengthened

theorem ay_ssgg_unsat_pushback
    (originalCnf : Prop) (strengthenedCnf : Prop)
    (strengthenedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_ssgg_ReconstructionWitnesses
      strengthenedCnf originalCnf strengthenedModel originalModel
      certificate conflict ->
    ay_ssgg_Replay strengthenedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses replay
  exact ay_ssgg_unsat_proof_replay
    strengthenedCnf originalCnf strengthenedModel originalModel
    certificate conflict witnesses replay

theorem ay_ssgg_public_sat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_ssgg_ExitCodeSound exitCode (ay_ssgg_Sat originalCnf originalModel) ->
    ay_ssgg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro satSound
  exact ay_ssgg_disj_left
    (ay_ssgg_ExitCodeSound exitCode (ay_ssgg_Sat originalCnf originalModel))
    (ay_ssgg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    satSound

theorem ay_ssgg_public_unsat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_ssgg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_ssgg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro unsatSound
  exact ay_ssgg_disj_right
    (ay_ssgg_ExitCodeSound exitCode (ay_ssgg_Sat originalCnf originalModel))
    (ay_ssgg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    unsatSound

theorem ay_ssgg_failure_digest
    (digestMismatch : Prop) (ledgerMismatch : Prop)
    (witnessMismatch : Prop) (replayMismatch : Prop)
    (reconstructionGap : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    digestMismatch ->
    ay_ssgg_StrengtheningGuardFailure
      digestMismatch ledgerMismatch witnessMismatch replayMismatch
      reconstructionGap missingBaseline buildDrift validatorFailure auditContradiction := by
  intro h result digest_case _ledger_case _witness_case _replay_case
    _reconstruction_case _baseline_case _build_case _validator_case _audit_case
  exact digest_case h

theorem ay_ssgg_failure_ledger
    (digestMismatch : Prop) (ledgerMismatch : Prop)
    (witnessMismatch : Prop) (replayMismatch : Prop)
    (reconstructionGap : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    ledgerMismatch ->
    ay_ssgg_StrengtheningGuardFailure
      digestMismatch ledgerMismatch witnessMismatch replayMismatch
      reconstructionGap missingBaseline buildDrift validatorFailure auditContradiction := by
  intro h result _digest_case ledger_case _witness_case _replay_case
    _reconstruction_case _baseline_case _build_case _validator_case _audit_case
  exact ledger_case h

theorem ay_ssgg_failure_witness
    (digestMismatch : Prop) (ledgerMismatch : Prop)
    (witnessMismatch : Prop) (replayMismatch : Prop)
    (reconstructionGap : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    witnessMismatch ->
    ay_ssgg_StrengtheningGuardFailure
      digestMismatch ledgerMismatch witnessMismatch replayMismatch
      reconstructionGap missingBaseline buildDrift validatorFailure auditContradiction := by
  intro h result _digest_case _ledger_case witness_case _replay_case
    _reconstruction_case _baseline_case _build_case _validator_case _audit_case
  exact witness_case h

theorem ay_ssgg_failure_replay
    (digestMismatch : Prop) (ledgerMismatch : Prop)
    (witnessMismatch : Prop) (replayMismatch : Prop)
    (reconstructionGap : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    replayMismatch ->
    ay_ssgg_StrengtheningGuardFailure
      digestMismatch ledgerMismatch witnessMismatch replayMismatch
      reconstructionGap missingBaseline buildDrift validatorFailure auditContradiction := by
  intro h result _digest_case _ledger_case _witness_case replay_case
    _reconstruction_case _baseline_case _build_case _validator_case _audit_case
  exact replay_case h

theorem ay_ssgg_failure_reconstruction
    (digestMismatch : Prop) (ledgerMismatch : Prop)
    (witnessMismatch : Prop) (replayMismatch : Prop)
    (reconstructionGap : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_ssgg_StrengtheningGuardFailure
      digestMismatch ledgerMismatch witnessMismatch replayMismatch
      reconstructionGap missingBaseline buildDrift validatorFailure auditContradiction := by
  intro h result _digest_case _ledger_case _witness_case _replay_case
    reconstruction_case _baseline_case _build_case _validator_case _audit_case
  exact reconstruction_case h

theorem ay_ssgg_failure_baseline
    (digestMismatch : Prop) (ledgerMismatch : Prop)
    (witnessMismatch : Prop) (replayMismatch : Prop)
    (reconstructionGap : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingBaseline ->
    ay_ssgg_StrengtheningGuardFailure
      digestMismatch ledgerMismatch witnessMismatch replayMismatch
      reconstructionGap missingBaseline buildDrift validatorFailure auditContradiction := by
  intro h result _digest_case _ledger_case _witness_case _replay_case
    _reconstruction_case baseline_case _build_case _validator_case _audit_case
  exact baseline_case h

theorem ay_ssgg_failure_build
    (digestMismatch : Prop) (ledgerMismatch : Prop)
    (witnessMismatch : Prop) (replayMismatch : Prop)
    (reconstructionGap : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_ssgg_StrengtheningGuardFailure
      digestMismatch ledgerMismatch witnessMismatch replayMismatch
      reconstructionGap missingBaseline buildDrift validatorFailure auditContradiction := by
  intro h result _digest_case _ledger_case _witness_case _replay_case
    _reconstruction_case _baseline_case build_case _validator_case _audit_case
  exact build_case h

theorem ay_ssgg_failure_validator
    (digestMismatch : Prop) (ledgerMismatch : Prop)
    (witnessMismatch : Prop) (replayMismatch : Prop)
    (reconstructionGap : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    validatorFailure ->
    ay_ssgg_StrengtheningGuardFailure
      digestMismatch ledgerMismatch witnessMismatch replayMismatch
      reconstructionGap missingBaseline buildDrift validatorFailure auditContradiction := by
  intro h result _digest_case _ledger_case _witness_case _replay_case
    _reconstruction_case _baseline_case _build_case validator_case _audit_case
  exact validator_case h

theorem ay_ssgg_failure_audit
    (digestMismatch : Prop) (ledgerMismatch : Prop)
    (witnessMismatch : Prop) (replayMismatch : Prop)
    (reconstructionGap : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_ssgg_StrengtheningGuardFailure
      digestMismatch ledgerMismatch witnessMismatch replayMismatch
      reconstructionGap missingBaseline buildDrift validatorFailure auditContradiction := by
  intro h result _digest_case _ledger_case _witness_case _replay_case
    _reconstruction_case _baseline_case _build_case _validator_case audit_case
  exact audit_case h

theorem ay_ssgg_diagnostic_no_claim
    (currentCnf : Prop)
    (digestMismatch : Prop) (ledgerMismatch : Prop)
    (witnessMismatch : Prop) (replayMismatch : Prop)
    (reconstructionGap : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_ssgg_DiagnosticStrengtheningGuard
      currentCnf digestMismatch ledgerMismatch witnessMismatch replayMismatch
      reconstructionGap missingBaseline buildDrift validatorFailure auditContradiction
      recompute diagnostic ->
    ay_ssgg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard
  exact ay_ssgg_conj_right
    (ay_ssgg_RecomputeObligation currentCnf recompute)
    (ay_ssgg_NoSemanticClaim diagnostic)
    (ay_ssgg_conj_right
      (ay_ssgg_StrengtheningGuardFailure
        digestMismatch ledgerMismatch witnessMismatch replayMismatch
        reconstructionGap missingBaseline buildDrift validatorFailure auditContradiction)
      (ay_ssgg_Conj
        (ay_ssgg_RecomputeObligation currentCnf recompute)
        (ay_ssgg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_ssgg_diagnostic_recompute
    (currentCnf : Prop)
    (digestMismatch : Prop) (ledgerMismatch : Prop)
    (witnessMismatch : Prop) (replayMismatch : Prop)
    (reconstructionGap : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_ssgg_DiagnosticStrengtheningGuard
      currentCnf digestMismatch ledgerMismatch witnessMismatch replayMismatch
      reconstructionGap missingBaseline buildDrift validatorFailure auditContradiction
      recompute diagnostic ->
    ay_ssgg_RecomputeObligation currentCnf recompute := by
  intro diagnosticGuard
  exact ay_ssgg_conj_left
    (ay_ssgg_RecomputeObligation currentCnf recompute)
    (ay_ssgg_NoSemanticClaim diagnostic)
    (ay_ssgg_conj_right
      (ay_ssgg_StrengtheningGuardFailure
        digestMismatch ledgerMismatch witnessMismatch replayMismatch
        reconstructionGap missingBaseline buildDrift validatorFailure auditContradiction)
      (ay_ssgg_Conj
        (ay_ssgg_RecomputeObligation currentCnf recompute)
        (ay_ssgg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_ssgg_failed_strengthening_cannot_bless_public_result
    (currentCnf : Prop)
    (digestMismatch : Prop) (ledgerMismatch : Prop)
    (witnessMismatch : Prop) (replayMismatch : Prop)
    (reconstructionGap : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_ssgg_DiagnosticStrengtheningGuard
      currentCnf digestMismatch ledgerMismatch witnessMismatch replayMismatch
      reconstructionGap missingBaseline buildDrift validatorFailure auditContradiction
      recompute diagnostic ->
    ay_ssgg_PublicResult originalCnf model certificate conflict exitCode ->
    ay_ssgg_Conj
      (ay_ssgg_NoSemanticClaim diagnostic)
      (ay_ssgg_RecomputeObligation currentCnf recompute) := by
  intro diagnosticGuard _publicResult
  exact ay_ssgg_conj_intro
    (ay_ssgg_NoSemanticClaim diagnostic)
    (ay_ssgg_RecomputeObligation currentCnf recompute)
    (ay_ssgg_diagnostic_no_claim
      currentCnf digestMismatch ledgerMismatch witnessMismatch replayMismatch
      reconstructionGap missingBaseline buildDrift validatorFailure auditContradiction
      recompute diagnostic diagnosticGuard)
    (ay_ssgg_diagnostic_recompute
      currentCnf digestMismatch ledgerMismatch witnessMismatch replayMismatch
      reconstructionGap missingBaseline buildDrift validatorFailure auditContradiction
      recompute diagnostic diagnosticGuard)

theorem ay_ssgg_failed_strengthening_cannot_bless_public_sat
    (currentCnf : Prop)
    (digestMismatch : Prop) (ledgerMismatch : Prop)
    (witnessMismatch : Prop) (replayMismatch : Prop)
    (reconstructionGap : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop) (exitCode : Prop) :
    ay_ssgg_DiagnosticStrengtheningGuard
      currentCnf digestMismatch ledgerMismatch witnessMismatch replayMismatch
      reconstructionGap missingBaseline buildDrift validatorFailure auditContradiction
      recompute diagnostic ->
    ay_ssgg_ExitCodeSound exitCode (ay_ssgg_Sat originalCnf model) ->
    ay_ssgg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _satClaim
  exact ay_ssgg_diagnostic_no_claim
    currentCnf digestMismatch ledgerMismatch witnessMismatch replayMismatch
    reconstructionGap missingBaseline buildDrift validatorFailure auditContradiction
    recompute diagnostic diagnosticGuard

theorem ay_ssgg_failed_strengthening_cannot_bless_public_unsat
    (currentCnf : Prop)
    (digestMismatch : Prop) (ledgerMismatch : Prop)
    (witnessMismatch : Prop) (replayMismatch : Prop)
    (reconstructionGap : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (certificate : Prop) (conflict : Prop)
    (exitCode : Prop) :
    ay_ssgg_DiagnosticStrengtheningGuard
      currentCnf digestMismatch ledgerMismatch witnessMismatch replayMismatch
      reconstructionGap missingBaseline buildDrift validatorFailure auditContradiction
      recompute diagnostic ->
    ay_ssgg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_ssgg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _unsatClaim
  exact ay_ssgg_diagnostic_no_claim
    currentCnf digestMismatch ledgerMismatch witnessMismatch replayMismatch
    reconstructionGap missingBaseline buildDrift validatorFailure auditContradiction
    recompute diagnostic diagnosticGuard
