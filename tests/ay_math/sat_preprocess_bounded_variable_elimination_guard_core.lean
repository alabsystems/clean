-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded-variable-elimination preprocessing guard soundness.
-- The propositions stand for original formula fingerprints, eliminated-variable
-- ledgers, occurrence-list digests, generated-resolvent digests, tautology or
-- skipped-resolvent witnesses, clause-deletion ledgers, resolvent bounds,
-- model extension, UNSAT replay/equisat evidence, build/validator gates,
-- fallback no-claim paths, audit transcripts, and public SAT/UNSAT reports.

def ay_bveg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bveg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_bveg_Equisat (original : Prop) (reduced : Prop) :=
  ay_bveg_Conj (original -> reduced) (reduced -> original)

def ay_bveg_Sat (cnf : Prop) (model : Prop) :=
  ay_bveg_Conj cnf model

def ay_bveg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_bveg_OriginalFormulaFingerprint
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop) :=
  ay_bveg_Conj fingerprintManifest (fingerprint -> fingerprintAccepted)

def ay_bveg_EliminatedVariableLedger
    (eliminatedVariableLedger : Prop) (eliminationAccepted : Prop)
    (eliminationCoverage : Prop) :=
  ay_bveg_Conj eliminationCoverage
    (eliminatedVariableLedger -> eliminationAccepted)

def ay_bveg_OccurrenceListDigest
    (occurrenceListDigest : Prop) (occurrenceDigestAccepted : Prop)
    (occurrenceManifest : Prop) :=
  ay_bveg_Conj occurrenceManifest
    (occurrenceListDigest -> occurrenceDigestAccepted)

def ay_bveg_GeneratedResolventDigest
    (generatedResolventDigest : Prop) (resolventDigestAccepted : Prop)
    (resolventManifest : Prop) :=
  ay_bveg_Conj resolventManifest
    (generatedResolventDigest -> resolventDigestAccepted)

def ay_bveg_TautologySkippedResolventWitness
    (tautologySkippedWitness : Prop) (tautologySkippedAccepted : Prop)
    (tautologySkippedCoverage : Prop) :=
  ay_bveg_Conj tautologySkippedCoverage
    (tautologySkippedWitness -> tautologySkippedAccepted)

def ay_bveg_ClauseDeletionLedger
    (clauseDeletionLedger : Prop) (deletionAccepted : Prop)
    (deletionCoverage : Prop) :=
  ay_bveg_Conj deletionCoverage (clauseDeletionLedger -> deletionAccepted)

def ay_bveg_ResolventBoundWitness
    (resolventBoundWitness : Prop) (boundAccepted : Prop)
    (boundCoverage : Prop) :=
  ay_bveg_Conj boundCoverage (resolventBoundWitness -> boundAccepted)

def ay_bveg_ValidatorGate
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop) :=
  ay_bveg_Conj checkerAccepted
    (ay_bveg_Conj validatorAccepted validatorVersion)

def ay_bveg_ModelExtensionWitness
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :=
  ay_bveg_Sat reducedCnf reducedModel ->
    ay_bveg_Sat originalCnf originalModel

def ay_bveg_UnsatReplayEquisatWitness
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_bveg_Replay reducedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_bveg_ReconstructionEvidence
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_bveg_Conj
    (ay_bveg_ModelExtensionWitness
      reducedCnf originalCnf reducedModel originalModel)
    (ay_bveg_UnsatReplayEquisatWitness
      originalCnf reducedCnf certificate conflict)

def ay_bveg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_bveg_Conj binaryFingerprint buildReproducible

def ay_bveg_FallbackNoClaimPath
    (baselineAvailable : Prop) (noClaimPath : Prop) :=
  ay_bveg_Conj baselineAvailable noClaimPath

def ay_bveg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_bveg_Conj auditAppended auditAppendOnly

def ay_bveg_AcceptedBoundedVariableEliminationGuard
    (originalCnf : Prop) (reducedCnf : Prop)
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop)
    (eliminatedVariableLedger : Prop) (eliminationAccepted : Prop)
    (eliminationCoverage : Prop)
    (occurrenceListDigest : Prop) (occurrenceDigestAccepted : Prop)
    (occurrenceManifest : Prop)
    (generatedResolventDigest : Prop) (resolventDigestAccepted : Prop)
    (resolventManifest : Prop)
    (tautologySkippedWitness : Prop) (tautologySkippedAccepted : Prop)
    (tautologySkippedCoverage : Prop)
    (clauseDeletionLedger : Prop) (deletionAccepted : Prop)
    (deletionCoverage : Prop)
    (resolventBoundWitness : Prop) (boundAccepted : Prop)
    (boundCoverage : Prop)
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (baselineAvailable : Prop) (noClaimPath : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_bveg_OriginalFormulaFingerprint
       fingerprint fingerprintAccepted fingerprintManifest ->
     ay_bveg_EliminatedVariableLedger
       eliminatedVariableLedger eliminationAccepted eliminationCoverage ->
     ay_bveg_OccurrenceListDigest
       occurrenceListDigest occurrenceDigestAccepted occurrenceManifest ->
     ay_bveg_GeneratedResolventDigest
       generatedResolventDigest resolventDigestAccepted resolventManifest ->
     ay_bveg_TautologySkippedResolventWitness
       tautologySkippedWitness tautologySkippedAccepted tautologySkippedCoverage ->
     ay_bveg_ClauseDeletionLedger
       clauseDeletionLedger deletionAccepted deletionCoverage ->
     ay_bveg_ResolventBoundWitness
       resolventBoundWitness boundAccepted boundCoverage ->
     ay_bveg_ReconstructionEvidence
       reducedCnf originalCnf reducedModel originalModel certificate conflict ->
     ay_bveg_Equisat originalCnf reducedCnf ->
     ay_bveg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_bveg_ValidatorGate checkerAccepted validatorAccepted validatorVersion ->
     ay_bveg_FallbackNoClaimPath baselineAvailable noClaimPath ->
     ay_bveg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_bveg_BveGuardFailure
    (occurrenceMismatch : Prop) (resolventMismatch : Prop)
    (boundMismatch : Prop) (deletionMismatch : Prop)
    (modelExtensionMismatch : Prop) (replayMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (auditMismatch : Prop) :=
  forall result : Prop,
    (occurrenceMismatch -> result) ->
    (resolventMismatch -> result) ->
    (boundMismatch -> result) ->
    (deletionMismatch -> result) ->
    (modelExtensionMismatch -> result) ->
    (replayMismatch -> result) ->
    (buildMismatch -> result) ->
    (validatorMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_bveg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_bveg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_bveg_Conj currentCnf recompute

def ay_bveg_DiagnosticBveGuard
    (currentCnf : Prop)
    (occurrenceMismatch : Prop) (resolventMismatch : Prop)
    (boundMismatch : Prop) (deletionMismatch : Prop)
    (modelExtensionMismatch : Prop) (replayMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_bveg_Conj
    (ay_bveg_BveGuardFailure
      occurrenceMismatch resolventMismatch boundMismatch deletionMismatch
      modelExtensionMismatch replayMismatch buildMismatch validatorMismatch
      auditMismatch)
    (ay_bveg_Conj
      (ay_bveg_RecomputeObligation currentCnf recompute)
      (ay_bveg_NoSemanticClaim diagnostic))

def ay_bveg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_bveg_Conj exitCode claim

def ay_bveg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_bveg_Disj
    (ay_bveg_ExitCodeSound exitCode (ay_bveg_Sat originalCnf model))
    (ay_bveg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_bveg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_bveg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_bveg_conj_left
    (left : Prop) (right : Prop) :
    ay_bveg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_bveg_conj_right
    (left : Prop) (right : Prop) :
    ay_bveg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_bveg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_bveg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_bveg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_bveg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_bveg_equisat_forward
    (original : Prop) (reduced : Prop) :
    ay_bveg_Equisat original reduced -> original -> reduced := by
  intro eqsat
  exact ay_bveg_conj_left (original -> reduced) (reduced -> original) eqsat

theorem ay_bveg_equisat_backward
    (original : Prop) (reduced : Prop) :
    ay_bveg_Equisat original reduced -> reduced -> original := by
  intro eqsat
  exact ay_bveg_conj_right (original -> reduced) (reduced -> original) eqsat

theorem ay_bveg_occurrence_digest_applies
    (occurrenceListDigest : Prop) (occurrenceDigestAccepted : Prop)
    (occurrenceManifest : Prop) :
    ay_bveg_OccurrenceListDigest
      occurrenceListDigest occurrenceDigestAccepted occurrenceManifest ->
    occurrenceListDigest -> occurrenceDigestAccepted := by
  intro digest
  exact ay_bveg_conj_right
    occurrenceManifest (occurrenceListDigest -> occurrenceDigestAccepted) digest

theorem ay_bveg_generated_resolvent_digest_applies
    (generatedResolventDigest : Prop) (resolventDigestAccepted : Prop)
    (resolventManifest : Prop) :
    ay_bveg_GeneratedResolventDigest
      generatedResolventDigest resolventDigestAccepted resolventManifest ->
    generatedResolventDigest -> resolventDigestAccepted := by
  intro digest
  exact ay_bveg_conj_right
    resolventManifest (generatedResolventDigest -> resolventDigestAccepted)
    digest

theorem ay_bveg_resolvent_bound_witness_applies
    (resolventBoundWitness : Prop) (boundAccepted : Prop)
    (boundCoverage : Prop) :
    ay_bveg_ResolventBoundWitness
      resolventBoundWitness boundAccepted boundCoverage ->
    resolventBoundWitness -> boundAccepted := by
  intro witness
  exact ay_bveg_conj_right
    boundCoverage (resolventBoundWitness -> boundAccepted) witness

theorem ay_bveg_clause_deletion_ledger_applies
    (clauseDeletionLedger : Prop) (deletionAccepted : Prop)
    (deletionCoverage : Prop) :
    ay_bveg_ClauseDeletionLedger
      clauseDeletionLedger deletionAccepted deletionCoverage ->
    clauseDeletionLedger -> deletionAccepted := by
  intro ledger
  exact ay_bveg_conj_right
    deletionCoverage (clauseDeletionLedger -> deletionAccepted) ledger

theorem ay_bveg_model_extension
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_bveg_ReconstructionEvidence
      reducedCnf originalCnf reducedModel originalModel certificate conflict ->
    ay_bveg_Sat reducedCnf reducedModel ->
    ay_bveg_Sat originalCnf originalModel := by
  intro witnesses
  exact ay_bveg_conj_left
    (ay_bveg_ModelExtensionWitness
      reducedCnf originalCnf reducedModel originalModel)
    (ay_bveg_UnsatReplayEquisatWitness
      originalCnf reducedCnf certificate conflict)
    witnesses

theorem ay_bveg_unsat_replay
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_bveg_ReconstructionEvidence
      reducedCnf originalCnf reducedModel originalModel certificate conflict ->
    ay_bveg_Replay reducedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses
  exact ay_bveg_conj_right
    (ay_bveg_ModelExtensionWitness
      reducedCnf originalCnf reducedModel originalModel)
    (ay_bveg_UnsatReplayEquisatWitness
      originalCnf reducedCnf certificate conflict)
    witnesses

theorem ay_bveg_accepted_equisat
    (originalCnf : Prop) (reducedCnf : Prop)
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop)
    (eliminatedVariableLedger : Prop) (eliminationAccepted : Prop)
    (eliminationCoverage : Prop)
    (occurrenceListDigest : Prop) (occurrenceDigestAccepted : Prop)
    (occurrenceManifest : Prop)
    (generatedResolventDigest : Prop) (resolventDigestAccepted : Prop)
    (resolventManifest : Prop)
    (tautologySkippedWitness : Prop) (tautologySkippedAccepted : Prop)
    (tautologySkippedCoverage : Prop)
    (clauseDeletionLedger : Prop) (deletionAccepted : Prop)
    (deletionCoverage : Prop)
    (resolventBoundWitness : Prop) (boundAccepted : Prop)
    (boundCoverage : Prop)
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (baselineAvailable : Prop) (noClaimPath : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_bveg_AcceptedBoundedVariableEliminationGuard
      originalCnf reducedCnf
      fingerprint fingerprintAccepted fingerprintManifest
      eliminatedVariableLedger eliminationAccepted eliminationCoverage
      occurrenceListDigest occurrenceDigestAccepted occurrenceManifest
      generatedResolventDigest resolventDigestAccepted resolventManifest
      tautologySkippedWitness tautologySkippedAccepted tautologySkippedCoverage
      clauseDeletionLedger deletionAccepted deletionCoverage
      resolventBoundWitness boundAccepted boundCoverage
      checkerAccepted validatorAccepted validatorVersion
      reducedModel originalModel certificate conflict
      binaryFingerprint buildReproducible
      baselineAvailable noClaimPath auditAppended auditAppendOnly ->
    ay_bveg_Equisat originalCnf reducedCnf := by
  intro accepted
  exact accepted (ay_bveg_Equisat originalCnf reducedCnf)
    (fun _fingerprint _elim _occ _res _skip _del _bound _reconstruct
      eqsat _build _validator _fallback _audit => eqsat)

theorem ay_bveg_accepted_reconstruction
    (originalCnf : Prop) (reducedCnf : Prop)
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop)
    (eliminatedVariableLedger : Prop) (eliminationAccepted : Prop)
    (eliminationCoverage : Prop)
    (occurrenceListDigest : Prop) (occurrenceDigestAccepted : Prop)
    (occurrenceManifest : Prop)
    (generatedResolventDigest : Prop) (resolventDigestAccepted : Prop)
    (resolventManifest : Prop)
    (tautologySkippedWitness : Prop) (tautologySkippedAccepted : Prop)
    (tautologySkippedCoverage : Prop)
    (clauseDeletionLedger : Prop) (deletionAccepted : Prop)
    (deletionCoverage : Prop)
    (resolventBoundWitness : Prop) (boundAccepted : Prop)
    (boundCoverage : Prop)
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (baselineAvailable : Prop) (noClaimPath : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_bveg_AcceptedBoundedVariableEliminationGuard
      originalCnf reducedCnf
      fingerprint fingerprintAccepted fingerprintManifest
      eliminatedVariableLedger eliminationAccepted eliminationCoverage
      occurrenceListDigest occurrenceDigestAccepted occurrenceManifest
      generatedResolventDigest resolventDigestAccepted resolventManifest
      tautologySkippedWitness tautologySkippedAccepted tautologySkippedCoverage
      clauseDeletionLedger deletionAccepted deletionCoverage
      resolventBoundWitness boundAccepted boundCoverage
      checkerAccepted validatorAccepted validatorVersion
      reducedModel originalModel certificate conflict
      binaryFingerprint buildReproducible
      baselineAvailable noClaimPath auditAppended auditAppendOnly ->
    ay_bveg_ReconstructionEvidence
      reducedCnf originalCnf reducedModel originalModel certificate conflict := by
  intro accepted
  exact accepted
    (ay_bveg_ReconstructionEvidence
      reducedCnf originalCnf reducedModel originalModel certificate conflict)
    (fun _fingerprint _elim _occ _res _skip _del _bound reconstruct
      _eqsat _build _validator _fallback _audit => reconstruct)

theorem ay_bveg_sat_pullback
    (originalCnf : Prop) (reducedCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_bveg_ReconstructionEvidence
      reducedCnf originalCnf reducedModel originalModel certificate conflict ->
    ay_bveg_Sat reducedCnf reducedModel ->
    ay_bveg_Sat originalCnf originalModel := by
  intro witnesses satReduced
  exact ay_bveg_model_extension
    reducedCnf originalCnf reducedModel originalModel
    certificate conflict witnesses satReduced

theorem ay_bveg_unsat_pushback
    (originalCnf : Prop) (reducedCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_bveg_ReconstructionEvidence
      reducedCnf originalCnf reducedModel originalModel certificate conflict ->
    ay_bveg_Replay reducedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses replay
  exact ay_bveg_unsat_replay
    reducedCnf originalCnf reducedModel originalModel
    certificate conflict witnesses replay

theorem ay_bveg_public_sat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_bveg_ExitCodeSound exitCode (ay_bveg_Sat originalCnf originalModel) ->
    ay_bveg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro satSound
  exact ay_bveg_disj_left
    (ay_bveg_ExitCodeSound exitCode (ay_bveg_Sat originalCnf originalModel))
    (ay_bveg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    satSound

theorem ay_bveg_public_unsat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_bveg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_bveg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro unsatSound
  exact ay_bveg_disj_right
    (ay_bveg_ExitCodeSound exitCode (ay_bveg_Sat originalCnf originalModel))
    (ay_bveg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    unsatSound

theorem ay_bveg_failure_occurrence
    (occurrenceMismatch resolventMismatch boundMismatch deletionMismatch : Prop)
    (modelExtensionMismatch replayMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    occurrenceMismatch ->
    ay_bveg_BveGuardFailure
      occurrenceMismatch resolventMismatch boundMismatch deletionMismatch
      modelExtensionMismatch replayMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result occurrence_case _resolvent_case _bound_case _deletion_case
    _model_case _replay_case _build_case _validator_case _audit_case
  exact occurrence_case h

theorem ay_bveg_failure_resolvent
    (occurrenceMismatch resolventMismatch boundMismatch deletionMismatch : Prop)
    (modelExtensionMismatch replayMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    resolventMismatch ->
    ay_bveg_BveGuardFailure
      occurrenceMismatch resolventMismatch boundMismatch deletionMismatch
      modelExtensionMismatch replayMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _occurrence_case resolvent_case _bound_case _deletion_case
    _model_case _replay_case _build_case _validator_case _audit_case
  exact resolvent_case h

theorem ay_bveg_failure_bound
    (occurrenceMismatch resolventMismatch boundMismatch deletionMismatch : Prop)
    (modelExtensionMismatch replayMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    boundMismatch ->
    ay_bveg_BveGuardFailure
      occurrenceMismatch resolventMismatch boundMismatch deletionMismatch
      modelExtensionMismatch replayMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _occurrence_case _resolvent_case bound_case _deletion_case
    _model_case _replay_case _build_case _validator_case _audit_case
  exact bound_case h

theorem ay_bveg_failure_deletion
    (occurrenceMismatch resolventMismatch boundMismatch deletionMismatch : Prop)
    (modelExtensionMismatch replayMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    deletionMismatch ->
    ay_bveg_BveGuardFailure
      occurrenceMismatch resolventMismatch boundMismatch deletionMismatch
      modelExtensionMismatch replayMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _occurrence_case _resolvent_case _bound_case deletion_case
    _model_case _replay_case _build_case _validator_case _audit_case
  exact deletion_case h

theorem ay_bveg_failure_model_extension
    (occurrenceMismatch resolventMismatch boundMismatch deletionMismatch : Prop)
    (modelExtensionMismatch replayMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    modelExtensionMismatch ->
    ay_bveg_BveGuardFailure
      occurrenceMismatch resolventMismatch boundMismatch deletionMismatch
      modelExtensionMismatch replayMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _occurrence_case _resolvent_case _bound_case _deletion_case
    model_case _replay_case _build_case _validator_case _audit_case
  exact model_case h

theorem ay_bveg_failure_replay
    (occurrenceMismatch resolventMismatch boundMismatch deletionMismatch : Prop)
    (modelExtensionMismatch replayMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    replayMismatch ->
    ay_bveg_BveGuardFailure
      occurrenceMismatch resolventMismatch boundMismatch deletionMismatch
      modelExtensionMismatch replayMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _occurrence_case _resolvent_case _bound_case _deletion_case
    _model_case replay_case _build_case _validator_case _audit_case
  exact replay_case h

theorem ay_bveg_failure_build
    (occurrenceMismatch resolventMismatch boundMismatch deletionMismatch : Prop)
    (modelExtensionMismatch replayMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    buildMismatch ->
    ay_bveg_BveGuardFailure
      occurrenceMismatch resolventMismatch boundMismatch deletionMismatch
      modelExtensionMismatch replayMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _occurrence_case _resolvent_case _bound_case _deletion_case
    _model_case _replay_case build_case _validator_case _audit_case
  exact build_case h

theorem ay_bveg_failure_validator
    (occurrenceMismatch resolventMismatch boundMismatch deletionMismatch : Prop)
    (modelExtensionMismatch replayMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    validatorMismatch ->
    ay_bveg_BveGuardFailure
      occurrenceMismatch resolventMismatch boundMismatch deletionMismatch
      modelExtensionMismatch replayMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _occurrence_case _resolvent_case _bound_case _deletion_case
    _model_case _replay_case _build_case validator_case _audit_case
  exact validator_case h

theorem ay_bveg_failure_audit
    (occurrenceMismatch resolventMismatch boundMismatch deletionMismatch : Prop)
    (modelExtensionMismatch replayMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    auditMismatch ->
    ay_bveg_BveGuardFailure
      occurrenceMismatch resolventMismatch boundMismatch deletionMismatch
      modelExtensionMismatch replayMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _occurrence_case _resolvent_case _bound_case _deletion_case
    _model_case _replay_case _build_case _validator_case audit_case
  exact audit_case h

theorem ay_bveg_diagnostic_no_claim
    (currentCnf : Prop)
    (occurrenceMismatch resolventMismatch boundMismatch deletionMismatch : Prop)
    (modelExtensionMismatch replayMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_bveg_DiagnosticBveGuard
      currentCnf occurrenceMismatch resolventMismatch boundMismatch
      deletionMismatch modelExtensionMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_bveg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard
  exact ay_bveg_conj_right
    (ay_bveg_RecomputeObligation currentCnf recompute)
    (ay_bveg_NoSemanticClaim diagnostic)
    (ay_bveg_conj_right
      (ay_bveg_BveGuardFailure
        occurrenceMismatch resolventMismatch boundMismatch deletionMismatch
        modelExtensionMismatch replayMismatch buildMismatch validatorMismatch
        auditMismatch)
      (ay_bveg_Conj
        (ay_bveg_RecomputeObligation currentCnf recompute)
        (ay_bveg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_bveg_diagnostic_recompute
    (currentCnf : Prop)
    (occurrenceMismatch resolventMismatch boundMismatch deletionMismatch : Prop)
    (modelExtensionMismatch replayMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_bveg_DiagnosticBveGuard
      currentCnf occurrenceMismatch resolventMismatch boundMismatch
      deletionMismatch modelExtensionMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_bveg_RecomputeObligation currentCnf recompute := by
  intro diagnosticGuard
  exact ay_bveg_conj_left
    (ay_bveg_RecomputeObligation currentCnf recompute)
    (ay_bveg_NoSemanticClaim diagnostic)
    (ay_bveg_conj_right
      (ay_bveg_BveGuardFailure
        occurrenceMismatch resolventMismatch boundMismatch deletionMismatch
        modelExtensionMismatch replayMismatch buildMismatch validatorMismatch
        auditMismatch)
      (ay_bveg_Conj
        (ay_bveg_RecomputeObligation currentCnf recompute)
        (ay_bveg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_bveg_failed_guard_cannot_bless_public_result
    (currentCnf : Prop)
    (occurrenceMismatch resolventMismatch boundMismatch deletionMismatch : Prop)
    (modelExtensionMismatch replayMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_bveg_DiagnosticBveGuard
      currentCnf occurrenceMismatch resolventMismatch boundMismatch
      deletionMismatch modelExtensionMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_bveg_PublicResult originalCnf model certificate conflict exitCode ->
    ay_bveg_Conj
      (ay_bveg_NoSemanticClaim diagnostic)
      (ay_bveg_RecomputeObligation currentCnf recompute) := by
  intro diagnosticGuard _publicResult
  exact ay_bveg_conj_intro
    (ay_bveg_NoSemanticClaim diagnostic)
    (ay_bveg_RecomputeObligation currentCnf recompute)
    (ay_bveg_diagnostic_no_claim
      currentCnf occurrenceMismatch resolventMismatch boundMismatch
      deletionMismatch modelExtensionMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic diagnosticGuard)
    (ay_bveg_diagnostic_recompute
      currentCnf occurrenceMismatch resolventMismatch boundMismatch
      deletionMismatch modelExtensionMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic diagnosticGuard)

theorem ay_bveg_failed_guard_cannot_bless_public_sat
    (currentCnf : Prop)
    (occurrenceMismatch resolventMismatch boundMismatch deletionMismatch : Prop)
    (modelExtensionMismatch replayMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop) (exitCode : Prop) :
    ay_bveg_DiagnosticBveGuard
      currentCnf occurrenceMismatch resolventMismatch boundMismatch
      deletionMismatch modelExtensionMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_bveg_ExitCodeSound exitCode (ay_bveg_Sat originalCnf model) ->
    ay_bveg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _satClaim
  exact ay_bveg_diagnostic_no_claim
    currentCnf occurrenceMismatch resolventMismatch boundMismatch
    deletionMismatch modelExtensionMismatch replayMismatch buildMismatch
    validatorMismatch auditMismatch recompute diagnostic diagnosticGuard

theorem ay_bveg_failed_guard_cannot_bless_public_unsat
    (currentCnf : Prop)
    (occurrenceMismatch resolventMismatch boundMismatch deletionMismatch : Prop)
    (modelExtensionMismatch replayMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (certificate : Prop) (conflict : Prop)
    (exitCode : Prop) :
    ay_bveg_DiagnosticBveGuard
      currentCnf occurrenceMismatch resolventMismatch boundMismatch
      deletionMismatch modelExtensionMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_bveg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_bveg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _unsatClaim
  exact ay_bveg_diagnostic_no_claim
    currentCnf occurrenceMismatch resolventMismatch boundMismatch
    deletionMismatch modelExtensionMismatch replayMismatch buildMismatch
    validatorMismatch auditMismatch recompute diagnostic diagnosticGuard
