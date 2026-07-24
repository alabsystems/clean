-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Failed-literal-probing preprocessing guard soundness.
-- The propositions stand for original formula fingerprints, probe literal
-- ledgers, temporary assignment trail digests, unit-propagation trace digests,
-- failed-branch conflict witnesses, forced-literal derivation ledgers, formula
-- simplification digests, model reconstruction, UNSAT replay/equisat evidence,
-- build/validator gates, fallback no-claim paths, audit transcripts, and
-- public SAT/UNSAT reports.

def ay_flpg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_flpg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_flpg_Equisat (original : Prop) (simplified : Prop) :=
  ay_flpg_Conj (original -> simplified) (simplified -> original)

def ay_flpg_Sat (cnf : Prop) (model : Prop) :=
  ay_flpg_Conj cnf model

def ay_flpg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_flpg_OriginalFormulaFingerprint
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop) :=
  ay_flpg_Conj fingerprintManifest (fingerprint -> fingerprintAccepted)

def ay_flpg_ProbeLiteralLedger
    (probeLiteralLedger : Prop) (probeAccepted : Prop)
    (probeCoverage : Prop) :=
  ay_flpg_Conj probeCoverage (probeLiteralLedger -> probeAccepted)

def ay_flpg_TemporaryAssignmentTrailDigest
    (trailDigest : Prop) (trailDigestAccepted : Prop)
    (trailDigestManifest : Prop) :=
  ay_flpg_Conj trailDigestManifest (trailDigest -> trailDigestAccepted)

def ay_flpg_UnitPropagationTraceDigest
    (propagationTraceDigest : Prop) (propagationTraceAccepted : Prop)
    (propagationTraceManifest : Prop) :=
  ay_flpg_Conj propagationTraceManifest
    (propagationTraceDigest -> propagationTraceAccepted)

def ay_flpg_ConflictWitness
    (conflictWitness : Prop) (conflictAccepted : Prop)
    (conflictCoverage : Prop) :=
  ay_flpg_Conj conflictCoverage (conflictWitness -> conflictAccepted)

def ay_flpg_ForcedLiteralDerivationLedger
    (forcedLiteralLedger : Prop) (forcedLiteralAccepted : Prop)
    (forcedLiteralCoverage : Prop) :=
  ay_flpg_Conj forcedLiteralCoverage
    (forcedLiteralLedger -> forcedLiteralAccepted)

def ay_flpg_FormulaSimplificationDigest
    (simplificationDigest : Prop) (simplificationDigestAccepted : Prop)
    (simplificationManifest : Prop) :=
  ay_flpg_Conj simplificationManifest
    (simplificationDigest -> simplificationDigestAccepted)

def ay_flpg_ValidatorGate
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop) :=
  ay_flpg_Conj checkerAccepted
    (ay_flpg_Conj validatorAccepted validatorVersion)

def ay_flpg_ModelReconstructionWitness
    (simplifiedCnf : Prop) (originalCnf : Prop)
    (simplifiedModel : Prop) (originalModel : Prop) :=
  ay_flpg_Sat simplifiedCnf simplifiedModel ->
    ay_flpg_Sat originalCnf originalModel

def ay_flpg_UnsatReplayEquisatWitness
    (originalCnf : Prop) (simplifiedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_flpg_Replay simplifiedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_flpg_ReconstructionEvidence
    (simplifiedCnf : Prop) (originalCnf : Prop)
    (simplifiedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_flpg_Conj
    (ay_flpg_ModelReconstructionWitness
      simplifiedCnf originalCnf simplifiedModel originalModel)
    (ay_flpg_UnsatReplayEquisatWitness
      originalCnf simplifiedCnf certificate conflict)

def ay_flpg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_flpg_Conj binaryFingerprint buildReproducible

def ay_flpg_FallbackNoClaimPath
    (baselineAvailable : Prop) (noClaimPath : Prop) :=
  ay_flpg_Conj baselineAvailable noClaimPath

def ay_flpg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_flpg_Conj auditAppended auditAppendOnly

def ay_flpg_AcceptedFailedLiteralProbingGuard
    (originalCnf : Prop) (simplifiedCnf : Prop)
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop)
    (probeLiteralLedger : Prop) (probeAccepted : Prop)
    (probeCoverage : Prop)
    (trailDigest : Prop) (trailDigestAccepted : Prop)
    (trailDigestManifest : Prop)
    (propagationTraceDigest : Prop) (propagationTraceAccepted : Prop)
    (propagationTraceManifest : Prop)
    (conflictWitness : Prop) (conflictAccepted : Prop)
    (conflictCoverage : Prop)
    (forcedLiteralLedger : Prop) (forcedLiteralAccepted : Prop)
    (forcedLiteralCoverage : Prop)
    (simplificationDigest : Prop) (simplificationDigestAccepted : Prop)
    (simplificationManifest : Prop)
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop)
    (simplifiedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (baselineAvailable : Prop) (noClaimPath : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_flpg_OriginalFormulaFingerprint
       fingerprint fingerprintAccepted fingerprintManifest ->
     ay_flpg_ProbeLiteralLedger
       probeLiteralLedger probeAccepted probeCoverage ->
     ay_flpg_TemporaryAssignmentTrailDigest
       trailDigest trailDigestAccepted trailDigestManifest ->
     ay_flpg_UnitPropagationTraceDigest
       propagationTraceDigest propagationTraceAccepted propagationTraceManifest ->
     ay_flpg_ConflictWitness
       conflictWitness conflictAccepted conflictCoverage ->
     ay_flpg_ForcedLiteralDerivationLedger
       forcedLiteralLedger forcedLiteralAccepted forcedLiteralCoverage ->
     ay_flpg_FormulaSimplificationDigest
       simplificationDigest simplificationDigestAccepted simplificationManifest ->
     ay_flpg_ReconstructionEvidence
       simplifiedCnf originalCnf simplifiedModel originalModel certificate conflict ->
     ay_flpg_Equisat originalCnf simplifiedCnf ->
     ay_flpg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_flpg_ValidatorGate checkerAccepted validatorAccepted validatorVersion ->
     ay_flpg_FallbackNoClaimPath baselineAvailable noClaimPath ->
     ay_flpg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_flpg_FailedProbeGuardFailure
    (probeMismatch : Prop) (trailMismatch : Prop)
    (propagationMismatch : Prop) (conflictMismatch : Prop)
    (forcedLiteralMismatch : Prop) (simplificationMismatch : Prop)
    (modelMismatch : Prop) (replayMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (auditMismatch : Prop) :=
  forall result : Prop,
    (probeMismatch -> result) ->
    (trailMismatch -> result) ->
    (propagationMismatch -> result) ->
    (conflictMismatch -> result) ->
    (forcedLiteralMismatch -> result) ->
    (simplificationMismatch -> result) ->
    (modelMismatch -> result) ->
    (replayMismatch -> result) ->
    (buildMismatch -> result) ->
    (validatorMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_flpg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_flpg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_flpg_Conj currentCnf recompute

def ay_flpg_DiagnosticFailedProbeGuard
    (currentCnf : Prop)
    (probeMismatch : Prop) (trailMismatch : Prop)
    (propagationMismatch : Prop) (conflictMismatch : Prop)
    (forcedLiteralMismatch : Prop) (simplificationMismatch : Prop)
    (modelMismatch : Prop) (replayMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_flpg_Conj
    (ay_flpg_FailedProbeGuardFailure
      probeMismatch trailMismatch propagationMismatch conflictMismatch
      forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch)
    (ay_flpg_Conj
      (ay_flpg_RecomputeObligation currentCnf recompute)
      (ay_flpg_NoSemanticClaim diagnostic))

def ay_flpg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_flpg_Conj exitCode claim

def ay_flpg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_flpg_Disj
    (ay_flpg_ExitCodeSound exitCode (ay_flpg_Sat originalCnf model))
    (ay_flpg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_flpg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_flpg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_flpg_conj_left
    (left : Prop) (right : Prop) :
    ay_flpg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_flpg_conj_right
    (left : Prop) (right : Prop) :
    ay_flpg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_flpg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_flpg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_flpg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_flpg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_flpg_equisat_forward
    (original : Prop) (simplified : Prop) :
    ay_flpg_Equisat original simplified -> original -> simplified := by
  intro eqsat
  exact ay_flpg_conj_left (original -> simplified) (simplified -> original) eqsat

theorem ay_flpg_equisat_backward
    (original : Prop) (simplified : Prop) :
    ay_flpg_Equisat original simplified -> simplified -> original := by
  intro eqsat
  exact ay_flpg_conj_right (original -> simplified) (simplified -> original) eqsat

theorem ay_flpg_probe_literal_ledger_applies
    (probeLiteralLedger : Prop) (probeAccepted : Prop)
    (probeCoverage : Prop) :
    ay_flpg_ProbeLiteralLedger
      probeLiteralLedger probeAccepted probeCoverage ->
    probeLiteralLedger -> probeAccepted := by
  intro ledger
  exact ay_flpg_conj_right
    probeCoverage (probeLiteralLedger -> probeAccepted) ledger

theorem ay_flpg_trail_digest_applies
    (trailDigest : Prop) (trailDigestAccepted : Prop)
    (trailDigestManifest : Prop) :
    ay_flpg_TemporaryAssignmentTrailDigest
      trailDigest trailDigestAccepted trailDigestManifest ->
    trailDigest -> trailDigestAccepted := by
  intro digest
  exact ay_flpg_conj_right
    trailDigestManifest (trailDigest -> trailDigestAccepted) digest

theorem ay_flpg_propagation_trace_digest_applies
    (propagationTraceDigest : Prop) (propagationTraceAccepted : Prop)
    (propagationTraceManifest : Prop) :
    ay_flpg_UnitPropagationTraceDigest
      propagationTraceDigest propagationTraceAccepted propagationTraceManifest ->
    propagationTraceDigest -> propagationTraceAccepted := by
  intro digest
  exact ay_flpg_conj_right
    propagationTraceManifest
    (propagationTraceDigest -> propagationTraceAccepted)
    digest

theorem ay_flpg_conflict_witness_applies
    (conflictWitness : Prop) (conflictAccepted : Prop)
    (conflictCoverage : Prop) :
    ay_flpg_ConflictWitness conflictWitness conflictAccepted conflictCoverage ->
    conflictWitness -> conflictAccepted := by
  intro witness
  exact ay_flpg_conj_right
    conflictCoverage (conflictWitness -> conflictAccepted) witness

theorem ay_flpg_forced_literal_ledger_applies
    (forcedLiteralLedger : Prop) (forcedLiteralAccepted : Prop)
    (forcedLiteralCoverage : Prop) :
    ay_flpg_ForcedLiteralDerivationLedger
      forcedLiteralLedger forcedLiteralAccepted forcedLiteralCoverage ->
    forcedLiteralLedger -> forcedLiteralAccepted := by
  intro ledger
  exact ay_flpg_conj_right
    forcedLiteralCoverage (forcedLiteralLedger -> forcedLiteralAccepted) ledger

theorem ay_flpg_simplification_digest_applies
    (simplificationDigest : Prop) (simplificationDigestAccepted : Prop)
    (simplificationManifest : Prop) :
    ay_flpg_FormulaSimplificationDigest
      simplificationDigest simplificationDigestAccepted simplificationManifest ->
    simplificationDigest -> simplificationDigestAccepted := by
  intro digest
  exact ay_flpg_conj_right
    simplificationManifest
    (simplificationDigest -> simplificationDigestAccepted)
    digest

theorem ay_flpg_model_reconstruction
    (simplifiedCnf : Prop) (originalCnf : Prop)
    (simplifiedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_flpg_ReconstructionEvidence
      simplifiedCnf originalCnf simplifiedModel originalModel certificate conflict ->
    ay_flpg_Sat simplifiedCnf simplifiedModel ->
    ay_flpg_Sat originalCnf originalModel := by
  intro witnesses
  exact ay_flpg_conj_left
    (ay_flpg_ModelReconstructionWitness
      simplifiedCnf originalCnf simplifiedModel originalModel)
    (ay_flpg_UnsatReplayEquisatWitness
      originalCnf simplifiedCnf certificate conflict)
    witnesses

theorem ay_flpg_unsat_replay
    (simplifiedCnf : Prop) (originalCnf : Prop)
    (simplifiedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_flpg_ReconstructionEvidence
      simplifiedCnf originalCnf simplifiedModel originalModel certificate conflict ->
    ay_flpg_Replay simplifiedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses
  exact ay_flpg_conj_right
    (ay_flpg_ModelReconstructionWitness
      simplifiedCnf originalCnf simplifiedModel originalModel)
    (ay_flpg_UnsatReplayEquisatWitness
      originalCnf simplifiedCnf certificate conflict)
    witnesses

theorem ay_flpg_accepted_equisat
    (originalCnf : Prop) (simplifiedCnf : Prop)
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop)
    (probeLiteralLedger : Prop) (probeAccepted : Prop)
    (probeCoverage : Prop)
    (trailDigest : Prop) (trailDigestAccepted : Prop)
    (trailDigestManifest : Prop)
    (propagationTraceDigest : Prop) (propagationTraceAccepted : Prop)
    (propagationTraceManifest : Prop)
    (conflictWitness : Prop) (conflictAccepted : Prop)
    (conflictCoverage : Prop)
    (forcedLiteralLedger : Prop) (forcedLiteralAccepted : Prop)
    (forcedLiteralCoverage : Prop)
    (simplificationDigest : Prop) (simplificationDigestAccepted : Prop)
    (simplificationManifest : Prop)
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop)
    (simplifiedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (baselineAvailable : Prop) (noClaimPath : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_flpg_AcceptedFailedLiteralProbingGuard
      originalCnf simplifiedCnf
      fingerprint fingerprintAccepted fingerprintManifest
      probeLiteralLedger probeAccepted probeCoverage
      trailDigest trailDigestAccepted trailDigestManifest
      propagationTraceDigest propagationTraceAccepted propagationTraceManifest
      conflictWitness conflictAccepted conflictCoverage
      forcedLiteralLedger forcedLiteralAccepted forcedLiteralCoverage
      simplificationDigest simplificationDigestAccepted simplificationManifest
      checkerAccepted validatorAccepted validatorVersion
      simplifiedModel originalModel certificate conflict
      binaryFingerprint buildReproducible
      baselineAvailable noClaimPath auditAppended auditAppendOnly ->
    ay_flpg_Equisat originalCnf simplifiedCnf := by
  intro accepted
  exact accepted (ay_flpg_Equisat originalCnf simplifiedCnf)
    (fun _fingerprint _probe _trail _propagation _conflict _forced
      _simplification _reconstruct eqsat _build _validator _fallback _audit =>
      eqsat)

theorem ay_flpg_accepted_reconstruction
    (originalCnf : Prop) (simplifiedCnf : Prop)
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop)
    (probeLiteralLedger : Prop) (probeAccepted : Prop)
    (probeCoverage : Prop)
    (trailDigest : Prop) (trailDigestAccepted : Prop)
    (trailDigestManifest : Prop)
    (propagationTraceDigest : Prop) (propagationTraceAccepted : Prop)
    (propagationTraceManifest : Prop)
    (conflictWitness : Prop) (conflictAccepted : Prop)
    (conflictCoverage : Prop)
    (forcedLiteralLedger : Prop) (forcedLiteralAccepted : Prop)
    (forcedLiteralCoverage : Prop)
    (simplificationDigest : Prop) (simplificationDigestAccepted : Prop)
    (simplificationManifest : Prop)
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop)
    (simplifiedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (baselineAvailable : Prop) (noClaimPath : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_flpg_AcceptedFailedLiteralProbingGuard
      originalCnf simplifiedCnf
      fingerprint fingerprintAccepted fingerprintManifest
      probeLiteralLedger probeAccepted probeCoverage
      trailDigest trailDigestAccepted trailDigestManifest
      propagationTraceDigest propagationTraceAccepted propagationTraceManifest
      conflictWitness conflictAccepted conflictCoverage
      forcedLiteralLedger forcedLiteralAccepted forcedLiteralCoverage
      simplificationDigest simplificationDigestAccepted simplificationManifest
      checkerAccepted validatorAccepted validatorVersion
      simplifiedModel originalModel certificate conflict
      binaryFingerprint buildReproducible
      baselineAvailable noClaimPath auditAppended auditAppendOnly ->
    ay_flpg_ReconstructionEvidence
      simplifiedCnf originalCnf simplifiedModel originalModel certificate conflict := by
  intro accepted
  exact accepted
    (ay_flpg_ReconstructionEvidence
      simplifiedCnf originalCnf simplifiedModel originalModel certificate conflict)
    (fun _fingerprint _probe _trail _propagation _conflict _forced
      _simplification reconstruct _eqsat _build _validator _fallback _audit =>
      reconstruct)

theorem ay_flpg_forced_literal_has_exact_failed_branch
    (probeLiteralLedger : Prop) (probeAccepted : Prop)
    (probeCoverage : Prop)
    (propagationTraceDigest : Prop) (propagationTraceAccepted : Prop)
    (propagationTraceManifest : Prop)
    (conflictWitness : Prop) (conflictAccepted : Prop)
    (conflictCoverage : Prop)
    (forcedLiteralLedger : Prop) (forcedLiteralAccepted : Prop)
    (forcedLiteralCoverage : Prop) :
    ay_flpg_ProbeLiteralLedger
      probeLiteralLedger probeAccepted probeCoverage ->
    ay_flpg_UnitPropagationTraceDigest
      propagationTraceDigest propagationTraceAccepted propagationTraceManifest ->
    ay_flpg_ConflictWitness conflictWitness conflictAccepted conflictCoverage ->
    ay_flpg_ForcedLiteralDerivationLedger
      forcedLiteralLedger forcedLiteralAccepted forcedLiteralCoverage ->
    probeLiteralLedger -> propagationTraceDigest -> conflictWitness ->
    forcedLiteralLedger ->
    ay_flpg_Conj probeAccepted
      (ay_flpg_Conj propagationTraceAccepted
        (ay_flpg_Conj conflictAccepted forcedLiteralAccepted)) := by
  intro probeOk propagationOk conflictOk forcedOk probe propagation conflict forced
  exact ay_flpg_conj_intro probeAccepted
    (ay_flpg_Conj propagationTraceAccepted
      (ay_flpg_Conj conflictAccepted forcedLiteralAccepted))
    (ay_flpg_probe_literal_ledger_applies
      probeLiteralLedger probeAccepted probeCoverage probeOk probe)
    (ay_flpg_conj_intro propagationTraceAccepted
      (ay_flpg_Conj conflictAccepted forcedLiteralAccepted)
      (ay_flpg_propagation_trace_digest_applies
        propagationTraceDigest propagationTraceAccepted propagationTraceManifest
        propagationOk propagation)
      (ay_flpg_conj_intro conflictAccepted forcedLiteralAccepted
        (ay_flpg_conflict_witness_applies
          conflictWitness conflictAccepted conflictCoverage conflictOk conflict)
        (ay_flpg_forced_literal_ledger_applies
          forcedLiteralLedger forcedLiteralAccepted forcedLiteralCoverage
          forcedOk forced)))

theorem ay_flpg_sat_pullback
    (originalCnf : Prop) (simplifiedCnf : Prop)
    (simplifiedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_flpg_ReconstructionEvidence
      simplifiedCnf originalCnf simplifiedModel originalModel certificate conflict ->
    ay_flpg_Sat simplifiedCnf simplifiedModel ->
    ay_flpg_Sat originalCnf originalModel := by
  intro witnesses satSimplified
  exact ay_flpg_model_reconstruction
    simplifiedCnf originalCnf simplifiedModel originalModel
    certificate conflict witnesses satSimplified

theorem ay_flpg_unsat_pushback
    (originalCnf : Prop) (simplifiedCnf : Prop)
    (simplifiedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_flpg_ReconstructionEvidence
      simplifiedCnf originalCnf simplifiedModel originalModel certificate conflict ->
    ay_flpg_Replay simplifiedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses replay
  exact ay_flpg_unsat_replay
    simplifiedCnf originalCnf simplifiedModel originalModel
    certificate conflict witnesses replay

theorem ay_flpg_public_sat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_flpg_ExitCodeSound exitCode (ay_flpg_Sat originalCnf originalModel) ->
    ay_flpg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro satSound
  exact ay_flpg_disj_left
    (ay_flpg_ExitCodeSound exitCode (ay_flpg_Sat originalCnf originalModel))
    (ay_flpg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    satSound

theorem ay_flpg_public_unsat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_flpg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_flpg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro unsatSound
  exact ay_flpg_disj_right
    (ay_flpg_ExitCodeSound exitCode (ay_flpg_Sat originalCnf originalModel))
    (ay_flpg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    unsatSound

theorem ay_flpg_failure_probe
    (probeMismatch trailMismatch propagationMismatch conflictMismatch : Prop)
    (forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    probeMismatch ->
    ay_flpg_FailedProbeGuardFailure
      probeMismatch trailMismatch propagationMismatch conflictMismatch
      forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result probe_case _trail_case _prop_case _conflict_case _forced_case
    _simplification_case _model_case _replay_case _build_case _validator_case
    _audit_case
  exact probe_case h

theorem ay_flpg_failure_trail
    (probeMismatch trailMismatch propagationMismatch conflictMismatch : Prop)
    (forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    trailMismatch ->
    ay_flpg_FailedProbeGuardFailure
      probeMismatch trailMismatch propagationMismatch conflictMismatch
      forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result _probe_case trail_case _prop_case _conflict_case _forced_case
    _simplification_case _model_case _replay_case _build_case _validator_case
    _audit_case
  exact trail_case h

theorem ay_flpg_failure_propagation
    (probeMismatch trailMismatch propagationMismatch conflictMismatch : Prop)
    (forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    propagationMismatch ->
    ay_flpg_FailedProbeGuardFailure
      probeMismatch trailMismatch propagationMismatch conflictMismatch
      forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result _probe_case _trail_case propagation_case _conflict_case
    _forced_case _simplification_case _model_case _replay_case _build_case
    _validator_case _audit_case
  exact propagation_case h

theorem ay_flpg_failure_conflict
    (probeMismatch trailMismatch propagationMismatch conflictMismatch : Prop)
    (forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    conflictMismatch ->
    ay_flpg_FailedProbeGuardFailure
      probeMismatch trailMismatch propagationMismatch conflictMismatch
      forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result _probe_case _trail_case _prop_case conflict_case _forced_case
    _simplification_case _model_case _replay_case _build_case _validator_case
    _audit_case
  exact conflict_case h

theorem ay_flpg_failure_forced_literal
    (probeMismatch trailMismatch propagationMismatch conflictMismatch : Prop)
    (forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    forcedLiteralMismatch ->
    ay_flpg_FailedProbeGuardFailure
      probeMismatch trailMismatch propagationMismatch conflictMismatch
      forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result _probe_case _trail_case _prop_case _conflict_case forced_case
    _simplification_case _model_case _replay_case _build_case _validator_case
    _audit_case
  exact forced_case h

theorem ay_flpg_failure_simplification
    (probeMismatch trailMismatch propagationMismatch conflictMismatch : Prop)
    (forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    simplificationMismatch ->
    ay_flpg_FailedProbeGuardFailure
      probeMismatch trailMismatch propagationMismatch conflictMismatch
      forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result _probe_case _trail_case _prop_case _conflict_case _forced_case
    simplification_case _model_case _replay_case _build_case _validator_case
    _audit_case
  exact simplification_case h

theorem ay_flpg_failure_model
    (probeMismatch trailMismatch propagationMismatch conflictMismatch : Prop)
    (forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    modelMismatch ->
    ay_flpg_FailedProbeGuardFailure
      probeMismatch trailMismatch propagationMismatch conflictMismatch
      forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result _probe_case _trail_case _prop_case _conflict_case _forced_case
    _simplification_case model_case _replay_case _build_case _validator_case
    _audit_case
  exact model_case h

theorem ay_flpg_failure_replay
    (probeMismatch trailMismatch propagationMismatch conflictMismatch : Prop)
    (forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    replayMismatch ->
    ay_flpg_FailedProbeGuardFailure
      probeMismatch trailMismatch propagationMismatch conflictMismatch
      forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result _probe_case _trail_case _prop_case _conflict_case _forced_case
    _simplification_case _model_case replay_case _build_case _validator_case
    _audit_case
  exact replay_case h

theorem ay_flpg_failure_build
    (probeMismatch trailMismatch propagationMismatch conflictMismatch : Prop)
    (forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    buildMismatch ->
    ay_flpg_FailedProbeGuardFailure
      probeMismatch trailMismatch propagationMismatch conflictMismatch
      forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result _probe_case _trail_case _prop_case _conflict_case _forced_case
    _simplification_case _model_case _replay_case build_case _validator_case
    _audit_case
  exact build_case h

theorem ay_flpg_failure_validator
    (probeMismatch trailMismatch propagationMismatch conflictMismatch : Prop)
    (forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    validatorMismatch ->
    ay_flpg_FailedProbeGuardFailure
      probeMismatch trailMismatch propagationMismatch conflictMismatch
      forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result _probe_case _trail_case _prop_case _conflict_case _forced_case
    _simplification_case _model_case _replay_case _build_case validator_case
    _audit_case
  exact validator_case h

theorem ay_flpg_failure_audit
    (probeMismatch trailMismatch propagationMismatch conflictMismatch : Prop)
    (forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    auditMismatch ->
    ay_flpg_FailedProbeGuardFailure
      probeMismatch trailMismatch propagationMismatch conflictMismatch
      forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result _probe_case _trail_case _prop_case _conflict_case _forced_case
    _simplification_case _model_case _replay_case _build_case _validator_case
    audit_case
  exact audit_case h

theorem ay_flpg_diagnostic_no_claim
    (currentCnf : Prop)
    (probeMismatch trailMismatch propagationMismatch conflictMismatch : Prop)
    (forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_flpg_DiagnosticFailedProbeGuard
      currentCnf probeMismatch trailMismatch propagationMismatch conflictMismatch
      forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch recompute diagnostic ->
    ay_flpg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard
  exact ay_flpg_conj_right
    (ay_flpg_RecomputeObligation currentCnf recompute)
    (ay_flpg_NoSemanticClaim diagnostic)
    (ay_flpg_conj_right
      (ay_flpg_FailedProbeGuardFailure
        probeMismatch trailMismatch propagationMismatch conflictMismatch
        forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch
        buildMismatch validatorMismatch auditMismatch)
      (ay_flpg_Conj
        (ay_flpg_RecomputeObligation currentCnf recompute)
        (ay_flpg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_flpg_diagnostic_recompute
    (currentCnf : Prop)
    (probeMismatch trailMismatch propagationMismatch conflictMismatch : Prop)
    (forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_flpg_DiagnosticFailedProbeGuard
      currentCnf probeMismatch trailMismatch propagationMismatch conflictMismatch
      forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch recompute diagnostic ->
    ay_flpg_RecomputeObligation currentCnf recompute := by
  intro diagnosticGuard
  exact ay_flpg_conj_left
    (ay_flpg_RecomputeObligation currentCnf recompute)
    (ay_flpg_NoSemanticClaim diagnostic)
    (ay_flpg_conj_right
      (ay_flpg_FailedProbeGuardFailure
        probeMismatch trailMismatch propagationMismatch conflictMismatch
        forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch
        buildMismatch validatorMismatch auditMismatch)
      (ay_flpg_Conj
        (ay_flpg_RecomputeObligation currentCnf recompute)
        (ay_flpg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_flpg_failed_guard_cannot_bless_public_result
    (currentCnf : Prop)
    (probeMismatch trailMismatch propagationMismatch conflictMismatch : Prop)
    (forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_flpg_DiagnosticFailedProbeGuard
      currentCnf probeMismatch trailMismatch propagationMismatch conflictMismatch
      forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch recompute diagnostic ->
    ay_flpg_PublicResult originalCnf model certificate conflict exitCode ->
    ay_flpg_Conj
      (ay_flpg_NoSemanticClaim diagnostic)
      (ay_flpg_RecomputeObligation currentCnf recompute) := by
  intro diagnosticGuard _publicResult
  exact ay_flpg_conj_intro
    (ay_flpg_NoSemanticClaim diagnostic)
    (ay_flpg_RecomputeObligation currentCnf recompute)
    (ay_flpg_diagnostic_no_claim
      currentCnf probeMismatch trailMismatch propagationMismatch conflictMismatch
      forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch recompute diagnostic
      diagnosticGuard)
    (ay_flpg_diagnostic_recompute
      currentCnf probeMismatch trailMismatch propagationMismatch conflictMismatch
      forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch recompute diagnostic
      diagnosticGuard)

theorem ay_flpg_failed_guard_cannot_bless_public_sat
    (currentCnf : Prop)
    (probeMismatch trailMismatch propagationMismatch conflictMismatch : Prop)
    (forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop) (exitCode : Prop) :
    ay_flpg_DiagnosticFailedProbeGuard
      currentCnf probeMismatch trailMismatch propagationMismatch conflictMismatch
      forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch recompute diagnostic ->
    ay_flpg_ExitCodeSound exitCode (ay_flpg_Sat originalCnf model) ->
    ay_flpg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _satClaim
  exact ay_flpg_diagnostic_no_claim
    currentCnf probeMismatch trailMismatch propagationMismatch conflictMismatch
    forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch
    buildMismatch validatorMismatch auditMismatch recompute diagnostic
    diagnosticGuard

theorem ay_flpg_failed_guard_cannot_bless_public_unsat
    (currentCnf : Prop)
    (probeMismatch trailMismatch propagationMismatch conflictMismatch : Prop)
    (forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (certificate : Prop) (conflict : Prop)
    (exitCode : Prop) :
    ay_flpg_DiagnosticFailedProbeGuard
      currentCnf probeMismatch trailMismatch propagationMismatch conflictMismatch
      forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch recompute diagnostic ->
    ay_flpg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_flpg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _unsatClaim
  exact ay_flpg_diagnostic_no_claim
    currentCnf probeMismatch trailMismatch propagationMismatch conflictMismatch
    forcedLiteralMismatch simplificationMismatch modelMismatch replayMismatch
    buildMismatch validatorMismatch auditMismatch recompute diagnostic
    diagnosticGuard
