-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Failed-literal probing replay guard soundness.
-- The propositions stand for probe assumption ledgers, implication-trail digests, contradiction
-- witnesses, derived unit/removed-clause coverage, reconstruction witnesses, fingerprint agreement, checker replay,
-- fallback/build/validator gates, audit transcripts, diagnostics, and public
-- SAT/UNSAT reports.

def ay_flpg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_flpg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_flpg_Equisat (before : Prop) (after : Prop) :=
  ay_flpg_Conj (before -> after) (after -> before)

def ay_flpg_Sat (cnf : Prop) (model : Prop) :=
  ay_flpg_Conj cnf model

def ay_flpg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_flpg_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_flpg_Conj (leftId -> rightId) (rightId -> leftId)

def ay_flpg_ProbeAssumptionLedger
    (probeAssumption : Prop) (assumptionWitness : Prop)
    (assumptionLedger : Prop) :=
  ay_flpg_Conj assumptionLedger (probeAssumption -> assumptionWitness)

def ay_flpg_DerivedUnitRemovedClauseCoverage
    (derivedUnitOrRemovedClause : Prop) (coveredDerivedResult : Prop)
    (derivedCoverageWitness : Prop) :=
  ay_flpg_Conj derivedCoverageWitness (derivedUnitOrRemovedClause -> coveredDerivedResult)

def ay_flpg_ImplicationTrailDigest
    (implicationTrail : Prop) (trailDigest : Prop)
    (trailDigestWitness : Prop) :=
  ay_flpg_Conj trailDigestWitness (implicationTrail -> trailDigest)

def ay_flpg_ContradictionWitnessLedger
    (probeAssumption : Prop) (contradictionWitness : Prop)
    (contradictionLedger : Prop) :=
  ay_flpg_Conj contradictionLedger
    (probeAssumption -> contradictionWitness)

def ay_flpg_ModelReconstruction
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :=
  ay_flpg_Sat replayedCnf replayedModel ->
    ay_flpg_Sat originalCnf originalModel

def ay_flpg_ProofReconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_flpg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_flpg_ReconstructionWitnesses
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_flpg_Conj
    (ay_flpg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_flpg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)

def ay_flpg_FingerprintAgreement
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_flpg_Conj fingerprintWitness
    (ay_flpg_IdMatch originalFingerprint replayedFingerprint)

def ay_flpg_CheckerReplay
    (probeAssumptionReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_flpg_Conj probeAssumptionReplayCertificate checkerAccepted

def ay_flpg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_flpg_Conj baselineSolver baselineAvailable

def ay_flpg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_flpg_Conj binaryFingerprint buildReproducible

def ay_flpg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_flpg_Conj validatorAccepted validatorVersion

def ay_flpg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_flpg_Conj auditAppended auditAppendOnly

def ay_flpg_AcceptedFailedLiteralProbeReplayGuard
    (originalCnf : Prop) (replayedCnf : Prop)
    (probeAssumption : Prop) (assumptionWitness : Prop) (assumptionLedger : Prop)
    (derivedUnitOrRemovedClause : Prop) (coveredDerivedResult : Prop)
    (derivedCoverageWitness : Prop)
    (implicationTrail : Prop) (trailDigest : Prop)
    (trailDigestWitness : Prop)
    (contradictionWitness : Prop) (contradictionLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (probeAssumptionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_flpg_ProbeAssumptionLedger
       probeAssumption assumptionWitness assumptionLedger ->
     ay_flpg_DerivedUnitRemovedClauseCoverage
       derivedUnitOrRemovedClause coveredDerivedResult derivedCoverageWitness ->
     ay_flpg_ImplicationTrailDigest
       implicationTrail trailDigest trailDigestWitness ->
     ay_flpg_ContradictionWitnessLedger
       probeAssumption contradictionWitness contradictionLedger ->
     ay_flpg_ReconstructionWitnesses
       replayedCnf originalCnf replayedModel originalModel
       certificate conflict ->
     ay_flpg_Equisat originalCnf replayedCnf ->
     ay_flpg_FingerprintAgreement
       originalFingerprint replayedFingerprint fingerprintWitness ->
     ay_flpg_CheckerReplay probeAssumptionReplayCertificate checkerAccepted ->
     ay_flpg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_flpg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_flpg_ValidatorGate validatorAccepted validatorVersion ->
     ay_flpg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_flpg_FailedLiteralProbeReplayGuardFailure
    (missingProbeAssumption : Prop) (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (missingProbeAssumption -> result) ->
    (derivedCoverageGap -> result) ->
    (trailDigestMismatch -> result) ->
    (missingContradictionWitness -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (missingBaseline -> result) ->
    (buildDrift -> result) ->
    (validatorFailure -> result) ->
    (auditContradiction -> result) ->
    result

def ay_flpg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_flpg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_flpg_Conj currentCnf recompute

def ay_flpg_DiagnosticFailedLiteralProbeReplayGuard
    (currentCnf : Prop)
    (missingProbeAssumption : Prop) (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_flpg_Conj
    (ay_flpg_FailedLiteralProbeReplayGuardFailure
      missingProbeAssumption derivedCoverageGap trailDigestMismatch
      missingContradictionWitness reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction)
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
    (before : Prop) (after : Prop) :
    ay_flpg_Equisat before after ->
    before -> after := by
  intro eqsat
  exact ay_flpg_conj_left (before -> after) (after -> before) eqsat

theorem ay_flpg_equisat_backward
    (before : Prop) (after : Prop) :
    ay_flpg_Equisat before after ->
    after -> before := by
  intro eqsat
  exact ay_flpg_conj_right (before -> after) (after -> before) eqsat

theorem ay_flpg_probe_assumption_applies
    (probeAssumption : Prop) (assumptionWitness : Prop)
    (assumptionLedger : Prop) :
    ay_flpg_ProbeAssumptionLedger
      probeAssumption assumptionWitness assumptionLedger ->
    probeAssumption -> assumptionWitness := by
  intro ledger
  exact ay_flpg_conj_right assumptionLedger
    (probeAssumption -> assumptionWitness) ledger

theorem ay_flpg_derived_unit_removed_clause_coverage
    (derivedUnitOrRemovedClause : Prop) (coveredDerivedResult : Prop)
    (derivedCoverageWitness : Prop) :
    ay_flpg_DerivedUnitRemovedClauseCoverage
      derivedUnitOrRemovedClause coveredDerivedResult derivedCoverageWitness ->
    derivedUnitOrRemovedClause -> coveredDerivedResult := by
  intro coverage
  exact ay_flpg_conj_right derivedCoverageWitness
    (derivedUnitOrRemovedClause -> coveredDerivedResult) coverage

theorem ay_flpg_implication_trail_digest_applies
    (implicationTrail : Prop) (trailDigest : Prop)
    (trailDigestWitness : Prop) :
    ay_flpg_ImplicationTrailDigest
      implicationTrail trailDigest trailDigestWitness ->
    implicationTrail -> trailDigest := by
  intro extension
  exact ay_flpg_conj_right trailDigestWitness
    (implicationTrail -> trailDigest) extension

theorem ay_flpg_contradiction_witness_applies
    (probeAssumption : Prop) (contradictionWitness : Prop)
    (contradictionLedger : Prop) :
    ay_flpg_ContradictionWitnessLedger
      probeAssumption contradictionWitness contradictionLedger ->
    probeAssumption -> contradictionWitness := by
  intro ledger
  exact ay_flpg_conj_right contradictionLedger
    (probeAssumption -> contradictionWitness) ledger

theorem ay_flpg_reconstruction_model
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_flpg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_flpg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel := by
  intro witnesses
  exact ay_flpg_conj_left
    (ay_flpg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_flpg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_flpg_reconstruction_proof
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_flpg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_flpg_ProofReconstruction
      originalCnf replayedCnf certificate conflict := by
  intro witnesses
  exact ay_flpg_conj_right
    (ay_flpg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_flpg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_flpg_accepted_equisat
    (originalCnf : Prop) (replayedCnf : Prop)
    (probeAssumption : Prop) (assumptionWitness : Prop) (assumptionLedger : Prop)
    (derivedUnitOrRemovedClause : Prop) (coveredDerivedResult : Prop)
    (derivedCoverageWitness : Prop)
    (implicationTrail : Prop) (trailDigest : Prop)
    (trailDigestWitness : Prop)
    (contradictionWitness : Prop) (contradictionLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (probeAssumptionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_flpg_AcceptedFailedLiteralProbeReplayGuard
      originalCnf replayedCnf
      probeAssumption assumptionWitness assumptionLedger
      derivedUnitOrRemovedClause coveredDerivedResult derivedCoverageWitness
      implicationTrail trailDigest trailDigestWitness
      contradictionWitness contradictionLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      probeAssumptionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_flpg_Equisat originalCnf replayedCnf := by
  intro accepted
  exact accepted (ay_flpg_Equisat originalCnf replayedCnf)
    (fun _assumption _coverage _trail _contradiction _reconstruct eqsat _fingerprint _checker
      _fallback _build _validator _audit => eqsat)

theorem ay_flpg_accepted_checker_replay
    (originalCnf : Prop) (replayedCnf : Prop)
    (probeAssumption : Prop) (assumptionWitness : Prop) (assumptionLedger : Prop)
    (derivedUnitOrRemovedClause : Prop) (coveredDerivedResult : Prop)
    (derivedCoverageWitness : Prop)
    (implicationTrail : Prop) (trailDigest : Prop)
    (trailDigestWitness : Prop)
    (contradictionWitness : Prop) (contradictionLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (probeAssumptionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_flpg_AcceptedFailedLiteralProbeReplayGuard
      originalCnf replayedCnf
      probeAssumption assumptionWitness assumptionLedger
      derivedUnitOrRemovedClause coveredDerivedResult derivedCoverageWitness
      implicationTrail trailDigest trailDigestWitness
      contradictionWitness contradictionLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      probeAssumptionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_flpg_CheckerReplay probeAssumptionReplayCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_flpg_CheckerReplay probeAssumptionReplayCertificate checkerAccepted)
    (fun _assumption _coverage _trail _contradiction _reconstruct _eqsat _fingerprint checker
      _fallback _build _validator _audit => checker)

theorem ay_flpg_accepted_audit_transcript
    (originalCnf : Prop) (replayedCnf : Prop)
    (probeAssumption : Prop) (assumptionWitness : Prop) (assumptionLedger : Prop)
    (derivedUnitOrRemovedClause : Prop) (coveredDerivedResult : Prop)
    (derivedCoverageWitness : Prop)
    (implicationTrail : Prop) (trailDigest : Prop)
    (trailDigestWitness : Prop)
    (contradictionWitness : Prop) (contradictionLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (probeAssumptionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_flpg_AcceptedFailedLiteralProbeReplayGuard
      originalCnf replayedCnf
      probeAssumption assumptionWitness assumptionLedger
      derivedUnitOrRemovedClause coveredDerivedResult derivedCoverageWitness
      implicationTrail trailDigest trailDigestWitness
      contradictionWitness contradictionLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      probeAssumptionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_flpg_AuditTranscript auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_flpg_AuditTranscript auditAppended auditAppendOnly)
    (fun _assumption _coverage _trail _contradiction _reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator audit => audit)

theorem ay_flpg_sat_pullback
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :
    ay_flpg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel ->
    ay_flpg_Sat replayedCnf replayedModel ->
    ay_flpg_Sat originalCnf originalModel := by
  intro reconstruct replayedSat
  exact reconstruct replayedSat

theorem ay_flpg_unsat_pushback
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_flpg_ProofReconstruction
      originalCnf replayedCnf certificate conflict ->
    ay_flpg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruct replayedReplay
  exact reconstruct replayedReplay

theorem ay_flpg_public_sat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (probeAssumption : Prop) (assumptionWitness : Prop) (assumptionLedger : Prop)
    (derivedUnitOrRemovedClause : Prop) (coveredDerivedResult : Prop)
    (derivedCoverageWitness : Prop)
    (implicationTrail : Prop) (trailDigest : Prop)
    (trailDigestWitness : Prop)
    (contradictionWitness : Prop) (contradictionLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (probeAssumptionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_flpg_AcceptedFailedLiteralProbeReplayGuard
      originalCnf replayedCnf
      probeAssumption assumptionWitness assumptionLedger
      derivedUnitOrRemovedClause coveredDerivedResult derivedCoverageWitness
      implicationTrail trailDigest trailDigestWitness
      contradictionWitness contradictionLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      probeAssumptionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_flpg_Sat replayedCnf replayedModel ->
    exitCode ->
    ay_flpg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedSat hexit
  exact accepted
    (ay_flpg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _assumption _coverage _trail _contradiction reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator _audit =>
      ay_flpg_disj_left
        (ay_flpg_ExitCodeSound exitCode
          (ay_flpg_Sat originalCnf originalModel))
        (ay_flpg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_flpg_conj_intro exitCode
          (ay_flpg_Sat originalCnf originalModel)
          hexit
          ((ay_flpg_reconstruction_model
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedSat)))

theorem ay_flpg_public_unsat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (probeAssumption : Prop) (assumptionWitness : Prop) (assumptionLedger : Prop)
    (derivedUnitOrRemovedClause : Prop) (coveredDerivedResult : Prop)
    (derivedCoverageWitness : Prop)
    (implicationTrail : Prop) (trailDigest : Prop)
    (trailDigestWitness : Prop)
    (contradictionWitness : Prop) (contradictionLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (probeAssumptionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_flpg_AcceptedFailedLiteralProbeReplayGuard
      originalCnf replayedCnf
      probeAssumption assumptionWitness assumptionLedger
      derivedUnitOrRemovedClause coveredDerivedResult derivedCoverageWitness
      implicationTrail trailDigest trailDigestWitness
      contradictionWitness contradictionLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      probeAssumptionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_flpg_Replay replayedCnf certificate conflict ->
    exitCode ->
    ay_flpg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedReplay hexit
  exact accepted
    (ay_flpg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _assumption _coverage _trail _contradiction reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator _audit =>
      ay_flpg_disj_right
        (ay_flpg_ExitCodeSound exitCode
          (ay_flpg_Sat originalCnf originalModel))
        (ay_flpg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_flpg_conj_intro exitCode
          (certificate -> originalCnf -> conflict)
          hexit
          ((ay_flpg_reconstruction_proof
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedReplay)))

theorem ay_flpg_failure_missing_probe_assumption
    (missingProbeAssumption : Prop) (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingProbeAssumption ->
    ay_flpg_FailedLiteralProbeReplayGuardFailure
      missingProbeAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result witness_case _coverage_case _trail_case _contradiction_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact witness_case failure

theorem ay_flpg_failure_derived_coverage
    (missingProbeAssumption : Prop) (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    derivedCoverageGap ->
    ay_flpg_FailedLiteralProbeReplayGuardFailure
      missingProbeAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case coverage_case _trail_case _contradiction_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact coverage_case failure

theorem ay_flpg_failure_trail_digest
    (missingProbeAssumption : Prop) (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    trailDigestMismatch ->
    ay_flpg_FailedLiteralProbeReplayGuardFailure
      missingProbeAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _coverage_case trail_case _contradiction_case
    _reconstruction_case _fingerprint_case _replay_case _baseline_case
    _build_case _validator_case _audit_case
  exact trail_case failure

theorem ay_flpg_failure_missing_contradiction_witness
    (missingProbeAssumption : Prop) (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingContradictionWitness ->
    ay_flpg_FailedLiteralProbeReplayGuardFailure
      missingProbeAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _coverage_case _trail_case contradiction_case
    _reconstruction_case _fingerprint_case _replay_case _baseline_case
    _build_case _validator_case _audit_case
  exact contradiction_case failure

theorem ay_flpg_failure_reconstruction
    (missingProbeAssumption : Prop) (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_flpg_FailedLiteralProbeReplayGuardFailure
      missingProbeAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _coverage_case _trail_case _contradiction_case reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case failure

theorem ay_flpg_failure_stale_fingerprint
    (missingProbeAssumption : Prop) (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_flpg_FailedLiteralProbeReplayGuardFailure
      missingProbeAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _coverage_case _trail_case _contradiction_case _reconstruction_case
    fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact fingerprint_case failure

theorem ay_flpg_failure_unchecked_replay
    (missingProbeAssumption : Prop) (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_flpg_FailedLiteralProbeReplayGuardFailure
      missingProbeAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _coverage_case _trail_case _contradiction_case _reconstruction_case
    _fingerprint_case replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact replay_case failure

theorem ay_flpg_failure_missing_baseline
    (missingProbeAssumption : Prop) (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingBaseline ->
    ay_flpg_FailedLiteralProbeReplayGuardFailure
      missingProbeAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _coverage_case _trail_case _contradiction_case _reconstruction_case
    _fingerprint_case _replay_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case failure

theorem ay_flpg_failure_build
    (missingProbeAssumption : Prop) (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_flpg_FailedLiteralProbeReplayGuardFailure
      missingProbeAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _coverage_case _trail_case _contradiction_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case failure

theorem ay_flpg_failure_validator
    (missingProbeAssumption : Prop) (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    validatorFailure ->
    ay_flpg_FailedLiteralProbeReplayGuardFailure
      missingProbeAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _coverage_case _trail_case _contradiction_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case failure

theorem ay_flpg_failure_audit
    (missingProbeAssumption : Prop) (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_flpg_FailedLiteralProbeReplayGuardFailure
      missingProbeAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _coverage_case _trail_case _contradiction_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case failure

theorem ay_flpg_diagnostic_no_claim
    (currentCnf : Prop)
    (missingProbeAssumption : Prop) (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_flpg_DiagnosticFailedLiteralProbeReplayGuard
      currentCnf missingProbeAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_flpg_NoSemanticClaim diagnostic := by
  intro diagnosticBundle
  exact ay_flpg_conj_right
    (ay_flpg_RecomputeObligation currentCnf recompute)
    (ay_flpg_NoSemanticClaim diagnostic)
    (ay_flpg_conj_right
      (ay_flpg_FailedLiteralProbeReplayGuardFailure
        missingProbeAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_flpg_Conj
        (ay_flpg_RecomputeObligation currentCnf recompute)
        (ay_flpg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_flpg_diagnostic_recompute
    (currentCnf : Prop)
    (missingProbeAssumption : Prop) (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_flpg_DiagnosticFailedLiteralProbeReplayGuard
      currentCnf missingProbeAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_flpg_RecomputeObligation currentCnf recompute := by
  intro diagnosticBundle
  exact ay_flpg_conj_left
    (ay_flpg_RecomputeObligation currentCnf recompute)
    (ay_flpg_NoSemanticClaim diagnostic)
    (ay_flpg_conj_right
      (ay_flpg_FailedLiteralProbeReplayGuardFailure
        missingProbeAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_flpg_Conj
        (ay_flpg_RecomputeObligation currentCnf recompute)
        (ay_flpg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_flpg_unchecked_probe_cannot_bless_public_result
    (currentCnf : Prop)
    (missingProbeAssumption : Prop) (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_flpg_DiagnosticFailedLiteralProbeReplayGuard
      currentCnf missingProbeAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_flpg_Conj
      (ay_flpg_NoSemanticClaim diagnostic)
      (ay_flpg_RecomputeObligation currentCnf recompute) := by
  intro _unchecked diagnosticBundle
  exact ay_flpg_conj_intro
    (ay_flpg_NoSemanticClaim diagnostic)
    (ay_flpg_RecomputeObligation currentCnf recompute)
    (ay_flpg_diagnostic_no_claim
      currentCnf missingProbeAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
    (ay_flpg_diagnostic_recompute
      currentCnf missingProbeAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
