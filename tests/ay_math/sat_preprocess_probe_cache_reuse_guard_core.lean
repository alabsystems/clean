-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Probe-cache reuse guard soundness.
-- The propositions stand for cache digests, cached assumption ledgers, implication-trail
-- digests, contradiction witnesses, derived unit/removed-clause coverage, reconstruction witnesses, fingerprint agreement, checker replay,
-- fallback/build/validator gates, audit transcripts, diagnostics, and public
-- SAT/UNSAT reports.

def ay_pcrg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pcrg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pcrg_Equisat (before : Prop) (after : Prop) :=
  ay_pcrg_Conj (before -> after) (after -> before)

def ay_pcrg_Sat (cnf : Prop) (model : Prop) :=
  ay_pcrg_Conj cnf model

def ay_pcrg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pcrg_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pcrg_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pcrg_ProbeCacheDigest
    (probeCache : Prop) (cacheDigest : Prop)
    (cacheDigestWitness : Prop) :=
  ay_pcrg_Conj cacheDigestWitness (probeCache -> cacheDigest)

def ay_pcrg_CachedAssumptionLedger
    (cachedAssumption : Prop) (cachedAssumptionWitness : Prop)
    (cachedAssumptionLedger : Prop) :=
  ay_pcrg_Conj cachedAssumptionLedger (cachedAssumption -> cachedAssumptionWitness)

def ay_pcrg_DerivedUnitRemovedClauseCoverage
    (derivedUnitOrRemovedClause : Prop) (coveredDerivedResult : Prop)
    (derivedCoverageWitness : Prop) :=
  ay_pcrg_Conj derivedCoverageWitness (derivedUnitOrRemovedClause -> coveredDerivedResult)

def ay_pcrg_ImplicationTrailDigest
    (implicationTrail : Prop) (trailDigest : Prop)
    (trailDigestWitness : Prop) :=
  ay_pcrg_Conj trailDigestWitness (implicationTrail -> trailDigest)

def ay_pcrg_ContradictionWitnessLedger
    (cachedAssumption : Prop) (contradictionWitness : Prop)
    (contradictionLedger : Prop) :=
  ay_pcrg_Conj contradictionLedger
    (cachedAssumption -> contradictionWitness)

def ay_pcrg_ModelReconstruction
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :=
  ay_pcrg_Sat replayedCnf replayedModel ->
    ay_pcrg_Sat originalCnf originalModel

def ay_pcrg_ProofReconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pcrg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pcrg_ReconstructionWitnesses
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pcrg_Conj
    (ay_pcrg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_pcrg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)

def ay_pcrg_FingerprintAgreement
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pcrg_Conj fingerprintWitness
    (ay_pcrg_IdMatch originalFingerprint replayedFingerprint)

def ay_pcrg_CheckerReplay
    (cachedAssumptionReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pcrg_Conj cachedAssumptionReplayCertificate checkerAccepted

def ay_pcrg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_pcrg_Conj baselineSolver baselineAvailable

def ay_pcrg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_pcrg_Conj binaryFingerprint buildReproducible

def ay_pcrg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_pcrg_Conj validatorAccepted validatorVersion

def ay_pcrg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_pcrg_Conj auditAppended auditAppendOnly

def ay_pcrg_AcceptedProbeCacheReuseGuard
    (originalCnf : Prop) (replayedCnf : Prop)
    (probeCache : Prop) (cacheDigest : Prop) (cacheDigestWitness : Prop)
    (cachedAssumption : Prop) (cachedAssumptionWitness : Prop) (cachedAssumptionLedger : Prop)
    (derivedUnitOrRemovedClause : Prop) (coveredDerivedResult : Prop)
    (derivedCoverageWitness : Prop)
    (implicationTrail : Prop) (trailDigest : Prop)
    (trailDigestWitness : Prop)
    (contradictionWitness : Prop) (contradictionLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (cachedAssumptionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_pcrg_ProbeCacheDigest
       probeCache cacheDigest cacheDigestWitness ->
     ay_pcrg_CachedAssumptionLedger
       cachedAssumption cachedAssumptionWitness cachedAssumptionLedger ->
     ay_pcrg_DerivedUnitRemovedClauseCoverage
       derivedUnitOrRemovedClause coveredDerivedResult derivedCoverageWitness ->
     ay_pcrg_ImplicationTrailDigest
       implicationTrail trailDigest trailDigestWitness ->
     ay_pcrg_ContradictionWitnessLedger
       cachedAssumption contradictionWitness contradictionLedger ->
     ay_pcrg_ReconstructionWitnesses
       replayedCnf originalCnf replayedModel originalModel
       certificate conflict ->
     ay_pcrg_Equisat originalCnf replayedCnf ->
     ay_pcrg_FingerprintAgreement
       originalFingerprint replayedFingerprint fingerprintWitness ->
     ay_pcrg_CheckerReplay cachedAssumptionReplayCertificate checkerAccepted ->
     ay_pcrg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_pcrg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_pcrg_ValidatorGate validatorAccepted validatorVersion ->
     ay_pcrg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_pcrg_ProbeCacheReuseGuardFailure
    (staleCacheDigest : Prop) (missingCachedAssumption : Prop)
    (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (staleCacheDigest -> result) ->
    (missingCachedAssumption -> result) ->
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

def ay_pcrg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pcrg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pcrg_Conj currentCnf recompute

def ay_pcrg_DiagnosticProbeCacheReuseGuard
    (currentCnf : Prop)
    (staleCacheDigest : Prop) (missingCachedAssumption : Prop)
    (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pcrg_Conj
    (ay_pcrg_ProbeCacheReuseGuardFailure
      staleCacheDigest missingCachedAssumption derivedCoverageGap trailDigestMismatch
      missingContradictionWitness reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction)
    (ay_pcrg_Conj
      (ay_pcrg_RecomputeObligation currentCnf recompute)
      (ay_pcrg_NoSemanticClaim diagnostic))

def ay_pcrg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pcrg_Conj exitCode claim

def ay_pcrg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pcrg_Disj
    (ay_pcrg_ExitCodeSound exitCode (ay_pcrg_Sat originalCnf model))
    (ay_pcrg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_pcrg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pcrg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pcrg_conj_left
    (left : Prop) (right : Prop) :
    ay_pcrg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pcrg_conj_right
    (left : Prop) (right : Prop) :
    ay_pcrg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pcrg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pcrg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pcrg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pcrg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pcrg_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pcrg_Equisat before after ->
    before -> after := by
  intro eqsat
  exact ay_pcrg_conj_left (before -> after) (after -> before) eqsat

theorem ay_pcrg_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pcrg_Equisat before after ->
    after -> before := by
  intro eqsat
  exact ay_pcrg_conj_right (before -> after) (after -> before) eqsat

theorem ay_pcrg_probe_cache_digest_applies
    (probeCache : Prop) (cacheDigest : Prop)
    (cacheDigestWitness : Prop) :
    ay_pcrg_ProbeCacheDigest
      probeCache cacheDigest cacheDigestWitness ->
    probeCache -> cacheDigest := by
  intro digest
  exact ay_pcrg_conj_right cacheDigestWitness
    (probeCache -> cacheDigest) digest

theorem ay_pcrg_cached_assumption_applies
    (cachedAssumption : Prop) (cachedAssumptionWitness : Prop)
    (cachedAssumptionLedger : Prop) :
    ay_pcrg_CachedAssumptionLedger
      cachedAssumption cachedAssumptionWitness cachedAssumptionLedger ->
    cachedAssumption -> cachedAssumptionWitness := by
  intro ledger
  exact ay_pcrg_conj_right cachedAssumptionLedger
    (cachedAssumption -> cachedAssumptionWitness) ledger

theorem ay_pcrg_derived_unit_removed_clause_coverage
    (derivedUnitOrRemovedClause : Prop) (coveredDerivedResult : Prop)
    (derivedCoverageWitness : Prop) :
    ay_pcrg_DerivedUnitRemovedClauseCoverage
      derivedUnitOrRemovedClause coveredDerivedResult derivedCoverageWitness ->
    derivedUnitOrRemovedClause -> coveredDerivedResult := by
  intro coverage
  exact ay_pcrg_conj_right derivedCoverageWitness
    (derivedUnitOrRemovedClause -> coveredDerivedResult) coverage

theorem ay_pcrg_implication_trail_digest_applies
    (implicationTrail : Prop) (trailDigest : Prop)
    (trailDigestWitness : Prop) :
    ay_pcrg_ImplicationTrailDigest
      implicationTrail trailDigest trailDigestWitness ->
    implicationTrail -> trailDigest := by
  intro extension
  exact ay_pcrg_conj_right trailDigestWitness
    (implicationTrail -> trailDigest) extension

theorem ay_pcrg_contradiction_witness_applies
    (cachedAssumption : Prop) (contradictionWitness : Prop)
    (contradictionLedger : Prop) :
    ay_pcrg_ContradictionWitnessLedger
      cachedAssumption contradictionWitness contradictionLedger ->
    cachedAssumption -> contradictionWitness := by
  intro ledger
  exact ay_pcrg_conj_right contradictionLedger
    (cachedAssumption -> contradictionWitness) ledger

theorem ay_pcrg_reconstruction_model
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pcrg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_pcrg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel := by
  intro witnesses
  exact ay_pcrg_conj_left
    (ay_pcrg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_pcrg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_pcrg_reconstruction_proof
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pcrg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_pcrg_ProofReconstruction
      originalCnf replayedCnf certificate conflict := by
  intro witnesses
  exact ay_pcrg_conj_right
    (ay_pcrg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_pcrg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_pcrg_accepted_equisat
    (originalCnf : Prop) (replayedCnf : Prop)
    (probeCache : Prop) (cacheDigest : Prop) (cacheDigestWitness : Prop)
    (cachedAssumption : Prop) (cachedAssumptionWitness : Prop) (cachedAssumptionLedger : Prop)
    (derivedUnitOrRemovedClause : Prop) (coveredDerivedResult : Prop)
    (derivedCoverageWitness : Prop)
    (implicationTrail : Prop) (trailDigest : Prop)
    (trailDigestWitness : Prop)
    (contradictionWitness : Prop) (contradictionLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (cachedAssumptionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pcrg_AcceptedProbeCacheReuseGuard
      originalCnf replayedCnf
      probeCache cacheDigest cacheDigestWitness
      cachedAssumption cachedAssumptionWitness cachedAssumptionLedger
      derivedUnitOrRemovedClause coveredDerivedResult derivedCoverageWitness
      implicationTrail trailDigest trailDigestWitness
      contradictionWitness contradictionLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      cachedAssumptionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pcrg_Equisat originalCnf replayedCnf := by
  intro accepted
  exact accepted (ay_pcrg_Equisat originalCnf replayedCnf)
    (fun _cache _assumption _coverage _trail _contradiction _reconstruct eqsat _fingerprint _checker
      _fallback _build _validator _audit => eqsat)

theorem ay_pcrg_accepted_checker_replay
    (originalCnf : Prop) (replayedCnf : Prop)
    (probeCache : Prop) (cacheDigest : Prop) (cacheDigestWitness : Prop)
    (cachedAssumption : Prop) (cachedAssumptionWitness : Prop) (cachedAssumptionLedger : Prop)
    (derivedUnitOrRemovedClause : Prop) (coveredDerivedResult : Prop)
    (derivedCoverageWitness : Prop)
    (implicationTrail : Prop) (trailDigest : Prop)
    (trailDigestWitness : Prop)
    (contradictionWitness : Prop) (contradictionLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (cachedAssumptionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pcrg_AcceptedProbeCacheReuseGuard
      originalCnf replayedCnf
      probeCache cacheDigest cacheDigestWitness
      cachedAssumption cachedAssumptionWitness cachedAssumptionLedger
      derivedUnitOrRemovedClause coveredDerivedResult derivedCoverageWitness
      implicationTrail trailDigest trailDigestWitness
      contradictionWitness contradictionLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      cachedAssumptionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pcrg_CheckerReplay cachedAssumptionReplayCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_pcrg_CheckerReplay cachedAssumptionReplayCertificate checkerAccepted)
    (fun _cache _assumption _coverage _trail _contradiction _reconstruct _eqsat _fingerprint checker
      _fallback _build _validator _audit => checker)

theorem ay_pcrg_accepted_audit_transcript
    (originalCnf : Prop) (replayedCnf : Prop)
    (probeCache : Prop) (cacheDigest : Prop) (cacheDigestWitness : Prop)
    (cachedAssumption : Prop) (cachedAssumptionWitness : Prop) (cachedAssumptionLedger : Prop)
    (derivedUnitOrRemovedClause : Prop) (coveredDerivedResult : Prop)
    (derivedCoverageWitness : Prop)
    (implicationTrail : Prop) (trailDigest : Prop)
    (trailDigestWitness : Prop)
    (contradictionWitness : Prop) (contradictionLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (cachedAssumptionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pcrg_AcceptedProbeCacheReuseGuard
      originalCnf replayedCnf
      probeCache cacheDigest cacheDigestWitness
      cachedAssumption cachedAssumptionWitness cachedAssumptionLedger
      derivedUnitOrRemovedClause coveredDerivedResult derivedCoverageWitness
      implicationTrail trailDigest trailDigestWitness
      contradictionWitness contradictionLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      cachedAssumptionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pcrg_AuditTranscript auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_pcrg_AuditTranscript auditAppended auditAppendOnly)
    (fun _cache _assumption _coverage _trail _contradiction _reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator audit => audit)

theorem ay_pcrg_sat_pullback
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :
    ay_pcrg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel ->
    ay_pcrg_Sat replayedCnf replayedModel ->
    ay_pcrg_Sat originalCnf originalModel := by
  intro reconstruct replayedSat
  exact reconstruct replayedSat

theorem ay_pcrg_unsat_pushback
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pcrg_ProofReconstruction
      originalCnf replayedCnf certificate conflict ->
    ay_pcrg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruct replayedReplay
  exact reconstruct replayedReplay

theorem ay_pcrg_public_sat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (probeCache : Prop) (cacheDigest : Prop) (cacheDigestWitness : Prop)
    (cachedAssumption : Prop) (cachedAssumptionWitness : Prop) (cachedAssumptionLedger : Prop)
    (derivedUnitOrRemovedClause : Prop) (coveredDerivedResult : Prop)
    (derivedCoverageWitness : Prop)
    (implicationTrail : Prop) (trailDigest : Prop)
    (trailDigestWitness : Prop)
    (contradictionWitness : Prop) (contradictionLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (cachedAssumptionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_pcrg_AcceptedProbeCacheReuseGuard
      originalCnf replayedCnf
      probeCache cacheDigest cacheDigestWitness
      cachedAssumption cachedAssumptionWitness cachedAssumptionLedger
      derivedUnitOrRemovedClause coveredDerivedResult derivedCoverageWitness
      implicationTrail trailDigest trailDigestWitness
      contradictionWitness contradictionLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      cachedAssumptionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pcrg_Sat replayedCnf replayedModel ->
    exitCode ->
    ay_pcrg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedSat hexit
  exact accepted
    (ay_pcrg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _cache _assumption _coverage _trail _contradiction reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator _audit =>
      ay_pcrg_disj_left
        (ay_pcrg_ExitCodeSound exitCode
          (ay_pcrg_Sat originalCnf originalModel))
        (ay_pcrg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_pcrg_conj_intro exitCode
          (ay_pcrg_Sat originalCnf originalModel)
          hexit
          ((ay_pcrg_reconstruction_model
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedSat)))

theorem ay_pcrg_public_unsat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (probeCache : Prop) (cacheDigest : Prop) (cacheDigestWitness : Prop)
    (cachedAssumption : Prop) (cachedAssumptionWitness : Prop) (cachedAssumptionLedger : Prop)
    (derivedUnitOrRemovedClause : Prop) (coveredDerivedResult : Prop)
    (derivedCoverageWitness : Prop)
    (implicationTrail : Prop) (trailDigest : Prop)
    (trailDigestWitness : Prop)
    (contradictionWitness : Prop) (contradictionLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (cachedAssumptionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_pcrg_AcceptedProbeCacheReuseGuard
      originalCnf replayedCnf
      probeCache cacheDigest cacheDigestWitness
      cachedAssumption cachedAssumptionWitness cachedAssumptionLedger
      derivedUnitOrRemovedClause coveredDerivedResult derivedCoverageWitness
      implicationTrail trailDigest trailDigestWitness
      contradictionWitness contradictionLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      cachedAssumptionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pcrg_Replay replayedCnf certificate conflict ->
    exitCode ->
    ay_pcrg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedReplay hexit
  exact accepted
    (ay_pcrg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _cache _assumption _coverage _trail _contradiction reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator _audit =>
      ay_pcrg_disj_right
        (ay_pcrg_ExitCodeSound exitCode
          (ay_pcrg_Sat originalCnf originalModel))
        (ay_pcrg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_pcrg_conj_intro exitCode
          (certificate -> originalCnf -> conflict)
          hexit
          ((ay_pcrg_reconstruction_proof
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedReplay)))

theorem ay_pcrg_failure_stale_cache_digest
    (staleCacheDigest : Prop) (missingCachedAssumption : Prop)
    (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleCacheDigest ->
    ay_pcrg_ProbeCacheReuseGuardFailure
      staleCacheDigest missingCachedAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result cache_case _assumption_case _coverage_case _trail_case
    _contradiction_case _reconstruction_case _fingerprint_case _replay_case
    _baseline_case _build_case _validator_case _audit_case
  exact cache_case failure

theorem ay_pcrg_failure_missing_cached_assumption
    (staleCacheDigest : Prop) (missingCachedAssumption : Prop)
    (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingCachedAssumption ->
    ay_pcrg_ProbeCacheReuseGuardFailure
      staleCacheDigest missingCachedAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _cache_case witness_case _coverage_case _trail_case _contradiction_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact witness_case failure

theorem ay_pcrg_failure_derived_coverage
    (staleCacheDigest : Prop) (missingCachedAssumption : Prop)
    (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    derivedCoverageGap ->
    ay_pcrg_ProbeCacheReuseGuardFailure
      staleCacheDigest missingCachedAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _cache_case _witness_case coverage_case _trail_case _contradiction_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact coverage_case failure

theorem ay_pcrg_failure_trail_digest
    (staleCacheDigest : Prop) (missingCachedAssumption : Prop)
    (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    trailDigestMismatch ->
    ay_pcrg_ProbeCacheReuseGuardFailure
      staleCacheDigest missingCachedAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _cache_case _witness_case _coverage_case trail_case _contradiction_case
    _reconstruction_case _fingerprint_case _replay_case _baseline_case
    _build_case _validator_case _audit_case
  exact trail_case failure

theorem ay_pcrg_failure_missing_contradiction_witness
    (staleCacheDigest : Prop) (missingCachedAssumption : Prop)
    (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingContradictionWitness ->
    ay_pcrg_ProbeCacheReuseGuardFailure
      staleCacheDigest missingCachedAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _cache_case _witness_case _coverage_case _trail_case contradiction_case
    _reconstruction_case _fingerprint_case _replay_case _baseline_case
    _build_case _validator_case _audit_case
  exact contradiction_case failure

theorem ay_pcrg_failure_reconstruction
    (staleCacheDigest : Prop) (missingCachedAssumption : Prop)
    (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_pcrg_ProbeCacheReuseGuardFailure
      staleCacheDigest missingCachedAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _cache_case _witness_case _coverage_case _trail_case _contradiction_case reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case failure

theorem ay_pcrg_failure_stale_fingerprint
    (staleCacheDigest : Prop) (missingCachedAssumption : Prop)
    (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_pcrg_ProbeCacheReuseGuardFailure
      staleCacheDigest missingCachedAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _cache_case _witness_case _coverage_case _trail_case _contradiction_case _reconstruction_case
    fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact fingerprint_case failure

theorem ay_pcrg_failure_unchecked_replay
    (staleCacheDigest : Prop) (missingCachedAssumption : Prop)
    (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_pcrg_ProbeCacheReuseGuardFailure
      staleCacheDigest missingCachedAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _cache_case _witness_case _coverage_case _trail_case _contradiction_case _reconstruction_case
    _fingerprint_case replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact replay_case failure

theorem ay_pcrg_failure_missing_baseline
    (staleCacheDigest : Prop) (missingCachedAssumption : Prop)
    (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingBaseline ->
    ay_pcrg_ProbeCacheReuseGuardFailure
      staleCacheDigest missingCachedAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _cache_case _witness_case _coverage_case _trail_case _contradiction_case _reconstruction_case
    _fingerprint_case _replay_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case failure

theorem ay_pcrg_failure_build
    (staleCacheDigest : Prop) (missingCachedAssumption : Prop)
    (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_pcrg_ProbeCacheReuseGuardFailure
      staleCacheDigest missingCachedAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _cache_case _witness_case _coverage_case _trail_case _contradiction_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case failure

theorem ay_pcrg_failure_validator
    (staleCacheDigest : Prop) (missingCachedAssumption : Prop)
    (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    validatorFailure ->
    ay_pcrg_ProbeCacheReuseGuardFailure
      staleCacheDigest missingCachedAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _cache_case _witness_case _coverage_case _trail_case _contradiction_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case failure

theorem ay_pcrg_failure_audit
    (staleCacheDigest : Prop) (missingCachedAssumption : Prop)
    (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_pcrg_ProbeCacheReuseGuardFailure
      staleCacheDigest missingCachedAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _cache_case _witness_case _coverage_case _trail_case _contradiction_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case failure

theorem ay_pcrg_diagnostic_no_claim
    (currentCnf : Prop)
    (staleCacheDigest : Prop) (missingCachedAssumption : Prop)
    (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pcrg_DiagnosticProbeCacheReuseGuard
      currentCnf staleCacheDigest missingCachedAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_pcrg_NoSemanticClaim diagnostic := by
  intro diagnosticBundle
  exact ay_pcrg_conj_right
    (ay_pcrg_RecomputeObligation currentCnf recompute)
    (ay_pcrg_NoSemanticClaim diagnostic)
    (ay_pcrg_conj_right
      (ay_pcrg_ProbeCacheReuseGuardFailure
        staleCacheDigest missingCachedAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_pcrg_Conj
        (ay_pcrg_RecomputeObligation currentCnf recompute)
        (ay_pcrg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_pcrg_diagnostic_recompute
    (currentCnf : Prop)
    (staleCacheDigest : Prop) (missingCachedAssumption : Prop)
    (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pcrg_DiagnosticProbeCacheReuseGuard
      currentCnf staleCacheDigest missingCachedAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_pcrg_RecomputeObligation currentCnf recompute := by
  intro diagnosticBundle
  exact ay_pcrg_conj_left
    (ay_pcrg_RecomputeObligation currentCnf recompute)
    (ay_pcrg_NoSemanticClaim diagnostic)
    (ay_pcrg_conj_right
      (ay_pcrg_ProbeCacheReuseGuardFailure
        staleCacheDigest missingCachedAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_pcrg_Conj
        (ay_pcrg_RecomputeObligation currentCnf recompute)
        (ay_pcrg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_pcrg_unchecked_cache_reuse_cannot_bless_public_result
    (currentCnf : Prop)
    (staleCacheDigest : Prop) (missingCachedAssumption : Prop)
    (derivedCoverageGap : Prop)
    (trailDigestMismatch : Prop)
    (missingContradictionWitness : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_pcrg_DiagnosticProbeCacheReuseGuard
      currentCnf staleCacheDigest missingCachedAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_pcrg_Conj
      (ay_pcrg_NoSemanticClaim diagnostic)
      (ay_pcrg_RecomputeObligation currentCnf recompute) := by
  intro _unchecked diagnosticBundle
  exact ay_pcrg_conj_intro
    (ay_pcrg_NoSemanticClaim diagnostic)
    (ay_pcrg_RecomputeObligation currentCnf recompute)
    (ay_pcrg_diagnostic_no_claim
      currentCnf staleCacheDigest missingCachedAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
    (ay_pcrg_diagnostic_recompute
      currentCnf staleCacheDigest missingCachedAssumption derivedCoverageGap trailDigestMismatch missingContradictionWitness reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
