-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Symmetry-breaking guard soundness.
-- The propositions stand for symmetry-generator manifests, orbit/representative witnesses, added-constraint
-- coverage digests, model reconstruction maps, reconstruction witnesses, fingerprint agreement, checker replay,
-- fallback/build/validator gates, audit transcripts, diagnostics, and public
-- SAT/UNSAT reports.

def ay_sbyg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_sbyg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_sbyg_Equisat (before : Prop) (after : Prop) :=
  ay_sbyg_Conj (before -> after) (after -> before)

def ay_sbyg_Sat (cnf : Prop) (model : Prop) :=
  ay_sbyg_Conj cnf model

def ay_sbyg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_sbyg_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_sbyg_Conj (leftId -> rightId) (rightId -> leftId)

def ay_sbyg_SymmetryGeneratorManifest
    (symmetryGenerators : Prop) (generatorManifestAccepted : Prop)
    (symmetryGeneratorsManifest : Prop) :=
  ay_sbyg_Conj symmetryGeneratorsManifest (symmetryGenerators -> generatorManifestAccepted)

def ay_sbyg_OrbitRepresentativeWitness
    (orbitRepresentativeSet : Prop) (orbitRepresentativeAccepted : Prop)
    (orbitRepresentativeWitness : Prop) :=
  ay_sbyg_Conj orbitRepresentativeWitness (orbitRepresentativeSet -> orbitRepresentativeAccepted)

def ay_sbyg_AddedConstraintCoverageDigest
    (addedConstraintSet : Prop) (addedConstraintCoverageAccepted : Prop)
    (addedConstraintCoverageWitness : Prop) :=
  ay_sbyg_Conj addedConstraintCoverageWitness (addedConstraintSet -> addedConstraintCoverageAccepted)

def ay_sbyg_ReducedSolutionModelMap
    (reducedSolution : Prop) (originalSolution : Prop)
    (modelReconstructionMap : Prop) :=
  ay_sbyg_Conj modelReconstructionMap (reducedSolution -> originalSolution)

def ay_sbyg_ModelReconstruction
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :=
  ay_sbyg_Sat replayedCnf replayedModel ->
    ay_sbyg_Sat originalCnf originalModel

def ay_sbyg_ProofReconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_sbyg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_sbyg_ReconstructionWitnesses
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_sbyg_Conj
    (ay_sbyg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_sbyg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)

def ay_sbyg_FingerprintAgreement
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_sbyg_Conj fingerprintWitness
    (ay_sbyg_IdMatch originalFingerprint replayedFingerprint)

def ay_sbyg_CheckerReplay
    (symmetryReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_sbyg_Conj symmetryReplayCertificate checkerAccepted

def ay_sbyg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_sbyg_Conj baselineSolver baselineAvailable

def ay_sbyg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_sbyg_Conj binaryFingerprint buildReproducible

def ay_sbyg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_sbyg_Conj validatorAccepted validatorVersion

def ay_sbyg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_sbyg_Conj auditAppended auditAppendOnly

def ay_sbyg_AcceptedSymmetryBreakingGuard
    (originalCnf : Prop) (replayedCnf : Prop)
    (symmetryGenerators : Prop) (generatorManifestAccepted : Prop) (symmetryGeneratorsManifest : Prop)
    (orbitRepresentativeSet : Prop) (orbitRepresentativeAccepted : Prop) (orbitRepresentativeWitness : Prop)
    (addedConstraintSet : Prop) (addedConstraintCoverageAccepted : Prop) (addedConstraintCoverageWitness : Prop)
    (reducedSolution : Prop) (originalSolution : Prop)
    (modelReconstructionMap : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (symmetryReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_sbyg_SymmetryGeneratorManifest
       symmetryGenerators generatorManifestAccepted symmetryGeneratorsManifest ->
     ay_sbyg_OrbitRepresentativeWitness
       orbitRepresentativeSet orbitRepresentativeAccepted orbitRepresentativeWitness ->
     ay_sbyg_AddedConstraintCoverageDigest
       addedConstraintSet addedConstraintCoverageAccepted addedConstraintCoverageWitness ->
     ay_sbyg_ReducedSolutionModelMap
       reducedSolution originalSolution modelReconstructionMap ->
     ay_sbyg_ReconstructionWitnesses
       replayedCnf originalCnf replayedModel originalModel
       certificate conflict ->
     ay_sbyg_Equisat originalCnf replayedCnf ->
     ay_sbyg_FingerprintAgreement
       originalFingerprint replayedFingerprint fingerprintWitness ->
     ay_sbyg_CheckerReplay symmetryReplayCertificate checkerAccepted ->
     ay_sbyg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_sbyg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_sbyg_ValidatorGate validatorAccepted validatorVersion ->
     ay_sbyg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_sbyg_SymmetryBreakingGuardFailure
    (staleSymmetryGeneratorManifest : Prop) (orbitRepresentativeMismatch : Prop)
    (addedConstraintCoverageMismatch : Prop)
    (modelReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (staleSymmetryGeneratorManifest -> result) ->
    (orbitRepresentativeMismatch -> result) ->
    (addedConstraintCoverageMismatch -> result) ->
    (modelReconstructionMapGap -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (missingBaseline -> result) ->
    (buildDrift -> result) ->
    (validatorFailure -> result) ->
    (auditContradiction -> result) ->
    result

def ay_sbyg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_sbyg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_sbyg_Conj currentCnf recompute

def ay_sbyg_DiagnosticSymmetryBreakingGuard
    (currentCnf : Prop)
    (staleSymmetryGeneratorManifest : Prop) (orbitRepresentativeMismatch : Prop)
    (addedConstraintCoverageMismatch : Prop)
    (modelReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_sbyg_Conj
    (ay_sbyg_SymmetryBreakingGuardFailure
      staleSymmetryGeneratorManifest orbitRepresentativeMismatch addedConstraintCoverageMismatch modelReconstructionMapGap
      reconstructionGap staleFingerprint uncheckedReplay missingBaseline
      buildDrift validatorFailure
      auditContradiction)
    (ay_sbyg_Conj
      (ay_sbyg_RecomputeObligation currentCnf recompute)
      (ay_sbyg_NoSemanticClaim diagnostic))

def ay_sbyg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_sbyg_Conj exitCode claim

def ay_sbyg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_sbyg_Disj
    (ay_sbyg_ExitCodeSound exitCode (ay_sbyg_Sat originalCnf model))
    (ay_sbyg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_sbyg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_sbyg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_sbyg_conj_left
    (left : Prop) (right : Prop) :
    ay_sbyg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_sbyg_conj_right
    (left : Prop) (right : Prop) :
    ay_sbyg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_sbyg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_sbyg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_sbyg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_sbyg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_sbyg_equisat_forward
    (before : Prop) (after : Prop) :
    ay_sbyg_Equisat before after ->
    before -> after := by
  intro eqsat
  exact ay_sbyg_conj_left (before -> after) (after -> before) eqsat

theorem ay_sbyg_equisat_backward
    (before : Prop) (after : Prop) :
    ay_sbyg_Equisat before after ->
    after -> before := by
  intro eqsat
  exact ay_sbyg_conj_right (before -> after) (after -> before) eqsat

theorem ay_sbyg_symmetry_generator_manifest_applies
    (symmetryGenerators : Prop) (generatorManifestAccepted : Prop)
    (symmetryGeneratorsManifest : Prop) :
    ay_sbyg_SymmetryGeneratorManifest
      symmetryGenerators generatorManifestAccepted symmetryGeneratorsManifest ->
    symmetryGenerators -> generatorManifestAccepted := by
  intro digest
  exact ay_sbyg_conj_right symmetryGeneratorsManifest
    (symmetryGenerators -> generatorManifestAccepted) digest

theorem ay_sbyg_orbit_representative_witness_applies
    (orbitRepresentativeSet : Prop) (orbitRepresentativeAccepted : Prop)
    (orbitRepresentativeWitness : Prop) :
    ay_sbyg_OrbitRepresentativeWitness
      orbitRepresentativeSet orbitRepresentativeAccepted orbitRepresentativeWitness ->
    orbitRepresentativeSet -> orbitRepresentativeAccepted := by
  intro digest
  exact ay_sbyg_conj_right orbitRepresentativeWitness
    (orbitRepresentativeSet -> orbitRepresentativeAccepted) digest

theorem ay_sbyg_added_constraint_coverage_digest_applies
    (addedConstraintSet : Prop) (addedConstraintCoverageAccepted : Prop)
    (addedConstraintCoverageWitness : Prop) :
    ay_sbyg_AddedConstraintCoverageDigest
      addedConstraintSet addedConstraintCoverageAccepted addedConstraintCoverageWitness ->
    addedConstraintSet -> addedConstraintCoverageAccepted := by
  intro ledger
  exact ay_sbyg_conj_right addedConstraintCoverageWitness
    (addedConstraintSet -> addedConstraintCoverageAccepted) ledger

theorem ay_sbyg_reduced_solution_model_map_applies
    (reducedSolution : Prop) (originalSolution : Prop)
    (modelReconstructionMap : Prop) :
    ay_sbyg_ReducedSolutionModelMap
      reducedSolution originalSolution modelReconstructionMap ->
    reducedSolution -> originalSolution := by
  intro coverage
  exact ay_sbyg_conj_right modelReconstructionMap
    (reducedSolution -> originalSolution) coverage

theorem ay_sbyg_model_reconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_sbyg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_sbyg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel := by
  intro witnesses
  exact ay_sbyg_conj_left
    (ay_sbyg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_sbyg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_sbyg_proof_reconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_sbyg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_sbyg_ProofReconstruction
      originalCnf replayedCnf certificate conflict := by
  intro witnesses
  exact ay_sbyg_conj_right
    (ay_sbyg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_sbyg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_sbyg_accepted_equisat
    (originalCnf : Prop) (replayedCnf : Prop)
    (symmetryGenerators : Prop) (generatorManifestAccepted : Prop) (symmetryGeneratorsManifest : Prop)
    (orbitRepresentativeSet : Prop) (orbitRepresentativeAccepted : Prop) (orbitRepresentativeWitness : Prop)
    (addedConstraintSet : Prop) (addedConstraintCoverageAccepted : Prop) (addedConstraintCoverageWitness : Prop)
    (reducedSolution : Prop) (originalSolution : Prop)
    (modelReconstructionMap : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (symmetryReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_sbyg_AcceptedSymmetryBreakingGuard
      originalCnf replayedCnf
      symmetryGenerators generatorManifestAccepted symmetryGeneratorsManifest
      orbitRepresentativeSet orbitRepresentativeAccepted orbitRepresentativeWitness
      addedConstraintSet addedConstraintCoverageAccepted addedConstraintCoverageWitness
      reducedSolution originalSolution modelReconstructionMap
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      symmetryReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_sbyg_Equisat originalCnf replayedCnf := by
  intro accepted
  exact accepted (ay_sbyg_Equisat originalCnf replayedCnf)
    (fun _manifest _orbit _constraint _model _reconstruct eqsat _model _checker
      _fallback _build _validator _audit => eqsat)

theorem ay_sbyg_accepted_checker_replay
    (originalCnf : Prop) (replayedCnf : Prop)
    (symmetryGenerators : Prop) (generatorManifestAccepted : Prop) (symmetryGeneratorsManifest : Prop)
    (orbitRepresentativeSet : Prop) (orbitRepresentativeAccepted : Prop) (orbitRepresentativeWitness : Prop)
    (addedConstraintSet : Prop) (addedConstraintCoverageAccepted : Prop) (addedConstraintCoverageWitness : Prop)
    (reducedSolution : Prop) (originalSolution : Prop)
    (modelReconstructionMap : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (symmetryReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_sbyg_AcceptedSymmetryBreakingGuard
      originalCnf replayedCnf
      symmetryGenerators generatorManifestAccepted symmetryGeneratorsManifest
      orbitRepresentativeSet orbitRepresentativeAccepted orbitRepresentativeWitness
      addedConstraintSet addedConstraintCoverageAccepted addedConstraintCoverageWitness
      reducedSolution originalSolution modelReconstructionMap
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      symmetryReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_sbyg_CheckerReplay symmetryReplayCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_sbyg_CheckerReplay symmetryReplayCertificate checkerAccepted)
    (fun _manifest _orbit _constraint _model _reconstruct _eqsat _model checker
      _fallback _build _validator _audit => checker)

theorem ay_sbyg_accepted_audit_transcript
    (originalCnf : Prop) (replayedCnf : Prop)
    (symmetryGenerators : Prop) (generatorManifestAccepted : Prop) (symmetryGeneratorsManifest : Prop)
    (orbitRepresentativeSet : Prop) (orbitRepresentativeAccepted : Prop) (orbitRepresentativeWitness : Prop)
    (addedConstraintSet : Prop) (addedConstraintCoverageAccepted : Prop) (addedConstraintCoverageWitness : Prop)
    (reducedSolution : Prop) (originalSolution : Prop)
    (modelReconstructionMap : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (symmetryReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_sbyg_AcceptedSymmetryBreakingGuard
      originalCnf replayedCnf
      symmetryGenerators generatorManifestAccepted symmetryGeneratorsManifest
      orbitRepresentativeSet orbitRepresentativeAccepted orbitRepresentativeWitness
      addedConstraintSet addedConstraintCoverageAccepted addedConstraintCoverageWitness
      reducedSolution originalSolution modelReconstructionMap
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      symmetryReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_sbyg_AuditTranscript auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_sbyg_AuditTranscript auditAppended auditAppendOnly)
    (fun _manifest _orbit _constraint _model _reconstruct _eqsat _model _checker
      _fallback _build _validator audit => audit)

theorem ay_sbyg_sat_pullback
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :
    ay_sbyg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel ->
    ay_sbyg_Sat replayedCnf replayedModel ->
    ay_sbyg_Sat originalCnf originalModel := by
  intro reconstruct replayedSat
  exact reconstruct replayedSat

theorem ay_sbyg_unsat_pushback
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_sbyg_ProofReconstruction
      originalCnf replayedCnf certificate conflict ->
    ay_sbyg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruct replayedReplay
  exact reconstruct replayedReplay

theorem ay_sbyg_public_sat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (symmetryGenerators : Prop) (generatorManifestAccepted : Prop) (symmetryGeneratorsManifest : Prop)
    (orbitRepresentativeSet : Prop) (orbitRepresentativeAccepted : Prop) (orbitRepresentativeWitness : Prop)
    (addedConstraintSet : Prop) (addedConstraintCoverageAccepted : Prop) (addedConstraintCoverageWitness : Prop)
    (reducedSolution : Prop) (originalSolution : Prop)
    (modelReconstructionMap : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (symmetryReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_sbyg_AcceptedSymmetryBreakingGuard
      originalCnf replayedCnf
      symmetryGenerators generatorManifestAccepted symmetryGeneratorsManifest
      orbitRepresentativeSet orbitRepresentativeAccepted orbitRepresentativeWitness
      addedConstraintSet addedConstraintCoverageAccepted addedConstraintCoverageWitness
      reducedSolution originalSolution modelReconstructionMap
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      symmetryReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_sbyg_Sat replayedCnf replayedModel ->
    exitCode ->
    ay_sbyg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedSat hexit
  exact accepted
    (ay_sbyg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _manifest _orbit _constraint _model reconstruct _eqsat _model _checker
      _fallback _build _validator _audit =>
      ay_sbyg_disj_left
        (ay_sbyg_ExitCodeSound exitCode
          (ay_sbyg_Sat originalCnf originalModel))
        (ay_sbyg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_sbyg_conj_intro exitCode
          (ay_sbyg_Sat originalCnf originalModel)
          hexit
          ((ay_sbyg_model_reconstruction
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedSat)))

theorem ay_sbyg_public_unsat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (symmetryGenerators : Prop) (generatorManifestAccepted : Prop) (symmetryGeneratorsManifest : Prop)
    (orbitRepresentativeSet : Prop) (orbitRepresentativeAccepted : Prop) (orbitRepresentativeWitness : Prop)
    (addedConstraintSet : Prop) (addedConstraintCoverageAccepted : Prop) (addedConstraintCoverageWitness : Prop)
    (reducedSolution : Prop) (originalSolution : Prop)
    (modelReconstructionMap : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (symmetryReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_sbyg_AcceptedSymmetryBreakingGuard
      originalCnf replayedCnf
      symmetryGenerators generatorManifestAccepted symmetryGeneratorsManifest
      orbitRepresentativeSet orbitRepresentativeAccepted orbitRepresentativeWitness
      addedConstraintSet addedConstraintCoverageAccepted addedConstraintCoverageWitness
      reducedSolution originalSolution modelReconstructionMap
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      symmetryReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_sbyg_Replay replayedCnf certificate conflict ->
    exitCode ->
    ay_sbyg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedReplay hexit
  exact accepted
    (ay_sbyg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _manifest _orbit _constraint _model reconstruct _eqsat _model _checker
      _fallback _build _validator _audit =>
      ay_sbyg_disj_right
        (ay_sbyg_ExitCodeSound exitCode
          (ay_sbyg_Sat originalCnf originalModel))
        (ay_sbyg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_sbyg_conj_intro exitCode
          (certificate -> originalCnf -> conflict)
          hexit
          ((ay_sbyg_proof_reconstruction
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedReplay)))

theorem ay_sbyg_failure_stale_symmetry_generator_manifest
    (staleSymmetryGeneratorManifest : Prop) (orbitRepresentativeMismatch : Prop)
    (addedConstraintCoverageMismatch : Prop)
    (modelReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleSymmetryGeneratorManifest ->
    ay_sbyg_SymmetryBreakingGuardFailure
      staleSymmetryGeneratorManifest orbitRepresentativeMismatch addedConstraintCoverageMismatch modelReconstructionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result generator_case _orbit_case _constraint_case _model_case _reconstruction_case
    _model_case _orbit_case _baseline_case _build_case
    _validator_case _audit_case
  exact generator_case failure

theorem ay_sbyg_failure_orbit_representative
    (staleSymmetryGeneratorManifest : Prop) (orbitRepresentativeMismatch : Prop)
    (addedConstraintCoverageMismatch : Prop)
    (modelReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    orbitRepresentativeMismatch ->
    ay_sbyg_SymmetryBreakingGuardFailure
      staleSymmetryGeneratorManifest orbitRepresentativeMismatch addedConstraintCoverageMismatch modelReconstructionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case orbit_case _constraint_case _model_case
    _reconstruction_case _model_case _orbit_case _baseline_case
    _build_case _validator_case _audit_case
  exact orbit_case failure

theorem ay_sbyg_failure_added_constraint_coverage_digest
    (staleSymmetryGeneratorManifest : Prop) (orbitRepresentativeMismatch : Prop)
    (addedConstraintCoverageMismatch : Prop)
    (modelReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    addedConstraintCoverageMismatch ->
    ay_sbyg_SymmetryBreakingGuardFailure
      staleSymmetryGeneratorManifest orbitRepresentativeMismatch addedConstraintCoverageMismatch modelReconstructionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _orbit_case constraint_case _model_case _reconstruction_case
    _model_case _orbit_case _baseline_case _build_case
    _validator_case _audit_case
  exact constraint_case failure

theorem ay_sbyg_failure_model_reconstruction_map
    (staleSymmetryGeneratorManifest : Prop) (orbitRepresentativeMismatch : Prop)
    (addedConstraintCoverageMismatch : Prop)
    (modelReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    modelReconstructionMapGap ->
    ay_sbyg_SymmetryBreakingGuardFailure
      staleSymmetryGeneratorManifest orbitRepresentativeMismatch addedConstraintCoverageMismatch modelReconstructionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _orbit_case _constraint_case constraint_case _reconstruction_case
    _model_case _orbit_case _baseline_case _build_case
    _validator_case _audit_case
  exact constraint_case failure

theorem ay_sbyg_failure_reconstruction
    (staleSymmetryGeneratorManifest : Prop) (orbitRepresentativeMismatch : Prop)
    (addedConstraintCoverageMismatch : Prop)
    (modelReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_sbyg_SymmetryBreakingGuardFailure
      staleSymmetryGeneratorManifest orbitRepresentativeMismatch addedConstraintCoverageMismatch modelReconstructionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _orbit_case _constraint_case _model_case reconstruction_case
    _model_case _orbit_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case failure

theorem ay_sbyg_failure_stale_fingerprint
    (staleSymmetryGeneratorManifest : Prop) (orbitRepresentativeMismatch : Prop)
    (addedConstraintCoverageMismatch : Prop)
    (modelReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_sbyg_SymmetryBreakingGuardFailure
      staleSymmetryGeneratorManifest orbitRepresentativeMismatch addedConstraintCoverageMismatch modelReconstructionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _orbit_case _constraint_case _model_case _reconstruction_case
    model_case _orbit_case _baseline_case _build_case
    _validator_case _audit_case
  exact model_case failure

theorem ay_sbyg_failure_unchecked_replay
    (staleSymmetryGeneratorManifest : Prop) (orbitRepresentativeMismatch : Prop)
    (addedConstraintCoverageMismatch : Prop)
    (modelReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_sbyg_SymmetryBreakingGuardFailure
      staleSymmetryGeneratorManifest orbitRepresentativeMismatch addedConstraintCoverageMismatch modelReconstructionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _orbit_case _constraint_case _model_case _reconstruction_case
    _model_case orbit_case _baseline_case _build_case
    _validator_case _audit_case
  exact orbit_case failure

theorem ay_sbyg_failure_missing_baseline
    (staleSymmetryGeneratorManifest : Prop) (orbitRepresentativeMismatch : Prop)
    (addedConstraintCoverageMismatch : Prop)
    (modelReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingBaseline ->
    ay_sbyg_SymmetryBreakingGuardFailure
      staleSymmetryGeneratorManifest orbitRepresentativeMismatch addedConstraintCoverageMismatch modelReconstructionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _orbit_case _constraint_case _model_case _reconstruction_case
    _model_case _orbit_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case failure

theorem ay_sbyg_failure_build
    (staleSymmetryGeneratorManifest : Prop) (orbitRepresentativeMismatch : Prop)
    (addedConstraintCoverageMismatch : Prop)
    (modelReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_sbyg_SymmetryBreakingGuardFailure
      staleSymmetryGeneratorManifest orbitRepresentativeMismatch addedConstraintCoverageMismatch modelReconstructionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _orbit_case _constraint_case _model_case _reconstruction_case
    _model_case _orbit_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case failure

theorem ay_sbyg_failure_validator
    (staleSymmetryGeneratorManifest : Prop) (orbitRepresentativeMismatch : Prop)
    (addedConstraintCoverageMismatch : Prop)
    (modelReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    validatorFailure ->
    ay_sbyg_SymmetryBreakingGuardFailure
      staleSymmetryGeneratorManifest orbitRepresentativeMismatch addedConstraintCoverageMismatch modelReconstructionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _orbit_case _constraint_case _model_case _reconstruction_case
    _model_case _orbit_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case failure

theorem ay_sbyg_failure_audit
    (staleSymmetryGeneratorManifest : Prop) (orbitRepresentativeMismatch : Prop)
    (addedConstraintCoverageMismatch : Prop)
    (modelReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_sbyg_SymmetryBreakingGuardFailure
      staleSymmetryGeneratorManifest orbitRepresentativeMismatch addedConstraintCoverageMismatch modelReconstructionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _orbit_case _constraint_case _model_case _reconstruction_case
    _model_case _orbit_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case failure

theorem ay_sbyg_diagnostic_no_claim
    (currentCnf : Prop)
    (staleSymmetryGeneratorManifest : Prop) (orbitRepresentativeMismatch : Prop)
    (addedConstraintCoverageMismatch : Prop)
    (modelReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_sbyg_DiagnosticSymmetryBreakingGuard
      currentCnf staleSymmetryGeneratorManifest orbitRepresentativeMismatch addedConstraintCoverageMismatch modelReconstructionMapGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_sbyg_NoSemanticClaim diagnostic := by
  intro diagnosticBundle
  exact ay_sbyg_conj_right
    (ay_sbyg_RecomputeObligation currentCnf recompute)
    (ay_sbyg_NoSemanticClaim diagnostic)
    (ay_sbyg_conj_right
      (ay_sbyg_SymmetryBreakingGuardFailure
        staleSymmetryGeneratorManifest orbitRepresentativeMismatch addedConstraintCoverageMismatch modelReconstructionMapGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_sbyg_Conj
        (ay_sbyg_RecomputeObligation currentCnf recompute)
        (ay_sbyg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_sbyg_diagnostic_recompute
    (currentCnf : Prop)
    (staleSymmetryGeneratorManifest : Prop) (orbitRepresentativeMismatch : Prop)
    (addedConstraintCoverageMismatch : Prop)
    (modelReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_sbyg_DiagnosticSymmetryBreakingGuard
      currentCnf staleSymmetryGeneratorManifest orbitRepresentativeMismatch addedConstraintCoverageMismatch modelReconstructionMapGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_sbyg_RecomputeObligation currentCnf recompute := by
  intro diagnosticBundle
  exact ay_sbyg_conj_left
    (ay_sbyg_RecomputeObligation currentCnf recompute)
    (ay_sbyg_NoSemanticClaim diagnostic)
    (ay_sbyg_conj_right
      (ay_sbyg_SymmetryBreakingGuardFailure
        staleSymmetryGeneratorManifest orbitRepresentativeMismatch addedConstraintCoverageMismatch modelReconstructionMapGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_sbyg_Conj
        (ay_sbyg_RecomputeObligation currentCnf recompute)
        (ay_sbyg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_sbyg_unchecked_symmetry_breaking_cannot_bless_public_result
    (currentCnf : Prop)
    (staleSymmetryGeneratorManifest : Prop) (orbitRepresentativeMismatch : Prop)
    (addedConstraintCoverageMismatch : Prop)
    (modelReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_sbyg_DiagnosticSymmetryBreakingGuard
      currentCnf staleSymmetryGeneratorManifest orbitRepresentativeMismatch addedConstraintCoverageMismatch modelReconstructionMapGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_sbyg_Conj
      (ay_sbyg_NoSemanticClaim diagnostic)
      (ay_sbyg_RecomputeObligation currentCnf recompute) := by
  intro _unchecked diagnosticBundle
  exact ay_sbyg_conj_intro
    (ay_sbyg_NoSemanticClaim diagnostic)
    (ay_sbyg_RecomputeObligation currentCnf recompute)
    (ay_sbyg_diagnostic_no_claim
      currentCnf staleSymmetryGeneratorManifest orbitRepresentativeMismatch addedConstraintCoverageMismatch modelReconstructionMapGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
    (ay_sbyg_diagnostic_recompute
      currentCnf staleSymmetryGeneratorManifest orbitRepresentativeMismatch addedConstraintCoverageMismatch modelReconstructionMapGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)

theorem ay_sbyg_unchecked_symmetry_breaking_cannot_bless_public_sat
    (currentCnf : Prop)
    (staleSymmetryGeneratorManifest : Prop) (orbitRepresentativeMismatch : Prop)
    (addedConstraintCoverageMismatch : Prop)
    (modelReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_sbyg_DiagnosticSymmetryBreakingGuard
      currentCnf staleSymmetryGeneratorManifest orbitRepresentativeMismatch addedConstraintCoverageMismatch modelReconstructionMapGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_sbyg_NoSemanticClaim diagnostic := by
  intro _unchecked diagnosticBundle
  exact ay_sbyg_diagnostic_no_claim
    currentCnf staleSymmetryGeneratorManifest orbitRepresentativeMismatch addedConstraintCoverageMismatch modelReconstructionMapGap reconstructionGap
    staleFingerprint uncheckedReplay missingBaseline buildDrift
    validatorFailure auditContradiction recompute diagnostic diagnosticBundle

theorem ay_sbyg_unchecked_symmetry_breaking_cannot_bless_public_unsat
    (currentCnf : Prop)
    (staleSymmetryGeneratorManifest : Prop) (orbitRepresentativeMismatch : Prop)
    (addedConstraintCoverageMismatch : Prop)
    (modelReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_sbyg_DiagnosticSymmetryBreakingGuard
      currentCnf staleSymmetryGeneratorManifest orbitRepresentativeMismatch addedConstraintCoverageMismatch modelReconstructionMapGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_sbyg_RecomputeObligation currentCnf recompute := by
  intro _unchecked diagnosticBundle
  exact ay_sbyg_diagnostic_recompute
    currentCnf staleSymmetryGeneratorManifest orbitRepresentativeMismatch addedConstraintCoverageMismatch modelReconstructionMapGap reconstructionGap
    staleFingerprint uncheckedReplay missingBaseline buildDrift
    validatorFailure auditContradiction recompute diagnostic diagnosticBundle
