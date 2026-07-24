-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Equivalent-literal-substitution preprocessing guard soundness.
-- The propositions stand for original/preprocessed formula digests,
-- equivalence-class ledgers, substitution map witnesses, propagation/
-- equivalence replay, checker replay, model/proof reconstruction,
-- fallback/build/validator gates, audit transcripts, diagnostics, and public
-- SAT/UNSAT reports.

def ay_elsg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_elsg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_elsg_Equisat (original : Prop) (preprocessed : Prop) :=
  ay_elsg_Conj (original -> preprocessed) (preprocessed -> original)

def ay_elsg_Sat (cnf : Prop) (model : Prop) :=
  ay_elsg_Conj cnf model

def ay_elsg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_elsg_OriginalFormulaDigest
    (originalDigest : Prop) (originalDigestAccepted : Prop)
    (originalManifest : Prop) :=
  ay_elsg_Conj originalManifest (originalDigest -> originalDigestAccepted)

def ay_elsg_PreprocessedFormulaDigest
    (preprocessedDigest : Prop) (preprocessedDigestAccepted : Prop)
    (preprocessedManifest : Prop) :=
  ay_elsg_Conj preprocessedManifest
    (preprocessedDigest -> preprocessedDigestAccepted)

def ay_elsg_EquivalenceClassLedger
    (equivalenceClassLedger : Prop) (equivalenceAccepted : Prop)
    (equivalenceCoverage : Prop) :=
  ay_elsg_Conj equivalenceCoverage
    (equivalenceClassLedger -> equivalenceAccepted)

def ay_elsg_SubstitutionMapWitness
    (substitutionMapWitness : Prop) (substitutionAccepted : Prop)
    (substitutionCoverage : Prop) :=
  ay_elsg_Conj substitutionCoverage
    (substitutionMapWitness -> substitutionAccepted)

def ay_elsg_EquivalenceReplay
    (equivalenceReplay : Prop) (replayAccepted : Prop)
    (replayCoverage : Prop) :=
  ay_elsg_Conj replayCoverage (equivalenceReplay -> replayAccepted)

def ay_elsg_CheckerReplay
    (checkerReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_elsg_Conj checkerReplayCertificate checkerAccepted

def ay_elsg_ModelReconstructionWitness
    (preprocessedCnf : Prop) (originalCnf : Prop)
    (preprocessedModel : Prop) (originalModel : Prop) :=
  ay_elsg_Sat preprocessedCnf preprocessedModel ->
    ay_elsg_Sat originalCnf originalModel

def ay_elsg_UnsatProofReconstructionWitness
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_elsg_Replay preprocessedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_elsg_ReconstructionWitnesses
    (preprocessedCnf : Prop) (originalCnf : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_elsg_Conj
    (ay_elsg_ModelReconstructionWitness
      preprocessedCnf originalCnf preprocessedModel originalModel)
    (ay_elsg_UnsatProofReconstructionWitness
      originalCnf preprocessedCnf certificate conflict)

def ay_elsg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_elsg_Conj baselineSolver baselineAvailable

def ay_elsg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_elsg_Conj binaryFingerprint buildReproducible

def ay_elsg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_elsg_Conj validatorAccepted validatorVersion

def ay_elsg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_elsg_Conj auditAppended auditAppendOnly

def ay_elsg_AcceptedEquivalentLiteralSubstitutionGuard
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (originalDigest : Prop) (originalDigestAccepted : Prop)
    (originalManifest : Prop)
    (preprocessedDigest : Prop) (preprocessedDigestAccepted : Prop)
    (preprocessedManifest : Prop)
    (equivalenceClassLedger : Prop) (equivalenceAccepted : Prop)
    (equivalenceCoverage : Prop)
    (substitutionMapWitness : Prop) (substitutionAccepted : Prop)
    (substitutionCoverage : Prop)
    (equivalenceReplay : Prop) (replayAccepted : Prop)
    (replayCoverage : Prop)
    (checkerReplayCertificate : Prop) (checkerAccepted : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_elsg_OriginalFormulaDigest
       originalDigest originalDigestAccepted originalManifest ->
     ay_elsg_PreprocessedFormulaDigest
       preprocessedDigest preprocessedDigestAccepted preprocessedManifest ->
     ay_elsg_EquivalenceClassLedger
       equivalenceClassLedger equivalenceAccepted equivalenceCoverage ->
     ay_elsg_SubstitutionMapWitness
       substitutionMapWitness substitutionAccepted substitutionCoverage ->
     ay_elsg_EquivalenceReplay
       equivalenceReplay replayAccepted replayCoverage ->
     ay_elsg_CheckerReplay checkerReplayCertificate checkerAccepted ->
     ay_elsg_ReconstructionWitnesses
       preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict ->
     ay_elsg_Equisat originalCnf preprocessedCnf ->
     ay_elsg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_elsg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_elsg_ValidatorGate validatorAccepted validatorVersion ->
     ay_elsg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_elsg_EquivalentLiteralSubstitutionGuardFailure
    (digestMismatch : Prop) (equivalenceMismatch : Prop)
    (substitutionMismatch : Prop) (replayMismatch : Prop)
    (reconstructionMismatch : Prop) (checkerMismatch : Prop)
    (baselineMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (digestMismatch -> result) ->
    (equivalenceMismatch -> result) ->
    (substitutionMismatch -> result) ->
    (replayMismatch -> result) ->
    (reconstructionMismatch -> result) ->
    (checkerMismatch -> result) ->
    (baselineMismatch -> result) ->
    (buildMismatch -> result) ->
    (validatorMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_elsg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_elsg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_elsg_Conj currentCnf recompute

def ay_elsg_DiagnosticEquivalentLiteralSubstitutionGuard
    (currentCnf : Prop)
    (digestMismatch : Prop) (equivalenceMismatch : Prop)
    (substitutionMismatch : Prop) (replayMismatch : Prop)
    (reconstructionMismatch : Prop) (checkerMismatch : Prop)
    (baselineMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_elsg_Conj
    (ay_elsg_EquivalentLiteralSubstitutionGuardFailure
      digestMismatch equivalenceMismatch substitutionMismatch replayMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch)
    (ay_elsg_Conj
      (ay_elsg_RecomputeObligation currentCnf recompute)
      (ay_elsg_NoSemanticClaim diagnostic))

def ay_elsg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_elsg_Conj exitCode claim

def ay_elsg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_elsg_Disj
    (ay_elsg_ExitCodeSound exitCode (ay_elsg_Sat originalCnf model))
    (ay_elsg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_elsg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_elsg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_elsg_conj_left
    (left : Prop) (right : Prop) :
    ay_elsg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_elsg_conj_right
    (left : Prop) (right : Prop) :
    ay_elsg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_elsg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_elsg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_elsg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_elsg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_elsg_equisat_forward
    (original : Prop) (preprocessed : Prop) :
    ay_elsg_Equisat original preprocessed -> original -> preprocessed := by
  intro eqsat
  exact ay_elsg_conj_left (original -> preprocessed) (preprocessed -> original) eqsat

theorem ay_elsg_equisat_backward
    (original : Prop) (preprocessed : Prop) :
    ay_elsg_Equisat original preprocessed -> preprocessed -> original := by
  intro eqsat
  exact ay_elsg_conj_right (original -> preprocessed) (preprocessed -> original) eqsat

theorem ay_elsg_original_formula_digest_applies
    (originalDigest : Prop) (originalDigestAccepted : Prop)
    (originalManifest : Prop) :
    ay_elsg_OriginalFormulaDigest
      originalDigest originalDigestAccepted originalManifest ->
    originalDigest -> originalDigestAccepted := by
  intro digest
  exact ay_elsg_conj_right
    originalManifest (originalDigest -> originalDigestAccepted) digest

theorem ay_elsg_preprocessed_formula_digest_applies
    (preprocessedDigest : Prop) (preprocessedDigestAccepted : Prop)
    (preprocessedManifest : Prop) :
    ay_elsg_PreprocessedFormulaDigest
      preprocessedDigest preprocessedDigestAccepted preprocessedManifest ->
    preprocessedDigest -> preprocessedDigestAccepted := by
  intro digest
  exact ay_elsg_conj_right
    preprocessedManifest
    (preprocessedDigest -> preprocessedDigestAccepted)
    digest

theorem ay_elsg_equivalence_class_ledger_applies
    (equivalenceClassLedger : Prop) (equivalenceAccepted : Prop)
    (equivalenceCoverage : Prop) :
    ay_elsg_EquivalenceClassLedger
      equivalenceClassLedger equivalenceAccepted equivalenceCoverage ->
    equivalenceClassLedger -> equivalenceAccepted := by
  intro ledger
  exact ay_elsg_conj_right
    equivalenceCoverage
    (equivalenceClassLedger -> equivalenceAccepted)
    ledger

theorem ay_elsg_substitution_map_witness_applies
    (substitutionMapWitness : Prop) (substitutionAccepted : Prop)
    (substitutionCoverage : Prop) :
    ay_elsg_SubstitutionMapWitness
      substitutionMapWitness substitutionAccepted substitutionCoverage ->
    substitutionMapWitness -> substitutionAccepted := by
  intro witness
  exact ay_elsg_conj_right
    substitutionCoverage
    (substitutionMapWitness -> substitutionAccepted)
    witness

theorem ay_elsg_equivalence_replay_applies
    (equivalenceReplay : Prop) (replayAccepted : Prop)
    (replayCoverage : Prop) :
    ay_elsg_EquivalenceReplay
      equivalenceReplay replayAccepted replayCoverage ->
    equivalenceReplay -> replayAccepted := by
  intro replay
  exact ay_elsg_conj_right
    replayCoverage (equivalenceReplay -> replayAccepted) replay

theorem ay_elsg_checker_replay_certificate
    (checkerReplayCertificate : Prop) (checkerAccepted : Prop) :
    ay_elsg_CheckerReplay checkerReplayCertificate checkerAccepted ->
    checkerReplayCertificate := by
  intro replay
  exact ay_elsg_conj_left checkerReplayCertificate checkerAccepted replay

theorem ay_elsg_model_reconstruction
    (preprocessedCnf : Prop) (originalCnf : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_elsg_ReconstructionWitnesses
      preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict ->
    ay_elsg_Sat preprocessedCnf preprocessedModel ->
    ay_elsg_Sat originalCnf originalModel := by
  intro witnesses
  exact ay_elsg_conj_left
    (ay_elsg_ModelReconstructionWitness
      preprocessedCnf originalCnf preprocessedModel originalModel)
    (ay_elsg_UnsatProofReconstructionWitness
      originalCnf preprocessedCnf certificate conflict)
    witnesses

theorem ay_elsg_unsat_proof_reconstruction
    (preprocessedCnf : Prop) (originalCnf : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_elsg_ReconstructionWitnesses
      preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict ->
    ay_elsg_Replay preprocessedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses
  exact ay_elsg_conj_right
    (ay_elsg_ModelReconstructionWitness
      preprocessedCnf originalCnf preprocessedModel originalModel)
    (ay_elsg_UnsatProofReconstructionWitness
      originalCnf preprocessedCnf certificate conflict)
    witnesses

theorem ay_elsg_accepted_equisat
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (originalDigest : Prop) (originalDigestAccepted : Prop)
    (originalManifest : Prop)
    (preprocessedDigest : Prop) (preprocessedDigestAccepted : Prop)
    (preprocessedManifest : Prop)
    (equivalenceClassLedger : Prop) (equivalenceAccepted : Prop)
    (equivalenceCoverage : Prop)
    (substitutionMapWitness : Prop) (substitutionAccepted : Prop)
    (substitutionCoverage : Prop)
    (equivalenceReplay : Prop) (replayAccepted : Prop)
    (replayCoverage : Prop)
    (checkerReplayCertificate : Prop) (checkerAccepted : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_elsg_AcceptedEquivalentLiteralSubstitutionGuard
      originalCnf preprocessedCnf
      originalDigest originalDigestAccepted originalManifest
      preprocessedDigest preprocessedDigestAccepted preprocessedManifest
      equivalenceClassLedger equivalenceAccepted equivalenceCoverage
      substitutionMapWitness substitutionAccepted substitutionCoverage
      equivalenceReplay replayAccepted replayCoverage
      checkerReplayCertificate checkerAccepted
      preprocessedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_elsg_Equisat originalCnf preprocessedCnf := by
  intro accepted
  exact accepted (ay_elsg_Equisat originalCnf preprocessedCnf)
    (fun _origDigest _prepDigest _equiv _substitution _replay _checker
      _reconstruct eqsat _fallback _build _validator _audit => eqsat)

theorem ay_elsg_accepted_reconstruction
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (originalDigest : Prop) (originalDigestAccepted : Prop)
    (originalManifest : Prop)
    (preprocessedDigest : Prop) (preprocessedDigestAccepted : Prop)
    (preprocessedManifest : Prop)
    (equivalenceClassLedger : Prop) (equivalenceAccepted : Prop)
    (equivalenceCoverage : Prop)
    (substitutionMapWitness : Prop) (substitutionAccepted : Prop)
    (substitutionCoverage : Prop)
    (equivalenceReplay : Prop) (replayAccepted : Prop)
    (replayCoverage : Prop)
    (checkerReplayCertificate : Prop) (checkerAccepted : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_elsg_AcceptedEquivalentLiteralSubstitutionGuard
      originalCnf preprocessedCnf
      originalDigest originalDigestAccepted originalManifest
      preprocessedDigest preprocessedDigestAccepted preprocessedManifest
      equivalenceClassLedger equivalenceAccepted equivalenceCoverage
      substitutionMapWitness substitutionAccepted substitutionCoverage
      equivalenceReplay replayAccepted replayCoverage
      checkerReplayCertificate checkerAccepted
      preprocessedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_elsg_ReconstructionWitnesses
      preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict := by
  intro accepted
  exact accepted
    (ay_elsg_ReconstructionWitnesses
      preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict)
    (fun _origDigest _prepDigest _equiv _substitution _replay _checker
      reconstruct _eqsat _fallback _build _validator _audit => reconstruct)

theorem ay_elsg_sat_pullback
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_elsg_ReconstructionWitnesses
      preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict ->
    ay_elsg_Sat preprocessedCnf preprocessedModel ->
    ay_elsg_Sat originalCnf originalModel := by
  intro witnesses satPreprocessed
  exact ay_elsg_model_reconstruction
    preprocessedCnf originalCnf preprocessedModel originalModel
    certificate conflict witnesses satPreprocessed

theorem ay_elsg_unsat_pushback
    (originalCnf : Prop) (preprocessedCnf : Prop)
    (preprocessedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_elsg_ReconstructionWitnesses
      preprocessedCnf originalCnf preprocessedModel originalModel certificate conflict ->
    ay_elsg_Replay preprocessedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses replay
  exact ay_elsg_unsat_proof_reconstruction
    preprocessedCnf originalCnf preprocessedModel originalModel
    certificate conflict witnesses replay

theorem ay_elsg_public_sat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_elsg_ExitCodeSound exitCode (ay_elsg_Sat originalCnf originalModel) ->
    ay_elsg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro satSound
  exact ay_elsg_disj_left
    (ay_elsg_ExitCodeSound exitCode (ay_elsg_Sat originalCnf originalModel))
    (ay_elsg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    satSound

theorem ay_elsg_public_unsat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_elsg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_elsg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro unsatSound
  exact ay_elsg_disj_right
    (ay_elsg_ExitCodeSound exitCode (ay_elsg_Sat originalCnf originalModel))
    (ay_elsg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    unsatSound

theorem ay_elsg_failure_digest
    (digestMismatch equivalenceMismatch substitutionMismatch replayMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    digestMismatch ->
    ay_elsg_EquivalentLiteralSubstitutionGuardFailure
      digestMismatch equivalenceMismatch substitutionMismatch replayMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result digest_case _equiv_case _substitution_case _replay_case
    _reconstruction_case _checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact digest_case h

theorem ay_elsg_failure_equivalence
    (digestMismatch equivalenceMismatch substitutionMismatch replayMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    equivalenceMismatch ->
    ay_elsg_EquivalentLiteralSubstitutionGuardFailure
      digestMismatch equivalenceMismatch substitutionMismatch replayMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case equivalence_case _substitution_case _replay_case
    _reconstruction_case _checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact equivalence_case h

theorem ay_elsg_failure_substitution
    (digestMismatch equivalenceMismatch substitutionMismatch replayMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    substitutionMismatch ->
    ay_elsg_EquivalentLiteralSubstitutionGuardFailure
      digestMismatch equivalenceMismatch substitutionMismatch replayMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _equiv_case substitution_case _replay_case
    _reconstruction_case _checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact substitution_case h

theorem ay_elsg_failure_replay
    (digestMismatch equivalenceMismatch substitutionMismatch replayMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    replayMismatch ->
    ay_elsg_EquivalentLiteralSubstitutionGuardFailure
      digestMismatch equivalenceMismatch substitutionMismatch replayMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _equiv_case _substitution_case replay_case
    _reconstruction_case _checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact replay_case h

theorem ay_elsg_failure_reconstruction
    (digestMismatch equivalenceMismatch substitutionMismatch replayMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    reconstructionMismatch ->
    ay_elsg_EquivalentLiteralSubstitutionGuardFailure
      digestMismatch equivalenceMismatch substitutionMismatch replayMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _equiv_case _substitution_case _replay_case
    reconstruction_case _checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case h

theorem ay_elsg_failure_checker
    (digestMismatch equivalenceMismatch substitutionMismatch replayMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    checkerMismatch ->
    ay_elsg_EquivalentLiteralSubstitutionGuardFailure
      digestMismatch equivalenceMismatch substitutionMismatch replayMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _equiv_case _substitution_case _replay_case
    _reconstruction_case checker_case _baseline_case _build_case
    _validator_case _audit_case
  exact checker_case h

theorem ay_elsg_failure_baseline
    (digestMismatch equivalenceMismatch substitutionMismatch replayMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    baselineMismatch ->
    ay_elsg_EquivalentLiteralSubstitutionGuardFailure
      digestMismatch equivalenceMismatch substitutionMismatch replayMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _equiv_case _substitution_case _replay_case
    _reconstruction_case _checker_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case h

theorem ay_elsg_failure_build
    (digestMismatch equivalenceMismatch substitutionMismatch replayMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    buildMismatch ->
    ay_elsg_EquivalentLiteralSubstitutionGuardFailure
      digestMismatch equivalenceMismatch substitutionMismatch replayMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _equiv_case _substitution_case _replay_case
    _reconstruction_case _checker_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case h

theorem ay_elsg_failure_validator
    (digestMismatch equivalenceMismatch substitutionMismatch replayMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    validatorMismatch ->
    ay_elsg_EquivalentLiteralSubstitutionGuardFailure
      digestMismatch equivalenceMismatch substitutionMismatch replayMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _equiv_case _substitution_case _replay_case
    _reconstruction_case _checker_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case h

theorem ay_elsg_failure_audit
    (digestMismatch equivalenceMismatch substitutionMismatch replayMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    auditMismatch ->
    ay_elsg_EquivalentLiteralSubstitutionGuardFailure
      digestMismatch equivalenceMismatch substitutionMismatch replayMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _equiv_case _substitution_case _replay_case
    _reconstruction_case _checker_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case h

theorem ay_elsg_diagnostic_no_claim
    (currentCnf : Prop)
    (digestMismatch equivalenceMismatch substitutionMismatch replayMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_elsg_DiagnosticEquivalentLiteralSubstitutionGuard
      currentCnf digestMismatch equivalenceMismatch substitutionMismatch replayMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_elsg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard
  exact ay_elsg_conj_right
    (ay_elsg_RecomputeObligation currentCnf recompute)
    (ay_elsg_NoSemanticClaim diagnostic)
    (ay_elsg_conj_right
      (ay_elsg_EquivalentLiteralSubstitutionGuardFailure
        digestMismatch equivalenceMismatch substitutionMismatch replayMismatch
        reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
        validatorMismatch auditMismatch)
      (ay_elsg_Conj
        (ay_elsg_RecomputeObligation currentCnf recompute)
        (ay_elsg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_elsg_diagnostic_recompute
    (currentCnf : Prop)
    (digestMismatch equivalenceMismatch substitutionMismatch replayMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_elsg_DiagnosticEquivalentLiteralSubstitutionGuard
      currentCnf digestMismatch equivalenceMismatch substitutionMismatch replayMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_elsg_RecomputeObligation currentCnf recompute := by
  intro diagnosticGuard
  exact ay_elsg_conj_left
    (ay_elsg_RecomputeObligation currentCnf recompute)
    (ay_elsg_NoSemanticClaim diagnostic)
    (ay_elsg_conj_right
      (ay_elsg_EquivalentLiteralSubstitutionGuardFailure
        digestMismatch equivalenceMismatch substitutionMismatch replayMismatch
        reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
        validatorMismatch auditMismatch)
      (ay_elsg_Conj
        (ay_elsg_RecomputeObligation currentCnf recompute)
        (ay_elsg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_elsg_failed_guard_cannot_bless_public_result
    (currentCnf : Prop)
    (digestMismatch equivalenceMismatch substitutionMismatch replayMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_elsg_DiagnosticEquivalentLiteralSubstitutionGuard
      currentCnf digestMismatch equivalenceMismatch substitutionMismatch replayMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_elsg_PublicResult originalCnf model certificate conflict exitCode ->
    ay_elsg_Conj
      (ay_elsg_NoSemanticClaim diagnostic)
      (ay_elsg_RecomputeObligation currentCnf recompute) := by
  intro diagnosticGuard _publicResult
  exact ay_elsg_conj_intro
    (ay_elsg_NoSemanticClaim diagnostic)
    (ay_elsg_RecomputeObligation currentCnf recompute)
    (ay_elsg_diagnostic_no_claim
      currentCnf digestMismatch equivalenceMismatch substitutionMismatch replayMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic diagnosticGuard)
    (ay_elsg_diagnostic_recompute
      currentCnf digestMismatch equivalenceMismatch substitutionMismatch replayMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic diagnosticGuard)

theorem ay_elsg_failed_guard_cannot_bless_public_sat
    (currentCnf : Prop)
    (digestMismatch equivalenceMismatch substitutionMismatch replayMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop) (exitCode : Prop) :
    ay_elsg_DiagnosticEquivalentLiteralSubstitutionGuard
      currentCnf digestMismatch equivalenceMismatch substitutionMismatch replayMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_elsg_ExitCodeSound exitCode (ay_elsg_Sat originalCnf model) ->
    ay_elsg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _satClaim
  exact ay_elsg_diagnostic_no_claim
    currentCnf digestMismatch equivalenceMismatch substitutionMismatch replayMismatch
    reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
    validatorMismatch auditMismatch recompute diagnostic diagnosticGuard

theorem ay_elsg_failed_guard_cannot_bless_public_unsat
    (currentCnf : Prop)
    (digestMismatch equivalenceMismatch substitutionMismatch replayMismatch : Prop)
    (reconstructionMismatch checkerMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (certificate : Prop) (conflict : Prop)
    (exitCode : Prop) :
    ay_elsg_DiagnosticEquivalentLiteralSubstitutionGuard
      currentCnf digestMismatch equivalenceMismatch substitutionMismatch replayMismatch
      reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_elsg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_elsg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _unsatClaim
  exact ay_elsg_diagnostic_no_claim
    currentCnf digestMismatch equivalenceMismatch substitutionMismatch replayMismatch
    reconstructionMismatch checkerMismatch baselineMismatch buildMismatch
    validatorMismatch auditMismatch recompute diagnostic diagnosticGuard
