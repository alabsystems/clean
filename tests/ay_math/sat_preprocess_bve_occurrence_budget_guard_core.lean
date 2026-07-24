-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded-variable-elimination occurrence-budget guard soundness.
-- The propositions stand for formula digests, occurrence and resolvent ledgers,
-- tautology policy, deletion ledgers, model/proof reconstruction, budget
-- manifests, fallback/build/validator gates, audit transcripts, diagnostics,
-- and public SAT/UNSAT reports.

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

def ay_bveg_OriginalFormulaDigest
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop) :=
  ay_bveg_Conj formulaManifest (formulaDigest -> formulaDigestAccepted)

def ay_bveg_CandidateOccurrenceLedger
    (occurrenceLedger : Prop) (occurrenceAccepted : Prop)
    (candidateVariableCoverage : Prop) :=
  ay_bveg_Conj candidateVariableCoverage
    (occurrenceLedger -> occurrenceAccepted)

def ay_bveg_ResolventGenerationLedger
    (resolventLedger : Prop) (resolventAccepted : Prop)
    (resolventCoverage : Prop) :=
  ay_bveg_Conj resolventCoverage (resolventLedger -> resolventAccepted)

def ay_bveg_TautologyPolicy
    (tautologyPolicy : Prop) (tautologyAccepted : Prop)
    (tautologyCoverage : Prop) :=
  ay_bveg_Conj tautologyCoverage (tautologyPolicy -> tautologyAccepted)

def ay_bveg_ClauseDeletionLedger
    (deletionLedger : Prop) (deletionAccepted : Prop)
    (deletedClauseCoverage : Prop) :=
  ay_bveg_Conj deletedClauseCoverage (deletionLedger -> deletionAccepted)

def ay_bveg_ModelExtensionWitness
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :=
  ay_bveg_Sat reducedCnf reducedModel ->
    ay_bveg_Sat originalCnf originalModel

def ay_bveg_UnsatProofReconstructionWitness
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_bveg_Replay reducedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_bveg_ReconstructionWitnesses
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_bveg_Conj
    (ay_bveg_ModelExtensionWitness
      reducedCnf originalCnf reducedModel originalModel)
    (ay_bveg_UnsatProofReconstructionWitness
      originalCnf reducedCnf certificate conflict)

def ay_bveg_BudgetCutoffManifest
    (budgetManifest : Prop) (budgetAccepted : Prop)
    (cutoffPolicy : Prop) :=
  ay_bveg_Conj cutoffPolicy (budgetManifest -> budgetAccepted)

def ay_bveg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_bveg_Conj baselineSolver baselineAvailable

def ay_bveg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_bveg_Conj binaryFingerprint buildReproducible

def ay_bveg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_bveg_Conj validatorAccepted validatorVersion

def ay_bveg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_bveg_Conj auditAppended auditAppendOnly

def ay_bveg_AcceptedBveOccurrenceBudgetGuard
    (originalCnf : Prop) (reducedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (occurrenceLedger : Prop) (occurrenceAccepted : Prop)
    (candidateVariableCoverage : Prop)
    (resolventLedger : Prop) (resolventAccepted : Prop)
    (resolventCoverage : Prop)
    (tautologyPolicy : Prop) (tautologyAccepted : Prop)
    (tautologyCoverage : Prop)
    (deletionLedger : Prop) (deletionAccepted : Prop)
    (deletedClauseCoverage : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (budgetManifest : Prop) (budgetAccepted : Prop)
    (cutoffPolicy : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_bveg_OriginalFormulaDigest
       formulaDigest formulaDigestAccepted formulaManifest ->
     ay_bveg_CandidateOccurrenceLedger
       occurrenceLedger occurrenceAccepted candidateVariableCoverage ->
     ay_bveg_ResolventGenerationLedger
       resolventLedger resolventAccepted resolventCoverage ->
     ay_bveg_TautologyPolicy
       tautologyPolicy tautologyAccepted tautologyCoverage ->
     ay_bveg_ClauseDeletionLedger
       deletionLedger deletionAccepted deletedClauseCoverage ->
     ay_bveg_ReconstructionWitnesses
       reducedCnf originalCnf reducedModel originalModel certificate conflict ->
     ay_bveg_BudgetCutoffManifest
       budgetManifest budgetAccepted cutoffPolicy ->
     ay_bveg_Equisat originalCnf reducedCnf ->
     ay_bveg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_bveg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_bveg_ValidatorGate validatorAccepted validatorVersion ->
     ay_bveg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_bveg_BveGuardFailure
    (digestMismatch : Prop) (occurrenceMismatch : Prop)
    (resolventMismatch : Prop) (tautologyMismatch : Prop)
    (deletionMismatch : Prop) (extensionMismatch : Prop)
    (reconstructionMismatch : Prop) (budgetMismatch : Prop)
    (baselineMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (digestMismatch -> result) ->
    (occurrenceMismatch -> result) ->
    (resolventMismatch -> result) ->
    (tautologyMismatch -> result) ->
    (deletionMismatch -> result) ->
    (extensionMismatch -> result) ->
    (reconstructionMismatch -> result) ->
    (budgetMismatch -> result) ->
    (baselineMismatch -> result) ->
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
    (digestMismatch : Prop) (occurrenceMismatch : Prop)
    (resolventMismatch : Prop) (tautologyMismatch : Prop)
    (deletionMismatch : Prop) (extensionMismatch : Prop)
    (reconstructionMismatch : Prop) (budgetMismatch : Prop)
    (baselineMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_bveg_Conj
    (ay_bveg_BveGuardFailure
      digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch
      deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch
      baselineMismatch buildMismatch validatorMismatch auditMismatch)
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

theorem ay_bveg_original_formula_digest_applies
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop) :
    ay_bveg_OriginalFormulaDigest
      formulaDigest formulaDigestAccepted formulaManifest ->
    formulaDigest -> formulaDigestAccepted := by
  intro digest
  exact ay_bveg_conj_right
    formulaManifest (formulaDigest -> formulaDigestAccepted) digest

theorem ay_bveg_candidate_occurrence_ledger_applies
    (occurrenceLedger : Prop) (occurrenceAccepted : Prop)
    (candidateVariableCoverage : Prop) :
    ay_bveg_CandidateOccurrenceLedger
      occurrenceLedger occurrenceAccepted candidateVariableCoverage ->
    occurrenceLedger -> occurrenceAccepted := by
  intro ledger
  exact ay_bveg_conj_right
    candidateVariableCoverage (occurrenceLedger -> occurrenceAccepted) ledger

theorem ay_bveg_resolvent_generation_ledger_applies
    (resolventLedger : Prop) (resolventAccepted : Prop)
    (resolventCoverage : Prop) :
    ay_bveg_ResolventGenerationLedger
      resolventLedger resolventAccepted resolventCoverage ->
    resolventLedger -> resolventAccepted := by
  intro ledger
  exact ay_bveg_conj_right
    resolventCoverage (resolventLedger -> resolventAccepted) ledger

theorem ay_bveg_tautology_policy_applies
    (tautologyPolicy : Prop) (tautologyAccepted : Prop)
    (tautologyCoverage : Prop) :
    ay_bveg_TautologyPolicy
      tautologyPolicy tautologyAccepted tautologyCoverage ->
    tautologyPolicy -> tautologyAccepted := by
  intro policy
  exact ay_bveg_conj_right
    tautologyCoverage (tautologyPolicy -> tautologyAccepted) policy

theorem ay_bveg_clause_deletion_ledger_applies
    (deletionLedger : Prop) (deletionAccepted : Prop)
    (deletedClauseCoverage : Prop) :
    ay_bveg_ClauseDeletionLedger
      deletionLedger deletionAccepted deletedClauseCoverage ->
    deletionLedger -> deletionAccepted := by
  intro ledger
  exact ay_bveg_conj_right
    deletedClauseCoverage (deletionLedger -> deletionAccepted) ledger

theorem ay_bveg_budget_cutoff_manifest_applies
    (budgetManifest : Prop) (budgetAccepted : Prop)
    (cutoffPolicy : Prop) :
    ay_bveg_BudgetCutoffManifest
      budgetManifest budgetAccepted cutoffPolicy ->
    budgetManifest -> budgetAccepted := by
  intro budget
  exact ay_bveg_conj_right
    cutoffPolicy (budgetManifest -> budgetAccepted) budget

theorem ay_bveg_model_extension
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_bveg_ReconstructionWitnesses
      reducedCnf originalCnf reducedModel originalModel certificate conflict ->
    ay_bveg_Sat reducedCnf reducedModel ->
    ay_bveg_Sat originalCnf originalModel := by
  intro witnesses
  exact ay_bveg_conj_left
    (ay_bveg_ModelExtensionWitness
      reducedCnf originalCnf reducedModel originalModel)
    (ay_bveg_UnsatProofReconstructionWitness
      originalCnf reducedCnf certificate conflict)
    witnesses

theorem ay_bveg_unsat_proof_reconstruction
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_bveg_ReconstructionWitnesses
      reducedCnf originalCnf reducedModel originalModel certificate conflict ->
    ay_bveg_Replay reducedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses
  exact ay_bveg_conj_right
    (ay_bveg_ModelExtensionWitness
      reducedCnf originalCnf reducedModel originalModel)
    (ay_bveg_UnsatProofReconstructionWitness
      originalCnf reducedCnf certificate conflict)
    witnesses

theorem ay_bveg_accepted_equisat
    (originalCnf : Prop) (reducedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (occurrenceLedger : Prop) (occurrenceAccepted : Prop)
    (candidateVariableCoverage : Prop)
    (resolventLedger : Prop) (resolventAccepted : Prop)
    (resolventCoverage : Prop)
    (tautologyPolicy : Prop) (tautologyAccepted : Prop)
    (tautologyCoverage : Prop)
    (deletionLedger : Prop) (deletionAccepted : Prop)
    (deletedClauseCoverage : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (budgetManifest : Prop) (budgetAccepted : Prop)
    (cutoffPolicy : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_bveg_AcceptedBveOccurrenceBudgetGuard
      originalCnf reducedCnf
      formulaDigest formulaDigestAccepted formulaManifest
      occurrenceLedger occurrenceAccepted candidateVariableCoverage
      resolventLedger resolventAccepted resolventCoverage
      tautologyPolicy tautologyAccepted tautologyCoverage
      deletionLedger deletionAccepted deletedClauseCoverage
      reducedModel originalModel certificate conflict
      budgetManifest budgetAccepted cutoffPolicy
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_bveg_Equisat originalCnf reducedCnf := by
  intro accepted
  exact accepted (ay_bveg_Equisat originalCnf reducedCnf)
    (fun _digestOk _occurrenceOk _resolventOk _tautologyOk _deletionOk
      _reconstruct _budgetOk eqsat _fallback _build _validator _audit => eqsat)

theorem ay_bveg_accepted_reconstruction
    (originalCnf : Prop) (reducedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (occurrenceLedger : Prop) (occurrenceAccepted : Prop)
    (candidateVariableCoverage : Prop)
    (resolventLedger : Prop) (resolventAccepted : Prop)
    (resolventCoverage : Prop)
    (tautologyPolicy : Prop) (tautologyAccepted : Prop)
    (tautologyCoverage : Prop)
    (deletionLedger : Prop) (deletionAccepted : Prop)
    (deletedClauseCoverage : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (budgetManifest : Prop) (budgetAccepted : Prop)
    (cutoffPolicy : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_bveg_AcceptedBveOccurrenceBudgetGuard
      originalCnf reducedCnf
      formulaDigest formulaDigestAccepted formulaManifest
      occurrenceLedger occurrenceAccepted candidateVariableCoverage
      resolventLedger resolventAccepted resolventCoverage
      tautologyPolicy tautologyAccepted tautologyCoverage
      deletionLedger deletionAccepted deletedClauseCoverage
      reducedModel originalModel certificate conflict
      budgetManifest budgetAccepted cutoffPolicy
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_bveg_ReconstructionWitnesses
      reducedCnf originalCnf reducedModel originalModel certificate conflict := by
  intro accepted
  exact accepted
    (ay_bveg_ReconstructionWitnesses
      reducedCnf originalCnf reducedModel originalModel certificate conflict)
    (fun _digestOk _occurrenceOk _resolventOk _tautologyOk _deletionOk
      reconstruct _budgetOk _eqsat _fallback _build _validator _audit => reconstruct)

theorem ay_bveg_sat_pullback
    (originalCnf : Prop) (reducedCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_bveg_ReconstructionWitnesses
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
    ay_bveg_ReconstructionWitnesses
      reducedCnf originalCnf reducedModel originalModel certificate conflict ->
    ay_bveg_Replay reducedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses replay
  exact ay_bveg_unsat_proof_reconstruction
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

theorem ay_bveg_failure_digest
    (digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch : Prop)
    (deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch : Prop)
    (baselineMismatch buildMismatch validatorMismatch auditMismatch : Prop) :
    digestMismatch ->
    ay_bveg_BveGuardFailure
      digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch
      deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch
      baselineMismatch buildMismatch validatorMismatch auditMismatch := by
  intro h result digest_case _occurrence_case _resolvent_case _tautology_case
    _deletion_case _extension_case _reconstruction_case _budget_case
    _baseline_case _build_case _validator_case _audit_case
  exact digest_case h

theorem ay_bveg_failure_occurrence
    (digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch : Prop)
    (deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch : Prop)
    (baselineMismatch buildMismatch validatorMismatch auditMismatch : Prop) :
    occurrenceMismatch ->
    ay_bveg_BveGuardFailure
      digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch
      deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch
      baselineMismatch buildMismatch validatorMismatch auditMismatch := by
  intro h result _digest_case occurrence_case _resolvent_case _tautology_case
    _deletion_case _extension_case _reconstruction_case _budget_case
    _baseline_case _build_case _validator_case _audit_case
  exact occurrence_case h

theorem ay_bveg_failure_resolvent
    (digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch : Prop)
    (deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch : Prop)
    (baselineMismatch buildMismatch validatorMismatch auditMismatch : Prop) :
    resolventMismatch ->
    ay_bveg_BveGuardFailure
      digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch
      deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch
      baselineMismatch buildMismatch validatorMismatch auditMismatch := by
  intro h result _digest_case _occurrence_case resolvent_case _tautology_case
    _deletion_case _extension_case _reconstruction_case _budget_case
    _baseline_case _build_case _validator_case _audit_case
  exact resolvent_case h

theorem ay_bveg_failure_tautology
    (digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch : Prop)
    (deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch : Prop)
    (baselineMismatch buildMismatch validatorMismatch auditMismatch : Prop) :
    tautologyMismatch ->
    ay_bveg_BveGuardFailure
      digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch
      deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch
      baselineMismatch buildMismatch validatorMismatch auditMismatch := by
  intro h result _digest_case _occurrence_case _resolvent_case tautology_case
    _deletion_case _extension_case _reconstruction_case _budget_case
    _baseline_case _build_case _validator_case _audit_case
  exact tautology_case h

theorem ay_bveg_failure_deletion
    (digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch : Prop)
    (deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch : Prop)
    (baselineMismatch buildMismatch validatorMismatch auditMismatch : Prop) :
    deletionMismatch ->
    ay_bveg_BveGuardFailure
      digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch
      deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch
      baselineMismatch buildMismatch validatorMismatch auditMismatch := by
  intro h result _digest_case _occurrence_case _resolvent_case _tautology_case
    deletion_case _extension_case _reconstruction_case _budget_case
    _baseline_case _build_case _validator_case _audit_case
  exact deletion_case h

theorem ay_bveg_failure_extension
    (digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch : Prop)
    (deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch : Prop)
    (baselineMismatch buildMismatch validatorMismatch auditMismatch : Prop) :
    extensionMismatch ->
    ay_bveg_BveGuardFailure
      digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch
      deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch
      baselineMismatch buildMismatch validatorMismatch auditMismatch := by
  intro h result _digest_case _occurrence_case _resolvent_case _tautology_case
    _deletion_case extension_case _reconstruction_case _budget_case
    _baseline_case _build_case _validator_case _audit_case
  exact extension_case h

theorem ay_bveg_failure_reconstruction
    (digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch : Prop)
    (deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch : Prop)
    (baselineMismatch buildMismatch validatorMismatch auditMismatch : Prop) :
    reconstructionMismatch ->
    ay_bveg_BveGuardFailure
      digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch
      deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch
      baselineMismatch buildMismatch validatorMismatch auditMismatch := by
  intro h result _digest_case _occurrence_case _resolvent_case _tautology_case
    _deletion_case _extension_case reconstruction_case _budget_case
    _baseline_case _build_case _validator_case _audit_case
  exact reconstruction_case h

theorem ay_bveg_failure_budget
    (digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch : Prop)
    (deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch : Prop)
    (baselineMismatch buildMismatch validatorMismatch auditMismatch : Prop) :
    budgetMismatch ->
    ay_bveg_BveGuardFailure
      digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch
      deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch
      baselineMismatch buildMismatch validatorMismatch auditMismatch := by
  intro h result _digest_case _occurrence_case _resolvent_case _tautology_case
    _deletion_case _extension_case _reconstruction_case budget_case
    _baseline_case _build_case _validator_case _audit_case
  exact budget_case h

theorem ay_bveg_failure_baseline
    (digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch : Prop)
    (deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch : Prop)
    (baselineMismatch buildMismatch validatorMismatch auditMismatch : Prop) :
    baselineMismatch ->
    ay_bveg_BveGuardFailure
      digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch
      deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch
      baselineMismatch buildMismatch validatorMismatch auditMismatch := by
  intro h result _digest_case _occurrence_case _resolvent_case _tautology_case
    _deletion_case _extension_case _reconstruction_case _budget_case
    baseline_case _build_case _validator_case _audit_case
  exact baseline_case h

theorem ay_bveg_failure_build
    (digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch : Prop)
    (deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch : Prop)
    (baselineMismatch buildMismatch validatorMismatch auditMismatch : Prop) :
    buildMismatch ->
    ay_bveg_BveGuardFailure
      digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch
      deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch
      baselineMismatch buildMismatch validatorMismatch auditMismatch := by
  intro h result _digest_case _occurrence_case _resolvent_case _tautology_case
    _deletion_case _extension_case _reconstruction_case _budget_case
    _baseline_case build_case _validator_case _audit_case
  exact build_case h

theorem ay_bveg_failure_validator
    (digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch : Prop)
    (deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch : Prop)
    (baselineMismatch buildMismatch validatorMismatch auditMismatch : Prop) :
    validatorMismatch ->
    ay_bveg_BveGuardFailure
      digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch
      deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch
      baselineMismatch buildMismatch validatorMismatch auditMismatch := by
  intro h result _digest_case _occurrence_case _resolvent_case _tautology_case
    _deletion_case _extension_case _reconstruction_case _budget_case
    _baseline_case _build_case validator_case _audit_case
  exact validator_case h

theorem ay_bveg_failure_audit
    (digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch : Prop)
    (deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch : Prop)
    (baselineMismatch buildMismatch validatorMismatch auditMismatch : Prop) :
    auditMismatch ->
    ay_bveg_BveGuardFailure
      digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch
      deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch
      baselineMismatch buildMismatch validatorMismatch auditMismatch := by
  intro h result _digest_case _occurrence_case _resolvent_case _tautology_case
    _deletion_case _extension_case _reconstruction_case _budget_case
    _baseline_case _build_case _validator_case audit_case
  exact audit_case h

theorem ay_bveg_diagnostic_no_claim
    (currentCnf : Prop)
    (digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch : Prop)
    (deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch : Prop)
    (baselineMismatch buildMismatch validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_bveg_DiagnosticBveGuard
      currentCnf digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch
      deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch
      baselineMismatch buildMismatch validatorMismatch auditMismatch
      recompute diagnostic ->
    ay_bveg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard
  exact ay_bveg_conj_right
    (ay_bveg_RecomputeObligation currentCnf recompute)
    (ay_bveg_NoSemanticClaim diagnostic)
    (ay_bveg_conj_right
      (ay_bveg_BveGuardFailure
        digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch
        deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch
        baselineMismatch buildMismatch validatorMismatch auditMismatch)
      (ay_bveg_Conj
        (ay_bveg_RecomputeObligation currentCnf recompute)
        (ay_bveg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_bveg_diagnostic_recompute
    (currentCnf : Prop)
    (digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch : Prop)
    (deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch : Prop)
    (baselineMismatch buildMismatch validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_bveg_DiagnosticBveGuard
      currentCnf digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch
      deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch
      baselineMismatch buildMismatch validatorMismatch auditMismatch
      recompute diagnostic ->
    ay_bveg_RecomputeObligation currentCnf recompute := by
  intro diagnosticGuard
  exact ay_bveg_conj_left
    (ay_bveg_RecomputeObligation currentCnf recompute)
    (ay_bveg_NoSemanticClaim diagnostic)
    (ay_bveg_conj_right
      (ay_bveg_BveGuardFailure
        digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch
        deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch
        baselineMismatch buildMismatch validatorMismatch auditMismatch)
      (ay_bveg_Conj
        (ay_bveg_RecomputeObligation currentCnf recompute)
        (ay_bveg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_bveg_failed_bve_cannot_bless_public_result
    (currentCnf : Prop)
    (digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch : Prop)
    (deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch : Prop)
    (baselineMismatch buildMismatch validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_bveg_DiagnosticBveGuard
      currentCnf digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch
      deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch
      baselineMismatch buildMismatch validatorMismatch auditMismatch
      recompute diagnostic ->
    ay_bveg_PublicResult originalCnf model certificate conflict exitCode ->
    ay_bveg_Conj
      (ay_bveg_NoSemanticClaim diagnostic)
      (ay_bveg_RecomputeObligation currentCnf recompute) := by
  intro diagnosticGuard _publicResult
  exact ay_bveg_conj_intro
    (ay_bveg_NoSemanticClaim diagnostic)
    (ay_bveg_RecomputeObligation currentCnf recompute)
    (ay_bveg_diagnostic_no_claim
      currentCnf digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch
      deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch
      baselineMismatch buildMismatch validatorMismatch auditMismatch
      recompute diagnostic diagnosticGuard)
    (ay_bveg_diagnostic_recompute
      currentCnf digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch
      deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch
      baselineMismatch buildMismatch validatorMismatch auditMismatch
      recompute diagnostic diagnosticGuard)

theorem ay_bveg_failed_bve_cannot_bless_public_sat
    (currentCnf : Prop)
    (digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch : Prop)
    (deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch : Prop)
    (baselineMismatch buildMismatch validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop) (exitCode : Prop) :
    ay_bveg_DiagnosticBveGuard
      currentCnf digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch
      deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch
      baselineMismatch buildMismatch validatorMismatch auditMismatch
      recompute diagnostic ->
    ay_bveg_ExitCodeSound exitCode (ay_bveg_Sat originalCnf model) ->
    ay_bveg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _satClaim
  exact ay_bveg_diagnostic_no_claim
    currentCnf digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch
    deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch
    baselineMismatch buildMismatch validatorMismatch auditMismatch
    recompute diagnostic diagnosticGuard

theorem ay_bveg_failed_bve_cannot_bless_public_unsat
    (currentCnf : Prop)
    (digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch : Prop)
    (deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch : Prop)
    (baselineMismatch buildMismatch validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (certificate : Prop) (conflict : Prop)
    (exitCode : Prop) :
    ay_bveg_DiagnosticBveGuard
      currentCnf digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch
      deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch
      baselineMismatch buildMismatch validatorMismatch auditMismatch
      recompute diagnostic ->
    ay_bveg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_bveg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _unsatClaim
  exact ay_bveg_diagnostic_no_claim
    currentCnf digestMismatch occurrenceMismatch resolventMismatch tautologyMismatch
    deletionMismatch extensionMismatch reconstructionMismatch budgetMismatch
    baselineMismatch buildMismatch validatorMismatch auditMismatch
    recompute diagnostic diagnosticGuard
