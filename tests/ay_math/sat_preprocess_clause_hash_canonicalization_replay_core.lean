-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Clause-hash canonicalization replay soundness for preprocessing. The
-- propositions stand for canonical literal order, duplicate/tautology
-- accounting, original-clause coverage, canonicalization ledgers, formula
-- fingerprints, checker replay, fallback baseline, build evidence, validator
-- gates, audit evidence, diagnostics, and public SAT/UNSAT reports.

def ay_pchc_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pchc_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pchc_Equisat (before : Prop) (after : Prop) :=
  ay_pchc_Conj (before -> after) (after -> before)

def ay_pchc_Sat (cnf : Prop) (model : Prop) :=
  ay_pchc_Conj cnf model

def ay_pchc_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pchc_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pchc_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pchc_CanonicalLiteralOrder
    (rawClauseHash : Prop) (canonicalClauseHash : Prop)
    (literalOrderWitness : Prop) :=
  ay_pchc_Conj literalOrderWitness
    (rawClauseHash -> canonicalClauseHash)

def ay_pchc_DuplicateTautologyAccounting
    (duplicateAccounted : Prop) (tautologyAccounted : Prop)
    (accountingLedger : Prop) :=
  ay_pchc_Conj accountingLedger
    (ay_pchc_Conj duplicateAccounted tautologyAccounted)

def ay_pchc_OriginalClauseCoverage
    (originalClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :=
  ay_pchc_Conj coverageWitness (originalClause -> coveredClause)

def ay_pchc_CanonicalizationLedger
    (canonicalizationLedger : Prop) (canonicalClauseHash : Prop)
    (ledgerWitness : Prop) :=
  ay_pchc_Conj ledgerWitness
    (canonicalClauseHash -> canonicalizationLedger)

def ay_pchc_ModelReconstruction
    (canonicalCnf : Prop) (originalCnf : Prop)
    (canonicalModel : Prop) (originalModel : Prop) :=
  ay_pchc_Sat canonicalCnf canonicalModel ->
    ay_pchc_Sat originalCnf originalModel

def ay_pchc_ProofReconstruction
    (originalCnf : Prop) (canonicalCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pchc_Replay canonicalCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pchc_FingerprintAgreement
    (originalFingerprint : Prop) (canonicalFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pchc_Conj fingerprintWitness
    (ay_pchc_IdMatch originalFingerprint canonicalFingerprint)

def ay_pchc_CheckerReplay
    (canonicalizationCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pchc_Conj canonicalizationCertificate checkerAccepted

def ay_pchc_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_pchc_Conj baselineSolver baselineAvailable

def ay_pchc_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_pchc_Conj binaryFingerprint buildReproducible

def ay_pchc_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_pchc_Conj validatorAccepted validatorVersion

def ay_pchc_AuditEvidence
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_pchc_Conj auditAppended auditAppendOnly

def ay_pchc_AcceptedClauseHashCanonicalizationReplay
    (originalCnf : Prop) (canonicalCnf : Prop)
    (rawClauseHash : Prop) (canonicalClauseHash : Prop)
    (literalOrderWitness : Prop)
    (duplicateAccounted : Prop) (tautologyAccounted : Prop)
    (accountingLedger : Prop)
    (originalClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (canonicalizationLedger : Prop) (ledgerWitness : Prop)
    (canonicalModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (canonicalFingerprint : Prop)
    (fingerprintWitness : Prop)
    (canonicalizationCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_pchc_CanonicalLiteralOrder
       rawClauseHash canonicalClauseHash literalOrderWitness ->
     ay_pchc_DuplicateTautologyAccounting
       duplicateAccounted tautologyAccounted accountingLedger ->
     ay_pchc_OriginalClauseCoverage
       originalClause coveredClause coverageWitness ->
     ay_pchc_CanonicalizationLedger
       canonicalizationLedger canonicalClauseHash ledgerWitness ->
     ay_pchc_Equisat originalCnf canonicalCnf ->
     ay_pchc_ModelReconstruction
       canonicalCnf originalCnf canonicalModel originalModel ->
     ay_pchc_ProofReconstruction
       originalCnf canonicalCnf certificate conflict ->
     ay_pchc_FingerprintAgreement
       originalFingerprint canonicalFingerprint fingerprintWitness ->
     ay_pchc_CheckerReplay
       canonicalizationCertificate checkerAccepted ->
     ay_pchc_FallbackBaseline baselineSolver baselineAvailable ->
     ay_pchc_BuildEvidence binaryFingerprint buildReproducible ->
     ay_pchc_ValidatorGate validatorAccepted validatorVersion ->
     ay_pchc_AuditEvidence auditAppended auditAppendOnly ->
     result) -> result

def ay_pchc_CanonicalizationFailure
    (hashDrift : Prop) (literalOrderMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :=
  ay_pchc_Disj hashDrift
    (ay_pchc_Disj literalOrderMismatch
      (ay_pchc_Disj coverageGap
        (ay_pchc_Disj staleFingerprint
          (ay_pchc_Disj uncheckedReplay
            (ay_pchc_Disj buildDrift auditContradiction)))))

def ay_pchc_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pchc_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pchc_Conj currentCnf recompute

def ay_pchc_DiagnosticCanonicalizationReplay
    (currentCnf : Prop)
    (hashDrift : Prop) (literalOrderMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pchc_Conj
    (ay_pchc_CanonicalizationFailure
      hashDrift literalOrderMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction)
    (ay_pchc_Conj
      (ay_pchc_RecomputeObligation currentCnf recompute)
      (ay_pchc_NoSemanticClaim diagnostic))

def ay_pchc_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pchc_Conj exitCode claim

def ay_pchc_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pchc_Disj
    (ay_pchc_ExitCodeSound exitCode (ay_pchc_Sat originalCnf model))
    (ay_pchc_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_pchc_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pchc_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pchc_conj_left
    (left : Prop) (right : Prop) :
    ay_pchc_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pchc_conj_right
    (left : Prop) (right : Prop) :
    ay_pchc_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pchc_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pchc_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pchc_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pchc_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pchc_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pchc_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pchc_conj_left (before -> after) (after -> before) eq

theorem ay_pchc_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pchc_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pchc_conj_right (before -> after) (after -> before) eq

theorem ay_pchc_canonical_literal_order_applies
    (rawClauseHash : Prop) (canonicalClauseHash : Prop)
    (literalOrderWitness : Prop) :
    ay_pchc_CanonicalLiteralOrder
      rawClauseHash canonicalClauseHash literalOrderWitness ->
    rawClauseHash ->
    canonicalClauseHash := by
  intro accepted raw
  exact
    (ay_pchc_conj_right literalOrderWitness
      (rawClauseHash -> canonicalClauseHash) accepted) raw

theorem ay_pchc_duplicate_tautology_accounting_duplicate
    (duplicateAccounted : Prop) (tautologyAccounted : Prop)
    (accountingLedger : Prop) :
    ay_pchc_DuplicateTautologyAccounting
      duplicateAccounted tautologyAccounted accountingLedger ->
    duplicateAccounted := by
  intro accepted
  exact accepted duplicateAccounted
    (fun _ledger pair =>
      pair duplicateAccounted
        (fun duplicate _tautology => duplicate))

theorem ay_pchc_duplicate_tautology_accounting_tautology
    (duplicateAccounted : Prop) (tautologyAccounted : Prop)
    (accountingLedger : Prop) :
    ay_pchc_DuplicateTautologyAccounting
      duplicateAccounted tautologyAccounted accountingLedger ->
    tautologyAccounted := by
  intro accepted
  exact accepted tautologyAccounted
    (fun _ledger pair =>
      pair tautologyAccounted
        (fun _duplicate tautology => tautology))

theorem ay_pchc_original_clause_coverage
    (originalClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :
    ay_pchc_OriginalClauseCoverage
      originalClause coveredClause coverageWitness ->
    originalClause ->
    coveredClause := by
  intro accepted original
  exact
    (ay_pchc_conj_right coverageWitness
      (originalClause -> coveredClause) accepted) original

theorem ay_pchc_canonicalization_ledger_records
    (canonicalizationLedger : Prop) (canonicalClauseHash : Prop)
    (ledgerWitness : Prop) :
    ay_pchc_CanonicalizationLedger
      canonicalizationLedger canonicalClauseHash ledgerWitness ->
    canonicalClauseHash ->
    canonicalizationLedger := by
  intro accepted canonical
  exact
    (ay_pchc_conj_right ledgerWitness
      (canonicalClauseHash -> canonicalizationLedger) accepted) canonical

theorem ay_pchc_accepted_equisat
    (originalCnf : Prop) (canonicalCnf : Prop)
    (rawClauseHash : Prop) (canonicalClauseHash : Prop)
    (literalOrderWitness : Prop)
    (duplicateAccounted : Prop) (tautologyAccounted : Prop)
    (accountingLedger : Prop)
    (originalClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (canonicalizationLedger : Prop) (ledgerWitness : Prop)
    (canonicalModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (canonicalFingerprint : Prop)
    (fingerprintWitness : Prop)
    (canonicalizationCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pchc_AcceptedClauseHashCanonicalizationReplay
      originalCnf canonicalCnf rawClauseHash canonicalClauseHash
      literalOrderWitness duplicateAccounted tautologyAccounted
      accountingLedger originalClause coveredClause coverageWitness
      canonicalizationLedger ledgerWitness canonicalModel originalModel
      certificate conflict originalFingerprint canonicalFingerprint
      fingerprintWitness canonicalizationCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pchc_Equisat originalCnf canonicalCnf := by
  intro accepted
  exact accepted (ay_pchc_Equisat originalCnf canonicalCnf)
    (fun _order _accounting _coverage _ledger eq _model _proof
      _fingerprint _checker _fallback _build _validator _audit => eq)

theorem ay_pchc_accepted_checker_replay
    (originalCnf : Prop) (canonicalCnf : Prop)
    (rawClauseHash : Prop) (canonicalClauseHash : Prop)
    (literalOrderWitness : Prop)
    (duplicateAccounted : Prop) (tautologyAccounted : Prop)
    (accountingLedger : Prop)
    (originalClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (canonicalizationLedger : Prop) (ledgerWitness : Prop)
    (canonicalModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (canonicalFingerprint : Prop)
    (fingerprintWitness : Prop)
    (canonicalizationCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pchc_AcceptedClauseHashCanonicalizationReplay
      originalCnf canonicalCnf rawClauseHash canonicalClauseHash
      literalOrderWitness duplicateAccounted tautologyAccounted
      accountingLedger originalClause coveredClause coverageWitness
      canonicalizationLedger ledgerWitness canonicalModel originalModel
      certificate conflict originalFingerprint canonicalFingerprint
      fingerprintWitness canonicalizationCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pchc_CheckerReplay canonicalizationCertificate checkerAccepted := by
  intro accepted
  exact accepted
    (ay_pchc_CheckerReplay canonicalizationCertificate checkerAccepted)
    (fun _order _accounting _coverage _ledger _eq _model _proof
      _fingerprint checker _fallback _build _validator _audit => checker)

theorem ay_pchc_accepted_audit_evidence
    (originalCnf : Prop) (canonicalCnf : Prop)
    (rawClauseHash : Prop) (canonicalClauseHash : Prop)
    (literalOrderWitness : Prop)
    (duplicateAccounted : Prop) (tautologyAccounted : Prop)
    (accountingLedger : Prop)
    (originalClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (canonicalizationLedger : Prop) (ledgerWitness : Prop)
    (canonicalModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (canonicalFingerprint : Prop)
    (fingerprintWitness : Prop)
    (canonicalizationCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pchc_AcceptedClauseHashCanonicalizationReplay
      originalCnf canonicalCnf rawClauseHash canonicalClauseHash
      literalOrderWitness duplicateAccounted tautologyAccounted
      accountingLedger originalClause coveredClause coverageWitness
      canonicalizationLedger ledgerWitness canonicalModel originalModel
      certificate conflict originalFingerprint canonicalFingerprint
      fingerprintWitness canonicalizationCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pchc_AuditEvidence auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_pchc_AuditEvidence auditAppended auditAppendOnly)
    (fun _order _accounting _coverage _ledger _eq _model _proof
      _fingerprint _checker _fallback _build _validator audit => audit)

theorem ay_pchc_sat_pullback
    (canonicalCnf : Prop) (originalCnf : Prop)
    (canonicalModel : Prop) (originalModel : Prop) :
    ay_pchc_ModelReconstruction
      canonicalCnf originalCnf canonicalModel originalModel ->
    ay_pchc_Sat canonicalCnf canonicalModel ->
    ay_pchc_Sat originalCnf originalModel := by
  intro reconstruct canonicalSat
  exact reconstruct canonicalSat

theorem ay_pchc_unsat_pushback
    (originalCnf : Prop) (canonicalCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pchc_ProofReconstruction
      originalCnf canonicalCnf certificate conflict ->
    ay_pchc_Replay canonicalCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro reconstruct replay cert original
  exact reconstruct replay cert original

theorem ay_pchc_public_sat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    ay_pchc_Sat originalCnf model ->
    ay_pchc_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit sat
  exact ay_pchc_disj_left
    (ay_pchc_ExitCodeSound exitCode (ay_pchc_Sat originalCnf model))
    (ay_pchc_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pchc_conj_intro exitCode
      (ay_pchc_Sat originalCnf model) exit sat)

theorem ay_pchc_public_unsat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    (certificate -> originalCnf -> conflict) ->
    ay_pchc_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit replay
  exact ay_pchc_disj_right
    (ay_pchc_ExitCodeSound exitCode (ay_pchc_Sat originalCnf model))
    (ay_pchc_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pchc_conj_intro exitCode
      (certificate -> originalCnf -> conflict) exit replay)

theorem ay_pchc_failure_hash_drift
    (hashDrift : Prop) (literalOrderMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    hashDrift ->
    ay_pchc_CanonicalizationFailure
      hashDrift literalOrderMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction := by
  intro drift
  exact ay_pchc_disj_left hashDrift
    (ay_pchc_Disj literalOrderMismatch
      (ay_pchc_Disj coverageGap
        (ay_pchc_Disj staleFingerprint
          (ay_pchc_Disj uncheckedReplay
            (ay_pchc_Disj buildDrift auditContradiction)))))
    drift

theorem ay_pchc_failure_literal_order_mismatch
    (hashDrift : Prop) (literalOrderMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    literalOrderMismatch ->
    ay_pchc_CanonicalizationFailure
      hashDrift literalOrderMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction := by
  intro mismatch
  exact ay_pchc_disj_right hashDrift
    (ay_pchc_Disj literalOrderMismatch
      (ay_pchc_Disj coverageGap
        (ay_pchc_Disj staleFingerprint
          (ay_pchc_Disj uncheckedReplay
            (ay_pchc_Disj buildDrift auditContradiction)))))
    (ay_pchc_disj_left literalOrderMismatch
      (ay_pchc_Disj coverageGap
        (ay_pchc_Disj staleFingerprint
          (ay_pchc_Disj uncheckedReplay
            (ay_pchc_Disj buildDrift auditContradiction))))
      mismatch)

theorem ay_pchc_failure_coverage_gap
    (hashDrift : Prop) (literalOrderMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    coverageGap ->
    ay_pchc_CanonicalizationFailure
      hashDrift literalOrderMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction := by
  intro gap
  exact ay_pchc_disj_right hashDrift
    (ay_pchc_Disj literalOrderMismatch
      (ay_pchc_Disj coverageGap
        (ay_pchc_Disj staleFingerprint
          (ay_pchc_Disj uncheckedReplay
            (ay_pchc_Disj buildDrift auditContradiction)))))
    (ay_pchc_disj_right literalOrderMismatch
      (ay_pchc_Disj coverageGap
        (ay_pchc_Disj staleFingerprint
          (ay_pchc_Disj uncheckedReplay
            (ay_pchc_Disj buildDrift auditContradiction))))
      (ay_pchc_disj_left coverageGap
        (ay_pchc_Disj staleFingerprint
          (ay_pchc_Disj uncheckedReplay
            (ay_pchc_Disj buildDrift auditContradiction)))
        gap))

theorem ay_pchc_failure_stale_fingerprint
    (hashDrift : Prop) (literalOrderMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_pchc_CanonicalizationFailure
      hashDrift literalOrderMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction := by
  intro stale
  exact ay_pchc_disj_right hashDrift
    (ay_pchc_Disj literalOrderMismatch
      (ay_pchc_Disj coverageGap
        (ay_pchc_Disj staleFingerprint
          (ay_pchc_Disj uncheckedReplay
            (ay_pchc_Disj buildDrift auditContradiction)))))
    (ay_pchc_disj_right literalOrderMismatch
      (ay_pchc_Disj coverageGap
        (ay_pchc_Disj staleFingerprint
          (ay_pchc_Disj uncheckedReplay
            (ay_pchc_Disj buildDrift auditContradiction))))
      (ay_pchc_disj_right coverageGap
        (ay_pchc_Disj staleFingerprint
          (ay_pchc_Disj uncheckedReplay
            (ay_pchc_Disj buildDrift auditContradiction)))
        (ay_pchc_disj_left staleFingerprint
          (ay_pchc_Disj uncheckedReplay
            (ay_pchc_Disj buildDrift auditContradiction))
          stale)))

theorem ay_pchc_failure_unchecked_replay
    (hashDrift : Prop) (literalOrderMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_pchc_CanonicalizationFailure
      hashDrift literalOrderMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction := by
  intro unchecked
  exact ay_pchc_disj_right hashDrift
    (ay_pchc_Disj literalOrderMismatch
      (ay_pchc_Disj coverageGap
        (ay_pchc_Disj staleFingerprint
          (ay_pchc_Disj uncheckedReplay
            (ay_pchc_Disj buildDrift auditContradiction)))))
    (ay_pchc_disj_right literalOrderMismatch
      (ay_pchc_Disj coverageGap
        (ay_pchc_Disj staleFingerprint
          (ay_pchc_Disj uncheckedReplay
            (ay_pchc_Disj buildDrift auditContradiction))))
      (ay_pchc_disj_right coverageGap
        (ay_pchc_Disj staleFingerprint
          (ay_pchc_Disj uncheckedReplay
            (ay_pchc_Disj buildDrift auditContradiction)))
        (ay_pchc_disj_right staleFingerprint
          (ay_pchc_Disj uncheckedReplay
            (ay_pchc_Disj buildDrift auditContradiction))
          (ay_pchc_disj_left uncheckedReplay
            (ay_pchc_Disj buildDrift auditContradiction)
            unchecked))))

theorem ay_pchc_failure_build_drift
    (hashDrift : Prop) (literalOrderMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_pchc_CanonicalizationFailure
      hashDrift literalOrderMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction := by
  intro drift
  exact ay_pchc_disj_right hashDrift
    (ay_pchc_Disj literalOrderMismatch
      (ay_pchc_Disj coverageGap
        (ay_pchc_Disj staleFingerprint
          (ay_pchc_Disj uncheckedReplay
            (ay_pchc_Disj buildDrift auditContradiction)))))
    (ay_pchc_disj_right literalOrderMismatch
      (ay_pchc_Disj coverageGap
        (ay_pchc_Disj staleFingerprint
          (ay_pchc_Disj uncheckedReplay
            (ay_pchc_Disj buildDrift auditContradiction))))
      (ay_pchc_disj_right coverageGap
        (ay_pchc_Disj staleFingerprint
          (ay_pchc_Disj uncheckedReplay
            (ay_pchc_Disj buildDrift auditContradiction)))
        (ay_pchc_disj_right staleFingerprint
          (ay_pchc_Disj uncheckedReplay
            (ay_pchc_Disj buildDrift auditContradiction))
          (ay_pchc_disj_right uncheckedReplay
            (ay_pchc_Disj buildDrift auditContradiction)
            (ay_pchc_disj_left buildDrift auditContradiction drift)))))

theorem ay_pchc_failure_audit_contradiction
    (hashDrift : Prop) (literalOrderMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_pchc_CanonicalizationFailure
      hashDrift literalOrderMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction := by
  intro auditBad
  exact ay_pchc_disj_right hashDrift
    (ay_pchc_Disj literalOrderMismatch
      (ay_pchc_Disj coverageGap
        (ay_pchc_Disj staleFingerprint
          (ay_pchc_Disj uncheckedReplay
            (ay_pchc_Disj buildDrift auditContradiction)))))
    (ay_pchc_disj_right literalOrderMismatch
      (ay_pchc_Disj coverageGap
        (ay_pchc_Disj staleFingerprint
          (ay_pchc_Disj uncheckedReplay
            (ay_pchc_Disj buildDrift auditContradiction))))
      (ay_pchc_disj_right coverageGap
        (ay_pchc_Disj staleFingerprint
          (ay_pchc_Disj uncheckedReplay
            (ay_pchc_Disj buildDrift auditContradiction)))
        (ay_pchc_disj_right staleFingerprint
          (ay_pchc_Disj uncheckedReplay
            (ay_pchc_Disj buildDrift auditContradiction))
          (ay_pchc_disj_right uncheckedReplay
            (ay_pchc_Disj buildDrift auditContradiction)
            (ay_pchc_disj_right buildDrift auditContradiction
              auditBad)))))

theorem ay_pchc_diagnostic_no_claim
    (currentCnf : Prop)
    (hashDrift : Prop) (literalOrderMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pchc_DiagnosticCanonicalizationReplay
      currentCnf hashDrift literalOrderMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction recompute diagnostic ->
    ay_pchc_NoSemanticClaim diagnostic := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pchc_NoSemanticClaim diagnostic)
    (fun _failure tail =>
      tail (ay_pchc_NoSemanticClaim diagnostic)
        (fun _recompute noClaim => noClaim))

theorem ay_pchc_diagnostic_recompute
    (currentCnf : Prop)
    (hashDrift : Prop) (literalOrderMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pchc_DiagnosticCanonicalizationReplay
      currentCnf hashDrift literalOrderMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction recompute diagnostic ->
    ay_pchc_RecomputeObligation currentCnf recompute := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pchc_RecomputeObligation currentCnf recompute)
    (fun _failure tail =>
      tail (ay_pchc_RecomputeObligation currentCnf recompute)
        (fun recomputeObligation _noClaim => recomputeObligation))

theorem ay_pchc_unchecked_replay_cannot_bless_public_result
    (currentCnf : Prop)
    (hashDrift : Prop) (literalOrderMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_pchc_RecomputeObligation currentCnf recompute ->
    ay_pchc_NoSemanticClaim diagnostic ->
    ay_pchc_DiagnosticCanonicalizationReplay
      currentCnf hashDrift literalOrderMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction recompute diagnostic := by
  intro unchecked recomputeObligation noClaim
  exact ay_pchc_conj_intro
    (ay_pchc_CanonicalizationFailure
      hashDrift literalOrderMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction)
    (ay_pchc_Conj
      (ay_pchc_RecomputeObligation currentCnf recompute)
      (ay_pchc_NoSemanticClaim diagnostic))
    (ay_pchc_failure_unchecked_replay
      hashDrift literalOrderMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction unchecked)
    (ay_pchc_conj_intro
      (ay_pchc_RecomputeObligation currentCnf recompute)
      (ay_pchc_NoSemanticClaim diagnostic)
      recomputeObligation noClaim)
