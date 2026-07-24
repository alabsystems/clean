-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Equivalence-delta compaction soundness for preprocessing certificates. The
-- propositions stand for omitted delta coverage, digest membership, composed
-- equisatisfiability witnesses, model/proof reconstruction composition,
-- formula fingerprint lineage, checker replay, diagnostics, and public
-- SAT/UNSAT reports.

def ay_pedc_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pedc_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pedc_Equisat (before : Prop) (after : Prop) :=
  ay_pedc_Conj (before -> after) (after -> before)

def ay_pedc_Sat (cnf : Prop) (model : Prop) :=
  ay_pedc_Conj cnf model

def ay_pedc_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pedc_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pedc_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pedc_DeltaCoverage
    (omittedDeltas : Prop) (coveredDeltas : Prop) (coverageWitness : Prop) :=
  ay_pedc_Conj coverageWitness
    (omittedDeltas -> coveredDeltas)

def ay_pedc_DigestMembership
    (coveredDeltas : Prop) (manifestDigest : Prop) (compactedDigest : Prop) :=
  ay_pedc_Conj coveredDeltas
    (ay_pedc_Conj manifestDigest compactedDigest)

def ay_pedc_ModelReconstructionComposition
    (finalCnf : Prop) (originalCnf : Prop)
    (finalModel : Prop) (originalModel : Prop) :=
  ay_pedc_Sat finalCnf finalModel ->
    ay_pedc_Sat originalCnf originalModel

def ay_pedc_ProofReconstructionComposition
    (originalCnf : Prop) (finalCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pedc_Replay finalCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pedc_FingerprintLineage
    (originalFingerprint : Prop) (finalFingerprint : Prop)
    (lineageWitness : Prop) :=
  ay_pedc_Conj lineageWitness
    (ay_pedc_IdMatch originalFingerprint finalFingerprint)

def ay_pedc_CheckerReplay
    (compactionCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pedc_Conj compactionCertificate checkerAccepted

def ay_pedc_AcceptedCompaction
    (originalCnf : Prop) (finalCnf : Prop)
    (omittedDeltas : Prop) (coveredDeltas : Prop)
    (coverageWitness : Prop)
    (manifestDigest : Prop) (compactedDigest : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (finalFingerprint : Prop)
    (lineageWitness : Prop)
    (compactionCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pedc_Conj
    (ay_pedc_DeltaCoverage omittedDeltas coveredDeltas coverageWitness)
    (ay_pedc_Conj
      (ay_pedc_DigestMembership
        coveredDeltas manifestDigest compactedDigest)
      (ay_pedc_Conj
        (ay_pedc_Equisat originalCnf finalCnf)
        (ay_pedc_Conj
          (ay_pedc_ModelReconstructionComposition
            finalCnf originalCnf finalModel originalModel)
          (ay_pedc_Conj
            (ay_pedc_ProofReconstructionComposition
              originalCnf finalCnf certificate conflict)
            (ay_pedc_Conj
              (ay_pedc_FingerprintLineage
                originalFingerprint finalFingerprint lineageWitness)
              (ay_pedc_CheckerReplay
                compactionCertificate checkerAccepted))))))

def ay_pedc_AcceptedCompactionLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (finalCnf : Prop)
    (omittedDeltas : Prop) (coveredDeltas : Prop)
    (coverageWitness : Prop)
    (manifestDigest : Prop) (compactedDigest : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (finalFingerprint : Prop)
    (lineageWitness : Prop)
    (compactionCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pedc_Conj previousLog
    (ay_pedc_Conj
      (ay_pedc_AcceptedCompaction
        originalCnf finalCnf omittedDeltas coveredDeltas coverageWitness
        manifestDigest compactedDigest finalModel originalModel certificate
        conflict originalFingerprint finalFingerprint lineageWitness
        compactionCertificate checkerAccepted)
      nextLog)

def ay_pedc_CompactionFailure
    (missingDeltaCoverage : Prop) (brokenComposition : Prop)
    (staleFingerprint : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) :=
  ay_pedc_Disj missingDeltaCoverage
    (ay_pedc_Disj brokenComposition
      (ay_pedc_Disj staleFingerprint
        (ay_pedc_Disj digestMismatch replayRejected)))

def ay_pedc_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pedc_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pedc_Conj currentCnf recompute

def ay_pedc_DiagnosticCompactionLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingDeltaCoverage : Prop) (brokenComposition : Prop)
    (staleFingerprint : Prop) (digestMismatch : Prop)
    (replayRejected : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pedc_Conj previousLog
    (ay_pedc_Conj
      (ay_pedc_Conj
        (ay_pedc_CompactionFailure
          missingDeltaCoverage brokenComposition staleFingerprint
          digestMismatch replayRejected)
        (ay_pedc_Conj
          (ay_pedc_RecomputeObligation currentCnf recompute)
          (ay_pedc_NoSemanticClaim diagnostic)))
      nextLog)

def ay_pedc_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pedc_Conj exitCode claim

def ay_pedc_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pedc_Disj
    (ay_pedc_ExitCodeSound exitCode (ay_pedc_Sat originalCnf model))
    (ay_pedc_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))

theorem ay_pedc_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pedc_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pedc_conj_left
    (left : Prop) (right : Prop) :
    ay_pedc_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pedc_conj_right
    (left : Prop) (right : Prop) :
    ay_pedc_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pedc_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pedc_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pedc_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pedc_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pedc_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pedc_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pedc_conj_left (before -> after) (after -> before) eq

theorem ay_pedc_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pedc_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pedc_conj_right (before -> after) (after -> before) eq

theorem ay_pedc_compaction_coverage
    (originalCnf : Prop) (finalCnf : Prop)
    (omittedDeltas : Prop) (coveredDeltas : Prop)
    (coverageWitness : Prop)
    (manifestDigest : Prop) (compactedDigest : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (finalFingerprint : Prop)
    (lineageWitness : Prop)
    (compactionCertificate : Prop) (checkerAccepted : Prop) :
    ay_pedc_AcceptedCompaction
      originalCnf finalCnf omittedDeltas coveredDeltas coverageWitness
      manifestDigest compactedDigest finalModel originalModel certificate
      conflict originalFingerprint finalFingerprint lineageWitness
      compactionCertificate checkerAccepted ->
    ay_pedc_DeltaCoverage omittedDeltas coveredDeltas coverageWitness := by
  intro accepted
  exact ay_pedc_conj_left
    (ay_pedc_DeltaCoverage omittedDeltas coveredDeltas coverageWitness)
    (ay_pedc_Conj
      (ay_pedc_DigestMembership
        coveredDeltas manifestDigest compactedDigest)
      (ay_pedc_Conj
        (ay_pedc_Equisat originalCnf finalCnf)
        (ay_pedc_Conj
          (ay_pedc_ModelReconstructionComposition
            finalCnf originalCnf finalModel originalModel)
          (ay_pedc_Conj
            (ay_pedc_ProofReconstructionComposition
              originalCnf finalCnf certificate conflict)
            (ay_pedc_Conj
              (ay_pedc_FingerprintLineage
                originalFingerprint finalFingerprint lineageWitness)
              (ay_pedc_CheckerReplay
                compactionCertificate checkerAccepted))))))
    accepted

theorem ay_pedc_compaction_digest
    (originalCnf : Prop) (finalCnf : Prop)
    (omittedDeltas : Prop) (coveredDeltas : Prop)
    (coverageWitness : Prop)
    (manifestDigest : Prop) (compactedDigest : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (finalFingerprint : Prop)
    (lineageWitness : Prop)
    (compactionCertificate : Prop) (checkerAccepted : Prop) :
    ay_pedc_AcceptedCompaction
      originalCnf finalCnf omittedDeltas coveredDeltas coverageWitness
      manifestDigest compactedDigest finalModel originalModel certificate
      conflict originalFingerprint finalFingerprint lineageWitness
      compactionCertificate checkerAccepted ->
    ay_pedc_DigestMembership coveredDeltas manifestDigest compactedDigest := by
  intro accepted
  exact accepted
    (ay_pedc_DigestMembership coveredDeltas manifestDigest compactedDigest)
    (fun _coverage rest1 =>
      rest1
        (ay_pedc_DigestMembership coveredDeltas manifestDigest compactedDigest)
        (fun digest _tail => digest))

theorem ay_pedc_compaction_equisat
    (originalCnf : Prop) (finalCnf : Prop)
    (omittedDeltas : Prop) (coveredDeltas : Prop)
    (coverageWitness : Prop)
    (manifestDigest : Prop) (compactedDigest : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (finalFingerprint : Prop)
    (lineageWitness : Prop)
    (compactionCertificate : Prop) (checkerAccepted : Prop) :
    ay_pedc_AcceptedCompaction
      originalCnf finalCnf omittedDeltas coveredDeltas coverageWitness
      manifestDigest compactedDigest finalModel originalModel certificate
      conflict originalFingerprint finalFingerprint lineageWitness
      compactionCertificate checkerAccepted ->
    ay_pedc_Equisat originalCnf finalCnf := by
  intro accepted
  exact accepted
    (ay_pedc_Equisat originalCnf finalCnf)
    (fun _coverage rest1 =>
      rest1
        (ay_pedc_Equisat originalCnf finalCnf)
        (fun _digest rest2 =>
          rest2
            (ay_pedc_Equisat originalCnf finalCnf)
            (fun eq _tail => eq)))

theorem ay_pedc_compaction_model_reconstruction
    (originalCnf : Prop) (finalCnf : Prop)
    (omittedDeltas : Prop) (coveredDeltas : Prop)
    (coverageWitness : Prop)
    (manifestDigest : Prop) (compactedDigest : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (finalFingerprint : Prop)
    (lineageWitness : Prop)
    (compactionCertificate : Prop) (checkerAccepted : Prop) :
    ay_pedc_AcceptedCompaction
      originalCnf finalCnf omittedDeltas coveredDeltas coverageWitness
      manifestDigest compactedDigest finalModel originalModel certificate
      conflict originalFingerprint finalFingerprint lineageWitness
      compactionCertificate checkerAccepted ->
    ay_pedc_ModelReconstructionComposition
      finalCnf originalCnf finalModel originalModel := by
  intro accepted
  exact accepted
    (ay_pedc_ModelReconstructionComposition
      finalCnf originalCnf finalModel originalModel)
    (fun _coverage rest1 =>
      rest1
        (ay_pedc_ModelReconstructionComposition
          finalCnf originalCnf finalModel originalModel)
        (fun _digest rest2 =>
          rest2
            (ay_pedc_ModelReconstructionComposition
              finalCnf originalCnf finalModel originalModel)
            (fun _eq rest3 =>
              rest3
                (ay_pedc_ModelReconstructionComposition
                  finalCnf originalCnf finalModel originalModel)
                (fun model _tail => model))))

theorem ay_pedc_compaction_proof_reconstruction
    (originalCnf : Prop) (finalCnf : Prop)
    (omittedDeltas : Prop) (coveredDeltas : Prop)
    (coverageWitness : Prop)
    (manifestDigest : Prop) (compactedDigest : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (finalFingerprint : Prop)
    (lineageWitness : Prop)
    (compactionCertificate : Prop) (checkerAccepted : Prop) :
    ay_pedc_AcceptedCompaction
      originalCnf finalCnf omittedDeltas coveredDeltas coverageWitness
      manifestDigest compactedDigest finalModel originalModel certificate
      conflict originalFingerprint finalFingerprint lineageWitness
      compactionCertificate checkerAccepted ->
    ay_pedc_ProofReconstructionComposition
      originalCnf finalCnf certificate conflict := by
  intro accepted
  exact accepted
    (ay_pedc_ProofReconstructionComposition
      originalCnf finalCnf certificate conflict)
    (fun _coverage rest1 =>
      rest1
        (ay_pedc_ProofReconstructionComposition
          originalCnf finalCnf certificate conflict)
        (fun _digest rest2 =>
          rest2
            (ay_pedc_ProofReconstructionComposition
              originalCnf finalCnf certificate conflict)
            (fun _eq rest3 =>
              rest3
                (ay_pedc_ProofReconstructionComposition
                  originalCnf finalCnf certificate conflict)
                (fun _model rest4 =>
                  rest4
                    (ay_pedc_ProofReconstructionComposition
                      originalCnf finalCnf certificate conflict)
                    (fun proof _tail => proof)))))

theorem ay_pedc_compaction_fingerprint
    (originalCnf : Prop) (finalCnf : Prop)
    (omittedDeltas : Prop) (coveredDeltas : Prop)
    (coverageWitness : Prop)
    (manifestDigest : Prop) (compactedDigest : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (finalFingerprint : Prop)
    (lineageWitness : Prop)
    (compactionCertificate : Prop) (checkerAccepted : Prop) :
    ay_pedc_AcceptedCompaction
      originalCnf finalCnf omittedDeltas coveredDeltas coverageWitness
      manifestDigest compactedDigest finalModel originalModel certificate
      conflict originalFingerprint finalFingerprint lineageWitness
      compactionCertificate checkerAccepted ->
    ay_pedc_FingerprintLineage
      originalFingerprint finalFingerprint lineageWitness := by
  intro accepted
  exact accepted
    (ay_pedc_FingerprintLineage
      originalFingerprint finalFingerprint lineageWitness)
    (fun _coverage rest1 =>
      rest1
        (ay_pedc_FingerprintLineage
          originalFingerprint finalFingerprint lineageWitness)
        (fun _digest rest2 =>
          rest2
            (ay_pedc_FingerprintLineage
              originalFingerprint finalFingerprint lineageWitness)
            (fun _eq rest3 =>
              rest3
                (ay_pedc_FingerprintLineage
                  originalFingerprint finalFingerprint lineageWitness)
                (fun _model rest4 =>
                  rest4
                    (ay_pedc_FingerprintLineage
                      originalFingerprint finalFingerprint lineageWitness)
                    (fun _proof rest5 =>
                      rest5
                        (ay_pedc_FingerprintLineage
                          originalFingerprint finalFingerprint lineageWitness)
                        (fun fp _tail => fp))))))

theorem ay_pedc_compaction_checker
    (originalCnf : Prop) (finalCnf : Prop)
    (omittedDeltas : Prop) (coveredDeltas : Prop)
    (coverageWitness : Prop)
    (manifestDigest : Prop) (compactedDigest : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (finalFingerprint : Prop)
    (lineageWitness : Prop)
    (compactionCertificate : Prop) (checkerAccepted : Prop) :
    ay_pedc_AcceptedCompaction
      originalCnf finalCnf omittedDeltas coveredDeltas coverageWitness
      manifestDigest compactedDigest finalModel originalModel certificate
      conflict originalFingerprint finalFingerprint lineageWitness
      compactionCertificate checkerAccepted ->
    ay_pedc_CheckerReplay compactionCertificate checkerAccepted := by
  intro accepted
  exact accepted
    (ay_pedc_CheckerReplay compactionCertificate checkerAccepted)
    (fun _coverage rest1 =>
      rest1
        (ay_pedc_CheckerReplay compactionCertificate checkerAccepted)
        (fun _digest rest2 =>
          rest2
            (ay_pedc_CheckerReplay compactionCertificate checkerAccepted)
            (fun _eq rest3 =>
              rest3
                (ay_pedc_CheckerReplay compactionCertificate checkerAccepted)
                (fun _model rest4 =>
                  rest4
                    (ay_pedc_CheckerReplay
                      compactionCertificate checkerAccepted)
                    (fun _proof rest5 =>
                      rest5
                        (ay_pedc_CheckerReplay
                          compactionCertificate checkerAccepted)
                        (fun _fp checker => checker))))))

theorem ay_pedc_sat_pullback
    (originalCnf : Prop) (finalCnf : Prop)
    (omittedDeltas : Prop) (coveredDeltas : Prop)
    (coverageWitness : Prop)
    (manifestDigest : Prop) (compactedDigest : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (finalFingerprint : Prop)
    (lineageWitness : Prop)
    (compactionCertificate : Prop) (checkerAccepted : Prop) :
    ay_pedc_AcceptedCompaction
      originalCnf finalCnf omittedDeltas coveredDeltas coverageWitness
      manifestDigest compactedDigest finalModel originalModel certificate
      conflict originalFingerprint finalFingerprint lineageWitness
      compactionCertificate checkerAccepted ->
    ay_pedc_Sat finalCnf finalModel ->
    ay_pedc_Sat originalCnf originalModel := by
  intro accepted finalSat
  exact
    (ay_pedc_compaction_model_reconstruction
      originalCnf finalCnf omittedDeltas coveredDeltas coverageWitness
      manifestDigest compactedDigest finalModel originalModel certificate
      conflict originalFingerprint finalFingerprint lineageWitness
      compactionCertificate checkerAccepted accepted)
      finalSat

theorem ay_pedc_unsat_pushback
    (originalCnf : Prop) (finalCnf : Prop)
    (omittedDeltas : Prop) (coveredDeltas : Prop)
    (coverageWitness : Prop)
    (manifestDigest : Prop) (compactedDigest : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (finalFingerprint : Prop)
    (lineageWitness : Prop)
    (compactionCertificate : Prop) (checkerAccepted : Prop) :
    ay_pedc_AcceptedCompaction
      originalCnf finalCnf omittedDeltas coveredDeltas coverageWitness
      manifestDigest compactedDigest finalModel originalModel certificate
      conflict originalFingerprint finalFingerprint lineageWitness
      compactionCertificate checkerAccepted ->
    ay_pedc_Replay finalCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro accepted replay cert original
  exact
    (ay_pedc_compaction_proof_reconstruction
      originalCnf finalCnf omittedDeltas coveredDeltas coverageWitness
      manifestDigest compactedDigest finalModel originalModel certificate
      conflict originalFingerprint finalFingerprint lineageWitness
      compactionCertificate checkerAccepted accepted)
      replay cert original

theorem ay_pedc_public_sat
    (originalCnf : Prop) (finalCnf : Prop)
    (omittedDeltas : Prop) (coveredDeltas : Prop)
    (coverageWitness : Prop)
    (manifestDigest : Prop) (compactedDigest : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (finalFingerprint : Prop)
    (lineageWitness : Prop)
    (compactionCertificate : Prop) (checkerAccepted : Prop)
    (exitCode : Prop) :
    ay_pedc_AcceptedCompaction
      originalCnf finalCnf omittedDeltas coveredDeltas coverageWitness
      manifestDigest compactedDigest finalModel originalModel certificate
      conflict originalFingerprint finalFingerprint lineageWitness
      compactionCertificate checkerAccepted ->
    ay_pedc_Sat finalCnf finalModel ->
    exitCode ->
    ay_pedc_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro accepted finalSat exit
  exact ay_pedc_disj_left
    (ay_pedc_ExitCodeSound exitCode (ay_pedc_Sat originalCnf originalModel))
    (ay_pedc_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pedc_conj_intro exitCode
      (ay_pedc_Sat originalCnf originalModel)
      exit
      (ay_pedc_sat_pullback
        originalCnf finalCnf omittedDeltas coveredDeltas coverageWitness
        manifestDigest compactedDigest finalModel originalModel certificate
        conflict originalFingerprint finalFingerprint lineageWitness
        compactionCertificate checkerAccepted accepted finalSat))

theorem ay_pedc_public_unsat
    (originalCnf : Prop) (finalCnf : Prop)
    (omittedDeltas : Prop) (coveredDeltas : Prop)
    (coverageWitness : Prop)
    (manifestDigest : Prop) (compactedDigest : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (finalFingerprint : Prop)
    (lineageWitness : Prop)
    (compactionCertificate : Prop) (checkerAccepted : Prop)
    (exitCode : Prop) :
    ay_pedc_AcceptedCompaction
      originalCnf finalCnf omittedDeltas coveredDeltas coverageWitness
      manifestDigest compactedDigest finalModel originalModel certificate
      conflict originalFingerprint finalFingerprint lineageWitness
      compactionCertificate checkerAccepted ->
    ay_pedc_Replay finalCnf certificate conflict ->
    exitCode ->
    ay_pedc_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro accepted replay exit
  exact ay_pedc_disj_right
    (ay_pedc_ExitCodeSound exitCode (ay_pedc_Sat originalCnf originalModel))
    (ay_pedc_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pedc_conj_intro exitCode
      (certificate -> originalCnf -> conflict)
      exit
      (fun cert original =>
        ay_pedc_unsat_pushback
          originalCnf finalCnf omittedDeltas coveredDeltas coverageWitness
          manifestDigest compactedDigest finalModel originalModel certificate
          conflict originalFingerprint finalFingerprint lineageWitness
          compactionCertificate checkerAccepted accepted replay cert original))

theorem ay_pedc_failure_missing_delta_coverage
    (missingDeltaCoverage : Prop) (brokenComposition : Prop)
    (staleFingerprint : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) :
    missingDeltaCoverage ->
    ay_pedc_CompactionFailure
      missingDeltaCoverage brokenComposition staleFingerprint digestMismatch
      replayRejected := by
  intro missing
  exact ay_pedc_disj_left missingDeltaCoverage
    (ay_pedc_Disj brokenComposition
      (ay_pedc_Disj staleFingerprint
        (ay_pedc_Disj digestMismatch replayRejected)))
    missing

theorem ay_pedc_failure_broken_composition
    (missingDeltaCoverage : Prop) (brokenComposition : Prop)
    (staleFingerprint : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) :
    brokenComposition ->
    ay_pedc_CompactionFailure
      missingDeltaCoverage brokenComposition staleFingerprint digestMismatch
      replayRejected := by
  intro broken
  exact ay_pedc_disj_right missingDeltaCoverage
    (ay_pedc_Disj brokenComposition
      (ay_pedc_Disj staleFingerprint
        (ay_pedc_Disj digestMismatch replayRejected)))
    (ay_pedc_disj_left brokenComposition
      (ay_pedc_Disj staleFingerprint
        (ay_pedc_Disj digestMismatch replayRejected))
      broken)

theorem ay_pedc_failure_stale_fingerprint
    (missingDeltaCoverage : Prop) (brokenComposition : Prop)
    (staleFingerprint : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) :
    staleFingerprint ->
    ay_pedc_CompactionFailure
      missingDeltaCoverage brokenComposition staleFingerprint digestMismatch
      replayRejected := by
  intro stale
  exact ay_pedc_disj_right missingDeltaCoverage
    (ay_pedc_Disj brokenComposition
      (ay_pedc_Disj staleFingerprint
        (ay_pedc_Disj digestMismatch replayRejected)))
    (ay_pedc_disj_right brokenComposition
      (ay_pedc_Disj staleFingerprint
        (ay_pedc_Disj digestMismatch replayRejected))
      (ay_pedc_disj_left staleFingerprint
        (ay_pedc_Disj digestMismatch replayRejected)
        stale))

theorem ay_pedc_failure_digest_mismatch
    (missingDeltaCoverage : Prop) (brokenComposition : Prop)
    (staleFingerprint : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) :
    digestMismatch ->
    ay_pedc_CompactionFailure
      missingDeltaCoverage brokenComposition staleFingerprint digestMismatch
      replayRejected := by
  intro mismatch
  exact ay_pedc_disj_right missingDeltaCoverage
    (ay_pedc_Disj brokenComposition
      (ay_pedc_Disj staleFingerprint
        (ay_pedc_Disj digestMismatch replayRejected)))
    (ay_pedc_disj_right brokenComposition
      (ay_pedc_Disj staleFingerprint
        (ay_pedc_Disj digestMismatch replayRejected))
      (ay_pedc_disj_right staleFingerprint
        (ay_pedc_Disj digestMismatch replayRejected)
        (ay_pedc_disj_left digestMismatch replayRejected mismatch)))

theorem ay_pedc_failure_replay_rejected
    (missingDeltaCoverage : Prop) (brokenComposition : Prop)
    (staleFingerprint : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) :
    replayRejected ->
    ay_pedc_CompactionFailure
      missingDeltaCoverage brokenComposition staleFingerprint digestMismatch
      replayRejected := by
  intro rejected
  exact ay_pedc_disj_right missingDeltaCoverage
    (ay_pedc_Disj brokenComposition
      (ay_pedc_Disj staleFingerprint
        (ay_pedc_Disj digestMismatch replayRejected)))
    (ay_pedc_disj_right brokenComposition
      (ay_pedc_Disj staleFingerprint
        (ay_pedc_Disj digestMismatch replayRejected))
      (ay_pedc_disj_right staleFingerprint
        (ay_pedc_Disj digestMismatch replayRejected)
        (ay_pedc_disj_right digestMismatch replayRejected rejected)))

theorem ay_pedc_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingDeltaCoverage : Prop) (brokenComposition : Prop)
    (staleFingerprint : Prop) (digestMismatch : Prop)
    (replayRejected : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pedc_DiagnosticCompactionLogEntry
      previousLog nextLog currentCnf missingDeltaCoverage brokenComposition
      staleFingerprint digestMismatch replayRejected recompute diagnostic ->
    ay_pedc_CompactionFailure
      missingDeltaCoverage brokenComposition staleFingerprint digestMismatch
      replayRejected := by
  intro entry
  exact entry
    (ay_pedc_CompactionFailure
      missingDeltaCoverage brokenComposition staleFingerprint digestMismatch
      replayRejected)
    (fun _previous rest1 =>
      rest1
        (ay_pedc_CompactionFailure
          missingDeltaCoverage brokenComposition staleFingerprint digestMismatch
          replayRejected)
        (fun body _next =>
          body
            (ay_pedc_CompactionFailure
              missingDeltaCoverage brokenComposition staleFingerprint
              digestMismatch replayRejected)
            (fun failure _tail => failure)))

theorem ay_pedc_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingDeltaCoverage : Prop) (brokenComposition : Prop)
    (staleFingerprint : Prop) (digestMismatch : Prop)
    (replayRejected : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pedc_DiagnosticCompactionLogEntry
      previousLog nextLog currentCnf missingDeltaCoverage brokenComposition
      staleFingerprint digestMismatch replayRejected recompute diagnostic ->
    ay_pedc_NoSemanticClaim diagnostic := by
  intro entry
  exact entry
    (ay_pedc_NoSemanticClaim diagnostic)
    (fun _previous rest1 =>
      rest1
        (ay_pedc_NoSemanticClaim diagnostic)
        (fun body _next =>
          body
            (ay_pedc_NoSemanticClaim diagnostic)
            (fun _failure rest2 =>
              rest2
                (ay_pedc_NoSemanticClaim diagnostic)
                (fun _recompute no_claim => no_claim))))

theorem ay_pedc_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingDeltaCoverage : Prop) (brokenComposition : Prop)
    (staleFingerprint : Prop) (digestMismatch : Prop)
    (replayRejected : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pedc_DiagnosticCompactionLogEntry
      previousLog nextLog currentCnf missingDeltaCoverage brokenComposition
      staleFingerprint digestMismatch replayRejected recompute diagnostic ->
    ay_pedc_RecomputeObligation currentCnf recompute := by
  intro entry
  exact entry
    (ay_pedc_RecomputeObligation currentCnf recompute)
    (fun _previous rest1 =>
      rest1
        (ay_pedc_RecomputeObligation currentCnf recompute)
        (fun body _next =>
          body
            (ay_pedc_RecomputeObligation currentCnf recompute)
            (fun _failure rest2 =>
              rest2
                (ay_pedc_RecomputeObligation currentCnf recompute)
                (fun recompute_obligation _no_claim =>
                  recompute_obligation))))

theorem ay_pedc_failure_no_claim
    (missingDeltaCoverage : Prop) (brokenComposition : Prop)
    (staleFingerprint : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (diagnostic : Prop) :
    ay_pedc_CompactionFailure
      missingDeltaCoverage brokenComposition staleFingerprint digestMismatch
      replayRejected ->
    diagnostic ->
    ay_pedc_NoSemanticClaim diagnostic := by
  intro _failure diag
  exact diag
