-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Preprocessing equivalence certificate-chain soundness. The propositions
-- stand for formula-fingerprint lineage, equisatisfiability witnesses, model
-- and UNSAT proof reconstruction maps, digest membership, checker replay,
-- diagnostics, and public SAT/UNSAT outcomes.

def ay_pecc_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pecc_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pecc_Equisat (before : Prop) (after : Prop) :=
  ay_pecc_Conj (before -> after) (after -> before)

def ay_pecc_Sat (cnf : Prop) (model : Prop) :=
  ay_pecc_Conj cnf model

def ay_pecc_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pecc_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pecc_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pecc_FingerprintLineage
    (sourceFingerprint : Prop) (targetFingerprint : Prop)
    (lineageWitness : Prop) :=
  ay_pecc_Conj lineageWitness
    (ay_pecc_IdMatch sourceFingerprint targetFingerprint)

def ay_pecc_ModelReconstruction
    (targetCnf : Prop) (sourceCnf : Prop)
    (targetModel : Prop) (sourceModel : Prop) :=
  ay_pecc_Sat targetCnf targetModel ->
    ay_pecc_Sat sourceCnf sourceModel

def ay_pecc_ProofReconstruction
    (sourceCnf : Prop) (targetCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pecc_Replay targetCnf certificate conflict ->
    certificate -> sourceCnf -> conflict

def ay_pecc_DigestMembership (digestRoot : Prop) (edgeDigest : Prop) :=
  ay_pecc_Conj digestRoot edgeDigest

def ay_pecc_CheckerReplay (edgeCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pecc_Conj edgeCertificate checkerAccepted

def ay_pecc_EquivalenceEdge
    (sourceCnf : Prop) (targetCnf : Prop)
    (sourceFingerprint : Prop) (targetFingerprint : Prop)
    (lineageWitness : Prop)
    (targetModel : Prop) (sourceModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (digestRoot : Prop) (edgeDigest : Prop)
    (edgeCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pecc_Conj
    (ay_pecc_FingerprintLineage
      sourceFingerprint targetFingerprint lineageWitness)
    (ay_pecc_Conj
      (ay_pecc_Equisat sourceCnf targetCnf)
      (ay_pecc_Conj
        (ay_pecc_ModelReconstruction
          targetCnf sourceCnf targetModel sourceModel)
        (ay_pecc_Conj
          (ay_pecc_ProofReconstruction
            sourceCnf targetCnf certificate conflict)
          (ay_pecc_Conj
            (ay_pecc_DigestMembership digestRoot edgeDigest)
            (ay_pecc_CheckerReplay
              edgeCertificate checkerAccepted)))))

def ay_pecc_AcceptedChainLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (sourceCnf : Prop) (targetCnf : Prop)
    (sourceFingerprint : Prop) (targetFingerprint : Prop)
    (lineageWitness : Prop)
    (targetModel : Prop) (sourceModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (digestRoot : Prop) (edgeDigest : Prop)
    (edgeCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pecc_Conj previousLog
    (ay_pecc_Conj
      (ay_pecc_EquivalenceEdge
        sourceCnf targetCnf sourceFingerprint targetFingerprint
        lineageWitness targetModel sourceModel certificate conflict
        digestRoot edgeDigest edgeCertificate checkerAccepted)
      nextLog)

def ay_pecc_ChainFailure
    (brokenEdge : Prop) (staleFingerprint : Prop)
    (missingReconstruction : Prop) (replayRejected : Prop) :=
  ay_pecc_Disj brokenEdge
    (ay_pecc_Disj staleFingerprint
      (ay_pecc_Disj missingReconstruction replayRejected))

def ay_pecc_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pecc_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pecc_Conj currentCnf recompute

def ay_pecc_DiagnosticChainLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (brokenEdge : Prop) (staleFingerprint : Prop)
    (missingReconstruction : Prop) (replayRejected : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pecc_Conj previousLog
    (ay_pecc_Conj
      (ay_pecc_Conj
        (ay_pecc_ChainFailure
          brokenEdge staleFingerprint missingReconstruction replayRejected)
        (ay_pecc_Conj
          (ay_pecc_RecomputeObligation currentCnf recompute)
          (ay_pecc_NoSemanticClaim diagnostic)))
      nextLog)

def ay_pecc_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pecc_Conj exitCode claim

def ay_pecc_PublicResult
    (sourceCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pecc_Disj
    (ay_pecc_ExitCodeSound exitCode (ay_pecc_Sat sourceCnf model))
    (ay_pecc_ExitCodeSound exitCode (certificate -> sourceCnf -> conflict))

theorem ay_pecc_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pecc_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pecc_conj_left
    (left : Prop) (right : Prop) :
    ay_pecc_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pecc_conj_right
    (left : Prop) (right : Prop) :
    ay_pecc_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pecc_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pecc_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pecc_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pecc_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pecc_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pecc_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pecc_conj_left (before -> after) (after -> before) eq

theorem ay_pecc_edge_equisat
    (sourceCnf : Prop) (targetCnf : Prop)
    (sourceFingerprint : Prop) (targetFingerprint : Prop)
    (lineageWitness : Prop)
    (targetModel : Prop) (sourceModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (digestRoot : Prop) (edgeDigest : Prop)
    (edgeCertificate : Prop) (checkerAccepted : Prop) :
    ay_pecc_EquivalenceEdge
      sourceCnf targetCnf sourceFingerprint targetFingerprint
      lineageWitness targetModel sourceModel certificate conflict
      digestRoot edgeDigest edgeCertificate checkerAccepted ->
    ay_pecc_Equisat sourceCnf targetCnf := by
  intro edge
  exact ay_pecc_conj_left
    (ay_pecc_Equisat sourceCnf targetCnf)
    (ay_pecc_Conj
      (ay_pecc_ModelReconstruction
        targetCnf sourceCnf targetModel sourceModel)
      (ay_pecc_Conj
        (ay_pecc_ProofReconstruction sourceCnf targetCnf certificate conflict)
        (ay_pecc_Conj
          (ay_pecc_DigestMembership digestRoot edgeDigest)
          (ay_pecc_CheckerReplay edgeCertificate checkerAccepted))))
    (ay_pecc_conj_right
      (ay_pecc_FingerprintLineage
        sourceFingerprint targetFingerprint lineageWitness)
      (ay_pecc_Conj
        (ay_pecc_Equisat sourceCnf targetCnf)
        (ay_pecc_Conj
          (ay_pecc_ModelReconstruction
            targetCnf sourceCnf targetModel sourceModel)
          (ay_pecc_Conj
            (ay_pecc_ProofReconstruction
              sourceCnf targetCnf certificate conflict)
            (ay_pecc_Conj
              (ay_pecc_DigestMembership digestRoot edgeDigest)
              (ay_pecc_CheckerReplay edgeCertificate checkerAccepted)))))
      edge)

theorem ay_pecc_edge_model_reconstruction
    (sourceCnf : Prop) (targetCnf : Prop)
    (sourceFingerprint : Prop) (targetFingerprint : Prop)
    (lineageWitness : Prop)
    (targetModel : Prop) (sourceModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (digestRoot : Prop) (edgeDigest : Prop)
    (edgeCertificate : Prop) (checkerAccepted : Prop) :
    ay_pecc_EquivalenceEdge
      sourceCnf targetCnf sourceFingerprint targetFingerprint
      lineageWitness targetModel sourceModel certificate conflict
      digestRoot edgeDigest edgeCertificate checkerAccepted ->
    ay_pecc_ModelReconstruction targetCnf sourceCnf targetModel sourceModel := by
  intro edge
  exact ay_pecc_conj_left
    (ay_pecc_ModelReconstruction targetCnf sourceCnf targetModel sourceModel)
    (ay_pecc_Conj
      (ay_pecc_ProofReconstruction sourceCnf targetCnf certificate conflict)
      (ay_pecc_Conj
        (ay_pecc_DigestMembership digestRoot edgeDigest)
        (ay_pecc_CheckerReplay edgeCertificate checkerAccepted)))
    (ay_pecc_conj_right
      (ay_pecc_Equisat sourceCnf targetCnf)
      (ay_pecc_Conj
        (ay_pecc_ModelReconstruction targetCnf sourceCnf targetModel sourceModel)
        (ay_pecc_Conj
          (ay_pecc_ProofReconstruction sourceCnf targetCnf certificate conflict)
          (ay_pecc_Conj
            (ay_pecc_DigestMembership digestRoot edgeDigest)
            (ay_pecc_CheckerReplay edgeCertificate checkerAccepted))))
      (ay_pecc_conj_right
        (ay_pecc_FingerprintLineage
          sourceFingerprint targetFingerprint lineageWitness)
        (ay_pecc_Conj
          (ay_pecc_Equisat sourceCnf targetCnf)
          (ay_pecc_Conj
            (ay_pecc_ModelReconstruction
              targetCnf sourceCnf targetModel sourceModel)
            (ay_pecc_Conj
              (ay_pecc_ProofReconstruction
                sourceCnf targetCnf certificate conflict)
              (ay_pecc_Conj
                (ay_pecc_DigestMembership digestRoot edgeDigest)
                (ay_pecc_CheckerReplay edgeCertificate checkerAccepted)))))
        edge))

theorem ay_pecc_edge_proof_reconstruction
    (sourceCnf : Prop) (targetCnf : Prop)
    (sourceFingerprint : Prop) (targetFingerprint : Prop)
    (lineageWitness : Prop)
    (targetModel : Prop) (sourceModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (digestRoot : Prop) (edgeDigest : Prop)
    (edgeCertificate : Prop) (checkerAccepted : Prop) :
    ay_pecc_EquivalenceEdge
      sourceCnf targetCnf sourceFingerprint targetFingerprint
      lineageWitness targetModel sourceModel certificate conflict
      digestRoot edgeDigest edgeCertificate checkerAccepted ->
    ay_pecc_ProofReconstruction sourceCnf targetCnf certificate conflict := by
  intro edge
  exact ay_pecc_conj_left
    (ay_pecc_ProofReconstruction sourceCnf targetCnf certificate conflict)
    (ay_pecc_Conj
      (ay_pecc_DigestMembership digestRoot edgeDigest)
      (ay_pecc_CheckerReplay edgeCertificate checkerAccepted))
    (ay_pecc_conj_right
      (ay_pecc_ModelReconstruction targetCnf sourceCnf targetModel sourceModel)
      (ay_pecc_Conj
        (ay_pecc_ProofReconstruction sourceCnf targetCnf certificate conflict)
        (ay_pecc_Conj
          (ay_pecc_DigestMembership digestRoot edgeDigest)
          (ay_pecc_CheckerReplay edgeCertificate checkerAccepted)))
      (ay_pecc_conj_right
        (ay_pecc_Equisat sourceCnf targetCnf)
        (ay_pecc_Conj
          (ay_pecc_ModelReconstruction
            targetCnf sourceCnf targetModel sourceModel)
          (ay_pecc_Conj
            (ay_pecc_ProofReconstruction
              sourceCnf targetCnf certificate conflict)
            (ay_pecc_Conj
              (ay_pecc_DigestMembership digestRoot edgeDigest)
              (ay_pecc_CheckerReplay edgeCertificate checkerAccepted))))
        (ay_pecc_conj_right
          (ay_pecc_FingerprintLineage
            sourceFingerprint targetFingerprint lineageWitness)
          (ay_pecc_Conj
            (ay_pecc_Equisat sourceCnf targetCnf)
            (ay_pecc_Conj
              (ay_pecc_ModelReconstruction
                targetCnf sourceCnf targetModel sourceModel)
              (ay_pecc_Conj
                (ay_pecc_ProofReconstruction
                  sourceCnf targetCnf certificate conflict)
                (ay_pecc_Conj
                  (ay_pecc_DigestMembership digestRoot edgeDigest)
                  (ay_pecc_CheckerReplay edgeCertificate checkerAccepted)))))
          edge)))

theorem ay_pecc_log_edge
    (previousLog : Prop) (nextLog : Prop)
    (sourceCnf : Prop) (targetCnf : Prop)
    (sourceFingerprint : Prop) (targetFingerprint : Prop)
    (lineageWitness : Prop)
    (targetModel : Prop) (sourceModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (digestRoot : Prop) (edgeDigest : Prop)
    (edgeCertificate : Prop) (checkerAccepted : Prop) :
    ay_pecc_AcceptedChainLogEntry
      previousLog nextLog sourceCnf targetCnf sourceFingerprint
      targetFingerprint lineageWitness targetModel sourceModel
      certificate conflict digestRoot edgeDigest edgeCertificate
      checkerAccepted ->
    ay_pecc_EquivalenceEdge
      sourceCnf targetCnf sourceFingerprint targetFingerprint
      lineageWitness targetModel sourceModel certificate conflict
      digestRoot edgeDigest edgeCertificate checkerAccepted := by
  intro log_entry
  exact ay_pecc_conj_left
    (ay_pecc_EquivalenceEdge
      sourceCnf targetCnf sourceFingerprint targetFingerprint
      lineageWitness targetModel sourceModel certificate conflict
      digestRoot edgeDigest edgeCertificate checkerAccepted)
    nextLog
    (ay_pecc_conj_right previousLog
      (ay_pecc_Conj
        (ay_pecc_EquivalenceEdge
          sourceCnf targetCnf sourceFingerprint targetFingerprint
          lineageWitness targetModel sourceModel certificate conflict
          digestRoot edgeDigest edgeCertificate checkerAccepted)
        nextLog)
      log_entry)

theorem ay_pecc_public_sat
    (previousLog : Prop) (nextLog : Prop)
    (sourceCnf : Prop) (targetCnf : Prop)
    (sourceFingerprint : Prop) (targetFingerprint : Prop)
    (lineageWitness : Prop)
    (targetModel : Prop) (sourceModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (digestRoot : Prop) (edgeDigest : Prop)
    (edgeCertificate : Prop) (checkerAccepted : Prop)
    (exitCode : Prop) :
    ay_pecc_AcceptedChainLogEntry
      previousLog nextLog sourceCnf targetCnf sourceFingerprint
      targetFingerprint lineageWitness targetModel sourceModel
      certificate conflict digestRoot edgeDigest edgeCertificate
      checkerAccepted ->
    ay_pecc_Sat targetCnf targetModel ->
    exitCode ->
    ay_pecc_PublicResult sourceCnf sourceModel certificate conflict exitCode := by
  intro log_entry sat hexit
  exact ay_pecc_disj_left
    (ay_pecc_ExitCodeSound exitCode (ay_pecc_Sat sourceCnf sourceModel))
    (ay_pecc_ExitCodeSound exitCode (certificate -> sourceCnf -> conflict))
    (ay_pecc_conj_intro exitCode (ay_pecc_Sat sourceCnf sourceModel)
      hexit
      (ay_pecc_edge_model_reconstruction sourceCnf targetCnf
        sourceFingerprint targetFingerprint lineageWitness targetModel
        sourceModel certificate conflict digestRoot edgeDigest
        edgeCertificate checkerAccepted
        (ay_pecc_log_edge previousLog nextLog sourceCnf targetCnf
          sourceFingerprint targetFingerprint lineageWitness targetModel
          sourceModel certificate conflict digestRoot edgeDigest
          edgeCertificate checkerAccepted log_entry)
        sat))

theorem ay_pecc_public_unsat
    (previousLog : Prop) (nextLog : Prop)
    (sourceCnf : Prop) (targetCnf : Prop)
    (sourceFingerprint : Prop) (targetFingerprint : Prop)
    (lineageWitness : Prop)
    (targetModel : Prop) (sourceModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (digestRoot : Prop) (edgeDigest : Prop)
    (edgeCertificate : Prop) (checkerAccepted : Prop)
    (exitCode : Prop) :
    ay_pecc_AcceptedChainLogEntry
      previousLog nextLog sourceCnf targetCnf sourceFingerprint
      targetFingerprint lineageWitness targetModel sourceModel
      certificate conflict digestRoot edgeDigest edgeCertificate
      checkerAccepted ->
    ay_pecc_Replay targetCnf certificate conflict ->
    exitCode ->
    ay_pecc_PublicResult sourceCnf sourceModel certificate conflict exitCode := by
  intro log_entry replay hexit
  exact ay_pecc_disj_right
    (ay_pecc_ExitCodeSound exitCode (ay_pecc_Sat sourceCnf sourceModel))
    (ay_pecc_ExitCodeSound exitCode (certificate -> sourceCnf -> conflict))
    (ay_pecc_conj_intro exitCode
      (certificate -> sourceCnf -> conflict)
      hexit
      (ay_pecc_edge_proof_reconstruction sourceCnf targetCnf
        sourceFingerprint targetFingerprint lineageWitness targetModel
        sourceModel certificate conflict digestRoot edgeDigest
        edgeCertificate checkerAccepted
        (ay_pecc_log_edge previousLog nextLog sourceCnf targetCnf
          sourceFingerprint targetFingerprint lineageWitness targetModel
          sourceModel certificate conflict digestRoot edgeDigest
          edgeCertificate checkerAccepted log_entry)
        replay))

theorem ay_pecc_failure_broken_edge
    (brokenEdge : Prop) (staleFingerprint : Prop)
    (missingReconstruction : Prop) (replayRejected : Prop) :
    brokenEdge ->
    ay_pecc_ChainFailure
      brokenEdge staleFingerprint missingReconstruction replayRejected := by
  intro hfailure
  exact ay_pecc_disj_left brokenEdge
    (ay_pecc_Disj staleFingerprint
      (ay_pecc_Disj missingReconstruction replayRejected))
    hfailure

theorem ay_pecc_failure_stale_fingerprint
    (brokenEdge : Prop) (staleFingerprint : Prop)
    (missingReconstruction : Prop) (replayRejected : Prop) :
    staleFingerprint ->
    ay_pecc_ChainFailure
      brokenEdge staleFingerprint missingReconstruction replayRejected := by
  intro hfailure
  exact ay_pecc_disj_right brokenEdge
    (ay_pecc_Disj staleFingerprint
      (ay_pecc_Disj missingReconstruction replayRejected))
    (ay_pecc_disj_left staleFingerprint
      (ay_pecc_Disj missingReconstruction replayRejected)
      hfailure)

theorem ay_pecc_failure_missing_reconstruction
    (brokenEdge : Prop) (staleFingerprint : Prop)
    (missingReconstruction : Prop) (replayRejected : Prop) :
    missingReconstruction ->
    ay_pecc_ChainFailure
      brokenEdge staleFingerprint missingReconstruction replayRejected := by
  intro hfailure
  exact ay_pecc_disj_right brokenEdge
    (ay_pecc_Disj staleFingerprint
      (ay_pecc_Disj missingReconstruction replayRejected))
    (ay_pecc_disj_right staleFingerprint
      (ay_pecc_Disj missingReconstruction replayRejected)
      (ay_pecc_disj_left missingReconstruction replayRejected hfailure))

theorem ay_pecc_failure_replay_rejected
    (brokenEdge : Prop) (staleFingerprint : Prop)
    (missingReconstruction : Prop) (replayRejected : Prop) :
    replayRejected ->
    ay_pecc_ChainFailure
      brokenEdge staleFingerprint missingReconstruction replayRejected := by
  intro hfailure
  exact ay_pecc_disj_right brokenEdge
    (ay_pecc_Disj staleFingerprint
      (ay_pecc_Disj missingReconstruction replayRejected))
    (ay_pecc_disj_right staleFingerprint
      (ay_pecc_Disj missingReconstruction replayRejected)
      (ay_pecc_disj_right missingReconstruction replayRejected hfailure))

theorem ay_pecc_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (brokenEdge : Prop) (staleFingerprint : Prop)
    (missingReconstruction : Prop) (replayRejected : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pecc_DiagnosticChainLogEntry
      previousLog nextLog currentCnf brokenEdge staleFingerprint
      missingReconstruction replayRejected recompute diagnostic ->
    ay_pecc_ChainFailure
      brokenEdge staleFingerprint missingReconstruction replayRejected := by
  intro log_entry
  exact ay_pecc_conj_left
    (ay_pecc_ChainFailure
      brokenEdge staleFingerprint missingReconstruction replayRejected)
    (ay_pecc_Conj
      (ay_pecc_RecomputeObligation currentCnf recompute)
      (ay_pecc_NoSemanticClaim diagnostic))
    (ay_pecc_conj_left
      (ay_pecc_Conj
        (ay_pecc_ChainFailure
          brokenEdge staleFingerprint missingReconstruction replayRejected)
        (ay_pecc_Conj
          (ay_pecc_RecomputeObligation currentCnf recompute)
          (ay_pecc_NoSemanticClaim diagnostic)))
      nextLog
      (ay_pecc_conj_right previousLog
        (ay_pecc_Conj
          (ay_pecc_Conj
            (ay_pecc_ChainFailure
              brokenEdge staleFingerprint missingReconstruction replayRejected)
            (ay_pecc_Conj
              (ay_pecc_RecomputeObligation currentCnf recompute)
              (ay_pecc_NoSemanticClaim diagnostic)))
          nextLog)
        log_entry))

theorem ay_pecc_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (brokenEdge : Prop) (staleFingerprint : Prop)
    (missingReconstruction : Prop) (replayRejected : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pecc_DiagnosticChainLogEntry
      previousLog nextLog currentCnf brokenEdge staleFingerprint
      missingReconstruction replayRejected recompute diagnostic ->
    ay_pecc_NoSemanticClaim diagnostic := by
  intro log_entry
  exact ay_pecc_conj_right
    (ay_pecc_RecomputeObligation currentCnf recompute)
    (ay_pecc_NoSemanticClaim diagnostic)
    (ay_pecc_conj_right
      (ay_pecc_ChainFailure
        brokenEdge staleFingerprint missingReconstruction replayRejected)
      (ay_pecc_Conj
        (ay_pecc_RecomputeObligation currentCnf recompute)
        (ay_pecc_NoSemanticClaim diagnostic))
      (ay_pecc_conj_left
        (ay_pecc_Conj
          (ay_pecc_ChainFailure
            brokenEdge staleFingerprint missingReconstruction replayRejected)
          (ay_pecc_Conj
            (ay_pecc_RecomputeObligation currentCnf recompute)
            (ay_pecc_NoSemanticClaim diagnostic)))
        nextLog
        (ay_pecc_conj_right previousLog
          (ay_pecc_Conj
            (ay_pecc_Conj
              (ay_pecc_ChainFailure
                brokenEdge staleFingerprint missingReconstruction replayRejected)
              (ay_pecc_Conj
                (ay_pecc_RecomputeObligation currentCnf recompute)
                (ay_pecc_NoSemanticClaim diagnostic)))
            nextLog)
          log_entry)))

theorem ay_pecc_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (brokenEdge : Prop) (staleFingerprint : Prop)
    (missingReconstruction : Prop) (replayRejected : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pecc_DiagnosticChainLogEntry
      previousLog nextLog currentCnf brokenEdge staleFingerprint
      missingReconstruction replayRejected recompute diagnostic ->
    ay_pecc_RecomputeObligation currentCnf recompute := by
  intro log_entry
  exact ay_pecc_conj_left
    (ay_pecc_RecomputeObligation currentCnf recompute)
    (ay_pecc_NoSemanticClaim diagnostic)
    (ay_pecc_conj_right
      (ay_pecc_ChainFailure
        brokenEdge staleFingerprint missingReconstruction replayRejected)
      (ay_pecc_Conj
        (ay_pecc_RecomputeObligation currentCnf recompute)
        (ay_pecc_NoSemanticClaim diagnostic))
      (ay_pecc_conj_left
        (ay_pecc_Conj
          (ay_pecc_ChainFailure
            brokenEdge staleFingerprint missingReconstruction replayRejected)
          (ay_pecc_Conj
            (ay_pecc_RecomputeObligation currentCnf recompute)
            (ay_pecc_NoSemanticClaim diagnostic)))
        nextLog
        (ay_pecc_conj_right previousLog
          (ay_pecc_Conj
            (ay_pecc_Conj
              (ay_pecc_ChainFailure
                brokenEdge staleFingerprint missingReconstruction replayRejected)
              (ay_pecc_Conj
                (ay_pecc_RecomputeObligation currentCnf recompute)
                (ay_pecc_NoSemanticClaim diagnostic)))
            nextLog)
          log_entry)))

theorem ay_pecc_failure_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (brokenEdge : Prop) (staleFingerprint : Prop)
    (missingReconstruction : Prop) (replayRejected : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pecc_DiagnosticChainLogEntry
      previousLog nextLog currentCnf brokenEdge staleFingerprint
      missingReconstruction replayRejected recompute diagnostic ->
    ay_pecc_Conj
      (ay_pecc_ChainFailure
        brokenEdge staleFingerprint missingReconstruction replayRejected)
      (ay_pecc_Conj
        (ay_pecc_RecomputeObligation currentCnf recompute)
        (ay_pecc_NoSemanticClaim diagnostic)) := by
  intro log_entry
  exact ay_pecc_conj_intro
    (ay_pecc_ChainFailure
      brokenEdge staleFingerprint missingReconstruction replayRejected)
    (ay_pecc_Conj
      (ay_pecc_RecomputeObligation currentCnf recompute)
      (ay_pecc_NoSemanticClaim diagnostic))
    (ay_pecc_diagnostic_failure previousLog nextLog currentCnf
      brokenEdge staleFingerprint missingReconstruction replayRejected
      recompute diagnostic log_entry)
    (ay_pecc_conj_intro
      (ay_pecc_RecomputeObligation currentCnf recompute)
      (ay_pecc_NoSemanticClaim diagnostic)
      (ay_pecc_diagnostic_recompute previousLog nextLog currentCnf
        brokenEdge staleFingerprint missingReconstruction replayRejected
        recompute diagnostic log_entry)
      (ay_pecc_diagnostic_no_claim previousLog nextLog currentCnf
        brokenEdge staleFingerprint missingReconstruction replayRejected
        recompute diagnostic log_entry))
