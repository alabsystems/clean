-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Incremental preprocessing digest-delta soundness. The propositions stand for
-- formula-fingerprint lineage, old/new digest roots, changed-cube coverage,
-- reconstruction witnesses, append-only delta logs, diagnostics, and public
-- SAT/UNSAT outcomes.

def ay_pidd_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pidd_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pidd_Equisat (before : Prop) (after : Prop) :=
  ay_pidd_Conj (before -> after) (after -> before)

def ay_pidd_Sat (cnf : Prop) (model : Prop) :=
  ay_pidd_Conj cnf model

def ay_pidd_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pidd_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pidd_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pidd_DigestStep
    (oldRoot : Prop) (newRoot : Prop) (deltaRoot : Prop) :=
  ay_pidd_Conj oldRoot (ay_pidd_Conj deltaRoot newRoot)

def ay_pidd_FingerprintLineage
    (oldFingerprint : Prop) (newFingerprint : Prop)
    (lineageWitness : Prop) :=
  ay_pidd_Conj lineageWitness
    (ay_pidd_IdMatch oldFingerprint newFingerprint)

def ay_pidd_ChangedCubeCoverage
    (changedCubes : Prop) (coveredCubes : Prop) :=
  ay_pidd_Conj changedCubes (changedCubes -> coveredCubes)

def ay_pidd_ReconstructionWitness
    (partitionCnf : Prop) (originalCnf : Prop)
    (partitionModel : Prop) (originalModel : Prop) :=
  ay_pidd_Conj
    (ay_pidd_Sat partitionCnf partitionModel ->
      ay_pidd_Sat originalCnf originalModel)
    (ay_pidd_Equisat originalCnf partitionCnf)

def ay_pidd_DeltaLogMembership
    (previousLog : Prop) (entry : Prop) (nextLog : Prop) :=
  ay_pidd_Conj previousLog (ay_pidd_Conj entry nextLog)

def ay_pidd_AcceptedDigestDelta
    (originalCnf : Prop) (partitionCnf : Prop)
    (oldFingerprint : Prop) (newFingerprint : Prop)
    (lineageWitness : Prop)
    (oldRoot : Prop) (newRoot : Prop) (deltaRoot : Prop)
    (changedCubes : Prop) (coveredCubes : Prop)
    (partitionModel : Prop) (originalModel : Prop) :=
  ay_pidd_Conj
    (ay_pidd_FingerprintLineage
      oldFingerprint newFingerprint lineageWitness)
    (ay_pidd_Conj
      (ay_pidd_DigestStep oldRoot newRoot deltaRoot)
      (ay_pidd_Conj
        (ay_pidd_ChangedCubeCoverage changedCubes coveredCubes)
        (ay_pidd_ReconstructionWitness
          partitionCnf originalCnf partitionModel originalModel)))

def ay_pidd_AcceptedDigestDeltaLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (partitionCnf : Prop)
    (oldFingerprint : Prop) (newFingerprint : Prop)
    (lineageWitness : Prop)
    (oldRoot : Prop) (newRoot : Prop) (deltaRoot : Prop)
    (changedCubes : Prop) (coveredCubes : Prop)
    (partitionModel : Prop) (originalModel : Prop) :=
  ay_pidd_DeltaLogMembership previousLog
    (ay_pidd_AcceptedDigestDelta
      originalCnf partitionCnf oldFingerprint newFingerprint
      lineageWitness oldRoot newRoot deltaRoot changedCubes coveredCubes
      partitionModel originalModel)
    nextLog

def ay_pidd_DeltaFailure
    (staleRoot : Prop) (missingChangedCube : Prop)
    (frameDrift : Prop) (nonAppendOnly : Prop) :=
  ay_pidd_Disj staleRoot
    (ay_pidd_Disj missingChangedCube
      (ay_pidd_Disj frameDrift nonAppendOnly))

def ay_pidd_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pidd_RecomputeObligation (currentDelta : Prop) (recompute : Prop) :=
  ay_pidd_Conj currentDelta recompute

def ay_pidd_DiagnosticDeltaLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentDelta : Prop)
    (staleRoot : Prop) (missingChangedCube : Prop)
    (frameDrift : Prop) (nonAppendOnly : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pidd_DeltaLogMembership previousLog
    (ay_pidd_Conj
      (ay_pidd_DeltaFailure
        staleRoot missingChangedCube frameDrift nonAppendOnly)
      (ay_pidd_Conj
        (ay_pidd_RecomputeObligation currentDelta recompute)
        (ay_pidd_NoSemanticClaim diagnostic)))
    nextLog

def ay_pidd_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pidd_Conj exitCode claim

def ay_pidd_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pidd_Disj
    (ay_pidd_ExitCodeSound exitCode (ay_pidd_Sat originalCnf model))
    (ay_pidd_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))

theorem ay_pidd_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pidd_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pidd_conj_left
    (left : Prop) (right : Prop) :
    ay_pidd_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pidd_conj_right
    (left : Prop) (right : Prop) :
    ay_pidd_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pidd_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pidd_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pidd_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pidd_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pidd_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pidd_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pidd_conj_left (before -> after) (after -> before) eq

theorem ay_pidd_delta_lineage
    (originalCnf : Prop) (partitionCnf : Prop)
    (oldFingerprint : Prop) (newFingerprint : Prop)
    (lineageWitness : Prop)
    (oldRoot : Prop) (newRoot : Prop) (deltaRoot : Prop)
    (changedCubes : Prop) (coveredCubes : Prop)
    (partitionModel : Prop) (originalModel : Prop) :
    ay_pidd_AcceptedDigestDelta
      originalCnf partitionCnf oldFingerprint newFingerprint
      lineageWitness oldRoot newRoot deltaRoot changedCubes coveredCubes
      partitionModel originalModel ->
    ay_pidd_FingerprintLineage
      oldFingerprint newFingerprint lineageWitness := by
  intro accepted
  exact ay_pidd_conj_left
    (ay_pidd_FingerprintLineage
      oldFingerprint newFingerprint lineageWitness)
    (ay_pidd_Conj
      (ay_pidd_DigestStep oldRoot newRoot deltaRoot)
      (ay_pidd_Conj
        (ay_pidd_ChangedCubeCoverage changedCubes coveredCubes)
        (ay_pidd_ReconstructionWitness
          partitionCnf originalCnf partitionModel originalModel)))
    accepted

theorem ay_pidd_delta_reconstruction
    (originalCnf : Prop) (partitionCnf : Prop)
    (oldFingerprint : Prop) (newFingerprint : Prop)
    (lineageWitness : Prop)
    (oldRoot : Prop) (newRoot : Prop) (deltaRoot : Prop)
    (changedCubes : Prop) (coveredCubes : Prop)
    (partitionModel : Prop) (originalModel : Prop) :
    ay_pidd_AcceptedDigestDelta
      originalCnf partitionCnf oldFingerprint newFingerprint
      lineageWitness oldRoot newRoot deltaRoot changedCubes coveredCubes
      partitionModel originalModel ->
    ay_pidd_ReconstructionWitness
      partitionCnf originalCnf partitionModel originalModel := by
  intro accepted
  exact ay_pidd_conj_right
    (ay_pidd_ChangedCubeCoverage changedCubes coveredCubes)
    (ay_pidd_ReconstructionWitness
      partitionCnf originalCnf partitionModel originalModel)
    (ay_pidd_conj_right
      (ay_pidd_DigestStep oldRoot newRoot deltaRoot)
      (ay_pidd_Conj
        (ay_pidd_ChangedCubeCoverage changedCubes coveredCubes)
        (ay_pidd_ReconstructionWitness
          partitionCnf originalCnf partitionModel originalModel))
      (ay_pidd_conj_right
        (ay_pidd_FingerprintLineage
          oldFingerprint newFingerprint lineageWitness)
        (ay_pidd_Conj
          (ay_pidd_DigestStep oldRoot newRoot deltaRoot)
          (ay_pidd_Conj
            (ay_pidd_ChangedCubeCoverage changedCubes coveredCubes)
            (ay_pidd_ReconstructionWitness
              partitionCnf originalCnf partitionModel originalModel)))
        accepted))

theorem ay_pidd_log_delta
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (partitionCnf : Prop)
    (oldFingerprint : Prop) (newFingerprint : Prop)
    (lineageWitness : Prop)
    (oldRoot : Prop) (newRoot : Prop) (deltaRoot : Prop)
    (changedCubes : Prop) (coveredCubes : Prop)
    (partitionModel : Prop) (originalModel : Prop) :
    ay_pidd_AcceptedDigestDeltaLogEntry
      previousLog nextLog originalCnf partitionCnf oldFingerprint
      newFingerprint lineageWitness oldRoot newRoot deltaRoot
      changedCubes coveredCubes partitionModel originalModel ->
    ay_pidd_AcceptedDigestDelta
      originalCnf partitionCnf oldFingerprint newFingerprint
      lineageWitness oldRoot newRoot deltaRoot changedCubes coveredCubes
      partitionModel originalModel := by
  intro log_entry
  exact ay_pidd_conj_left
    (ay_pidd_AcceptedDigestDelta
      originalCnf partitionCnf oldFingerprint newFingerprint
      lineageWitness oldRoot newRoot deltaRoot changedCubes coveredCubes
      partitionModel originalModel)
    nextLog
    (ay_pidd_conj_right previousLog
      (ay_pidd_Conj
        (ay_pidd_AcceptedDigestDelta
          originalCnf partitionCnf oldFingerprint newFingerprint
          lineageWitness oldRoot newRoot deltaRoot changedCubes
          coveredCubes partitionModel originalModel)
        nextLog)
      log_entry)

theorem ay_pidd_reconstruct_sat
    (partitionCnf : Prop) (originalCnf : Prop)
    (partitionModel : Prop) (originalModel : Prop) :
    ay_pidd_ReconstructionWitness
      partitionCnf originalCnf partitionModel originalModel ->
    ay_pidd_Sat partitionCnf partitionModel ->
    ay_pidd_Sat originalCnf originalModel := by
  intro witness
  exact ay_pidd_conj_left
    (ay_pidd_Sat partitionCnf partitionModel ->
      ay_pidd_Sat originalCnf originalModel)
    (ay_pidd_Equisat originalCnf partitionCnf)
    witness

theorem ay_pidd_reconstruction_equisat
    (partitionCnf : Prop) (originalCnf : Prop)
    (partitionModel : Prop) (originalModel : Prop) :
    ay_pidd_ReconstructionWitness
      partitionCnf originalCnf partitionModel originalModel ->
    ay_pidd_Equisat originalCnf partitionCnf := by
  intro witness
  exact ay_pidd_conj_right
    (ay_pidd_Sat partitionCnf partitionModel ->
      ay_pidd_Sat originalCnf originalModel)
    (ay_pidd_Equisat originalCnf partitionCnf)
    witness

theorem ay_pidd_public_sat
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (partitionCnf : Prop)
    (oldFingerprint : Prop) (newFingerprint : Prop)
    (lineageWitness : Prop)
    (oldRoot : Prop) (newRoot : Prop) (deltaRoot : Prop)
    (changedCubes : Prop) (coveredCubes : Prop)
    (partitionModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_pidd_AcceptedDigestDeltaLogEntry
      previousLog nextLog originalCnf partitionCnf oldFingerprint
      newFingerprint lineageWitness oldRoot newRoot deltaRoot
      changedCubes coveredCubes partitionModel originalModel ->
    ay_pidd_Sat partitionCnf partitionModel ->
    exitCode ->
    ay_pidd_PublicResult originalCnf originalModel
      certificate conflict exitCode := by
  intro log_entry sat hexit
  exact ay_pidd_disj_left
    (ay_pidd_ExitCodeSound exitCode
      (ay_pidd_Sat originalCnf originalModel))
    (ay_pidd_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pidd_conj_intro exitCode
      (ay_pidd_Sat originalCnf originalModel)
      hexit
      (ay_pidd_reconstruct_sat partitionCnf originalCnf
        partitionModel originalModel
        (ay_pidd_delta_reconstruction originalCnf partitionCnf
          oldFingerprint newFingerprint lineageWitness oldRoot newRoot
          deltaRoot changedCubes coveredCubes partitionModel originalModel
          (ay_pidd_log_delta previousLog nextLog originalCnf
            partitionCnf oldFingerprint newFingerprint lineageWitness
            oldRoot newRoot deltaRoot changedCubes coveredCubes
            partitionModel originalModel log_entry))
        sat))

theorem ay_pidd_public_unsat
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (partitionCnf : Prop)
    (oldFingerprint : Prop) (newFingerprint : Prop)
    (lineageWitness : Prop)
    (oldRoot : Prop) (newRoot : Prop) (deltaRoot : Prop)
    (changedCubes : Prop) (coveredCubes : Prop)
    (partitionModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_pidd_AcceptedDigestDeltaLogEntry
      previousLog nextLog originalCnf partitionCnf oldFingerprint
      newFingerprint lineageWitness oldRoot newRoot deltaRoot
      changedCubes coveredCubes partitionModel originalModel ->
    ay_pidd_Replay partitionCnf certificate conflict ->
    exitCode ->
    ay_pidd_PublicResult originalCnf originalModel
      certificate conflict exitCode := by
  intro log_entry replay hexit
  exact ay_pidd_disj_right
    (ay_pidd_ExitCodeSound exitCode
      (ay_pidd_Sat originalCnf originalModel))
    (ay_pidd_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pidd_conj_intro exitCode
      (certificate -> originalCnf -> conflict)
      hexit
      (fun hcertificate horiginal =>
        replay
          (ay_pidd_equisat_forward originalCnf partitionCnf
            (ay_pidd_reconstruction_equisat partitionCnf originalCnf
              partitionModel originalModel
              (ay_pidd_delta_reconstruction originalCnf partitionCnf
                oldFingerprint newFingerprint lineageWitness oldRoot
                newRoot deltaRoot changedCubes coveredCubes
                partitionModel originalModel
                (ay_pidd_log_delta previousLog nextLog originalCnf
                  partitionCnf oldFingerprint newFingerprint lineageWitness
                  oldRoot newRoot deltaRoot changedCubes coveredCubes
                  partitionModel originalModel log_entry)))
            horiginal)
          hcertificate))

theorem ay_pidd_failure_stale_root
    (staleRoot : Prop) (missingChangedCube : Prop)
    (frameDrift : Prop) (nonAppendOnly : Prop) :
    staleRoot ->
    ay_pidd_DeltaFailure
      staleRoot missingChangedCube frameDrift nonAppendOnly := by
  intro hfailure
  exact ay_pidd_disj_left staleRoot
    (ay_pidd_Disj missingChangedCube
      (ay_pidd_Disj frameDrift nonAppendOnly))
    hfailure

theorem ay_pidd_failure_missing_changed_cube
    (staleRoot : Prop) (missingChangedCube : Prop)
    (frameDrift : Prop) (nonAppendOnly : Prop) :
    missingChangedCube ->
    ay_pidd_DeltaFailure
      staleRoot missingChangedCube frameDrift nonAppendOnly := by
  intro hfailure
  exact ay_pidd_disj_right staleRoot
    (ay_pidd_Disj missingChangedCube
      (ay_pidd_Disj frameDrift nonAppendOnly))
    (ay_pidd_disj_left missingChangedCube
      (ay_pidd_Disj frameDrift nonAppendOnly)
      hfailure)

theorem ay_pidd_failure_frame_drift
    (staleRoot : Prop) (missingChangedCube : Prop)
    (frameDrift : Prop) (nonAppendOnly : Prop) :
    frameDrift ->
    ay_pidd_DeltaFailure
      staleRoot missingChangedCube frameDrift nonAppendOnly := by
  intro hfailure
  exact ay_pidd_disj_right staleRoot
    (ay_pidd_Disj missingChangedCube
      (ay_pidd_Disj frameDrift nonAppendOnly))
    (ay_pidd_disj_right missingChangedCube
      (ay_pidd_Disj frameDrift nonAppendOnly)
      (ay_pidd_disj_left frameDrift nonAppendOnly hfailure))

theorem ay_pidd_failure_non_append_only
    (staleRoot : Prop) (missingChangedCube : Prop)
    (frameDrift : Prop) (nonAppendOnly : Prop) :
    nonAppendOnly ->
    ay_pidd_DeltaFailure
      staleRoot missingChangedCube frameDrift nonAppendOnly := by
  intro hfailure
  exact ay_pidd_disj_right staleRoot
    (ay_pidd_Disj missingChangedCube
      (ay_pidd_Disj frameDrift nonAppendOnly))
    (ay_pidd_disj_right missingChangedCube
      (ay_pidd_Disj frameDrift nonAppendOnly)
      (ay_pidd_disj_right frameDrift nonAppendOnly hfailure))

theorem ay_pidd_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentDelta : Prop)
    (staleRoot : Prop) (missingChangedCube : Prop)
    (frameDrift : Prop) (nonAppendOnly : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pidd_DiagnosticDeltaLogEntry
      previousLog nextLog currentDelta staleRoot missingChangedCube
      frameDrift nonAppendOnly recompute diagnostic ->
    ay_pidd_DeltaFailure
      staleRoot missingChangedCube frameDrift nonAppendOnly := by
  intro log_entry
  exact ay_pidd_conj_left
    (ay_pidd_DeltaFailure
      staleRoot missingChangedCube frameDrift nonAppendOnly)
    (ay_pidd_Conj
      (ay_pidd_RecomputeObligation currentDelta recompute)
      (ay_pidd_NoSemanticClaim diagnostic))
    (ay_pidd_conj_left
      (ay_pidd_Conj
        (ay_pidd_DeltaFailure
          staleRoot missingChangedCube frameDrift nonAppendOnly)
        (ay_pidd_Conj
          (ay_pidd_RecomputeObligation currentDelta recompute)
          (ay_pidd_NoSemanticClaim diagnostic)))
      nextLog
      (ay_pidd_conj_right previousLog
        (ay_pidd_Conj
          (ay_pidd_Conj
            (ay_pidd_DeltaFailure
              staleRoot missingChangedCube frameDrift nonAppendOnly)
            (ay_pidd_Conj
              (ay_pidd_RecomputeObligation currentDelta recompute)
              (ay_pidd_NoSemanticClaim diagnostic)))
          nextLog)
        log_entry))

theorem ay_pidd_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentDelta : Prop)
    (staleRoot : Prop) (missingChangedCube : Prop)
    (frameDrift : Prop) (nonAppendOnly : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pidd_DiagnosticDeltaLogEntry
      previousLog nextLog currentDelta staleRoot missingChangedCube
      frameDrift nonAppendOnly recompute diagnostic ->
    ay_pidd_NoSemanticClaim diagnostic := by
  intro log_entry
  exact ay_pidd_conj_right
    (ay_pidd_RecomputeObligation currentDelta recompute)
    (ay_pidd_NoSemanticClaim diagnostic)
    (ay_pidd_conj_right
      (ay_pidd_DeltaFailure
        staleRoot missingChangedCube frameDrift nonAppendOnly)
      (ay_pidd_Conj
        (ay_pidd_RecomputeObligation currentDelta recompute)
        (ay_pidd_NoSemanticClaim diagnostic))
      (ay_pidd_conj_left
        (ay_pidd_Conj
          (ay_pidd_DeltaFailure
            staleRoot missingChangedCube frameDrift nonAppendOnly)
          (ay_pidd_Conj
            (ay_pidd_RecomputeObligation currentDelta recompute)
            (ay_pidd_NoSemanticClaim diagnostic)))
        nextLog
        (ay_pidd_conj_right previousLog
          (ay_pidd_Conj
            (ay_pidd_Conj
              (ay_pidd_DeltaFailure
                staleRoot missingChangedCube frameDrift nonAppendOnly)
              (ay_pidd_Conj
                (ay_pidd_RecomputeObligation currentDelta recompute)
                (ay_pidd_NoSemanticClaim diagnostic)))
            nextLog)
          log_entry)))

theorem ay_pidd_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentDelta : Prop)
    (staleRoot : Prop) (missingChangedCube : Prop)
    (frameDrift : Prop) (nonAppendOnly : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pidd_DiagnosticDeltaLogEntry
      previousLog nextLog currentDelta staleRoot missingChangedCube
      frameDrift nonAppendOnly recompute diagnostic ->
    ay_pidd_RecomputeObligation currentDelta recompute := by
  intro log_entry
  exact ay_pidd_conj_left
    (ay_pidd_RecomputeObligation currentDelta recompute)
    (ay_pidd_NoSemanticClaim diagnostic)
    (ay_pidd_conj_right
      (ay_pidd_DeltaFailure
        staleRoot missingChangedCube frameDrift nonAppendOnly)
      (ay_pidd_Conj
        (ay_pidd_RecomputeObligation currentDelta recompute)
        (ay_pidd_NoSemanticClaim diagnostic))
      (ay_pidd_conj_left
        (ay_pidd_Conj
          (ay_pidd_DeltaFailure
            staleRoot missingChangedCube frameDrift nonAppendOnly)
          (ay_pidd_Conj
            (ay_pidd_RecomputeObligation currentDelta recompute)
            (ay_pidd_NoSemanticClaim diagnostic)))
        nextLog
        (ay_pidd_conj_right previousLog
          (ay_pidd_Conj
            (ay_pidd_Conj
              (ay_pidd_DeltaFailure
                staleRoot missingChangedCube frameDrift nonAppendOnly)
              (ay_pidd_Conj
                (ay_pidd_RecomputeObligation currentDelta recompute)
                (ay_pidd_NoSemanticClaim diagnostic)))
            nextLog)
          log_entry)))

theorem ay_pidd_failure_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentDelta : Prop)
    (staleRoot : Prop) (missingChangedCube : Prop)
    (frameDrift : Prop) (nonAppendOnly : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pidd_DiagnosticDeltaLogEntry
      previousLog nextLog currentDelta staleRoot missingChangedCube
      frameDrift nonAppendOnly recompute diagnostic ->
    ay_pidd_Conj
      (ay_pidd_DeltaFailure
        staleRoot missingChangedCube frameDrift nonAppendOnly)
      (ay_pidd_Conj
        (ay_pidd_RecomputeObligation currentDelta recompute)
        (ay_pidd_NoSemanticClaim diagnostic)) := by
  intro log_entry
  exact ay_pidd_conj_intro
    (ay_pidd_DeltaFailure
      staleRoot missingChangedCube frameDrift nonAppendOnly)
    (ay_pidd_Conj
      (ay_pidd_RecomputeObligation currentDelta recompute)
      (ay_pidd_NoSemanticClaim diagnostic))
    (ay_pidd_diagnostic_failure previousLog nextLog currentDelta
      staleRoot missingChangedCube frameDrift nonAppendOnly recompute
      diagnostic log_entry)
    (ay_pidd_conj_intro
      (ay_pidd_RecomputeObligation currentDelta recompute)
      (ay_pidd_NoSemanticClaim diagnostic)
      (ay_pidd_diagnostic_recompute previousLog nextLog currentDelta
        staleRoot missingChangedCube frameDrift nonAppendOnly recompute
        diagnostic log_entry)
      (ay_pidd_diagnostic_no_claim previousLog nextLog currentDelta
        staleRoot missingChangedCube frameDrift nonAppendOnly recompute
        diagnostic log_entry))
