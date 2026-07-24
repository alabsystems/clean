-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Preprocessing partition digest archive soundness. The propositions stand for
-- formula fingerprints, cube frames, digest roots, reconstruction witnesses,
-- append-only archive membership, diagnostics, and public SAT/UNSAT outcomes.

def ay_ppda_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_ppda_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_ppda_Equisat (before : Prop) (after : Prop) :=
  ay_ppda_Conj (before -> after) (after -> before)

def ay_ppda_Sat (cnf : Prop) (model : Prop) :=
  ay_ppda_Conj cnf model

def ay_ppda_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_ppda_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_ppda_Conj (leftId -> rightId) (rightId -> leftId)

def ay_ppda_DigestMatch (archiveRoot : Prop) (runRoot : Prop) :=
  ay_ppda_Conj (archiveRoot -> runRoot) (runRoot -> archiveRoot)

def ay_ppda_CubeFrame (formulaFingerprint : Prop) (cubeFrame : Prop) :=
  ay_ppda_Conj formulaFingerprint cubeFrame

def ay_ppda_ReconstructionWitness
    (partitionCnf : Prop) (originalCnf : Prop)
    (partitionModel : Prop) (originalModel : Prop) :=
  ay_ppda_Conj
    (ay_ppda_Sat partitionCnf partitionModel ->
      ay_ppda_Sat originalCnf originalModel)
    (ay_ppda_Equisat originalCnf partitionCnf)

def ay_ppda_ArchiveMembership
    (previousArchive : Prop) (entry : Prop) (nextArchive : Prop) :=
  ay_ppda_Conj previousArchive (ay_ppda_Conj entry nextArchive)

def ay_ppda_PartitionArchiveEntry
    (originalCnf : Prop) (partitionCnf : Prop)
    (formulaFingerprint : Prop) (currentFingerprint : Prop)
    (cubeFrame : Prop) (currentCubeFrame : Prop)
    (archiveRoot : Prop) (runRoot : Prop)
    (partitionModel : Prop) (originalModel : Prop) :=
  ay_ppda_Conj
    (ay_ppda_IdMatch formulaFingerprint currentFingerprint)
    (ay_ppda_Conj
      (ay_ppda_IdMatch cubeFrame currentCubeFrame)
      (ay_ppda_Conj
        (ay_ppda_DigestMatch archiveRoot runRoot)
        (ay_ppda_ReconstructionWitness
          partitionCnf originalCnf partitionModel originalModel)))

def ay_ppda_AcceptedArchiveLogEntry
    (previousArchive : Prop) (nextArchive : Prop)
    (originalCnf : Prop) (partitionCnf : Prop)
    (formulaFingerprint : Prop) (currentFingerprint : Prop)
    (cubeFrame : Prop) (currentCubeFrame : Prop)
    (archiveRoot : Prop) (runRoot : Prop)
    (partitionModel : Prop) (originalModel : Prop) :=
  ay_ppda_ArchiveMembership previousArchive
    (ay_ppda_PartitionArchiveEntry
      originalCnf partitionCnf formulaFingerprint currentFingerprint
      cubeFrame currentCubeFrame archiveRoot runRoot partitionModel
      originalModel)
    nextArchive

def ay_ppda_ArchiveFailure
    (staleDigestRoot : Prop) (missingEntry : Prop)
    (frameDrift : Prop) (nonAppendOnly : Prop) :=
  ay_ppda_Disj staleDigestRoot
    (ay_ppda_Disj missingEntry
      (ay_ppda_Disj frameDrift nonAppendOnly))

def ay_ppda_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_ppda_RecomputeObligation (currentArchive : Prop) (recompute : Prop) :=
  ay_ppda_Conj currentArchive recompute

def ay_ppda_DiagnosticArchiveLogEntry
    (previousArchive : Prop) (nextArchive : Prop)
    (currentArchive : Prop)
    (staleDigestRoot : Prop) (missingEntry : Prop)
    (frameDrift : Prop) (nonAppendOnly : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_ppda_ArchiveMembership previousArchive
    (ay_ppda_Conj
      (ay_ppda_ArchiveFailure
        staleDigestRoot missingEntry frameDrift nonAppendOnly)
      (ay_ppda_Conj
        (ay_ppda_RecomputeObligation currentArchive recompute)
        (ay_ppda_NoSemanticClaim diagnostic)))
    nextArchive

def ay_ppda_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_ppda_Conj exitCode claim

def ay_ppda_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_ppda_Disj
    (ay_ppda_ExitCodeSound exitCode (ay_ppda_Sat originalCnf model))
    (ay_ppda_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))

theorem ay_ppda_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_ppda_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_ppda_conj_left
    (left : Prop) (right : Prop) :
    ay_ppda_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_ppda_conj_right
    (left : Prop) (right : Prop) :
    ay_ppda_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_ppda_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_ppda_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_ppda_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_ppda_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_ppda_equisat_forward
    (before : Prop) (after : Prop) :
    ay_ppda_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_ppda_conj_left (before -> after) (after -> before) eq

theorem ay_ppda_archive_entry_reconstruction
    (originalCnf : Prop) (partitionCnf : Prop)
    (formulaFingerprint : Prop) (currentFingerprint : Prop)
    (cubeFrame : Prop) (currentCubeFrame : Prop)
    (archiveRoot : Prop) (runRoot : Prop)
    (partitionModel : Prop) (originalModel : Prop) :
    ay_ppda_PartitionArchiveEntry
      originalCnf partitionCnf formulaFingerprint currentFingerprint
      cubeFrame currentCubeFrame archiveRoot runRoot partitionModel
      originalModel ->
    ay_ppda_ReconstructionWitness
      partitionCnf originalCnf partitionModel originalModel := by
  intro entry
  exact ay_ppda_conj_right
    (ay_ppda_DigestMatch archiveRoot runRoot)
    (ay_ppda_ReconstructionWitness
      partitionCnf originalCnf partitionModel originalModel)
    (ay_ppda_conj_right
      (ay_ppda_IdMatch cubeFrame currentCubeFrame)
      (ay_ppda_Conj
        (ay_ppda_DigestMatch archiveRoot runRoot)
        (ay_ppda_ReconstructionWitness
          partitionCnf originalCnf partitionModel originalModel))
      (ay_ppda_conj_right
        (ay_ppda_IdMatch formulaFingerprint currentFingerprint)
        (ay_ppda_Conj
          (ay_ppda_IdMatch cubeFrame currentCubeFrame)
          (ay_ppda_Conj
            (ay_ppda_DigestMatch archiveRoot runRoot)
            (ay_ppda_ReconstructionWitness
              partitionCnf originalCnf partitionModel originalModel)))
        entry))

theorem ay_ppda_archive_entry_fingerprint
    (originalCnf : Prop) (partitionCnf : Prop)
    (formulaFingerprint : Prop) (currentFingerprint : Prop)
    (cubeFrame : Prop) (currentCubeFrame : Prop)
    (archiveRoot : Prop) (runRoot : Prop)
    (partitionModel : Prop) (originalModel : Prop) :
    ay_ppda_PartitionArchiveEntry
      originalCnf partitionCnf formulaFingerprint currentFingerprint
      cubeFrame currentCubeFrame archiveRoot runRoot partitionModel
      originalModel ->
    ay_ppda_IdMatch formulaFingerprint currentFingerprint := by
  intro entry
  exact ay_ppda_conj_left
    (ay_ppda_IdMatch formulaFingerprint currentFingerprint)
    (ay_ppda_Conj
      (ay_ppda_IdMatch cubeFrame currentCubeFrame)
      (ay_ppda_Conj
        (ay_ppda_DigestMatch archiveRoot runRoot)
        (ay_ppda_ReconstructionWitness
          partitionCnf originalCnf partitionModel originalModel)))
    entry

theorem ay_ppda_log_entry
    (previousArchive : Prop) (nextArchive : Prop)
    (originalCnf : Prop) (partitionCnf : Prop)
    (formulaFingerprint : Prop) (currentFingerprint : Prop)
    (cubeFrame : Prop) (currentCubeFrame : Prop)
    (archiveRoot : Prop) (runRoot : Prop)
    (partitionModel : Prop) (originalModel : Prop) :
    ay_ppda_AcceptedArchiveLogEntry
      previousArchive nextArchive originalCnf partitionCnf
      formulaFingerprint currentFingerprint cubeFrame currentCubeFrame
      archiveRoot runRoot partitionModel originalModel ->
    ay_ppda_PartitionArchiveEntry
      originalCnf partitionCnf formulaFingerprint currentFingerprint
      cubeFrame currentCubeFrame archiveRoot runRoot partitionModel
      originalModel := by
  intro log_entry
  exact ay_ppda_conj_left
    (ay_ppda_PartitionArchiveEntry
      originalCnf partitionCnf formulaFingerprint currentFingerprint
      cubeFrame currentCubeFrame archiveRoot runRoot partitionModel
      originalModel)
    nextArchive
    (ay_ppda_conj_right previousArchive
      (ay_ppda_Conj
        (ay_ppda_PartitionArchiveEntry
          originalCnf partitionCnf formulaFingerprint currentFingerprint
          cubeFrame currentCubeFrame archiveRoot runRoot partitionModel
          originalModel)
        nextArchive)
      log_entry)

theorem ay_ppda_reconstruct_sat
    (partitionCnf : Prop) (originalCnf : Prop)
    (partitionModel : Prop) (originalModel : Prop) :
    ay_ppda_ReconstructionWitness
      partitionCnf originalCnf partitionModel originalModel ->
    ay_ppda_Sat partitionCnf partitionModel ->
    ay_ppda_Sat originalCnf originalModel := by
  intro witness
  exact ay_ppda_conj_left
    (ay_ppda_Sat partitionCnf partitionModel ->
      ay_ppda_Sat originalCnf originalModel)
    (ay_ppda_Equisat originalCnf partitionCnf)
    witness

theorem ay_ppda_reconstruction_equisat
    (partitionCnf : Prop) (originalCnf : Prop)
    (partitionModel : Prop) (originalModel : Prop) :
    ay_ppda_ReconstructionWitness
      partitionCnf originalCnf partitionModel originalModel ->
    ay_ppda_Equisat originalCnf partitionCnf := by
  intro witness
  exact ay_ppda_conj_right
    (ay_ppda_Sat partitionCnf partitionModel ->
      ay_ppda_Sat originalCnf originalModel)
    (ay_ppda_Equisat originalCnf partitionCnf)
    witness

theorem ay_ppda_public_sat
    (previousArchive : Prop) (nextArchive : Prop)
    (originalCnf : Prop) (partitionCnf : Prop)
    (formulaFingerprint : Prop) (currentFingerprint : Prop)
    (cubeFrame : Prop) (currentCubeFrame : Prop)
    (archiveRoot : Prop) (runRoot : Prop)
    (partitionModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_ppda_AcceptedArchiveLogEntry
      previousArchive nextArchive originalCnf partitionCnf
      formulaFingerprint currentFingerprint cubeFrame currentCubeFrame
      archiveRoot runRoot partitionModel originalModel ->
    ay_ppda_Sat partitionCnf partitionModel ->
    exitCode ->
    ay_ppda_PublicResult originalCnf originalModel
      certificate conflict exitCode := by
  intro log_entry sat hexit
  exact ay_ppda_disj_left
    (ay_ppda_ExitCodeSound exitCode
      (ay_ppda_Sat originalCnf originalModel))
    (ay_ppda_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_ppda_conj_intro exitCode
      (ay_ppda_Sat originalCnf originalModel)
      hexit
      (ay_ppda_reconstruct_sat partitionCnf originalCnf
        partitionModel originalModel
        (ay_ppda_archive_entry_reconstruction originalCnf partitionCnf
          formulaFingerprint currentFingerprint cubeFrame currentCubeFrame
          archiveRoot runRoot partitionModel originalModel
          (ay_ppda_log_entry previousArchive nextArchive originalCnf
            partitionCnf formulaFingerprint currentFingerprint cubeFrame
            currentCubeFrame archiveRoot runRoot partitionModel
            originalModel log_entry))
        sat))

theorem ay_ppda_public_unsat
    (previousArchive : Prop) (nextArchive : Prop)
    (originalCnf : Prop) (partitionCnf : Prop)
    (formulaFingerprint : Prop) (currentFingerprint : Prop)
    (cubeFrame : Prop) (currentCubeFrame : Prop)
    (archiveRoot : Prop) (runRoot : Prop)
    (partitionModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_ppda_AcceptedArchiveLogEntry
      previousArchive nextArchive originalCnf partitionCnf
      formulaFingerprint currentFingerprint cubeFrame currentCubeFrame
      archiveRoot runRoot partitionModel originalModel ->
    ay_ppda_Replay partitionCnf certificate conflict ->
    exitCode ->
    ay_ppda_PublicResult originalCnf originalModel
      certificate conflict exitCode := by
  intro log_entry replay hexit
  exact ay_ppda_disj_right
    (ay_ppda_ExitCodeSound exitCode
      (ay_ppda_Sat originalCnf originalModel))
    (ay_ppda_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_ppda_conj_intro exitCode
      (certificate -> originalCnf -> conflict)
      hexit
      (fun hcertificate horiginal =>
        replay
          (ay_ppda_equisat_forward originalCnf partitionCnf
            (ay_ppda_reconstruction_equisat partitionCnf originalCnf
              partitionModel originalModel
              (ay_ppda_archive_entry_reconstruction originalCnf partitionCnf
                formulaFingerprint currentFingerprint cubeFrame
                currentCubeFrame archiveRoot runRoot partitionModel
                originalModel
                (ay_ppda_log_entry previousArchive nextArchive originalCnf
                  partitionCnf formulaFingerprint currentFingerprint
                  cubeFrame currentCubeFrame archiveRoot runRoot
                  partitionModel originalModel log_entry)))
            horiginal)
          hcertificate))

theorem ay_ppda_failure_stale_digest
    (staleDigestRoot : Prop) (missingEntry : Prop)
    (frameDrift : Prop) (nonAppendOnly : Prop) :
    staleDigestRoot ->
    ay_ppda_ArchiveFailure
      staleDigestRoot missingEntry frameDrift nonAppendOnly := by
  intro hfailure
  exact ay_ppda_disj_left staleDigestRoot
    (ay_ppda_Disj missingEntry
      (ay_ppda_Disj frameDrift nonAppendOnly))
    hfailure

theorem ay_ppda_failure_missing_entry
    (staleDigestRoot : Prop) (missingEntry : Prop)
    (frameDrift : Prop) (nonAppendOnly : Prop) :
    missingEntry ->
    ay_ppda_ArchiveFailure
      staleDigestRoot missingEntry frameDrift nonAppendOnly := by
  intro hfailure
  exact ay_ppda_disj_right staleDigestRoot
    (ay_ppda_Disj missingEntry
      (ay_ppda_Disj frameDrift nonAppendOnly))
    (ay_ppda_disj_left missingEntry
      (ay_ppda_Disj frameDrift nonAppendOnly)
      hfailure)

theorem ay_ppda_failure_frame_drift
    (staleDigestRoot : Prop) (missingEntry : Prop)
    (frameDrift : Prop) (nonAppendOnly : Prop) :
    frameDrift ->
    ay_ppda_ArchiveFailure
      staleDigestRoot missingEntry frameDrift nonAppendOnly := by
  intro hfailure
  exact ay_ppda_disj_right staleDigestRoot
    (ay_ppda_Disj missingEntry
      (ay_ppda_Disj frameDrift nonAppendOnly))
    (ay_ppda_disj_right missingEntry
      (ay_ppda_Disj frameDrift nonAppendOnly)
      (ay_ppda_disj_left frameDrift nonAppendOnly hfailure))

theorem ay_ppda_failure_non_append_only
    (staleDigestRoot : Prop) (missingEntry : Prop)
    (frameDrift : Prop) (nonAppendOnly : Prop) :
    nonAppendOnly ->
    ay_ppda_ArchiveFailure
      staleDigestRoot missingEntry frameDrift nonAppendOnly := by
  intro hfailure
  exact ay_ppda_disj_right staleDigestRoot
    (ay_ppda_Disj missingEntry
      (ay_ppda_Disj frameDrift nonAppendOnly))
    (ay_ppda_disj_right missingEntry
      (ay_ppda_Disj frameDrift nonAppendOnly)
      (ay_ppda_disj_right frameDrift nonAppendOnly hfailure))

theorem ay_ppda_diagnostic_failure
    (previousArchive : Prop) (nextArchive : Prop)
    (currentArchive : Prop)
    (staleDigestRoot : Prop) (missingEntry : Prop)
    (frameDrift : Prop) (nonAppendOnly : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_ppda_DiagnosticArchiveLogEntry
      previousArchive nextArchive currentArchive staleDigestRoot
      missingEntry frameDrift nonAppendOnly recompute diagnostic ->
    ay_ppda_ArchiveFailure
      staleDigestRoot missingEntry frameDrift nonAppendOnly := by
  intro log_entry
  exact ay_ppda_conj_left
    (ay_ppda_ArchiveFailure
      staleDigestRoot missingEntry frameDrift nonAppendOnly)
    (ay_ppda_Conj
      (ay_ppda_RecomputeObligation currentArchive recompute)
      (ay_ppda_NoSemanticClaim diagnostic))
    (ay_ppda_conj_left
      (ay_ppda_Conj
        (ay_ppda_ArchiveFailure
          staleDigestRoot missingEntry frameDrift nonAppendOnly)
        (ay_ppda_Conj
          (ay_ppda_RecomputeObligation currentArchive recompute)
          (ay_ppda_NoSemanticClaim diagnostic)))
      nextArchive
      (ay_ppda_conj_right previousArchive
        (ay_ppda_Conj
          (ay_ppda_Conj
            (ay_ppda_ArchiveFailure
              staleDigestRoot missingEntry frameDrift nonAppendOnly)
            (ay_ppda_Conj
              (ay_ppda_RecomputeObligation currentArchive recompute)
              (ay_ppda_NoSemanticClaim diagnostic)))
          nextArchive)
        log_entry))

theorem ay_ppda_diagnostic_no_claim
    (previousArchive : Prop) (nextArchive : Prop)
    (currentArchive : Prop)
    (staleDigestRoot : Prop) (missingEntry : Prop)
    (frameDrift : Prop) (nonAppendOnly : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_ppda_DiagnosticArchiveLogEntry
      previousArchive nextArchive currentArchive staleDigestRoot
      missingEntry frameDrift nonAppendOnly recompute diagnostic ->
    ay_ppda_NoSemanticClaim diagnostic := by
  intro log_entry
  exact ay_ppda_conj_right
    (ay_ppda_RecomputeObligation currentArchive recompute)
    (ay_ppda_NoSemanticClaim diagnostic)
    (ay_ppda_conj_right
      (ay_ppda_ArchiveFailure
        staleDigestRoot missingEntry frameDrift nonAppendOnly)
      (ay_ppda_Conj
        (ay_ppda_RecomputeObligation currentArchive recompute)
        (ay_ppda_NoSemanticClaim diagnostic))
      (ay_ppda_conj_left
        (ay_ppda_Conj
          (ay_ppda_ArchiveFailure
            staleDigestRoot missingEntry frameDrift nonAppendOnly)
          (ay_ppda_Conj
            (ay_ppda_RecomputeObligation currentArchive recompute)
            (ay_ppda_NoSemanticClaim diagnostic)))
        nextArchive
        (ay_ppda_conj_right previousArchive
          (ay_ppda_Conj
            (ay_ppda_Conj
              (ay_ppda_ArchiveFailure
                staleDigestRoot missingEntry frameDrift nonAppendOnly)
              (ay_ppda_Conj
                (ay_ppda_RecomputeObligation currentArchive recompute)
                (ay_ppda_NoSemanticClaim diagnostic)))
            nextArchive)
          log_entry)))

theorem ay_ppda_diagnostic_recompute
    (previousArchive : Prop) (nextArchive : Prop)
    (currentArchive : Prop)
    (staleDigestRoot : Prop) (missingEntry : Prop)
    (frameDrift : Prop) (nonAppendOnly : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_ppda_DiagnosticArchiveLogEntry
      previousArchive nextArchive currentArchive staleDigestRoot
      missingEntry frameDrift nonAppendOnly recompute diagnostic ->
    ay_ppda_RecomputeObligation currentArchive recompute := by
  intro log_entry
  exact ay_ppda_conj_left
    (ay_ppda_RecomputeObligation currentArchive recompute)
    (ay_ppda_NoSemanticClaim diagnostic)
    (ay_ppda_conj_right
      (ay_ppda_ArchiveFailure
        staleDigestRoot missingEntry frameDrift nonAppendOnly)
      (ay_ppda_Conj
        (ay_ppda_RecomputeObligation currentArchive recompute)
        (ay_ppda_NoSemanticClaim diagnostic))
      (ay_ppda_conj_left
        (ay_ppda_Conj
          (ay_ppda_ArchiveFailure
            staleDigestRoot missingEntry frameDrift nonAppendOnly)
          (ay_ppda_Conj
            (ay_ppda_RecomputeObligation currentArchive recompute)
            (ay_ppda_NoSemanticClaim diagnostic)))
        nextArchive
        (ay_ppda_conj_right previousArchive
          (ay_ppda_Conj
            (ay_ppda_Conj
              (ay_ppda_ArchiveFailure
                staleDigestRoot missingEntry frameDrift nonAppendOnly)
              (ay_ppda_Conj
                (ay_ppda_RecomputeObligation currentArchive recompute)
                (ay_ppda_NoSemanticClaim diagnostic)))
            nextArchive)
          log_entry)))

theorem ay_ppda_failure_no_claim
    (previousArchive : Prop) (nextArchive : Prop)
    (currentArchive : Prop)
    (staleDigestRoot : Prop) (missingEntry : Prop)
    (frameDrift : Prop) (nonAppendOnly : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_ppda_DiagnosticArchiveLogEntry
      previousArchive nextArchive currentArchive staleDigestRoot
      missingEntry frameDrift nonAppendOnly recompute diagnostic ->
    ay_ppda_Conj
      (ay_ppda_ArchiveFailure
        staleDigestRoot missingEntry frameDrift nonAppendOnly)
      (ay_ppda_Conj
        (ay_ppda_RecomputeObligation currentArchive recompute)
        (ay_ppda_NoSemanticClaim diagnostic)) := by
  intro log_entry
  exact ay_ppda_conj_intro
    (ay_ppda_ArchiveFailure
      staleDigestRoot missingEntry frameDrift nonAppendOnly)
    (ay_ppda_Conj
      (ay_ppda_RecomputeObligation currentArchive recompute)
      (ay_ppda_NoSemanticClaim diagnostic))
    (ay_ppda_diagnostic_failure previousArchive nextArchive currentArchive
      staleDigestRoot missingEntry frameDrift nonAppendOnly recompute
      diagnostic log_entry)
    (ay_ppda_conj_intro
      (ay_ppda_RecomputeObligation currentArchive recompute)
      (ay_ppda_NoSemanticClaim diagnostic)
      (ay_ppda_diagnostic_recompute previousArchive nextArchive
        currentArchive staleDigestRoot missingEntry frameDrift
        nonAppendOnly recompute diagnostic log_entry)
      (ay_ppda_diagnostic_no_claim previousArchive nextArchive
        currentArchive staleDigestRoot missingEntry frameDrift
        nonAppendOnly recompute diagnostic log_entry))
