-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Cube-batch manifest partition soundness. The propositions stand for
-- coverage, disjointness, cube frames, delta digests, reconstruction evidence,
-- diagnostics, and public SAT/UNSAT outcomes for bounded cube partitions.

def AyConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyEquisat (before : Prop) (after : Prop) :=
  AyConj (before -> after) (after -> before)

def AySat (cnf : Prop) (model : Prop) :=
  AyConj cnf model

def AyReplay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def AyDigestMatch (manifestDigest : Prop) (runDigest : Prop) :=
  AyConj (manifestDigest -> runDigest) (runDigest -> manifestDigest)

def AyCubeFrame (baseCnf : Prop) (cubeAssumptions : Prop) :=
  AyConj baseCnf cubeAssumptions

def AyPartitionEvidence
    (intendedSpace : Prop) (leftCube : Prop) (rightCube : Prop)
    (coverage : Prop) (disjointness : Prop) :=
  AyConj coverage
    (AyConj disjointness
      (AyConj (intendedSpace -> AyDisj leftCube rightCube)
        (leftCube -> rightCube -> False)))

def AyReconstructionMap
    (preprocessedCube : Prop) (cubeFrame : Prop)
    (preModel : Prop) (cubeModel : Prop) :=
  AyConj
    (AySat preprocessedCube preModel -> AySat cubeFrame cubeModel)
    (AyEquisat cubeFrame preprocessedCube)

def AyManifestPartitionEntry
    (cubeFrame : Prop) (preprocessedCube : Prop)
    (deltaDigest : Prop) (runDigest : Prop)
    (preModel : Prop) (cubeModel : Prop) :=
  AyConj
    (AyDigestMatch deltaDigest runDigest)
    (AyReconstructionMap preprocessedCube cubeFrame preModel cubeModel)

def AyBatchManifest
    (intendedSpace : Prop)
    (leftCube : Prop) (rightCube : Prop)
    (coverage : Prop) (disjointness : Prop)
    (leftFrame : Prop) (leftPre : Prop)
    (leftDigest : Prop) (leftRunDigest : Prop)
    (leftPreModel : Prop) (leftModel : Prop)
    (rightFrame : Prop) (rightPre : Prop)
    (rightDigest : Prop) (rightRunDigest : Prop)
    (rightPreModel : Prop) (rightModel : Prop) :=
  AyConj
    (AyPartitionEvidence intendedSpace leftCube rightCube
      coverage disjointness)
    (AyConj
      (AyManifestPartitionEntry
        leftFrame leftPre leftDigest leftRunDigest leftPreModel leftModel)
      (AyManifestPartitionEntry
        rightFrame rightPre rightDigest rightRunDigest
        rightPreModel rightModel))

def AyPartitionFailure
    (overlap : Prop) (missingPartition : Prop)
    (digestMismatch : Prop) (frameMismatch : Prop) :=
  AyDisj overlap
    (AyDisj missingPartition (AyDisj digestMismatch frameMismatch))

def AyNoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def AyRecomputeObligation (currentManifest : Prop) (recompute : Prop) :=
  AyConj currentManifest recompute

def AyAppendOnlyEntry (previousLog : Prop) (entry : Prop) (nextLog : Prop) :=
  AyConj previousLog (AyConj entry nextLog)

def AyAcceptedBatchManifestLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (intendedSpace : Prop)
    (leftCube : Prop) (rightCube : Prop)
    (coverage : Prop) (disjointness : Prop)
    (leftFrame : Prop) (leftPre : Prop)
    (leftDigest : Prop) (leftRunDigest : Prop)
    (leftPreModel : Prop) (leftModel : Prop)
    (rightFrame : Prop) (rightPre : Prop)
    (rightDigest : Prop) (rightRunDigest : Prop)
    (rightPreModel : Prop) (rightModel : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyBatchManifest intendedSpace leftCube rightCube coverage
      disjointness leftFrame leftPre leftDigest leftRunDigest
      leftPreModel leftModel rightFrame rightPre rightDigest
      rightRunDigest rightPreModel rightModel)
    nextLog

def AyDiagnosticBatchManifestLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentManifest : Prop)
    (overlap : Prop) (missingPartition : Prop)
    (digestMismatch : Prop) (frameMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyConj
      (AyPartitionFailure
        overlap missingPartition digestMismatch frameMismatch)
      (AyConj
        (AyRecomputeObligation currentManifest recompute)
        (AyNoSemanticClaim diagnostic)))
    nextLog

def AyExitCodeSound (exitCode : Prop) (claim : Prop) :=
  AyConj exitCode claim

def AyPublicResult
    (cubeFrame : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  AyDisj
    (AyExitCodeSound exitCode (AySat cubeFrame model))
    (AyExitCodeSound exitCode (certificate -> cubeFrame -> conflict))

theorem ay_pbmp_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyConj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pbmp_conj_left
    (left : Prop) (right : Prop) :
    AyConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pbmp_conj_right
    (left : Prop) (right : Prop) :
    AyConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pbmp_disj_left
    (left : Prop) (right : Prop) :
    left -> AyDisj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pbmp_disj_right
    (left : Prop) (right : Prop) :
    right -> AyDisj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pbmp_equisat_forward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pbmp_conj_left (before -> after) (after -> before) eq

theorem ay_pbmp_partition_coverage
    (intendedSpace : Prop) (leftCube : Prop) (rightCube : Prop)
    (coverage : Prop) (disjointness : Prop) :
    AyPartitionEvidence intendedSpace leftCube rightCube
      coverage disjointness ->
    coverage := by
  intro evidence
  exact ay_pbmp_conj_left coverage
    (AyConj disjointness
      (AyConj (intendedSpace -> AyDisj leftCube rightCube)
        (leftCube -> rightCube -> False)))
    evidence

theorem ay_pbmp_partition_disjointness
    (intendedSpace : Prop) (leftCube : Prop) (rightCube : Prop)
    (coverage : Prop) (disjointness : Prop) :
    AyPartitionEvidence intendedSpace leftCube rightCube
      coverage disjointness ->
    disjointness := by
  intro evidence
  exact ay_pbmp_conj_left disjointness
    (AyConj (intendedSpace -> AyDisj leftCube rightCube)
      (leftCube -> rightCube -> False))
    (ay_pbmp_conj_right coverage
      (AyConj disjointness
        (AyConj (intendedSpace -> AyDisj leftCube rightCube)
          (leftCube -> rightCube -> False)))
      evidence)

theorem ay_pbmp_entry_reconstruction
    (cubeFrame : Prop) (preprocessedCube : Prop)
    (deltaDigest : Prop) (runDigest : Prop)
    (preModel : Prop) (cubeModel : Prop) :
    AyManifestPartitionEntry
      cubeFrame preprocessedCube deltaDigest runDigest preModel cubeModel ->
    AyReconstructionMap preprocessedCube cubeFrame preModel cubeModel := by
  intro entry
  exact ay_pbmp_conj_right
    (AyDigestMatch deltaDigest runDigest)
    (AyReconstructionMap preprocessedCube cubeFrame preModel cubeModel)
    entry

theorem ay_pbmp_reconstruct_sat
    (preprocessedCube : Prop) (cubeFrame : Prop)
    (preModel : Prop) (cubeModel : Prop) :
    AyReconstructionMap preprocessedCube cubeFrame preModel cubeModel ->
    AySat preprocessedCube preModel ->
    AySat cubeFrame cubeModel := by
  intro reconstruction
  exact ay_pbmp_conj_left
    (AySat preprocessedCube preModel -> AySat cubeFrame cubeModel)
    (AyEquisat cubeFrame preprocessedCube)
    reconstruction

theorem ay_pbmp_reconstruction_equisat
    (preprocessedCube : Prop) (cubeFrame : Prop)
    (preModel : Prop) (cubeModel : Prop) :
    AyReconstructionMap preprocessedCube cubeFrame preModel cubeModel ->
    AyEquisat cubeFrame preprocessedCube := by
  intro reconstruction
  exact ay_pbmp_conj_right
    (AySat preprocessedCube preModel -> AySat cubeFrame cubeModel)
    (AyEquisat cubeFrame preprocessedCube)
    reconstruction

theorem ay_pbmp_manifest_left_entry
    (intendedSpace : Prop)
    (leftCube : Prop) (rightCube : Prop)
    (coverage : Prop) (disjointness : Prop)
    (leftFrame : Prop) (leftPre : Prop)
    (leftDigest : Prop) (leftRunDigest : Prop)
    (leftPreModel : Prop) (leftModel : Prop)
    (rightFrame : Prop) (rightPre : Prop)
    (rightDigest : Prop) (rightRunDigest : Prop)
    (rightPreModel : Prop) (rightModel : Prop) :
    AyBatchManifest intendedSpace leftCube rightCube coverage
      disjointness leftFrame leftPre leftDigest leftRunDigest
      leftPreModel leftModel rightFrame rightPre rightDigest
      rightRunDigest rightPreModel rightModel ->
    AyManifestPartitionEntry
      leftFrame leftPre leftDigest leftRunDigest leftPreModel leftModel := by
  intro manifest
  exact ay_pbmp_conj_left
    (AyManifestPartitionEntry
      leftFrame leftPre leftDigest leftRunDigest leftPreModel leftModel)
    (AyManifestPartitionEntry
      rightFrame rightPre rightDigest rightRunDigest
      rightPreModel rightModel)
    (ay_pbmp_conj_right
      (AyPartitionEvidence intendedSpace leftCube rightCube
        coverage disjointness)
      (AyConj
        (AyManifestPartitionEntry
          leftFrame leftPre leftDigest leftRunDigest leftPreModel leftModel)
        (AyManifestPartitionEntry
          rightFrame rightPre rightDigest rightRunDigest
          rightPreModel rightModel))
      manifest)

theorem ay_pbmp_log_manifest
    (previousLog : Prop) (nextLog : Prop)
    (intendedSpace : Prop)
    (leftCube : Prop) (rightCube : Prop)
    (coverage : Prop) (disjointness : Prop)
    (leftFrame : Prop) (leftPre : Prop)
    (leftDigest : Prop) (leftRunDigest : Prop)
    (leftPreModel : Prop) (leftModel : Prop)
    (rightFrame : Prop) (rightPre : Prop)
    (rightDigest : Prop) (rightRunDigest : Prop)
    (rightPreModel : Prop) (rightModel : Prop) :
    AyAcceptedBatchManifestLogEntry previousLog nextLog
      intendedSpace leftCube rightCube coverage disjointness
      leftFrame leftPre leftDigest leftRunDigest leftPreModel leftModel
      rightFrame rightPre rightDigest rightRunDigest
      rightPreModel rightModel ->
    AyBatchManifest intendedSpace leftCube rightCube coverage
      disjointness leftFrame leftPre leftDigest leftRunDigest
      leftPreModel leftModel rightFrame rightPre rightDigest
      rightRunDigest rightPreModel rightModel := by
  intro entry
  exact ay_pbmp_conj_left
    (AyBatchManifest intendedSpace leftCube rightCube coverage
      disjointness leftFrame leftPre leftDigest leftRunDigest
      leftPreModel leftModel rightFrame rightPre rightDigest
      rightRunDigest rightPreModel rightModel)
    nextLog
    (ay_pbmp_conj_right previousLog
      (AyConj
        (AyBatchManifest intendedSpace leftCube rightCube coverage
          disjointness leftFrame leftPre leftDigest leftRunDigest
          leftPreModel leftModel rightFrame rightPre rightDigest
          rightRunDigest rightPreModel rightModel)
        nextLog)
      entry)

theorem ay_pbmp_public_sat_left
    (previousLog : Prop) (nextLog : Prop)
    (intendedSpace : Prop)
    (leftCube : Prop) (rightCube : Prop)
    (coverage : Prop) (disjointness : Prop)
    (leftFrame : Prop) (leftPre : Prop)
    (leftDigest : Prop) (leftRunDigest : Prop)
    (leftPreModel : Prop) (leftModel : Prop)
    (rightFrame : Prop) (rightPre : Prop)
    (rightDigest : Prop) (rightRunDigest : Prop)
    (rightPreModel : Prop) (rightModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedBatchManifestLogEntry previousLog nextLog
      intendedSpace leftCube rightCube coverage disjointness
      leftFrame leftPre leftDigest leftRunDigest leftPreModel leftModel
      rightFrame rightPre rightDigest rightRunDigest
      rightPreModel rightModel ->
    AySat leftPre leftPreModel ->
    exitCode ->
    AyPublicResult leftFrame leftModel certificate conflict exitCode := by
  intro entry sat hexit
  exact ay_pbmp_disj_left
    (AyExitCodeSound exitCode (AySat leftFrame leftModel))
    (AyExitCodeSound exitCode (certificate -> leftFrame -> conflict))
    (ay_pbmp_conj_intro exitCode (AySat leftFrame leftModel)
      hexit
      (ay_pbmp_reconstruct_sat leftPre leftFrame leftPreModel leftModel
        (ay_pbmp_entry_reconstruction leftFrame leftPre leftDigest
          leftRunDigest leftPreModel leftModel
          (ay_pbmp_manifest_left_entry intendedSpace leftCube rightCube
            coverage disjointness leftFrame leftPre leftDigest
            leftRunDigest leftPreModel leftModel rightFrame rightPre
            rightDigest rightRunDigest rightPreModel rightModel
            (ay_pbmp_log_manifest previousLog nextLog intendedSpace
              leftCube rightCube coverage disjointness leftFrame leftPre
              leftDigest leftRunDigest leftPreModel leftModel rightFrame
              rightPre rightDigest rightRunDigest rightPreModel rightModel
              entry)))
        sat))

theorem ay_pbmp_public_unsat_left
    (previousLog : Prop) (nextLog : Prop)
    (intendedSpace : Prop)
    (leftCube : Prop) (rightCube : Prop)
    (coverage : Prop) (disjointness : Prop)
    (leftFrame : Prop) (leftPre : Prop)
    (leftDigest : Prop) (leftRunDigest : Prop)
    (leftPreModel : Prop) (leftModel : Prop)
    (rightFrame : Prop) (rightPre : Prop)
    (rightDigest : Prop) (rightRunDigest : Prop)
    (rightPreModel : Prop) (rightModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedBatchManifestLogEntry previousLog nextLog
      intendedSpace leftCube rightCube coverage disjointness
      leftFrame leftPre leftDigest leftRunDigest leftPreModel leftModel
      rightFrame rightPre rightDigest rightRunDigest
      rightPreModel rightModel ->
    AyReplay leftPre certificate conflict ->
    exitCode ->
    AyPublicResult leftFrame leftModel certificate conflict exitCode := by
  intro entry replay hexit
  exact ay_pbmp_disj_right
    (AyExitCodeSound exitCode (AySat leftFrame leftModel))
    (AyExitCodeSound exitCode (certificate -> leftFrame -> conflict))
    (ay_pbmp_conj_intro exitCode
      (certificate -> leftFrame -> conflict)
      hexit
      (fun hcertificate hframe =>
        replay
          (ay_pbmp_equisat_forward leftFrame leftPre
            (ay_pbmp_reconstruction_equisat leftPre leftFrame
              leftPreModel leftModel
              (ay_pbmp_entry_reconstruction leftFrame leftPre leftDigest
                leftRunDigest leftPreModel leftModel
                (ay_pbmp_manifest_left_entry intendedSpace leftCube
                  rightCube coverage disjointness leftFrame leftPre
                  leftDigest leftRunDigest leftPreModel leftModel
                  rightFrame rightPre rightDigest rightRunDigest
                  rightPreModel rightModel
                  (ay_pbmp_log_manifest previousLog nextLog intendedSpace
                    leftCube rightCube coverage disjointness leftFrame
                    leftPre leftDigest leftRunDigest leftPreModel leftModel
                    rightFrame rightPre rightDigest rightRunDigest
                    rightPreModel rightModel entry))))
            hframe)
          hcertificate))

theorem ay_pbmp_failure_overlap
    (overlap : Prop) (missingPartition : Prop)
    (digestMismatch : Prop) (frameMismatch : Prop) :
    overlap ->
    AyPartitionFailure overlap missingPartition digestMismatch frameMismatch := by
  intro hfailure
  exact ay_pbmp_disj_left overlap
    (AyDisj missingPartition (AyDisj digestMismatch frameMismatch))
    hfailure

theorem ay_pbmp_failure_missing
    (overlap : Prop) (missingPartition : Prop)
    (digestMismatch : Prop) (frameMismatch : Prop) :
    missingPartition ->
    AyPartitionFailure overlap missingPartition digestMismatch frameMismatch := by
  intro hfailure
  exact ay_pbmp_disj_right overlap
    (AyDisj missingPartition (AyDisj digestMismatch frameMismatch))
    (ay_pbmp_disj_left missingPartition
      (AyDisj digestMismatch frameMismatch)
      hfailure)

theorem ay_pbmp_failure_digest
    (overlap : Prop) (missingPartition : Prop)
    (digestMismatch : Prop) (frameMismatch : Prop) :
    digestMismatch ->
    AyPartitionFailure overlap missingPartition digestMismatch frameMismatch := by
  intro hfailure
  exact ay_pbmp_disj_right overlap
    (AyDisj missingPartition (AyDisj digestMismatch frameMismatch))
    (ay_pbmp_disj_right missingPartition
      (AyDisj digestMismatch frameMismatch)
      (ay_pbmp_disj_left digestMismatch frameMismatch hfailure))

theorem ay_pbmp_failure_frame
    (overlap : Prop) (missingPartition : Prop)
    (digestMismatch : Prop) (frameMismatch : Prop) :
    frameMismatch ->
    AyPartitionFailure overlap missingPartition digestMismatch frameMismatch := by
  intro hfailure
  exact ay_pbmp_disj_right overlap
    (AyDisj missingPartition (AyDisj digestMismatch frameMismatch))
    (ay_pbmp_disj_right missingPartition
      (AyDisj digestMismatch frameMismatch)
      (ay_pbmp_disj_right digestMismatch frameMismatch hfailure))

theorem ay_pbmp_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentManifest : Prop)
    (overlap : Prop) (missingPartition : Prop)
    (digestMismatch : Prop) (frameMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticBatchManifestLogEntry
      previousLog nextLog currentManifest overlap missingPartition
      digestMismatch frameMismatch recompute diagnostic ->
    AyPartitionFailure overlap missingPartition digestMismatch frameMismatch := by
  intro entry
  exact ay_pbmp_conj_left
    (AyPartitionFailure overlap missingPartition digestMismatch frameMismatch)
    (AyConj
      (AyRecomputeObligation currentManifest recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_pbmp_conj_left
      (AyConj
        (AyPartitionFailure
          overlap missingPartition digestMismatch frameMismatch)
        (AyConj
          (AyRecomputeObligation currentManifest recompute)
          (AyNoSemanticClaim diagnostic)))
      nextLog
      (ay_pbmp_conj_right previousLog
        (AyConj
          (AyConj
            (AyPartitionFailure
              overlap missingPartition digestMismatch frameMismatch)
            (AyConj
              (AyRecomputeObligation currentManifest recompute)
              (AyNoSemanticClaim diagnostic)))
          nextLog)
        entry))

theorem ay_pbmp_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentManifest : Prop)
    (overlap : Prop) (missingPartition : Prop)
    (digestMismatch : Prop) (frameMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticBatchManifestLogEntry
      previousLog nextLog currentManifest overlap missingPartition
      digestMismatch frameMismatch recompute diagnostic ->
    AyNoSemanticClaim diagnostic := by
  intro entry
  exact ay_pbmp_conj_right
    (AyRecomputeObligation currentManifest recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_pbmp_conj_right
      (AyPartitionFailure overlap missingPartition digestMismatch frameMismatch)
      (AyConj
        (AyRecomputeObligation currentManifest recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_pbmp_conj_left
        (AyConj
          (AyPartitionFailure
            overlap missingPartition digestMismatch frameMismatch)
          (AyConj
            (AyRecomputeObligation currentManifest recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_pbmp_conj_right previousLog
          (AyConj
            (AyConj
              (AyPartitionFailure
                overlap missingPartition digestMismatch frameMismatch)
              (AyConj
                (AyRecomputeObligation currentManifest recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_pbmp_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentManifest : Prop)
    (overlap : Prop) (missingPartition : Prop)
    (digestMismatch : Prop) (frameMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticBatchManifestLogEntry
      previousLog nextLog currentManifest overlap missingPartition
      digestMismatch frameMismatch recompute diagnostic ->
    AyRecomputeObligation currentManifest recompute := by
  intro entry
  exact ay_pbmp_conj_left
    (AyRecomputeObligation currentManifest recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_pbmp_conj_right
      (AyPartitionFailure overlap missingPartition digestMismatch frameMismatch)
      (AyConj
        (AyRecomputeObligation currentManifest recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_pbmp_conj_left
        (AyConj
          (AyPartitionFailure
            overlap missingPartition digestMismatch frameMismatch)
          (AyConj
            (AyRecomputeObligation currentManifest recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_pbmp_conj_right previousLog
          (AyConj
            (AyConj
              (AyPartitionFailure
                overlap missingPartition digestMismatch frameMismatch)
              (AyConj
                (AyRecomputeObligation currentManifest recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_pbmp_failure_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentManifest : Prop)
    (overlap : Prop) (missingPartition : Prop)
    (digestMismatch : Prop) (frameMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticBatchManifestLogEntry
      previousLog nextLog currentManifest overlap missingPartition
      digestMismatch frameMismatch recompute diagnostic ->
    AyConj
      (AyPartitionFailure overlap missingPartition digestMismatch frameMismatch)
      (AyConj
        (AyRecomputeObligation currentManifest recompute)
        (AyNoSemanticClaim diagnostic)) := by
  intro entry
  exact ay_pbmp_conj_intro
    (AyPartitionFailure overlap missingPartition digestMismatch frameMismatch)
    (AyConj
      (AyRecomputeObligation currentManifest recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_pbmp_diagnostic_failure previousLog nextLog currentManifest
      overlap missingPartition digestMismatch frameMismatch recompute
      diagnostic entry)
    (ay_pbmp_conj_intro
      (AyRecomputeObligation currentManifest recompute)
      (AyNoSemanticClaim diagnostic)
      (ay_pbmp_diagnostic_recompute previousLog nextLog currentManifest
        overlap missingPartition digestMismatch frameMismatch recompute
        diagnostic entry)
      (ay_pbmp_diagnostic_no_claim previousLog nextLog currentManifest
        overlap missingPartition digestMismatch frameMismatch recompute
        diagnostic entry))
