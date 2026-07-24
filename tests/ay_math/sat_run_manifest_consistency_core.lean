-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Run-manifest consistency for complete ay SAT-COMP executions. The manifest
-- records preprocessing proof, solver trace digest, branch artifact digest,
-- compressed top outcome, and archive lookup keys.

def AyDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyEquisat (before : Prop) (after : Prop) :=
  AyConj (before -> after) (after -> before)

def AyPreprocessingProof (originalFormula : Prop) (visibleFormula : Prop) :=
  originalFormula -> visibleFormula

def AyVisibleModelReconstruction (visibleModel : Prop) (originalModel : Prop) :=
  visibleModel -> originalModel

def AyUnsatReplayWitness (visibleFormula : Prop) (finalClause : Prop) :=
  finalClause -> visibleFormula -> False

def AySatArchiveEntry (visibleModel : Prop) (originalModel : Prop) :=
  AyConj visibleModel
    (AyVisibleModelReconstruction visibleModel originalModel)

def AyUnsatArchiveEntry
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :=
  AyConj finalClause
    (AyConj
      (AyPreprocessingProof originalFormula visibleFormula)
      (AyUnsatReplayWitness visibleFormula finalClause))

def AyCompressedTopOutcome
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop) :=
  AyDisj
    (AySatArchiveEntry visibleModel originalModel)
    (AyUnsatArchiveEntry originalFormula visibleFormula finalClause)

def AyRunTopOutcome (originalModel : Prop) (originalUnsat : Prop) :=
  AyDisj originalModel originalUnsat

def AySolverTraceDigest (visibleModel : Prop) (finalClause : Prop) :=
  AyDisj visibleModel finalClause

def AyBranchArtifactDigest (visibleModel : Prop) (finalClause : Prop) :=
  AyDisj visibleModel finalClause

def AyArchiveKeys (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop) :=
  AyConj satKey (AyConj unsatKey outcomeKey)

def AyCertificateArchive
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop) :=
  AyConj
    (satKey -> AySatArchiveEntry visibleModel originalModel)
    (AyConj
      (unsatKey ->
        AyUnsatArchiveEntry originalFormula visibleFormula finalClause)
      (outcomeKey ->
        AyCompressedTopOutcome
          originalFormula visibleFormula visibleModel originalModel
          finalClause))

def AyRunManifest
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop) :=
  AyConj
    (AyPreprocessingProof originalFormula visibleFormula)
    (AyConj
      (AySolverTraceDigest visibleModel finalClause)
      (AyConj
        (AyBranchArtifactDigest visibleModel finalClause)
        (AyConj
          (AyCompressedTopOutcome
            originalFormula visibleFormula visibleModel originalModel
            finalClause)
          (AyArchiveKeys satKey unsatKey outcomeKey))))

def AyManifestConsistency
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop) :=
  AyConj
    (AyCompressedTopOutcome
      originalFormula visibleFormula visibleModel originalModel finalClause ->
      AyRunTopOutcome originalModel (Not originalFormula))
    (AyConj
      (AySatArchiveEntry visibleModel originalModel -> originalModel)
      (AyUnsatArchiveEntry originalFormula visibleFormula finalClause ->
        Not originalFormula))

theorem ay_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_conj_left
    (p : Prop) (q : Prop) :
    AyConj p q -> p := by
  intro both
  exact both p
    (fun hp _hq => hp)

theorem ay_disj_left
    (p : Prop) (q : Prop) :
    p -> AyDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_disj_right
    (p : Prop) (q : Prop) :
    q -> AyDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyEquisat before after := by
  intro forward
  intro backward
  exact ay_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_equisat_forward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    AyPreprocessingProof before after := by
  intro equisat
  exact ay_conj_left
    (before -> after)
    (after -> before)
    equisat

theorem ay_sat_entry_visible_model
    (visibleModel : Prop) (originalModel : Prop) :
    AySatArchiveEntry visibleModel originalModel ->
    visibleModel := by
  intro entry
  exact ay_conj_left visibleModel
    (AyVisibleModelReconstruction visibleModel originalModel)
    entry

theorem ay_sat_entry_reconstruction
    (visibleModel : Prop) (originalModel : Prop) :
    AySatArchiveEntry visibleModel originalModel ->
    AyVisibleModelReconstruction visibleModel originalModel := by
  intro entry
  exact entry (AyVisibleModelReconstruction visibleModel originalModel)
    (fun _visible reconstruct => reconstruct)

theorem ay_sat_entry_reconstructs_original_model
    (visibleModel : Prop) (originalModel : Prop) :
    AySatArchiveEntry visibleModel originalModel ->
    originalModel := by
  intro entry
  exact
    (ay_sat_entry_reconstruction visibleModel originalModel entry)
    (ay_sat_entry_visible_model visibleModel originalModel entry)

theorem ay_unsat_entry_final_clause
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyUnsatArchiveEntry originalFormula visibleFormula finalClause ->
    finalClause := by
  intro entry
  exact ay_conj_left finalClause
    (AyConj
      (AyPreprocessingProof originalFormula visibleFormula)
      (AyUnsatReplayWitness visibleFormula finalClause))
    entry

theorem ay_unsat_entry_preprocessing
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyUnsatArchiveEntry originalFormula visibleFormula finalClause ->
    AyPreprocessingProof originalFormula visibleFormula := by
  intro entry
  exact entry (AyPreprocessingProof originalFormula visibleFormula)
    (fun _final maps =>
      maps (AyPreprocessingProof originalFormula visibleFormula)
        (fun preprocess _replay => preprocess))

theorem ay_unsat_entry_replay
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyUnsatArchiveEntry originalFormula visibleFormula finalClause ->
    AyUnsatReplayWitness visibleFormula finalClause := by
  intro entry
  exact entry (AyUnsatReplayWitness visibleFormula finalClause)
    (fun _final maps =>
      maps (AyUnsatReplayWitness visibleFormula finalClause)
        (fun _preprocess replay => replay))

theorem ay_unsat_entry_reconstructs_original_unsat
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyUnsatArchiveEntry originalFormula visibleFormula finalClause ->
    Not originalFormula := by
  intro entry
  intro horiginal
  exact
    (ay_unsat_entry_replay originalFormula visibleFormula finalClause entry)
    (ay_unsat_entry_final_clause
      originalFormula visibleFormula finalClause entry)
    ((ay_unsat_entry_preprocessing
      originalFormula visibleFormula finalClause entry)
      horiginal)

theorem ay_manifest_lookup_preprocessing
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop) :
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey ->
    AyPreprocessingProof originalFormula visibleFormula := by
  intro manifest
  exact manifest (AyPreprocessingProof originalFormula visibleFormula)
    (fun preprocess _tail => preprocess)

theorem ay_manifest_lookup_solver_trace
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop) :
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey ->
    AySolverTraceDigest visibleModel finalClause := by
  intro manifest
  exact manifest (AySolverTraceDigest visibleModel finalClause)
    (fun _preprocess tail =>
      tail (AySolverTraceDigest visibleModel finalClause)
        (fun solver_digest _tail2 => solver_digest))

theorem ay_manifest_lookup_branch_digest
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop) :
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey ->
    AyBranchArtifactDigest visibleModel finalClause := by
  intro manifest
  exact manifest (AyBranchArtifactDigest visibleModel finalClause)
    (fun _preprocess tail =>
      tail (AyBranchArtifactDigest visibleModel finalClause)
        (fun _solver_digest tail2 =>
          tail2 (AyBranchArtifactDigest visibleModel finalClause)
            (fun branch_digest _tail3 => branch_digest)))

theorem ay_manifest_lookup_outcome
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop) :
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey ->
    AyCompressedTopOutcome
      originalFormula visibleFormula visibleModel originalModel finalClause := by
  intro manifest
  exact manifest
    (AyCompressedTopOutcome
      originalFormula visibleFormula visibleModel originalModel finalClause)
    (fun _preprocess tail =>
      tail
        (AyCompressedTopOutcome
          originalFormula visibleFormula visibleModel originalModel
          finalClause)
        (fun _solver_digest tail2 =>
          tail2
            (AyCompressedTopOutcome
              originalFormula visibleFormula visibleModel originalModel
              finalClause)
            (fun _branch_digest tail3 =>
              tail3
                (AyCompressedTopOutcome
                  originalFormula visibleFormula visibleModel originalModel
                  finalClause)
                (fun outcome _keys => outcome))))

theorem ay_manifest_lookup_keys
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop) :
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey ->
    AyArchiveKeys satKey unsatKey outcomeKey := by
  intro manifest
  exact manifest (AyArchiveKeys satKey unsatKey outcomeKey)
    (fun _preprocess tail =>
      tail (AyArchiveKeys satKey unsatKey outcomeKey)
        (fun _solver_digest tail2 =>
          tail2 (AyArchiveKeys satKey unsatKey outcomeKey)
            (fun _branch_digest tail3 =>
              tail3 (AyArchiveKeys satKey unsatKey outcomeKey)
                (fun _outcome keys => keys))))

theorem ay_manifest_sat_key
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop) :
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey ->
    satKey := by
  intro manifest
  exact ay_conj_left satKey (AyConj unsatKey outcomeKey)
    (ay_manifest_lookup_keys
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey manifest)

theorem ay_manifest_unsat_key
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop) :
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey ->
    unsatKey := by
  intro manifest
  exact
    (ay_manifest_lookup_keys
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey manifest)
    unsatKey
    (fun _sat_key tail =>
      tail unsatKey
        (fun hunsat_key _outcome_key => hunsat_key))

theorem ay_manifest_outcome_key
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop) :
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey ->
    outcomeKey := by
  intro manifest
  exact
    (ay_manifest_lookup_keys
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey manifest)
    outcomeKey
    (fun _sat_key tail =>
      tail outcomeKey
        (fun _unsat_key houtcome_key => houtcome_key))

theorem ay_archive_lookup_sat_entry
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop) :
    AyCertificateArchive
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey ->
    satKey ->
    AySatArchiveEntry visibleModel originalModel := by
  intro archive
  exact archive
    (satKey -> AySatArchiveEntry visibleModel originalModel)
    (fun sat_lookup _tail => sat_lookup)

theorem ay_archive_lookup_unsat_entry
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop) :
    AyCertificateArchive
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey ->
    unsatKey ->
    AyUnsatArchiveEntry originalFormula visibleFormula finalClause := by
  intro archive
  exact archive
    (unsatKey ->
      AyUnsatArchiveEntry originalFormula visibleFormula finalClause)
    (fun _sat_lookup tail =>
      tail
        (unsatKey ->
          AyUnsatArchiveEntry originalFormula visibleFormula finalClause)
        (fun unsat_lookup _outcome_lookup => unsat_lookup))

theorem ay_archive_lookup_outcome
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop) :
    AyCertificateArchive
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey ->
    outcomeKey ->
    AyCompressedTopOutcome
      originalFormula visibleFormula visibleModel originalModel finalClause := by
  intro archive
  exact archive
    (outcomeKey ->
      AyCompressedTopOutcome
        originalFormula visibleFormula visibleModel originalModel finalClause)
    (fun _sat_lookup tail =>
      tail
        (outcomeKey ->
          AyCompressedTopOutcome
            originalFormula visibleFormula visibleModel originalModel
            finalClause)
        (fun _unsat_lookup outcome_lookup => outcome_lookup))

theorem ay_public_checker_retrieves_sat_entry
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop) :
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey ->
    AyCertificateArchive
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey ->
    AySatArchiveEntry visibleModel originalModel := by
  intro manifest
  intro archive
  exact ay_archive_lookup_sat_entry
    originalFormula visibleFormula visibleModel originalModel finalClause
    satKey unsatKey outcomeKey archive
    (ay_manifest_sat_key
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey manifest)

theorem ay_public_checker_retrieves_unsat_entry
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop) :
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey ->
    AyCertificateArchive
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey ->
    AyUnsatArchiveEntry originalFormula visibleFormula finalClause := by
  intro manifest
  intro archive
  exact ay_archive_lookup_unsat_entry
    originalFormula visibleFormula visibleModel originalModel finalClause
    satKey unsatKey outcomeKey archive
    (ay_manifest_unsat_key
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey manifest)

theorem ay_public_checker_retrieves_archive_outcome
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop) :
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey ->
    AyCertificateArchive
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey ->
    AyCompressedTopOutcome
      originalFormula visibleFormula visibleModel originalModel finalClause := by
  intro manifest
  intro archive
  exact ay_archive_lookup_outcome
    originalFormula visibleFormula visibleModel originalModel finalClause
    satKey unsatKey outcomeKey archive
    (ay_manifest_outcome_key
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey manifest)

theorem ay_outcome_to_top_outcome
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop) :
    AyCompressedTopOutcome
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyRunTopOutcome originalModel (Not originalFormula) := by
  intro outcome
  exact outcome (AyRunTopOutcome originalModel (Not originalFormula))
    (fun sat_entry =>
      ay_disj_left originalModel (Not originalFormula)
        (ay_sat_entry_reconstructs_original_model
          visibleModel originalModel sat_entry))
    (fun unsat_entry =>
      ay_disj_right originalModel (Not originalFormula)
        (ay_unsat_entry_reconstructs_original_unsat
          originalFormula visibleFormula finalClause unsat_entry))

theorem ay_manifest_consistency_intro
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop) :
    AyManifestConsistency
      originalFormula visibleFormula visibleModel originalModel finalClause := by
  exact ay_conj_intro
    (AyCompressedTopOutcome
      originalFormula visibleFormula visibleModel originalModel finalClause ->
      AyRunTopOutcome originalModel (Not originalFormula))
    (AyConj
      (AySatArchiveEntry visibleModel originalModel -> originalModel)
      (AyUnsatArchiveEntry originalFormula visibleFormula finalClause ->
        Not originalFormula))
    (ay_outcome_to_top_outcome
      originalFormula visibleFormula visibleModel originalModel finalClause)
    (ay_conj_intro
      (AySatArchiveEntry visibleModel originalModel -> originalModel)
      (AyUnsatArchiveEntry originalFormula visibleFormula finalClause ->
        Not originalFormula)
      (ay_sat_entry_reconstructs_original_model
        visibleModel originalModel)
      (ay_unsat_entry_reconstructs_original_unsat
        originalFormula visibleFormula finalClause))

theorem ay_consistency_sat_sound_lookup
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop) :
    AyManifestConsistency
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AySatArchiveEntry visibleModel originalModel ->
    originalModel := by
  intro consistency
  exact consistency
    (AySatArchiveEntry visibleModel originalModel -> originalModel)
    (fun _top_lookup branch_tail =>
      branch_tail
        (AySatArchiveEntry visibleModel originalModel -> originalModel)
        (fun sat_sound _unsat_sound => sat_sound))

theorem ay_consistency_unsat_sound_lookup
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop) :
    AyManifestConsistency
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyUnsatArchiveEntry originalFormula visibleFormula finalClause ->
    Not originalFormula := by
  intro consistency
  exact consistency
    (AyUnsatArchiveEntry originalFormula visibleFormula finalClause ->
      Not originalFormula)
    (fun _top_lookup branch_tail =>
      branch_tail
        (AyUnsatArchiveEntry originalFormula visibleFormula finalClause ->
          Not originalFormula)
        (fun _sat_sound unsat_sound => unsat_sound))

theorem ay_consistency_top_sound_lookup
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop) :
    AyManifestConsistency
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyCompressedTopOutcome
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyRunTopOutcome originalModel (Not originalFormula) := by
  intro consistency
  exact consistency
    (AyCompressedTopOutcome
      originalFormula visibleFormula visibleModel originalModel finalClause ->
      AyRunTopOutcome originalModel (Not originalFormula))
    (fun top_sound _branch_tail => top_sound)

theorem ay_public_checker_sat_soundness
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop) :
    AyManifestConsistency
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey ->
    AyCertificateArchive
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey ->
    originalModel := by
  intro consistency
  intro manifest
  intro archive
  exact ay_consistency_sat_sound_lookup
    originalFormula visibleFormula visibleModel originalModel finalClause
    consistency
    (ay_public_checker_retrieves_sat_entry
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey manifest archive)

theorem ay_public_checker_unsat_soundness
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop) :
    AyManifestConsistency
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey ->
    AyCertificateArchive
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey ->
    Not originalFormula := by
  intro consistency
  intro manifest
  intro archive
  exact ay_consistency_unsat_sound_lookup
    originalFormula visibleFormula visibleModel originalModel finalClause
    consistency
    (ay_public_checker_retrieves_unsat_entry
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey manifest archive)

theorem ay_manifest_outcome_to_top
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop) :
    AyManifestConsistency
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey ->
    AyRunTopOutcome originalModel (Not originalFormula) := by
  intro consistency
  intro manifest
  exact ay_consistency_top_sound_lookup
    originalFormula visibleFormula visibleModel originalModel finalClause
    consistency
    (ay_manifest_lookup_outcome
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey manifest)

theorem ay_archive_outcome_to_top
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop) :
    AyManifestConsistency
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey ->
    AyCertificateArchive
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey ->
    AyRunTopOutcome originalModel (Not originalFormula) := by
  intro consistency
  intro manifest
  intro archive
  exact ay_consistency_top_sound_lookup
    originalFormula visibleFormula visibleModel originalModel finalClause
    consistency
    (ay_public_checker_retrieves_archive_outcome
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey manifest archive)

theorem ay_manifest_outcome_agrees_with_archive_outcome
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop) :
    AyManifestConsistency
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey ->
    AyCertificateArchive
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey ->
    AyConj
      (AyRunTopOutcome originalModel (Not originalFormula))
      (AyRunTopOutcome originalModel (Not originalFormula)) := by
  intro consistency
  intro manifest
  intro archive
  exact ay_conj_intro
    (AyRunTopOutcome originalModel (Not originalFormula))
    (AyRunTopOutcome originalModel (Not originalFormula))
    (ay_manifest_outcome_to_top
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey consistency manifest)
    (ay_archive_outcome_to_top
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey consistency manifest archive)

theorem ay_public_checker_exact_artifacts
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop) :
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey ->
    AyCertificateArchive
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey ->
    AyConj
      (AySatArchiveEntry visibleModel originalModel)
      (AyUnsatArchiveEntry originalFormula visibleFormula finalClause) := by
  intro manifest
  intro archive
  exact ay_conj_intro
    (AySatArchiveEntry visibleModel originalModel)
    (AyUnsatArchiveEntry originalFormula visibleFormula finalClause)
    (ay_public_checker_retrieves_sat_entry
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey manifest archive)
    (ay_public_checker_retrieves_unsat_entry
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey manifest archive)
