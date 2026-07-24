-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Certificate archive consistency for SAT-COMP runs. Archive entries are
-- SAT-specific boundary artifacts: preprocessing maps, visible SAT models,
-- UNSAT replay witnesses, compressed outcomes, and run-level top outcomes.

def AyDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyEquisat (before : Prop) (after : Prop) :=
  AyConj (before -> after) (after -> before)

def AyPreprocessingMap (originalFormula : Prop) (visibleFormula : Prop) :=
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
      (AyPreprocessingMap originalFormula visibleFormula)
      (AyUnsatReplayWitness visibleFormula finalClause))

def AyCompressedOutcome
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :=
  AyDisj
    (AySatArchiveEntry visibleModel originalModel)
    (AyUnsatArchiveEntry originalFormula visibleFormula finalClause)

def AyRunTopOutcome (originalModel : Prop) (originalUnsat : Prop) :=
  AyDisj originalModel originalUnsat

def AyCertificateArchive
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :=
  AyConj
    (AyCompressedOutcome
      originalFormula visibleFormula visibleModel originalModel finalClause)
    (AyConj
      (AySatArchiveEntry visibleModel originalModel)
      (AyUnsatArchiveEntry originalFormula visibleFormula finalClause))

def AyArchiveConsistency
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :=
  AyConj
    (AyCompressedOutcome
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
    AyPreprocessingMap before after := by
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
      (AyPreprocessingMap originalFormula visibleFormula)
      (AyUnsatReplayWitness visibleFormula finalClause))
    entry

theorem ay_unsat_entry_preprocessing
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyUnsatArchiveEntry originalFormula visibleFormula finalClause ->
    AyPreprocessingMap originalFormula visibleFormula := by
  intro entry
  exact entry (AyPreprocessingMap originalFormula visibleFormula)
    (fun _final maps =>
      maps (AyPreprocessingMap originalFormula visibleFormula)
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

theorem ay_archive_lookup_outcome
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyCertificateArchive
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyCompressedOutcome
      originalFormula visibleFormula visibleModel originalModel finalClause := by
  intro archive
  exact archive
    (AyCompressedOutcome
      originalFormula visibleFormula visibleModel originalModel finalClause)
    (fun outcome _tail => outcome)

theorem ay_archive_lookup_sat_entry
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyCertificateArchive
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AySatArchiveEntry visibleModel originalModel := by
  intro archive
  exact archive (AySatArchiveEntry visibleModel originalModel)
    (fun _outcome tail =>
      tail (AySatArchiveEntry visibleModel originalModel)
        (fun sat_entry _unsat_entry => sat_entry))

theorem ay_archive_lookup_unsat_entry
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyCertificateArchive
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyUnsatArchiveEntry originalFormula visibleFormula finalClause := by
  intro archive
  exact archive (AyUnsatArchiveEntry originalFormula visibleFormula finalClause)
    (fun _outcome tail =>
      tail (AyUnsatArchiveEntry originalFormula visibleFormula finalClause)
        (fun _sat_entry unsat_entry => unsat_entry))

theorem ay_outcome_to_top_outcome
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyCompressedOutcome
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

theorem ay_archive_consistency_intro
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyArchiveConsistency
      originalFormula visibleFormula visibleModel originalModel finalClause := by
  exact ay_conj_intro
    (AyCompressedOutcome
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

theorem ay_consistency_top_lookup
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyArchiveConsistency
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyCompressedOutcome
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyRunTopOutcome originalModel (Not originalFormula) := by
  intro consistency
  exact consistency
    (AyCompressedOutcome
      originalFormula visibleFormula visibleModel originalModel finalClause ->
      AyRunTopOutcome originalModel (Not originalFormula))
    (fun top_lookup _branch_tail => top_lookup)

theorem ay_consistency_sat_lookup_reconstructs
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyArchiveConsistency
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AySatArchiveEntry visibleModel originalModel ->
    originalModel := by
  intro consistency
  exact consistency
    (AySatArchiveEntry visibleModel originalModel -> originalModel)
    (fun _top_lookup branch_tail =>
      branch_tail
        (AySatArchiveEntry visibleModel originalModel -> originalModel)
        (fun sat_lookup _unsat_lookup => sat_lookup))

theorem ay_consistency_unsat_lookup_reconstructs
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyArchiveConsistency
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
        (fun _sat_lookup unsat_lookup => unsat_lookup))

theorem ay_archive_sat_entry_reconstructs
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyArchiveConsistency
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyCertificateArchive
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    originalModel := by
  intro consistency
  intro archive
  exact ay_consistency_sat_lookup_reconstructs
    originalFormula visibleFormula visibleModel originalModel finalClause
    consistency
    (ay_archive_lookup_sat_entry
      originalFormula visibleFormula visibleModel originalModel finalClause
      archive)

theorem ay_archive_unsat_entry_reconstructs
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyArchiveConsistency
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyCertificateArchive
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    Not originalFormula := by
  intro consistency
  intro archive
  exact ay_consistency_unsat_lookup_reconstructs
    originalFormula visibleFormula visibleModel originalModel finalClause
    consistency
    (ay_archive_lookup_unsat_entry
      originalFormula visibleFormula visibleModel originalModel finalClause
      archive)

theorem ay_archive_top_lookup_agrees_with_artifacts
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyArchiveConsistency
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyCertificateArchive
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyRunTopOutcome originalModel (Not originalFormula) := by
  intro consistency
  intro archive
  exact ay_consistency_top_lookup
    originalFormula visibleFormula visibleModel originalModel finalClause
    consistency
    (ay_archive_lookup_outcome
      originalFormula visibleFormula visibleModel originalModel finalClause
      archive)

theorem ay_archive_top_lookup_sat_branch_agrees
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyCertificateArchive
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyRunTopOutcome originalModel (Not originalFormula) := by
  intro archive
  exact ay_disj_left originalModel (Not originalFormula)
    (ay_sat_entry_reconstructs_original_model
      visibleModel originalModel
      (ay_archive_lookup_sat_entry
        originalFormula visibleFormula visibleModel originalModel finalClause
        archive))

theorem ay_archive_top_lookup_unsat_branch_agrees
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyCertificateArchive
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyRunTopOutcome originalModel (Not originalFormula) := by
  intro archive
  exact ay_disj_right originalModel (Not originalFormula)
    (ay_unsat_entry_reconstructs_original_unsat
      originalFormula visibleFormula finalClause
      (ay_archive_lookup_unsat_entry
        originalFormula visibleFormula visibleModel originalModel finalClause
        archive))
