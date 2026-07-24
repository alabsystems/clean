-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Indexable preprocessing artifacts for SAT-COMP certificate replay. The
-- propositions stand for CNF satisfiability, model payloads, replay clauses,
-- and lookup results from a preprocessing artifact table.

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

def AyPreprocessArtifact
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop) :=
  AyConj
    (AyEquisat originalCnf internalCnf)
    (AyEquisat internalCnf visibleCnf)

def AyArtifactIndex (artifactId : Prop)
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop) :=
  artifactId -> AyPreprocessArtifact originalCnf internalCnf visibleCnf

def AyVisibleSatArtifact
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop) :=
  AyConj originalCnf
    (AyConj visibleCnf
      (AyConj visibleModel (visibleModel -> originalModel)))

def AyUnsatReplayArtifact
    (originalCnf : Prop) (visibleCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  AyConj originalCnf
    (AyConj visibleCnf (AyConj certificate conflict))

def AyIndexedOutcome
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  AyDisj
    (AyVisibleSatArtifact
      originalCnf visibleCnf visibleModel originalModel)
    (AyUnsatReplayArtifact
      originalCnf visibleCnf certificate conflict)

theorem ay_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_conj_left
    (left : Prop) (right : Prop) :
    AyConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_conj_right
    (left : Prop) (right : Prop) :
    AyConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_disj_left
    (left : Prop) (right : Prop) :
    left -> AyDisj left right := by
  intro hleft
  intro result
  intro left_case
  intro _right_case
  exact left_case hleft

theorem ay_disj_right
    (left : Prop) (right : Prop) :
    right -> AyDisj left right := by
  intro hright
  intro result
  intro _left_case
  intro right_case
  exact right_case hright

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
    before ->
    after := by
  intro eq
  exact ay_conj_left (before -> after) (after -> before) eq

theorem ay_equisat_backward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    after ->
    before := by
  intro eq
  exact ay_conj_right (before -> after) (after -> before) eq

theorem ay_equisat_trans
    (first : Prop) (middle : Prop) (last : Prop) :
    AyEquisat first middle ->
    AyEquisat middle last ->
    AyEquisat first last := by
  intro first_middle
  intro middle_last
  exact ay_equisat_intro first last
    (fun hfirst =>
      ay_equisat_forward middle last middle_last
        (ay_equisat_forward first middle first_middle hfirst))
    (fun hlast =>
      ay_equisat_backward first middle first_middle
        (ay_equisat_backward middle last middle_last hlast))

theorem ay_sat_cnf
    (cnf : Prop) (model : Prop) :
    AySat cnf model ->
    cnf := by
  intro sat
  exact ay_conj_left cnf model sat

theorem ay_sat_model
    (cnf : Prop) (model : Prop) :
    AySat cnf model ->
    model := by
  intro sat
  exact ay_conj_right cnf model sat

theorem ay_index_lookup
    (artifactId : Prop)
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop) :
    AyArtifactIndex artifactId originalCnf internalCnf visibleCnf ->
    artifactId ->
    AyPreprocessArtifact originalCnf internalCnf visibleCnf := by
  intro index
  intro hid
  exact index hid

theorem ay_artifact_original_internal
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop) :
    AyPreprocessArtifact originalCnf internalCnf visibleCnf ->
    AyEquisat originalCnf internalCnf := by
  intro artifact
  exact ay_conj_left
    (AyEquisat originalCnf internalCnf)
    (AyEquisat internalCnf visibleCnf)
    artifact

theorem ay_artifact_internal_visible
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop) :
    AyPreprocessArtifact originalCnf internalCnf visibleCnf ->
    AyEquisat internalCnf visibleCnf := by
  intro artifact
  exact ay_conj_right
    (AyEquisat originalCnf internalCnf)
    (AyEquisat internalCnf visibleCnf)
    artifact

theorem ay_artifact_original_visible
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop) :
    AyPreprocessArtifact originalCnf internalCnf visibleCnf ->
    AyEquisat originalCnf visibleCnf := by
  intro artifact
  exact ay_equisat_trans originalCnf internalCnf visibleCnf
    (ay_artifact_original_internal
      originalCnf internalCnf visibleCnf artifact)
    (ay_artifact_internal_visible
      originalCnf internalCnf visibleCnf artifact)

theorem ay_lookup_original_to_internal
    (artifactId : Prop)
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop) :
    AyArtifactIndex artifactId originalCnf internalCnf visibleCnf ->
    artifactId ->
    originalCnf ->
    internalCnf := by
  intro index
  intro hid
  exact ay_equisat_forward originalCnf internalCnf
    (ay_artifact_original_internal originalCnf internalCnf visibleCnf
      (ay_index_lookup artifactId originalCnf internalCnf visibleCnf
        index hid))

theorem ay_lookup_internal_to_original
    (artifactId : Prop)
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop) :
    AyArtifactIndex artifactId originalCnf internalCnf visibleCnf ->
    artifactId ->
    internalCnf ->
    originalCnf := by
  intro index
  intro hid
  exact ay_equisat_backward originalCnf internalCnf
    (ay_artifact_original_internal originalCnf internalCnf visibleCnf
      (ay_index_lookup artifactId originalCnf internalCnf visibleCnf
        index hid))

theorem ay_lookup_internal_to_visible
    (artifactId : Prop)
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop) :
    AyArtifactIndex artifactId originalCnf internalCnf visibleCnf ->
    artifactId ->
    internalCnf ->
    visibleCnf := by
  intro index
  intro hid
  exact ay_equisat_forward internalCnf visibleCnf
    (ay_artifact_internal_visible originalCnf internalCnf visibleCnf
      (ay_index_lookup artifactId originalCnf internalCnf visibleCnf
        index hid))

theorem ay_lookup_visible_to_internal
    (artifactId : Prop)
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop) :
    AyArtifactIndex artifactId originalCnf internalCnf visibleCnf ->
    artifactId ->
    visibleCnf ->
    internalCnf := by
  intro index
  intro hid
  exact ay_equisat_backward internalCnf visibleCnf
    (ay_artifact_internal_visible originalCnf internalCnf visibleCnf
      (ay_index_lookup artifactId originalCnf internalCnf visibleCnf
        index hid))

theorem ay_lookup_original_to_visible
    (artifactId : Prop)
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop) :
    AyArtifactIndex artifactId originalCnf internalCnf visibleCnf ->
    artifactId ->
    originalCnf ->
    visibleCnf := by
  intro index
  intro hid
  intro horiginal
  exact ay_lookup_internal_to_visible
    artifactId originalCnf internalCnf visibleCnf index hid
    (ay_lookup_original_to_internal
      artifactId originalCnf internalCnf visibleCnf index hid horiginal)

theorem ay_lookup_visible_to_original
    (artifactId : Prop)
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop) :
    AyArtifactIndex artifactId originalCnf internalCnf visibleCnf ->
    artifactId ->
    visibleCnf ->
    originalCnf := by
  intro index
  intro hid
  intro hvisible
  exact ay_lookup_internal_to_original
    artifactId originalCnf internalCnf visibleCnf index hid
    (ay_lookup_visible_to_internal
      artifactId originalCnf internalCnf visibleCnf index hid hvisible)

theorem ay_indexed_internal_sat_to_visible_sat
    (artifactId : Prop)
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop)
    (model : Prop) :
    AyArtifactIndex artifactId originalCnf internalCnf visibleCnf ->
    artifactId ->
    AySat internalCnf model ->
    AySat visibleCnf model := by
  intro index
  intro hid
  intro sat
  exact ay_conj_intro visibleCnf model
    (ay_lookup_internal_to_visible
      artifactId originalCnf internalCnf visibleCnf index hid
      (ay_sat_cnf internalCnf model sat))
    (ay_sat_model internalCnf model sat)

theorem ay_indexed_visible_sat_to_internal_sat
    (artifactId : Prop)
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop)
    (model : Prop) :
    AyArtifactIndex artifactId originalCnf internalCnf visibleCnf ->
    artifactId ->
    AySat visibleCnf model ->
    AySat internalCnf model := by
  intro index
  intro hid
  intro sat
  exact ay_conj_intro internalCnf model
    (ay_lookup_visible_to_internal
      artifactId originalCnf internalCnf visibleCnf index hid
      (ay_sat_cnf visibleCnf model sat))
    (ay_sat_model visibleCnf model sat)

theorem ay_indexed_internal_sat_to_original_visible_artifact
    (artifactId : Prop)
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop) :
    AyArtifactIndex artifactId originalCnf internalCnf visibleCnf ->
    artifactId ->
    AySat internalCnf visibleModel ->
    (visibleModel -> originalModel) ->
    AyVisibleSatArtifact
      originalCnf visibleCnf visibleModel originalModel := by
  intro index
  intro hid
  intro sat
  intro reconstruct
  exact ay_conj_intro originalCnf
    (AyConj visibleCnf
      (AyConj visibleModel (visibleModel -> originalModel)))
    (ay_lookup_internal_to_original
      artifactId originalCnf internalCnf visibleCnf index hid
      (ay_sat_cnf internalCnf visibleModel sat))
    (ay_conj_intro visibleCnf
      (AyConj visibleModel (visibleModel -> originalModel))
      (ay_lookup_internal_to_visible
        artifactId originalCnf internalCnf visibleCnf index hid
        (ay_sat_cnf internalCnf visibleModel sat))
      (ay_conj_intro visibleModel (visibleModel -> originalModel)
        (ay_sat_model internalCnf visibleModel sat)
        reconstruct))

theorem ay_visible_sat_artifact_original
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop) :
    AyVisibleSatArtifact
      originalCnf visibleCnf visibleModel originalModel ->
    originalCnf := by
  intro artifact
  exact ay_conj_left originalCnf
    (AyConj visibleCnf
      (AyConj visibleModel (visibleModel -> originalModel)))
    artifact

theorem ay_visible_sat_artifact_model
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop) :
    AyVisibleSatArtifact
      originalCnf visibleCnf visibleModel originalModel ->
    originalModel := by
  intro artifact
  exact ay_conj_right visibleModel (visibleModel -> originalModel)
    (ay_conj_right visibleCnf
      (AyConj visibleModel (visibleModel -> originalModel))
      (ay_conj_right originalCnf
        (AyConj visibleCnf
          (AyConj visibleModel (visibleModel -> originalModel)))
        artifact))
    (ay_conj_left visibleModel (visibleModel -> originalModel)
      (ay_conj_right visibleCnf
        (AyConj visibleModel (visibleModel -> originalModel))
        (ay_conj_right originalCnf
          (AyConj visibleCnf
            (AyConj visibleModel (visibleModel -> originalModel)))
          artifact)))

theorem ay_indexed_sat_model_transport
    (artifactId : Prop)
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop) :
    AyArtifactIndex artifactId originalCnf internalCnf visibleCnf ->
    artifactId ->
    AySat internalCnf visibleModel ->
    (visibleModel -> originalModel) ->
    AySat originalCnf originalModel := by
  intro index
  intro hid
  intro sat
  intro reconstruct
  exact ay_conj_intro originalCnf originalModel
    (ay_lookup_internal_to_original
      artifactId originalCnf internalCnf visibleCnf index hid
      (ay_sat_cnf internalCnf visibleModel sat))
    (reconstruct
      (ay_sat_model internalCnf visibleModel sat))

theorem ay_indexed_original_sat_to_internal_sat
    (artifactId : Prop)
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop)
    (model : Prop) :
    AyArtifactIndex artifactId originalCnf internalCnf visibleCnf ->
    artifactId ->
    AySat originalCnf model ->
    AySat internalCnf model := by
  intro index
  intro hid
  intro sat
  exact ay_conj_intro internalCnf model
    (ay_lookup_original_to_internal
      artifactId originalCnf internalCnf visibleCnf index hid
      (ay_sat_cnf originalCnf model sat))
    (ay_sat_model originalCnf model sat)

theorem ay_indexed_unsat_replay_transport
    (artifactId : Prop)
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyArtifactIndex artifactId originalCnf internalCnf visibleCnf ->
    artifactId ->
    AyReplay internalCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro index
  intro hid
  intro replay
  intro hcertificate
  intro horiginal
  exact replay
    (ay_lookup_original_to_internal
      artifactId originalCnf internalCnf visibleCnf index hid horiginal)
    hcertificate

theorem ay_indexed_unsat_visible_replay_transport
    (artifactId : Prop)
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyArtifactIndex artifactId originalCnf internalCnf visibleCnf ->
    artifactId ->
    AyReplay visibleCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro index
  intro hid
  intro replay
  intro hcertificate
  intro horiginal
  exact replay
    (ay_lookup_original_to_visible
      artifactId originalCnf internalCnf visibleCnf index hid horiginal)
    hcertificate

theorem ay_indexed_unsat_replay_artifact
    (artifactId : Prop)
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyArtifactIndex artifactId originalCnf internalCnf visibleCnf ->
    artifactId ->
    AyReplay internalCnf certificate conflict ->
    certificate ->
    originalCnf ->
    AyUnsatReplayArtifact
      originalCnf visibleCnf certificate conflict := by
  intro index
  intro hid
  intro replay
  intro hcertificate
  intro horiginal
  exact ay_conj_intro originalCnf
    (AyConj visibleCnf (AyConj certificate conflict))
    horiginal
    (ay_conj_intro visibleCnf (AyConj certificate conflict)
      (ay_lookup_original_to_visible
        artifactId originalCnf internalCnf visibleCnf index hid horiginal)
      (ay_conj_intro certificate conflict
        hcertificate
        (ay_indexed_unsat_replay_transport
          artifactId originalCnf internalCnf visibleCnf
          certificate conflict index hid replay hcertificate horiginal)))

theorem ay_unsat_replay_artifact_conflict
    (originalCnf : Prop) (visibleCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyUnsatReplayArtifact originalCnf visibleCnf certificate conflict ->
    conflict := by
  intro artifact
  exact ay_conj_right certificate conflict
    (ay_conj_right visibleCnf (AyConj certificate conflict)
      (ay_conj_right originalCnf
        (AyConj visibleCnf (AyConj certificate conflict))
        artifact))

theorem ay_indexed_outcome_sat
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyVisibleSatArtifact
      originalCnf visibleCnf visibleModel originalModel ->
    AyIndexedOutcome
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict := by
  exact ay_disj_left
    (AyVisibleSatArtifact
      originalCnf visibleCnf visibleModel originalModel)
    (AyUnsatReplayArtifact originalCnf visibleCnf certificate conflict)

theorem ay_indexed_outcome_unsat
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyUnsatReplayArtifact originalCnf visibleCnf certificate conflict ->
    AyIndexedOutcome
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict := by
  exact ay_disj_right
    (AyVisibleSatArtifact
      originalCnf visibleCnf visibleModel originalModel)
    (AyUnsatReplayArtifact originalCnf visibleCnf certificate conflict)

theorem ay_lookup_sat_outcome
    (artifactId : Prop)
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyArtifactIndex artifactId originalCnf internalCnf visibleCnf ->
    artifactId ->
    AySat internalCnf visibleModel ->
    (visibleModel -> originalModel) ->
    AyIndexedOutcome
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict := by
  intro index
  intro hid
  intro sat
  intro reconstruct
  exact ay_indexed_outcome_sat
    originalCnf visibleCnf visibleModel originalModel
    certificate conflict
    (ay_indexed_internal_sat_to_original_visible_artifact
      artifactId originalCnf internalCnf visibleCnf
      visibleModel originalModel index hid sat reconstruct)

theorem ay_lookup_unsat_outcome
    (artifactId : Prop)
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyArtifactIndex artifactId originalCnf internalCnf visibleCnf ->
    artifactId ->
    AyReplay internalCnf certificate conflict ->
    certificate ->
    originalCnf ->
    AyIndexedOutcome
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict := by
  intro index
  intro hid
  intro replay
  intro hcertificate
  intro horiginal
  exact ay_indexed_outcome_unsat
    originalCnf visibleCnf visibleModel originalModel
    certificate conflict
    (ay_indexed_unsat_replay_artifact
      artifactId originalCnf internalCnf visibleCnf
      certificate conflict index hid replay hcertificate horiginal)
