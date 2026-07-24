-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Compact checked package combining preprocessing roundtrip witnesses with
-- compressed SAT/UNSAT outcome certificates.

def AyConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyEquisat (before : Prop) (after : Prop) :=
  AyConj (before -> after) (after -> before)

def AySat (formula : Prop) (model : Prop) :=
  AyConj formula model

def AyReplay (formula : Prop) (certificate : Prop) (conflict : Prop) :=
  formula -> certificate -> conflict

def AyPreprocessMap (original : Prop) (preprocessed : Prop) (visible : Prop) :=
  AyConj (AyEquisat original preprocessed) (AyEquisat preprocessed visible)

def AyCompressedSat (visibleModel : Prop) (originalModel : Prop) :=
  AyConj visibleModel (visibleModel -> originalModel)

def AyCompressedUnsat
    (original : Prop) (visible : Prop) (finalClause : Prop) :=
  AyConj finalClause (AyConj (original -> visible) (visible -> finalClause -> False))

def AyCompressedOutcome
    (original : Prop) (visible : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop) :=
  AyDisj
    (AyCompressedSat visibleModel originalModel)
    (AyCompressedUnsat original visible finalClause)

def AyRoundtrip (source : Prop) (target : Prop) :=
  AyConj (source -> target) (target -> source)

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

theorem ay_preprocess_original_step
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyPreprocessMap original preprocessed visible ->
    AyEquisat original preprocessed := by
  intro prep
  exact ay_conj_left
    (AyEquisat original preprocessed)
    (AyEquisat preprocessed visible)
    prep

theorem ay_preprocess_visible_step
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyPreprocessMap original preprocessed visible ->
    AyEquisat preprocessed visible := by
  intro prep
  exact ay_conj_right
    (AyEquisat original preprocessed)
    (AyEquisat preprocessed visible)
    prep

theorem ay_original_to_preprocessed
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyPreprocessMap original preprocessed visible ->
    original ->
    preprocessed := by
  intro prep
  exact ay_equisat_forward original preprocessed
    (ay_preprocess_original_step original preprocessed visible prep)

theorem ay_preprocessed_to_original
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyPreprocessMap original preprocessed visible ->
    preprocessed ->
    original := by
  intro prep
  exact ay_equisat_backward original preprocessed
    (ay_preprocess_original_step original preprocessed visible prep)

theorem ay_preprocessed_to_visible
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyPreprocessMap original preprocessed visible ->
    preprocessed ->
    visible := by
  intro prep
  exact ay_equisat_forward preprocessed visible
    (ay_preprocess_visible_step original preprocessed visible prep)

theorem ay_visible_to_preprocessed
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyPreprocessMap original preprocessed visible ->
    visible ->
    preprocessed := by
  intro prep
  exact ay_equisat_backward preprocessed visible
    (ay_preprocess_visible_step original preprocessed visible prep)

theorem ay_original_to_visible
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyPreprocessMap original preprocessed visible ->
    original ->
    visible := by
  intro prep
  intro horiginal
  exact ay_preprocessed_to_visible original preprocessed visible prep
    (ay_original_to_preprocessed original preprocessed visible prep
      horiginal)

theorem ay_sat_formula
    (formula : Prop) (model : Prop) :
    AySat formula model ->
    formula := by
  intro sat
  exact ay_conj_left formula model sat

theorem ay_sat_model
    (formula : Prop) (model : Prop) :
    AySat formula model ->
    model := by
  intro sat
  exact ay_conj_right formula model sat

theorem ay_compressed_sat_visible
    (visibleModel : Prop) (originalModel : Prop) :
    AyCompressedSat visibleModel originalModel ->
    visibleModel := by
  intro compressed
  exact ay_conj_left visibleModel (visibleModel -> originalModel)
    compressed

theorem ay_compressed_sat_reconstruct
    (visibleModel : Prop) (originalModel : Prop) :
    AyCompressedSat visibleModel originalModel ->
    originalModel := by
  intro compressed
  exact ay_conj_right visibleModel (visibleModel -> originalModel)
    compressed
    (ay_compressed_sat_visible visibleModel originalModel compressed)

theorem ay_sat_to_compressed_sat
    (original : Prop) (preprocessed : Prop)
    (visible : Prop) (visibleModel : Prop) (originalModel : Prop) :
    AyPreprocessMap original preprocessed visible ->
    AySat preprocessed visibleModel ->
    (visibleModel -> originalModel) ->
    AyCompressedSat visibleModel originalModel := by
  intro _prep
  intro sat
  intro reconstruct
  exact ay_conj_intro visibleModel (visibleModel -> originalModel)
    (ay_sat_model preprocessed visibleModel sat)
    reconstruct

theorem ay_compressed_sat_to_visible_sat
    (visibleModel : Prop) (originalModel : Prop) :
    AyCompressedSat visibleModel originalModel ->
    AySat originalModel visibleModel := by
  intro compressed
  exact ay_conj_intro originalModel visibleModel
    (ay_compressed_sat_reconstruct visibleModel originalModel compressed)
    (ay_compressed_sat_visible visibleModel originalModel compressed)

theorem ay_sat_compressed_roundtrip
    (original : Prop) (preprocessed : Prop)
    (visible : Prop) (visibleModel : Prop) (originalModel : Prop) :
    AyPreprocessMap original preprocessed visible ->
    (visibleModel -> originalModel) ->
    (visibleModel -> preprocessed) ->
    AyRoundtrip
      (AySat preprocessed visibleModel)
      (AyCompressedSat visibleModel originalModel) := by
  intro prep
  intro reconstruct
  intro decompress
  exact ay_conj_intro
    (AySat preprocessed visibleModel ->
      AyCompressedSat visibleModel originalModel)
    (AyCompressedSat visibleModel originalModel ->
      AySat preprocessed visibleModel)
    (fun sat =>
      ay_sat_to_compressed_sat
        original preprocessed visible visibleModel originalModel
        prep sat reconstruct)
    (fun compressed =>
      ay_conj_intro preprocessed visibleModel
        (decompress
          (ay_compressed_sat_visible visibleModel originalModel compressed))
        (ay_compressed_sat_visible visibleModel originalModel compressed))

theorem ay_compressed_unsat_final_clause
    (original : Prop) (visible : Prop) (finalClause : Prop) :
    AyCompressedUnsat original visible finalClause ->
    finalClause := by
  intro compressed
  exact ay_conj_left finalClause
    (AyConj (original -> visible) (visible -> finalClause -> False))
    compressed

theorem ay_compressed_unsat_original_to_visible
    (original : Prop) (visible : Prop) (finalClause : Prop) :
    AyCompressedUnsat original visible finalClause ->
    original -> visible := by
  intro compressed
  exact ay_conj_left (original -> visible) (visible -> finalClause -> False)
    (ay_conj_right finalClause
      (AyConj (original -> visible) (visible -> finalClause -> False))
      compressed)

theorem ay_compressed_unsat_replay
    (original : Prop) (visible : Prop) (finalClause : Prop) :
    AyCompressedUnsat original visible finalClause ->
    visible -> finalClause -> False := by
  intro compressed
  exact ay_conj_right (original -> visible) (visible -> finalClause -> False)
    (ay_conj_right finalClause
      (AyConj (original -> visible) (visible -> finalClause -> False))
      compressed)

theorem ay_replay_to_compressed_unsat
    (original : Prop) (preprocessed : Prop)
    (visible : Prop) (finalClause : Prop) :
    AyPreprocessMap original preprocessed visible ->
    AyReplay preprocessed finalClause False ->
    finalClause ->
    AyCompressedUnsat original visible finalClause := by
  intro prep
  intro replay
  intro hfinal
  exact ay_conj_intro finalClause
    (AyConj (original -> visible) (visible -> finalClause -> False))
    hfinal
    (ay_conj_intro (original -> visible) (visible -> finalClause -> False)
      (ay_original_to_visible original preprocessed visible prep)
      (fun hvisible hclause =>
        replay
          (ay_visible_to_preprocessed original preprocessed visible prep
            hvisible)
          hclause))

theorem ay_compressed_unsat_blocks_original
    (original : Prop) (visible : Prop) (finalClause : Prop) :
    AyCompressedUnsat original visible finalClause ->
    original ->
    False := by
  intro compressed
  intro horiginal
  exact ay_compressed_unsat_replay original visible finalClause compressed
    (ay_compressed_unsat_original_to_visible
      original visible finalClause compressed horiginal)
    (ay_compressed_unsat_final_clause original visible finalClause compressed)

theorem ay_compressed_outcome_sat
    (original : Prop) (visible : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop) :
    AyCompressedSat visibleModel originalModel ->
    AyCompressedOutcome
      original visible visibleModel originalModel finalClause := by
  exact ay_disj_left
    (AyCompressedSat visibleModel originalModel)
    (AyCompressedUnsat original visible finalClause)

theorem ay_compressed_outcome_unsat
    (original : Prop) (visible : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop) :
    AyCompressedUnsat original visible finalClause ->
    AyCompressedOutcome
      original visible visibleModel originalModel finalClause := by
  exact ay_disj_right
    (AyCompressedSat visibleModel originalModel)
    (AyCompressedUnsat original visible finalClause)
