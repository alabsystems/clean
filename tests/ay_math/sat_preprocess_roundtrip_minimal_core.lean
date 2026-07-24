-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Minimal checked roundtrip witnesses for SAT/UNSAT solver outcomes passing
-- through preprocessing and visible projection. All structure is Church
-- encoded so this file remains self-contained.

def AyConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyEquisat (before : Prop) (after : Prop) :=
  AyConj (before -> after) (after -> before)

def AySat (formula : Prop) (model : Prop) :=
  AyConj formula model

def AyReplay (formula : Prop) (certificate : Prop) (conflict : Prop) :=
  formula -> certificate -> conflict

def AyPreprocessMap (original : Prop) (preprocessed : Prop) (visible : Prop) :=
  AyConj (AyEquisat original preprocessed) (AyEquisat preprocessed visible)

def AyVisibleSat (original : Prop) (visible : Prop) (model : Prop) :=
  AyConj original (AyConj visible model)

def AyVisibleUnsat
    (original : Prop) (visible : Prop)
    (certificate : Prop) (conflict : Prop) :=
  AyConj original (AyConj visible (AyConj certificate conflict))

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

theorem ay_visible_to_original
    (original : Prop) (preprocessed : Prop) (visible : Prop) :
    AyPreprocessMap original preprocessed visible ->
    visible ->
    original := by
  intro prep
  intro hvisible
  exact ay_preprocessed_to_original original preprocessed visible prep
    (ay_visible_to_preprocessed original preprocessed visible prep hvisible)

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

theorem ay_visible_sat_visible
    (original : Prop) (visible : Prop) (model : Prop) :
    AyVisibleSat original visible model ->
    visible := by
  intro sat
  exact ay_conj_left visible model
    (ay_conj_right original (AyConj visible model) sat)

theorem ay_visible_sat_model
    (original : Prop) (visible : Prop) (model : Prop) :
    AyVisibleSat original visible model ->
    model := by
  intro sat
  exact ay_conj_right visible model
    (ay_conj_right original (AyConj visible model) sat)

theorem ay_sat_to_visible
    (original : Prop) (preprocessed : Prop)
    (visible : Prop) (model : Prop) :
    AyPreprocessMap original preprocessed visible ->
    AySat preprocessed model ->
    AyVisibleSat original visible model := by
  intro prep
  intro sat
  exact ay_conj_intro original (AyConj visible model)
    (ay_preprocessed_to_original original preprocessed visible prep
      (ay_sat_formula preprocessed model sat))
    (ay_conj_intro visible model
      (ay_preprocessed_to_visible original preprocessed visible prep
        (ay_sat_formula preprocessed model sat))
      (ay_sat_model preprocessed model sat))

theorem ay_visible_to_sat
    (original : Prop) (preprocessed : Prop)
    (visible : Prop) (model : Prop) :
    AyPreprocessMap original preprocessed visible ->
    AyVisibleSat original visible model ->
    AySat preprocessed model := by
  intro prep
  intro sat
  exact ay_conj_intro preprocessed model
    (ay_visible_to_preprocessed original preprocessed visible prep
      (ay_visible_sat_visible original visible model sat))
    (ay_visible_sat_model original visible model sat)

theorem ay_sat_minimal_roundtrip
    (original : Prop) (preprocessed : Prop)
    (visible : Prop) (model : Prop) :
    AyPreprocessMap original preprocessed visible ->
    AyRoundtrip
      (AySat preprocessed model)
      (AyVisibleSat original visible model) := by
  intro prep
  exact ay_conj_intro
    (AySat preprocessed model -> AyVisibleSat original visible model)
    (AyVisibleSat original visible model -> AySat preprocessed model)
    (ay_sat_to_visible original preprocessed visible model prep)
    (ay_visible_to_sat original preprocessed visible model prep)

theorem ay_sat_minimal_identity_witness
    (original : Prop) (preprocessed : Prop)
    (visible : Prop) (model : Prop) :
    AyPreprocessMap original preprocessed visible ->
    AySat preprocessed model ->
    AySat preprocessed model := by
  intro prep
  intro sat
  exact ay_conj_right
    (AySat preprocessed model -> AyVisibleSat original visible model)
    (AyVisibleSat original visible model -> AySat preprocessed model)
    (ay_sat_minimal_roundtrip original preprocessed visible model prep)
    (ay_conj_left
      (AySat preprocessed model -> AyVisibleSat original visible model)
      (AyVisibleSat original visible model -> AySat preprocessed model)
      (ay_sat_minimal_roundtrip original preprocessed visible model prep)
      sat)

theorem ay_unsat_to_visible
    (original : Prop) (preprocessed : Prop)
    (visible : Prop) (certificate : Prop) (conflict : Prop) :
    AyPreprocessMap original preprocessed visible ->
    AyReplay preprocessed certificate conflict ->
    certificate ->
    original ->
    AyVisibleUnsat original visible certificate conflict := by
  intro prep
  intro replay
  intro hcertificate
  intro horiginal
  exact ay_conj_intro original
    (AyConj visible (AyConj certificate conflict))
    horiginal
    (ay_conj_intro visible (AyConj certificate conflict)
      (ay_original_to_visible original preprocessed visible prep horiginal)
      (ay_conj_intro certificate conflict
        hcertificate
        (replay
          (ay_original_to_preprocessed original preprocessed visible prep
            horiginal)
          hcertificate)))

theorem ay_visible_unsat_original
    (original : Prop) (visible : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyVisibleUnsat original visible certificate conflict ->
    original := by
  intro unsat
  exact ay_conj_left original
    (AyConj visible (AyConj certificate conflict))
    unsat

theorem ay_visible_unsat_certificate
    (original : Prop) (visible : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyVisibleUnsat original visible certificate conflict ->
    certificate := by
  intro unsat
  exact ay_conj_left certificate conflict
    (ay_conj_right visible (AyConj certificate conflict)
      (ay_conj_right original
        (AyConj visible (AyConj certificate conflict))
        unsat))

theorem ay_visible_unsat_conflict
    (original : Prop) (visible : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyVisibleUnsat original visible certificate conflict ->
    conflict := by
  intro unsat
  exact ay_conj_right certificate conflict
    (ay_conj_right visible (AyConj certificate conflict)
      (ay_conj_right original
        (AyConj visible (AyConj certificate conflict))
        unsat))

theorem ay_unsat_minimal_identity_witness
    (original : Prop) (visible : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyVisibleUnsat original visible certificate conflict ->
    AyConj certificate conflict := by
  intro unsat
  exact ay_conj_intro certificate conflict
    (ay_visible_unsat_certificate
      original visible certificate conflict unsat)
    (ay_visible_unsat_conflict
      original visible certificate conflict unsat)

theorem ay_unsat_original_identity_witness
    (original : Prop) (visible : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyVisibleUnsat original visible certificate conflict ->
    original := by
  exact ay_visible_unsat_original original visible certificate conflict
