-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked propositional skeleton for global SAT-COMP pipeline soundness.
-- Each stage is abstracted as explicit forward/backward model maps. The final
-- theorem composes BVE projection, vivification strengthening, HBR/RAT
-- addition, LRAT trace splicing, and visible-model reconstruction.

def AyGlobalDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyGlobalConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyGlobalEquisat (before : Prop) (after : Prop) :=
  AyGlobalConj (before -> after) (after -> before)

def AyGlobalForwardMap (before : Prop) (after : Prop) :=
  before -> after

def AyGlobalBackwardMap (before : Prop) (after : Prop) :=
  after -> before

def AyGlobalBveProjection (before : Prop) (after : Prop) :=
  AyGlobalEquisat before after

def AyGlobalVivificationStrengthening (before : Prop) (after : Prop) :=
  AyGlobalEquisat before after

def AyGlobalHbrRatAddition (before : Prop) (after : Prop) :=
  AyGlobalEquisat before after

def AyGlobalLratTraceSplice (before : Prop) (after : Prop) :=
  AyGlobalEquisat before after

def AyGlobalVisibleModelReconstruction
    (internalFinal : Prop) (visibleFinal : Prop) :=
  AyGlobalEquisat internalFinal visibleFinal

theorem ay_global_disj_left
    (left : Prop) (right : Prop) :
    left -> AyGlobalDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_global_disj_right
    (left : Prop) (right : Prop) :
    right -> AyGlobalDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_global_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyGlobalConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_global_conj_left
    (left : Prop) (right : Prop) :
    AyGlobalConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_global_conj_right
    (left : Prop) (right : Prop) :
    AyGlobalConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_global_equisat_intro
    (before : Prop) (after : Prop) :
    AyGlobalForwardMap before after ->
    AyGlobalBackwardMap before after ->
    AyGlobalEquisat before after := by
  intro forward
  intro backward
  exact ay_global_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_global_forward_map
    (before : Prop) (after : Prop) :
    AyGlobalEquisat before after ->
    AyGlobalForwardMap before after := by
  intro eqsat
  exact ay_global_conj_left (before -> after) (after -> before) eqsat

theorem ay_global_backward_map
    (before : Prop) (after : Prop) :
    AyGlobalEquisat before after ->
    AyGlobalBackwardMap before after := by
  intro eqsat
  exact ay_global_conj_right (before -> after) (after -> before) eqsat

theorem ay_global_forward_compose
    (a : Prop) (b : Prop) (c : Prop) :
    AyGlobalForwardMap a b ->
    AyGlobalForwardMap b c ->
    AyGlobalForwardMap a c := by
  intro ab
  intro bc
  intro ha
  exact bc (ab ha)

theorem ay_global_backward_compose
    (a : Prop) (b : Prop) (c : Prop) :
    AyGlobalBackwardMap a b ->
    AyGlobalBackwardMap b c ->
    AyGlobalBackwardMap a c := by
  intro ba
  intro cb
  intro hc
  exact ba (cb hc)

theorem ay_global_equisat_compose
    (a : Prop) (b : Prop) (c : Prop) :
    AyGlobalEquisat a b ->
    AyGlobalEquisat b c ->
    AyGlobalEquisat a c := by
  intro ab
  intro bc
  exact ay_global_equisat_intro a c
    (ay_global_forward_compose a b c
      (ay_global_forward_map a b ab)
      (ay_global_forward_map b c bc))
    (ay_global_backward_compose a b c
      (ay_global_backward_map a b ab)
      (ay_global_backward_map b c bc))

theorem ay_global_bve_projection_forward
    (before : Prop) (after : Prop) :
    AyGlobalBveProjection before after ->
    AyGlobalForwardMap before after := by
  intro stage
  exact ay_global_forward_map before after stage

theorem ay_global_bve_projection_backward
    (before : Prop) (after : Prop) :
    AyGlobalBveProjection before after ->
    AyGlobalBackwardMap before after := by
  intro stage
  exact ay_global_backward_map before after stage

theorem ay_global_vivification_forward
    (before : Prop) (after : Prop) :
    AyGlobalVivificationStrengthening before after ->
    AyGlobalForwardMap before after := by
  intro stage
  exact ay_global_forward_map before after stage

theorem ay_global_vivification_backward
    (before : Prop) (after : Prop) :
    AyGlobalVivificationStrengthening before after ->
    AyGlobalBackwardMap before after := by
  intro stage
  exact ay_global_backward_map before after stage

theorem ay_global_hbr_rat_forward
    (before : Prop) (after : Prop) :
    AyGlobalHbrRatAddition before after ->
    AyGlobalForwardMap before after := by
  intro stage
  exact ay_global_forward_map before after stage

theorem ay_global_hbr_rat_backward
    (before : Prop) (after : Prop) :
    AyGlobalHbrRatAddition before after ->
    AyGlobalBackwardMap before after := by
  intro stage
  exact ay_global_backward_map before after stage

theorem ay_global_lrat_splice_forward
    (before : Prop) (after : Prop) :
    AyGlobalLratTraceSplice before after ->
    AyGlobalForwardMap before after := by
  intro stage
  exact ay_global_forward_map before after stage

theorem ay_global_lrat_splice_backward
    (before : Prop) (after : Prop) :
    AyGlobalLratTraceSplice before after ->
    AyGlobalBackwardMap before after := by
  intro stage
  exact ay_global_backward_map before after stage

theorem ay_global_visible_model_forward
    (internalFinal : Prop) (visibleFinal : Prop) :
    AyGlobalVisibleModelReconstruction internalFinal visibleFinal ->
    AyGlobalForwardMap internalFinal visibleFinal := by
  intro stage
  exact ay_global_forward_map internalFinal visibleFinal stage

theorem ay_global_visible_model_backward
    (internalFinal : Prop) (visibleFinal : Prop) :
    AyGlobalVisibleModelReconstruction internalFinal visibleFinal ->
    AyGlobalBackwardMap internalFinal visibleFinal := by
  intro stage
  exact ay_global_backward_map internalFinal visibleFinal stage

theorem ay_global_pipeline_forward_map
    (input bve viv hbr lrat visible : Prop) :
    AyGlobalBveProjection input bve ->
    AyGlobalVivificationStrengthening bve viv ->
    AyGlobalHbrRatAddition viv hbr ->
    AyGlobalLratTraceSplice hbr lrat ->
    AyGlobalVisibleModelReconstruction lrat visible ->
    AyGlobalForwardMap input visible := by
  intro bve_stage
  intro viv_stage
  intro hbr_stage
  intro lrat_stage
  intro visible_stage
  exact ay_global_forward_compose input lrat visible
    (ay_global_forward_compose input hbr lrat
      (ay_global_forward_compose input viv hbr
        (ay_global_forward_compose input bve viv
          (ay_global_bve_projection_forward input bve bve_stage)
          (ay_global_vivification_forward bve viv viv_stage))
        (ay_global_hbr_rat_forward viv hbr hbr_stage))
      (ay_global_lrat_splice_forward hbr lrat lrat_stage))
    (ay_global_visible_model_forward lrat visible visible_stage)

theorem ay_global_pipeline_backward_map
    (input bve viv hbr lrat visible : Prop) :
    AyGlobalBveProjection input bve ->
    AyGlobalVivificationStrengthening bve viv ->
    AyGlobalHbrRatAddition viv hbr ->
    AyGlobalLratTraceSplice hbr lrat ->
    AyGlobalVisibleModelReconstruction lrat visible ->
    AyGlobalBackwardMap input visible := by
  intro bve_stage
  intro viv_stage
  intro hbr_stage
  intro lrat_stage
  intro visible_stage
  exact ay_global_backward_compose input lrat visible
    (ay_global_backward_compose input hbr lrat
      (ay_global_backward_compose input viv hbr
        (ay_global_backward_compose input bve viv
          (ay_global_bve_projection_backward input bve bve_stage)
          (ay_global_vivification_backward bve viv viv_stage))
        (ay_global_hbr_rat_backward viv hbr hbr_stage))
      (ay_global_lrat_splice_backward hbr lrat lrat_stage))
    (ay_global_visible_model_backward lrat visible visible_stage)

theorem ay_global_satcomp_pipeline_equisat
    (input bve viv hbr lrat visible : Prop) :
    AyGlobalBveProjection input bve ->
    AyGlobalVivificationStrengthening bve viv ->
    AyGlobalHbrRatAddition viv hbr ->
    AyGlobalLratTraceSplice hbr lrat ->
    AyGlobalVisibleModelReconstruction lrat visible ->
    AyGlobalEquisat input visible := by
  intro bve_stage
  intro viv_stage
  intro hbr_stage
  intro lrat_stage
  intro visible_stage
  exact ay_global_equisat_intro input visible
    (ay_global_pipeline_forward_map
      input bve viv hbr lrat visible
      bve_stage viv_stage hbr_stage lrat_stage visible_stage)
    (ay_global_pipeline_backward_map
      input bve viv hbr lrat visible
      bve_stage viv_stage hbr_stage lrat_stage visible_stage)

theorem ay_global_visible_model_reconstructs_input
    (input bve viv hbr lrat visible : Prop) :
    AyGlobalBveProjection input bve ->
    AyGlobalVivificationStrengthening bve viv ->
    AyGlobalHbrRatAddition viv hbr ->
    AyGlobalLratTraceSplice hbr lrat ->
    AyGlobalVisibleModelReconstruction lrat visible ->
    visible ->
    input := by
  intro bve_stage
  intro viv_stage
  intro hbr_stage
  intro lrat_stage
  intro visible_stage
  exact ay_global_pipeline_backward_map
    input bve viv hbr lrat visible
    bve_stage viv_stage hbr_stage lrat_stage visible_stage

