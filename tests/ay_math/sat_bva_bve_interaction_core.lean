-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked propositional abstraction for bounded variable addition followed by
-- bounded variable elimination. The visible formula exposes a factored visible
-- constraint; BVA introduces an auxiliary gate for that factor, and BVE
-- projects the auxiliary formula back to the visible formula.

def AyBvaBveDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyBvaBveConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyBvaBveProjection (before : Prop) (after : Prop) :=
  before -> after

def AyBvaBveReconstruction (before : Prop) (after : Prop) :=
  after -> before

def AyBvaBveEquisat (before : Prop) (after : Prop) :=
  AyBvaBveConj
    (AyBvaBveProjection before after)
    (AyBvaBveReconstruction before after)

def AyBvaVisibleFactor (left : Prop) (right : Prop) :=
  AyBvaBveDisj left right

def AyBvaVisibleFormula (left : Prop) (right : Prop) (rest : Prop) :=
  AyBvaBveConj (AyBvaVisibleFactor left right) rest

def AyBvaAuxFormula
    (aux : Prop) (left : Prop) (right : Prop) (rest : Prop) :=
  AyBvaBveConj
    aux
    (AyBvaBveConj (aux -> AyBvaVisibleFactor left right) rest)

def AyBveEliminatedFormula (left : Prop) (right : Prop) (rest : Prop) :=
  AyBvaVisibleFormula left right rest

def AyBvaAuxReconstruction
    (aux : Prop) (left : Prop) (right : Prop) :=
  AyBvaVisibleFactor left right -> aux

def AyBvaBveVisibleMap
    (internal : Prop) (visible : Prop) :=
  AyBvaBveConj (internal -> visible) (visible -> internal)

theorem ay_bva_bve_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyBvaBveConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_bva_bve_disj_left
    (p : Prop) (q : Prop) :
    p -> AyBvaBveDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_bva_bve_disj_right
    (p : Prop) (q : Prop) :
    q -> AyBvaBveDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_bva_bve_equisat_intro
    (before : Prop) (after : Prop) :
    AyBvaBveProjection before after ->
    AyBvaBveReconstruction before after ->
    AyBvaBveEquisat before after := by
  intro project
  intro reconstruct
  exact ay_bva_bve_conj_intro
    (AyBvaBveProjection before after)
    (AyBvaBveReconstruction before after)
    project
    reconstruct

theorem ay_bva_bve_equisat_projection
    (before : Prop) (after : Prop) :
    AyBvaBveEquisat before after ->
    AyBvaBveProjection before after := by
  intro certificate
  exact certificate
    (AyBvaBveProjection before after)
    (fun project _reconstruct => project)

theorem ay_bva_bve_equisat_reconstruction
    (before : Prop) (after : Prop) :
    AyBvaBveEquisat before after ->
    AyBvaBveReconstruction before after := by
  intro certificate
  exact certificate
    (AyBvaBveReconstruction before after)
    (fun _project reconstruct => reconstruct)

theorem ay_bva_bve_projection_compose
    (a : Prop) (b : Prop) (c : Prop) :
    AyBvaBveProjection a b ->
    AyBvaBveProjection b c ->
    AyBvaBveProjection a c := by
  intro project_ab
  intro project_bc
  intro ha
  exact project_bc (project_ab ha)

theorem ay_bva_bve_reconstruction_compose
    (a : Prop) (b : Prop) (c : Prop) :
    AyBvaBveReconstruction a b ->
    AyBvaBveReconstruction b c ->
    AyBvaBveReconstruction a c := by
  intro reconstruct_ab
  intro reconstruct_bc
  intro hc
  exact reconstruct_ab (reconstruct_bc hc)

theorem ay_bva_bve_equisat_compose
    (a : Prop) (b : Prop) (c : Prop) :
    AyBvaBveEquisat a b ->
    AyBvaBveEquisat b c ->
    AyBvaBveEquisat a c := by
  intro cert_ab
  intro cert_bc
  exact ay_bva_bve_equisat_intro
    a
    c
    (ay_bva_bve_projection_compose a b c
      (ay_bva_bve_equisat_projection a b cert_ab)
      (ay_bva_bve_equisat_projection b c cert_bc))
    (ay_bva_bve_reconstruction_compose a b c
      (ay_bva_bve_equisat_reconstruction a b cert_ab)
      (ay_bva_bve_equisat_reconstruction b c cert_bc))

theorem ay_bva_factor_introduction_left
    (left : Prop) (right : Prop) :
    left -> AyBvaVisibleFactor left right := by
  intro hleft
  exact ay_bva_bve_disj_left left right hleft

theorem ay_bva_factor_introduction_right
    (left : Prop) (right : Prop) :
    right -> AyBvaVisibleFactor left right := by
  intro hright
  exact ay_bva_bve_disj_right left right hright

theorem ay_bva_aux_formula_project_visible
    (aux : Prop) (left : Prop) (right : Prop) (rest : Prop) :
    AyBvaAuxFormula aux left right rest ->
    AyBvaVisibleFormula left right rest := by
  intro aux_formula
  intro result
  intro build
  exact aux_formula result
    (fun haux tail =>
      tail result
        (fun aux_to_factor hrest =>
          build (aux_to_factor haux) hrest))

theorem ay_bva_auxiliary_reconstruction
    (aux : Prop) (left : Prop) (right : Prop) (rest : Prop) :
    AyBvaAuxReconstruction aux left right ->
    AyBvaVisibleFormula left right rest ->
    AyBvaAuxFormula aux left right rest := by
  intro factor_to_aux
  intro visible
  intro result
  intro build
  exact visible result
    (fun factor hrest =>
      build
        (factor_to_aux factor)
        (ay_bva_bve_conj_intro
          (aux -> AyBvaVisibleFactor left right)
          rest
          (fun _haux => factor)
          hrest))

theorem ay_bva_addition_equisat
    (aux : Prop) (left : Prop) (right : Prop) (rest : Prop) :
    AyBvaAuxReconstruction aux left right ->
    AyBvaBveEquisat
      (AyBvaVisibleFormula left right rest)
      (AyBvaAuxFormula aux left right rest) := by
  intro factor_to_aux
  exact ay_bva_bve_equisat_intro
    (AyBvaVisibleFormula left right rest)
    (AyBvaAuxFormula aux left right rest)
    (ay_bva_auxiliary_reconstruction aux left right rest factor_to_aux)
    (ay_bva_aux_formula_project_visible aux left right rest)

theorem ay_bve_projection_after_elimination
    (aux : Prop) (left : Prop) (right : Prop) (rest : Prop) :
    AyBvaAuxFormula aux left right rest ->
    AyBveEliminatedFormula left right rest := by
  intro aux_formula
  exact ay_bva_aux_formula_project_visible aux left right rest aux_formula

theorem ay_bve_reconstruction_after_elimination
    (aux : Prop) (left : Prop) (right : Prop) (rest : Prop) :
    AyBvaAuxReconstruction aux left right ->
    AyBveEliminatedFormula left right rest ->
    AyBvaAuxFormula aux left right rest := by
  intro factor_to_aux
  intro eliminated
  exact ay_bva_auxiliary_reconstruction
    aux
    left
    right
    rest
    factor_to_aux
    eliminated

theorem ay_bve_elimination_equisat
    (aux : Prop) (left : Prop) (right : Prop) (rest : Prop) :
    AyBvaAuxReconstruction aux left right ->
    AyBvaBveEquisat
      (AyBvaAuxFormula aux left right rest)
      (AyBveEliminatedFormula left right rest) := by
  intro factor_to_aux
  exact ay_bva_bve_equisat_intro
    (AyBvaAuxFormula aux left right rest)
    (AyBveEliminatedFormula left right rest)
    (ay_bve_projection_after_elimination aux left right rest)
    (ay_bve_reconstruction_after_elimination
      aux left right rest factor_to_aux)

theorem ay_bva_then_bve_projection
    (aux : Prop) (left : Prop) (right : Prop) (rest : Prop) :
    AyBvaVisibleFormula left right rest ->
    AyBveEliminatedFormula left right rest := by
  intro visible
  exact visible

theorem ay_bva_then_bve_reconstruction
    (aux : Prop) (left : Prop) (right : Prop) (rest : Prop) :
    AyBveEliminatedFormula left right rest ->
    AyBvaVisibleFormula left right rest := by
  intro eliminated
  exact eliminated

theorem ay_bva_then_bve_visible_equisat
    (aux : Prop) (left : Prop) (right : Prop) (rest : Prop) :
    AyBvaBveEquisat
      (AyBvaVisibleFormula left right rest)
      (AyBveEliminatedFormula left right rest) := by
  exact ay_bva_bve_equisat_intro
    (AyBvaVisibleFormula left right rest)
    (AyBveEliminatedFormula left right rest)
    (ay_bva_then_bve_projection aux left right rest)
    (ay_bva_then_bve_reconstruction aux left right rest)

theorem ay_bva_then_bve_composed_equisat
    (aux : Prop) (left : Prop) (right : Prop) (rest : Prop) :
    AyBvaAuxReconstruction aux left right ->
    AyBvaBveEquisat
      (AyBvaVisibleFormula left right rest)
      (AyBveEliminatedFormula left right rest) := by
  intro factor_to_aux
  exact ay_bva_bve_equisat_compose
    (AyBvaVisibleFormula left right rest)
    (AyBvaAuxFormula aux left right rest)
    (AyBveEliminatedFormula left right rest)
    (ay_bva_addition_equisat aux left right rest factor_to_aux)
    (ay_bve_elimination_equisat aux left right rest factor_to_aux)

theorem ay_bva_bve_visible_map_intro
    (internal : Prop) (visible : Prop) :
    (internal -> visible) ->
    (visible -> internal) ->
    AyBvaBveVisibleMap internal visible := by
  intro project_visible
  intro reconstruct_visible
  exact ay_bva_bve_conj_intro
    (internal -> visible)
    (visible -> internal)
    project_visible
    reconstruct_visible

theorem ay_bva_bve_visible_map_for_eliminated
    (aux : Prop) (left : Prop) (right : Prop) (rest : Prop) :
    AyBvaBveVisibleMap
      (AyBveEliminatedFormula left right rest)
      (AyBvaVisibleFormula left right rest) := by
  exact ay_bva_bve_visible_map_intro
    (AyBveEliminatedFormula left right rest)
    (AyBvaVisibleFormula left right rest)
    (ay_bva_then_bve_reconstruction aux left right rest)
    (ay_bva_then_bve_projection aux left right rest)
