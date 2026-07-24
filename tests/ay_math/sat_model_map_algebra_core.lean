-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Model-map algebra for ay SAT transformations.
-- A projection maps models of the original formula to models of the
-- transformed formula. A reconstruction maps models back to the original.

def AyModelConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyProjection (original : Prop) (transformed : Prop) :=
  original -> transformed

def AyReconstruction (original : Prop) (transformed : Prop) :=
  transformed -> original

def AyModelEquiv (original : Prop) (transformed : Prop) :=
  AyModelConj
    (AyProjection original transformed)
    (AyReconstruction original transformed)

theorem ay_model_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyModelConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_projection_compose
    (a : Prop) (b : Prop) (c : Prop) :
    AyProjection a b ->
    AyProjection b c ->
    AyProjection a c := by
  intro ab
  intro bc
  intro ha
  exact bc (ab ha)

theorem ay_reconstruction_compose
    (a : Prop) (b : Prop) (c : Prop) :
    AyReconstruction a b ->
    AyReconstruction b c ->
    AyReconstruction a c := by
  intro ba
  intro cb
  intro hc
  exact ba (cb hc)

theorem ay_model_equiv_projection
    (original : Prop) (transformed : Prop) :
    AyModelEquiv original transformed ->
    AyProjection original transformed := by
  intro equiv
  exact equiv (AyProjection original transformed)
    (fun projection _reconstruction => projection)

theorem ay_model_equiv_reconstruction
    (original : Prop) (transformed : Prop) :
    AyModelEquiv original transformed ->
    AyReconstruction original transformed := by
  intro equiv
  exact equiv (AyReconstruction original transformed)
    (fun _projection reconstruction => reconstruction)

theorem ay_model_equiv_compose
    (a : Prop) (b : Prop) (c : Prop) :
    AyModelEquiv a b ->
    AyModelEquiv b c ->
    AyModelEquiv a c := by
  intro ab
  intro bc
  exact ay_model_conj_intro
    (AyProjection a c)
    (AyReconstruction a c)
    (ay_projection_compose a b c
      (ay_model_equiv_projection a b ab)
      (ay_model_equiv_projection b c bc))
    (ay_reconstruction_compose a b c
      (ay_model_equiv_reconstruction a b ab)
      (ay_model_equiv_reconstruction b c bc))
