-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked model projection/reconstruction certificate algebra for SAT
-- preprocessing certificates. The propositions stand for model predicates:
-- projection maps an original model to a transformed model, reconstruction maps
-- back, and visible maps package the model seen on user-visible variables.

def AyMPCDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyMPCConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyMPCProjection (original : Prop) (transformed : Prop) :=
  original -> transformed

def AyMPCReconstruction (original : Prop) (transformed : Prop) :=
  transformed -> original

def AyMPCEquisat (original : Prop) (transformed : Prop) :=
  AyMPCConj
    (AyMPCProjection original transformed)
    (AyMPCReconstruction original transformed)

def AyMPCVisibleProjection (internal : Prop) (visible : Prop) :=
  internal -> visible

def AyMPCVisibleReconstruction (visible : Prop) (internal : Prop) :=
  visible -> internal

def AyMPCVisibleModelMap (internal : Prop) (visible : Prop) :=
  AyMPCConj
    (AyMPCVisibleProjection internal visible)
    (AyMPCVisibleReconstruction visible internal)

def AyMPCPreprocessCertificate
    (original : Prop) (transformed : Prop) (visible : Prop) :=
  AyMPCConj
    (AyMPCEquisat original transformed)
    (AyMPCVisibleModelMap transformed visible)

theorem ay_mpc_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyMPCConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_mpc_disj_left
    (p : Prop) (q : Prop) :
    p -> AyMPCDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_mpc_disj_right
    (p : Prop) (q : Prop) :
    q -> AyMPCDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_mpc_equisat_intro
    (original : Prop) (transformed : Prop) :
    AyMPCProjection original transformed ->
    AyMPCReconstruction original transformed ->
    AyMPCEquisat original transformed := by
  intro project
  intro reconstruct
  exact ay_mpc_conj_intro
    (AyMPCProjection original transformed)
    (AyMPCReconstruction original transformed)
    project
    reconstruct

theorem ay_mpc_equisat_projection
    (original : Prop) (transformed : Prop) :
    AyMPCEquisat original transformed ->
    AyMPCProjection original transformed := by
  intro certificate
  exact certificate
    (AyMPCProjection original transformed)
    (fun project _reconstruct => project)

theorem ay_mpc_equisat_reconstruction
    (original : Prop) (transformed : Prop) :
    AyMPCEquisat original transformed ->
    AyMPCReconstruction original transformed := by
  intro certificate
  exact certificate
    (AyMPCReconstruction original transformed)
    (fun _project reconstruct => reconstruct)

theorem ay_mpc_projection_compose
    (a : Prop) (b : Prop) (c : Prop) :
    AyMPCProjection a b ->
    AyMPCProjection b c ->
    AyMPCProjection a c := by
  intro project_ab
  intro project_bc
  intro ha
  exact project_bc (project_ab ha)

theorem ay_mpc_reconstruction_compose
    (a : Prop) (b : Prop) (c : Prop) :
    AyMPCReconstruction a b ->
    AyMPCReconstruction b c ->
    AyMPCReconstruction a c := by
  intro reconstruct_ab
  intro reconstruct_bc
  intro hc
  exact reconstruct_ab (reconstruct_bc hc)

theorem ay_mpc_equisat_compose
    (a : Prop) (b : Prop) (c : Prop) :
    AyMPCEquisat a b ->
    AyMPCEquisat b c ->
    AyMPCEquisat a c := by
  intro cert_ab
  intro cert_bc
  exact ay_mpc_equisat_intro
    a
    c
    (ay_mpc_projection_compose a b c
      (ay_mpc_equisat_projection a b cert_ab)
      (ay_mpc_equisat_projection b c cert_bc))
    (ay_mpc_reconstruction_compose a b c
      (ay_mpc_equisat_reconstruction a b cert_ab)
      (ay_mpc_equisat_reconstruction b c cert_bc))

theorem ay_mpc_transport_witness_forward
    (original : Prop) (transformed : Prop) (witness : Prop) :
    AyMPCEquisat original transformed ->
    (transformed -> witness) ->
    original ->
    witness := by
  intro certificate
  intro transformed_to_witness
  intro horiginal
  exact transformed_to_witness
    (ay_mpc_equisat_projection original transformed certificate horiginal)

theorem ay_mpc_transport_witness_backward
    (original : Prop) (transformed : Prop) (witness : Prop) :
    AyMPCEquisat original transformed ->
    (original -> witness) ->
    transformed ->
    witness := by
  intro certificate
  intro original_to_witness
  intro htransformed
  exact original_to_witness
    (ay_mpc_equisat_reconstruction original transformed certificate htransformed)

theorem ay_mpc_visible_map_intro
    (internal : Prop) (visible : Prop) :
    AyMPCVisibleProjection internal visible ->
    AyMPCVisibleReconstruction visible internal ->
    AyMPCVisibleModelMap internal visible := by
  intro project_visible
  intro reconstruct_visible
  exact ay_mpc_conj_intro
    (AyMPCVisibleProjection internal visible)
    (AyMPCVisibleReconstruction visible internal)
    project_visible
    reconstruct_visible

theorem ay_mpc_visible_projection
    (internal : Prop) (visible : Prop) :
    AyMPCVisibleModelMap internal visible ->
    AyMPCVisibleProjection internal visible := by
  intro visible_map
  exact visible_map
    (AyMPCVisibleProjection internal visible)
    (fun project_visible _reconstruct_visible => project_visible)

theorem ay_mpc_visible_reconstruction
    (internal : Prop) (visible : Prop) :
    AyMPCVisibleModelMap internal visible ->
    AyMPCVisibleReconstruction visible internal := by
  intro visible_map
  exact visible_map
    (AyMPCVisibleReconstruction visible internal)
    (fun _project_visible reconstruct_visible => reconstruct_visible)

theorem ay_mpc_visible_projection_transport
    (original : Prop) (transformed : Prop) (visible : Prop) :
    AyMPCEquisat original transformed ->
    AyMPCVisibleModelMap transformed visible ->
    AyMPCVisibleProjection original visible := by
  intro certificate
  intro visible_map
  exact ay_mpc_projection_compose
    original
    transformed
    visible
    (ay_mpc_equisat_projection original transformed certificate)
    (ay_mpc_visible_projection transformed visible visible_map)

theorem ay_mpc_visible_reconstruction_transport
    (original : Prop) (transformed : Prop) (visible : Prop) :
    AyMPCEquisat original transformed ->
    AyMPCVisibleModelMap transformed visible ->
    AyMPCVisibleReconstruction visible original := by
  intro certificate
  intro visible_map
  intro hvisible
  exact ay_mpc_equisat_reconstruction original transformed certificate
    (ay_mpc_visible_reconstruction transformed visible visible_map hvisible)

theorem ay_mpc_visible_map_transport
    (original : Prop) (transformed : Prop) (visible : Prop) :
    AyMPCEquisat original transformed ->
    AyMPCVisibleModelMap transformed visible ->
    AyMPCVisibleModelMap original visible := by
  intro certificate
  intro visible_map
  exact ay_mpc_visible_map_intro
    original
    visible
    (ay_mpc_visible_projection_transport
      original transformed visible certificate visible_map)
    (ay_mpc_visible_reconstruction_transport
      original transformed visible certificate visible_map)

theorem ay_mpc_certificate_intro
    (original : Prop) (transformed : Prop) (visible : Prop) :
    AyMPCEquisat original transformed ->
    AyMPCVisibleModelMap transformed visible ->
    AyMPCPreprocessCertificate original transformed visible := by
  intro certificate
  intro visible_map
  exact ay_mpc_conj_intro
    (AyMPCEquisat original transformed)
    (AyMPCVisibleModelMap transformed visible)
    certificate
    visible_map

theorem ay_mpc_certificate_equisat
    (original : Prop) (transformed : Prop) (visible : Prop) :
    AyMPCPreprocessCertificate original transformed visible ->
    AyMPCEquisat original transformed := by
  intro certificate
  exact certificate
    (AyMPCEquisat original transformed)
    (fun equisat _visible_map => equisat)

theorem ay_mpc_certificate_visible_map
    (original : Prop) (transformed : Prop) (visible : Prop) :
    AyMPCPreprocessCertificate original transformed visible ->
    AyMPCVisibleModelMap transformed visible := by
  intro certificate
  exact certificate
    (AyMPCVisibleModelMap transformed visible)
    (fun _equisat visible_map => visible_map)

theorem ay_mpc_certificate_visible_original_map
    (original : Prop) (transformed : Prop) (visible : Prop) :
    AyMPCPreprocessCertificate original transformed visible ->
    AyMPCVisibleModelMap original visible := by
  intro certificate
  exact ay_mpc_visible_map_transport
    original
    transformed
    visible
    (ay_mpc_certificate_equisat original transformed visible certificate)
    (ay_mpc_certificate_visible_map original transformed visible certificate)

theorem ay_mpc_certificate_compose
    (original : Prop) (middle : Prop) (transformed : Prop) (visible : Prop) :
    AyMPCPreprocessCertificate original middle visible ->
    AyMPCPreprocessCertificate middle transformed visible ->
    AyMPCPreprocessCertificate original transformed visible :=
  fun first second result build =>
    first result
      (fun first_equisat _first_visible =>
        second result
          (fun second_equisat second_visible =>
            build
              (ay_mpc_equisat_compose
                original
                middle
                transformed
                first_equisat
                second_equisat)
              second_visible))
