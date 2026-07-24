-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked propositional abstraction for two-level circuit factorization followed
-- by Tseitin auxiliary gate extension. Repeated subgates are factored, the
-- repeated parent gate is factored, and the factored parent gate is replaced by
-- an auxiliary parent gate under an explicit equivalence witness.

def AyCFTTConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyCFTTEquisat (original : Prop) (transformed : Prop) :=
  AyCFTTConj (original -> transformed) (transformed -> original)

def AyCFTTEquiv (p : Prop) (q : Prop) :=
  AyCFTTConj (p -> q) (q -> p)

def AyCFTTDuplicateBlock (gate : Prop) (left : Prop) (right : Prop) :=
  AyCFTTConj gate (AyCFTTConj left (AyCFTTConj gate right))

def AyCFTTFactoredBlock (gate : Prop) (left : Prop) (right : Prop) :=
  AyCFTTConj gate (AyCFTTConj left right)

def AyCFTTOriginal
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop) :=
  AyCFTTDuplicateBlock
    (AyCFTTDuplicateBlock sub subLeft subRight)
    parentLeft
    parentRight

def AyCFTTSubgatesFactored
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop) :=
  AyCFTTDuplicateBlock
    (AyCFTTFactoredBlock sub subLeft subRight)
    parentLeft
    parentRight

def AyCFTTParentsFactored
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop) :=
  AyCFTTFactoredBlock
    (AyCFTTFactoredBlock sub subLeft subRight)
    parentLeft
    parentRight

def AyCFTTTseitinParent
    (auxParent : Prop) (parentLeft : Prop) (parentRight : Prop) :=
  AyCFTTFactoredBlock auxParent parentLeft parentRight

theorem ay_cftt_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyCFTTConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_cftt_equisat_intro
    (original : Prop) (transformed : Prop) :
    (original -> transformed) ->
    (transformed -> original) ->
    AyCFTTEquisat original transformed := by
  intro forward
  intro backward
  exact ay_cftt_conj_intro
    (original -> transformed)
    (transformed -> original)
    forward
    backward

theorem ay_cftt_equiv_forward
    (p : Prop) (q : Prop) :
    AyCFTTEquiv p q -> p -> q := by
  intro equiv
  exact equiv (p -> q) (fun forward _backward => forward)

theorem ay_cftt_equiv_backward
    (p : Prop) (q : Prop) :
    AyCFTTEquiv p q -> q -> p := by
  intro equiv
  exact equiv (q -> p) (fun _forward backward => backward)

theorem ay_cftt_duplicate_project
    (gate : Prop) (left : Prop) (right : Prop) :
    AyCFTTDuplicateBlock gate left right ->
    AyCFTTFactoredBlock gate left right := by
  intro duplicated
  intro result
  intro build
  exact duplicated result
    (fun hgate tail =>
      tail result
        (fun hleft tail2 =>
          tail2 result
            (fun _hgate_again hright =>
              build hgate (ay_cftt_conj_intro left right hleft hright))))

theorem ay_cftt_duplicate_reconstruct
    (gate : Prop) (left : Prop) (right : Prop) :
    AyCFTTFactoredBlock gate left right ->
    AyCFTTDuplicateBlock gate left right := by
  intro factored
  intro result
  intro build
  exact factored result
    (fun hgate tail =>
      tail result
        (fun hleft hright =>
          build hgate
            (ay_cftt_conj_intro
              left
              (AyCFTTConj gate right)
              hleft
              (ay_cftt_conj_intro gate right hgate hright))))

theorem ay_cftt_subgates_project
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop) :
    AyCFTTOriginal sub subLeft subRight parentLeft parentRight ->
    AyCFTTSubgatesFactored sub subLeft subRight parentLeft parentRight := by
  intro original
  intro result
  intro build
  exact original result
    (fun parentGate tail =>
      tail result
        (fun hparentLeft tail2 =>
          tail2 result
            (fun parentGateAgain hparentRight =>
              build
                (ay_cftt_duplicate_project sub subLeft subRight parentGate)
                (ay_cftt_conj_intro
                  parentLeft
                  (AyCFTTConj
                    (AyCFTTFactoredBlock sub subLeft subRight)
                    parentRight)
                  hparentLeft
                  (ay_cftt_conj_intro
                    (AyCFTTFactoredBlock sub subLeft subRight)
                    parentRight
                    (ay_cftt_duplicate_project
                      sub subLeft subRight parentGateAgain)
                    hparentRight)))))

theorem ay_cftt_subgates_reconstruct
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop) :
    AyCFTTSubgatesFactored sub subLeft subRight parentLeft parentRight ->
    AyCFTTOriginal sub subLeft subRight parentLeft parentRight := by
  intro transformed
  intro result
  intro build
  exact transformed result
    (fun parentGate tail =>
      tail result
        (fun hparentLeft tail2 =>
          tail2 result
            (fun parentGateAgain hparentRight =>
              build
                (ay_cftt_duplicate_reconstruct
                  sub subLeft subRight parentGate)
                (ay_cftt_conj_intro
                  parentLeft
                  (AyCFTTConj
                    (AyCFTTDuplicateBlock sub subLeft subRight)
                    parentRight)
                  hparentLeft
                  (ay_cftt_conj_intro
                    (AyCFTTDuplicateBlock sub subLeft subRight)
                    parentRight
                    (ay_cftt_duplicate_reconstruct
                      sub subLeft subRight parentGateAgain)
                    hparentRight)))))

theorem ay_cftt_parent_project
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop) :
    AyCFTTSubgatesFactored sub subLeft subRight parentLeft parentRight ->
    AyCFTTParentsFactored sub subLeft subRight parentLeft parentRight := by
  intro transformed
  exact ay_cftt_duplicate_project
    (AyCFTTFactoredBlock sub subLeft subRight)
    parentLeft
    parentRight
    transformed

theorem ay_cftt_parent_reconstruct
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop) :
    AyCFTTParentsFactored sub subLeft subRight parentLeft parentRight ->
    AyCFTTSubgatesFactored sub subLeft subRight parentLeft parentRight := by
  intro transformed
  exact ay_cftt_duplicate_reconstruct
    (AyCFTTFactoredBlock sub subLeft subRight)
    parentLeft
    parentRight
    transformed

theorem ay_cftt_two_level_project
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop) :
    AyCFTTOriginal sub subLeft subRight parentLeft parentRight ->
    AyCFTTParentsFactored sub subLeft subRight parentLeft parentRight := by
  intro original
  exact ay_cftt_parent_project sub subLeft subRight parentLeft parentRight
    (ay_cftt_subgates_project
      sub subLeft subRight parentLeft parentRight original)

theorem ay_cftt_two_level_reconstruct
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop) :
    AyCFTTParentsFactored sub subLeft subRight parentLeft parentRight ->
    AyCFTTOriginal sub subLeft subRight parentLeft parentRight := by
  intro transformed
  exact ay_cftt_subgates_reconstruct
    sub subLeft subRight parentLeft parentRight
    (ay_cftt_parent_reconstruct
      sub subLeft subRight parentLeft parentRight transformed)

theorem ay_cftt_tseitin_extend_parent
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (auxParent : Prop)
    (parentLeft : Prop) (parentRight : Prop) :
    AyCFTTEquiv auxParent (AyCFTTFactoredBlock sub subLeft subRight) ->
    AyCFTTParentsFactored sub subLeft subRight parentLeft parentRight ->
    AyCFTTTseitinParent auxParent parentLeft parentRight := by
  intro aux_equiv_parent
  intro factored
  intro result
  intro build
  exact factored result
    (fun parentGate pair =>
      build
        (ay_cftt_equiv_backward
          auxParent
          (AyCFTTFactoredBlock sub subLeft subRight)
          aux_equiv_parent
          parentGate)
        pair)

theorem ay_cftt_tseitin_project_parent
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (auxParent : Prop)
    (parentLeft : Prop) (parentRight : Prop) :
    AyCFTTEquiv auxParent (AyCFTTFactoredBlock sub subLeft subRight) ->
    AyCFTTTseitinParent auxParent parentLeft parentRight ->
    AyCFTTParentsFactored sub subLeft subRight parentLeft parentRight := by
  intro aux_equiv_parent
  intro transformed
  intro result
  intro build
  exact transformed result
    (fun auxGate pair =>
      build
        (ay_cftt_equiv_forward
          auxParent
          (AyCFTTFactoredBlock sub subLeft subRight)
          aux_equiv_parent
          auxGate)
        pair)

theorem ay_cftt_factor_then_tseitin_forward
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (auxParent : Prop)
    (parentLeft : Prop) (parentRight : Prop) :
    AyCFTTEquiv auxParent (AyCFTTFactoredBlock sub subLeft subRight) ->
    AyCFTTOriginal sub subLeft subRight parentLeft parentRight ->
    AyCFTTTseitinParent auxParent parentLeft parentRight := by
  intro aux_equiv_parent
  intro original
  exact ay_cftt_tseitin_extend_parent
    sub subLeft subRight auxParent parentLeft parentRight
    aux_equiv_parent
    (ay_cftt_two_level_project
      sub subLeft subRight parentLeft parentRight original)

theorem ay_cftt_factor_then_tseitin_backward
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (auxParent : Prop)
    (parentLeft : Prop) (parentRight : Prop) :
    AyCFTTEquiv auxParent (AyCFTTFactoredBlock sub subLeft subRight) ->
    AyCFTTTseitinParent auxParent parentLeft parentRight ->
    AyCFTTOriginal sub subLeft subRight parentLeft parentRight := by
  intro aux_equiv_parent
  intro transformed
  exact ay_cftt_two_level_reconstruct
    sub subLeft subRight parentLeft parentRight
    (ay_cftt_tseitin_project_parent
      sub subLeft subRight auxParent parentLeft parentRight
      aux_equiv_parent
      transformed)

theorem ay_cftt_factor_then_tseitin_equisat
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (auxParent : Prop)
    (parentLeft : Prop) (parentRight : Prop) :
    AyCFTTEquiv auxParent (AyCFTTFactoredBlock sub subLeft subRight) ->
    AyCFTTEquisat
      (AyCFTTOriginal sub subLeft subRight parentLeft parentRight)
      (AyCFTTTseitinParent auxParent parentLeft parentRight) := by
  intro aux_equiv_parent
  exact ay_cftt_equisat_intro
    (AyCFTTOriginal sub subLeft subRight parentLeft parentRight)
    (AyCFTTTseitinParent auxParent parentLeft parentRight)
    (ay_cftt_factor_then_tseitin_forward
      sub subLeft subRight auxParent parentLeft parentRight
      aux_equiv_parent)
    (ay_cftt_factor_then_tseitin_backward
      sub subLeft subRight auxParent parentLeft parentRight
      aux_equiv_parent)
