-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked propositional abstraction for circuit-pattern factorization with two
-- levels of repeated gates. First factor repeated subgate occurrences inside a
-- repeated parent gate, then factor the repeated parent gate itself.

def AyCFTLConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyCFTLEquisat (original : Prop) (transformed : Prop) :=
  AyCFTLConj (original -> transformed) (transformed -> original)

def AyCFTLDuplicateBlock (gate : Prop) (left : Prop) (right : Prop) :=
  AyCFTLConj gate (AyCFTLConj left (AyCFTLConj gate right))

def AyCFTLFactoredBlock (gate : Prop) (left : Prop) (right : Prop) :=
  AyCFTLConj gate (AyCFTLConj left right)

def AyCFTLOriginal
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop) :=
  AyCFTLDuplicateBlock
    (AyCFTLDuplicateBlock sub subLeft subRight)
    parentLeft
    parentRight

def AyCFTLSubgatesFactored
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop) :=
  AyCFTLDuplicateBlock
    (AyCFTLFactoredBlock sub subLeft subRight)
    parentLeft
    parentRight

def AyCFTLParentsFactored
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop) :=
  AyCFTLFactoredBlock
    (AyCFTLFactoredBlock sub subLeft subRight)
    parentLeft
    parentRight

theorem ay_cftl_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyCFTLConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_cftl_equisat_intro
    (original : Prop) (transformed : Prop) :
    (original -> transformed) ->
    (transformed -> original) ->
    AyCFTLEquisat original transformed := by
  intro forward
  intro backward
  exact ay_cftl_conj_intro
    (original -> transformed)
    (transformed -> original)
    forward
    backward

theorem ay_cftl_duplicate_project
    (gate : Prop) (left : Prop) (right : Prop) :
    AyCFTLDuplicateBlock gate left right ->
    AyCFTLFactoredBlock gate left right := by
  intro duplicated
  intro result
  intro build
  exact duplicated result
    (fun hgate tail =>
      tail result
        (fun hleft tail2 =>
          tail2 result
            (fun _hgate_again hright =>
              build hgate (ay_cftl_conj_intro left right hleft hright))))

theorem ay_cftl_duplicate_reconstruct
    (gate : Prop) (left : Prop) (right : Prop) :
    AyCFTLFactoredBlock gate left right ->
    AyCFTLDuplicateBlock gate left right := by
  intro factored
  intro result
  intro build
  exact factored result
    (fun hgate tail =>
      tail result
        (fun hleft hright =>
          build hgate
            (ay_cftl_conj_intro
              left
              (AyCFTLConj gate right)
              hleft
              (ay_cftl_conj_intro gate right hgate hright))))

theorem ay_cftl_subgates_project
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop) :
    AyCFTLOriginal sub subLeft subRight parentLeft parentRight ->
    AyCFTLSubgatesFactored sub subLeft subRight parentLeft parentRight := by
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
                (ay_cftl_duplicate_project sub subLeft subRight parentGate)
                (ay_cftl_conj_intro
                  parentLeft
                  (AyCFTLConj
                    (AyCFTLFactoredBlock sub subLeft subRight)
                    parentRight)
                  hparentLeft
                  (ay_cftl_conj_intro
                    (AyCFTLFactoredBlock sub subLeft subRight)
                    parentRight
                    (ay_cftl_duplicate_project
                      sub subLeft subRight parentGateAgain)
                    hparentRight)))))

theorem ay_cftl_subgates_reconstruct
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop) :
    AyCFTLSubgatesFactored sub subLeft subRight parentLeft parentRight ->
    AyCFTLOriginal sub subLeft subRight parentLeft parentRight := by
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
                (ay_cftl_duplicate_reconstruct sub subLeft subRight parentGate)
                (ay_cftl_conj_intro
                  parentLeft
                  (AyCFTLConj
                    (AyCFTLDuplicateBlock sub subLeft subRight)
                    parentRight)
                  hparentLeft
                  (ay_cftl_conj_intro
                    (AyCFTLDuplicateBlock sub subLeft subRight)
                    parentRight
                    (ay_cftl_duplicate_reconstruct
                      sub subLeft subRight parentGateAgain)
                    hparentRight)))))

theorem ay_cftl_parent_project
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop) :
    AyCFTLSubgatesFactored sub subLeft subRight parentLeft parentRight ->
    AyCFTLParentsFactored sub subLeft subRight parentLeft parentRight := by
  intro transformed
  exact ay_cftl_duplicate_project
    (AyCFTLFactoredBlock sub subLeft subRight)
    parentLeft
    parentRight
    transformed

theorem ay_cftl_parent_reconstruct
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop) :
    AyCFTLParentsFactored sub subLeft subRight parentLeft parentRight ->
    AyCFTLSubgatesFactored sub subLeft subRight parentLeft parentRight := by
  intro transformed
  exact ay_cftl_duplicate_reconstruct
    (AyCFTLFactoredBlock sub subLeft subRight)
    parentLeft
    parentRight
    transformed

theorem ay_cftl_two_level_project
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop) :
    AyCFTLOriginal sub subLeft subRight parentLeft parentRight ->
    AyCFTLParentsFactored sub subLeft subRight parentLeft parentRight := by
  intro original
  exact ay_cftl_parent_project sub subLeft subRight parentLeft parentRight
    (ay_cftl_subgates_project
      sub subLeft subRight parentLeft parentRight original)

theorem ay_cftl_two_level_reconstruct
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop) :
    AyCFTLParentsFactored sub subLeft subRight parentLeft parentRight ->
    AyCFTLOriginal sub subLeft subRight parentLeft parentRight := by
  intro transformed
  exact ay_cftl_subgates_reconstruct
    sub subLeft subRight parentLeft parentRight
    (ay_cftl_parent_reconstruct
      sub subLeft subRight parentLeft parentRight transformed)

theorem ay_cftl_two_level_equisat
    (sub : Prop) (subLeft : Prop) (subRight : Prop)
    (parentLeft : Prop) (parentRight : Prop) :
    AyCFTLEquisat
      (AyCFTLOriginal sub subLeft subRight parentLeft parentRight)
      (AyCFTLParentsFactored sub subLeft subRight parentLeft parentRight) := by
  exact ay_cftl_equisat_intro
    (AyCFTLOriginal sub subLeft subRight parentLeft parentRight)
    (AyCFTLParentsFactored sub subLeft subRight parentLeft parentRight)
    (ay_cftl_two_level_project
      sub subLeft subRight parentLeft parentRight)
    (ay_cftl_two_level_reconstruct
      sub subLeft subRight parentLeft parentRight)
