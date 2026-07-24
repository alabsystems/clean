-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked propositional abstraction for repeated CNF factorization chains.
-- This models three duplicated circuit subconstraints factored in sequence,
-- with explicit projection and reconstruction maps for the composed transform.

def AyRepeatFactorConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyRepeatFactorEquisat (original : Prop) (transformed : Prop) :=
  AyRepeatFactorConj (original -> transformed) (transformed -> original)

def AyRepeatDuplicateBlock (sub : Prop) (left : Prop) (right : Prop) :=
  AyRepeatFactorConj
    sub
    (AyRepeatFactorConj left (AyRepeatFactorConj sub right))

def AyRepeatFactoredBlock (sub : Prop) (left : Prop) (right : Prop) :=
  AyRepeatFactorConj sub (AyRepeatFactorConj left right)

def AyRepeatFactorOriginal
    (subA : Prop) (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (subC : Prop) (leftC : Prop) (rightC : Prop)
    (rest : Prop) :=
  AyRepeatFactorConj
    (AyRepeatDuplicateBlock subA leftA rightA)
    (AyRepeatFactorConj
      (AyRepeatDuplicateBlock subB leftB rightB)
      (AyRepeatFactorConj
        (AyRepeatDuplicateBlock subC leftC rightC)
        rest))

def AyRepeatFactorAfterFirst
    (subA : Prop) (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (subC : Prop) (leftC : Prop) (rightC : Prop)
    (rest : Prop) :=
  AyRepeatFactorConj
    (AyRepeatFactoredBlock subA leftA rightA)
    (AyRepeatFactorConj
      (AyRepeatDuplicateBlock subB leftB rightB)
      (AyRepeatFactorConj
        (AyRepeatDuplicateBlock subC leftC rightC)
        rest))

def AyRepeatFactorAfterSecond
    (subA : Prop) (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (subC : Prop) (leftC : Prop) (rightC : Prop)
    (rest : Prop) :=
  AyRepeatFactorConj
    (AyRepeatFactoredBlock subA leftA rightA)
    (AyRepeatFactorConj
      (AyRepeatFactoredBlock subB leftB rightB)
      (AyRepeatFactorConj
        (AyRepeatDuplicateBlock subC leftC rightC)
        rest))

def AyRepeatFactorFinal
    (subA : Prop) (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (subC : Prop) (leftC : Prop) (rightC : Prop)
    (rest : Prop) :=
  AyRepeatFactorConj
    (AyRepeatFactoredBlock subA leftA rightA)
    (AyRepeatFactorConj
      (AyRepeatFactoredBlock subB leftB rightB)
      (AyRepeatFactorConj
        (AyRepeatFactoredBlock subC leftC rightC)
        rest))

theorem ay_repeat_factor_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyRepeatFactorConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_repeat_factor_equisat_intro
    (original : Prop) (transformed : Prop) :
    (original -> transformed) ->
    (transformed -> original) ->
    AyRepeatFactorEquisat original transformed := by
  intro forward
  intro backward
  exact ay_repeat_factor_conj_intro
    (original -> transformed)
    (transformed -> original)
    forward
    backward

theorem ay_repeat_duplicate_block_project
    (sub : Prop) (left : Prop) (right : Prop) :
    AyRepeatDuplicateBlock sub left right ->
    AyRepeatFactoredBlock sub left right := by
  intro duplicated
  intro result
  intro build
  exact duplicated result
    (fun hsub tail =>
      tail result
        (fun hleft tail2 =>
          tail2 result
            (fun _hsub_again hright =>
              build hsub
                (ay_repeat_factor_conj_intro left right hleft hright))))

theorem ay_repeat_duplicate_block_reconstruct
    (sub : Prop) (left : Prop) (right : Prop) :
    AyRepeatFactoredBlock sub left right ->
    AyRepeatDuplicateBlock sub left right := by
  intro factored
  intro result
  intro build
  exact factored result
    (fun hsub tail =>
      tail result
        (fun hleft hright =>
          build hsub
            (ay_repeat_factor_conj_intro
              left
              (AyRepeatFactorConj sub right)
              hleft
              (ay_repeat_factor_conj_intro sub right hsub hright))))

theorem ay_repeat_factor_first_project
    (subA : Prop) (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (subC : Prop) (leftC : Prop) (rightC : Prop)
    (rest : Prop) :
    AyRepeatFactorOriginal
      subA leftA rightA subB leftB rightB subC leftC rightC rest ->
    AyRepeatFactorAfterFirst
      subA leftA rightA subB leftB rightB subC leftC rightC rest := by
  intro original
  intro result
  intro build
  exact original result
    (fun blockA tail =>
      build
        (ay_repeat_duplicate_block_project subA leftA rightA blockA)
        tail)

theorem ay_repeat_factor_first_reconstruct
    (subA : Prop) (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (subC : Prop) (leftC : Prop) (rightC : Prop)
    (rest : Prop) :
    AyRepeatFactorAfterFirst
      subA leftA rightA subB leftB rightB subC leftC rightC rest ->
    AyRepeatFactorOriginal
      subA leftA rightA subB leftB rightB subC leftC rightC rest := by
  intro transformed
  intro result
  intro build
  exact transformed result
    (fun blockA tail =>
      build
        (ay_repeat_duplicate_block_reconstruct subA leftA rightA blockA)
        tail)

theorem ay_repeat_factor_second_project
    (subA : Prop) (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (subC : Prop) (leftC : Prop) (rightC : Prop)
    (rest : Prop) :
    AyRepeatFactorAfterFirst
      subA leftA rightA subB leftB rightB subC leftC rightC rest ->
    AyRepeatFactorAfterSecond
      subA leftA rightA subB leftB rightB subC leftC rightC rest := by
  intro original
  intro result
  intro build
  exact original result
    (fun blockA tail =>
      tail result
        (fun blockB tail2 =>
          build blockA
            (ay_repeat_factor_conj_intro
              (AyRepeatFactoredBlock subB leftB rightB)
              (AyRepeatFactorConj
                (AyRepeatDuplicateBlock subC leftC rightC)
                rest)
              (ay_repeat_duplicate_block_project subB leftB rightB blockB)
              tail2)))

theorem ay_repeat_factor_second_reconstruct
    (subA : Prop) (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (subC : Prop) (leftC : Prop) (rightC : Prop)
    (rest : Prop) :
    AyRepeatFactorAfterSecond
      subA leftA rightA subB leftB rightB subC leftC rightC rest ->
    AyRepeatFactorAfterFirst
      subA leftA rightA subB leftB rightB subC leftC rightC rest := by
  intro transformed
  intro result
  intro build
  exact transformed result
    (fun blockA tail =>
      tail result
        (fun blockB tail2 =>
          build blockA
            (ay_repeat_factor_conj_intro
              (AyRepeatDuplicateBlock subB leftB rightB)
              (AyRepeatFactorConj
                (AyRepeatDuplicateBlock subC leftC rightC)
                rest)
              (ay_repeat_duplicate_block_reconstruct subB leftB rightB blockB)
              tail2)))

theorem ay_repeat_factor_third_project
    (subA : Prop) (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (subC : Prop) (leftC : Prop) (rightC : Prop)
    (rest : Prop) :
    AyRepeatFactorAfterSecond
      subA leftA rightA subB leftB rightB subC leftC rightC rest ->
    AyRepeatFactorFinal
      subA leftA rightA subB leftB rightB subC leftC rightC rest := by
  intro original
  intro result
  intro build
  exact original result
    (fun blockA tail =>
      tail result
        (fun blockB tail2 =>
          tail2 result
            (fun blockC hrest =>
              build blockA
                (ay_repeat_factor_conj_intro
                  (AyRepeatFactoredBlock subB leftB rightB)
                  (AyRepeatFactorConj
                    (AyRepeatFactoredBlock subC leftC rightC)
                    rest)
                  blockB
                  (ay_repeat_factor_conj_intro
                    (AyRepeatFactoredBlock subC leftC rightC)
                    rest
                    (ay_repeat_duplicate_block_project subC leftC rightC blockC)
                    hrest)))))

theorem ay_repeat_factor_third_reconstruct
    (subA : Prop) (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (subC : Prop) (leftC : Prop) (rightC : Prop)
    (rest : Prop) :
    AyRepeatFactorFinal
      subA leftA rightA subB leftB rightB subC leftC rightC rest ->
    AyRepeatFactorAfterSecond
      subA leftA rightA subB leftB rightB subC leftC rightC rest := by
  intro transformed
  intro result
  intro build
  exact transformed result
    (fun blockA tail =>
      tail result
        (fun blockB tail2 =>
          tail2 result
            (fun blockC hrest =>
              build blockA
                (ay_repeat_factor_conj_intro
                  (AyRepeatFactoredBlock subB leftB rightB)
                  (AyRepeatFactorConj
                    (AyRepeatDuplicateBlock subC leftC rightC)
                    rest)
                  blockB
                  (ay_repeat_factor_conj_intro
                    (AyRepeatDuplicateBlock subC leftC rightC)
                    rest
                    (ay_repeat_duplicate_block_reconstruct subC leftC rightC blockC)
                    hrest)))))

theorem ay_repeat_factor_chain_project
    (subA : Prop) (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (subC : Prop) (leftC : Prop) (rightC : Prop)
    (rest : Prop) :
    AyRepeatFactorOriginal
      subA leftA rightA subB leftB rightB subC leftC rightC rest ->
    AyRepeatFactorFinal
      subA leftA rightA subB leftB rightB subC leftC rightC rest := by
  intro original
  exact ay_repeat_factor_third_project
    subA leftA rightA subB leftB rightB subC leftC rightC rest
    (ay_repeat_factor_second_project
      subA leftA rightA subB leftB rightB subC leftC rightC rest
      (ay_repeat_factor_first_project
        subA leftA rightA subB leftB rightB subC leftC rightC rest
        original))

theorem ay_repeat_factor_chain_reconstruct
    (subA : Prop) (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (subC : Prop) (leftC : Prop) (rightC : Prop)
    (rest : Prop) :
    AyRepeatFactorFinal
      subA leftA rightA subB leftB rightB subC leftC rightC rest ->
    AyRepeatFactorOriginal
      subA leftA rightA subB leftB rightB subC leftC rightC rest := by
  intro transformed
  exact ay_repeat_factor_first_reconstruct
    subA leftA rightA subB leftB rightB subC leftC rightC rest
    (ay_repeat_factor_second_reconstruct
      subA leftA rightA subB leftB rightB subC leftC rightC rest
      (ay_repeat_factor_third_reconstruct
        subA leftA rightA subB leftB rightB subC leftC rightC rest
        transformed))

theorem ay_repeat_factor_chain_equisat
    (subA : Prop) (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (subC : Prop) (leftC : Prop) (rightC : Prop)
    (rest : Prop) :
    AyRepeatFactorEquisat
      (AyRepeatFactorOriginal
        subA leftA rightA subB leftB rightB subC leftC rightC rest)
      (AyRepeatFactorFinal
        subA leftA rightA subB leftB rightB subC leftC rightC rest) := by
  exact ay_repeat_factor_equisat_intro
    (AyRepeatFactorOriginal
      subA leftA rightA subB leftB rightB subC leftC rightC rest)
    (AyRepeatFactorFinal
      subA leftA rightA subB leftB rightB subC leftC rightC rest)
    (ay_repeat_factor_chain_project
      subA leftA rightA subB leftB rightB subC leftC rightC rest)
    (ay_repeat_factor_chain_reconstruct
      subA leftA rightA subB leftB rightB subC leftC rightC rest)
