-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked propositional abstraction for the interaction between repeated CNF
-- factorization and Tseitin auxiliary gate extension. Three duplicated circuit
-- subconstraints are factored, then the first factored gate is replaced by an
-- auxiliary gate under an explicit equivalence witness.

def AyFTIConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyFTIEquisat (original : Prop) (transformed : Prop) :=
  AyFTIConj (original -> transformed) (transformed -> original)

def AyFTIEquiv (p : Prop) (q : Prop) :=
  AyFTIConj (p -> q) (q -> p)

def AyFTIDuplicateBlock (sub : Prop) (left : Prop) (right : Prop) :=
  AyFTIConj sub (AyFTIConj left (AyFTIConj sub right))

def AyFTIFactoredBlock (gate : Prop) (left : Prop) (right : Prop) :=
  AyFTIConj gate (AyFTIConj left right)

def AyFTIOriginal
    (subA : Prop) (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (subC : Prop) (leftC : Prop) (rightC : Prop)
    (rest : Prop) :=
  AyFTIConj
    (AyFTIDuplicateBlock subA leftA rightA)
    (AyFTIConj
      (AyFTIDuplicateBlock subB leftB rightB)
      (AyFTIConj (AyFTIDuplicateBlock subC leftC rightC) rest))

def AyFTIFactored
    (subA : Prop) (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (subC : Prop) (leftC : Prop) (rightC : Prop)
    (rest : Prop) :=
  AyFTIConj
    (AyFTIFactoredBlock subA leftA rightA)
    (AyFTIConj
      (AyFTIFactoredBlock subB leftB rightB)
      (AyFTIConj (AyFTIFactoredBlock subC leftC rightC) rest))

def AyFTITseitinFactored
    (auxA : Prop) (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (subC : Prop) (leftC : Prop) (rightC : Prop)
    (rest : Prop) :=
  AyFTIConj
    (AyFTIFactoredBlock auxA leftA rightA)
    (AyFTIConj
      (AyFTIFactoredBlock subB leftB rightB)
      (AyFTIConj (AyFTIFactoredBlock subC leftC rightC) rest))

theorem ay_fti_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyFTIConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_fti_equisat_intro
    (original : Prop) (transformed : Prop) :
    (original -> transformed) ->
    (transformed -> original) ->
    AyFTIEquisat original transformed := by
  intro forward
  intro backward
  exact ay_fti_conj_intro
    (original -> transformed)
    (transformed -> original)
    forward
    backward

theorem ay_fti_equiv_forward
    (p : Prop) (q : Prop) :
    AyFTIEquiv p q -> p -> q := by
  intro equiv
  exact equiv (p -> q) (fun forward _backward => forward)

theorem ay_fti_equiv_backward
    (p : Prop) (q : Prop) :
    AyFTIEquiv p q -> q -> p := by
  intro equiv
  exact equiv (q -> p) (fun _forward backward => backward)

theorem ay_fti_duplicate_block_project
    (sub : Prop) (left : Prop) (right : Prop) :
    AyFTIDuplicateBlock sub left right ->
    AyFTIFactoredBlock sub left right := by
  intro duplicated
  intro result
  intro build
  exact duplicated result
    (fun hsub tail =>
      tail result
        (fun hleft tail2 =>
          tail2 result
            (fun _hsub_again hright =>
              build hsub (ay_fti_conj_intro left right hleft hright))))

theorem ay_fti_duplicate_block_reconstruct
    (sub : Prop) (left : Prop) (right : Prop) :
    AyFTIFactoredBlock sub left right ->
    AyFTIDuplicateBlock sub left right := by
  intro factored
  intro result
  intro build
  exact factored result
    (fun hsub tail =>
      tail result
        (fun hleft hright =>
          build hsub
            (ay_fti_conj_intro
              left
              (AyFTIConj sub right)
              hleft
              (ay_fti_conj_intro sub right hsub hright))))

theorem ay_fti_factor_project
    (subA : Prop) (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (subC : Prop) (leftC : Prop) (rightC : Prop)
    (rest : Prop) :
    AyFTIOriginal
      subA leftA rightA subB leftB rightB subC leftC rightC rest ->
    AyFTIFactored
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
              build
                (ay_fti_duplicate_block_project subA leftA rightA blockA)
                (ay_fti_conj_intro
                  (AyFTIFactoredBlock subB leftB rightB)
                  (AyFTIConj (AyFTIFactoredBlock subC leftC rightC) rest)
                  (ay_fti_duplicate_block_project subB leftB rightB blockB)
                  (ay_fti_conj_intro
                    (AyFTIFactoredBlock subC leftC rightC)
                    rest
                    (ay_fti_duplicate_block_project
                      subC leftC rightC blockC)
                    hrest)))))

theorem ay_fti_factor_reconstruct
    (subA : Prop) (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (subC : Prop) (leftC : Prop) (rightC : Prop)
    (rest : Prop) :
    AyFTIFactored
      subA leftA rightA subB leftB rightB subC leftC rightC rest ->
    AyFTIOriginal
      subA leftA rightA subB leftB rightB subC leftC rightC rest := by
  intro factored
  intro result
  intro build
  exact factored result
    (fun blockA tail =>
      tail result
        (fun blockB tail2 =>
          tail2 result
            (fun blockC hrest =>
              build
                (ay_fti_duplicate_block_reconstruct subA leftA rightA blockA)
                (ay_fti_conj_intro
                  (AyFTIDuplicateBlock subB leftB rightB)
                  (AyFTIConj (AyFTIDuplicateBlock subC leftC rightC) rest)
                  (ay_fti_duplicate_block_reconstruct subB leftB rightB blockB)
                  (ay_fti_conj_intro
                    (AyFTIDuplicateBlock subC leftC rightC)
                    rest
                    (ay_fti_duplicate_block_reconstruct
                      subC leftC rightC blockC)
                    hrest)))))

theorem ay_fti_tseitin_extend_first_gate
    (subA : Prop) (auxA : Prop)
    (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (subC : Prop) (leftC : Prop) (rightC : Prop)
    (rest : Prop) :
    AyFTIEquiv auxA subA ->
    AyFTIFactored
      subA leftA rightA subB leftB rightB subC leftC rightC rest ->
    AyFTITseitinFactored
      auxA leftA rightA subB leftB rightB subC leftC rightC rest := by
  intro aux_equiv_sub
  intro factored
  intro result
  intro build
  exact factored result
    (fun blockA tail =>
      blockA result
        (fun hsubA pairA =>
          tail result
            (fun blockB tail2 =>
              build
                (ay_fti_conj_intro auxA (AyFTIConj leftA rightA)
                  (ay_fti_equiv_backward auxA subA aux_equiv_sub hsubA)
                  pairA)
                (ay_fti_conj_intro
                  (AyFTIFactoredBlock subB leftB rightB)
                  (AyFTIConj (AyFTIFactoredBlock subC leftC rightC) rest)
                  blockB
                  tail2))))

theorem ay_fti_tseitin_project_first_gate
    (subA : Prop) (auxA : Prop)
    (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (subC : Prop) (leftC : Prop) (rightC : Prop)
    (rest : Prop) :
    AyFTIEquiv auxA subA ->
    AyFTITseitinFactored
      auxA leftA rightA subB leftB rightB subC leftC rightC rest ->
    AyFTIFactored
      subA leftA rightA subB leftB rightB subC leftC rightC rest := by
  intro aux_equiv_sub
  intro transformed
  intro result
  intro build
  exact transformed result
    (fun blockA tail =>
      blockA result
        (fun hauxA pairA =>
          tail result
            (fun blockB tail2 =>
              build
                (ay_fti_conj_intro subA (AyFTIConj leftA rightA)
                  (ay_fti_equiv_forward auxA subA aux_equiv_sub hauxA)
                  pairA)
                (ay_fti_conj_intro
                  (AyFTIFactoredBlock subB leftB rightB)
                  (AyFTIConj (AyFTIFactoredBlock subC leftC rightC) rest)
                  blockB
                  tail2))))

theorem ay_fti_factor_then_tseitin_forward
    (subA : Prop) (auxA : Prop)
    (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (subC : Prop) (leftC : Prop) (rightC : Prop)
    (rest : Prop) :
    AyFTIEquiv auxA subA ->
    AyFTIOriginal
      subA leftA rightA subB leftB rightB subC leftC rightC rest ->
    AyFTITseitinFactored
      auxA leftA rightA subB leftB rightB subC leftC rightC rest := by
  intro aux_equiv_sub
  intro original
  exact ay_fti_tseitin_extend_first_gate
    subA auxA leftA rightA subB leftB rightB subC leftC rightC rest
    aux_equiv_sub
    (ay_fti_factor_project
      subA leftA rightA subB leftB rightB subC leftC rightC rest
      original)

theorem ay_fti_factor_then_tseitin_backward
    (subA : Prop) (auxA : Prop)
    (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (subC : Prop) (leftC : Prop) (rightC : Prop)
    (rest : Prop) :
    AyFTIEquiv auxA subA ->
    AyFTITseitinFactored
      auxA leftA rightA subB leftB rightB subC leftC rightC rest ->
    AyFTIOriginal
      subA leftA rightA subB leftB rightB subC leftC rightC rest := by
  intro aux_equiv_sub
  intro transformed
  exact ay_fti_factor_reconstruct
    subA leftA rightA subB leftB rightB subC leftC rightC rest
    (ay_fti_tseitin_project_first_gate
      subA auxA leftA rightA subB leftB rightB subC leftC rightC rest
      aux_equiv_sub
      transformed)

theorem ay_fti_factor_then_tseitin_equisat
    (subA : Prop) (auxA : Prop)
    (leftA : Prop) (rightA : Prop)
    (subB : Prop) (leftB : Prop) (rightB : Prop)
    (subC : Prop) (leftC : Prop) (rightC : Prop)
    (rest : Prop) :
    AyFTIEquiv auxA subA ->
    AyFTIEquisat
      (AyFTIOriginal
        subA leftA rightA subB leftB rightB subC leftC rightC rest)
      (AyFTITseitinFactored
        auxA leftA rightA subB leftB rightB subC leftC rightC rest) := by
  intro aux_equiv_sub
  exact ay_fti_equisat_intro
    (AyFTIOriginal
      subA leftA rightA subB leftB rightB subC leftC rightC rest)
    (AyFTITseitinFactored
      auxA leftA rightA subB leftB rightB subC leftC rightC rest)
    (ay_fti_factor_then_tseitin_forward
      subA auxA leftA rightA subB leftB rightB subC leftC rightC rest
      aux_equiv_sub)
    (ay_fti_factor_then_tseitin_backward
      subA auxA leftA rightA subB leftB rightB subC leftC rightC rest
      aux_equiv_sub)
